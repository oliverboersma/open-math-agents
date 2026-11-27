import FormalConjectures.Wikipedia.ButsonHadamardMatrix

/-! Fourth-root Hadamard matrices from finite fields and dephased phase cores.

The quadratic character over every odd finite field gives a conference
matrix. Adding the appropriate fourth root on its diagonal gives a
quaternary Hadamard matrix of order q+1. Kronecker products then remove
all powers of two from the half-order. A complementary pair supplies
another construction. For the remaining odd half-orders, a dephased
matrix exists exactly when its finite phase core has two specified
difference counts for every pair of distinct rows.

For the conference construction see Paley, On orthogonal matrices (1933).
For the fourth-root problem see Turyn, Complex Hadamard matrices (1970). -/

namespace QuaternaryPaley

/-- The quadratic characters of two translates have correlation minus one
off the diagonal. At equal translates every nonzero argument contributes one. -/
theorem correlation {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (x y : F) :
    (∑ t : F, quadraticChar F (x-t) * quadraticChar F (y-t)) =
      if x=y then (Fintype.card F : ℤ)-1 else -1 := by
  by_cases hxy : x = y
  · subst y
    rw [if_pos rfl]
    have term (t : F) : quadraticChar F (x-t) * quadraticChar F (x-t) =
        1 - (if t=x then 1 else 0 : ℤ) := by
      by_cases ht : t=x
      · subst t; simp
      · simpa [ht, ← pow_two] using quadraticChar_sq_one (sub_ne_zero.mpr (Ne.symm ht))
    simp_rw [term]
    simp [Finset.sum_sub_distrib]
  · rw [if_neg hxy]
    let e : F ≃ F := ((Equiv.subLeft y).trans (Equiv.divLeft₀ (x-y) (sub_ne_zero.mpr hxy))).trans
      (Equiv.addLeft 1)
    have he (t : F) : e t = 1 + (x-y)/(y-t) := rfl
    have term (t : F) : quadraticChar F (x-t) * quadraticChar F (y-t) =
        quadraticChar F (e t) - (if t=y then 1 else 0 : ℤ) := by
      by_cases ht : t=y
      · subst t; simp [he]
      · have hz : y-t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
        have split_product : (x-t)*(y-t) = e t * (y-t)^2 := by
          rw [he]
          field_simp [hz]
          ring
        rw [← map_mul, split_product, map_mul, quadraticChar_sq_one' hz, mul_one,
          if_neg ht, sub_zero]
    simp_rw [term]
    rw [Finset.sum_sub_distrib, e.sum_comp (quadraticChar F), quadraticChar_sum_zero hF]
    simp

end QuaternaryPaley

namespace QuaternaryPaley

/-- A symmetric conference matrix is completed with an imaginary diagonal, and a
skew-symmetric conference matrix with a real diagonal. -/
private lemma complete_conference {S : Type*} [Fintype S] [DecidableEq S] (C : Matrix S S ℤ)
    (q ε : ℤ) (hε : ε=1 ∨ ε = -1) (hd : ∀ i, C i i=0)
    (ho : ∀ i j, i≠j → C i j=1 ∨ C i j = -1) (ht : ∀ i j, C j i=ε*C i j)
    (hgram : ∀ i j, (∑ t, C i t*C j t) = if i=j then q else 0) :
    ∃ H : Matrix S S ℂ, (∀ i j, H i j^4=1) ∧
      ∀ i j, (∑ t, H i t*star (H j t)) = if i=j then (q : ℂ)+1 else 0 := by
  classical
  let E (i j : S) : ℂ := C i j
  have hreal (i j : S) : star (E i j)=E i j := star_intCast _
  have hg (i j : S) : (∑ t, E i t*E j t)=if i=j then (q : ℂ) else 0 := by
    have h := congrArg (fun z : ℤ => (z : ℂ)) (hgram i j)
    by_cases hij : i=j <;> simpa only [hij,ite_true,ite_false,Int.cast_sum,Int.cast_mul,Int.cast_zero,E] using h
  have he (i j : S) : E j i = (ε : ℂ)*E i j := by
    dsimp only [E]
    exact_mod_cast ht i j
  obtain ⟨d,hfour,hnorm,hcancel⟩ : ∃ d : ℂ, d^4=1 ∧ d*star d=1 ∧ star d+d*(ε : ℂ)=0 := by
    rcases hε with rfl|rfl
    · refine ⟨Complex.I,Complex.I_pow_four,?_,?_⟩ <;> simp
    · refine ⟨1,?_,?_,?_⟩ <;> norm_num
  let D (i t : S) : ℂ := if i=t then d else 0
  let H : Matrix S S ℂ := fun i j => E i j + D i j
  refine ⟨H,?_,?_⟩
  · intro i j
    by_cases hij : i=j
    · subst j
      simpa [H,E,D,hd] using hfour
    · rcases ho i j hij with h|h <;> norm_num [H,E,D,hij,h]
  · intro i j
    have col (f : S → ℂ) (l : S) : (∑ t, f t*star (D l t))=f l*star d := by
      simp [D,apply_ite,Finset.sum_ite_eq]
    have row (f : S → ℂ) (l : S) : (∑ t, D l t*f t)=d*f l := by
      simp [D,ite_mul,Finset.sum_ite_eq]
    have ddiag : (∑ t, D i t*star (D j t))=if i=j then 1 else 0 := by
      rw [row]
      by_cases hij : i=j
      · subst j
        simpa only [D,if_true] using hnorm
      · simp only [D,if_neg (Ne.symm hij),if_neg hij,star_zero,mul_zero]
    have hc : E i j * star d + d * E j i=0 := by
      rw [he i j,show E i j * star d + d*((ε : ℂ)*E i j) = E i j*(star d+d*ε) by ring,hcancel,mul_zero]
    simp only [H,star_add,hreal,add_mul,mul_add,Finset.sum_add_distrib]
    rw [hg,col,row,ddiag]
    by_cases hij : i=j <;> simp only [hij,ite_true,ite_false] at hc ⊢ <;> linear_combination hc

/-- The Paley conference construction for any finite field of odd characteristic. -/
lemma field_order_of_correlation {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2)
    (cor : ∀ x y : F, (∑ t : F, quadraticChar F (x-t)*quadraticChar F (y-t)) =
      if x=y then (Fintype.card F : ℤ)-1 else -1) :
    ∃ M, ButsonHadamardMatrix.IsButsonHadamard (n:=Fintype.card F+1) 4 M := by
  classical
  let ε := quadraticChar F (-1)
  let C : Matrix (Option F) (Option F) ℤ
    | none,none => 0
    | none,some _ => 1
    | some _,none => ε
    | some i,some j => quadraticChar F (i-j)
  have hε : ε=1 ∨ ε = -1 := quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1:F) ≠ 0))
  have hs : ε*ε=1 := by rcases hε with h|h <;> rw [h] <;> norm_num
  have hzero (x : F) : (∑ t : F, quadraticChar F (x-t))=0 :=
    ((Equiv.subLeft x).sum_comp (quadraticChar F)).trans (quadraticChar_sum_zero hF)
  have hd (i : Option F) : C i i=0 := by cases i <;> simp [C]
  have ho (i j : Option F) (hne : i≠j) : C i j=1 ∨ C i j = -1 := by
    rcases i with _|i <;> rcases j with _|j
    · exact (hne rfl).elim
    · exact Or.inl rfl
    · exact hε
    · exact quadraticChar_dichotomy (sub_ne_zero.mpr (fun h => hne (congrArg some h)))
  have ht (i j : Option F) : C j i=ε*C i j := by
    rcases i with _|i <;> rcases j with _|j
    · simp [C]
    · simp [C]
    · exact hs.symm
    · change quadraticChar F (j-i)=quadraticChar F (-1)*quadraticChar F (i-j)
      rw [← map_mul,neg_one_mul,neg_sub]
  have hg (i j : Option F) : (∑ t, C i t*C j t)=if i=j then (Fintype.card F : ℤ) else 0 := by
    rcases i with _|i <;> rcases j with _|j
    · simp [Fintype.sum_option,C]
    · simpa [Fintype.sum_option,C] using hzero j
    · simpa [Fintype.sum_option,C] using hzero i
    · simp only [Fintype.sum_option,C,hs,cor,Option.some.injEq]
      by_cases h : i=j <;> simp [h]
  obtain ⟨H,hfour,hgram⟩ := complete_conference C (Fintype.card F) ε hε hd ho ht hg
  let e : Fin (Fintype.card F+1) ≃ Option F := Fintype.equivOfCardEq (by simp)
  refine ⟨H.submatrix e e,by decide,fun i j => hfour (e i) (e j),?_⟩
  ext i j
  change (∑ t, H (e i) (e t)*star (H (e j) (e t))) = _
  rw [e.sum_comp (fun t => H (e i) t*star (H (e j) t)),hgram]
  simp [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_ite]

/-- Every odd prime power gives a fourth-root Hadamard matrix of the next order. -/
lemma prime_power_order (p k : ℕ) (hp : p.Prime) (ho : p ≠ 2) (hk : 0 < k) :
    ∃ M, ButsonHadamardMatrix.IsButsonHadamard (n:=p^k+1) 4 M := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hF : ringChar (GaloisField p k) ≠ 2 := by rw [ringChar.eq _ p]; exact ho
  have hcard : Fintype.card (GaloisField p k)=p^k :=
    Fintype.card_eq_nat_card.trans (GaloisField.card p k hk.ne')
  rw [← hcard]
  exact field_order_of_correlation hF (correlation hF)

end QuaternaryPaley

namespace QuaternaryCore

open ButsonHadamardMatrix
open scoped Kronecker

/-- Kronecker multiplication preserves fourth-root entries and the scalar Gram matrix. -/
lemma product {m n : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} {B : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsButsonHadamard 4 A) (hB : IsButsonHadamard 4 B) :
    ∃ H, IsButsonHadamard (n := m*n) 4 H := by
  classical
  let e : Fin (m*n) ≃ Fin m × Fin n := Fintype.equivOfCardEq (by simp)
  let P := A ⊗ₖ B
  have hP : P * P.conjTranspose = ((m*n : ℕ) : ℂ) • 1 := by
    dsimp only [P]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA.2.2, hB.2.2,
      Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul, Nat.cast_mul]
  refine ⟨P.submatrix e e, by decide, ?_, ?_⟩
  · intro i j
    change (A (e i).1 (e j).1 * B (e i).2 (e j).2)^4 = 1
    rw [mul_pow, hA.2.1, hB.2.1, one_mul]
  · rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hP]
    change ((m*n : ℕ) : ℂ) • ((1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ).submatrix e e) = _
    rw [Matrix.submatrix_one_equiv]

end QuaternaryCore

namespace QuaternaryCore

/-- The all-ones column cancels the excess of phase differences equal to two.
Equal numbers of the two imaginary phases cancel in every off-diagonal row product. -/
lemma of_counts {n : ℕ} (C : Fin n → Fin n → ZMod 4)
    (h : let row (x : Option (Fin n)) (j : Fin n) := x.elim 0 (fun i => C i j)
         ∀ x y : Option (Fin n), x ≠ y →
           let count (k : ZMod 4) := (Finset.univ.filter (fun j => row x j - row y j = k)).card
           count 2 = count 0 + 1 ∧ count 1 = count 3) :
    ∃ M, ButsonHadamardMatrix.IsButsonHadamard (n:=n+1) 4 M := by
  classical
  let phase (k : ZMod 4) : ℂ := ![1, Complex.I, -1, -Complex.I] k
  let row (x : Option (Fin n)) (j : Fin n) := x.elim 0 (fun i => C i j)
  let count (d : Fin n → ZMod 4) (k : ZMod 4) := (Finset.univ.filter (fun i => d i=k)).card
  have roots (k : ZMod 4) : phase k ^ 4 = 1 := by
    fin_cases k <;> norm_num [phase,pow_succ,Complex.I_mul_I]
  have product (a b : ZMod 4) : phase a * star (phase b) = phase (a-b) := by
    fin_cases a <;> fin_cases b <;> norm_num [phase,Complex.star_def,Complex.conj_I,Complex.I_mul_I] <;> rfl
  have sums (d : Fin n → ZMod 4) : (∑ j, phase (d j)) =
      (count d 0 : ℂ) - count d 2 + Complex.I*((count d 1 : ℂ) - count d 3) := by
    calc
      _ = ∑ k : ZMod 4, (count d k : ℂ)*phase k := by
        rw [← Finset.sum_fiberwise' Finset.univ d phase]
        simp only [Finset.sum_const,nsmul_eq_mul,count]
      _ = _ := by
        change (∑ k : Fin 4, (count d k : ℂ)*phase k) = _
        rw [Fin.sum_univ_four]
        change (count d 0 : ℂ)*1 + count d 1*Complex.I + count d 2*(-1) + count d 3*(-Complex.I) = _
        ring
  let e := finSuccEquiv n
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ := fun i => Fin.cases 1 (fun k => phase (row (e i) k))
  have gram (i j : Fin (n+1)) : (M*M.conjTranspose) i j =
      1 + ∑ k, phase (row (e i) k-row (e j) k) := by
    change (∑ k, M i k * star (M j k)) = _
    rw [Fin.sum_univ_succ]
    simp only [M,Fin.cases_zero,Fin.cases_succ,star_one,mul_one,product]
  refine ⟨M,by decide,?_,?_⟩
  · intro i j
    cases j using Fin.cases with
    | zero => simp [M]
    | succ j => exact roots _
  · ext i j
    rw [gram,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    by_cases hij : i=j
    · subst j
      simp [phase,add_comm]
    · let d (k : Fin n) := row (e i) k-row (e j) k
      obtain ⟨hr,hi⟩ := h (e i) (e j) (fun he => hij (e.injective he))
      change count d 2 = count d 0+1 at hr
      change count d 1 = count d 3 at hi
      change 1 + ∑ k, phase (d k) = _
      rw [sums,hr,hi,if_neg hij,mul_zero]
      push_cast
      ring

end QuaternaryCore

namespace QuaternaryCore

/-- Dephasing any fourth-root Hadamard matrix gives a core with the two difference-count identities. -/
lemma counts_of_matrix {n : ℕ} {M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ}
    (h : ButsonHadamardMatrix.IsButsonHadamard 4 M) :
    ∃ C : Fin n → Fin n → ZMod 4,
      let row (x : Option (Fin n)) (j : Fin n) := x.elim 0 (fun i => C i j)
      ∀ x y : Option (Fin n), x ≠ y →
        let count (k : ZMod 4) := (Finset.univ.filter (fun j => row x j-row y j=k)).card
        count 2 = count 0 + 1 ∧ count 1 = count 3 := by
  classical
  let phase (k : ZMod 4) : ℂ := ![1,Complex.I,-1,-Complex.I] k
  have product (a b : ZMod 4) : phase a * star (phase b) = phase (a-b) := by
    fin_cases a <;> fin_cases b <;> norm_num [phase,Complex.star_def,Complex.conj_I,Complex.I_mul_I] <;> rfl
  have add_phase (a b : ZMod 4) : phase a * phase b = phase (a+b) := by
    fin_cases a <;> fin_cases b <;> norm_num [phase,Complex.I_mul_I] <;> rfl
  have classify (z : ℂ) (hz : z^4=1) : ∃ k, z=phase k := by
    have hsq : (z^2)^2=1 := by simpa only [← pow_mul] using hz
    rcases sq_eq_one_iff.mp hsq with hp|hm
    · rcases sq_eq_one_iff.mp hp with hz|hz
      · exact ⟨0,hz⟩
      · exact ⟨2,hz⟩
    · have hf : (z-Complex.I)*(z+Complex.I)=0 := by
        calc
          _ = z^2-Complex.I^2 := by ring
          _ = 0 := by rw [hm,Complex.I_sq,sub_self]
      rcases mul_eq_zero.mp hf with hp|hm
      · exact ⟨1,sub_eq_zero.mp hp⟩
      · exact ⟨3,eq_neg_of_add_eq_zero_left hm⟩
  choose L hL using fun i j => classify (M i j) (h.2.1 i j)
  have orth (i j : Fin (n+1)) (hij : i≠j) : ∑ k, phase (L i k-L j k) = 0 := by
    have entry := congrFun (congrFun h.2.2 i) j
    change (∑ k, M i k * star (M j k)) = _ at entry
    simpa only [hL,product,Matrix.smul_apply,Matrix.one_apply,if_neg hij,smul_eq_mul,mul_zero] using entry
  let e := finSuccEquiv n
  let R (i j : Fin (n+1)) := L i j-L 0 j-L i 0+L 0 0
  let C (i j : Fin n) := R i.succ j.succ
  let row (x : Option (Fin n)) (j : Fin n) := x.elim 0 (fun i => C i j)
  have proper (x : Option (Fin n)) (j : Fin n) : row x j=R (e.symm x) j.succ := by
    cases x <;> simp [row,C,R,e]
  refine ⟨C,?_⟩
  dsimp only
  intro x y hxy
  let u := e.symm x
  let v := e.symm y
  have huv : u≠v := fun hab => hxy (e.symm.injective hab)
  have corr : (∑ k, phase (R u k - R v k))=0 := by
    calc
      _ = (∑ k, phase (L u k - L v k))*phase (L v 0 - L u 0) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        rw [add_phase]
        congr 1
        dsimp [R]
        abel
      _ = 0 := by rw [orth u v huv,zero_mul]
  let d (k : Fin n) := row x k - row y k
  let count (k : ZMod 4) := (Finset.univ.filter (fun i => d i=k)).card
  have hz : (1 : ℂ) + ∑ k, phase (d k)=0 := by
    rw [Fin.sum_univ_succ] at corr
    simpa only [d,proper,u,v,show ∀ i, R i 0=0 from fun i => by dsimp [R]; abel,
      sub_self,show phase 0=1 from rfl] using corr
  have sum_diff : (∑ j, phase (d j)) = (count 0 : ℂ)-count 2 + Complex.I*((count 1 : ℂ)-count 3) := by
    calc
      _ = ∑ k : ZMod 4, (count k : ℂ)*phase k := by
        rw [← Finset.sum_fiberwise' Finset.univ d phase]
        simp only [Finset.sum_const,nsmul_eq_mul,count]
      _ = _ := by
        change (∑ k : Fin 4, (count k : ℂ)*phase k) = _
        rw [Fin.sum_univ_four]
        change (count 0 : ℂ)*1 + count 1*Complex.I + count 2*(-1) + count 3*(-Complex.I) = _
        ring
  rw [sum_diff] at hz
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp [Complex.mul_re] at hr
  simp [Complex.mul_im] at hi
  change count 2=count 0+1 ∧ count 1=count 3
  constructor
  · have q : (count 2 : ℝ)=(count 0 : ℝ)+1 := by linarith
    exact_mod_cast q
  · have q : (count 1 : ℝ)=(count 3 : ℝ) := by linarith
    exact_mod_cast q

end QuaternaryCore

namespace QuaternaryCore

/-- Exact dephased-core search at each order, including the one-dimensional case. -/
lemma core_iff {n : ℕ} : (∃ M, ButsonHadamardMatrix.IsButsonHadamard (n:=n+1) 4 M) ↔
    ∃ C : Fin n → Fin n → ZMod 4,
      let row (x : Option (Fin n)) (j : Fin n) := x.elim 0 (fun i => C i j)
      ∀ x y : Option (Fin n), x ≠ y →
        let count (k : ZMod 4) := (Finset.univ.filter (fun j => row x j - row y j = k)).card
        count 2 = count 0 + 1 ∧ count 1 = count 3 := by
  constructor
  · rintro ⟨M,hM⟩
    exact counts_of_matrix hM
  · rintro ⟨C,hC⟩
    exact of_counts C hC

end QuaternaryCore

namespace OMA.R_ButsonHadamardMatrix_butson_hadamard_fourth_roots_conjecture_R1

open ButsonHadamardMatrix

section Complementary

/-- A periodic complementary pair yields a fourth-root Hadamard matrix. -/
def H1 : Prop :=
  ∀ m : ℕ, 0 < m → ∀ a b : Fin m → ℂ, (∀ j, a j ^ 4 = 1 ∧ b j ^ 4 = 1) →
    (∀ i k : Fin m, i ≠ k → (∑ j : Fin m, (a (j+i)*star (a (j+k)) + b (j+i)*star (b (j+k)))) = 0) →
    ∃ M, IsButsonHadamard (n:=2*m) 4 M

end Complementary

section Residual

/-- Finite phase cores for odd half-orders outside the two constructions. -/
def H2 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m →
    (¬ ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < k ∧ 2*m = p^k+1) →
    let phase (k : ZMod 4) : ℂ := ![1,Complex.I,-1,-Complex.I] k
    (¬ ∃ u v : Fin m → ZMod 4, ∀ i k : Fin m, i ≠ k →
      (∑ j : Fin m, (phase (u (j+i)) * star (phase (u (j+k))) +
        phase (v (j+i)) * star (phase (v (j+k))))) = 0) →
    let n := 2*m-1
    ∃ C : Fin n → Fin n → ZMod 4,
      let row (x : Option (Fin n)) (j : Fin n) := x.elim 0 (fun i => C i j)
      ∀ x y : Option (Fin n), x ≠ y →
        let count (k : ZMod 4) := (Finset.univ.filter (fun j => row x j - row y j = k)).card
        count 2 = count 0 + 1 ∧ count 1 = count 3

end Residual

theorem main : H1 → H2 → type_of% @ButsonHadamardMatrix.butson_hadamard_fourth_roots_conjecture := by
  classical
  intro h₁ h₂ m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases first : m=1
    · subst m
      exact exists_isButsonHadamard_four_two
    by_cases even : Even m
    · obtain ⟨k,hk⟩ := even
      have hkpos : 1 ≤ k := by omega
      obtain ⟨B,hB⟩ := ih k (by omega) hkpos
      obtain ⟨A,hA⟩ := exists_isButsonHadamard_four_two
      rw [show m=2*k by omega]
      exact QuaternaryCore.product hA hB
    have odd : Odd m := Nat.not_even_iff_odd.mp even
    by_cases paley : ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < k ∧ 2*m = p^k+1
    · obtain ⟨p,k,hp,ho,hk,he⟩ := paley
      rw [he]
      exact QuaternaryPaley.prime_power_order p k hp ho hk
    let phase (k : ZMod 4) : ℂ := ![1,Complex.I,-1,-Complex.I] k
    have roots (z : ZMod 4) : phase z ^ 4 = 1 := by
      fin_cases z <;> norm_num [phase,Complex.I_sq,pow_succ] <;> rfl
    by_cases pair : ∃ u v : Fin m → ZMod 4, ∀ i k : Fin m, i ≠ k →
      (∑ j : Fin m, (phase (u (j+i)) * star (phase (u (j+k))) +
        phase (v (j+i)) * star (phase (v (j+k))))) = 0
    · obtain ⟨u,v,h⟩ := pair
      exact h₁ m hm (fun i => phase (u i)) (fun i => phase (v i))
        (fun i => ⟨roots _, roots _⟩) h
    · have hc := (QuaternaryCore.core_iff (n:=2*m-1)).mpr (h₂ m (by omega) odd paley pair)
      exact Eq.mp (congrArg (fun N : ℕ => ∃ M, IsButsonHadamard (n:=N) 4 M)
        (show 2*m-1+1=2*m by omega)) hc

end OMA.R_ButsonHadamardMatrix_butson_hadamard_fourth_roots_conjecture_R1
