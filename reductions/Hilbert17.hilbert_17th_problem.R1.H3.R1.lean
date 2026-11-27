import OMAReductions.R_Hilbert17_hilbert_17th_problem_R1
import Mathlib

-- Reduction Hilbert17.hilbert_17th_problem.R1.H3.R1 of Hilbert17.hilbert_17th_problem.R1.H3
-- Credit: @green-notes

/-!
Reduces the Tarski-Seidenberg transfer hypothesis (`Hilbert17.hilbert_17th_problem.R1.H3`) to three
independent pillars of the Cohen-Hormander decision method:
1. `H1`: Intermediate Value Theorem for polynomials over any ordered real closed field.
2. `H2`: Polynomial Mean Value Theorem and asymptotic leading-coefficient sign dominance for any
   ordered field satisfying Polynomial IVT.
3. `H3`: One-variable Cohen-Hormander sign-system transfer over a commutative ring `A` between two
   ordered fields satisfying IVT, MVT, and asymptotic sign dominance.
-/

namespace OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1

def H1 : Prop :=
  ∀ {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (p : Polynomial R) {a b : R}, a < b → p.eval a < 0 → 0 < p.eval b →
    ∃ c : R, a < c ∧ c < b ∧ p.eval c = 0

def H2 : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K],
    (∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0) →
    (∀ (p : Polynomial K) {u v : K}, u < v →
      ∃ c : K, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c) ∧
    (∀ (p : Polynomial K), p ≠ 0 →
      ∃ M : K, ∀ x : K, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))

def H3 : Prop :=
  ∀ {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂],
    (∀ (p : Polynomial K₁) {a b : K₁}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₁, a < c ∧ c < b ∧ p.eval c = 0) →
    (∀ (p : Polynomial K₂) {a b : K₂}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₂, a < c ∧ c < b ∧ p.eval c = 0) →
    (∀ (p : Polynomial K₁) {u v : K₁}, u < v →
      ∃ c : K₁, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c) →
    (∀ (p : Polynomial K₂) {u v : K₂}, u < v →
      ∃ c : K₂, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c) →
    (∀ (p : Polynomial K₁), p ≠ 0 →
      ∃ M : K₁, ∀ x : K₁, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0)) →
    (∀ (p : Polynomial K₂), p ≠ 0 →
      ∃ M : K₂, ∀ x : K₂, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0)) →
    ∀ (φ₁ : A →+* K₁) (P : List (Polynomial A)),
      ∃ Q : List A, ∀ (φ₂ : A →+* K₂),
        (∀ r ∈ Q, (φ₁ r < 0 ↔ φ₂ r < 0) ∧ (φ₁ r = 0 ↔ φ₂ r = 0)) →
        ∀ t₁ : K₁, ∃ t₂ : K₂, ∀ p ∈ P,
          ((p.map φ₁).eval t₁ < 0 ↔ (p.map φ₂).eval t₂ < 0) ∧
          ((p.map φ₁).eval t₁ = 0 ↔ (p.map φ₂).eval t₂ = 0)

section Helpers

lemma real_ivt (p : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ c : ℝ, a < c ∧ c < b ∧ p.eval c = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) := ⟨ha, hb⟩
  obtain ⟨c, hcIoo, hce⟩ := intermediate_value_Ioo hab.le p.continuous.continuousOn hmem
  exact ⟨c, hcIoo.1, hcIoo.2, hce⟩

lemma real_hom_sign {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (j : ℝ →+* R) (r : ℝ) :
    (j r < 0 ↔ r < 0) ∧ (j r = 0 ↔ r = 0) := by
  have hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ j x := by
    intro x hx
    have hsq : x = (Real.sqrt x) ^ 2 := (Real.sq_sqrt hx).symm
    rw [hsq, map_pow]
    exact sq_nonneg (j (Real.sqrt x))
  have heq : j r = 0 ↔ r = 0 := map_eq_zero j
  refine ⟨?_, heq⟩
  constructor
  · intro hj
    by_contra hnr
    have hr : 0 ≤ r := le_of_not_gt hnr
    exact not_lt_of_ge (hnonneg r hr) hj
  · intro hr
    have hpos : 0 ≤ -r := neg_nonneg.mpr hr.le
    have hj_le : j r ≤ 0 := by
      have h0 := hnonneg (-r) hpos
      rw [map_neg] at h0
      linarith
    have hj_ne : j r ≠ 0 := fun h => hr.ne (heq.mp h)
    exact lt_of_le_of_ne hj_le hj_ne

lemma eval₂_finCons {n : ℕ} {R : Type} [CommRing R] (j : ℝ →+* R) (y : R) (s : Fin n → R)
    (f : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial.eval₂ j (Fin.cons y s) f =
      Polynomial.eval y
        (Polynomial.map (MvPolynomial.eval₂Hom j s) (MvPolynomial.finSuccEquiv ℝ n f)) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq =>
    simp [map_add, hp, hq]
  | mul_X p i hp =>
    refine Fin.cases ?_ ?_ i
    · simp [hp, MvPolynomial.finSuccEquiv_X_zero]
    · intro k
      simp [hp, MvPolynomial.finSuccEquiv_X_succ]

lemma transfer_list {n : ℕ} {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] (h1 : H1) (h2 : H2) (h3 : H3) (j : ℝ →+* R) :
    ∀ (L : List (MvPolynomial (Fin n) ℝ)) (y : Fin n → R),
      ∃ x : Fin n → ℝ, ∀ p ∈ L,
        (MvPolynomial.eval₂ j y p < 0 ↔ MvPolynomial.eval x p < 0) ∧
        (MvPolynomial.eval₂ j y p = 0 ↔ MvPolynomial.eval x p = 0) := by
  induction n with
  | zero =>
    intro L y
    refine ⟨Fin.elim0, fun p _ => ?_⟩
    have hp : p = MvPolynomial.C (p.coeff 0) := MvPolynomial.eq_C_of_isEmpty p
    conv_lhs => rw [hp]
    conv_rhs => rw [hp]
    simp only [MvPolynomial.eval₂_C, MvPolynomial.eval_C]
    exact real_hom_sign j (p.coeff 0)
  | succ n ih =>
    intro L y
    have hIVTR : ∀ (p : Polynomial R) {a b : R}, a < b → p.eval a < 0 → 0 < p.eval b →
        ∃ c : R, a < c ∧ c < b ∧ p.eval c = 0 := fun p {_ _} hab => h1 p hab
    obtain ⟨hMVTR, hAsympR⟩ := h2 hIVTR
    obtain ⟨hMVTReal, hAsympReal⟩ := h2 real_ivt
    let P : List (Polynomial (MvPolynomial (Fin n) ℝ)) := L.map (MvPolynomial.finSuccEquiv ℝ n)
    let y' : Fin n → R := Fin.tail y
    let t₁ : R := y 0
    let φ₁ : MvPolynomial (Fin n) ℝ →+* R := MvPolynomial.eval₂Hom j y'
    obtain ⟨Q, hQ⟩ := h3 hIVTR real_ivt hMVTR hMVTReal hAsympR hAsympReal φ₁ P
    obtain ⟨x', hx'⟩ := ih Q y'
    let φ₂ : MvPolynomial (Fin n) ℝ →+* ℝ := MvPolynomial.eval x'
    have hagree : ∀ r ∈ Q, (φ₁ r < 0 ↔ φ₂ r < 0) ∧ (φ₁ r = 0 ↔ φ₂ r = 0) := by
      intro r hr
      simpa [φ₁, φ₂] using hx' r hr
    obtain ⟨t₂, ht₂⟩ := hQ φ₂ hagree t₁
    refine ⟨Fin.cons t₂ x', fun p hp => ?_⟩
    have hpP : MvPolynomial.finSuccEquiv ℝ n p ∈ P := List.mem_map_of_mem hp
    have hsigns := ht₂ (MvPolynomial.finSuccEquiv ℝ n p) hpP
    have hy_eq : y = Fin.cons t₁ y' := (Fin.cons_self_tail y).symm
    have hlhs : MvPolynomial.eval₂ j y p =
        (Polynomial.map φ₁ (MvPolynomial.finSuccEquiv ℝ n p)).eval t₁ := by
      conv_lhs => rw [hy_eq]
      exact eval₂_finCons j t₁ y' p
    have hrhs : MvPolynomial.eval (Fin.cons t₂ x') p =
        (Polynomial.map φ₂ (MvPolynomial.finSuccEquiv ℝ n p)).eval t₂ :=
      MvPolynomial.eval_eq_eval_mv_eval' x' t₂ p
    rw [hlhs, hrhs]
    exact hsigns

end Helpers

theorem main : H1 → H2 → H3 → OMA.R_Hilbert17_hilbert_17th_problem_R1.H3 := by
  intro h1 h2 h3 n R _ _ _ _ j f ⟨y, hy⟩
  obtain ⟨x, hx⟩ := transfer_list h1 h2 h3 j [f] y
  exact ⟨x, (hx f (List.mem_singleton_self f)).1.mp hy⟩

end OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1
