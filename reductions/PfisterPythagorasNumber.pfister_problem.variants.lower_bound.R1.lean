import FormalConjectures.Paper.PfisterPythagorasNumber

/-!
# Reduction of the Cassels-Ellison-Pfister lower bound for the Pythagoras number

This reduction splits `PfisterPythagorasNumber.pfister_problem.variants.lower_bound`
(`n + 2 ≤ p(ℝ(X_1, ..., X_n))` for `n ≥ 2`) into its two classical ingredients:
- `H1`: Cassels-Ellison-Pfister (1971), that the Motzkin polynomial is not a sum of 3 squares
  in `ℝ(X_0, X_1)`;
- `H2`: Cassels (1964), that adjoining a new variable `X_k` and adding `X_k^2` raises the
  minimum number of squares needed by at least 1.

The reduction proves the explicit sum-of-squares representation of the Motzkin polynomial in
`ℝ(X_0, X_1)`, lifts sums of squares along `MvPolynomial.rename Fin.castSucc`, and concludes
for every `n ≥ 2` by induction.
-/

-- Reduction PfisterPythagorasNumber.pfister_problem.variants.lower_bound.R1 of Pfister's problem on the Pythagoras number of $\mathbb{R}(X_1, \dots, X_n)$ — lower bound
-- Credit: @mvanhorn
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1

/-- Cassels-Ellison-Pfister (1971): the Motzkin polynomial is not a sum of 3 squares in R(X_0, X_1). -/
def H1 : Prop :=
  ¬ IsSumSqOfLength 3 (algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)
    (1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
      MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 -
      3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2))

/-- Cassels (1964) variable-adjunction step: if f is not a sum of m squares in R(X_0, ..., X_{k-1}),
then f + X_k^2 is not a sum of m + 1 squares in R(X_0, ..., X_k). -/
def H2 : Prop :=
  ∀ (k m : ℕ) (f : MvPolynomial (Fin k) ℝ),
    ¬ IsSumSqOfLength m (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) f) →
    ¬ IsSumSqOfLength (m + 1)
      (algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)
        (MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last k) ^ 2))

section Proof

private lemma isSumSq_sq {R : Type*} [Semiring R] (a : R) : IsSumSq (a ^ 2) := by
  simpa [sq] using IsSumSq.sq_add a IsSumSq.zero

private lemma isSumSq_map {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) {a : R}
    (ha : IsSumSq a) : IsSumSq (φ a) := by
  induction ha with
  | zero => simp
  | sq_add b _ ih =>
    rw [map_add, map_mul]
    exact IsSumSq.sq_add (φ b) ih

private lemma motzkin_isSumSq :
    IsSumSq (algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)
      (1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
        MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 -
        3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)) := by
  set x : MvRatFunc (Fin 2) ℝ := algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ) (MvPolynomial.X 0)
  set y : MvRatFunc (Fin 2) ℝ := algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ) (MvPolynomial.X 1)
  have hd_poly : (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) ≠ 0 := by
    intro h
    have hev := congr_arg (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)) h
    simp at hev
  have hd : x ^ 2 + y ^ 2 ≠ 0 := by
    have hinj := IsFractionRing.injective (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)
    intro h
    apply hd_poly
    apply hinj
    simpa [x, y] using h
  set d : MvRatFunc (Fin 2) ℝ := x ^ 2 + y ^ 2
  set a : MvRatFunc (Fin 2) ℝ := x * y * (x ^ 2 + y ^ 2 - 2)
  set b : MvRatFunc (Fin 2) ℝ := x * (y ^ 2 - 1)
  set c : MvRatFunc (Fin 2) ℝ := y * (x ^ 2 - 1)
  have heq :
      algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)
        (1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
          MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 -
          3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2) =
      (x * a / d) ^ 2 + (y * a / d) ^ 2 + (x * b / d) ^ 2 + (y * b / d) ^ 2 +
        (x * c / d) ^ 2 + (y * c / d) ^ 2 := by
    have hmap :
        algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)
          (1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
            MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 -
            3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2) =
        1 + x ^ 2 * y ^ 4 + x ^ 4 * y ^ 2 - 3 * x ^ 2 * y ^ 2 := by
      simp [x, y, map_ofNat]
    rw [hmap]
    have hd' : d ≠ 0 := hd
    field_simp [hd']
    simp only [d, a, b, c]
    ring
  rw [heq]
  exact (((((isSumSq_sq _).add (isSumSq_sq _)).add (isSumSq_sq _)).add
    (isSumSq_sq _)).add (isSumSq_sq _)).add (isSumSq_sq _)

private lemma rename_castSucc_isSumSq (k : ℕ) (f : MvPolynomial (Fin k) ℝ)
    (hf : IsSumSq (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) f)) :
    IsSumSq (algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)
      (MvPolynomial.rename Fin.castSucc f)) := by
  have hinj : Function.Injective (MvPolynomial.rename (R := ℝ) (Fin.castSucc : Fin k → Fin (k + 1))) :=
    MvPolynomial.rename_injective _ (Fin.castSucc_injective k)
  let φ : MvRatFunc (Fin k) ℝ →+* MvRatFunc (Fin (k + 1)) ℝ :=
    IsFractionRing.lift (g := (algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)).comp
      (MvPolynomial.rename (R := ℝ) Fin.castSucc).toRingHom)
      ((IsFractionRing.injective (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)).comp hinj)
  have hcomm : φ (algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) f) =
      algebraMap (MvPolynomial (Fin (k + 1)) ℝ) (MvRatFunc (Fin (k + 1)) ℝ)
        (MvPolynomial.rename Fin.castSucc f) := by
    exact IsFractionRing.lift_algebraMap _ f
  rw [← hcomm]
  exact isSumSq_map φ hf

theorem main : H1 → H2 → type_of% @PfisterPythagorasNumber.pfister_problem.variants.lower_bound := by
  intro h1 h2
  have hex : ∀ r : ℕ, ∃ f : MvPolynomial (Fin (r + 2)) ℝ,
      IsSumSq (algebraMap (MvPolynomial (Fin (r + 2)) ℝ) (MvRatFunc (Fin (r + 2)) ℝ) f) ∧
      ¬ IsSumSqOfLength (r + 3)
        (algebraMap (MvPolynomial (Fin (r + 2)) ℝ) (MvRatFunc (Fin (r + 2)) ℝ) f) := by
    intro r
    induction r with
    | zero =>
      exact ⟨1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
        MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 -
        3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2, motzkin_isSumSq, h1⟩
    | succ r ih =>
      obtain ⟨f, hsq, hnot⟩ := ih
      refine ⟨MvPolynomial.rename Fin.castSucc f + MvPolynomial.X (Fin.last (r + 2)) ^ 2, ?_, ?_⟩
      · rw [map_add, map_pow]
        exact (rename_castSucc_isSumSq (r + 2) f hsq).add (isSumSq_sq _)
      · exact h2 (r + 2) (r + 3) f hnot
  intro n hn p hp
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hn
  obtain ⟨f, hsq, hnot⟩ := hex r
  by_contra hlt
  have hle : p ≤ r + 3 := by omega
  exact hnot ((hp _ hsq).of_le hle)

end Proof

end OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1
