import OMAReductions.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1

-- Reduction Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2.R1 of step Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2
-- Credit: @sobrien032
-- Sources: Gao, Yu and Zhi, arXiv:2610.10248v2, Section 3 and Theorem 2.5;
-- Alekseev, Liu and Thom, arXiv:2609.37761v2, Theorem B; Thom, arXiv:2609.27795, Theorem 1.2.

namespace OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1

open Green100 Filter
open scoped Topology commutatorElement

/-- The algebra of a finite presentation: the stabilizer data of the target step, elements `x`
satisfying the relations (3.1)–(3.5) of Gao–Yu–Zhi and shears `c` satisfying (3.6)–(3.8),
normality, generation by the positive part and the shears, compression of the positive part,
and the group-theoretic fact that normalization by `c 0 1` kills the marked generator. -/
def H1 : Prop :=
  ∃ (R : Finset (List (Fin 74 × Bool))) (Q : Type) (_ : Group Q) (X : Type) (_ : MulAction Q X) (p : X) (h t : Q),
  let S := FreeGroup.mk '' (↑R : Set (List (Fin 74 × Bool)))
  let J := PresentedGroup.mk S (FreeGroup.of (72 : Fin 74))
  h • p = p ∧ h • (t • p) ≠ t • p ∧
  (∀ (G : Type) [Group G] (a b : Q →* G) (j z : G), (∀ q, q • p = p → a q = b q) → j ^ 2 = 1 →
    (∀ q, Commute j (a q) ∧ Commute j (b q)) → Commute j z →
    z * ⁅a h, b t * (a t)⁻¹⁆ * z⁻¹ = ⁅a h, b t * (a t)⁻¹⁆ * j → ∃ f : PresentedGroup S →* G, f J = j) ∧
  ∃ (x : Fin 3 → Fin 3 → Fin 7 → PresentedGroup S) (c : Fin 3 → Fin 3 → PresentedGroup S),
  let E := {g | ∃ i j m, i ≠ j ∧ m.val < 4 ∧ x i j m = g}
  (∀ i m, x i i m = 1 ∧ c i i = 1) ∧ (∀ i j m, x i j m ^ 5 = 1) ∧
  (∀ i j k l m n, i ≠ l → j ≠ k → ⁅x i j m, x k l n⁆ = 1 ∧ ⁅c i j, c k l⁆ = 1) ∧
  (∀ i j k m, i ≠ j → j ≠ k → i ≠ k →
    ⁅x i j m, x j k 0⁆ = x i k m ∧ ⁅x i j 0, x j k m⁆ = x i k m ∧ ⁅c i j, c j k⁆ = c i k) ∧
  (∀ i j k a b m n l, i ≠ j → j ≠ k → i ≠ k → i ≠ b → k ≠ a → ⁅⁅x i j m, x j k n⁆, x a b l⁆ = 1) ∧
  (c 0 1 * (c 1 0)⁻¹ * c 0 1) ^ 4 = 1 ∧
  (∀ a b i j m, c a b * x i j m * (c a b)⁻¹ ∈ Subgroup.closure (Set.range ↿x) ∧
    (c a b)⁻¹ * x i j m * c a b ∈ Subgroup.closure (Set.range ↿x) ∧
    x i j m ∈ Subgroup.closure (E ∪ Set.range ↿c) ∧
    (m.val < 4 → c a b * x i j m * (c a b)⁻¹ ∈ Subgroup.closure E)) ∧
  ∀ (G : Type) [Group G] (f : PresentedGroup S →* G),
    f (c 0 1) ∈ Subgroup.normalizer (Subgroup.centralizer (f '' E) : Set G) → f J = 1

/-- Property (T) input (Ershov–Jaikin-Zapirain for the relations (3.1)–(3.5), Steinberg's
presentation of SL₃(ℤ), extension), transferred to every matrix ultraproduct: lifts of the
positive generators, and of these together with the shears, have spectral gap. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] (x : Fin 3 → Fin 3 → Fin 7 → G) (c : Fin 3 → Fin 3 → G),
  (∀ i m, x i i m = 1 ∧ c i i = 1) → (∀ i j m, x i j m ^ 5 = 1) →
  (∀ i j k l m n, i ≠ l → j ≠ k → ⁅x i j m, x k l n⁆ = 1 ∧ ⁅c i j, c k l⁆ = 1) →
  (∀ i j k m, i ≠ j → j ≠ k → i ≠ k →
    ⁅x i j m, x j k 0⁆ = x i k m ∧ ⁅x i j 0, x j k m⁆ = x i k m ∧ ⁅c i j, c j k⁆ = c i k) →
  (∀ i j k a b m n l, i ≠ j → j ≠ k → i ≠ k → i ≠ b → k ≠ a → ⁅⁅x i j m, x j k n⁆, x a b l⁆ = 1) →
  (c 0 1 * (c 1 0)⁻¹ * c 0 1) ^ 4 = 1 →
  (∀ a b i j m, c a b * x i j m * (c a b)⁻¹ ∈ Subgroup.closure (Set.range ↿x) ∧
    (c a b)⁻¹ * x i j m * c a b ∈ Subgroup.closure (Set.range ↿x) ∧
    x i j m ∈ Subgroup.closure ({g | ∃ i j m, i ≠ j ∧ m.val < 4 ∧ x i j m = g} ∪ Set.range ↿c)) →
  ∃ κ : ℝ, 0 < κ ∧ ∀ (d : ℕ → ℕ), (∀ n, 0 < d n) →
  let U := (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ
  let q := fun (n : ℕ) (y : Matrix (Fin (d n)) (Fin (d n)) ℂ) => (∑ a, ∑ b, ‖y a b‖ ^ 2) / (d n : ℝ)
  let B := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) =>
    ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C
  ∀ (ρ : G →* U ⧸ Subgroup.normalClosure {v : U | Tendsto (fun n => hsDist (v n) 1) (hyperfilter ℕ) (𝓝 0)})
    (w : Fin 3 → Fin 3 → Fin 8 → U), (∀ i j m, (w i j m : U ⧸ _) = ρ (if hm : m.val < 7 then x i j ⟨m.val, hm⟩ else c i j)) →
  ∀ (s : Fin 8 → Prop) [DecidablePred s], s = (· < 4) ∨ s = (fun m => m < 4 ∨ m = 7) →
  ∀ y, B y → ∃ e, B e ∧ (∀ i j m, i ≠ j → s m →
    Tendsto (fun n => q n ((w i j m n : Matrix _ _ ℂ) * e n - e n * (w i j m n : Matrix _ _ ℂ))) (hyperfilter ℕ) (𝓝 0)) ∧
  ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ, κ * q n (y n - e n) ≤ ε + ∑ i, ∑ j, ∑ m,
    if i ≠ j ∧ s m then q n ((w i j m n : Matrix _ _ ℂ) * y n - y n * (w i j m n : Matrix _ _ ℂ)) else 0

/-- Alekseev–Liu–Thom, Theorem B: a spectral gap off the relative commutant of a finite unitary
tuple in a tracial matrix ultraproduct makes that relative commutant internal. -/
def H3 : Prop :=
  ∀ (d : ℕ → ℕ), (∀ n, 0 < d n) → ∀ (ι : Type) [Fintype ι]
    (u : ι → (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) (κ : ℝ), 0 < κ →
  let q := fun (n : ℕ) (y : Matrix (Fin (d n)) (Fin (d n)) ℂ) => (∑ a, ∑ b, ‖y a b‖ ^ 2) / (d n : ℝ)
  let B := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) =>
    ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C
  let K := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) => B y ∧ ∀ a,
    Tendsto (fun n => q n ((u a n : Matrix _ _ ℂ) * y n - y n * (u a n : Matrix _ _ ℂ))) (hyperfilter ℕ) (𝓝 0)
  (∀ y, B y → ∃ e, K e ∧ ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ,
    κ * q n (y n - e n) ≤ ε + ∑ a, q n ((u a n : Matrix _ _ ℂ) * y n - y n * (u a n : Matrix _ _ ℂ))) →
  ∃ A : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ), ∀ y, B y →
    (K y ↔ ∃ a, B a ∧ (∀ n, a n ∈ A n) ∧ Tendsto (fun n => q n (y n - a n)) (hyperfilter ℕ) (𝓝 0))

/-- Thom's normalization theorem in the internal case: if the relative commutants of a tuple
and of its extension are internal and each added unitary conjugates the first commutant into
itself, then it conjugates that commutant onto itself. -/
def H4 : Prop :=
  ∀ (d : ℕ → ℕ), (∀ n, 0 < d n) → ∀ (ι : Type) [Fintype ι] (s : ι → Bool)
    (u : ι → (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ),
  let q := fun (n : ℕ) (y : Matrix (Fin (d n)) (Fin (d n)) ℂ) => (∑ a, ∑ b, ‖y a b‖ ^ 2) / (d n : ℝ)
  let B := fun (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) =>
    ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C
  let K := fun (all : Bool) (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ) => B y ∧ ∀ a, (all || s a) = true →
    Tendsto (fun n => q n ((u a n : Matrix _ _ ℂ) * y n - y n * (u a n : Matrix _ _ ℂ))) (hyperfilter ℕ) (𝓝 0)
  let I := fun (all : Bool) => ∃ A : (n : ℕ) → StarSubalgebra ℂ (Matrix (Fin (d n)) (Fin (d n)) ℂ), ∀ y, B y →
    (K all y ↔ ∃ a, B a ∧ (∀ n, a n ∈ A n) ∧ Tendsto (fun n => q n (y n - a n)) (hyperfilter ℕ) (𝓝 0))
  I false → I true →
  (∀ a, s a = false → ∀ y, K false y → K false (fun n => star (u a n : Matrix _ _ ℂ) * y n * (u a n : Matrix _ _ ℂ))) →
  ∀ a, s a = false → ∀ y, K false y → K false (fun n => (u a n : Matrix _ _ ℂ) * y n * star (u a n : Matrix _ _ ℂ))

/-! ### Matrix norms, the quotient `U ⧸ N`, and asymptotic commutation -/

/-- Column estimate: the squared Frobenius norm of `Y * A` is at most the squared operator
norm of `Y` times the squared Frobenius norm of `A`. -/
theorem ss_mul_left_le {k : ℕ} (Y A : Matrix (Fin k) (Fin k) ℂ) :
    ∑ a, ∑ b, ‖(Y * A) a b‖ ^ 2 ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y‖ ^ 2 * ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  rw [Finset.sum_comm, Finset.sum_comm (f := fun a b => ‖A a b‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have h1 := (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y).le_opNorm
    (WithLp.toLp 2 (fun l => A l b))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h2

/-- Row estimate, obtained from `ss_mul_left_le` by taking adjoints. -/
theorem ss_mul_right_le {k : ℕ} (A Y : Matrix (Fin k) (Fin k) ℂ) :
    ∑ a, ∑ b, ‖(A * Y) a b‖ ^ 2 ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y‖ ^ 2 * ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  have h := ss_mul_left_le (star Y) (star A)
  have e1 : ∑ a, ∑ b, ‖(star Y * star A) a b‖ ^ 2 = ∑ a, ∑ b, ‖(A * Y) a b‖ ^ 2 := by
    rw [← star_mul, Finset.sum_comm]
    simp [Matrix.star_apply]
  have e2 : ∑ a, ∑ b, ‖(star A) a b‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
    rw [Finset.sum_comm]
    simp [Matrix.star_apply]
  have e3 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star Y)‖ =
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y‖ := by
    rw [map_star]
    exact norm_star (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y)
  rw [e1, e2, e3] at h
  exact h

/-- A unitary matrix has operator norm at most one (C*-identity). -/
theorem opnorm_unitary_le {k : ℕ} {U : Matrix (Fin k) (Fin k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) U‖ ≤ 1 := by
  have h1 : star (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) U) *
      Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) U = 1 := by
    rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem hU, map_one]
  have h2 : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) U‖ *
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) U‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, h1]
    exact ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) U)]

/-- The Frobenius norm is invariant under left multiplication by a unitary. -/
theorem ss_unitary_mul {k : ℕ} {U : Matrix (Fin k) (Fin k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (A : Matrix (Fin k) (Fin k) ℂ) :
    ∑ a, ∑ b, ‖(U * A) a b‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  apply le_antisymm
  · calc _ ≤ _ := ss_mul_left_le U A
      _ ≤ 1 ^ 2 * ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
          gcongr
          exact opnorm_unitary_le hU
      _ = _ := by ring
  · calc ∑ a, ∑ b, ‖A a b‖ ^ 2 = ∑ a, ∑ b, ‖(star U * (U * A)) a b‖ ^ 2 := by
          rw [← mul_assoc, Unitary.star_mul_self_of_mem hU, one_mul]
      _ ≤ _ := ss_mul_left_le _ _
      _ ≤ 1 ^ 2 * ∑ a, ∑ b, ‖(U * A) a b‖ ^ 2 := by
          gcongr
          exact opnorm_unitary_le (Unitary.star_mem hU)
      _ = _ := by ring

/-- The Frobenius norm is invariant under right multiplication by a unitary. -/
theorem ss_mul_unitary {k : ℕ} {U : Matrix (Fin k) (Fin k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (A : Matrix (Fin k) (Fin k) ℂ) :
    ∑ a, ∑ b, ‖(A * U) a b‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  apply le_antisymm
  · calc _ ≤ _ := ss_mul_right_le A U
      _ ≤ 1 ^ 2 * ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
          gcongr
          exact opnorm_unitary_le hU
      _ = _ := by ring
  · calc ∑ a, ∑ b, ‖A a b‖ ^ 2 = ∑ a, ∑ b, ‖((A * U) * star U) a b‖ ^ 2 := by
          rw [mul_assoc, Unitary.mul_star_self_of_mem hU, mul_one]
      _ ≤ _ := ss_mul_right_le _ _
      _ ≤ 1 ^ 2 * ∑ a, ∑ b, ‖(A * U) a b‖ ^ 2 := by
          gcongr
          exact opnorm_unitary_le (Unitary.star_mem hU)
      _ = _ := by ring

/-- Squared Frobenius norm of a sum: `|A + B|^2 ≤ 2 |A|^2 + 2 |B|^2`. -/
theorem ss_add_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ∑ a, ∑ b, ‖(A + B) a b‖ ^ 2 ≤
      2 * ∑ a, ∑ b, ‖A a b‖ ^ 2 + 2 * ∑ a, ∑ b, ‖B a b‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Matrix.add_apply]
  have := norm_add_le (A a b) (B a b)
  nlinarith [norm_nonneg (A a b), norm_nonneg (B a b), norm_nonneg (A a b + B a b),
    sq_nonneg (‖A a b‖ - ‖B a b‖)]

/-- The Frobenius norm of `-A` equals that of `A`. -/
theorem ss_neg {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∑ a, ∑ b, ‖(-A) a b‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  simp [Matrix.neg_apply]

/-- Conjugating by a unitary does not increase the operator norm. -/
theorem opnorm_conj_le {k : ℕ} {U : Matrix (Fin k) (Fin k) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin k) ℂ) (Y : Matrix (Fin k) (Fin k) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star U * Y * U)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y‖ := by
  rw [map_mul, map_mul]
  calc _ ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) (star U)‖ *
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y‖ *
        ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) U‖ := by
        refine (norm_mul_le _ _).trans ?_
        gcongr
        exact norm_mul_le _ _
    _ ≤ 1 * ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y‖ * 1 := by
        gcongr
        · exact opnorm_unitary_le (Unitary.star_mem hU)
        · exact opnorm_unitary_le hU
    _ = _ := by ring

/-- The square of `hsDist` is the normalized squared Frobenius norm of the difference. -/
theorem hsDist_sq {k : ℕ} (u v : Matrix.unitaryGroup (Fin k) ℂ) :
    hsDist u v ^ 2 =
      (∑ a, ∑ b, ‖((u : Matrix (Fin k) (Fin k) ℂ) - (v : Matrix (Fin k) (Fin k) ℂ)) a b‖ ^ 2) /
        (k : ℝ) := by
  rw [hsDist, Real.sq_sqrt (by positivity)]
  simp [Matrix.sub_apply]

/-- `hsDist` as the square root of the normalized squared Frobenius norm of the difference. -/
theorem hsDist_eq {k : ℕ} (u v : Matrix.unitaryGroup (Fin k) ℂ) :
    hsDist u v = Real.sqrt
      ((∑ a, ∑ b, ‖((u : Matrix (Fin k) (Fin k) ℂ) - (v : Matrix (Fin k) (Fin k) ℂ)) a b‖ ^ 2) /
        (k : ℝ)) := by
  rw [hsDist]
  simp [Matrix.sub_apply]

/-- Squeeze: a nonnegative sequence bounded by `2 g + 2 h` with `g, h → 0` tends to `0`. -/
theorem tendsto_zero_of_le_two {l : Filter ℕ} {f g h : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hle : ∀ n, f n ≤ 2 * g n + 2 * h n) (hg : Tendsto g l (𝓝 0)) (hh : Tendsto h l (𝓝 0)) :
    Tendsto f l (𝓝 0) := by
  refine squeeze_zero hf hle ?_
  simpa using (hg.const_mul 2).add (hh.const_mul 2)

/-- Normalized form of `ss_add_le`. -/
theorem q_add_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    (∑ a, ∑ b, ‖(A + B) a b‖ ^ 2) / (k : ℝ) ≤
      2 * ((∑ a, ∑ b, ‖A a b‖ ^ 2) / (k : ℝ)) + 2 * ((∑ a, ∑ b, ‖B a b‖ ^ 2) / (k : ℝ)) := by
  rw [mul_div_assoc', mul_div_assoc', ← add_div]
  exact div_le_div_of_nonneg_right (ss_add_le A B) (Nat.cast_nonneg _)

/-- Normalized squared Frobenius norm of a difference. -/
theorem q_sub_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    (∑ a, ∑ b, ‖(A - B) a b‖ ^ 2) / (k : ℝ) ≤
      2 * ((∑ a, ∑ b, ‖A a b‖ ^ 2) / (k : ℝ)) + 2 * ((∑ a, ∑ b, ‖B a b‖ ^ 2) / (k : ℝ)) := by
  rw [sub_eq_add_neg, ← ss_neg B]
  exact q_add_le A (-B)

/-- Normalized form of `ss_mul_left_le` with an operator norm bound `C`. -/
theorem q_mul_left_le {k : ℕ} (Y A : Matrix (Fin k) (Fin k) ℂ) {C : ℝ}
    (hY : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y‖ ≤ C) :
    (∑ a, ∑ b, ‖(Y * A) a b‖ ^ 2) / (k : ℝ) ≤ C ^ 2 * ((∑ a, ∑ b, ‖A a b‖ ^ 2) / (k : ℝ)) := by
  rw [mul_div_assoc']
  refine div_le_div_of_nonneg_right ((ss_mul_left_le Y A).trans ?_) (Nat.cast_nonneg _)
  gcongr

/-- Normalized form of `ss_mul_right_le` with an operator norm bound `C`. -/
theorem q_mul_right_le {k : ℕ} (A Y : Matrix (Fin k) (Fin k) ℂ) {C : ℝ}
    (hY : ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) Y‖ ≤ C) :
    (∑ a, ∑ b, ‖(A * Y) a b‖ ^ 2) / (k : ℝ) ≤ C ^ 2 * ((∑ a, ∑ b, ‖A a b‖ ^ 2) / (k : ℝ)) := by
  rw [mul_div_assoc']
  refine div_le_div_of_nonneg_right ((ss_mul_right_le A Y).trans ?_) (Nat.cast_nonneg _)
  gcongr

/-- Asymptotically negligible matrix sequences are closed under addition. -/
theorem tendsto_q_add {d : ℕ → ℕ} {l : Filter ℕ}
    {X Y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ}
    (hX : Tendsto (fun n => (∑ a, ∑ b, ‖X n a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0))
    (hY : Tendsto (fun n => (∑ a, ∑ b, ‖Y n a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0)) :
    Tendsto (fun n => (∑ a, ∑ b, ‖(X n + Y n) a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0) :=
  tendsto_zero_of_le_two (fun n => by positivity) (fun n => q_add_le _ _) hX hY

/-- Asymptotically negligible matrix sequences are closed under subtraction. -/
theorem tendsto_q_sub {d : ℕ → ℕ} {l : Filter ℕ}
    {X Y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ}
    (hX : Tendsto (fun n => (∑ a, ∑ b, ‖X n a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0))
    (hY : Tendsto (fun n => (∑ a, ∑ b, ‖Y n a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0)) :
    Tendsto (fun n => (∑ a, ∑ b, ‖(X n - Y n) a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0) :=
  tendsto_zero_of_le_two (fun n => by positivity) (fun n => q_sub_le _ _) hX hY

/-- Left multiplication by a bounded sequence keeps a sequence negligible. -/
theorem tendsto_q_mul_left {d : ℕ → ℕ} {l : Filter ℕ}
    {X Y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ} {C : ℝ}
    (hY : ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (Y n)‖ ≤ C)
    (hX : Tendsto (fun n => (∑ a, ∑ b, ‖X n a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0)) :
    Tendsto (fun n => (∑ a, ∑ b, ‖(Y n * X n) a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0) :=
  squeeze_zero (fun n => by positivity) (fun n => q_mul_left_le (Y n) (X n) (hY n))
    (by simpa using hX.const_mul (C ^ 2))

/-- Right multiplication by a bounded sequence keeps a sequence negligible. -/
theorem tendsto_q_mul_right {d : ℕ → ℕ} {l : Filter ℕ}
    {X Y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ} {C : ℝ}
    (hY : ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (Y n)‖ ≤ C)
    (hX : Tendsto (fun n => (∑ a, ∑ b, ‖X n a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0)) :
    Tendsto (fun n => (∑ a, ∑ b, ‖(X n * Y n) a b‖ ^ 2) / (d n : ℝ)) l (𝓝 0) :=
  squeeze_zero (fun n => by positivity) (fun n => q_mul_right_le (X n) (Y n) (hY n))
    (by simpa using hX.const_mul (C ^ 2))

/-- Membership in the normal closure forces the normalized Hilbert–Schmidt distance to the
identity to tend to zero. -/
theorem tendsto_of_mem_normalClosure {d : ℕ → ℕ} {v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ}
    (hv : v ∈ Subgroup.normalClosure {v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ |
      Tendsto (fun n => hsDist (v n) 1) (hyperfilter ℕ) (𝓝 0)}) :
    Tendsto (fun n => (∑ a, ∑ b, ‖((v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1) a b‖ ^ 2) /
      (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
  have hv' : v ∈ Subgroup.closure (Group.conjugatesOfSet
      {v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ |
        Tendsto (fun n => hsDist (v n) 1) (hyperfilter ℕ) (𝓝 0)}) := hv
  clear hv
  induction hv' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    have ha' := (ha : Tendsto (fun n => hsDist (a n) 1) (hyperfilter ℕ) (𝓝 0)).pow 2
    simp only [hsDist_sq, Matrix.UnitaryGroup.one_val] at ha'
    rw [zero_pow two_ne_zero] at ha'
    refine ha'.congr (fun n => ?_)
    have e : (((c * a * c⁻¹) n : Matrix.unitaryGroup (Fin (d n)) ℂ) :
        Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1 =
        (c n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * ((a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1) *
          star (c n : Matrix (Fin (d n)) (Fin (d n)) ℂ) := by
      change (c n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (a n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
        star (c n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1 = _
      rw [mul_sub, sub_mul, mul_one, Unitary.mul_star_self_of_mem (c n).2]
    rw [e, ss_mul_unitary (Unitary.star_mem (c n).2), ss_unitary_mul (c n).2]
  | one => simp
  | mul x y _ _ hx hy =>
    have e : ∀ n, (((x * y) n : Matrix.unitaryGroup (Fin (d n)) ℂ) :
        Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1 =
        (x n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * ((y n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1) +
          ((x n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1) := by
      intro n
      change (x n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (y n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1 = _
      noncomm_ring
    simp only [e]
    refine tendsto_q_add ?_ hx
    refine hy.congr (fun n => ?_)
    rw [ss_unitary_mul (x n).2]
  | inv x _ hx =>
    have e : ∀ n, ((x⁻¹ n : Matrix.unitaryGroup (Fin (d n)) ℂ) :
        Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1 =
        -(star (x n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
          ((x n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1)) := by
      intro n
      change star (x n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1 = _
      rw [mul_sub, Unitary.star_mul_self_of_mem (x n).2, mul_one, neg_sub]
    simp only [e]
    refine hx.congr (fun n => ?_)
    rw [ss_neg, ss_unitary_mul (Unitary.star_mem (x n).2)]

/-- Two unitary sequences have the same image in `U ⧸ N` exactly when their normalized
Hilbert–Schmidt distance tends to zero along the ultrafilter. -/
theorem mk_eq_iff {d : ℕ → ℕ} (v v' : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) :
    (QuotientGroup.mk v : ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸
      Subgroup.normalClosure {v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ |
        Tendsto (fun n => hsDist (v n) 1) (hyperfilter ℕ) (𝓝 0)}) = QuotientGroup.mk v' ↔
    Tendsto (fun n => (∑ a, ∑ b, ‖((v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
      (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
  rw [QuotientGroup.eq]
  have e : ∀ n, (((v⁻¹ * v') n : Matrix.unitaryGroup (Fin (d n)) ℂ) :
      Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1 =
      star (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
        ((v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := by
    intro n
    change star (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ)
      - 1 = _
    rw [mul_sub, Unitary.star_mul_self_of_mem (v n).2]
  have e2 : ∀ n, (∑ a, ∑ b, ‖((((v⁻¹ * v') n : Matrix.unitaryGroup (Fin (d n)) ℂ) :
      Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1) a b‖ ^ 2) =
      ∑ a, ∑ b, ‖((v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
        (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2 := by
    intro n
    rw [e n, ss_unitary_mul (Unitary.star_mem (v n).2)]
  constructor
  · intro h
    have := tendsto_of_mem_normalClosure h
    simp only [e2] at this
    exact this
  · intro h
    apply Subgroup.subset_normalClosure
    show Tendsto (fun n => hsDist ((v⁻¹ * v') n) 1) (hyperfilter ℕ) (𝓝 0)
    simp only [hsDist_eq, Matrix.UnitaryGroup.one_val, e2]
    simpa using h.sqrt

/-- Asymptotic commutation with a bounded sequence `y` does not depend on the lift. -/
theorem tendsto_comm_of_mk_eq {d : ℕ → ℕ}
    {N : Subgroup ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ)}
    (hN : ∀ v v' : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ,
      (QuotientGroup.mk v : ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸ N) = QuotientGroup.mk v' →
      Tendsto (fun n => (∑ a, ∑ b, ‖((v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
        (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0))
    {y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ} {C : ℝ}
    (hy : ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C)
    {v v' : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ}
    (h : (QuotientGroup.mk v : ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸ N) = QuotientGroup.mk v')
    (hv : Tendsto (fun n => (∑ a, ∑ b, ‖((v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
      y n * (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0)) :
    Tendsto (fun n => (∑ a, ∑ b, ‖((v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
      y n * (v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
  have hD := hN v v' h
  have e : ∀ n, (v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
      y n * (v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) =
      ((v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n - y n * (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) +
        (((v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) * y n -
          y n * ((v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ))) := by
    intro n
    noncomm_ring
  simp only [e]
  exact tendsto_q_add hv (tendsto_q_sub (tendsto_q_mul_right hy hD) (tendsto_q_mul_left hy hD))

/-- Commutator identity for the inverse of a unitary. -/
theorem star_comm_eq {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin k) ℂ)
    (Y : Matrix (Fin k) (Fin k) ℂ) :
    star A * Y - Y * star A = -(star A * (A * Y - Y * A) * star A) := by
  have h1 := Unitary.star_mul_self_of_mem hA
  have h2 := Unitary.mul_star_self_of_mem hA
  calc star A * Y - Y * star A = star A * Y * (A * star A) - (star A * A) * Y * star A := by
        rw [h1, h2, mul_one, one_mul]
    _ = -(star A * (A * Y - Y * A) * star A) := by noncomm_ring

/-- For a bounded sequence `y`, the elements of `U ⧸ N` all of whose lifts asymptotically
commute with `y` form a subgroup: closure induction. -/
theorem tendsto_comm_closure {d : ℕ → ℕ}
    {N : Subgroup ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ)} [N.Normal]
    (hN : ∀ v v' : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ,
      (QuotientGroup.mk v : ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸ N) = QuotientGroup.mk v' →
      Tendsto (fun n => (∑ a, ∑ b, ‖((v' n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
        (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0))
    {y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ} {C : ℝ}
    (hy : ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C)
    (s : Set (((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸ N))
    (hs : ∀ g ∈ s, ∀ v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ,
      (QuotientGroup.mk v : ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸ N) = g →
      Tendsto (fun n => (∑ a, ∑ b, ‖((v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
        y n * (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0))
    {g : ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸ N} (hg : g ∈ Subgroup.closure s)
    (v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ)
    (hv : (QuotientGroup.mk v : ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸ N) = g) :
    Tendsto (fun n => (∑ a, ∑ b, ‖((v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
      y n * (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) / (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
  induction hg using Subgroup.closure_induction generalizing v with
  | mem g hg => exact hs g hg v hv
  | one =>
    have h1 : Tendsto (fun n => (∑ a, ∑ b, ‖((((1 : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) n :
        Matrix.unitaryGroup (Fin (d n)) ℂ) : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
        y n * (((1 : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) n :
        Matrix.unitaryGroup (Fin (d n)) ℂ) : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) /
          (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
      simp
    exact tendsto_comm_of_mk_eq hN hy (by rw [hv, QuotientGroup.mk_one]) h1
  | mul g1 g2 _ _ ih1 ih2 =>
    obtain ⟨v1, rfl⟩ := QuotientGroup.mk_surjective g1
    obtain ⟨v2, rfl⟩ := QuotientGroup.mk_surjective g2
    have h1 := ih1 v1 rfl
    have h2 := ih2 v2 rfl
    have e : ∀ n, ((((v1 * v2) n : Matrix.unitaryGroup (Fin (d n)) ℂ) :
        Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n - y n * (((v1 * v2) n :
          Matrix.unitaryGroup (Fin (d n)) ℂ) : Matrix (Fin (d n)) (Fin (d n)) ℂ)) =
        (v1 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * ((v2 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
          y n * (v2 n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) +
        ((v1 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n - y n * (v1 n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) *
          (v2 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) := by
      intro n
      change (v1 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (v2 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
        y n * ((v1 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (v2 n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) = _
      noncomm_ring
    have h12 : Tendsto (fun n => (∑ a, ∑ b, ‖((((v1 * v2) n : Matrix.unitaryGroup (Fin (d n)) ℂ) :
        Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n - y n * (((v1 * v2) n :
          Matrix.unitaryGroup (Fin (d n)) ℂ) : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) /
          (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
      simp only [e]
      refine tendsto_q_add (h2.congr fun n => ?_) (h1.congr fun n => ?_)
      · rw [ss_unitary_mul (v1 n).2]
      · rw [ss_mul_unitary (v2 n).2]
    exact tendsto_comm_of_mk_eq hN hy (by rw [hv, QuotientGroup.mk_mul]) h12
  | inv g _ ih =>
    obtain ⟨v1, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := ih v1 rfl
    have e : ∀ n, (((v1⁻¹ n : Matrix.unitaryGroup (Fin (d n)) ℂ) :
        Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n - y n * ((v1⁻¹ n :
          Matrix.unitaryGroup (Fin (d n)) ℂ) : Matrix (Fin (d n)) (Fin (d n)) ℂ)) =
        -(star (v1 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * ((v1 n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
          y n - y n * (v1 n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) *
            star (v1 n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) := by
      intro n
      exact star_comm_eq (v1 n).2 (y n)
    have h1' : Tendsto (fun n => (∑ a, ∑ b, ‖(((v1⁻¹ n : Matrix.unitaryGroup (Fin (d n)) ℂ) :
        Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n - y n * ((v1⁻¹ n :
          Matrix.unitaryGroup (Fin (d n)) ℂ) : Matrix (Fin (d n)) (Fin (d n)) ℂ)) a b‖ ^ 2) /
          (d n : ℝ)) (hyperfilter ℕ) (𝓝 0) := by
      simp only [e]
      refine h1.congr fun n => ?_
      rw [ss_neg, ss_mul_unitary (Unitary.star_mem (v1 n).2),
        ss_unitary_mul (Unitary.star_mem (v1 n).2)]
    exact tendsto_comm_of_mk_eq hN hy (by rw [hv, QuotientGroup.mk_inv]) h1'

/-- A triple sum restricted by an `if` equals the sum over the corresponding subtype. -/
theorem sum_ite_subtype (s : Fin 8 → Prop) [DecidablePred s] (f : Fin 3 → Fin 3 → Fin 8 → ℝ) :
    ∑ i, ∑ j, ∑ m, (if i ≠ j ∧ s m then f i j m else 0) =
      ∑ a : {a : Fin 3 × Fin 3 × Fin 8 // a.1 ≠ a.2.1 ∧ s a.2.2}, f a.1.1 a.1.2.1 a.1.2.2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter
    (fun a : Fin 3 × Fin 3 × Fin 8 => a.1 ≠ a.2.1 ∧ s a.2.2)) (by simp)
    (fun a => f a.1 a.2.1 a.2.2), Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

/-- The Frobenius norm of `A - B` equals that of `B - A`. -/
theorem ss_sub_comm {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    ∑ a, ∑ b, ‖(A - B) a b‖ ^ 2 = ∑ a, ∑ b, ‖(B - A) a b‖ ^ 2 := by
  rw [← neg_sub, ss_neg]

/-- Commutator of `V` with a unitary conjugate `W⋆ Y W`, rewritten as a conjugate of the
commutator of `W V W⋆` with `Y`. -/
theorem conj_comm_eq {k : ℕ} {W : Matrix (Fin k) (Fin k) ℂ} (hW : W ∈ Matrix.unitaryGroup (Fin k) ℂ)
    (V Y : Matrix (Fin k) (Fin k) ℂ) :
    V * (star W * Y * W) - star W * Y * W * V =
      star W * ((W * V * star W) * Y - Y * (W * V * star W)) * W := by
  have h1 := Unitary.star_mul_self_of_mem hW
  calc V * (star W * Y * W) - star W * Y * W * V =
        (star W * W) * V * (star W * Y * W) - star W * Y * W * V * (star W * W) := by
        rw [h1, one_mul, mul_one]
    _ = _ := by noncomm_ring

/-- If the conjugates of `V` and `X` by `W` commute, then `V` and `X` commute. -/
theorem comm_of_conj_comm {G : Type*} [Group G] {W V X : G}
    (h : W * V * W⁻¹ * (W * X * W⁻¹) = W * X * W⁻¹ * (W * V * W⁻¹)) : X * V = V * X := by
  have h1 : W * (V * X) * W⁻¹ = W * (X * V) * W⁻¹ := by
    simpa only [mul_assoc, inv_mul_cancel_left] using h
  exact (mul_left_cancel (mul_right_cancel h1)).symm

/-- The reduction: H1 supplies the presentation and its group theory, H2 the spectral gaps,
H3 internality of the two relative commutants and H4 the normalization step. -/
theorem main : H1 → H2 → H3 → H4 → OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1.H2 := by
  intro hH1 hH2 hH3 hH4
  obtain ⟨R, Q, _, X, _, p, h, t, hfix, hmove, hlift, x, c, hdiag, hpow, hcomm, hst, hthree, hcox,
    hconj, hkill⟩ := hH1
  refine ⟨R, Q, _, X, _, p, h, t, hfix, hmove, ?_, ?_⟩
  · intro G _ a b j z h1 h2 h3 h4 h5
    exact hlift G a b j z h1 h2 h3 h4 h5
  intro d hd
  dsimp only
  intro ρ
  apply hkill _ ρ
  choose w hw using fun (i j : Fin 3) (m : Fin 8) =>
    QuotientGroup.mk_surjective (ρ (if hm : m.val < 7 then x i j ⟨m.val, hm⟩ else c i j))
  have hwx : ∀ (i j : Fin 3) (m : Fin 8) (hm : m.val < 7),
      (QuotientGroup.mk (w i j m) : _) = ρ (x i j ⟨m.val, hm⟩) := by
    intro i j m hm
    rw [hw, dif_pos hm]
  have hwE : ∀ (i j : Fin 3) (m : Fin 7),
      (QuotientGroup.mk (w i j ⟨m.val, by omega⟩) : _) = ρ (x i j m) := fun i j m =>
    hwx i j _ m.isLt
  have hwc : ∀ i j : Fin 3, (QuotientGroup.mk (w i j 7) : _) = ρ (c i j) := by
    intro i j
    rw [hw, dif_neg (by decide)]
  have hN := fun v v' => (mk_eq_iff (d := d) v v').1
  obtain ⟨κ, hκ, hgap⟩ := hH2 _ x c hdiag hpow hcomm hst hthree hcox
    (fun a b i j m => ⟨(hconj a b i j m).1, (hconj a b i j m).2.1, (hconj a b i j m).2.2.1⟩)
  have gap := hgap d hd ρ w hw
  obtain ⟨A1, hA1⟩ := hH3 d hd {a : Fin 3 × Fin 3 × Fin 8 // a.1 ≠ a.2.1 ∧ a.2.2 < 4}
    (fun a => w a.1.1 a.1.2.1 a.1.2.2) κ hκ (by
      intro y hy
      obtain ⟨e, he, hce, hineq⟩ := gap (· < 4) (Or.inl rfl) y hy
      refine ⟨e, ⟨he, fun a => hce _ _ _ a.2.1 a.2.2⟩, fun ε hε => ?_⟩
      filter_upwards [hineq ε hε] with n hn
      rw [sum_ite_subtype] at hn
      exact hn)
  obtain ⟨A2, hA2⟩ := hH3 d hd {a : Fin 3 × Fin 3 × Fin 8 // a.1 ≠ a.2.1 ∧ (a.2.2 < 4 ∨ a.2.2 = 7)}
    (fun a => w a.1.1 a.1.2.1 a.1.2.2) κ hκ (by
      intro y hy
      obtain ⟨e, he, hce, hineq⟩ := gap (fun m => m < 4 ∨ m = 7) (Or.inr rfl) y hy
      refine ⟨e, ⟨he, fun a => hce _ _ _ a.2.1 a.2.2⟩, fun ε hε => ?_⟩
      filter_upwards [hineq ε hε] with n hn
      rw [sum_ite_subtype] at hn
      exact hn)
  have key := hH4 d hd {a : Fin 3 × Fin 3 × Fin 8 // a.1 ≠ a.2.1 ∧ (a.2.2 < 4 ∨ a.2.2 = 7)}
    (fun a => decide (a.1.2.2 < 4)) (fun a => w a.1.1 a.1.2.1 a.1.2.2) ?I0 ?I1 ?incl
  case I0 =>
    refine ⟨A1, fun y hy => Iff.trans ?_ (hA1 y hy)⟩
    beta_reduce
    constructor
    · rintro ⟨hb, hK⟩
      exact ⟨hb, fun a => hK ⟨a.1, a.2.1, Or.inl a.2.2⟩ (by simpa using a.2.2)⟩
    · rintro ⟨hb, hK⟩
      exact ⟨hb, fun a ha => hK ⟨a.1, a.2.1, by simpa using ha⟩⟩
  case I1 =>
    refine ⟨A2, fun y hy => Iff.trans ?_ (hA2 y hy)⟩
    beta_reduce
    constructor
    · rintro ⟨hb, hK⟩
      exact ⟨hb, fun a => hK a rfl⟩
    · rintro ⟨hb, hK⟩
      exact ⟨hb, fun a _ => hK a⟩
  case incl =>
    rintro ⟨⟨i, j, m⟩, hij, hm⟩ ha y ⟨⟨C, hC⟩, hy⟩
    have hm7 : m = 7 := hm.resolve_left (by simpa using ha)
    subst hm7
    refine ⟨⟨C, fun n => (opnorm_conj_le (w i j 7 n).2 (y n)).trans (hC n)⟩, ?_⟩
    rintro ⟨⟨i', j', m'⟩, hij', hm'⟩ hb
    have hm4 : m' < 4 := by simpa using hb
    have hm4' : m'.val < 4 := hm4
    have h7 : m'.val < 7 := by omega
    have hcl := tendsto_comm_closure hN hC
      (ρ '' {g | ∃ i j m, i ≠ j ∧ (m : Fin 7).val < 4 ∧ x i j m = g}) ?base
      (g := QuotientGroup.mk (w i j 7 * w i' j' m' * (w i j 7)⁻¹)) ?mem
      (w i j 7 * w i' j' m' * (w i j 7)⁻¹) rfl
    case base =>
      rintro g ⟨e, ⟨i'', j'', m'', hij'', hm'', rfl⟩, rfl⟩ v hv
      have h8 : m''.val < 8 := by omega
      have hlt : (⟨m''.val, h8⟩ : Fin 8) < 4 := hm''
      have := hy ⟨(i'', j'', ⟨m''.val, h8⟩), hij'', Or.inl hlt⟩ (by simpa using hlt)
      exact tendsto_comm_of_mk_eq hN hC ((hwE i'' j'' m'').trans hv.symm) this
    case mem =>
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hwc, hwx i' j' m' h7,
        ← map_inv, ← map_mul, ← map_mul, ← MonoidHom.map_closure]
      exact Subgroup.mem_map_of_mem ρ ((hconj i j i' j' ⟨m'.val, h7⟩).2.2.2 hm4')
    refine hcl.congr fun n => ?_
    beta_reduce
    rw [conj_comm_eq (w i j 7 n).2, ss_mul_unitary (w i j 7 n).2,
      ss_unitary_mul (Unitary.star_mem (w i j 7 n).2)]
    rfl
  rw [Subgroup.mem_normalizer_iff]
  intro z
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective z
  rw [← hwc 0 1, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  constructor
  · intro hz
    have hKv := key ⟨(0, 1, 7), by decide, Or.inr rfl⟩ rfl
      (fun n => (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ))
      ⟨⟨1, fun n => opnorm_unitary_le (v n).2⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      rintro g ⟨e, ⟨i, j, m, hij, hm, rfl⟩, rfl⟩
      have h8 : m.val < 8 := by omega
      have hlt : (⟨m.val, h8⟩ : Fin 8) < 4 := hm
      rw [← hwE i j m, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      apply (mk_eq_iff _ _).2
      have h2 := hKv.2 ⟨(i, j, ⟨m.val, h8⟩), hij, Or.inl hlt⟩ (by simpa using hlt)
      refine h2.congr fun n => ?_
      beta_reduce
      rw [ss_sub_comm]
      rfl
    · rintro ⟨⟨i, j, m⟩, hij, hm⟩ ha
      have hm4 : m < 4 := by simpa using ha
      have hm4' : m.val < 4 := hm4
      have h7 : m.val < 7 := by omega
      have hc := Subgroup.mem_centralizer_iff.1 hz (ρ (x i j ⟨m.val, h7⟩))
        ⟨_, ⟨i, j, ⟨m.val, h7⟩, hij, hm4', rfl⟩, rfl⟩
      rw [← hwx i j m h7, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hc
      refine ((mk_eq_iff _ _).1 hc).congr fun n => ?_
      beta_reduce
      rw [ss_sub_comm]
      rfl
  · intro hz
    rw [Subgroup.mem_centralizer_iff]
    rintro g ⟨e, ⟨i, j, m, hij, hm, rfl⟩, rfl⟩
    have hc : (QuotientGroup.mk (w 0 1 7) : _) * ρ (x i j m) * (QuotientGroup.mk (w 0 1 7))⁻¹ ∈
        Subgroup.closure (ρ '' {g | ∃ i j m, i ≠ j ∧ (m : Fin 7).val < 4 ∧ x i j m = g}) := by
      rw [hwc, ← map_inv, ← map_mul, ← map_mul, ← MonoidHom.map_closure]
      exact Subgroup.mem_map_of_mem ρ ((hconj 0 1 i j m).2.2.2 hm)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hz
    exact comm_of_conj_comm (Subgroup.mem_centralizer_iff.1
      (Subgroup.closure_le_centralizer_centralizer _ hc) _ hz)

end OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1
