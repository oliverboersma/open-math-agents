import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1
import Mathlib

/-! Crossed-kernel product symmetrization and sup-rescaling reduction, adapted
under Apache-2.0 from openai/math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Sidorenko/Symmetrization.lean. -/

namespace OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1

def H1 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let uMean := fun {A : Type} [Fintype A] (f : A → ℝ) => (∑ a, f a) / (Fintype.card A : ℝ)
  ∃ (M : {q : ℕ // q.Prime ∧ q ≠ 2} → Type) (_ : ∀ q, AddCommGroup (M q)) (_ : ∀ q, Fintype (M q))
    (R : ∀ q, ℤ → M q → ℝ),
    (∀ q ξ z, 0 ≤ R q ξ z) ∧ (∀ q ξ, (ξ = 1 ∨ ξ = -1) → uMean (R q ξ) = 1) ∧
    (∀ q ξ z, R q ξ (-z) = R q ξ z) ∧
    ∀ (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ), (∀ j k, ξ j k = 1 ∨ ξ j k = -1) →
      Filter.Tendsto (fun q => uMean (fun xy : (Fin 13 → M q) × (Fin 22 → M q) =>
          ∏ j, ∏ k ∈ T j, R q (ξ j k) (xy.1 (t j k) - xy.2 j)))
        (Filter.comap Subtype.val Filter.atTop)
        (nhds (uMean (fun η : Fin 33 → Bool => ∏ j, ∏ k,
          if sL k ∈ T j ∧ sR k ∈ T j then
            1 + (if η (p j k) then (1 : ℝ) else -1) * (ξ j (sL k) : ℝ) * (ξ j (sR k) : ℝ) else 1)))

def H2 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let uMean := fun {A : Type} [Fintype A] (f : A → ℝ) => (∑ a, f a) / (Fintype.card A : ℝ)
  let bMom := fun {A B : Type} [Fintype A] [Fintype B] (u : A → ℝ) (v : B → ℝ) (U : A → B → ℝ) =>
    ∑ x : Fin 13 → A, (∏ i, u (x i)) * ∑ y : Fin 22 → B, (∏ j, v (y j)) * ∏ k : Fin 22 × Fin 3, U (x (t k.1 k.2)) (y k.1)
  ∀ (M : {q : ℕ // q.Prime ∧ q ≠ 2} → Type) [∀ q, AddCommGroup (M q)] [∀ q, Fintype (M q)]
    (R : ∀ q, ℤ → M q → ℝ),
    (∀ q ξ z, 0 ≤ R q ξ z) → (∀ q ξ, (ξ = 1 ∨ ξ = -1) → uMean (R q ξ) = 1) →
    (∀ q ξ z, R q ξ (-z) = R q ξ z) →
    (∀ (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ), (∀ j k, ξ j k = 1 ∨ ξ j k = -1) →
      Filter.Tendsto (fun q => uMean (fun xy : (Fin 13 → M q) × (Fin 22 → M q) =>
          ∏ j, ∏ k ∈ T j, R q (ξ j k) (xy.1 (t j k) - xy.2 j)))
        (Filter.comap Subtype.val Filter.atTop)
        (nhds (uMean (fun η : Fin 33 → Bool => ∏ j, ∏ k,
          if sL k ∈ T j ∧ sR k ∈ T j then
            1 + (if η (p j k) then (1 : ℝ) else -1) * (ξ j (sL k) : ℝ) * (ξ j (sR k) : ℝ) else 1)))) →
    ∃ (X Y : Type) (_ : Fintype X) (_ : Fintype Y) (_ : Nonempty X) (_ : Nonempty Y)
      (wX : X → ℝ) (wY : Y → ℝ) (W : X → Y → ℝ),
      (∀ x, 0 ≤ wX x) ∧ ∑ x, wX x = 1 ∧ (∀ y, 0 ≤ wY y) ∧ ∑ y, wY y = 1 ∧
      (∀ x y, 0 ≤ W x y) ∧ (∑ x, wX x * ∑ y, wY y * W x y) = 1 ∧
      bMom wX wY W * bMom wY wX (fun y x => W x y) < 1

lemma four_sums_factor {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (p : A → ℝ) (q : B → ℝ) (r : C → ℝ) (s : D → ℝ) (f : A → D → ℝ) (g : C → B → ℝ) :
    (∑ a, p a * ∑ b, q b * ∑ c, r c * ∑ d, s d * (f a d * g c b)) =
      (∑ a, p a * ∑ d, s d * f a d) * (∑ c, r c * ∑ b, q b * g c b) := by
  have h1 : ∀ a b c, (∑ d, s d * (f a d * g c b)) = (∑ d, s d * f a d) * g c b := by
    intro a b c
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  simp_rw [h1]
  have h2 : ∀ a b, (∑ c, r c * ((∑ d, s d * f a d) * g c b)) =
      (∑ d, s d * f a d) * ∑ c, r c * g c b := by
    intro a b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  simp_rw [h2]
  have h3 : ∀ a, (∑ b, q b * ((∑ d, s d * f a d) * ∑ c, r c * g c b)) =
      (∑ d, s d * f a d) * ∑ b, q b * ∑ c, r c * g c b := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [h3]
  have h4 : (∑ a, p a * ((∑ d, s d * f a d) * ∑ b, q b * ∑ c, r c * g c b)) =
      (∑ a, p a * ∑ d, s d * f a d) * ∑ b, q b * ∑ c, r c * g c b := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h4]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma sum_prod_weight {X Y : Type*} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ) (hwX : ∑ x, wX x = 1) (hwY : ∑ y, wY y = 1) :
    ∑ z : X × Y, wX z.1 * wY z.2 = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hwY, mul_one, hwX]

lemma crossed_mean {X Y : Type*} [Fintype X] [Fintype Y]
    (wX : X → ℝ) (wY : Y → ℝ) (W : X → Y → ℝ) :
    (∑ z1 : X × Y, (wX z1.1 * wY z1.2) *
      ∑ z2 : X × Y, (wX z2.1 * wY z2.2) * (W z1.1 z2.2 * W z2.1 z1.2)) =
      (∑ x, wX x * ∑ y, wY y * W x y) ^ 2 := by
  simp_rw [Fintype.sum_prod_type]
  have h : (∑ a : X, ∑ b : Y, (wX a * wY b) *
      ∑ c : X, ∑ d : Y, (wX c * wY d) * (W a d * W c b)) =
      ∑ a : X, wX a * ∑ b : Y, wY b * ∑ c : X, wX c * ∑ d : Y, wY d * (W a d * W c b) := by
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [h, four_sums_factor, sq]

lemma crossed_moment {X Y : Type*} [Fintype X] [Fintype Y]
    (t : Fin 22 → Fin 3 → Fin 13) (wX : X → ℝ) (wY : Y → ℝ) (W : X → Y → ℝ) :
    (∑ x : Fin 13 → X × Y, (∏ i, wX (x i).1 * wY (x i).2) *
      ∑ y : Fin 22 → X × Y, (∏ j, wX (y j).1 * wY (y j).2) *
        ∏ k : Fin 22 × Fin 3, (W (x (t k.1 k.2)).1 (y k.1).2 * W (y k.1).1 (x (t k.1 k.2)).2)) =
      (∑ x : Fin 13 → X, (∏ i, wX (x i)) *
        ∑ y : Fin 22 → Y, (∏ j, wY (y j)) * ∏ k : Fin 22 × Fin 3, W (x (t k.1 k.2)) (y k.1)) *
      (∑ y : Fin 13 → Y, (∏ i, wY (y i)) *
        ∑ x : Fin 22 → X, (∏ j, wX (x j)) * ∏ k : Fin 22 × Fin 3, W (x k.1) (y (t k.1 k.2))) := by
  rw [Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin 13) (fun _ => X) (fun _ => Y)) _
    (fun x : (Fin 13 → X) × (Fin 13 → Y) =>
      ((∏ i, wX (x.1 i)) * (∏ i, wY (x.2 i))) *
        ∑ y : (Fin 22 → X) × (Fin 22 → Y),
          ((∏ j, wX (y.1 j)) * (∏ j, wY (y.2 j))) *
            ((∏ k : Fin 22 × Fin 3, W (x.1 (t k.1 k.2)) (y.2 k.1)) *
             (∏ k : Fin 22 × Fin 3, W (y.1 k.1) (x.2 (t k.1 k.2)))))]
  · simp_rw [Fintype.sum_prod_type]
    have h : (∑ x1 : Fin 13 → X, ∑ x2 : Fin 13 → Y,
        ((∏ i, wX (x1 i)) * (∏ i, wY (x2 i))) *
          ∑ y1 : Fin 22 → X, ∑ y2 : Fin 22 → Y,
            ((∏ j, wX (y1 j)) * (∏ j, wY (y2 j))) *
              ((∏ k : Fin 22 × Fin 3, W (x1 (t k.1 k.2)) (y2 k.1)) *
               (∏ k : Fin 22 × Fin 3, W (y1 k.1) (x2 (t k.1 k.2))))) =
        ∑ x1 : Fin 13 → X, (∏ i, wX (x1 i)) *
          ∑ x2 : Fin 13 → Y, (∏ i, wY (x2 i)) *
            ∑ y1 : Fin 22 → X, (∏ j, wX (y1 j)) *
              ∑ y2 : Fin 22 → Y, (∏ j, wY (y2 j)) *
                ((∏ k : Fin 22 × Fin 3, W (x1 (t k.1 k.2)) (y2 k.1)) *
                 (∏ k : Fin 22 × Fin 3, W (y1 k.1) (x2 (t k.1 k.2)))) := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x2 _ =>
        Finset.sum_congr rfl fun y1 _ => Finset.sum_congr rfl fun y2 _ => ?_
      ring
    rw [h, four_sums_factor]
    congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  · intro x
    simp only [Finset.prod_mul_distrib]
    congr 1
    exact Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin 22) (fun _ => X) (fun _ => Y)) _
      (fun y : (Fin 22 → X) × (Fin 22 → Y) =>
        ((∏ j, wX (y.1 j)) * (∏ j, wY (y.2 j))) *
          ((∏ k : Fin 22 × Fin 3, W (x (t k.1 k.2)).1 (y.2 k.1)) *
           (∏ k : Fin 22 × Fin 3, W (y.1 k.1) (x (t k.1 k.2)).2)))
      fun _ => rfl

lemma mean_div {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (V : Ω → Ω → ℝ) (L : ℝ) :
    (∑ x, w x * ∑ y, w y * (V x y / L)) = (∑ x, w x * ∑ y, w y * V x y) / L := by
  simp_rw [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  simp_rw [← mul_assoc, ← Finset.sum_mul]

lemma moment_div {Ω : Type*} [Fintype Ω] (t : Fin 22 → Fin 3 → Fin 13)
    (w : Ω → ℝ) (V : Ω → Ω → ℝ) (L : ℝ) :
    (∑ x : Fin 13 → Ω, (∏ i, w (x i)) *
      ∑ y : Fin 22 → Ω, (∏ j, w (y j)) * ∏ k : Fin 22 × Fin 3, (V (x (t k.1 k.2)) (y k.1) / L)) =
    (∑ x : Fin 13 → Ω, (∏ i, w (x i)) *
      ∑ y : Fin 22 → Ω, (∏ j, w (y j)) * ∏ k : Fin 22 × Fin 3, V (x (t k.1 k.2)) (y k.1)) / L ^ 66 := by
  have hc : Fintype.card (Fin 22 × Fin 3) = 66 := by decide
  simp_rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, hc,
    div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
  simp_rw [← mul_assoc, ← Finset.sum_mul]

theorem main : H1 → H2 → OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1.H1 := by
  intro h1 h2
  obtain ⟨M, hAdd, hFin, R, hRnonneg, hRsum, hRsymm, hRtend⟩ := h1
  obtain ⟨X, Y, fiX, fiY, neX, neY, wX, wY, W, hwX0, hwX1, hwY0, hwY1, hW0, hWmean, hWgap⟩ :=
    @h2 M hAdd hFin R hRnonneg hRsum hRsymm hRtend
  letI := fiX
  letI := fiY
  letI := neX
  letI := neY
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]
  let Ω := X × Y
  let w : Ω → ℝ := fun z => wX z.1 * wY z.2
  let V : Ω → Ω → ℝ := fun z1 z2 => W z1.1 z2.2 * W z2.1 z1.2
  let L : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun zz : Ω × Ω => V zz.1 zz.2)
  let K : Ω → Ω → ℝ := fun z1 z2 => V z1 z2 / L
  have hw0 : ∀ z, 0 ≤ w z := fun z => mul_nonneg (hwX0 z.1) (hwY0 z.2)
  have hw1 : ∑ z, w z = 1 := sum_prod_weight wX wY hwX1 hwY1
  have hV0 : ∀ z1 z2, 0 ≤ V z1 z2 := fun z1 z2 => mul_nonneg (hW0 _ _) (hW0 _ _)
  have hL : ∀ z1 z2, V z1 z2 ≤ L := fun z1 z2 =>
    Finset.le_sup' (fun zz : Ω × Ω => V zz.1 zz.2) (Finset.mem_univ (z1, z2))
  have hVmean : ∑ x, w x * ∑ y, w y * V x y = 1 := by
    rw [crossed_mean, hWmean, one_pow]
  have hone : 1 ≤ L := by
    calc
      (1 : ℝ) = ∑ x, w x * ∑ y, w y * V x y := hVmean.symm
      _ ≤ ∑ x, w x * ∑ y, w y * L := by
        refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hw0 x)
        exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hL x y) (hw0 y)
      _ = L := by simp_rw [← Finset.sum_mul, hw1, one_mul]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hone
  have hKmean : ∑ x, w x * ∑ y, w y * K x y = 1 / L := by
    rw [mean_div, hVmean]
  have hVgap :
      (∑ x : Fin 13 → Ω, (∏ i, w (x i)) *
        ∑ y : Fin 22 → Ω, (∏ j, w (y j)) * ∏ k : Fin 22 × Fin 3, V (x (t k.1 k.2)) (y k.1)) < 1 := by
    rw [crossed_moment]
    exact hWgap
  refine ⟨Ω, inferInstance, inferInstance, w, K, hw0, hw1, ?_, ?_, ?_, ?_⟩
  · intro a b
    exact ⟨div_nonneg (hV0 a b) hLpos.le, (div_le_one hLpos).mpr (hL a b)⟩
  · intro a b
    exact congrArg (· / L) (mul_comm (W a.1 b.2) (W b.1 a.2))
  · rw [hKmean]
    exact div_pos zero_lt_one hLpos
  · rw [moment_div, hKmean, one_div_pow]
    exact div_lt_div_of_pos_right hVgap (pow_pos hLpos 66)

end OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1
