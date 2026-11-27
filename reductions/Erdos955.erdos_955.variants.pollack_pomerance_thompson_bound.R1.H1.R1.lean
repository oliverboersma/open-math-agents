import OMAReductions.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1

/-! Pollack, Pomerance and Thompson, Divisor-sum fibers (2018), section 2,
arXiv:1706.03120. Split Theorem 1.2 at the four exceptional classes in its proof.
Outside those classes a fixed positive value has few preimages. Summation over the
target set and the two exceptional-set estimates give the uniform conclusion. -/

namespace OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1
open Filter Topology Finset
open scoped Classical

/-- The near-square-root divisor window in condition (b) of Theorem 1.2. -/
def H1 : Prop :=
  ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
    let η := max (ε x) (1 / Real.log (Real.log x))
    let window := fun n : ℕ => ∃ d ∈ n.divisors,
      (x : ℝ) ^ ((1 / 2 : ℝ) - 10 * η) < d ∧ (d : ℝ) < (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η)
    (((Icc 1 x).filter window).card : ℝ) ≤ δ * x

/-- The small-prime, squarefull-divisor, and small-integer exceptions (a), (c), (d). -/
def H2 : Prop :=
  ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
    let η := max (ε x) (1 / Real.log (Real.log x))
    let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨
      (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x
    (((Icc 1 x).filter other).card : ℝ) ≤ δ * x

/-- A uniform bound on one positive fiber after deleting the four exceptional classes.
K bounds each individual fiber, including when the value is larger than x. -/
def H3 : Prop :=
  ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ → ∀ᶠ x : ℕ in atTop,
    let η := max (ε x) (1 / Real.log (Real.log x))
    let window := fun n : ℕ => ∃ d ∈ n.divisors,
      (x : ℝ) ^ ((1 / 2 : ℝ) - 10 * η) < d ∧ (d : ℝ) < (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η)
    let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨
      (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x
    let good := (Icc 1 x).filter (fun n => ¬ window n ∧ ¬ other n)
    ∃ K : ℕ, (x : ℝ) ^ ((1 / 2 : ℝ) + ε x) * K ≤ δ * x ∧
      ∀ a : ℕ, 0 < a → (good.filter (fun n => Erdos955.s n = a)).card ≤ K

lemma finite_fiber_split (S A : Finset ℕ) (s : ℕ → ℕ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (K : ℕ)
    (fiber : ∀ a ∈ A, ((S.filter (fun n => ¬ P n ∧ ¬ Q n)).filter
      (fun n => s n = a)).card ≤ K) :
    (S.filter (fun n => s n ∈ A)).card ≤
      (S.filter P).card + (S.filter Q).card + A.card * K := by
  let G := S.filter (fun n => ¬ P n ∧ ¬ Q n)
  have sub : S.filter (fun n => s n ∈ A) ⊆
      (S.filter P ∪ S.filter Q) ∪ G.filter (fun n => s n ∈ A) := by
    intro n hn
    obtain ⟨hnS, hnA⟩ := mem_filter.mp hn
    by_cases hp : P n
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hnS, hp⟩))
    by_cases hq : Q n
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hnS, hq⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr ⟨hnS,hp,hq⟩,hnA⟩)
  have good : (G.filter (fun n => s n ∈ A)).card ≤ A.card * K := by
    rw [← sum_card_fiberwise_eq_card_filter G A s]
    calc
      _ ≤ ∑ _a ∈ A, K := sum_le_sum fiber
      _ = _ := by simp
  exact (card_le_card sub).trans <| (card_union_le ..).trans <|
    Nat.add_le_add (card_union_le ..) good

theorem main : H1 → H2 → H3 → OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.H1 := by
  classical
  intro h₁ h₂ h₃ ε hε δ hδ
  have hpart : 0 < δ / 3 := by linarith
  filter_upwards [h₁ ε hε (δ / 3) hpart, h₂ ε hε (δ / 3) hpart,
    h₃ ε hε (δ / 3) hpart] with x hwindow hother hsingle
  intro A hpos hsize
  let η := max (ε x) (1 / Real.log (Real.log x))
  let window := fun n : ℕ => ∃ d ∈ n.divisors,
      (x : ℝ) ^ ((1 / 2 : ℝ) - 10 * η) < d ∧ (d : ℝ) < (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η)
  let other := fun n : ℕ => (¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log x) ∨
      (∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < q ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) ∨ n ^ 2 ≤ x
  obtain ⟨K,hK,hfiber⟩ := hsingle
  have htotal := finite_fiber_split (Icc 1 x) A Erdos955.s window other K
    (fun a ha => hfiber a (hpos a ha))
  have hcount : (((Icc 1 x).filter (fun n => Erdos955.s n ∈ A)).card : ℝ) ≤
      (((Icc 1 x).filter window).card : ℝ) + (((Icc 1 x).filter other).card : ℝ) +
      (A.card : ℝ) * K := by exact_mod_cast htotal
  change (((Icc 1 x).filter window).card : ℝ) ≤ δ / 3 * x at hwindow
  change (((Icc 1 x).filter other).card : ℝ) ≤ δ / 3 * x at hother
  have hprod := mul_le_mul_of_nonneg_right hsize (Nat.cast_nonneg (α := ℝ) K)
  linarith

end OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1
