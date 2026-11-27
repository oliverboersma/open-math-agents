import FormalConjectures.ErdosProblems.«448»
import Mathlib

/-! Complementary divisors reduce the dyadic block count to blocks below the
square-root scale, with absolute loss at most three. Double counting then
separates Ford's uniform divisor-in-an-interval estimate from the elementary
sum of its dyadic weights. -/
namespace OMA.R_Erdos448_erdos_448_variants_ford_R1

open Finset Filter Asymptotics Erdos448 Real
open scoped Topology

/-- Ford's dyadic divisor-interval bound, uniform up to the square-root scale.
The half-open block is exactly the integer interval (y,2y] for y=2^j-1/2. -/
def H1 : Prop :=
  let α : ℝ := 1 - (1 + log (log 2)) / log 2
  let w (j : ℕ) := ((j:ℝ)+1)^(-α) / (log ((j:ℝ)+2))^((3:ℝ)/2)
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℕ in atTop, ∀ j ≤ Nat.log 2 x / 2,
    let D := (Icc 1 x).filter fun n => j ∈ n.divisors.image (Nat.log 2)
    c*((x:ℝ)*w j) ≤ D.card ∧ (D.card:ℝ) ≤ C*((x:ℝ)*w j)

/-- Summation of a power with a logarithmic factor, up to half the binary logarithm. -/
def H2 : Prop :=
  let α : ℝ := 1 - (1 + log (log 2)) / log 2
  let w (j : ℕ) := ((j:ℝ)+1)^(-α) / (log ((j:ℝ)+2))^((3:ℝ)/2)
  (fun x : ℕ => ∑ j ∈ range (Nat.log 2 x / 2 + 1), w j) =Θ[atTop]
    (fun x : ℕ => log (x:ℝ)^(1-α) / log (log (x:ℝ))^((3:ℝ)/2))

lemma log_product {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    Nat.log 2 d + Nat.log 2 e ≤ Nat.log 2 (d*e) ∧
      Nat.log 2 (d*e) ≤ Nat.log 2 d + Nat.log 2 e + 1 := by
  constructor
  · apply Nat.le_log_of_pow_le (by decide)
    rw [pow_add]
    exact Nat.mul_le_mul (Nat.pow_log_le_self 2 hd) (Nat.pow_log_le_self 2 he)
  · have h := Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) d)
        (Nat.lt_pow_succ_log_self (by decide : 1 < 2) e)
    rw [← pow_add] at h
    have := Nat.log_lt_of_lt_pow (Nat.mul_ne_zero hd he) h
    omega

lemma block_card {x n : ℕ} (hn : n ≠ 0) (hnx : n ≤ x) :
    let S := n.divisors.image (Nat.log 2)
    let B := S.filter fun j => j ≤ Nat.log 2 x / 2
    B.card ≤ S.card ∧ S.card ≤ 3*B.card := by
  intro S B
  refine ⟨card_le_card (filter_subset _ _),?_⟩
  let L := Nat.log 2 n
  let Lx := Nat.log 2 x
  have cov : S ⊆ B ∪ B.image (fun k => L-k) ∪ B.image (fun k => L-(k+1)) := by
    intro j hj
    by_cases small : j ≤ Lx/2
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hj,small⟩))
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hj
    obtain ⟨e,heq⟩ := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := by rintro rfl; simp_all
    have he0 : e ≠ 0 := by rintro rfl; simp_all
    have hlog := log_product hd0 he0
    rw [← heq] at hlog
    have hL : L ≤ Lx := Nat.log_mono_right hnx
    change _ ≤ L ∧ L ≤ _ at hlog
    have hediv : e ∈ n.divisors := Nat.mem_divisors.mpr ⟨⟨d,by simpa [Nat.mul_comm] using heq⟩,hn⟩
    have heb : Nat.log 2 e ∈ B := mem_filter.mpr ⟨mem_image.mpr ⟨e,hediv,rfl⟩,by change _ ≤ Lx/2; omega⟩
    by_cases h : Nat.log 2 d + Nat.log 2 e = L
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨_,heb,by omega⟩))
    · exact mem_union_right _ (mem_image.mpr ⟨_,heb,by omega⟩)
  have h := card_le_card cov
  have h₁ := card_union_le B (B.image fun k => L-k)
  have h₂ := card_union_le (B ∪ B.image fun k => L-k) (B.image fun k => L-(k+1))
  have h₃ : (B.image fun k => L-k).card ≤ B.card := card_image_le
  have h₄ : (B.image fun k => L-(k+1)).card ≤ B.card := card_image_le
  omega

lemma total_blocks (x : ℕ) :
    let J := range (Nat.log 2 x / 2 + 1)
    let D (j : ℕ) := (Icc 1 x).filter fun n => j ∈ n.divisors.image (Nat.log 2)
    let U := ∑ j ∈ J, ((D j).card : ℝ)
    U ≤ ∑ n ∈ Icc 1 x, (tauPlus n : ℝ) ∧ (∑ n ∈ Icc 1 x, (tauPlus n : ℝ)) ≤ 3*U := by
  intro J D U
  let B (n : ℕ) := (n.divisors.image (Nat.log 2)).filter fun j => j ≤ Nat.log 2 x / 2
  have row (n : ℕ) : (B n).card = (J.filter fun j => j ∈ n.divisors.image (Nat.log 2)).card := by
    congr 1
    ext j
    simp [B,J,and_comm]
  have eqn : U = ∑ n ∈ Icc 1 x, ((B n).card : ℝ) := by
    dsimp only [U,D]
    simp_rw [row,card_filter]
    push_cast
    rw [sum_comm]
  have bounds (n : ℕ) (hn : n ∈ Icc 1 x) :
      ((B n).card:ℝ) ≤ tauPlus n ∧ (tauPlus n:ℝ) ≤ 3*(B n).card := by
    have hb := block_card (by have := (mem_Icc.mp hn).1; omega : n ≠ 0) (mem_Icc.mp hn).2
    constructor
    · exact_mod_cast hb.1
    · exact_mod_cast hb.2
  rw [eqn,mul_sum]
  exact ⟨sum_le_sum fun n hn => (bounds n hn).1,sum_le_sum fun n hn => (bounds n hn).2⟩
theorem main : H1 → H2 → type_of% @Erdos448.erdos_448.variants.ford := by
  intro ford weights
  let α : ℝ := 1 - (1 + log (log 2)) / log 2
  let w (j : ℕ) := ((j:ℝ)+1)^(-α) / (log ((j:ℝ)+2))^((3:ℝ)/2)
  let J (x : ℕ) := range (Nat.log 2 x / 2 + 1)
  let W (x : ℕ) := ∑ j ∈ J x, w j
  let A (x : ℕ) := ∑ n ∈ Icc 1 x, (tauPlus n:ℝ)
  have wpos (j : ℕ) : 0 ≤ w j := by
    have := log_pos (by linarith [Nat.cast_nonneg (α := ℝ) j] : (1:ℝ) < j+2)
    dsimp [w]
    positivity
  have wp (x : ℕ) : 0 ≤ (x:ℝ)*W x := mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun j _ => wpos j)
  have ap (x : ℕ) : 0 ≤ A x := sum_nonneg fun _ _ => Nat.cast_nonneg _
  obtain ⟨c,C,hc,hC,hf⟩ := ford
  have both : ∀ᶠ x : ℕ in atTop, c*((x:ℝ)*W x) ≤ A x ∧ A x ≤ 3*C*((x:ℝ)*W x) := by
    filter_upwards [hf] with x hx
    let D (j : ℕ) := (Icc 1 x).filter fun n => j ∈ n.divisors.image (Nat.log 2)
    have bound (j : ℕ) (hj : j ∈ J x) : c*((x:ℝ)*w j) ≤ (D j).card ∧ (D j).card ≤ C*((x:ℝ)*w j) :=
      hx j (by have := mem_range.mp hj; omega)
    have low := sum_le_sum (s := J x) fun j hj => (bound j hj).1
    have high := sum_le_sum (s := J x) fun j hj => (bound j hj).2
    simp_rw [← mul_sum] at low high
    have b := total_blocks x
    change (∑ j ∈ J x, ((D j).card:ℝ)) ≤ A x ∧ A x ≤ 3*(∑ j ∈ J x, ((D j).card:ℝ)) at b
    exact ⟨low.trans b.1,b.2.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left high (by norm_num))⟩
  have comp : A =Θ[atTop] (fun x : ℕ => (x:ℝ)*W x) := by
    constructor
    · apply isBigO_iff.mpr
      exact ⟨3*C,both.mono fun x h => by simpa only [Real.norm_of_nonneg (wp x),Real.norm_of_nonneg (ap x)] using h.2⟩
    · apply isBigO_iff.mpr
      refine ⟨c⁻¹,both.mono fun x h => ?_⟩
      rw [Real.norm_of_nonneg (wp x),Real.norm_of_nonneg (ap x),← div_eq_inv_mul,le_div_iff₀ hc,mul_comm]
      exact h.1
  have idth : (fun x : ℕ => (x:ℝ)) =Θ[atTop] (fun x : ℕ => (x:ℝ)) := isTheta_refl _ _
  have combined := comp.trans (idth.mul weights)
  apply combined.trans_eventuallyEq
  exact Eventually.of_forall fun x => by dsimp [α]; ring

end OMA.R_Erdos448_erdos_448_variants_ford_R1
