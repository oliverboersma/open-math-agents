import OMAReductions.R_Erdos3_erdos_3_variants_green_tao_R2

-- Proof of step Erdos3.erdos_3.variants.green_tao.R2.H1
-- Credit: @skhakim

/-!
# Generalized von Neumann Theorem for 4-term Arithmetic Progressions

We prove `OMA.R_Erdos3_erdos_3_variants_green_tao_R2.H1`: if a 4-AP-free subset
`S ⊆ {1, ..., N}` has balanced function `f = 1_S - (|S|/N) 1_{[1,N]}` whose integer Gowers `U³`
sum is `< κ (|S|/N)^32 N^4`, then `|S| ≤ 100 N (log N)⁻¹` for all `N ≥ 100`.

The proof embeds `{1, ..., N}` into `ZMod (6*N + 1)` (where `±1, ±2, ±3` are units and neither
4-APs nor `U³` cubes wrap around), applies three Cauchy–Schwarz steps to bound each of the four
telescoping terms `Λ(f, g, g, g)`, `Λ(h, f, g, g)`, `Λ(h, h, f, g)`, `Λ(h, h, h, f)` by
`(6*N + 1)^(3/2) U₃(f)^(1/8)`, and compares with `Λ(h, h, h, h) ≥ (1/20) α^4 N^2` and
`Λ(g, g, g, g) = |S|`.
-/

namespace Erdos3R2H1

open Finset BigOperators

/- ## Section 1: Generalized von Neumann over a finite commutative ring -/

section RingGVN

variable {R : Type*} [Fintype R] [CommRing R]

/-- Bijection `x ↦ u * x` induced by a unit `u : Rˣ`. -/
def mulUnitEquiv (u : Rˣ) : R ≃ R where
  toFun x := (u : R) * x
  invFun x := (↑u⁻¹ : R) * x
  left_inv x := by dsimp only; rw [← mul_assoc, Units.inv_mul, one_mul]
  right_inv x := by dsimp only; rw [← mul_assoc, Units.mul_inv, one_mul]

/-- Multiplicative discrete derivative `(Δ_h f)(x) = f(x) * f(x + h)`. -/
def diff (f : R → ℝ) (h x : R) : ℝ := f x * f (x + h)

omit [Fintype R] in
lemma abs_diff_le_one {f : R → ℝ} (hf : ∀ x, |f x| ≤ 1) (h x : R) :
    |diff f h x| ≤ 1 := by
  unfold diff
  rw [abs_mul]
  exact mul_le_one₀ (hf x) (abs_nonneg _) (hf (x + h))

/-- Cauchy–Schwarz when one factor is pointwise bounded by `1`. -/
lemma sq_sum_mul_le {ι : Type*} [Fintype ι] (g F : ι → ℝ) (hg : ∀ i, |g i| ≤ 1) :
    (∑ i : ι, g i * F i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i : ι, (F i) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) g F
  have hgle : ∑ i : ι, (g i) ^ 2 ≤ (Fintype.card ι : ℝ) := by
    calc ∑ i : ι, (g i) ^ 2
        ≤ ∑ _i : ι, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : |g i| ≤ 1 := hg i
          nlinarith [sq_abs (g i), abs_nonneg (g i)]
      _ = (Fintype.card ι : ℝ) := by simp
  have hFnn : 0 ≤ ∑ i : ι, (F i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact hcs.trans (mul_le_mul_of_nonneg_right hgle hFnn)

/-- Step 1: eliminate `g₃(u + c₃ * d)` using `IsUnit c₃`. -/
lemma gvn_step1 (f g₁ g₂ g₃ : R → ℝ) (c₁ c₂ c₃ : R)
    (hc₃ : IsUnit c₃) (hg₃ : ∀ x, |g₃ x| ≤ 1) :
    let u₃ : Rˣ := (-hc₃.unit)
    (∑ u : R, ∑ d : R, f u * g₁ (u + c₁ * d) * g₂ (u + c₂ * d) * g₃ (u + c₃ * d)) ^ 2 ≤
      (Fintype.card R : ℝ) *
        ∑ a : R, ∑ u : R, ∑ d : R,
          diff f a u *
          diff g₁ ((c₁ - c₃) * (↑u₃⁻¹ : R) * a) (u + c₁ * d) *
          diff g₂ ((c₂ - c₃) * (↑u₃⁻¹ : R) * a) (u + c₂ * d) := by
  intro u₃
  have hu₃_val : (↑u₃ : R) = -c₃ := by simp [u₃]
  have hneg_c3_inv : ∀ a : R, -c₃ * ((↑u₃⁻¹ : R) * a) = a := by
    intro a
    rw [← mul_assoc, ← hu₃_val, Units.mul_inv, one_mul]
  -- Reindex `(u, d)` via `w = u + c₃ * d`, `u = w - c₃ * d`.
  have hrew :
      ∑ u : R, ∑ d : R, f u * g₁ (u + c₁ * d) * g₂ (u + c₂ * d) * g₃ (u + c₃ * d) =
      ∑ w : R, g₃ w *
        ∑ d : R, f (w - c₃ * d) * g₁ (w + (c₁ - c₃) * d) * g₂ (w + (c₂ - c₃) * d) := by
    rw [Finset.sum_comm]
    have hinner : ∀ d : R,
        ∑ u : R, f u * g₁ (u + c₁ * d) * g₂ (u + c₂ * d) * g₃ (u + c₃ * d) =
        ∑ w : R, g₃ w *
          (f (w - c₃ * d) * g₁ (w + (c₁ - c₃) * d) * g₂ (w + (c₂ - c₃) * d)) := by
      intro d
      refine Fintype.sum_equiv (Equiv.addRight (c₃ * d)) _ _ fun u => ?_
      change f u * g₁ (u + c₁ * d) * g₂ (u + c₂ * d) * g₃ (u + c₃ * d) =
        g₃ (u + c₃ * d) * (f (u + c₃ * d - c₃ * d) *
          g₁ (u + c₃ * d + (c₁ - c₃) * d) * g₂ (u + c₃ * d + (c₂ - c₃) * d))
      have h1 : u + c₃ * d - c₃ * d = u := by ring
      have h2 : u + c₃ * d + (c₁ - c₃) * d = u + c₁ * d := by ring
      have h3 : u + c₃ * d + (c₂ - c₃) * d = u + c₂ * d := by ring
      rw [h1, h2, h3]
      ring
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
  rw [hrew]
  refine (sq_sum_mul_le g₃ _ hg₃).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  -- Expand the square and reindex `(w, d₁, d₂) ↦ (a, u, d₁)` with `d₂ = d₁ + h`, `w = u + c₃*d₁`, `a = -c₃*h`.
  have hexp : ∀ w : R,
      (∑ d : R, f (w - c₃ * d) * g₁ (w + (c₁ - c₃) * d) * g₂ (w + (c₂ - c₃) * d)) ^ 2 =
      ∑ d₁ : R, ∑ h : R,
        (f (w - c₃ * d₁) * f (w - c₃ * d₁ + (-c₃ * h))) *
        (g₁ (w + (c₁ - c₃) * d₁) * g₁ (w + (c₁ - c₃) * d₁ + (c₁ - c₃) * h)) *
        (g₂ (w + (c₂ - c₃) * d₁) * g₂ (w + (c₂ - c₃) * d₁ + (c₂ - c₃) * h)) := by
    intro w
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    refine Fintype.sum_equiv (Equiv.addLeft d₁).symm _ _ fun d₂ => ?_
    simp only [Equiv.addLeft_symm_apply]
    have h1 : w - c₃ * d₁ + -c₃ * (-d₁ + d₂) = w - c₃ * d₂ := by ring
    have h2 : w + (c₁ - c₃) * d₁ + (c₁ - c₃) * (-d₁ + d₂) = w + (c₁ - c₃) * d₂ := by ring
    have h3 : w + (c₂ - c₃) * d₁ + (c₂ - c₃) * (-d₁ + d₂) = w + (c₂ - c₃) * d₂ := by ring
    rw [h1, h2, h3]
    ring
  simp_rw [hexp]
  -- Swap `w` inside `(d₁, h)`
  rw [Finset.sum_comm]
  have hswap1 :
      (∑ d₁ : R, ∑ w : R, ∑ h : R,
        (f (w - c₃ * d₁) * f (w - c₃ * d₁ + (-c₃ * h))) *
        (g₁ (w + (c₁ - c₃) * d₁) * g₁ (w + (c₁ - c₃) * d₁ + (c₁ - c₃) * h)) *
        (g₂ (w + (c₂ - c₃) * d₁) * g₂ (w + (c₂ - c₃) * d₁ + (c₂ - c₃) * h))) =
      ∑ h : R, ∑ u : R, ∑ d₁ : R,
        diff f (-c₃ * h) u *
        diff g₁ ((c₁ - c₃) * h) (u + c₁ * d₁) *
        diff g₂ ((c₂ - c₃) * h) (u + c₂ * d₁) := by
    have h1 : ∀ d₁ : R,
        (∑ w : R, ∑ h : R,
          (f (w - c₃ * d₁) * f (w - c₃ * d₁ + (-c₃ * h))) *
          (g₁ (w + (c₁ - c₃) * d₁) * g₁ (w + (c₁ - c₃) * d₁ + (c₁ - c₃) * h)) *
          (g₂ (w + (c₂ - c₃) * d₁) * g₂ (w + (c₂ - c₃) * d₁ + (c₂ - c₃) * h))) =
        ∑ u : R, ∑ h : R,
          diff f (-c₃ * h) u *
          diff g₁ ((c₁ - c₃) * h) (u + c₁ * d₁) *
          diff g₂ ((c₂ - c₃) * h) (u + c₂ * d₁) := by
      intro d₁
      refine Fintype.sum_equiv (Equiv.addRight (c₃ * d₁)).symm _ _ fun w => ?_
      simp only [Equiv.addRight_symm_apply, diff]
      refine Finset.sum_congr rfl fun h _ => ?_
      have e1 : w + -(c₃ * d₁) = w - c₃ * d₁ := by ring
      have e2 : w - c₃ * d₁ + c₁ * d₁ = w + (c₁ - c₃) * d₁ := by ring
      have e3 : w - c₃ * d₁ + c₂ * d₁ = w + (c₂ - c₃) * d₁ := by ring
      rw [e1, e2, e3]
    simp_rw [h1]
    -- Currently `∑ d₁, ∑ u, ∑ h, ...`; reorder to `∑ h, ∑ u, ∑ d₁, ...`
    rw [Finset.sum_comm]
    trans ∑ u : R, ∑ h : R, ∑ d₁ : R,
        diff f (-c₃ * h) u *
        diff g₁ ((c₁ - c₃) * h) (u + c₁ * d₁) *
        diff g₂ ((c₂ - c₃) * h) (u + c₂ * d₁)
    · exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
    · exact Finset.sum_comm
  rw [hswap1]
  -- Reindex `h ↦ a = u₃ * h = -c₃ * h`
  have hbij :
      (∑ h : R, ∑ u : R, ∑ d₁ : R,
        diff f (-c₃ * h) u *
        diff g₁ ((c₁ - c₃) * h) (u + c₁ * d₁) *
        diff g₂ ((c₂ - c₃) * h) (u + c₂ * d₁)) =
      ∑ a : R, ∑ u : R, ∑ d₁ : R,
        diff f a u *
        diff g₁ ((c₁ - c₃) * (↑u₃⁻¹ : R) * a) (u + c₁ * d₁) *
        diff g₂ ((c₂ - c₃) * (↑u₃⁻¹ : R) * a) (u + c₂ * d₁) := by
    refine Fintype.sum_equiv (mulUnitEquiv u₃) _ _ fun h => ?_
    simp only [mulUnitEquiv, Equiv.coe_fn_mk, hu₃_val]
    have hinv : (↑u₃⁻¹ : R) * (-c₃ * h) = h := by
      rw [← hu₃_val, ← mul_assoc, Units.inv_mul, one_mul]
    simp_rw [mul_assoc (c₁ - c₃), mul_assoc (c₂ - c₃), hinv]
  exact le_of_eq hbij

/-- Step 2: eliminate `G₂ a (u + c₂ * d)` using `IsUnit c₂`. -/
lemma gvn_step2 (F : R → R → ℝ) (G₁ G₂ : R → R → ℝ) (c₁ c₂ : R)
    (hc₂ : IsUnit c₂) (hG₂ : ∀ a x, |G₂ a x| ≤ 1) :
    let u₂ : Rˣ := (-hc₂.unit)
    (∑ a : R, ∑ u : R, ∑ d : R, F a u * G₁ a (u + c₁ * d) * G₂ a (u + c₂ * d)) ^ 2 ≤
      ((Fintype.card R : ℝ) ^ 2) *
        ∑ a : R, ∑ b : R, ∑ u : R, ∑ d : R,
          diff (F a) b u *
          diff (G₁ a) ((c₁ - c₂) * (↑u₂⁻¹ : R) * b) (u + c₁ * d) := by
  intro u₂
  have hu₂_val : (↑u₂ : R) = -c₂ := by simp [u₂]
  have hrew :
      (∑ a : R, ∑ u : R, ∑ d : R, F a u * G₁ a (u + c₁ * d) * G₂ a (u + c₂ * d)) =
      ∑ p : R × R, G₂ p.1 p.2 *
        ∑ d : R, F p.1 (p.2 - c₂ * d) * G₁ p.1 (p.2 + (c₁ - c₂) * d) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    have hinner : ∀ d : R,
        ∑ u : R, F a u * G₁ a (u + c₁ * d) * G₂ a (u + c₂ * d) =
        ∑ w : R, G₂ a w * (F a (w - c₂ * d) * G₁ a (w + (c₁ - c₂) * d)) := by
      intro d
      refine Fintype.sum_equiv (Equiv.addRight (c₂ * d)) _ _ fun u => ?_
      change F a u * G₁ a (u + c₁ * d) * G₂ a (u + c₂ * d) =
        G₂ a (u + c₂ * d) * (F a (u + c₂ * d - c₂ * d) * G₁ a (u + c₂ * d + (c₁ - c₂) * d))
      have h1 : u + c₂ * d - c₂ * d = u := by ring
      have h2 : u + c₂ * d + (c₁ - c₂) * d = u + c₁ * d := by ring
      rw [h1, h2]; ring
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
  rw [hrew]
  have hcs := sq_sum_mul_le (fun p : R × R => G₂ p.1 p.2)
    (fun p : R × R => ∑ d : R, F p.1 (p.2 - c₂ * d) * G₁ p.1 (p.2 + (c₁ - c₂) * d))
    (fun p => hG₂ p.1 p.2)
  have hcard : (Fintype.card (R × R) : ℝ) = (Fintype.card R : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Nat.cast_mul, sq]
  rw [hcard] at hcs
  have hcs' : (∑ p : R × R, G₂ p.1 p.2 *
        ∑ d : R, F p.1 (p.2 - c₂ * d) * G₁ p.1 (p.2 + (c₁ - c₂) * d)) ^ 2 ≤
      (Fintype.card R : ℝ) ^ 2 *
        ∑ a : R, ∑ w : R, (∑ d : R, F a (w - c₂ * d) * G₁ a (w + (c₁ - c₂) * d)) ^ 2 := by
    simpa only [Fintype.sum_prod_type] using hcs
  refine hcs'.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine le_of_eq (Finset.sum_congr rfl fun a _ => ?_)
  have hexp : ∀ w : R,
      (∑ d : R, F a (w - c₂ * d) * G₁ a (w + (c₁ - c₂) * d)) ^ 2 =
      ∑ d₁ : R, ∑ h : R,
        (F a (w - c₂ * d₁) * F a (w - c₂ * d₁ + (-c₂ * h))) *
        (G₁ a (w + (c₁ - c₂) * d₁) * G₁ a (w + (c₁ - c₂) * d₁ + (c₁ - c₂) * h)) := by
    intro w
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    refine Fintype.sum_equiv (Equiv.addLeft d₁).symm _ _ fun d₂ => ?_
    simp only [Equiv.addLeft_symm_apply]
    have h1 : w - c₂ * d₁ + -c₂ * (-d₁ + d₂) = w - c₂ * d₂ := by ring
    have h2 : w + (c₁ - c₂) * d₁ + (c₁ - c₂) * (-d₁ + d₂) = w + (c₁ - c₂) * d₂ := by ring
    rw [h1, h2]; ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hswap :
      (∑ d₁ : R, ∑ w : R, ∑ h : R,
        (F a (w - c₂ * d₁) * F a (w - c₂ * d₁ + (-c₂ * h))) *
        (G₁ a (w + (c₁ - c₂) * d₁) * G₁ a (w + (c₁ - c₂) * d₁ + (c₁ - c₂) * h))) =
      ∑ h : R, ∑ u : R, ∑ d₁ : R,
        diff (F a) (-c₂ * h) u * diff (G₁ a) ((c₁ - c₂) * h) (u + c₁ * d₁) := by
    have h1 : ∀ d₁ : R,
        (∑ w : R, ∑ h : R,
          (F a (w - c₂ * d₁) * F a (w - c₂ * d₁ + (-c₂ * h))) *
          (G₁ a (w + (c₁ - c₂) * d₁) * G₁ a (w + (c₁ - c₂) * d₁ + (c₁ - c₂) * h))) =
        ∑ u : R, ∑ h : R,
          diff (F a) (-c₂ * h) u * diff (G₁ a) ((c₁ - c₂) * h) (u + c₁ * d₁) := by
      intro d₁
      refine Fintype.sum_equiv (Equiv.addRight (c₂ * d₁)).symm _ _ fun w => ?_
      simp only [Equiv.addRight_symm_apply, diff]
      refine Finset.sum_congr rfl fun h _ => ?_
      have e1 : w + -(c₂ * d₁) = w - c₂ * d₁ := by ring
      have e2 : w - c₂ * d₁ + c₁ * d₁ = w + (c₁ - c₂) * d₁ := by ring
      rw [e1, e2]
    simp_rw [h1]
    rw [Finset.sum_comm]
    trans ∑ u : R, ∑ h : R, ∑ d₁ : R,
        diff (F a) (-c₂ * h) u * diff (G₁ a) ((c₁ - c₂) * h) (u + c₁ * d₁)
    · exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
    · exact Finset.sum_comm
  rw [hswap]
  refine Fintype.sum_equiv (mulUnitEquiv u₂) _ _ fun h => ?_
  simp only [mulUnitEquiv, Equiv.coe_fn_mk, hu₂_val]
  have hinv : (↑u₂⁻¹ : R) * (-c₂ * h) = h := by
    rw [← hu₂_val, ← mul_assoc, Units.inv_mul, one_mul]
  simp_rw [mul_assoc (c₁ - c₂), hinv]

/-- Step 3: eliminate `H₁ a b (u + c₁ * d)` using `IsUnit c₁`. -/
lemma gvn_step3 (F : R → R → R → ℝ) (H₁ : R → R → R → ℝ) (c₁ : R)
    (hc₁ : IsUnit c₁) (hH₁ : ∀ a b x, |H₁ a b x| ≤ 1) :
    (∑ a : R, ∑ b : R, ∑ u : R, ∑ d : R, F a b u * H₁ a b (u + c₁ * d)) ^ 2 ≤
      ((Fintype.card R : ℝ) ^ 4) *
        ∑ a : R, ∑ b : R, ∑ e : R, ∑ x : R, diff (F a b) e x := by
  let u₁ : Rˣ := (-hc₁.unit)
  have hu₁_val : (↑u₁ : R) = -c₁ := by simp [u₁]
  have hrew :
      (∑ a : R, ∑ b : R, ∑ u : R, ∑ d : R, F a b u * H₁ a b (u + c₁ * d)) =
      ∑ p : (R × R) × R, H₁ p.1.1 p.1.2 p.2 * ∑ d : R, F p.1.1 p.1.2 (p.2 - c₁ * d) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    have hinner : ∀ d : R,
        ∑ u : R, F a b u * H₁ a b (u + c₁ * d) =
        ∑ w : R, H₁ a b w * F a b (w - c₁ * d) := by
      intro d
      refine Fintype.sum_equiv (Equiv.addRight (c₁ * d)) _ _ fun u => ?_
      change F a b u * H₁ a b (u + c₁ * d) = H₁ a b (u + c₁ * d) * F a b (u + c₁ * d - c₁ * d)
      have h1 : u + c₁ * d - c₁ * d = u := by ring
      rw [h1]; ring
    simp_rw [hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
  rw [hrew]
  have hcs := sq_sum_mul_le (fun p : (R × R) × R => H₁ p.1.1 p.1.2 p.2)
    (fun p : (R × R) × R => ∑ d : R, F p.1.1 p.1.2 (p.2 - c₁ * d))
    (fun p => hH₁ p.1.1 p.1.2 p.2)
  have hcard : (Fintype.card ((R × R) × R) : ℝ) = (Fintype.card R : ℝ) ^ 3 := by
    rw [Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul]; ring
  rw [hcard] at hcs
  have hcs' : (∑ p : (R × R) × R, H₁ p.1.1 p.1.2 p.2 *
        ∑ d : R, F p.1.1 p.1.2 (p.2 - c₁ * d)) ^ 2 ≤
      (Fintype.card R : ℝ) ^ 3 *
        ∑ a : R, ∑ b : R, ∑ w : R, (∑ d : R, F a b (w - c₁ * d)) ^ 2 := by
    simpa only [Fintype.sum_prod_type] using hcs
  have hinner_eq : ∀ a b : R,
      ∑ w : R, (∑ d : R, F a b (w - c₁ * d)) ^ 2 =
      (Fintype.card R : ℝ) * ∑ e : R, ∑ x : R, diff (F a b) e x := by
    intro a b
    have hexp : ∀ w : R,
        (∑ d : R, F a b (w - c₁ * d)) ^ 2 =
        ∑ d₁ : R, ∑ h : R, F a b (w - c₁ * d₁) * F a b (w - c₁ * d₁ + (-c₁ * h)) := by
      intro w
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      refine Fintype.sum_equiv (Equiv.addLeft d₁).symm _ _ fun d₂ => ?_
      simp only [Equiv.addLeft_symm_apply]
      have h1 : w - c₁ * d₁ + -c₁ * (-d₁ + d₂) = w - c₁ * d₂ := by ring
      rw [h1]
    simp_rw [hexp]
    rw [Finset.sum_comm]
    have hconst : ∀ d₁ : R,
        (∑ w : R, ∑ h : R, F a b (w - c₁ * d₁) * F a b (w - c₁ * d₁ + (-c₁ * h))) =
        ∑ e : R, ∑ x : R, diff (F a b) e x := by
      intro d₁
      have hsub :
          (∑ w : R, ∑ h : R, F a b (w - c₁ * d₁) * F a b (w - c₁ * d₁ + (-c₁ * h))) =
          ∑ x : R, ∑ h : R, diff (F a b) (-c₁ * h) x := by
        refine Fintype.sum_equiv (Equiv.addRight (c₁ * d₁)).symm _ _ fun w => ?_
        simp only [Equiv.addRight_symm_apply, diff]
        have e1 : w + -(c₁ * d₁) = w - c₁ * d₁ := by ring
        rw [e1]
      rw [hsub, Finset.sum_comm]
      refine Fintype.sum_equiv (mulUnitEquiv u₁) _ _ fun h => ?_
      simp only [mulUnitEquiv, Equiv.coe_fn_mk, hu₁_val]
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [hinner_eq] at hcs'
  have hpull :
      ∑ a : R, ∑ b : R, (Fintype.card R : ℝ) * ∑ e : R, ∑ x : R, diff (F a b) e x =
      (Fintype.card R : ℝ) * ∑ a : R, ∑ b : R, ∑ e : R, ∑ x : R, diff (F a b) e x := by
    simp_rw [← Finset.mul_sum]
  rw [hpull] at hcs'
  calc (∑ p : (R × R) × R, H₁ p.1.1 p.1.2 p.2 * ∑ d : R, F p.1.1 p.1.2 (p.2 - c₁ * d)) ^ 2
      ≤ (Fintype.card R : ℝ) ^ 3 *
          ((Fintype.card R : ℝ) * ∑ a : R, ∑ b : R, ∑ e : R, ∑ x : R, diff (F a b) e x) := hcs'
    _ = (Fintype.card R : ℝ) ^ 4 *
          ∑ a : R, ∑ b : R, ∑ e : R, ∑ x : R, diff (F a b) e x := by ring

/-- Combined 3-step generalized von Neumann bound over any finite commutative ring `R`. -/
theorem gvn_ring (f g₁ g₂ g₃ : R → ℝ) (c₁ c₂ c₃ : R)
    (hc₁ : IsUnit c₁) (hc₂ : IsUnit c₂) (hc₃ : IsUnit c₃)
    (hg₁ : ∀ x, |g₁ x| ≤ 1) (hg₂ : ∀ x, |g₂ x| ≤ 1) (hg₃ : ∀ x, |g₃ x| ≤ 1) :
    (∑ u : R, ∑ d : R, f u * g₁ (u + c₁ * d) * g₂ (u + c₂ * d) * g₃ (u + c₃ * d)) ^ 8 ≤
      (Fintype.card R : ℝ) ^ 12 *
        ∑ x : R, ∑ a : R, ∑ b : R, ∑ e : R,
          f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
            f (x + b + e) * f (x + a + b + e) := by
  let M : ℝ := (Fintype.card R : ℝ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  let u₃ : Rˣ := -hc₃.unit
  let u₂ : Rˣ := -hc₂.unit
  let G₁ : R → R → ℝ := fun a x => diff g₁ ((c₁ - c₃) * (↑u₃⁻¹ : R) * a) x
  let G₂ : R → R → ℝ := fun a x => diff g₂ ((c₂ - c₃) * (↑u₃⁻¹ : R) * a) x
  let H₁ : R → R → R → ℝ := fun a b x => diff (G₁ a) ((c₁ - c₂) * (↑u₂⁻¹ : R) * b) x
  have hG₁ : ∀ a x, |G₁ a x| ≤ 1 := fun a x => abs_diff_le_one hg₁ _ x
  have hG₂ : ∀ a x, |G₂ a x| ≤ 1 := fun a x => abs_diff_le_one hg₂ _ x
  have hH₁ : ∀ a b x, |H₁ a b x| ≤ 1 := fun a b x => abs_diff_le_one (hG₁ a) _ x
  have h1 := gvn_step1 f g₁ g₂ g₃ c₁ c₂ c₃ hc₃ hg₃
  have h2 := gvn_step2 (fun a u => diff f a u) G₁ G₂ c₁ c₂ hc₂ hG₂
  have h3 := gvn_step3 (fun a b u => diff (diff f a) b u) H₁ c₁ hc₁ hH₁
  let T := ∑ u : R, ∑ d : R, f u * g₁ (u + c₁ * d) * g₂ (u + c₂ * d) * g₃ (u + c₃ * d)
  let S₁ := ∑ a : R, ∑ u : R, ∑ d : R, diff f a u * G₁ a (u + c₁ * d) * G₂ a (u + c₂ * d)
  let S₂ := ∑ a : R, ∑ b : R, ∑ u : R, ∑ d : R, diff (diff f a) b u * H₁ a b (u + c₁ * d)
  let U := ∑ a : R, ∑ b : R, ∑ e : R, ∑ x : R, diff (diff (diff f a) b) e x
  have hT2 : T ^ 2 ≤ M * S₁ := h1
  have hS1_2 : S₁ ^ 2 ≤ M ^ 2 * S₂ := h2
  have hS2_2 : S₂ ^ 2 ≤ M ^ 4 * U := h3
  have hT4 : T ^ 4 ≤ M ^ 4 * S₂ := by
    have hsq : (T ^ 2) ^ 2 ≤ (M * S₁) ^ 2 := pow_le_pow_left₀ (sq_nonneg T) hT2 2
    calc T ^ 4 = (T ^ 2) ^ 2 := by ring
      _ ≤ (M * S₁) ^ 2 := hsq
      _ = M ^ 2 * S₁ ^ 2 := by ring
      _ ≤ M ^ 2 * (M ^ 2 * S₂) := mul_le_mul_of_nonneg_left hS1_2 (sq_nonneg M)
      _ = M ^ 4 * S₂ := by ring
  have hT8 : T ^ 8 ≤ M ^ 12 * U := by
    have hsq : (T ^ 4) ^ 2 ≤ (M ^ 4 * S₂) ^ 2 := pow_le_pow_left₀ (by positivity) hT4 2
    calc T ^ 8 = (T ^ 4) ^ 2 := by ring
      _ ≤ (M ^ 4 * S₂) ^ 2 := hsq
      _ = M ^ 8 * S₂ ^ 2 := by ring
      _ ≤ M ^ 8 * (M ^ 4 * U) := mul_le_mul_of_nonneg_left hS2_2 (by positivity)
      _ = M ^ 12 * U := by ring
  -- Reorder sums and expand `diff (diff (diff f a) b) e x`
  have hU_eq : U = ∑ x : R, ∑ a : R, ∑ b : R, ∑ e : R,
      f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
        f (x + b + e) * f (x + a + b + e) := by
    have hterm : ∀ a b e x : R,
        diff (diff (diff f a) b) e x =
        f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
          f (x + b + e) * f (x + a + b + e) := by
      intro a b e x
      simp only [diff]
      have e1 : x + b + a = x + a + b := by ring
      have e2 : x + e + a = x + a + e := by ring
      have e3 : x + e + b = x + b + e := by ring
      have e4 : x + b + e + a = x + a + b + e := by ring
      rw [e1, e2, e3, e4]; ring
    dsimp only [U]
    simp_rw [hterm]
    -- Move `x` to the outermost sum
    trans ∑ a : R, ∑ b : R, ∑ x : R, ∑ e : R,
        f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
          f (x + b + e) * f (x + a + b + e)
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    trans ∑ a : R, ∑ x : R, ∑ b : R, ∑ e : R,
        f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
          f (x + b + e) * f (x + a + b + e)
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    exact Finset.sum_comm
  simpa only [M, ← hU_eq] using hT8

/-- Bound the 4-AP sum over `R` by the `U³` sum of any of the four positions, assuming `±1, ±2, ±3`
are units in `R`. -/
lemma gvn_4ap_pos (f₀ f₁ f₂ f₃ : R → ℝ)
    (h1 : IsUnit (1 : R)) (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) :
    let Λ := ∑ x : R, ∑ d : R, f₀ x * f₁ (x + d) * f₂ (x + 2 * d) * f₃ (x + 3 * d)
    let U3 (f : R → ℝ) := ∑ x : R, ∑ a : R, ∑ b : R, ∑ e : R,
      f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
        f (x + b + e) * f (x + a + b + e)
    ((∀ x, |f₁ x| ≤ 1) → (∀ x, |f₂ x| ≤ 1) → (∀ x, |f₃ x| ≤ 1) →
      Λ ^ 8 ≤ (Fintype.card R : ℝ) ^ 12 * U3 f₀) ∧
    ((∀ x, |f₀ x| ≤ 1) → (∀ x, |f₂ x| ≤ 1) → (∀ x, |f₃ x| ≤ 1) →
      Λ ^ 8 ≤ (Fintype.card R : ℝ) ^ 12 * U3 f₁) ∧
    ((∀ x, |f₀ x| ≤ 1) → (∀ x, |f₁ x| ≤ 1) → (∀ x, |f₃ x| ≤ 1) →
      Λ ^ 8 ≤ (Fintype.card R : ℝ) ^ 12 * U3 f₂) ∧
    ((∀ x, |f₀ x| ≤ 1) → (∀ x, |f₁ x| ≤ 1) → (∀ x, |f₂ x| ≤ 1) →
      Λ ^ 8 ≤ (Fintype.card R : ℝ) ^ 12 * U3 f₃) := by
  intro Λ U3
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hf₁ hf₂ hf₃
    have heq : Λ = ∑ u : R, ∑ d : R,
        f₀ u * f₁ (u + 1 * d) * f₂ (u + 2 * d) * f₃ (u + 3 * d) := by
      simp [Λ]
    rw [heq]
    exact gvn_ring f₀ f₁ f₂ f₃ 1 2 3 h1 h2 h3 hf₁ hf₂ hf₃
  · intro hf₀ hf₂ hf₃
    have heq : Λ = ∑ u : R, ∑ d : R,
        f₁ u * f₀ (u + (-1) * d) * f₂ (u + 1 * d) * f₃ (u + 2 * d) := by
      dsimp only [Λ]
      rw [Finset.sum_comm]
      trans ∑ d : R, ∑ u : R, f₁ u * f₀ (u + (-1) * d) * f₂ (u + 1 * d) * f₃ (u + 2 * d)
      · refine Finset.sum_congr rfl fun d _ => ?_
        refine Fintype.sum_equiv (Equiv.addRight d) _ _ fun x => ?_
        change f₀ x * f₁ (x + d) * f₂ (x + 2 * d) * f₃ (x + 3 * d) =
          f₁ (x + d) * f₀ (x + d + (-1) * d) * f₂ (x + d + 1 * d) * f₃ (x + d + 2 * d)
        have e0 : x + d + (-1) * d = x := by ring
        have e2 : x + d + 1 * d = x + 2 * d := by ring
        have e3 : x + d + 2 * d = x + 3 * d := by ring
        rw [e0, e2, e3]; ring
      · exact Finset.sum_comm
    rw [heq]
    exact gvn_ring f₁ f₀ f₂ f₃ (-1) 1 2 h1.neg h1 h2 hf₀ hf₂ hf₃
  · intro hf₀ hf₁ hf₃
    have heq : Λ = ∑ u : R, ∑ d : R,
        f₂ u * f₀ (u + (-2) * d) * f₁ (u + (-1) * d) * f₃ (u + 1 * d) := by
      dsimp only [Λ]
      rw [Finset.sum_comm]
      trans ∑ d : R, ∑ u : R, f₂ u * f₀ (u + (-2) * d) * f₁ (u + (-1) * d) * f₃ (u + 1 * d)
      · refine Finset.sum_congr rfl fun d _ => ?_
        refine Fintype.sum_equiv (Equiv.addRight (2 * d)) _ _ fun x => ?_
        change f₀ x * f₁ (x + d) * f₂ (x + 2 * d) * f₃ (x + 3 * d) =
          f₂ (x + 2 * d) * f₀ (x + 2 * d + (-2) * d) * f₁ (x + 2 * d + (-1) * d) * f₃ (x + 2 * d + 1 * d)
        have e0 : x + 2 * d + (-2) * d = x := by ring
        have e1 : x + 2 * d + (-1) * d = x + d := by ring
        have e3 : x + 2 * d + 1 * d = x + 3 * d := by ring
        rw [e0, e1, e3]; ring
      · exact Finset.sum_comm
    rw [heq]
    exact gvn_ring f₂ f₀ f₁ f₃ (-2) (-1) 1 h2.neg h1.neg h1 hf₀ hf₁ hf₃
  · intro hf₀ hf₁ hf₂
    have heq : Λ = ∑ u : R, ∑ d : R,
        f₃ u * f₀ (u + (-3) * d) * f₁ (u + (-2) * d) * f₂ (u + (-1) * d) := by
      dsimp only [Λ]
      rw [Finset.sum_comm]
      trans ∑ d : R, ∑ u : R, f₃ u * f₀ (u + (-3) * d) * f₁ (u + (-2) * d) * f₂ (u + (-1) * d)
      · refine Finset.sum_congr rfl fun d _ => ?_
        refine Fintype.sum_equiv (Equiv.addRight (3 * d)) _ _ fun x => ?_
        change f₀ x * f₁ (x + d) * f₂ (x + 2 * d) * f₃ (x + 3 * d) =
          f₃ (x + 3 * d) * f₀ (x + 3 * d + (-3) * d) * f₁ (x + 3 * d + (-2) * d) * f₂ (x + 3 * d + (-1) * d)
        have e0 : x + 3 * d + (-3) * d = x := by ring
        have e1 : x + 3 * d + (-2) * d = x + d := by ring
        have e2 : x + 3 * d + (-1) * d = x + 2 * d := by ring
        rw [e0, e1, e2]; ring
      · exact Finset.sum_comm
    rw [heq]
    exact gvn_ring f₃ f₀ f₁ f₂ (-3) (-2) (-1) h3.neg h2.neg h1.neg hf₀ hf₁ hf₂

end RingGVN

/- ## Section 2: Embedding `[1, N]` into `ZMod (6 * N + 1)` without wraparound -/

section ZModEmbed

/-- Sum equality under an injective map `i : s → t` whose image covers all nonzero terms of `g`. -/
lemma sum_eq_sum_of_injOn_nonzero {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : Finset β} {f : α → ℝ} {g : β → ℝ} (i : α → β)
    (hmaps : ∀ a ∈ s, i a ∈ t)
    (hinj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, i a₁ = i a₂ → a₁ = a₂)
    (hsurj : ∀ b ∈ t, g b ≠ 0 → ∃ a ∈ s, i a = b)
    (hval : ∀ a ∈ s, f a = g (i a)) :
    ∑ a ∈ s, f a = ∑ b ∈ t, g b := by
  have hsub : s.image i ⊆ t := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hmaps a ha
  calc ∑ a ∈ s, f a
      = ∑ a ∈ s, g (i a) := Finset.sum_congr rfl hval
    _ = ∑ b ∈ s.image i, g b := (Finset.sum_image (fun a₁ ha₁ a₂ ha₂ h => hinj a₁ ha₁ a₂ ha₂ h)).symm
    _ = ∑ b ∈ t, g b := Finset.sum_subset hsub fun b hb hbnot => by
          by_contra hne
          obtain ⟨a, ha, rfl⟩ := hsurj b hb hne
          exact hbnot (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- Lift a function `ℤ → ℝ` supported on `[1, N]` to `ZMod (6 * N + 1)`. -/
def liftZ (N : ℕ) (f : ℤ → ℝ) (z : ZMod (6 * N + 1)) : ℝ :=
  if 1 ≤ z.val ∧ z.val ≤ N then f (z.val : ℤ) else 0

lemma isUnit_one_two_three (N : ℕ) :
    IsUnit (1 : ZMod (6 * N + 1)) ∧
    IsUnit (2 : ZMod (6 * N + 1)) ∧
    IsUnit (3 : ZMod (6 * N + 1)) := by
  refine ⟨isUnit_one, ?_, ?_⟩
  · rw [show (2 : ZMod (6 * N + 1)) = ((2 : ℕ) : ZMod (6 * N + 1)) by norm_num,
      ZMod.isUnit_iff_coprime]
    have hmod : (6 * N + 1) % 2 = 1 := by omega
    rw [Nat.Coprime, Nat.gcd_rec, hmod]
    norm_num
  · rw [show (3 : ZMod (6 * N + 1)) = ((3 : ℕ) : ZMod (6 * N + 1)) by norm_num,
      ZMod.isUnit_iff_coprime]
    have hmod : (6 * N + 1) % 3 = 1 := by omega
    rw [Nat.Coprime, Nat.gcd_rec, hmod]
    norm_num

lemma abs_liftZ_le_one (N : ℕ) {f : ℤ → ℝ} (hf : ∀ k, |f k| ≤ 1) (z : ZMod (6 * N + 1)) :
    |liftZ N f z| ≤ 1 := by
  unfold liftZ
  split_ifs
  · exact hf _
  · simp

lemma intCast_zmod_val_nonneg {M : ℕ} [NeZero M] {k : ℤ} (h0 : 0 ≤ k) (hM : k < (M : ℤ)) :
    ((k : ZMod M)).val = k.toNat := by
  have hk : k = (k.toNat : ℤ) := (Int.toNat_of_nonneg h0).symm
  rw [hk, Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), Int.toNat_natCast]

lemma intCast_zmod_val_neg {M : ℕ} [NeZero M] {k : ℤ} (hk : k < 0) (hM : -(M : ℤ) ≤ k) :
    ((k : ZMod M)).val = (k + M).toNat := by
  have h0 : 0 ≤ k + M := by omega
  have hlt : k + M < (M : ℤ) := by omega
  have heq : (k : ZMod M) = ((k + M : ℤ) : ZMod M) := by
    push_cast; simp
  rw [heq]
  exact intCast_zmod_val_nonneg h0 hlt

/-- For `k ∈ [-5N, 6N]`, `liftZ N f (k : ZMod (6*N + 1)) = f k` whenever `f` vanishes off `[1, N]`. -/
lemma liftZ_intCast_eq (N : ℕ) {f : ℤ → ℝ}
    (hsupp : ∀ k : ℤ, ¬ (1 ≤ k ∧ k ≤ (N : ℤ)) → f k = 0)
    {k : ℤ} (hlo : -(5 * (N : ℤ)) ≤ k) (hhi : k ≤ 6 * (N : ℤ)) :
    liftZ N f (k : ZMod (6 * N + 1)) = f k := by
  unfold liftZ
  by_cases h1 : 1 ≤ k ∧ k ≤ (N : ℤ)
  · have hv : ((k : ZMod (6 * N + 1))).val = k.toNat :=
      intCast_zmod_val_nonneg (by omega) (by omega)
    rw [hv]
    have hc : 1 ≤ k.toNat ∧ k.toNat ≤ N := by omega
    rw [if_pos hc]
    congr 1; omega
  · rw [hsupp k h1]
    split_ifs with h2
    · exfalso
      by_cases hk0 : 0 ≤ k
      · have hv : ((k : ZMod (6 * N + 1))).val = k.toNat :=
          intCast_zmod_val_nonneg hk0 (by omega)
        rw [hv] at h2; omega
      · have hv : ((k : ZMod (6 * N + 1))).val = (k + (6 * N + 1 : ℕ)).toNat :=
          intCast_zmod_val_neg (by omega) (by omega)
        rw [hv] at h2; omega
    · rfl

lemma intCast_injOn_Icc (N : ℕ) {a b : ℤ}
    (ha : -(N : ℤ) ≤ a ∧ a ≤ (N : ℤ)) (hb : -(N : ℤ) ≤ b ∧ b ≤ (N : ℤ))
    (heq : (a : ZMod (6 * N + 1)) = (b : ZMod (6 * N + 1))) : a = b := by
  have hdvd : ((6 * N + 1 : ℕ) : ℤ) ∣ (a - b) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr heq
  obtain ⟨q, hq⟩ := hdvd
  have hq' : a - b = (6 * (N : ℤ) + 1) * q := by simpa using hq
  have hab : -(2 * (N : ℤ)) ≤ a - b ∧ a - b ≤ 2 * (N : ℤ) := by omega
  have hq0 : q = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : q ≤ -1 := by omega
      nlinarith
    · have : 1 ≤ q := by omega
      nlinarith
  rw [hq0, mul_zero] at hq'
  omega

/-- Exact equality between the 4-AP sum over `ZMod (6*N + 1)` and over `ℤ`. -/
lemma sum_4ap_zmod_eq_int (N : ℕ) (f₀ f₁ f₂ f₃ : ℤ → ℝ)
    (hs0 : ∀ k, ¬ (1 ≤ k ∧ k ≤ (N : ℤ)) → f₀ k = 0)
    (hs1 : ∀ k, ¬ (1 ≤ k ∧ k ≤ (N : ℤ)) → f₁ k = 0)
    (hs2 : ∀ k, ¬ (1 ≤ k ∧ k ≤ (N : ℤ)) → f₂ k = 0)
    (hs3 : ∀ k, ¬ (1 ≤ k ∧ k ≤ (N : ℤ)) → f₃ k = 0) :
    ∑ x : ZMod (6 * N + 1), ∑ d : ZMod (6 * N + 1),
      liftZ N f₀ x * liftZ N f₁ (x + d) * liftZ N f₂ (x + 2 * d) * liftZ N f₃ (x + 3 * d) =
    ∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ d ∈ Finset.Icc (-(N : ℤ)) N,
      f₀ x * f₁ (x + d) * f₂ (x + 2 * d) * f₃ (x + 3 * d) := by
  let M := 6 * N + 1
  let Fz : ZMod M × ZMod M → ℝ := fun p =>
    liftZ N f₀ p.1 * liftZ N f₁ (p.1 + p.2) * liftZ N f₂ (p.1 + 2 * p.2) *
      liftZ N f₃ (p.1 + 3 * p.2)
  let Fi : ℤ × ℤ → ℝ := fun p =>
    f₀ p.1 * f₁ (p.1 + p.2) * f₂ (p.1 + 2 * p.2) * f₃ (p.1 + 3 * p.2)
  have hL : (∑ x : ZMod M, ∑ d : ZMod M,
      liftZ N f₀ x * liftZ N f₁ (x + d) * liftZ N f₂ (x + 2 * d) * liftZ N f₃ (x + 3 * d)) =
      ∑ p ∈ (Finset.univ : Finset (ZMod M × ZMod M)), Fz p := by
    rw [← Fintype.sum_prod_type']
  have hR : (∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ d ∈ Finset.Icc (-(N : ℤ)) N,
      f₀ x * f₁ (x + d) * f₂ (x + 2 * d) * f₃ (x + 3 * d)) =
      ∑ p ∈ (Finset.Icc (1 : ℤ) N ×ˢ Finset.Icc (-(N : ℤ)) N), Fi p := by
    rw [Finset.sum_product]
  rw [hL, hR]
  symm
  refine sum_eq_sum_of_injOn_nonzero (fun p => ((p.1 : ZMod M), (p.2 : ZMod M))) ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_univ _
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
    have h1 := intCast_injOn_Icc N ⟨by omega, hp₁.1.2⟩ ⟨by omega, hp₂.1.2⟩ (congrArg Prod.fst heq)
    have h2 := intCast_injOn_Icc N hp₁.2 hp₂.2 (congrArg Prod.snd heq)
    exact Prod.ext h1 h2
  · intro q _ hq_ne
    -- Since `Fz q ≠ 0`, both `q.1` and `q.1 + q.2` have `.val ∈ [1, N]`.
    have hne0 : liftZ N f₀ q.1 ≠ 0 := by
      intro h; apply hq_ne; simp [Fz, h]
    have hne1 : liftZ N f₁ (q.1 + q.2) ≠ 0 := by
      intro h; apply hq_ne; simp [Fz, h]
    have hv0 : 1 ≤ q.1.val ∧ q.1.val ≤ N := by
      by_contra hc; exact hne0 (by simp [liftZ, hc])
    have hv1 : 1 ≤ (q.1 + q.2).val ∧ (q.1 + q.2).val ≤ N := by
      by_contra hc; exact hne1 (by simp [liftZ, hc])
    refine ⟨((q.1.val : ℤ), ((q.1 + q.2).val : ℤ) - (q.1.val : ℤ)), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_Icc]; omega
    · apply Prod.ext
      · simp
      · simp
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    have he0 : liftZ N f₀ (p.1 : ZMod M) = f₀ p.1 :=
      liftZ_intCast_eq N hs0 (by omega) (by omega)
    have he1 : liftZ N f₁ ((p.1 : ZMod M) + (p.2 : ZMod M)) = f₁ (p.1 + p.2) := by
      rw [← Int.cast_add]; exact liftZ_intCast_eq N hs1 (by omega) (by omega)
    have he2 : liftZ N f₂ ((p.1 : ZMod M) + 2 * (p.2 : ZMod M)) = f₂ (p.1 + 2 * p.2) := by
      have hc : (p.1 : ZMod M) + 2 * (p.2 : ZMod M) = ((p.1 + 2 * p.2 : ℤ) : ZMod M) := by
        push_cast; ring
      rw [hc]; exact liftZ_intCast_eq N hs2 (by omega) (by omega)
    have he3 : liftZ N f₃ ((p.1 : ZMod M) + 3 * (p.2 : ZMod M)) = f₃ (p.1 + 3 * p.2) := by
      have hc : (p.1 : ZMod M) + 3 * (p.2 : ZMod M) = ((p.1 + 3 * p.2 : ℤ) : ZMod M) := by
        push_cast; ring
      rw [hc]; exact liftZ_intCast_eq N hs3 (by omega) (by omega)
    simp only [Fi, Fz, he0, he1, he2, he3]

/-- Exact equality between the Gowers `U³` sum over `ZMod (6*N + 1)` and over `ℤ`. -/
lemma sum_u3_zmod_eq_int (N : ℕ) (f : ℤ → ℝ)
    (hsupp : ∀ k, ¬ (1 ≤ k ∧ k ≤ (N : ℤ)) → f k = 0) :
    ∑ x : ZMod (6 * N + 1), ∑ a : ZMod (6 * N + 1), ∑ b : ZMod (6 * N + 1),
      ∑ e : ZMod (6 * N + 1),
        liftZ N f x * liftZ N f (x + a) * liftZ N f (x + b) * liftZ N f (x + e) *
          liftZ N f (x + a + b) * liftZ N f (x + a + e) *
          liftZ N f (x + b + e) * liftZ N f (x + a + b + e) =
    ∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ a ∈ Finset.Icc (-(N : ℤ)) N, ∑ b ∈ Finset.Icc (-(N : ℤ)) N,
      ∑ e ∈ Finset.Icc (-(N : ℤ)) N,
        f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
          f (x + b + e) * f (x + a + b + e) := by
  let M := 6 * N + 1
  let Fz : ((ZMod M × ZMod M) × ZMod M) × ZMod M → ℝ := fun q =>
    let x := q.1.1.1; let a := q.1.1.2; let b := q.1.2; let e := q.2
    liftZ N f x * liftZ N f (x + a) * liftZ N f (x + b) * liftZ N f (x + e) *
      liftZ N f (x + a + b) * liftZ N f (x + a + e) *
      liftZ N f (x + b + e) * liftZ N f (x + a + b + e)
  let Fi : ((ℤ × ℤ) × ℤ) × ℤ → ℝ := fun p =>
    let x := p.1.1.1; let a := p.1.1.2; let b := p.1.2; let e := p.2
    f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
      f (x + b + e) * f (x + a + b + e)
  let dom := ((Finset.Icc (1 : ℤ) N ×ˢ Finset.Icc (-(N : ℤ)) N) ×ˢ
    Finset.Icc (-(N : ℤ)) N) ×ˢ Finset.Icc (-(N : ℤ)) N
  have hL : (∑ x : ZMod M, ∑ a : ZMod M, ∑ b : ZMod M, ∑ e : ZMod M,
      liftZ N f x * liftZ N f (x + a) * liftZ N f (x + b) * liftZ N f (x + e) *
        liftZ N f (x + a + b) * liftZ N f (x + a + e) *
        liftZ N f (x + b + e) * liftZ N f (x + a + b + e)) =
      ∑ q ∈ (Finset.univ : Finset (((ZMod M × ZMod M) × ZMod M) × ZMod M)), Fz q := by
    simp only [Fz, Fintype.sum_prod_type]
  have hR : (∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ a ∈ Finset.Icc (-(N : ℤ)) N,
      ∑ b ∈ Finset.Icc (-(N : ℤ)) N, ∑ e ∈ Finset.Icc (-(N : ℤ)) N,
        f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
          f (x + b + e) * f (x + a + b + e)) =
      ∑ p ∈ dom, Fi p := by
    simp only [dom, Fi, Finset.sum_product]
  rw [hL, hR]
  symm
  refine sum_eq_sum_of_injOn_nonzero
    (fun p => ((((p.1.1.1 : ZMod M), (p.1.1.2 : ZMod M)), (p.1.2 : ZMod M)), (p.2 : ZMod M)))
    ?_ ?_ ?_ ?_
  · intro p _; exact Finset.mem_univ _
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [dom, Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
    have h1 := intCast_injOn_Icc N ⟨by omega, hp₁.1.1.1.2⟩ ⟨by omega, hp₂.1.1.1.2⟩
      (congrArg (fun q => q.1.1.1) heq)
    have h2 := intCast_injOn_Icc N hp₁.1.1.2 hp₂.1.1.2 (congrArg (fun q => q.1.1.2) heq)
    have h3 := intCast_injOn_Icc N hp₁.1.2 hp₂.1.2 (congrArg (fun q => q.1.2) heq)
    have h4 := intCast_injOn_Icc N hp₁.2 hp₂.2 (congrArg (fun q => q.2) heq)
    exact Prod.ext (Prod.ext (Prod.ext h1 h2) h3) h4
  · intro q _ hq_ne
    have hne0 : liftZ N f q.1.1.1 ≠ 0 := by intro h; apply hq_ne; simp [Fz, h]
    have hne1 : liftZ N f (q.1.1.1 + q.1.1.2) ≠ 0 := by intro h; apply hq_ne; simp [Fz, h]
    have hne2 : liftZ N f (q.1.1.1 + q.1.2) ≠ 0 := by intro h; apply hq_ne; simp [Fz, h]
    have hne3 : liftZ N f (q.1.1.1 + q.2) ≠ 0 := by intro h; apply hq_ne; simp [Fz, h]
    have hv0 : 1 ≤ q.1.1.1.val ∧ q.1.1.1.val ≤ N := by
      by_contra hc; exact hne0 (by simp [liftZ, hc])
    have hv1 : 1 ≤ (q.1.1.1 + q.1.1.2).val ∧ (q.1.1.1 + q.1.1.2).val ≤ N := by
      by_contra hc; exact hne1 (by simp [liftZ, hc])
    have hv2 : 1 ≤ (q.1.1.1 + q.1.2).val ∧ (q.1.1.1 + q.1.2).val ≤ N := by
      by_contra hc; exact hne2 (by simp [liftZ, hc])
    have hv3 : 1 ≤ (q.1.1.1 + q.2).val ∧ (q.1.1.1 + q.2).val ≤ N := by
      by_contra hc; exact hne3 (by simp [liftZ, hc])
    let x₀ : ℤ := (q.1.1.1.val : ℤ)
    let a₀ : ℤ := ((q.1.1.1 + q.1.1.2).val : ℤ) - x₀
    let b₀ : ℤ := ((q.1.1.1 + q.1.2).val : ℤ) - x₀
    let e₀ : ℤ := ((q.1.1.1 + q.2).val : ℤ) - x₀
    refine ⟨(((x₀, a₀), b₀), e₀), ?_, ?_⟩
    · simp only [dom, Finset.mem_product, Finset.mem_Icc, x₀, a₀, b₀, e₀]; omega
    · refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) ?_
      · simp [x₀]
      · simp [x₀, a₀]
      · simp [x₀, b₀]
      · simp [x₀, e₀]
  · intro p hp
    simp only [dom, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨⟨hx1, hx2⟩, ⟨ha1, ha2⟩⟩, ⟨hb1, hb2⟩⟩, ⟨he1, he2⟩⟩ := hp
    have e0 : liftZ N f (p.1.1.1 : ZMod M) = f p.1.1.1 :=
      liftZ_intCast_eq N hsupp (by omega) (by omega)
    have e1 : liftZ N f ((p.1.1.1 : ZMod M) + (p.1.1.2 : ZMod M)) = f (p.1.1.1 + p.1.1.2) := by
      rw [← Int.cast_add]; exact liftZ_intCast_eq N hsupp (by omega) (by omega)
    have e2 : liftZ N f ((p.1.1.1 : ZMod M) + (p.1.2 : ZMod M)) = f (p.1.1.1 + p.1.2) := by
      rw [← Int.cast_add]; exact liftZ_intCast_eq N hsupp (by omega) (by omega)
    have e3 : liftZ N f ((p.1.1.1 : ZMod M) + (p.2 : ZMod M)) = f (p.1.1.1 + p.2) := by
      rw [← Int.cast_add]; exact liftZ_intCast_eq N hsupp (by omega) (by omega)
    have e4 : liftZ N f ((p.1.1.1 : ZMod M) + (p.1.1.2 : ZMod M) + (p.1.2 : ZMod M)) =
        f (p.1.1.1 + p.1.1.2 + p.1.2) := by
      rw [← Int.cast_add, ← Int.cast_add]; exact liftZ_intCast_eq N hsupp (by omega) (by omega)
    have e5 : liftZ N f ((p.1.1.1 : ZMod M) + (p.1.1.2 : ZMod M) + (p.2 : ZMod M)) =
        f (p.1.1.1 + p.1.1.2 + p.2) := by
      rw [← Int.cast_add, ← Int.cast_add]; exact liftZ_intCast_eq N hsupp (by omega) (by omega)
    have e6 : liftZ N f ((p.1.1.1 : ZMod M) + (p.1.2 : ZMod M) + (p.2 : ZMod M)) =
        f (p.1.1.1 + p.1.2 + p.2) := by
      rw [← Int.cast_add, ← Int.cast_add]; exact liftZ_intCast_eq N hsupp (by omega) (by omega)
    have e7 : liftZ N f
        ((p.1.1.1 : ZMod M) + (p.1.1.2 : ZMod M) + (p.1.2 : ZMod M) + (p.2 : ZMod M)) =
        f (p.1.1.1 + p.1.1.2 + p.1.2 + p.2) := by
      rw [← Int.cast_add, ← Int.cast_add, ← Int.cast_add]
      exact liftZ_intCast_eq N hsupp (by omega) (by omega)
    simp only [Fi, Fz, e0, e1, e2, e3, e4, e5, e6, e7]

end ZModEmbed

/- ## Section 3: Counting 4-APs and closing `H1` -/

/-- Helper to extract `|T| < (1 / 1000) * α^4 * N^2` from an 8th-power bound. -/
lemma abs_lt_of_pow8_bound {N : ℕ} {α U3 T : ℝ}
    (hN : 1 ≤ N) (hα : 0 < α)
    (hU3 : U3 < (1 / ((1000 : ℝ) ^ 8 * 7 ^ 12)) * α ^ 32 * (N : ℝ) ^ 4)
    (hT8 : T ^ 8 ≤ (Fintype.card (ZMod (6 * N + 1)) : ℝ) ^ 12 * U3) :
    |T| < (1 / 1000 : ℝ) * α ^ 4 * (N : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hM_le : (Fintype.card (ZMod (6 * N + 1)) : ℝ) ≤ 7 * (N : ℝ) := by
    rw [ZMod.card]
    have : 6 * N + 1 ≤ 7 * N := by omega
    exact_mod_cast this
  have hU3_nn : 0 ≤ U3 := by
    have h1 : 0 ≤ (Fintype.card (ZMod (6 * N + 1)) : ℝ) ^ 12 * U3 :=
      le_trans (by positivity : (0 : ℝ) ≤ T ^ 8) hT8
    have hMpos : (0 : ℝ) < (Fintype.card (ZMod (6 * N + 1)) : ℝ) ^ 12 := by
      rw [ZMod.card]; positivity
    exact nonneg_of_mul_nonneg_right h1 hMpos
  have hM12 : (Fintype.card (ZMod (6 * N + 1)) : ℝ) ^ 12 ≤ (7 * (N : ℝ)) ^ 12 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hM_le 12
  have hlt8 : |T| ^ 8 < ((1 / 1000 : ℝ) * α ^ 4 * (N : ℝ) ^ 2) ^ 8 := by
    have habs8 : |T| ^ 8 = T ^ 8 := by
      rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, pow_mul, sq_abs]
    rw [habs8]
    calc T ^ 8
        ≤ (Fintype.card (ZMod (6 * N + 1)) : ℝ) ^ 12 * U3 := hT8
      _ ≤ (7 * (N : ℝ)) ^ 12 * U3 := mul_le_mul_of_nonneg_right hM12 hU3_nn
      _ < (7 * (N : ℝ)) ^ 12 * ((1 / ((1000 : ℝ) ^ 8 * 7 ^ 12)) * α ^ 32 * (N : ℝ) ^ 4) :=
          mul_lt_mul_of_pos_left hU3 (by positivity)
      _ = ((1 / 1000 : ℝ) * α ^ 4 * (N : ℝ) ^ 2) ^ 8 := by ring
  by_contra hnot
  push Not at hnot
  have hrhs_nn : 0 ≤ (1 / 1000 : ℝ) * α ^ 4 * (N : ℝ) ^ 2 := by positivity
  have hge8 := pow_le_pow_left₀ hrhs_nn hnot 8
  linarith

/-- The integer 4-AP multilinear form over `x ∈ [1, N]`, `d ∈ [-N, N]`. -/
def lam4 (N : ℕ) (f₀ f₁ f₂ f₃ : ℤ → ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ d ∈ Finset.Icc (-(N : ℤ)) N,
    f₀ x * f₁ (x + d) * f₂ (x + 2 * d) * f₃ (x + 3 * d)

lemma lam4_telescope (N : ℕ) (g h : ℤ → ℝ) :
    let f := fun x => g x - h x
    lam4 N g g g g - lam4 N h h h h =
      lam4 N f g g g + lam4 N h f g g + lam4 N h h f g + lam4 N h h h f := by
  intro f
  simp only [lam4, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun d _ => ?_
  dsimp only [f]
  ring

lemma log_cubed_le (N : ℕ) (hN : 1 ≤ N) :
    (Real.log (N : ℝ)) ^ 3 ≤ 27 * (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  let t : ℝ := (N : ℝ) ^ ((1 : ℝ) / 3)
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hNpos _
  have ht3 : t ^ 3 = (N : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num
  have hlog_eq : Real.log (N : ℝ) = 3 * Real.log t := by
    rw [← ht3, Real.log_pow]
    norm_num
  have hlog_le : Real.log t ≤ t := by
    have h1 := Real.log_le_sub_one_of_pos ht_pos
    linarith
  have hlog_nn : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have h3t : Real.log (N : ℝ) ≤ 3 * t := by linarith
  calc (Real.log (N : ℝ)) ^ 3
      ≤ (3 * t) ^ 3 := pow_le_pow_left₀ hlog_nn h3t 3
    _ = 27 * t ^ 3 := by ring
    _ = 27 * (N : ℝ) := by rw [ht3]

end Erdos3R2H1

theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_green_tao_R2.H1 := by
  open Erdos3R2H1 Finset BigOperators in
  refine ⟨32, 1 / ((1000 : ℝ) ^ 8 * 7 ^ 12), by positivity, 1, by norm_num, 100, by norm_num, 100, ?_⟩
  intro N hN S hS hfree hU3
  set α : ℝ := (S.card : ℝ) / (N : ℝ)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hS_le_N : S.card ≤ N := by
    have h1 := Finset.card_le_card hS
    simpa [Nat.card_Icc] using h1
  have hα_nn : 0 ≤ α := by positivity
  have hα_le1 : α ≤ 1 := by
    dsimp only [α]
    rw [div_le_one hNpos]
    exact_mod_cast hS_le_N
  -- If `S` is empty, the target bound is trivial.
  by_cases hS0 : S.card = 0
  · rw [hS0, Nat.cast_zero]
    have hlog_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    exact mul_nonneg (by norm_num) (mul_nonneg hNpos.le (Real.rpow_nonneg hlog_nn _))
  have hα_pos : 0 < α := div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hS0)) hNpos
  -- Define `g`, `h`, and `f = g - h` matching the definition in `H1`.
  let g : ℤ → ℝ := fun x => if 0 < x ∧ x.toNat ∈ S then 1 else 0
  let h : ℤ → ℝ := fun x => if 0 < x ∧ x ≤ (N : ℤ) then α else 0
  let f : ℤ → ℝ := fun x => g x - h x
  have hsupp_g : ∀ k : ℤ, ¬ (1 ≤ k ∧ k ≤ (N : ℤ)) → g k = 0 := by
    intro k hk
    dsimp only [g]
    rw [if_neg]
    rintro ⟨hkpos, hkS⟩
    have hmem := Finset.mem_Icc.mp (hS hkS)
    exact hk ⟨by omega, by omega⟩
  have hsupp_h : ∀ k : ℤ, ¬ (1 ≤ k ∧ k ≤ (N : ℤ)) → h k = 0 := by
    intro k hk
    dsimp only [h]
    rw [if_neg]; omega
  have hsupp_f : ∀ k : ℤ, ¬ (1 ≤ k ∧ k ≤ (N : ℤ)) → f k = 0 := by
    intro k hk
    dsimp only [f]; rw [hsupp_g k hk, hsupp_h k hk, sub_zero]
  have habs_g : ∀ k : ℤ, |g k| ≤ 1 := by
    intro k; dsimp only [g]; split_ifs <;> norm_num
  have habs_h : ∀ k : ℤ, |h k| ≤ 1 := by
    intro k; dsimp only [h]; split_ifs
    · rw [abs_of_nonneg hα_nn]; exact hα_le1
    · norm_num
  -- Step 1: `lam4 N g g g g = S.card` because `S` is 4-AP-free.
  have hlam_g : lam4 N g g g g = (S.card : ℝ) := by
    unfold lam4
    have hinner : ∀ x ∈ Finset.Icc (1 : ℤ) N,
        (∑ d ∈ Finset.Icc (-(N : ℤ)) N, g x * g (x + d) * g (x + 2 * d) * g (x + 3 * d)) =
        g x := by
      intro x hx
      have h0mem : (0 : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := by
        simp only [Finset.mem_Icc]; omega
      rw [Finset.sum_eq_single (0 : ℤ)]
      · simp only [add_zero, mul_zero]
        dsimp only [g]; split_ifs <;> ring
      · intro d _ hd0
        by_contra hne
        have h0 : 0 < x ∧ x.toNat ∈ S := by
          by_contra hc; apply hne; simp [g, hc]
        have h1 : 0 < x + d ∧ (x + d).toNat ∈ S := by
          by_contra hc; apply hne; simp [g, hc]
        have h2 : 0 < x + 2 * d ∧ (x + 2 * d).toNat ∈ S := by
          by_contra hc; apply hne; simp [g, hc]
        have h3 : 0 < x + 3 * d ∧ (x + 3 * d).toNat ∈ S := by
          by_contra hc; apply hne; simp [g, hc]
        rcases lt_or_gt_of_ne hd0 with hd_neg | hd_pos
        · have hd' : 0 < (-d).toNat := by omega
          have e1 : (x + 3 * d).toNat + (-d).toNat = (x + 2 * d).toNat := by omega
          have e2 : (x + 3 * d).toNat + 2 * (-d).toNat = (x + d).toNat := by omega
          have e3 : (x + 3 * d).toNat + 3 * (-d).toNat = x.toNat := by omega
          exact hfree (x + 3 * d).toNat (-d).toNat hd' h3.2 (e1 ▸ h2.2) (e2 ▸ h1.2) (e3 ▸ h0.2)
        · have hd' : 0 < d.toNat := by omega
          have e1 : x.toNat + d.toNat = (x + d).toNat := by omega
          have e2 : x.toNat + 2 * d.toNat = (x + 2 * d).toNat := by omega
          have e3 : x.toNat + 3 * d.toNat = (x + 3 * d).toNat := by omega
          exact hfree x.toNat d.toNat hd' h0.2 (e1 ▸ h1.2) (e2 ▸ h2.2) (e3 ▸ h3.2)
      · intro habs; exact (habs h0mem).elim
    rw [Finset.sum_congr rfl hinner]
    -- `∑ x ∈ Icc 1 N, g x = S.card`
    have hsum_g : ∑ x ∈ Finset.Icc (1 : ℤ) N, g x =
        ((Finset.Icc (1 : ℤ) N).filter fun x => 0 < x ∧ x.toNat ∈ S).card := by
      dsimp only [g]
      rw [Finset.sum_boole]
    rw [hsum_g]
    congr 1
    refine Finset.card_bij (fun x _ => x.toNat) ?_ ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2.2
    · intro x₁ hx₁ x₂ hx₂ heq
      have h1 := (Finset.mem_filter.mp hx₁).2.1
      have h2 := (Finset.mem_filter.mp hx₂).2.1
      omega
    · intro n hn
      have hmn := Finset.mem_Icc.mp (hS hn)
      refine ⟨(n : ℤ), Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ?_⟩,
        by simp⟩
      simpa using hn
  -- Step 2: `lam4 N h h h h ≥ (1 / 20) * α^4 * N^2`.
  have hlam_h : (1 / 20 : ℝ) * α ^ 4 * (N : ℝ) ^ 2 ≤ lam4 N h h h h := by
    unfold lam4
    have hterm_nn : ∀ x ∈ Finset.Icc (1 : ℤ) N, ∀ d ∈ Finset.Icc (-(N : ℤ)) N,
        0 ≤ h x * h (x + d) * h (x + 2 * d) * h (x + 3 * d) := by
      intro x _ d _
      have hh : ∀ z, 0 ≤ h z := fun z => by dsimp only [h]; split_ifs <;> linarith
      exact mul_nonneg (mul_nonneg (mul_nonneg (hh _) (hh _)) (hh _)) (hh _)
    let Q : ℕ := N / 4
    have hQsub1 : Finset.Icc (1 : ℤ) Q ⊆ Finset.Icc (1 : ℤ) N :=
      Finset.Icc_subset_Icc_right (by omega)
    have hQsub2 : Finset.Icc (1 : ℤ) Q ⊆ Finset.Icc (-(N : ℤ)) N :=
      Finset.Icc_subset_Icc (by omega) (by omega)
    have hge1 :
        (∑ x ∈ Finset.Icc (1 : ℤ) Q, ∑ d ∈ Finset.Icc (1 : ℤ) Q,
          h x * h (x + d) * h (x + 2 * d) * h (x + 3 * d)) ≤
        ∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ d ∈ Finset.Icc (-(N : ℤ)) N,
          h x * h (x + d) * h (x + 2 * d) * h (x + 3 * d) := by
      refine (Finset.sum_le_sum fun x hx =>
        Finset.sum_le_sum_of_subset_of_nonneg hQsub2 (fun d hd _ => hterm_nn x (hQsub1 hx) d hd)).trans ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg hQsub1
        (fun x hx _ => Finset.sum_nonneg fun d hd => hterm_nn x hx d hd)
    have hQval :
        (∑ x ∈ Finset.Icc (1 : ℤ) Q, ∑ d ∈ Finset.Icc (1 : ℤ) Q,
          h x * h (x + d) * h (x + 2 * d) * h (x + 3 * d)) =
        (Q : ℝ) ^ 2 * α ^ 4 := by
      have hconst : ∀ x ∈ Finset.Icc (1 : ℤ) Q, ∀ d ∈ Finset.Icc (1 : ℤ) Q,
          h x * h (x + d) * h (x + 2 * d) * h (x + 3 * d) = α ^ 4 := by
        intro x hx d hd
        simp only [Finset.mem_Icc] at hx hd
        have c0 : 0 < x ∧ x ≤ (N : ℤ) := by omega
        have c1 : 0 < x + d ∧ x + d ≤ (N : ℤ) := by omega
        have c2 : 0 < x + 2 * d ∧ x + 2 * d ≤ (N : ℤ) := by omega
        have c3 : 0 < x + 3 * d ∧ x + 3 * d ≤ (N : ℤ) := by omega
        dsimp only [h]
        rw [if_pos c0, if_pos c1, if_pos c2, if_pos c3]; ring
      calc (∑ x ∈ Finset.Icc (1 : ℤ) Q, ∑ d ∈ Finset.Icc (1 : ℤ) Q,
            h x * h (x + d) * h (x + 2 * d) * h (x + 3 * d))
          = ∑ x ∈ Finset.Icc (1 : ℤ) Q, ∑ _d ∈ Finset.Icc (1 : ℤ) Q, α ^ 4 :=
            Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun d hd => hconst x hx d hd
        _ = ((Finset.Icc (1 : ℤ) Q).card : ℝ) * (((Finset.Icc (1 : ℤ) Q).card : ℝ) * α ^ 4) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ = (Q : ℝ) ^ 2 * α ^ 4 := by
            have hc : (Finset.Icc (1 : ℤ) Q).card = Q := by
              rw [Int.card_Icc]; omega
            rw [hc]; ring
    have hQlb : (N : ℝ) ^ 2 / 20 ≤ (Q : ℝ) ^ 2 := by
      have hQnat : N ≤ 4 * Q + 3 := by dsimp [Q]; omega
      have hQr : (N : ℝ) ≤ 4 * (Q : ℝ) + 3 := by exact_mod_cast hQnat
      have hN100 : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith
    calc (1 / 20 : ℝ) * α ^ 4 * (N : ℝ) ^ 2
        = ((N : ℝ) ^ 2 / 20) * α ^ 4 := by ring
      _ ≤ (Q : ℝ) ^ 2 * α ^ 4 := mul_le_mul_of_nonneg_right hQlb (by positivity)
      _ ≤ _ := hQval ▸ hge1
  -- Step 3: Bound each of the 4 telescoping terms using `gvn_4ap_pos`.
  set U3_int : ℝ :=
    ∑ x ∈ Finset.Icc (1 : ℤ) N, ∑ a ∈ Finset.Icc (-(N : ℤ)) N, ∑ b ∈ Finset.Icc (-(N : ℤ)) N,
      ∑ e ∈ Finset.Icc (-(N : ℤ)) N,
        f x * f (x + a) * f (x + b) * f (x + e) * f (x + a + b) * f (x + a + e) *
          f (x + b + e) * f (x + a + b + e)
  have hU3_lt : U3_int < (1 / ((1000 : ℝ) ^ 8 * 7 ^ 12)) * α ^ 32 * (N : ℝ) ^ 4 := hU3
  obtain ⟨hu1, hu2, hu3⟩ := isUnit_one_two_three N
  have hU3_eq : (∑ x : ZMod (6 * N + 1), ∑ a : ZMod (6 * N + 1), ∑ b : ZMod (6 * N + 1),
      ∑ e : ZMod (6 * N + 1),
        liftZ N f x * liftZ N f (x + a) * liftZ N f (x + b) * liftZ N f (x + e) *
          liftZ N f (x + a + b) * liftZ N f (x + a + e) *
          liftZ N f (x + b + e) * liftZ N f (x + a + b + e)) = U3_int :=
    sum_u3_zmod_eq_int N f hsupp_f
  have hT0 : |lam4 N f g g g| < (1 / 1000 : ℝ) * α ^ 4 * (N : ℝ) ^ 2 := by
    apply abs_lt_of_pow8_bound (by omega : 1 ≤ N) hα_pos hU3_lt
    unfold lam4
    rw [← sum_4ap_zmod_eq_int N f g g g hsupp_f hsupp_g hsupp_g hsupp_g, ← hU3_eq]
    exact (gvn_4ap_pos (liftZ N f) (liftZ N g) (liftZ N g) (liftZ N g) hu1 hu2 hu3).1
      (abs_liftZ_le_one N habs_g) (abs_liftZ_le_one N habs_g) (abs_liftZ_le_one N habs_g)
  have hT1 : |lam4 N h f g g| < (1 / 1000 : ℝ) * α ^ 4 * (N : ℝ) ^ 2 := by
    apply abs_lt_of_pow8_bound (by omega : 1 ≤ N) hα_pos hU3_lt
    unfold lam4
    rw [← sum_4ap_zmod_eq_int N h f g g hsupp_h hsupp_f hsupp_g hsupp_g, ← hU3_eq]
    exact (gvn_4ap_pos (liftZ N h) (liftZ N f) (liftZ N g) (liftZ N g) hu1 hu2 hu3).2.1
      (abs_liftZ_le_one N habs_h) (abs_liftZ_le_one N habs_g) (abs_liftZ_le_one N habs_g)
  have hT2 : |lam4 N h h f g| < (1 / 1000 : ℝ) * α ^ 4 * (N : ℝ) ^ 2 := by
    apply abs_lt_of_pow8_bound (by omega : 1 ≤ N) hα_pos hU3_lt
    unfold lam4
    rw [← sum_4ap_zmod_eq_int N h h f g hsupp_h hsupp_h hsupp_f hsupp_g, ← hU3_eq]
    exact (gvn_4ap_pos (liftZ N h) (liftZ N h) (liftZ N f) (liftZ N g) hu1 hu2 hu3).2.2.1
      (abs_liftZ_le_one N habs_h) (abs_liftZ_le_one N habs_h) (abs_liftZ_le_one N habs_g)
  have hT3 : |lam4 N h h h f| < (1 / 1000 : ℝ) * α ^ 4 * (N : ℝ) ^ 2 := by
    apply abs_lt_of_pow8_bound (by omega : 1 ≤ N) hα_pos hU3_lt
    unfold lam4
    rw [← sum_4ap_zmod_eq_int N h h h f hsupp_h hsupp_h hsupp_h hsupp_f, ← hU3_eq]
    exact (gvn_4ap_pos (liftZ N h) (liftZ N h) (liftZ N h) (liftZ N f) hu1 hu2 hu3).2.2.2
      (abs_liftZ_le_one N habs_h) (abs_liftZ_le_one N habs_h) (abs_liftZ_le_one N habs_h)
  -- Step 4: Combine via telescoping to deduce `α^3 * N < 25`.
  have htel := lam4_telescope N g h
  have hS_eq : (S.card : ℝ) = α * (N : ℝ) := by
    dsimp only [α]; exact (div_mul_cancel₀ _ hNpos.ne').symm
  have hα3N : α ^ 3 * (N : ℝ) < 25 := by
    have hdiff : lam4 N h h h h - lam4 N g g g g ≤
        |lam4 N f g g g| + |lam4 N h f g g| + |lam4 N h h f g| + |lam4 N h h h f| := by
      have heq : lam4 N h h h h - lam4 N g g g g =
          -(lam4 N f g g g + lam4 N h f g g + lam4 N h h f g + lam4 N h h h f) := by
        linarith
      rw [heq]
      have a0 := neg_le_abs (lam4 N f g g g)
      have a1 := neg_le_abs (lam4 N h f g g)
      have a2 := neg_le_abs (lam4 N h h f g)
      have a3 := neg_le_abs (lam4 N h h h f)
      linarith
    have hmain : (46 / 1000 : ℝ) * α ^ 4 * (N : ℝ) ^ 2 < α * (N : ℝ) := by
      rw [hlam_g, hS_eq] at hdiff
      linarith
    have hfac : (46 / 1000 : ℝ) * (α ^ 3 * (N : ℝ)) * (α * (N : ℝ)) < 1 * (α * (N : ℝ)) := by
      linarith
    have h1 := lt_of_mul_lt_mul_right hfac (mul_nonneg hα_nn hNpos.le)
    linarith
  -- Step 5: Deduce `|S| ≤ 100 * N * (Real.log N)^(-1)`.
  have hlog_pos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlog3 := log_cubed_le N (by omega)
  have hprod3 : (α * Real.log (N : ℝ)) ^ 3 < 100 ^ 3 := by
    calc (α * Real.log (N : ℝ)) ^ 3
        = α ^ 3 * (Real.log (N : ℝ)) ^ 3 := by ring
      _ ≤ α ^ 3 * (27 * (N : ℝ)) := mul_le_mul_of_nonneg_left hlog3 (pow_nonneg hα_nn 3)
      _ = 27 * (α ^ 3 * (N : ℝ)) := by ring
      _ < 27 * 25 := by linarith
      _ < 100 ^ 3 := by norm_num
  have hprod : α * Real.log (N : ℝ) ≤ 100 := by
    by_contra! hgt
    have := pow_lt_pow_left₀ hgt (by norm_num) (by norm_num : 3 ≠ 0)
    linarith
  have hα_le : α ≤ 100 * (Real.log (N : ℝ)) ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hlog_pos]
    exact hprod
  rw [hS_eq]
  calc α * (N : ℝ)
      ≤ (100 * (Real.log (N : ℝ)) ^ (-(1 : ℝ))) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hα_le hNpos.le
    _ = 100 * ((N : ℝ) * (Real.log (N : ℝ)) ^ (-(1 : ℝ))) := by ring
