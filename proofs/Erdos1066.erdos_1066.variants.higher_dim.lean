import FormalConjectures.ErdosProblems.«1066»
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.BilinearForm.Basic

-- Credit: @cjchaffin
-- The finite-field pairing is the Kerdock construction of Kantor and Williams, §5.2.
-- https://pages.uoregon.edu/kantor/PAPERS/KWfinal.pdf
-- De Caen's equiangular-line theorem gives a separate paper proof of the same obstruction.
-- https://doi.org/10.37236/1533
-- Mathematical research: GPT-6.2 Astra. Lean formalization: GPT-6.2 Sol.

/-! The pinned independent-set bound for a two-angle configuration. -/

open Finset
open scoped InnerProductSpace

namespace Erdos1066

theorem gDim_le_of_configuration {d k : ℕ} (X : Finset (EuclideanSpace ℝ (Fin d)))
    (hX : (X : Set (EuclideanSpace ℝ (Fin d))).Pairwise (fun x y => 1 ≤ dist x y))
    (hbound : ∀ Y ⊆ X,
      (Y : Set (EuclideanSpace ℝ (Fin d))).Pairwise (fun x y => 1 < dist x y) → Y.card ≤ k) :
    gDim d X.card ≤ k := by
  unfold gDim
  apply csSup_le'
  intro m hm
  obtain ⟨Y, hYX, hmY, hY⟩ := hm X rfl hX
  exact hmY.trans (hbound Y hYX hY)

theorem card_mul_le_of_inner_pairs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Y : Finset E) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hdiag : ∀ x ∈ Y, ⟪x, x⟫_ℝ = b)
    (hoff : (Y : Set E).Pairwise (fun x y => ⟪x, y⟫_ℝ = -a)) :
    (Y.card : ℝ) * a ≤ b + a := by
  classical
  by_cases hY : Y.Nonempty
  · have hrow (x : E) (hx : x ∈ Y) :
        (∑ y ∈ Y, ⟪x, y⟫_ℝ) = b + a - (Y.card : ℝ) * a := by
      calc
        _ = ∑ y ∈ Y, ((if y = x then b + a else 0) - a) := by
          refine sum_congr rfl fun y hy => ?_
          by_cases h : y = x
          · subst y
            rw [if_pos rfl, hdiag x hx]
            ring
          · rw [hoff hx hy (Ne.symm h), if_neg h, zero_sub]
        _ = _ := by
          rw [sum_sub_distrib, sum_ite_eq' Y x (fun _ => b + a), if_pos hx,
            sum_const, nsmul_eq_mul]
    have hp : 0 ≤ ⟪∑ x ∈ Y, x, ∑ y ∈ Y, y⟫_ℝ := real_inner_self_nonneg
    rw [sum_inner] at hp
    simp_rw [inner_sum] at hp
    rw [sum_congr rfl hrow, sum_const, nsmul_eq_mul] at hp
    have hcard : (0 : ℝ) < (Y.card : ℝ) := by
      exact_mod_cast card_pos.mpr hY
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hp hcard)
  · have he : Y = ∅ := not_nonempty_iff_eq_empty.mp hY
    simp [he, add_nonneg hb ha.le]

theorem gDim_le_of_two_angles {d k : ℕ} (X : Finset (EuclideanSpace ℝ (Fin d)))
    {a b : ℝ} (ha : 0 < a)
    (hb : b = 1 / 2 + a) (hk : b + a ≤ (k : ℝ) * a)
    (hdiag : ∀ x ∈ X, ⟪x, x⟫_ℝ = b)
    (hoff : (X : Set (EuclideanSpace ℝ (Fin d))).Pairwise
      (fun x y => ⟪x, y⟫_ℝ = a ∨ ⟪x, y⟫_ℝ = -a)) :
    gDim d X.card ≤ k := by
  have hdist (x y : EuclideanSpace ℝ (Fin d)) (hx : x ∈ X) (hy : y ∈ X) :
      (dist x y) ^ 2 = 2 * b - 2 * ⟪x, y⟫_ℝ := by
    rw [dist_eq_norm, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, hdiag x hx, hdiag y hy]
    ring
  apply gDim_le_of_configuration X
  · intro x hx y hy hne
    have hp := dist_nonneg (x := x) (y := y)
    rcases hoff hx hy hne with h | h <;>
      have hd := hdist x y hx hy <;> rw [h, hb] at hd <;> nlinarith
  · intro Y hYX hY
    have hneg : (Y : Set (EuclideanSpace ℝ (Fin d))).Pairwise
        (fun x y => ⟪x, y⟫_ℝ = -a) := by
      intro x hx y hy hne
      rcases hoff (hYX hx) (hYX hy) hne with h | h
      · have hd := hdist x y (hYX hx) (hYX hy)
        have hd' := hY hx hy hne
        rw [h, hb] at hd
        nlinarith
      · exact h
    have hmul := card_mul_le_of_inner_pairs Y ha (by rw [hb]; positivity)
      (fun x hx => hdiag x (hYX hx)) hneg
    exact_mod_cast (le_of_mul_le_mul_right (hmul.trans hk) ha)


end Erdos1066

/- Walsh sums of linear and nonsingular quadratic binary functions. -/

open Finset
open scoped BigOperators

namespace Erdos1066

noncomputable def binarySign (x : ZMod 2) : ℝ := if x = 0 then 1 else -1

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by simp [binarySign]

@[simp] theorem binarySign_one : binarySign 1 = -1 := by
  have h : (1 : ZMod 2) ≠ 0 := one_ne_zero
  simp [binarySign, h]

theorem binarySign_add (x y : ZMod 2) : binarySign (x + y) = binarySign x * binarySign y := by
  have cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
    have hz := ZMod.val_lt z
    rcases (show z.val = 0 ∨ z.val = 1 by omega) with h | h
    · exact Or.inl (by simpa [h] using (ZMod.natCast_zmod_val z).symm)
    · exact Or.inr (by simpa [h] using (ZMod.natCast_zmod_val z).symm)
  rcases cases x with rfl | rfl <;> rcases cases y with rfl | rfl <;>
    simp [CharTwo.add_self_eq_zero]

theorem sum_binarySign_eq_zero_of_translation {V : Type*} [Fintype V] [AddGroup V]
    (f : V → ZMod 2) (h : V) (hf : ∀ x, f (x + h) = f x + 1) :
    (∑ x : V, binarySign (f x)) = 0 := by
  have hsum := Equiv.sum_comp (Equiv.addRight h) (fun x => binarySign (f x))
  change (∑ x : V, binarySign (f (x + h))) = _ at hsum
  simp_rw [hf, binarySign_add, binarySign_one, mul_neg, mul_one, sum_neg_distrib] at hsum
  linarith

theorem walsh_sq_of_nondegenerate {V : Type*} [Fintype V] [AddGroup V]
    (q : V → ZMod 2) (B : V → V → ZMod 2)
    (q0 : q 0 = 0) (B0 : ∀ x, B x 0 = 0)
    (hq : ∀ x h, q (x + h) = q x + q h + B x h)
    (hB : ∀ x y h, B (x + y) h = B x h + B y h)
    (hne : ∀ h, h ≠ 0 → ∃ y, B y h = 1) :
    (∑ x : V, binarySign (q x)) ^ 2 = (Fintype.card V : ℝ) := by
  classical
  calc
    _ = ∑ x : V, ∑ y : V, binarySign (q x) * binarySign (q y) := by
      simp only [pow_two, sum_mul, mul_sum]
      simp only [mul_comm]
    _ = ∑ x : V, ∑ h : V, binarySign (q x) * binarySign (q (x + h)) := by
      refine sum_congr rfl fun x _ => ?_
      exact (Equiv.sum_comp (Equiv.addLeft x) (fun y => binarySign (q x) * binarySign (q y))).symm
    _ = ∑ x : V, ∑ h : V, binarySign (q h) * binarySign (B x h) := by
      refine sum_congr rfl fun x _ => sum_congr rfl fun h _ => ?_
      rw [← binarySign_add, hq]
      have hqadd : q x + (q x + q h + B x h) = q h + B x h := by
        calc
          _ = (q x + q x) + (q h + B x h) := by abel
          _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]
      rw [hqadd, binarySign_add]
    _ = (Fintype.card V : ℝ) := by
      rw [sum_comm]
      simp_rw [← mul_sum]
      have ht (h : V) : (∑ x : V, binarySign (B x h)) =
          if h = 0 then (Fintype.card V : ℝ) else 0 := by
        split_ifs with hz
        · simp [hz, B0]
        · obtain ⟨y, hy⟩ := hne h hz
          exact sum_binarySign_eq_zero_of_translation _ y (fun x => by rw [hB, hy])
      simp [ht, q0, mul_ite]


end Erdos1066

/- A quadratic function with a prescribed symmetric alternating binary polarization. -/

namespace Erdos1066

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem exists_quadratic_with_polar {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hdiag : ∀ x, B x x = 0)
    (hsymm : ∀ x y, B x y = B y x) :
    ∃ Q : V → ZMod 2, Q 0 = 0 ∧ ∀ x y, Q (x + y) = Q x + Q y + B x y := by
  classical
  let e := Module.finBasis (ZMod 2) V
  let M : Matrix (Fin (Module.finrank (ZMod 2) V)) (Fin (Module.finrank (ZMod 2) V)) (ZMod 2) :=
    fun i j => if i < j then B (e i) (e j) else 0
  let C := Matrix.toBilin e M
  have hentry (i j : Fin (Module.finrank (ZMod 2) V)) : C (e i) (e j) = M i j := by
    have h := congrArg (fun D => D i j) (LinearMap.BilinForm.toMatrix_toBilin e M)
    simpa only [LinearMap.BilinForm.toMatrix_apply] using h
  have hform : C + C.flip = B := by
    apply (LinearMap.BilinForm.toMatrix e).injective
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply]
    change C (e i) (e j) + C (e j) (e i) = B (e i) (e j)
    simp only [hentry, M]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst j
      simp [hdiag]
    · simp [h, not_lt_of_gt h, hsymm (e j) (e i)]
  refine ⟨fun x => C x x, by simp, fun x y => ?_⟩
  have hxy := congrArg (fun D : LinearMap.BilinForm (ZMod 2) V => D x y) hform
  change C x y + C y x = B x y at hxy
  simp only [map_add, LinearMap.add_apply]
  rw [← hxy]
  abel


end Erdos1066

/- Explicit alternating binary forms from an odd degree extension of the binary field. -/

open Finset

namespace Erdos1066.Kerdock

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev F (m : ℕ) := GaloisField 2 m
abbrev V (m : ℕ) := F m × ZMod 2

noncomputable abbrev tr (m : ℕ) : F m →ₗ[ZMod 2] ZMod 2 :=
  Algebra.trace (ZMod 2) (F m)

theorem bit_cases (r : ZMod 2) : r = 0 ∨ r = 1 := by
  have hr := ZMod.val_lt r
  rcases (show r.val = 0 ∨ r.val = 1 by omega) with h | h
  · exact Or.inl (by simpa [h] using (ZMod.natCast_zmod_val r).symm)
  · exact Or.inr (by simpa [h] using (ZMod.natCast_zmod_val r).symm)

theorem bit_sq (r : ZMod 2) : r ^ 2 = r := by rcases bit_cases r with rfl | rfl <;> simp

theorem tr_algebraMap {m : ℕ} (hm : Odd m) (z : ZMod 2) :
    tr m (algebraMap (ZMod 2) (F m) z) = z := by
  have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hm; omega
  rw [tr, Algebra.trace_algebraMap, GaloisField.finrank 2 hm0]
  obtain ⟨k, rfl⟩ := hm
  rw [add_nsmul, mul_nsmul, two_nsmul, CharTwo.add_self_eq_zero, nsmul_zero, zero_add,
    one_nsmul]

theorem tr_one {m : ℕ} (hm : Odd m) : tr m 1 = 1 := by
  simpa using tr_algebraMap hm (1 : ZMod 2)

theorem tr_sq {m : ℕ} (x : F m) : tr m (x ^ 2) = tr m x := by
  apply (algebraMap (ZMod 2) (F m)).injective
  calc
    _ = ∑ i ∈ range (Module.finrank (ZMod 2) (F m)), (x ^ 2) ^ (Nat.card (ZMod 2) ^ i) :=
      FiniteField.algebraMap_trace_eq_sum_pow _ _ _
    _ = ∑ i ∈ range (Module.finrank (ZMod 2) (F m)), (x ^ (Nat.card (ZMod 2) ^ i)) ^ 2 := by
      exact sum_congr rfl fun i _ => by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2]
    _ = (∑ i ∈ range (Module.finrank (ZMod 2) (F m)), x ^ (Nat.card (ZMod 2) ^ i)) ^ 2 := by
      exact (map_sum (frobenius (F m) 2) _ _).symm
    _ = _ := by
      rw [← FiniteField.algebraMap_trace_eq_sum_pow, ← map_pow, bit_sq]

noncomputable def eval {m : ℕ} (a : F m) (x y : V m) : ZMod 2 :=
  tr m (a ^ 2 * x.1 * y.1) + tr m (a * x.1) * tr m (a * y.1) +
    x.2 * tr m (a * y.1) + y.2 * tr m (a * x.1)

theorem eval_symm {m : ℕ} (a : F m) (x y : V m) : eval a x y = eval a y x := by
  unfold eval
  rw [show a ^ 2 * x.1 * y.1 = a ^ 2 * y.1 * x.1 by ring]
  ring

theorem eval_zero_left {m : ℕ} (a : F m) (y : V m) : eval a 0 y = 0 := by
  simp [eval]

theorem eval_zero_right {m : ℕ} (a : F m) (x : V m) : eval a x 0 = 0 := by
  rw [eval_symm, eval_zero_left]

theorem eval_add_left {m : ℕ} (a : F m) (x y z : V m) :
    eval a (x + y) z = eval a x z + eval a y z := by
  simp only [eval, Prod.fst_add, Prod.snd_add, mul_add, add_mul, map_add]
  ring

theorem eval_add_right {m : ℕ} (a : F m) (x y z : V m) :
    eval a x (y + z) = eval a x y + eval a x z := by
  rw [eval_symm a x, eval_add_left, eval_symm a y, eval_symm a z]

theorem eval_diag {m : ℕ} (a : F m) (x : V m) : eval a x x = 0 := by
  have ha : a ^ 2 * x.1 * x.1 = (a * x.1) ^ 2 := by ring
  unfold eval
  rw [ha, tr_sq, ← pow_two, bit_sq, CharTwo.add_self_eq_zero, zero_add,
    CharTwo.add_self_eq_zero]

noncomputable def bilin {m : ℕ} (a : F m) : LinearMap.BilinForm (ZMod 2) (V m) where
  toFun := fun x =>
    { toFun := eval a x
      map_add' := eval_add_right a x
      map_smul' := fun r y => by
        rcases bit_cases r with rfl | rfl <;> simp [eval_zero_right] }
  map_add' := fun x y => by
    apply LinearMap.ext
    intro z
    exact eval_add_left a x y z
  map_smul' := fun r x => by
    apply LinearMap.ext
    intro z
    change eval a (r • x) z = r • (eval a x z)
    rcases bit_cases r with rfl | rfl <;> simp [eval_zero_left]

@[simp] theorem bilin_apply {m : ℕ} (a : F m) (x y : V m) : bilin a x y = eval a x y := rfl

theorem tr_mul_algebraMap {m : ℕ} (r : ZMod 2) (z : F m) :
    tr m (algebraMap (ZMod 2) (F m) r * z) = r * tr m z := by
  rw [← Algebra.smul_def, map_smul]
  rfl

theorem exists_eval_diff_one {m : ℕ} (hm : Odd m) {a b : F m} (hab : a ≠ b)
    {x : V m} (hx : x ≠ 0) : ∃ y : V m, eval a y x + eval b y x = 1 := by
  by_contra! h
  have hz (y : V m) : eval a y x + eval b y x = 0 :=
    (bit_cases _).resolve_right (h y)
  let δ := a + b
  have hδ : δ ≠ 0 := fun hzero => hab (CharTwo.add_eq_zero.mp hzero)
  have htrace : tr m (δ * x.1) = 0 := by
    rw [show δ * x.1 = a * x.1 + b * x.1 by dsimp [δ]; ring, map_add]
    simpa [eval] using hz (0, 1)
  let A := tr m (a * x.1)
  have hA : tr m (b * x.1) = A := by
    have hsum : tr m (a * x.1) + tr m (b * x.1) = 0 := by
      simpa [δ, add_mul] using htrace
    exact (CharTwo.add_eq_zero.mp hsum).symm
  let ell := algebraMap (ZMod 2) (F m) (A + x.2)
  let c := δ ^ 2 * x.1 + ell * δ
  have hcoef (y : F m) : tr m (c * y) = 0 := by
    have hfirst : δ ^ 2 * x.1 * y = a ^ 2 * y * x.1 + b ^ 2 * y * x.1 := by
      unfold δ
      rw [CharTwo.add_sq]
      ring
    have hsec : tr m (δ * y) = tr m (a * y) + tr m (b * y) := by simp [δ, add_mul]
    calc
      _ = tr m (a ^ 2 * y * x.1) + tr m (b ^ 2 * y * x.1) +
          (A + x.2) * (tr m (a * y) + tr m (b * y)) := by
        change tr m ((δ ^ 2 * x.1 + ell * δ) * y) = _
        rw [add_mul, map_add, hfirst, map_add, mul_assoc ell, tr_mul_algebraMap, hsec]
      _ = eval a (y, 0) x + eval b (y, 0) x := by
        simp only [eval, zero_mul, add_zero, hA]
        change _ = _ + tr m (a * y) * A + x.2 * tr m (a * y) +
          (_ + tr m (b * y) * A + x.2 * tr m (b * y))
        ring
      _ = _ := hz (y, 0)
  have hc : c = 0 := by
    by_contra hne
    have hh := hcoef c⁻¹
    rw [mul_inv_cancel₀ hne, tr_one hm] at hh
    exact one_ne_zero hh
  have hmul : δ * (δ * x.1 + ell) = 0 := by
    calc
      _ = c := by unfold c; ring
      _ = 0 := hc
  have heq : δ * x.1 = ell :=
    CharTwo.add_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hδ)
  have ht : A + x.2 = 0 := by
    rw [← tr_algebraMap hm (A + x.2)]
    change tr m ell = 0
    exact heq ▸ htrace
  have hx1 : x.1 = 0 := by
    have hprod : δ * x.1 = 0 := by
      rw [heq]
      change (algebraMap (ZMod 2) (F m)) (A + x.2) = 0
      rw [ht, map_zero]
    exact (mul_eq_zero.mp hprod).resolve_left hδ
  have hx2 : x.2 = 0 := by simpa [A, hx1] using ht
  exact hx (Prod.ext hx1 hx2)

noncomputable def pairing {m : ℕ} (x y : V m) : ZMod 2 :=
  tr m (x.1 * y.1) + x.2 * y.2

theorem pairing_add_left {m : ℕ} (x y z : V m) :
    pairing (x + y) z = pairing x z + pairing y z := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, add_mul, map_add]
  ring

theorem pairing_add_right {m : ℕ} (x y z : V m) :
    pairing x (y + z) = pairing x y + pairing x z := by
  simp only [pairing, Prod.fst_add, Prod.snd_add, mul_add, map_add]
  ring

theorem exists_pairing_one {m : ℕ} (hm : Odd m) {x : V m} (hx : x ≠ 0) :
    ∃ y, pairing x y = 1 := by
  by_cases h : x.1 = 0
  · have h' : x.2 ≠ 0 := fun e => hx (Prod.ext h e)
    refine ⟨(0, 1), ?_⟩
    simpa [pairing] using (bit_cases x.2).resolve_left h'
  · exact ⟨(x.1⁻¹, 0), by simp [pairing, h, tr_one hm]⟩


end Erdos1066.Kerdock

/- Orthogonal and unbiased sign vectors associated with the Kerdock forms. -/

open Finset

namespace Erdos1066.Kerdock

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

noncomputable instance fieldFintype (m : ℕ) : Fintype (F m) := Fintype.ofFinite _

noncomputable def q {m : ℕ} (a : F m) : V m → ZMod 2 :=
  Classical.choose (exists_quadratic_with_polar (bilin a) (eval_diag a) (eval_symm a))

theorem q_zero {m : ℕ} (a : F m) : q a 0 = 0 :=
  (Classical.choose_spec (exists_quadratic_with_polar (bilin a) (eval_diag a) (eval_symm a))).1

theorem q_add {m : ℕ} (a : F m) (x y : V m) :
    q a (x + y) = q a x + q a y + eval a x y :=
  (Classical.choose_spec (exists_quadratic_with_polar (bilin a) (eval_diag a) (eval_symm a))).2 x y

noncomputable def phase {m : ℕ} (a : F m) (u v : V m) : ZMod 2 := q a v + pairing u v

theorem phase_zero {m : ℕ} (a : F m) (u : V m) : phase a u 0 = 0 := by
  simp [phase, q_zero, pairing]

theorem phase_add {m : ℕ} (a : F m) (u x y : V m) :
    phase a u (x + y) = phase a u x + phase a u y + eval a x y := by
  simp only [phase, q_add, pairing_add_right]
  abel

theorem phase_product_self {m : ℕ} (a : F m) (u v : V m) :
    binarySign (phase a u v) * binarySign (phase a u v) = 1 := by
  rw [← binarySign_add, CharTwo.add_self_eq_zero, binarySign_zero]

theorem sign_dot_eq_zero_of_same {m : ℕ} (hm : Odd m) (a : F m) {u w : V m}
    (huw : u ≠ w) :
    (∑ v : V m, binarySign (phase a u v) * binarySign (phase a w v)) = 0 := by
  have hun : u + w ≠ 0 := by
    intro hz
    have h₁ : u.1 + w.1 = 0 := congrArg Prod.fst hz
    have h₂ : u.2 + w.2 = 0 := congrArg Prod.snd hz
    exact huw (Prod.ext (CharTwo.add_eq_zero.mp h₁) (CharTwo.add_eq_zero.mp h₂))
  have hphase (v : V m) : phase a u v + phase a w v = pairing (u + w) v := by
    rw [pairing_add_left]
    unfold phase
    calc
      _ = (q a v + q a v) + (pairing u v + pairing w v) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]
  simp_rw [← binarySign_add, hphase]
  obtain ⟨y, hy⟩ := exists_pairing_one hm hun
  exact sum_binarySign_eq_zero_of_translation _ y fun v => by rw [pairing_add_right, hy]

theorem sign_dot_sq_of_distinct {m : ℕ} (hm : Odd m) {a b : F m} (hab : a ≠ b)
    (u w : V m) :
    (∑ v : V m, binarySign (phase a u v) * binarySign (phase b w v)) ^ 2 =
      (Fintype.card (V m) : ℝ) := by
  simp_rw [← binarySign_add]
  apply walsh_sq_of_nondegenerate _ (fun x y => eval a x y + eval b x y)
  · simp [phase_zero]
  · intro x
    simp [eval_zero_right]
  · intro x y
    rw [phase_add, phase_add]
    abel
  · intro x y h
    rw [eval_add_left, eval_add_left]
    abel
  · intro h hne
    exact exists_eval_diff_one hm hab hne


end Erdos1066.Kerdock

/- The real configuration obtained by adding one coordinate for each basis. -/

open Finset
open scoped InnerProductSpace Classical

namespace Erdos1066.Kerdock

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev Labels (m : ℕ) := F m × V m
abbrev Coordinates (m : ℕ) := V m ⊕ F m

noncomputable def raw {m : ℕ} (k : ℝ) (u : Labels m) : Coordinates m → ℝ := by
  classical
  exact Sum.elim (fun v => binarySign (phase u.1 u.2 v))
    (fun a => if a = u.1 then Real.sqrt k else 0)

theorem raw_dot {m : ℕ} {k : ℝ} (hk : 0 ≤ k) (u w : Labels m) :
    (∑ i : Coordinates m, raw k u i * raw k w i) =
    (∑ v : V m, binarySign (phase u.1 u.2 v) * binarySign (phase w.1 w.2 v)) +
      if u.1 = w.1 then k else 0 := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [raw, Sum.elim_inl, Sum.elim_inr]
  congr 1
  by_cases h : u.1 = w.1
  · rw [if_pos h]
    simp only [← h]
    have hterm (a : F m) :
        (if a = u.1 then Real.sqrt k else 0) * (if a = u.1 then Real.sqrt k else 0) =
          if a = u.1 then k else 0 := by
      by_cases h' : a = u.1 <;> simp [h', Real.mul_self_sqrt hk]
    simp_rw [hterm]
    simp
  · rw [if_neg h]
    refine sum_eq_zero fun a _ => ?_
    split_ifs with hu hw
    · exact (h (hu.symm.trans hw)).elim
    · exact mul_zero _
    · exact zero_mul _
    · exact zero_mul _

theorem raw_dot_self {m : ℕ} {k : ℝ} (hk : 0 ≤ k) (u : Labels m) :
    (∑ i : Coordinates m, raw k u i * raw k u i) = (Fintype.card (V m) : ℝ) + k := by
  rw [raw_dot hk]
  simp [phase_product_self]

theorem raw_dot_distinct {m : ℕ} (hm : Odd m) {k : ℝ} (hk : 0 < k)
    (hcard : (Fintype.card (V m) : ℝ) = k ^ 2) {u w : Labels m} (huw : u ≠ w) :
    let t := ∑ i : Coordinates m, raw k u i * raw k w i
    t = k ∨ t = -k := by
  classical
  dsimp
  rw [raw_dot hk.le]
  by_cases h : u.1 = w.1
  · have h' : u.2 ≠ w.2 := fun e => huw (Prod.ext h e)
    rw [if_pos h, ← h, sign_dot_eq_zero_of_same hm u.1 h', zero_add]
    exact Or.inl rfl
  · rw [if_neg h, add_zero]
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [sign_dot_sq_of_distinct hm h, hcard]

theorem bound_from_field {m k : ℕ} (hm : Odd m) (hk : 0 < k)
    (hcard : (Fintype.card (V m) : ℝ) = (k : ℝ) ^ 2) :
    gDim (Fintype.card (Coordinates m)) (Fintype.card (Labels m)) ≤ k + 2 := by
  classical
  let d := Fintype.card (Coordinates m)
  let e : Fin d ≃ Coordinates m := (Fintype.equivFin (Coordinates m)).symm
  let R := Real.sqrt (2 * (k : ℝ) ^ 2)
  let a : ℝ := (k : ℝ) / (2 * (k : ℝ) ^ 2)
  let b : ℝ := ((k : ℝ) ^ 2 + (k : ℝ)) / (2 * (k : ℝ) ^ 2)
  let f : Labels m → EuclideanSpace ℝ (Fin d) := fun u =>
    WithLp.toLp 2 (fun i => raw (k : ℝ) u (e i) / R)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : 0 < (2 : ℝ) * (k : ℝ) ^ 2 := by positivity
  have ha : 0 < a := div_pos hk' hden
  have hb : b = 1 / 2 + a := by
    dsimp [b, a]
    field_simp
  have hba : b + a = ((k + 2 : ℕ) : ℝ) * a := by
    dsimp [b, a]
    push_cast
    field_simp
    ring
  have hscale (u w : Labels m) :
      ⟪f u, f w⟫_ℝ = (∑ i : Coordinates m, raw (k : ℝ) u i * raw (k : ℝ) w i) /
        (2 * (k : ℝ) ^ 2) := by
    rw [PiLp.inner_apply]
    have hstep (i : Fin d) :
        ⟪f u i, f w i⟫_ℝ =
        (raw (k : ℝ) u (e i) * raw (k : ℝ) w (e i)) / (2 * (k : ℝ) ^ 2) := by
      change (raw (k : ℝ) w (e i) / R) * (raw (k : ℝ) u (e i) / R) = _
      rw [div_mul_div_comm, ← pow_two, show R ^ 2 = 2 * (k : ℝ) ^ 2 from
        Real.sq_sqrt hden.le, mul_comm (raw (k : ℝ) w (e i))]
    simp_rw [hstep, div_eq_mul_inv, ← sum_mul]
    rw [Equiv.sum_comp e (fun i => raw (k : ℝ) u i * raw (k : ℝ) w i)]
  have hdiag (u : Labels m) : ⟪f u, f u⟫_ℝ = b := by
    rw [hscale, raw_dot_self hk'.le, hcard]
  have hoff {u w : Labels m} (hne : u ≠ w) :
      ⟪f u, f w⟫_ℝ = a ∨ ⟪f u, f w⟫_ℝ = -a := by
    obtain h | h := raw_dot_distinct hm hk' hcard hne
    · exact Or.inl (by rw [hscale, h])
    · exact Or.inr (by rw [hscale, h, neg_div])
  have hinj : Function.Injective f := by
    intro u w hf
    by_contra hne
    have h := hoff hne
    rw [← hf, hdiag] at h
    rcases h with h | h <;> linarith
  let X : Finset (EuclideanSpace ℝ (Fin d)) := univ.image f
  have hX : X.card = Fintype.card (Labels m) := by
    rw [show X = univ.image f by rfl, card_image_of_injective _ hinj, card_univ]
  rw [← hX]
  apply gDim_le_of_two_angles X ha hb hba.le
  · intro x hx
    obtain ⟨u, _, rfl⟩ := mem_image.mp hx
    exact hdiag u
  · intro x hx y hy hxy
    obtain ⟨u, _, rfl⟩ := mem_image.mp hx
    obtain ⟨w, _, rfl⟩ := mem_image.mp hy
    exact hoff (fun h => hxy (congrArg f h))


end Erdos1066.Kerdock

/- The counterexample family and negation of the exact pinned target. -/

namespace Erdos1066.Kerdock

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem parameter_square (t : ℕ) :
    2 * (2 : ℕ) ^ (2 * t + 1) = ((2 : ℕ) ^ (t + 1)) ^ 2 := by
  calc
    _ = (2 : ℕ) ^ (1 + (2 * t + 1)) := by
      simpa only [pow_one] using (pow_add (2 : ℕ) 1 (2 * t + 1)).symm
    _ = _ := by rw [← pow_mul]; congr 1; omega

theorem counterexample_family (t : ℕ) :
    gDim (3 * 2 ^ (2 * t + 1)) (2 * (2 ^ (2 * t + 1)) ^ 2) ≤ 2 ^ (t + 1) + 2 := by
  let m := 2 * t + 1
  let k := 2 ^ (t + 1)
  have hm : Odd m := ⟨t, rfl⟩
  have hF : Fintype.card (F m) = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 m (by dsimp [m]; omega)
  have hV : Fintype.card (V m) = 2 * 2 ^ m := by
    simp only [V, Fintype.card_prod, hF, ZMod.card, mul_comm]
  have hC : Fintype.card (Coordinates m) = 3 * 2 ^ m := by
    rw [Fintype.card_sum, hV, hF]
    ring
  have hU : Fintype.card (Labels m) = 2 * (2 ^ m) ^ 2 := by
    rw [Fintype.card_prod, hV, hF]
    ring
  have hk : 0 < k := by dsimp [k]; positivity
  have hsq : (Fintype.card (V m) : ℝ) = (k : ℝ) ^ 2 := by
    rw [hV]
    exact_mod_cast parameter_square t
  have hb := bound_from_field hm hk hsq
  rw [hC, hU] at hb
  exact hb

end Erdos1066.Kerdock

theorem OMA.disproof : ¬ (type_of% @Erdos1066.erdos_1066.variants.higher_dim) := by
  rintro ⟨c, hc, hgood⟩
  obtain ⟨t, ht⟩ := exists_nat_gt (6 / c)
  let q : ℕ := 2 ^ (2 * t + 1)
  let k : ℕ := 2 ^ (t + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hk : 2 ≤ k := by
    dsimp [k]
    rw [pow_succ]
    have h : 0 < (2 : ℕ) ^ t := by positivity
    omega
  have hqt : t < k := (Nat.lt_succ_self t).trans ((t + 1).lt_two_pow_self)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hck : (6 : ℝ) < c * (k : ℝ) := by
    have htk : (t : ℝ) < k := by exact_mod_cast hqt
    exact (div_lt_iff₀ hc).mp (ht.trans htk) |>.trans_eq (mul_comm _ _)
  have hlower := hgood (3 * q) (2 * q ^ 2) (by omega)
  have hupper : ((Erdos1066.gDim (3 * q) (2 * q ^ 2) : ℕ) : ℝ) ≤ (k + 2 : ℕ) := by
    exact_mod_cast Erdos1066.Kerdock.counterexample_family t
  have hineq := hlower.trans hupper
  push_cast at hineq
  have hmul := (div_le_iff₀ (show (0 : ℝ) < 3 * (q : ℝ) by positivity)).mp hineq
  have hcancel : c * (2 * (q : ℝ)) ≤ ((k : ℝ) + 2) * 3 := by
    apply le_of_mul_le_mul_right _ hq'
    convert hmul using 1 <;> ring
  have hsq : 2 * (q : ℝ) = (k : ℝ) ^ 2 := by
    exact_mod_cast Erdos1066.Kerdock.parameter_square t
  rw [hsq] at hcancel
  have hgreat := mul_lt_mul_of_pos_right hck (show (0 : ℝ) < k by linarith)
  nlinarith
