import FormalConjectures.ErdosProblems.«510»
import Mathlib

/-!
Erdos 510, Ruzsa variant: a proof following I. Z. Ruzsa, Negative values of
cosine sums, Acta Arith. 111 (2004), 179-186. Everything is discretised on the
finite field ZMod Q (Q a large prime), so all integrals are finite sums.
-/
-- Credit: @LordMike

namespace OMA.Ruzsa

open Finset

variable {Q : ℕ} [Fact Q.Prime]

/- ## Definitions (fixed) -/

/-- The standard character of `ZMod Q`: `e x = exp (2 π i x / Q)`. -/
noncomputable def e (x : ZMod Q) : ℂ := ZMod.stdAddChar x

/-- Exponential sum with frequency set `B`. -/
noncomputable def gB (B : Finset (ZMod Q)) (x : ZMod Q) : ℂ := ∑ b ∈ B, e (b * x)

/-- Real exponential sum (equal to `gB A` when `A` is symmetric). -/
noncomputable def fR (A : Finset (ZMod Q)) (x : ZMod Q) : ℝ := ∑ a ∈ A, (e (a * x)).re

/-- Normalised convolution on `ZMod Q`. -/
noncomputable def conv (u v : ZMod Q → ℂ) (x : ZMod Q) : ℂ :=
  (∑ t, u t * v (x - t)) / (Q : ℂ)

/-- Twist: multiplication by the character `x ↦ e (-(δ x))` (shifts frequencies by `-δ`). -/
noncomputable def tw (δ : ZMod Q) (u : ZMod Q → ℂ) (x : ZMod Q) : ℂ := e (-(δ * x)) * u x

/-- Normalised `L¹` norm. -/
noncomputable def E1 (u : ZMod Q → ℂ) : ℝ := (∑ x, ‖u x‖) / (Q : ℝ)

/-- Normalised square of the `L²` norm. -/
noncomputable def E2 (u : ZMod Q → ℂ) : ℝ := (∑ x, ‖u x‖ ^ 2) / (Q : ℝ)

/-- Normalised fourth power of the `L⁴` norm. -/
noncomputable def E4 (u : ZMod Q → ℂ) : ℝ := (∑ x, ‖u x‖ ^ 4) / (Q : ℝ)

/-- `A` is symmetric about `0`. -/
def Sym (A : Finset (ZMod Q)) : Prop := ∀ a ∈ A, -a ∈ A

/-- `sh B δ = B ∩ (B - δ)`. -/
def sh (B : Finset (ZMod Q)) (δ : ZMod Q) : Finset (ZMod Q) := B.filter (fun b => b + δ ∈ B)

/-- Bourgain-Ruzsa decomposition of `gB B`. -/
def Dec (A : Finset (ZMod Q)) (K L ε : ℝ) (B : Finset (ZMod Q)) : Prop :=
  ∃ h1 h2 h3 : ZMod Q → ℂ, (∀ x, gB B x = h1 x + h2 x + h3 x) ∧
    (∀ x, ‖h1 x‖ ≤ fR A x + K) ∧ (∀ x, ‖h2 x‖ ≤ L) ∧ E1 h3 ≤ ε

/-- The quadratic form of the kernel `1_A (x - y) + K [x = y]`. -/
noncomputable def Phi (A : Finset (ZMod Q)) (K : ℝ) (c : ZMod Q → ℝ) : ℝ :=
  (∑ x, ∑ y, c x * c y * (if x - y ∈ A then (1 : ℝ) else 0)) + K * ∑ x, c x ^ 2

/-- The symmetrised image of a set of naturals in `ZMod Q`. -/
noncomputable def AG (Q : ℕ) (A : Finset ℕ) : Finset (ZMod Q) :=
  A.image (fun n : ℕ => (n : ZMod Q)) ∪ A.image (fun n : ℕ => -(n : ZMod Q))

/- ## Block E: the character -/

theorem e_basic (x y : ZMod Q) :
    e (x + y) = e x * e y ∧ e (0 : ZMod Q) = 1 ∧ ‖e x‖ = 1 ∧
      e (-x) = (starRingEnd ℂ) (e x) := by
  have hn : ‖e x‖ = 1 := by
    unfold e
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  refine ⟨?_, ?_, hn, ?_⟩
  · unfold e
    exact AddChar.map_add_eq_mul _ _ _
  · unfold e
    exact AddChar.map_zero_eq_one _
  · unfold e
    rw [AddChar.map_neg_eq_inv]
    exact Complex.inv_eq_conj hn

theorem e_orth (r : ZMod Q) : ∑ x : ZMod Q, e (r * x) = if r = 0 then (Q : ℂ) else 0 := by
  unfold e
  simp_rw [mul_comm r]
  rw [AddChar.sum_mulShift r (ZMod.isPrimitive_stdAddChar Q)]
  simp [ZMod.card]

theorem e_natCast (n : ℕ) (x : ZMod Q) :
    (e ((n : ZMod Q) * x)).re = Real.cos ((n : ℝ) * (2 * Real.pi * (x.val : ℝ) / (Q : ℝ))) := by
  have h : (n : ZMod Q) * x = (((n * x.val : ℕ) : ℤ) : ZMod Q) := by
    rw [Int.cast_natCast, Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [h]
  unfold e
  rw [ZMod.stdAddChar_coe]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I * (((n * x.val : ℕ) : ℤ) : ℂ) / ((Q : ℕ) : ℂ))
      = (((2 * Real.pi * ((n : ℝ) * (x.val : ℝ)) / (Q : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h2, Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

/- ## Block G: exponential sums of sets -/

theorem gB_eq_fR (A : Finset (ZMod Q)) (hA : Sym A) (x : ZMod Q) :
    gB A x = ((fR A x : ℝ) : ℂ) := by
  have hconj : (starRingEnd ℂ) (gB A x) = gB A x := by
    unfold gB
    rw [map_sum]
    refine Finset.sum_nbij' (fun a => -a) (fun a => -a) (fun a ha => hA a ha)
      (fun a ha => hA a ha) (fun a _ => neg_neg a) (fun a _ => neg_neg a) (fun a _ => ?_)
    have h := (e_basic (a * x) 0).2.2.2
    show (starRingEnd ℂ) (e (a * x)) = e (-a * x)
    rw [← h, neg_mul]
  rw [Complex.conj_eq_iff_re] at hconj
  rw [← hconj]
  congr 1
  unfold gB fR
  rw [Complex.re_sum]

theorem sum_fR (A : Finset (ZMod Q)) (h0 : (0 : ZMod Q) ∉ A) : ∑ x, fR A x = 0 := by
  unfold fR
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a ha
  have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
  rw [← Complex.re_sum, e_orth, if_neg ha0]
  simp

theorem conv_gB (B C : Finset (ZMod Q)) (x : ZMod Q) :
    conv (gB B) (gB C) x = gB (B ∩ C) x := by
  have hpt : ∀ b c t : ZMod Q, e (b * t) * e (c * (x - t)) = e (c * x) * e ((b - c) * t) := by
    intro b c t
    rw [← (e_basic (b * t) (c * (x - t))).1, ← (e_basic (c * x) ((b - c) * t)).1]
    congr 1
    ring
  have hinner : ∀ b c : ZMod Q, ∑ t : ZMod Q, e (c * x) * e ((b - c) * t) =
      if b = c then (Q : ℂ) * e (c * x) else 0 := by
    intro b c
    rw [← Finset.mul_sum, e_orth]
    by_cases h : b = c
    · subst h
      simp [mul_comm]
    · rw [if_neg (sub_ne_zero.mpr h), if_neg h]
      simp
  have hQC : (Q : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : Q.Prime).ne_zero
  have hexp : ∀ t : ZMod Q, (∑ b ∈ B, e (b * t)) * (∑ c ∈ C, e (c * (x - t))) =
      ∑ b ∈ B, ∑ c ∈ C, e (c * x) * e ((b - c) * t) := by
    intro t
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    exact hpt b c t
  unfold conv gB
  rw [Finset.sum_congr rfl (fun t _ => hexp t), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => hinner b c))]
  simp only [Finset.sum_ite_eq]
  have h2 : ∑ b ∈ B ∩ C, e (b * x) = ∑ b ∈ B, if b ∈ C then e (b * x) else 0 := by
    rw [← Finset.sum_filter]
    congr 1
  have h3 : ∀ b : ZMod Q, (if b ∈ C then (Q : ℂ) * e (b * x) else 0) =
      (Q : ℂ) * (if b ∈ C then e (b * x) else 0) := by
    intro b
    split_ifs <;> simp
  rw [h2, Finset.sum_congr rfl (fun b _ => h3 b), ← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ hQC

theorem tw_gB (B : Finset (ZMod Q)) (δ x : ZMod Q) :
    tw δ (gB B) x = gB (B.image (fun b => b - δ)) x := by
  unfold tw gB
  rw [Finset.sum_image (fun a _ b _ h => sub_left_injective h), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← (e_basic (-(δ * x)) (b * x)).1]
  congr 1
  ring

theorem conv_tw_gB (B : Finset (ZMod Q)) (δ x : ZMod Q) :
    conv (gB B) (tw δ (gB B)) x = gB (sh B δ) x := by
  have htw : tw δ (gB B) = gB (B.image (fun b => b - δ)) := funext (tw_gB B δ)
  have hset : B ∩ B.image (fun b => b - δ) = sh B δ := by
    ext b
    simp only [Finset.mem_inter, Finset.mem_image, sh, Finset.mem_filter]
    constructor
    · rintro ⟨hb, a, ha, hab⟩
      exact ⟨hb, by rw [← hab, sub_add_cancel]; exact ha⟩
    · rintro ⟨hb, hbd⟩
      exact ⟨hb, b + δ, hbd, add_sub_cancel_right b δ⟩
  rw [htw, conv_gB, hset]

theorem parseval (c : ZMod Q → ℂ) :
    ∑ x : ZMod Q, ‖∑ r, c r * e (r * x)‖ ^ 2 = (Q : ℝ) * ∑ r, ‖c r‖ ^ 2 := by
  have hcj : ∀ a b x : ZMod Q, e (a * x) * (starRingEnd ℂ) (e (b * x)) = e ((a - b) * x) := by
    intro a b x
    rw [← (e_basic (b * x) 0).2.2.2, ← (e_basic (a * x) (-(b * x))).1]
    congr 1
    ring
  have hpt : ∀ x : ZMod Q, (((‖∑ r, c r * e (r * x)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ r, ∑ r', (c r * (starRingEnd ℂ) (c r')) * e ((r - r') * x) := by
    intro x
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro r' _
    rw [map_mul]
    linear_combination (c r * (starRingEnd ℂ) (c r')) * hcj r r' x
  have step1 : ∑ x : ZMod Q, ∑ r, ∑ r', (c r * (starRingEnd ℂ) (c r')) * e ((r - r') * x) =
      ∑ r, ∑ r', (c r * (starRingEnd ℂ) (c r')) * ∑ x : ZMod Q, e ((r - r') * x) := by
    refine Eq.trans Finset.sum_comm ?_
    apply Finset.sum_congr rfl
    intro r _
    refine Eq.trans Finset.sum_comm ?_
    apply Finset.sum_congr rfl
    intro r' _
    rw [Finset.mul_sum]
  have step2 : ∑ r, ∑ r', (c r * (starRingEnd ℂ) (c r')) * ∑ x : ZMod Q, e ((r - r') * x) =
      ∑ r, (c r * (starRingEnd ℂ) (c r)) * (Q : ℂ) := by
    apply Finset.sum_congr rfl
    intro r _
    simp [e_orth, sub_eq_zero, mul_ite]
  have hsum : ∑ x : ZMod Q, (((‖∑ r, c r * e (r * x)‖ ^ 2 : ℝ)) : ℂ) =
      (((Q : ℝ) * ∑ r, ‖c r‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun x _ => hpt x), step1, step2]
    rw [Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_natCast, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
    ring
  exact_mod_cast hsum

theorem E2_gB (B : Finset (ZMod Q)) : E2 (gB B) = (B.card : ℝ) := by
  have hc : ∀ x, gB B x = ∑ r, (if r ∈ B then (1 : ℂ) else 0) * e (r * x) := by
    intro x
    simp [gB, ite_mul, Finset.sum_ite_mem]
  have hpars := parseval (fun r => if r ∈ B then (1 : ℂ) else 0)
  have hcard : ∑ r : ZMod Q, ‖(if r ∈ B then (1 : ℂ) else 0)‖ ^ 2 = (B.card : ℝ) := by
    have h1 : ∀ r : ZMod Q, ‖(if r ∈ B then (1 : ℂ) else 0)‖ ^ 2 =
        if r ∈ B then (1 : ℝ) else 0 := by
      intro r
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun r _ => h1 r), Finset.sum_boole]
    simp
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : Q.Prime).ne_zero
  unfold E2
  simp only [hc]
  rw [hpars, hcard]
  exact mul_div_cancel_left₀ _ hQ

theorem gB_mul_conj_aux1 (a b x : ZMod Q) :
    e (a * x) * (starRingEnd ℂ) (e (b * x)) = e ((a - b) * x) := by
  rw [← (e_basic (b * x) 0).2.2.2, ← (e_basic (a * x) (-(b * x))).1]
  congr 1
  ring

theorem gB_mul_conj_aux2 (B : Finset (ZMod Q)) (b : ZMod Q) :
    univ.filter (fun δ : ZMod Q => b + δ ∈ B) = B.image (fun c => c - b) := by
  ext δ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    exact ⟨b + δ, h, by ring⟩
  · rintro ⟨c, hc, rfl⟩
    simpa using hc

theorem gB_mul_conj_aux3 (B : Finset (ZMod Q)) (b x : ZMod Q) :
    ∑ δ : ZMod Q, (if b + δ ∈ B then e (δ * x) else 0) = ∑ c ∈ B, e ((c - b) * x) := by
  rw [← Finset.sum_filter, gB_mul_conj_aux2 B b,
    Finset.sum_image (by intro c _ d _ h; simpa using h)]

theorem gB_mul_conj (B : Finset (ZMod Q)) (x : ZMod Q) :
    gB B x * (starRingEnd ℂ) (gB B x) = ∑ δ, ((sh B δ).card : ℂ) * e (δ * x) := by
  have hL : gB B x * (starRingEnd ℂ) (gB B x) = ∑ b ∈ B, ∑ c ∈ B, e ((b - c) * x) := by
    unfold gB
    rw [map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => gB_mul_conj_aux1 b c x
  have h1 : ∀ δ : ZMod Q, ((sh B δ).card : ℂ) * e (δ * x)
      = ∑ b ∈ B, (if b + δ ∈ B then e (δ * x) else 0) := by
    intro δ
    rw [sh, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  have hR : ∑ δ, ((sh B δ).card : ℂ) * e (δ * x) = ∑ b ∈ B, ∑ c ∈ B, e ((c - b) * x) := by
    simp only [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => gB_mul_conj_aux3 B b x
  rw [hL, hR, Finset.sum_comm]

theorem E4_gB (B : Finset (ZMod Q)) :
    E4 (gB B) = ∑ δ, ((sh B δ).card : ℝ) ^ 2 := by
  have hpt : ∀ x : ZMod Q, ‖gB B x‖ ^ 4 = ‖∑ δ, ((sh B δ).card : ℂ) * e (δ * x)‖ ^ 2 := by
    intro x
    rw [← gB_mul_conj, norm_mul, Complex.norm_conj]
    ring
  have hpar : ∑ x : ZMod Q, ‖∑ r, ((sh B r).card : ℂ) * e (r * x)‖ ^ 2
      = (Q : ℝ) * ∑ r, ‖((sh B r).card : ℂ)‖ ^ 2 := parseval _
  have hQ : (Q : ℝ) ≠ 0 := by
    have := (Fact.out : Q.Prime).pos
    exact_mod_cast this.ne'
  unfold E4
  simp only [hpt, hpar, Complex.norm_natCast]
  field_simp

theorem sum_sh_aux1 (B : Finset (ZMod Q)) (b : ZMod Q) :
    ∑ δ : ZMod Q, (if b + δ ∈ B then 1 else 0 : ℕ) = B.card := by
  have him : univ.filter (fun δ : ZMod Q => b + δ ∈ B) = B.image (fun c => c - b) := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨b + δ, h, by ring⟩
    · rintro ⟨c, hc, rfl⟩
      simpa using hc
  rw [← Finset.card_filter, him, Finset.card_image_of_injective _ (by intro c d h; simpa using h)]

theorem sum_sh (B : Finset (ZMod Q)) :
    ∑ δ, ((sh B δ).card : ℝ) = (B.card : ℝ) ^ 2 := by
  have hc : ∀ δ : ZMod Q, (sh B δ).card = ∑ b ∈ B, (if b + δ ∈ B then 1 else 0) :=
    fun δ => Finset.card_filter _ _
  have hN : ∑ δ : ZMod Q, (sh B δ).card = B.card ^ 2 := by
    simp only [hc]
    rw [Finset.sum_comm]
    simp only [sum_sh_aux1 B, Finset.sum_const, smul_eq_mul]
    ring
  have := congrArg (Nat.cast : ℕ → ℝ) hN
  push_cast at this
  exact this

/- ## Block N: norm inequalities -/

theorem holder_aux1 (a : ZMod Q → ℝ) (ha : ∀ x, 0 ≤ a x) :
    (∑ x, a x ^ 2) ^ 2 ≤ (∑ x, a x) * ∑ x, a x ^ 3 := by
  have h : (∑ x, Real.sqrt (a x) * (a x * Real.sqrt (a x))) ^ 2
      ≤ (∑ x, Real.sqrt (a x) ^ 2) * ∑ x, (a x * Real.sqrt (a x)) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => Real.sqrt (a x)) (fun x => a x * Real.sqrt (a x))
  have e1 : ∑ x, Real.sqrt (a x) * (a x * Real.sqrt (a x)) = ∑ x, a x ^ 2 :=
    Finset.sum_congr rfl fun x _ => by linear_combination a x * Real.mul_self_sqrt (ha x)
  have e2 : ∑ x, Real.sqrt (a x) ^ 2 = ∑ x, a x :=
    Finset.sum_congr rfl fun x _ => Real.sq_sqrt (ha x)
  have e3 : ∑ x, (a x * Real.sqrt (a x)) ^ 2 = ∑ x, a x ^ 3 :=
    Finset.sum_congr rfl fun x _ => by rw [mul_pow, Real.sq_sqrt (ha x)]; ring
  rw [e1, e2, e3] at h
  exact h

theorem holder_aux2 (a : ZMod Q → ℝ) :
    (∑ x, a x ^ 3) ^ 2 ≤ (∑ x, a x ^ 2) * ∑ x, a x ^ 4 := by
  have h : (∑ x, a x * a x ^ 2) ^ 2 ≤ (∑ x, a x ^ 2) * ∑ x, (a x ^ 2) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq univ (fun x => a x) (fun x => a x ^ 2)
  have e1 : ∑ x, a x * a x ^ 2 = ∑ x, a x ^ 3 := Finset.sum_congr rfl fun x _ => by ring
  have e2 : ∑ x, (a x ^ 2) ^ 2 = ∑ x, a x ^ 4 := Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e2] at h
  exact h

theorem holder_aux3 (S1 S2 S3 S4 : ℝ) (h0 : 0 ≤ S2) (h4 : 0 ≤ S4) (hP : S2 ^ 2 ≤ S1 * S3)
    (hR : S3 ^ 2 ≤ S2 * S4) : S2 ^ 3 ≤ S1 ^ 2 * S4 := by
  have h1 : (S2 ^ 2) ^ 2 ≤ (S1 * S3) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hP 2
  have h2 : S1 ^ 2 * S3 ^ 2 ≤ S1 ^ 2 * (S2 * S4) := mul_le_mul_of_nonneg_left hR (sq_nonneg _)
  have key : S2 * S2 ^ 3 ≤ S2 * (S1 ^ 2 * S4) := by
    calc S2 * S2 ^ 3 = (S2 ^ 2) ^ 2 := by ring
      _ ≤ (S1 * S3) ^ 2 := h1
      _ = S1 ^ 2 * S3 ^ 2 := by ring
      _ ≤ S1 ^ 2 * (S2 * S4) := h2
      _ = S2 * (S1 ^ 2 * S4) := by ring
  rcases h0.eq_or_lt with h | h
  · rw [← h]
    nlinarith [mul_nonneg (sq_nonneg S1) h4]
  · exact le_of_mul_le_mul_left key h

theorem holder (u : ZMod Q → ℂ) : (E2 u) ^ 3 ≤ (E1 u) ^ 2 * E4 u := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (Fact.out : Q.Prime).pos
  have P : (∑ x, ‖u x‖ ^ 2) ^ 2 ≤ (∑ x, ‖u x‖) * ∑ x, ‖u x‖ ^ 3 :=
    holder_aux1 (fun x => ‖u x‖) (fun x => norm_nonneg _)
  have R : (∑ x, ‖u x‖ ^ 3) ^ 2 ≤ (∑ x, ‖u x‖ ^ 2) * ∑ x, ‖u x‖ ^ 4 :=
    holder_aux2 (fun x => ‖u x‖)
  have hk := holder_aux3 (∑ x, ‖u x‖) (∑ x, ‖u x‖ ^ 2) (∑ x, ‖u x‖ ^ 3) (∑ x, ‖u x‖ ^ 4)
    (Finset.sum_nonneg fun x _ => sq_nonneg _) (Finset.sum_nonneg fun x _ => by positivity) P R
  unfold E1 E2 E4
  rw [show ((∑ x, ‖u x‖ ^ 2) / (Q : ℝ)) ^ 3 = (∑ x, ‖u x‖ ^ 2) ^ 3 / (Q : ℝ) ^ 3 by ring,
    show ((∑ x, ‖u x‖) / (Q : ℝ)) ^ 2 * ((∑ x, ‖u x‖ ^ 4) / (Q : ℝ))
      = (∑ x, ‖u x‖) ^ 2 * (∑ x, ‖u x‖ ^ 4) / (Q : ℝ) ^ 3 by ring]
  exact div_le_div_of_nonneg_right hk (by positivity)

theorem E1_add (u v : ZMod Q → ℂ) : E1 (fun x => u x + v x) ≤ E1 u + E1 v := by
  unfold E1
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => norm_add_le _ _

theorem E1_sq_le_E2 (u : ZMod Q → ℂ) : (E1 u) ^ 2 ≤ E2 u := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (Fact.out : Q.Prime).pos
  have h : (∑ x, ‖u x‖) ^ 2 ≤ (Q : ℝ) * ∑ x, ‖u x‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ZMod Q)) (fun _ => (1 : ℝ))
      (fun x => ‖u x‖)
    simpa [ZMod.card] using this
  unfold E1 E2
  rw [div_pow, div_le_div_iff₀ (pow_pos hQ 2) hQ]
  nlinarith [mul_le_mul_of_nonneg_right h hQ.le]

theorem E2_add_le (u h : ZMod Q → ℂ) (L : ℝ) (hh : ∀ x, ‖h x‖ ≤ L) :
    E2 (fun x => u x + h x) ≤ 2 * E2 u + 2 * L ^ 2 := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (Fact.out : Q.Prime).pos
  have hpt : ∀ x, ‖u x + h x‖ ^ 2 ≤ 2 * ‖u x‖ ^ 2 + 2 * L ^ 2 := by
    intro x
    have h1 : ‖u x + h x‖ ≤ ‖u x‖ + ‖h x‖ := norm_add_le _ _
    have h2 : ‖u x + h x‖ ^ 2 ≤ (‖u x‖ + ‖h x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : ‖h x‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hh x) 2
    nlinarith [sq_nonneg (‖u x‖ - ‖h x‖)]
  have hsum : ∑ x, ‖u x + h x‖ ^ 2 ≤ ∑ x, (2 * ‖u x‖ ^ 2 + 2 * L ^ 2) :=
    Finset.sum_le_sum fun x _ => hpt x
  unfold E2
  calc (∑ x, ‖u x + h x‖ ^ 2) / (Q : ℝ) ≤ (∑ x, (2 * ‖u x‖ ^ 2 + 2 * L ^ 2)) / (Q : ℝ) :=
        div_le_div_of_nonneg_right hsum hQ.le
    _ = 2 * ((∑ x, ‖u x‖ ^ 2) / (Q : ℝ)) + 2 * L ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul]
        field_simp

theorem E4_le_add_aux1 (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (p + q) ^ 4 ≤ 8 * p ^ 4 + 8 * q ^ 4 := by
  have h1 : (p + q) ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) := by nlinarith [sq_nonneg (p - q)]
  have h2 : ((p + q) ^ 2) ^ 2 ≤ (2 * (p ^ 2 + q ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
  nlinarith [sq_nonneg (p ^ 2 - q ^ 2)]

theorem E4_le_add (u h : ZMod Q → ℂ) (L : ℝ) (hh : ∀ x, ‖h x‖ ≤ L) :
    E4 u ≤ 8 * E4 (fun x => u x + h x) + 8 * L ^ 4 := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (Fact.out : Q.Prime).pos
  have hpt : ∀ x, ‖u x‖ ^ 4 ≤ 8 * ‖u x + h x‖ ^ 4 + 8 * L ^ 4 := by
    intro x
    have h1 : ‖u x‖ ≤ ‖u x + h x‖ + ‖h x‖ := by
      have := norm_sub_le (u x + h x) (h x)
      rwa [add_sub_cancel_right] at this
    have h2 : ‖u x‖ ^ 4 ≤ (‖u x + h x‖ + ‖h x‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) h1 4
    have h3 : ‖h x‖ ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (norm_nonneg _) (hh x) 4
    have h4 := E4_le_add_aux1 ‖u x + h x‖ ‖h x‖ (norm_nonneg _) (norm_nonneg _)
    linarith
  have hsum : ∑ x, ‖u x‖ ^ 4 ≤ ∑ x, (8 * ‖u x + h x‖ ^ 4 + 8 * L ^ 4) :=
    Finset.sum_le_sum fun x _ => hpt x
  unfold E4
  calc (∑ x, ‖u x‖ ^ 4) / (Q : ℝ) ≤ (∑ x, (8 * ‖u x + h x‖ ^ 4 + 8 * L ^ 4)) / (Q : ℝ) :=
        div_le_div_of_nonneg_right hsum hQ.le
    _ = 8 * ((∑ x, ‖u x + h x‖ ^ 4) / (Q : ℝ)) + 8 * L ^ 4 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          ZMod.card, nsmul_eq_mul]
        field_simp

theorem young_inf_left (u v : ZMod Q → ℂ) (L : ℝ) (hv : ∀ x, ‖v x‖ ≤ L) (x : ZMod Q) :
    ‖conv u v x‖ ≤ E1 u * L := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (Fact.out : Q.Prime).pos
  have hQc : ‖(Q : ℂ)‖ = (Q : ℝ) := Complex.norm_natCast Q
  have hs : ‖∑ t, u t * v (x - t)‖ ≤ (∑ t, ‖u t‖) * L := by
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hv _) (norm_nonneg _)
  unfold conv E1
  rw [norm_div, hQc, show (∑ t, ‖u t‖) / (Q : ℝ) * L = ((∑ t, ‖u t‖) * L) / (Q : ℝ) by ring]
  exact div_le_div_of_nonneg_right hs hQ.le

theorem young_inf_right (u v : ZMod Q → ℂ) (L : ℝ) (hu : ∀ x, ‖u x‖ ≤ L) (x : ZMod Q) :
    ‖conv u v x‖ ≤ L * E1 v := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (Fact.out : Q.Prime).pos
  have hQc : ‖(Q : ℂ)‖ = (Q : ℝ) := Complex.norm_natCast Q
  have hs : ‖∑ t, u t * v (x - t)‖ ≤ ∑ t, L * ‖v (x - t)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hu t) (norm_nonneg _)
  have hre : ∑ t, ‖v (x - t)‖ = ∑ y, ‖v y‖ :=
    Equiv.sum_comp (Equiv.subLeft x) (fun y => ‖v y‖)
  have hs' : ‖∑ t, u t * v (x - t)‖ ≤ L * ∑ y, ‖v y‖ := by
    rw [← hre, Finset.mul_sum]
    exact hs
  unfold conv E1
  rw [norm_div, hQc, show L * ((∑ y, ‖v y‖) / (Q : ℝ)) = (L * ∑ y, ‖v y‖) / (Q : ℝ) by ring]
  exact div_le_div_of_nonneg_right hs' hQ.le

theorem young_one (u v : ZMod Q → ℂ) : E1 (conv u v) ≤ E1 u * E1 v := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (Fact.out : Q.Prime).pos
  have hn : ‖(Q : ℂ)‖ = (Q : ℝ) := by simp
  have h1 : ∀ x, ‖conv u v x‖ ≤ (∑ t, ‖u t‖ * ‖v (x - t)‖) / (Q : ℝ) := by
    intro x
    have hS : ‖∑ t, u t * v (x - t)‖ ≤ ∑ t, ‖u t‖ * ‖v (x - t)‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun t _ => norm_mul _ _
    unfold conv
    rw [norm_div, hn]
    gcongr
  have hswap : ∑ x, ∑ t, ‖u t‖ * ‖v (x - t)‖ = (∑ t, ‖u t‖) * (∑ x, ‖v x‖) := by
    rw [Finset.sum_comm, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp (Equiv.subRight t) (fun y => ‖v y‖)
  have hs : ∑ x, ‖conv u v x‖ ≤ (∑ x, ∑ t, ‖u t‖ * ‖v (x - t)‖) / (Q : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun x _ => h1 x
  rw [hswap, le_div_iff₀ hQpos] at hs
  unfold E1
  rw [div_mul_div_comm, div_le_div_iff₀ hQpos (mul_pos hQpos hQpos)]
  nlinarith [mul_le_mul_of_nonneg_right hs hQpos.le]

theorem conv_add (u u' v v' : ZMod Q → ℂ) (x : ZMod Q) :
    conv (fun y => u y + u' y) v x = conv u v x + conv u' v x ∧
      conv u (fun y => v y + v' y) x = conv u v x + conv u v' x := by
  constructor
  · simp only [conv, add_mul, Finset.sum_add_distrib, add_div]
  · simp only [conv, mul_add, Finset.sum_add_distrib, add_div]

theorem tw_add (δ : ZMod Q) (u v : ZMod Q → ℂ) (x : ZMod Q) :
    tw δ (fun y => u y + v y) x = tw δ u x + tw δ v x := by
  simp only [tw, mul_add]

theorem norm_tw (δ : ZMod Q) (u : ZMod Q → ℂ) :
    (∀ x, ‖tw δ u x‖ = ‖u x‖) ∧ E1 (tw δ u) = E1 u := by
  have hn : ∀ x, ‖tw δ u x‖ = ‖u x‖ := by
    intro x
    unfold tw
    rw [norm_mul, (e_basic (-(δ * x)) 0).2.2.1, one_mul]
  refine ⟨hn, ?_⟩
  unfold E1
  simp only [hn]

theorem conv_dom (u v : ZMod Q → ℂ) (w : ZMod Q → ℝ) (hu : ∀ x, ‖u x‖ ≤ w x)
    (hv : ∀ x, ‖v x‖ ≤ w x) (x : ZMod Q) :
    ‖conv u v x‖ ≤ (∑ t, w t * w (x - t)) / (Q : ℝ) := by
  have hsum : ‖∑ t, u t * v (x - t)‖ ≤ ∑ t, w t * w (x - t) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hu t) (hv (x - t)) (norm_nonneg _) ((norm_nonneg _).trans (hu t))
  have hn : ‖(Q : ℂ)‖ = (Q : ℝ) := by simp
  unfold conv
  rw [norm_div, hn]
  gcongr

theorem ww (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K : ℝ) (x : ZMod Q) :
    (∑ t, (fR A t + K) * (fR A (x - t) + K)) / (Q : ℝ) = fR A x + K ^ 2 := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (Fact.out : Q.Prime).pos
  have hQne : (Q : ℝ) ≠ 0 := hQpos.ne'
  have hrefl : ∑ t, fR A (x - t) = 0 :=
    (Equiv.sum_comp (Equiv.subLeft x) (fun y => fR A y)).trans (sum_fR A h0)
  have hconv : (∑ t, fR A t * fR A (x - t)) / (Q : ℝ) = fR A x := by
    have hc : conv (gB A) (gB A) x = gB A x := by
      rw [conv_gB, Finset.inter_self]
    unfold conv at hc
    simp only [gB_eq_fR A hA] at hc
    apply Complex.ofReal_injective
    push_cast
    exact_mod_cast hc
  have hexp : ∑ t, (fR A t + K) * (fR A (x - t) + K)
      = ∑ t, fR A t * fR A (x - t) + (Q : ℝ) * K ^ 2 := by
    have hpt : ∀ t, (fR A t + K) * (fR A (x - t) + K)
        = fR A t * fR A (x - t) + K * fR A t + K * fR A (x - t) + K ^ 2 := fun t => by ring
    simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hrefl, sum_fR A h0]
    simp [Finset.sum_const, Finset.card_univ, ZMod.card]
  rw [hexp, add_div, hconv, mul_div_cancel_left₀ _ hQne]

theorem split_norm (z : ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : ‖z‖ ≤ a + b) :
    ∃ z1 z2 : ℂ, z = z1 + z2 ∧ ‖z1‖ ≤ a ∧ ‖z2‖ ≤ b := by
  by_cases hab : a + b = 0
  · have hz0 : z = 0 := norm_eq_zero.mp (le_antisymm (by linarith) (norm_nonneg z))
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · rw [hz0]; simp
    · simpa using ha
    · simpa using hb
  · have hpos : 0 < a + b := lt_of_le_of_ne (by linarith) (Ne.symm hab)
    have h1 : a / (a + b) + b / (a + b) = 1 := by rw [← add_div, div_self hab]
    refine ⟨(a / (a + b) : ℝ) • z, (b / (a + b) : ℝ) • z, ?_, ?_, ?_⟩
    · rw [← add_smul, h1, one_smul]
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hpos.le)]
      calc a / (a + b) * ‖z‖ ≤ a / (a + b) * (a + b) :=
            mul_le_mul_of_nonneg_left hz (div_nonneg ha hpos.le)
        _ = a := by field_simp
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb hpos.le)]
      calc b / (a + b) * ‖z‖ ≤ b / (a + b) * (a + b) :=
            mul_le_mul_of_nonneg_left hz (div_nonneg hb hpos.le)
        _ = b := by field_simp

theorem sum_conv_tw_aux1 (u v : ZMod Q → ℂ) (x δ : ZMod Q) :
    conv u (tw δ v) x = e (-(δ * x)) * ((Q : ℂ)⁻¹ * ∑ t, (u t * v (x - t)) * e (t * δ)) := by
  have hterm : ∀ t, u t * (e (-(δ * (x - t))) * v (x - t))
      = e (-(δ * x)) * ((u t * v (x - t)) * e (t * δ)) := by
    intro t
    have h := (e_basic (-(δ * x)) (t * δ)).1
    have h2 : e (-(δ * (x - t))) = e (-(δ * x)) * e (t * δ) := by
      rw [← h]; congr 1; ring
    rw [h2]; ring
  unfold conv tw
  simp only [hterm]
  rw [← Finset.mul_sum]
  ring

theorem sum_conv_tw_aux2 (u v : ZMod Q → ℂ) (x : ZMod Q) :
    ∑ δ, ‖conv u (tw δ v) x‖ ^ 2 = (1 / (Q : ℝ)) * ∑ t, ‖u t‖ ^ 2 * ‖v (x - t)‖ ^ 2 := by
  have hn : ‖(Q : ℂ)⁻¹‖ = 1 / (Q : ℝ) := by simp
  have hP := parseval (fun t => u t * v (x - t))
  have hstep : ∀ δ, ‖conv u (tw δ v) x‖ ^ 2
      = (1 / (Q : ℝ)) ^ 2 * ‖∑ t, (u t * v (x - t)) * e (t * δ)‖ ^ 2 := by
    intro δ
    rw [sum_conv_tw_aux1 u v x δ, norm_mul, norm_mul, (e_basic (-(δ * x)) 0).2.2.1, one_mul, hn]
    ring
  simp only [hstep]
  rw [← Finset.mul_sum, hP]
  simp only [norm_mul, mul_pow]
  field_simp

theorem sum_conv_tw (u v : ZMod Q → ℂ) :
    ∑ δ, E2 (conv u (tw δ v)) = E2 u * E2 v := by
  have hsw : ∑ x, ∑ t, ‖u t‖ ^ 2 * ‖v (x - t)‖ ^ 2 = (∑ t, ‖u t‖ ^ 2) * (∑ x, ‖v x‖ ^ 2) := by
    rw [Finset.sum_comm, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp (Equiv.subRight t) (fun y => ‖v y‖ ^ 2)
  calc ∑ δ, E2 (conv u (tw δ v))
      = (∑ δ, ∑ x, ‖conv u (tw δ v) x‖ ^ 2) / (Q : ℝ) := by
        unfold E2; rw [Finset.sum_div]
    _ = (∑ x, ∑ δ, ‖conv u (tw δ v) x‖ ^ 2) / (Q : ℝ) := by rw [Finset.sum_comm]
    _ = (∑ x, (1 / (Q : ℝ)) * ∑ t, ‖u t‖ ^ 2 * ‖v (x - t)‖ ^ 2) / (Q : ℝ) := by
        congr 1
        exact Finset.sum_congr rfl fun x _ => sum_conv_tw_aux2 u v x
    _ = (1 / (Q : ℝ)) * ((∑ t, ‖u t‖ ^ 2) * (∑ x, ‖v x‖ ^ 2)) / (Q : ℝ) := by
        rw [← Finset.mul_sum, hsw]
    _ = E2 u * E2 v := by unfold E2; ring

/- ## Block S: one step of the Bourgain-Ruzsa iteration -/

theorem E1_h1 (A : Finset (ZMod Q)) (h0 : (0 : ZMod Q) ∉ A) (K : ℝ) (h1 : ZMod Q → ℂ)
    (hh : ∀ x, ‖h1 x‖ ≤ fR A x + K) : E1 h1 ≤ K := by
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (Fact.out : Q.Prime).pos
  have hs : ∑ x, ‖h1 x‖ ≤ ∑ x, (fR A x + K) := Finset.sum_le_sum fun x _ => hh x
  rw [Finset.sum_add_distrib, sum_fR A h0, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, zero_add] at hs
  unfold E1
  rw [div_le_iff₀ hQpos]
  linarith

theorem energy_lb (A : Finset (ZMod Q)) (h0 : (0 : ZMod Q) ∉ A) (K L ε : ℝ)
    (hK : 0 < K) (B : Finset (ZMod Q)) (hD : Dec A K L ε B) (hε : ε ≤ K) (hL : 0 ≤ L)
    (h4 : 4 * L ^ 2 ≤ (B.card : ℝ)) (h6 : 4096 * K ^ 2 * L ^ 4 ≤ (B.card : ℝ) ^ 3) :
    (B.card : ℝ) ^ 3 ≤ 4096 * K ^ 2 * E4 (gB B) := by
  obtain ⟨h1, h2, h3, hg, hh1, hh2, hh3⟩ := hD
  have hfun : (fun x => h1 x + h3 x + h2 x) = gB B := funext fun x => by
    show h1 x + h3 x + h2 x = gB B x
    rw [hg x]; ring
  have hE2 : E2 (fun x => h1 x + h3 x + h2 x) ≤ 2 * E2 (fun x => h1 x + h3 x) + 2 * L ^ 2 :=
    E2_add_le (fun x => h1 x + h3 x) h2 L hh2
  rw [hfun, E2_gB] at hE2
  have hE2u : (B.card : ℝ) / 4 ≤ E2 (fun x => h1 x + h3 x) := by linarith
  have hE1u : E1 (fun x => h1 x + h3 x) ≤ 2 * K := by
    have h := E1_add h1 h3
    have h' := E1_h1 A h0 K h1 hh1
    linarith
  have hE1u0 : 0 ≤ E1 (fun x => h1 x + h3 x) := by unfold E1; positivity
  have hE4 : E4 (fun x => h1 x + h3 x) ≤ 8 * E4 (gB B) + 8 * L ^ 4 := by
    have h : E4 (fun x => h1 x + h3 x) ≤ 8 * E4 (fun x => h1 x + h3 x + h2 x) + 8 * L ^ 4 :=
      E4_le_add (fun x => h1 x + h3 x) h2 L hh2
    rw [hfun] at h
    exact h
  have hE4u0 : 0 ≤ E4 (fun x => h1 x + h3 x) := by unfold E4; positivity
  have hsq : E1 (fun x => h1 x + h3 x) ^ 2 ≤ 4 * K ^ 2 := by
    nlinarith [mul_nonneg hE1u0 (sub_nonneg.mpr hE1u)]
  have hm0 : 0 ≤ (B.card : ℝ) / 4 := by linarith [sq_nonneg L]
  have hcube : ((B.card : ℝ) / 4) ^ 3 ≤ E2 (fun x => h1 x + h3 x) ^ 3 :=
    pow_le_pow_left₀ hm0 hE2u 3
  have hholder : E2 (fun x => h1 x + h3 x) ^ 3 ≤ E1 (fun x => h1 x + h3 x) ^ 2 * E4 (fun x => h1 x + h3 x) :=
    holder _
  have h5 : E1 (fun x => h1 x + h3 x) ^ 2 * E4 (fun x => h1 x + h3 x) ≤ 4 * K ^ 2 * E4 (fun x => h1 x + h3 x) :=
    mul_le_mul_of_nonneg_right hsq hE4u0
  have h6' : 4 * K ^ 2 * E4 (fun x => h1 x + h3 x) ≤ 4 * K ^ 2 * (8 * E4 (gB B) + 8 * L ^ 4) :=
    mul_le_mul_of_nonneg_left hE4 (by positivity)
  have hcube' : ((B.card : ℝ) / 4) ^ 3 = (B.card : ℝ) ^ 3 / 64 := by ring
  nlinarith [hcube, hholder, h5, h6', hcube', h6]

theorem popular (B : Finset (ZMod Q)) (K : ℝ) (hK : 0 < K)
    (h : (B.card : ℝ) ^ 3 ≤ 4096 * K ^ 2 * ∑ δ, ((sh B δ).card : ℝ) ^ 2) :
    (B.card : ℝ) ≤ 8192 * K ^ 2 *
      ((univ.filter (fun δ : ZMod Q =>
        (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ))).card : ℝ) := by
  have hsum : ∑ δ, ((sh B δ).card : ℝ) = (B.card : ℝ) ^ 2 := sum_sh B
  have hrm : ∀ δ : ZMod Q, ((sh B δ).card : ℝ) ≤ (B.card : ℝ) := fun δ => by
    exact_mod_cast Finset.card_filter_le _ _
  have hr0 : ∀ δ : ZMod Q, (0 : ℝ) ≤ ((sh B δ).card : ℝ) := fun δ => Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
  have hC : (0 : ℝ) < 8192 * K ^ 2 := by positivity
  have hpt : ∀ δ : ZMod Q, ((sh B δ).card : ℝ) ^ 2 ≤
      (if (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ) then (B.card : ℝ) ^ 2 else 0)
        + (B.card : ℝ) / (8192 * K ^ 2) * ((sh B δ).card : ℝ) := by
    intro δ
    have h1 := hr0 δ
    have h2 := hrm δ
    have h3 : 0 ≤ (B.card : ℝ) / (8192 * K ^ 2) * ((sh B δ).card : ℝ) := by positivity
    have h4 : ((sh B δ).card : ℝ) * ((sh B δ).card : ℝ) ≤ (B.card : ℝ) * (B.card : ℝ) :=
      mul_le_mul h2 h2 h1 hm0
    split_ifs with hP
    · nlinarith
    · push_neg at hP
      have hr : ((sh B δ).card : ℝ) ≤ (B.card : ℝ) / (8192 * K ^ 2) := by
        rw [le_div_iff₀ hC]; nlinarith
      have h5 := mul_le_mul_of_nonneg_right hr h1
      nlinarith
  have hD : ∑ δ, ((sh B δ).card : ℝ) ^ 2 ≤
      ((univ.filter (fun δ : ZMod Q =>
        (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ))).card : ℝ) * (B.card : ℝ) ^ 2
        + (B.card : ℝ) / (8192 * K ^ 2) * (B.card : ℝ) ^ 2 := by
    calc ∑ δ, ((sh B δ).card : ℝ) ^ 2
        ≤ ∑ δ, ((if (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ) then (B.card : ℝ) ^ 2 else 0)
          + (B.card : ℝ) / (8192 * K ^ 2) * ((sh B δ).card : ℝ)) :=
          Finset.sum_le_sum (fun δ _ => hpt δ)
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_ite,
            Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  generalize hd : ((univ.filter (fun δ : ZMod Q =>
        (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ))).card : ℝ) = d at hD ⊢
  have hkey : (B.card : ℝ) ^ 3 ≤ 8192 * K ^ 2 * d * (B.card : ℝ) ^ 2 := by
    have e1 : (B.card : ℝ) / (8192 * K ^ 2) * (B.card : ℝ) ^ 2 * (4096 * K ^ 2)
        = (B.card : ℝ) ^ 3 / 2 := by
      field_simp
      ring
    have hpos : (0 : ℝ) ≤ 4096 * K ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hD hpos
    nlinarith
  rcases eq_or_lt_of_le hm0 with h0 | hpos
  · rw [← h0]
    have : (0 : ℝ) ≤ 8192 * K ^ 2 * d := by
      rw [← hd]; positivity
    linarith
  · have hm2 : (0 : ℝ) < (B.card : ℝ) ^ 2 := by positivity
    have : (B.card : ℝ) * (B.card : ℝ) ^ 2 ≤ (8192 * K ^ 2 * d) * (B.card : ℝ) ^ 2 := by
      nlinarith [hkey]
    exact le_of_mul_le_mul_right this hm2

theorem pick (D : Finset (ZMod Q)) (m C L τ : ℝ) (hm : 0 < m) (hC : 0 < C)
    (hD : m ≤ 2 * C * (D.card : ℝ)) (h2 : ZMod Q → ℂ) (hh : ∀ x, ‖h2 x‖ ≤ L) (hL : 0 ≤ L)
    (hτ : 0 ≤ τ) (hτm : 2 * C * L ^ 4 ≤ τ ^ 2 * m) :
    ∃ δ ∈ D, E1 (conv h2 (tw δ h2)) ≤ τ := by
  have hQ : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (Fact.out : Q.Prime).pos
  have hE2L : E2 h2 ≤ L ^ 2 := by
    unfold E2
    rw [div_le_iff₀ hQ]
    calc ∑ x, ‖h2 x‖ ^ 2 ≤ ∑ _x : ZMod Q, L ^ 2 :=
          Finset.sum_le_sum (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hh x) 2)
      _ = L ^ 2 * (Q : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring
  have hE2nn : 0 ≤ E2 h2 := by unfold E2; positivity
  have hsum : ∑ δ ∈ D, E2 (conv h2 (tw δ h2)) ≤ L ^ 4 := by
    calc ∑ δ ∈ D, E2 (conv h2 (tw δ h2))
        ≤ ∑ δ, E2 (conv h2 (tw δ h2)) :=
          Finset.sum_le_univ_sum_of_nonneg (fun δ => by unfold E2; positivity)
      _ = E2 h2 * E2 h2 := sum_conv_tw h2 h2
      _ ≤ L ^ 2 * L ^ 2 := mul_le_mul hE2L hE2L hE2nn (by positivity)
      _ = L ^ 4 := by ring
  have hDpos : 0 < (D.card : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have h0 : (D.card : ℝ) = 0 := le_antisymm hcon (Nat.cast_nonneg _)
    rw [h0] at hD
    nlinarith
  have hL4 : L ^ 4 ≤ τ ^ 2 * (D.card : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hD (sq_nonneg τ)
    have hC2 : 0 < 2 * C := by linarith
    have h2' : 2 * C * L ^ 4 ≤ 2 * C * (τ ^ 2 * (D.card : ℝ)) := by nlinarith
    exact le_of_mul_le_mul_left h2' hC2
  by_contra hcon
  push_neg at hcon
  have hne : D.Nonempty := Finset.card_pos.mp (by exact_mod_cast hDpos)
  have hgt : ∀ δ ∈ D, τ ^ 2 < E2 (conv h2 (tw δ h2)) := by
    intro δ hδ
    have h1 := hcon δ hδ
    have hsq := E1_sq_le_E2 (conv h2 (tw δ h2))
    have h3 : 0 ≤ E1 (conv h2 (tw δ h2)) := by unfold E1; positivity
    nlinarith
  have hlt : ∑ _δ ∈ D, τ ^ 2 < ∑ δ ∈ D, E2 (conv h2 (tw δ h2)) :=
    Finset.sum_lt_sum_of_nonempty hne hgt
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  linarith

theorem h11_split (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K : ℝ)
    (hK : 1 ≤ K) (hf : ∀ x, -K ≤ fR A x) (h1 : ZMod Q → ℂ)
    (hh : ∀ x, ‖h1 x‖ ≤ fR A x + K) (δ : ZMod Q) :
    ∃ p q : ZMod Q → ℂ, (∀ x, conv h1 (tw δ h1) x = p x + q x) ∧
      (∀ x, ‖p x‖ ≤ fR A x + K) ∧ (∀ x, ‖q x‖ ≤ K ^ 2 - K) := by
  have hK0 : 0 ≤ K ^ 2 - K := by nlinarith
  have key : ∀ x, ∃ z1 z2 : ℂ, conv h1 (tw δ h1) x = z1 + z2 ∧
      ‖z1‖ ≤ fR A x + K ∧ ‖z2‖ ≤ K ^ 2 - K := by
    intro x
    apply split_norm (conv h1 (tw δ h1) x) (fR A x + K) (K ^ 2 - K)
    · have := hf x
      linarith
    · exact hK0
    · have hb : ‖conv h1 (tw δ h1) x‖ ≤ fR A x + K ^ 2 := by
        rw [← ww A hA h0 K x]
        exact conv_dom h1 (tw δ h1) (fun y => fR A y + K) hh
          (fun y => by rw [(norm_tw δ h1).1 y]; exact hh y) x
      linarith
  choose p q hpq hp hq using key
  exact ⟨p, q, hpq, hp, hq⟩

theorem h2_bound (K L ε : ℝ) (hK : 1 ≤ K) (hKL : K ≤ L) (hε : ε ≤ K)
    (h1 h2 h3 q : ZMod Q → ℂ) (δ : ZMod Q) (hh1 : E1 h1 ≤ K) (hh2 : ∀ x, ‖h2 x‖ ≤ L)
    (hh3 : E1 h3 ≤ ε) (hq : ∀ x, ‖q x‖ ≤ K ^ 2 - K) (x : ZMod Q) :
    ‖q x + conv (fun y => h1 y + h3 y) (tw δ h2) x +
        conv h2 (tw δ (fun y => h1 y + h3 y)) x‖ ≤ 5 * K * L := by
  have hL0 : 0 ≤ L := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hE1u : E1 (fun y => h1 y + h3 y) ≤ 2 * K := by
    have := E1_add h1 h3
    linarith
  have hE1t : E1 (tw δ (fun y => h1 y + h3 y)) ≤ 2 * K := by
    rw [(norm_tw δ _).2]
    exact hE1u
  have hA1 : ‖conv (fun y => h1 y + h3 y) (tw δ h2) x‖ ≤ 2 * K * L := by
    have h := young_inf_left (fun y => h1 y + h3 y) (tw δ h2) L
      (fun y => by rw [(norm_tw δ h2).1 y]; exact hh2 y) x
    have h' := mul_le_mul_of_nonneg_right hE1u hL0
    linarith
  have hA2 : ‖conv h2 (tw δ (fun y => h1 y + h3 y)) x‖ ≤ 2 * K * L := by
    have h := young_inf_right h2 (tw δ (fun y => h1 y + h3 y)) L hh2 x
    have h' := mul_le_mul_of_nonneg_left hE1t hL0
    linarith
  have hKK : K ^ 2 - K ≤ K * L := by
    have := mul_le_mul_of_nonneg_left (show K - 1 ≤ L by linarith) hK0
    nlinarith
  have t1 := norm_add_le (q x + conv (fun y => h1 y + h3 y) (tw δ h2) x)
    (conv h2 (tw δ (fun y => h1 y + h3 y)) x)
  have t2 := norm_add_le (q x) (conv (fun y => h1 y + h3 y) (tw δ h2) x)
  have hq' := hq x
  linarith

theorem h3_bound (K ε τ : ℝ) (hε : ε ≤ K) (h1 h2 h3 : ZMod Q → ℂ) (δ : ZMod Q)
    (hh1 : E1 h1 ≤ K) (hh3 : E1 h3 ≤ ε) (hτ : E1 (conv h2 (tw δ h2)) ≤ τ) :
    E1 (fun x => conv h1 (tw δ h3) x + conv h3 (tw δ h1) x + conv h3 (tw δ h3) x +
        conv h2 (tw δ h2) x) ≤ 3 * K * ε + τ := by
  have h1nn : 0 ≤ E1 h1 := by unfold E1; positivity
  have h3nn : 0 ≤ E1 h3 := by unfold E1; positivity
  have hK0 : 0 ≤ K := le_trans h1nn hh1
  have hε0 : 0 ≤ ε := le_trans h3nn hh3
  have eA : E1 (conv h1 (tw δ h3)) ≤ K * ε := by
    have h := young_one h1 (tw δ h3)
    rw [(norm_tw δ h3).2] at h
    exact h.trans (mul_le_mul hh1 hh3 h3nn hK0)
  have eB : E1 (conv h3 (tw δ h1)) ≤ ε * K := by
    have h := young_one h3 (tw δ h1)
    rw [(norm_tw δ h1).2] at h
    exact h.trans (mul_le_mul hh3 hh1 h1nn hε0)
  have eC : E1 (conv h3 (tw δ h3)) ≤ ε * ε := by
    have h := young_one h3 (tw δ h3)
    rw [(norm_tw δ h3).2] at h
    exact h.trans (mul_le_mul hh3 hh3 h3nn hε0)
  have s1 : E1 (fun x => conv h1 (tw δ h3) x + conv h3 (tw δ h1) x) ≤
      E1 (conv h1 (tw δ h3)) + E1 (conv h3 (tw δ h1)) := E1_add _ _
  have s2 : E1 (fun x => conv h1 (tw δ h3) x + conv h3 (tw δ h1) x + conv h3 (tw δ h3) x) ≤
      E1 (fun x => conv h1 (tw δ h3) x + conv h3 (tw δ h1) x) + E1 (conv h3 (tw δ h3)) :=
    E1_add _ _
  have s3 : E1 (fun x => conv h1 (tw δ h3) x + conv h3 (tw δ h1) x + conv h3 (tw δ h3) x +
        conv h2 (tw δ h2) x) ≤
      E1 (fun x => conv h1 (tw δ h3) x + conv h3 (tw δ h1) x + conv h3 (tw δ h3) x) +
        E1 (conv h2 (tw δ h2)) := E1_add _ _
  have hε2 : ε * ε ≤ K * ε := mul_le_mul_of_nonneg_right hε hε0
  nlinarith

theorem conv_expand (g h1 h2 h3 : ZMod Q → ℂ) (hg : ∀ x, g x = h1 x + h2 x + h3 x)
    (δ x : ZMod Q) :
    conv g (tw δ g) x = conv h1 (tw δ h1) x +
      (conv (fun y => h1 y + h3 y) (tw δ h2) x + conv h2 (tw δ (fun y => h1 y + h3 y)) x) +
      (conv h1 (tw δ h3) x + conv h3 (tw δ h1) x + conv h3 (tw δ h3) x +
        conv h2 (tw δ h2) x) := by
  have hT : tw δ g = fun y => (tw δ h1 y + tw δ h2 y) + tw δ h3 y := by
    funext y
    have hgy : g y = h1 y + h2 y + h3 y := hg y
    simp only [tw]
    rw [hgy]
    ring
  have hT13 : tw δ (fun y => h1 y + h3 y) = fun y => tw δ h1 y + tw δ h3 y :=
    funext fun y => tw_add δ h1 h3 y
  have hg' : g = fun y => h1 y + h2 y + h3 y := funext hg
  have ca1 : ∀ (u u' v : ZMod Q → ℂ) (x : ZMod Q),
      conv (fun y => u y + u' y) v x = conv u v x + conv u' v x :=
    fun u u' v x => (conv_add u u' v v x).1
  have ca2 : ∀ (u v v' : ZMod Q → ℂ) (x : ZMod Q),
      conv u (fun y => v y + v' y) x = conv u v x + conv u v' x :=
    fun u v v' x => (conv_add u u v v' x).2
  rw [hT, hg', hT13]
  simp only [ca1, ca2]
  ring

theorem dec_step (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K L ε τ : ℝ)
    (hK : 1 ≤ K) (hf : ∀ x, -K ≤ fR A x) (hKL : K ≤ L) (hε : ε ≤ K)
    (B : Finset (ZMod Q)) (h1 h2 h3 : ZMod Q → ℂ)
    (hg : ∀ x, gB B x = h1 x + h2 x + h3 x) (hh1 : ∀ x, ‖h1 x‖ ≤ fR A x + K)
    (hh2 : ∀ x, ‖h2 x‖ ≤ L) (hh3 : E1 h3 ≤ ε) (δ : ZMod Q)
    (hτ : E1 (conv h2 (tw δ h2)) ≤ τ) :
    Dec A K (5 * K * L) (3 * K * ε + τ) (sh B δ) := by
  obtain ⟨p, q, hpq, hp, hq⟩ := h11_split A hA h0 K hK hf h1 hh1 δ
  have hE1h1 : E1 h1 ≤ K := E1_h1 A h0 K h1 hh1
  refine ⟨p, fun x => q x + conv (fun y => h1 y + h3 y) (tw δ h2) x +
      conv h2 (tw δ (fun y => h1 y + h3 y)) x,
    fun x => conv h1 (tw δ h3) x + conv h3 (tw δ h1) x + conv h3 (tw δ h3) x +
      conv h2 (tw δ h2) x, ?_, hp, ?_, ?_⟩
  · intro x
    dsimp only
    rw [← conv_tw_gB B δ x, conv_expand (gB B) h1 h2 h3 hg δ x, hpq x]
    ring
  · intro x
    exact h2_bound K L ε hK hKL hε h1 h2 h3 q δ hE1h1 hh2 hh3 hq x
  · exact h3_bound K ε τ hε h1 h2 h3 δ hE1h1 hh3 hτ

theorem step (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K L ε τ : ℝ)
    (hK : 1 ≤ K) (hf : ∀ x, -K ≤ fR A x) (hKL : K ≤ L) (hε : ε ≤ K)
    (B : Finset (ZMod Q)) (hD : Dec A K L ε B)
    (h4 : 4 * L ^ 2 ≤ (B.card : ℝ)) (h6 : 4096 * K ^ 2 * L ^ 4 ≤ (B.card : ℝ) ^ 3)
    (F : Finset (ZMod Q)) (hF : 2 * (8192 * K ^ 2) * (F.card : ℝ) ≤ (B.card : ℝ))
    (hτ : 0 ≤ τ) (hτm : 2 * (8192 * K ^ 2) * L ^ 4 ≤ τ ^ 2 * (B.card : ℝ)) :
    ∃ δ : ZMod Q, δ ∉ F ∧ (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ) ∧
      Dec A K (5 * K * L) (3 * K * ε + τ) (sh B δ) := by 
  have hKpos : 0 < K := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hK2 : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK
  have hE := energy_lb A h0 K L ε hKpos B hD hε hL0 h4 h6
  rw [E4_gB] at hE
  have hpop := popular B K hKpos hE
  obtain ⟨h1, h2, h3, hg, hh1, hh2, hh3⟩ := hD
  have hm0 : (0 : ℝ) < (B.card : ℝ) := by
    have : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    linarith
  have hC0 : (0 : ℝ) ≤ 8192 * K ^ 2 := by positivity
  have hCpos : (0 : ℝ) < 8192 * K ^ 2 := by linarith
  have hcard0 : (univ.filter (fun δ : ZMod Q =>
      (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ))).card ≤
      ((univ.filter (fun δ : ZMod Q =>
      (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ))) \ F).card + F.card :=
    Finset.card_le_card_sdiff_add_card
  have hcard : ((univ.filter (fun δ : ZMod Q =>
      (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ))).card : ℝ) ≤
      (((univ.filter (fun δ : ZMod Q =>
      (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ))) \ F).card : ℝ) + (F.card : ℝ) := by
    exact_mod_cast hcard0
  have h5 := mul_le_mul_of_nonneg_left hcard hC0
  have hm2 : (B.card : ℝ) ≤ 2 * (8192 * K ^ 2) *
      (((univ.filter (fun δ : ZMod Q =>
      (B.card : ℝ) ≤ 8192 * K ^ 2 * ((sh B δ).card : ℝ))) \ F).card : ℝ) := by
    linarith
  obtain ⟨δ, hδ, hτδ⟩ := pick _ (B.card : ℝ) (8192 * K ^ 2) L τ hm0 hCpos hm2 h2 hh2 hL0 hτ hτm
  rw [Finset.mem_sdiff, Finset.mem_filter] at hδ
  exact ⟨δ, hδ.2, hδ.1.2,
    dec_step A hA h0 K L ε τ hK hf hKL hε B h1 h2 h3 hg hh1 hh2 hh3 δ hτδ⟩

/- ## Block I: iteration (Ruzsa Lemma 2.1) -/

theorem dec_base (A : Finset (ZMod Q)) (hA : Sym A) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ x, -K ≤ fR A x) : Dec A K K 0 A := by 
  unfold Dec
  refine ⟨fun x => ((max (fR A x) 0 : ℝ) : ℂ), fun x => ((min (fR A x) 0 : ℝ) : ℂ),
    fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro x
    have hs : ((max (fR A x) 0 : ℝ) : ℂ) + ((min (fR A x) 0 : ℝ) : ℂ) = ((fR A x : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add, max_add_min, add_zero]
    show gB A x = ((max (fR A x) 0 : ℝ) : ℂ) + ((min (fR A x) 0 : ℝ) : ℂ) + 0
    rw [gB_eq_fR A hA x, add_zero, hs]
  · intro x
    show ‖((max (fR A x) 0 : ℝ) : ℂ)‖ ≤ fR A x + K
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 := hf x
    constructor
    · have := le_max_right (fR A x) 0
      linarith
    · exact max_le (by linarith) (by linarith)
  · intro x
    show ‖((min (fR A x) 0 : ℝ) : ℂ)‖ ≤ K
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have h1 := hf x
    constructor
    · exact le_min h1 (by linarith)
    · exact (min_le_right _ _).trans (by linarith)
  · simp [E1]

theorem dec_mono (A B : Finset (ZMod Q)) (K L L' ε ε' : ℝ) (hL : L ≤ L') (hε : ε ≤ ε')
    (h : Dec A K L ε B) : Dec A K L' ε' B := by 
  unfold Dec at h ⊢
  obtain ⟨h1, h2, h3, hg, hh1, hh2, hh3⟩ := h
  exact ⟨h1, h2, h3, hg, hh1, fun x => (hh2 x).trans hL, hh3.trans hε⟩

theorem num0 (K C : ℝ) (hK : 1 ≤ K) (hC : C = 8192 * K ^ 2) (j : ℕ) :
    ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 2 ≤ C ^ (j + 1) ∧ K ≤ (5 : ℝ) ^ j * K ^ (j + 1) := by 
  have h5 : (1 : ℝ) ≤ (5 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hK0 : (0 : ℝ) ≤ K := by linarith
  refine ⟨?_, ?_⟩
  · have e1 : ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 2 = ((5 : ℝ) ^ j * (5 : ℝ) ^ j) * (K ^ 2) ^ (j + 1) := by
      ring
    have e2 : C ^ (j + 1) = (8192 : ℝ) ^ (j + 1) * (K ^ 2) ^ (j + 1) := by
      rw [hC, mul_pow]
    have e3 : (5 : ℝ) ^ j * (5 : ℝ) ^ j = (25 : ℝ) ^ j := by
      rw [← mul_pow]
      norm_num
    have e4 : (25 : ℝ) ^ j ≤ (8192 : ℝ) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have e5 : (8192 : ℝ) ^ j ≤ (8192 : ℝ) ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e6 : (0 : ℝ) ≤ (K ^ 2) ^ (j + 1) := by positivity
    rw [e1, e2, e3]
    exact mul_le_mul_of_nonneg_right (e4.trans e5) e6
  · have h2 : K ^ 1 ≤ K ^ (j + 1) := pow_le_pow_right₀ hK (by omega)
    rw [pow_one] at h2
    nlinarith [mul_le_mul_of_nonneg_right h5 (pow_nonneg hK0 (j + 1))]

theorem numA (K C m : ℝ) (hK : 1 ≤ K) (hC : C = 8192 * K ^ 2) (j J : ℕ) (hj : j ≤ J)
    (hm : C ^ (3 * J + 4) ≤ m) :
    4 * ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 2 ≤ m ∧
      4096 * K ^ 2 * ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4 ≤ m ^ 3 ∧
      2 * C * (4 : ℝ) ^ j ≤ m := by 
  have hn := (num0 K C hK hC j).1
  have hK2 : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK
  have hCK : (8192 : ℝ) ≤ C := by rw [hC]; nlinarith
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hC4 : (4096 : ℝ) * K ^ 2 ≤ C := by rw [hC]; nlinarith [sq_nonneg K]
  have hmono : ∀ a b : ℕ, a ≤ b → C ^ a ≤ C ^ b := fun a b h => pow_le_pow_right₀ hC1 h
  have p1 : 4 * ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 2 ≤ C ^ (j + 2) := by
    have e : C ^ (j + 2) = C * C ^ (j + 1) := by ring
    rw [e]
    have h4 : 4 * C ^ (j + 1) ≤ C * C ^ (j + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hC0 _)
    linarith
  have hA1 : 4 * ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 2 ≤ m :=
    p1.trans ((hmono (j + 2) (3 * J + 4) (by omega)).trans hm)
  have q1 : ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4 ≤ (C ^ (j + 1)) ^ 2 := by
    have h4 : ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4 = (((5 : ℝ) ^ j * K ^ (j + 1)) ^ 2) ^ 2 := by
      ring
    rw [h4]
    exact pow_le_pow_left₀ (by positivity) hn 2
  have q3 : 4096 * K ^ 2 * ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4 ≤ C * (C ^ (j + 1)) ^ 2 :=
    mul_le_mul hC4 q1 (by positivity) hC0
  have q4 : C * (C ^ (j + 1)) ^ 2 = C ^ (2 * j + 3) := by ring
  have q5 : (C ^ (3 * J + 4)) ^ 3 = C ^ (9 * J + 12) := by ring
  have q6 : C ^ (2 * j + 3) ≤ C ^ (9 * J + 12) := hmono _ _ (by omega)
  have q7 : (C ^ (3 * J + 4)) ^ 3 ≤ m ^ 3 := pow_le_pow_left₀ (pow_nonneg hC0 _) hm 3
  have hA2 : 4096 * K ^ 2 * ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4 ≤ m ^ 3 := by
    rw [q4] at q3
    linarith
  have r1 : (4 : ℝ) ^ j ≤ C ^ j := pow_le_pow_left₀ (by norm_num) (by linarith) j
  have r3 : 2 * C * C ^ j ≤ C * C * C ^ j :=
    mul_le_mul_of_nonneg_right (by nlinarith) (pow_nonneg hC0 j)
  have hA3 : 2 * C * (4 : ℝ) ^ j ≤ m := by
    have r4 : 2 * C * (4 : ℝ) ^ j ≤ 2 * C * C ^ j := mul_le_mul_of_nonneg_left r1 (by linarith)
    have r5 : C * C * C ^ j = C ^ (j + 2) := by ring
    have h6 := hmono (j + 2) (3 * J + 4) (by omega)
    linarith
  exact ⟨hA1, hA2, hA3⟩

theorem numB (K C m : ℝ) (hK : 1 ≤ K) (hC : C = 8192 * K ^ 2) (j J : ℕ) (hj : j ≤ J)
    (hm : C ^ (3 * J + 4) ≤ m) :
    2 * C * ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4 ≤ (C ^ j / (2 * C ^ J)) ^ 2 * m ∧
      3 * K * (C ^ j / C ^ (J + 1)) + C ^ j / (2 * C ^ J) ≤ C ^ (j + 1) / C ^ (J + 1) ∧
      C ^ j / C ^ (J + 1) ≤ K := by 
  have hn := (num0 K C hK hC j).1
  have hK2 : (1 : ℝ) ≤ K ^ 2 := one_le_pow₀ hK
  have hCK : (8192 : ℝ) ≤ C := by rw [hC]; nlinarith
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hCpos : (0 : ℝ) < C := by linarith
  have hCne : C ≠ 0 := hCpos.ne'
  have hC6 : 6 * K ≤ C := by rw [hC]; nlinarith
  have hmono : ∀ a b : ℕ, a ≤ b → C ^ a ≤ C ^ b := fun a b h => pow_le_pow_right₀ hC1 h
  have hP4 : ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4 ≤ C ^ (2 * j + 2) := by
    have h4 : ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4 = (((5 : ℝ) ^ j * K ^ (j + 1)) ^ 2) ^ 2 := by
      ring
    have h5 : C ^ (2 * j + 2) = (C ^ (j + 1)) ^ 2 := by ring
    rw [h4, h5]
    exact pow_le_pow_left₀ (by positivity) hn 2
  have hCJ : (8192 : ℝ) ≤ C ^ (J + 1) := by
    have : (1 : ℝ) ≤ C ^ J := one_le_pow₀ hC1
    rw [pow_succ]
    nlinarith
  have A1 : 2 * C * ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4 ≤ 2 * C * C ^ (2 * j + 2) :=
    mul_le_mul_of_nonneg_left hP4 (by linarith)
  have A2 : 2 * C * C ^ (2 * j + 2) = 2 * C ^ (2 * j + 3) := by ring
  have A3 : C ^ (2 * j + 3) * 8192 ≤ C ^ (2 * j + 3) * C ^ (J + 1) :=
    mul_le_mul_of_nonneg_left hCJ (pow_nonneg hC0 _)
  have A4 : C ^ (2 * j + 3) * C ^ (J + 1) = C ^ (2 * j + J + 4) := by ring
  have A5 : (C ^ j / (2 * C ^ J)) ^ 2 * C ^ (3 * J + 4) = C ^ (2 * j + J + 4) / 4 := by
    field_simp
    ring
  have A6 : (C ^ j / (2 * C ^ J)) ^ 2 * C ^ (3 * J + 4) ≤ (C ^ j / (2 * C ^ J)) ^ 2 * m :=
    mul_le_mul_of_nonneg_left hm (sq_nonneg _)
  have A7 : (0 : ℝ) ≤ C ^ (2 * j + 3) := pow_nonneg hC0 _
  have hZ : 0 ≤ C ^ j / C ^ (J + 1) := div_nonneg (pow_nonneg hC0 _) (pow_nonneg hC0 _)
  have e1 : C ^ j / (2 * C ^ J) = C * (C ^ j / C ^ (J + 1)) / 2 := by
    rw [pow_succ]
    field_simp
  have e2 : C ^ (j + 1) / C ^ (J + 1) = C * (C ^ j / C ^ (J + 1)) := by ring
  have hC6' : 0 ≤ C - 6 * K := by linarith
  have part2 : 3 * K * (C ^ j / C ^ (J + 1)) + C ^ j / (2 * C ^ J) ≤
      C ^ (j + 1) / C ^ (J + 1) := by
    rw [e1, e2]
    nlinarith [mul_nonneg hC6' hZ]
  have part3 : C ^ j / C ^ (J + 1) ≤ K := by
    rw [div_le_iff₀ (pow_pos hCpos _)]
    have h1 : C ^ J ≤ C ^ (J + 1) := hmono J (J + 1) (by omega)
    have h2 : C ^ (J + 1) ≤ K * C ^ (J + 1) := le_mul_of_one_le_left (pow_nonneg hC0 _) hK
    have h3 : C ^ j ≤ C ^ J := hmono j J hj
    linarith
  refine ⟨?_, part2, part3⟩
  linarith

theorem m_lb (C n m : ℝ) (hC : 1 ≤ C) (j J : ℕ) (hj : j ≤ J)
    (hn : C ^ (4 * J + 4) ≤ n) (hm : n ≤ C ^ j * m) : C ^ (3 * J + 4) ≤ m := by 
  have hCpos : (0 : ℝ) < C := by linarith
  have hJpos : (0 : ℝ) < C ^ J := pow_pos hCpos J
  have h1 : C ^ j ≤ C ^ J := pow_le_pow_right₀ hC hj
  have hpos : (0 : ℝ) < C ^ (4 * J + 4) := pow_pos hCpos _
  have hm0 : (0 : ℝ) ≤ m := by
    by_contra h
    rw [not_le] at h
    have : C ^ j * m < 0 := mul_neg_of_pos_of_neg (pow_pos hCpos j) h
    linarith
  have h2 : C ^ (3 * J + 4) * C ^ J ≤ m * C ^ J := by
    have e : C ^ (3 * J + 4) * C ^ J = C ^ (4 * J + 4) := by ring
    rw [e, mul_comm m]
    calc C ^ (4 * J + 4) ≤ n := hn
      _ ≤ C ^ j * m := hm
      _ ≤ C ^ J * m := mul_le_mul_of_nonneg_right h1 hm0
  exact le_of_mul_le_mul_right h2 hJpos

theorem T_double (A B T : Finset (ZMod Q)) (δ : ZMod Q)
    (hTB : ∀ t ∈ T, ∀ b ∈ B, t + b ∈ A)
    (hδ : δ ∉ (T ×ˢ T).image (fun p : ZMod Q × ZMod Q => p.1 - p.2)) :
    ∃ T' : Finset (ZMod Q), T'.card = 2 * T.card ∧ ∀ t ∈ T', ∀ b ∈ sh B δ, t + b ∈ A := by
  
  classical
  refine ⟨T ∪ T.image (· + δ), ?_, ?_⟩
  · have hdisj : Disjoint T (T.image (· + δ)) := by
      rw [Finset.disjoint_left]
      intro t ht hti
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hti
      apply hδ
      refine Finset.mem_image.mpr ⟨(s + δ, s), Finset.mem_product.mpr ⟨ht, hs⟩, ?_⟩
      show s + δ - s = δ
      ring
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (add_left_injective δ)]
    ring
  · intro t ht b hb
    have hb' := Finset.mem_filter.mp hb
    rcases Finset.mem_union.mp ht with h | h
    · exact hTB t h b hb'.1
    · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp h
      have h2 := hTB s hs (b + δ) hb'.2
      show s + δ + b ∈ A
      have e : s + δ + b = s + (b + δ) := by ring
      rw [e]
      exact h2

theorem iter_succ (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K C : ℝ)
    (hK : 1 ≤ K) (hC : C = 8192 * K ^ 2) (hf : ∀ x, -K ≤ fR A x) (j J : ℕ) (hj : j ≤ J)
    (hn : C ^ (4 * J + 4) ≤ (A.card : ℝ)) (B T : Finset (ZMod Q))
    (hT : T.card = 2 ^ j)
    (hB : (A.card : ℝ) ≤ C ^ j * (B.card : ℝ))
    (hD : Dec A K ((5 : ℝ) ^ j * K ^ (j + 1)) (C ^ j / C ^ (J + 1)) B) :
    ∃ δ : ZMod Q, δ ∉ (T ×ˢ T).image (fun p : ZMod Q × ZMod Q => p.1 - p.2) ∧
      (A.card : ℝ) ≤ C ^ (j + 1) * ((sh B δ).card : ℝ) ∧
      Dec A K ((5 : ℝ) ^ (j + 1) * K ^ (j + 2)) (C ^ (j + 1) / C ^ (J + 1)) (sh B δ) := by
  have hC0 : (0 : ℝ) ≤ C := by rw [hC]; positivity
  have hC1 : (1 : ℝ) ≤ C := by rw [hC]; nlinarith
  have hm := m_lb C (A.card : ℝ) (B.card : ℝ) hC1 j J hj hn hB
  obtain ⟨hL4, hL6, hF⟩ := numA K C (B.card : ℝ) hK hC j J hj hm
  obtain ⟨hτm, hnum2, hεK⟩ := numB K C (B.card : ℝ) hK hC j J hj hm
  have hKL : K ≤ (5 : ℝ) ^ j * K ^ (j + 1) := (num0 K C hK hC j).2
  have hFcard : ((((T ×ˢ T).image (fun p : ZMod Q × ZMod Q => p.1 - p.2)).card : ℕ) : ℝ) ≤ (4 : ℝ) ^ j := by
    have h1 : ((T ×ˢ T).image (fun p : ZMod Q × ZMod Q => p.1 - p.2)).card ≤ 2 ^ j * 2 ^ j := by
      calc ((T ×ˢ T).image (fun p : ZMod Q × ZMod Q => p.1 - p.2)).card ≤ (T ×ˢ T).card :=
            Finset.card_image_le
        _ = 2 ^ j * 2 ^ j := by rw [Finset.card_product, hT]
    have h2 : ((((T ×ˢ T).image (fun p : ZMod Q × ZMod Q => p.1 - p.2)).card : ℕ) : ℝ)
        ≤ ((2 ^ j * 2 ^ j : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 : ((2 ^ j * 2 ^ j : ℕ) : ℝ) = (4 : ℝ) ^ j := by
      push_cast
      rw [← mul_pow]
      norm_num
    linarith
  have hFb : 2 * (8192 * K ^ 2) * ((((T ×ˢ T).image (fun p : ZMod Q × ZMod Q => p.1 - p.2)).card : ℕ) : ℝ)
      ≤ (B.card : ℝ) := by
    rw [← hC]
    have := mul_le_mul_of_nonneg_left hFcard (by linarith : (0 : ℝ) ≤ 2 * C)
    linarith
  have hτnn : (0 : ℝ) ≤ C ^ j / (2 * C ^ J) :=
    div_nonneg (pow_nonneg hC0 j) (by have := pow_nonneg hC0 J; linarith)
  have hτm' : 2 * (8192 * K ^ 2) * ((5 : ℝ) ^ j * K ^ (j + 1)) ^ 4
      ≤ (C ^ j / (2 * C ^ J)) ^ 2 * (B.card : ℝ) := by
    rw [← hC]
    exact hτm
  obtain ⟨δ, hδF, hmδ, hDec⟩ := step A hA h0 K ((5 : ℝ) ^ j * K ^ (j + 1)) (C ^ j / C ^ (J + 1))
    (C ^ j / (2 * C ^ J)) hK hf hKL hεK B hD hL4 hL6 _ hFb hτnn hτm'
  refine ⟨δ, hδF, ?_, ?_⟩
  · calc (A.card : ℝ) ≤ C ^ j * (B.card : ℝ) := hB
      _ ≤ C ^ j * (C * ((sh B δ).card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hC0 j)
        rw [hC]
        exact hmδ
      _ = C ^ (j + 1) * ((sh B δ).card : ℝ) := by ring
  · exact dec_mono A (sh B δ) K (5 * K * ((5 : ℝ) ^ j * K ^ (j + 1))) ((5 : ℝ) ^ (j + 1) * K ^ (j + 2))
      (3 * K * (C ^ j / C ^ (J + 1)) + C ^ j / (2 * C ^ J)) (C ^ (j + 1) / C ^ (J + 1))
      (le_of_eq (by ring)) hnum2 hDec

theorem iter (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K C : ℝ)
    (hK : 1 ≤ K) (hC : C = 8192 * K ^ 2) (hf : ∀ x, -K ≤ fR A x) (J : ℕ)
    (hn : C ^ (4 * J + 4) ≤ (A.card : ℝ)) (j : ℕ) (hj : j ≤ J) :
    ∃ B T : Finset (ZMod Q), (∀ t ∈ T, ∀ b ∈ B, t + b ∈ A) ∧ T.card = 2 ^ j ∧
      (A.card : ℝ) ≤ C ^ j * (B.card : ℝ) ∧
      Dec A K ((5 : ℝ) ^ j * K ^ (j + 1)) (C ^ j / C ^ (J + 1)) B := by
  have hC0 : (0 : ℝ) ≤ C := by rw [hC]; positivity
  revert hj
  induction j with
  | zero =>
    intro _
    refine ⟨A, {0}, ?_, by simp, by simp, ?_⟩
    · intro t ht b hb
      rw [Finset.mem_singleton.mp ht, zero_add]
      exact hb
    · have hε : (0 : ℝ) ≤ C ^ 0 / C ^ (J + 1) := div_nonneg (pow_nonneg hC0 0) (pow_nonneg hC0 _)
      exact dec_mono A A K K ((5 : ℝ) ^ 0 * K ^ (0 + 1)) 0 (C ^ 0 / C ^ (J + 1))
        (le_of_eq (by ring)) hε (dec_base A hA K (by linarith) hf)
  | succ j ih =>
    intro hj
    obtain ⟨B, T, hTB, hT, hB, hD⟩ := ih (by omega)
    obtain ⟨δ, hδ, hmδ, hDec⟩ := iter_succ A hA h0 K C hK hC hf j J (by omega) hn B T hT hB hD
    obtain ⟨T', hT'card, hT'⟩ := T_double A B T δ hTB hδ
    refine ⟨sh B δ, T', hT', ?_, hmδ, hDec⟩
    rw [hT'card, hT]
    ring

theorem struct (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K : ℝ)
    (hK : 1 ≤ K) (hf : ∀ x, -K ≤ fR A x) (J : ℕ)
    (hn : (8192 * K ^ 2) ^ (4 * J + 4) ≤ (A.card : ℝ)) :
    ∃ (S T : Finset (ZMod Q)) (d : ZMod Q), d ≠ 0 ∧ T.card = 2 ^ J ∧ 2 ^ J ≤ S.card ∧
      ∀ s ∈ S, ∀ t ∈ T, s + t ∈ A ∧ s + t + d ∈ A := by
  have hC1 : (1 : ℝ) ≤ 8192 * K ^ 2 := by nlinarith
  obtain ⟨B, T, hTB, hT, hB, hD⟩ := iter A hA h0 K (8192 * K ^ 2) hK rfl hf J hn J le_rfl
  obtain ⟨δ, hδ, hmδ, _⟩ := iter_succ A hA h0 K (8192 * K ^ 2) hK rfl hf J J le_rfl hn B T hT hB hD
  have hδ0 : δ ≠ 0 := by
    intro h00
    have hTpos : 0 < T.card := by
      rw [hT]
      positivity
    obtain ⟨t, ht⟩ := Finset.card_pos.mp hTpos
    apply hδ
    exact Finset.mem_image.mpr ⟨(t, t), Finset.mem_product.mpr ⟨ht, ht⟩, by simp [h00]⟩
  refine ⟨sh B δ, T, δ, hδ0, hT, ?_, ?_⟩
  · have hpos : (0 : ℝ) < (8192 * K ^ 2) ^ (J + 1) := by positivity
    have e4 : (8192 * K ^ 2) ^ (4 * J + 4)
        = (8192 * K ^ 2) ^ (J + 1) * (8192 * K ^ 2) ^ (3 * J + 3) := by ring
    have h1 := hn.trans hmδ
    rw [e4] at h1
    have h2 : (8192 * K ^ 2) ^ (3 * J + 3) ≤ ((sh B δ).card : ℝ) :=
      le_of_mul_le_mul_left h1 hpos
    have h3 : (2 : ℝ) ^ J ≤ (8192 * K ^ 2) ^ J :=
      pow_le_pow_left₀ (by norm_num) (by nlinarith) J
    have h4 : (8192 * K ^ 2) ^ J ≤ (8192 * K ^ 2) ^ (3 * J + 3) :=
      pow_le_pow_right₀ hC1 (by omega)
    have h5 : (2 : ℝ) ^ J ≤ ((sh B δ).card : ℝ) := by linarith
    exact_mod_cast h5
  · intro s hs t ht
    simp only [sh, Finset.mem_filter] at hs
    obtain ⟨hsB, hsδ⟩ := hs
    refine ⟨?_, ?_⟩
    · rw [add_comm]
      exact hTB t ht s hsB
    · have h6 := hTB t ht (s + δ) hsδ
      rw [show s + t + δ = t + (s + δ) by ring]
      exact h6

/- ## Block M: from structure to minimum (Ruzsa Lemma 3.1) -/

theorem psd_id_aux1 (c : ZMod Q → ℝ) (x : ZMod Q) :
    ((‖∑ y, ((c y : ℝ) : ℂ) * e (y * x)‖ ^ 2 : ℝ) : ℂ) =
      ∑ y : ZMod Q, ∑ y' : ZMod Q, ((c y : ℂ) * (c y' : ℂ)) * e ((y - y') * x) := by
  have key : ∀ y y' : ZMod Q, e ((y - y') * x) = e (y * x) * (starRingEnd ℂ) (e (y' * x)) := by
    intro y y'
    have h1 : (y - y') * x = y * x + -(y' * x) := by ring
    rw [h1, (e_basic (y * x) (-(y' * x))).1, (e_basic (y' * x) 0).2.2.2]
  have hz : ((‖∑ y, ((c y : ℝ) : ℂ) * e (y * x)‖ ^ 2 : ℝ) : ℂ) =
      (∑ y, ((c y : ℝ) : ℂ) * e (y * x)) * (starRingEnd ℂ) (∑ y, ((c y : ℝ) : ℂ) * e (y * x)) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hz, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
  rw [map_mul, Complex.conj_ofReal, key y y']
  ring

theorem psd_id_aux3 (u v x : ZMod Q) : e (u * x) * e (v * x) = e ((u + v) * x) := by
  rw [← (e_basic (u * x) (v * x)).1, add_mul]

theorem psd_id_aux2 (A : Finset (ZMod Q)) (K : ℝ) (c : ZMod Q → ℝ) (x : ZMod Q) :
    (∑ y : ZMod Q, ∑ y' : ZMod Q, ((c y : ℂ) * (c y' : ℂ)) * e ((y - y') * x)) *
        (∑ a ∈ A, e (a * x) + (K : ℂ))
      = ∑ y : ZMod Q, ∑ y' : ZMod Q, ∑ a ∈ A, ((c y : ℂ) * (c y' : ℂ)) * e ((y - y' + a) * x)
        + ∑ y : ZMod Q, ∑ y' : ZMod Q, ((c y : ℂ) * (c y' : ℂ)) * e ((y - y') * x) * (K : ℂ) := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [mul_assoc]
  rw [psd_id_aux3]

theorem psd_id_swap3 (f : ZMod Q → ZMod Q → ZMod Q → ℂ) :
    ∑ x : ZMod Q, ∑ y : ZMod Q, ∑ z : ZMod Q, f x y z = ∑ y : ZMod Q, ∑ z : ZMod Q, ∑ x : ZMod Q, f x y z := by
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Finset.sum_comm

theorem psd_id_swap4 (f : ZMod Q → ZMod Q → ZMod Q → ZMod Q → ℂ) :
    ∑ x : ZMod Q, ∑ y : ZMod Q, ∑ z : ZMod Q, ∑ w : ZMod Q, f x y z w
      = ∑ y : ZMod Q, ∑ z : ZMod Q, ∑ w : ZMod Q, ∑ x : ZMod Q, f x y z w := by
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => psd_id_swap3 (fun x z w => f x y z w)

theorem psd_id_swap4A (A : Finset (ZMod Q)) (f : ZMod Q → ZMod Q → ZMod Q → ZMod Q → ℂ) :
    ∑ x : ZMod Q, ∑ y : ZMod Q, ∑ z : ZMod Q, ∑ a ∈ A, f x y z a
      = ∑ y : ZMod Q, ∑ z : ZMod Q, ∑ a ∈ A, ∑ x : ZMod Q, f x y z a := by
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact Finset.sum_comm

theorem psd_id_hs (A : Finset (ZMod Q)) (y y' : ZMod Q) :
    ∑ a ∈ A, (if y - y' + a = 0 then (1 : ℂ) else 0) = if y' - y ∈ A then (1 : ℂ) else 0 := by
  have h : ∀ a : ZMod Q, (y - y' + a = 0 ↔ a = y' - y) := fun a => by
    constructor
    · intro h1
      linear_combination h1
    · intro h1
      linear_combination h1
  simp only [h]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem psd_id_P1 (A : Finset (ZMod Q)) (c : ZMod Q → ℝ) :
    ∑ x : ZMod Q, ∑ y : ZMod Q, ∑ y' : ZMod Q, ∑ a ∈ A,
        ((c y : ℂ) * (c y' : ℂ)) * e ((y - y' + a) * x)
      = (Q : ℂ) * ∑ y : ZMod Q, ∑ y' : ZMod Q,
          (c y : ℂ) * (c y' : ℂ) * (if y' - y ∈ A then (1 : ℂ) else 0) := by
  have hs : ∑ x : ZMod Q, ∑ y : ZMod Q, ∑ y' : ZMod Q, ∑ a ∈ A,
      ((c y : ℂ) * (c y' : ℂ)) * e ((y - y' + a) * x)
      = ∑ y : ZMod Q, ∑ y' : ZMod Q, ∑ a ∈ A, ∑ x : ZMod Q,
          ((c y : ℂ) * (c y' : ℂ)) * e ((y - y' + a) * x) :=
    psd_id_swap4A A (fun x y y' a => ((c y : ℂ) * (c y' : ℂ)) * e ((y - y' + a) * x))
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  have inner : ∀ a : ZMod Q, ∑ x : ZMod Q, ((c y : ℂ) * (c y' : ℂ)) * e ((y - y' + a) * x)
      = ((c y : ℂ) * (c y' : ℂ)) * ((Q : ℂ) * if y - y' + a = 0 then 1 else 0) := by
    intro a
    rw [← Finset.mul_sum, e_orth]
    split_ifs <;> ring
  simp only [inner]
  rw [← Finset.mul_sum, ← Finset.mul_sum, psd_id_hs A y y']
  ring

theorem psd_id_P2 (K : ℝ) (c : ZMod Q → ℝ) :
    ∑ x : ZMod Q, ∑ y : ZMod Q, ∑ y' : ZMod Q, ((c y : ℂ) * (c y' : ℂ)) * e ((y - y') * x) * (K : ℂ)
      = (Q : ℂ) * ((K : ℂ) * ∑ y : ZMod Q, (c y : ℂ) ^ 2) := by
  rw [psd_id_swap3]
  have inner : ∀ y y' : ZMod Q, ∑ x : ZMod Q, ((c y : ℂ) * (c y' : ℂ)) * e ((y - y') * x) * (K : ℂ)
      = ((c y : ℂ) * (c y' : ℂ) * (K : ℂ)) * ((Q : ℂ) * if y = y' then 1 else 0) := by
    intro y y'
    rw [← Finset.sum_mul, ← Finset.mul_sum, e_orth]
    by_cases h : y = y'
    · subst h
      rw [if_pos (sub_self _), if_pos rfl]
      ring
    · have h' : y - y' ≠ 0 := sub_ne_zero.mpr h
      simp [h, h']
  simp only [inner]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [mul_ite, Finset.sum_ite_eq] <;> ring

theorem psd_id (A : Finset (ZMod Q)) (K : ℝ) (c : ZMod Q → ℝ) :
    ∑ x : ZMod Q, ‖∑ y, ((c y : ℝ) : ℂ) * e (y * x)‖ ^ 2 * (fR A x + K) =
      (Q : ℝ) * Phi A K c := by
  have hreG : ∀ x : ZMod Q, (∑ a ∈ A, e (a * x)).re = fR A x := fun x => by
    simp only [fR, Complex.re_sum]
  have hcomm : ∑ y : ZMod Q, ∑ y' : ZMod Q, (c y : ℂ) * (c y' : ℂ) * (if y' - y ∈ A then (1 : ℂ) else 0)
      = ∑ x : ZMod Q, ∑ y : ZMod Q, (c x : ℂ) * (c y : ℂ) * (if x - y ∈ A then (1 : ℂ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  have hPhi : (((Q : ℝ) * Phi A K c : ℝ) : ℂ) =
      (Q : ℂ) * (∑ y : ZMod Q, ∑ y' : ZMod Q, (c y : ℂ) * (c y' : ℂ) * (if y' - y ∈ A then (1 : ℂ) else 0))
        + (Q : ℂ) * ((K : ℂ) * ∑ y : ZMod Q, (c y : ℂ) ^ 2) := by
    rw [hcomm]
    simp only [Phi]
    push_cast
    simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero]
    ring
  have hM : ∑ x : ZMod Q, ((‖∑ y, ((c y : ℝ) : ℂ) * e (y * x)‖ ^ 2 : ℝ) : ℂ) * ((∑ a ∈ A, e (a * x)) + (K : ℂ))
      = (((Q : ℝ) * Phi A K c : ℝ) : ℂ) := by
    simp only [psd_id_aux1, psd_id_aux2]
    rw [Finset.sum_add_distrib, psd_id_P1, psd_id_P2, hPhi]
  have hre := congrArg Complex.re hM
  rw [Complex.re_sum, Complex.ofReal_re] at hre
  refine Eq.trans ?_ hre
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re, hreG]

theorem psd (A : Finset (ZMod Q)) (K : ℝ) (hf : ∀ x, -K ≤ fR A x) (c : ZMod Q → ℝ) :
    0 ≤ Phi A K c := by
  have hid := psd_id A K c
  have hQ : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (Fact.out : Q.Prime).pos
  have hnn : 0 ≤ ∑ x : ZMod Q, ‖∑ y, ((c y : ℝ) : ℂ) * e (y * x)‖ ^ 2 * (fR A x + K) := by
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (sq_nonneg _)
    linarith [hf x]
  rw [hid] at hnn
  nlinarith

theorem phi_shift (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K t : ℝ)
    (c : ZMod Q → ℝ) :
    Phi A K (fun x => c x + if x = 0 then t else 0) =
      Phi A K c + 2 * t * ((∑ x, c x * (if x ∈ A then (1 : ℝ) else 0)) + K * c 0) +
        t ^ 2 * K := by
  have hsym : ∀ y : ZMod Q, (-y ∈ A ↔ y ∈ A) := fun y =>
    ⟨fun h => by simpa using hA _ h, fun h => hA y h⟩
  have key : ∀ x y : ZMod Q,
      (c x + (if x = 0 then t else 0)) * (c y + (if y = 0 then t else 0)) * (if x - y ∈ A then (1 : ℝ) else 0)
        = c x * c y * (if x - y ∈ A then (1 : ℝ) else 0)
          + ((if x = 0 then t else 0) * (c y * (if x - y ∈ A then (1 : ℝ) else 0))
            + c x * ((if y = 0 then t else 0) * (if x - y ∈ A then (1 : ℝ) else 0))
            + (if x = 0 then t else 0) * (if y = 0 then t else 0) * (if x - y ∈ A then (1 : ℝ) else 0)) := by
    intro x y
    ring
  have H1 : ∑ x : ZMod Q, ∑ y : ZMod Q, (if x = 0 then t else 0) * (c y * (if x - y ∈ A then (1 : ℝ) else 0))
      = t * ∑ y : ZMod Q, c y * (if y ∈ A then (1 : ℝ) else 0) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single (0 : ZMod Q)]
    · simp [hsym]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have H2 : ∑ x : ZMod Q, ∑ y : ZMod Q, c x * ((if y = 0 then t else 0) * (if x - y ∈ A then (1 : ℝ) else 0))
      = t * ∑ x : ZMod Q, c x * (if x ∈ A then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single (0 : ZMod Q)]
    · rw [if_pos rfl, sub_zero]
      ring
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have H3 : ∑ x : ZMod Q, ∑ y : ZMod Q,
      (if x = 0 then t else 0) * (if y = 0 then t else 0) * (if x - y ∈ A then (1 : ℝ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy, h0]
  have Kpart : ∑ x : ZMod Q, (c x + (if x = 0 then t else 0)) ^ 2
      = ∑ x : ZMod Q, c x ^ 2 + 2 * t * c 0 + t ^ 2 := by
    have hp : ∀ x : ZMod Q, (c x + (if x = 0 then t else 0)) ^ 2
        = c x ^ 2 + 2 * (if x = 0 then t * c x else 0) + (if x = 0 then t ^ 2 else 0) := by
      intro x
      by_cases hx : x = 0 <;> simp [hx] <;> ring
    simp [hp, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq'] <;> ring
  have hquad : ∑ x : ZMod Q, ∑ y : ZMod Q,
      (c x + (if x = 0 then t else 0)) * (c y + (if y = 0 then t else 0)) * (if x - y ∈ A then (1 : ℝ) else 0)
      = (∑ x : ZMod Q, ∑ y : ZMod Q, c x * c y * (if x - y ∈ A then (1 : ℝ) else 0))
        + 2 * t * ∑ x : ZMod Q, c x * (if x ∈ A then (1 : ℝ) else 0) := by
    simp only [key, Finset.sum_add_distrib]
    rw [H1, H2, H3]
    ring
  simp only [Phi]
  rw [hquad, Kpart]
  ring

theorem phi_UV (A : Finset (ZMod Q)) (hA : Sym A) (K α β : ℝ) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (U V : Finset (ZMod Q)) (hUV : ∀ u ∈ U, ∀ v ∈ V, u - v ∈ A) :
    Phi A K (fun x => (if x ∈ U then α else 0) - (if x ∈ V then β else 0)) ≤
      α ^ 2 * (U.card : ℝ) ^ 2 + β ^ 2 * (V.card : ℝ) ^ 2 -
        2 * α * β * (U.card : ℝ) * (V.card : ℝ) +
        K * (α ^ 2 * (U.card : ℝ) + β ^ 2 * (V.card : ℝ)) := by
  classical
  have hsymm : ∀ x ∈ V, ∀ y ∈ U, x - y ∈ A := by
    intro x hx y hy
    have h1 := hA _ (hUV y hy x hx)
    have e : -(y - x) = x - y := by ring
    rwa [e] at h1
  have hsumU : ∑ x : ZMod Q, (if x ∈ U then (1 : ℝ) else 0) = (U.card : ℝ) := by
    simp [Finset.sum_boole]
  have hsumV : ∑ x : ZMod Q, (if x ∈ V then (1 : ℝ) else 0) = (V.card : ℝ) := by
    simp [Finset.sum_boole]
  have hid : ∀ x y : ZMod Q,
      ((if x ∈ U then α else 0) - (if x ∈ V then β else 0)) *
        ((if y ∈ U then α else 0) - (if y ∈ V then β else 0)) *
        (if x - y ∈ A then (1 : ℝ) else 0) =
      α ^ 2 * ((if x ∈ U then (1 : ℝ) else 0) * (if y ∈ U then (1 : ℝ) else 0) *
          (if x - y ∈ A then (1 : ℝ) else 0))
      - α * β * ((if x ∈ U then (1 : ℝ) else 0) * (if y ∈ V then (1 : ℝ) else 0) *
          (if x - y ∈ A then (1 : ℝ) else 0))
      - α * β * ((if x ∈ V then (1 : ℝ) else 0) * (if y ∈ U then (1 : ℝ) else 0) *
          (if x - y ∈ A then (1 : ℝ) else 0))
      + β ^ 2 * ((if x ∈ V then (1 : ℝ) else 0) * (if y ∈ V then (1 : ℝ) else 0) *
          (if x - y ∈ A then (1 : ℝ) else 0)) := by
    intro x y
    split_ifs <;> ring
  have hcr1 : ∀ x y : ZMod Q, (if x ∈ U then (1 : ℝ) else 0) * (if y ∈ V then (1 : ℝ) else 0) *
      (if x - y ∈ A then (1 : ℝ) else 0) =
      (if x ∈ U then (1 : ℝ) else 0) * (if y ∈ V then (1 : ℝ) else 0) := by
    intro x y
    by_cases h1 : x ∈ U
    · by_cases h2 : y ∈ V
      · simp [h1, h2, hUV x h1 y h2]
      · simp [h2]
    · simp [h1]
  have hcr2 : ∀ x y : ZMod Q, (if x ∈ V then (1 : ℝ) else 0) * (if y ∈ U then (1 : ℝ) else 0) *
      (if x - y ∈ A then (1 : ℝ) else 0) =
      (if x ∈ V then (1 : ℝ) else 0) * (if y ∈ U then (1 : ℝ) else 0) := by
    intro x y
    by_cases h1 : x ∈ V
    · by_cases h2 : y ∈ U
      · simp [h1, h2, hsymm x h1 y h2]
      · simp [h2]
    · simp [h1]
  have hPU : ∀ x y : ZMod Q, (if x ∈ U then (1 : ℝ) else 0) * (if y ∈ U then (1 : ℝ) else 0) *
      (if x - y ∈ A then (1 : ℝ) else 0) ≤
      (if x ∈ U then (1 : ℝ) else 0) * (if y ∈ U then (1 : ℝ) else 0) := by
    intro x y
    have h0 : 0 ≤ (if x ∈ U then (1 : ℝ) else 0) * (if y ∈ U then (1 : ℝ) else 0) := by
      positivity
    have h1 : (if x - y ∈ A then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hPV : ∀ x y : ZMod Q, (if x ∈ V then (1 : ℝ) else 0) * (if y ∈ V then (1 : ℝ) else 0) *
      (if x - y ∈ A then (1 : ℝ) else 0) ≤
      (if x ∈ V then (1 : ℝ) else 0) * (if y ∈ V then (1 : ℝ) else 0) := by
    intro x y
    have h0 : 0 ≤ (if x ∈ V then (1 : ℝ) else 0) * (if y ∈ V then (1 : ℝ) else 0) := by
      positivity
    have h1 : (if x - y ∈ A then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]
  have hS1 : ∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ U then (1 : ℝ) else 0) *
      (if y ∈ U then (1 : ℝ) else 0) * (if x - y ∈ A then (1 : ℝ) else 0) ≤ (U.card : ℝ) ^ 2 := by
    calc _ ≤ ∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ U then (1 : ℝ) else 0) *
            (if y ∈ U then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hPU x y
      _ = (∑ x : ZMod Q, (if x ∈ U then (1 : ℝ) else 0)) *
            (∑ y : ZMod Q, (if y ∈ U then (1 : ℝ) else 0)) := by rw [Finset.sum_mul_sum]
      _ = (U.card : ℝ) ^ 2 := by rw [hsumU]; ring
  have hS4 : ∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ V then (1 : ℝ) else 0) *
      (if y ∈ V then (1 : ℝ) else 0) * (if x - y ∈ A then (1 : ℝ) else 0) ≤ (V.card : ℝ) ^ 2 := by
    calc _ ≤ ∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ V then (1 : ℝ) else 0) *
            (if y ∈ V then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hPV x y
      _ = (∑ x : ZMod Q, (if x ∈ V then (1 : ℝ) else 0)) *
            (∑ y : ZMod Q, (if y ∈ V then (1 : ℝ) else 0)) := by rw [Finset.sum_mul_sum]
      _ = (V.card : ℝ) ^ 2 := by rw [hsumV]; ring
  have hS2 : ∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ U then (1 : ℝ) else 0) *
      (if y ∈ V then (1 : ℝ) else 0) * (if x - y ∈ A then (1 : ℝ) else 0) =
      (U.card : ℝ) * (V.card : ℝ) := by
    simp only [hcr1]
    rw [← hsumU, ← hsumV, Finset.sum_mul_sum]
  have hS3 : ∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ V then (1 : ℝ) else 0) *
      (if y ∈ U then (1 : ℝ) else 0) * (if x - y ∈ A then (1 : ℝ) else 0) =
      (V.card : ℝ) * (U.card : ℝ) := by
    simp only [hcr2]
    rw [← hsumU, ← hsumV, Finset.sum_mul_sum]
  have hc : ∑ x : ZMod Q, ((if x ∈ U then α else 0) - (if x ∈ V then β else 0)) ^ 2 ≤
      α ^ 2 * (U.card : ℝ) + β ^ 2 * (V.card : ℝ) := by
    have hpt : ∀ x : ZMod Q, ((if x ∈ U then α else 0) - (if x ∈ V then β else 0)) ^ 2 ≤
        α ^ 2 * (if x ∈ U then (1 : ℝ) else 0) + β ^ 2 * (if x ∈ V then (1 : ℝ) else 0) := by
      intro x
      by_cases h1 : x ∈ U <;> by_cases h2 : x ∈ V <;> simp [h1, h2] <;>
        nlinarith [mul_nonneg hα hβ]
    calc _ ≤ ∑ x : ZMod Q, (α ^ 2 * (if x ∈ U then (1 : ℝ) else 0) +
            β ^ 2 * (if x ∈ V then (1 : ℝ) else 0)) := Finset.sum_le_sum fun x _ => hpt x
      _ = α ^ 2 * (U.card : ℝ) + β ^ 2 * (V.card : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsumU, hsumV]
  have hmain : (∑ x : ZMod Q, ∑ y : ZMod Q, ((if x ∈ U then α else 0) - (if x ∈ V then β else 0)) *
        ((if y ∈ U then α else 0) - (if y ∈ V then β else 0)) *
        (if x - y ∈ A then (1 : ℝ) else 0)) =
      α ^ 2 * (∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ U then (1 : ℝ) else 0) *
          (if y ∈ U then (1 : ℝ) else 0) * (if x - y ∈ A then (1 : ℝ) else 0))
      - α * β * (∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ U then (1 : ℝ) else 0) *
          (if y ∈ V then (1 : ℝ) else 0) * (if x - y ∈ A then (1 : ℝ) else 0))
      - α * β * (∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ V then (1 : ℝ) else 0) *
          (if y ∈ U then (1 : ℝ) else 0) * (if x - y ∈ A then (1 : ℝ) else 0))
      + β ^ 2 * (∑ x : ZMod Q, ∑ y : ZMod Q, (if x ∈ V then (1 : ℝ) else 0) *
          (if y ∈ V then (1 : ℝ) else 0) * (if x - y ∈ A then (1 : ℝ) else 0)) := by
    simp only [hid, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [Phi]
  rw [hmain, hS2, hS3]
  have hPb := mul_le_mul_of_nonneg_left hS1 (sq_nonneg α)
  have hTb := mul_le_mul_of_nonneg_left hS4 (sq_nonneg β)
  have hKb := mul_le_mul_of_nonneg_left hc hK
  linarith [hPb, hTb, hKb]

theorem min_UV (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K : ℝ)
    (hK : 0 < K) (hpsd : ∀ c : ZMod Q → ℝ, 0 ≤ Phi A K c) (U V : Finset (ZMod Q))
    (hU : U ⊆ A) (hV : ∀ v ∈ V, v ∉ A) (hV0 : (0 : ZMod Q) ∉ V)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u - v ∈ A) (l : ℕ) (hl : 0 < l) (hlU : l ≤ U.card)
    (hlV : l ≤ V.card) : (l : ℝ) ≤ 2 * K ^ 2 := by
  classical
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hlU' : (l : ℝ) ≤ U.card := by exact_mod_cast hlU
  have hlV' : (l : ℝ) ≤ V.card := by exact_mod_cast hlV
  have hUpos : (0 : ℝ) < U.card := lt_of_lt_of_le hl' hlU'
  have hVpos : (0 : ℝ) < V.card := lt_of_lt_of_le hl' hlV'
  have hUne : (U.card : ℝ) ≠ 0 := hUpos.ne'
  have hVne : (V.card : ℝ) ≠ 0 := hVpos.ne'
  have h0U : (0 : ZMod Q) ∉ U := fun h => h0 (hU h)
  have hbound := phi_UV A hA K (1 / (U.card : ℝ)) (1 / (V.card : ℝ)) hK.le
    (by positivity) (by positivity) U V hUV
  have e1 : (1 / (U.card : ℝ)) ^ 2 * (U.card : ℝ) ^ 2 = 1 := by field_simp
  have e2 : (1 / (V.card : ℝ)) ^ 2 * (V.card : ℝ) ^ 2 = 1 := by field_simp
  have e3 : 2 * (1 / (U.card : ℝ)) * (1 / (V.card : ℝ)) * (U.card : ℝ) * (V.card : ℝ) = 2 := by
    field_simp
  have e4 : (1 / (U.card : ℝ)) ^ 2 * (U.card : ℝ) = 1 / (U.card : ℝ) := by field_simp
  have e5 : (1 / (V.card : ℝ)) ^ 2 * (V.card : ℝ) = 1 / (V.card : ℝ) := by field_simp
  have hbound2 : Phi A K (fun x => (if x ∈ U then 1 / (U.card : ℝ) else 0) -
      (if x ∈ V then 1 / (V.card : ℝ) else 0)) ≤
      K * (1 / (U.card : ℝ) + 1 / (V.card : ℝ)) := by
    have e7 : K * ((1 / (U.card : ℝ)) ^ 2 * (U.card : ℝ) + (1 / (V.card : ℝ)) ^ 2 * (V.card : ℝ)) =
        K * (1 / (U.card : ℝ) + 1 / (V.card : ℝ)) := by
      rw [e4, e5]
    linarith [hbound, e1, e2, e3, e7]
  have hsA : ∑ x : ZMod Q, ((if x ∈ U then 1 / (U.card : ℝ) else 0) -
      (if x ∈ V then 1 / (V.card : ℝ) else 0)) * (if x ∈ A then (1 : ℝ) else 0) = 1 := by
    have hpt : ∀ x : ZMod Q, ((if x ∈ U then 1 / (U.card : ℝ) else 0) -
        (if x ∈ V then 1 / (V.card : ℝ) else 0)) * (if x ∈ A then (1 : ℝ) else 0) =
        (if x ∈ U then 1 / (U.card : ℝ) else 0) := by
      intro x
      by_cases h1 : x ∈ U
      · have h3 : x ∈ A := hU h1
        have h2 : x ∉ V := fun h => hV x h h3
        simp [h1, h2, h3]
      · by_cases h2 : x ∈ V
        · have h3 : x ∉ A := hV x h2
          simp [h1, h2, h3]
        · simp [h1, h2]
    rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
    field_simp
  have h00 : ((if (0 : ZMod Q) ∈ U then 1 / (U.card : ℝ) else 0) -
      (if (0 : ZMod Q) ∈ V then 1 / (V.card : ℝ) else 0)) = 0 := by
    simp [h0U, hV0]
  have hp := hpsd (fun x => ((if x ∈ U then 1 / (U.card : ℝ) else 0) -
      (if x ∈ V then 1 / (V.card : ℝ) else 0)) + if x = 0 then (-1 / K) else 0)
  rw [phi_shift A hA h0 K] at hp
  rw [hsA, h00] at hp
  have e6 : 2 * (-1 / K) * (1 + K * 0) + (-1 / K) ^ 2 * K = -(1 / K) := by
    field_simp
    ring
  have hkey : 1 / K ≤ K * (1 / (U.card : ℝ) + 1 / (V.card : ℝ)) := by
    linarith [hp, hbound2, e6]
  have hUl : 1 / (U.card : ℝ) ≤ 1 / (l : ℝ) := one_div_le_one_div_of_le hl' hlU'
  have hVl : 1 / (V.card : ℝ) ≤ 1 / (l : ℝ) := one_div_le_one_div_of_le hl' hlV'
  have hkey2 : 1 / K ≤ K * (2 / (l : ℝ)) := by
    have h7 : K * (1 / (U.card : ℝ) + 1 / (V.card : ℝ)) ≤ K * (2 / (l : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      have h8 : (2 : ℝ) / l = 1 / l + 1 / l := by ring
      linarith
    linarith
  rw [div_le_iff₀ hK] at hkey2
  have h9 : K * (2 / (l : ℝ)) * K = 2 * K ^ 2 / (l : ℝ) := by ring
  rw [h9, le_div_iff₀ hl'] at hkey2
  linarith

theorem chain_count (A S : Finset (ZMod Q)) (d t0 : ZMod Q) (hd : d ≠ 0) (l : ℕ)
    (h0 : l ≤ (S.filter (fun s => s + t0 + 0 * d ∈ A)).card)
    (hQ : S.card * A.card < l * Q) :
    ∃ x : ZMod Q, l ≤ (S.filter (fun s => s + t0 + x * d ∈ A)).card ∧
      (S.filter (fun s => s + t0 + (x + 1) * d ∈ A)).card < l := by
  classical
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ n : ℕ, l ≤ (S.filter (fun s => s + t0 + (n : ZMod Q) * d ∈ A)).card := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have := hcon (n : ZMod Q) ih
      push_cast
      exact this
  have hall : ∀ x : ZMod Q, l ≤ (S.filter (fun s => s + t0 + x * d ∈ A)).card := by
    intro x
    have := hstep x.val
    rwa [ZMod.natCast_zmod_val] at this
  have hsum : ∑ x : ZMod Q, (S.filter (fun s => s + t0 + x * d ∈ A)).card = S.card * A.card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    rw [show S.card * A.card = ∑ s ∈ S, A.card by simp]
    apply Finset.sum_congr rfl
    intro s _
    have hb : Function.Bijective (fun x : ZMod Q => s + t0 + x * d) := by
      apply Finite.injective_iff_bijective.mp
      intro a b hab
      have hab' : s + t0 + a * d = s + t0 + b * d := hab
      exact mul_right_cancel₀ hd (add_left_cancel hab')
    rw [Fintype.sum_bijective (fun x : ZMod Q => s + t0 + x * d) hb
      (fun x : ZMod Q => if s + t0 + x * d ∈ A then 1 else 0)
      (fun y : ZMod Q => if y ∈ A then 1 else 0) (fun x => rfl)]
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    congr 1
    ext y
    simp
  have hle : ∑ x : ZMod Q, l ≤ ∑ x : ZMod Q, (S.filter (fun s => s + t0 + x * d ∈ A)).card :=
    Finset.sum_le_sum fun x _ => hall x
  rw [hsum] at hle
  have hQl : Fintype.card (ZMod Q) * l ≤ S.card * A.card := by
    simpa [Finset.sum_const, Finset.card_univ] using hle
  rw [ZMod.card] at hQl
  linarith

theorem chain_UV (A : Finset (ZMod Q)) (hA : Sym A) (S T : Finset (ZMod Q)) (d t0 : ZMod Q)
    (ht0 : t0 ∈ T) (hST : ∀ s ∈ S, ∀ t ∈ T, s + t ∈ A ∧ s + t + d ∈ A) (l : ℕ)
    (hS : S.card = 2 * l) (hT : 2 * l ≤ T.card) (x : ZMod Q)
    (hx : l ≤ (S.filter (fun s => s + t0 + x * d ∈ A)).card)
    (hx1 : (S.filter (fun s => s + t0 + (x + 1) * d ∈ A)).card < l) :
    ∃ U V : Finset (ZMod Q), U ⊆ A ∧ (∀ v ∈ V, v ∉ A) ∧ (0 : ZMod Q) ∉ V ∧
      (∀ u ∈ U, ∀ v ∈ V, u - v ∈ A) ∧ l ≤ U.card ∧ l ≤ V.card := by
  classical
  have hYc : (T.image (fun t => t0 + x * d - t)).card = T.card :=
    Finset.card_image_of_injective _ sub_right_injective
  have hinjA : Function.Injective (fun s : ZMod Q => s + t0 + x * d) := fun a b h =>
    add_right_cancel (add_right_cancel (show a + t0 + x * d = b + t0 + x * d from h))
  have hinjB : Function.Injective (fun s : ZMod Q => s + t0 + (x + 1) * d) := fun a b h =>
    add_right_cancel (add_right_cancel (show a + t0 + (x + 1) * d = b + t0 + (x + 1) * d from h))
  by_cases hcase : l ≤ ((T.image (fun t => t0 + x * d - t)).filter (fun v => v ∈ A)).card
  · refine ⟨(T.image (fun t => t0 + x * d - t)).filter (fun v => v ∈ A),
      ((S.filter (fun s => s + t0 + (x + 1) * d ∉ A)).image (fun s => s + t0 + (x + 1) * d)).erase 0,
      (fun u hu => (Finset.mem_filter.mp hu).2), ?_, ?_, ?_, hcase, ?_⟩
    · intro v hv
      obtain ⟨_, hvi⟩ := Finset.mem_erase.mp hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hvi
      exact (Finset.mem_filter.mp hs).2
    · exact fun h => (Finset.mem_erase.mp h).1 rfl
    · intro u hu v hv
      obtain ⟨hu1, _⟩ := Finset.mem_filter.mp hu
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu1
      obtain ⟨_, hvi⟩ := Finset.mem_erase.mp hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hvi
      have hs' := (Finset.mem_filter.mp hs).1
      have hsm := (hST s hs' t ht).2
      have e : t0 + x * d - t - (s + t0 + (x + 1) * d) = -(s + t + d) := by ring
      rw [e]
      exact hA _ hsm
    · have hcardV : ((S.filter (fun s => s + t0 + (x + 1) * d ∉ A)).image
          (fun s => s + t0 + (x + 1) * d)).card = (S.filter (fun s => s + t0 + (x + 1) * d ∉ A)).card :=
        Finset.card_image_of_injective _ hinjB
      have hsplit := Finset.card_filter_add_card_filter_not
        (s := S) (fun s => s + t0 + (x + 1) * d ∈ A)
      have herase := (Finset.pred_card_le_card_erase (s := ((S.filter (fun s => s + t0 + (x + 1) * d ∉ A)).image
          (fun s => s + t0 + (x + 1) * d))) (a := 0))
      omega
  · push_neg at hcase
    refine ⟨(S.filter (fun s => s + t0 + x * d ∈ A)).image (fun s => s + t0 + x * d),
      ((T.image (fun t => t0 + x * d - t)).filter (fun v => v ∉ A)).erase 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hs).2
    · intro v hv
      exact (Finset.mem_filter.mp (Finset.mem_erase.mp hv).2).2
    · exact fun h => (Finset.mem_erase.mp h).1 rfl
    · intro u hu v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨_, hvi⟩ := Finset.mem_erase.mp hv
      obtain ⟨hvY, _⟩ := Finset.mem_filter.mp hvi
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hvY
      have e : s + t0 + x * d - (t0 + x * d - t) = s + t := by ring
      rw [e]
      exact (hST s (Finset.mem_filter.mp hs).1 t ht).1
    · rw [Finset.card_image_of_injective _ hinjA]
      exact hx
    · have hsplit2 := Finset.card_filter_add_card_filter_not
        (s := T.image (fun t => t0 + x * d - t)) (fun v => v ∈ A)
      have herase := (Finset.pred_card_le_card_erase (s := ((T.image (fun t => t0 + x * d - t)).filter
          (fun v => v ∉ A))) (a := 0))
      omega

theorem min_bound (A : Finset (ZMod Q)) (hA : Sym A) (h0 : (0 : ZMod Q) ∉ A) (K : ℝ)
    (hK : 0 < K) (hf : ∀ x, -K ≤ fR A x) (S T : Finset (ZMod Q)) (d : ZMod Q) (hd : d ≠ 0)
    (hST : ∀ s ∈ S, ∀ t ∈ T, s + t ∈ A ∧ s + t + d ∈ A) (l : ℕ) (hl : 0 < l)
    (hS : 2 * l ≤ S.card) (hT : 2 * l ≤ T.card) (hQ : 2 * A.card < Q) :
    (l : ℝ) ≤ 2 * K ^ 2 := by
  classical
  have hT0 : 0 < T.card := by omega
  obtain ⟨t0, ht0⟩ := Finset.card_pos.mp hT0
  obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hS
  have hST' : ∀ s ∈ S', ∀ t ∈ T, s + t ∈ A ∧ s + t + d ∈ A :=
    fun s hs t ht => hST s (hS'sub hs) t ht
  have hfilt : S'.filter (fun s => s + t0 + 0 * d ∈ A) = S' := by
    apply Finset.filter_true_of_mem
    intro s hs
    have h1 := (hST' s hs t0 ht0).1
    simpa using h1
  have h0' : l ≤ (S'.filter (fun s => s + t0 + 0 * d ∈ A)).card := by
    rw [hfilt, hS'card]
    omega
  have hQ' : S'.card * A.card < l * Q := by
    rw [hS'card]
    nlinarith
  obtain ⟨x, hx, hx1⟩ := chain_count A S' d t0 hd l h0' hQ'
  obtain ⟨U, V, hUA, hVA, hV0, hUV, hlU, hlV⟩ :=
    chain_UV A hA S' T d t0 ht0 hST' l hS'card hT x hx hx1
  exact min_UV A hA h0 K hK (psd A K hf) U V hUA hVA hV0 hUV l hl hlU hlV

/- ## Block B: bridge from cosine sums over the reals to `ZMod Q` -/

theorem AG_props (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n ∧ 2 * n < Q) :
    Sym (AG Q A) ∧ (0 : ZMod Q) ∉ AG Q A ∧ (AG Q A).card = 2 * A.card := by
  classical
  have hlt : ∀ n ∈ A, n < Q := fun n hn => by
    have := hA n hn
    omega
  have hpos : ∀ n ∈ A, 0 < n := fun n hn => (hA n hn).1
  have hinj : ∀ a ∈ A, ∀ b ∈ A, (a : ZMod Q) = (b : ZMod Q) → a = b := by
    intro a ha b hb h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt a ha),
      Nat.mod_eq_of_lt (hlt b hb)] at h
    exact h
  have hneg : ∀ a ∈ A, ∀ b ∈ A, (a : ZMod Q) ≠ -(b : ZMod Q) := by
    intro a ha b hb h
    have h' : ((a + b : ℕ) : ZMod Q) = 0 := by
      push_cast
      rw [h]
      ring
    rw [ZMod.natCast_eq_zero_iff] at h'
    have h1 := Nat.le_of_dvd (by have := hpos a ha; omega) h'
    have h2 := (hA a ha).2
    have h3 := (hA b hb).2
    omega
  have hz : ∀ a ∈ A, (a : ZMod Q) ≠ 0 := by
    intro a ha h
    rw [ZMod.natCast_eq_zero_iff] at h
    have h1 := Nat.le_of_dvd (hpos a ha) h
    have := hlt a ha
    omega
  have hsym : Sym (AG Q A) := by
    intro a ha
    unfold AG at ha ⊢
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ha
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases ha with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · exact Or.inr ⟨n, hn, rfl⟩
    · exact Or.inl ⟨n, hn, (neg_neg _).symm⟩
  have hzero : (0 : ZMod Q) ∉ AG Q A := by
    unfold AG
    intro h
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at h
    rcases h with ⟨n, hn, h⟩ | ⟨n, hn, h⟩
    · exact hz n hn h
    · exact hz n hn (neg_eq_zero.mp h)
  have hdisj : Disjoint (A.image (fun n : ℕ => (n : ZMod Q)))
      (A.image (fun n : ℕ => -(n : ZMod Q))) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hz2
    exact hneg a ha b hb hab.symm
  have hinj1 : Set.InjOn (fun n : ℕ => (n : ZMod Q)) (A : Set ℕ) :=
    fun a ha b hb h => hinj a ha b hb h
  have hinj2 : Set.InjOn (fun n : ℕ => -(n : ZMod Q)) (A : Set ℕ) :=
    fun a ha b hb h => hinj a ha b hb (neg_injective h)
  have hcard : (AG Q A).card = 2 * A.card := by
    unfold AG
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
      Finset.card_image_of_injOn hinj2]
    ring
  exact ⟨hsym, hzero, hcard⟩

theorem fR_AG (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n ∧ 2 * n < Q) (x : ZMod Q) :
    fR (AG Q A) x =
      2 * ∑ n ∈ A, Real.cos ((n : ℝ) * (2 * Real.pi * (x.val : ℝ) / (Q : ℝ))) := by
  have hlt : ∀ n ∈ A, n < Q := fun n hn => by have := (hA n hn).2; omega
  have hmod : ∀ m ∈ A, ∀ n ∈ A, (m : ZMod Q) = (n : ZMod Q) → m = n := by
    intro m hm n hn h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt m hm),
      Nat.mod_eq_of_lt (hlt n hn)] at h
    exact h
  have hdisj : Disjoint (A.image (fun n : ℕ => (n : ZMod Q)))
      (A.image (fun n : ℕ => -(n : ZMod Q))) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨n, hn, hmn⟩ := Finset.mem_image.mp hb
    have hmn' : -(n : ZMod Q) = (m : ZMod Q) := hmn
    have h0 : ((m + n : ℕ) : ZMod Q) = 0 := by
      push_cast
      linear_combination -hmn'
    have hdvd : Q ∣ m + n := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have h1 := hA m hm
    have h2 := hA n hn
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hi1 : ∀ m ∈ A, ∀ n ∈ A, (m : ZMod Q) = (n : ZMod Q) → m = n :=
    fun m hm n hn h => hmod m hm n hn h
  have hi2 : ∀ m ∈ A, ∀ n ∈ A, -(m : ZMod Q) = -(n : ZMod Q) → m = n :=
    fun m hm n hn h => hmod m hm n hn (neg_inj.mp h)
  rw [fR, AG, Finset.sum_union hdisj, Finset.sum_image hi1, Finset.sum_image hi2,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  show (e ((n : ZMod Q) * x)).re + (e (-(n : ZMod Q) * x)).re =
    2 * Real.cos ((n : ℝ) * (2 * Real.pi * (x.val : ℝ) / (Q : ℝ)))
  rw [neg_mul, (e_basic ((n : ZMod Q) * x) 0).2.2.2, Complex.conj_re, e_natCast]
  ring

/-- Contradiction for one set `A`, inside `ZMod Q`. -/
theorem contra_Q (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n ∧ 2 * n < Q) (hQ : 4 * A.card < Q)
    (K : ℝ) (hK : 1 ≤ K) (J : ℕ) (hJ : 1 ≤ J)
    (hn : (8192 * K ^ 2) ^ (4 * J + 4) ≤ 2 * (A.card : ℝ)) (hJK : 4 * K ^ 2 < 2 ^ J)
    (hcos : ∀ θ : ℝ, -(K / 2) ≤ ∑ n ∈ A, Real.cos ((n : ℝ) * θ)) : False := by
  obtain ⟨hsym, h0, hcard⟩ := AG_props A hA
  have hf : ∀ x : ZMod Q, -K ≤ fR (AG Q A) x := by
    intro x
    rw [fR_AG A hA x]
    have := hcos (2 * Real.pi * (x.val : ℝ) / (Q : ℝ))
    linarith
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  obtain ⟨S, T, d, hd, hT, hST_card, hST⟩ := struct (AG Q A) hsym h0 K hK hf (J' + 1)
    (by rw [hcard]; push_cast; exact hn)
  have hl : 0 < 2 ^ J' := by positivity
  have hmin := min_bound (AG Q A) hsym h0 K (by linarith) hf S T d hd hST (2 ^ J') hl
    (by rw [pow_succ (2 : ℕ) J'] at hST_card; linarith)
    (by rw [hT, pow_succ (2 : ℕ) J']; linarith)
    (by rw [hcard]; omega)
  push_cast at hmin
  rw [pow_succ (2 : ℝ) J'] at hJK
  linarith

end OMA.Ruzsa

namespace OMA.Ruzsa

/- ## Block F: choice of the prime and final numerics -/

theorem exists_prime_gt (A : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ (∀ n ∈ A, 2 * n < p) ∧ 4 * A.card < p := by
  obtain ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes (2 * A.sup id + 4 * A.card + 1)
  refine ⟨p, hpp, fun n hn => ?_, by omega⟩
  have : n ≤ A.sup id := Finset.le_sup (f := id) hn
  omega

theorem numeric : ∀ᶠ N : ℕ in Filter.atTop,
    1 ≤ ⌈Real.sqrt (Real.log (N : ℝ))⌉₊ ∧
      (8192 * (2 * Real.exp (1 / 10 * Real.sqrt (Real.log (N : ℝ)))) ^ 2) ^
          (4 * ⌈Real.sqrt (Real.log (N : ℝ))⌉₊ + 4) ≤ 2 * (N : ℝ) ∧
      4 * (2 * Real.exp (1 / 10 * Real.sqrt (Real.log (N : ℝ)))) ^ 2 <
        2 ^ ⌈Real.sqrt (Real.log (N : ℝ))⌉₊ := by
  have hev : ∀ᶠ N : ℕ in Filter.atTop, (90000 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 90000
  filter_upwards [hev] with N hlog
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      norm_num at hlog
    · exact_mod_cast h
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = Real.sqrt (Real.log (N : ℝ)) := ⟨_, rfl⟩
  rw [← hs_def]
  have hs2 : s ^ 2 = Real.log (N : ℝ) := by
    rw [hs_def]; exact Real.sq_sqrt (by linarith)
  have hsnn : 0 ≤ s := by rw [hs_def]; exact Real.sqrt_nonneg _
  have hs300 : 300 ≤ s := by nlinarith
  have hNexp : Real.exp (s ^ 2) = (N : ℝ) := by rw [hs2, Real.exp_log hNpos]
  obtain ⟨J, hJ_def⟩ : ∃ J : ℕ, J = ⌈s⌉₊ := ⟨_, rfl⟩
  rw [← hJ_def]
  have hJlo : s ≤ (J : ℝ) := by rw [hJ_def]; exact Nat.le_ceil s
  have hJhi : (J : ℝ) < s + 1 := by rw [hJ_def]; exact Nat.ceil_lt_add_one hsnn
  have hJpos : 1 ≤ J := by
    have := Nat.ceil_pos.mpr (show (0 : ℝ) < s by linarith)
    rw [← hJ_def] at this
    omega
  have he1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hexp11 : (32768 : ℝ) ≤ Real.exp 11 := by
    have h : Real.exp 11 = Real.exp 1 ^ 11 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (32768 : ℝ) ≤ 2.7 ^ 11 := by norm_num
      _ ≤ Real.exp 1 ^ 11 := pow_le_pow_left₀ (by norm_num) he1 11
  have hexp3 : (16 : ℝ) ≤ Real.exp 3 := by
    have h : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    calc (16 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he1 3
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hE : ∀ x : ℝ, Real.exp (1 / 10 * x) * Real.exp (1 / 10 * x) = Real.exp (1 / 5 * x) := by
    intro x; rw [← Real.exp_add]; congr 1; ring
  have hnn : ∀ x : ℝ, 0 ≤ Real.exp (1 / 10 * x) * Real.exp (1 / 10 * x) :=
    fun x => by positivity
  have key1 : 8192 * (2 * Real.exp (1 / 10 * s)) ^ 2 ≤ Real.exp (11 + 1 / 5 * s) := by
    have h5 : Real.exp (11 + 1 / 5 * s) =
        Real.exp 11 * (Real.exp (1 / 10 * s) * Real.exp (1 / 10 * s)) := by
      rw [hE s, ← Real.exp_add]
    rw [h5]
    nlinarith [mul_le_mul_of_nonneg_right hexp11 (hnn s)]
  have key2 : (8192 * (2 * Real.exp (1 / 10 * s)) ^ 2) ^ (4 * J + 4) ≤ Real.exp (s ^ 2) := by
    calc (8192 * (2 * Real.exp (1 / 10 * s)) ^ 2) ^ (4 * J + 4)
        ≤ (Real.exp (11 + 1 / 5 * s)) ^ (4 * J + 4) :=
          pow_le_pow_left₀ (by positivity) key1 _
      _ = Real.exp (((4 * J + 4 : ℕ) : ℝ) * (11 + 1 / 5 * s)) := by
          rw [Real.exp_nat_mul]
      _ ≤ Real.exp (s ^ 2) := by
          apply Real.exp_le_exp.mpr
          push_cast
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ 11 + 1 / 5 * s by linarith)
              (show (0 : ℝ) ≤ s + 1 - J by linarith),
            mul_nonneg (show (0 : ℝ) ≤ s - 300 by linarith) hsnn]
  have goal2 : (8192 * (2 * Real.exp (1 / 10 * s)) ^ 2) ^ (4 * J + 4) ≤ 2 * (N : ℝ) := by
    rw [← hNexp]
    linarith [key2, Real.exp_pos (s ^ 2)]
  have hA3 : 4 * (2 * Real.exp (1 / 10 * s)) ^ 2 ≤ Real.exp (3 + 1 / 5 * s) := by
    have h5 : Real.exp (3 + 1 / 5 * s) =
        Real.exp 3 * (Real.exp (1 / 10 * s) * Real.exp (1 / 10 * s)) := by
      rw [hE s, ← Real.exp_add]
    rw [h5]
    nlinarith [mul_le_mul_of_nonneg_right hexp3 (hnn s)]
  have hB3 : Real.exp (3 + 1 / 5 * s) < Real.exp ((J : ℝ) * Real.log 2) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (J : ℝ) - s by linarith)
        (show (0 : ℝ) ≤ Real.log 2 by linarith),
      mul_nonneg (show (0 : ℝ) ≤ Real.log 2 - 0.69 by linarith) hsnn]
  have hC3 : Real.exp ((J : ℝ) * Real.log 2) = 2 ^ J := by
    rw [Real.exp_nat_mul, Real.exp_log (show (0 : ℝ) < 2 by norm_num)]
  have goal3 : 4 * (2 * Real.exp (1 / 10 * s)) ^ 2 < 2 ^ J := by
    rw [← hC3]; linarith [hA3, hB3]
  exact ⟨hJpos, goal2, goal3⟩

end OMA.Ruzsa

theorem OMA.solution : type_of% @Erdos510.erdos_510.variants.ruzsa := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  filter_upwards [OMA.Ruzsa.numeric] with N hN A h0 hcard
  obtain ⟨hJ, hn, hJK⟩ := hN
  by_contra hcon
  push Not at hcon
  have hK : (1 : ℝ) ≤ 2 * Real.exp (1 / 10 * Real.sqrt (Real.log (N : ℝ))) := by
    have h1 : (1 : ℝ) ≤ Real.exp (1 / 10 * Real.sqrt (Real.log (N : ℝ))) :=
      Real.one_le_exp (by positivity)
    linarith
  obtain ⟨p, hp, hpA, hpc⟩ := OMA.Ruzsa.exists_prime_gt A
  have : Fact p.Prime := ⟨hp⟩
  have hApos : ∀ n ∈ A, 0 < n ∧ 2 * n < p := fun n hnA =>
    ⟨Nat.pos_of_ne_zero (fun h => h0 (h ▸ hnA)), hpA n hnA⟩
  refine OMA.Ruzsa.contra_Q (Q := p) A hApos hpc _ hK _ hJ (by rw [hcard]; exact hn) hJK ?_
  intro θ
  have := hcon θ
  linarith
