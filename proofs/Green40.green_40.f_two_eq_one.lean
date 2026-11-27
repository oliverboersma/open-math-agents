import FormalConjectures.GreensOpenProblems.«40»

/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the “License”);
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an “AS IS” BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
/-!
# Proof of Ben Green's Open Problem 40 (`f 2 = 1`)

Formalizes the quadratic-map construction of Jensen Kohlmeyer and Liam Kruer (2026) proving
`Green40.green_40.f_two_eq_one : f 2 = 1`.
-/

-- Lean formalization by Maxence Faldor. This file adapts it to the desk target.
-- Source: https://github.com/maxencefaldor/formal-conjectures/blob/08c3499c134bc446ba4b855a5e4f0cb197e79454/Solution.lean

open Filter Topology Fintype
open scoped ENNReal Pointwise

namespace Green40

/- ### Private helpers for `green_40.f_two_eq_one` (Kohlmeyer–Kruer construction) -/

private lemma zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  calc x + x = (1 : ZMod 2) • x + (1 : ZMod 2) • x := by simp
    _ = ((1 : ZMod 2) + 1) • x := (add_smul _ _ _).symm
    _ = (0 : ZMod 2) • x := by rw [h11]
    _ = 0 := zero_smul _ _

private lemma zmod2_add_eq_zero_iff {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x y : M} :
    x + y = 0 ↔ x = y := by
  constructor
  · intro h
    calc x = x + (x + y) := by rw [h, add_zero]
      _ = (x + x) + y := (add_assoc _ _ _).symm
      _ = y := by rw [zmod2_add_self, zero_add]
  · rintro rfl
    exact zmod2_add_self x

private lemma zmod2_add_cancel_left {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x + (x + y) = y := by
  rw [← add_assoc, zmod2_add_self, zero_add]

private lemma zmod2_add_cancel_right {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x + y + y = x := by
  rw [add_assoc, zmod2_add_self, add_zero]

private lemma zmod2_add_cancel_mid {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x y : M) :
    x + y + x = y := by
  rw [add_comm x y, add_assoc, zmod2_add_self, add_zero]

private def zmod2LinearMap {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [AddCommGroup N] [Module (ZMod 2) N]
    (f : M → N) (hadd : ∀ x y, f (x + y) = f x + f y) : M →ₗ[ZMod 2] N where
  toFun := f
  map_add' := hadd
  map_smul' r x := by
    have hf0 : f 0 = 0 := by
      have h0 := hadd 0 0
      rw [add_zero] at h0
      exact add_left_cancel (h0.symm.trans (add_zero (f 0)).symm)
    rcases zmod2_eq_zero_or_one r with rfl | rfl
    · simp [hf0]
    · simp

private lemma fintypeCard_F2 (n : ℕ) : Fintype.card (𝔽₂ n) = 2 ^ n := by
  simp [𝔽₂, 𝔽, ZMod.card]

private lemma natCard_F2 (n : ℕ) : Nat.card (𝔽₂ n) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, fintypeCard_F2]

/-- Sphere-covering lower bound: `1 ≤ minDensity n r` for every `n, r`. -/
private lemma one_le_minDensity (n r : ℕ) : (1 : ℝ≥0∞) ≤ minDensity n r := by
  unfold minDensity
  refine le_iInf₂ fun V hV => ?_
  have hcard : 2 ^ n ≤ Nat.card V * Nat.card (hammingBall n r) := by
    rw [← natCard_F2 n, ← Nat.card_prod]
    have hsurj : Function.Surjective (fun p : V × hammingBall n r => (p.1 : 𝔽₂ n) + (p.2 : 𝔽₂ n)) := by
      intro x
      have hx : x ∈ (V : Set (𝔽₂ n)) + hammingBall n r := hV ▸ Set.mem_univ x
      obtain ⟨a, ha, b, hb, hab⟩ := hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
    exact Nat.card_le_card_of_surjective _ hsurj
  have h2ne0 : (2 ^ n : ℝ≥0∞) ≠ 0 := by positivity
  have h2netop : (2 ^ n : ℝ≥0∞) ≠ ⊤ := by finiteness
  calc (1 : ℝ≥0∞) = (2 ^ n : ℝ≥0∞) / (2 ^ n : ℝ≥0∞) := (ENNReal.div_self h2ne0 h2netop).symm
    _ ≤ ((Nat.card V * Nat.card (hammingBall n r) : ℕ) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞) := by
      gcongr
      exact_mod_cast hcard
    _ = (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞) := by
      rw [Nat.cast_mul]

private lemma one_le_f_two : (1 : ℝ≥0∞) ≤ f 2 := by
  unfold f
  exact Filter.le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun n => one_le_minDensity n 2)

/-- An admissible binary quadratic map with parameters `(n, c)` (Kohlmeyer–Kruer Def. 3.1). -/
private structure AdmissibleQuad (n c : ℕ) where
  hc : 1 ≤ c
  hcn : c ≤ n
  Q : 𝔽₂ c × 𝔽₂ (n - c) → 𝔽₂ (n - 1)
  Q_zero_left : ∀ z, Q (0, z) = 0
  polar_add_left : ∀ u₁ u₂ v,
    Q (u₁ + u₂ + v) + Q (u₁ + u₂) + Q v =
      (Q (u₁ + v) + Q u₁ + Q v) + (Q (u₂ + v) + Q u₂ + Q v)
  ker_polar : ∀ a z x w, a ≠ 0 →
    Q ((a, z) + (x, w)) + Q (a, z) + Q (x, w) = 0 →
    (x, w) = 0 ∨ (x, w) = (a, z)

private def AdmissibleQuad.polar {n c : ℕ} (q : AdmissibleQuad n c)
    (u v : 𝔽₂ c × 𝔽₂ (n - c)) : 𝔽₂ (n - 1) :=
  q.Q (u + v) + q.Q u + q.Q v

private lemma AdmissibleQuad.polar_comm {n c : ℕ} (q : AdmissibleQuad n c)
    (u v : 𝔽₂ c × 𝔽₂ (n - c)) : q.polar u v = q.polar v u := by
  simp only [AdmissibleQuad.polar, add_comm u v]
  abel

private lemma AdmissibleQuad.polar_add_right {n c : ℕ} (q : AdmissibleQuad n c)
    (u v₁ v₂ : 𝔽₂ c × 𝔽₂ (n - c)) :
    q.polar u (v₁ + v₂) = q.polar u v₁ + q.polar u v₂ := by
  rw [q.polar_comm u (v₁ + v₂), q.polar_comm u v₁, q.polar_comm u v₂]
  exact q.polar_add_left v₁ v₂ u

private lemma AdmissibleQuad.polar_self {n c : ℕ} (q : AdmissibleQuad n c)
    (u : 𝔽₂ c × 𝔽₂ (n - c)) : q.polar u u = 0 := by
  rw [AdmissibleQuad.polar, zmod2_add_self, zmod2_add_cancel_right]
  exact q.Q_zero_left 0

private lemma AdmissibleQuad.polar_zero_right {n c : ℕ} (q : AdmissibleQuad n c)
    (u : 𝔽₂ c × 𝔽₂ (n - c)) : q.polar u 0 = 0 := by
  simp only [AdmissibleQuad.polar, add_zero]
  rw [zmod2_add_self, zero_add]
  exact q.Q_zero_left 0

private lemma AdmissibleQuad.polar_zero_left_zero_left {n c : ℕ} (q : AdmissibleQuad n c)
    (z w : 𝔽₂ (n - c)) : q.polar (0, z) (0, w) = 0 := by
  simp only [AdmissibleQuad.polar, Prod.mk_add_mk, add_zero, q.Q_zero_left]

/-- Base admissible quadratic map with parameters `(1, 1)`. -/
private def baseAdmissibleQuad : AdmissibleQuad 1 1 where
  hc := le_rfl
  hcn := le_rfl
  Q _ := 0
  Q_zero_left _ := rfl
  polar_add_left _ _ _ := by simp
  ker_polar a z x w ha _ := by
    have hz : w = z := funext fun i => Fin.elim0 i
    have h0 : w = 0 := funext fun i => Fin.elim0 i
    have hax : x = 0 ∨ x = a := by
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        have hx0 : x 0 ≠ 0 := by
          intro h
          apply hx
          ext j
          fin_cases j
          exact h
        have ha0 : a 0 ≠ 0 := by
          intro h
          apply ha
          ext j
          fin_cases j
          exact h
        have hx1 : x 0 = 1 := (zmod2_eq_zero_or_one (x 0)).resolve_left hx0
        have ha1 : a 0 = 1 := (zmod2_eq_zero_or_one (a 0)).resolve_left ha0
        ext i
        fin_cases i
        change x 0 = a 0
        rw [hx1, ha1]
    rcases hax with rfl | rfl
    · left; exact Prod.ext rfl h0
    · right; exact Prod.ext rfl hz

private def interpIota {F : Type} [Field F] [Algebra (ZMod 2) F] {m : ℕ}
    (h : 𝔽₂ m) : F → Fin m → F :=
  fun _ j => algebraMap (ZMod 2) F (h j)

private def interpD {F : Type} [Field F] [Fintype F] {m : ℕ}
    (t : F → Fin m → F) : F → Fin m → F :=
  fun s j => s * t s j + ∑ u : F, t u j

private def interpP {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}
    (lam : F →ₗ[ZMod 2] ZMod 2) (t : F → Fin m → F) : 𝔽₂ m :=
  fun j => lam (∑ s ∈ Finset.univ.erase (0 : F), t s j)

private lemma interpIota_add {F : Type} [Field F] [Algebra (ZMod 2) F] {m : ℕ} (h₁ h₂ : 𝔽₂ m) :
    interpIota (F := F) (h₁ + h₂) = interpIota h₁ + interpIota h₂ := by
  ext s j
  simp [interpIota, map_add]

private lemma interpIota_zero {F : Type} [Field F] [Algebra (ZMod 2) F] {m : ℕ} :
    interpIota (F := F) (0 : 𝔽₂ m) = 0 := by
  ext s j
  simp [interpIota]

private lemma interpD_add {F : Type} [Field F] [Fintype F] {m : ℕ}
    (t₁ t₂ : F → Fin m → F) :
    interpD (t₁ + t₂) = interpD t₁ + interpD t₂ := by
  ext s j
  simp only [interpD, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  abel

private lemma interpD_smul {F : Type} [Field F] [Fintype F] {m : ℕ}
    (a : F) (t : F → Fin m → F) :
    interpD (a • t) = a • interpD t := by
  ext s j
  simp only [interpD, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add]
  ring

private lemma interpP_add {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    {m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) (t₁ t₂ : F → Fin m → F) :
    interpP lam (t₁ + t₂) = interpP lam t₁ + interpP lam t₂ := by
  ext j
  simp [interpP, Finset.sum_add_distrib, map_add]

private lemma interpP_zero {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    {m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) :
    interpP lam (0 : F → Fin m → F) = 0 := by
  ext j
  simp [interpP]

/-- Lemma 4.1 (Kohlmeyer–Kruer Interpolation): exact solution of `(D + ρ id) t = ι(h)`. -/
private lemma interp_sol {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    {m : ℕ} (ρ : F) (h : 𝔽₂ m) (t : F → Fin m → F)
    (ht : interpD t + ρ • t = interpIota h) :
    ∀ s j, t s j = if s = ρ then algebraMap (ZMod 2) F (h j) else 0 := by
  intro s j
  have hEq : ∀ s', (s' + ρ) * t s' j + ∑ u : F, t u j = algebraMap (ZMod 2) F (h j) := by
    intro s'
    have hpt := congrFun (congrFun ht s') j
    simp only [interpD, interpIota, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpt
    linear_combination hpt
  have hsum : ∑ u : F, t u j = algebraMap (ZMod 2) F (h j) := by
    have hρ := hEq ρ
    rw [zmod2_add_self, zero_mul, zero_add] at hρ
    exact hρ
  have hne : ∀ s', s' ≠ ρ → t s' j = 0 := by
    intro s' hs'
    have hsEq := hEq s'
    rw [hsum] at hsEq
    have hmul : (s' + ρ) * t s' j = 0 := by
      have := congrArg (· + algebraMap (ZMod 2) F (h j)) hsEq
      simpa only [zmod2_add_cancel_right, zmod2_add_self] using this
    have hsr : s' + ρ ≠ 0 := by
      intro h0
      exact hs' (zmod2_add_eq_zero_iff.mp h0)
    exact (mul_eq_zero.mp hmul).resolve_left hsr
  split_ifs with hsr
  · subst hsr
    have hsingle : ∑ u : F, t u j = t s j := by
      rw [Finset.sum_eq_single s]
      · intro u _ hus
        exact hne u hus
      · intro hs; exact absurd (Finset.mem_univ s) hs
    rw [← hsingle, hsum]
  · exact hne s hsr

private lemma interp_zero {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    {m : ℕ} (ρ : F) (t : F → Fin m → F)
    (ht : interpD t + ρ • t = 0) : t = 0 := by
  have ht' : interpD t + ρ • t = interpIota (0 : 𝔽₂ m) := by
    rw [ht, interpIota_zero]
  have hsol := interp_sol ρ 0 t ht'
  ext s j
  rw [hsol s j]
  simp

private lemma interp_P_zero {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    {m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) (h : 𝔽₂ m) (t : F → Fin m → F)
    (ht : interpD t + (0 : F) • t = interpIota h) :
    interpP lam t = 0 := by
  have hsol := interp_sol (0 : F) h t ht
  ext j
  simp only [interpP, Pi.zero_apply]
  have hsum0 : ∑ s ∈ Finset.univ.erase (0 : F), t s j = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [hsol s j, if_neg (Finset.ne_of_mem_erase hs)]
  rw [hsum0, map_zero]

private lemma interp_P_ne_zero {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) (hlam : lam 1 = 1)
    (ρ : F) (hρ : ρ ≠ 0) (h : 𝔽₂ m) (t : F → Fin m → F)
    (ht : interpD t + ρ • t = interpIota h) :
    interpP lam t = h := by
  have hsol := interp_sol ρ h t ht
  ext j
  simp only [interpP]
  have hsum : ∑ s ∈ Finset.univ.erase (0 : F), t s j = algebraMap (ZMod 2) F (h j) := by
    rw [Finset.sum_eq_single ρ]
    · rw [hsol ρ j, if_pos rfl]
    · intro s _ hsρ
      rw [hsol s j, if_neg hsρ]
    · intro hnot
      exact absurd (Finset.mem_erase.mpr ⟨hρ, Finset.mem_univ ρ⟩) hnot
  rw [hsum, Algebra.algebraMap_eq_smul_one, map_smul, hlam, smul_eq_mul, mul_one]

/-- Abstract-field raw doubling step: keeps `F` abstract so Lean never unfolds `GaloisField`. -/
private def rawDoubleQ {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    {k m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) (Qt : F × 𝔽₂ k → 𝔽₂ m)
    (p : (F × F) × (𝔽₂ k × (F → Fin m → F))) : F × 𝔽₂ m × (F → Fin m → F) :=
  let a := p.1.1
  let b := p.1.2
  let z := p.2.1
  let t := p.2.2
  (a * b,
   Qt (a, z) + Qt (b, z) + interpP lam (a • t),
   a • interpD t + b • t + interpIota (F := F) (Qt (a, z)))

private def rawDoubleB {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    {k m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) (Qt : F × 𝔽₂ k → 𝔽₂ m)
    (p₁ p₂ : (F × F) × (𝔽₂ k × (F → Fin m → F))) : F × 𝔽₂ m × (F → Fin m → F) :=
  let a := p₁.1.1; let b := p₁.1.2; let z := p₁.2.1; let t := p₁.2.2
  let x := p₂.1.1; let y := p₂.1.2; let w := p₂.2.1; let u := p₂.2.2
  let Bt := fun r s => Qt (r + s) + Qt r + Qt s
  (a * y + b * x,
   Bt (a, z) (x, w) + Bt (b, z) (y, w) + interpP lam (a • u + x • t),
   a • interpD u + x • interpD t + b • u + y • t + interpIota (F := F) (Bt (a, z) (x, w)))

private lemma rawDouble_polar_eq {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {k m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) (Qt : F × 𝔽₂ k → 𝔽₂ m)
    (p₁ p₂ : (F × F) × (𝔽₂ k × (F → Fin m → F))) :
    rawDoubleQ lam Qt (p₁ + p₂) + rawDoubleQ lam Qt p₁ + rawDoubleQ lam Qt p₂ =
      rawDoubleB lam Qt p₁ p₂ := by
  rcases p₁ with ⟨⟨a, b⟩, ⟨z, t⟩⟩
  rcases p₂ with ⟨⟨x, y⟩, ⟨w, u⟩⟩
  have hsmul_bilin : ∀ (c₁ c₂ : F) (v₁ v₂ : F → Fin m → F),
      (c₁ + c₂) • (v₁ + v₂) + c₁ • v₁ + c₂ • v₂ = c₁ • v₂ + c₂ • v₁ := by
    intro c₁ c₂ v₁ v₂
    ext s j
    change (c₁ + c₂) * (v₁ s j + v₂ s j) + c₁ * v₁ s j + c₂ * v₂ s j =
      c₁ * v₂ s j + c₂ * v₁ s j
    have hring : (c₁ + c₂) * (v₁ s j + v₂ s j) + c₁ * v₁ s j + c₂ * v₂ s j =
        (c₁ * v₁ s j + c₁ * v₁ s j) + (c₂ * v₂ s j + c₂ * v₂ s j) +
        (c₁ * v₂ s j + c₂ * v₁ s j) := by ring
    rw [hring, zmod2_add_self, zmod2_add_self, zero_add, zero_add]
  apply Prod.ext
  · change (a + x) * (b + y) + a * b + x * y = a * y + b * x
    have h1 : (a + x) * (b + y) + a * b + x * y =
        (a * b + a * b) + (x * y + x * y) + (a * y + b * x) := by ring
    rw [h1, zmod2_add_self, zmod2_add_self, zero_add, zero_add]
  · apply Prod.ext
    · change (Qt (a + x, z + w) + Qt (b + y, z + w) + interpP lam ((a + x) • (t + u))) +
          (Qt (a, z) + Qt (b, z) + interpP lam (a • t)) +
          (Qt (x, w) + Qt (y, w) + interpP lam (x • u)) =
          (Qt ((a, z) + (x, w)) + Qt (a, z) + Qt (x, w)) +
          (Qt ((b, z) + (y, w)) + Qt (b, z) + Qt (y, w)) + interpP lam (a • u + x • t)
      have hP : interpP lam ((a + x) • (t + u)) + interpP lam (a • t) + interpP lam (x • u) =
          interpP lam (a • u + x • t) := by
        rw [← interpP_add, ← interpP_add, hsmul_bilin]
      simp only [Prod.mk_add_mk]
      rw [← hP]
      abel
    · change ((a + x) • interpD (t + u) + (b + y) • (t + u) +
            interpIota (F := F) (Qt (a + x, z + w))) +
          (a • interpD t + b • t + interpIota (F := F) (Qt (a, z))) +
          (x • interpD u + y • u + interpIota (F := F) (Qt (x, w))) =
          a • interpD u + x • interpD t + b • u + y • t +
            interpIota (F := F) (Qt ((a, z) + (x, w)) + Qt (a, z) + Qt (x, w))
      have hD : (a + x) • interpD (t + u) + a • interpD t + x • interpD u =
          a • interpD u + x • interpD t := by
        rw [interpD_add, hsmul_bilin]
      have hB : (b + y) • (t + u) + b • t + y • u = b • u + y • t := hsmul_bilin b y t u
      have hI : interpIota (F := F) (Qt (a + x, z + w)) + interpIota (F := F) (Qt (a, z)) +
          interpIota (F := F) (Qt (x, w)) =
          interpIota (F := F) (Qt ((a, z) + (x, w)) + Qt (a, z) + Qt (x, w)) := by
        simp only [Prod.mk_add_mk, interpIota_add]
      calc ((a + x) • interpD (t + u) + (b + y) • (t + u) +
              interpIota (F := F) (Qt (a + x, z + w))) +
            (a • interpD t + b • t + interpIota (F := F) (Qt (a, z))) +
            (x • interpD u + y • u + interpIota (F := F) (Qt (x, w)))
          = ((a + x) • interpD (t + u) + a • interpD t + x • interpD u) +
            ((b + y) • (t + u) + b • t + y • u) +
            (interpIota (F := F) (Qt (a + x, z + w)) + interpIota (F := F) (Qt (a, z)) +
              interpIota (F := F) (Qt (x, w))) := by abel
        _ = (a • interpD u + x • interpD t) + (b • u + y • t) +
              interpIota (F := F) (Qt ((a, z) + (x, w)) + Qt (a, z) + Qt (x, w)) := by
            rw [hD, hB, hI]
        _ = a • interpD u + x • interpD t + b • u + y • t +
              interpIota (F := F) (Qt ((a, z) + (x, w)) + Qt (a, z) + Qt (x, w)) := by abel

private lemma rawDouble_Q_zero_left {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {k m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) (Qt : F × 𝔽₂ k → 𝔽₂ m)
    (hQt0 : ∀ z, Qt (0, z) = 0) (zt : 𝔽₂ k × (F → Fin m → F)) :
    rawDoubleQ lam Qt ((0, 0), zt) = 0 := by
  rcases zt with ⟨z, t⟩
  apply Prod.ext
  · change (0 : F) * 0 = 0; simp
  · apply Prod.ext
    · change Qt (0, z) + Qt (0, z) + interpP lam ((0 : F) • t) = 0
      simp [hQt0, interpP_zero]
    · change (0 : F) • interpD t + (0 : F) • t + interpIota (F := F) (Qt (0, z)) = 0
      simp [hQt0, interpIota_zero]

private lemma rawDouble_B_add_left {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {k m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) (Qt : F × 𝔽₂ k → 𝔽₂ m)
    (hBt_add : ∀ u₁ u₂ v,
      (Qt (u₁ + u₂ + v) + Qt (u₁ + u₂) + Qt v) =
      (Qt (u₁ + v) + Qt u₁ + Qt v) + (Qt (u₂ + v) + Qt u₂ + Qt v))
    (p₁ p₂ v : (F × F) × (𝔽₂ k × (F → Fin m → F))) :
    rawDoubleB lam Qt (p₁ + p₂) v = rawDoubleB lam Qt p₁ v + rawDoubleB lam Qt p₂ v := by
  rcases p₁ with ⟨⟨a₁, b₁⟩, ⟨z₁, t₁⟩⟩
  rcases p₂ with ⟨⟨a₂, b₂⟩, ⟨z₂, t₂⟩⟩
  rcases v with ⟨⟨x, y⟩, ⟨w, u⟩⟩
  apply Prod.ext
  · change (a₁ + a₂) * y + (b₁ + b₂) * x = (a₁ * y + b₁ * x) + (a₂ * y + b₂ * x)
    ring
  · apply Prod.ext
    · dsimp only [rawDoubleB, Prod.fst_add, Prod.snd_add]
      have h1 := hBt_add (a₁, z₁) (a₂, z₂) (x, w)
      have h2 := hBt_add (b₁, z₁) (b₂, z₂) (y, w)
      have h3 : interpP lam ((a₁ + a₂) • u + x • (t₁ + t₂)) =
          interpP lam (a₁ • u + x • t₁) + interpP lam (a₂ • u + x • t₂) := by
        rw [← interpP_add, add_smul, smul_add]
        congr 1
        abel
      simp only [Prod.mk_add_mk] at h1 h2 ⊢
      rw [h1, h2, h3]
      abel
    · dsimp only [rawDoubleB, Prod.fst_add, Prod.snd_add]
      have h1 := hBt_add (a₁, z₁) (a₂, z₂) (x, w)
      simp only [Prod.mk_add_mk] at h1 ⊢
      rw [h1, interpIota_add, interpD_add, add_smul, smul_add, add_smul, smul_add]
      abel

private lemma rawDouble_ker_polar {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Algebra (ZMod 2) F] {k m : ℕ} (lam : F →ₗ[ZMod 2] ZMod 2) (hlam : lam 1 = 1)
    (Qt : F × 𝔽₂ k → 𝔽₂ m)
    (hQt0 : ∀ z, Qt (0, z) = 0)
    (hBt_ker : ∀ a z x w, a ≠ 0 →
      Qt ((a, z) + (x, w)) + Qt (a, z) + Qt (x, w) = 0 →
      (x, w) = 0 ∨ (x, w) = (a, z))
    (ab : F × F) (zt : 𝔽₂ k × (F → Fin m → F))
    (xy : F × F) (wu : 𝔽₂ k × (F → Fin m → F))
    (hab : ab ≠ 0) (hB : rawDoubleB lam Qt (ab, zt) (xy, wu) = 0) :
    (xy, wu) = 0 ∨ (xy, wu) = (ab, zt) := by
  rcases ab with ⟨a, b⟩
  rcases zt with ⟨z, t⟩
  rcases xy with ⟨x, y⟩
  rcases wu with ⟨w, u⟩
  let Bt : F × 𝔽₂ k → F × 𝔽₂ k → 𝔽₂ m := fun r s => Qt (r + s) + Qt r + Qt s
  have hBt_zl : ∀ r s, Bt (0, r) (0, s) = 0 := fun r s => by
    simp [Bt, Prod.mk_add_mk, hQt0]
  have hBt_zr : ∀ r, Bt r (0, 0) = 0 := fun r => by
    change Qt (r + 0) + Qt r + Qt (0, 0) = 0
    rw [add_zero, zmod2_add_self, zero_add, hQt0]
  have hBt_self : ∀ r, Bt r r = 0 := fun r => by
    simp only [Bt, zmod2_add_self, zmod2_add_cancel_right]
    exact hQt0 0
  have h1 : a * y + b * x = 0 := congrArg Prod.fst hB
  have h2 : Bt (a, z) (x, w) + Bt (b, z) (y, w) + interpP lam (a • u + x • t) = 0 :=
    congrArg (fun p => p.2.1) hB
  have h3 : a • interpD u + x • interpD t + b • u + y • t +
      interpIota (F := F) (Bt (a, z) (x, w)) = 0 :=
    congrArg (fun p => p.2.2) hB
  have smul_eq_zero_Z : ∀ {c : F} {v : F → Fin m → F}, c ≠ 0 → c • v = 0 → v = 0 := by
    intro c v hc0 hcv
    ext s j
    have hpt := congrFun (congrFun hcv s) j
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hpt
    exact (mul_eq_zero.mp hpt).resolve_left hc0
  by_cases ha : a = 0
  · -- Case 3: `a = 0`, so `b ≠ 0`.
    have hb : b ≠ 0 := by
      intro hb0
      exact hab (Prod.ext ha hb0)
    have hx : x = 0 := by
      rw [ha, zero_mul, zero_add] at h1
      exact (mul_eq_zero.mp h1).resolve_left hb
    rw [ha, hx] at h2 h3
    simp only [hBt_zl, zero_smul, add_zero, zero_add, interpP_zero, interpIota_zero] at h2 h3
    rcases hBt_ker b z y w hb h2 with h0 | heq
    · have hy : y = 0 := congrArg Prod.fst h0
      have hw : w = 0 := congrArg Prod.snd h0
      rw [hy, zero_smul, add_zero] at h3
      have hu : u = 0 := smul_eq_zero_Z hb h3
      left
      rw [hx, hy, hw, hu]; rfl
    · have hy : y = b := congrArg Prod.fst heq
      have hw : w = z := congrArg Prod.snd heq
      rw [hy, ← smul_add] at h3
      have hu : u = t := zmod2_add_eq_zero_iff.mp (smul_eq_zero_Z hb h3)
      right
      rw [ha, hx, hy, hw, hu]
  · -- Cases 1 & 2: `a ≠ 0`. Set `ρ := b * a⁻¹`.
    let ρ : F := b * a⁻¹
    have hbρ : b = ρ * a := by
      dsimp [ρ]
      rw [mul_assoc, inv_mul_cancel₀ ha, mul_one]
    have hy : y = ρ * x := by
      have h1' : a * (y + ρ * x) = 0 := by
        calc a * (y + ρ * x) = a * y + (ρ * a) * x := by ring
          _ = a * y + b * x := by rw [← hbρ]
          _ = 0 := h1
      exact zmod2_add_eq_zero_iff.mp ((mul_eq_zero.mp h1').resolve_left ha)
    have h3_interp : interpD (a • u + x • t) + ρ • (a • u + x • t) =
        interpIota (F := F) (Bt (a, z) (x, w)) := by
      have hD : interpD (a • u + x • t) = a • interpD u + x • interpD t := by
        rw [interpD_add, interpD_smul, interpD_smul]
      have hρs : ρ • (a • u + x • t) = b • u + y • t := by
        rw [smul_add, smul_smul, smul_smul, ← hbρ, ← hy]
      rw [hD, hρs]
      have h3' : (a • interpD u + x • interpD t) + (b • u + y • t) +
          interpIota (F := F) (Bt (a, z) (x, w)) = 0 := by
        simpa [add_assoc] using h3
      exact zmod2_add_eq_zero_iff.mp h3'
    by_cases hb : b = 0
    · -- Case 1: `a ≠ 0` and `b = 0`.
      have hρ0 : ρ = 0 := by simp [ρ, hb]
      have hy0 : y = 0 := by rw [hy, hρ0, zero_mul]
      rw [hρ0] at h3_interp
      have hP0 : interpP lam (a • u + x • t) = 0 :=
        interp_P_zero lam (Bt (a, z) (x, w)) (a • u + x • t) h3_interp
      rw [hb, hy0, hBt_zl, add_zero, hP0, add_zero] at h2
      rw [h2, interpIota_zero] at h3_interp
      have haut : a • u + x • t = 0 := interp_zero 0 (a • u + x • t) h3_interp
      rcases hBt_ker a z x w ha h2 with h0 | heq
      · have hx0 : x = 0 := congrArg Prod.fst h0
        have hw0 : w = 0 := congrArg Prod.snd h0
        rw [hx0, zero_smul, add_zero] at haut
        have hu0 : u = 0 := smul_eq_zero_Z ha haut
        left
        rw [hx0, hy0, hw0, hu0]; rfl
      · have hxa : x = a := congrArg Prod.fst heq
        have hwz : w = z := congrArg Prod.snd heq
        rw [hxa, ← smul_add] at haut
        have hut : u = t := zmod2_add_eq_zero_iff.mp (smul_eq_zero_Z ha haut)
        right
        rw [hb, hxa, hy0, hwz, hut]
    · -- Case 2: `a ≠ 0` and `b ≠ 0`.
      have hρ : ρ ≠ 0 := mul_ne_zero hb (inv_ne_zero ha)
      have hP : interpP lam (a • u + x • t) = Bt (a, z) (x, w) :=
        interp_P_ne_zero lam hlam ρ hρ (Bt (a, z) (x, w)) (a • u + x • t) h3_interp
      rw [hP, zmod2_add_cancel_mid] at h2
      rcases hBt_ker b z y w hb h2 with h0 | heq
      · have hy0 : y = 0 := congrArg Prod.fst h0
        have hw0 : w = 0 := congrArg Prod.snd h0
        have hx0 : x = 0 := (mul_eq_zero.mp (hy.symm.trans hy0)).resolve_left hρ
        rw [hx0, hw0, hBt_zr, interpIota_zero] at h3_interp
        have haut : a • u + (0 : F) • t = 0 := interp_zero ρ _ h3_interp
        rw [zero_smul, add_zero] at haut
        have hu0 : u = 0 := smul_eq_zero_Z ha haut
        left
        rw [hx0, hy0, hw0, hu0]; rfl
      · have hyb : y = b := congrArg Prod.fst heq
        have hwz : w = z := congrArg Prod.snd heq
        have hxa : x = a := mul_left_cancel₀ hρ (by rw [← hy, hyb, hbρ])
        rw [hxa, hwz, hBt_self, interpIota_zero] at h3_interp
        have haut : a • u + a • t = 0 := interp_zero ρ _ h3_interp
        rw [← smul_add] at haut
        have hut : u = t := zmod2_add_eq_zero_iff.mp (smul_eq_zero_Z ha haut)
        right
        rw [hxa, hyb, hwz, hut]

/-- Proposition 5.1 (Kohlmeyer–Kruer Doubling): an admissible quadratic map `(n, c)` doubles
    to an admissible quadratic map `(n + c + c * 2^c * (n - 1), 2 * c)`. -/
private noncomputable def doubleAdmissibleQuad {n c : ℕ} (q : AdmissibleQuad n c) :
    AdmissibleQuad (n + c + c * 2 ^ c * (n - 1)) (2 * c) := by
  classical
  have hc_ne : c ≠ 0 := by have := q.hc; omega
  let F := GaloisField 2 c
  letI : Fintype F := Fintype.ofFinite F
  have hdimF : Module.finrank (ZMod 2) F = c := GaloisField.finrank 2 hc_ne
  have hcardF : Fintype.card F = 2 ^ c := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 c hc_ne
  let eF : F ≃ₗ[ZMod 2] 𝔽₂ c :=
    LinearEquiv.ofFinrankEq F (𝔽₂ c) (by rw [hdimF, Module.finrank_fin_fun])
  -- Construct a `ZMod 2`-linear functional `lam : F →ₗ[ZMod 2] ZMod 2` with `lam 1 = 1`.
  have he1 : eF (1 : F) ≠ 0 := by
    intro h0
    exact one_ne_zero (eF.injective (h0.trans (map_zero eF).symm))
  have hcoord : ∃ i₀ : Fin c, eF (1 : F) i₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact he1 (funext hall)
  let i₀ : Fin c := hcoord.choose
  have hi₀_ne : eF (1 : F) i₀ ≠ 0 := hcoord.choose_spec
  let lam : F →ₗ[ZMod 2] ZMod 2 := (LinearMap.proj i₀).comp eF.toLinearMap
  have hlam : lam 1 = 1 :=
    (zmod2_eq_zero_or_one (eF (1 : F) i₀)).resolve_left hi₀_ne
  -- Transferred quadratic map `Qt : F × 𝔽₂ (n - c) → 𝔽₂ (n - 1)`.
  let Qt : F × 𝔽₂ (n - c) → 𝔽₂ (n - 1) := fun p => q.Q (eF p.1, p.2)
  have hQt0 : ∀ z, Qt (0, z) = 0 := fun z => by
    simp only [Qt, map_zero]
    exact q.Q_zero_left z
  have hBt_add : ∀ u₁ u₂ v,
      (Qt (u₁ + u₂ + v) + Qt (u₁ + u₂) + Qt v) =
      (Qt (u₁ + v) + Qt u₁ + Qt v) + (Qt (u₂ + v) + Qt u₂ + Qt v) := by
    intro u₁ u₂ v
    simpa only [Qt, Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk] using
      q.polar_add_left (eF u₁.1, u₁.2) (eF u₂.1, u₂.2) (eF v.1, v.2)
  have hBt_ker : ∀ a z x w, a ≠ 0 →
      Qt ((a, z) + (x, w)) + Qt (a, z) + Qt (x, w) = 0 →
      (x, w) = 0 ∨ (x, w) = (a, z) := by
    intro a z x w ha hB
    have hB' : q.Q ((eF a, z) + (eF x, w)) + q.Q (eF a, z) + q.Q (eF x, w) = 0 := by
      simpa only [Qt, Prod.mk_add_mk, map_add] using hB
    have hea : eF a ≠ 0 := by
      intro h0
      exact ha (eF.injective (h0.trans (map_zero eF).symm))
    rcases q.ker_polar (eF a) z (eF x) w hea hB' with h0 | heq
    · left
      have hx : x = 0 := eF.injective ((congrArg Prod.fst h0).trans (map_zero eF).symm)
      have hw : w = 0 := congrArg Prod.snd h0
      exact Prod.ext hx hw
    · right
      have hx : x = a := eF.injective (congrArg Prod.fst heq)
      have hw : w = z := congrArg Prod.snd heq
      exact Prod.ext hx hw
  -- Dimension calculations and linear equivalences to `𝔽₂`-spaces.
  let m := n - 1
  let Z := F → Fin m → F
  have hc' : 1 ≤ 2 * c := by have := q.hc; omega
  have hcn' : 2 * c ≤ n + c + c * 2 ^ c * (n - 1) := by have := q.hcn; omega
  have hdimZ : Module.finrank (ZMod 2) Z = c * 2 ^ c * (n - 1) := by
    dsimp [Z, m]
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, hcardF, smul_eq_mul,
      Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hdimF]
    ring
  have hdimA : Module.finrank (ZMod 2) (𝔽₂ (2 * c)) = Module.finrank (ZMod 2) (F × F) := by
    rw [Module.finrank_fin_fun, Module.finrank_prod, hdimF]
    omega
  have hdimK : Module.finrank (ZMod 2) (𝔽₂ (n + c + c * 2 ^ c * (n - 1) - 2 * c)) =
      Module.finrank (ZMod 2) (𝔽₂ (n - c) × Z) := by
    rw [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_fin_fun, hdimZ]
    have := q.hcn
    omega
  have hdimH : Module.finrank (ZMod 2) (F × 𝔽₂ m × Z) =
      Module.finrank (ZMod 2) (𝔽₂ (n + c + c * 2 ^ c * (n - 1) - 1)) := by
    rw [Module.finrank_prod, Module.finrank_prod, hdimF, Module.finrank_fin_fun, hdimZ,
      Module.finrank_fin_fun]
    dsimp [m]
    have := q.hc
    have := q.hcn
    omega
  let eA : 𝔽₂ (2 * c) ≃ₗ[ZMod 2] F × F := LinearEquiv.ofFinrankEq _ _ hdimA
  let eK : 𝔽₂ (n + c + c * 2 ^ c * (n - 1) - 2 * c) ≃ₗ[ZMod 2] 𝔽₂ (n - c) × Z :=
    LinearEquiv.ofFinrankEq _ _ hdimK
  let eH : (F × 𝔽₂ m × Z) ≃ₗ[ZMod 2] 𝔽₂ (n + c + c * 2 ^ c * (n - 1) - 1) :=
    LinearEquiv.ofFinrankEq _ _ hdimH
  exact
    { hc := hc'
      hcn := hcn'
      Q := fun p => eH (rawDoubleQ lam Qt (eA p.1, eK p.2))
      Q_zero_left := fun z => by
        simp only [map_zero]
        change eH (rawDoubleQ lam Qt ((0, 0), eK z)) = 0
        rw [rawDouble_Q_zero_left lam Qt hQt0, map_zero]
      polar_add_left := fun u₁ u₂ v => by
        have hE : ∀ (x y : 𝔽₂ (2 * c) × 𝔽₂ (n + c + c * 2 ^ c * (n - 1) - 2 * c)),
            eH (rawDoubleQ lam Qt (eA (x + y).1, eK (x + y).2)) +
            eH (rawDoubleQ lam Qt (eA x.1, eK x.2)) + eH (rawDoubleQ lam Qt (eA y.1, eK y.2)) =
            eH (rawDoubleB lam Qt (eA x.1, eK x.2) (eA y.1, eK y.2)) := by
          intro x y
          rw [← map_add, ← map_add]
          congr 1
          simpa [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk] using
            rawDouble_polar_eq lam Qt (eA x.1, eK x.2) (eA y.1, eK y.2)
        rw [hE (u₁ + u₂) v, hE u₁ v, hE u₂ v, ← map_add]
        congr 1
        simpa [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk] using
          rawDouble_B_add_left lam Qt hBt_add (eA u₁.1, eK u₁.2) (eA u₂.1, eK u₂.2) (eA v.1, eK v.2)
      ker_polar := fun a z x w ha hQ => by
        rw [← map_add, ← map_add] at hQ
        have hraw : rawDoubleB lam Qt (eA a, eK z) (eA x, eK w) = 0 := by
          have h0 : rawDoubleQ lam Qt ((eA a, eK z) + (eA x, eK w)) +
              rawDoubleQ lam Qt (eA a, eK z) + rawDoubleQ lam Qt (eA x, eK w) = 0 := by
            have := eH.injective (hQ.trans (map_zero eH).symm)
            simpa [Prod.mk_add_mk, map_add] using this
          rwa [← rawDouble_polar_eq]
        have hea : eA a ≠ 0 := by
          intro h0
          exact ha (eA.injective (h0.trans (map_zero eA).symm))
        rcases rawDouble_ker_polar lam hlam Qt hQt0 hBt_ker
            (eA a) (eK z) (eA x) (eK w) hea hraw with h0 | heq
        · left
          have hx : x = 0 := eA.injective ((congrArg Prod.fst h0).trans (map_zero eA).symm)
          have hw : w = 0 := eK.injective ((congrArg Prod.snd h0).trans (map_zero eK).symm)
          exact Prod.ext hx hw
        · right
          have hx : x = a := eA.injective (congrArg Prod.fst heq)
          have hw : w = z := eK.injective (congrArg Prod.snd heq)
          exact Prod.ext hx hw }

/-- Existence of admissible quadratic maps of codimension `2^r` for every `r`. -/
private lemma exists_admissibleQuad_pow_two :
    ∀ r : ℕ, ∃ n : ℕ, Nonempty (AdmissibleQuad n (2 ^ r))
  | 0 => ⟨1, ⟨baseAdmissibleQuad⟩⟩
  | r + 1 => by
    obtain ⟨n, ⟨q⟩⟩ := exists_admissibleQuad_pow_two r
    refine ⟨n + 2 ^ r + 2 ^ r * 2 ^ (2 ^ r) * (n - 1), ⟨?_⟩⟩
    simpa [pow_succ, mul_comm] using doubleAdmissibleQuad q

/-- Upper bound `2 * Nat.card (hammingBall N 2) ≤ N ^ 2 + N + 2`. -/
private lemma two_mul_natCard_hammingBall_two_le (N : ℕ) :
    2 * Nat.card (hammingBall N 2) ≤ N ^ 2 + N + 2 := by
  let supp : 𝔽₂ N → Finset (Fin N) := fun x => Finset.univ.filter (fun i => x i ≠ 0)
  let U : Finset (Finset (Fin N)) :=
    Finset.powersetCard 0 Finset.univ ∪
    (Finset.powersetCard 1 Finset.univ ∪ Finset.powersetCard 2 Finset.univ)
  have hmem : ∀ x : hammingBall N 2, supp x.1 ∈ U := by
    intro ⟨x, hx⟩
    have hle : (supp x).card ≤ 2 := hx
    have hcases : (supp x).card = 0 ∨ (supp x).card = 1 ∨ (supp x).card = 2 := by omega
    simp only [U, Finset.mem_union, Finset.mem_powersetCard]
    rcases hcases with h0 | h1 | h2
    · exact Or.inl ⟨Finset.subset_univ _, h0⟩
    · exact Or.inr (Or.inl ⟨Finset.subset_univ _, h1⟩)
    · exact Or.inr (Or.inr ⟨Finset.subset_univ _, h2⟩)
  have hinj : Function.Injective (fun x : hammingBall N 2 => (⟨supp x.1, hmem x⟩ : U)) := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hsupp : supp x = supp y := congrArg Subtype.val hxy
    apply Subtype.ext
    ext i
    have hiff : x i ≠ 0 ↔ y i ≠ 0 := by
      have := Finset.ext_iff.mp hsupp i
      simpa [supp] using this
    rcases zmod2_eq_zero_or_one (x i) with hxi | hxi <;>
      rcases zmod2_eq_zero_or_one (y i) with hyi | hyi <;> simp_all
  have hcard1 : Nat.card (hammingBall N 2) ≤ U.card := by
    have hle := Nat.card_le_card_of_injective _ hinj
    simpa [Nat.card_eq_fintype_card] using hle
  have hcardU : U.card ≤ N.choose 0 + N.choose 1 + N.choose 2 := by
    calc U.card
        ≤ (Finset.powersetCard 0 (Finset.univ : Finset (Fin N))).card +
            (Finset.powersetCard 1 (Finset.univ : Finset (Fin N)) ∪
              Finset.powersetCard 2 (Finset.univ : Finset (Fin N))).card :=
          Finset.card_union_le _ _
      _ ≤ (Finset.powersetCard 0 (Finset.univ : Finset (Fin N))).card +
            ((Finset.powersetCard 1 (Finset.univ : Finset (Fin N))).card +
              (Finset.powersetCard 2 (Finset.univ : Finset (Fin N))).card) := by
          gcongr
          exact Finset.card_union_le _ _
      _ = N.choose 0 + N.choose 1 + N.choose 2 := by
          simp [Finset.card_powersetCard, add_assoc]
  have hchoose : 2 * (N.choose 0 + N.choose 1 + N.choose 2) ≤ N ^ 2 + N + 2 := by
    rw [Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_two_right]
    cases N with
    | zero => norm_num
    | succ k =>
      simp only [Nat.add_sub_cancel]
      have hdiv : 2 * ((k + 1) * k / 2) ≤ (k + 1) * k := Nat.mul_div_le ((k + 1) * k) 2
      have hring : (k + 1) * k + 2 * (k + 1) + 2 = (k + 1) ^ 2 + (k + 1) + 2 := by ring
      omega
  omega

/-- From an admissible quadratic map `(n, 2 * t)` with `1 ≤ t`, produce a length `N ≥ 2 ^ n`
    whose radius-2 minimal covering density is at most `1 + 12 / 2 ^ t`. -/
private lemma exists_minDensity_le_of_admissibleQuad {n t : ℕ} (ht : 1 ≤ t)
    (q : AdmissibleQuad n (2 * t)) :
    ∃ N : ℕ, 2 ^ n ≤ N ∧ minDensity N 2 ≤ 1 + (12 : ℝ≥0∞) / (2 ^ t : ℝ≥0∞) := by
  classical
  have h2tn : 2 * t ≤ n := q.hcn
  have hn1 : 1 ≤ n := by omega
  let W := (𝔽₂ (2 * t) × 𝔽₂ (n - 2 * t)) × 𝔽₂ (n - 1)
  let Idx := (𝔽₂ (2 * t) × 𝔽₂ (n - 2 * t)) ⊕ (𝔽₂ (n - 2 * t) × 𝔽₂ (t - 1)) ⊕ 𝔽₂ (n - t)
  let col : Idx → W := fun idx =>
    match idx with
    | Sum.inl v => (v, q.Q v)
    | Sum.inr (Sum.inl (z, h₁)) =>
      ((0, z), fun j : Fin (n - 1) => if hj : j.val < t - 1 then h₁ ⟨j.val, hj⟩ else 0)
    | Sum.inr (Sum.inr h₂) =>
      ((0, 0), fun j : Fin (n - 1) =>
        if hj : t - 1 ≤ j.val then h₂ ⟨j.val - (t - 1), by omega⟩ else 0)
  -- Every syndrome `w : W` is a sum of two columns `col i + col j`.
  have hcoverW : ∀ w : W, ∃ i j : Idx, col i + col j = w := by
    rintro ⟨⟨a, z⟩, h⟩
    by_cases ha : a = 0
    · subst ha
      let h₁ : 𝔽₂ (t - 1) := fun i => h ⟨i.val, by omega⟩
      let h₂ : 𝔽₂ (n - t) := fun i => h ⟨i.val + (t - 1), by omega⟩
      refine ⟨Sum.inr (Sum.inl (z, h₁)), Sum.inr (Sum.inr h₂), ?_⟩
      apply Prod.ext
      · change (0, z) + (0, 0) = (0, z)
        simp
      · ext j
        change (if hj : j.val < t - 1 then h₁ ⟨j.val, hj⟩ else 0) +
          (if hj : t - 1 ≤ j.val then h₂ ⟨j.val - (t - 1), by omega⟩ else 0) = h j
        by_cases hj : j.val < t - 1
        · have hj' : ¬ (t - 1 ≤ j.val) := by omega
          simp [hj, hj', h₁]
        · have hj' : t - 1 ≤ j.val := by omega
          simp only [hj, ↓reduceDIte, hj', zero_add, h₂]
          exact congrArg h (Fin.ext (by dsimp; omega))
    · -- `a ≠ 0`: polar map `L := q.polar (a, z)` is surjective onto `𝔽₂ (n - 1)`.
      let L : 𝔽₂ (2 * t) × 𝔽₂ (n - 2 * t) →ₗ[ZMod 2] 𝔽₂ (n - 1) :=
        zmod2LinearMap (fun v => q.polar (a, z) v) (fun v₁ v₂ => q.polar_add_right (a, z) v₁ v₂)
      have hker_le : Nat.card (LinearMap.ker L) ≤ 2 := by
        let g : LinearMap.ker L → Bool := fun v => decide (v.1 = 0)
        have hginj : Function.Injective g := by
          intro ⟨⟨a₁, z₁⟩, hv₁⟩ ⟨⟨a₂, z₂⟩, hv₂⟩ hg
          apply Subtype.ext
          have hv₁' := q.ker_polar a z a₁ z₁ ha hv₁
          have hv₂' := q.ker_polar a z a₂ z₂ ha hv₂
          rcases hv₁' with h1 | h1 <;> rcases hv₂' with h2 | h2
          · exact h1.trans h2.symm
          · simp only [g, h1, h2, decide_true] at hg
            exact absurd (congrArg Prod.fst (of_decide_eq_true hg.symm)) ha
          · simp only [g, h1, h2, decide_true] at hg
            exact absurd (congrArg Prod.fst (of_decide_eq_true hg)) ha
          · exact h1.trans h2.symm
        have hle := Nat.card_le_card_of_injective g hginj
        simpa using hle
      have hcardV : Nat.card (𝔽₂ (2 * t) × 𝔽₂ (n - 2 * t)) = 2 ^ n := by
        rw [Nat.card_prod, natCard_F2, natCard_F2, ← pow_add]
        congr 1
        omega
      have hcard_mul : Nat.card (𝔽₂ (2 * t) × 𝔽₂ (n - 2 * t)) =
          Nat.card (LinearMap.ker L) * Nat.card (LinearMap.range L) := by
        rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker L)]
        congr 1
        exact Nat.card_congr (LinearMap.quotKerEquivRange L).toEquiv
      have hrange_ge : 2 ^ (n - 1) ≤ Nat.card (LinearMap.range L) := by
        have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega, pow_succ, mul_comm]
        have hmul : 2 * 2 ^ (n - 1) ≤ 2 * Nat.card (LinearMap.range L) := by
          calc 2 * 2 ^ (n - 1) = 2 ^ n := hpow.symm
            _ = Nat.card (LinearMap.ker L) * Nat.card (LinearMap.range L) := by
              rw [← hcardV, hcard_mul]
            _ ≤ 2 * Nat.card (LinearMap.range L) := Nat.mul_le_mul_right _ hker_le
        omega
      have hrange_eq : Fintype.card (LinearMap.range L) = Fintype.card (𝔽₂ (n - 1)) := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        apply le_antisymm
        · exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
        · rw [natCard_F2]; exact hrange_ge
      have hsurjL : Function.Surjective L := by
        have hbij : Function.Bijective (Subtype.val : LinearMap.range L → 𝔽₂ (n - 1)) :=
          (Fintype.bijective_iff_injective_and_card _).mpr ⟨Subtype.val_injective, hrange_eq⟩
        intro y
        obtain ⟨⟨y', hy'⟩, rfl⟩ := hbij.2 y
        exact hy'
      obtain ⟨v, hv⟩ := hsurjL (h + q.Q (a, z))
      refine ⟨Sum.inl v, Sum.inl (v + (a, z)), ?_⟩
      apply Prod.ext
      · change v + (v + (a, z)) = (a, z)
        exact zmod2_add_cancel_left v (a, z)
      · change q.Q v + q.Q (v + (a, z)) = h
        have hB : q.Q ((a, z) + v) + q.Q (a, z) + q.Q v = h + q.Q (a, z) := hv
        rw [add_comm (a, z) v] at hB
        have hstep := congrArg (· + q.Q (a, z)) hB
        rw [zmod2_add_cancel_right] at hstep
        calc q.Q v + q.Q (v + (a, z))
            = (q.Q (v + (a, z)) + q.Q (a, z) + q.Q v) + q.Q (a, z) := by
              rw [add_comm (q.Q (v + (a, z)) + q.Q (a, z)) (q.Q v), add_assoc,
                zmod2_add_cancel_right]
          _ = h := hstep
  -- Compute `N = Fintype.card Idx`.
  let N : ℕ := Fintype.card Idx
  have hN_eq : N = 2 ^ n + 2 ^ (n - t - 1) + 2 ^ (n - t) := by
    dsimp [N, Idx]
    simp only [Fintype.card_sum, Fintype.card_prod, fintypeCard_F2, ← pow_add]
    have h1 : 2 * t + (n - 2 * t) = n := by omega
    have h2 : (n - 2 * t) + (t - 1) = n - t - 1 := by omega
    rw [h1, h2, add_assoc]
  have hN_ge : 2 ^ n ≤ N := by
    rw [hN_eq, add_assoc]
    exact Nat.le_add_right _ _
  let eIdx : Fin N ≃ Idx := (Fintype.equivFin Idx).symm
  -- Parity-check map `M : 𝔽₂ N →ₗ[ZMod 2] W`.
  let M : 𝔽₂ N →ₗ[ZMod 2] W :=
    zmod2LinearMap (fun x => ∑ i : Fin N, x i • col (eIdx i)) (fun x y => by
      simp [Pi.add_apply, add_smul, Finset.sum_add_distrib])
  have hM_single : ∀ i : Fin N, M (Pi.single i (1 : ZMod 2) : 𝔽₂ N) = col (eIdx i) := by
    intro i
    change ∑ k : Fin N, (Pi.single i (1 : ZMod 2) : 𝔽₂ N) k • col (eIdx k) = col (eIdx i)
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [Pi.single_eq_of_ne hki]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hM_surj : Function.Surjective M := by
    intro w
    obtain ⟨i, j, hij⟩ := hcoverW w
    refine ⟨(Pi.single (eIdx.symm i) (1 : ZMod 2) : 𝔽₂ N) +
        (Pi.single (eIdx.symm j) (1 : ZMod 2) : 𝔽₂ N), ?_⟩
    rw [map_add, hM_single, hM_single, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hij]
  -- `V := ker M` is a radius-2 covering subspace of `𝔽₂ N`.
  let V := LinearMap.ker M
  have hV_cov : IsCoveringSubspace N 2 V := by
    unfold IsCoveringSubspace
    ext x
    simp only [Set.mem_univ, iff_true]
    obtain ⟨i, j, hij⟩ := hcoverW (M x)
    let u : 𝔽₂ N := (Pi.single (eIdx.symm i) (1 : ZMod 2) : 𝔽₂ N) +
      (Pi.single (eIdx.symm j) (1 : ZMod 2) : 𝔽₂ N)
    have hMu : M u = M x := by
      dsimp [u]
      rw [map_add, hM_single, hM_single, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hij]
    have hxv : x + u ∈ V := by
      change M (x + u) = 0
      rw [map_add, hMu, zmod2_add_self]
    have hu_ball : u ∈ hammingBall N 2 := by
      change hammingNorm u ≤ 2
      unfold hammingNorm
      have hsub : Finset.univ.filter (fun k => u k ≠ 0) ⊆ {eIdx.symm i, eIdx.symm j} := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, u, Pi.add_apply] at hk
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hnot
        push Not at hnot
        have : (Pi.single (eIdx.symm i) (1 : ZMod 2) : 𝔽₂ N) k +
            (Pi.single (eIdx.symm j) (1 : ZMod 2) : 𝔽₂ N) k = 0 := by
          rw [Pi.single_eq_of_ne hnot.1, Pi.single_eq_of_ne hnot.2, add_zero]
        exact hk this
      calc (Finset.univ.filter (fun k => u k ≠ 0)).card
          ≤ ({eIdx.symm i, eIdx.symm j} : Finset (Fin N)).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    exact ⟨x + u, hxv, u, hu_ball, zmod2_add_cancel_right x u⟩
  -- Compute `Nat.card V * 2 ^ (2 * n - 1) = 2 ^ N`.
  have hcardW : Nat.card W = 2 ^ (2 * n - 1) := by
    dsimp [W]
    rw [Nat.card_prod, Nat.card_prod, natCard_F2, natCard_F2, natCard_F2, ← pow_add, ← pow_add]
    congr 1
    omega
  have hcardV_mul : Nat.card V * 2 ^ (2 * n - 1) = 2 ^ N := by
    have h1 := Submodule.card_eq_card_quotient_mul_card V
    rw [natCard_F2] at h1
    have h2 : Nat.card (𝔽₂ N ⧸ V) = Nat.card W :=
      Nat.card_congr (LinearMap.quotKerEquivOfSurjective M hM_surj).toEquiv
    rw [h2, hcardW] at h1
    exact h1.symm
  have hcardV_ne0 : (Nat.card V : ℝ≥0∞) ≠ 0 := by
    have hpos : 0 < Nat.card V := by
      rw [Nat.card_pos_iff]
      exact ⟨⟨0⟩, Finite.of_fintype _⟩
    exact_mod_cast hpos.ne'
  -- Pure `ℕ` upper bound: `2 ^ t * (N ^ 2 + N + 2) ≤ (2 ^ t + 12) * 2 ^ (2 * n)`.
  have hNat_bound : 2 ^ t * (N ^ 2 + N + 2) ≤ (2 ^ t + 12) * 2 ^ (2 * n) := by
    have hN_le1 : N ≤ 2 ^ n + 2 * 2 ^ (n - t) := by
      have hpow : 2 ^ (n - t - 1) ≤ 2 ^ (n - t) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hN_le2 : N ≤ 2 * 2 ^ n := by
      have hpow : 2 * 2 ^ (n - t) ≤ 2 ^ n := by
        rw [mul_comm, ← pow_succ]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2tN : 2 ^ t * N ≤ (2 ^ t + 2) * 2 ^ n := by
      have hpow : 2 ^ t * 2 ^ (n - t) = 2 ^ n := by
        rw [← pow_add, show t + (n - t) = n by omega]
      calc 2 ^ t * N ≤ 2 ^ t * (2 ^ n + 2 * 2 ^ (n - t)) := Nat.mul_le_mul_left _ hN_le1
        _ = 2 ^ t * 2 ^ n + 2 * (2 ^ t * 2 ^ (n - t)) := by ring
        _ = (2 ^ t + 2) * 2 ^ n := by rw [hpow]; ring
    have hsq : 2 ^ t * N ^ 2 ≤ (2 ^ t + 8) * 2 ^ (2 * n) := by
      have h2t_pos : 0 < 2 ^ t := by positivity
      have h4le : 4 ≤ 4 * 2 ^ t := by
        have : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by norm_num)
        omega
      have hmul : 2 ^ t * (2 ^ t * N ^ 2) ≤ 2 ^ t * ((2 ^ t + 8) * 2 ^ (2 * n)) := by
        calc 2 ^ t * (2 ^ t * N ^ 2) = (2 ^ t * N) ^ 2 := by ring
          _ ≤ ((2 ^ t + 2) * 2 ^ n) ^ 2 := Nat.pow_le_pow_left h2tN 2
          _ = (2 ^ t * 2 ^ t + 4 * 2 ^ t + 4) * 2 ^ (2 * n) := by
            rw [mul_pow, ← pow_mul, mul_comm n 2]; ring
          _ ≤ (2 ^ t * 2 ^ t + 4 * 2 ^ t + 4 * 2 ^ t) * 2 ^ (2 * n) := by
            apply Nat.mul_le_mul_right; omega
          _ = 2 ^ t * ((2 ^ t + 8) * 2 ^ (2 * n)) := by ring
      exact Nat.le_of_mul_le_mul_left hmul h2t_pos
    have hlin : 2 ^ t * N ≤ 2 * 2 ^ (2 * n) := by
      have hpow : 2 ^ t * 2 ^ n ≤ 2 ^ (2 * n) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 ^ t * N ≤ 2 ^ t * (2 * 2 ^ n) := Nat.mul_le_mul_left _ hN_le2
        _ = 2 * (2 ^ t * 2 ^ n) := by ring
        _ ≤ 2 * 2 ^ (2 * n) := Nat.mul_le_mul_left 2 hpow
    have hconst : 2 ^ t * 2 ≤ 2 * 2 ^ (2 * n) := by
      have hpow : 2 ^ t ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 2 ^ t * (N ^ 2 + N + 2)
        = 2 ^ t * N ^ 2 + 2 ^ t * N + 2 ^ t * 2 := by ring
      _ ≤ (2 ^ t + 8) * 2 ^ (2 * n) + 2 * 2 ^ (2 * n) + 2 * 2 ^ (2 * n) := by omega
      _ = (2 ^ t + 12) * 2 ^ (2 * n) := by ring
  -- Assemble the `ℝ≥0∞` density bound.
  refine ⟨N, hN_ge, ?_⟩
  have h2pow : (2 ^ (2 * n) : ℝ≥0∞) = (2 : ℝ≥0∞) * (2 ^ (2 * n - 1) : ℝ≥0∞) := by
    have : (2 : ℕ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      conv_lhs => rw [show 2 * n = (2 * n - 1) + 1 by omega, pow_succ, mul_comm]
    exact_mod_cast this
  have h2t_ne0 : (2 ^ t : ℝ≥0∞) ≠ 0 := by positivity
  have h2t_top : (2 ^ t : ℝ≥0∞) ≠ ⊤ := by finiteness
  have h22n_ne0 : (2 ^ (2 * n) : ℝ≥0∞) ≠ 0 := by positivity
  have h22n_top : (2 ^ (2 * n) : ℝ≥0∞) ≠ ⊤ := by finiteness
  calc minDensity N 2
      ≤ (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall N 2) : ℝ≥0∞) / (2 ^ N : ℝ≥0∞) :=
        iInf₂_le V hV_cov
    _ = (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall N 2) : ℝ≥0∞) /
          ((Nat.card V : ℝ≥0∞) * (2 ^ (2 * n - 1) : ℝ≥0∞)) := by
        congr 1
        exact_mod_cast hcardV_mul.symm
    _ = (Nat.card (hammingBall N 2) : ℝ≥0∞) / (2 ^ (2 * n - 1) : ℝ≥0∞) :=
        ENNReal.mul_div_mul_left _ _ hcardV_ne0 (ENNReal.natCast_ne_top _)
    _ = ((2 : ℝ≥0∞) * (Nat.card (hammingBall N 2) : ℝ≥0∞)) /
          ((2 : ℝ≥0∞) * (2 ^ (2 * n - 1) : ℝ≥0∞)) :=
        (ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)).symm
    _ = ((2 * Nat.card (hammingBall N 2) : ℕ) : ℝ≥0∞) / (2 ^ (2 * n) : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, ← h2pow]
    _ ≤ ((N ^ 2 + N + 2 : ℕ) : ℝ≥0∞) / (2 ^ (2 * n) : ℝ≥0∞) := by
        gcongr
        exact_mod_cast two_mul_natCard_hammingBall_two_le N
    _ = ((2 ^ t : ℝ≥0∞) * ((N ^ 2 + N + 2 : ℕ) : ℝ≥0∞)) /
          ((2 ^ t : ℝ≥0∞) * (2 ^ (2 * n) : ℝ≥0∞)) :=
        (ENNReal.mul_div_mul_left _ _ h2t_ne0 h2t_top).symm
    _ ≤ (((2 ^ t + 12 : ℕ) : ℝ≥0∞) * (2 ^ (2 * n) : ℝ≥0∞)) /
          ((2 ^ t : ℝ≥0∞) * (2 ^ (2 * n) : ℝ≥0∞)) := by
        apply ENNReal.div_le_div_right
        have hcast : ((2 ^ t * (N ^ 2 + N + 2) : ℕ) : ℝ≥0∞) ≤
            (((2 ^ t + 12) * 2 ^ (2 * n) : ℕ) : ℝ≥0∞) := by exact_mod_cast hNat_bound
        simpa [Nat.cast_mul, Nat.cast_pow] using hcast
    _ = ((2 ^ t + 12 : ℕ) : ℝ≥0∞) / (2 ^ t : ℝ≥0∞) :=
        ENNReal.mul_div_mul_right _ _ h22n_ne0 h22n_top
    _ = 1 + (12 : ℝ≥0∞) / (2 ^ t : ℝ≥0∞) := by
        rw [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat, ENNReal.add_div,
          ENNReal.div_self h2t_ne0 h2t_top]

private lemma f_two_le_one : f 2 ≤ (1 : ℝ≥0∞) := by
  have hle_t : ∀ t₀ : ℕ, 1 ≤ t₀ → f 2 ≤ 1 + (12 : ℝ≥0∞) / (2 ^ t₀ : ℝ≥0∞) := by
    intro t₀ ht₀
    unfold f
    refine Filter.liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hb
    let r : ℕ := t₀ + M + 1
    let t : ℕ := 2 ^ (t₀ + M)
    have ht1 : 1 ≤ t := Nat.one_le_pow _ 2 (by norm_num)
    have ht_ge_t0 : t₀ ≤ t := le_trans (by omega) (Nat.lt_two_pow_self (n := t₀ + M)).le
    have ht_ge_M : M ≤ t := le_trans (by omega) (Nat.lt_two_pow_self (n := t₀ + M)).le
    obtain ⟨n, ⟨q0⟩⟩ := exists_admissibleQuad_pow_two r
    have hpow : 2 ^ r = 2 * t := by
      dsimp [r, t]
      rw [pow_succ, mul_comm]
    let q : AdmissibleQuad n (2 * t) := hpow ▸ q0
    obtain ⟨N, hN_ge, hdens⟩ := exists_minDensity_le_of_admissibleQuad ht1 q
    have hNM : M ≤ N := by
      have h2tn : 2 * t ≤ n := q.hcn
      have h1 : t ≤ 2 ^ n := le_trans (by omega : t ≤ n) (Nat.lt_two_pow_self (n := n)).le
      omega
    calc b ≤ minDensity N 2 := hM N hNM
      _ ≤ 1 + (12 : ℝ≥0∞) / (2 ^ t : ℝ≥0∞) := hdens
      _ ≤ 1 + (12 : ℝ≥0∞) / (2 ^ t₀ : ℝ≥0∞) := by
        gcongr
        norm_num
  refine ENNReal.le_of_forall_pos_le_add fun (ε : NNReal) hε _ => ?_
  obtain ⟨k, hk⟩ := exists_nat_gt ((12 : NNReal) / ε)
  let t₀ : ℕ := k + 1
  have ht₀ : 1 ≤ t₀ := by omega
  have hpow_ge : (12 : ℝ≥0∞) / (2 ^ t₀ : ℝ≥0∞) ≤ (ε : ℝ≥0∞) := by
    have h12 : (12 : NNReal) ≤ ε * ((2 ^ t₀ : ℕ) : NNReal) := by
      have hlt : (12 : NNReal) / ε < ((2 ^ t₀ : ℕ) : NNReal) := by
        refine lt_of_lt_of_le hk ?_
        have hkt : k ≤ 2 ^ t₀ := le_trans (by omega : k ≤ t₀) (Nat.lt_two_pow_self (n := t₀)).le
        exact_mod_cast hkt
      have hmul := (div_lt_iff₀ hε).mp hlt
      linarith [mul_comm (((2 ^ t₀ : ℕ) : NNReal)) ε]
    rw [ENNReal.div_le_iff (by positivity) (by finiteness)]
    have hcast : ((12 : NNReal) : ℝ≥0∞) ≤ ((ε * ((2 ^ t₀ : ℕ) : NNReal) : NNReal) : ℝ≥0∞) := by
      exact_mod_cast h12
    simpa [ENNReal.coe_mul] using hcast
  exact le_trans (hle_t t₀ ht₀) (add_le_add le_rfl hpow_ge)

/-- The asymptotic binary linear covering density at radius $2$ satisfies $f(2) = 1$. -/
private theorem proved_f_two_eq_one : f 2 = 1 :=
  le_antisymm f_two_le_one one_le_f_two

end Green40

theorem OMA.solution : type_of% @Green40.green_40.f_two_eq_one :=
  Green40.proved_f_two_eq_one

/-

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      “License” shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      “Licensor” shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      “Legal Entity” shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      “control” means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      “You” (or “Your”) shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      “Source” form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      “Object” form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      “Work” shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      “Derivative Works” shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      “Contribution” shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, “submitted”
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as “Not a Contribution.”

      “Contributor” shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a “NOTICE” text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an “AS IS” BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets “[]”
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same “printed page” as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the “License”);
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an “AS IS” BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
