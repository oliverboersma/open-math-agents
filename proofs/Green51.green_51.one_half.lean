import FormalConjectures.GreensOpenProblems.«51»

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
# Proof of Ben Green's Open Problem 51 at Density One Half

Independent Lean 4 formalization of the proof by Jensen Kohlmeyer and Liam Kruer (2026)
answering Sanders' Question 5.1 (`Green51.green_51.one_half`).
-/

-- Lean formalization by Maxence Faldor. This file adapts it to the desk target.
-- Source: https://github.com/maxencefaldor/formal-conjectures/blob/0866dc3e290daac563bf732977abd9281f387220/Solution.lean

open Filter Real
open scoped Pointwise

namespace Green51

section G51Helpers

private lemma g51_zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma g51_zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma g51_zmod2_mul_self (a : ZMod 2) : a * a = a := by
  fin_cases a <;> rfl

private lemma g51_f2_add_self {n : ℕ} (v : 𝔽₂ n) : v + v = 0 := by
  funext i
  exact g51_zmod2_add_self (v i)

private lemma g51_f2_add_cancel_left {n : ℕ} (u v : 𝔽₂ n) : u + (u + v) = v := by
  rw [← add_assoc, g51_f2_add_self, zero_add]

private lemma g51_f2_add_eq_zero_iff {n : ℕ} (u v : 𝔽₂ n) : u + v = 0 ↔ u = v := by
  constructor
  · intro h
    have h1 := congrArg (u + ·) h
    simpa [g51_f2_add_cancel_left] using h1.symm
  · rintro rfl
    exact g51_f2_add_self u

/- ### Part 1: Boolean cube, variance, and elementary ternary separator estimate -/

private abbrev g51_Cube (m : ℕ) := Fin m → Bool

private lemma g51_card_cube (m : ℕ) : Fintype.card (g51_Cube m) = 2 ^ m := by
  simp [g51_Cube]

private noncomputable def g51_mean {m : ℕ} (f : g51_Cube m → ℝ) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ * ∑ y : g51_Cube m, f y

private noncomputable def g51_var {m : ℕ} (f : g51_Cube m → ℝ) : ℝ :=
  g51_mean (fun y => (f y) ^ 2) - (g51_mean f) ^ 2

private noncomputable def g51_zeroDens {m : ℕ} (f : g51_Cube m → ℝ) : ℝ :=
  g51_mean (fun y => if f y = 0 then (1 : ℝ) else 0)

private lemma g51_mean_const {m : ℕ} (c : ℝ) :
    g51_mean (fun _ : g51_Cube m => c) = c := by
  simp [g51_mean]

private lemma g51_mean_add {m : ℕ} (f g : g51_Cube m → ℝ) :
    g51_mean (fun y => f y + g y) = g51_mean f + g51_mean g := by
  simp [g51_mean, Finset.sum_add_distrib, mul_add]

private lemma g51_mean_sub {m : ℕ} (f g : g51_Cube m → ℝ) :
    g51_mean (fun y => f y - g y) = g51_mean f - g51_mean g := by
  simp [g51_mean, Finset.sum_sub_distrib, mul_sub]

private lemma g51_mean_const_mul {m : ℕ} (c : ℝ) (f : g51_Cube m → ℝ) :
    g51_mean (fun y => c * f y) = c * g51_mean f := by
  simp [g51_mean, ← Finset.mul_sum]
  ring

private lemma g51_mean_mono {m : ℕ} {f g : g51_Cube m → ℝ} (h : ∀ y, f y ≤ g y) :
    g51_mean f ≤ g51_mean g := by
  unfold g51_mean
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum (fun y _ => h y)
  · positivity

private lemma g51_abs_mean_le {m : ℕ} (f : g51_Cube m → ℝ) :
    |g51_mean f| ≤ g51_mean (fun y => |f y|) := by
  unfold g51_mean
  rw [abs_mul, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left
  · exact Finset.abs_sum_le_sum_abs f Finset.univ
  · positivity

private lemma g51_zeroDens_nonneg {m : ℕ} (f : g51_Cube m → ℝ) :
    0 ≤ g51_zeroDens f := by
  unfold g51_zeroDens g51_mean
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro y _
  split_ifs <;> norm_num

private lemma g51_sum_update {m : ℕ} (j : Fin m) (b : Bool) (f : g51_Cube m → ℝ) :
    ∑ y : g51_Cube m, f (Function.update y j b) =
      2 * ∑ y ∈ Finset.univ.filter (fun y : g51_Cube m => y j = b), f y := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : g51_Cube m => y j = b)]
  have h1 : ∑ y ∈ Finset.univ.filter (fun y : g51_Cube m => y j = b), f (Function.update y j b) =
      ∑ y ∈ Finset.univ.filter (fun y : g51_Cube m => y j = b), f y := by
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Function.update_eq_self_iff.mpr hy.symm]
  have h2 : ∑ y ∈ Finset.univ.filter (fun y : g51_Cube m => ¬ y j = b), f (Function.update y j b) =
      ∑ y ∈ Finset.univ.filter (fun y : g51_Cube m => y j = b), f y := by
    apply Finset.sum_bij (fun y _ => Function.update y j b)
    · intro y _
      simp
    · intro y₁ hy₁ y₂ hy₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
      funext i
      by_cases hi : i = j
      · subst hi
        cases b <;> cases h1' : y₁ i <;> cases h2' : y₂ i <;> simp_all
      · have := congrFun heq i
        simpa [Function.update, hi] using this
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      refine ⟨Function.update z j (!b), ?_, ?_⟩
      · simp
      · ext i
        by_cases hi : i = j
        · subst hi; simp [hz]
        · simp [Function.update, hi]
    · intro _ _
      rfl
  rw [h1, h2, two_mul]

private lemma g51_mean_split {m : ℕ} (j : Fin m) (f : g51_Cube m → ℝ) :
    g51_mean f =
      (g51_mean (fun y => f (Function.update y j false)) +
        g51_mean (fun y => f (Function.update y j true))) / 2 := by
  unfold g51_mean
  rw [g51_sum_update j false f, g51_sum_update j true f]
  have hpart :
      ∑ y ∈ Finset.univ.filter (fun y : g51_Cube m => y j = false), f y +
        ∑ y ∈ Finset.univ.filter (fun y : g51_Cube m => y j = true), f y =
      ∑ y : g51_Cube m, f y := by
    have hfilt : Finset.univ.filter (fun y : g51_Cube m => y j = true) =
        Finset.univ.filter (fun y : g51_Cube m => ¬ y j = false) := by
      ext y
      cases y j <;> simp
    rw [hfilt]
    exact Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : g51_Cube m => y j = false) f
  linarith [congrArg (((2 : ℝ) ^ m)⁻¹ * ·) hpart]

private lemma g51_var_le_sqrt_mul_zeroDens {m : ℕ} (I : Finset (Fin m)) :
    ∀ (u : g51_Cube m → ℝ),
      (∀ y, u y = -1 ∨ u y = 0 ∨ u y = 1) →
      (∀ y y', (∀ j ∈ I, y j = y' j) → u y = u y') →
      (∀ y (j : Fin m) (b : Bool), |u y - u (Function.update y j b)| ≤ 1) →
      g51_var u ≤ 2 * Real.sqrt (I.card : ℝ) * g51_zeroDens u := by
  induction I using Finset.induction_on with
  | empty =>
    intro u _ hdep _
    have hconst : ∀ y : g51_Cube m, u y = u (fun _ => false) := fun y =>
      hdep y (fun _ => false) (fun j hj => (Finset.notMem_empty j hj).elim)
    unfold g51_var
    have h1 : g51_mean u = u (fun _ => false) := by
      rw [show u = fun _ => u (fun _ => false) from funext hconst, g51_mean_const]
    have h2 : g51_mean (fun y => (u y) ^ 2) = (u (fun _ => false)) ^ 2 := by
      rw [show (fun y => (u y) ^ 2) = fun _ => (u (fun _ => false)) ^ 2 from
        funext (fun y => by rw [hconst y]), g51_mean_const]
    rw [h1, h2]
    simp
  | @insert j I hj ih =>
    intro u hval hdep hsep
    have hcard : ((insert j I).card : ℝ) = (I.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem hj, Nat.cast_add, Nat.cast_one]
    by_cases hbig : 1 ≤ 2 * Real.sqrt ((insert j I).card : ℝ) * g51_zeroDens u
    · have hvar1 : g51_var u ≤ 1 := by
        unfold g51_var
        have hsq : g51_mean (fun y => (u y) ^ 2) ≤ 1 := by
          calc g51_mean (fun y => (u y) ^ 2)
              ≤ g51_mean (fun _ : g51_Cube m => (1 : ℝ)) := by
                apply g51_mean_mono
                intro y
                rcases hval y with hy | hy | hy <;> rw [hy] <;> norm_num
            _ = 1 := g51_mean_const 1
        nlinarith [sq_nonneg (g51_mean u)]
      linarith
    · push Not at hbig
      let u0 : g51_Cube m → ℝ := fun y => u (Function.update y j false)
      let u1 : g51_Cube m → ℝ := fun y => u (Function.update y j true)
      have hval0 : ∀ y, u0 y = -1 ∨ u0 y = 0 ∨ u0 y = 1 := fun y => hval _
      have hval1 : ∀ y, u1 y = -1 ∨ u1 y = 0 ∨ u1 y = 1 := fun y => hval _
      have hdep0 : ∀ y y', (∀ i ∈ I, y i = y' i) → u0 y = u0 y' := by
        intro y y' hy
        apply hdep
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · simp
        · have hne : i ≠ j := fun h => hj (h ▸ hi')
          simp [Function.update, hne, hy i hi']
      have hdep1 : ∀ y y', (∀ i ∈ I, y i = y' i) → u1 y = u1 y' := by
        intro y y' hy
        apply hdep
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · simp
        · have hne : i ≠ j := fun h => hj (h ▸ hi')
          simp [Function.update, hne, hy i hi']
      have hsep0 : ∀ y (i : Fin m) (b : Bool), |u0 y - u0 (Function.update y i b)| ≤ 1 := by
        intro y i b
        dsimp only [u0]
        by_cases hi : i = j
        · subst hi
          simp [Function.update_idem]
        · rw [Function.update_comm hi]
          exact hsep _ i b
      have hsep1 : ∀ y (i : Fin m) (b : Bool), |u1 y - u1 (Function.update y i b)| ≤ 1 := by
        intro y i b
        dsimp only [u1]
        by_cases hi : i = j
        · subst hi
          simp [Function.update_idem]
        · rw [Function.update_comm hi]
          exact hsep _ i b
      have ih0 := ih u0 hval0 hdep0 hsep0
      have ih1 := ih u1 hval1 hdep1 hsep1
      have hmean : g51_mean u = (g51_mean u0 + g51_mean u1) / 2 := g51_mean_split j u
      have hsq : g51_mean (fun y => (u y) ^ 2) =
          (g51_mean (fun y => (u0 y) ^ 2) + g51_mean (fun y => (u1 y) ^ 2)) / 2 :=
        g51_mean_split j (fun y => (u y) ^ 2)
      have hzd : g51_zeroDens u = (g51_zeroDens u0 + g51_zeroDens u1) / 2 :=
        g51_mean_split j (fun y => if u y = 0 then (1 : ℝ) else 0)
      have hvar_eq : g51_var u = (g51_var u0 + g51_var u1) / 2 +
          (g51_mean u0 - g51_mean u1) ^ 2 / 4 := by
        unfold g51_var
        rw [hmean, hsq]
        ring
      have hdiff_pt : ∀ y : g51_Cube m,
          |u0 y - u1 y| ≤ (if u0 y = 0 then (1 : ℝ) else 0) + (if u1 y = 0 then (1 : ℝ) else 0) := by
        intro y
        have hstep : |u0 y - u1 y| ≤ 1 := by
          have := hsep (Function.update y j false) j true
          simpa [u0, u1, Function.update_idem] using this
        rcases hval0 y with h0 | h0 | h0 <;> rcases hval1 y with h1 | h1 | h1
        · rw [h0, h1]; norm_num
        · rw [h0, h1]; norm_num
        · rw [h0, h1] at hstep; norm_num at hstep
        · rw [h0, h1]; norm_num
        · rw [h0, h1]; norm_num
        · rw [h0, h1]; norm_num
        · rw [h0, h1] at hstep; norm_num at hstep
        · rw [h0, h1]; norm_num
        · rw [h0, h1]; norm_num
      have hdiff_mean : |g51_mean u0 - g51_mean u1| ≤ 2 * g51_zeroDens u := by
        calc |g51_mean u0 - g51_mean u1|
            = |g51_mean (fun y => u0 y - u1 y)| := by rw [g51_mean_sub]
          _ ≤ g51_mean (fun y => |u0 y - u1 y|) := g51_abs_mean_le _
          _ ≤ g51_mean (fun y => (if u0 y = 0 then (1 : ℝ) else 0) +
                (if u1 y = 0 then (1 : ℝ) else 0)) := g51_mean_mono hdiff_pt
          _ = g51_zeroDens u0 + g51_zeroDens u1 := g51_mean_add _ _
          _ = 2 * g51_zeroDens u := by linarith [hzd]
      have hdiff_sq : (g51_mean u0 - g51_mean u1) ^ 2 / 4 ≤ (g51_zeroDens u) ^ 2 := by
        have h1 : (g51_mean u0 - g51_mean u1) ^ 2 ≤ (2 * g51_zeroDens u) ^ 2 := by
          rw [← sq_abs (g51_mean u0 - g51_mean u1)]
          exact pow_le_pow_left₀ (abs_nonneg _) hdiff_mean 2
        linarith
      have hcomb : g51_var u ≤ 2 * Real.sqrt (I.card : ℝ) * g51_zeroDens u + (g51_zeroDens u) ^ 2 := by
        calc g51_var u
            = (g51_var u0 + g51_var u1) / 2 + (g51_mean u0 - g51_mean u1) ^ 2 / 4 := hvar_eq
          _ ≤ (2 * Real.sqrt (I.card : ℝ) * g51_zeroDens u0 +
                2 * Real.sqrt (I.card : ℝ) * g51_zeroDens u1) / 2 + (g51_zeroDens u) ^ 2 := by
              linarith [ih0, ih1, hdiff_sq]
          _ = 2 * Real.sqrt (I.card : ℝ) * ((g51_zeroDens u0 + g51_zeroDens u1) / 2) +
                (g51_zeroDens u) ^ 2 := by ring
          _ = 2 * Real.sqrt (I.card : ℝ) * g51_zeroDens u + (g51_zeroDens u) ^ 2 := by rw [← hzd]
      set a := Real.sqrt (I.card : ℝ)
      set b := Real.sqrt ((insert j I).card : ℝ)
      set z := g51_zeroDens u
      have ha0 : 0 ≤ a := Real.sqrt_nonneg _
      have hb0 : 0 < b := Real.sqrt_pos.mpr (by rw [hcard]; positivity)
      have hz0 : 0 ≤ z := g51_zeroDens_nonneg u
      have hab_sq : b ^ 2 - a ^ 2 = 1 := by
        rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), hcard]
        ring
      have hab_le : a ≤ b := Real.sqrt_le_sqrt (by rw [hcard]; linarith)
      have hz_le : z ≤ 2 * (b - a) := by
        have hpos : 0 < b + a := by linarith
        have hmul : z * (b + a) ≤ 2 * (b - a) * (b + a) := by
          have h1 : 2 * (b - a) * (b + a) = 2 := by nlinarith [hab_sq]
          have h2 : z * (b + a) ≤ z * (2 * b) := by nlinarith
          nlinarith [hbig]
        nlinarith
      nlinarith

/- ### Part 2: Walsh-Fourier analysis and face variance identity -/

private def g51_walsh {m : ℕ} (S : Finset (Fin m)) (y : g51_Cube m) : ℝ :=
  ∏ j ∈ S, if y j then (-1 : ℝ) else 1

private noncomputable def g51_walshCoeff {m : ℕ} (u : g51_Cube m → ℝ) (S : Finset (Fin m)) : ℝ :=
  g51_mean (fun y => u y * g51_walsh S y)

private lemma g51_walsh_eq_prod_univ {m : ℕ} (S : Finset (Fin m)) (y : g51_Cube m) :
    g51_walsh S y = ∏ j : Fin m, if j ∈ S ∧ y j = true then (-1 : ℝ) else 1 := by
  unfold g51_walsh
  rw [← Finset.prod_subset (Finset.subset_univ S)]
  · apply Finset.prod_congr rfl
    intro j hj
    cases y j <;> simp [hj]
  · intro j _ hj
    simp [hj]

private lemma g51_walsh_mul {m : ℕ} (S T : Finset (Fin m)) (y : g51_Cube m) :
    g51_walsh S y * g51_walsh T y = g51_walsh (symmDiff S T) y := by
  rw [g51_walsh_eq_prod_univ, g51_walsh_eq_prod_univ, g51_walsh_eq_prod_univ,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> cases y j <;>
    simp [Finset.mem_symmDiff, hS, hT]

private lemma g51_walsh_update_neg {m : ℕ} (S : Finset (Fin m)) {j : Fin m} (hj : j ∈ S)
    (y : g51_Cube m) :
    g51_walsh S (Function.update y j (!y j)) = - g51_walsh S y := by
  unfold g51_walsh
  rw [← Finset.mul_prod_erase S _ hj, ← Finset.mul_prod_erase S _ hj]
  have hrest :
      ∏ i ∈ S.erase j, (if Function.update y j (!y j) i then (-1 : ℝ) else 1) =
        ∏ i ∈ S.erase j, (if y i then (-1 : ℝ) else 1) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Function.update, hne]
  rw [hrest]
  cases hy : y j <;> simp

private lemma g51_mean_walsh {m : ℕ} (S : Finset (Fin m)) :
    g51_mean (g51_walsh S) = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅
  · subst hS
    have h1 : g51_walsh (m := m) ∅ = fun _ => 1 := funext fun _ => by simp [g51_walsh]
    rw [h1, g51_mean_const]
    simp
  · simp only [hS, ite_false]
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    unfold g51_mean
    suffices hsum : ∑ y : g51_Cube m, g51_walsh S y = 0 by simp [hsum]
    let e : g51_Cube m ≃ g51_Cube m :=
      { toFun := fun y => Function.update y j (!y j)
        invFun := fun y => Function.update y j (!y j)
        left_inv := fun y => by
          ext i
          by_cases hi : i = j
          · subst hi; simp
          · simp [Function.update, hi]
        right_inv := fun y => by
          ext i
          by_cases hi : i = j
          · subst hi; simp
          · simp [Function.update, hi] }
    have hneg : ∑ y : g51_Cube m, g51_walsh S y = - ∑ y : g51_Cube m, g51_walsh S y := by
      calc ∑ y : g51_Cube m, g51_walsh S y
          = ∑ y : g51_Cube m, g51_walsh S (e y) := (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
        _ = ∑ y : g51_Cube m, - g51_walsh S y := by
            apply Finset.sum_congr rfl
            intro y _
            exact g51_walsh_update_neg S hj y
        _ = - ∑ y : g51_Cube m, g51_walsh S y := by rw [Finset.sum_neg_distrib]
    linarith

private lemma g51_mean_walsh_mul {m : ℕ} (S T : Finset (Fin m)) :
    g51_mean (fun y => g51_walsh S y * g51_walsh T y) = if S = T then 1 else 0 := by
  simp_rw [g51_walsh_mul, g51_mean_walsh, ← Finset.bot_eq_empty, symmDiff_eq_bot]

private lemma g51_prod_add_finset {m : ℕ} (f g : Fin m → ℝ) :
    ∑ I : Finset (Fin m), (∏ j : Fin m, if j ∈ I then f j else g j) =
      ∏ j : Fin m, (f j + g j) := by
  rw [Finset.prod_add]
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.prod_ite]
  have h1 : Finset.univ.filter (fun j : Fin m => j ∈ I) = I := by
    ext j; simp
  have h2 : Finset.univ.filter (fun j : Fin m => j ∉ I) = Finset.univ \ I := by
    ext j; simp
  rw [h1, h2]

private lemma g51_sum_walsh_mul {m : ℕ} (z y : g51_Cube m) :
    ∑ S : Finset (Fin m), g51_walsh S z * g51_walsh S y =
      if z = y then (2 : ℝ) ^ m else 0 := by
  have hterm : ∀ S : Finset (Fin m),
      g51_walsh S z * g51_walsh S y =
        ∏ j : Fin m, if j ∈ S then (if z j = y j then (1 : ℝ) else -1) else 1 := by
    intro S
    unfold g51_walsh
    rw [← Finset.prod_mul_distrib, ← Finset.prod_subset (Finset.subset_univ S)]
    · apply Finset.prod_congr rfl
      intro j hj
      cases z j <;> cases y j <;> simp [hj]
    · intro j _ hj
      simp [hj]
  simp_rw [hterm]
  rw [g51_prod_add_finset]
  by_cases hzy : z = y
  · subst hzy
    simp [show (1 : ℝ) + 1 = 2 by norm_num]
  · simp only [hzy, ite_false]
    have hex : ∃ j : Fin m, z j ≠ y j := by
      by_contra h
      push Not at h
      exact hzy (funext h)
    obtain ⟨j, hj⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

private lemma g51_walsh_inversion {m : ℕ} (u : g51_Cube m → ℝ) (y : g51_Cube m) :
    u y = ∑ S : Finset (Fin m), g51_walshCoeff u S * g51_walsh S y := by
  unfold g51_walshCoeff g51_mean
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ z : g51_Cube m,
      ∑ S : Finset (Fin m), u z * g51_walsh S z * g51_walsh S y =
        u z * (if z = y then (2 : ℝ) ^ m else 0) := by
    intro z
    simp_rw [mul_assoc, ← Finset.mul_sum, g51_sum_walsh_mul]
  simp_rw [hinner]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hpos : (2 : ℝ) ^ m ≠ 0 := by positivity
  field_simp [hpos]

private lemma g51_parseval {m : ℕ} (u : g51_Cube m → ℝ) :
    g51_mean (fun y => (u y) ^ 2) = ∑ S : Finset (Fin m), (g51_walshCoeff u S) ^ 2 := by
  have h1 : ∀ y : g51_Cube m,
      (u y) ^ 2 = ∑ S : Finset (Fin m), g51_walshCoeff u S * (u y * g51_walsh S y) := by
    intro y
    conv_lhs => rw [sq]; rhs; rw [g51_walsh_inversion u y]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring
  simp_rw [h1]
  unfold g51_mean
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.mul_sum]
  unfold g51_walshCoeff g51_mean
  ring

private def g51_patch {m : ℕ} (I : Finset (Fin m)) (a z : g51_Cube m) : g51_Cube m :=
  fun j => if j ∈ I then z j else a j

private lemma g51_mean_patch {m : ℕ} (I : Finset (Fin m)) (F : g51_Cube m → ℝ) :
    g51_mean (fun a => g51_mean (fun z => F (g51_patch I a z))) = g51_mean F := by
  unfold g51_mean
  rw [← Finset.mul_sum, ← mul_assoc]
  have hsum : ∑ a : g51_Cube m, ∑ z : g51_Cube m, F (g51_patch I a z) =
      (2 : ℝ) ^ m * ∑ a : g51_Cube m, F a := by
    let e : (g51_Cube m × g51_Cube m) ≃ (g51_Cube m × g51_Cube m) :=
      { toFun := fun p => (g51_patch I p.1 p.2, g51_patch I p.2 p.1)
        invFun := fun p => (g51_patch I p.1 p.2, g51_patch I p.2 p.1)
        left_inv := fun ⟨a, z⟩ => by
          apply Prod.ext <;> funext j <;> by_cases hj : j ∈ I <;> simp [g51_patch, hj]
        right_inv := fun ⟨a, z⟩ => by
          apply Prod.ext <;> funext j <;> by_cases hj : j ∈ I <;> simp [g51_patch, hj] }
    calc ∑ a : g51_Cube m, ∑ z : g51_Cube m, F (g51_patch I a z)
        = ∑ p : g51_Cube m × g51_Cube m, F (e p).1 :=
          (Fintype.sum_prod_type (fun p : g51_Cube m × g51_Cube m => F (e p).1)).symm
      _ = ∑ p : g51_Cube m × g51_Cube m, F p.1 :=
          Fintype.sum_equiv e (fun p => F (e p).1) (fun p => F p.1) (fun _ => rfl)
      _ = ∑ a : g51_Cube m, ∑ _z : g51_Cube m, F a :=
          Fintype.sum_prod_type (fun p : g51_Cube m × g51_Cube m => F p.1)
      _ = (2 : ℝ) ^ m * ∑ a : g51_Cube m, F a := by
          simp [Finset.mul_sum]
  rw [hsum, ← mul_assoc, mul_assoc (((2 : ℝ) ^ m)⁻¹), inv_mul_cancel₀ (by positivity), mul_one]

private lemma g51_walsh_patch {m : ℕ} (I S : Finset (Fin m)) (a z : g51_Cube m) :
    g51_walsh S (g51_patch I a z) = g51_walsh (S ∩ I) z * g51_walsh (S \ I) a := by
  unfold g51_walsh
  have hunion : S = (S ∩ I) ∪ (S \ I) := by
    ext j
    by_cases hj : j ∈ I <;> simp [hj]
  have hdisj : Disjoint (S ∩ I) (S \ I) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    exact (Finset.mem_sdiff.mp hj2).2 (Finset.mem_inter.mp hj1).2
  conv_lhs => rw [hunion]
  rw [Finset.prod_union hdisj]
  congr 1
  · apply Finset.prod_congr rfl
    intro j hj
    simp [g51_patch, (Finset.mem_inter.mp hj).2]
  · apply Finset.prod_congr rfl
    intro j hj
    simp [g51_patch, (Finset.mem_sdiff.mp hj).2]

private lemma g51_mean_var_patch {m : ℕ} (I : Finset (Fin m)) (u : g51_Cube m → ℝ) :
    g51_mean (fun a => g51_var (fun z => u (g51_patch I a z))) =
      ∑ S : Finset (Fin m), if Disjoint S I then 0 else (g51_walshCoeff u S) ^ 2 := by
  unfold g51_var
  rw [g51_mean_sub]
  dsimp only
  rw [g51_mean_patch I (fun y => (u y) ^ 2), g51_parseval]
  let g : g51_Cube m → ℝ := fun a => g51_mean (fun z => u (g51_patch I a z))
  have hg_eq : ∀ a : g51_Cube m,
      g a = ∑ S : Finset (Fin m), (if Disjoint S I then g51_walshCoeff u S else 0) * g51_walsh S a := by
    intro a
    dsimp only [g]
    have hinv : ∀ z : g51_Cube m,
        u (g51_patch I a z) =
          ∑ S : Finset (Fin m), g51_walshCoeff u S * g51_walsh (S \ I) a * g51_walsh (S ∩ I) z := by
      intro z
      rw [g51_walsh_inversion u (g51_patch I a z)]
      apply Finset.sum_congr rfl
      intro S _
      rw [g51_walsh_patch]
      ring
    simp_rw [hinv]
    unfold g51_mean
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [← Finset.mul_sum]
    have hmw : ((2 : ℝ) ^ m)⁻¹ * ∑ z : g51_Cube m, g51_walsh (S ∩ I) z =
        if Disjoint S I then 1 else 0 := by
      simpa [g51_mean, Finset.disjoint_iff_inter_eq_empty] using g51_mean_walsh (S ∩ I)
    calc ((2 : ℝ) ^ m)⁻¹ * (g51_walshCoeff u S * g51_walsh (S \ I) a *
            ∑ z : g51_Cube m, g51_walsh (S ∩ I) z)
        = g51_walshCoeff u S * g51_walsh (S \ I) a *
            (((2 : ℝ) ^ m)⁻¹ * ∑ z : g51_Cube m, g51_walsh (S ∩ I) z) := by ring
      _ = g51_walshCoeff u S * g51_walsh (S \ I) a * (if Disjoint S I then 1 else 0) := by rw [hmw]
      _ = (if Disjoint S I then g51_walshCoeff u S else 0) * g51_walsh S a := by
          by_cases hd : Disjoint S I
          · simp [hd, Finset.sdiff_eq_self_of_disjoint hd]
          · simp [hd]
  have hg_coeff : ∀ T : Finset (Fin m),
      g51_walshCoeff g T = if Disjoint T I then g51_walshCoeff u T else 0 := by
    intro T
    unfold g51_walshCoeff
    simp_rw [hg_eq, Finset.sum_mul]
    unfold g51_mean
    rw [Finset.sum_comm, Finset.mul_sum]
    have hterm : ∀ S : Finset (Fin m),
        ((2 : ℝ) ^ m)⁻¹ *
            ∑ y : g51_Cube m,
              (if Disjoint S I then g51_walshCoeff u S else 0) * g51_walsh S y * g51_walsh T y =
          (if Disjoint S I then g51_walshCoeff u S else 0) * (if S = T then 1 else 0) := by
      intro S
      simp_rw [mul_assoc, ← Finset.mul_sum]
      have horth := g51_mean_walsh_mul S T
      unfold g51_mean at horth
      calc ((2 : ℝ) ^ m)⁻¹ * ((if Disjoint S I then g51_walshCoeff u S else 0) *
              ∑ y : g51_Cube m, g51_walsh S y * g51_walsh T y)
          = (if Disjoint S I then g51_walshCoeff u S else 0) *
              (((2 : ℝ) ^ m)⁻¹ * ∑ y : g51_Cube m, g51_walsh S y * g51_walsh T y) := by ring
        _ = (if Disjoint S I then g51_walshCoeff u S else 0) * (if S = T then 1 else 0) := by
            rw [horth]
    simp_rw [hterm]
    simp [g51_walshCoeff, g51_mean]
  have hg_sq : g51_mean (fun a => (g a) ^ 2) =
      ∑ S : Finset (Fin m), if Disjoint S I then (g51_walshCoeff u S) ^ 2 else 0 := by
    rw [g51_parseval g]
    apply Finset.sum_congr rfl
    intro S _
    rw [hg_coeff S]
    split_ifs <;> simp
  change (∑ S : Finset (Fin m), (g51_walshCoeff u S) ^ 2) - g51_mean (fun a => (g a) ^ 2) = _
  rw [hg_sq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> ring

/- ### Part 3: Bernoulli face averaging and low-degree Walsh coefficient -/

private noncomputable def g51_bern {m : ℕ} (p : ℝ) (I : Finset (Fin m)) : ℝ :=
  ∏ j : Fin m, if j ∈ I then p else 1 - p

private lemma g51_bern_nonneg {m : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (I : Finset (Fin m)) :
    0 ≤ g51_bern p I := by
  apply Finset.prod_nonneg
  intro j _
  split_ifs <;> linarith

private lemma g51_sum_bern {m : ℕ} (p : ℝ) :
    ∑ I : Finset (Fin m), g51_bern p I = 1 := by
  unfold g51_bern
  rw [g51_prod_add_finset]
  simp

private lemma g51_sum_bern_disjoint {m : ℕ} (p : ℝ) (S : Finset (Fin m)) :
    ∑ I : Finset (Fin m), (if Disjoint S I then g51_bern p I else 0) = (1 - p) ^ S.card := by
  have hterm : ∀ I : Finset (Fin m),
      (if Disjoint S I then g51_bern p I else 0) =
        ∏ j : Fin m, if j ∈ I then (if j ∈ S then (0 : ℝ) else p) else 1 - p := by
    intro I
    by_cases hd : Disjoint S I
    · simp only [hd, ite_true]
      unfold g51_bern
      apply Finset.prod_congr rfl
      intro j _
      by_cases hjI : j ∈ I
      · have hjS : j ∉ S := Finset.disjoint_right.mp hd hjI
        simp [hjI, hjS]
      · simp [hjI]
    · simp only [hd, ite_false]
      rw [Finset.not_disjoint_iff] at hd
      obtain ⟨j, hjS, hjI⟩ := hd
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hjI, hjS]
  simp_rw [hterm]
  rw [g51_prod_add_finset]
  have hfac : ∀ j : Fin m, (if j ∈ S then (0 : ℝ) else p) + (1 - p) =
      if j ∈ S then 1 - p else 1 := by
    intro j
    split_ifs <;> ring
  simp_rw [hfac]
  rw [Finset.prod_ite]
  simp

private lemma g51_sum_bern_not_disjoint {m : ℕ} (p : ℝ) (S : Finset (Fin m)) :
    ∑ I : Finset (Fin m), (if Disjoint S I then (0 : ℝ) else g51_bern p I) =
      1 - (1 - p) ^ S.card := by
  have hadd :
      (∑ I : Finset (Fin m), (if Disjoint S I then g51_bern p I else 0)) +
        (∑ I : Finset (Fin m), (if Disjoint S I then (0 : ℝ) else g51_bern p I)) =
      ∑ I : Finset (Fin m), g51_bern p I := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I _
    split_ifs <;> ring
  rw [g51_sum_bern_disjoint, g51_sum_bern] at hadd
  linarith

private lemma g51_sum_bern_card {m : ℕ} (p : ℝ) :
    ∑ I : Finset (Fin m), g51_bern p I * (I.card : ℝ) = p * (m : ℝ) := by
  have hcard : ∀ I : Finset (Fin m),
      (I.card : ℝ) = ∑ j : Fin m, if j ∈ I then (1 : ℝ) else 0 := by
    intro I
    simp
  simp_rw [hcard, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ j : Fin m,
      ∑ I : Finset (Fin m), g51_bern p I * (if j ∈ I then (1 : ℝ) else 0) = p := by
    intro j
    have hterm : ∀ I : Finset (Fin m),
        g51_bern p I * (if j ∈ I then (1 : ℝ) else 0) =
          ∏ i : Fin m, if i ∈ I then p else (if i = j then (0 : ℝ) else 1 - p) := by
      intro I
      by_cases hj : j ∈ I
      · simp only [hj, ite_true, mul_one]
        unfold g51_bern
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : i ∈ I
        · simp [hi]
        · have hne : i ≠ j := fun h => hi (h ▸ hj)
          simp [hi, hne]
      · simp only [hj, ite_false, mul_zero]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        simp [hj]
    simp_rw [hterm]
    rw [g51_prod_add_finset]
    have hfac : ∀ i : Fin m, p + (if i = j then (0 : ℝ) else 1 - p) =
        if i = j then p else 1 := by
      intro i
      split_ifs <;> ring
    simp_rw [hfac]
    simp
  simp_rw [hinner]
  simp [mul_comm]

private lemma g51_exists_low_degree_walsh {m : ℕ} (u : g51_Cube m → ℝ)
    (hval : ∀ y, u y = -1 ∨ u y = 0 ∨ u y = 1)
    (hsep : ∀ y (j : Fin m) (b : Bool), |u y - u (Function.update y j b)| ≤ 1)
    (hz : g51_zeroDens u ≤ 1 / 2) :
    ∃ S : Finset (Fin m), g51_walshCoeff u S ≠ 0 ∧
      (S.card : ℝ) ≤ 64 * (m : ℝ) * (g51_zeroDens u) ^ 2 := by
  set z := g51_zeroDens u
  have hz0 : 0 ≤ z := g51_zeroDens_nonneg u
  set K : ℕ := Nat.floor (64 * (m : ℝ) * z ^ 2)
  have hK : 64 * (m : ℝ) * z ^ 2 < ((K + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (64 * (m : ℝ) * z ^ 2)
  by_contra hno
  push Not at hno
  have hcoeff_zero : ∀ S : Finset (Fin m), g51_walshCoeff u S ≠ 0 → K + 1 ≤ S.card := by
    intro S hS
    by_contra hlt
    push Not at hlt
    have hle : S.card ≤ K := Nat.lt_succ_iff.mp hlt
    have hleR : (S.card : ℝ) ≤ 64 * (m : ℝ) * z ^ 2 := by
      calc (S.card : ℝ) ≤ (K : ℝ) := Nat.cast_le.mpr hle
        _ ≤ 64 * (m : ℝ) * z ^ 2 := Nat.floor_le (by positivity)
    exact (hno S hS).not_ge hleR
  set p : ℝ := (((K + 1 : ℕ) : ℝ))⁻¹
  have hp_pos : 0 < p := by positivity
  have hp0 : 0 ≤ p := le_of_lt hp_pos
  have hp1 : p ≤ 1 := by
    dsimp only [p]
    rw [inv_le_one₀ (by positivity)]
    exact_mod_cast Nat.succ_pos K
  have hupper :
      ∑ I : Finset (Fin m), g51_bern p I * g51_mean (fun a => g51_var (fun w => u (g51_patch I a w))) ≤
        2 * z * Real.sqrt (p * (m : ℝ)) := by
    have hface : ∀ I : Finset (Fin m),
        g51_mean (fun a => g51_var (fun w => u (g51_patch I a w))) ≤
          2 * Real.sqrt (I.card : ℝ) * z := by
      intro I
      calc g51_mean (fun a => g51_var (fun w => u (g51_patch I a w)))
          ≤ g51_mean (fun a => 2 * Real.sqrt (I.card : ℝ) * g51_zeroDens (fun w => u (g51_patch I a w))) := by
            apply g51_mean_mono
            intro a
            apply g51_var_le_sqrt_mul_zeroDens I
            · intro w; exact hval _
            · intro w w' hw
              congr 1
              funext j
              by_cases hj : j ∈ I
              · simp [g51_patch, hj, hw j hj]
              · simp [g51_patch, hj]
            · intro w j b
              by_cases hj : j ∈ I
              · have heq : g51_patch I a (Function.update w j b) =
                    Function.update (g51_patch I a w) j b := by
                  funext i
                  by_cases hi : i = j
                  · subst hi; simp [g51_patch, hj]
                  · simp [g51_patch, Function.update, hi]
                rw [heq]
                exact hsep _ j b
              · have heq : g51_patch I a (Function.update w j b) = g51_patch I a w := by
                  funext i
                  by_cases hi : i = j
                  · subst hi; simp [g51_patch, hj]
                  · simp [g51_patch, Function.update, hi]
                rw [heq]
                simp
        _ = 2 * Real.sqrt (I.card : ℝ) * g51_mean (fun a => g51_zeroDens (fun w => u (g51_patch I a w))) :=
            g51_mean_const_mul _ _
        _ = 2 * Real.sqrt (I.card : ℝ) * z := by
            rw [show g51_mean (fun a => g51_zeroDens (fun w => u (g51_patch I a w))) = z from
              g51_mean_patch I (fun y => if u y = 0 then (1 : ℝ) else 0)]
    have hcs :
        ∑ I : Finset (Fin m), g51_bern p I * Real.sqrt (I.card : ℝ) ≤ Real.sqrt (p * (m : ℝ)) := by
      have hsq :
          (∑ I : Finset (Fin m), g51_bern p I * Real.sqrt (I.card : ℝ)) ^ 2 ≤ p * (m : ℝ) := by
        have hrew : ∀ I : Finset (Fin m),
            g51_bern p I * Real.sqrt (I.card : ℝ) =
              Real.sqrt (g51_bern p I) * (Real.sqrt (g51_bern p I) * Real.sqrt (I.card : ℝ)) := by
          intro I
          have hb := g51_bern_nonneg hp0 hp1 I
          rw [← mul_assoc, Real.mul_self_sqrt hb]
        simp_rw [hrew]
        calc (∑ I : Finset (Fin m),
                Real.sqrt (g51_bern p I) * (Real.sqrt (g51_bern p I) * Real.sqrt (I.card : ℝ))) ^ 2
            ≤ (∑ I : Finset (Fin m), (Real.sqrt (g51_bern p I)) ^ 2) *
                (∑ I : Finset (Fin m), (Real.sqrt (g51_bern p I) * Real.sqrt (I.card : ℝ)) ^ 2) :=
              Finset.sum_mul_sq_le_sq_mul_sq _ _ _
          _ = (∑ I : Finset (Fin m), g51_bern p I) *
                (∑ I : Finset (Fin m), g51_bern p I * (I.card : ℝ)) := by
              congr 1
              · apply Finset.sum_congr rfl
                intro I _
                exact Real.sq_sqrt (g51_bern_nonneg hp0 hp1 I)
              · apply Finset.sum_congr rfl
                intro I _
                rw [mul_pow, Real.sq_sqrt (g51_bern_nonneg hp0 hp1 I), Real.sq_sqrt (Nat.cast_nonneg _)]
          _ = 1 * (p * (m : ℝ)) := by rw [g51_sum_bern, g51_sum_bern_card]
          _ = p * (m : ℝ) := one_mul _
      calc ∑ I : Finset (Fin m), g51_bern p I * Real.sqrt (I.card : ℝ)
          ≤ Real.sqrt ((∑ I : Finset (Fin m), g51_bern p I * Real.sqrt (I.card : ℝ)) ^ 2) := by
            rw [Real.sqrt_sq]
            apply Finset.sum_nonneg
            intro I _
            exact mul_nonneg (g51_bern_nonneg hp0 hp1 I) (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt (p * (m : ℝ)) := Real.sqrt_le_sqrt hsq
    calc ∑ I : Finset (Fin m), g51_bern p I *
            g51_mean (fun a => g51_var (fun w => u (g51_patch I a w)))
        ≤ ∑ I : Finset (Fin m), g51_bern p I * (2 * Real.sqrt (I.card : ℝ) * z) := by
          apply Finset.sum_le_sum
          intro I _
          exact mul_le_mul_of_nonneg_left (hface I) (g51_bern_nonneg hp0 hp1 I)
      _ = 2 * z * ∑ I : Finset (Fin m), g51_bern p I * Real.sqrt (I.card : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro I _
          ring
      _ ≤ 2 * z * Real.sqrt (p * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
  have hlower :
      (1 / 4 : ℝ) ≤
        ∑ I : Finset (Fin m), g51_bern p I *
          g51_mean (fun a => g51_var (fun w => u (g51_patch I a w))) := by
    simp_rw [g51_mean_var_patch, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hswap : ∀ S : Finset (Fin m),
        ∑ I : Finset (Fin m), g51_bern p I * (if Disjoint S I then 0 else (g51_walshCoeff u S) ^ 2) =
          (g51_walshCoeff u S) ^ 2 * (1 - (1 - p) ^ S.card) := by
      intro S
      rw [← g51_sum_bern_not_disjoint p S, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      split_ifs <;> ring
    simp_rw [hswap]
    have hexp_half : (1 - p) ^ (K + 1) ≤ 1 / 2 := by
      have h1 : 1 - p ≤ Real.exp (-p) := by
        simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-p)
      have h2 : (1 - p) ^ (K + 1) ≤ (Real.exp (-p)) ^ (K + 1) :=
        pow_le_pow_left₀ (by linarith) h1 (K + 1)
      have h3 : (Real.exp (-p)) ^ (K + 1) = Real.exp (-1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        dsimp only [p]
        have hKpos : ((K + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hKpos]
      have h4 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg]
        have he2 : (2 : ℝ) ≤ Real.exp 1 := by
          linarith [Real.add_one_le_exp (1 : ℝ)]
        have : (Real.exp 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he2
        linarith
      linarith
    have hsum_ge :
        (1 / 2 : ℝ) * ∑ S : Finset (Fin m), (g51_walshCoeff u S) ^ 2 ≤
          ∑ S : Finset (Fin m), (g51_walshCoeff u S) ^ 2 * (1 - (1 - p) ^ S.card) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : g51_walshCoeff u S = 0
      · simp [hS]
      · have hScard : K + 1 ≤ S.card := hcoeff_zero S hS
        have hpow : (1 - p) ^ S.card ≤ (1 - p) ^ (K + 1) :=
          pow_le_pow_of_le_one (by linarith) (by linarith) hScard
        have h1m : (1 / 2 : ℝ) ≤ 1 - (1 - p) ^ S.card := by linarith
        nlinarith [sq_nonneg (g51_walshCoeff u S)]
    have hparseval : ∑ S : Finset (Fin m), (g51_walshCoeff u S) ^ 2 = 1 - z := by
      rw [← g51_parseval]
      have hpt : ∀ y : g51_Cube m, (u y) ^ 2 = 1 - (if u y = 0 then (1 : ℝ) else 0) := by
        intro y
        rcases hval y with hy | hy | hy <;> rw [hy] <;> norm_num
      simp_rw [hpt]
      rw [g51_mean_sub, g51_mean_const]
      rfl
    linarith
  have hineq : (1 / 4 : ℝ) ≤ 2 * z * Real.sqrt (p * (m : ℝ)) := le_trans hlower hupper
  have hsq : (1 / 4 : ℝ) ^ 2 ≤ (2 * z * Real.sqrt (p * (m : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hineq 2
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)] at hsq
  have hKpos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hmul : (1 / 16 : ℝ) * ((K + 1 : ℕ) : ℝ) ≤ 4 * z ^ 2 * (m : ℝ) := by
    have : (1 / 16 : ℝ) ≤ 4 * z ^ 2 * (p * (m : ℝ)) := by linarith
    have hpK : p * ((K + 1 : ℕ) : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hKpos)
    calc (1 / 16 : ℝ) * ((K + 1 : ℕ) : ℝ)
        ≤ (4 * z ^ 2 * (p * (m : ℝ))) * ((K + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right this (le_of_lt hKpos)
      _ = 4 * z ^ 2 * (m : ℝ) * (p * ((K + 1 : ℕ) : ℝ)) := by ring
      _ = 4 * z ^ 2 * (m : ℝ) := by rw [hpK, mul_one]
  linarith

/- ### Part 4: Fourier analysis on `𝔽₂ n` and good linear functionals -/

private def g51_dot {n : ℕ} (r v : 𝔽₂ n) : ZMod 2 :=
  ∑ i : Fin n, r i * v i

private def g51_char {n : ℕ} (r v : 𝔽₂ n) : ℝ :=
  if g51_dot r v = 0 then 1 else -1

private lemma g51_dot_add_right {n : ℕ} (r u v : 𝔽₂ n) :
    g51_dot r (u + v) = g51_dot r u + g51_dot r v := by
  simp [g51_dot, mul_add, Finset.sum_add_distrib]

private lemma g51_dot_add_left {n : ℕ} (r s v : 𝔽₂ n) :
    g51_dot (r + s) v = g51_dot r v + g51_dot s v := by
  simp [g51_dot, add_mul, Finset.sum_add_distrib]

private lemma g51_dot_zero_right {n : ℕ} (r : 𝔽₂ n) : g51_dot r 0 = 0 := by
  simp [g51_dot]

private lemma g51_char_add_right {n : ℕ} (r u v : 𝔽₂ n) :
    g51_char r (u + v) = g51_char r u * g51_char r v := by
  unfold g51_char
  rw [g51_dot_add_right]
  rcases g51_zmod2_eq_zero_or_one (g51_dot r u) with hu | hu <;>
    rcases g51_zmod2_eq_zero_or_one (g51_dot r v) with hv | hv <;>
    simp [hu, hv, g51_zmod2_add_self]

private lemma g51_char_add_left {n : ℕ} (r s v : 𝔽₂ n) :
    g51_char (r + s) v = g51_char r v * g51_char s v := by
  unfold g51_char
  rw [g51_dot_add_left]
  rcases g51_zmod2_eq_zero_or_one (g51_dot r v) with hr | hr <;>
    rcases g51_zmod2_eq_zero_or_one (g51_dot s v) with hs | hs <;>
    simp [hr, hs, g51_zmod2_add_self]

private lemma g51_char_zero_right {n : ℕ} (r : 𝔽₂ n) : g51_char r 0 = 1 := by
  simp [g51_char, g51_dot_zero_right]

private lemma g51_dot_single_left {n : ℕ} (i : Fin n) (v : 𝔽₂ n) :
    g51_dot (Pi.single i (1 : ZMod 2)) v = v i := by
  unfold g51_dot
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hne
    simp [Pi.single_eq_of_ne hne]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma g51_card_f2 (n : ℕ) : Fintype.card (𝔽₂ n) = 2 ^ n := by
  simp [𝔽₂, 𝔽]

private lemma g51_sum_char {n : ℕ} (v : 𝔽₂ n) :
    ∑ r : 𝔽₂ n, g51_char r v = if v = 0 then (2 : ℝ) ^ n else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [g51_char_zero_right]
  · simp only [hv, ite_false]
    have hex : ∃ i : Fin n, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨i, hi⟩ := hex
    let s : 𝔽₂ n := Pi.single i (1 : ZMod 2)
    have hchar_s : g51_char s v = -1 := by
      unfold g51_char
      rw [g51_dot_single_left]
      simp [hi]
    let e : 𝔽₂ n ≃ 𝔽₂ n :=
      { toFun := fun r => r + s
        invFun := fun r => r + s
        left_inv := fun r => by dsimp only; rw [add_assoc, g51_f2_add_self, add_zero]
        right_inv := fun r => by dsimp only; rw [add_assoc, g51_f2_add_self, add_zero] }
    have hneg : ∑ r : 𝔽₂ n, g51_char r v = - ∑ r : 𝔽₂ n, g51_char r v := by
      calc ∑ r : 𝔽₂ n, g51_char r v
          = ∑ r : 𝔽₂ n, g51_char (e r) v := (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
        _ = ∑ r : 𝔽₂ n, - g51_char r v := by
            apply Finset.sum_congr rfl
            intro r _
            change g51_char (r + s) v = - g51_char r v
            rw [g51_char_add_left, hchar_s]
            ring
        _ = - ∑ r : 𝔽₂ n, g51_char r v := by rw [Finset.sum_neg_distrib]
    linarith

private lemma g51_fourier_f2 {n : ℕ} (h : 𝔽₂ n → ℝ) (g : 𝔽₂ n) :
    h g = ((2 : ℝ) ^ n)⁻¹ * ∑ r : 𝔽₂ n, (∑ v : 𝔽₂ n, h v * g51_char r v) * g51_char r g := by
  simp_rw [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  have hinner : ∀ v : 𝔽₂ n,
      ∑ r : 𝔽₂ n, h v * (g51_char r v * g51_char r g) =
        h v * (if v = g then (2 : ℝ) ^ n else 0) := by
    intro v
    rw [← Finset.mul_sum]
    congr 1
    simp_rw [← g51_char_add_right, g51_sum_char, g51_f2_add_eq_zero_iff]
  simp_rw [hinner]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hpos : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp [hpos]

private lemma g51_char_sum {n m : ℕ} (r : 𝔽₂ n) (f : Fin m → 𝔽₂ n) :
    g51_char r (∑ j : Fin m, f j) = ∏ j : Fin m, g51_char r (f j) := by
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp [g51_char_zero_right]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, g51_char_add_right, ih]

private lemma g51_exists_good_functional {n : ℕ} (A D : Finset (𝔽₂ n)) (ε : ℝ)
    (_hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hA : (1 / 2 : ℝ) - ε ≤ (A.dens : ℝ))
    (hD_ne : D.Nonempty)
    (hD_miss : ∀ d ∈ D, d ∉ A + A) :
    ∃ r : 𝔽₂ n, ((D.filter (fun v => g51_dot r v = 0)).card : ℝ) ≤ 256 * ε ^ 2 * (D.card : ℝ) := by
  set m := D.card
  have hm_pos : 0 < m := hD_ne.card_pos
  let eqD : D ≃ Fin m := D.equivFin
  let d : Fin m → 𝔽₂ n := fun j => (eqD.symm j).1
  have hd_mem : ∀ j : Fin m, d j ∈ D := fun j => (eqD.symm j).2
  have hd_miss : ∀ j : Fin m, d j ∉ A + A := fun j => hD_miss (d j) (hd_mem j)
  let d0 : 𝔽₂ n := d ⟨0, hm_pos⟩
  have hd0_miss : d0 ∉ A + A := hd_miss ⟨0, hm_pos⟩
  let Φ : g51_Cube m → 𝔽₂ n := fun y => ∑ j : Fin m, if y j then d j else 0
  let h : 𝔽₂ n → ℝ := fun g => (if g ∈ A then (1 : ℝ) else 0) - (if g + d0 ∈ A then 1 else 0)
  let u : 𝔽₂ n → g51_Cube m → ℝ := fun x y => g51_walsh Finset.univ y * h (x + Φ y)
  have hnot_both : ∀ g : 𝔽₂ n, ¬ (g ∈ A ∧ g + d0 ∈ A) := by
    intro g ⟨h1, h2⟩
    apply hd0_miss
    have hsum : g + (g + d0) = d0 := g51_f2_add_cancel_left g d0
    rw [← hsum]
    exact Finset.add_mem_add h1 h2
  have hwalsh_univ_pm : ∀ y : g51_Cube m, g51_walsh Finset.univ y = 1 ∨ g51_walsh Finset.univ y = -1 := by
    intro y
    unfold g51_walsh
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => left; simp
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj]
      rcases ih with h' | h' <;> cases y j <;> simp [h']
  have hval : ∀ x y, u x y = -1 ∨ u x y = 0 ∨ u x y = 1 := by
    intro x y
    dsimp only [u, h]
    rcases hwalsh_univ_pm y with hw | hw <;>
      by_cases h1 : x + Φ y ∈ A <;> by_cases h2 : x + Φ y + d0 ∈ A
    · exact (hnot_both _ ⟨h1, h2⟩).elim
    · simp [hw, h1, h2]
    · simp [hw, h1, h2]
    · simp [hw, h1, h2]
    · exact (hnot_both _ ⟨h1, h2⟩).elim
    · simp [hw, h1, h2]
    · simp [hw, h1, h2]
    · simp [hw, h1, h2]
  have hsep : ∀ x y (j : Fin m) (b : Bool), |u x y - u x (Function.update y j b)| ≤ 1 := by
    intro x y j b
    by_cases hby : b = y j
    · subst hby
      simp [Function.update_eq_self]
    · have hupd : Function.update y j b = Function.update y j (!y j) := by
        congr 1
        cases b <;> cases hy : y j <;> simp_all
      rw [hupd]
      have hΦ : Φ (Function.update y j (!y j)) = Φ y + d j := by
        dsimp only [Φ]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
            ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have hrest :
            ∑ i ∈ Finset.univ.erase j, (if Function.update y j (!y j) i then d i else 0) =
              ∑ i ∈ Finset.univ.erase j, (if y i then d i else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hne : i ≠ j := Finset.ne_of_mem_erase hi
          simp [Function.update, hne]
        rw [hrest]
        cases hy : y j
        · simp [add_comm]
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Function.update_self, zero_add]
          rw [add_assoc, add_comm (∑ i ∈ Finset.univ.erase j, if y i then d i else 0) (d j),
              ← add_assoc, g51_f2_add_self, zero_add]
      have hwneg : g51_walsh Finset.univ (Function.update y j (!y j)) = - g51_walsh Finset.univ y :=
        g51_walsh_update_neg Finset.univ (Finset.mem_univ j) y
      set g := x + Φ y
      have hdiff_eq : u x y - u x (Function.update y j (!y j)) =
          g51_walsh Finset.univ y * (h g + h (g + d j)) := by
        dsimp only [u]
        rw [hwneg, hΦ, ← add_assoc]
        ring
      rw [hdiff_eq, abs_mul]
      have hwabs : |g51_walsh Finset.univ y| = 1 := by
        rcases hwalsh_univ_pm y with hw | hw <;> rw [hw] <;> norm_num
      rw [hwabs, one_mul]
      have hnot_dj : ∀ v : 𝔽₂ n, ¬ (v ∈ A ∧ v + d j ∈ A) := by
        intro v ⟨hv1, hv2⟩
        apply hd_miss j
        rw [← g51_f2_add_cancel_left v (d j)]
        exact Finset.add_mem_add hv1 hv2
      dsimp only [h]
      by_cases ha1 : g ∈ A <;> by_cases ha2 : g + d0 ∈ A <;>
        by_cases hb1 : g + d j ∈ A <;> by_cases hb2 : g + d j + d0 ∈ A
      · exact (hnot_both g ⟨ha1, ha2⟩).elim
      · exact (hnot_both g ⟨ha1, ha2⟩).elim
      · exact (hnot_both g ⟨ha1, ha2⟩).elim
      · exact (hnot_both g ⟨ha1, ha2⟩).elim
      · exact (hnot_both (g + d j) ⟨hb1, hb2⟩).elim
      · exact (hnot_dj g ⟨ha1, hb1⟩).elim
      · simp [ha1, ha2, hb1, hb2]
      · simp [ha1, ha2, hb1, hb2]
      · exact (hnot_both (g + d j) ⟨hb1, hb2⟩).elim
      · simp [ha1, ha2, hb1, hb2]
      · have : g + d0 + d j = g + d j + d0 := by abel
        exact (hnot_dj (g + d0) ⟨ha2, this.symm ▸ hb2⟩).elim
      · simp [ha1, ha2, hb1, hb2]
      · exact (hnot_both (g + d j) ⟨hb1, hb2⟩).elim
      · simp [ha1, ha2, hb1, hb2]
      · simp [ha1, ha2, hb1, hb2]
      · simp [ha1, ha2, hb1, hb2]
  have havg_zd : ∑ x : 𝔽₂ n, g51_zeroDens (u x) = (2 : ℝ) ^ n * (1 - 2 * (A.dens : ℝ)) := by
    unfold g51_zeroDens g51_mean
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hinner : ∀ y : g51_Cube m,
        ∑ x : 𝔽₂ n, (if u x y = 0 then (1 : ℝ) else 0) = (2 : ℝ) ^ n - 2 * (A.card : ℝ) := by
      intro y
      have hzero_iff : ∀ x : 𝔽₂ n, u x y = 0 ↔ x + Φ y ∉ A ∧ x + Φ y + d0 ∉ A := by
        intro x
        dsimp only [u, h]
        have hwne : g51_walsh Finset.univ y ≠ 0 := by
          rcases hwalsh_univ_pm y with hw | hw <;> rw [hw] <;> norm_num
        rw [mul_eq_zero]
        simp only [hwne, false_or]
        by_cases h1 : x + Φ y ∈ A <;> by_cases h2 : x + Φ y + d0 ∈ A
        · exact (hnot_both _ ⟨h1, h2⟩).elim
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      let e : 𝔽₂ n ≃ 𝔽₂ n :=
        { toFun := fun x => x + Φ y
          invFun := fun x => x + Φ y
          left_inv := fun x => by dsimp only; rw [add_assoc, g51_f2_add_self, add_zero]
          right_inv := fun x => by dsimp only; rw [add_assoc, g51_f2_add_self, add_zero] }
      have hshift :
          ∑ x : 𝔽₂ n, (if u x y = 0 then (1 : ℝ) else 0) =
            ∑ g : 𝔽₂ n, (if g ∉ A ∧ g + d0 ∉ A then (1 : ℝ) else 0) := by
        calc ∑ x : 𝔽₂ n, (if u x y = 0 then (1 : ℝ) else 0)
            = ∑ x : 𝔽₂ n, (if e x ∉ A ∧ e x + d0 ∉ A then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              simp [hzero_iff, e]
          _ = ∑ g : 𝔽₂ n, (if g ∉ A ∧ g + d0 ∉ A then (1 : ℝ) else 0) :=
              Fintype.sum_equiv e _ _ (fun _ => rfl)
      rw [hshift]
      have hpt : ∀ g : 𝔽₂ n,
          (if g ∉ A ∧ g + d0 ∉ A then (1 : ℝ) else 0) =
            1 - (if g ∈ A then (1 : ℝ) else 0) - (if g + d0 ∈ A then (1 : ℝ) else 0) := by
        intro g
        by_cases h1 : g ∈ A <;> by_cases h2 : g + d0 ∈ A
        · exact (hnot_both g ⟨h1, h2⟩).elim
        · simp [h1, h2]
        · simp [h1, h2]
        · simp [h1, h2]
      simp_rw [hpt, Finset.sum_sub_distrib]
      have h1 : ∑ _g : 𝔽₂ n, (1 : ℝ) = (2 : ℝ) ^ n := by simp
      have h2 : ∑ g : 𝔽₂ n, (if g ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by simp
      have h3 : ∑ g : 𝔽₂ n, (if g + d0 ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
        let e0 : 𝔽₂ n ≃ 𝔽₂ n :=
          { toFun := fun g => g + d0
            invFun := fun g => g + d0
            left_inv := fun g => by dsimp only; rw [add_assoc, g51_f2_add_self, add_zero]
            right_inv := fun g => by dsimp only; rw [add_assoc, g51_f2_add_self, add_zero] }
        rw [Fintype.sum_equiv e0 (fun g => if g + d0 ∈ A then (1 : ℝ) else 0)
              (fun g => if g ∈ A then (1 : ℝ) else 0) (fun _ => rfl)]
        simp
      rw [h1, h2, h3]
      ring
    simp_rw [hinner]
    simp only [Finset.sum_const, Finset.card_univ, g51_card_cube, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat]
    have hpowm : (2 : ℝ) ^ m ≠ 0 := by positivity
    have hpown : (2 : ℝ) ^ n ≠ 0 := by positivity
    have hdens : (A.dens : ℝ) = (A.card : ℝ) / (2 : ℝ) ^ n := by
      rw [Finset.nnratCast_dens, g51_card_f2]
      norm_cast
    rw [hdens]
    field_simp [hpowm, hpown]
  have hex_x : ∃ x : 𝔽₂ n, g51_zeroDens (u x) ≤ 2 * ε := by
    by_contra hno
    push Not at hno
    have hgt : ∑ x : 𝔽₂ n, (2 * ε) < ∑ x : 𝔽₂ n, g51_zeroDens (u x) := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro x _
      exact hno x
    simp only [Finset.sum_const, Finset.card_univ, g51_card_f2, nsmul_eq_mul, Nat.cast_pow,
      Nat.cast_ofNat] at hgt
    rw [havg_zd] at hgt
    have hpown : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    nlinarith
  obtain ⟨x, hx⟩ := hex_x
  have hzx : g51_zeroDens (u x) ≤ 1 / 2 := by linarith
  obtain ⟨S, hS_ne, hS_card⟩ := g51_exists_low_degree_walsh (u x) (hval x) (hsep x) hzx
  have hS_bound : (S.card : ℝ) ≤ 256 * ε ^ 2 * (m : ℝ) := by
    have hzd_nonneg : 0 ≤ g51_zeroDens (u x) := g51_zeroDens_nonneg (u x)
    have hsq : (g51_zeroDens (u x)) ^ 2 ≤ (2 * ε) ^ 2 :=
      pow_le_pow_left₀ hzd_nonneg hx 2
    nlinarith
  let Z : 𝔽₂ n → Finset (Fin m) := fun r => Finset.univ.filter (fun j : Fin m => g51_dot r (d j) = 0)
  let coeff : 𝔽₂ n → ℝ := fun r =>
    ((2 : ℝ) ^ n)⁻¹ * (∑ v : 𝔽₂ n, h v * g51_char r v) * g51_char r x
  have hu_expand : ∀ y : g51_Cube m,
      u x y = ∑ r : 𝔽₂ n, coeff r * g51_walsh (Z r) y := by
    intro y
    dsimp only [u, coeff]
    rw [g51_fourier_f2 h (x + Φ y), Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [g51_char_add_right]
    have hprod : g51_walsh Finset.univ y * g51_char r (Φ y) = g51_walsh (Z r) y := by
      dsimp only [Φ]
      rw [g51_char_sum, g51_walsh_eq_prod_univ, g51_walsh_eq_prod_univ, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      by_cases hdot : g51_dot r (d j) = 0 <;> cases y j <;>
        simp [Z, g51_char, g51_dot_zero_right, hdot]
    calc g51_walsh Finset.univ y * (((2 : ℝ) ^ n)⁻¹ *
            ((∑ v : 𝔽₂ n, h v * g51_char r v) * (g51_char r x * g51_char r (Φ y))))
        = (((2 : ℝ) ^ n)⁻¹ * (∑ v : 𝔽₂ n, h v * g51_char r v) * g51_char r x) *
            (g51_walsh Finset.univ y * g51_char r (Φ y)) := by ring
      _ = _ := by rw [hprod]
  have hwc : g51_walshCoeff (u x) S = ∑ r : 𝔽₂ n, if Z r = S then coeff r else 0 := by
    unfold g51_walshCoeff
    simp_rw [hu_expand, Finset.sum_mul]
    unfold g51_mean
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    have hpull :
        ∑ y : g51_Cube m, coeff r * g51_walsh (Z r) y * g51_walsh S y =
          coeff r * ∑ y : g51_Cube m, g51_walsh (Z r) y * g51_walsh S y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [hpull]
    have horth := g51_mean_walsh_mul (Z r) S
    unfold g51_mean at horth
    calc ((2 : ℝ) ^ m)⁻¹ * (coeff r * ∑ y : g51_Cube m, g51_walsh (Z r) y * g51_walsh S y)
        = coeff r * (((2 : ℝ) ^ m)⁻¹ * ∑ y : g51_Cube m, g51_walsh (Z r) y * g51_walsh S y) := by ring
      _ = coeff r * (if Z r = S then 1 else 0) := by rw [horth]
      _ = if Z r = S then coeff r else 0 := by split_ifs <;> ring
  have hex_r : ∃ r : 𝔽₂ n, Z r = S := by
    by_contra hno
    push Not at hno
    apply hS_ne
    rw [hwc]
    apply Finset.sum_eq_zero
    intro r _
    simp [hno r]
  obtain ⟨r, hr⟩ := hex_r
  refine ⟨r, ?_⟩
  have hcard_eq : (D.filter (fun v => g51_dot r v = 0)).card = (Z r).card := by
    apply Finset.card_bij (fun v hv => eqD ⟨v, (Finset.mem_filter.mp hv).1⟩)
    · intro v hv
      simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
      have hvD := (Finset.mem_filter.mp hv).1
      have hv0 := (Finset.mem_filter.mp hv).2
      simpa [d] using hv0
    · intro v₁ hv₁ v₂ hv₂ heq
      have h1 := eqD.injective heq
      exact congrArg Subtype.val h1
    · intro j hj
      simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨d j, Finset.mem_filter.mpr ⟨hd_mem j, hj⟩, ?_⟩
      simp [d]
  rw [hcard_eq, hr]
  exact hS_bound

/- ### Part 5: Minimal covering obstruction, polynomial interpolation, and main bound -/

private def g51_CoveredBy {n : ℕ} (k : ℕ) (S : Finset (𝔽₂ n)) : Prop :=
  ∃ r : Fin k → 𝔽₂ n, ∀ s ∈ S, ∃ i : Fin k, g51_dot (r i) s ≠ 0

private def g51_monom {n : ℕ} (I : Finset (Fin n)) (x : 𝔽₂ n) : ZMod 2 :=
  ∏ i ∈ I, x i

private def g51_polySpace (n k : ℕ) : Submodule (ZMod 2) (𝔽₂ n → ZMod 2) :=
  Submodule.span (ZMod 2) (g51_monom '' {I : Finset (Fin n) | I.card ≤ k})

private lemma g51_monom_mul_coord {n : ℕ} (I : Finset (Fin n)) (a : Fin n) :
    (fun x : 𝔽₂ n => g51_monom I x * x a) = g51_monom (insert a I) := by
  funext x
  unfold g51_monom
  by_cases ha : a ∈ I
  · rw [Finset.insert_eq_of_mem ha, ← Finset.mul_prod_erase I _ ha]
    rw [mul_comm (x a), mul_assoc, g51_zmod2_mul_self, mul_comm]
  · rw [Finset.prod_insert ha, mul_comm]

private lemma g51_polySpace_mono {n k : ℕ} :
    g51_polySpace n k ≤ g51_polySpace n (k + 1) := by
  apply Submodule.span_mono
  rintro f ⟨I, hI, rfl⟩
  exact ⟨I, Nat.le_succ_of_le hI, rfl⟩

private lemma g51_mul_one_sub_dot_mem {n k : ℕ} (r : 𝔽₂ n) {f : 𝔽₂ n → ZMod 2}
    (hf : f ∈ g51_polySpace n k) :
    (fun x : 𝔽₂ n => f x * (1 - g51_dot r x)) ∈ g51_polySpace n (k + 1) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨I, hI, rfl⟩
    have hrew : (fun x : 𝔽₂ n => g51_monom I x * (1 - g51_dot r x)) =
        g51_monom I - ∑ a : Fin n, r a • g51_monom (insert a I) := by
      funext x
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g51_dot]
      rw [mul_sub, mul_one, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      have hm := congrFun (g51_monom_mul_coord I a) x
      rw [← hm]
      ring
    rw [hrew]
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨I, Nat.le_succ_of_le hI, rfl⟩
    · apply Submodule.sum_mem
      intro a _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨insert a I, le_trans (Finset.card_insert_le a I) (Nat.add_le_add_right hI 1), rfl⟩
  | zero =>
    have h0 : (fun x : 𝔽₂ n => (0 : 𝔽₂ n → ZMod 2) x * (1 - g51_dot r x)) = 0 := by
      funext x; simp
    rw [h0]
    exact Submodule.zero_mem _
  | add g₁ g₂ _ _ ih₁ ih₂ =>
    have hrew : (fun x : 𝔽₂ n => (g₁ + g₂) x * (1 - g51_dot r x)) =
        (fun x => g₁ x * (1 - g51_dot r x)) + (fun x => g₂ x * (1 - g51_dot r x)) := by
      funext x; simp [add_mul]
    rw [hrew]
    exact Submodule.add_mem _ ih₁ ih₂
  | smul c g _ ih =>
    have hrew : (fun x : 𝔽₂ n => (c • g) x * (1 - g51_dot r x)) =
        c • (fun x => g x * (1 - g51_dot r x)) := by
      funext x; simp [mul_assoc]
    rw [hrew]
    exact Submodule.smul_mem _ c ih

private lemma g51_prod_one_sub_dot_mem {n : ℕ} :
    ∀ (k : ℕ) (r : Fin k → 𝔽₂ n),
      (fun x : 𝔽₂ n => ∏ i : Fin k, (1 - g51_dot (r i) x)) ∈ g51_polySpace n k
  | 0, _ => by
    have h1 : (fun x : 𝔽₂ n => ∏ i : Fin 0, (1 - g51_dot (Fin.elim0 i) x)) = g51_monom ∅ := by
      funext x; simp [g51_monom]
    have h1' : (fun _ : 𝔽₂ n => (1 : ZMod 2)) = g51_monom ∅ := by
      funext x; simp [g51_monom]
    change (fun _ : 𝔽₂ n => (1 : ZMod 2)) ∈ g51_polySpace n 0
    rw [h1']
    exact Submodule.subset_span ⟨∅, by simp, rfl⟩
  | k + 1, r => by
    have hrew : (fun x : 𝔽₂ n => ∏ i : Fin (k + 1), (1 - g51_dot (r i) x)) =
        (fun x : 𝔽₂ n => (∏ i : Fin k, (1 - g51_dot (r i.castSucc) x)) *
          (1 - g51_dot (r (Fin.last k)) x)) := by
      funext x
      exact Fin.prod_univ_castSucc _
    rw [hrew]
    exact g51_mul_one_sub_dot_mem (r (Fin.last k)) (g51_prod_one_sub_dot_mem k (fun i => r i.castSucc))

private lemma g51_finrank_polySpace (n k : ℕ) :
    Module.finrank (ZMod 2) (g51_polySpace n k) ≤
      ∑ j ∈ Finset.range (k + 1), Nat.choose n j := by
  let T : Finset (Finset (Fin n)) := Finset.univ.filter (fun I => I.card ≤ k)
  have hset : g51_monom '' {I : Finset (Fin n) | I.card ≤ k} = ↑(T.image g51_monom) := by
    ext f
    simp [T]
  unfold g51_polySpace
  rw [hset]
  calc Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (↑(T.image g51_monom) : Set (𝔽₂ n → ZMod 2)))
      ≤ (T.image g51_monom).card := by
        simpa using finrank_span_le_card (R := ZMod 2) (↑(T.image g51_monom) : Set (𝔽₂ n → ZMod 2))
    _ ≤ T.card := Finset.card_image_le
    _ = ∑ j ∈ Finset.range (k + 1), Nat.choose n j := by
        have hT : T = (Finset.range (k + 1)).biUnion (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n))) := by
          ext I
          simp [T]
        rw [hT, Finset.card_biUnion]
        · apply Finset.sum_congr rfl
          intro j _
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        · intro i _ j _ hij
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro I hIi hIj
          simp only [Finset.mem_powersetCard] at hIi hIj
          exact hij (hIi.2.symm.trans hIj.2)

private lemma g51_minimal_obstruction_card_le {n k : ℕ} (M : Finset (𝔽₂ n))
    (hM_not : ¬ g51_CoveredBy k M)
    (hM_min : ∀ s ∈ M, g51_CoveredBy k (M.erase s)) :
    M.card ≤ ∑ j ∈ Finset.range (k + 1), Nat.choose n j := by
  choose r hr using fun s : M => hM_min s.1 s.2
  have hrs_zero : ∀ (s : M) (i : Fin k), g51_dot (r s i) s.1 = 0 := by
    intro s i
    by_contra hne
    apply hM_not
    refine ⟨r s, fun t ht => ?_⟩
    by_cases hts : t = s.1
    · exact ⟨i, hts ▸ hne⟩
    · exact hr s t (Finset.mem_erase.mpr ⟨hts, ht⟩)
  let P : M → g51_polySpace n k := fun s =>
    ⟨fun x => ∏ i : Fin k, (1 - g51_dot (r s i) x), g51_prod_one_sub_dot_mem k (r s)⟩
  have hP_diag : ∀ s : M, (P s).1 s.1 = 1 := by
    intro s
    change ∏ i : Fin k, (1 - g51_dot (r s i) s.1) = 1
    simp [hrs_zero s]
  have hP_off : ∀ s t : M, t ≠ s → (P s).1 t.1 = 0 := by
    intro s t hne
    change ∏ i : Fin k, (1 - g51_dot (r s i) t.1) = 0
    have ht_er : t.1 ∈ M.erase s.1 := Finset.mem_erase.mpr ⟨fun h => hne (Subtype.ext h), t.2⟩
    obtain ⟨i, hi⟩ := hr s t.1 ht_er
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases g51_zmod2_eq_zero_or_one (g51_dot (r s i) t.1) with h0 | h1
    · exact (hi h0).elim
    · rw [h1, sub_self]
  have hlin : LinearIndependent (ZMod 2) P := by
    rw [Fintype.linearIndependent_iff]
    intro c hc t
    have heval := congrFun (congrArg Subtype.val hc) t.1
    simp only [Submodule.coe_sum, Submodule.coe_smul, ZeroMemClass.coe_zero,
      Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at heval
    rw [Finset.sum_eq_single t] at heval
    · simpa [hP_diag t] using heval
    · intro s _ hst
      rw [hP_off s t (Ne.symm hst), mul_zero]
    · intro ht
      exact (ht (Finset.mem_univ t)).elim
  calc M.card
      = Fintype.card M := (Fintype.card_coe M).symm
    _ ≤ Module.finrank (ZMod 2) (g51_polySpace n k) := hlin.fintype_card_le_finrank
    _ ≤ ∑ j ∈ Finset.range (k + 1), Nat.choose n j := g51_finrank_polySpace n k

private lemma g51_sum_choose_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ)) ≤
      (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 1 ≤ n := le_trans hk hkn
    positivity
  set x : ℝ := (k : ℝ) / (n : ℝ)
  have hx_pos : 0 < x := div_pos hk_pos hn_pos
  have hx_le : x ≤ 1 := (div_le_one hn_pos).mpr (Nat.cast_le.mpr hkn)
  have h1 : x ^ k * ∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ) ≤ (Real.exp 1) ^ k := by
    calc x ^ k * ∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ)
        = ∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ) * x ^ k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ ≤ ∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ) * x ^ j := by
          apply Finset.sum_le_sum
          intro j hj
          have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (le_of_lt hx_pos) hx_le hjk)
            (Nat.cast_nonneg _)
      _ ≤ ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) * x ^ j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_mono (Nat.add_le_add_right hkn 1)
          · intro j _ _
            positivity
      _ = (x + 1) ^ n := by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ ≤ (Real.exp x) ^ n := pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp x) n
      _ = Real.exp ((n : ℝ) * x) := (Real.exp_nat_mul x n).symm
      _ = Real.exp ((k : ℝ) * 1) := by
          congr 1
          dsimp only [x]
          field_simp [ne_of_gt hn_pos]
      _ = (Real.exp 1) ^ k := by rw [Real.exp_nat_mul]
  have hxk_pos : 0 < x ^ k := pow_pos hx_pos k
  have hdiv : ∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ) ≤ (Real.exp 1) ^ k / x ^ k :=
    (le_div_iff₀' hxk_pos).mpr h1
  calc ∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ)
      ≤ (Real.exp 1) ^ k / x ^ k := hdiv
    _ = (Real.exp 1 / x) ^ k := (div_pow (Real.exp 1) x k).symm
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
        congr 1
        dsimp only [x]
        field_simp [ne_of_gt hk_pos, ne_of_gt hn_pos]

private lemma g51_greedy_iter {n : ℕ} (A M : Finset (𝔽₂ n)) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hA : (1 / 2 : ℝ) - ε ≤ (A.dens : ℝ))
    (hM_miss : ∀ d ∈ M, d ∉ A + A)
    (k : ℕ) (hM_not : ¬ g51_CoveredBy k M) :
    ∀ t ≤ k, ∃ r : Fin t → 𝔽₂ n,
      ((M.filter (fun b => ∀ i : Fin t, g51_dot (r i) b = 0)).card : ℝ) ≤
        (256 * ε ^ 2) ^ t * (M.card : ℝ) := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨Fin.elim0, ?_⟩
    simp
  | succ t ih =>
    intro htk
    obtain ⟨r, hr⟩ := ih (Nat.le_of_succ_le htk)
    let Dt := M.filter (fun b => ∀ i : Fin t, g51_dot (r i) b = 0)
    have hDt_ne : Dt.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hM_not
      refine ⟨fun i : Fin k => if hi : i.1 < t then r ⟨i.1, hi⟩ else 0, fun s hs => ?_⟩
      have hs_not : s ∉ Dt := hempty ▸ Finset.notMem_empty s
      simp only [Dt, Finset.mem_filter, hs, true_and, not_forall] at hs_not
      obtain ⟨i, hi⟩ := hs_not
      refine ⟨⟨i.1, lt_of_lt_of_le i.2 (Nat.le_of_succ_le htk)⟩, ?_⟩
      simpa [i.2] using hi
    have hDt_miss : ∀ d ∈ Dt, d ∉ A + A := fun d hd => hM_miss d (Finset.mem_filter.mp hd).1
    obtain ⟨r_next, hr_next⟩ := g51_exists_good_functional A Dt ε hε0 hε hA hDt_ne hDt_miss
    let r' : Fin (t + 1) → 𝔽₂ n := Fin.snoc r r_next
    refine ⟨r', ?_⟩
    have hfilt :
        M.filter (fun b => ∀ i : Fin (t + 1), g51_dot (r' i) b = 0) =
          Dt.filter (fun b => g51_dot r_next b = 0) := by
      ext b
      simp only [Dt, Finset.mem_filter, and_assoc]
      constructor
      · rintro ⟨hb, hall⟩
        refine ⟨hb, fun i => ?_, ?_⟩
        · simpa [r', Fin.snoc_castSucc] using hall i.castSucc
        · simpa [r', Fin.snoc_last] using hall (Fin.last t)
      · rintro ⟨hb, hall, hlast⟩
        refine ⟨hb, fun i => ?_⟩
        refine Fin.lastCases ?_ ?_ i
        · simpa [r', Fin.snoc_last] using hlast
        · intro j
          simpa [r', Fin.snoc_castSucc] using hall j
    rw [hfilt]
    calc ((Dt.filter (fun b => g51_dot r_next b = 0)).card : ℝ)
        ≤ 256 * ε ^ 2 * (Dt.card : ℝ) := hr_next
      _ ≤ 256 * ε ^ 2 * ((256 * ε ^ 2) ^ t * (M.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (256 * ε ^ 2) ^ (t + 1) * (M.card : ℝ) := by ring

private lemma g51_subspace_codim_bound {n : ℕ} (A : Finset (𝔽₂ n)) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hA : (1 / 2 : ℝ) - ε ≤ (A.dens : ℝ)) :
    ∃ H : Submodule (ZMod 2) (𝔽₂ n),
      (H : Set (𝔽₂ n)) ⊆ ↑(A + A) ∧
      (n : ℝ) ≤ (Module.finrank (ZMod 2) H : ℝ) +
        (1 + 256 * Real.exp 1 * (n : ℝ) * ε ^ 2) := by
  let B : Finset (𝔽₂ n) := Finset.univ.filter (fun x => x ∉ A + A)
  have hA_ne : A.Nonempty := by
    have hpos : (0 : ℝ) < (A.dens : ℝ) := by linarith
    exact Finset.dens_pos.mp (by exact_mod_cast hpos)
  have h0_mem : (0 : 𝔽₂ n) ∈ A + A := by
    obtain ⟨a, ha⟩ := hA_ne
    rw [← g51_f2_add_self a]
    exact Finset.add_mem_add ha ha
  have hcov_n : g51_CoveredBy n B := by
    refine ⟨fun i => Pi.single i (1 : ZMod 2), fun b hb => ?_⟩
    have hb_ne : b ≠ 0 := by
      intro h0
      exact (Finset.mem_filter.mp hb).2 (h0 ▸ h0_mem)
    have hex : ∃ i : Fin n, b i ≠ 0 := by
      by_contra h
      push Not at h
      exact hb_ne (funext h)
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simpa [g51_dot_single_left] using hi⟩
  classical
  let d : ℕ := Nat.find (⟨n, hcov_n⟩ : ∃ m, g51_CoveredBy m B)
  have hd_cov : g51_CoveredBy d B := Nat.find_spec (⟨n, hcov_n⟩ : ∃ m, g51_CoveredBy m B)
  have hd_le_n : d ≤ n := Nat.find_min' (⟨n, hcov_n⟩ : ∃ m, g51_CoveredBy m B) hcov_n
  have hd_min : ∀ m < d, ¬ g51_CoveredBy m B := fun m hm =>
    Nat.find_min (⟨n, hcov_n⟩ : ∃ m, g51_CoveredBy m B) hm
  obtain ⟨r, hr⟩ := hd_cov
  let T : 𝔽₂ n →ₗ[ZMod 2] (Fin d → ZMod 2) :=
    { toFun := fun x i => g51_dot (r i) x
      map_add' := fun x y => by funext i; exact g51_dot_add_right (r i) x y
      map_smul' := fun c x => by
        funext i
        simp only [g51_dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }
  let H : Submodule (ZMod 2) (𝔽₂ n) := LinearMap.ker T
  have hH_sub : (H : Set (𝔽₂ n)) ⊆ ↑(A + A) := by
    intro x hx
    change x ∈ A + A
    by_contra hnot
    have hxB : x ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hnot⟩
    obtain ⟨i, hi⟩ := hr x hxB
    have hTx : T x = 0 := LinearMap.mem_ker.mp hx
    exact hi (congrFun hTx i)
  have hH_rank : n ≤ Module.finrank (ZMod 2) H + d := by
    have hrn := LinearMap.finrank_range_add_finrank_ker T
    have hdom : Module.finrank (ZMod 2) (𝔽₂ n) = n := Module.finrank_fin_fun (ZMod 2)
    have hcod : Module.finrank (ZMod 2) (LinearMap.range T) ≤ d := by
      calc Module.finrank (ZMod 2) (LinearMap.range T)
          ≤ Module.finrank (ZMod 2) (Fin d → ZMod 2) := Submodule.finrank_le _
        _ = d := Module.finrank_fin_fun (ZMod 2)
    change n ≤ Module.finrank (ZMod 2) (LinearMap.ker T) + d
    omega
  have hd_bound : (d : ℝ) ≤ 1 + 256 * Real.exp 1 * (n : ℝ) * ε ^ 2 := by
    by_cases hd1 : d ≤ 1
    · have : (d : ℝ) ≤ 1 := by exact_mod_cast hd1
      have hpos : 0 ≤ 256 * Real.exp 1 * (n : ℝ) * ε ^ 2 := by positivity
      linarith
    · push Not at hd1
      set k := d - 1
      have hk1 : 1 ≤ k := by omega
      have hkd : k < d := by omega
      have hkn : k ≤ n := le_trans (le_of_lt hkd) hd_le_n
      have hd_eq : (d : ℝ) = (k : ℝ) + 1 := by
        have : d = k + 1 := by omega
        rw [this, Nat.cast_add, Nat.cast_one]
      have hB_not : ¬ g51_CoveredBy k B := hd_min k hkd
      have hex_min : ∃ s : ℕ, ∃ M ⊆ B, M.card = s ∧ ¬ g51_CoveredBy k M :=
        ⟨B.card, B, Finset.Subset.refl B, rfl, hB_not⟩
      let s0 := Nat.find hex_min
      obtain ⟨M, hMB, hMcard, hM_not⟩ := Nat.find_spec hex_min
      have hM_min : ∀ v ∈ M, g51_CoveredBy k (M.erase v) := by
        intro v hv
        by_contra hnot
        have hlt : (M.erase v).card < Nat.find hex_min := by
          rw [← hMcard]
          exact Finset.card_erase_lt_of_mem hv
        exact Nat.find_min hex_min hlt
          ⟨M.erase v, Finset.Subset.trans (Finset.erase_subset v M) hMB, rfl, hnot⟩
      have hM_upper : (M.card : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
        calc (M.card : ℝ)
            ≤ (∑ j ∈ Finset.range (k + 1), (Nat.choose n j : ℝ)) := by
              exact_mod_cast g51_minimal_obstruction_card_le M hM_not hM_min
          _ ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := g51_sum_choose_le hk1 hkn
      have hM_miss : ∀ v ∈ M, v ∉ A + A := fun v hv => (Finset.mem_filter.mp (hMB hv)).2
      obtain ⟨rg, hrg⟩ := g51_greedy_iter A M ε hε0 hε hA hM_miss k hM_not k le_rfl
      let Dk := M.filter (fun b => ∀ i : Fin k, g51_dot (rg i) b = 0)
      have hDk_ne : Dk.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        apply hM_not
        refine ⟨rg, fun s hs => ?_⟩
        have hs_not : s ∉ Dk := hempty ▸ Finset.notMem_empty s
        simp only [Dk, Finset.mem_filter, hs, true_and, not_forall] at hs_not
        exact hs_not
      have h1_le : (1 : ℝ) ≤ (256 * Real.exp 1 * (n : ℝ) * ε ^ 2 / (k : ℝ)) ^ k := by
        calc (1 : ℝ)
            ≤ (Dk.card : ℝ) := by exact_mod_cast hDk_ne.card_pos
          _ ≤ (256 * ε ^ 2) ^ k * (M.card : ℝ) := hrg
          _ ≤ (256 * ε ^ 2) ^ k * (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k :=
              mul_le_mul_of_nonneg_left hM_upper (by positivity)
          _ = (256 * ε ^ 2 * (Real.exp 1 * (n : ℝ) / (k : ℝ))) ^ k := (mul_pow _ _ k).symm
          _ = (256 * Real.exp 1 * (n : ℝ) * ε ^ 2 / (k : ℝ)) ^ k := by
              congr 1
              ring
      have hratio : (1 : ℝ) ≤ 256 * Real.exp 1 * (n : ℝ) * ε ^ 2 / (k : ℝ) := by
        by_contra hlt
        push Not at hlt
        have hpow_lt : (256 * Real.exp 1 * (n : ℝ) * ε ^ 2 / (k : ℝ)) ^ k < 1 :=
          pow_lt_one₀ (by positivity) hlt (by omega)
        linarith
      have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
      have hk_le : (k : ℝ) ≤ 256 * Real.exp 1 * (n : ℝ) * ε ^ 2 := by
        have := (one_le_div hk_pos).mp hratio
        linarith
      linarith
  refine ⟨H, hH_sub, ?_⟩
  have hH_rankR : (n : ℝ) ≤ (Module.finrank (ZMod 2) H : ℝ) + (d : ℝ) := by
    exact_mod_cast hH_rank
  linarith

end G51Helpers

/--
If $A \subset \mathbb{F}_2^n$ has density $\alpha > 1/2 - k/\sqrt{n}$, then $A + A$ contains a
subspace of co-dimension at most $\lceil 1 + 256 e k^2 \rceil$.
-/
private theorem proved_one_half :
    ∀ (k : ℝ), 0 < k →
      ∃ (c : ℕ), ∀ᶠ (n : ℕ) in atTop,
        ∀ (α : ℝ), α > (1/2 : ℝ) - k / sqrt (n : ℝ) → α ≤ 1 →
          n ≤ guaranteedMaxCosetDim n α + c := by
  intro k hk
  refine ⟨Nat.ceil (1 + 256 * Real.exp 1 * k ^ 2), ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨max 1 (Nat.ceil (16 * k ^ 2)), fun n hn α hα hα1 => ?_⟩
  set c : ℕ := Nat.ceil (1 + 256 * Real.exp 1 * k ^ 2)
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hn_ge : 16 * k ^ 2 ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (le_trans (le_max_right _ _) hn))
  set ε : ℝ := k / Real.sqrt (n : ℝ)
  have hε0 : 0 ≤ ε := by positivity
  have hε_le : ε ≤ 1 / 4 := by
    dsimp only [ε]
    rw [div_le_div_iff₀ hsqrt_pos (by norm_num : (0 : ℝ) < 4)]
    have hsq : (k * 4) ^ 2 ≤ (Real.sqrt (n : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (le_of_lt hn_pos)]
      nlinarith
    nlinarith [sq_nonneg (k * 4 - Real.sqrt (n : ℝ))]
  have hne2 : (n : ℝ) * ε ^ 2 = k ^ 2 := by
    dsimp only [ε]
    rw [div_pow, Real.sq_sqrt (le_of_lt hn_pos)]
    field_simp [ne_of_gt hn_pos]
  have hbound : ∀ A : Finset (𝔽₂ n), (A.dens : ℝ) ≥ α →
      n - c ≤ maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A + A) := by
    intro A hAdens
    have hA' : (1 / 2 : ℝ) - ε ≤ (A.dens : ℝ) := by linarith
    obtain ⟨H, hH_sub, hH_dim⟩ := g51_subspace_codim_bound A ε hε0 hε_le hA'
    have hH_dim' : (n : ℝ) ≤ (Module.finrank (ZMod 2) H : ℝ) + (c : ℝ) := by
      have hc_ge : 1 + 256 * Real.exp 1 * k ^ 2 ≤ (c : ℝ) := Nat.le_ceil _
      have hrew : 1 + 256 * Real.exp 1 * (n : ℝ) * ε ^ 2 = 1 + 256 * Real.exp 1 * k ^ 2 := by
        calc 1 + 256 * Real.exp 1 * (n : ℝ) * ε ^ 2
            = 1 + 256 * Real.exp 1 * ((n : ℝ) * ε ^ 2) := by ring
          _ = 1 + 256 * Real.exp 1 * k ^ 2 := by rw [hne2]
      linarith
    have hH_nat : n ≤ Module.finrank (ZMod 2) H + c := by exact_mod_cast hH_dim'
    have hmono := maxCosetDim_mono (ZMod 2) (𝔽₂ n)
      (show (H.toAffineSubspace : Set (𝔽₂ n)) ⊆ ↑(A + A) from hH_sub)
    rw [maxCosetDim_affineSubspace, Submodule.toAffineSubspace_direction] at hmono
    omega
  have hS_ne :
      { maxCosetDim (ZMod 2) (𝔽₂ n) ↑(A + A) | (A : Finset (𝔽₂ n)) (_h : (A.dens : ℝ) ≥ α) }.Nonempty := by
    refine ⟨maxCosetDim (ZMod 2) (𝔽₂ n) ↑((Finset.univ : Finset (𝔽₂ n)) + (Finset.univ : Finset (𝔽₂ n))),
      Finset.univ, ?_, rfl⟩
    simp [hα1]
  have hinf : n - c ≤ guaranteedMaxCosetDim n α := by
    unfold guaranteedMaxCosetDim
    apply le_csInf hS_ne
    rintro _ ⟨A, hA, rfl⟩
    exact hbound A hA
  omega

end Green51

theorem OMA.solution : type_of% @Green51.green_51.one_half :=
  Green51.proved_one_half

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
