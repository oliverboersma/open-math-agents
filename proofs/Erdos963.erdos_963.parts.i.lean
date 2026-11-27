import FormalConjectures.ErdosProblems.«963»

-- Problem: Erdős Problem 963, part i (it asks for a value). Answer: n ↦ log₂ n, that is f(n) ~ log₂ n.
-- Credit: @marcusbuffett (solver of record on Left to Solve).
--
-- PORT OF A PUBLIC PROOF, not a new result. Source: github.com/jmanuellb/erdos-963-lean,
-- commit dc3acbaf7e75fdb442f86444a7d29950c0ed45a0, modules E963.Kernel, Step, StepThm, Iterate,
-- Upper and Main. Lean formalization by Manuel Lopez (formalization.yaml lists him as author).
-- Mathematical argument from the erdosproblems.com forum thread for problem 963 (post by
-- KoishiChan, 5 December 2025, with comments by Quanyu Tang, Terence Tao and Thomas Bloom).
-- Copyright Manuel Lopez. Licensed under the Apache License, Version 2.0; you may not use this
-- file except in compliance with the License. You may obtain a copy of the License at
-- https://www.apache.org/licenses/LICENSE-2.0 . Distributed on an AS IS BASIS, WITHOUT
-- WARRANTIES OR CONDITIONS OF ANY KIND. Changes here: modules concatenated into one file, the
-- namespace renamed to OMA.E963 (its f is the source's verbatim copy of the pinned Erdos963.f),
-- module headers and documentation removed, adapted to the pinned Lean and Mathlib, result
-- stated in the OMA.answer form.

-- source module E963.Defs (the Formal Conjectures definition of f, copied by the source)
section
open Filter Asymptotics

namespace OMA.E963

noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)}

theorem le_f {n k : ℕ}
    (h : ∀ A : Finset ℝ, A.card = n → ∃ B ⊆ A, k ≤ B.card ∧ AddDissociated (B : Set ℝ)) :
    k ≤ f n := by
  refine le_csSup ⟨n, fun m hm ↦ ?_⟩ h
  obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℝ n
  obtain ⟨B, hBA, hmB, -⟩ := hm A hA
  exact hmB.trans ((Finset.card_le_card hBA).trans hA.le)

theorem f_le {n m : ℕ} (A : Finset ℝ) (hA : A.card = n)
    (h : ∀ B ⊆ A, AddDissociated (B : Set ℝ) → B.card ≤ m) : f n ≤ m := by
  refine csSup_le ⟨0, fun A' _ ↦ ⟨∅, Finset.empty_subset _, Nat.zero_le _, by simp⟩⟩ ?_
  intro k hk
  obtain ⟨B, hBA, hkB, hB⟩ := hk A hA
  exact hkB.trans (h B hBA hB)

end OMA.E963

end

-- source module E963.Kernel
section
open Finset

namespace OMA.E963

variable {q : ℕ} [NeZero q]


lemma norm_chi (x : ZMod q) : ‖(ZMod.stdAddChar (N := q)) x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

/-- Lower bound for the chord `‖(ZMod.stdAddChar (N := q)) x - 1‖`. -/
lemma chi_sub_one_lower (x : ZMod q) :
    4 * |(x.valMinAbs : ℝ)| / q ≤ ‖(ZMod.stdAddChar (N := q)) x - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  set v : ℤ := x.valMinAbs with hv
  have hx : (ZMod.stdAddChar (N := q)) x = Complex.exp (Complex.I * ((2 * Real.pi * v / q : ℝ) : ℂ)) := by
    conv_lhs => rw [← ZMod.coe_valMinAbs x]
    rw [ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hx, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hmem := ZMod.valMinAbs_mem_Ioc x
  have h1 : -(q : ℝ) < (v : ℝ) * 2 := by exact_mod_cast hmem.1
  have h2 : (v : ℝ) * 2 ≤ q := by exact_mod_cast hmem.2
  set y : ℝ := 2 * Real.pi * v / q / 2 with hy
  have hy' : y = Real.pi * v / q := by rw [hy]; ring
  have hpi := Real.pi_pos
  have habs : |y| ≤ Real.pi / 2 := by
    rw [hy', abs_le]
    constructor
    · rw [le_div_iff₀ hq]; nlinarith
    · rw [div_le_iff₀ hq]; nlinarith
  have hsin : 2 / Real.pi * |y| ≤ |Real.sin y| := by
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h] at habs ⊢
      exact (Real.mul_le_sin h habs).trans (le_abs_self _)
    · rw [abs_of_nonpos h] at habs ⊢
      have := Real.mul_le_sin (neg_nonneg.2 h) habs
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have hyabs : |y| = Real.pi * |(v : ℝ)| / q := by
    rw [hy', abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hq]
  rw [Real.norm_eq_abs, abs_mul, abs_two]
  calc 4 * |(v : ℝ)| / q = 2 * (2 / Real.pi * |y|) := by
        rw [hyabs]; field_simp; ring
    _ ≤ 2 * |Real.sin y| := by linarith

/-- The Dirichlet-type sum `∑_{j ≤ M} (ZMod.stdAddChar (N := q))(j x)`. -/
noncomputable def dir (M : ℕ) (x : ZMod q) : ℂ :=
  ∑ j ∈ range (M + 1), (ZMod.stdAddChar (N := q)) ((j : ZMod q) * x)

/-- The (unnormalised) Fejér kernel. -/
noncomputable def ker (M : ℕ) (x : ZMod q) : ℝ := ‖dir M x‖ ^ 2

lemma ker_nonneg (M : ℕ) (x : ZMod q) : 0 ≤ ker M x := sq_nonneg _

lemma dir_eq_geom (M : ℕ) (x : ZMod q) : dir M x = ∑ j ∈ range (M + 1), (ZMod.stdAddChar (N := q)) x ^ j := by
  unfold dir
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

lemma ker_le (M : ℕ) {x : ZMod q} (hx : x ≠ 0) :
    ker M x ≤ (q : ℝ) ^ 2 / (4 * (x.valMinAbs : ℝ) ^ 2) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hv : (x.valMinAbs : ℝ) ≠ 0 := by
    exact_mod_cast (not_iff_not.2 (ZMod.valMinAbs_eq_zero x)).2 hx
  have hvpos : 0 < |(x.valMinAbs : ℝ)| := abs_pos.2 hv
  have hlow := chi_sub_one_lower x
  have hpos : 0 < 4 * |(x.valMinAbs : ℝ)| / q := by positivity
  have hne : 0 < ‖(ZMod.stdAddChar (N := q)) x - 1‖ := lt_of_lt_of_le hpos hlow
  have hgeom : dir M x * ((ZMod.stdAddChar (N := q)) x - 1) = (ZMod.stdAddChar (N := q)) x ^ (M + 1) - 1 := by
    rw [dir_eq_geom, geom_sum_mul]
  have hnorm : ‖dir M x‖ * ‖(ZMod.stdAddChar (N := q)) x - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc ‖(ZMod.stdAddChar (N := q)) x ^ (M + 1) - 1‖ ≤ ‖(ZMod.stdAddChar (N := q)) x ^ (M + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_chi, one_pow, norm_one]; norm_num
  have hd : ‖dir M x‖ ≤ q / (2 * |(x.valMinAbs : ℝ)|) := by
    rw [le_div_iff₀ (by positivity)]
    have h3 : ‖dir M x‖ * (4 * |(x.valMinAbs : ℝ)| / q) ≤ 2 :=
      (mul_le_mul_of_nonneg_left hlow (norm_nonneg _)).trans hnorm
    have h4 : ‖dir M x‖ * (4 * |(x.valMinAbs : ℝ)| / q) * q
        = ‖dir M x‖ * (2 * |(x.valMinAbs : ℝ)|) * 2 := by
      field_simp; ring
    nlinarith
  unfold ker
  calc ‖dir M x‖ ^ 2 ≤ (q / (2 * |(x.valMinAbs : ℝ)|)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd 2
    _ = (q : ℝ) ^ 2 / (4 * (x.valMinAbs : ℝ) ^ 2) := by
        rw [div_pow, mul_pow, sq_abs]; norm_num

lemma ker_cast (M : ℕ) (y : ZMod q) :
    ((ker M y : ℝ) : ℂ) =
      ∑ p ∈ range (M + 1) ×ˢ range (M + 1), (ZMod.stdAddChar (N := q)) (((p.1 : ZMod q) - (p.2 : ZMod q)) * y) := by
  unfold ker
  push_cast
  rw [← Complex.mul_conj', dir, map_sum, sum_mul_sum, ← sum_product']
  refine sum_congr rfl fun p _ ↦ ?_
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1; ring

variable (A : Finset (ZMod q))

/-- The exponential sum over `A`. -/
noncomputable def expSum (η : ZMod q) : ℂ := ∑ a ∈ A, (ZMod.stdAddChar (N := q)) (η * a)

/-- Weighted count of the `a ∈ A` with `r * a` close to `c`. -/
noncomputable def cnt (M : ℕ) (c r : ZMod q) : ℝ := ∑ a ∈ A, ker M (r * a - c)

lemma parseval : ∑ η : ZMod q, ‖expSum A η‖ ^ 2 = (q : ℝ) * A.card := by
  classical
  have h : ∀ η : ZMod q, ((‖expSum A η‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ A, ∑ b ∈ A, (ZMod.stdAddChar (N := q)) (η * (a - b)) := by
    intro η
    push_cast
    rw [← Complex.mul_conj', expSum, map_sum, sum_mul_sum]
    refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1; ring
  have h2 : ((∑ η : ZMod q, ‖expSum A η‖ ^ 2 : ℝ) : ℂ) = ((q : ℝ) * A.card : ℝ) := by
    rw [Complex.ofReal_sum]
    simp_rw [h]
    rw [sum_comm]
    simp_rw [sum_comm (s := (univ : Finset (ZMod q)))]
    simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q), sub_eq_zero]
    simp [ZMod.card, mul_comm]
  exact_mod_cast h2

lemma cnt_sub (M : ℕ) (c r : ZMod q) :
    ((cnt A M c r : ℝ) : ℂ) - (A.card : ℂ) * (M + 1) =
      ∑ p ∈ (range (M + 1)).offDiag,
        (ZMod.stdAddChar (N := q)) (-(((p.1 : ZMod q) - (p.2 : ZMod q)) * c)) *
          expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r) := by
  classical
  unfold cnt
  rw [Complex.ofReal_sum]
  simp_rw [ker_cast]
  rw [sum_comm, ← diag_union_offDiag, sum_union (disjoint_diag_offDiag _), sum_diag]
  have h1 : ∑ i ∈ range (M + 1), ∑ a ∈ A, (ZMod.stdAddChar (N := q)) (((i : ZMod q) - (i : ZMod q)) * (r * a - c))
      = (A.card : ℂ) * (M + 1) := by
    simp [mul_comm]
  rw [h1, add_sub_cancel_left]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [expSum, mul_sum]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1; ring

lemma second_moment (M : ℕ) (hM : M + 1 ≤ q) [Fact q.Prime] (c : ZMod q) :
    ∑ r : ZMod q, (cnt A M c r - A.card * (M + 1)) ^ 2 ≤
      ((M : ℝ) + 1) ^ 4 * q * A.card := by
  classical
  set P := (range (M + 1)).offDiag with hP
  have hPcard : (P.card : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := by
    have : P.card ≤ (M + 1) * (M + 1) := by
      rw [hP, offDiag_card, card_range]; exact Nat.sub_le _ _
    calc (P.card : ℝ) ≤ ((M + 1) * (M + 1) : ℕ) := by exact_mod_cast this
      _ = ((M : ℝ) + 1) ^ 2 := by push_cast; ring
  have hpt : ∀ r : ZMod q, (cnt A M c r - A.card * (M + 1)) ^ 2 ≤
      P.card * ∑ p ∈ P, ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ ^ 2 := by
    intro r
    have h1 : |cnt A M c r - A.card * (M + 1)| ≤
        ∑ p ∈ P, ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ := by
      have : ((cnt A M c r - A.card * (M + 1) : ℝ) : ℂ) =
          ((cnt A M c r : ℝ) : ℂ) - (A.card : ℂ) * (M + 1) := by push_cast; ring
      rw [← Real.norm_eq_abs, ← Complex.norm_real, this, cnt_sub]
      refine (norm_sum_le _ _).trans (sum_le_sum fun p _ ↦ ?_)
      rw [norm_mul, norm_chi, one_mul]
    calc (cnt A M c r - A.card * (M + 1)) ^ 2
        = |cnt A M c r - A.card * (M + 1)| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ p ∈ P, ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ _ := sq_sum_le_card_mul_sum_sq
  have hshift : ∀ p ∈ P, ∑ r : ZMod q,
      ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ ^ 2 = (q : ℝ) * A.card := by
    intro p hp
    rw [hP, mem_offDiag] at hp
    have hd : ((p.1 : ZMod q) - (p.2 : ZMod q)) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      rw [ZMod.natCast_eq_natCast_iff'] at h
      have h1 := mem_range.1 hp.1
      have h2 := mem_range.1 hp.2.1
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
      exact hp.2.2 h
    rw [← parseval A]
    exact Fintype.sum_equiv (Equiv.mulLeft₀ _ hd) _ _ fun r ↦ rfl
  calc ∑ r : ZMod q, (cnt A M c r - A.card * (M + 1)) ^ 2
      ≤ ∑ r : ZMod q, P.card *
          ∑ p ∈ P, ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ ^ 2 :=
        sum_le_sum fun r _ ↦ hpt r
    _ = P.card * ∑ p ∈ P, ∑ r : ZMod q,
          ‖expSum A (((p.1 : ZMod q) - (p.2 : ZMod q)) * r)‖ ^ 2 := by
        rw [← mul_sum, sum_comm]
    _ = P.card * (P.card * ((q : ℝ) * A.card)) := by
        rw [sum_congr rfl hshift, sum_const, nsmul_eq_mul]
    _ ≤ ((M : ℝ) + 1) ^ 2 * (((M : ℝ) + 1) ^ 2 * ((q : ℝ) * A.card)) := by
        gcongr
    _ = ((M : ℝ) + 1) ^ 4 * q * A.card := by ring

end OMA.E963

end

-- source module E963.Step
section
open Finset

namespace OMA.E963

lemma bad_card {q : ℕ} [NeZero q] [Fact q.Prime] (A : Finset (ZMod q)) (M : ℕ) (hM : M + 1 ≤ q)
    (c : ZMod q) :
    (((univ : Finset (ZMod q)).filter
        fun r ↦ cnt A M c r ≤ A.card * ((M : ℝ) + 1) / 2).card : ℝ) * A.card
      ≤ 4 * ((M : ℝ) + 1) ^ 2 * q := by
  classical
  set Bad := (univ : Finset (ZMod q)).filter
    fun r ↦ cnt A M c r ≤ A.card * ((M : ℝ) + 1) / 2 with hBad
  rcases Nat.eq_zero_or_pos A.card with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, mul_zero]; positivity
  have hn : (0 : ℝ) < A.card := by exact_mod_cast hpos
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have h1 : ∑ _r ∈ Bad, (A.card * ((M : ℝ) + 1) / 2) ^ 2 ≤
      ∑ r ∈ Bad, (cnt A M c r - A.card * (M + 1)) ^ 2 := by
    refine sum_le_sum fun r hr ↦ ?_
    have hr' : cnt A M c r ≤ A.card * ((M : ℝ) + 1) / 2 := (mem_filter.1 hr).2
    have h0 : 0 ≤ A.card * ((M : ℝ) + 1) / 2 := by positivity
    nlinarith [mul_nonneg (sub_nonneg.2 hr')
      (sub_nonneg.2 (hr'.trans (le_mul_of_one_le_left h0 (by norm_num : (1 : ℝ) ≤ 3))))]
  have h2 : ∑ r ∈ Bad, (cnt A M c r - A.card * (M + 1)) ^ 2 ≤
      ∑ r : ZMod q, (cnt A M c r - A.card * (M + 1)) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
  have h3 := second_moment A M hM c
  rw [sum_const, nsmul_eq_mul] at h1
  have h4 : (Bad.card : ℝ) * (A.card * ((M : ℝ) + 1) / 2) ^ 2 ≤
      ((M : ℝ) + 1) ^ 4 * q * A.card := h1.trans (h2.trans h3)
  have h5 : ((Bad.card : ℝ) * A.card) * (A.card * ((M : ℝ) + 1) ^ 2 / 4) ≤
      (4 * ((M : ℝ) + 1) ^ 2 * q) * (A.card * ((M : ℝ) + 1) ^ 2 / 4) := by
    calc ((Bad.card : ℝ) * A.card) * (A.card * ((M : ℝ) + 1) ^ 2 / 4)
        = (Bad.card : ℝ) * (A.card * ((M : ℝ) + 1) / 2) ^ 2 := by ring
      _ ≤ ((M : ℝ) + 1) ^ 4 * q * A.card := h4
      _ = (4 * ((M : ℝ) + 1) ^ 2 * q) * (A.card * ((M : ℝ) + 1) ^ 2 / 4) := by ring
  exact le_of_mul_le_mul_right h5 (by positivity)

lemma hit_of_cnt {q : ℕ} [NeZero q] (A : Finset (ZMod q)) (M : ℕ) (c r : ZMod q)
    (h : A.card * ((M : ℝ) + 1) / 2 < cnt A M c r) :
    ∃ a ∈ A, ∃ v : ℤ, (v : ZMod q) = r * a - c ∧ 2 * ((M : ℤ) + 1) * v ^ 2 < (q : ℤ) ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have : cnt A M c r ≤ A.card * ((M : ℝ) + 1) / 2 := by
    unfold cnt
    calc ∑ a ∈ A, ker M (r * a - c) ≤ ∑ _a ∈ A, ((M : ℝ) + 1) / 2 := by
          refine sum_le_sum fun a ha ↦ ?_
          have hv := hcon a ha (r * a - c).valMinAbs (ZMod.coe_valMinAbs _)
          have hvR : (q : ℝ) ^ 2 ≤ 2 * ((M : ℝ) + 1) * ((r * a - c).valMinAbs : ℝ) ^ 2 := by
            exact_mod_cast hv
          have hv0 : ((r * a - c).valMinAbs : ℝ) ≠ 0 := by
            intro h0; rw [h0] at hvR; nlinarith
          have hx : r * a - c ≠ 0 := by
            intro h0; apply hv0; rw [h0, ZMod.valMinAbs_zero]; simp
          refine (ker_le M hx).trans ?_
          have hv2 : 0 < ((r * a - c).valMinAbs : ℝ) ^ 2 := by positivity
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
      _ = A.card * ((M : ℝ) + 1) / 2 := by rw [sum_const, nsmul_eq_mul]; ring
  linarith

lemma dirichlet {q : ℕ} [NeZero q] (w J : ℕ) (hJ : q ≤ w * J) (x : ZMod q) :
    ∃ s ∈ Icc 1 J, ∃ v : ℤ, (v : ZMod q) = (s : ZMod q) * x ∧ |v| < w := by
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; simp only [zero_mul, nonpos_iff_eq_zero] at hJ; exact absurd hJ (NeZero.ne q)
    · exact h
  have hmaps : ∀ t ∈ range (J + 1), (((t : ZMod q) * x).val / w) ∈ range J := by
    intro t _
    rw [mem_range]
    have := ZMod.val_lt ((t : ZMod q) * x)
    exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le this hJ)
  obtain ⟨t, ht, t', ht', hne, heq⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to (by simp) hmaps
  wlog hlt : t < t' generalizing t t'
  · exact this t' ht' t ht hne.symm heq.symm (lt_of_le_of_ne (not_lt.1 hlt) hne.symm)
  refine ⟨t' - t, ?_, (((t' : ZMod q) * x).val : ℤ) - (((t : ZMod q) * x).val : ℤ), ?_, ?_⟩
  · rw [mem_Icc]; rw [mem_range] at ht ht'; omega
  · push_cast [Nat.cast_sub hlt.le]
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
  · have h1 := Nat.div_add_mod ((t' : ZMod q) * x).val w
    have h2 := Nat.div_add_mod ((t : ZMod q) * x).val w
    have h3 := Nat.mod_lt ((t' : ZMod q) * x).val hw
    have h4 := Nat.mod_lt ((t : ZMod q) * x).val hw
    rw [heq] at h2
    generalize w * (((t' : ZMod q) * x).val / w) = z at h1 h2
    rw [abs_lt]
    constructor <;> omega

/-- The lifting lemma: elements sent near `2 ^ j * g` together with a dissociated set of
elements sent near `0` form a dissociated set. -/
lemma lift {q : ℕ} [NeZero q] (r : ZMod q) (g ρ m K : ℕ) (h1 : (m + K) * ρ < g)
    (h2 : g * 2 ^ (m + 1) ≤ q) (a : ℕ → ℤ) (D : Finset ℤ)
    (hD : AddDissociated (D : Set ℤ)) (hK : D.card ≤ K)
    (hDν : ∀ d ∈ D, |(r * (d : ZMod q)).valMinAbs| ≤ ρ)
    (hEν : ∀ j < m, |(r * (a j : ZMod q)).valMinAbs - 2 ^ j * g| ≤ ρ) :
    Set.InjOn a (range m) ∧ (∀ j < m, a j ∉ D) ∧
      AddDissociated ((D ∪ (range m).image a : Finset ℤ) : Set ℤ) := by
  classical
  set ν : ℤ → ℤ := fun x ↦ (r * (x : ZMod q)).valMinAbs with hν
  have hg0 : (0 : ℤ) ≤ g := Int.natCast_nonneg g
  have hρ0 : (0 : ℤ) ≤ ρ := Int.natCast_nonneg ρ
  have h1' : ((m : ℤ) + K) * ρ < g := by exact_mod_cast h1
  -- injectivity
  have hinj : Set.InjOn a (range m) := by
    have key : ∀ j j', j < m → j' < m → j < j' → a j ≠ a j' := by
      intro j j' hj hj' hlt heq
      have e1 := hEν j hj
      have e2 := hEν j' hj'
      rw [← heq] at e2
      rw [abs_le] at e1 e2
      have hp : (2 : ℤ) * 2 ^ j ≤ 2 ^ j' := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hlt
      have hp1 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hm2 : (2 : ℤ) ≤ (m : ℤ) + K := by
        have : 2 ≤ m := by omega
        have h3 : (2 : ℤ) ≤ m := by exact_mod_cast this
        have h4 : (0 : ℤ) ≤ K := Int.natCast_nonneg K
        linarith
      have h5 : (2 : ℤ) * ρ ≤ ((m : ℤ) + K) * ρ := mul_le_mul_of_nonneg_right hm2 hρ0
      have h6 : (2 : ℤ) * 2 ^ j * g ≤ 2 ^ j' * g := mul_le_mul_of_nonneg_right hp hg0
      have h7 : (1 : ℤ) * g ≤ 2 ^ j * g := mul_le_mul_of_nonneg_right hp1 hg0
      linarith
    intro j hj j' hj' heq
    rw [coe_range, Set.mem_Iio] at hj hj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key j j' hj hj' h heq
    · exact key j' j hj' hj h heq.symm
  -- the `a j` are not in `D`
  have hnot : ∀ j < m, a j ∉ D := by
    intro j hj hmem
    have e1 := hEν j hj
    have e2 := hDν _ hmem
    rw [abs_le] at e1 e2
    have hp1 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hK1 : 1 ≤ K := (Finset.card_pos.2 ⟨_, hmem⟩).trans_le hK
    have hm2 : (2 : ℤ) ≤ (m : ℤ) + K := by
      have h3 : (1 : ℤ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
      have h4 : (1 : ℤ) ≤ K := by exact_mod_cast hK1
      linarith
    have h5 : (2 : ℤ) * ρ ≤ ((m : ℤ) + K) * ρ := mul_le_mul_of_nonneg_right hm2 hρ0
    have h7 : (1 : ℤ) * g ≤ 2 ^ j * g := mul_le_mul_of_nonneg_right hp1 hg0
    linarith
  refine ⟨hinj, hnot, ?_⟩
  set E := (range m).image a with hE
  by_contra hcon
  rw [not_addDissociated_iff_exists_disjoint] at hcon
  obtain ⟨t, u, ht, hu, hdisj, hne, hsum⟩ := hcon
  rw [coe_subset] at ht hu
  set β : ℤ → ℕ := fun x ↦ ∑ j ∈ (range m).filter (fun j ↦ a j = x), 2 ^ j with hβ
  have hβsum : ∀ s : Finset ℤ, ∑ x ∈ s, β x = ∑ j ∈ (range m).filter (fun j ↦ a j ∈ s), 2 ^ j :=
    fun s ↦ sum_fiberwise_eq_sum_filter (range m) s a fun j ↦ 2 ^ j
  have hβlt : ∀ s : Finset ℤ, ∑ x ∈ s, β x < 2 ^ m := by
    intro s
    rw [hβsum]
    exact Nat.geomSum_lt le_rfl fun k hk ↦ mem_range.1 (mem_filter.1 hk).1
  -- decomposition of ν
  have hdec : ∀ x ∈ D ∪ E, |ν x - g * (β x : ℤ)| ≤ ρ := by
    intro x hx
    by_cases hxD : x ∈ D
    · have : β x = 0 := by
        rw [hβ]
        apply sum_eq_zero
        intro j hj
        rw [mem_filter, mem_range] at hj
        exact absurd (hj.2 ▸ hxD) (hnot j hj.1)
      rw [this]; simpa using hDν x hxD
    · have hxE : x ∈ E := (mem_union.1 hx).resolve_left hxD
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hxE
      have hj' := mem_range.1 hj
      have : (range m).filter (fun j' ↦ a j' = a j) = {j} := by
        ext j'
        rw [mem_filter, mem_singleton]
        constructor
        · rintro ⟨h1, h2⟩; exact hinj h1 hj h2
        · rintro rfl; exact ⟨hj, rfl⟩
      have hb : β (a j) = 2 ^ j := by rw [hβ]; simp only; rw [this, sum_singleton]
      rw [hb]
      have := hEν j hj'
      push_cast
      rwa [mul_comm]
  -- congruence
  have hcong : (q : ℤ) ∣ ∑ x ∈ t, ν x - ∑ x ∈ u, ν x := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp only [hν, ZMod.coe_valMinAbs]
    rw [← mul_sum, ← mul_sum, ← Int.cast_sum, ← Int.cast_sum, hsum, sub_self]
  -- error terms
  set e : ℤ → ℤ := fun x ↦ ν x - g * (β x : ℤ) with he
  have hsplit : ∀ s : Finset ℤ, ∑ x ∈ s, ν x = g * ((∑ x ∈ s, β x : ℕ) : ℤ) + ∑ x ∈ s, e x := by
    intro s
    rw [he, sum_sub_distrib, Nat.cast_sum, mul_sum]; ring
  have herr : ∀ s : Finset ℤ, s ⊆ D ∪ E → |∑ x ∈ s, e x| ≤ s.card * ρ := by
    intro s hs
    calc |∑ x ∈ s, e x| ≤ ∑ x ∈ s, |e x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ s, (ρ : ℤ) := sum_le_sum fun x hx ↦ hdec x (hs hx)
      _ = s.card * ρ := by rw [sum_const, nsmul_eq_mul]
  have hcard : ((t.card : ℤ) + u.card) * ρ ≤ ((m : ℤ) + K) * ρ := by
    refine mul_le_mul_of_nonneg_right ?_ hρ0
    have h3 : t.card + u.card ≤ m + K := by
      rw [← card_union_of_disjoint hdisj]
      calc (t ∪ u).card ≤ (D ∪ E).card := card_le_card (union_subset ht hu)
        _ ≤ D.card + E.card := card_union_le _ _
        _ ≤ K + m := add_le_add hK (card_image_le.trans (card_range m).le)
        _ = m + K := add_comm _ _
    exact_mod_cast h3
  set Z : ℤ := ((∑ x ∈ t, β x : ℕ) : ℤ) - ((∑ x ∈ u, β x : ℕ) : ℤ) with hZ
  set W : ℤ := ∑ x ∈ t, e x - ∑ x ∈ u, e x with hW
  have hW' : |W| < g := by
    have h3 := herr t ht
    have h4 := herr u hu
    have : |W| ≤ |∑ x ∈ t, e x| + |∑ x ∈ u, e x| := abs_sub _ _
    have h5 : (t.card : ℤ) * ρ + u.card * ρ = ((t.card : ℤ) + u.card) * ρ := by ring
    linarith
  have hZW : ∑ x ∈ t, ν x - ∑ x ∈ u, ν x = g * Z + W := by
    rw [hsplit t, hsplit u, hZ, hW]; ring
  have hZabs : |Z| ≤ 2 ^ m - 1 := by
    have h3 : ((∑ x ∈ t, β x : ℕ) : ℤ) < 2 ^ m := by exact_mod_cast hβlt t
    have h4 : ((∑ x ∈ u, β x : ℕ) : ℤ) < 2 ^ m := by exact_mod_cast hβlt u
    have h5 : (0 : ℤ) ≤ ((∑ x ∈ t, β x : ℕ) : ℤ) := Int.natCast_nonneg _
    have h6 : (0 : ℤ) ≤ ((∑ x ∈ u, β x : ℕ) : ℤ) := Int.natCast_nonneg _
    rw [hZ, abs_le]; constructor <;> linarith
  have hzero : (g : ℤ) * Z + W = 0 := by
    rw [← hZW]
    refine Int.eq_zero_of_abs_lt_dvd hcong ?_
    rw [hZW]
    have h3 : |(g : ℤ) * Z| ≤ g * (2 ^ m - 1) := by
      rw [abs_mul, abs_of_nonneg hg0]; exact mul_le_mul_of_nonneg_left hZabs hg0
    have h4 : ((g * 2 ^ (m + 1) : ℕ) : ℤ) ≤ q := by exact_mod_cast h2
    have h5 : (g : ℤ) * 2 ^ m ≤ ((g * 2 ^ (m + 1) : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ]
      have : (0 : ℤ) ≤ (g : ℤ) * 2 ^ m := by positivity
      linarith
    have := abs_add_le ((g : ℤ) * Z) W
    linarith
  have hZ0 : Z = 0 := by
    by_contra hZne
    have h3 : (1 : ℤ) ≤ |Z| := Int.one_le_abs hZne
    have h4 : (g : ℤ) * 1 ≤ g * |Z| := mul_le_mul_of_nonneg_left h3 hg0
    have h5 : |(g : ℤ) * Z| = |W| := by
      have : (g : ℤ) * Z = -W := by linarith
      rw [this, abs_neg]
    rw [abs_mul, abs_of_nonneg hg0] at h5
    linarith
  have hβeq : ∑ x ∈ t, β x = ∑ x ∈ u, β x := by
    have : ((∑ x ∈ t, β x : ℕ) : ℤ) = ((∑ x ∈ u, β x : ℕ) : ℤ) := by
      rw [hZ] at hZ0; linarith
    exact_mod_cast this
  rw [hβsum t, hβsum u] at hβeq
  have hfil := Finset.geomSum_injective le_rfl hβeq
  have hnone : ∀ j < m, a j ∉ t ∧ a j ∉ u := by
    intro j hj
    have hiff : a j ∈ t ↔ a j ∈ u := by
      have := Finset.ext_iff.1 hfil j
      simpa [mem_filter, mem_range, hj] using this
    constructor
    · intro h; exact (disjoint_left.1 hdisj h) (hiff.1 h)
    · intro h; exact (disjoint_left.1 hdisj (hiff.2 h)) h
  have htD : t ⊆ D := by
    intro x hx
    rcases mem_union.1 (ht hx) with h | h
    · exact h
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 h
      exact absurd hx (hnone j (mem_range.1 hj)).1
  have huD : u ⊆ D := by
    intro x hx
    rcases mem_union.1 (hu hx) with h | h
    · exact h
    · obtain ⟨j, hj, rfl⟩ := mem_image.1 h
      exact absurd hx (hnone j (mem_range.1 hj)).2
  exact hne (hD (coe_subset.2 htD) (coe_subset.2 huD) hsum)

end OMA.E963

end

-- source module E963.StepThm
section
open Finset

namespace OMA.E963

/-- **Step theorem.** If `A` is a large finite set of integers then there are a subset `A₁` of
density at least `1 / (2 ^ (m + 4) * (m + K))` and `m` elements `E` of `A` which can be added
to every dissociated subset of `A₁` with at most `K` elements. -/
theorem step (A : Finset ℤ) (m K : ℕ) (hm : 1 ≤ m)
    (hn : 4 * m * (2 ^ (m + 4) * (m + K)) ^ 5 < A.card) :
    ∃ A₁ ⊆ A, A.card / (2 ^ (m + 4) * (m + K)) ≤ A₁.card ∧ ∃ E ⊆ A, E.card = m ∧
      ∀ D ⊆ A₁, AddDissociated (D : Set ℤ) → D.card ≤ K →
        Disjoint D E ∧ AddDissociated ((D ∪ E : Finset ℤ) : Set ℤ) := by
  classical
  set B := 2 ^ (m + 3) * (m + K) with hB
  set J := 2 ^ (m + 4) * (m + K) with hJ
  have hJB : J = 2 * B := by rw [hJ, hB]; ring
  have hmK : 0 < m + K := by omega
  have hBpos : 0 < B := by positivity
  have hJpos : 0 < J := by positivity
  have hB2 : 2 ≤ B := by
    have : 2 ^ 1 ≤ 2 ^ (m + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 = 2 ^ 1 * 1 := by norm_num
      _ ≤ 2 ^ (m + 3) * (m + K) := Nat.mul_le_mul this hmK
  have hB3 : 2 ^ (m + 3) ≤ B := Nat.le_mul_of_pos_right _ hmK
  set S := A.sup Int.natAbs with hS
  obtain ⟨J2, hJ2⟩ : ∃ J2, J2 = J ^ 2 := ⟨_, rfl⟩
  have hJ2pos : 0 < J2 := by rw [hJ2]; positivity
  obtain ⟨q, hqge, hqp⟩ :=
    Nat.exists_infinite_primes (J2 + B + 2 * S + 1)
  have : Fact q.Prime := ⟨hqp⟩
  have : NeZero q := ⟨hqp.ne_zero⟩
  set ρ := q / B with hρ
  set g := q / 2 ^ (m + 1) with hg
  obtain ⟨M, hM1'⟩ : ∃ M, M + 1 = J2 := ⟨J2 - 1, Nat.sub_add_cancel hJ2pos⟩
  have hM1 : M + 1 = J ^ 2 := hM1'.trans hJ2
  have hMq : M + 1 ≤ q := by omega
  have hJq : J < q := by
    have : J ≤ J2 := hJ2 ▸ Nat.le_self_pow (by norm_num) J
    omega
  -- arithmetic of the parameters
  have hg2 : g * 2 ^ (m + 1) ≤ q := Nat.div_mul_le_self _ _
  have hρB : ρ * B ≤ q := Nat.div_mul_le_self _ _
  have hρ1 : 1 ≤ ρ := Nat.div_pos (by omega) hBpos
  have h1 : (m + K) * ρ < g := by
    by_contra hcon
    push Not at hcon
    set P := 2 ^ (m + 1) with hP
    have hPpos : 0 < P := by positivity
    have h4P : 2 ^ (m + 3) = 4 * P := by rw [hP]; ring
    have hX : 4 * ((m + K) * ρ * P) ≤ q := by
      calc 4 * ((m + K) * ρ * P) = ρ * B := by rw [hB, h4P]; ring
        _ ≤ q := hρB
    have hlt : q < P * (g + 1) := Nat.lt_mul_div_succ q hPpos
    have hle : P * (g + 1) ≤ (m + K) * ρ * P + P := by
      calc P * (g + 1) ≤ P * ((m + K) * ρ + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (m + K) * ρ * P + P := by ring
    have hq4 : 4 * P ≤ q := by
      have : 4 * P ≤ B := h4P ▸ hB3
      omega
    generalize (m + K) * ρ * P = X at hX hle
    generalize P * (g + 1) = Y at hlt hle
    omega
  have hρg : ρ < g := by
    calc ρ = 1 * ρ := (one_mul _).symm
      _ ≤ (m + K) * ρ := Nat.mul_le_mul_right _ hmK
      _ < g := h1
  have hwJ : q ≤ ρ * J := by
    have h3 : q < B * (ρ + 1) := Nat.lt_mul_div_succ q hBpos
    have h4 : ρ * J = 2 * (B * ρ) := by rw [hJB]; ring
    have h5 : B * (ρ + 1) = B * ρ + B := by ring
    have h6 : B ≤ B * ρ := Nat.le_mul_of_pos_right _ hρ1
    omega
  have h2ρq : 2 * ρ ≤ q := by
    calc 2 * ρ = ρ * 2 := mul_comm _ _
      _ ≤ ρ * B := Nat.mul_le_mul_left _ hB2
      _ ≤ q := hρB
  -- the cast is injective on `A`
  have hinjA : Set.InjOn (Int.cast : ℤ → ZMod q) A := by
    intro x hx y hy hxy
    have hx' : x.natAbs ≤ S := Finset.le_sup (f := Int.natAbs) hx
    have hy' : y.natAbs ≤ S := Finset.le_sup (f := Int.natAbs) hy
    have hdvd : (q : ℤ) ∣ y - x := (ZMod.intCast_eq_intCast_iff_dvd_sub x y q).1 hxy
    have habs : |y - x| < q := by
      have h3 : |y - x| ≤ |y| + |x| := abs_sub _ _
      have h4 : |x| = (x.natAbs : ℤ) := Int.abs_eq_natAbs x
      have h5 : |y| = (y.natAbs : ℤ) := Int.abs_eq_natAbs y
      have h6 : ((x.natAbs : ℕ) : ℤ) ≤ S := by exact_mod_cast hx'
      have h7 : ((y.natAbs : ℕ) : ℤ) ≤ S := by exact_mod_cast hy'
      have h8 : ((2 * S + 1 : ℕ) : ℤ) ≤ q := by exact_mod_cast (by omega : 2 * S + 1 ≤ q)
      push_cast at h8
      linarith
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    linarith
  set A' : Finset (ZMod q) := A.image (Int.cast : ℤ → ZMod q) with hA'
  have hA'card : A'.card = A.card := card_image_of_injOn hinjA
  set c : ℕ → ZMod q := fun j ↦ ((2 ^ j * g : ℕ) : ZMod q) with hc
  set Bad : ℕ → Finset (ZMod q) := fun j ↦ (univ : Finset (ZMod q)).filter
    fun r ↦ cnt A' M (c j) r ≤ A'.card * ((M : ℝ) + 1) / 2 with hBad
  have hbad : ∀ j, ((Bad j).card : ℝ) * A.card ≤ 4 * (J : ℝ) ^ 4 * q := by
    intro j
    have h := bad_card A' M hMq (c j)
    have hMJ : (M : ℝ) + 1 = (J : ℝ) ^ 2 := by exact_mod_cast hM1
    calc ((Bad j).card : ℝ) * A.card = ((Bad j).card : ℝ) * A'.card := by rw [hA'card]
      _ ≤ 4 * ((M : ℝ) + 1) ^ 2 * q := h
      _ = 4 * (J : ℝ) ^ 4 * q := by rw [hMJ]; ring
  have hsne : ∀ s ∈ Icc 1 J, (s : ZMod q) ≠ 0 := by
    intro s hs h0
    rw [mem_Icc] at hs
    rw [ZMod.natCast_eq_zero_iff] at h0
    have := Nat.le_of_dvd (by omega) h0
    omega
  set U : Finset (ZMod q) := (Icc 1 J ×ˢ range m).biUnion
    fun p ↦ (univ : Finset (ZMod q)).filter fun r ↦ (p.1 : ZMod q) * r ∈ Bad p.2 with hU
  have hpiece : ∀ p ∈ Icc 1 J ×ˢ range m,
      ((univ : Finset (ZMod q)).filter fun r ↦ (p.1 : ZMod q) * r ∈ Bad p.2).card ≤
        (Bad p.2).card := by
    intro p hp
    have hs := hsne p.1 (mem_product.1 hp).1
    refine card_le_card_of_injOn (fun r ↦ (p.1 : ZMod q) * r) ?_ ?_
    · intro r hr
      exact (mem_filter.1 hr).2
    · intro r _ r' _ h
      exact mul_left_cancel₀ hs h
  have hUcard : (U.card : ℝ) * A.card ≤ (J * m : ℕ) * (4 * (J : ℝ) ^ 4 * q) := by
    have h3 : U.card ≤ ∑ p ∈ Icc 1 J ×ˢ range m, (Bad p.2).card :=
      card_biUnion_le.trans (sum_le_sum hpiece)
    have h4 : (U.card : ℝ) ≤ ∑ p ∈ Icc 1 J ×ˢ range m, ((Bad p.2).card : ℝ) := by
      exact_mod_cast h3
    calc (U.card : ℝ) * A.card
        ≤ (∑ p ∈ Icc 1 J ×ˢ range m, ((Bad p.2).card : ℝ)) * A.card :=
          mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _)
      _ = ∑ p ∈ Icc 1 J ×ˢ range m, ((Bad p.2).card : ℝ) * A.card := sum_mul _ _ _
      _ ≤ ∑ _p ∈ Icc 1 J ×ˢ range m, 4 * (J : ℝ) ^ 4 * q := sum_le_sum fun p _ ↦ hbad p.2
      _ = (J * m : ℕ) * (4 * (J : ℝ) ^ 4 * q) := by
          rw [sum_const, nsmul_eq_mul, card_product, Nat.card_Icc, card_range]
          simp
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hUq : U.card < q := by
    by_contra hcon
    push Not at hcon
    have h3 : (q : ℝ) ≤ U.card := by exact_mod_cast hcon
    have h4 : ((4 * m * J ^ 5 : ℕ) : ℝ) < A.card := by exact_mod_cast hn
    push_cast at h4 hUcard
    have h5 : (q : ℝ) * A.card ≤ U.card * A.card :=
      mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
    have h6 : (J : ℝ) * m * (4 * (J : ℝ) ^ 4 * q) = (4 * m * (J : ℝ) ^ 5) * q := by ring
    have h7 : (4 * m * (J : ℝ) ^ 5) * q < A.card * q := mul_lt_mul_of_pos_right h4 hq0
    linarith
  obtain ⟨r, hr⟩ : ∃ r : ZMod q, r ∉ U := by
    by_contra hcon
    push Not at hcon
    have : U = univ := eq_univ_iff_forall.2 hcon
    rw [this, card_univ, ZMod.card] at hUq
    exact lt_irrefl _ hUq
  -- hits
  have hits : ∀ s ∈ Icc 1 J, ∀ j, j < m → ∃ a, a ∈ A ∧
      |((s : ZMod q) * r * (a : ZMod q)).valMinAbs - 2 ^ j * g| ≤ ρ := by
    intro s hs j hj
    have hnb : (s : ZMod q) * r ∉ Bad j := by
      intro hmem
      apply hr
      rw [hU, mem_biUnion]
      exact ⟨(s, j), mem_product.2 ⟨hs, mem_range.2 hj⟩, mem_filter.2 ⟨mem_univ _, hmem⟩⟩
    have hcnt : A'.card * ((M : ℝ) + 1) / 2 < cnt A' M (c j) ((s : ZMod q) * r) := by
      by_contra hcon
      exact hnb (mem_filter.2 ⟨mem_univ _, not_lt.1 hcon⟩)
    obtain ⟨a', ha', v, hv, hv2⟩ := hit_of_cnt A' M (c j) _ hcnt
    obtain ⟨a, ha, rfl⟩ := mem_image.1 ha'
    refine ⟨a, ha, ?_⟩
    -- `|v| ≤ ρ`
    have hvρ : v.natAbs ≤ ρ := by
      rw [hρ, Nat.le_div_iff_mul_le hBpos]
      have hMJ : ((M : ℤ) + 1) = (J : ℤ) ^ 2 := by exact_mod_cast hM1
      rw [hMJ] at hv2
      have hJB' : (J : ℤ) = 2 * B := by exact_mod_cast hJB
      have h3 : ((v.natAbs : ℤ) * B) ^ 2 < (q : ℤ) ^ 2 := by
        have h4 : ((v.natAbs : ℤ) * B) ^ 2 = v ^ 2 * (B : ℤ) ^ 2 := by
          rw [mul_pow, Int.natCast_natAbs, sq_abs]
        have h5 : (0 : ℤ) ≤ v ^ 2 * (B : ℤ) ^ 2 := by positivity
        rw [h4]
        have h6 : 2 * (J : ℤ) ^ 2 * v ^ 2 = 8 * (v ^ 2 * (B : ℤ) ^ 2) := by rw [hJB']; ring
        linarith
      have h7 : (v.natAbs : ℤ) * B < q :=
        lt_of_pow_lt_pow_left₀ 2 (Int.natCast_nonneg q) h3
      have h8 : v.natAbs * B < q := by exact_mod_cast h7
      exact h8.le
    have hvabs : |v| ≤ ρ := by rw [Int.abs_eq_natAbs]; exact_mod_cast hvρ
    have hval : ((s : ZMod q) * r * (a : ZMod q)).valMinAbs = v + 2 ^ j * g := by
      rw [ZMod.valMinAbs_spec]
      have hρg' : (ρ : ℤ) < g := by exact_mod_cast hρg
      have hp1 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      have hg0 : (0 : ℤ) ≤ g := Int.natCast_nonneg g
      have h7 : (1 : ℤ) * g ≤ 2 ^ j * g := mul_le_mul_of_nonneg_right hp1 hg0
      have hpj : (2 : ℤ) * 2 ^ j ≤ 2 ^ m := by
        rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) hj
      have h8 : (2 : ℤ) * 2 ^ j * g ≤ 2 ^ m * g := mul_le_mul_of_nonneg_right hpj hg0
      have hpm : (2 : ℤ) ≤ 2 ^ m := by
        calc (2 : ℤ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
      have h9 : (2 : ℤ) * g ≤ 2 ^ m * g := mul_le_mul_of_nonneg_right hpm hg0
      have h10 : ((g * 2 ^ (m + 1) : ℕ) : ℤ) ≤ q := by exact_mod_cast hg2
      push_cast at h10
      rw [pow_succ] at h10
      have hq0' : (0 : ℤ) < q := by exact_mod_cast hqp.pos
      rw [abs_le] at hvabs
      refine ⟨?_, ?_, ?_⟩
      · have : ((s : ZMod q) * r * (a : ZMod q)) = (v : ZMod q) + c j := by rw [hv]; ring
        rw [this, hc]; push_cast; ring
      · linarith
      · linarith
    rw [hval, add_sub_cancel_right]
    exact hvabs
  -- Dirichlet and pigeonhole
  have hdir : ∀ x : ℤ, ∃ s, s ∈ Icc 1 J ∧ ∃ v : ℤ,
      (v : ZMod q) = (s : ZMod q) * (r * (x : ZMod q)) ∧ |v| < ρ := fun x ↦
    dirichlet ρ J hwJ (r * (x : ZMod q))
  choose sA hsA hsAv using hdir
  obtain ⟨s, hs, hcard⟩ : ∃ s ∈ Icc 1 J, A.card / J ≤ (A.filter fun x ↦ sA x = s).card := by
    refine exists_le_card_fiber_of_mul_le_card_of_maps_to (fun x _ ↦ hsA x) ?_ ?_
    · exact ⟨1, mem_Icc.2 ⟨le_rfl, hJpos⟩⟩
    · rw [Nat.card_Icc, Nat.add_sub_cancel]; exact Nat.mul_div_le _ _
  set A₁ := A.filter fun x ↦ sA x = s with hA₁
  have hnear : ∀ d ∈ A₁, |((s : ZMod q) * r * (d : ZMod q)).valMinAbs| ≤ ρ := by
    intro d hd
    obtain ⟨v, hv, hvlt⟩ := hsAv d
    rw [(mem_filter.1 hd).2] at hv
    have hval : ((s : ZMod q) * r * (d : ZMod q)).valMinAbs = v := by
      rw [ZMod.valMinAbs_spec]
      rw [abs_lt] at hvlt
      have h3 : ((2 * ρ : ℕ) : ℤ) ≤ q := by exact_mod_cast h2ρq
      push_cast at h3
      refine ⟨by rw [hv]; ring, ?_, ?_⟩ <;> linarith
    rw [hval]; exact hvlt.le
  have hitss := hits s hs
  choose! a haA ha using hitss
  set E := (range m).image a with hE
  have hinj : Set.InjOn a (range m) :=
    (lift ((s : ZMod q) * r) g ρ m K h1 hg2 a ∅ (by simp) (by simp) (by simp) ha).1
  refine ⟨A₁, filter_subset _ _, hcard, E, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
    exact haA j (mem_range.1 hj)
  · rw [hE, card_image_of_injOn hinj, card_range]
  · intro D hD hDdiss hDK
    obtain ⟨-, hnot, hdiss⟩ := lift ((s : ZMod q) * r) g ρ m K h1 hg2 a D hDdiss hDK
      (fun d hd ↦ hnear d (hD hd)) ha
    refine ⟨?_, hdiss⟩
    rw [disjoint_left]
    intro x hxD hxE
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hxE
    exact hnot j (mem_range.1 hj) hxD

end OMA.E963

end

-- source module E963.Iterate
section
open Finset

namespace OMA.E963

/-- Iterating the step theorem `i ≤ t` times gives a dissociated set with `i * m` elements. -/
theorem iterate (m t J : ℕ) (hm : 1 ≤ m) (hJ : J = 2 ^ (m + 4) * (m + t * m)) :
    ∀ i ≤ t, ∀ A : Finset ℤ, (4 * m * J ^ 5 + 1) * J ^ i ≤ A.card →
      ∃ B ⊆ A, B.card = i * m ∧ AddDissociated (B : Set ℤ) := by
  classical
  have hJpos : 0 < J := by
    rw [hJ]; exact Nat.mul_pos (by positivity) (by omega)
  intro i
  induction i with
  | zero => intro _ A _; exact ⟨∅, empty_subset _, by simp, by simp⟩
  | succ i ih =>
    intro hi A hA
    have hbig : 4 * m * J ^ 5 < A.card := by
      have h1 : 1 ≤ J ^ (i + 1) := Nat.one_le_pow _ _ hJpos
      calc 4 * m * J ^ 5 < (4 * m * J ^ 5 + 1) * 1 := by omega
        _ ≤ (4 * m * J ^ 5 + 1) * J ^ (i + 1) := Nat.mul_le_mul_left _ h1
        _ ≤ A.card := hA
    obtain ⟨A₁, hA₁, hcard, E, hE, hEcard, hstep⟩ :=
      step A m (t * m) hm (by rw [← hJ]; exact hbig)
    rw [← hJ] at hcard
    have hA₁big : (4 * m * J ^ 5 + 1) * J ^ i ≤ A₁.card := by
      refine le_trans ?_ hcard
      rw [Nat.le_div_iff_mul_le hJpos]
      calc (4 * m * J ^ 5 + 1) * J ^ i * J = (4 * m * J ^ 5 + 1) * J ^ (i + 1) := by
            rw [pow_succ]; ring
        _ ≤ A.card := hA
    obtain ⟨B₁, hB₁, hB₁card, hB₁d⟩ := ih (by omega) A₁ hA₁big
    have hK : B₁.card ≤ t * m := by
      rw [hB₁card]; exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨hdisj, hdiss⟩ := hstep B₁ hB₁ hB₁d hK
    refine ⟨B₁ ∪ E, union_subset (hB₁.trans hA₁) hE, ?_, hdiss⟩
    rw [card_union_of_disjoint hdisj, hB₁card, hEcard]; ring

/-- A finite set of reals can be mapped injectively to the integers in such a way that
dissociated sets pull back to dissociated sets. -/
theorem exists_int_model (A : Finset ℝ) :
    ∃ φ : ℝ → ℤ, Set.InjOn φ A ∧
      ∀ B ⊆ A, AddDissociated ((B.image φ : Finset ℤ) : Set ℤ) →
        AddDissociated (B : Set ℝ) := by
  classical
  set S : Finset ℝ := ((A ×ˢ A).image fun p ↦ p.1 - p.2).filter (· ≠ 0) with hS
  obtain ⟨g, hg⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ) (M := ℝ)
    (fun i : S ↦ (i : ℝ)) (fun i ↦ (mem_filter.1 i.2).2)
  have hginj : Set.InjOn g A := by
    intro x hx y hy hxy
    by_contra hne
    have hmem : x - y ∈ S :=
      mem_filter.2 ⟨mem_image.2 ⟨(x, y), mem_product.2 ⟨hx, hy⟩, rfl⟩, sub_ne_zero.2 hne⟩
    apply hg ⟨_, hmem⟩
    simp only [map_sub, hxy, sub_self]
  set N : ℕ := ∏ a ∈ A, (g a).den with hN
  have hint : ∀ a ∈ A, ∃ z : ℤ, (z : ℚ) = N * g a := by
    intro a ha
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun a ↦ (g a).den) ha
    refine ⟨c * (g a).num, ?_⟩
    rw [hN, hc]
    push_cast
    have := Rat.mul_den_eq_num (g a)
    rw [← this]; ring
  set φ : ℝ → ℤ := fun x ↦ ⌊(N : ℚ) * g x⌋ with hφ
  have hφ' : ∀ a ∈ A, (φ a : ℚ) = N * g a := by
    intro a ha
    obtain ⟨z, hz⟩ := hint a ha
    simp only [hφ]
    rw [← hz, Int.floor_intCast]
  have hNpos : (0 : ℚ) < N := by
    have : 0 < N := Finset.prod_pos fun a _ ↦ (g a).den_pos
    exact_mod_cast this
  have hφinj : Set.InjOn φ A := by
    intro x hx y hy hxy
    apply hginj hx hy
    have : (N : ℚ) * g x = N * g y := by rw [← hφ' x hx, ← hφ' y hy, hxy]
    exact mul_left_cancel₀ hNpos.ne' this
  refine ⟨φ, hφinj, ?_⟩
  intro B hB hdiss t ht u hu hsum
  have ht' : t ⊆ B := coe_subset.1 ht
  have hu' : u ⊆ B := coe_subset.1 hu
  have hsumφ : ∀ s : Finset ℝ, s ⊆ B →
      ((∑ y ∈ s.image φ, y : ℤ) : ℚ) = N * g (∑ x ∈ s, x) := by
    intro s hs
    rw [sum_image (fun x hx y hy h ↦ hφinj (hB (hs hx)) (hB (hs hy)) h), Int.cast_sum,
      map_sum, mul_sum]
    exact sum_congr rfl fun x hx ↦ hφ' x (hB (hs hx))
  have heq : ∑ y ∈ t.image φ, y = ∑ y ∈ u.image φ, y := by
    have h1 : ((∑ y ∈ t.image φ, y : ℤ) : ℚ) = ((∑ y ∈ u.image φ, y : ℤ) : ℚ) := by
      rw [hsumφ t ht', hsumφ u hu']
      have : ∑ x ∈ t, x = ∑ x ∈ u, x := hsum
      rw [this]
    exact_mod_cast h1
  have himg : t.image φ = u.image φ :=
    hdiss (coe_subset.2 (image_subset_image ht')) (coe_subset.2 (image_subset_image hu')) heq
  ext x
  constructor
  · intro hx
    have h1 : φ x ∈ u.image φ := himg ▸ mem_image_of_mem φ hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 h1
    have h2 := hφinj (hB (hu' hy)) (hB (ht' hx)) hyx
    rwa [← h2]
  · intro hx
    have h1 : φ x ∈ t.image φ := himg ▸ mem_image_of_mem φ hx
    obtain ⟨y, hy, hyx⟩ := mem_image.1 h1
    have h2 := hφinj (hB (ht' hy)) (hB (hu' hx)) hyx
    rwa [← h2]

/-- The lower bound for `f` coming out of the iteration. -/
theorem f_lower (m t n : ℕ) (hm : 1 ≤ m)
    (hn : (4 * m * (2 ^ (m + 4) * (m + t * m)) ^ 5 + 1) * (2 ^ (m + 4) * (m + t * m)) ^ t ≤ n) :
    t * m ≤ f n := by
  classical
  refine le_f fun A hA ↦ ?_
  obtain ⟨φ, hφinj, hφ⟩ := exists_int_model A
  have hA' : (A.image φ).card = n := by rw [card_image_of_injOn hφinj, hA]
  obtain ⟨B', hB', hB'card, hB'd⟩ :=
    iterate m t _ hm rfl t le_rfl (A.image φ) (by rw [hA']; exact hn)
  obtain ⟨B, hB, rfl⟩ := subset_image_iff.1 hB'
  refine ⟨B, hB, ?_, hφ B hB hB'd⟩
  rw [← hB'card]
  exact card_image_le

end OMA.E963

end

-- source module E963.Upper
section
open Finset

namespace OMA.E963

/-- A dissociated subset `B` of `{1, …, n}` satisfies `2 ^ |B| ≤ |B| n + 1`. -/
theorem diss_Icc_bound (n : ℕ) (B : Finset ℝ)
    (hB : B ⊆ (Icc 1 n).image (Nat.cast : ℕ → ℝ))
    (hd : AddDissociated (B : Set ℝ)) : 2 ^ B.card ≤ B.card * n + 1 := by
  classical
  obtain ⟨B₀, hB₀, rfl⟩ := subset_image_iff.1 hB
  rw [card_image_of_injective _ Nat.cast_injective]
  have key : (B₀.powerset).card ≤ (range (B₀.card * n + 1)).card := by
    refine card_le_card_of_injOn (fun t ↦ ∑ y ∈ t, y) ?_ ?_
    · intro t ht
      have ht' : t ⊆ B₀ := mem_powerset.1 ht
      have : ∑ y ∈ t, y < B₀.card * n + 1 := by
        rw [Nat.lt_succ_iff]
        calc ∑ y ∈ t, y ≤ ∑ _y ∈ t, n :=
              sum_le_sum fun y hy ↦ (mem_Icc.1 (hB₀ (ht' hy))).2
          _ = t.card * n := by rw [sum_const, smul_eq_mul]
          _ ≤ B₀.card * n := Nat.mul_le_mul_right _ (card_le_card ht')
      exact mem_range.2 this
    · intro t ht u hu h
      have ht' : t ⊆ B₀ := mem_powerset.1 ht
      have hu' : u ⊆ B₀ := mem_powerset.1 hu
      have h0 : ∑ y ∈ t, y = ∑ y ∈ u, y := h
      have h' : ∑ x ∈ t.image (Nat.cast : ℕ → ℝ), x = ∑ x ∈ u.image (Nat.cast : ℕ → ℝ), x := by
        rw [sum_image (Nat.cast_injective.injOn), sum_image (Nat.cast_injective.injOn),
          ← Nat.cast_sum, ← Nat.cast_sum, h0]
      have := hd (coe_subset.2 (image_subset_image ht')) (coe_subset.2 (image_subset_image hu')) h'
      exact Finset.image_injective Nat.cast_injective this
  rwa [card_powerset, card_range] at key

/-- The upper bound `f n ≤ log₂ (n log₂ (n² + 1) + 1)`. -/
theorem f_upper (n : ℕ) : f n ≤ Nat.log 2 (Nat.log 2 (n * n + 1) * n + 1) := by
  classical
  refine f_le ((Icc 1 n).image (Nat.cast : ℕ → ℝ))
    (by rw [card_image_of_injective _ Nat.cast_injective]; simp) fun B hB hd ↦ ?_
  have h1 := diss_Icc_bound n B hB hd
  have hBn : B.card ≤ n := by
    calc B.card ≤ ((Icc 1 n).image (Nat.cast : ℕ → ℝ)).card := card_le_card hB
      _ ≤ (Icc 1 n).card := card_image_le
      _ = n := by simp
  have h2 : 2 ^ B.card ≤ n * n + 1 :=
    h1.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hBn) 1)
  have h3 : B.card ≤ Nat.log 2 (n * n + 1) := Nat.le_log_of_pow_le (by norm_num) h2
  have h4 : 2 ^ B.card ≤ Nat.log 2 (n * n + 1) * n + 1 :=
    h1.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ h3) 1)
  exact Nat.le_log_of_pow_le (by norm_num) h4

end OMA.E963

end

-- source module E963.Main
section
open Filter Asymptotics Finset

namespace OMA.E963

/-- Exponentials beat polynomials. -/
lemma exists_pow_le_two_pow (k C : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, (C * m) ^ k ≤ 2 ^ m := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)
  have hε : (0 : ℝ) < 1 / ((C : ℝ) ^ k + 1) := by positivity
  have hev : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ k / 2 ^ m < 1 / ((C : ℝ) ^ k + 1) :=
    h.eventually (gt_mem_nhds hε)
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 hev
  refine ⟨m₀, fun m hm ↦ ?_⟩
  have h1 := hm₀ m hm
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_lt_div_iff₀ h2 (by positivity)] at h1
  have h3 : ((C : ℝ) * m) ^ k ≤ 2 ^ m := by
    rw [mul_pow]
    have h4 : (0 : ℝ) ≤ (m : ℝ) ^ k := by positivity
    nlinarith
  exact_mod_cast h3

/-- Clean form of the lower bound: `f n ≥ t m` as soon as `n ≥ 2 ^ (m (t + 7))` and `m` is
large in terms of `t`. -/
lemma f_lower' (t : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ n, 2 ^ (m * (t + 7)) ≤ n → t * m ≤ f n := by
  obtain ⟨m₁, hm₁⟩ := exists_pow_le_two_pow (t + 6) (16 * (t + 1))
  refine ⟨m₁ + 1, fun m hm n hn ↦ ?_⟩
  have hm1 : 1 ≤ m := by omega
  refine f_lower m t n hm1 (le_trans ?_ hn)
  obtain ⟨J, hJ⟩ : ∃ J, J = 2 ^ (m + 4) * (m + t * m) := ⟨_, rfl⟩
  rw [← hJ]
  have hJeq : J = 2 ^ m * (16 * (t + 1) * m) := by rw [hJ, pow_add]; ring
  have hJ4 : 4 * m + 1 ≤ J := by
    rw [hJeq]
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    calc 4 * m + 1 ≤ 1 * (16 * (t + 1) * m) := by nlinarith [Nat.zero_le (t * m)]
      _ ≤ 2 ^ m * (16 * (t + 1) * m) := Nat.mul_le_mul_right _ h1
  calc (4 * m * J ^ 5 + 1) * J ^ t ≤ (J * J ^ 5) * J ^ t := by
        refine Nat.mul_le_mul_right _ ?_
        have h5 : 1 ≤ J ^ 5 := Nat.one_le_pow _ _ (by omega)
        have h6 := Nat.mul_le_mul_right (J ^ 5) hJ4
        nlinarith
    _ = J ^ (t + 6) := by ring
    _ = (2 ^ m) ^ (t + 6) * (16 * (t + 1) * m) ^ (t + 6) := by rw [hJeq, mul_pow]
    _ ≤ (2 ^ m) ^ (t + 6) * 2 ^ m := Nat.mul_le_mul_left _ (hm₁ m (by omega))
    _ = 2 ^ (m * (t + 7)) := by
        rw [← pow_mul, ← pow_add]; congr 1

lemma tendsto_logb_nat : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ)) atTop atTop :=
  (Real.tendsto_logb_atTop one_lt_two).comp tendsto_natCast_atTop_atTop

lemma upper_ev (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) - Real.logb 2 n ≤ c * Real.logb 2 n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have key : ∀ᶠ x : ℝ in atTop, Real.logb 2 (2 + 2 * x) ≤ c * x := by
    have hε : 0 < c * Real.log 2 / 4 := by positivity
    have hlo := Real.isLittleO_log_id_atTop.def hε
    have htend : Tendsto (fun x : ℝ ↦ 2 + 2 * x) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (by norm_num))
    filter_upwards [htend.eventually hlo, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hpos : (0 : ℝ) < 2 + 2 * x := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_pos hpos] at hx
    have h1 : Real.log (2 + 2 * x) ≤ c * Real.log 2 / 4 * (2 + 2 * x) := (le_abs_self _).trans hx
    rw [Real.logb, div_le_iff₀ hl2]
    have h2 : 0 ≤ c * Real.log 2 * (x - 1) :=
      mul_nonneg (mul_nonneg hc.le hl2.le) (by linarith)
    nlinarith
  filter_upwards [tendsto_logb_nat.eventually key, eventually_ge_atTop 1] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  set x := Real.logb 2 (n : ℝ) with hx
  have hx0 : 0 ≤ x := Real.logb_nonneg one_lt_two hnR
  set L := Nat.log 2 (n * n + 1) with hL
  -- bound on `L`
  have hL1 : (L : ℝ) ≤ 1 + 2 * x := by
    have h1 : (L : ℝ) ≤ Real.logb 2 ((n * n + 1 : ℕ) : ℝ) := by
      have := Real.natLog_le_logb (n * n + 1) 2
      simpa using this
    have h2 : Real.logb 2 ((n * n + 1 : ℕ) : ℝ) ≤ Real.logb 2 (2 * n * n) := by
      refine Real.logb_le_logb_of_le one_lt_two (by positivity) ?_
      push_cast
      nlinarith
    have h3 : Real.logb 2 (2 * (n : ℝ) * n) = 1 + 2 * x := by
      rw [Real.logb_mul (by positivity) hn0.ne', Real.logb_mul (by norm_num) hn0.ne',
        Real.logb_self_eq_one one_lt_two]
      ring
    linarith
  have hf : (f n : ℝ) ≤ Real.logb 2 ((L * n + 1 : ℕ) : ℝ) := by
    have h1 : ((f n : ℕ) : ℝ) ≤ (Nat.log 2 (L * n + 1) : ℝ) := by exact_mod_cast f_upper n
    have h2 := Real.natLog_le_logb (L * n + 1) 2
    have h3 : (Nat.log 2 (L * n + 1) : ℝ) ≤ Real.logb 2 ((L * n + 1 : ℕ) : ℝ) := by
      simpa using h2
    linarith
  have h4 : Real.logb 2 ((L * n + 1 : ℕ) : ℝ) ≤ Real.logb 2 (((L : ℝ) + 1) * n) := by
    refine Real.logb_le_logb_of_le one_lt_two (by positivity) ?_
    push_cast
    nlinarith
  have h5 : Real.logb 2 (((L : ℝ) + 1) * n) = Real.logb 2 ((L : ℝ) + 1) + x := by
    rw [Real.logb_mul (by positivity) hn0.ne']
  have h6 : Real.logb 2 ((L : ℝ) + 1) ≤ Real.logb 2 (2 + 2 * x) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
  linarith

lemma lower_ev (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.logb 2 n - (f n : ℝ) ≤ c * Real.logb 2 n := by
  set t : ℕ := ⌈14 / c⌉₊ with ht
  have htc : 14 / c ≤ t := Nat.le_ceil _
  have htc' : 14 ≤ c * t := by
    rw [div_le_iff₀ hc] at htc; linarith
  obtain ⟨m₀, hm₀⟩ := f_lower' t
  filter_upwards [tendsto_logb_nat.eventually
    (eventually_ge_atTop (((m₀ : ℝ) + 1) * (t + 7) + 1 + 2 * (t + 1) / c)),
    eventually_ge_atTop 1] with n hn hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  set x := Real.logb 2 (n : ℝ) with hx
  have ht7 : (0 : ℝ) < (t : ℝ) + 7 := by positivity
  have hm0nn : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg _
  have htnn : (0 : ℝ) ≤ t := Nat.cast_nonneg _
  have hdivnn : 0 ≤ 2 * ((t : ℝ) + 1) / c := by positivity
  have hprod : (0 : ℝ) ≤ (m₀ : ℝ) * (t + 7) := by positivity
  have hx1 : ((m₀ : ℝ) + 1) * (t + 7) + 1 ≤ x := by linarith
  have hx2 : 2 * ((t : ℝ) + 1) ≤ c * x := by
    have h1 : 2 * ((t : ℝ) + 1) / c ≤ x := by nlinarith
    rw [div_le_iff₀ hc] at h1; linarith
  set d := (x - 1) / ((t : ℝ) + 7) with hd
  have hdmul : d * ((t : ℝ) + 7) = x - 1 := div_mul_cancel₀ _ ht7.ne'
  have hd0 : (m₀ : ℝ) ≤ d := by
    rw [hd, le_div_iff₀ ht7]; nlinarith
  have hdnn : 0 ≤ d := hm0nn.trans hd0
  set m := ⌊d⌋₊ with hm
  have hmm₀ : m₀ ≤ m := Nat.le_floor hd0
  have hmle : (m : ℝ) ≤ d := Nat.floor_le hdnn
  have hmgt : d < (m : ℝ) + 1 := Nat.lt_floor_add_one d
  have hpow : 2 ^ (m * (t + 7)) ≤ n := by
    have h1 : ((2 : ℝ)) ^ (m * (t + 7)) ≤ n := by
      rw [← Real.rpow_natCast]
      have h2 : ((m * (t + 7) : ℕ) : ℝ) ≤ x := by
        push_cast
        have := mul_le_mul_of_nonneg_right hmle ht7.le
        linarith
      calc (2 : ℝ) ^ ((m * (t + 7) : ℕ) : ℝ) ≤ (2 : ℝ) ^ x :=
            Real.rpow_le_rpow_of_exponent_le one_le_two h2
        _ = n := Real.rpow_logb two_pos (by norm_num) hn0
    exact_mod_cast h1
  have hf : ((t * m : ℕ) : ℝ) ≤ (f n : ℝ) := by exact_mod_cast hm₀ m hmm₀ n hpow
  push_cast at hf
  have h1 : (t : ℝ) * (d - 1) ≤ t * m := mul_le_mul_of_nonneg_left (by linarith) htnn
  have h2 : 14 * d ≤ c * x := by
    have h3 : 14 * d ≤ c * ((t : ℝ) + 7) * d :=
      mul_le_mul_of_nonneg_right (by nlinarith) hdnn
    have h4 : c * ((t : ℝ) + 7) * d = c * (x - 1) := by rw [mul_assoc, mul_comm _ d, hdmul]
    nlinarith
  have h5 : (t : ℝ) * d = x - 1 - 7 * d := by linarith
  nlinarith

/--
Let $f(n)$ be the maximal $k$ such that in any set $A\subset \mathbb{R}$ of size $n$ there is a
subset $B\subseteq A$ of size $\lvert B\rvert\geq k$ which is dissociated, that is, the sums
$\sum_{b\in S}b$ are distinct for all $S\subseteq B$. Then $f(n)\sim\log_2 n$.

This is the first part of Erdős problem 963 with the answer written out.
-/
theorem f_isEquivalent_logb :
    (fun n : ℕ ↦ (f n : ℝ)) ~[atTop] fun n : ℕ ↦ Real.logb 2 n := by
  rw [Asymptotics.IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [upper_ev c hc, lower_ev c hc, eventually_ge_atTop 1] with n h1 h2 hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg one_lt_two hnR
  simp only [Pi.sub_apply]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx, abs_le]
  constructor <;> linarith

end OMA.E963

end

noncomputable def OMA.answer : ℕ → ℝ := fun n ↦ Real.logb 2 n

theorem OMA.solution : Erdos963.erdos_963.parts.i.answer = OMA.answer → type_of% @Erdos963.erdos_963.parts.i := by
  intro h
  rw [h]
  exact OMA.E963.f_isEquivalent_logb
