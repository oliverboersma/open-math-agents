import OMAReductions.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1_H1_R1
import Mathlib

-- Step Erdos1099.erdos_1099.variants.lcm.R1.H1.R1.H2.R1.H1.R1.H2: hypothesis H2 of reduction Erdos1099.erdos_1099.variants.lcm.R1.H1.R1.H2.R1.H1.R1
-- Credit: @ivillar (original proof).
-- Strategy. Let E be the iterated backward difference of log along the steps of h. By the mean value
-- theorem and induction (through the family y^-m), -E lies between (d-1)! prod h / (x + sum h)^d and
-- (d-1)! prod h / x^d. If every s log (x + sum t), t a sublist of h, were within eta of 2 pi Z, then
-- s E would be within 2^d eta of some 2 pi z; the bounds force z = 0 and then a contradiction.

namespace OMA.FinDiff1099

open Real

/-- Backward iterated difference along the steps of a list. -/
noncomputable def E (f : ℝ → ℝ) : List ℕ → ℝ → ℝ
  | [], x => f x
  | a :: h, x => E f h x - E f h (x + a)

/-- The function `y ↦ y⁻ᵐ`. -/
noncomputable def g (m : ℕ) (y : ℝ) : ℝ := (y ^ m)⁻¹

/-- Rising products `m (m+1) ... (m+d-1)`. -/
def K : ℕ → ℕ → ℝ
  | _, 0 => 1
  | m, d + 1 => m * K (m + 1) d

lemma K_factorial : ∀ (d m : ℕ), K (m + 1) d * (m.factorial : ℝ) = ((m + d).factorial : ℝ)
  | 0, m => by simp [K]
  | d + 1, m => by
    have ih := K_factorial d (m + 1)
    show ((m + 1 : ℕ) : ℝ) * K (m + 1 + 1) d * (m.factorial : ℝ) = _
    have e : m + (d + 1) = m + 1 + d := by ring
    rw [e, ← ih, Nat.factorial_succ]
    push_cast
    ring

lemma K_one (d : ℕ) : K 1 d = (d.factorial : ℝ) := by
  have := K_factorial d 0
  simpa using this

lemma hasDerivAt_g (m : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (g m) (-(m : ℝ) * g (m + 1) y) y := by
  unfold g
  have h : HasDerivAt (fun y : ℝ => (y ^ m)⁻¹) (-(↑m * y ^ (m - 1)) / (y ^ m) ^ 2) y :=
    (hasDerivAt_pow m y).inv (pow_ne_zero m hy.ne')
  refine h.congr_deriv ?_
  have hy0 : y ≠ 0 := hy.ne'
  rcases m with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

lemma hasDerivAt_E_g : ∀ (h : List ℕ) (m : ℕ) (y : ℝ), 0 < y →
    HasDerivAt (E (g m) h) (-(m : ℝ) * E (g (m + 1)) h y) y
  | [], m, y, hy => hasDerivAt_g m hy
  | a :: h, m, y, hy => by
    have h1 := hasDerivAt_E_g h m y hy
    have h2 := (hasDerivAt_E_g h m (y + a) (by positivity)).comp_add_const y (a : ℝ)
    show HasDerivAt (fun x => E (g m) h x - E (g m) h (x + a)) _ y
    refine (h1.sub h2).congr_deriv ?_
    show _ = -(m : ℝ) * (E (g (m + 1)) h y - E (g (m + 1)) h (y + a))
    ring

lemma hasDerivAt_E_log : ∀ (h : List ℕ) (y : ℝ), 0 < y →
    HasDerivAt (E Real.log h) (E (g 1) h y) y
  | [], y, hy => by
    show HasDerivAt Real.log ((y ^ 1)⁻¹) y
    rw [pow_one]
    exact Real.hasDerivAt_log hy.ne'
  | a :: h, y, hy => by
    have h1 := hasDerivAt_E_log h y hy
    have h2 := (hasDerivAt_E_log h (y + a) (by positivity)).comp_add_const y (a : ℝ)
    show HasDerivAt (fun x => E Real.log h x - E Real.log h (x + a)) _ y
    exact h1.sub h2

/-- Mean value step: one backward difference is `-a` times a derivative at an interior point. -/
lemma mvt_step (F F' : ℝ → ℝ) (x : ℝ) (a : ℕ) (hx : 0 < x) (ha : 0 < a)
    (hF : ∀ y, 0 < y → HasDerivAt F (F' y) y) :
    ∃ ξ, x < ξ ∧ ξ < x + a ∧ F x - F (x + a) = -(a : ℝ) * F' ξ := by
  have hlt : x < x + a := by
    have : (0 : ℝ) < a := by exact_mod_cast ha
    linarith
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope F F' hlt
    (fun y hy => (hF y (lt_of_lt_of_le hx hy.1)).continuousAt.continuousWithinAt)
    (fun y hy => hF y (lt_trans hx hy.1))
  refine ⟨ξ, hξ.1, hξ.2, ?_⟩
  have hane : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have e1 : x + a - x = a := by ring
  rw [hξeq, e1]
  have e2 : (a : ℝ) * ((F (x + a) - F x) / a) = F (x + a) - F x := by field_simp
  linarith

lemma E_g_bounds : ∀ (h : List ℕ), (∀ a ∈ h, 0 < a) → ∀ (m : ℕ) (x : ℝ), 0 < x →
    K m h.length * (h.prod : ℝ) / (x + (h.sum : ℝ)) ^ (m + h.length) ≤ E (g m) h x ∧
    E (g m) h x ≤ K m h.length * (h.prod : ℝ) / x ^ (m + h.length)
  | [], _, m, x, hx => by simp [E, g, K]
  | a :: h, hpos, m, x, hx => by
    have ha : 0 < a := hpos a (by simp)
    have hpos' : ∀ b ∈ h, 0 < b := fun b hb => hpos b (by simp [hb])
    obtain ⟨ξ, hξ1, hξ2, hξ⟩ := mvt_step (E (g m) h) (fun y => -(m : ℝ) * E (g (m + 1)) h y) x a hx ha
      (fun y hy => hasDerivAt_E_g h m y hy)
    have hξ0 : 0 < ξ := hx.trans hξ1
    obtain ⟨lo, up⟩ := E_g_bounds h hpos' (m + 1) ξ hξ0
    have hE : E (g m) (a :: h) x = (a : ℝ) * m * E (g (m + 1)) h ξ := by
      show E (g m) h x - E (g m) h (x + a) = _
      rw [hξ]
      ring
    have hS : (0 : ℝ) ≤ (h.sum : ℝ) := Nat.cast_nonneg _
    have hP : (0 : ℝ) ≤ (h.prod : ℝ) := Nat.cast_nonneg _
    have hK : 0 ≤ K (m + 1) h.length := by
      have := K_factorial h.length m
      have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
      have hf2 : (0 : ℝ) < ((m + h.length).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      nlinarith
    have ham : (0 : ℝ) ≤ (a : ℝ) * m := by positivity
    have hexp : m + (a :: h).length = m + 1 + h.length := by simp; ring
    have hKs : K m (a :: h).length = m * K (m + 1) h.length := by simp [K]
    have hprod : (((a :: h).prod : ℕ) : ℝ) = (a : ℝ) * (h.prod : ℝ) := by
      rw [List.prod_cons, Nat.cast_mul]
    have hsum : (((a :: h).sum : ℕ) : ℝ) = (a : ℝ) + (h.sum : ℝ) := by
      rw [List.sum_cons, Nat.cast_add]
    rw [hE, hexp, hKs, hprod, hsum]
    constructor
    · have step : K (m + 1) h.length * (h.prod : ℝ) / (x + ((a : ℝ) + h.sum)) ^ (m + 1 + h.length) ≤
          K (m + 1) h.length * (h.prod : ℝ) / (ξ + (h.sum : ℝ)) ^ (m + 1 + h.length) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        linarith
      calc (m : ℝ) * K (m + 1) h.length * ((a : ℝ) * h.prod) / (x + ((a : ℝ) + h.sum)) ^ (m + 1 + h.length)
          = (a : ℝ) * m * (K (m + 1) h.length * (h.prod : ℝ) / (x + ((a : ℝ) + h.sum)) ^ (m + 1 + h.length)) := by
            ring
        _ ≤ (a : ℝ) * m * E (g (m + 1)) h ξ := mul_le_mul_of_nonneg_left (step.trans lo) ham
    · have step : K (m + 1) h.length * (h.prod : ℝ) / ξ ^ (m + 1 + h.length) ≤
          K (m + 1) h.length * (h.prod : ℝ) / x ^ (m + 1 + h.length) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        apply pow_le_pow_left₀ hx.le hξ1.le
      calc (a : ℝ) * m * E (g (m + 1)) h ξ ≤ (a : ℝ) * m * (K (m + 1) h.length * (h.prod : ℝ) / x ^ (m + 1 + h.length)) :=
            mul_le_mul_of_nonneg_left (up.trans step) ham
        _ = (m : ℝ) * K (m + 1) h.length * ((a : ℝ) * h.prod) / x ^ (m + 1 + h.length) := by ring

lemma E_log_bounds (h : List ℕ) (hne : h ≠ []) (hpos : ∀ a ∈ h, 0 < a) (x : ℝ) (hx : 0 < x) :
    ((h.length - 1).factorial : ℝ) * (h.prod : ℝ) / (x + (h.sum : ℝ)) ^ h.length ≤ -E Real.log h x ∧
    -E Real.log h x ≤ ((h.length - 1).factorial : ℝ) * (h.prod : ℝ) / x ^ h.length := by
  obtain ⟨a, h', rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha : 0 < a := hpos a (by simp)
  have hpos' : ∀ b ∈ h', 0 < b := fun b hb => hpos b (by simp [hb])
  obtain ⟨ξ, hξ1, hξ2, hξ⟩ := mvt_step (E Real.log h') (E (g 1) h') x a hx ha
    (fun y hy => hasDerivAt_E_log h' y hy)
  have hξ0 : 0 < ξ := hx.trans hξ1
  obtain ⟨lo, up⟩ := E_g_bounds h' hpos' 1 ξ hξ0
  have hE : -E Real.log (a :: h') x = (a : ℝ) * E (g 1) h' ξ := by
    show -(E Real.log h' x - E Real.log h' (x + a)) = _
    rw [hξ]
    ring
  have hS : (0 : ℝ) ≤ (h'.sum : ℝ) := Nat.cast_nonneg _
  have hP : (0 : ℝ) ≤ (h'.prod : ℝ) := Nat.cast_nonneg _
  have hK : K 1 h'.length = (h'.length.factorial : ℝ) := K_one _
  have hlen : (a :: h').length - 1 = h'.length := by simp
  have hexp : (a :: h').length = 1 + h'.length := by simp; ring
  have hprod : (((a :: h').prod : ℕ) : ℝ) = (a : ℝ) * (h'.prod : ℝ) := by
    rw [List.prod_cons, Nat.cast_mul]
  have hsum : (((a :: h').sum : ℕ) : ℝ) = (a : ℝ) + (h'.sum : ℝ) := by
    rw [List.sum_cons, Nat.cast_add]
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg _
  rw [hE, hlen, hprod, hsum, hexp, ← hK]
  have hK0 : 0 ≤ K 1 h'.length := by rw [hK]; positivity
  constructor
  · have step : K 1 h'.length * (h'.prod : ℝ) / (x + ((a : ℝ) + h'.sum)) ^ (1 + h'.length) ≤
        K 1 h'.length * (h'.prod : ℝ) / (ξ + (h'.sum : ℝ)) ^ (1 + h'.length) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      linarith
    calc K 1 h'.length * ((a : ℝ) * h'.prod) / (x + ((a : ℝ) + h'.sum)) ^ (1 + h'.length)
        = (a : ℝ) * (K 1 h'.length * (h'.prod : ℝ) / (x + ((a : ℝ) + h'.sum)) ^ (1 + h'.length)) := by
          ring
      _ ≤ (a : ℝ) * E (g 1) h' ξ := mul_le_mul_of_nonneg_left (step.trans lo) ha0
  · have step : K 1 h'.length * (h'.prod : ℝ) / ξ ^ (1 + h'.length) ≤
        K 1 h'.length * (h'.prod : ℝ) / x ^ (1 + h'.length) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply pow_le_pow_left₀ hx.le hξ1.le
    calc (a : ℝ) * E (g 1) h' ξ ≤ (a : ℝ) * (K 1 h'.length * (h'.prod : ℝ) / x ^ (1 + h'.length)) :=
          mul_le_mul_of_nonneg_left (up.trans step) ha0
      _ = K 1 h'.length * ((a : ℝ) * h'.prod) / x ^ (1 + h'.length) := by ring

lemma E_smul (s : ℝ) (F : ℝ → ℝ) : ∀ (h : List ℕ) (x : ℝ), E (fun y => s * F y) h x = s * E F h x
  | [], x => rfl
  | a :: h, x => by
    show E (fun y => s * F y) h x - E (fun y => s * F y) h (x + a) = s * (E F h x - E F h (x + a))
    rw [E_smul s F h x, E_smul s F h (x + a)]
    ring

lemma E_near (F : ℝ → ℝ) (η : ℝ) : ∀ (h : List ℕ) (x : ℝ),
    (∀ t : List ℕ, t.Sublist h → ∃ z : ℤ, |F (x + (t.sum : ℝ)) - 2 * π * z| ≤ η) →
    ∃ z : ℤ, |E F h x - 2 * π * z| ≤ 2 ^ h.length * η
  | [], x, hF => by
    obtain ⟨z, hz⟩ := hF [] (List.Sublist.slnil)
    exact ⟨z, by simpa [E] using hz⟩
  | a :: h, x, hF => by
    obtain ⟨z1, hz1⟩ := E_near F η h x (fun t ht => hF t (ht.cons a))
    obtain ⟨z2, hz2⟩ := E_near F η h (x + a) (fun t ht => by
      obtain ⟨z, hz⟩ := hF (a :: t) (ht.cons_cons a)
      refine ⟨z, ?_⟩
      have : x + (((a :: t).sum : ℕ) : ℝ) = x + a + (t.sum : ℝ) := by
        rw [List.sum_cons, Nat.cast_add]; ring
      rw [this] at hz
      exact hz)
    refine ⟨z1 - z2, ?_⟩
    show |E F h x - E F h (x + a) - 2 * π * ((z1 - z2 : ℤ) : ℝ)| ≤ 2 ^ (a :: h).length * η
    have heq : E F h x - E F h (x + a) - 2 * π * ((z1 - z2 : ℤ) : ℝ) =
        (E F h x - 2 * π * z1) - (E F h (x + a) - 2 * π * z2) := by push_cast; ring
    rw [heq]
    calc _ ≤ |E F h x - 2 * π * z1| + |E F h (x + a) - 2 * π * z2| := abs_sub _ _
      _ ≤ 2 ^ h.length * η + 2 ^ h.length * η := add_le_add hz1 hz2
      _ = 2 ^ (a :: h).length * η := by simp [pow_succ]; ring

end OMA.FinDiff1099


open Real in
theorem OMA.solution : OMA.R_Erdos1099_erdos_1099_variants_lcm_R1_H1_R1_H2_R1_H1_R1.H2 := by
  intro x h s η hx hne hpos hη hlow hup
  by_contra hcon
  push Not at hcon
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  obtain ⟨Z, hZ⟩ := OMA.FinDiff1099.E_near (fun y => s * Real.log y) η h (x : ℝ) (fun t ht => by
    obtain ⟨z, hz⟩ := hcon t ht
    exact ⟨z, by rw [Nat.cast_add] at hz; exact hz⟩)
  rw [OMA.FinDiff1099.E_smul] at hZ
  obtain ⟨lo, up⟩ := OMA.FinDiff1099.E_log_bounds h hne hpos (x : ℝ) hx'
  set L := -OMA.FinDiff1099.E Real.log h x with hL
  set Lo := ((h.length - 1).factorial : ℝ) * (h.prod : ℝ) / ((x : ℝ) + (h.sum : ℝ)) ^ h.length
  set Up := ((h.length - 1).factorial : ℝ) * (h.prod : ℝ) / (x : ℝ) ^ h.length
  have hlow' : (2 : ℝ) ^ h.length * η < |s| * Lo := by
    have : |s| * Lo = |s| * ((h.length - 1).factorial : ℝ) * (h.prod : ℝ) /
        ((x + h.sum : ℕ) : ℝ) ^ h.length := by
      rw [Nat.cast_add]; ring
    rw [this]; exact hlow
  have hup' : |s| * Up ≤ 1 := by
    have : |s| * Up = |s| * ((h.length - 1).factorial : ℝ) * (h.prod : ℝ) / (x : ℝ) ^ h.length := by
      ring
    rw [this]; exact hup
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have h1 : |s| * Lo ≤ |s| * L := mul_le_mul_of_nonneg_left lo hs0
  have h2 : |s| * L ≤ |s| * Up := mul_le_mul_of_nonneg_left up hs0
  have hL0 : 0 ≤ L := le_trans (by positivity) lo
  have hEL : OMA.FinDiff1099.E Real.log h x = -L := by rw [hL, neg_neg]
  rw [hEL] at hZ
  have habs : |s * -L| = |s| * L := by rw [abs_mul, abs_neg, abs_of_nonneg hL0]
  by_cases hZ0 : Z = 0
  · rw [hZ0, Int.cast_zero, mul_zero, sub_zero, habs] at hZ
    linarith
  · have hZ1 : (1 : ℝ) ≤ |(Z : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hZ0
    have htri : |2 * π * (Z : ℝ)| ≤ |s * -L| + |s * -L - 2 * π * Z| := by
      have := abs_sub (s * -L) (s * -L - 2 * π * Z)
      simpa using this
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos pi_pos, habs] at htri
    have := pi_gt_three
    nlinarith
