import FormalConjectures.GreensOpenProblems.«17»

/-!
# Green's Open Problem 17 (Symmetric Sets, Hązła 2020, q = 3)

Credit: Daniel Whorlow (@draonbioetl)

Self-contained proof of `Green17.green_17.variants.symmetric` using quantitative arithmetic
triangle removal (`SimpleGraph.TripartiteFromTriangles` and `SimpleGraph.FarFromTriangleFree`)
on `ZMod M × ZMod M` combined with elementary multinomial ratio bounds.
-/

-- Problem: Green17.green_17.variants.symmetric (Hązła 2020, q = 3)
-- Upstream: formal-conjectures FormalConjectures/GreensOpenProblems/17.lean:166
-- Credit: Daniel Whorlow (@draonbioetl)

open Finset SimpleGraph TripartiteFromTriangles

namespace OMA.Green17Symmetric

section Helpers

/-- Elementary bound: `1 - x ≥ exp (-2x)` for `0 ≤ x ≤ 1 / 2`. -/
lemma exp_neg_two_mul_le_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x)
    linarith
  have h2 : 1 ≤ (1 + 2 * x) * (1 - x) := by nlinarith
  have h3 : 1 ≤ Real.exp (2 * x) * (1 - x) := by
    have h1x : 0 ≤ 1 - x := by linarith
    calc (1 : ℝ) ≤ (1 + 2 * x) * (1 - x) := h2
      _ ≤ Real.exp (2 * x) * (1 - x) := mul_le_mul_of_nonneg_right h1 h1x
  rw [show (-2 * x : ℝ) = -(2 * x) by ring, Real.exp_neg]
  exact (inv_le_iff_one_le_mul₀' (Real.exp_pos _)).mpr h3

/-- Product of `zpow`s over a finset equals `zpow` of the sum. -/
lemma prod_zpow_eq_zpow_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) {B : ℝ} (hB : B ≠ 0)
    (f : ι → ℤ) : (∏ j ∈ s, B ^ f j) = B ^ (∑ j ∈ s, f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hB]

/-- Factorial ratio bound relative to a base `B > 0` when both `a` and `b` lie within `D` of `B`
    and `2 * D ≤ B`. -/
lemma factorial_div_ratio_bounds {a b : ℕ} {B D : ℝ}
    (hB : 0 < B) (hD0 : 0 ≤ D) (hDB : 2 * D ≤ B)
    (ha : |(a : ℝ) - B| ≤ D) (hb : |(b : ℝ) - B| ≤ D) :
    B ^ ((b : ℤ) - (a : ℤ)) * Real.exp (-4 * D ^ 2 / B) ≤ (b.factorial : ℝ) / (a.factorial : ℝ) ∧
    (b.factorial : ℝ) / (a.factorial : ℝ) ≤ B ^ ((b : ℤ) - (a : ℤ)) * Real.exp (4 * D ^ 2 / B) := by
  have hstep_le : ∀ {u v : ℕ}, u ≤ v → |(u : ℝ) - B| ≤ D → |(v : ℝ) - B| ≤ D →
      B ^ (v - u) * Real.exp (-4 * D ^ 2 / B) ≤ (v.factorial : ℝ) / (u.factorial : ℝ) ∧
      (v.factorial : ℝ) / (u.factorial : ℝ) ≤ B ^ (v - u) * Real.exp (4 * D ^ 2 / B) := by
    intro u v huv hu hv
    have hprod : (v.factorial : ℝ) / (u.factorial : ℝ) =
        ∏ t ∈ Finset.range (v - u), ((u + 1 + t : ℕ) : ℝ) := by
      have hfac : ∀ d : ℕ, ((u + d).factorial : ℝ) =
          (u.factorial : ℝ) * ∏ t ∈ Finset.range d, ((u + 1 + t : ℕ) : ℝ) := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
          rw [← Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
          push_cast; ring
      have hpos : (0 : ℝ) < u.factorial := Nat.cast_pos.mpr (Nat.factorial_pos u)
      have hv_eq : v = u + (v - u) := by omega
      conv_lhs => rw [hv_eq, hfac (v - u)]
      field_simp
    rw [hprod]
    have hdiff : ((v - u : ℕ) : ℝ) ≤ 2 * D := by
      have h1 : (v : ℝ) - (u : ℝ) ≤ 2 * D := by
        rw [abs_le] at hu hv; linarith
      rwa [Nat.cast_sub huv]
    have hlow_fac : ∀ t ∈ Finset.range (v - u),
        B * Real.exp (-2 * (D / B)) ≤ ((u + 1 + t : ℕ) : ℝ) := by
      intro t ht
      have hu_lo : B - D ≤ (u : ℝ) := by rw [abs_le] at hu; linarith
      have hDB' : D / B ≤ 1 / 2 := by rw [div_le_iff₀ hB]; linarith
      have hexp := exp_neg_two_mul_le_one_sub (div_nonneg hD0 hB.le) hDB'
      calc B * Real.exp (-2 * (D / B))
          ≤ B * (1 - D / B) := mul_le_mul_of_nonneg_left hexp hB.le
        _ = B - D := by field_simp
        _ ≤ (u : ℝ) := hu_lo
        _ ≤ ((u + 1 + t : ℕ) : ℝ) := by push_cast; linarith
    have hhigh_fac : ∀ t ∈ Finset.range (v - u),
        ((u + 1 + t : ℕ) : ℝ) ≤ B * Real.exp (D / B) := by
      intro t ht
      rw [Finset.mem_range] at ht
      have hv_hi : (v : ℝ) ≤ B + D := by rw [abs_le] at hv; linarith
      have hle_v : ((u + 1 + t : ℕ) : ℝ) ≤ (v : ℝ) := by exact_mod_cast (show u + 1 + t ≤ v by omega)
      have hexp : 1 + D / B ≤ Real.exp (D / B) := by linarith [Real.add_one_le_exp (D / B)]
      calc ((u + 1 + t : ℕ) : ℝ) ≤ (v : ℝ) := hle_v
        _ ≤ B + D := hv_hi
        _ = B * (1 + D / B) := by field_simp
        _ ≤ B * Real.exp (D / B) := mul_le_mul_of_nonneg_left hexp hB.le
    constructor
    · calc B ^ (v - u) * Real.exp (-4 * D ^ 2 / B)
          ≤ B ^ (v - u) * Real.exp (((v - u : ℕ) : ℝ) * (-2 * (D / B))) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB.le _)
            apply Real.exp_le_exp.mpr
            have : -4 * D ^ 2 / B = (2 * D) * (-2 * (D / B)) := by ring
            rw [this]
            have hneg : -2 * (D / B) ≤ 0 := by
              have : 0 ≤ D / B := div_nonneg hD0 hB.le
              linarith
            exact mul_le_mul_of_nonpos_right hdiff hneg
        _ = (B * Real.exp (-2 * (D / B))) ^ (v - u) := by
            rw [mul_pow, ← Real.exp_nat_mul]
        _ = ∏ _t ∈ Finset.range (v - u), (B * Real.exp (-2 * (D / B))) := by
            rw [Finset.prod_const, Finset.card_range]
        _ ≤ ∏ t ∈ Finset.range (v - u), ((u + 1 + t : ℕ) : ℝ) := by
            apply Finset.prod_le_prod
            · intro t _; positivity
            · exact hlow_fac
    · calc ∏ t ∈ Finset.range (v - u), ((u + 1 + t : ℕ) : ℝ)
          ≤ ∏ _t ∈ Finset.range (v - u), (B * Real.exp (D / B)) := by
            apply Finset.prod_le_prod
            · intro t _; positivity
            · exact hhigh_fac
        _ = (B * Real.exp (D / B)) ^ (v - u) := by
            rw [Finset.prod_const, Finset.card_range]
        _ = B ^ (v - u) * Real.exp (((v - u : ℕ) : ℝ) * (D / B)) := by
            rw [mul_pow, ← Real.exp_nat_mul]
        _ ≤ B ^ (v - u) * Real.exp (4 * D ^ 2 / B) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB.le _)
            apply Real.exp_le_exp.mpr
            have h1 : ((v - u : ℕ) : ℝ) * (D / B) ≤ (2 * D) * (D / B) :=
              mul_le_mul_of_nonneg_right hdiff (div_nonneg hD0 hB.le)
            have h2 : (2 * D) * (D / B) = 2 * D ^ 2 / B := by ring
            have h3 : 0 ≤ 2 * D ^ 2 / B := by positivity
            have h4 : 4 * D ^ 2 / B = 2 * (2 * D ^ 2 / B) := by ring
            linarith
  rcases le_total a b with hab | hba
  · have h := hstep_le hab ha hb
    have hpow : B ^ ((b : ℤ) - (a : ℤ)) = B ^ (b - a) := by
      rw [← Int.ofNat_sub hab, zpow_natCast]
    simpa [hpow] using h
  · have h := hstep_le hba hb ha
    have hpos_a : (0 : ℝ) < a.factorial := Nat.cast_pos.mpr (Nat.factorial_pos a)
    have hpos_b : (0 : ℝ) < b.factorial := Nat.cast_pos.mpr (Nat.factorial_pos b)
    have hpow : B ^ ((b : ℤ) - (a : ℤ)) = (B ^ (a - b))⁻¹ := by
      rw [show (b : ℤ) - (a : ℤ) = -((a - b : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    rw [hpow]
    constructor
    · have h2 := h.2
      have hpos_rhs : 0 < B ^ (a - b) * Real.exp (4 * D ^ 2 / B) := by positivity
      have hinv := (inv_le_inv₀ hpos_rhs (div_pos hpos_a hpos_b)).mpr h2
      rw [inv_div, mul_inv, ← Real.exp_neg] at hinv
      simpa [neg_div] using hinv
    · have h1 := h.1
      have hpos_lhs : 0 < B ^ (a - b) * Real.exp (-4 * D ^ 2 / B) := by positivity
      have hinv := (inv_le_inv₀ (div_pos hpos_a hpos_b) hpos_lhs).mpr h1
      rw [inv_div, mul_inv, ← Real.exp_neg] at hinv
      simpa [neg_div] using hinv

/-- Multinomial weight of a count vector `c : Fin k → ℕ` summing to `n`. -/
noncomputable def multiWeight {k : ℕ} (n : ℕ) (c : Fin k → ℕ) : ℝ :=
  (n.factorial : ℝ) / ∏ j : Fin k, ((c j).factorial : ℝ)

/-- Ratio bound between two multinomial weights when both `c` and `c'` are within `D` of `B = n / k`. -/
lemma multiWeight_ratio_bound {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    {c c' : Fin k → ℕ} (hc : ∑ j, c j = n) (hc' : ∑ j, c' j = n)
    {D : ℝ} (hD0 : 0 ≤ D) (hDB : 2 * D ≤ (n : ℝ) / k)
    (hcD : ∀ j, |(c j : ℝ) - (n : ℝ) / k| ≤ D)
    (hc'D : ∀ j, |(c' j : ℝ) - (n : ℝ) / k| ≤ D) :
    Real.exp (-4 * (k : ℝ) * D ^ 2 / ((n : ℝ) / k)) * multiWeight n c ≤ multiWeight n c' ∧
    multiWeight n c' ≤ Real.exp (4 * (k : ℝ) * D ^ 2 / ((n : ℝ) / k)) * multiWeight n c := by
  set B : ℝ := (n : ℝ) / k
  have hB : 0 < B := by positivity
  have hprod_c_pos : 0 < ∏ j : Fin k, ((c j).factorial : ℝ) :=
    Finset.prod_pos fun j _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hprod_c'_pos : 0 < ∏ j : Fin k, ((c' j).factorial : ℝ) :=
    Finset.prod_pos fun j _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hratio : multiWeight n c' / multiWeight n c =
      ∏ j : Fin k, ((c j).factorial : ℝ) / ((c' j).factorial : ℝ) := by
    unfold multiWeight
    have hnf : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [div_div_div_eq, Finset.prod_div_distrib]
    field_simp
  have hsum_zero : ∑ j : Fin k, ((c j : ℤ) - (c' j : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ j : Fin k, (c j : ℤ)) = (n : ℤ) := by exact_mod_cast hc
    have h2 : (∑ j : Fin k, (c' j : ℤ)) = (n : ℤ) := by exact_mod_cast hc'
    omega
  have hBprod : (∏ j : Fin k, B ^ ((c j : ℤ) - (c' j : ℤ))) = 1 := by
    rw [prod_zpow_eq_zpow_sum Finset.univ hB.ne', hsum_zero, zpow_zero]
  have hw_pos : 0 < multiWeight n c := by
    unfold multiWeight
    exact div_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) hprod_c_pos
  have hlow : Real.exp (-4 * (k : ℝ) * D ^ 2 / B) ≤ multiWeight n c' / multiWeight n c := by
    rw [hratio]
    calc Real.exp (-4 * (k : ℝ) * D ^ 2 / B)
        = (∏ j : Fin k, B ^ ((c j : ℤ) - (c' j : ℤ))) *
            (∏ _j : Fin k, Real.exp (-4 * D ^ 2 / B)) := by
          rw [hBprod, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          congr 1; ring
      _ = ∏ j : Fin k, (B ^ ((c j : ℤ) - (c' j : ℤ)) * Real.exp (-4 * D ^ 2 / B)) := by
          rw [Finset.prod_mul_distrib]
      _ ≤ ∏ j : Fin k, ((c j).factorial : ℝ) / ((c' j).factorial : ℝ) := by
          apply Finset.prod_le_prod
          · intro j _; positivity
          · intro j _; exact (factorial_div_ratio_bounds hB hD0 hDB (hc'D j) (hcD j)).1
  have hhigh : multiWeight n c' / multiWeight n c ≤ Real.exp (4 * (k : ℝ) * D ^ 2 / B) := by
    rw [hratio]
    calc ∏ j : Fin k, ((c j).factorial : ℝ) / ((c' j).factorial : ℝ)
        ≤ ∏ j : Fin k, (B ^ ((c j : ℤ) - (c' j : ℤ)) * Real.exp (4 * D ^ 2 / B)) := by
          apply Finset.prod_le_prod
          · intro j _; positivity
          · intro j _; exact (factorial_div_ratio_bounds hB hD0 hDB (hc'D j) (hcD j)).2
      _ = (∏ j : Fin k, B ^ ((c j : ℤ) - (c' j : ℤ))) *
            (∏ _j : Fin k, Real.exp (4 * D ^ 2 / B)) := by
          rw [Finset.prod_mul_distrib]
      _ = Real.exp (4 * (k : ℝ) * D ^ 2 / B) := by
          rw [hBprod, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          congr 1; ring
  exact ⟨(le_div_iff₀ hw_pos).mp hlow, (div_le_iff₀ hw_pos).mp hhigh⟩

end Helpers

section FibersAndChebyshev

/-- Count of occurrences of `j : Fin k` in `f : Fin n → Fin k`. -/
def finCount {k n : ℕ} (f : Fin n → Fin k) (j : Fin k) : ℕ :=
  (Finset.univ.filter fun i : Fin n => f i = j).card

lemma sum_finCount {k n : ℕ} (f : Fin n → Fin k) :
    ∑ j : Fin k, finCount f j = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  simpa [finCount] using h.symm

/-- Multiplicative multinomial formula for the number of functions `Fin n → Fin k` with prescribed
    fiber sizes `c : Fin k → ℕ` summing to `n`. -/
lemma prod_factorial_mul_card_fiber {k : ℕ} :
    ∀ {n : ℕ} (c : Fin k → ℕ), (∑ j, c j = n) →
      (∏ j : Fin k, (c j).factorial) *
        (Finset.univ.filter fun f : Fin n → Fin k => ∀ j, finCount f j = c j).card = n.factorial := by
  induction k with
  | zero =>
    intro n c hc
    have hn : n = 0 := by simpa using hc.symm
    subst hn
    have hcard : (Finset.univ.filter fun f : Fin 0 → Fin 0 => ∀ j, finCount f j = c j).card = 1 := by
      rw [Finset.filter_true_of_mem (fun _ _ j => Fin.elim0 j)]
      simp
    simp
  | succ k ih =>
    intro n c hc
    rw [Fin.sum_univ_succ] at hc
    set c0 := c 0
    set c' : Fin k → ℕ := fun j => c j.succ
    have hc'_sum : ∑ j : Fin k, c' j = n - c0 := by
      have : c0 + ∑ j : Fin k, c' j = n := hc
      omega
    have hc0_le : c0 ≤ n := by omega
    let Fiber := Finset.univ.filter fun f : Fin n → Fin (k + 1) => ∀ j, finCount f j = c j
    let Sset := (Finset.univ : Finset (Fin n)).powersetCard c0
    have hcard_eq : Fiber.card = ∑ S ∈ Sset,
        (Fiber.filter fun f => (Finset.univ.filter fun i => f i = 0) = S).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext f
        simp only [Finset.mem_biUnion, Finset.mem_filter, Sset, Finset.mem_powersetCard,
          Finset.subset_univ, true_and, Fiber, Finset.mem_univ]
        constructor
        · intro hf
          exact ⟨Finset.univ.filter (fun i => f i = 0), hf 0, hf, rfl⟩
        · rintro ⟨_, _, hf, _⟩; exact hf
      · intro S₁ _ S₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro f hf1 hf2
        simp only [Finset.mem_filter] at hf1 hf2
        exact hne (hf1.2.symm.trans hf2.2)
    have hconst : ∀ S ∈ Sset,
        (Fiber.filter fun f => (Finset.univ.filter fun i => f i = 0) = S).card =
        (Finset.univ.filter fun g : Fin (n - c0) → Fin k => ∀ j, finCount g j = c' j).card := by
      intro S hS
      rw [Finset.mem_powersetCard] at hS
      have hcompl_card : Fintype.card {i : Fin n // i ∉ S} = n - c0 := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hS.2]
      let e : {i : Fin n // i ∉ S} ≃ Fin (n - c0) := Fintype.equivFinOfCardEq hcompl_card
      apply Finset.card_bij (fun f hf => fun m : Fin (n - c0) =>
        (f (e.symm m).1).pred (by
          intro h0
          have hS_eq : (Finset.univ.filter fun i => f i = 0) = S := (Finset.mem_filter.mp hf).2
          have hmem : (e.symm m).1 ∈ Finset.univ.filter (fun i => f i = 0) := by simp [h0]
          exact (e.symm m).2 (hS_eq ▸ hmem)))
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fiber] at hf ⊢
        intro j
        have hcnt := hf.1 j.succ
        change finCount (fun m => (f (e.symm m).1).pred _) j = c j.succ
        rw [← hcnt]
        unfold finCount
        apply Finset.card_bij (fun m _ => (e.symm m).1)
        · intro m hm
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
          have hne0 : f (e.symm m).1 ≠ 0 := fun h0 =>
            (e.symm m).2 (hf.2 ▸ (by simp [h0] : (e.symm m).1 ∈ Finset.univ.filter (fun i => f i = 0)))
          have := congrArg Fin.succ hm
          simpa [Fin.succ_pred _ hne0] using this
        · intro m₁ _ m₂ _ heq
          exact e.symm.injective (Subtype.ext heq)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have hiS : i ∉ S := by
            intro hmem
            rw [← hf.2] at hmem
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
            exact Fin.succ_ne_zero j (hi.symm.trans hmem)
          refine ⟨e ⟨i, hiS⟩, ?_, by simp⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
          simp [hi]
      · intro f₁ hf₁ f₂ hf₂ heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fiber] at hf₁ hf₂
        funext i
        by_cases hi : i ∈ S
        · have h1 : f₁ i = 0 := by rw [← hf₁.2] at hi; exact (Finset.mem_filter.mp hi).2
          have h2 : f₂ i = 0 := by rw [← hf₂.2] at hi; exact (Finset.mem_filter.mp hi).2
          exact h1.trans h2.symm
        · have hne1 : f₁ i ≠ 0 := fun h0 => hi (by rw [← hf₁.2]; simp [h0])
          have hne2 : f₂ i ≠ 0 := fun h0 => hi (by rw [← hf₂.2]; simp [h0])
          have h := congrFun heq (e ⟨i, hi⟩)
          simp only [Equiv.symm_apply_apply] at h
          have h' := congrArg Fin.succ h
          simpa [Fin.succ_pred _ hne1, Fin.succ_pred _ hne2] using h'
      · intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
        let f : Fin n → Fin (k + 1) := fun i =>
          if hi : i ∈ S then 0 else (g (e ⟨i, hi⟩)).succ
        have hfS : (Finset.univ.filter fun i => f i = 0) = S := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]
          split_ifs with hi
          · exact ⟨fun _ => hi, fun _ => rfl⟩
          · exact ⟨fun h => absurd h (Fin.succ_ne_zero _), fun h => absurd h hi⟩
        refine ⟨f, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fiber]
          refine ⟨?_, hfS⟩
          intro j
          refine Fin.cases ?_ ?_ j
          · unfold finCount; rw [hfS, hS.2]
          · intro j'
            change finCount f j'.succ = c' j'
            rw [← hg j']
            unfold finCount
            apply Finset.card_bij (fun i hi => e ⟨i, by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, f] at hi
              intro hmem; simp [hmem] at hi; exact Fin.succ_ne_zero _ hi.symm⟩)
            · intro i hi
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, f] at hi ⊢
              split_ifs at hi with hmem
              · exact absurd hi.symm (Fin.succ_ne_zero _)
              · exact Fin.succ_injective _ hi
            · intro i₁ _ i₂ _ heq
              exact congrArg Subtype.val (e.injective heq)
            · intro m hm
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
              refine ⟨(e.symm m).1, ?_, by simp⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, f, (e.symm m).2, ↓reduceDIte]
              have hη : (⟨(e.symm m).1, (e.symm m).2⟩ : {i : Fin n // i ∉ S}) = e.symm m := rfl
              rw [hη, Equiv.apply_symm_apply, hm]
        · funext m
          simp only [f, (e.symm m).2, ↓reduceDIte, Fin.pred_succ]
          have hη : (⟨(e.symm m).1, (e.symm m).2⟩ : {i : Fin n // i ∉ S}) = e.symm m := rfl
          rw [hη, Equiv.apply_symm_apply]
    have hcard_final : Fiber.card = n.choose c0 *
        (Finset.univ.filter fun g : Fin (n - c0) → Fin k => ∀ j, finCount g j = c' j).card := by
      rw [hcard_eq, Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
      simp [Sset]
    rw [Fin.prod_univ_succ, hcard_final]
    have hih := ih c' hc'_sum
    calc c0.factorial * (∏ j : Fin k, (c' j).factorial) *
          (n.choose c0 * (Finset.univ.filter fun g : Fin (n - c0) → Fin k => ∀ j, finCount g j = c' j).card)
        = n.choose c0 * c0.factorial * ((∏ j : Fin k, (c' j).factorial) *
          (Finset.univ.filter fun g : Fin (n - c0) → Fin k => ∀ j, finCount g j = c' j).card) := by ring
      _ = n.choose c0 * c0.factorial * (n - c0).factorial := by rw [hih]
      _ = n.factorial := Nat.choose_mul_factorial_mul_factorial hc0_le

/-- Cardinality of a multinomial fiber in `ℝ` equals `multiWeight n c`. -/
lemma card_fiber_eq_multiWeight {k n : ℕ} (c : Fin k → ℕ) (hc : ∑ j, c j = n) :
    ((Finset.univ.filter fun f : Fin n → Fin k => ∀ j, finCount f j = c j).card : ℝ) =
      multiWeight n c := by
  have h := prod_factorial_mul_card_fiber c hc
  have hcast : (∏ j : Fin k, ((c j).factorial : ℝ)) *
      ((Finset.univ.filter fun f : Fin n → Fin k => ∀ j, finCount f j = c j).card : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast h
  have hpos : (0 : ℝ) < ∏ j : Fin k, ((c j).factorial : ℝ) :=
    Finset.prod_pos fun j _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  unfold multiWeight
  exact eq_div_of_mul_eq hpos.ne' (by linarith)

/-- Exact second moment of a single coordinate count in `Fin n → Fin k`. -/
lemma sum_sq_finCount {k n : ℕ} (hk : 0 < k) (j₀ : Fin k) :
    ∑ f : Fin n → Fin k, ((k : ℝ) * (finCount f j₀ : ℝ) - (n : ℝ)) ^ 2 =
      ((k : ℝ) - 1) * (n : ℝ) * (k : ℝ) ^ n := by
  let g : Fin k → ℝ := fun z => if z = j₀ then (k : ℝ) - 1 else -1
  have hsum_g : ∑ z : Fin k, g z = 0 := by
    have h1 : ∑ z : Fin k, g z = g j₀ + ∑ z ∈ Finset.univ.erase j₀, g z :=
      (Finset.add_sum_erase Finset.univ g (Finset.mem_univ j₀)).symm
    rw [h1]
    have h2 : ∑ z ∈ Finset.univ.erase j₀, g z = ((k - 1 : ℕ) : ℝ) * (-1) := by
      have hcon : ∀ z ∈ Finset.univ.erase j₀, g z = -1 := fun z hz => by
        simp [g, (Finset.mem_erase.mp hz).1]
      rw [Finset.sum_congr rfl hcon, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h2]
    have hgj : g j₀ = (k : ℝ) - 1 := by simp [g]
    rw [hgj, Nat.cast_sub (by omega : 1 ≤ k)]; push_cast; ring
  have hsum_g2 : ∑ z : Fin k, (g z) ^ 2 = ((k : ℝ) - 1) * (k : ℝ) := by
    have h1 : ∑ z : Fin k, (g z) ^ 2 = (g j₀) ^ 2 + ∑ z ∈ Finset.univ.erase j₀, (g z) ^ 2 :=
      (Finset.add_sum_erase Finset.univ (fun z => (g z) ^ 2) (Finset.mem_univ j₀)).symm
    rw [h1]
    have h2 : ∑ z ∈ Finset.univ.erase j₀, (g z) ^ 2 = ((k - 1 : ℕ) : ℝ) * 1 := by
      have hcon : ∀ z ∈ Finset.univ.erase j₀, (g z) ^ 2 = 1 := fun z hz => by
        simp [g, (Finset.mem_erase.mp hz).1]
      rw [Finset.sum_congr rfl hcon, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h2]
    have hgj : g j₀ = (k : ℝ) - 1 := by simp [g]
    rw [hgj, Nat.cast_sub (by omega : 1 ≤ k)]; push_cast; ring
  have hrewrite : ∀ f : Fin n → Fin k,
      (k : ℝ) * (finCount f j₀ : ℝ) - (n : ℝ) = ∑ i : Fin n, g (f i) := by
    intro f
    have : ∑ i : Fin n, g (f i) = ∑ i : Fin n, ((if f i = j₀ then (k : ℝ) else 0) - 1) := by
      apply Finset.sum_congr rfl; intro i _; simp only [g]; split_ifs <;> ring
    rw [this, Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
      add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
    unfold finCount; ring
  simp_rw [hrewrite, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ i : Fin n, ∑ f : Fin n → Fin k, ∑ j : Fin n, g (f i) * g (f j) =
      ((k : ℝ) - 1) * (k : ℝ) ^ n := by
    intro i
    rw [Finset.sum_comm]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hdiag : ∑ f : Fin n → Fin k, g (f i) * g (f i) = ((k : ℝ) - 1) * (k : ℝ) ^ n := by
      let e : (Fin n → Fin k) ≃ Fin k × ({m : Fin n // m ≠ i} → Fin k) :=
        { toFun := fun f => (f i, fun m => f m.1)
          invFun := fun p m => if h : m = i then p.1 else p.2 ⟨m, h⟩
          left_inv := fun f => by funext m; dsimp only; split_ifs with h <;> simp [h]
          right_inv := fun ⟨a, h⟩ => Prod.ext (by simp) (by funext ⟨m, hm⟩; simp [hm]) }
      rw [Fintype.sum_equiv e (fun f => g (f i) * g (f i)) (fun p => g p.1 * g p.1) (fun _ => rfl)]
      rw [Fintype.sum_prod_type]
      dsimp only
      simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin, nsmul_eq_mul, ← sq]
      rw [← Finset.mul_sum, hsum_g2]
      have hn1 : 1 ≤ n := Fin.pos i
      rw [Nat.cast_pow, show (k : ℝ) ^ n = (k : ℝ) * (k : ℝ) ^ (n - 1) by
        conv_lhs => rw [show n = 1 + (n - 1) by omega, pow_add, pow_one]]
      ring
    have hoff : ∀ j ∈ Finset.univ.erase i, ∑ f : Fin n → Fin k, g (f i) * g (f j) = 0 := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      let e : (Fin n → Fin k) ≃ Fin k × Fin k × ({m : Fin n // m ≠ i ∧ m ≠ j} → Fin k) :=
        { toFun := fun f => (f i, f j, fun m => f m.1)
          invFun := fun p m =>
            if h1 : m = i then p.1 else if h2 : m = j then p.2.1 else p.2.2 ⟨m, h1, h2⟩
          left_inv := fun f => by
            funext m; dsimp only
            split_ifs with h1 h2
            · simp [h1]
            · simp [h2]
            · rfl
          right_inv := fun ⟨a, b, h⟩ =>
            Prod.ext (by simp) (Prod.ext (by simp [hji]) (by funext ⟨m, hm1, hm2⟩; simp [hm1, hm2])) }
      rw [Fintype.sum_equiv e (fun f => g (f i) * g (f j)) (fun p => g p.1 * g p.2.1) (fun _ => rfl)]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
        ← Finset.sum_mul, hsum_g, mul_zero]
    rw [Finset.sum_eq_zero hoff, add_zero, hdiag]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Chebyshev concentration for all `k` coordinate counts simultaneously. -/
lemma card_bad_finCount_le {k n : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R) :
    ((Finset.univ.filter fun f : Fin n → Fin k =>
        ∃ j : Fin k, R < |(finCount f j : ℝ) - (n : ℝ) / k|).card : ℝ) ≤
      (n : ℝ) / R ^ 2 * (k : ℝ) ^ n := by
  have hsum : ∑ f : Fin n → Fin k, ∑ j : Fin k, ((k : ℝ) * (finCount f j : ℝ) - (n : ℝ)) ^ 2 =
      (k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) * (k : ℝ) ^ n := by
    rw [Finset.sum_comm]
    simp_rw [sum_sq_finCount hk]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  set Bad := Finset.univ.filter fun f : Fin n → Fin k =>
    ∃ j : Fin k, R < |(finCount f j : ℝ) - (n : ℝ) / k|
  have hlow : (Bad.card : ℝ) * ((k : ℝ) * R) ^ 2 ≤
      ∑ f : Fin n → Fin k, ∑ j : Fin k, ((k : ℝ) * (finCount f j : ℝ) - (n : ℝ)) ^ 2 := by
    calc (Bad.card : ℝ) * ((k : ℝ) * R) ^ 2
        = ∑ _f ∈ Bad, ((k : ℝ) * R) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ f ∈ Bad, ∑ j : Fin k, ((k : ℝ) * (finCount f j : ℝ) - (n : ℝ)) ^ 2 := by
          apply Finset.sum_le_sum
          intro f hf
          obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hf).2
          have h1 : (k : ℝ) * R < |(k : ℝ) * (finCount f j : ℝ) - (n : ℝ)| := by
            have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
            have heq : (k : ℝ) * ((finCount f j : ℝ) - (n : ℝ) / k) =
                (k : ℝ) * (finCount f j : ℝ) - (n : ℝ) := by field_simp
            rw [← heq, abs_mul, abs_of_pos hkpos]
            exact mul_lt_mul_of_pos_left hj hkpos
          have h2 : ((k : ℝ) * R) ^ 2 ≤ ((k : ℝ) * (finCount f j : ℝ) - (n : ℝ)) ^ 2 := by
            rw [← sq_abs ((k : ℝ) * (finCount f j : ℝ) - (n : ℝ))]
            exact pow_le_pow_left₀ (by positivity) h1.le 2
          exact h2.trans (Finset.single_le_sum
            (f := fun j : Fin k => ((k : ℝ) * (finCount f j : ℝ) - (n : ℝ)) ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
      _ ≤ ∑ f : Fin n → Fin k, ∑ j : Fin k, ((k : ℝ) * (finCount f j : ℝ) - (n : ℝ)) ^ 2 := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro f; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hsum] at hlow
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 2)]
  have hk1 : (k : ℝ) - 1 ≤ (k : ℝ) := by linarith
  have hstep : (Bad.card : ℝ) * (k : ℝ) ^ 2 * R ^ 2 ≤ (k : ℝ) ^ 2 * ((n : ℝ) * (k : ℝ) ^ n) := by
    calc (Bad.card : ℝ) * (k : ℝ) ^ 2 * R ^ 2
        = (Bad.card : ℝ) * ((k : ℝ) * R) ^ 2 := by ring
      _ ≤ (k : ℝ) * ((k : ℝ) - 1) * (n : ℝ) * (k : ℝ) ^ n := hlow
      _ ≤ (k : ℝ) * (k : ℝ) * (n : ℝ) * (k : ℝ) ^ n := by gcongr
      _ = (k : ℝ) ^ 2 * ((n : ℝ) * (k : ℝ) ^ n) := by ring
  nlinarith [sq_pos_of_pos hkpos]

end FibersAndChebyshev

section WeightBounds

/-- Trinomial weight upper bound in the `R`-box around `(n/3, n/3, n/3)` (zero Stirling!). -/
lemma trinomial_weight_upper {n K : ℕ} (hK1 : 1 ≤ K) (hn : (60 * K + 60) ^ 2 ≤ n)
    (c : Fin 3 → ℕ) (hc : ∑ j, c j = n)
    (hcd : ∀ j, |(c j : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ)) :
    multiWeight n c ≤ 40 * Real.exp (72 + 72 * ((K : ℝ) + 1) ^ 2) * (3 : ℝ) ^ n / (n : ℝ) := by
  set s : ℕ := Nat.sqrt n
  have hs_lo : 60 * K + 60 ≤ s := by
    have h := Nat.sqrt_le_sqrt hn
    rw [sq, Nat.sqrt_eq] at h
    exact h
  have hs2_le : s ^ 2 ≤ n := by simpa [sq] using Nat.sqrt_le n
  have hn_lt_s1 : n < (s + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt n
  have hs1_sq_le : ((s + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (n : ℝ) := by
    have h1 : (s + 1) ^ 2 ≤ 2 * s ^ 2 := by nlinarith
    exact_mod_cast (h1.trans (by omega : 2 * s ^ 2 ≤ 2 * n))
  have hn_pos : 0 < n := by nlinarith
  set R : ℕ := K * (s + 1)
  have h3_lo : (3 : ℝ) * ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.mul_div_le n 3
  have h3_hi : (n : ℝ) < (3 : ℝ) * ((n / 3 : ℕ) : ℝ) + 3 := by
    exact_mod_cast (show n < 3 * (n / 3) + 3 by omega)
  let c3_0 : Fin 3 → ℕ := ![n / 3, n / 3, n - 2 * (n / 3)]
  have hc3_0_sum : ∑ j : Fin 3, c3_0 j = n := by
    simp [Fin.sum_univ_three, c3_0]; omega
  have hc3_0_near : ∀ j : Fin 3, |(c3_0 j : ℝ) - (n : ℝ) / 3| ≤ 2 := by
    intro j
    fin_cases j
    · change |((n / 3 : ℕ) : ℝ) - (n : ℝ) / 3| ≤ 2
      rw [abs_le]; constructor <;> linarith
    · change |((n / 3 : ℕ) : ℝ) - (n : ℝ) / 3| ≤ 2
      rw [abs_le]; constructor <;> linarith
    · change |((n - 2 * (n / 3) : ℕ) : ℝ) - (n : ℝ) / 3| ≤ 2
      rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, abs_le]
      constructor <;> linarith
  have hw3_0_upper : multiWeight n c3_0 ≤ 40 * Real.exp 72 * (3 : ℝ) ^ n / (n : ℝ) := by
    let m : ℕ := s / 2
    have hm_le_s : 2 * m ≤ s := by omega
    have hs_le_n3 : s ≤ n / 3 := by
      have : 3 * s ≤ s ^ 2 := by nlinarith
      omega
    let BoxSmall : Finset (ℕ × ℕ) :=
      Finset.Ico (n / 3) (n / 3 + m) ×ˢ Finset.Ico (n / 3) (n / 3 + m)
    have hcard_small : BoxSmall.card = m ^ 2 := by simp [BoxSmall, sq]
    have hdisj_small : ∀ p ∈ BoxSmall,
        (∑ j : Fin 3, ![p.1, p.2, n - p.1 - p.2] j = n) ∧
        (∀ j : Fin 3, |(![p.1, p.2, n - p.1 - p.2] j : ℝ) - (n : ℝ) / 3| ≤ (s : ℝ) + 2) := by
      intro p hp
      simp only [BoxSmall, Finset.mem_product, Finset.mem_Ico] at hp
      have hp1 : p.1 + p.2 ≤ n := by omega
      have hmle : (m : ℝ) ≤ (s : ℝ) / 2 := by
        have : (2 : ℝ) * (m : ℝ) ≤ (s : ℝ) := by exact_mod_cast hm_le_s
        linarith
      have hlo1 : ((n / 3 : ℕ) : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hp.1.1
      have hhi1 : (p.1 : ℝ) ≤ ((n / 3 : ℕ) : ℝ) + (m : ℝ) := by exact_mod_cast hp.1.2.le
      have hlo2 : ((n / 3 : ℕ) : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hp.2.1
      have hhi2 : (p.2 : ℝ) ≤ ((n / 3 : ℕ) : ℝ) + (m : ℝ) := by exact_mod_cast hp.2.2.le
      refine ⟨by simp [Fin.sum_univ_three]; omega, fun j => ?_⟩
      fin_cases j
      · change |(p.1 : ℝ) - (n : ℝ) / 3| ≤ (s : ℝ) + 2
        rw [abs_le]; constructor <;> linarith
      · change |(p.2 : ℝ) - (n : ℝ) / 3| ≤ (s : ℝ) + 2
        rw [abs_le]; constructor <;> linarith
      · change |((n - p.1 - p.2 : ℕ) : ℝ) - (n : ℝ) / 3| ≤ (s : ℝ) + 2
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), abs_le]
        constructor <;> linarith
    have hsum_le : ∑ p ∈ BoxSmall, multiWeight n ![p.1, p.2, n - p.1 - p.2] ≤ (3 : ℝ) ^ n := by
      have hdisj_fib : (BoxSmall.biUnion fun p =>
          Finset.univ.filter fun f : Fin n → Fin 3 => ∀ j, finCount f j = ![p.1, p.2, n - p.1 - p.2] j).card =
          ∑ p ∈ BoxSmall, (Finset.univ.filter fun f : Fin n → Fin 3 =>
            ∀ j, finCount f j = ![p.1, p.2, n - p.1 - p.2] j).card := by
        apply Finset.card_biUnion
        intro p₁ _ p₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro f hf1 hf2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf1 hf2
        exact hne (Prod.ext ((hf1 0).symm.trans (hf2 0)) ((hf1 1).symm.trans (hf2 1)))
      have hcard_le : (BoxSmall.biUnion fun p =>
          Finset.univ.filter fun f : Fin n → Fin 3 => ∀ j, finCount f j = ![p.1, p.2, n - p.1 - p.2] j).card ≤
          3 ^ n := by
        calc _ ≤ (Finset.univ : Finset (Fin n → Fin 3)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = 3 ^ n := by simp
      have hcast : ∑ p ∈ BoxSmall, multiWeight n ![p.1, p.2, n - p.1 - p.2] =
          ((∑ p ∈ BoxSmall, (Finset.univ.filter fun f : Fin n → Fin 3 =>
            ∀ j, finCount f j = ![p.1, p.2, n - p.1 - p.2] j).card : ℕ) : ℝ) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro p hp
        exact (card_fiber_eq_multiWeight _ (hdisj_small p hp).1).symm
      rw [hcast, ← hdisj_fib]
      exact_mod_cast hcard_le
    have hD_le : 2 * ((s : ℝ) + 2) ≤ (n : ℝ) / 3 := by
      have : 6 * (s + 2) ≤ s ^ 2 := by nlinarith
      have : (6 : ℝ) * ((s : ℝ) + 2) ≤ (n : ℝ) := by exact_mod_cast (this.trans hs2_le)
      linarith
    have hterm_ge : ∀ p ∈ BoxSmall, Real.exp (-72) * multiWeight n c3_0 ≤
        multiWeight n ![p.1, p.2, n - p.1 - p.2] := by
      intro p hp
      have hrat := (multiWeight_ratio_bound (k := 3) (n := n) (by omega) hn_pos
        hc3_0_sum (hdisj_small p hp).1 (by positivity) hD_le
        (fun j => (hc3_0_near j).trans (by linarith))
        (hdisj_small p hp).2).1
      have hexp : -72 ≤ -4 * (3 : ℝ) * ((s : ℝ) + 2) ^ 2 / ((n : ℝ) / 3) := by
        have h1 : ((s : ℝ) + 2) ^ 2 ≤ 2 * (n : ℝ) := by
          have : (s + 2) ^ 2 ≤ 2 * s ^ 2 := by nlinarith
          exact_mod_cast (this.trans (by omega : 2 * s ^ 2 ≤ 2 * n))
        have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
        have h2 : -4 * (3 : ℝ) * ((s : ℝ) + 2) ^ 2 / ((n : ℝ) / 3) =
            -(36 * ((s : ℝ) + 2) ^ 2 / (n : ℝ)) := by ring
        have h3 : 36 * ((s : ℝ) + 2) ^ 2 / (n : ℝ) ≤ 72 := by
          rw [div_le_iff₀ hn_r]; linarith
        linarith
      have hw_nn : 0 ≤ multiWeight n c3_0 := by unfold multiWeight; positivity
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) hw_nn).trans hrat
    have hlow_sum : (m ^ 2 : ℝ) * (Real.exp (-72) * multiWeight n c3_0) ≤ (3 : ℝ) ^ n := by
      calc (m ^ 2 : ℝ) * (Real.exp (-72) * multiWeight n c3_0)
          = ∑ _p ∈ BoxSmall, (Real.exp (-72) * multiWeight n c3_0) := by
            rw [Finset.sum_const, hcard_small, nsmul_eq_mul]; push_cast; ring
        _ ≤ ∑ p ∈ BoxSmall, multiWeight n ![p.1, p.2, n - p.1 - p.2] := Finset.sum_le_sum hterm_ge
        _ ≤ (3 : ℝ) ^ n := hsum_le
    have hm2_ge : (n : ℝ) / 40 ≤ (m : ℝ) ^ 2 := by
      have : n ≤ 40 * m ^ 2 := by
        have : s ≤ 2 * m + 1 := by omega
        nlinarith
      have : (n : ℝ) ≤ 40 * (m : ℝ) ^ 2 := by exact_mod_cast this
      linarith
    have h1 : ((n : ℝ) / 40) * (Real.exp (-72) * multiWeight n c3_0) ≤ (3 : ℝ) ^ n :=
      (mul_le_mul_of_nonneg_right hm2_ge (by unfold multiWeight; positivity)).trans hlow_sum
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 40 * Real.exp 72 by positivity)
    have h3 : 40 * Real.exp 72 * ((n : ℝ) / 40 * (Real.exp (-72) * multiWeight n c3_0)) =
        multiWeight n c3_0 * (n : ℝ) := by
      have hexp_inv : Real.exp 72 * Real.exp (-72) = 1 := by rw [← Real.exp_add]; simp
      calc 40 * Real.exp 72 * ((n : ℝ) / 40 * (Real.exp (-72) * multiWeight n c3_0))
          = (Real.exp 72 * Real.exp (-72)) * (multiWeight n c3_0 * (n : ℝ)) := by ring
        _ = multiWeight n c3_0 * (n : ℝ) := by rw [hexp_inv, one_mul]
    rw [h3] at h2
    exact (le_div_iff₀ (Nat.cast_pos.mpr hn_pos)).mpr h2
  have hD_le : 2 * ((R : ℝ) + 2) ≤ (n : ℝ) / 3 := by
    have : 6 * (R + 2) ≤ s ^ 2 := by simp only [R]; nlinarith
    have : (6 : ℝ) * ((R : ℝ) + 2) ≤ (n : ℝ) := by exact_mod_cast (this.trans hs2_le)
    linarith
  have hrat := (multiWeight_ratio_bound (k := 3) (n := n) (by omega) hn_pos
    hc3_0_sum hc (by positivity) hD_le
    (fun j => (hc3_0_near j).trans (by linarith))
    (fun j => (hcd j).trans (by linarith))).2
  have hexp : 4 * (3 : ℝ) * ((R : ℝ) + 2) ^ 2 / ((n : ℝ) / 3) ≤ 72 * ((K : ℝ) + 1) ^ 2 := by
    have h1 : (R : ℝ) + 2 ≤ ((K : ℝ) + 1) * ((s + 1 : ℕ) : ℝ) := by
      have : R + 2 ≤ (K + 1) * (s + 1) := by simp only [R]; nlinarith
      exact_mod_cast this
    have h2 : ((R : ℝ) + 2) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 * (2 * (n : ℝ)) := by
      calc ((R : ℝ) + 2) ^ 2
          ≤ (((K : ℝ) + 1) * ((s + 1 : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
        _ = ((K : ℝ) + 1) ^ 2 * ((s + 1 : ℕ) : ℝ) ^ 2 := by ring
        _ ≤ ((K : ℝ) + 1) ^ 2 * (2 * (n : ℝ)) := by gcongr
    have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    have h3 : 4 * (3 : ℝ) * ((R : ℝ) + 2) ^ 2 / ((n : ℝ) / 3) =
        36 * ((R : ℝ) + 2) ^ 2 / (n : ℝ) := by ring
    rw [h3, div_le_iff₀ hn_r]
    linarith
  have hw_nn : 0 ≤ multiWeight n c3_0 := by unfold multiWeight; positivity
  calc multiWeight n c
      ≤ Real.exp (4 * (3 : ℝ) * ((R : ℝ) + 2) ^ 2 / ((n : ℝ) / 3)) * multiWeight n c3_0 := hrat
    _ ≤ Real.exp (72 * ((K : ℝ) + 1) ^ 2) * (40 * Real.exp 72 * (3 : ℝ) ^ n / (n : ℝ)) := by
        gcongr
    _ = 40 * Real.exp (72 + 72 * ((K : ℝ) + 1) ^ 2) * (3 : ℝ) ^ n / (n : ℝ) := by
        rw [Real.exp_add]; ring

/-- 6-nomial weight lower bound in the `D6`-box around `(n/6, ..., n/6)` (zero Stirling!). -/
lemma sixnomial_weight_lower {n K : ℕ} (hK1 : 1 ≤ K) (hn : (60 * K + 60) ^ 2 ≤ n)
    (c : Fin 6 → ℕ) (hc : ∑ j, c j = n)
    (hcd : ∀ j, |(c j : ℝ) - (n : ℝ) / 6| ≤ (2 * (K : ℝ) + 2) * ((Nat.sqrt n + 1 : ℕ) : ℝ)) :
    (1 / 2 : ℝ) / ((9 : ℝ) ^ 5 * Real.exp (288 * 9 + 288 * (2 * (K : ℝ) + 2) ^ 2)) * (6 : ℝ) ^ n /
      ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 5 ≤ multiWeight n c := by
  set s : ℕ := Nat.sqrt n
  have hs_lo : 60 * K + 60 ≤ s := by
    have h := Nat.sqrt_le_sqrt hn
    rw [sq, Nat.sqrt_eq] at h
    exact h
  have hs2_le : s ^ 2 ≤ n := by simpa [sq] using Nat.sqrt_le n
  have hn_lt_s1 : n < (s + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt n
  have hs1_sq_le : ((s + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (n : ℝ) := by
    have h1 : (s + 1) ^ 2 ≤ 2 * s ^ 2 := by nlinarith
    exact_mod_cast (h1.trans (by omega : 2 * s ^ 2 ≤ 2 * n))
  have hn_pos : 0 < n := by nlinarith
  have h6_lo : (6 : ℝ) * ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.mul_div_le n 6
  have h6_hi : (n : ℝ) < (6 : ℝ) * ((n / 6 : ℕ) : ℝ) + 6 := by
    exact_mod_cast (show n < 6 * (n / 6) + 6 by omega)
  let c6_0 : Fin 6 → ℕ := ![n / 6, n / 6, n / 6, n / 6, n / 6, n - 5 * (n / 6)]
  have hc6_0_sum : ∑ j : Fin 6, c6_0 j = n := by
    simp [Fin.sum_univ_six, c6_0]; omega
  have hc6_0_near : ∀ j : Fin 6, |(c6_0 j : ℝ) - (n : ℝ) / 6| ≤ 5 := by
    intro j
    fin_cases j
    · change |((n / 6 : ℕ) : ℝ) - (n : ℝ) / 6| ≤ 5; rw [abs_le]; constructor <;> linarith
    · change |((n / 6 : ℕ) : ℝ) - (n : ℝ) / 6| ≤ 5; rw [abs_le]; constructor <;> linarith
    · change |((n / 6 : ℕ) : ℝ) - (n : ℝ) / 6| ≤ 5; rw [abs_le]; constructor <;> linarith
    · change |((n / 6 : ℕ) : ℝ) - (n : ℝ) / 6| ≤ 5; rw [abs_le]; constructor <;> linarith
    · change |((n / 6 : ℕ) : ℝ) - (n : ℝ) / 6| ≤ 5; rw [abs_le]; constructor <;> linarith
    · change |((n - 5 * (n / 6) : ℕ) : ℝ) - (n : ℝ) / 6| ≤ 5
      rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, abs_le]; constructor <;> linarith
  have hw6_0_lower : (1 / 2 : ℝ) / ((9 : ℝ) ^ 5 * Real.exp (288 * 9)) * (6 : ℝ) ^ n /
      ((s + 1 : ℕ) : ℝ) ^ 5 ≤ multiWeight n c6_0 := by
    let R6 : ℝ := 2 * ((s + 1 : ℕ) : ℝ)
    have hR6_pos : 0 < R6 := by positivity
    have hbad6 := card_bad_finCount_le (k := 6) (n := n) (by omega) hR6_pos
    have hbad6_half : ((Finset.univ.filter fun f : Fin n → Fin 6 =>
        ∃ j : Fin 6, R6 < |(finCount f j : ℝ) - (n : ℝ) / 6|).card : ℝ) ≤ (1 / 2 : ℝ) * 6 ^ n := by
      have h1 : (n : ℝ) / R6 ^ 2 ≤ 1 / 2 := by
        have : (n : ℝ) ≤ ((s + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hn_lt_s1.le
        rw [div_le_iff₀ (by positivity)]
        simp only [R6]; linarith
      calc _ ≤ (n : ℝ) / R6 ^ 2 * (6 : ℝ) ^ n := by simpa using hbad6
        _ ≤ (1 / 2 : ℝ) * (6 : ℝ) ^ n := by gcongr
    let Good6 : Finset (Fin n → Fin 6) :=
      Finset.univ.filter fun f => ∀ j : Fin 6, |(finCount f j : ℝ) - (n : ℝ) / 6| ≤ R6
    have hGood6_ge : (1 / 2 : ℝ) * (6 : ℝ) ^ n ≤ (Good6.card : ℝ) := by
      have hcomp : Good6.card + (Finset.univ.filter fun f : Fin n → Fin 6 =>
          ∃ j : Fin 6, R6 < |(finCount f j : ℝ) - (n : ℝ) / 6|).card = 6 ^ n := by
        have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (p := fun f : Fin n → Fin 6 => ∀ j : Fin 6, |(finCount f j : ℝ) - (n : ℝ) / 6| ≤ R6)
        simp only [not_forall, not_le, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at this
        exact this
      have htot : (Good6.card : ℝ) + ((Finset.univ.filter fun f : Fin n → Fin 6 =>
          ∃ j : Fin 6, R6 < |(finCount f j : ℝ) - (n : ℝ) / 6|).card : ℝ) = (6 : ℝ) ^ n := by
        exact_mod_cast hcomp
      linarith
    let lo6 : ℕ := n / 6 - 3 * (s + 1)
    let hi6 : ℕ := n / 6 + 3 * (s + 1)
    let Box6_5 : Finset (Fin 5 → ℕ) :=
      Fintype.piFinset fun _ : Fin 5 => Finset.Icc lo6 hi6
    have hBox6_5_card : (Box6_5.card : ℝ) ≤ (9 : ℝ) ^ 5 * ((s + 1 : ℕ) : ℝ) ^ 5 := by
      have hIcc : (Finset.Icc lo6 hi6).card ≤ 9 * (s + 1) := by
        rw [Nat.card_Icc]; omega
      have hpi : Box6_5.card = (Finset.Icc lo6 hi6).card ^ 5 := by
        simp [Box6_5, Fintype.card_piFinset]
      rw [hpi, Nat.cast_pow]
      calc ((Finset.Icc lo6 hi6).card : ℝ) ^ 5
          ≤ ((9 * (s + 1) : ℕ) : ℝ) ^ 5 := by exact_mod_cast Nat.pow_le_pow_left hIcc 5
        _ = (9 : ℝ) ^ 5 * ((s + 1 : ℕ) : ℝ) ^ 5 := by push_cast; ring
    let Types6 : Finset (Fin 6 → ℕ) := Good6.image fun f => finCount f
    have hTypes6_card : (Types6.card : ℝ) ≤ (9 : ℝ) ^ 5 * ((s + 1 : ℕ) : ℝ) ^ 5 := by
      let proj5 : (Fin 6 → ℕ) → (Fin 5 → ℕ) := fun c j => c j.castSucc
      have hproj_inj : Set.InjOn proj5 (Types6 : Set (Fin 6 → ℕ)) := by
        intro c₁ hc₁ c₂ hc₂ heq
        obtain ⟨f₁, _, rfl⟩ := Finset.mem_image.mp hc₁
        obtain ⟨f₂, _, rfl⟩ := Finset.mem_image.mp hc₂
        have hs1 := sum_finCount f₁
        have hs2 := sum_finCount f₂
        have h5 : ∀ j : Fin 5, finCount f₁ j.castSucc = finCount f₂ j.castSucc :=
          fun j => congrFun heq j
        funext j
        refine Fin.lastCases ?_ h5 j
        rw [Fin.sum_univ_castSucc] at hs1 hs2
        have hsum5 : ∑ i : Fin 5, finCount f₁ i.castSucc = ∑ i : Fin 5, finCount f₂ i.castSucc :=
          Finset.sum_congr rfl fun i _ => h5 i
        omega
      have hsub5 : Types6.image proj5 ⊆ Box6_5 := by
        intro g hg
        rw [Finset.mem_image] at hg
        obtain ⟨c, hc, rfl⟩ := hg
        obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc
        have hf_ok := (Finset.mem_filter.mp hf).2
        simp only [Box6_5, Fintype.mem_piFinset, Finset.mem_Icc, proj5]
        intro j
        have hj := hf_ok j.castSucc
        rw [abs_le] at hj
        have hs1_ge1 : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos s
        have h1 : (n / 6 : ℤ) - 3 * ((s + 1 : ℕ) : ℤ) ≤ (finCount f j.castSucc : ℤ) := by
          have : ((n / 6 : ℕ) : ℝ) - 3 * ((s + 1 : ℕ) : ℝ) ≤ (finCount f j.castSucc : ℝ) := by
            simp only [R6] at hj; linarith
          exact_mod_cast this
        have h2 : (finCount f j.castSucc : ℤ) ≤ (n / 6 : ℤ) + 3 * ((s + 1 : ℕ) : ℤ) := by
          have : (finCount f j.castSucc : ℝ) ≤ ((n / 6 : ℕ) : ℝ) + 3 * ((s + 1 : ℕ) : ℝ) := by
            simp only [R6] at hj; linarith
          exact_mod_cast this
        exact ⟨by omega, by omega⟩
      have hcard_le : Types6.card ≤ Box6_5.card := by
        rw [← Finset.card_image_of_injOn hproj_inj]
        exact Finset.card_le_card hsub5
      exact (Nat.cast_le.mpr hcard_le).trans hBox6_5_card
    have hD6_le : 2 * (3 * ((s + 1 : ℕ) : ℝ)) ≤ (n : ℝ) / 6 := by
      have : 36 * (s + 1) ≤ s ^ 2 := by nlinarith
      have : (36 : ℝ) * ((s + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (this.trans hs2_le)
      linarith
    have hGood6_upper : (Good6.card : ℝ) ≤
        (Types6.card : ℝ) * (Real.exp (288 * 9) * multiWeight n c6_0) := by
      have hpart : Good6.card ≤ ∑ c ∈ Types6,
          (Finset.univ.filter fun f : Fin n → Fin 6 => ∀ j, finCount f j = c j).card := by
        calc Good6.card
            ≤ (Types6.biUnion fun c => Finset.univ.filter fun f : Fin n → Fin 6 =>
                ∀ j, finCount f j = c j).card := by
              apply Finset.card_le_card
              intro f hf
              rw [Finset.mem_biUnion]
              exact ⟨finCount f, Finset.mem_image_of_mem _ hf, by simp⟩
          _ ≤ _ := Finset.card_biUnion_le
      calc (Good6.card : ℝ)
          ≤ ∑ c ∈ Types6, ((Finset.univ.filter fun f : Fin n → Fin 6 =>
              ∀ j, finCount f j = c j).card : ℝ) := by exact_mod_cast hpart
        _ = ∑ c ∈ Types6, multiWeight n c := by
            apply Finset.sum_congr rfl
            intro c hc
            obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hc
            exact card_fiber_eq_multiWeight _ (sum_finCount f)
        _ ≤ ∑ _c ∈ Types6, (Real.exp (288 * 9) * multiWeight n c6_0) := by
            apply Finset.sum_le_sum
            intro c hc
            obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hc
            have hf_ok := (Finset.mem_filter.mp hf).2
            have hrat := (multiWeight_ratio_bound (k := 6) (n := n) (by omega) hn_pos
              hc6_0_sum (sum_finCount f) (by positivity) hD6_le
              (fun j => (hc6_0_near j).trans (by
                have : 5 ≤ 3 * (s + 1) := by omega
                exact_mod_cast this))
              (fun j => (hf_ok j).trans (by simp only [R6]; linarith))).2
            have hexp : 4 * (6 : ℝ) * (3 * ((s + 1 : ℕ) : ℝ)) ^ 2 / ((n : ℝ) / 6) ≤ 288 * 9 := by
              have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
              have h1 : 4 * (6 : ℝ) * (3 * ((s + 1 : ℕ) : ℝ)) ^ 2 / ((n : ℝ) / 6) =
                  144 * 9 * ((s + 1 : ℕ) : ℝ) ^ 2 / (n : ℝ) := by ring
              rw [h1, div_le_iff₀ hn_r]; linarith
            have hw_nn : 0 ≤ multiWeight n c6_0 := by unfold multiWeight; positivity
            exact hrat.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) hw_nn)
        _ = (Types6.card : ℝ) * (Real.exp (288 * 9) * multiWeight n c6_0) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcomb := hGood6_ge.trans (hGood6_upper.trans
      (mul_le_mul_of_nonneg_right hTypes6_card (by unfold multiWeight; positivity)))
    have hrew : (1 / 2 : ℝ) * (6 : ℝ) ^ n ≤
        multiWeight n c6_0 * ((9 : ℝ) ^ 5 * Real.exp (288 * 9) * ((s + 1 : ℕ) : ℝ) ^ 5) := by
      linarith
    have hdiv1 : (1 / 2 : ℝ) * (6 : ℝ) ^ n / ((9 : ℝ) ^ 5 * Real.exp (288 * 9) * ((s + 1 : ℕ) : ℝ) ^ 5) ≤
        multiWeight n c6_0 := (div_le_iff₀ (by positivity)).mpr hrew
    have hrew2 : (1 / 2 : ℝ) / ((9 : ℝ) ^ 5 * Real.exp (288 * 9)) * (6 : ℝ) ^ n / ((s + 1 : ℕ) : ℝ) ^ 5 =
        (1 / 2 : ℝ) * (6 : ℝ) ^ n / ((9 : ℝ) ^ 5 * Real.exp (288 * 9) * ((s + 1 : ℕ) : ℝ) ^ 5) := by ring
    rwa [hrew2]
  let D6 : ℝ := (2 * (K : ℝ) + 2) * ((s + 1 : ℕ) : ℝ)
  have hD6_big_le : 2 * D6 ≤ (n : ℝ) / 6 := by
    have : 12 * (2 * K + 2) * (s + 1) ≤ s ^ 2 := by nlinarith
    have : (12 : ℝ) * (2 * (K : ℝ) + 2) * ((s + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (this.trans hs2_le)
    simp only [D6]; linarith
  have h5_le_D6 : (5 : ℝ) ≤ D6 := by
    have : 5 ≤ (2 * K + 2) * (s + 1) := by nlinarith
    have hcast : (5 : ℝ) ≤ ((2 * K + 2 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) := by exact_mod_cast this
    simp only [D6, Nat.cast_add, Nat.cast_one]; push_cast at hcast; linarith
  have hrat := (multiWeight_ratio_bound (k := 6) (n := n) (by omega) hn_pos
    hc6_0_sum hc (by positivity) hD6_big_le
    (fun j => (hc6_0_near j).trans h5_le_D6) hcd).1
  have hexp : -(288 * (2 * (K : ℝ) + 2) ^ 2) ≤ -4 * (6 : ℝ) * D6 ^ 2 / ((n : ℝ) / 6) := by
    have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    have h1 : -4 * (6 : ℝ) * D6 ^ 2 / ((n : ℝ) / 6) = -(144 * D6 ^ 2 / (n : ℝ)) := by ring
    have h2 : D6 ^ 2 ≤ (2 * (K : ℝ) + 2) ^ 2 * (2 * (n : ℝ)) := by
      simp only [D6, mul_pow]; gcongr
    have h3 : 144 * D6 ^ 2 / (n : ℝ) ≤ 288 * (2 * (K : ℝ) + 2) ^ 2 := by
      rw [div_le_iff₀ hn_r]; linarith
    linarith
  have hw_nn : 0 ≤ multiWeight n c6_0 := by unfold multiWeight; positivity
  calc (1 / 2 : ℝ) / ((9 : ℝ) ^ 5 * Real.exp (288 * 9 + 288 * (2 * (K : ℝ) + 2) ^ 2)) * (6 : ℝ) ^ n /
          ((s + 1 : ℕ) : ℝ) ^ 5
      = Real.exp (-(288 * (2 * (K : ℝ) + 2) ^ 2)) *
          ((1 / 2 : ℝ) / ((9 : ℝ) ^ 5 * Real.exp (288 * 9)) * (6 : ℝ) ^ n / ((s + 1 : ℕ) : ℝ) ^ 5) := by
        rw [Real.exp_add, Real.exp_neg]; field_simp
    _ ≤ Real.exp (-(288 * (2 * (K : ℝ) + 2) ^ 2)) * multiWeight n c6_0 :=
        mul_le_mul_of_nonneg_left hw6_0_lower (Real.exp_pos _).le
    _ ≤ Real.exp (-4 * (6 : ℝ) * D6 ^ 2 / ((n : ℝ) / 6)) * multiWeight n c6_0 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) hw_nn
    _ ≤ multiWeight n c := hrat

end WeightBounds

section ArithmeticTriangleRemoval

/-- On `G = ZMod M × ZMod M`, the 60-degree rotation `rot (u, v) = (-v, u + v)`
    and `rot2 (u, v) = (-u - v, u)` satisfy `rot2 x - rot x + x = 0`. -/
def rot {M : ℕ} (p : ZMod M × ZMod M) : ZMod M × ZMod M := (-p.2, p.1 + p.2)

def rot2 {M : ℕ} (p : ZMod M × ZMod M) : ZMod M × ZMod M := (-p.1 - p.2, p.1)

lemma rot_injective {M : ℕ} : Function.Injective (rot (M := M)) := by
  rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
  simp only [rot, Prod.mk.injEq] at h
  have hv : v₁ = v₂ := neg_inj.mp h.1
  subst hv
  exact Prod.ext (add_right_cancel h.2) rfl

lemma rot2_injective {M : ℕ} : Function.Injective (rot2 (M := M)) := by
  rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ h
  simp only [rot2, Prod.mk.injEq] at h
  have hu : u₁ = u₂ := h.2
  subst hu
  have hv : -v₁ = -v₂ := by linear_combination h.1
  exact Prod.ext rfl (neg_inj.mp hv)

lemma rot2_add_self {M : ℕ} (p : ZMod M × ZMod M) : rot2 p + p = rot p := by
  rcases p with ⟨u, v⟩
  ext
  · simp [rot, rot2]; ring
  · simp [rot, rot2]

/-- Quantitative arithmetic triangle removal: for any subset `S` of `G = ZMod M × ZMod M` of
    density `≥ γ > 0`, there are at least `27 * triangleRemovalBound (γ / 9) * |G| ^ 2`
    triples `(s₀, s₁, s₂) ∈ S³` satisfying `rot2 s₀ - rot s₁ + s₂ = 0`. -/
lemma card_rot_triples_ge {M : ℕ} [NeZero M] (S : Finset (ZMod M × ZMod M))
    {γ : ℝ} (_hγ : 0 < γ) (hS : γ * (Fintype.card (ZMod M × ZMod M) : ℝ) ≤ (S.card : ℝ)) :
    27 * triangleRemovalBound (γ / 9) * (Fintype.card (ZMod M × ZMod M) : ℝ) ^ 2 ≤
      (((S ×ˢ S ×ˢ S).filter fun t => rot2 t.1 - rot t.2.1 + t.2.2 = 0).card : ℝ) := by
  classical
  let G := ZMod M × ZMod M
  let triIdx : Finset (G × G × G) :=
    (Finset.univ ×ˢ S).image fun p => (p.1, p.1 + rot2 p.2, p.1 - p.2)
  have htri_card : triIdx.card = Fintype.card G * S.card := by
    rw [Finset.card_image_of_injective]
    · simp
    · rintro ⟨g₁, s₁⟩ ⟨g₂, s₂⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, _, h3⟩ := h
      exact Prod.ext rfl (sub_right_inj.mp h3)
  have hED : ExplicitDisjoint triIdx := by
    constructor
    · intro a b c a' h1 h2
      obtain ⟨⟨g₁, s₁⟩, _, h1eq⟩ := Finset.mem_image.mp h1
      obtain ⟨⟨g₂, s₂⟩, _, h2eq⟩ := Finset.mem_image.mp h2
      simp only [Prod.mk.injEq] at h1eq h2eq
      obtain ⟨rfl, rfl, rfl⟩ := h1eq
      obtain ⟨rfl, hb, hc⟩ := h2eq
      have hbc : (g₂ + rot2 s₂) - (g₂ - s₂) = (g₁ + rot2 s₁) - (g₁ - s₁) := by rw [hb, hc]
      have hrot : rot s₂ = rot s₁ := by
        calc rot s₂ = rot2 s₂ + s₂ := (rot2_add_self s₂).symm
          _ = (g₂ + rot2 s₂) - (g₂ - s₂) := by abel
          _ = (g₁ + rot2 s₁) - (g₁ - s₁) := hbc
          _ = rot2 s₁ + s₁ := by abel
          _ = rot s₁ := rot2_add_self s₁
      have hs : s₂ = s₁ := rot_injective hrot
      subst hs
      exact sub_left_inj.mp hc.symm
    · intro a b c b' h1 h2
      obtain ⟨⟨g₁, s₁⟩, _, h1eq⟩ := Finset.mem_image.mp h1
      obtain ⟨⟨g₂, s₂⟩, _, h2eq⟩ := Finset.mem_image.mp h2
      simp only [Prod.mk.injEq] at h1eq h2eq
      obtain ⟨rfl, rfl, rfl⟩ := h1eq
      obtain ⟨rfl, rfl, hc⟩ := h2eq
      have hs : s₂ = s₁ := sub_right_inj.mp hc
      subst hs; rfl
    · intro a b c c' h1 h2
      obtain ⟨⟨g₁, s₁⟩, _, h1eq⟩ := Finset.mem_image.mp h1
      obtain ⟨⟨g₂, s₂⟩, _, h2eq⟩ := Finset.mem_image.mp h2
      simp only [Prod.mk.injEq] at h1eq h2eq
      obtain ⟨rfl, rfl, rfl⟩ := h1eq
      obtain ⟨rfl, hb, rfl⟩ := h2eq
      have hs : s₂ = s₁ := rot2_injective (add_left_cancel hb)
      subst hs; rfl
  have hfar : (graph triIdx).FarFromTriangleFree (γ / 9) := by
    apply TripartiteFromTriangles.farFromTriangleFree triIdx
    rw [htri_card, Nat.cast_mul]
    have hcalc : (γ / 9) * (((Fintype.card G + Fintype.card G + Fintype.card G) ^ 2 : ℕ) : ℝ) =
        (Fintype.card G : ℝ) * (γ * (Fintype.card G : ℝ)) := by push_cast; ring
    rw [hcalc]
    exact mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
  have hrem := hfar.le_card_cliqueFinset
  have hcardV : (Fintype.card (G ⊕ G ⊕ G) : ℝ) = 3 * (Fintype.card G : ℝ) := by
    simp only [Fintype.card_sum, Nat.cast_add]; ring
  rw [hcardV] at hrem
  set Valid := (S ×ˢ S ×ˢ S).filter fun t : G × G × G => rot2 t.1 - rot t.2.1 + t.2.2 = 0
  let φ : G × (G × G × G) → Finset (G ⊕ G ⊕ G) :=
    fun p => {Sum3.in₀ p.1, Sum3.in₁ (p.1 + rot2 p.2.1), Sum3.in₂ (p.1 - p.2.2.2)}
  have hsub : (graph triIdx).cliqueFinset 3 ⊆ (Finset.univ ×ˢ Valid).image φ := by
    intro cl hcl
    rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_iff] at hcl
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hcl
    obtain ⟨a, b, c, habc, hab, hac, hbc⟩ := TripartiteFromTriangles.graph_triple hxy hxz hyz
    obtain ⟨c', hc'⟩ := TripartiteFromTriangles.Graph.in₀₁_iff.mp hab
    obtain ⟨b', hb'⟩ := TripartiteFromTriangles.Graph.in₀₂_iff.mp hac
    obtain ⟨a', ha'⟩ := TripartiteFromTriangles.Graph.in₁₂_iff.mp hbc
    obtain ⟨⟨g₀, s₀⟩, hgs₀, h0eq⟩ := Finset.mem_image.mp hc'
    obtain ⟨⟨g₂, s₂⟩, hgs₂, h2eq⟩ := Finset.mem_image.mp hb'
    obtain ⟨⟨g₁, s₁⟩, hgs₁, h1eq⟩ := Finset.mem_image.mp ha'
    simp only [Finset.mem_product, Finset.mem_univ, true_and] at hgs₀ hgs₁ hgs₂
    simp only [Prod.mk.injEq] at h0eq h1eq h2eq
    obtain ⟨hg₀, hb_eq, _⟩ := h0eq
    obtain ⟨hg₂, _, hc_eq⟩ := h2eq
    obtain ⟨_, hb_eq', hc_eq'⟩ := h1eq
    have hrot_eq : rot2 s₀ - rot s₁ + s₂ = 0 := by
      have h1 : rot2 s₀ = b - a := by rw [← hb_eq, hg₀]; abel
      have h2 : rot s₁ = b - c := by
        calc rot s₁ = rot2 s₁ + s₁ := (rot2_add_self s₁).symm
          _ = (g₁ + rot2 s₁) - (g₁ - s₁) := by abel
          _ = b - c := by rw [hb_eq', hc_eq']
      have h3 : s₂ = a - c := by rw [← hc_eq, hg₂]; abel
      rw [h1, h2, h3]; abel
    have ha_b : a + rot2 s₀ = b := by rw [← hg₀, hb_eq]
    have ha_c : a - s₂ = c := by rw [← hg₂, hc_eq]
    rw [Finset.mem_image]
    refine ⟨(a, (s₀, s₁, s₂)), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_univ, true_and, Valid, Finset.mem_filter]
      exact ⟨⟨hgs₀, hgs₁, hgs₂⟩, hrot_eq⟩
    · simp only [φ, ha_b, ha_c]; exact habc
  have hcl_le : ((graph triIdx).cliqueFinset 3).card ≤ Fintype.card G * Valid.card := by
    calc ((graph triIdx).cliqueFinset 3).card
        ≤ ((Finset.univ ×ˢ Valid).image φ).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ ×ˢ Valid).card := Finset.card_image_le
      _ = Fintype.card G * Valid.card := by simp
  have hGpos : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  have hcomb : triangleRemovalBound (γ / 9) * (3 * (Fintype.card G : ℝ)) ^ 3 ≤
      (Fintype.card G : ℝ) * (Valid.card : ℝ) := hrem.trans (by exact_mod_cast hcl_le)
  have hcomb' : (Fintype.card G : ℝ) * (27 * triangleRemovalBound (γ / 9) * (Fintype.card G : ℝ) ^ 2) ≤
      (Fintype.card G : ℝ) * (Valid.card : ℝ) := by
    calc (Fintype.card G : ℝ) * (27 * triangleRemovalBound (γ / 9) * (Fintype.card G : ℝ) ^ 2)
        = triangleRemovalBound (γ / 9) * (3 * (Fintype.card G : ℝ)) ^ 3 := by ring
      _ ≤ (Fintype.card G : ℝ) * (Valid.card : ℝ) := hcomb
  exact le_of_mul_le_mul_left hcomb' hGpos

end ArithmeticTriangleRemoval

section MainTheorem

/-- Embedding `Fin 3 ≃ ZMod 3`. -/
def fin3Equiv : Fin 3 ≃ ZMod 3 where
  toFun j := (j.val : ZMod 3)
  invFun z := ⟨z.val, z.val_lt⟩
  left_inv j := by ext; simp [ZMod.val_natCast_of_lt j.isLt]
  right_inv z := by simp

/-- Decoding `Fin 6` into `(x_i, d_i) ∈ ZMod 3 × {0, 1}`. -/
def dec6 : Fin 6 → ZMod 3 × ZMod 3
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (2, 0)
  | 3 => (0, 1)
  | 4 => (1, 1)
  | 5 => (2, 1)

lemma dec6_injective : Function.Injective dec6 := by
  decide

lemma dec6_snd_mem (j : Fin 6) : (dec6 j).2 = 0 ∨ (dec6 j).2 = 1 := by
  fin_cases j <;> simp [dec6]

/-- From two `Fin n → ZMod 3` with identical counts of `0, 1, 2`, produce a coordinate permutation. -/
lemma exists_perm_of_same_finCount {n : ℕ} (x y : Fin n → ZMod 3)
    (h : ∀ j : Fin 3, finCount (fun i => fin3Equiv.symm (x i)) j =
      finCount (fun i => fin3Equiv.symm (y i)) j) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, x (σ i) = y i := by
  have heq : ∀ j : Fin 3, Fintype.card {i : Fin n // fin3Equiv.symm (y i) = j} =
      Fintype.card {i : Fin n // fin3Equiv.symm (x i) = j} := fun j => by
    simp only [Fintype.card_subtype]
    exact (h j).symm
  let e : ∀ j : Fin 3, {i : Fin n // fin3Equiv.symm (y i) = j} ≃
      {i : Fin n // fin3Equiv.symm (x i) = j} :=
    fun j => Fintype.equivOfCardEq (heq j)
  let σfun : Fin n → Fin n := fun i => (e (fin3Equiv.symm (y i)) ⟨i, rfl⟩).1
  have hσ_eq : ∀ i, x (σfun i) = y i := fun i => by
    have hprop := (e (fin3Equiv.symm (y i)) ⟨i, rfl⟩).2
    exact fin3Equiv.symm.injective hprop
  have hcast_e : ∀ (j₁ j₂ : Fin 3) (hj : j₁ = j₂) (a : {i : Fin n // fin3Equiv.symm (y i) = j₁}),
      (e j₁ a).1 = (e j₂ ⟨a.1, a.2.trans hj⟩).1 := by
    rintro _ _ rfl _; rfl
  have hσ_inj : Function.Injective σfun := by
    intro i₁ i₂ h12
    have hy : y i₁ = y i₂ := by rw [← hσ_eq i₁, ← hσ_eq i₂, h12]
    have hsy : fin3Equiv.symm (y i₂) = fin3Equiv.symm (y i₁) := congrArg _ hy.symm
    have hsub : e (fin3Equiv.symm (y i₁)) ⟨i₁, rfl⟩ = e (fin3Equiv.symm (y i₁)) ⟨i₂, hsy⟩ := by
      apply Subtype.ext
      change σfun i₁ = (e (fin3Equiv.symm (y i₁)) ⟨i₂, hsy⟩).1
      rw [h12]
      exact hcast_e (fin3Equiv.symm (y i₂)) (fin3Equiv.symm (y i₁)) hsy ⟨i₂, rfl⟩
    exact congrArg Subtype.val ((e (fin3Equiv.symm (y i₁))).injective hsub)
  exact ⟨Equiv.ofBijective σfun (Finite.injective_iff_bijective.mp hσ_inj), hσ_eq⟩

/-- Counts of `0, 1, 2` in `x`, `x + d`, `x + 2 • d` for a `Fin 6`-encoded pair `f`. -/
lemma counts_of_dec6 {n : ℕ} (f : Fin n → Fin 6) :
    let x : Fin n → ZMod 3 := fun i => (dec6 (f i)).1
    let d : Fin n → ZMod 3 := fun i => (dec6 (f i)).2
    (finCount (fun i => fin3Equiv.symm (x i)) 0 = finCount f 0 + finCount f 3 ∧
     finCount (fun i => fin3Equiv.symm (x i)) 1 = finCount f 1 + finCount f 4 ∧
     finCount (fun i => fin3Equiv.symm (x i)) 2 = finCount f 2 + finCount f 5) ∧
    (finCount (fun i => fin3Equiv.symm ((x + d) i)) 0 = finCount f 0 + finCount f 5 ∧
     finCount (fun i => fin3Equiv.symm ((x + d) i)) 1 = finCount f 1 + finCount f 3 ∧
     finCount (fun i => fin3Equiv.symm ((x + d) i)) 2 = finCount f 2 + finCount f 4) ∧
    (finCount (fun i => fin3Equiv.symm ((x + 2 • d) i)) 0 = finCount f 0 + finCount f 4 ∧
     finCount (fun i => fin3Equiv.symm ((x + 2 • d) i)) 1 = finCount f 1 + finCount f 5 ∧
     finCount (fun i => fin3Equiv.symm ((x + 2 • d) i)) 2 = finCount f 2 + finCount f 3) := by
  dsimp only
  have hsplit : ∀ (P : Fin 6 → Prop) [DecidablePred P] (a b : Fin 6), a ≠ b →
      (∀ z : Fin 6, P z ↔ z = a ∨ z = b) →
      (Finset.univ.filter fun i : Fin n => P (f i)).card = finCount f a + finCount f b := by
    intro P _ a b hab hP
    unfold finCount
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext i; simp [hP]
    · rw [Finset.disjoint_left]; intro i h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hab (h1.symm.trans h2)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact hsplit (fun z => fin3Equiv.symm (dec6 z).1 = 0) 0 3 (by decide) (by decide)
  · exact hsplit (fun z => fin3Equiv.symm (dec6 z).1 = 1) 1 4 (by decide) (by decide)
  · exact hsplit (fun z => fin3Equiv.symm (dec6 z).1 = 2) 2 5 (by decide) (by decide)
  · exact hsplit (fun z => fin3Equiv.symm ((dec6 z).1 + (dec6 z).2) = 0) 0 5 (by decide) (by decide)
  · exact hsplit (fun z => fin3Equiv.symm ((dec6 z).1 + (dec6 z).2) = 1) 1 3 (by decide) (by decide)
  · exact hsplit (fun z => fin3Equiv.symm ((dec6 z).1 + (dec6 z).2) = 2) 2 4 (by decide) (by decide)
  · exact hsplit (fun z => fin3Equiv.symm ((dec6 z).1 + 2 • (dec6 z).2) = 0) 0 4 (by decide) (by decide)
  · exact hsplit (fun z => fin3Equiv.symm ((dec6 z).1 + 2 • (dec6 z).2) = 1) 1 5 (by decide) (by decide)
  · exact hsplit (fun z => fin3Equiv.symm ((dec6 z).1 + 2 • (dec6 z).2) = 2) 2 3 (by decide) (by decide)

/-- Helper: integer mod `M` vanishes when `|x| < M / 2`. -/
lemma int_eq_zero_of_zmod_eq_zero {M : ℕ} {x : ℤ} (hM : 0 < M)
    (hx : (x : ZMod M) = 0) (habs : 2 * |x| < (M : ℤ)) : x = 0 := by
  have hdvd : (M : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x M).mp hx
  obtain ⟨q, rfl⟩ := hdvd
  by_contra h
  have hq : q ≠ 0 := fun h0 => h (by simp [h0])
  have h1 : 1 ≤ |q| := Int.one_le_abs hq
  have h2 : (M : ℤ) ≤ |(M : ℤ) * q| := by
    rw [abs_mul, abs_of_pos (Int.natCast_pos.mpr hM)]
    nlinarith
  omega

/-- Step 4–5 helper: lift `S_type` in the `R`-box into `ZMod M × ZMod M`, apply arithmetic triangle
    removal, and recover exact integer triples in `S_type³`. -/
lemma card_validInt_ge {n K : ℕ} (hK1 : 1 ≤ K) (hn : (60 * K + 60) ^ 2 ≤ n)
    (S_type : Finset (ℕ × ℕ)) {γ : ℝ} (hγ_pos : 0 < γ)
    (hS_box : ∀ t ∈ S_type, t.1 + t.2 ≤ n ∧
      |(t.1 : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ) ∧
      |(t.2 : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ) ∧
      |((n - t.1 - t.2 : ℕ) : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ))
    (hS_card : γ * (98 * (K : ℝ) ^ 2 * (n : ℝ)) ≤ (S_type.card : ℝ)) :
    27 * triangleRemovalBound (γ / 9) * (n : ℝ) ^ 2 ≤
      (((S_type ×ˢ S_type ×ˢ S_type).filter fun t =>
          t.2.2.1 + t.2.1.2 = t.1.1 + t.1.2 ∧ t.2.2.1 + t.2.2.2 = t.2.1.1 + t.1.2).card : ℝ) := by
  let s : ℕ := Nat.sqrt n
  have hs_lo : 60 * K + 60 ≤ s := by
    have h := Nat.sqrt_le_sqrt hn; rw [sq, Nat.sqrt_eq] at h; exact h
  have hs2_le : s ^ 2 ≤ n := by simpa [sq] using Nat.sqrt_le n
  have hn_lt_s1 : n < (s + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt n
  have hs1_sq_le : ((s + 1 : ℕ) : ℝ) ^ 2 ≤ 2 * (n : ℝ) := by
    have h1 : (s + 1) ^ 2 ≤ 2 * s ^ 2 := by nlinarith
    exact_mod_cast (h1.trans (by omega : 2 * s ^ 2 ≤ 2 * n))
  let R : ℕ := K * (s + 1)
  let a_c : ℕ := n / 3
  let M : ℕ := 6 * R + 15
  have : NeZero M := ⟨by omega⟩
  let toG : ℕ × ℕ → ZMod M × ZMod M :=
    fun t => ((((t.1 : ℤ) - (a_c : ℤ) : ℤ) : ZMod M), (((t.2 : ℤ) - (a_c : ℤ) : ℤ) : ZMod M))
  have hS_bounds : ∀ t ∈ S_type,
      |(t.1 : ℤ) - (a_c : ℤ)| ≤ (R : ℤ) + 1 ∧
      |(t.2 : ℤ) - (a_c : ℤ)| ≤ (R : ℤ) + 1 ∧
      |((t.1 : ℤ) - (a_c : ℤ)) + ((t.2 : ℤ) - (a_c : ℤ))| ≤ (R : ℤ) + 2 := by
    intro t ht
    obtain ⟨hle, h0, h1, h2⟩ := hS_box t ht
    have ha_lo : (3 : ℝ) * ((a_c : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.mul_div_le n 3
    have ha_hi : (n : ℝ) < (3 : ℝ) * ((a_c : ℕ) : ℝ) + 3 := by
      exact_mod_cast (show n < 3 * a_c + 3 by omega)
    rw [abs_le] at h0 h1 h2
    have hc_eq : ((n - t.1 - t.2 : ℕ) : ℝ) = (n : ℝ) - (t.1 : ℝ) - (t.2 : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [hc_eq] at h2
    refine ⟨?_, ?_, ?_⟩
    · rw [abs_le]
      have : -((R : ℝ) + 1) ≤ (t.1 : ℝ) - (a_c : ℝ) ∧ (t.1 : ℝ) - (a_c : ℝ) ≤ (R : ℝ) + 1 :=
        ⟨by linarith, by linarith⟩
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
    · rw [abs_le]
      have : -((R : ℝ) + 1) ≤ (t.2 : ℝ) - (a_c : ℝ) ∧ (t.2 : ℝ) - (a_c : ℝ) ≤ (R : ℝ) + 1 :=
        ⟨by linarith, by linarith⟩
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
    · rw [abs_le]
      have : -((R : ℝ) + 2) ≤ ((t.1 : ℝ) - (a_c : ℝ)) + ((t.2 : ℝ) - (a_c : ℝ)) ∧
          ((t.1 : ℝ) - (a_c : ℝ)) + ((t.2 : ℝ) - (a_c : ℝ)) ≤ (R : ℝ) + 2 :=
        ⟨by linarith, by linarith⟩
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  have htoG_inj : Set.InjOn toG (S_type : Set (ℕ × ℕ)) := by
    intro t₁ ht₁ t₂ ht₂ heq
    have hb1 := hS_bounds t₁ ht₁
    have hb2 := hS_bounds t₂ ht₂
    simp only [toG, Prod.mk.injEq] at heq
    have h1 : (((t₁.1 : ℤ) - (t₂.1 : ℤ) : ℤ) : ZMod M) = 0 := by
      rw [show (t₁.1 : ℤ) - (t₂.1 : ℤ) = ((t₁.1 : ℤ) - (a_c : ℤ)) - ((t₂.1 : ℤ) - (a_c : ℤ)) by ring,
        Int.cast_sub, heq.1, sub_self]
    have h2 : (((t₁.2 : ℤ) - (t₂.2 : ℤ) : ℤ) : ZMod M) = 0 := by
      rw [show (t₁.2 : ℤ) - (t₂.2 : ℤ) = ((t₁.2 : ℤ) - (a_c : ℤ)) - ((t₂.2 : ℤ) - (a_c : ℤ)) by ring,
        Int.cast_sub, heq.2, sub_self]
    have hz1 : (t₁.1 : ℤ) - (t₂.1 : ℤ) = 0 := by
      apply int_eq_zero_of_zmod_eq_zero (by omega) h1
      have : |(t₁.1 : ℤ) - (t₂.1 : ℤ)| ≤ |(t₁.1 : ℤ) - (a_c : ℤ)| + |(t₂.1 : ℤ) - (a_c : ℤ)| := by
        rw [show (t₁.1 : ℤ) - (t₂.1 : ℤ) = ((t₁.1 : ℤ) - (a_c : ℤ)) - ((t₂.1 : ℤ) - (a_c : ℤ)) by ring]
        exact abs_sub _ _
      omega
    have hz2 : (t₁.2 : ℤ) - (t₂.2 : ℤ) = 0 := by
      apply int_eq_zero_of_zmod_eq_zero (by omega) h2
      have : |(t₁.2 : ℤ) - (t₂.2 : ℤ)| ≤ |(t₁.2 : ℤ) - (a_c : ℤ)| + |(t₂.2 : ℤ) - (a_c : ℤ)| := by
        rw [show (t₁.2 : ℤ) - (t₂.2 : ℤ) = ((t₁.2 : ℤ) - (a_c : ℤ)) - ((t₂.2 : ℤ) - (a_c : ℤ)) by ring]
        exact abs_sub _ _
      omega
    exact Prod.ext (by omega) (by omega)
  let S_G : Finset (ZMod M × ZMod M) := S_type.image toG
  have hS_G_card : S_G.card = S_type.card := Finset.card_image_of_injOn htoG_inj
  have hG_card_eq : (Fintype.card (ZMod M × ZMod M) : ℝ) = (M : ℝ) ^ 2 := by
    simp [ZMod.card, sq]
  have hG_upper : (Fintype.card (ZMod M × ZMod M) : ℝ) ≤ 98 * (K : ℝ) ^ 2 * (n : ℝ) := by
    rw [hG_card_eq]
    have hM_le : (M : ℝ) ≤ 7 * (K : ℝ) * ((s + 1 : ℕ) : ℝ) := by
      have : M ≤ 7 * K * (s + 1) := by simp only [M, R]; nlinarith
      exact_mod_cast this
    calc (M : ℝ) ^ 2 ≤ (7 * (K : ℝ) * ((s + 1 : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hM_le 2
      _ = 49 * (K : ℝ) ^ 2 * ((s + 1 : ℕ) : ℝ) ^ 2 := by ring
      _ ≤ 49 * (K : ℝ) ^ 2 * (2 * (n : ℝ)) := by gcongr
      _ = 98 * (K : ℝ) ^ 2 * (n : ℝ) := by ring
  have hG_lower : (n : ℝ) ≤ (Fintype.card (ZMod M × ZMod M) : ℝ) := by
    rw [hG_card_eq]
    have : n ≤ M ^ 2 := by
      have h1 : s + 1 ≤ M := by simp only [M, R]; nlinarith
      exact hn_lt_s1.le.trans (Nat.pow_le_pow_left h1 2)
    exact_mod_cast this
  have hS_G_dens : γ * (Fintype.card (ZMod M × ZMod M) : ℝ) ≤ (S_G.card : ℝ) := by
    rw [hS_G_card]
    exact (mul_le_mul_of_nonneg_left hG_upper hγ_pos.le).trans hS_card
  have htri_G := card_rot_triples_ge S_G hγ_pos hS_G_dens
  set ValidInt : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
    (S_type ×ˢ S_type ×ˢ S_type).filter fun t =>
      t.2.2.1 + t.2.1.2 = t.1.1 + t.1.2 ∧ t.2.2.1 + t.2.2.2 = t.2.1.1 + t.1.2
  let map3 : ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) → (ZMod M × ZMod M) × (ZMod M × ZMod M) × (ZMod M × ZMod M) :=
    fun t => (toG t.1, toG t.2.1, toG t.2.2)
  have hsub3 : ((S_G ×ˢ S_G ×ˢ S_G).filter fun q => rot2 q.1 - rot q.2.1 + q.2.2 = 0) ⊆
      ValidInt.image map3 := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, S_G, Finset.mem_image] at hq
    obtain ⟨⟨⟨t₀, ht₀, hq₀⟩, ⟨t₁, ht₁, hq₁⟩, ⟨t₂, ht₂, hq₂⟩⟩, heq⟩ := hq
    rw [← hq₀, ← hq₁, ← hq₂] at heq
    have hb0 := hS_bounds t₀ ht₀
    have hb1 := hS_bounds t₁ ht₁
    have hb2 := hS_bounds t₂ ht₂
    let u₀ : ℤ := (t₀.1 : ℤ) - a_c; let v₀ : ℤ := (t₀.2 : ℤ) - a_c
    let u₁ : ℤ := (t₁.1 : ℤ) - a_c; let v₁ : ℤ := (t₁.2 : ℤ) - a_c
    let u₂ : ℤ := (t₂.1 : ℤ) - a_c; let v₂ : ℤ := (t₂.2 : ℤ) - a_c
    have hcoord1 : (((-u₀ - v₀ + v₁ + u₂ : ℤ)) : ZMod M) = 0 := by
      have := congrArg Prod.fst heq
      simp only [toG, rot, rot2, Prod.fst_sub, Prod.fst_add, Prod.fst_zero] at this
      push_cast; linear_combination this
    have hcoord2 : (((u₀ - u₁ - v₁ + v₂ : ℤ)) : ZMod M) = 0 := by
      have := congrArg Prod.snd heq
      simp only [toG, rot, rot2, Prod.snd_sub, Prod.snd_add, Prod.snd_zero] at this
      push_cast; linear_combination this
    have hz1 : -u₀ - v₀ + v₁ + u₂ = 0 := by
      apply int_eq_zero_of_zmod_eq_zero (by omega) hcoord1
      have h1 : |-u₀ - v₀ + v₁ + u₂| ≤ |u₀ + v₀| + |v₁| + |u₂| := by
        have ha : -u₀ - v₀ + v₁ + u₂ = -(u₀ + v₀) + v₁ + u₂ := by ring
        rw [ha]
        calc |-(u₀ + v₀) + v₁ + u₂| ≤ |-(u₀ + v₀) + v₁| + |u₂| := abs_add_le _ _
          _ ≤ |-(u₀ + v₀)| + |v₁| + |u₂| := by linarith [abs_add_le (-(u₀ + v₀)) v₁]
          _ = |u₀ + v₀| + |v₁| + |u₂| := by rw [abs_neg]
      have hb0_3 : |u₀ + v₀| ≤ (R : ℤ) + 2 := hb0.2.2
      have hb1_2 : |v₁| ≤ (R : ℤ) + 1 := hb1.2.1
      have hb2_1 : |u₂| ≤ (R : ℤ) + 1 := hb2.1
      have hM_eq : (M : ℤ) = 6 * (R : ℤ) + 15 := by simp [M]
      linarith
    have hz2 : u₀ - u₁ - v₁ + v₂ = 0 := by
      apply int_eq_zero_of_zmod_eq_zero (by omega) hcoord2
      have h2 : |u₀ - u₁ - v₁ + v₂| ≤ |u₀| + |u₁ + v₁| + |v₂| := by
        have ha : u₀ - u₁ - v₁ + v₂ = (u₀ - (u₁ + v₁)) + v₂ := by ring
        rw [ha]
        calc |(u₀ - (u₁ + v₁)) + v₂| ≤ |u₀ - (u₁ + v₁)| + |v₂| := abs_add_le _ _
          _ ≤ |u₀| + |u₁ + v₁| + |v₂| := by linarith [abs_sub u₀ (u₁ + v₁)]
      have hb0_1 : |u₀| ≤ (R : ℤ) + 1 := hb0.1
      have hb1_3 : |u₁ + v₁| ≤ (R : ℤ) + 2 := hb1.2.2
      have hb2_2 : |v₂| ≤ (R : ℤ) + 1 := hb2.2.1
      have hM_eq : (M : ℤ) = 6 * (R : ℤ) + 15 := by simp [M]
      linarith
    rw [Finset.mem_image]
    refine ⟨(t₀, t₁, t₂), ?_, by simp [map3, hq₀, hq₁, hq₂]⟩
    simp only [ValidInt, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨ht₀, ht₁, ht₂⟩, by omega, by omega⟩
  have hcard3 : ((S_G ×ˢ S_G ×ˢ S_G).filter fun q => rot2 q.1 - rot q.2.1 + q.2.2 = 0).card ≤
      ValidInt.card := (Finset.card_le_card hsub3).trans Finset.card_image_le
  have htrb_pos : 0 < triangleRemovalBound (γ / 9) := triangleRemovalBound_pos (by positivity)
  calc 27 * triangleRemovalBound (γ / 9) * (n : ℝ) ^ 2
      ≤ 27 * triangleRemovalBound (γ / 9) * (Fintype.card (ZMod M × ZMod M) : ℝ) ^ 2 := by gcongr
    _ ≤ (((S_G ×ˢ S_G ×ˢ S_G).filter fun q => rot2 q.1 - rot q.2.1 + q.2.2 = 0).card : ℝ) := htri_G
    _ ≤ (ValidInt.card : ℝ) := by exact_mod_cast hcard3

/-- The 6-nomial count vector associated to a valid triple `(t₀, t₁, t₂)` and free parameter `p`. -/
def makeC6 (n : ℕ) (q : ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) × ℕ) : Fin 6 → ℕ :=
  let t₀ := q.1.1
  let t₁ := q.1.2.1
  let t₂ := q.1.2.2
  let p := q.2
  ![t₀.1 - p, t₁.2 - p, n - t₂.1 - t₂.2 - p, p, p + t₂.1 - t₀.1, p + t₁.1 - t₀.1]

/-- Helper verifying sum, box-distance, and `Good`-membership for `makeC6`. -/
lemma makeC6_ok {n K : ℕ} (hK1 : 1 ≤ K) (hn : (60 * K + 60) ^ 2 ≤ n)
    (A : Finset (Fin n → ZMod 3)) (S_type : Finset (ℕ × ℕ))
    (hS_props : ∀ t ∈ S_type,
      t.1 + t.2 ≤ n ∧
      (∀ x : Fin n → ZMod 3,
        finCount (fun i => fin3Equiv.symm (x i)) 0 = t.1 →
        finCount (fun i => fin3Equiv.symm (x i)) 1 = t.2 → x ∈ A) ∧
      |(t.1 : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ) ∧
      |(t.2 : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ) ∧
      |((n - t.1 - t.2 : ℕ) : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ))
    {t₀ t₁ t₂ : ℕ × ℕ} {p : ℕ}
    (ht₀ : t₀ ∈ S_type) (ht₁ : t₁ ∈ S_type) (ht₂ : t₂ ∈ S_type)
    (heq1 : t₂.1 + t₁.2 = t₀.1 + t₀.2) (heq2 : t₂.1 + t₂.2 = t₁.1 + t₀.2)
    (hp_lo : n / 6 - Nat.sqrt n ≤ p) (hp_hi : p ≤ n / 6 + Nat.sqrt n) :
    (∑ j, makeC6 n ((t₀, t₁, t₂), p) j = n) ∧
    (∀ j, |(makeC6 n ((t₀, t₁, t₂), p) j : ℝ) - (n : ℝ) / 6| ≤
      (2 * (K : ℝ) + 2) * ((Nat.sqrt n + 1 : ℕ) : ℝ)) ∧
    (∀ f : Fin n → Fin 6, (∀ j, finCount f j = makeC6 n ((t₀, t₁, t₂), p) j) →
      (fun i => (dec6 (f i)).1, fun i => (dec6 (f i)).2) ∈
        Finset.univ.filter fun p : (Fin n → ZMod 3) × (Fin n → ZMod 3) =>
          (∀ i, p.2 i = 0 ∨ p.2 i = 1) ∧ p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + 2 • p.2 ∈ A) := by
  let s : ℕ := Nat.sqrt n
  have hs_lo : 60 * K + 60 ≤ s := by
    have h := Nat.sqrt_le_sqrt hn; rw [sq, Nat.sqrt_eq] at h; exact h
  have hs2_le : s ^ 2 ≤ n := by simpa [sq] using Nat.sqrt_le n
  let R : ℕ := K * (s + 1)
  let D6 : ℝ := (2 * (K : ℝ) + 2) * ((s + 1 : ℕ) : ℝ)
  have hR_bound : 12 * (2 * R + s + 10) ≤ n := by
    have : 12 * (2 * R + s + 10) ≤ s ^ 2 := by simp only [R]; nlinarith
    exact this.trans hs2_le
  have hR_real : (12 : ℝ) * (2 * (R : ℝ) + (s : ℝ) + 10) ≤ (n : ℝ) := by exact_mod_cast hR_bound
  have hD6_ge : 2 * (R : ℝ) + (s : ℝ) + 2 ≤ D6 := by
    simp only [D6, R, Nat.cast_mul, Nat.cast_add, Nat.cast_one]; linarith
  have h6_lo : (6 : ℝ) * ((n / 6 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.mul_div_le n 6
  have h6_hi : (n : ℝ) < (6 : ℝ) * ((n / 6 : ℕ) : ℝ) + 6 := by
    exact_mod_cast (show n < 6 * (n / 6) + 6 by omega)
  obtain ⟨hle0, hA0, hb00, hb01, hb02⟩ := hS_props t₀ ht₀
  obtain ⟨hle1, hA1, hb10, hb11, hb12⟩ := hS_props t₁ ht₁
  obtain ⟨hle2, hA2, hb20, hb21, hb22⟩ := hS_props t₂ ht₂
  rw [abs_le] at hb00 hb01 hb02 hb10 hb11 hb12 hb20 hb21 hb22
  have hp_real_lo : (n : ℝ) / 6 - (s : ℝ) - 1 ≤ (p : ℝ) := by
    have : ((n / 6 : ℕ) : ℝ) ≤ (p : ℝ) + (s : ℝ) := by exact_mod_cast (show n / 6 ≤ p + s by omega)
    linarith
  have hp_real_hi : (p : ℝ) ≤ (n : ℝ) / 6 + (s : ℝ) := by
    have : (p : ℝ) ≤ ((n / 6 : ℕ) : ℝ) + (s : ℝ) := by exact_mod_cast hp_hi
    linarith
  have hp_le_t01 : p ≤ t₀.1 := by exact_mod_cast (show (p : ℝ) ≤ (t₀.1 : ℝ) by linarith)
  have hp_le_t12 : p ≤ t₁.2 := by exact_mod_cast (show (p : ℝ) ≤ (t₁.2 : ℝ) by linarith)
  have hp_le_t2c : p ≤ n - t₂.1 - t₂.2 := by
    exact_mod_cast (show (p : ℝ) ≤ ((n - t₂.1 - t₂.2 : ℕ) : ℝ) by linarith)
  have ht01_le_pt21 : t₀.1 ≤ p + t₂.1 := by
    exact_mod_cast (show (t₀.1 : ℝ) ≤ (p : ℝ) + (t₂.1 : ℝ) by linarith)
  have ht01_le_pt11 : t₀.1 ≤ p + t₁.1 := by
    exact_mod_cast (show (t₀.1 : ℝ) ≤ (p : ℝ) + (t₁.1 : ℝ) by linarith)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_six, makeC6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    omega
  · intro j
    fin_cases j
    · change |((t₀.1 - p : ℕ) : ℝ) - (n : ℝ) / 6| ≤ D6
      rw [Nat.cast_sub hp_le_t01, abs_le]; constructor <;> linarith
    · change |((t₁.2 - p : ℕ) : ℝ) - (n : ℝ) / 6| ≤ D6
      rw [Nat.cast_sub hp_le_t12, abs_le]; constructor <;> linarith
    · change |((n - t₂.1 - t₂.2 - p : ℕ) : ℝ) - (n : ℝ) / 6| ≤ D6
      rw [Nat.cast_sub hp_le_t2c, abs_le]; constructor <;> linarith
    · change |(p : ℝ) - (n : ℝ) / 6| ≤ D6
      rw [abs_le]; constructor <;> linarith
    · change |((p + t₂.1 - t₀.1 : ℕ) : ℝ) - (n : ℝ) / 6| ≤ D6
      rw [Nat.cast_sub ht01_le_pt21, Nat.cast_add, abs_le]; constructor <;> linarith
    · change |((p + t₁.1 - t₀.1 : ℕ) : ℝ) - (n : ℝ) / 6| ≤ D6
      rw [Nat.cast_sub ht01_le_pt11, Nat.cast_add, abs_le]; constructor <;> linarith
  · intro f hf
    have hc := counts_of_dec6 f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun i => dec6_snd_mem (f i), ?_, ?_, ?_⟩
    · exact hA0 _
        (by rw [hc.1.1, hf 0, hf 3]; simp only [makeC6, Matrix.cons_val_zero, Matrix.cons_val]; omega)
        (by rw [hc.1.2.1, hf 1, hf 4]; simp only [makeC6, Matrix.cons_val]; omega)
    · exact hA1 _
        (by rw [hc.2.1.1, hf 0, hf 5]; simp only [makeC6, Matrix.cons_val_zero, Matrix.cons_val]; omega)
        (by rw [hc.2.1.2.1, hf 1, hf 3]; simp only [makeC6, Matrix.cons_val]; omega)
    · exact hA2 _
        (by rw [hc.2.2.1, hf 0, hf 4]; simp only [makeC6, Matrix.cons_val_zero, Matrix.cons_val]; omega)
        (by rw [hc.2.2.2.1, hf 1, hf 5]; simp only [makeC6, Matrix.cons_val]; omega)

/-- Step 6 helper: from integer triples in `ValidInt`, build disjoint 6-nomial fibers in `Good`. -/
lemma card_good_ge_of_validInt {n K : ℕ} (hK1 : 1 ≤ K) (hn : (60 * K + 60) ^ 2 ≤ n)
    (A : Finset (Fin n → ZMod 3)) (S_type : Finset (ℕ × ℕ))
    (hS_props : ∀ t ∈ S_type,
      t.1 + t.2 ≤ n ∧
      (∀ x : Fin n → ZMod 3,
        finCount (fun i => fin3Equiv.symm (x i)) 0 = t.1 →
        finCount (fun i => fin3Equiv.symm (x i)) 1 = t.2 → x ∈ A) ∧
      |(t.1 : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ) ∧
      |(t.2 : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ) ∧
      |((n - t.1 - t.2 : ℕ) : ℝ) - (n : ℝ) / 3| ≤ ((K * (Nat.sqrt n + 1) : ℕ) : ℝ)) :
    ((((S_type ×ˢ S_type ×ˢ S_type).filter fun t =>
          t.2.2.1 + t.2.1.2 = t.1.1 + t.1.2 ∧ t.2.2.1 + t.2.2.2 = t.2.1.1 + t.1.2).card : ℝ) *
        (Nat.sqrt n : ℝ)) *
      ((1 / 2 : ℝ) / ((9 : ℝ) ^ 5 * Real.exp (288 * 9 + 288 * (2 * (K : ℝ) + 2) ^ 2)) *
        (6 : ℝ) ^ n / ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 5) ≤
      ((Finset.univ.filter fun p : (Fin n → ZMod 3) × (Fin n → ZMod 3) =>
          (∀ i, p.2 i = 0 ∨ p.2 i = 1) ∧ p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + 2 • p.2 ∈ A).card : ℝ) := by
  let s : ℕ := Nat.sqrt n
  have hs_lo : 60 * K + 60 ≤ s := by
    have h := Nat.sqrt_le_sqrt hn; rw [sq, Nat.sqrt_eq] at h; exact h
  have hs2_le : s ^ 2 ≤ n := by simpa [sq] using Nat.sqrt_le n
  let D6 : ℝ := (2 * (K : ℝ) + 2) * ((s + 1 : ℕ) : ℝ)
  let c₆ : ℝ := (1 / 2 : ℝ) / ((9 : ℝ) ^ 5 * Real.exp (288 * 9 + 288 * (2 * (K : ℝ) + 2) ^ 2))
  set Good := Finset.univ.filter fun p : (Fin n → ZMod 3) × (Fin n → ZMod 3) =>
    (∀ i, p.2 i = 0 ∨ p.2 i = 1) ∧ p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + 2 • p.2 ∈ A
  set ValidInt : Finset ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) :=
    (S_type ×ˢ S_type ×ˢ S_type).filter fun t =>
      t.2.2.1 + t.2.1.2 = t.1.1 + t.1.2 ∧ t.2.2.1 + t.2.2.2 = t.2.1.1 + t.1.2
  let P_range : Finset ℕ := Finset.Icc (n / 6 - s) (n / 6 + s)
  have hP_card : s ≤ P_range.card := by rw [Nat.card_Icc]; omega
  have hmakeC6_ok : ∀ q ∈ ValidInt ×ˢ P_range,
      (∑ j, makeC6 n q j = n) ∧
      (∀ j, |(makeC6 n q j : ℝ) - (n : ℝ) / 6| ≤ D6) ∧
      (∀ f : Fin n → Fin 6, (∀ j, finCount f j = makeC6 n q j) →
        (fun i => (dec6 (f i)).1, fun i => (dec6 (f i)).2) ∈ Good) := by
    rintro ⟨⟨t₀, t₁, t₂⟩, p⟩ hq
    simp only [Finset.mem_product, ValidInt, Finset.mem_filter, P_range, Finset.mem_Icc] at hq
    exact makeC6_ok hK1 hn A S_type hS_props hq.1.1.1 hq.1.1.2.1 hq.1.1.2.2 hq.1.2.1 hq.1.2.2 hq.2.1 hq.2.2
  have hD6_lt : D6 < (n : ℝ) / 6 := by
    have : 12 * (2 * K + 2) * (s + 1) ≤ s ^ 2 := by nlinarith
    have : (12 : ℝ) * (2 * (K : ℝ) + 2) * ((s + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (this.trans hs2_le)
    have hD6_pos : 0 < D6 := by positivity
    simp only [D6] at hD6_pos ⊢; linarith
  have hmakeC6_inj : Set.InjOn (makeC6 n) ((ValidInt ×ˢ P_range : Finset _) : Set _) := by
    rintro ⟨⟨t₀, t₁, t₂⟩, p⟩ hq ⟨⟨t₀', t₁', t₂'⟩, p'⟩ hq' heq
    rw [Finset.mem_coe] at hq hq'
    have h0 := congrFun heq 0; have h1 := congrFun heq 1; have h3 := congrFun heq 3
    have h4 := congrFun heq 4; have h5 := congrFun heq 5
    simp only [makeC6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0 h1 h3 h4 h5
    subst h3
    have hpos_q : ∀ j, 0 < makeC6 n ⟨⟨t₀, t₁, t₂⟩, p⟩ j := fun j => by
      have hj := (hmakeC6_ok _ hq).2.1 j; rw [abs_le] at hj
      exact_mod_cast (show (0 : ℝ) < (makeC6 n ⟨⟨t₀, t₁, t₂⟩, p⟩ j : ℝ) by linarith)
    have hpos_q' : ∀ j, 0 < makeC6 n ⟨⟨t₀', t₁', t₂'⟩, p⟩ j := fun j => by
      have hj := (hmakeC6_ok _ hq').2.1 j; rw [abs_le] at hj
      exact_mod_cast (show (0 : ℝ) < (makeC6 n ⟨⟨t₀', t₁', t₂'⟩, p⟩ j : ℝ) by linarith)
    have h0p := hpos_q 0; have h1p := hpos_q 1; have h4p := hpos_q 4; have h5p := hpos_q 5
    have h0p' := hpos_q' 0; have h1p' := hpos_q' 1; have h4p' := hpos_q' 4; have h5p' := hpos_q' 5
    simp only [makeC6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h0p h1p h4p h5p h0p' h1p' h4p' h5p'
    simp only [Finset.mem_product, ValidInt, Finset.mem_filter] at hq hq'
    have ht01 : t₀.1 = t₀'.1 := by omega
    have ht12 : t₁.2 = t₁'.2 := by omega
    have ht21 : t₂.1 = t₂'.1 := by omega
    have ht11 : t₁.1 = t₁'.1 := by omega
    have ht02 : t₀.2 = t₀'.2 := by omega
    have ht22 : t₂.2 = t₂'.2 := by omega
    exact Prod.ext (Prod.ext (Prod.ext ht01 ht02) (Prod.ext (Prod.ext ht11 ht12) (Prod.ext ht21 ht22))) rfl
  let dec6Map : (Fin n → Fin 6) ↪ (Fin n → ZMod 3) × (Fin n → ZMod 3) :=
    ⟨fun f => (fun i => (dec6 (f i)).1, fun i => (dec6 (f i)).2), fun f₁ f₂ h => by
      funext i
      exact dec6_injective (Prod.ext (congrFun (congrArg Prod.fst h) i) (congrFun (congrArg Prod.snd h) i))⟩
  let BigUnion : Finset (Fin n → Fin 6) :=
    (ValidInt ×ˢ P_range).biUnion fun q =>
      Finset.univ.filter fun f : Fin n → Fin 6 => ∀ j, finCount f j = makeC6 n q j
  have hBigUnion_sub : BigUnion.map dec6Map ⊆ Good := by
    intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨f, hf, rfl⟩ := hp
    rw [Finset.mem_biUnion] at hf
    obtain ⟨q, hq, hf_eq⟩ := hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf_eq
    exact (hmakeC6_ok q hq).2.2 f hf_eq
  have hBigUnion_card : BigUnion.card = ∑ q ∈ ValidInt ×ˢ P_range,
      (Finset.univ.filter fun f : Fin n → Fin 6 => ∀ j, finCount f j = makeC6 n q j).card := by
    apply Finset.card_biUnion
    intro q₁ hq₁ q₂ hq₂ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro f hf1 hf2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf1 hf2
    exact hne (hmakeC6_inj hq₁ hq₂ (funext fun j => (hf1 j).symm.trans (hf2 j)))
  have hVP_le : (ValidInt.card : ℝ) * (s : ℝ) ≤ ((ValidInt ×ˢ P_range).card : ℝ) := by
    rw [Finset.card_product, Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hP_card) (Nat.cast_nonneg _)
  have hc₆_nn : 0 ≤ c₆ * (6 : ℝ) ^ n / ((s + 1 : ℕ) : ℝ) ^ 5 := by positivity
  calc ((ValidInt.card : ℝ) * (s : ℝ)) * (c₆ * (6 : ℝ) ^ n / ((s + 1 : ℕ) : ℝ) ^ 5)
      ≤ ((ValidInt ×ˢ P_range).card : ℝ) * (c₆ * (6 : ℝ) ^ n / ((s + 1 : ℕ) : ℝ) ^ 5) :=
        mul_le_mul_of_nonneg_right hVP_le hc₆_nn
    _ = ∑ _q ∈ ValidInt ×ˢ P_range, (c₆ * (6 : ℝ) ^ n / ((s + 1 : ℕ) : ℝ) ^ 5) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ q ∈ ValidInt ×ˢ P_range, multiWeight n (makeC6 n q) := by
        apply Finset.sum_le_sum
        intro q hq
        exact sixnomial_weight_lower hK1 hn (makeC6 n q) (hmakeC6_ok q hq).1 (hmakeC6_ok q hq).2.1
    _ = ∑ q ∈ ValidInt ×ˢ P_range,
          ((Finset.univ.filter fun f : Fin n → Fin 6 => ∀ j, finCount f j = makeC6 n q j).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro q hq
        exact (card_fiber_eq_multiWeight _ (hmakeC6_ok q hq).1).symm
    _ = (BigUnion.card : ℝ) := by rw [hBigUnion_card, Nat.cast_sum]
    _ = ((BigUnion.map dec6Map).card : ℝ) := by rw [Finset.card_map]
    _ ≤ (Good.card : ℝ) := by exact_mod_cast Finset.card_le_card hBigUnion_sub

/-- Main theorem (Hązła 2020, q = 3): every symmetric subset of `𝔽₃^n` of density `≥ μ > 0`
    has at least `δ(μ) * 6^n` restricted arithmetic progressions (counting `d = 0`). -/
theorem green_17_symmetric_main :
    ∀ μ : ℝ, 0 < μ → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ A : Finset (Fin n → ZMod 3),
      (∀ σ : Equiv.Perm (Fin n), ∀ x ∈ A, (fun i => x (σ i)) ∈ A) →
      μ * 3 ^ n ≤ (A.card : ℝ) →
      δ * 6 ^ n ≤
        ((Finset.univ.filter fun p : (Fin n → ZMod 3) × (Fin n → ZMod 3) =>
            (∀ i, p.2 i = 0 ∨ p.2 i = 1) ∧ p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + 2 • p.2 ∈ A).card : ℝ) := by
  intro μ hμ
  let K : ℕ := Nat.ceil (Real.sqrt (2 / μ)) + 1
  have hK1 : 1 ≤ K := Nat.le_add_left 1 _
  have hK_sq : 2 / μ ≤ (K : ℝ) ^ 2 := by
    have h1 : Real.sqrt (2 / μ) ≤ (K : ℝ) := by
      have := Nat.le_ceil (Real.sqrt (2 / μ))
      push_cast [K]; linarith
    calc 2 / μ = (Real.sqrt (2 / μ)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
      _ ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  let N₀ : ℕ := (60 * K + 60) ^ 2
  let E₃ : ℝ := 72 * ((K : ℝ) + 1) ^ 2
  let E₆ : ℝ := 288 * (2 * (K : ℝ) + 2) ^ 2
  let w₃_const : ℝ := 40 * Real.exp (72 + E₃)
  let γ : ℝ := μ / (2 * w₃_const * (98 * (K : ℝ) ^ 2))
  have hγ_pos : 0 < γ := by
    have hKpos : (0 : ℝ) < K := Nat.cast_pos.mpr (by omega)
    positivity
  let c₆ : ℝ := (1 / 2 : ℝ) / ((9 : ℝ) ^ 5 * Real.exp (288 * 9 + E₆))
  have hc₆_pos : 0 < c₆ := by positivity
  let δ_large : ℝ := (27 / 32 : ℝ) * triangleRemovalBound (γ / 9) * c₆
  have hδ_large_pos : 0 < δ_large := by
    have := triangleRemovalBound_pos (show 0 < γ / 9 by positivity)
    positivity
  let δ_small : ℝ := μ / (2 : ℝ) ^ N₀
  have hδ_small_pos : 0 < δ_small := by positivity
  refine ⟨min δ_small δ_large, lt_min hδ_small_pos hδ_large_pos, ?_⟩
  intro n A hsym hA
  set Good := Finset.univ.filter fun p : (Fin n → ZMod 3) × (Fin n → ZMod 3) =>
    (∀ i, p.2 i = 0 ∨ p.2 i = 1) ∧ p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + 2 • p.2 ∈ A
  -- Case 1: small n < N₀
  by_cases hn : n < N₀
  · have hA_le_Good : A.card ≤ Good.card := by
      let emb : (Fin n → ZMod 3) ↪ (Fin n → ZMod 3) × (Fin n → ZMod 3) :=
        ⟨fun x => (x, 0), fun _ _ h => congrArg Prod.fst h⟩
      calc A.card = (A.map emb).card := (Finset.card_map emb).symm
        _ ≤ Good.card := Finset.card_le_card (by
            intro p hp
            rw [Finset.mem_map] at hp
            obtain ⟨x, hx, rfl⟩ := hp
            change (x, (0 : Fin n → ZMod 3)) ∈ Good
            simp [Good, hx])
    have hpow2 : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ N₀ := pow_le_pow_right₀ (by norm_num) hn.le
    calc min δ_small δ_large * (6 : ℝ) ^ n
        ≤ δ_small * (6 : ℝ) ^ n := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = (μ / (2 : ℝ) ^ N₀) * ((2 : ℝ) ^ n * (3 : ℝ) ^ n) := by
          simp only [δ_small]; rw [← mul_pow]; norm_num
      _ ≤ (μ / (2 : ℝ) ^ n) * ((2 : ℝ) ^ n * (3 : ℝ) ^ n) := by gcongr
      _ = μ * (3 : ℝ) ^ n := by field_simp
      _ ≤ (A.card : ℝ) := hA
      _ ≤ (Good.card : ℝ) := by exact_mod_cast hA_le_Good
  -- Case 2: large n ≥ N₀
  push Not at hn
  set s : ℕ := Nat.sqrt n
  have hs_lo : 60 * K + 60 ≤ s := by
    have h := Nat.sqrt_le_sqrt hn; dsimp only [N₀] at h; rw [sq, Nat.sqrt_eq] at h; exact h
  have hs2_le : s ^ 2 ≤ n := by simpa [sq] using Nat.sqrt_le n
  have hn_lt_s1 : n < (s + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt n
  have hn_pos : 0 < n := by nlinarith
  let R : ℕ := K * (s + 1)
  have hR_pos : (0 : ℝ) < R := Nat.cast_pos.mpr (Nat.mul_pos (by omega) (by omega))
  -- Step 1: Identify A with Fin 3 functions
  let toFin3 : (Fin n → ZMod 3) ≃ (Fin n → Fin 3) := Equiv.arrowCongr (Equiv.refl _) fin3Equiv.symm
  let A3 : Finset (Fin n → Fin 3) := A.map toFin3.toEmbedding
  have hA3_card : A3.card = A.card := Finset.card_map _
  have hA3_sym : ∀ f g : Fin n → Fin 3, (∀ j, finCount f j = finCount g j) → (f ∈ A3 ↔ g ∈ A3) := by
    intro f g hfg
    simp only [A3, Finset.mem_map_equiv]
    have hxy : ∀ j : Fin 3, finCount (fun i => fin3Equiv.symm (toFin3.symm f i)) j =
        finCount (fun i => fin3Equiv.symm (toFin3.symm g i)) j := by
      intro j
      have hf' : (fun i => fin3Equiv.symm (toFin3.symm f i)) = f := by funext i; simp [toFin3]
      have hg' : (fun i => fin3Equiv.symm (toFin3.symm g i)) = g := by funext i; simp [toFin3]
      rw [hf', hg']; exact hfg j
    constructor
    · intro hf
      obtain ⟨σ, hσ⟩ := exists_perm_of_same_finCount (toFin3.symm f) (toFin3.symm g) hxy
      have := hsym σ _ hf
      rwa [show (fun i => toFin3.symm f (σ i)) = toFin3.symm g from funext hσ] at this
    · intro hg
      obtain ⟨σ, hσ⟩ := exists_perm_of_same_finCount (toFin3.symm g) (toFin3.symm f)
        (fun j => (hxy j).symm)
      have := hsym σ _ hg
      rwa [show (fun i => toFin3.symm g (σ i)) = toFin3.symm f from funext hσ] at this
  -- Step 2: Chebyshev concentration for k = 3
  let GoodBox3 : Finset (Fin n → Fin 3) :=
    Finset.univ.filter fun f => ∀ j : Fin 3, |(finCount f j : ℝ) - (n : ℝ) / 3| ≤ (R : ℝ)
  have hA3_box : (μ / 2) * (3 : ℝ) ^ n ≤ ((A3 ∩ GoodBox3).card : ℝ) := by
    have hbad3 : ((Finset.univ.filter fun f : Fin n → Fin 3 =>
        ∃ j : Fin 3, (R : ℝ) < |(finCount f j : ℝ) - (n : ℝ) / 3|).card : ℝ) ≤ (μ / 2) * 3 ^ n := by
      have hch := card_bad_finCount_le (k := 3) (n := n) (by omega) hR_pos
      have hR2 : (n : ℝ) / (R : ℝ) ^ 2 ≤ μ / 2 := by
        have h1 : (n : ℝ) ≤ ((s + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hn_lt_s1.le
        have h2 : (R : ℝ) ^ 2 = (K : ℝ) ^ 2 * ((s + 1 : ℕ) : ℝ) ^ 2 := by
          simp only [R, Nat.cast_mul]; ring
        rw [h2, div_le_iff₀ (by positivity)]
        calc (n : ℝ) ≤ ((s + 1 : ℕ) : ℝ) ^ 2 := h1
          _ = (μ / 2) * (2 / μ) * ((s + 1 : ℕ) : ℝ) ^ 2 := by field_simp
          _ ≤ (μ / 2) * (K : ℝ) ^ 2 * ((s + 1 : ℕ) : ℝ) ^ 2 := by gcongr
          _ = μ / 2 * ((K : ℝ) ^ 2 * ((s + 1 : ℕ) : ℝ) ^ 2) := by ring
      calc _ ≤ (n : ℝ) / (R : ℝ) ^ 2 * (3 : ℝ) ^ n := by simpa using hch
        _ ≤ (μ / 2) * (3 : ℝ) ^ n := by gcongr
    have hsub : A3 \ GoodBox3 ⊆ Finset.univ.filter fun f : Fin n → Fin 3 =>
        ∃ j : Fin 3, (R : ℝ) < |(finCount f j : ℝ) - (n : ℝ) / 3| := by
      intro f hf
      rw [Finset.mem_sdiff] at hf
      simp only [GoodBox3, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_le] at hf ⊢
      exact hf.2
    have h1 : (A3.card : ℝ) = ((A3 ∩ GoodBox3).card : ℝ) + ((A3 \ GoodBox3).card : ℝ) := by
      exact_mod_cast (Finset.card_inter_add_card_sdiff A3 GoodBox3).symm
    have h2 : ((A3 \ GoodBox3).card : ℝ) ≤ (μ / 2) * 3 ^ n :=
      (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hbad3
    rw [hA3_card] at h1
    linarith
  -- Step 3: Active types S_type in the R-box
  let S_type : Finset (ℕ × ℕ) :=
    (A3 ∩ GoodBox3).image fun f => (finCount f 0, finCount f 1)
  have hS_props : ∀ t ∈ S_type,
      t.1 + t.2 ≤ n ∧
      (∀ x : Fin n → ZMod 3,
        finCount (fun i => fin3Equiv.symm (x i)) 0 = t.1 →
        finCount (fun i => fin3Equiv.symm (x i)) 1 = t.2 → x ∈ A) ∧
      |(t.1 : ℝ) - (n : ℝ) / 3| ≤ (R : ℝ) ∧
      |(t.2 : ℝ) - (n : ℝ) / 3| ≤ (R : ℝ) ∧
      |((n - t.1 - t.2 : ℕ) : ℝ) - (n : ℝ) / 3| ≤ (R : ℝ) := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨f, hf, rfl⟩ := ht
    rw [Finset.mem_inter] at hf
    have hsum := sum_finCount f
    rw [Fin.sum_univ_three] at hsum
    have hf2 : finCount f 2 = n - finCount f 0 - finCount f 1 := by omega
    have hgb := (Finset.mem_filter.mp hf.2).2
    refine ⟨by omega, ?_, hgb 0, hgb 1, by rw [← hf2]; exact hgb 2⟩
    intro x hx0 hx1
    let g : Fin n → Fin 3 := fun i => fin3Equiv.symm (x i)
    have hg0 : finCount g 0 = finCount f 0 := hx0
    have hg1 : finCount g 1 = finCount f 1 := hx1
    have hgs := sum_finCount g
    rw [Fin.sum_univ_three] at hgs
    have hg2 : finCount g 2 = finCount f 2 := by omega
    have hgA3 : g ∈ A3 := (hA3_sym f g (fun j => by fin_cases j <;> simp [hg0, hg1, hg2])).mp hf.1
    have hgx : toFin3.symm g = x := by funext i; simp [toFin3, g]
    rw [← hgx]
    exact (Finset.mem_map_equiv (f := toFin3)).mp hgA3
  have hS_type_card : (μ / (2 * w₃_const)) * (n : ℝ) ≤ (S_type.card : ℝ) := by
    have hsum_le : ((A3 ∩ GoodBox3).card : ℝ) ≤
        (S_type.card : ℝ) * (w₃_const * (3 : ℝ) ^ n / (n : ℝ)) := by
      have hpart : (A3 ∩ GoodBox3).card ≤
          ∑ t ∈ S_type, (Finset.univ.filter fun f : Fin n → Fin 3 =>
            ∀ j, finCount f j = ![t.1, t.2, n - t.1 - t.2] j).card := by
        calc (A3 ∩ GoodBox3).card
            ≤ (S_type.biUnion fun t => Finset.univ.filter fun f : Fin n → Fin 3 =>
                ∀ j, finCount f j = ![t.1, t.2, n - t.1 - t.2] j).card := by
              apply Finset.card_le_card
              intro f hf
              rw [Finset.mem_biUnion]
              refine ⟨(finCount f 0, finCount f 1), Finset.mem_image_of_mem _ hf, ?_⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              have hsum := sum_finCount f
              rw [Fin.sum_univ_three] at hsum
              intro j; fin_cases j <;> (simp; try omega)
          _ ≤ _ := Finset.card_biUnion_le
      calc ((A3 ∩ GoodBox3).card : ℝ)
          ≤ ∑ t ∈ S_type, ((Finset.univ.filter fun f : Fin n → Fin 3 =>
              ∀ j, finCount f j = ![t.1, t.2, n - t.1 - t.2] j).card : ℝ) := by
            exact_mod_cast hpart
        _ = ∑ t ∈ S_type, multiWeight n ![t.1, t.2, n - t.1 - t.2] := by
            apply Finset.sum_congr rfl
            intro t ht
            have hle := (hS_props t ht).1
            exact card_fiber_eq_multiWeight _ (by simp [Fin.sum_univ_three]; omega)
        _ ≤ ∑ _t ∈ S_type, (w₃_const * (3 : ℝ) ^ n / (n : ℝ)) := by
            apply Finset.sum_le_sum
            intro t ht
            obtain ⟨hle, _, h0, h1, h2⟩ := hS_props t ht
            exact trinomial_weight_upper hK1 hn ![t.1, t.2, n - t.1 - t.2]
              (by simp [Fin.sum_univ_three]; omega)
              (fun j => match j with
                | ⟨0, _⟩ => h0
                | ⟨1, _⟩ => h1
                | ⟨2, _⟩ => h2)
        _ = (S_type.card : ℝ) * (w₃_const * (3 : ℝ) ^ n / (n : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcomb := hA3_box.trans hsum_le
    have hpos1 : 0 < w₃_const := by positivity
    have hpos2 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    have hpos3 : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    have hrew : (S_type.card : ℝ) * (w₃_const * (3 : ℝ) ^ n / (n : ℝ)) =
        (S_type.card : ℝ) * w₃_const * (3 : ℝ) ^ n / (n : ℝ) := by ring
    rw [hrew, le_div_iff₀ hpos3] at hcomb
    have h2 : (μ / 2) * (n : ℝ) ≤ (S_type.card : ℝ) * w₃_const :=
      le_of_mul_le_mul_right (by linarith) hpos2
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  -- Step 4–5: Apply `card_validInt_ge`
  have hS_dens : γ * (98 * (K : ℝ) ^ 2 * (n : ℝ)) ≤ (S_type.card : ℝ) := by
    have hEq : γ * (98 * (K : ℝ) ^ 2 * (n : ℝ)) = (μ / (2 * w₃_const)) * (n : ℝ) := by
      simp only [γ]
      have hKne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hne : w₃_const ≠ 0 := by positivity
      field_simp
    rwa [hEq]
  have hValidInt_ge := card_validInt_ge hK1 hn S_type hγ_pos
    (fun t ht => let ⟨h1, _, h2, h3, h4⟩ := hS_props t ht; ⟨h1, h2, h3, h4⟩) hS_dens
  -- Step 6: Apply `card_good_ge_of_validInt`
  have hGood_ge := card_good_ge_of_validInt hK1 hn A S_type hS_props
  have hs5_ratio : (1 / 32 : ℝ) ≤ (n : ℝ) ^ 2 * (s : ℝ) / ((s + 1 : ℕ) : ℝ) ^ 5 := by
    have h1 : s + 1 ≤ 2 * s := by omega
    have h2 : (s + 1) ^ 5 ≤ 32 * s ^ 5 := by
      calc (s + 1) ^ 5 ≤ (2 * s) ^ 5 := Nat.pow_le_pow_left h1 5
        _ = 32 * s ^ 5 := by ring
    have h3 : s ^ 5 ≤ n ^ 2 * s := by
      have : s ^ 4 ≤ n ^ 2 := by
        calc s ^ 4 = (s ^ 2) ^ 2 := by ring
          _ ≤ n ^ 2 := Nat.pow_le_pow_left hs2_le 2
      calc s ^ 5 = s ^ 4 * s := by ring
        _ ≤ n ^ 2 * s := Nat.mul_le_mul_right s this
    have h4 : ((s + 1 : ℕ) : ℝ) ^ 5 ≤ 32 * ((n : ℝ) ^ 2 * (s : ℝ)) := by
      exact_mod_cast (h2.trans (Nat.mul_le_mul_left 32 h3))
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have htrb_pos : 0 < triangleRemovalBound (γ / 9) := triangleRemovalBound_pos (by positivity)
  calc min δ_small δ_large * (6 : ℝ) ^ n
      ≤ δ_large * (6 : ℝ) ^ n := mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
    _ = 27 * triangleRemovalBound (γ / 9) * (1 / 32 : ℝ) * (c₆ * (6 : ℝ) ^ n) := by
        simp only [δ_large]; ring
    _ ≤ 27 * triangleRemovalBound (γ / 9) *
          ((n : ℝ) ^ 2 * (s : ℝ) / ((s + 1 : ℕ) : ℝ) ^ 5) * (c₆ * (6 : ℝ) ^ n) := by gcongr
    _ = (27 * triangleRemovalBound (γ / 9) * (n : ℝ) ^ 2 * (s : ℝ)) *
          (c₆ * (6 : ℝ) ^ n / ((s + 1 : ℕ) : ℝ) ^ 5) := by ring
    _ ≤ ((((S_type ×ˢ S_type ×ˢ S_type).filter fun t =>
            t.2.2.1 + t.2.1.2 = t.1.1 + t.1.2 ∧ t.2.2.1 + t.2.2.2 = t.2.1.1 + t.1.2).card : ℝ) *
          (s : ℝ)) * (c₆ * (6 : ℝ) ^ n / ((s + 1 : ℕ) : ℝ) ^ 5) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hValidInt_ge (Nat.cast_nonneg _)) (by positivity)
    _ ≤ (Good.card : ℝ) := hGood_ge

end MainTheorem

end OMA.Green17Symmetric

namespace OMA.Green17Symmetric

/-- Counting restricted APs including `d = 0` gives `numRestrictedAPs A + A.card`. -/
lemma card_good_eq_numRestrictedAPs_add {n : ℕ} (A : Finset (𝔽₃ n)) :
    (Finset.univ.filter fun p : 𝔽₃ n × 𝔽₃ n =>
        (∀ i, p.2 i = 0 ∨ p.2 i = 1) ∧ p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + 2 • p.2 ∈ A).card =
      Green17.numRestrictedAPs A + A.card := by
  classical
  set Good := Finset.univ.filter fun p : 𝔽₃ n × 𝔽₃ n =>
    (∀ i, p.2 i = 0 ∨ p.2 i = 1) ∧ p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + 2 • p.2 ∈ A
  set Nonzero := Good.filter fun p => p.2 ≠ 0
  set ZeroPart := Good.filter fun p => p.2 = 0
  have hdisj : Disjoint Nonzero ZeroPart := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact (Finset.mem_filter.mp hp1).2 (Finset.mem_filter.mp hp2).2
  have hunion : Nonzero ∪ ZeroPart = Good := by
    ext p
    simp only [Finset.mem_union, Nonzero, ZeroPart, Finset.mem_filter]
    tauto
  have hpart : Good.card = Nonzero.card + ZeroPart.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hnz : Nonzero.card = Green17.numRestrictedAPs A := by
    unfold Green17.numRestrictedAPs
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext ⟨x, d⟩
    simp [Nonzero, Good, Green17.IsRestrictedAP]
    tauto
  have hz : ZeroPart.card = A.card := by
    let emb : 𝔽₃ n ↪ 𝔽₃ n × 𝔽₃ n := ⟨fun x => (x, 0), fun _ _ h => congrArg Prod.fst h⟩
    have heq : ZeroPart = A.map emb := by
      ext ⟨x, d⟩
      simp only [ZeroPart, Good, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · rintro ⟨⟨_, hx, _, _⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, hxy⟩
        have hx : y = x := congrArg Prod.fst hxy
        have hd : (0 : 𝔽₃ n) = d := congrArg Prod.snd hxy
        subst hx; subst hd
        refine ⟨⟨fun _ => Or.inl rfl, hy, ?_, ?_⟩, rfl⟩
        · simpa using hy
        · simpa using hy
    rw [heq, Finset.card_map]
  rw [hpart, hnz, hz]

end OMA.Green17Symmetric

theorem OMA.solution : type_of% @Green17.green_17.variants.symmetric := by
  intro μ hμ
  obtain ⟨δ, hδ, hmain⟩ := OMA.Green17Symmetric.green_17_symmetric_main μ hμ
  refine ⟨δ, hδ, fun n A hsym hA => ?_⟩
  have hcard := OMA.Green17Symmetric.card_good_eq_numRestrictedAPs_add A
  have hres := hmain n A hsym hA
  have hcast :
      ((Finset.univ.filter fun p : (Fin n → ZMod 3) × (Fin n → ZMod 3) =>
          (∀ i, p.2 i = 0 ∨ p.2 i = 1) ∧ p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + 2 • p.2 ∈ A).card : ℝ) =
        (Green17.numRestrictedAPs A + A.card : ℝ) := by
    exact_mod_cast hcard
  linarith
