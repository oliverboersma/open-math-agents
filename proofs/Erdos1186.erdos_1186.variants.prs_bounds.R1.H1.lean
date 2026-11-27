import OMAReductions.R_Erdos1186_erdos_1186_variants_prs_bounds_R1

-- Step Erdos1186.erdos_1186.variants.prs_bounds.R1.H1: hypothesis H1 of reduction Erdos1186.erdos_1186.variants.prs_bounds.R1
-- Reduction credit: @dk8827. This proof: @koolkao (original).

/-!
Exact count for the twelve-block colouring. Put `w = 2q` and `n = 548 w`. A progression
`(a, a + d, a + 2d)` is written as `a - 1 = w α + s`, `d = w β + t` with `s, t < w`. The blocks
of the three terms are `α`, `α + β + ⌊(s+t)/w⌋` and `α + 2β + ⌊(s+2t)/w⌋`, and only four carry
patterns occur, for `q² + q`, `q²`, `q²` and `q² - q` pairs `(s, t)`. Summing the block counts
`T₀₀ = 16304`, `T₀₁ = T₁₁ = 16028`, `T₁₂ = 15756` (checked by `decide`) gives
`monoCount 3 (1096 q) c + 1096 q = 64116 q² + 548 q`, where the `1096 q` accounts for `d = 0`.
-/

open Finset Erdos1186

namespace OMA.Erdos1186H1

/-- Colour of a block. -/
def col (b : ℕ) : Bool :=
  b < 28 || (34 ≤ b && b < 62) || (99 ≤ b && b < 158) ||
      (274 ≤ b && b < 390) || (449 ≤ b && b < 486) || (514 ≤ b && b < 520)

/-- A monochromatic block pattern: blocks `a`, `a + b + e₁`, `a + 2b + e₂`, the last below `548`. -/
def G (e₁ e₂ a b : ℕ) : ℕ :=
  if a + 2 * b + e₂ < 548 ∧ col (a + b + e₁) = col a ∧ col (a + 2 * b + e₂) = col a then 1 else 0

-- The four block counts, computed by the kernel on a `Bool`/`Nat.rec` version of `G`.

/-- `col` with `Nat.blt`/`Nat.ble`, for fast kernel evaluation. -/
def colB (b : ℕ) : Bool :=
  b.blt 28 || (Nat.ble 34 b && b.blt 62) || (Nat.ble 99 b && b.blt 158) ||
      (Nat.ble 274 b && b.blt 390) || (Nat.ble 449 b && b.blt 486) || (Nat.ble 514 b && b.blt 520)

/-- `G` with `Bool` operations only. -/
def GB (e₁ e₂ a b : ℕ) : ℕ :=
  cond ((a + 2 * b + e₂).blt 548 && !(xor (colB (a + b + e₁)) (colB a)) &&
    !(xor (colB (a + 2 * b + e₂)) (colB a))) 1 0

/-- A sum over `range n` written as a primitive recursion. -/
def rsum (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec 0 (fun k acc => acc + f k) n

lemma rsum_eq (f : ℕ → ℕ) (n : ℕ) : ∑ k ∈ range n, f k = rsum f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ih]; rfl

lemma dlt (x y : ℕ) : decide (x < y) = x.blt y := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]

lemma dle (x y : ℕ) : decide (x ≤ y) = Nat.ble x y := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.ble_eq]

lemma col_eq (b : ℕ) : col b = colB b := by
  simp only [col, colB, dlt, dle]

lemma G_eq (e₁ e₂ a b : ℕ) : G e₁ e₂ a b = GB e₁ e₂ a b := by
  unfold G GB
  simp only [← col_eq, ← dlt]
  generalize col (a + b + e₁) = x
  generalize col (a + 2 * b + e₂) = z
  generalize col a = y
  by_cases h1 : a + 2 * b + e₂ < 548 <;> cases x <;> cases y <;> cases z <;> simp [h1]

lemma T_eq (e₁ e₂ : ℕ) : ∑ a ∈ range 548, ∑ b ∈ range 274, G e₁ e₂ a b =
    rsum (fun a => rsum (fun b => GB e₁ e₂ a b) 274) 548 := by
  simp only [G_eq, rsum_eq]

lemma T00 : ∑ a ∈ range 548, ∑ b ∈ range 274, G 0 0 a b = 16304 := by
  rw [T_eq]; decide +kernel

lemma T01 : ∑ a ∈ range 548, ∑ b ∈ range 274, G 0 1 a b = 16028 := by
  rw [T_eq]; decide +kernel

lemma T11 : ∑ a ∈ range 548, ∑ b ∈ range 274, G 1 1 a b = 16028 := by
  rw [T_eq]; decide +kernel

lemma T12 : ∑ a ∈ range 548, ∑ b ∈ range 274, G 1 2 a b = 15756 := by
  rw [T_eq]; decide +kernel

lemma G_half (e₁ e₂ a : ℕ) : ∑ b ∈ range 548, G e₁ e₂ a b = ∑ b ∈ range 274, G e₁ e₂ a b := by
  rw [show (548 : ℕ) = 274 + 274 from rfl, sum_range_add]
  have : ∑ x ∈ range 274, G e₁ e₂ a (274 + x) = 0 := by
    apply sum_eq_zero
    intro x _
    unfold G
    rw [if_neg]
    omega
  rw [this, add_zero]

lemma sum_range_mul (f : ℕ → ℕ) (m w : ℕ) :
    ∑ i ∈ range (m * w), f i = ∑ α ∈ range m, ∑ s ∈ range w, f (w * α + s) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ, mul_comm w m]

lemma sum_Icc_one (f : ℕ → ℕ) (n : ℕ) : ∑ d ∈ Icc 1 n, f d = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- The inner sum over `t` for `t < q`. -/
lemma inner_lo (q t : ℕ) (ht : t < q) (h : ℕ → ℕ → ℕ) :
    ∑ s ∈ range (2 * q), h ((s + t) / (2 * q)) ((s + 2 * t) / (2 * q)) =
      (2 * q - 2 * t) * h 0 0 + t * h 0 1 + t * h 1 1 := by
  have hw : 2 * q = (2 * q - 2 * t) + t + t := by omega
  have hpos : 0 < 2 * q := by omega
  conv_lhs => rw [hw]
  rw [sum_range_add, sum_range_add]
  rw [← hw]
  have h1 : ∑ x ∈ range (2 * q - 2 * t), h ((x + t) / (2 * q)) ((x + 2 * t) / (2 * q)) =
      (2 * q - 2 * t) * h 0 0 := by
    rw [sum_const_nat (m := h 0 0), card_range]
    intro x hx
    rw [mem_range] at hx
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  have h2 : ∑ x ∈ range t, h ((2 * q - 2 * t + x + t) / (2 * q))
      ((2 * q - 2 * t + x + 2 * t) / (2 * q)) = t * h 0 1 := by
    rw [sum_const_nat (m := h 0 1), card_range]
    intro x hx
    rw [mem_range] at hx
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  have h3 : ∑ x ∈ range t, h ((2 * q - 2 * t + t + x + t) / (2 * q))
      ((2 * q - 2 * t + t + x + 2 * t) / (2 * q)) = t * h 1 1 := by
    rw [sum_const_nat (m := h 1 1), card_range]
    intro x hx
    rw [mem_range] at hx
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega), Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  rw [h1, h2, h3]

/-- The inner sum over `t = q + t'` for `t' < q`. -/
lemma inner_hi (q t : ℕ) (ht : t < q) (h : ℕ → ℕ → ℕ) :
    ∑ s ∈ range (2 * q), h ((s + (q + t)) / (2 * q)) ((s + 2 * (q + t)) / (2 * q)) =
      (q - t) * h 0 1 + (q - t) * h 1 1 + (2 * t) * h 1 2 := by
  have hw : 2 * q = (q - t) + (q - t) + 2 * t := by omega
  conv_lhs => rw [hw]
  rw [sum_range_add, sum_range_add]
  rw [← hw]
  have h1 : ∑ x ∈ range (q - t), h ((x + (q + t)) / (2 * q)) ((x + 2 * (q + t)) / (2 * q)) =
      (q - t) * h 0 1 := by
    rw [sum_const_nat (m := h 0 1), card_range]
    intro x hx
    rw [mem_range] at hx
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  have h2 : ∑ x ∈ range (q - t), h ((q - t + x + (q + t)) / (2 * q))
      ((q - t + x + 2 * (q + t)) / (2 * q)) = (q - t) * h 1 1 := by
    rw [sum_const_nat (m := h 1 1), card_range]
    intro x hx
    rw [mem_range] at hx
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega), Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
  have h3 : ∑ x ∈ range (2 * t), h ((q - t + (q - t) + x + (q + t)) / (2 * q))
      ((q - t + (q - t) + x + 2 * (q + t)) / (2 * q)) = (2 * t) * h 1 2 := by
    rw [sum_const_nat (m := h 1 2), card_range]
    intro x hx
    rw [mem_range] at hx
    rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega), Nat.div_eq_of_lt_le (k := 2) (by omega) (by omega)]
  rw [h1, h2, h3]

/-- Counting the pairs `(s, t)` by their carry pattern. -/
lemma inner (q : ℕ) (h : ℕ → ℕ → ℕ) :
    ∑ s ∈ range (2 * q), ∑ t ∈ range (2 * q), h ((s + t) / (2 * q)) ((s + 2 * t) / (2 * q)) =
      (q * q + q) * h 0 0 + q * q * h 0 1 + q * q * h 1 1 + (q * q - q) * h 1 2 := by
  rw [sum_comm, two_mul q, sum_range_add, ← two_mul q]
  rw [sum_congr rfl (fun t ht => inner_lo q t (mem_range.1 ht) h)]
  rw [sum_congr rfl (fun t ht => inner_hi q t (mem_range.1 ht) h)]
  simp only [sum_add_distrib, ← sum_mul]
  have hA := sum_range_id_mul_two q
  have hr1 : ∑ t ∈ range q, (2 * q - 2 * t) = ∑ t ∈ range q, (2 * t + 2) := by
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro t ht
    rw [mem_range] at ht
    omega
  have hr2 : ∑ t ∈ range q, (q - t) = ∑ t ∈ range q, (t + 1) := by
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro t ht
    rw [mem_range] at ht
    omega
  have hqq : q ≤ q * q := Nat.le_mul_self q
  have hA : (∑ i ∈ range q, i) * 2 = q * q - q := by
    rw [sum_range_id_mul_two, Nat.mul_sub_one]
  have s1 : ∑ t ∈ range q, (2 * q - 2 * t) = (∑ i ∈ range q, i) * 2 + 2 * q := by
    rw [hr1, sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum]
    ring
  have s3 : ∑ t ∈ range q, (q - t) = (∑ i ∈ range q, i) + q := by
    rw [hr2, sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
  have s4 : ∑ t ∈ range q, 2 * t = (∑ i ∈ range q, i) * 2 := by
    rw [← mul_sum, mul_comm]
  rw [s1, s3, s4]
  generalize (∑ i ∈ range q, i) = A at hA ⊢
  have hQ : q * q = A * 2 + q := by omega
  rw [hQ, show A * 2 + q - q = A * 2 by omega]
  ring

end OMA.Erdos1186H1

open OMA.Erdos1186H1 in
theorem OMA.solution : OMA.R_Erdos1186_erdos_1186_variants_prs_bounds_R1.H1 := by
  intro q hq
  show monoCount 3 (1096 * q) (fun x => col ((x - 1) / (2 * q))) ≤ 64116 * q ^ 2
  set w := 2 * q with hw
  have hwpos : 0 < w := by omega
  have hn : 1096 * q = 548 * w := by omega
  rw [hn]
  set n := 548 * w with hndef
  -- the indicator in normalised coordinates
  let F : ℕ → ℕ → ℕ := fun i d =>
    if i + 2 * d < n ∧ col ((i + d) / w) = col (i / w) ∧ col ((i + 2 * d) / w) = col (i / w)
    then 1 else 0
  have hcount : monoCount 3 n (fun x => col ((x - 1) / w)) + n =
      ∑ i ∈ range n, ∑ d ∈ range n, F i d := by
    have step1 : ∀ i ∈ range n, ∑ d ∈ range n, F i d = ∑ d ∈ range n, F i (d + 1) + 1 := by
      intro i hi
      rw [mem_range] at hi
      have hF0 : F i 0 = 1 := by
        simp [F, hi]
      have hFn : F i n = 0 := by
        simp only [F]
        rw [if_neg]
        omega
      have h1 := sum_range_succ' (F i) n
      rw [sum_range_succ, hFn, add_zero, hF0] at h1
      exact h1
    rw [sum_congr rfl step1, sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
    congr 1
    unfold monoCount
    rw [card_filter, sum_product, sum_Icc_one]
    apply sum_congr rfl
    intro i _
    rw [sum_Icc_one]
    apply sum_congr rfl
    intro d _
    dsimp only [F]
    apply if_congr _ rfl rfl
    have e0 : i + 1 - 1 = i := by omega
    have e1 : i + 1 + 1 * (d + 1) - 1 = i + (d + 1) := by omega
    have e2 : i + 1 + 2 * (d + 1) - 1 = i + 2 * (d + 1) := by omega
    constructor
    · rintro ⟨hle, hall⟩
      refine ⟨by omega, ?_, ?_⟩
      · have := hall 1 (by omega)
        rwa [e1, e0] at this
      · have := hall 2 (by omega)
        rwa [e2, e0] at this
    · rintro ⟨hlt, h1, h2⟩
      refine ⟨by omega, fun k hk => ?_⟩
      interval_cases k
      · simp
      · rw [e1, e0]; exact h1
      · rw [e2, e0]; exact h2
  have hS : ∑ i ∈ range n, ∑ d ∈ range n, F i d =
      ∑ α ∈ range 548, ∑ β ∈ range 548, ((q * q + q) * G 0 0 α β + q * q * G 0 1 α β +
        q * q * G 1 1 α β + (q * q - q) * G 1 2 α β) := by
    rw [hndef, sum_range_mul]
    apply sum_congr rfl
    intro α _
    simp_rw [sum_range_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro β _
    rw [← inner q (fun e₁ e₂ => G e₁ e₂ α β)]
    apply sum_congr rfl
    intro s hs
    apply sum_congr rfl
    intro t ht
    rw [mem_range] at hs ht
    have d0 : (w * α + s) / w = α := by
      rw [add_comm, Nat.add_mul_div_left _ _ hwpos, Nat.div_eq_of_lt hs, zero_add]
    have d1 : (w * α + s + (w * β + t)) / w = α + β + (s + t) / w := by
      rw [show w * α + s + (w * β + t) = (s + t) + w * (α + β) by ring,
        Nat.add_mul_div_left _ _ hwpos]
      ring
    have d2 : (w * α + s + 2 * (w * β + t)) / w = α + 2 * β + (s + 2 * t) / w := by
      rw [show w * α + s + 2 * (w * β + t) = (s + 2 * t) + w * (α + 2 * β) by ring,
        Nat.add_mul_div_left _ _ hwpos]
      ring
    have d3 : w * α + s + 2 * (w * β + t) < 548 * w ↔ α + 2 * β + (s + 2 * t) / w < 548 := by
      rw [← d2, Nat.div_lt_iff_lt_mul hwpos]
    simp only [F, G, hndef, ← hw, d0, d1, d2, d3]
  have hT : ∑ α ∈ range 548, ∑ β ∈ range 548, ((q * q + q) * G 0 0 α β + q * q * G 0 1 α β +
        q * q * G 1 1 α β + (q * q - q) * G 1 2 α β) =
      (q * q + q) * 16304 + q * q * 16028 + q * q * 16028 + (q * q - q) * 15756 := by
    simp only [sum_add_distrib, ← mul_sum, G_half, T00, T01, T11, T12]
  have hqq : q ≤ q * q := Nat.le_mul_self q
  have key := hcount.trans (hS.trans hT)
  rw [pow_two]
  generalize q * q = Q at key hqq ⊢
  omega
