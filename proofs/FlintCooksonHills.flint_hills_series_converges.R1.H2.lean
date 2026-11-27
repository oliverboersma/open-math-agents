import OMAReductions.R_FlintCooksonHills_flint_hills_series_converges_R1

-- Step FlintCooksonHills.flint_hills_series_converges.R1.H2: hypothesis H2 of reduction FlintCooksonHills.flint_hills_series_converges.R1
-- Credit: @ivillar
-- H2 := ∀ α c ν : ℝ, 0 < c → 1 < ν → ν < 5 / 2 →     (∀ q : ℕ, 0 < q →       c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|) →     Summable (fun q : ℕ =>       1 / ((q : ℝ) ^ 3 * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)| ^ 2))
--
-- Proof: write t(q) = q*alpha - round(q*alpha). For q in the dyadic block [2^j, 2^(j+1)) the
-- hypothesis gives |t(q)| >= delta_j := c*(2^(1-nu))^(j+1), and for q1 < q2 in the same block
-- |t(q2) - t(q1)| >= |(q2-q1)*alpha - round((q2-q1)*alpha)| >= delta_j. So q -> (j, floor(t(q)/delta_j))
-- is injective, and 1/(q^3 t(q)^2) <= 4/(2^(3j) delta_j^2 k^2) with k = floor(t(q)/delta_j) != 0.
-- The majorant is a product of a geometric series of ratio 2^(2nu-5) < 1 and sum 1/k^2.

namespace OMA.FCH

lemma sep (α c ν : ℝ)
    (h : ∀ q : ℕ, 0 < q → c * (q : ℝ) ^ (1 - ν) ≤ |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|)
    (q1 q2 : ℕ) (hlt : q1 < q2) :
    c * ((q2 - q1 : ℕ) : ℝ) ^ (1 - ν) ≤
      |((q2 : ℝ) * α - (round ((q2 : ℝ) * α) : ℝ)) - ((q1 : ℝ) * α - (round ((q1 : ℝ) * α) : ℝ))| := by
  refine (h (q2 - q1) (by omega)).trans ?_
  rw [Nat.cast_sub hlt.le]
  refine (round_le (((q2 : ℝ) - q1) * α) (round ((q2 : ℝ) * α) - round ((q1 : ℝ) * α))).trans ?_
  apply le_of_eq
  congr 1
  push_cast
  ring

lemma blk (c ν : ℝ) (hc : 0 < c) (hν : 1 < ν) (j m : ℕ) (hm : 0 < m) (hmj : m ≤ 2 ^ (j + 1)) :
    c * ((2 : ℝ) ^ (1 - ν)) ^ (j + 1) ≤ c * (m : ℝ) ^ (1 - ν) := by
  apply mul_le_mul_of_nonneg_left _ hc.le
  rw [Real.rpow_pow_comm (by norm_num)]
  apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hm) (by exact_mod_cast hmj) (by linarith)

lemma floor_close (a b δ : ℝ) (hδ : 0 < δ) (h : ⌊a / δ⌋ = ⌊b / δ⌋) : |b - a| < δ := by
  have h1 := Int.floor_le (a / δ)
  have h2 := Int.lt_floor_add_one (a / δ)
  have h3 := Int.floor_le (b / δ)
  have h4 := Int.lt_floor_add_one (b / δ)
  rw [h] at h1 h2
  have h5 : |b / δ - a / δ| < 1 := by rw [abs_lt]; constructor <;> linarith
  rwa [← sub_div, abs_div, abs_of_pos hδ, div_lt_one hδ] at h5

lemma floor_bound (t δ : ℝ) (hδ : 0 < δ) (ht : δ ≤ |t|) :
    (⌊t / δ⌋ : ℝ) ≠ 0 ∧ δ * |(⌊t / δ⌋ : ℝ)| ≤ 2 * |t| := by
  have h1 := Int.floor_le (t / δ)
  have h2 := Int.lt_floor_add_one (t / δ)
  have hq : 1 ≤ |t| / δ := by rwa [le_div_iff₀ hδ, one_mul]
  have habs : |t / δ| = |t| / δ := by rw [abs_div, abs_of_pos hδ]
  have hle : t / δ ≤ |t| / δ := habs ▸ le_abs_self _
  have hge : -(|t| / δ) ≤ t / δ := habs ▸ neg_abs_le _
  constructor
  · intro h0
    rw [h0] at h1 h2
    have : |t / δ| < 1 := by rw [abs_lt]; constructor <;> linarith
    linarith
  · have hk : |(⌊t / δ⌋ : ℝ)| ≤ 2 * (|t| / δ) := by
      rw [abs_le]; constructor <;> linarith
    calc δ * |(⌊t / δ⌋ : ℝ)| ≤ δ * (2 * (|t| / δ)) := mul_le_mul_of_nonneg_left hk hδ.le
      _ = 2 * |t| := by field_simp

end OMA.FCH

open OMA.FCH in
theorem OMA.solution : OMA.R_FlintCooksonHills_flint_hills_series_converges_R1.H2 := by
  intro α c ν hc hν1 hν2 h
  set r : ℝ := (2 : ℝ) ^ (1 - ν) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  set δ : ℕ → ℝ := fun j => c * r ^ (j + 1) with hδdef
  have hδ : ∀ j, 0 < δ j := fun j => mul_pos hc (pow_pos hr0 _)
  set T : ℕ → ℝ := fun q => (q : ℝ) * α - (round ((q : ℝ) * α) : ℝ) with hT
  set J : ℕ → ℕ := fun n => Nat.log 2 (n + 1) with hJ
  set key : ℕ → ℕ × ℤ := fun n => (J n, ⌊T (n + 1) / δ (J n)⌋) with hkey
  set a : ℕ → ℝ := fun j => 4 / ((2 : ℝ) ^ (3 * j) * (δ j) ^ 2) with ha
  set b : ℤ → ℝ := fun k => 1 / (k : ℝ) ^ 2 with hb
  have hJ1 : ∀ n, 2 ^ (J n) ≤ n + 1 := fun n => Nat.pow_log_le_self 2 (by omega)
  have hJ2 : ∀ n, n + 1 < 2 ^ (J n + 1) := fun n => Nat.lt_pow_succ_log_self (by norm_num) _
  have hlow : ∀ j m : ℕ, 0 < m → m ≤ 2 ^ (j + 1) → δ j ≤ c * (m : ℝ) ^ (1 - ν) :=
    fun j m hm hmj => blk c ν hc hν1 j m hm hmj
  have hTlow : ∀ n, δ (J n) ≤ |T (n + 1)| := fun n =>
    (hlow _ _ (by omega) (hJ2 n).le).trans (h (n + 1) (by omega))
  -- the key map is injective
  have hinj : Function.Injective key := by
    have one : ∀ n1 n2 : ℕ, n1 < n2 → key n1 = key n2 → False := by
      intro n1 n2 hlt hk
      simp only [hkey, Prod.mk.injEq] at hk
      obtain ⟨hj, hfl⟩ := hk
      rw [hj] at hfl
      have hc1 := floor_close _ _ _ (hδ (J n2)) hfl
      have hs := sep α c ν h (n1 + 1) (n2 + 1) (by omega)
      have hd : δ (J n2) ≤ c * (((n2 + 1) - (n1 + 1) : ℕ) : ℝ) ^ (1 - ν) :=
        hlow _ _ (by omega) (by have := hJ2 n2; omega)
      have : δ (J n2) ≤ |T (n2 + 1) - T (n1 + 1)| := hd.trans hs
      linarith
    intro n1 n2 hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact one n1 n2 hlt hk
    · exact one n2 n1 hlt hk.symm
  -- termwise bound
  have hbound : ∀ n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 3 * |((n + 1 : ℕ) : ℝ) * α - (round (((n + 1 : ℕ) : ℝ) * α) : ℝ)| ^ 2)
      ≤ (fun p : ℕ × ℤ => a p.1 * b p.2) (key n) := by
    intro n
    obtain ⟨hk0, hk⟩ := floor_bound (T (n + 1)) (δ (J n)) (hδ _) (hTlow n)
    simp only [hkey, ha, hb]
    set k : ℝ := (⌊T (n + 1) / δ (J n)⌋ : ℝ) with hkdef
    set t : ℝ := T (n + 1) with htdef
    have ht0 : 0 < |t| := lt_of_lt_of_le (hδ _) (hTlow n)
    have hk2 : 0 < k ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk0))
    have hq3 : (2 : ℝ) ^ (3 * J n) ≤ ((n + 1 : ℕ) : ℝ) ^ 3 := by
      rw [pow_mul']
      have : ((2 : ℝ) ^ (J n)) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hJ1 n
      exact pow_le_pow_left₀ (by positivity) this 3
    have hdk : (δ (J n)) ^ 2 * k ^ 2 ≤ 4 * |t| ^ 2 := by
      have := mul_self_le_mul_self (by positivity) hk
      nlinarith [abs_mul_abs_self k, abs_mul_abs_self t, sq_abs k, sq_abs t]
    change 1 / (((n + 1 : ℕ) : ℝ) ^ 3 * |t| ^ 2) ≤ 4 / ((2 : ℝ) ^ (3 * J n) * δ (J n) ^ 2) * (1 / k ^ 2)
    rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
    have hδ2 : 0 < δ (J n) ^ 2 := by have := hδ (J n); positivity
    calc 1 * ((2 : ℝ) ^ (3 * J n) * δ (J n) ^ 2 * k ^ 2)
        = (2 : ℝ) ^ (3 * J n) * (δ (J n) ^ 2 * k ^ 2) := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 3 * (4 * |t| ^ 2) :=
          mul_le_mul hq3 hdk (by positivity) (by positivity)
      _ = 4 * (((n + 1 : ℕ) : ℝ) ^ 3 * |t| ^ 2) := by ring
  -- summability of the majorant
  have h8 : 1 < 8 * r ^ 2 := by
    have e : 8 * r ^ 2 = (2 : ℝ) ^ ((3 : ℝ) + (1 - ν) * 2) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_mul (by norm_num), hr]
      norm_num
    rw [e]
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hasum : Summable a := by
    have e : a = fun j => (4 / (c ^ 2 * r ^ 2)) * ((8 * r ^ 2)⁻¹) ^ j := by
      funext j
      simp only [ha, hδdef]
      rw [pow_mul, inv_pow]
      field_simp
      ring
    rw [e]
    exact (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ h8)).mul_left _
  have hbsum : Summable b := by
    simpa [hb] using (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hgsum : Summable (fun p : ℕ × ℤ => a p.1 * b p.2) :=
    hasum.mul_of_nonneg hbsum (fun j => by simp only [ha]; have := hδ j; positivity)
      (fun k => by simp only [hb]; positivity)
  have hF : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 3 *
      |((n + 1 : ℕ) : ℝ) * α - (round (((n + 1 : ℕ) : ℝ) * α) : ℝ)| ^ 2)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hbound (hgsum.comp_injective hinj)
  exact (summable_nat_add_iff 1).mp hF
