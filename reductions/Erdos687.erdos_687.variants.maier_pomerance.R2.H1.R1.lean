import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R2
import Mathlib.NumberTheory.Chebyshev

-- Reduction Erdos687.erdos_687.variants.maier_pomerance.R2.H1.R1 of step Erdos687.erdos_687.variants.maier_pomerance.R2.H1
-- Credit: @JamesSlash

/-!
# Erdős 687, Maier–Pomerance variant: the initial-sieve step from OpenAI's survivor count

Step `H1` of reduction `R2` asks that sifting `[1, y]` by one class for each prime up to
`min x ⌊√y⌋` leaves more survivors than there are primes in `(min x ⌊√y⌋, x]`, where
`y = ⌊x (log x)^(2+ε)⌋ + 1`.

We reduce it to two published results.

* `H1` is Theorem 1.2 of OpenAI, *A quadratic bound for Jacobsthal's function* (OpenAI Math
  Release preprint, 25 September 2026): with `L = log z`, `Y = ⌊z²/L²⌋`, `w = L/(log L)²`,
  `B = L/log w` and `V₀ = ∏_{p ≤ w} (1 - 1/p)`, every choice of one class per prime `p ≤ z`
  leaves at least `c Y V₀ / B²` survivors in `[1, Y]`, for all large real `z`.
* `H2` is the lower bound in Mertens' third theorem, `∏_{p ≤ x} (1 - 1/p) ≥ c₀ / log x`
  (Mertens 1874), stated exactly as step `H2` of `Erdos687.erdos_687.variants.iwaniec.R1`.

The deduction applies `H1` at `z = √y log √y`. Then `Y ≤ y`, the sieving range contains every
prime up to `⌊√y⌋`, and `H2` turns `c Y V₀ / B²` into at least a constant times `y / (log y)²`
survivors. Chebyshev's bound `π(x) ≤ 8x / log x` and `y ≥ x (log x)²` finish the comparison.
The Chebyshev lemma is copied from the merged reduction `Erdos687.erdos_687.variants.iwaniec.R1`
by @ItsNotTheGabs.
-/

namespace OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1

open Filter Finset

/-- OpenAI's survivor count (Theorem 1.2 of *A quadratic bound for Jacobsthal's function*,
2026): there are `c > 0` and `z₀` such that for every real `z ≥ z₀` and every choice of one
residue class `a p` for each prime `p ≤ z`, with `L = log z`, `Y = ⌊z²/L²⌋`, `w = L/(log L)²`,
`B = L/log w` and `V₀ = ∏_{p ≤ w} (1 - 1/p)`, at least `c Y V₀ / B²` integers of `[1, Y]`
avoid every class. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ z₀ : ℝ, ∀ z : ℝ, z₀ ≤ z → ∀ a : ℕ → ℕ,
    let L := Real.log z
    let Y := ⌊z ^ 2 / L ^ 2⌋₊
    let w := L / Real.log L ^ 2
    let B := L / Real.log w
    let V₀ := ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)
    c * (Y : ℝ) * V₀ / B ^ 2 ≤
      (((Finset.Icc 1 Y).filter fun n => ∀ p ≤ ⌊z⌋₊, p.Prime → ¬ (n ≡ a p [MOD p])).card : ℝ)

/-- Mertens' third theorem lower bound (Mertens 1874): there is `c₀ > 0` with
`c₀ / log x ≤ ∏_{p ≤ x} (1 - 1/p)` for all `x ≥ 2`. -/
def H2 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℕ, 2 ≤ x →
    c₀ / Real.log (x : ℝ) ≤
      ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)

/-- Chebyshev's bound `π(x) ≤ 8x / log x` (copied from the merged reduction
`Erdos687.erdos_687.variants.iwaniec.R1` by @ItsNotTheGabs). -/
lemma primeCounting_le_eight_mul_div_log {x : ℕ} (hx : 2 ≤ x) :
    (Nat.primeCounting x : ℝ) ≤ 8 * (x : ℝ) / Real.log (x : ℝ) := by
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hpi := Chebyshev.pi_le_log4_mul_div hx1
  rw [Nat.floor_natCast] at hpi
  have hlog_sqrt : Real.log √(x : ℝ) = Real.log (x : ℝ) / 2 := Real.log_sqrt hx0
  have hterm1 : Real.log 4 * (x : ℝ) / Real.log √(x : ℝ) ≤ 6 * (x : ℝ) / Real.log (x : ℝ) := by
    rw [hlog_sqrt]
    have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hrewrite : Real.log 4 * (x : ℝ) / (Real.log (x : ℝ) / 2) =
        (2 * Real.log 4) * (x : ℝ) / Real.log (x : ℝ) := by
      field_simp
    rw [hrewrite]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hx0) hlogx_pos.le
  have hterm2 : √(x : ℝ) ≤ 2 * (x : ℝ) / Real.log (x : ℝ) := by
    rw [le_div_iff₀ hlogx_pos]
    have hsqrt_pos : 0 < √(x : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog_le : Real.log √(x : ℝ) ≤ √(x : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hsqrt_pos]
    have hlogx_eq : Real.log (x : ℝ) = 2 * Real.log √(x : ℝ) := by linarith
    calc
      √(x : ℝ) * Real.log (x : ℝ) = 2 * (√(x : ℝ) * Real.log √(x : ℝ)) := by
        rw [hlogx_eq]; ring
      _ ≤ 2 * (√(x : ℝ) * √(x : ℝ)) := by
        gcongr
      _ = 2 * (x : ℝ) := by
        rw [Real.mul_self_sqrt hx0]
  have hsum : 6 * (x : ℝ) / Real.log (x : ℝ) + 2 * (x : ℝ) / Real.log (x : ℝ) =
      8 * (x : ℝ) / Real.log (x : ℝ) := by ring
  linarith

/-- A threshold beyond which `(log t)² ≤ t / 3`. -/
lemma exists_log_sq_le : ∃ T : ℝ, ∀ t ≥ T, Real.log t ^ 2 ≤ t / 3 := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show (0 : ℝ) < 1 / 3 by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨hb, ht1⟩ := hT t ht
  rw [norm_pow, Real.norm_eq_abs, sq_abs, id, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hb
  linarith

/-- The interval length `⌊y s² / L²⌋` lies between `y / 8` and `y` when `s ≤ L ≤ 2s`. -/
lemma floor_bounds (y : ℕ) {s L : ℝ} (hy8 : (8 : ℝ) ≤ y) (hs : 0 < s) (hsL : s ≤ L)
    (hL2 : L ≤ 2 * s) :
    ⌊(y : ℝ) * s ^ 2 / L ^ 2⌋₊ ≤ y ∧ (y : ℝ) / 8 ≤ (⌊(y : ℝ) * s ^ 2 / L ^ 2⌋₊ : ℝ) := by
  have hL : 0 < L := by linarith
  have hy0 : (0 : ℝ) ≤ y := by linarith
  constructor
  · apply Nat.floor_le_of_le
    rw [div_le_iff₀ (by positivity)]
    have h1 : s ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hs.le hsL 2
    exact mul_le_mul_of_nonneg_left h1 hy0
  · have h1 := Nat.lt_floor_add_one ((y : ℝ) * s ^ 2 / L ^ 2)
    have h2 : (y : ℝ) / 4 ≤ (y : ℝ) * s ^ 2 / L ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h3 : L ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ hL.le hL2 2
      have h4 : (y : ℝ) / 4 * L ^ 2 ≤ (y : ℝ) / 4 * (2 * s) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      linarith [show (y : ℝ) / 4 * (2 * s) ^ 2 = (y : ℝ) * s ^ 2 by ring]
    linarith

/-- The final comparison of `c Y V / B²` with `y / (2s)²`. -/
lemma real_bound {c c₀ y s L w V Y : ℝ} (hc : 0 < c) (hc₀ : 0 < c₀) (hy : 0 ≤ y)
    (hL : 0 < L) (hL2 : L ≤ 2 * s) (hlw : 1 ≤ Real.log w) (hVw : c₀ ≤ V * Real.log w)
    (hYge : y / 8 ≤ Y) :
    c * c₀ / 32 * y / (2 * s) ^ 2 ≤ c * Y * V / (L / Real.log w) ^ 2 := by
  have hlw0 : 0 < Real.log w := by linarith
  have hY0 : 0 ≤ Y := le_trans (by positivity) hYge
  have hVw0 : 0 ≤ V * Real.log w := by linarith
  have e1 : c * Y * V / (L / Real.log w) ^ 2 = c * Y * (V * Real.log w) * Real.log w / L ^ 2 := by
    field_simp
  rw [e1]
  have hnum : c * (y / 8) * c₀ ≤ c * Y * (V * Real.log w) * Real.log w := by
    calc c * (y / 8) * c₀ = c * (y / 8) * c₀ * 1 := by ring
      _ ≤ c * Y * (V * Real.log w) * Real.log w := by
        apply mul_le_mul _ hlw zero_le_one (mul_nonneg (mul_nonneg hc.le hY0) hVw0)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hYge hc.le) hVw hc₀.le
          (mul_nonneg hc.le hY0)
  have hden : L ^ 2 ≤ (2 * s) ^ 2 := pow_le_pow_left₀ hL.le hL2 2
  have hn0 : c * c₀ / 32 * y ≤ c * (y / 8) * c₀ := by
    rw [show c * (y / 8) * c₀ = 4 * (c * c₀ / 32 * y) by ring]
    linarith [show 0 ≤ c * c₀ / 32 * y by positivity]
  calc c * c₀ / 32 * y / (2 * s) ^ 2
      ≤ c * (y / 8) * c₀ / (2 * s) ^ 2 := div_le_div_of_nonneg_right hn0 (by positivity)
    _ ≤ c * (y / 8) * c₀ / L ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ ≤ c * Y * (V * Real.log w) * Real.log w / L ^ 2 :=
        div_le_div_of_nonneg_right hnum (by positivity)

/-- The two hypotheses give at least a constant times `y / (log y)²` survivors when `[1, y]`
is sifted by one class for each prime up to `⌊√y⌋`. -/
lemma survivors_lower (h1 : H1) (h2 : H2) : ∃ K : ℝ, 0 < K ∧ ∀ᶠ y : ℕ in atTop,
    ∀ a : ℕ → ℕ, K * (y : ℝ) / Real.log (y : ℝ) ^ 2 ≤
      (((Finset.Icc 1 y).filter fun m => ∀ p ≤ y.sqrt, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
  obtain ⟨c, hc, z₀, hOAI⟩ := h1
  obtain ⟨c₀, hc₀, hMert⟩ := h2
  obtain ⟨T, hT⟩ := exists_log_sq_le
  refine ⟨c * c₀ / 32, by positivity, ?_⟩
  have hy : Tendsto (fun y : ℕ => (y : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlogy : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hy
  filter_upwards [hy.eventually_ge_atTop (max 8 (z₀ ^ 2)),
    hlogy.eventually_ge_atTop (2 * max T 2)] with y hy8 hlog a
  have hy8' : (8 : ℝ) ≤ y := le_trans (le_max_left _ _) hy8
  have hyz : z₀ ^ 2 ≤ (y : ℝ) := le_trans (le_max_right _ _) hy8
  have hy0 : (0 : ℝ) < y := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.log (Real.sqrt (y : ℝ)) := ⟨_, rfl⟩
  have hs2 : Real.log (y : ℝ) = 2 * s := by
    rw [hs, Real.log_sqrt hy0.le]; ring
  have hsT : max T 2 ≤ s := by linarith
  have hs1 : (2 : ℝ) ≤ s := le_trans (le_max_right _ _) hsT
  have hspos : (0 : ℝ) < s := by linarith
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (y : ℝ) := Real.sqrt_pos.mpr hy0
  -- the cutoff `z = √y · s`
  have hz₀ : z₀ ≤ Real.sqrt (y : ℝ) * s := by
    have h1 : z₀ ≤ Real.sqrt (y : ℝ) := le_trans (le_abs_self z₀) (Real.abs_le_sqrt hyz)
    have h2 : Real.sqrt (y : ℝ) ≤ Real.sqrt (y : ℝ) * s :=
      le_mul_of_one_le_right hsqrt_pos.le (by linarith)
    linarith
  have key := hOAI (Real.sqrt (y : ℝ) * s) hz₀ a
  dsimp only at key
  have hL : Real.log (Real.sqrt (y : ℝ) * s) = s + Real.log s := by
    rw [Real.log_mul hsqrt_pos.ne' hspos.ne', ← hs]
  rw [hL] at key
  have hlogs0 : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hlogs1 : Real.log s ≤ s := by linarith [Real.log_le_sub_one_of_pos hspos]
  have hz2 : (Real.sqrt (y : ℝ) * s) ^ 2 = (y : ℝ) * s ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hy0.le]
  rw [hz2] at key
  generalize hLdef : s + Real.log s = L at key
  have hsL : s ≤ L := by linarith
  have hL2 : L ≤ 2 * s := by linarith
  have hLpos : 0 < L := by linarith
  have hLT : T ≤ L := le_trans (le_max_left _ _) (hsT.trans hsL)
  have hlogLpos : 0 < Real.log L := Real.log_pos (by linarith)
  have hlogL := hT L hLT
  -- the small-prime cutoff `w = L / (log L)²` is at least 3
  have hw3 : (3 : ℝ) ≤ L / Real.log L ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  generalize hwdef : L / Real.log L ^ 2 = w at key hw3
  have hfw : 3 ≤ ⌊w⌋₊ := Nat.le_floor (by exact_mod_cast hw3)
  have hfw' : (3 : ℝ) ≤ (⌊w⌋₊ : ℝ) := by exact_mod_cast hfw
  have hlogfw : 0 < Real.log (⌊w⌋₊ : ℝ) := Real.log_pos (by linarith)
  have hlogw1 : 1 ≤ Real.log w := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hV : c₀ / Real.log w ≤
      ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
    refine le_trans ?_ (hMert ⌊w⌋₊ (by omega))
    apply div_le_div_of_nonneg_left hc₀.le hlogfw
    exact Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  generalize hVdef : ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) = V
    at key hV
  have hVw : c₀ ≤ V * Real.log w := by
    rwa [div_le_iff₀ (by linarith)] at hV
  -- the interval length `Y = ⌊y s² / L²⌋` lies in `[y / 8, y]`
  obtain ⟨hYle, hYge⟩ := floor_bounds y hy8' hspos hsL hL2
  generalize hYdef : ⌊(y : ℝ) * s ^ 2 / L ^ 2⌋₊ = Y at key hYle hYge
  -- compare the bound of `H1` with `K y / (log y)²`
  have hmain : c * c₀ / 32 * (y : ℝ) / Real.log (y : ℝ) ^ 2 ≤
      c * (Y : ℝ) * V / (L / Real.log w) ^ 2 := by
    rw [hs2]
    exact real_bound hc hc₀ (Nat.cast_nonneg y) hLpos hL2 hlogw1 hVw hYge
  refine le_trans hmain (le_trans key ?_)
  -- the sifted set of `H1` sits inside the sifted set of the step
  have hsq : y.sqrt ≤ ⌊Real.sqrt (y : ℝ) * s⌋₊ := by
    apply Nat.le_floor
    exact le_trans Real.nat_sqrt_le_real_sqrt
      (le_mul_of_one_le_right hsqrt_pos.le (by linarith))
  exact_mod_cast Finset.card_le_card (fun m hm => by
    rw [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨⟨hm.1.1, hm.1.2.trans hYle⟩, fun p hp hpp => hm.2 p (hp.trans hsq) hpp⟩)

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2.H1 := by
  intro h1 h2 ε hε
  obtain ⟨K, hK, hsurv⟩ := survivors_lower h1 h2
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp hsurv
  have hx : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlogx : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hsmall : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ^ (2 + ε) ≤ (x : ℝ) / 2 := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 + ε) one_pos).bound
      (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [hx.eventually h, hlogx.eventually_ge_atTop 1] with x hb hl
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), abs_of_nonneg (Nat.cast_nonneg _)] at hb
    linarith
  filter_upwards [hsmall, hlogx.eventually_ge_atTop (max 1 (64 / K)),
    eventually_ge_atTop (max 3 Y₀)] with x hxs hxl hx3 a
  dsimp only
  have hx3' : 3 ≤ x := le_trans (le_max_left _ _) hx3
  have hxR : (3 : ℝ) ≤ x := by exact_mod_cast hx3'
  have hl1 : 1 ≤ Real.log (x : ℝ) := le_trans (le_max_left _ _) hxl
  have hlK : 64 / K ≤ Real.log (x : ℝ) := le_trans (le_max_right _ _) hxl
  have hlpos : 0 < Real.log (x : ℝ) := by linarith
  set t : ℝ := (x : ℝ) * Real.log (x : ℝ) ^ (2 + ε) with ht
  have hpow2 : Real.log (x : ℝ) ^ 2 ≤ Real.log (x : ℝ) ^ (2 + ε) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hl1 (by push_cast; linarith)
  have hpow1 : 1 ≤ Real.log (x : ℝ) ^ 2 := one_le_pow₀ hl1
  have htx : (x : ℝ) ≤ t := by
    rw [ht]; nlinarith
  have hyx : x ≤ ⌊t⌋₊ + 1 := by
    have := Nat.le_floor htx
    omega
  have hyR1 : (x : ℝ) * Real.log (x : ℝ) ^ 2 ≤ ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one t
    push_cast
    nlinarith
  have hyR2 : ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ (x : ℝ) ^ 2 := by
    have h1 := Nat.floor_le (show 0 ≤ t by positivity)
    push_cast
    have : t ≤ (x : ℝ) * ((x : ℝ) / 2) := by
      rw [ht]; exact mul_le_mul_of_nonneg_left hxs (Nat.cast_nonneg _)
    nlinarith
  generalize hydef : ⌊t⌋₊ + 1 = y at hyx hyR1 hyR2 ⊢
  have hyY : Y₀ ≤ y := le_trans (le_max_right _ _) (hx3.trans hyx)
  have hS := hY₀ y hyY a
  have hy0 : (0 : ℝ) < y := by
    have : (1 : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ^ 2 := by nlinarith
    linarith
  have hlogy : Real.log (y : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    calc Real.log (y : ℝ) ≤ Real.log ((x : ℝ) ^ 2) := Real.log_le_log hy0 hyR2
      _ = 2 * Real.log (x : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogy0 : 0 < Real.log (y : ℝ) := Real.log_pos (by
    have : (3 : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ^ 2 := by nlinarith
    linarith)
  -- survivors of the step contain the survivors sifted up to `⌊√y⌋`
  have hsub : ((Finset.Icc 1 y).filter fun m => ∀ p ≤ y.sqrt, p.Prime → ¬ (m ≡ a p [MOD p])) ⊆
      ((Finset.Icc 1 y).filter fun m => ∀ p ≤ min x y.sqrt, p.Prime → ¬ (m ≡ a p [MOD p])) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, fun p hp hpp => hm.2 p (hp.trans (min_le_right _ _)) hpp⟩
  have hcardS := Finset.card_le_card hsub
  -- primes in `(min x ⌊√y⌋, x]` number at most `π(x)`
  have hprimes : ((Finset.Ioc (min x y.sqrt) x).filter Nat.Prime).card ≤ Nat.primeCounting x := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact Nat.mem_primesLE.mpr ⟨hp.1.2, hp.2⟩
  have hpi := primeCounting_le_eight_mul_div_log (show 2 ≤ x by omega)
  -- the comparison `8x / log x < K x / 4 ≤ K y / (log y)²`
  have hcmp1 : 8 * (x : ℝ) / Real.log (x : ℝ) < K * (x : ℝ) / 4 := by
    rw [div_lt_div_iff₀ hlpos (by norm_num)]
    have hKl : 64 ≤ K * Real.log (x : ℝ) := by
      rwa [div_le_iff₀ hK, mul_comm] at hlK
    nlinarith
  have hcmp2 : K * (x : ℝ) / 4 ≤ K * (y : ℝ) / Real.log (y : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have h1 : Real.log (y : ℝ) ^ 2 ≤ 4 * Real.log (x : ℝ) ^ 2 := by nlinarith
    have h2 : K * (x : ℝ) * Real.log (y : ℝ) ^ 2 ≤ K * (x : ℝ) * (4 * Real.log (x : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  have hfinal : (((Finset.Ioc (min x y.sqrt) x).filter Nat.Prime).card : ℝ) <
      (((Finset.Icc 1 y).filter fun m => ∀ p ≤ min x y.sqrt, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
    have e1 : (((Finset.Ioc (min x y.sqrt) x).filter Nat.Prime).card : ℝ) ≤ Nat.primeCounting x := by
      exact_mod_cast hprimes
    have e2 : (((Finset.Icc 1 y).filter fun m => ∀ p ≤ y.sqrt, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) ≤
        (((Finset.Icc 1 y).filter fun m => ∀ p ≤ min x y.sqrt, p.Prime → ¬ (m ≡ a p [MOD p])).card : ℝ) := by
      exact_mod_cast hcardS
    linarith
  exact_mod_cast hfinal

end OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R2_H1_R1
