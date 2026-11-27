import FormalConjectures.ErdosProblems.«687»

-- Reduction Erdos687.erdos_687.variants.fgkmt.R1 of Erdős Problem 687 — fgkmt
-- Credit: @JamesSlash

/-!
# Erdős 687, FGKMT lower bound: reduction to the three inputs of §3 of [FGKMT18]

Ford, Green, Konyagin, Maynard and Tao, *Long gaps between primes*, J. Amer. Math. Soc. 31 (2018),
prove `Y(x) ≫ x log x log₃ x / log₂ x`. Their §3 deduces this from three inputs, which are the
hypotheses here (`log₂ = log log`, `log₃ = log log log`).

* `H1` is their Theorem 2 (sieving primes): with `y = c x log x log₃ x / log₂ x` (3.1) and
  `z = x ^ (log₃ x / (4 log₂ x))` (3.2), there are classes `a s` for the primes
  `log²⁰ x < s ≤ z` and `b p` for the primes `x/2 < p ≤ x` that leave `≪ x / log x` primes of
  `(x, y]` unsifted.
* `H2` is the smooth-number count used there (de Bruijn's theorem): at most `x / log x` integers in
  `[1, x log x]` are `z`-smooth, for large `x` (the true count is `x / (log x)^(3+o(1))`).
* `H3` is Chebyshev's estimate: for every `A` there is `C` with at least `A x / log x` primes in
  `(x, C x]` for large `x`.

The proof of `main` is the Westzynthius–Erdős–Rankin argument of §3: extend the classes by `0`
on all other primes `p ≤ x`; an unsifted integer of `(x, y]` is `z`-smooth or a prime of `(x, y]`
unsifted by `a` and `b` (a prime factor above `x/2` times a cofactor with prime factors above
`log²⁰ x` exceeds `y`); then each of the `≪ x / log x` survivors gets its own prime of `(x, C x]`.
This covers an interval of length `⌊y⌋ - x` with the primes up to `(C + 1) x`, and the stated
asymptotic follows. The matching step adapts `cover_of_packing_budget` from the merged reduction
`Erdos687.erdos_687.variants.maier_pomerance.R2` by @NicholasWierenga.
-/

namespace OMA.R_Erdos687_erdos_687_variants_fgkmt_R1

open Filter Finset

/-- Theorem 2 of [FGKMT18] (sieving primes), for natural `x`: there are `c > 0` and `C₁` such
that for all large `x`, with `y = c x log x log₃ x / log₂ x` and `z = x ^ (log₃ x / (4 log₂ x))`,
some classes `a s` (primes `log²⁰ x < s ≤ z`) and `b p` (primes `x/2 < p ≤ x`) leave at most
`C₁ x / log x` primes `q ∈ (x, y]` in none of these classes. -/
def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ᶠ x : ℕ in atTop, ∃ a b : ℕ → ℕ,
    let y := c * x * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)
    let z := (x : ℝ) ^ (Real.log (Real.log (Real.log x)) / (4 * Real.log (Real.log x)))
    (((Finset.Ioc x ⌊y⌋₊).filter fun q => q.Prime ∧
        (∀ s ≤ ⌊z⌋₊, s.Prime → Real.log x ^ 20 < s → ¬ (q ≡ a s [MOD s])) ∧
        (∀ p ≤ x, p.Prime → (x : ℝ) / 2 < p → ¬ (q ≡ b p [MOD p]))).card : ℝ) ≤
      C₁ * x / Real.log x

/-- The smooth-number count used in §3 of [FGKMT18] (de Bruijn's theorem): for all large `x`, at
most `x / log x` integers of `[1, x log x]` have all their prime factors at most
`z = x ^ (log₃ x / (4 log₂ x))`. -/
def H2 : Prop :=
  ∀ᶠ x : ℕ in atTop,
    (((Finset.Icc 1 ⌊(x : ℝ) * Real.log x⌋₊).filter fun n : ℕ => ∀ p : ℕ, p ≤ n → p.Prime → p ∣ n →
        (p : ℝ) ≤ (x : ℝ) ^ (Real.log (Real.log (Real.log x)) / (4 * Real.log (Real.log x)))).card
      : ℝ) ≤ x / Real.log x

/-- Chebyshev's estimate: for every `A` there is `C` such that `(x, C x]` contains at least
`A x / log x` primes for all large `x`. -/
def H3 : Prop :=
  ∀ A : ℝ, ∃ C : ℕ, ∀ᶠ x : ℕ in atTop,
    A * x / Real.log x ≤ (((Finset.Ioc x (C * x)).filter Nat.Prime).card : ℝ)

/-- Give each survivor of the sieve by the primes up to `x` its own prime of `(x, X]`
(adapted from `cover_of_packing_budget` in the merged reduction
`Erdos687.erdos_687.variants.maier_pomerance.R2` by @NicholasWierenga). -/
lemma cover_of_budget {x X Y : ℕ} (hxX : x ≤ X) (α : ℕ → ℕ)
    (h : ((Icc 1 Y).filter fun m => ∀ p ≤ x, p.Prime → ¬ (m ≡ α p [MOD p])).card ≤
      ((Ioc x X).filter Nat.Prime).card) :
    Green46.IsCoveredByResidues X Y := by
  set S := (Icc 1 Y).filter fun m => ∀ p ≤ x, p.Prime → ¬ (m ≡ α p [MOD p]) with hS
  have hCard : Fintype.card ↥S ≤ ((Ioc x X).filter Nat.Prime).card := by
    simpa only [Fintype.card_coe] using h
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hCard
  have hChoose : ∀ p : ℕ, ∃ b : ℕ, ∀ m : ↥S, e m = p → (m : ℕ) ≡ b [MOD p] := by
    intro p
    by_cases hex : ∃ m : ↥S, e m = p
    · obtain ⟨n, hn⟩ := hex
      refine ⟨n, fun m hm => ?_⟩
      rw [e.injective (hm.trans hn.symm)]
    · exact ⟨0, fun m hm => (hex ⟨m, hm⟩).elim⟩
  choose β hβ using hChoose
  refine ⟨fun p => if p ≤ x then α p else β p, fun m hm => ?_⟩
  by_cases hs : m ∈ S
  · let r : ↥S := ⟨m, hs⟩
    have hp : e r ∈ (Ioc x X).filter Nat.Prime := he ⟨r, rfl⟩
    obtain ⟨hp, hpPrime⟩ := mem_filter.mp hp
    obtain ⟨hpLower, hpUpper⟩ := mem_Ioc.mp hp
    exact ⟨e r, hpUpper, hpPrime, by
      simpa only [if_neg (not_le_of_gt hpLower)] using hβ (e r) r rfl⟩
  · have hmHit : ¬ ∀ p ≤ x, p.Prime → ¬ (m ≡ α p [MOD p]) :=
      fun hAvoid => hs (mem_filter.mpr ⟨hm, hAvoid⟩)
    push Not at hmHit
    obtain ⟨p, hp, hpPrime, hCongr⟩ := hmHit
    exact ⟨p, hp.trans hxX, hpPrime, by simpa only [if_pos hp] using hCongr⟩

/-- Shifting classes by `x`. -/
lemma shift_modEq {m x a p : ℕ} (hp : 1 ≤ p) (h : m + x ≡ a [MOD p]) :
    m ≡ a + x * (p - 1) [MOD p] := by
  have h1 : m + x + x * (p - 1) ≡ a + x * (p - 1) [MOD p] := Nat.ModEq.add_right _ h
  have h2 : m + x + x * (p - 1) = m + p * x := by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have h3 : m + p * x ≡ m [MOD p] := by
    unfold Nat.ModEq
    rw [Nat.add_mul_mod_self_left]
  rw [h2] at h1
  exact h3.symm.trans h1

lemma log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht)
  rw [Real.log_sqrt ht.le] at h
  linarith [Real.sqrt_nonneg t]

/-- The three hypotheses cover an interval of length `⌊y⌋ - x` with the primes up to `D x`. -/
lemma covered_eventually (h1 : H1) (h2 : H2) (h3 : H3) : ∃ c : ℝ, 0 < c ∧ ∃ D : ℕ, 0 < D ∧
    ∀ᶠ x : ℕ in atTop, Green46.IsCoveredByResidues (D * x)
      (⌊c * x * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)⌋₊ - x) := by
  classical
  obtain ⟨c, hc, C₁, hC₁, hev1⟩ := h1
  obtain ⟨C, hev3⟩ := h3 (C₁ + 1)
  refine ⟨c, hc, C + 1, by omega, ?_⟩
  have hx : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hl2 : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hl
  have h20 : ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ^ 20 ≤ (x : ℝ) / 4 := by
    have h := (Real.isLittleO_pow_log_id_atTop (n := 20)).bound
      (show (0 : ℝ) < 1 / 4 by norm_num)
    filter_upwards [hx.eventually h, hx.eventually_ge_atTop 1] with x hb hx1
    have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx1
    simp only [id, norm_pow, Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg (show (0 : ℝ) ≤ x by linarith)] at hb
    linarith
  filter_upwards [hev1, h2, hev3, h20, hl.eventually_ge_atTop 2,
    hl2.eventually_ge_atTop (4 * c ^ 2 + 1), hx.eventually_ge_atTop 5] with
    x hx1 hsm hpr hx20 hlx hl2x hx5
  obtain ⟨a, b, hab⟩ := hx1
  dsimp only at hab hsm
  set L2 := Real.log (Real.log (x : ℝ)) with hL2
  set L3 := Real.log L2 with hL3
  set y := c * x * Real.log x * L3 / L2 with hy
  set z := (x : ℝ) ^ (L3 / (4 * L2)) with hz
  have hxR : (5 : ℝ) ≤ x := hx5
  have hlpos : 0 < Real.log (x : ℝ) := by linarith
  have hL2pos : 0 < L2 := by nlinarith [sq_nonneg c]
  have hL3nn : 0 ≤ L3 := Real.log_nonneg (by nlinarith [sq_nonneg c])
  have hy0 : 0 ≤ y := div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc.le (Nat.cast_nonneg _))
    hlpos.le) hL3nn) hL2pos.le
  -- `y ≤ x log x`
  have hyle : y ≤ (x : ℝ) * Real.log x := by
    have hL3le : c * L3 ≤ L2 := by
      have h1 : L3 ≤ 2 * Real.sqrt L2 := log_le_two_sqrt hL2pos
      have h2 : 2 * c ≤ Real.sqrt L2 := by
        rw [show 2 * c = Real.sqrt ((2 * c) ^ 2) by rw [Real.sqrt_sq (by linarith)]]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have h3 : Real.sqrt L2 * Real.sqrt L2 = L2 := Real.mul_self_sqrt hL2pos.le
      nlinarith [Real.sqrt_nonneg L2]
    rw [hy, div_le_iff₀ hL2pos]
    have hxl : 0 ≤ (x : ℝ) * Real.log x := by positivity
    nlinarith
  -- `z ≤ √x < x / 2`
  have hzsq : z ≤ Real.sqrt x := by
    rw [hz, Real.sqrt_eq_rpow]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    rw [div_le_iff₀ (by positivity)]
    have : L3 ≤ L2 := by linarith [Real.log_le_sub_one_of_pos hL2pos]
    linarith
  have hsqx : Real.sqrt x < (x : ℝ) / 2 := by
    have hs2 : 2 < Real.sqrt x := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ x by linarith)
    nlinarith
  have hz0 : 0 ≤ z := by rw [hz]; positivity
  have hzx2 : z < (x : ℝ) / 2 := lt_of_le_of_lt hzsq hsqx
  have hfz : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz0
  -- the extended classes and their shift to `[1, ⌊y⌋ - x]`
  let a' : ℕ → ℕ := fun p =>
    if p ≤ ⌊z⌋₊ ∧ Real.log x ^ 20 < p then a p else if (x : ℝ) / 2 < p then b p else 0
  apply cover_of_budget (show x ≤ (C + 1) * x by nlinarith) (fun p => a' p + x * (p - 1))
  beta_reduce
  set T := (Icc 1 (⌊y⌋₊ - x)).filter
    fun m => ∀ p ≤ x, p.Prime → ¬ (m ≡ a' p + x * (p - 1) [MOD p]) with hT
  set Sm := (Finset.Icc 1 ⌊(x : ℝ) * Real.log x⌋₊).filter fun n : ℕ => ∀ p : ℕ, p ≤ n → p.Prime → p ∣ n →
    (p : ℝ) ≤ z with hSm
  set QS := (Finset.Ioc x ⌊y⌋₊).filter fun q => q.Prime ∧
    (∀ s ≤ ⌊z⌋₊, s.Prime → Real.log x ^ 20 < s → ¬ (q ≡ a s [MOD s])) ∧
    (∀ p ≤ x, p.Prime → (x : ℝ) / 2 < p → ¬ (q ≡ b p [MOD p])) with hQS
  have hTle : T.card ≤ (Sm ∪ QS).card := by
    apply card_le_card_of_injOn (fun m => m + x)
    · intro m hm
      simp only [Finset.mem_coe] at hm ⊢
      beta_reduce
      rw [hT, mem_filter, mem_Icc] at hm
      obtain ⟨⟨hm1, hm2⟩, hmS⟩ := hm
      have hsurv : ∀ p ≤ x, p.Prime → ¬ (m + x ≡ a' p [MOD p]) :=
        fun p hp hpp hcong => hmS p hp hpp (shift_modEq hpp.one_lt.le hcong)
      have hnx : x < m + x := by omega
      have hny : m + x ≤ ⌊y⌋₊ := by omega
      have hnyR : ((m + x : ℕ) : ℝ) ≤ y := le_trans (Nat.cast_le.mpr hny) (Nat.floor_le hy0)
      by_cases hsmooth : ∀ q : ℕ, q ≤ m + x → q.Prime → q ∣ m + x → (q : ℝ) ≤ z
      · apply mem_union_left
        rw [hSm, mem_filter, mem_Icc]
        exact ⟨⟨by omega, hny.trans (Nat.floor_le_floor hyle)⟩, hsmooth⟩
      · apply mem_union_right
        push Not at hsmooth
        obtain ⟨q, hqn, hqp, hqd, hqz⟩ := hsmooth
        have hqfz : ¬ q ≤ ⌊z⌋₊ := fun h => by
          have : (q : ℝ) ≤ ⌊z⌋₊ := Nat.cast_le.mpr h
          linarith
        have hqx2 : (x : ℝ) / 2 < q := by
          by_contra hle
          push Not at hle
          have hqx : q ≤ x := by
            have : (q : ℝ) ≤ x := by linarith
            exact_mod_cast this
          have ha' : a' q = 0 := by
            simp only [a']
            rw [if_neg (fun h => hqfz h.1), if_neg (not_lt.mpr hle)]
          exact hsurv q hqx hqp (by rw [ha']; exact Nat.modEq_zero_iff_dvd.mpr hqd)
        obtain ⟨k, hk⟩ := hqd
        have hk1 : k = 1 := by
          by_contra hk1
          obtain ⟨r, hrp, hrk⟩ := Nat.exists_prime_and_dvd hk1
          have hrn : r ∣ m + x := hk ▸ Dvd.dvd.mul_left hrk q
          have hr20 : Real.log x ^ 20 < r := by
            by_contra hle
            push Not at hle
            have hrx : r ≤ x := by
              have : (r : ℝ) ≤ x := by linarith
              exact_mod_cast this
            have ha' : a' r = 0 := by
              simp only [a']
              rw [if_neg (fun h => absurd h.2 (not_lt.mpr hle)), if_neg (by
                push_neg; linarith)]
            exact hsurv r hrx hrp (by rw [ha']; exact Nat.modEq_zero_iff_dvd.mpr hrn)
          have hkpos : 0 < k := by
            rcases Nat.eq_zero_or_pos k with h0 | h0
            · rw [h0, mul_zero] at hk; omega
            · exact h0
          have hkr : (r : ℝ) ≤ k := Nat.cast_le.mpr (Nat.le_of_dvd hkpos hrk)
          have hnqk : ((m + x : ℕ) : ℝ) = (q : ℝ) * k := by exact_mod_cast hk
          have hbig : (x : ℝ) / 2 * Real.log x ^ 20 < (q : ℝ) * k := by
            apply mul_lt_mul'' hqx2 (by linarith) (by positivity) (by positivity)
          have hl19 : 2 ≤ Real.log x ^ 19 := by
            calc (2 : ℝ) ≤ 2 ^ 19 := by norm_num
              _ ≤ Real.log x ^ 19 := pow_le_pow_left₀ (by norm_num) hlx 19
          have hxl : (x : ℝ) * Real.log x ≤ (x : ℝ) / 2 * Real.log x ^ 20 := by
            have : (x : ℝ) / 2 * Real.log x ^ 20 = (x : ℝ) * Real.log x * (Real.log x ^ 19 / 2) := by
              ring
            rw [this]
            have h0 : 0 ≤ (x : ℝ) * Real.log x := by positivity
            nlinarith
          linarith
        rw [hk1, mul_one] at hk
        rw [hQS, mem_filter, mem_Ioc]
        refine ⟨⟨hnx, hny⟩, hk ▸ hqp, fun s hs hsp hs20 => ?_, fun p hp hpp hpx => ?_⟩
        · have hsx : s ≤ x := by
            have : (s : ℝ) ≤ x := by
              have : (s : ℝ) ≤ ⌊z⌋₊ := Nat.cast_le.mpr hs
              linarith
            exact_mod_cast this
          have ha' : a' s = a s := by
            simp only [a']
            rw [if_pos ⟨hs, hs20⟩]
          rw [← ha']
          exact hsurv s hsx hsp
        · have hpz : ¬ p ≤ ⌊z⌋₊ := fun h => by
            have : (p : ℝ) ≤ ⌊z⌋₊ := Nat.cast_le.mpr h
            linarith
          have ha' : a' p = b p := by
            simp only [a']
            rw [if_neg (fun h => hpz h.1), if_pos hpx]
          rw [← ha']
          exact hsurv p hp hpp
    · intro m _ n _ hmn
      simp only at hmn
      omega
  have hpr' : ((Finset.Ioc x (C * x)).filter Nat.Prime).card ≤
      ((Finset.Ioc x ((C + 1) * x)).filter Nat.Prime).card := by
    apply card_le_card
    intro p hp
    rw [mem_filter, mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (by nlinarith)⟩, hp.2⟩
  have hfinal : (T.card : ℝ) ≤ (((Finset.Ioc x ((C + 1) * x)).filter Nat.Prime).card : ℝ) := by
    have e1 : (T.card : ℝ) ≤ ((Sm ∪ QS).card : ℝ) := by exact_mod_cast hTle
    have e2 : ((Sm ∪ QS).card : ℝ) ≤ (Sm.card : ℝ) + (QS.card : ℝ) := by
      exact_mod_cast card_union_le Sm QS
    have e3 : (((Finset.Ioc x (C * x)).filter Nat.Prime).card : ℝ) ≤
        (((Finset.Ioc x ((C + 1) * x)).filter Nat.Prime).card : ℝ) := by exact_mod_cast hpr'
    have e4 : (C₁ + 1) * (x : ℝ) / Real.log x = C₁ * x / Real.log x + x / Real.log x := by ring
    linarith
  exact_mod_cast hfinal

/-- `y(x) ≥ 4 x` once `log x ≥ 64 / c²` and `log₃ x ≥ 1`. -/
lemma four_le_y {c : ℝ} (hc : 0 < c) {x : ℕ} (hx : 1 ≤ x)
    (hl : 64 / c ^ 2 ≤ Real.log (x : ℝ)) (hl' : 3 ≤ Real.log (x : ℝ))
    (hl3 : 1 ≤ Real.log (Real.log (Real.log (x : ℝ)))) :
    4 * (x : ℝ) ≤
      c * x * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) := by
  set L := Real.log (x : ℝ)
  set L2 := Real.log L
  set L3 := Real.log L2
  have hLpos : 0 < L := by linarith
  have hL2pos : 0 < L2 := Real.log_pos (by linarith)
  have hsq : 8 / c ≤ Real.sqrt L := by
    rw [show 8 / c = Real.sqrt ((8 / c) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    rw [div_pow]
    have : (8 : ℝ) ^ 2 = 64 := by norm_num
    rw [this]
    exact hl
  have hL2le : L2 ≤ 2 * Real.sqrt L := log_le_two_sqrt hLpos
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hcs : 8 ≤ c * Real.sqrt L := by
    rw [div_le_iff₀ hc] at hsq
    linarith
  rw [le_div_iff₀ hL2pos]
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have key : 4 * L2 ≤ c * L * L3 := by
    have hcL : 0 ≤ c * L := mul_nonneg hc.le hLpos.le
    have h1 : c * L ≤ c * L * L3 := by
      calc c * L = c * L * 1 := by ring
        _ ≤ c * L * L3 := mul_le_mul_of_nonneg_left hl3 hcL
    have h2 : 4 * L2 ≤ 8 * Real.sqrt L := by linarith
    have h3 : 8 * Real.sqrt L ≤ c * Real.sqrt L * Real.sqrt L := by
      nlinarith [Real.sqrt_nonneg L]
    have h4 : c * Real.sqrt L * Real.sqrt L = c * L := by rw [mul_assoc, hss]
    linarith
  have : 4 * (x : ℝ) * L2 = (x : ℝ) * (4 * L2) := by ring
  rw [this]
  have : c * (x : ℝ) * L * L3 = (x : ℝ) * (c * L * L3) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left key hx0

/-- The final real comparison. -/
lemma real_compare {c D N x LN Lx L2N L2x L3N L3x : ℝ} (hc : 0 < c) (hD : 0 < D)
    (hN : 0 ≤ N) (hx : N / (2 * D) ≤ x) (hLN : 0 ≤ LN) (hLx : LN / 2 ≤ Lx)
    (hL3N : 0 ≤ L3N) (hL3x : L3N / 2 ≤ L3x) (hL2x : 0 < L2x) (hL2 : L2x ≤ L2N) :
    N * LN * L3N / L2N ≤ 8 * D / c * (c * x * Lx * L3x / L2x) := by
  have hL2N : 0 < L2N := lt_of_lt_of_le hL2x hL2
  have hcne := hc.ne'
  have hDne := hD.ne'
  have hL2Nne := hL2N.ne'
  have hND : 0 ≤ N / (2 * D) := div_nonneg hN (by linarith)
  have hx0 : 0 ≤ x := le_trans hND hx
  have hLx0 : 0 ≤ Lx := le_trans (by linarith) hLx
  have hL3x0 : 0 ≤ L3x := le_trans (by linarith) hL3x
  have e : N * LN * L3N / L2N = 8 * D / c * (c * (N / (2 * D)) * (LN / 2) * (L3N / 2) / L2N) := by
    field_simp
    ring
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith) hc.le)
  have hnum : c * (N / (2 * D)) * (LN / 2) * (L3N / 2) ≤ c * x * Lx * L3x := by
    have h1 : c * (N / (2 * D)) ≤ c * x := mul_le_mul_of_nonneg_left hx hc.le
    have h2 : c * (N / (2 * D)) * (LN / 2) ≤ c * x * Lx :=
      mul_le_mul h1 hLx (by linarith) (mul_nonneg hc.le hx0)
    exact mul_le_mul h2 hL3x (by linarith) (mul_nonneg (mul_nonneg hc.le hx0) hLx0)
  calc c * (N / (2 * D)) * (LN / 2) * (L3N / 2) / L2N
      ≤ c * x * Lx * L3x / L2N := div_le_div_of_nonneg_right hnum hL2N.le
    _ ≤ c * x * Lx * L3x / L2x :=
        div_le_div_of_nonneg_left (mul_nonneg (mul_nonneg (mul_nonneg hc.le hx0) hLx0) hL3x0)
          hL2x hL2

theorem main : H1 → H2 → H3 → type_of% @Erdos687.erdos_687.variants.fgkmt := by
  intro h1 h2 h3
  obtain ⟨c, hc, D, hD, hcov⟩ := covered_eventually h1 h2 h3
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hcov
  have hx : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hx
  have hl2 : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hl
  have hl3 : Tendsto (fun x : ℕ => Real.log (Real.log (Real.log (x : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hl2
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.mp
    ((hl.eventually_ge_atTop (max (64 / c ^ 2) 3)).and (hl3.eventually_ge_atTop 1))
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  refine Asymptotics.IsBigO.of_bound (16 * D / c) ?_
  filter_upwards [eventually_ge_atTop (D * (x₀ + x₁ + 2) + 4 * D ^ 2),
    hl.eventually_ge_atTop 3, hl2.eventually_ge_atTop 2, hl3.eventually_ge_atTop 2] with
    N hN hN1 hN2 hN3
  set x := N / D with hxdef
  have hDx : D * x ≤ N := Nat.mul_div_le N D
  have hNlt : N < D * (x + 1) := by
    have h1 := Nat.div_add_mod N D
    have h2 := Nat.mod_lt N hD
    rw [Nat.mul_add, Nat.mul_one]
    generalize D * x = t at h1 ⊢
    omega
  have hxge : x₀ + x₁ + 2 ≤ x := by
    rw [hxdef, Nat.le_div_iff_mul_le hD]
    nlinarith
  have hxN : x ≤ N := Nat.div_le_self N D
  -- covering at `D x`, then at `N`
  have hcovx := hx₀ x (by omega)
  set k := ⌊c * x * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)⌋₊ - x
    with hk
  have hcovN : Green46.IsCoveredByResidues N k := by
    obtain ⟨α, hα⟩ := hcovx
    exact ⟨α, fun m hm => by
      obtain ⟨p, hp, hpp, hpm⟩ := hα m hm
      exact ⟨p, hp.trans hDx, hpp, hpm⟩⟩
  have hkY : k ≤ Erdos687.Y N :=
    le_csSup ⟨primorial N, fun _ hh => (Erdos687.lt_primorial_of_isCoveredByResidues hh).le⟩ hcovN
  -- `k ≥ y / 2`
  obtain ⟨hlx, hl3x⟩ := hx₁ x (by omega)
  have hx1 : 1 ≤ x := by omega
  have hy4 := four_le_y hc hx1 (le_trans (le_max_left _ _) hlx)
    (le_trans (le_max_right _ _) hlx) hl3x
  set yx := c * x * Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) with hyx
  have hxR1 : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hkR : yx / 2 ≤ (k : ℝ) := by
    have hfl := Nat.lt_floor_add_one yx
    have hxle : x ≤ ⌊yx⌋₊ := by
      apply Nat.le_floor
      linarith
    rw [hk, Nat.cast_sub hxle]
    linarith
  have hYR : (k : ℝ) ≤ (Erdos687.Y N : ℝ) := by exact_mod_cast hkY
  -- comparison of the logarithms at `x` and `N`
  have hNR : (4 * (D : ℝ) ^ 2) ≤ N := by
    have : 4 * D ^ 2 ≤ N := le_trans (Nat.le_add_left _ _) hN
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by nlinarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hxNR : (x : ℝ) ≤ N := by exact_mod_cast hxN
  have hxlow : (N : ℝ) / (2 * D) ≤ x := by
    have h1 : (N : ℝ) < D * (x + 1) := by exact_mod_cast hNlt
    rw [div_le_iff₀ (by positivity)]
    have h2 : (D : ℝ) * 2 ≤ D * x := by
      have : (2 : ℝ) ≤ x := by
        have : 2 ≤ x := by omega
        exact_mod_cast this
      nlinarith
    nlinarith
  have hsqrtN : Real.sqrt N ≤ x := by
    have h2D : 2 * (D : ℝ) ≤ Real.sqrt N := by
      rw [show 2 * (D : ℝ) = Real.sqrt ((2 * D) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hs := Real.mul_self_sqrt hNpos.le
    have hsp : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
    rw [div_le_iff₀ (by positivity)] at hxlow
    nlinarith
  have hLxN : Real.log N / 2 ≤ Real.log x := by
    have := Real.log_le_log (Real.sqrt_pos.mpr hNpos) hsqrtN
    rwa [Real.log_sqrt hNpos.le] at this
  set LN := Real.log (N : ℝ)
  set L2N := Real.log LN
  set L3N := Real.log L2N
  have hL2Npos : 0 < L2N := by linarith
  have hLNpos : 0 < LN := by linarith
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hLx2pos : 0 < LN / 2 := by positivity
  have hL2x : L2N / 2 ≤ Real.log (Real.log x) := by
    have h1 := Real.log_le_log hLx2pos hLxN
    rw [Real.log_div hLNpos.ne' (by norm_num)] at h1
    linarith
  have hL2xpos : 0 < Real.log (Real.log x) := by linarith
  have hL2xle : Real.log (Real.log x) ≤ L2N := by
    apply Real.log_le_log (by linarith) (Real.log_le_log hxpos hxNR)
  have hL3x : L3N / 2 ≤ Real.log (Real.log (Real.log x)) := by
    have h1 := Real.log_le_log (by positivity) hL2x
    rw [Real.log_div hL2Npos.ne' (by norm_num)] at h1
    linarith
  have hcmp := real_compare hc hDR hNpos.le hxlow hLNpos.le hLxN (by linarith) hL3x hL2xpos
    hL2xle
  -- conclude
  have hf0 : 0 ≤ (N : ℝ) * LN * L3N / L2N :=
    div_nonneg (mul_nonneg (mul_nonneg hNpos.le hLNpos.le) (by linarith)) hL2Npos.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf0,
    abs_of_nonneg (Nat.cast_nonneg _)]
  calc (N : ℝ) * LN * L3N / L2N ≤ 8 * D / c * yx := hcmp
    _ ≤ 8 * D / c * (2 * (k : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg (by positivity) hc.le)
        linarith
    _ = 16 * D / c * (k : ℝ) := by ring
    _ ≤ 16 * D / c * (Erdos687.Y N : ℝ) :=
        mul_le_mul_of_nonneg_left hYR (div_nonneg (by positivity) hc.le)

end OMA.R_Erdos687_erdos_687_variants_fgkmt_R1
