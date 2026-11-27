import FormalConjectures.ErdosProblems.«977»
import Mathlib

-- Reduction Erdos977.erdos_977.variants.stewart.R1 of Stewart's bound for P(2^n - 1)
-- Source: C. L. Stewart, On divisors of Lucas and Lehmer numbers, Acta Math. 211 (2013),
--   291-314 (arXiv:1008.1274), Lemma 8 of arXiv:1008.1274 and the proof of Theorem 1.1.
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Stewart's lower bound for the greatest prime factor of `2^n - 1`

Following Section 6 of Stewart's paper, specialised to `(α, β) = (2, 1)`:

* `H1` (Stewart's Lemma 8 of arXiv:1008.1274, a consequence of K. Yu's estimates for p-adic linear forms in
  logarithms): for every prime `p` above an absolute constant and every `n > 1`,
  `ord_p (2^n - 1) < p * exp (-log p / (51.9 log log p)) * log 2 * log n`.
  This is the only deep input.
* `H2` (cyclotomic part, elementary): the part of `2^n - 1` made of primes `p ≡ 1 (mod n)` is at
  least `2^φ(n) / (4 n)`. Indeed `Φ_n(2) ≥ 2^φ(n) / 4` divides `2^n - 1`, and a prime factor of
  `Φ_n(2)` is either `≡ 1 (mod n)` or is the largest prime factor of `n`, in which case it
  divides `Φ_n(2)` exactly once.
* `H3` (elementary): `n ≤ φ(n) * (log₂ n + 1)`, because `n / φ(n) = ∏ p / (p - 1) ≤ ω(n) + 1`.
* `H4` (elementary real analysis): the inequality that `main` extracts forces
  `P ≥ c * n ^ (1 + 1 / (104 log log n))` for all large `n`. The slack between `51.9` and
  `52 = 104 / 2` absorbs all the logarithmic factors.

`main` bounds each prime power `p ^ ord_p (2^n - 1)` with `p ≡ 1 (mod n)` by `H1` (such primes
exceed `n`, and `x * exp (-log x / (51.9 log log x))` is increasing), counts these primes
trivially by `P / n`, where `P = P(2^n - 1)`, and compares with `H2` and `H3` to get
`n log 2 / (log₂ n + 1) ≤ log (4 n) + (P / n) * P * exp (-log P / (51.9 log log P)) * log 2 * log n
* log P`. Then `H4` finishes.
-/

namespace OMA.R_Erdos977_erdos_977_variants_stewart_R1

open Real Filter

/-- Stewart's Lemma 8 of arXiv:1008.1274 for `(α, β) = (2, 1)` (Yu's p-adic linear forms in logarithms). -/
def H1 : Prop :=
  ∃ C : ℕ, ∀ p : ℕ, p.Prime → C < p → ∀ n : ℕ, 1 < n →
    (padicValNat p (2 ^ n - 1) : ℝ) <
      p * exp (-log p / (51.9 * log (log p))) * log 2 * log n

/-- The part of `2^n - 1` supported on primes `≡ 1 (mod n)` is at least `2^φ(n) / (4 n)`. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    2 ^ n.totient ≤ 4 * n * ∏ p ∈ (2 ^ n - 1).primeFactors.filter (fun p => p % n = 1),
      p ^ padicValNat p (2 ^ n - 1)

/-- `n / φ(n) ≤ log₂ n + 1`. -/
def H3 : Prop := ∀ n : ℕ, 1 ≤ n → n ≤ n.totient * (Nat.log 2 n + 1)

/-- The final asymptotic comparison. -/
def H4 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ P : ℕ,
    (n : ℝ) / ((Nat.log 2 n : ℝ) + 1) * log 2 ≤
        log (4 * n) + (P : ℝ) / n *
          ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P) →
      c * (n : ℝ) ^ (1 + 1 / (104 * log (log n))) ≤ P

/-- `x * exp (-log x / (51.9 log log x))` is nondecreasing on `[16, ∞)`. -/
lemma mono_aux {x y : ℝ} (hx : 16 ≤ x) (hxy : x ≤ y) :
    x * exp (-log x / (51.9 * log (log x))) ≤ y * exp (-log y / (51.9 * log (log y))) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have h16 : exp 1 ≤ log 16 := by
    have h : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [h, log_pow]
    have h1 := Real.log_two_gt_d9
    have h2 := Real.exp_one_lt_d9
    push_cast
    linarith
  have he : 0 < exp (1 : ℝ) := exp_pos 1
  have hlx : exp 1 ≤ log x := h16.trans (log_le_log (by norm_num) hx)
  have hlxy : log x ≤ log y := log_le_log hx0 hxy
  have hllx : 1 ≤ log (log x) := by
    have := log_le_log he hlx
    rwa [log_exp] at this
  have hll : log (log x) ≤ log (log y) := log_le_log (by linarith) hlxy
  have key : ∀ z : ℝ, 0 < z → z * exp (-log z / (51.9 * log (log z))) =
      exp (log z * (1 - 1 / (51.9 * log (log z)))) := by
    intro z hz
    have : log z * (1 - 1 / (51.9 * log (log z))) =
        log z + -log z / (51.9 * log (log z)) := by ring
    rw [this, exp_add, exp_log hz]
  rw [key x hx0, key y hy0]
  apply exp_le_exp.mpr
  have hpos : (0 : ℝ) < 51.9 * log (log x) := by nlinarith
  have ha : 1 / (51.9 * log (log y)) ≤ 1 / (51.9 * log (log x)) :=
    one_div_le_one_div_of_le hpos (by linarith)
  have ha1 : 1 / (51.9 * log (log x)) ≤ 1 := by
    rw [div_le_one hpos]
    nlinarith
  have hlx0 : 0 ≤ log x := by linarith
  have hly0 : 0 ≤ log y := by linarith
  calc log x * (1 - 1 / (51.9 * log (log x)))
      ≤ log y * (1 - 1 / (51.9 * log (log x))) :=
        mul_le_mul_of_nonneg_right hlxy (by linarith)
    _ ≤ log y * (1 - 1 / (51.9 * log (log y))) :=
        mul_le_mul_of_nonneg_left (by linarith) hly0

/-- The inequality extracted from `H1`, `H2`, `H3` for a single large `n`. -/
lemma core (C : ℕ)
    (hC : ∀ p : ℕ, p.Prime → C < p → ∀ n : ℕ, 1 < n →
      (padicValNat p (2 ^ n - 1) : ℝ) <
        p * exp (-log p / (51.9 * log (log p))) * log 2 * log n)
    (h2 : H2) (h3 : H3) (n N P : ℕ) (hN : N = 2 ^ n - 1) (hP : P = Nat.maxPrimeFac N)
    (hn16 : 16 ≤ n) (hnC : C ≤ n) :
    (n : ℝ) / ((Nat.log 2 n : ℝ) + 1) * log 2 ≤
      log (4 * n) + (P : ℝ) / n *
        ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P) := by
  have hN0 : N ≠ 0 := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn16
  have hlogn : 0 < log (n : ℝ) := log_pos (by linarith)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogP : 0 ≤ log (P : ℝ) := log_natCast_nonneg P
  have hA0 : 0 ≤ (P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n :=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg P) (exp_pos _).le) hlog2.le) hlogn.le
  have hB0 : 0 ≤ (P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P :=
    mul_nonneg hA0 hlogP
  -- the primes that count
  have hmem : ∀ p ∈ N.primeFactors.filter (fun p => p % n = 1), p.Prime ∧ n < p ∧ p ≤ P := by
    intro p hp
    rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
    obtain ⟨⟨hpp, hdvd, _⟩, hmod⟩ := hp
    refine ⟨hpp, ?_, hP ▸ Nat.le_maxPrimeFac hN0 hpp hdvd⟩
    by_contra hle
    rw [not_lt] at hle
    rcases hle.eq_or_lt with h | h
    · subst h
      rw [Nat.mod_self] at hmod
      omega
    · rw [Nat.mod_eq_of_lt h] at hmod
      subst hmod
      exact Nat.not_prime_one hpp
  have hterm : ∀ p ∈ N.primeFactors.filter (fun p => p % n = 1),
      (p : ℝ) ^ padicValNat p N ≤
        exp ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P) := by
    intro p hp
    obtain ⟨hpp, hnp, hpP⟩ := hmem p hp
    have hv := hC p hpp (by omega) n (by omega)
    rw [← hN] at hv
    have hpR : (16 : ℝ) ≤ p := by exact_mod_cast (by omega : 16 ≤ p)
    have hpPR : (p : ℝ) ≤ P := by exact_mod_cast hpP
    have hp0 : (0 : ℝ) < p := by linarith
    have hlogp : 0 < log (p : ℝ) := log_pos (by linarith)
    have hmono := mono_aux hpR hpPR
    have hlogpP : log (p : ℝ) ≤ log P := log_le_log hp0 hpPR
    have hexp : (p : ℝ) ^ padicValNat p N = exp ((padicValNat p N : ℝ) * log p) := by
      rw [Real.exp_nat_mul, exp_log hp0]
    rw [hexp]
    apply exp_le_exp.mpr
    calc (padicValNat p N : ℝ) * log p
        ≤ ((p : ℝ) * exp (-log p / (51.9 * log (log p))) * log 2 * log n) * log p :=
          mul_le_mul_of_nonneg_right hv.le hlogp.le
      _ ≤ ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n) * log P :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hlog2.le) hlogn.le)
            hlogpP hlogp.le hA0
  -- there are at most P / n of them
  have hcard : (N.primeFactors.filter (fun p => p % n = 1)).card ≤ P / n := by
    have h : (N.primeFactors.filter (fun p => p % n = 1)).card ≤ (Finset.Icc 1 (P / n)).card := by
      apply Finset.card_le_card_of_injOn (fun p => p / n)
      · intro p hp
        obtain ⟨hpp, hnp, hpP⟩ := hmem p hp
        exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr
          ⟨(Nat.one_le_div_iff (by omega)).mpr hnp.le, Nat.div_le_div_right hpP⟩)
      · intro p hp q hq hpq
        have h1 : p % n = 1 := (Finset.mem_filter.mp hp).2
        have h2 : q % n = 1 := (Finset.mem_filter.mp hq).2
        have hpq' : p / n = q / n := hpq
        have e1 := Nat.div_add_mod p n
        have e2 := Nat.div_add_mod q n
        rw [hpq', h1] at e1
        rw [h2] at e2
        exact e1.symm.trans e2
    simpa using h
  have hcardR : ((N.primeFactors.filter (fun p => p % n = 1)).card : ℝ) ≤ (P : ℝ) / n :=
    (Nat.cast_le.mpr hcard).trans Nat.cast_div_le
  have hprod : (∏ p ∈ N.primeFactors.filter (fun p => p % n = 1), (p : ℝ) ^ padicValNat p N) ≤
      exp ((P : ℝ) / n *
        ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P)) := by
    calc (∏ p ∈ N.primeFactors.filter (fun p => p % n = 1), (p : ℝ) ^ padicValNat p N)
        ≤ ∏ _p ∈ N.primeFactors.filter (fun p => p % n = 1),
            exp ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P) :=
          Finset.prod_le_prod (fun p _ => by positivity) hterm
      _ = exp (((N.primeFactors.filter (fun p => p % n = 1)).card : ℝ) *
            ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P)) := by
          rw [Finset.prod_const, Real.exp_nat_mul]
      _ ≤ _ := exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcardR hB0)
  have h2' := h2 n (by omega)
  rw [← hN] at h2'
  have h2R : (2 : ℝ) ^ n.totient ≤ 4 * n * exp ((P : ℝ) / n *
      ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P)) := by
    have hcast : ((2 ^ n.totient : ℕ) : ℝ) ≤
        ((4 * n * ∏ p ∈ N.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p N : ℕ) : ℝ) :=
      Nat.cast_le.mpr h2'
    push_cast at hcast
    exact hcast.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hlog : (n.totient : ℝ) * log 2 ≤ log (4 * n) + (P : ℝ) / n *
      ((P : ℝ) * exp (-log P / (51.9 * log (log P))) * log 2 * log n * log P) := by
    have h := log_le_log (by positivity) h2R
    rwa [log_pow, log_mul (by positivity) (exp_pos _).ne', log_exp] at h
  have h3' := h3 n (by omega)
  have h3R : (n : ℝ) / ((Nat.log 2 n : ℝ) + 1) ≤ n.totient := by
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast h3'
  exact (mul_le_mul_of_nonneg_right h3R hlog2.le).trans hlog

theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos977.erdos_977.variants.stewart := by
  rintro ⟨C, hC⟩ h2 h3 ⟨c, hc, h4⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [h4, eventually_ge_atTop (max C 16)] with n hn hnC
  exact hn _ (core C hC h2 h3 n _ _ rfl rfl (le_trans (le_max_right _ _) hnC)
    (le_trans (le_max_left _ _) hnC))

end OMA.R_Erdos977_erdos_977_variants_stewart_R1
