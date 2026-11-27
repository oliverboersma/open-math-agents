import FormalConjectures.ErdosProblems.«687»
import Mathlib.NumberTheory.Chebyshev

-- Reduction Erdos687.erdos_687.variants.iwaniec.R1 of Erdős Problem 687 — iwaniec
-- Credit: @ItsNotTheGabs
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Shifted-sieve and Mertens reduction of Iwaniec's bound `Y(x) ≪ x²`

Following Iwaniec's 1978 paper *On the problem of Jacobsthal* (Demonstratio Math. 11, 225–231),
we reduce `Erdos687.erdos_687.variants.iwaniec` to two classical, independent theorems:

1. `H1`: **Iwaniec's shifted-sieve gap bound for primorials**: there exists `C > 0` such that
   for all sufficiently large `x`, every shift `M : ℕ`, and every interval length
   `y ≥ C * π(x)² * log(π(x)) / ∏_{p ≤ x} (1 - 1 / p)`, the interval `[M + 1, M + y]` contains
   an integer not divisible by any prime `p ≤ x`.
2. `H2`: **Mertens' third theorem lower bound**: there exists `c₀ > 0` such that
   `c₀ / log x ≤ ∏_{p ≤ x} (1 - 1 / p)` for all `x ≥ 2`.

Inside this reduction we prove unconditionally:
- `exists_shift_of_isCoveredByResidues`: Chinese Remainder Theorem reduction turning any
  residue covering of `[1, y]` by primes `p ≤ x` into a shifted interval `[M + 1, M + y]`
  containing no `x`-rough integer.
- `Y_lt_of_forall_shift_exists_rough`: upper bound `Erdos687.Y x < B` from uniform existence
  of `x`-rough integers in all shifted intervals of length `B`.
- `primeCounting_le_eight_mul_div_log`: explicit Chebyshev bound `π(x) ≤ 8 * x / log x` for
  all `x ≥ 2`, deduced from `Chebyshev.pi_le_log4_mul_div`.
- `main`: assembling `H1`, `H2`, Chebyshev's bound, and CRT into
  `(fun x : ℕ ↦ (Erdos687.Y x : ℝ)) =O[Filter.atTop] (fun x : ℕ ↦ (x : ℝ) ^ 2)`.
-/

namespace OMA.R_Erdos687_erdos_687_variants_iwaniec_R1

open Filter Finset Real

/-- Iwaniec's shifted-sieve gap bound for primorials ([Iw78]):
there exists `C > 0` such that for all sufficiently large `x : ℕ`, every shift `M : ℕ`, and
every `y : ℕ` with `C * (π(x) ^ 2 * log (π(x))) / ∏_{p ≤ x} (1 - 1 / p) ≤ y`,
the interval `[M + 1, M + y]` contains an integer not divisible by any prime `p ≤ x`. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ M y : ℕ,
    C * ((Nat.primeCounting x : ℝ) ^ 2 * Real.log (Nat.primeCounting x : ℝ)) /
      (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤ (y : ℝ) →
    ∃ n ∈ Finset.Icc (M + 1) (M + y), ∀ p ≤ x, p.Prime → ¬ (p ∣ n)

/-- Mertens' third theorem lower bound (Mertens 1874):
there exists `c₀ > 0` such that `c₀ / log x ≤ ∏_{p ≤ x} (1 - 1 / p)` for all `x ≥ 2`. -/
def H2 : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℕ, 2 ≤ x →
    c₀ / Real.log (x : ℝ) ≤
      ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)

lemma eulerProd_pos (x : ℕ) :
    0 < ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
  apply Finset.prod_pos
  intro p hp
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
  have hinv : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
  linarith

lemma exists_shift_of_isCoveredByResidues {x y : ℕ} (h : Green46.IsCoveredByResidues x y) :
    ∃ M : ℕ, ∀ n ∈ Finset.Icc (M + 1) (M + y), ∃ p ≤ x, p.Prime ∧ p ∣ n := by
  obtain ⟨a, ha⟩ := h
  let t := (Finset.range (x + 1)).filter Nat.Prime
  have hs : ∀ p ∈ t, (fun p : ℕ ↦ p) p ≠ 0 :=
    fun p hp ↦ (Finset.mem_filter.mp hp).2.ne_zero
  have pp : Set.Pairwise (t : Set ℕ) (Function.onFun Nat.Coprime fun p : ℕ ↦ p) :=
    fun p hp q hq hpq ↦
      (Nat.coprime_primes (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2).2 hpq
  let k := Nat.chineseRemainderOfFinset (fun p ↦ p - a p % p) (fun p ↦ p) t hs pp
  refine ⟨(k : ℕ), fun n hn ↦ ?_⟩
  obtain ⟨hn1, hny⟩ := Finset.mem_Icc.mp hn
  let m : ℕ := n - (k : ℕ)
  have hm_mem : m ∈ Finset.Icc 1 y := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨p, hpx, hp, hpm⟩ := ha m hm_mem
  have hpt : p ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpx), hp⟩
  have hkp : (k : ℕ) ≡ p - a p % p [MOD p] := k.2 p hpt
  have hnm : (k : ℕ) + m = n := by omega
  have hsum : n ≡ (p - a p % p) + a p [MOD p] := by
    rw [← hnm]
    exact hkp.add hpm
  have hrem_le : a p % p ≤ p := (Nat.mod_lt (a p) hp.pos).le
  have hdiv_eq : (p - a p % p) + a p = p * (1 + a p / p) := by
    have hdm := Nat.div_add_mod (a p) p
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hzero : (p - a p % p) + a p ≡ 0 [MOD p] := by
    rw [hdiv_eq]
    exact Nat.modEq_zero_iff_dvd.mpr ⟨1 + a p / p, rfl⟩
  have hdvd : p ∣ n := Nat.modEq_zero_iff_dvd.mp (hsum.trans hzero)
  exact ⟨p, hpx, hp, hdvd⟩

lemma Y_lt_of_forall_shift_exists_rough {x B : ℕ} (hB : 0 < B)
    (h : ∀ M : ℕ, ∃ n ∈ Finset.Icc (M + 1) (M + B), ∀ p ≤ x, p.Prime → ¬ (p ∣ n)) :
    Erdos687.Y x < B := by
  have hnotB : ¬ Green46.IsCoveredByResidues x B := by
    intro hcov
    obtain ⟨M, hM⟩ := exists_shift_of_isCoveredByResidues hcov
    obtain ⟨n, hn, hrough⟩ := h M
    obtain ⟨p, hpx, hp, hpn⟩ := hM n hn
    exact hrough p hpx hp hpn
  have hle : ∀ y ∈ {y : ℕ | Green46.IsCoveredByResidues x y}, y ≤ B - 1 := by
    intro y hy
    by_contra hgt
    have hBy : B ≤ y := by omega
    apply hnotB
    obtain ⟨a, ha⟩ := hy
    refine ⟨a, fun m hm ↦ ha m ?_⟩
    obtain ⟨hm1, hmB⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨hm1, hmB.trans hBy⟩
  have h0 : (0 : ℕ) ∈ {y : ℕ | Green46.IsCoveredByResidues x y} := by
    refine ⟨fun _ ↦ 0, fun m hm ↦ ?_⟩
    simp at hm
  have hsup : Erdos687.Y x ≤ B - 1 := csSup_le ⟨0, h0⟩ hle
  omega

lemma primeCounting_le_self (x : ℕ) : Nat.primeCounting x ≤ x := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have hsub : Nat.primesLE x ⊆ (Finset.range (x + 1)).erase 0 := by
    intro p hp
    rw [Finset.mem_erase, Finset.mem_range]
    have hp' := Nat.mem_primesLE.mp hp
    exact ⟨hp'.2.ne_zero, Nat.lt_succ_of_le hp'.1⟩
  calc
    (Nat.primesLE x).card ≤ ((Finset.range (x + 1)).erase 0).card :=
      Finset.card_le_card hsub
    _ = x := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.succ_pos x)), Finset.card_range]
      omega

lemma one_le_primeCounting {x : ℕ} (hx : 2 ≤ x) : 1 ≤ Nat.primeCounting x := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact Finset.card_pos.mpr ⟨2, Nat.mem_primesLE.mpr ⟨hx, Nat.prime_two⟩⟩

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

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.variants.iwaniec := by
  rintro ⟨C, hC, hIw⟩ ⟨c₀, hc₀, hMert⟩
  let K : ℝ := 64 * C / c₀ + 1
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [hIw, eventually_ge_atTop 2] with x hIw_x hx2
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hpi_ge1 : (1 : ℝ) ≤ (Nat.primeCounting x : ℝ) := by
    exact_mod_cast one_le_primeCounting hx2
  have hpi_le_x : (Nat.primeCounting x : ℝ) ≤ (x : ℝ) := by
    exact_mod_cast primeCounting_le_self x
  have hpi_pos : (0 : ℝ) < (Nat.primeCounting x : ℝ) := by linarith
  have hlog_pi_nonneg : 0 ≤ Real.log (Nat.primeCounting x : ℝ) := Real.log_nonneg hpi_ge1
  have hlog_pi_le : Real.log (Nat.primeCounting x : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log hpi_pos hpi_le_x
  have hpi_ub : (Nat.primeCounting x : ℝ) ≤ 8 * (x : ℝ) / Real.log (x : ℝ) :=
    primeCounting_le_eight_mul_div_log hx2
  have hV_pos : 0 < ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) :=
    eulerProd_pos x
  have hV_lb : c₀ / Real.log (x : ℝ) ≤
      ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) :=
    hMert x hx2
  have hnum_le :
      (Nat.primeCounting x : ℝ) ^ 2 * Real.log (Nat.primeCounting x : ℝ) ≤
        64 * (x : ℝ) ^ 2 / Real.log (x : ℝ) := by
    have hsq : (Nat.primeCounting x : ℝ) ^ 2 ≤ (8 * (x : ℝ) / Real.log (x : ℝ)) ^ 2 := by
      gcongr
    calc
      (Nat.primeCounting x : ℝ) ^ 2 * Real.log (Nat.primeCounting x : ℝ)
          ≤ (8 * (x : ℝ) / Real.log (x : ℝ)) ^ 2 * Real.log (x : ℝ) := by
            gcongr
      _ = 64 * (x : ℝ) ^ 2 / Real.log (x : ℝ) := by
            field_simp
            ring
  have hratio_le :
      C * ((Nat.primeCounting x : ℝ) ^ 2 * Real.log (Nat.primeCounting x : ℝ)) /
        (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤
          (64 * C / c₀) * (x : ℝ) ^ 2 := by
    have hnum_nn : 0 ≤ C * ((Nat.primeCounting x : ℝ) ^ 2 * Real.log (Nat.primeCounting x : ℝ)) := by
      positivity
    have hden_pos : 0 < c₀ / Real.log (x : ℝ) := div_pos hc₀ hlogx_pos
    calc
      C * ((Nat.primeCounting x : ℝ) ^ 2 * Real.log (Nat.primeCounting x : ℝ)) /
          (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹))
          ≤ C * (64 * (x : ℝ) ^ 2 / Real.log (x : ℝ)) / (c₀ / Real.log (x : ℝ)) := by
            gcongr
      _ = (64 * C / c₀) * (x : ℝ) ^ 2 := by
            field_simp
  let B : ℕ := ⌈(64 * C / c₀) * (x : ℝ) ^ 2⌉₊ + 1
  have hB_pos : 0 < B := Nat.succ_pos _
  have hB_ge :
      C * ((Nat.primeCounting x : ℝ) ^ 2 * Real.log (Nat.primeCounting x : ℝ)) /
        (∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹)) ≤ (B : ℝ) := by
    have hceil : (64 * C / c₀) * (x : ℝ) ^ 2 ≤ (⌈(64 * C / c₀) * (x : ℝ) ^ 2⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hsucc : (⌈(64 * C / c₀) * (x : ℝ) ^ 2⌉₊ : ℝ) ≤ (B : ℝ) := by
      dsimp [B]
      push_cast
      linarith
    exact hratio_le.trans (hceil.trans hsucc)
  have hY_lt : Erdos687.Y x < B :=
    Y_lt_of_forall_shift_exists_rough hB_pos (fun M ↦ hIw_x M B hB_ge)
  have hY_le_ceil : (Erdos687.Y x : ℝ) ≤ (⌈(64 * C / c₀) * (x : ℝ) ^ 2⌉₊ : ℝ) := by
    exact_mod_cast Nat.le_of_lt_succ hY_lt
  have hceil_lt : (⌈(64 * C / c₀) * (x : ℝ) ^ 2⌉₊ : ℝ) < (64 * C / c₀) * (x : ℝ) ^ 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hx2_ge1 : (1 : ℝ) ≤ (x : ℝ) ^ 2 := by nlinarith
  have hY_bound : (Erdos687.Y x : ℝ) ≤ K * (x : ℝ) ^ 2 := by
    dsimp [K]
    nlinarith
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
  exact hY_bound

end OMA.R_Erdos687_erdos_687_variants_iwaniec_R1
