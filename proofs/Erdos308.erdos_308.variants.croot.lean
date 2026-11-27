import FormalConjectures.ErdosProblems.«308»
import Mathlib

/-!
# Croot's bounds for the first missing integer

This proof combines @marcusbuffett's Erdős 308 reduction (PR 4519) with
the harmonic-weight estimate (PR 4735) and the constructive argument
(PRs 5151, 5534, 5615 and 5676). All bounds below are proved in this file.
-/

section

/-! A large prime p with J=(N/p) and J*J!<p cannot divide any denominator
in an integral reciprocal sum: after clearing the other denominators a
positive numerator at most J*J! would have to be divisible by p.
For the lower bound one only needs one representation per large cutoff,
since its target integer can increase by at most one per step.

The fixed-integer Egyptian expansion below is from @PanPapag's merged
Erdős 283 Burr proof, adapted from @Blackmore-Math (#1570) and the
Apache-2.0 Shashi456/erdos-formalizations project, Erdos/P283/Egyptian.lean.
Copyright (c) 2026. The arithmetic obstruction and cutoff argument are new. -/
namespace OMA.R_Erdos308_erdos_308_variants_croot_R1

open Finset Real Filter Erdos308
open scoped Topology

/-- Croot's constructive input needs just the top integer at each cutoff. -/
def H1 : Prop := ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ N : ℕ in atTop,
  IsRepresentable N ⌊(harmonic N:ℝ) - 9/2*(1+e N)*(log (log N))^2/log N⌋₊

/-- Harmonic weight of the excluded large-prime multiples. This is an
estimate about primes alone and involves no Egyptian representation. -/
def H2 : Prop :=
  let D (N : ℕ) := (Icc 1 N).filter fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial < p
  Tendsto (fun N : ℕ => (∑ n ∈ D N, (1:ℝ)/n)*log N/(log (log N))^2) atTop (𝓝 (1/2:ℝ))


lemma forced_omission {N k : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N)
    (hs : ∑ d ∈ A, (1:ℚ)/d = k) {p : ℕ} (hp : p.Prime)
    (small : (N/p)*(N/p).factorial < p) (d : ℕ) (hd : d ∈ A) : ¬p ∣ d := by
  classical
  intro hpd
  let J := N/p
  let F := J.factorial
  let E := A.filter (p ∣ ·)
  let B := A.filter (fun n => ¬p ∣ n)
  let D := ∏ n ∈ B, n
  let C := ∑ n ∈ E, F/(n/p)
  let Q := ∑ n ∈ B, D/n
  have bounds {n : ℕ} (hn : n ∈ E) : 0 < n/p ∧ n/p ≤ J := by
    have h := (mem_filter.mp hn)
    have g := mem_Icc.mp (hA h.1)
    exact ⟨Nat.div_pos (Nat.le_of_dvd g.1 h.2) hp.pos,Nat.div_le_div_right g.2⟩
  have hc : E.card ≤ J := by
    have h : E.card ≤ (Icc 1 J).card := by
      apply card_le_card_of_injOn (·/p)
      · intro n hn; exact mem_Icc.mpr (bounds hn)
      · intro a ha b hb he
        have ha' := Nat.div_mul_cancel (mem_filter.mp ha).2
        have hb' := Nat.div_mul_cancel (mem_filter.mp hb).2
        change a/p = b/p at he
        grind
    simpa using h
  have cu : C < p := calc
    C ≤ ∑ _n ∈ E, F := sum_le_sum fun n _ => Nat.div_le_self _ _
    _ = E.card*F := by simp
    _ ≤ J*F := Nat.mul_le_mul_right F hc
    _ < p := small
  have cpos : 0 < C := by
    apply sum_pos' (fun _ _ => Nat.zero_le _)
    refine ⟨d,mem_filter.mpr ⟨hd,hpd⟩,?_⟩
    have b := bounds (mem_filter.mpr ⟨hd,hpd⟩ : d ∈ E)
    exact Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.dvd_factorial b.1 b.2)) b.1
  have nd : ¬ p ∣ D := by
    rw [show D = ∏ n ∈ B, n by rfl,hp.prime.dvd_finsetProd_iff]
    rintro ⟨n,hn,hpn⟩
    exact (mem_filter.mp hn).2 hpn
  have hE : (p:ℚ)*F*(∑ n ∈ E, (1:ℚ)/n) = C := by
    rw [mul_sum]
    dsimp [C]
    push_cast
    apply sum_congr rfl
    intro n hn
    have h := mem_filter.mp hn
    have b := bounds hn
    have dF : n/p ∣ F := Nat.dvd_factorial b.1 b.2
    rw [Nat.cast_div dF (by exact_mod_cast b.1.ne' : ((n/p:ℕ):ℚ) ≠ 0)]
    have eqn : (n:ℚ) = (n/p:ℕ)* (p:ℚ) := by exact_mod_cast (Nat.div_mul_cancel h.2).symm
    conv_lhs => rw [eqn]
    have pp : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have np : ((n/p:ℕ):ℚ) ≠ 0 := by exact_mod_cast b.1.ne'
    field_simp
  have hB : (D:ℚ)*(∑ n ∈ B, (1:ℚ)/n) = Q := by
    rw [mul_sum]
    dsimp [Q]
    push_cast
    apply sum_congr rfl
    intro n hn
    have dd : n ∣ D := dvd_prod_of_mem id hn
    have nz : (n:ℚ) ≠ 0 := by exact_mod_cast (show 0 < n from (mem_Icc.mp (hA (mem_filter.mp hn).1)).1).ne'
    rw [Nat.cast_div dd nz]
    ring
  have split : (∑ n ∈ E, (1:ℚ)/n) + ∑ n ∈ B, (1:ℚ)/n = k :=
    (sum_filter_add_sum_filter_not ..).trans hs
  have eqn : D*C + p*F*Q = p*F*D*k := by
    apply Nat.cast_injective (R := ℚ)
    push_cast
    rw [← hE,← hB,← split]
    ring
  have dvd : p ∣ D*C := by
    apply (Nat.dvd_add_iff_left (show p ∣ p*F*Q by exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).mpr
    rw [eqn]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  exact (not_le_of_gt cu) (Nat.le_of_dvd cpos ((hp.dvd_mul.mp dvd).resolve_left nd))

private lemma harmonic_mono_aux (m n : ℕ) (h : m ≤ n) : harmonic m ≤ harmonic n := by
  induction n, h using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih =>
    rw [harmonic_succ]
    have h_pos : (0 : ℚ) ≤ ((n + 1 : ℕ) : ℚ)⁻¹ := by positivity
    linarith

/-- For any rational `R`, there exists a natural `N` with `harmonic N > R`. -/
private lemma exists_harmonic_gt_aux (R : ℚ) : ∃ N : ℕ, harmonic N > R := by
  have h : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (1 : ℝ) / (↑i + 1))
      Filter.atTop Filter.atTop := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h ((R : ℝ) + 1)
  use N
  have h_eq : (∑ i ∈ Finset.range N, (1 : ℝ) / (↑i + 1)) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [show (Finset.Icc 1 N) = (Finset.range N).image (· + 1) from ?_]
    · rw [Finset.sum_image (fun a _ b _ h => by simp at h; omega)]
      simp
    · ext x
      constructor
      · intro hx
        rw [Finset.mem_Icc] at hx
        rw [Finset.mem_image]
        refine ⟨x - 1, ?_, by omega⟩
        rw [Finset.mem_range]
        omega
      · intro hx
        rw [Finset.mem_image] at hx
        rcases hx with ⟨a, ha, rfl⟩
        rw [Finset.mem_range] at ha
        rw [Finset.mem_Icc]
        omega
  have h_test : ((R : ℝ) + 1) ≤ (harmonic N : ℝ) := h_eq ▸ hN N le_rfl
  have h_cast : (R : ℝ) < (harmonic N : ℝ) := by linarith
  exact_mod_cast h_cast

/-- The harmonic tail `∑_{j=L+1}^N 1/j` equals `harmonic N - harmonic L`. -/
private lemma harmonicTail_eq_aux (L N : ℕ) (h : L ≤ N) :
    ∑ j ∈ Finset.Ioc L N, (1 : ℚ) / j = harmonic N - harmonic L := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  rw [show Finset.Ioc L N = Finset.Icc (L+1) N from by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]]
  have h_split : Finset.Icc 1 N = Finset.Icc 1 L ∪ Finset.Icc (L+1) N := by
    ext x; simp [Finset.mem_Icc, Finset.mem_union]; omega
  rw [h_split, Finset.sum_union ?_]
  · simp [one_div]
  · rw [Finset.disjoint_left]
    intro x hx_left hx_right
    rw [Finset.mem_Icc] at hx_left hx_right
    omega

/-- For any positive rational `R` and natural `L`, there exists `N ≥ L` such that
the harmonic tail from `L+1` to `N` is at least `R`. -/
private lemma exists_harmonicTail_ge_aux (R : ℚ) (L : ℕ) :
    ∃ N : ℕ, L ≤ N ∧ R ≤ ∑ j ∈ Finset.Ioc L N, (1 : ℚ) / j := by
  obtain ⟨N₀, hN₀⟩ := exists_harmonic_gt_aux (R + harmonic L)
  refine ⟨max N₀ L, le_max_right _ _, ?_⟩
  have hLN : L ≤ max N₀ L := le_max_right _ _
  rw [harmonicTail_eq_aux _ _ hLN]
  have h_mono : harmonic N₀ ≤ harmonic (max N₀ L) :=
    harmonic_mono_aux _ _ (le_max_left _ _)
  linarith

/-- Algebraic identity: rewrite `R - 1/q` as a `Rat.divInt`. -/
private lemma sub_one_div_eq_divInt_aux (R : ℚ) (q : ℕ) (hq_pos : 0 < q) :
    R - 1/(q : ℚ) = ((R.num * q - R.den : ℤ) : ℚ) / ((R.den * q : ℕ) : ℤ) := by
  have hRd : (R.den : ℚ) ≠ 0 := by exact_mod_cast R.den_pos.ne'
  have hq_q : (q : ℚ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hR_eq : (R.num : ℚ) = R * R.den := by
    have h := Rat.num_div_den R
    field_simp at h
    linarith
  push_cast
  rw [eq_div_iff (by positivity : (R.den : ℚ) * q ≠ 0)]
  rw [sub_mul]
  rw [show R * ((R.den : ℚ) * q) = (R * R.den) * q from by ring]
  rw [← hR_eq]
  rw [show (1 / (q : ℚ)) * ((R.den : ℚ) * q) = ((q : ℚ) * (q : ℚ)⁻¹) * R.den from by
    rw [one_div]; ring]
  rw [mul_inv_cancel₀ hq_q, one_mul]

/-- The greedy step decreases the numerator (in `natAbs`). -/
private lemma greedy_num_decrease_aux (R : ℚ) (hR : 0 < R)
    (h_neq : R ≠ 1 / (⌈(R⁻¹ : ℚ)⌉₊ : ℚ)) :
    (R - 1 / (⌈(R⁻¹ : ℚ)⌉₊ : ℚ)).num.natAbs < R.num.natAbs := by
  set q : ℕ := ⌈(R⁻¹ : ℚ)⌉₊ with hq_def
  have hq_pos : 0 < q := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hq
    have h : (R⁻¹ : ℚ) ≤ 0 := by rw [Nat.ceil_eq_zero] at hq; exact hq
    have h_pos : (0 : ℚ) < R⁻¹ := inv_pos.mpr hR
    linarith
  have ha_pos : 0 < R.num := Rat.num_pos.mpr hR
  have hb_pos : (0 : ℕ) < R.den := R.den_pos
  have hR_inv : (R⁻¹ : ℚ) = (R.den : ℚ) / R.num := by
    rw [show R = (R.num : ℚ) / R.den from (Rat.num_div_den R).symm]
    rw [inv_div, Rat.num_div_den]
  have ha_pos_q : (0 : ℚ) < R.num := by exact_mod_cast ha_pos
  have hb_pos_q : (0 : ℚ) < R.den := by exact_mod_cast hb_pos
  have h_qa_ge_b : (R.den : ℤ) ≤ R.num * q := by
    have h1 : (R⁻¹ : ℚ) ≤ q := Nat.le_ceil _
    rw [hR_inv] at h1
    rw [div_le_iff₀ ha_pos_q] at h1
    have h_int : (R.den : ℤ) ≤ (q : ℤ) * R.num := by exact_mod_cast h1
    linarith
  have h_qa_lt : (R.num : ℤ) * q < R.den + R.num := by
    have h2 : ((q : ℚ) : ℚ) < R⁻¹ + 1 :=
      Nat.ceil_lt_add_one (le_of_lt (inv_pos.mpr hR))
    rw [hR_inv] at h2
    have h3 : (q : ℚ) * R.num < R.den + R.num := by
      have := mul_lt_mul_of_pos_right h2 ha_pos_q
      rw [add_mul, div_mul_cancel₀ _ ha_pos_q.ne', one_mul] at this
      exact this
    have h_int : (q : ℤ) * R.num < R.den + R.num := by exact_mod_cast h3
    linarith
  have h_div : (R - 1/(q : ℚ)).num ∣ (R.num * q - R.den : ℤ) := by
    rw [sub_one_div_eq_divInt_aux R q hq_pos]
    have h_cast : ((R.den * q : ℕ) : ℤ) = (R.den : ℤ) * q := by push_cast; ring
    rw [h_cast]
    rw [show ((R.num * q - R.den : ℤ) : ℚ) / ((R.den : ℤ) * q : ℤ) =
            Rat.divInt (R.num * q - R.den) ((R.den : ℤ) * q) from
      (Rat.divInt_eq_div _ _).symm]
    apply Rat.num_dvd
    have h1 : 0 < (q : ℤ) := by exact_mod_cast hq_pos
    have h2 : 0 < (R.den : ℤ) := by exact_mod_cast hb_pos
    positivity
  have h_nonneg : 0 ≤ R.num * q - R.den := by linarith
  have h_lt' : R.num * q - R.den < R.num := by linarith
  have h_diff_pos : 0 < R.num * q - R.den := by
    by_contra h_neg
    push Not at h_neg
    have h_eq : R.num * q - R.den = 0 := by omega
    have hq_pos_q : (0 : ℚ) < q := by exact_mod_cast hq_pos
    have h_R_eq : R = 1/(q : ℚ) := by
      rw [show R = (R.num : ℚ) / R.den from (Rat.num_div_den R).symm]
      rw [div_eq_div_iff hb_pos_q.ne' hq_pos_q.ne']
      have : (R.num * q : ℤ) = R.den := by linarith
      have hh : (R.num : ℚ) * q = R.den := by exact_mod_cast this
      linarith
    exact h_neq h_R_eq
  have ha_eq : (R.num.natAbs : ℤ) = R.num := Int.natAbs_of_nonneg ha_pos.le
  have hd_eq : ((R.num * q - R.den).natAbs : ℤ) = R.num * q - R.den :=
    Int.natAbs_of_nonneg h_nonneg
  have h_lt_natabs : (R.num * q - R.den).natAbs < R.num.natAbs := by
    have : ((R.num * q - R.den).natAbs : ℤ) < R.num.natAbs := by
      rw [hd_eq, ha_eq]; exact h_lt'
    exact_mod_cast this
  have h_pos_natabs : 0 < (R.num * q - R.den).natAbs := by
    have : 0 < ((R.num * q - R.den).natAbs : ℤ) := by rw [hd_eq]; exact h_diff_pos
    exact_mod_cast this
  have h_le_natabs : (R - 1/(q : ℚ)).num.natAbs ≤ (R.num * q - R.den).natAbs :=
    Nat.le_of_dvd h_pos_natabs (Int.natAbs_dvd_natAbs.mpr h_div)
  omega

/-- For positive rational `R`, `0 ≤ R - 1/⌈R⁻¹⌉₊`. -/
private lemma greedy_step_nonneg_aux (R : ℚ) (hR : 0 < R) :
    0 ≤ R - 1/((⌈(R⁻¹ : ℚ)⌉₊ : ℕ) : ℚ) := by
  set q := ⌈(R⁻¹ : ℚ)⌉₊
  have hq_pos : 0 < q := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hq
    have h : (R⁻¹ : ℚ) ≤ 0 := by rw [Nat.ceil_eq_zero] at hq; exact hq
    have h_pos : (0 : ℚ) < R⁻¹ := inv_pos.mpr hR
    linarith
  have hq_pos_q : (0 : ℚ) < q := by exact_mod_cast hq_pos
  have h1 : (R⁻¹ : ℚ) ≤ q := Nat.le_ceil _
  rw [sub_nonneg, div_le_iff₀ hq_pos_q, mul_comm, ← div_le_iff₀ hR, one_div]
  exact h1

/-- Greedy expansion for a residual `S` with the precondition that
`minDen ≥ 2` and either `S = 0` or `⌈S⁻¹⌉₊ ≥ minDen`.
This produces a finite set of distinct integers `≥ minDen` whose reciprocals
sum to `S`.

Proven by strong induction on `S.num.natAbs`. -/
private lemma greedy_residual_aux (n : ℕ) :
    ∀ (S : ℚ), 0 ≤ S → S.num.natAbs ≤ n → ∀ (minDen : ℕ), 2 ≤ minDen →
      (S = 0 ∨ minDen ≤ ⌈(S⁻¹ : ℚ)⌉₊) →
      ∃ E : Finset ℕ, (∀ e ∈ E, minDen ≤ e) ∧ S = ∑ e ∈ E, (1 : ℚ) / e := by
  induction n with
  | zero =>
    intros S hS_nonneg hS_num minDen _ _
    have hS_num_zero : S.num.natAbs = 0 := Nat.le_zero.mp hS_num
    have hS_zero_num : S.num = 0 := Int.natAbs_eq_zero.mp hS_num_zero
    have hS : S = 0 := Rat.num_eq_zero.mp hS_zero_num
    refine ⟨∅, by simp, ?_⟩
    rw [hS]; simp
  | succ n ih =>
    intros S hS_nonneg hS_num minDen hminDen_two hS_inv
    by_cases hS_zero : S = 0
    · refine ⟨∅, by simp, ?_⟩
      rw [hS_zero]; simp
    have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_zero)
    have hq_ge : minDen ≤ ⌈(S⁻¹ : ℚ)⌉₊ := by
      rcases hS_inv with hS_eq | hq_le
      · exact (hS_zero hS_eq).elim
      · exact hq_le
    set q : ℕ := ⌈(S⁻¹ : ℚ)⌉₊ with hq_def
    have hq_pos : 0 < q := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hq
      have h : (S⁻¹ : ℚ) ≤ 0 := by rw [Nat.ceil_eq_zero] at hq; exact hq
      have h_pos : (0 : ℚ) < S⁻¹ := inv_pos.mpr hS_pos
      linarith
    have hq_ge_two : 2 ≤ q := by omega
    have hq_pos_q : (0 : ℚ) < q := by exact_mod_cast hq_pos
    -- Case: S = 1/q
    by_cases h_eq : S = 1/(q : ℚ)
    · refine ⟨{q}, ?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        rw [he]
        exact hq_ge
      · rw [Finset.sum_singleton]; exact h_eq
    -- S ≠ 1/q: greedy step
    have h_nonneg' : 0 ≤ S - 1/(q : ℚ) := greedy_step_nonneg_aux S hS_pos
    have h_num_lt : (S - 1/(q : ℚ)).num.natAbs < S.num.natAbs :=
      greedy_num_decrease_aux S hS_pos h_eq
    have h_num_le : (S - 1/(q : ℚ)).num.natAbs ≤ n := by omega
    -- Need: (S - 1/q) = 0 OR ⌈(S-1/q)⁻¹⌉₊ ≥ q + 1.
    have h_new_inv : (S - 1/(q : ℚ)) = 0 ∨ q + 1 ≤ ⌈((S - 1/(q : ℚ))⁻¹ : ℚ)⌉₊ := by
      by_cases h_zero : S - 1/(q : ℚ) = 0
      · left; exact h_zero
      right
      have h_pos' : 0 < S - 1/(q : ℚ) := lt_of_le_of_ne h_nonneg' (Ne.symm h_zero)
      have hq_minus_one_pos : (0 : ℚ) < (q : ℚ) - 1 := by
        have : (2 : ℚ) ≤ q := by exact_mod_cast hq_ge_two
        linarith
      -- Step 1: S⁻¹ > q - 1 (since q = ⌈S⁻¹⌉₊).
      have hSinv_gt : (q : ℚ) - 1 < S⁻¹ := by
        by_contra h_neg
        push Not at h_neg
        -- S⁻¹ ≤ q - 1, so ⌈S⁻¹⌉₊ ≤ ⌈q - 1⌉₊ = q - 1, contradicting q = ⌈S⁻¹⌉₊.
        have h_ceil_le : ⌈(S⁻¹ : ℚ)⌉₊ ≤ ⌈((q : ℚ) - 1)⌉₊ := Nat.ceil_le_ceil h_neg
        have h_eq_cast : ((q : ℚ) - 1) = ((q - 1 : ℕ) : ℚ) := by
          have hq_ge : 1 ≤ q := by omega
          rw [Nat.cast_sub hq_ge]; push_cast; ring
        rw [h_eq_cast, Nat.ceil_natCast] at h_ceil_le
        omega
      -- Step 2: 1/(q-1) ≤ 2/q (since q ≥ 2).
      have h_two_q_ineq : 1/((q : ℚ) - 1) ≤ 2/(q : ℚ) := by
        rw [div_le_div_iff₀ hq_minus_one_pos hq_pos_q]
        have : (2 : ℚ) ≤ q := by exact_mod_cast hq_ge_two
        nlinarith
      -- Step 3: S < 1/(q-1)
      have hS_lt_inv : S < 1/((q : ℚ) - 1) := by
        have h1 : (q : ℚ) - 1 < S⁻¹ := hSinv_gt
        rw [lt_div_iff₀ hq_minus_one_pos]
        have h2 : ((q : ℚ) - 1) * S < S⁻¹ * S := by
          have := mul_lt_mul_of_pos_right h1 hS_pos
          linarith
        rw [inv_mul_cancel₀ hS_pos.ne'] at h2
        linarith
      -- Step 4: S - 1/q < 1/q
      have hS_lt_two_q : S < 2/(q : ℚ) := lt_of_lt_of_le hS_lt_inv h_two_q_ineq
      have h_diff_lt : S - 1/(q : ℚ) < 1/(q : ℚ) := by
        have : (2 : ℚ) / q = 1/(q : ℚ) + 1/(q : ℚ) := by ring
        linarith
      -- Step 5: (S - 1/q)⁻¹ > q.
      have h_inv_gt : (q : ℚ) < (S - 1/(q : ℚ))⁻¹ := by
        rw [lt_inv_comm₀ hq_pos_q h_pos']
        have : (1 : ℚ) / q = (q : ℚ)⁻¹ := one_div _
        linarith
      -- Step 6: ⌈(S-1/q)⁻¹⌉₊ ≥ q + 1.
      rw [Nat.add_one_le_iff, Nat.lt_ceil]
      exact h_inv_gt
    obtain ⟨E', hE'_lb, hE'_sum⟩ := ih (S - 1/(q : ℚ)) h_nonneg' h_num_le (q + 1)
      (by omega) h_new_inv
    have hq_notin : q ∉ E' := by
      intro h
      have := hE'_lb q h
      omega
    refine ⟨insert q E', ?_, ?_⟩
    · intro e he
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · exact hq_ge
      · have := hE'_lb e he
        omega
    · rw [Finset.sum_insert hq_notin, ← hE'_sum]
      ring

/-- Auxiliary: a single Egyptian expansion exists (greedy).

The proof uses a harmonic-tail prelude to reduce to a small residual `S ≤ 1/N`,
then applies the greedy step recursion `greedy_residual_aux`. -/
lemma egyptian_expansion_exists (R : ℚ) (hR : 0 < R) (L : ℕ) :
    ∃ E : Finset ℕ, (∀ e ∈ E, L < e) ∧ R = ∑ e ∈ E, (1 : ℚ) / e := by
  classical
  -- Lift to L' = max L 1 so that minDen ≥ 2.
  set L' := max L 1 with hL'_def
  have hL'_ge : 1 ≤ L' := le_max_right _ _
  have hL_le_L' : L ≤ L' := le_max_left _ _
  -- Find smallest N ≥ L' with R ≤ harmonicTail L' N. Such N exists by harmonic divergence.
  set P : ℕ → Prop := fun N => L' ≤ N ∧ R ≤ ∑ j ∈ Finset.Ioc L' N, (1 : ℚ) / j with hP_def
  have hP_ex : ∃ N, P N := exists_harmonicTail_ge_aux R L'
  set N := Nat.find hP_ex with hN_def
  have hN_spec : P N := Nat.find_spec hP_ex
  obtain ⟨hLN, hRle⟩ := hN_spec
  have hN_min : ∀ M, M < N → ¬ P M := fun M hM => Nat.find_min hP_ex hM
  -- Note R > 0, harmonicTail L' L' = 0, so N ≠ L'. Hence N > L'.
  have hN_gt : L' < N := by
    rcases lt_or_eq_of_le hLN with h | h
    · exact h
    · -- N = L', so harmonicTail L' L' = 0 ≥ R, contradicting R > 0.
      exfalso
      rw [← h, Finset.Ioc_self, Finset.sum_empty] at hRle
      linarith
  -- The harmonicTail to N-1 is < R (otherwise N is not minimal).
  have hN_minus_one_lt : ∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j < R := by
    by_contra h_neg
    push Not at h_neg
    have hN_minus_pos : N - 1 < N := by omega
    have hLeN : L' ≤ N - 1 := by omega
    apply hN_min (N - 1) hN_minus_pos
    exact ⟨hLeN, h_neg⟩
  -- Residual S = R - harmonicTail L' (N-1).
  set S := R - ∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j with hS_def
  have hS_pos : 0 < S := by simp only [hS_def]; linarith
  -- The harmonic sum to N is harmonic to N-1 plus 1/N (since N > L').
  have hSplit : (∑ j ∈ Finset.Ioc L' N, (1 : ℚ) / j) =
                (∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j) + 1/(N : ℚ) := by
    have h_succ : N = (N - 1) + 1 := by omega
    have hLeN_minus : L' ≤ N - 1 := by omega
    have hN_minus_le_N : N - 1 ≤ N := by omega
    rw [show Finset.Ioc L' N = Finset.Ioc L' (N - 1) ∪ Finset.Ioc (N - 1) N from ?_]
    · rw [Finset.sum_union ?_]
      · congr 1
        rw [show Finset.Ioc (N - 1) N = {N} from by
          ext x; simp [Finset.mem_Ioc]; omega]
        rw [Finset.sum_singleton]
      · rw [Finset.disjoint_left]
        intros a ha hb
        simp [Finset.mem_Ioc] at ha hb
        omega
    · ext x
      simp [Finset.mem_Ioc, Finset.mem_union]
      omega
  -- S ≤ 1/N
  have hS_le : S ≤ 1/(N : ℚ) := by
    simp only [hS_def]
    have := hRle
    rw [hSplit] at this
    linarith
  -- N ≥ 2 (since L' ≥ 1 and N > L')
  have hN_ge_two : 2 ≤ N := by omega
  -- Apply greedy on S with minDen = N.
  have hN_pos : 0 < (N : ℚ) := by exact_mod_cast (by omega : 0 < N)
  -- Need to show N ≤ ⌈S⁻¹⌉₊.
  have hSinv_ge : (N : ℚ) ≤ S⁻¹ := by
    rw [le_inv_comm₀ hN_pos hS_pos]
    rwa [one_div] at hS_le
  have h_minDen_le_ceil : N ≤ ⌈(S⁻¹ : ℚ)⌉₊ := by
    have : (N : ℚ) ≤ ⌈(S⁻¹ : ℚ)⌉₊ := le_trans hSinv_ge (Nat.le_ceil _)
    exact_mod_cast this
  obtain ⟨E', hE'_lb, hE'_sum⟩ :=
    greedy_residual_aux S.num.natAbs S hS_pos.le le_rfl N hN_ge_two
      (Or.inr h_minDen_le_ceil)
  -- Combine harmonic-tail with E'.
  refine ⟨Finset.Ioc L' (N - 1) ∪ E', ?_, ?_⟩
  · -- All elements > L
    intros e he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · -- e ∈ Ioc L' (N-1), so e > L' ≥ L
      simp [Finset.mem_Ioc] at he
      omega
    · -- e ∈ E', so e ≥ N > L' ≥ L
      have := hE'_lb e he
      omega
  · -- Sum
    have h_disj : Disjoint (Finset.Ioc L' (N - 1)) E' := by
      rw [Finset.disjoint_left]
      intros a ha hb
      simp [Finset.mem_Ioc] at ha
      have := hE'_lb a hb
      omega
    rw [Finset.sum_union h_disj]
    have : R = (∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j) + S := by
      simp only [hS_def]; ring
    rw [this]
    rw [← hE'_sum]

lemma mass_le {N k : ℕ} (h : IsRepresentable N k) :
    (k:ℝ) ≤ (harmonic N:ℝ) -
      ∑ n ∈ (Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial < p), (1:ℝ)/n := by
  classical
  obtain ⟨A,hA,hk⟩ := h
  let D := (Icc 1 N).filter fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial < p
  have dis : Disjoint A D := by
    apply disjoint_left.mpr
    intro n hn hD
    obtain ⟨p,hp,small⟩ := (mem_filter.mp hD).2
    exact forced_omission hA hk (Nat.prime_of_mem_primeFactors hp) small n hn (Nat.dvd_of_mem_primeFactors hp)
  have he : (∑ n ∈ A, (1:ℝ)/n) = k := by simpa using (congrArg (fun q : ℚ => (q:ℝ)) hk)
  have htot : (harmonic N:ℝ) = ∑ n ∈ Icc 1 N, (1:ℝ)/n := by
    simp [harmonic_eq_sum_Icc,one_div]
  rw [htot,le_sub_iff_add_le,← he]
  change (∑ n ∈ A, (1:ℝ)/n) + (∑ n ∈ D, (1:ℝ)/n) ≤ _
  rw [← sum_union dis]
  exact sum_le_sum_of_subset_of_nonneg (union_subset hA (filter_subset _ _)) fun _ _ _ => by positivity

lemma finite_cover (K : ℕ) : ∀ᶠ N : ℕ in atTop, ∀ k ≤ K, 0 < k → IsRepresentable N k := by
  have one (k : ℕ) (hk : 0 < k) : ∀ᶠ N : ℕ in atTop, IsRepresentable N k := by
    obtain ⟨A,hA,hs⟩ := egyptian_expansion_exists (k:ℚ) (by exact_mod_cast hk) 0
    filter_upwards [eventually_ge_atTop (A.sup id)] with N hn
    exact ⟨A,fun i hi => mem_Icc.mpr ⟨hA i hi,(le_sup (f := id) hi).trans hn⟩,hs.symm⟩
  have h := (eventually_all_finite (Set.finite_Icc 1 K)).mpr (fun k hk => one k hk.1)
  filter_upwards [h] with N hn
  exact fun k hk hp => hn k ⟨hp,hk⟩

lemma lower {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hrep : ∀ᶠ N : ℕ in atTop,
      IsRepresentable N ⌊(harmonic N:ℝ)-9/2*(1+e N)*(log (log N))^2/log N⌋₊) :
    ∀ᶠ N : ℕ in atTop, ⌊(harmonic N:ℝ)-9/2*(1+e N)*(log (log N))^2/log N⌋₊+1 ≤ f N := by
  let E (N : ℕ) := 9/2*(1+e N)*(log (log N))^2/log N
  let b (N : ℕ) := ⌊(harmonic N:ℝ)-E N⌋₊
  have err : Tendsto E atTop (𝓝 0) := by
    have hlog := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h := ((tendsto_const_nhds (x := (9/2:ℝ))).mul ((tendsto_const_nhds (x := (1:ℝ))).add he)).mul hlog
    simpa only [mul_zero,Real.rpow_one,Real.rpow_two,Function.comp_apply,mul_div_assoc,E] using h
  obtain ⟨a,ha⟩ := eventually_atTop.mp ((hrep.and
    ((err.eventually_const_lt (by norm_num : -(1/4:ℝ)<0)).and
     (err.eventually_lt_const (by norm_num : (0:ℝ)<1/4)))).and (eventually_ge_atTop 2))
  have step (n : ℕ) (hn : a ≤ n) : b (n+1) ≤ b n + 1 := by
    have hE := (ha n hn).1.2
    have hE' := (ha (n+1) (by omega)).1.2
    have hn2 := (ha n hn).2
    have hdiff : ((harmonic (n+1):ℚ):ℝ) = (harmonic n:ℝ) + 1/((n:ℝ)+1) := by
      rw [harmonic_succ]; push_cast; simp [one_div]
    have small : 1/((n:ℝ)+1) ≤ 1/2 := by gcongr; exact_mod_cast (by omega : 2 ≤ n+1)
    have H := Nat.lt_floor_add_one ((harmonic n:ℝ)-E n)
    apply Nat.lt_succ_iff.mp
    apply (Nat.floor_lt' (Nat.succ_ne_zero (b n + 1))).mpr
    push_cast
    rw [hdiff]
    change (harmonic n:ℝ)-E n < (b n:ℝ)+1 at H
    linarith
  have trail (n : ℕ) (hn : a ≤ n) : ∀ k : ℕ, b a < k → k ≤ b n → IsRepresentable n k := by
    induction n,hn using Nat.le_induction with
    | base => omega
    | succ n hn ih =>
      intro k hlarge hsmall
      by_cases h : k ≤ b n
      · obtain ⟨A,hA,s⟩ := ih k hlarge h
        exact ⟨A,hA.trans (Icc_subset_Icc_right (by omega)),s⟩
      · have eqn : k = b (n+1) := by have := step n hn; omega
        exact eqn ▸ (ha (n+1) (by omega)).1.1
  filter_upwards [finite_cover (b a),eventually_ge_atTop a] with N hsmall hn
  have non : {k : ℕ | 0<k ∧ ¬ IsRepresentable N k}.Nonempty := by
    refine ⟨⌊(harmonic N:ℝ)⌋₊+1,by omega,fun h => ?_⟩
    have ub := mass_le h
    have sn : 0 ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial < p), (1:ℝ)/n :=
      sum_nonneg fun _ _ => by positivity
    push_cast at ub
    linarith [Nat.lt_floor_add_one (harmonic N:ℝ)]
  have bad : 0 < f N ∧ ¬ IsRepresentable N (f N) := Nat.sInf_mem non
  change b N+1 ≤ f N
  by_contra! h
  apply bad.2
  rcases le_or_gt (f N) (b a) with hs|hl
  · exact hsmall _ hs bad.1
  · exact trail N hn _ hl (by omega)

theorem main : H1 → H2 → type_of% @Erdos308.erdos_308.variants.croot := by
  rintro ⟨e,he,hrep⟩ hmass
  let D (N : ℕ) := (Icc 1 N).filter fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial < p
  let M (N : ℕ) := ∑ n ∈ D N, (1:ℝ)/n
  let R (N : ℕ) := M N * log N / (log (log N))^2
  have hr : Tendsto R atTop (𝓝 (1/2:ℝ)) := hmass
  refine ⟨e,fun n => 2*R n-1,he,?_,?_⟩
  · convert (hr.const_mul 2).sub_const 1 using 1 <;> norm_num
  filter_upwards [lower he hrep,(tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 1] with N hlo hn
  refine ⟨hlo,?_⟩
  change 1 < log (N:ℝ) at hn
  have hl : 0 < log (log (N:ℝ)) := log_pos hn
  change f N ≤ ⌊(harmonic N:ℝ)-1/2*(1+(2*R N-1))*log (log N)^2/log N⌋₊+1
  have eqn : 1/2*(1+(2*R N-1))*log (log N)^2/log N = M N := by
    dsimp [R]; field_simp [hl.ne',(show log (N:ℝ) ≠ 0 by linarith)] <;> ring
  rw [eqn]
  apply Nat.sInf_le
  refine ⟨by omega,fun h => ?_⟩
  have hb := mass_le h
  change ((⌊(harmonic N:ℝ)-M N⌋₊+1:ℕ):ℝ) ≤ (harmonic N:ℝ)-M N at hb
  push_cast at hb
  linarith [Nat.lt_floor_add_one ((harmonic N:ℝ)-M N)]

end OMA.R_Erdos308_erdos_308_variants_croot_R1
end

section

/-!
# Croot's constructive lower bound

We follow Ernest S. Croot III, On some questions of Erdős and Graham about
Egyptian fractions, Mathematika 46 (1999), 359–372, Propositions 1–3.
The cutoff removes all integers with a prime-power divisor above
N / (log N)^a. The remaining denominators are divided into disjoint classes
according to the first least common multiple that they divide.
The descent adapts @marcusbuffett's merged Erdős 297 reduction. Denominator
one survives every cancellation, so an integer one larger than the desired
floor can be reduced to that floor.
-/
namespace OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1
open Finset Real Filter Erdos308
open scoped Classical Topology

/-- Reciprocal mass lost at the initial prime-power cutoff. -/
def H1 : Prop := ∀ a : ℝ, 3<a → ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
  let J (i : ℕ) := (Icc 1 i).lcm id
  let Q := ⌊(N:ℝ)/(log N)^a⌋₊
  (∑ n ∈ (Icc 1 N).filter (fun n => ¬n∣J Q), (1:ℝ)/n) ≤
    (a^2/2+ε)*(log (log N))^2/log N

/-- Small and medium prime powers. The small-power costs telescope to less
than one and the intermediate powers contribute a negligible tail. -/
def H2 : Prop := ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
  let J (i : ℕ) := (Icc 1 i).lcm id
  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬ n∣J (i-1)
  ∃ cost : ℕ→ℚ, ((∑ i ∈ Ioc 1 N.sqrt, cost i : ℚ):ℝ) ≤
    1 + ε*(log (log N))^2/log N ∧
    ∀ i ∈ Ioc 1 N.sqrt, ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V,(1:ℚ)/n) ≤ cost i ∧ ∃ b : ℤ,
        (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n

/-- The modular subset sums for the large prime powers, in the range for
which logarithmically many denominators are available. -/
def H3 : Prop := ∀ a : ℝ, 3<a → ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop,
  let J (i : ℕ) := (Icc 1 i).lcm id
  let Q := ⌊(N:ℝ)/(log N)^a⌋₊
  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬ n∣J (i-1)
  ∃ cost : ℕ→ℚ, ((∑ i ∈ Ioc N.sqrt Q, cost i : ℚ):ℝ) ≤
    ε*(log (log N))^2/log N ∧
    ∀ i ∈ Ioc N.sqrt Q, ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V,(1:ℚ)/n) ≤ cost i ∧ ∃ b : ℤ,
        (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n

lemma descend (J : ℕ → ℕ) (R : ℕ → Finset ℕ) (cost : ℕ → ℚ)
    (L B : ℕ) (hB : L ≤ B) (step : ∀ i ∈ Ioc L B, ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V, (1:ℚ)/n) ≤ cost i ∧ ∃ a : ℤ,
        (a:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V, (1:ℚ)/n)
    (apart : ∀ i ∈ Ioc L B, ∀ j ∈ Ioc L B,
      i < j → Disjoint (R i) (R j)) (z : ℤ) :
    ∃ P ⊆ (Ioc L B).biUnion R, (∑ n ∈ P, (1:ℚ)/n) ≤ ∑ i ∈ Ioc L B, cost i ∧
    ∃ a : ℤ, (a:ℚ)/J L = (z:ℚ)/J B - ∑ n ∈ P, (1:ℚ)/n := by
  induction B,hB using Nat.le_induction generalizing z with
  | base => exact ⟨∅,empty_subset _,by simp,z,by simp⟩
  | succ b hb ih =>
    have last : b+1 ∈ Ioc L (b+1) := mem_Ioc.mpr ⟨by omega,le_rfl⟩
    have sub : Ioc L b ⊆ Ioc L (b+1) := fun i hi => mem_Ioc.mpr
      ⟨(mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2.trans (Nat.le_succ _)⟩
    obtain ⟨V,hV,hv,a,ha⟩ := step (b+1) last z
    obtain ⟨P,hP,hp,j,hj⟩ := ih (fun i hi => step i (sub hi)) (fun i hi k hk => apart i (sub hi) k (sub hk)) a
    have dj : Disjoint P V := by
      apply disjoint_left.mpr
      intro n hn hnV
      obtain ⟨i,hi,hnR⟩ := mem_biUnion.mp (hP hn)
      exact disjoint_left.mp (apart i (sub hi) _ last (Nat.lt_succ_of_le (mem_Ioc.mp hi).2)) hnR (hV hnV)
    have eq : Ioc L (b+1) = insert (b+1) (Ioc L b) := by
      ext i; simp only [mem_Ioc,mem_insert]; omega
    refine ⟨P∪V,union_subset (fun n hn => ?_) (fun n hn => mem_biUnion.mpr ⟨_,last,hV hn⟩),?_,j,?_⟩
    · obtain ⟨i,hi,hh⟩ := mem_biUnion.mp (hP hn)
      exact mem_biUnion.mpr ⟨_,sub hi,hh⟩
    · rw [sum_union dj,eq,sum_insert (by simp)]
      linarith
    · simp only [Nat.add_sub_cancel] at ha
      rw [sum_union dj,hj,ha]
      ring




lemma assemble (N Q : ℕ) (hN : 1≤N) (hQ : 1≤Q) (cost : ℕ→ℚ) :
  let J (i : ℕ) := (Icc 1 i).lcm id
  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬ n∣J (i-1)
  (∀ i ∈ Ioc 1 Q, ∀ z : ℤ, ∃ V ⊆ R i,
      (∑ n ∈ V,(1:ℚ)/n) ≤ cost i ∧ ∃ b : ℤ,
        (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n) →
  ∃ S ⊆ Icc 1 N, 1∈S ∧ ∃ z : ℕ, (∑ n ∈ S,(1:ℚ)/n) = z ∧
    (harmonic N:ℝ)-z ≤
      (∑ n ∈ (Icc 1 N).filter (fun n => ¬n∣J Q),(1:ℝ)/n) +
      ((∑ i ∈ Ioc 1 Q,cost i:ℚ):ℝ) := by
  intro J R step
  let G := (Icc 1 N).filter fun n => n∣J Q
  have Jpos (i : ℕ) : 0<J i := by
    apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro n hn
    exact Nat.ne_of_gt (mem_Icc.mp hn).1
  have Jdvd {i j : ℕ} (h : i≤j) : J i∣J j :=
    Finset.lcm_dvd (fun n hn => Finset.dvd_lcm (f:=id) (mem_Icc.mpr
      ⟨(mem_Icc.mp hn).1,(mem_Icc.mp hn).2.trans h⟩))
  have part (i j : ℕ) (h : i<j) : Disjoint (R i) (R j) := by
    apply disjoint_left.mpr
    intro n hi hj
    have d := (mem_filter.mp hi).2.1
    exact (mem_filter.mp hj).2.2 (dvd_trans d (Jdvd (by omega)))
  let t : ℤ := ∑ n ∈ G, (J Q/n : ℕ)
  have grid : (t:ℚ)/J Q=∑ n ∈ G,(1:ℚ)/n := by
    dsimp only [t]
    push_cast
    rw [sum_div]
    apply sum_congr rfl
    intro n hn
    have dv := (mem_filter.mp hn).2
    have np := (mem_Icc.mp (mem_filter.mp hn).1).1
    apply (div_eq_div_iff (by exact_mod_cast (Jpos Q).ne') (by exact_mod_cast (Nat.ne_of_gt np))).mpr
    rw [one_mul]
    exact_mod_cast Nat.div_mul_cancel dv
  obtain ⟨P,sub,hcost,b,hb⟩ := descend J R cost 1 Q hQ step (fun i _ j _ => part i j) t
  have good : P⊆G := by
    intro n hn
    obtain ⟨i,hi,hr⟩ := mem_biUnion.mp (sub hn)
    exact mem_filter.mpr ⟨(mem_filter.mp hr).1,dvd_trans (mem_filter.mp hr).2.1 (Jdvd (mem_Ioc.mp hi).2)⟩
  have untouched : 1∉P := by
    intro hp
    obtain ⟨i,hi,hr⟩ := mem_biUnion.mp (sub hp)
    exact (mem_filter.mp hr).2.2 (one_dvd _)
  have jone : J 1=1 := by simp [J]
  rw [jone,Nat.cast_one,div_one,grid,←Finset.sum_sdiff_eq_sub good] at hb
  have nonneg : 0≤b := by
    have h : 0≤(b:ℚ) := by rw [hb]; positivity
    exact_mod_cast h
  lift b to ℕ using nonneg
  refine ⟨G \ P,fun n hn => (mem_filter.mp (mem_sdiff.mp hn).1).1,
    mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,hN⟩,one_dvd _⟩,untouched⟩,b,?_,?_⟩
  · exact_mod_cast hb.symm
  have hp : (∑ n ∈ P,(1:ℝ)/n) ≤ ((∑ i ∈ Ioc 1 Q,cost i:ℚ):ℝ) := by
    have t : ((∑ n ∈ P, (1:ℚ)/n):ℝ) ≤ ((∑ i ∈ Ioc 1 Q,cost i:ℚ):ℝ) := by exact_mod_cast hcost
    simpa using t
  have bb : (b:ℝ) = ∑ n ∈ G \ P,(1:ℝ)/n := by simpa using congrArg (fun t : ℚ => (t:ℝ)) hb
  have split := Finset.sum_sdiff good (f:=fun n : ℕ => (1:ℝ)/n)
  have both := Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun n => n∣J Q) (fun n : ℕ => (1:ℝ)/n)
  rw [harmonic_eq_sum_Icc]
  push_cast
  change (∑ n ∈ G, (1:ℝ)/n) + _ = _ at both
  simp only [one_div,Rat.cast_sum] at hp bb split both ⊢
  linarith only [hp,bb,split,both]



lemma floor_rep {N z : ℕ} {S : Finset ℕ} (sub : S⊆Icc 1 N) (one : 1∈S)
    (eq : (∑ n ∈ S,(1:ℚ)/n) = z) {u : ℝ} (hu : u≤1)
    (low : (harmonic N:ℝ)-z < 1+u) : IsRepresentable N ⌊(harmonic N:ℝ)-u⌋₊ := by
  let k := ⌊(harmonic N:ℝ)-u⌋₊
  have hz : IsRepresentable N z := ⟨S,sub,eq⟩
  have hi := OMA.R_Erdos308_erdos_308_variants_croot_R1.mass_le hz
  have om : 0≤∑ n ∈ (Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial < p), (1:ℝ)/n := by positivity
  have hzle : z≤k+1 := by
    have h := Nat.lt_floor_add_one ((harmonic N:ℝ)-u)
    change (harmonic N:ℝ)-u < (k:ℝ)+1 at h
    have zlt : z<k+2 := by exact_mod_cast (show (z:ℝ)<(k:ℝ)+2 by linarith)
    omega
  have hkz : k≤z := by
    apply Nat.le_of_lt_succ
    exact (Nat.floor_lt' (Nat.succ_ne_zero z)).mpr (by push_cast; linarith)
  rcases Nat.eq_or_lt_of_le hkz with hk|hk
  · change IsRepresentable N k
    exact hk ▸ hz
  have e : z=k+1 := by omega
  refine ⟨S.erase 1,(erase_subset _ _).trans sub,?_⟩
  have h := Finset.sum_erase_add (f:=fun n : ℕ => (1:ℚ)/n) S one
  rw [eq,e] at h
  push_cast at h
  change _ = (k:ℚ)
  norm_num at h
  simpa only [one_div] using h


lemma fixed (cut : H1) (small : H2) (large : H3) (η : ℝ) (η0 : 0<η) (η1 : η≤1) :
    ∀ᶠ N : ℕ in atTop, IsRepresentable N
      ⌊(harmonic N:ℝ)-9/2*(1+η)*(log (log N))^2/log N⌋₊ := by
  let a := 3+η/2
  let b := 9/2*(1+η)
  have a3 : 3<a := by dsimp [a]; linarith
  have δ : 0<η/4 := by positivity
  have gap : a^2/2+3*(η/4)<b := by
    dsimp [a,b]
    nlinarith [mul_nonneg η0.le (sub_nonneg.mpr η1)]
  have lc := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have grow := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop a (show 0<(1/2:ℝ) by norm_num)).bound zero_lt_one)
  have sc := ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero.comp lc).const_mul b
  rw [mul_zero] at sc
  filter_upwards [cut a a3 (η/4) δ,small (η/4) δ,large a a3 (η/4) δ,
      sc.eventually_lt_const zero_lt_one,grow,
      lc.eventually_gt_atTop 1,eventually_ge_atTop 2] with N hc hs hl hcst hg hn hN
  let J (i : ℕ) := (Icc 1 i).lcm id
  let Q := ⌊(N:ℝ)/(log N)^a⌋₊
  let R (i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬n∣J (i-1)
  let s := (log (log N))^2/log N
  have np : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  change 1<log (N:ℝ) at hn
  have lp : 0<log (N:ℝ) := by linarith
  have sp : 0<s := div_pos (sq_pos_of_pos (log_pos hn)) lp
  have un : b*s≤1 := by
    apply le_of_lt
    simpa [Function.comp_def,s,Real.rpow_two,Real.rpow_one] using hcst
  have hlp := rpow_pos_of_pos lp a
  have rad : (log (N:ℝ))^a ≤ sqrt N := by
    change ‖(log (N:ℝ))^a‖ ≤ 1*‖(N:ℝ)^(1/2:ℝ)‖ at hg
    rw [sqrt_eq_rpow]
    simpa only [Real.norm_eq_abs,abs_of_pos hlp,abs_of_pos (rpow_pos_of_pos np _),one_mul] using hg
  have sqQ : N.sqrt≤Q := by
    apply Nat.le_floor
    apply (le_div_iff₀ hlp).mpr
    exact (mul_le_mul Real.nat_sqrt_le_real_sqrt rad hlp.le (sqrt_nonneg _)).trans_eq
      (by rw [←sq,Real.sq_sqrt np.le])
  have s1 : 1≤N.sqrt := Nat.le_sqrt.mpr (by omega)
  obtain ⟨lo,lcost,low⟩ := hs
  obtain ⟨hi,hcost,high⟩ := hl
  let cost (i:ℕ) := if i≤N.sqrt then lo i else hi i
  have merge : (∑ i ∈ Ioc 1 Q,cost i) = (∑ i ∈ Ioc 1 N.sqrt,lo i)+(∑ i ∈ Ioc N.sqrt Q,hi i) := by
    rw [←Finset.Ioc_union_Ioc_eq_Ioc s1 sqQ,Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)]
    congr 1
    · exact sum_congr rfl (fun i h => if_pos (mem_Ioc.mp h).2)
    · exact sum_congr rfl (fun i h => if_neg (not_le.mpr (mem_Ioc.mp h).1))
  obtain ⟨S,sub,one,z,eq,loss⟩ := assemble N Q (by omega) (s1.trans sqQ) cost (by
    intro i hi z
    by_cases ht : i≤N.sqrt
    · simpa only [cost,if_pos ht] using low i (mem_Ioc.mpr ⟨(mem_Ioc.mp hi).1,ht⟩) z
    · simpa only [cost,if_neg ht] using high i (mem_Ioc.mpr ⟨not_le.mp ht,(mem_Ioc.mp hi).2⟩) z)
  dsimp only at hc lcost hcost
  rw [merge,Rat.cast_add] at loss
  have cle : (∑ n ∈ (Icc 1 N).filter (fun n => ¬n∣J Q),(1:ℝ)/n) ≤ (a^2/2+η/4)*s := by
    simpa only [J,Q,s,mul_div_assoc] using hc
  have ll : ((∑ i ∈ Ioc 1 N.sqrt,lo i:ℚ):ℝ) ≤ 1+(η/4)*s := by simpa only [s,mul_div_assoc] using lcost
  have hh : ((∑ i ∈ Ioc N.sqrt Q,hi i:ℚ):ℝ) ≤ (η/4)*s := by simpa only [Q,s,mul_div_assoc] using hcost
  have rep := floor_rep sub one eq un (by
    change (harmonic N:ℝ)-z < 1+b*s
    linarith only [loss,cle,ll,hh,mul_lt_mul_of_pos_right gap sp])
  simpa only [b,s,mul_div_assoc] using rep


theorem main : H1 → H2 → H3 → OMA.R_Erdos308_erdos_308_variants_croot_R1.H1 := by
  intro cut small large
  let d (k : ℕ) : ℝ := 1/((k:ℝ)+1)
  let P (N k : ℕ) := IsRepresentable N
    ⌊(harmonic N:ℝ)-9/2*(1+d k)*(log (log N))^2/log N⌋₊
  have row (k : ℕ) : ∀ᶠ N : ℕ in atTop, P N k :=
    fixed cut small large (d k) (by dsimp [d]; positivity)
      (by dsimp [d]; apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg (α:=ℝ) k])
  let j (N : ℕ) := Nat.findGreatest (P N) N
  have top : Tendsto j atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [row k,eventually_ge_atTop k] with N hp hn
    exact Nat.le_findGreatest hn hp
  refine ⟨fun N => d (j N),tendsto_one_div_add_atTop_nhds_zero_nat.comp top,?_⟩
  filter_upwards [row 0] with N hN
  exact Nat.findGreatest_spec (Nat.zero_le N) hN
end OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1
end

section

/-!
# The reciprocal mass excluded by the large prime factorial obstruction

The first Mertens estimate is adapted from @senamakel's merged Erdős 962 proof
(open-math-agents commit d757b84b7870c7b80a9e62d5e93a293328aee0d4),
as reused in @marcusbuffett's Erdős 377 proof. All subsequent arguments are new.

Integrating Mertens' bounded error over a logarithmic window gives its
weighted first moment. Harmonic cofactor weights have the same main term.
The factorial cutoff lies between the exponents 1 − d and 1 + d, and
distinct eligible primes never divide the same denominator.
-/


open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

end OMALib.Mertens

open Filter Finset MeasureTheory Real
open scoped Classical Topology
namespace Window308
noncomputable def primes (b : ℝ) := Nat.primesLE ⌊exp b⌋₊
noncomputable def band (l b : ℝ) := primes b \ primes l
noncomputable abbrev weight (p : ℕ) := log p/(p:ℝ)
noncomputable abbrev raw (l b : ℝ) := ∑ p ∈ band l b, weight p
noncomputable abbrev moment (l b : ℝ) := ∑ p ∈ band l b, (b-log p)*weight p
lemma mem_primes {p : ℕ} {b : ℝ} : p∈primes b ↔ p.Prime ∧ log p≤b := by
  rw [primes,Nat.mem_primesLE]
  constructor
  · rintro ⟨le,pp⟩
    have hp : 0<(p:ℝ) := by exact_mod_cast pp.pos
    exact ⟨pp,(log_le_iff_le_exp hp).mpr ((Nat.le_floor_iff (exp_pos b).le).mp le)⟩
  · rintro ⟨pp,le⟩
    have hp : 0<(p:ℝ) := by exact_mod_cast pp.pos
    exact ⟨Nat.le_floor ((log_le_iff_le_exp hp).mp le),pp⟩
lemma mem_band {p : ℕ} {l b : ℝ} : p∈band l b ↔ p.Prime ∧ l<log p ∧ log p≤b := by
  change p∈primes b \ primes l ↔ _
  rw [Finset.mem_sdiff,mem_primes,mem_primes]
  constructor
  · rintro ⟨⟨pp,hi⟩,hn⟩
    exact ⟨pp,lt_of_not_ge (fun h => hn ⟨pp,h⟩),hi⟩
  · rintro ⟨pp,h,hi⟩
    exact ⟨⟨pp,hi⟩,fun h' => h.not_ge h'.2⟩
lemma raw_error : ∃ C : ℝ, 0≤C ∧ ∀ l b : ℝ, log 2≤l → l≤b → |raw l b-(b-l)|≤C := by
  obtain ⟨c,hc⟩ := OMALib.Mertens.mertens1
  have cp := (abs_nonneg _).trans (hc 2 le_rfl)
  refine ⟨2*c,by linarith,?_⟩
  intro l b hl h
  have he (t : ℝ) (ht : log 2≤t) : |(∑ p ∈ primes t,weight p)-t|≤c := by
    have h2 : 2≤exp t := (log_le_iff_le_exp (by norm_num : (0:ℝ)<2)).mp ht
    simpa only [primes,weight,log_exp] using hc (exp t) h2
  have sub : primes l ⊆ primes b := fun p hp =>
    mem_primes.mpr ⟨(mem_primes.mp hp).1,(mem_primes.mp hp).2.trans h⟩
  have eq := sum_sdiff sub (f:=weight)
  change raw l b+(∑ p ∈ primes l,weight p)=∑ p ∈ primes b,weight p at eq
  have hl' := abs_le.mp (he l hl)
  have hb' := abs_le.mp (he b (hl.trans h))
  exact abs_le.mpr ⟨by linarith [hl'.1,hl'.2,hb'.1,hb'.2],by linarith [hl'.1,hl'.2,hb'.1,hb'.2]⟩
lemma moment_error {C : ℝ} (err : ∀ l b : ℝ, log 2≤l → l≤b → |raw l b-(b-l)|≤C)
    {l b : ℝ} (hl : log 2≤l) (hlb : l≤b) :
    |moment l b-(b-l)^2/2| ≤ C*(b-l) := by
  classical
  let Y := b-l
  have hY : 0≤Y := sub_nonneg.mpr hlb
  let v (p : ℕ) (u : ℝ) := (Set.Iic (b-log p)).indicator (fun _ => weight p) u
  let cum (u : ℝ) := ∑ p ∈ band l b, v p u
  have intv (p : ℕ) : IntervalIntegrable (v p) volume 0 Y := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hY).mpr
    exact (integrableOn_const (C:=weight p) (hs:=measure_Ioc_lt_top.ne)).indicator measurableSet_Iic
  have intc : IntervalIntegrable cum volume 0 Y := by
    have go (S : Finset ℕ) : IntervalIntegrable (fun u => ∑ p ∈ S, v p u) volume 0 Y := by
      induction S using Finset.induction_on with
      | empty => simpa using (intervalIntegrable_const (μ:=volume) (a:=0) (b:=Y) (c:=(0:ℝ)))
      | insert p S hp ih => simpa only [sum_insert hp] using (intv p).add ih
    exact go _
  have iMoment : (∫ u in 0..Y, cum u) = moment l b := by
    dsimp only [cum]
    rw [intervalIntegral.integral_finsetSum (fun p _ => intv p)]
    apply sum_congr rfl
    intro p hp
    obtain ⟨_,lo,hi⟩ := mem_band.mp hp
    have hv : b-log p ∈ Set.Icc 0 Y := ⟨by linarith,by dsimp [Y];linarith⟩
    change (∫ u in (0:ℝ)..Y, Set.indicator {u : ℝ | u≤b-log p} (fun _ => weight p) u) = _
    rw [intervalIntegral.integral_indicator hv,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  have point (u : ℝ) (hu : u∈Set.Icc 0 Y) : |cum u-(Y-u)|≤C := by
    have sub : (band l b).filter (fun p : ℕ => u≤b-log p) = band l (b-u) := by
      ext p
      simp only [mem_filter,mem_band]
      have h0 := hu.1
      constructor
      · rintro ⟨⟨pp,h₁,h₂⟩,h₃⟩; exact ⟨pp,h₁,by linarith⟩
      · rintro ⟨pp,h₁,h₂⟩; exact ⟨⟨pp,h₁,by linarith⟩,by linarith⟩
    have e : cum u=raw l (b-u) := by
      dsimp only [cum,v,raw]
      rw [←sub,sum_filter]
      apply sum_congr rfl
      intro p hp
      by_cases h : u≤b-log p <;> simp [Set.indicator,Set.mem_Iic,h]
    rw [e,show Y-u=b-u-l by dsimp [Y];ring]
    apply err _ _ hl
    have : u≤b-l := hu.2
    linarith
  have linear : IntervalIntegrable (fun u : ℝ => Y-u) volume 0 Y :=
    (continuous_const.sub continuous_id).intervalIntegrable _ _
  have ilin : (∫ u in 0..Y,Y-u) = Y^2/2 := by
    rw [intervalIntegral.integral_sub (f:=fun _ : ℝ => Y) (g:=fun t : ℝ => t) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const,integral_id]
    simp only [sub_zero,smul_eq_mul,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
    ring
  have ide : (∫ u in 0..Y,cum u-(Y-u)) = moment l b-Y^2/2 := by
    rw [intervalIntegral.integral_sub intc linear,iMoment,ilin]
  change |moment l b-Y^2/2|≤C*Y
  rw [←ide]
  calc _ ≤ ∫ u in 0..Y,|cum u-(Y-u)| := intervalIntegral.abs_integral_le_integral_abs hY
       _ ≤ ∫ _ in (0:ℝ)..Y,C := intervalIntegral.integral_mono_on hY (intc.sub linear).abs
             intervalIntegrable_const point
       _ = _ := by simp [mul_comm]
end Window308

open Filter Finset Real
open scoped Classical Topology
namespace Window308
noncomputable abbrev L (N : ℕ) := log (N:ℝ)
noncomputable abbrev W (N : ℕ) := log (L N)
noncomputable abbrev lo (a : ℝ) (N : ℕ) := L N-a*W N
noncomputable abbrev harmonicMass (a : ℝ) (N : ℕ) := ∑ p ∈ band (lo a N) (L N),
  (harmonic (N/p):ℝ)/p
lemma band_nat {N : ℕ} (hN : 1<N) (a : ℝ) : band (lo a N) (L N) =
    (Nat.primesLE N).filter (fun p : ℕ => (N:ℝ)<p*(log N)^a) := by
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hL : 0<log (N:ℝ) := log_pos (by exact_mod_cast hN)
  ext p
  rw [mem_band,mem_filter,Nat.mem_primesLE]
  by_cases pp : p.Prime
  · have hp : 0<(p:ℝ) := by exact_mod_cast pp.pos
    have e : lo a N < log p ↔ (N:ℝ)<p*(log N)^a := by
      rw [← Real.log_lt_log_iff hn (mul_pos hp (rpow_pos_of_pos hL _)),Real.log_mul hp.ne' (rpow_pos_of_pos hL _).ne',
        Real.log_rpow hL]
      dsimp [lo,L,W]; constructor <;> intro h <;> linarith
    have e' : log (p:ℝ)≤L N ↔ p≤N := by
      rw [L,Real.log_le_log_iff hp hn,Nat.cast_le]
    simp [e,e',pp,and_comm]
  · simp [pp]
lemma harmonic_bounds (N : ℕ) (hN : 1<N) (a : ℝ) (hl : 0≤lo a N) :
    moment (lo a N) (L N) ≤ harmonicMass a N*L N ∧
    harmonicMass a N*lo a N ≤ moment (lo a N) (L N)+raw (lo a N) (L N) := by
  have h (p : ℕ) (hp : p ∈ band (lo a N) (L N)) :
      (L N-log p)*weight p ≤ (harmonic (N/p):ℝ)/p*L N ∧
      (harmonic (N/p):ℝ)/p*lo a N ≤ (L N-log p)*weight p+weight p := by
    obtain ⟨pr,lo',up⟩ := mem_band.mp hp
    have pos : 0<(p:ℝ) := by exact_mod_cast pr.pos
    have npos : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
    have pN : (p:ℝ)≤N := (log_le_log_iff pos npos).mp up
    have ratio : 1≤(N:ℝ)/p := (one_le_div pos).mpr pN
    have fl : ⌊(N:ℝ)/p⌋₊=N/p := by rw [Nat.floor_div_natCast,Nat.floor_natCast]
    have low := log_le_harmonic_floor ((N:ℝ)/p) (by positivity)
    have high := harmonic_floor_le_one_add_log ((N:ℝ)/p) ratio
    rw [fl,log_div npos.ne' pos.ne'] at low high
    change L N-log p ≤ (harmonic (N/p):ℝ) at low
    change (harmonic (N/p):ℝ) ≤ 1+(L N-log p) at high
    have lg := hl.trans lo'.le
    have diff : 0≤L N-log p := sub_nonneg.mpr up
    constructor
    · unfold weight
      rw [mul_div_assoc',div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ pos.le
      exact mul_le_mul low up lg (diff.trans low)
    · unfold weight
      rw [div_mul_eq_mul_div,mul_div_assoc',←add_div]
      apply div_le_div_of_nonneg_right _ pos.le
      calc _ ≤ (1+(L N-log p))*log p := mul_le_mul high lo'.le hl (by linarith)
           _ = _ := by ring
  constructor
  · change _ ≤ (∑ p ∈ band (lo a N) (L N), (harmonic (N/p):ℝ)/p)*L N
    rw [sum_mul]
    exact sum_le_sum fun p hp => (h p hp).1
  · change (∑ p ∈ band (lo a N) (L N), (harmonic (N/p):ℝ)/p)*lo a N ≤
        (∑ p ∈ band (lo a N) (L N), (L N-log p)*weight p)+∑ p ∈ band (lo a N) (L N),weight p
    rw [sum_mul,←sum_add_distrib]
    exact sum_le_sum fun p hp => (h p hp).2
lemma limit (a : ℝ) (ha : 0<a) :
    Tendsto (fun N : ℕ => (∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (N:ℝ)<p*(log N)^a),
      (harmonic (N/p):ℝ)/p)*log N/(log (log N))^2) atTop (𝓝 (a^2/2)) := by
  have ltop : Tendsto L atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have wtop : Tendsto W atTop atTop := tendsto_log_atTop.comp ltop
  have ratio : Tendsto (fun N : ℕ => W N/L N) atTop (𝓝 0) := by
    simpa only [Function.comp_def,W,one_mul,add_zero,pow_one] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ltop
  have invw : Tendsto (fun N : ℕ => (W N)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp wtop
  have rr : Tendsto (fun N : ℕ => 1-a*(W N/L N)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (ratio.const_mul a)
  have poslo : ∀ᶠ N : ℕ in atTop, log 2 ≤ lo a N := by
    filter_upwards [rr.eventually_const_lt (show (1/2:ℝ)<1 by norm_num),
      ltop.eventually_gt_atTop (2*log 2)] with N r hL
    have lp : 0<L N := by linarith [log_pos one_lt_two]
    have hh := mul_lt_mul_of_pos_right r lp
    field_simp [lp.ne'] at hh
    dsimp only [lo]; nlinarith
  have lr : Tendsto (fun N : ℕ => L N/lo a N) atTop (𝓝 1) := by
    have hh := rr.inv₀ (by norm_num : (1:ℝ)≠0)
    apply (show Tendsto (fun N => (1-a*(W N/L N))⁻¹) atTop (𝓝 1) by simpa using hh).congr'
    filter_upwards [ltop.eventually_gt_atTop 0,poslo] with N hL hlo
    have hll : 0<lo a N := (log_pos one_lt_two).trans_le hlo
    dsimp only [lo] at hll ⊢
    field_simp
  obtain ⟨C,hC,err⟩ := raw_error
  let low (N : ℕ) := a^2/2-C*a*(W N)⁻¹
  let high (N : ℕ) := (a^2/2 + (C*a+a)*(W N)⁻¹+C*((W N)⁻¹)^2)*(L N/lo a N)
  have ll : Tendsto low atTop (𝓝 (a^2/2)) := by
    simpa [low] using (tendsto_const_nhds (x:=a^2/2)).sub (invw.const_mul (C*a))
  have hh : Tendsto high atTop (𝓝 (a^2/2)) := by
    simpa [high] using (((tendsto_const_nhds (x:=a^2/2)).add (invw.const_mul (C*a+a))).add
      ((invw.pow 2).const_mul C)).mul lr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ll hh
  all_goals filter_upwards [eventually_gt_atTop 1,poslo,wtop.eventually_gt_atTop 0] with N hn hl hw
  all_goals
    rw [←band_nat hn a]
    change _ ≤ _
    have hL : 0<L N := log_pos (by exact_mod_cast hn)
    have hlpos := (log_pos one_lt_two).trans_le hl
    have bandle : lo a N≤L N := sub_le_self _ (mul_nonneg ha.le hw.le)
    have gap : L N-lo a N = a*W N := by dsimp [lo];ring
    have me := abs_le.mp (moment_error err hl bandle)
    have re := abs_le.mp (err _ _ hl bandle)
    rw [gap] at me re
    have bh := harmonic_bounds N hn a hlpos.le
  · change low N ≤ harmonicMass a N*L N/(W N)^2
    apply (le_div_iff₀ (sq_pos_of_pos hw)).mpr
    have alg : low N*(W N)^2=(a*W N)^2/2-C*(a*W N) := by dsimp [low];field_simp <;> ring
    rw [alg]
    linarith only [bh.1,me.1]
  · change harmonicMass a N*L N/(W N)^2 ≤ high N
    have ub : harmonicMass a N*lo a N ≤ (a*W N)^2/2+C*(a*W N)+(a*W N)+C := by linarith only [bh.2,me.2,re.2]
    have mul := mul_le_mul_of_nonneg_right ub ((div_pos hL hlpos).le)
    have alg : high N*(W N)^2 = ((a*W N)^2/2+C*(a*W N)+(a*W N)+C)*(L N/lo a N) := by
      dsimp [high];field_simp;ring
    apply (div_le_iff₀ (sq_pos_of_pos hw)).mpr
    rw [alg]
    calc _ = harmonicMass a N*lo a N*(L N/lo a N) := by field_simp
         _ ≤ _ := mul
end Window308

open Filter Real Finset
open scoped Topology
namespace Factor308
lemma bounds (a b : ℝ) (ha : 0<a) (ha1 : a<1) (hb : 1<b) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ Nat.primesLE N,
    ((N:ℝ)<p*(log N)^a → (N/p)*(N/p).factorial<p) ∧
    ((N/p)*(N/p).factorial<p → (N:ℝ)<p*(log N)^b) := by
  let L (N : ℕ) := log (N:ℝ)
  let W (N : ℕ) := log (L N)
  have ltend : Tendsto L atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have sm : Tendsto (fun N => W N/(L N)^(1-a)) atTop (𝓝 0) := by
    simpa [Function.comp_def,W] using (isLittleO_log_rpow_atTop (sub_pos.mpr ha1)).tendsto_div_nhds_zero.comp ltend
  have grow := (tendsto_rpow_atTop (sub_pos.mpr hb)).comp ltend
  filter_upwards [sm.eventually_lt_const (show 0<1/(4*a) by positivity),ltend.eventually_gt_atTop 2,
      grow.eventually_gt_atTop (2+1/log 2),eventually_ge_atTop 2] with N small lg grow hn
  intro p hp
  obtain ⟨le,pp⟩ := Nat.mem_primesLE.mp hp
  have ppos : 0<(p:ℝ) := by exact_mod_cast pp.pos
  have npos : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  let j := N/p
  have jpos : 0<j := Nat.div_pos le pp.pos
  have jr : 0<(j:ℝ) := by exact_mod_cast jpos
  have j1 : 1≤(j:ℝ) := by exact_mod_cast jpos
  have jbound : (j:ℝ) ≤ (N:ℝ)/p := by
    apply (le_div_iff₀ ppos).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  have jnext : (N:ℝ)/p < (j:ℝ)+1 := by
    rw [div_lt_iff₀ ppos]
    have h : N < (j+1)*p := by simpa only [j,Nat.mul_comm] using Nat.lt_mul_div_succ N pp.pos
    exact_mod_cast h
  have lpos : 0<L N := by linarith
  have la : 1≤(L N)^a := one_le_rpow (by linarith) ha.le
  have wpos : 0<W N := log_pos (by linarith)
  have scale : 4*a*W N*(L N)^a < L N := by
    have hs := (div_lt_div_iff₀ (rpow_pos_of_pos lpos (1-a)) (by positivity : 0<4*a)).mp small
    have hh := mul_lt_mul_of_pos_right hs (rpow_pos_of_pos lpos a)
    rw [one_mul,←rpow_add lpos,sub_add_cancel,rpow_one] at hh
    nlinarith only [hh]
  constructor
  · intro cut
    have jsmall : (j:ℝ)<(L N)^a := jbound.trans_lt ((div_lt_iff₀ ppos).mpr (by simpa [L,mul_comm] using cut))
    have jlog := log_le_log jr jsmall.le
    rw [log_rpow lpos] at jlog
    have hpoly : ((j:ℝ)+1)*log j < L N/2 := by
      have hs := mul_le_mul (show (j:ℝ)+1 ≤ 2*(L N)^a by linarith) jlog (log_nonneg j1) (by positivity)
      change ((j:ℝ)+1)*log j ≤ 2*(L N)^a*(a*W N) at hs
      nlinarith only [hs,scale]
    have pcut := log_lt_log npos cut
    rw [log_mul ppos.ne' (rpow_pos_of_pos lpos a).ne',log_rpow lpos] at pcut
    change L N < log p+a*W N at pcut
    have hwbound : a*W N<L N/2 := by nlinarith [mul_le_mul_of_nonneg_left la (mul_nonneg ha.le wpos.le)]
    have jp : j^(j+1)<p := by
      have h : log ((j:ℝ)^(j+1))<log (p:ℝ) := by rw [log_pow,Nat.cast_add,Nat.cast_one]; linarith
      exact_mod_cast (log_lt_log_iff (pow_pos jr _) ppos).mp h
    apply lt_of_le_of_lt _ jp
    rw [pow_succ]
    simpa [mul_comm] using Nat.mul_le_mul_left j (Nat.factorial_le_pow j)
  · intro cut
    have fac : 2^(j-1) ≤ j.factorial := by
      by_cases h : j=1
      · simp [h]
      · have hj : 2≤j := by omega
        have e : j-1=(j-2)+1 := by omega
        rw [e,pow_succ,mul_comm]
        simpa using (Nat.factorial_mul_pow_sub_le_factorial (n:=2) (m:=j) hj)
    have fp : j.factorial≤j*j.factorial := by simpa using Nat.mul_le_mul_right j.factorial (show 1≤j from jpos)
    have hpow : (2:ℝ)^(j-1) ≤ N := by exact_mod_cast (fac.trans (fp.trans (cut.le.trans le)))
    have logbd := log_le_log (by positivity) hpow
    rw [log_pow,Nat.cast_sub jpos,Nat.cast_one] at logbd
    change ((j:ℝ)-1)*log 2 ≤ L N at logbd
    have lp2 : 0<log 2 := log_pos one_lt_two
    have ju : (j:ℝ)-1 ≤ L N/log 2 := (le_div_iff₀ lp2).mpr logbd
    change 2+1/log 2 < (L N)^(b-1) at grow
    have big := mul_lt_mul_of_pos_left grow lpos
    have rpoweq : (L N)^(b-1)*L N=(L N)^b := by rw [←rpow_add_one lpos.ne',sub_add_cancel]
    rw [mul_comm _ ((L N)^(b-1)),rpoweq] at big
    have next : (j:ℝ)+1 < (L N)^b := by
      rw [mul_add,mul_one_div] at big
      linarith
    exact (div_lt_iff₀ ppos).mp (jnext.trans next) |>.trans_eq (mul_comm _ _)
end Factor308

open Real Filter Finset
open scoped Classical Topology
namespace Count308
noncomputable def eligible (N : ℕ) := (Nat.primesLE N).filter fun p => (N/p)*(N/p).factorial < p
lemma unique {N n p q : ℕ} (hn : n∈Icc 1 N) (hp : p∈eligible N) (hq : q∈eligible N)
    (dp : p∣n) (dq : q∣n) : p=q := by
  wlog h : p≤q generalizing p q
  · exact (this hq hp dq dp (by omega)).symm
  by_contra ne
  have prm := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have qrm := (Nat.mem_primesLE.mp (mem_filter.mp hq).1).2
  have hd : p*q∣n := ((Nat.coprime_primes prm qrm).mpr ne).mul_dvd_of_dvd_of_dvd dp dq
  have hb := (Nat.le_of_dvd (mem_Icc.mp hn).1 hd).trans (mem_Icc.mp hn).2
  have hq' : q≤N/p := (Nat.le_div_iff_mul_le prm.pos).mpr (by simpa [mul_comm] using hb)
  have hh : N/p<p := (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)).trans_lt (mem_filter.mp hp).2
  omega
lemma fiber (N p : ℕ) (hp : p.Prime) :
    (∑ n ∈ (Icc 1 N).filter (p∣·), (1:ℝ)/n) = (harmonic (N/p):ℝ)/p := by
  rw [harmonic_eq_sum_Icc,Rat.cast_sum,sum_div]
  apply sum_bij (fun n _ => n/p)
  · intro n hn
    obtain ⟨hn,hp'⟩ := mem_filter.mp hn
    obtain ⟨pos,le⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd pos hp') hp.pos,Nat.div_le_div_right le⟩
  · intro n hn m hm eq
    have a := Nat.div_mul_cancel (mem_filter.mp hn).2
    have b := Nat.div_mul_cancel (mem_filter.mp hm).2
    grind
  · intro m hm
    obtain ⟨pos,le⟩ := mem_Icc.mp hm
    refine ⟨m*p, mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos pos hp.pos,(Nat.le_div_iff_mul_le hp.pos).mp le⟩,dvd_mul_left _ _⟩,?_⟩
    exact Nat.mul_div_cancel _ hp.pos
  · intro n hn
    have e := Nat.div_mul_cancel (mem_filter.mp hn).2
    have er : (↑(n/p):ℝ)*p=n := by exact_mod_cast e
    push_cast
    rw [←one_div,div_div,er]
lemma total (N : ℕ) :
    (∑ n ∈ (Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial<p), (1:ℝ)/n) =
      ∑ p ∈ eligible N, (harmonic (N/p):ℝ)/p := by
  classical
  have term (n : ℕ) (hn : n∈Icc 1 N) :
      (if ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial<p then (1:ℝ)/n else 0) =
        ∑ p ∈ eligible N, if p∣n then (1:ℝ)/n else 0 := by
    split_ifs with he
    · obtain ⟨p,hp,hcut⟩ := he
      have dp := Nat.dvd_of_mem_primeFactors hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have pel : p∈eligible N := mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (mem_Icc.mp hn).1 dp).trans (mem_Icc.mp hn).2,hpr⟩,hcut⟩
      rw [sum_eq_single_of_mem p pel]
      · simp [dp]
      · intro q hq ne
        exact if_neg (fun dq => ne (unique hn hq pel dq dp))
    · symm
      apply sum_eq_zero
      intro p hp
      apply if_neg
      intro dp
      apply he
      exact ⟨p,Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2,dp,(show 0<n from (mem_Icc.mp hn).1).ne'⟩,(mem_filter.mp hp).2⟩
  rw [sum_filter]
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ eligible N, if p∣n then (1:ℝ)/n else 0 := sum_congr rfl term
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      rw [←sum_filter]
      exact fiber N p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
end Count308

open Real Filter Finset
open scoped Classical Topology
namespace Count308
noncomputable abbrev scaled (N : ℕ) (s : Finset ℕ) :=
  (∑ p ∈ s, (harmonic (N/p):ℝ)/p)*log N/(log (log N))^2
noncomputable abbrev window (N : ℕ) (a : ℝ) :=
  (Nat.primesLE N).filter fun p : ℕ => (N:ℝ)<p*(log N)^a
lemma mono {N : ℕ} (hn : 1≤N) {s t : Finset ℕ} (sub : s⊆t) :
    scaled N s ≤ scaled N t := by
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (log_nonneg (by exact_mod_cast hn))
  apply sum_le_sum_of_subset_of_nonneg sub
  intro p _ _
  rw [harmonic_eq_sum_Icc]
  push_cast
  positivity
theorem final_estimate :
    Tendsto (fun N : ℕ => (∑ n ∈ (Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors,
      (N/p)*(N/p).factorial<p), (1:ℝ)/n)*log N/(log (log N))^2) atTop (𝓝 (1/2:ℝ)) := by
  simp_rw [total]
  change Tendsto (fun N => scaled N (eligible N)) _ _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have low : Tendsto (fun d : ℝ => (1-d)^2/2) (𝓝 0) (𝓝 (1/2:ℝ)) := by
    simpa using ((show Continuous (fun d : ℝ => (1-d)^2/2) by fun_prop).continuousAt (x:=0)).tendsto
  have high : Tendsto (fun d : ℝ => (1+d)^2/2) (𝓝 0) (𝓝 (1/2:ℝ)) := by
    simpa using ((show Continuous (fun d : ℝ => (1+d)^2/2) by fun_prop).continuousAt (x:=0)).tendsto
  have evlow := low.eventually_const_lt (show 1/2-ε < (1/2:ℝ) by linarith)
  have evhigh := high.eventually_lt_const (show (1/2:ℝ)<1/2+ε by linarith)
  have ev : ∀ᶠ d in 𝓝[>] (0:ℝ), 1/2-ε<(1-d)^2/2 ∧ (1+d)^2/2<1/2+ε := (evlow.and evhigh).filter_mono nhdsWithin_le_nhds
  obtain ⟨d,⟨ld,ud⟩,hd⟩ := (ev.and
    (show ∀ᶠ d in 𝓝[>] (0:ℝ), d∈ Set.Ioo 0 1 from Ioo_mem_nhdsGT zero_lt_one)).exists
  have ha : 0<1-d := sub_pos.mpr hd.2
  have hb : 0<1+d := by linarith [hd.1]
  filter_upwards [(Window308.limit (1-d) ha).eventually_const_lt ld,
    (Window308.limit (1+d) hb).eventually_lt_const ud,
    Factor308.bounds (1-d) (1+d) ha (by linarith [hd.1]) (by linarith [hd.1]),
    eventually_ge_atTop (1:ℕ)] with N l u bd hn
  change 1/2-ε < scaled N (window N (1-d)) at l
  change scaled N (window N (1+d)) < 1/2+ε at u
  have sl : window N (1-d) ⊆ eligible N := by
    intro p hp
    obtain ⟨hP,hcut⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hP,(bd p hP).1 hcut⟩
  have su : eligible N ⊆ window N (1+d) := by
    intro p hp
    obtain ⟨hP,hcut⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hP,(bd p hP).2 hcut⟩
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith [mono hn sl,mono hn su]
end Count308

end

section

/-!
# Harmonic cost of Croot's prime-power cutoff

The prime contribution is the logarithmic-window estimate in @marcusbuffett's
Erdős 308 proof. Its Mertens estimate originates in @senamakel's merged
Erdős 962 proof, commit d757b84b7870c7b80a9e62d5e93a293328aee0d4.
The proper powers have base at most the square root of N and exponent at
most the binary logarithm. Their total contribution vanishes after scaling.
-/

open Filter Finset Real
open scoped Classical Topology
namespace Cut308
noncomputable abbrev cap (Q : ℕ) := (Icc 1 Q).lcm id
noncomputable abbrev pp (N Q : ℕ) := (Ioc Q N).filter fun q => IsPrimePow q ∧ ¬q.Prime
noncomputable abbrev pr (N Q : ℕ) := (Nat.primesLE N).filter fun p => Q<p
lemma obstruction {N Q n : ℕ} (hn : n∈Icc 1 N) (bad : ¬n∣cap Q) :
    ∃ t ∈ pr N Q ∪ pp N Q, t∣n := by
  have n0 : n≠0 := (show 0<n from (mem_Icc.mp hn).1).ne'
  have cap0 : cap Q ≠ 0 := Finset.lcm_ne_zero_iff.mpr
    (fun i hi => (show 0 < i from (mem_Icc.mp hi).1).ne')
  have fail : ¬ n.factorization ≤ (cap Q).factorization :=
    fun h => bad ((Nat.factorization_le_iff_dvd n0 cap0).mp h)
  obtain ⟨p,hp⟩ : ∃ p, (cap Q).factorization p < n.factorization p := by
    by_contra! h
    exact fail h
  have ne : n.factorization p ≠ 0 := by omega
  have m : p∈n.primeFactors := Finsupp.mem_support_iff.mpr ne
  have prime := Nat.prime_of_mem_primeFactors m
  let t := p^n.factorization p
  have d : t∣n := Nat.ordProj_dvd _ _
  have tN := (Nat.le_of_dvd (mem_Icc.mp hn).1 d).trans (mem_Icc.mp hn).2
  have high : Q<t := by
    by_contra! h
    have dv : t∣cap Q := Finset.dvd_lcm (f:=id) (mem_Icc.mpr ⟨Nat.pow_pos prime.pos,h⟩)
    exact (not_le.mpr hp) ((prime.pow_dvd_iff_le_factorization cap0).mp dv)
  refine ⟨t,?_,d⟩
  by_cases pt : t.Prime
  · exact mem_union_left _ (mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨tN,pt⟩,high⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨high,tN⟩,
      ⟨p,n.factorization p,prime.prime,(by omega),rfl⟩,pt⟩)

lemma count_pp (N Q : ℕ) : (pp N Q).card ≤ N.sqrt*(Nat.log 2 N+1) := by
  let U := Icc 1 N.sqrt ×ˢ range (Nat.log 2 N+1)
  have sub : pp N Q ⊆ U.image (fun z : ℕ×ℕ => z.1^z.2) := by
    intro q hq
    obtain ⟨hh,pow,nop⟩ := mem_filter.mp hq
    obtain ⟨p,k,hp,hk,rfl⟩ := pow
    have pr := Nat.prime_iff.mpr hp
    have pk := (mem_Ioc.mp hh).2
    have k2 : 2≤k := by
      by_contra! h
      have : k=1 := by omega
      exact nop (by simpa [this] using pr)
    have p2 : p^2≤N := (Nat.pow_le_pow_right pr.pos k2).trans pk
    have pair : (p,k)∈U := mem_product.mpr ⟨mem_Icc.mpr ⟨pr.pos,Nat.le_sqrt.mpr (by simpa [sq] using p2)⟩,
      mem_range.mpr (Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by decide)
        ((Nat.pow_le_pow_left pr.two_le k).trans pk)))⟩
    exact mem_image.mpr ⟨(p,k),pair,rfl⟩
  exact (card_le_card sub).trans (card_image_le.trans (by simp [U]))

end Cut308

open Filter Finset Real
open scoped Classical Topology
namespace Cut308
lemma fiber (N p : ℕ) (hp : 0<p) :
    (∑ n ∈ (Icc 1 N).filter (p∣·), (1:ℝ)/n) = (harmonic (N/p):ℝ)/p := by
  rw [harmonic_eq_sum_Icc,Rat.cast_sum,sum_div]
  apply sum_bij (fun n _ => n/p)
  · intro n hn
    obtain ⟨hn,hp'⟩ := mem_filter.mp hn
    obtain ⟨pos,le⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd pos hp') hp,Nat.div_le_div_right le⟩
  · intro n hn m hm eq
    have a := Nat.div_mul_cancel (mem_filter.mp hn).2
    have b := Nat.div_mul_cancel (mem_filter.mp hm).2
    grind
  · intro m hm
    obtain ⟨pos,le⟩ := mem_Icc.mp hm
    refine ⟨m*p, mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos pos hp,(Nat.le_div_iff_mul_le hp).mp le⟩,dvd_mul_left _ _⟩,?_⟩
    exact Nat.mul_div_cancel _ hp
  · intro n hn
    have e := Nat.div_mul_cancel (mem_filter.mp hn).2
    have er : (↑(n/p):ℝ)*p=n := by exact_mod_cast e
    push_cast
    rw [←one_div,div_div,er]

lemma dominated (N Q : ℕ) :
    (∑ n ∈ (Icc 1 N).filter (fun n => ¬n∣cap Q),(1:ℝ)/n) ≤
    (∑ p ∈ pr N Q,(harmonic (N/p):ℝ)/p)+(∑ t ∈ pp N Q,(harmonic (N/t):ℝ)/t) := by
  let F := pr N Q ∪ pp N Q
  have pos {t : ℕ} (ht : t∈F) : 0<t := by
    rcases mem_union.mp ht with h|h
    · exact (Nat.mem_primesLE.mp (mem_filter.mp h).1).2.pos
    · exact lt_of_le_of_lt (Nat.zero_le _) (mem_Ioc.mp (mem_filter.mp h).1).1
  have dj : Disjoint (pr N Q) (pp N Q) := disjoint_left.mpr (by
    intro t h j
    exact (mem_filter.mp j).2.2 (Nat.mem_primesLE.mp (mem_filter.mp h).1).2)
  rw [←sum_union dj,sum_filter]
  calc _ ≤ ∑ n ∈ Icc 1 N, ∑ t ∈ F, if t∣n then (1:ℝ)/n else 0 := by
         apply sum_le_sum
         intro n hn
         split_ifs with h
         · exact sum_nonneg (fun t _ => by split_ifs <;> positivity)
         · obtain ⟨t,ht,hd⟩ := obstruction hn h
           have one := single_le_sum (s:=F) (f:=fun t : ℕ => if t∣n then (1:ℝ)/n else 0)
             (fun i _ => by split_ifs <;> positivity) ht
           simpa only [if_pos hd] using one
       _ = _ := by
         rw [sum_comm]
         apply sum_congr rfl
         intro t ht
         rw [←sum_filter]
         exact fiber N t (pos ht)
lemma error (a : ℝ) {N : ℕ} (hN : 1<N) (hl : 1≤log (N:ℝ)) :
    let Q := ⌊(N:ℝ)/(log N)^a⌋₊
    (∑ t ∈ pp N Q,(harmonic (N/t):ℝ)/t) ≤
      (sqrt N)*((log N)/(log 2)+1)*((1+log N)*(log N)^a/(N:ℝ)) := by
  intro Q
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have lp : 0<log (N:ℝ) := by linarith
  have cp := rpow_pos_of_pos lp a
  have ct (t : ℕ) (ht : t∈pp N Q) :
      (harmonic (N/t):ℝ)/t ≤ (1+log N)*(log N)^a/N := by
    have high := (mem_Ioc.mp (mem_filter.mp ht).1).1
    have tn := (mem_Ioc.mp (mem_filter.mp ht).1).2
    have tp : 0<t := by omega
    have tr : 0<(t:ℝ) := by exact_mod_cast tp
    have high' : (N:ℝ)/((log N)^a)<t := (Nat.floor_lt' tp.ne').mp high
    have cross := (div_lt_iff₀ cp).mp high'
    have divp : 0<N/t := Nat.div_pos tn tp
    have lb : ((N/t:ℕ):ℝ)≤(N:ℝ) := by exact_mod_cast Nat.div_le_self N t
    have hh : (harmonic (N/t):ℝ)≤1+log N := (harmonic_le_one_add_log (N/t)).trans
      (add_le_add_right (log_le_log (by exact_mod_cast divp) lb) 1)
    apply (div_le_div_iff₀ tr np).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hh np.le,
      mul_le_mul_of_nonneg_left cross.le (by linarith : 0≤1+log (N:ℝ))]
  have log2 := log_pos (by norm_num : (1:ℝ)<2)
  have nl : (Nat.log 2 N:ℝ)≤log N/log 2 := by
    rw [←Real.natFloor_logb_natCast]
    exact Nat.floor_le (div_nonneg lp.le log2.le)
  have count : ((pp N Q).card:ℝ) ≤ sqrt N*(log N/log 2+1) := by
    calc _ ≤ (N.sqrt:ℝ)*((Nat.log 2 N:ℝ)+1) := by exact_mod_cast count_pp N Q
         _ ≤ _ := mul_le_mul Real.nat_sqrt_le_real_sqrt (by linarith) (by positivity) (sqrt_nonneg _)
  calc _ ≤ ∑ _t ∈ pp N Q, (1+log N)*(log N)^a/(N:ℝ) := sum_le_sum ct
       _ ≤ _ := by rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right count (by positivity)
end Cut308

open Filter Finset Real
open scoped Classical Topology
namespace Cut308
lemma negligible (a ε : ℝ) (hε : 0<ε) : ∀ᶠ N : ℕ in atTop,
    (∑ t ∈ pp N ⌊(N:ℝ)/(log N)^a⌋₊,(harmonic (N/t):ℝ)/t) * log N ≤ ε := by
  let D := 2*(1/log 2+1)
  have l2 : 0<log 2 := log_pos (by norm_num)
  have d0 : 0<D := by dsimp [D]; positivity
  have ev := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop (a+3) (show 0<(1/2:ℝ) by norm_num)).bound (div_pos hε d0))
  filter_upwards [ev,eventually_ge_atTop 2,
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1] with N hg hn hl
  let L := log (N:ℝ)
  change 1≤L at hl
  have lp : 0<L := by linarith
  have np : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have s0 := sqrt_nonneg (N:ℝ)
  have sqr := sq_sqrt np.le
  have pow : L^(a+3) = L^a*L^3 := by rw [rpow_add lp]; norm_num
  have sm : D*(sqrt N)*L^(a+3) ≤ ε*(N:ℝ) := by
    change ‖L^(a+3)‖ ≤ (ε/D)*‖(N:ℝ)^(1/2:ℝ)‖ at hg
    rw [Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos lp _),Real.norm_eq_abs,
      abs_of_pos (rpow_pos_of_pos np _),←sqrt_eq_rpow] at hg
    have h : L^(a+3)*D ≤ ε*sqrt N := by
      rw [div_mul_eq_mul_div,le_div_iff₀ d0] at hg
      exact hg
    nlinarith only [mul_le_mul_of_nonneg_right h s0,sqr,
      show ε*(sqrt N*sqrt N)=ε*(N:ℝ) by rw [←sq,sqr]]
  let Q := ⌊(N:ℝ)/L^a⌋₊
  let v := ∑ t ∈ pp N Q,(harmonic (N/t):ℝ)/t
  have e0 := error a (show 1<N by omega) hl
  have e : v ≤ sqrt N*(L/log 2+1)*((1+L)*L^a/N) := e0
  have b1 : L/log 2+1 ≤ (1/log 2+1)*L := by
    calc _ ≤ L/log 2+L := by linarith
         _ = _ := by ring
  have b2 : 1+L≤2*L := by linarith
  have bound : v*L ≤ (D*(sqrt N)*L^(a+3))/(N:ℝ) := by
    calc _ ≤ (sqrt N*((1/log 2+1)*L)*((2*L)*L^a/N))*L := by
             apply mul_le_mul_of_nonneg_right _ lp.le
             apply e.trans
             gcongr
         _ = _ := by rw [pow]; dsimp [D]; ring
  exact bound.trans ((div_le_iff₀ np).mpr sm)

lemma result : OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1.H1 := by
  intro a ha ε hε
  have lim := Window308.limit a (by linarith)
  have p := lim.eventually_lt_const (show a^2/2<a^2/2+ε/2 by linarith)
  have lc := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [p,negligible a (ε/2) (by linarith),
      (tendsto_log_atTop.comp lc).eventually_ge_atTop 1,lc.eventually_gt_atTop 1,
      eventually_ge_atTop 2] with N hp he hw hl hn
  let L := log (N:ℝ)
  let W := log L
  let Q := ⌊(N:ℝ)/L^a⌋₊
  change 1≤W at hw
  change 1<L at hl
  have lp : 0<L := by linarith
  have wp : 0<W^2 := by positivity
  have eq : pr N Q = (Nat.primesLE N).filter (fun p : ℕ => (N:ℝ)<p*L^a) := by
    apply filter_congr
    intro p h
    have pos := (Nat.mem_primesLE.mp h).2.pos
    rw [Nat.floor_lt' pos.ne',div_lt_iff₀ (rpow_pos_of_pos lp a)]
  let S := ∑ p ∈ pr N Q,(harmonic (N/p):ℝ)/p
  let T := ∑ t ∈ pp N Q,(harmonic (N/t):ℝ)/t
  have hb : S*L ≤ (a^2/2+ε/2)*W^2 := by
    dsimp only [S]
    rw [eq]
    exact ((div_lt_iff₀ wp).mp hp).le
  have eb : T*L≤ε/2 := he
  have d := mul_le_mul_of_nonneg_right (dominated N Q) lp.le
  change _ ≤ (S+T)*L at d
  apply (le_div_iff₀ lp).mpr
  nlinarith only [d,hb,eb,mul_le_mul_of_nonneg_left
    (show 1≤W^2 by nlinarith [sq_nonneg (W-1)]) (show 0≤ε/2 by linarith)]
end Cut308

end

section

/-!
# Cheap cancellation of the small and medium prime powers

Adapted the lcm-grid divisibility observations from @marcusbuffett
in open-math-agents PR 5072. The cancellation argument follows
Ernest S. Croot III, On some questions of Erdős and Graham about Egyptian
fractions. In a small layer, removing one denominator costs at most the
difference of the reciprocals of the two lcm values. In a medium layer of
index i = p^k, an inverse-residue pigeonhole argument supplies at most two
denominators of size at least i²/16. Their cost is dominated by a telescoping
tail starting at a constant multiple of log N.
Credit: @marcusbuffett.
-/

section
open Finset Nat
open scoped Classical
namespace Egyptian

lemma ongrid {m i : ℕ} (hm : 0 < m) (hmi : m ≤ i) : m ∣ lcmUpto i :=
  Finset.dvd_lcm (f := id) (mem_Icc.mpr ⟨hm,hmi⟩)

lemma unchanged {i : ℕ} (hi : 1 < i) (h : ¬ IsPrimePow i) :
    lcmUpto i = lcmUpto (i-1) := by
  have nz : i ≠ 0 := by omega
  have last : i ∣ lcmUpto (i-1) := by
    apply (Nat.factorization_prime_le_iff_dvd nz (lcmUpto_ne_zero _)).mp
    intro p hp
    apply (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero _)).mp
    have hd := (hp.pow_dvd_iff_le_factorization nz).mpr (le_refl (i.factorization p))
    apply ongrid (pow_pos hp.pos _)
    have hl := Nat.le_of_dvd (by omega : 0 < i) hd
    by_contra! hf
    have eq : p ^ i.factorization p = i := by omega
    have he : 0 < i.factorization p := by
      by_contra! e
      simp [Nat.eq_zero_of_le_zero e] at eq
      omega
    exact h ((isPrimePow_nat_iff _).mpr ⟨p,_,hp,he,eq⟩)
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro n hn
    obtain ⟨hn,hle⟩ := mem_Icc.mp hn
    by_cases e : n = i
    · simpa [e] using last
    · exact ongrid (m := n) hn (by omega)
  · apply Finset.lcm_dvd
    intro n hn
    exact ongrid (m := n) (mem_Icc.mp hn).1 (by have := (mem_Icc.mp hn).2; omega)

lemma complement {i : ℕ} (hi : IsPrimePow i) :
    i.Coprime (lcmUpto i / i) := by
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp hi
  apply (hp.coprime_iff_not_dvd.mpr ?_).pow_left
  have hi := pow_pos hp.pos k
  have dvd := ongrid hi le_rfl
  have nz : lcmUpto (p^k) / p^k ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (lcmUpto_pos _) dvd) hi)
  intro h
  have hf := hp.factorization_pos_of_dvd nz h
  rw [Nat.factorization_div dvd] at hf
  simpa [Finsupp.coe_tsub, factorization_lcmUpto _ hp, Nat.log_pow hp.one_lt, hp.factorization_pow] using hf

end Egyptian

namespace Mid308
abbrev J := Nat.lcmUpto
def layer (N i : ℕ) := (Icc 1 N).filter fun n => n∣J i ∧ ¬n∣J (i-1)
def desc (N i : ℕ) (c : ℚ) : Prop := ∀ z : ℤ, ∃ V ⊆ layer N i,
  (∑ n ∈ V,(1:ℚ)/n) ≤ c ∧ ∃ b : ℤ, (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n

lemma pp_not_prev {p k i : ℕ} (hp : p.Prime) (hk : 0<k) (eqi : p^k=i) :
    ¬i∣J (i-1) := by
  have hi := (isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,eqi⟩ |>.one_lt
  intro h
  have h' := (hp.pow_dvd_iff_le_factorization (lcmUpto_ne_zero (i-1))).mp (eqi ▸ h : p^k∣J (i-1))
  rw [factorization_lcmUpto _ hp] at h'
  have lt := Nat.log_lt_of_lt_pow (b:=p) (x:=k) (y:=i-1) (by omega) (by omega)
  omega

lemma jump {p k i : ℕ} (hp : p.Prime) (hk : 0<k) (eqi : p^k=i) :
    J i = p*J (i-1) := by
  have hi := (isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,eqi⟩ |>.one_lt
  have on := Egyptian.ongrid (m:=i) (by omega) le_rfl
  have d1 : J (i-1) ∣ J i := by
    apply Finset.lcm_dvd
    intro a ha
    change a ∣ J i
    exact Egyptian.ongrid (mem_Icc.mp ha).1 (by have := (mem_Icc.mp ha).2;omega)
  obtain ⟨g,hg⟩ := d1
  have div : J i ∣ p*J (i-1) := by
    apply Finset.lcm_dvd
    intro a ha
    obtain ⟨hl,hu⟩ := mem_Icc.mp ha
    by_cases e : a=i
    · subst a
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      have hlo := pow_pos hp.pos j
      have hlt : p^j < i := by rw [←eqi,pow_succ]; nlinarith [Nat.mul_le_mul_left (p^j) hp.two_le]
      have hdiv := Egyptian.ongrid hlo (show p^j ≤ i-1 by omega)
      simpa [←eqi,pow_succ, Nat.mul_comm] using Nat.mul_dvd_mul_left p hdiv
    · exact dvd_trans (Egyptian.ongrid hl (show a ≤ i-1 by omega)) (dvd_mul_left _ _)
  have hgdiv : g∣p := by
    rw [hg, Nat.mul_comm p] at div
    exact (Nat.mul_dvd_mul_iff_left (lcmUpto_pos _)).mp div
  rcases (Nat.dvd_prime hp).mp hgdiv with he | he
  · simp only [he,mul_one] at hg
    exact False.elim (pp_not_prev hp hk eqi (hg ▸ on))
  · rw [hg,he,Nat.mul_comm]

lemma empty_step {N i : ℕ} (hi : 1 < i) (h : ¬IsPrimePow i) :
    desc N i 0 := by
  intro z
  exact ⟨∅,empty_subset _,by simp,z,by simp [Egyptian.unchanged hi h]⟩

/-- Cancel a numerator modulo the new prime when passing between the two lcm grids. -/
lemma descent {p i : ℕ} (hp : p.Prime) (hj : J i=p*J (i-1)) (z : ℤ)
    (V : Finset ℕ) (hV : ∀ n ∈ V, 0<n ∧ n∣J i)
    (hz : ((z:ZMod p) - ∑ n ∈ V, ((J i/n:ℕ):ZMod p))=0) :
    ∃ b : ℤ, (b:ℚ)/J (i-1) = (z:ℚ)/J i - ∑ n ∈ V,(1:ℚ)/n := by
  have hh : (((z - ∑ n ∈ V, ((J i/n:ℕ):ℤ)):ℤ):ZMod p)=0 := by simpa only [Int.cast_sub,Int.cast_sum,Int.cast_natCast] using hz
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hh
  refine ⟨b,?_⟩
  have rat (n : ℕ) (hn : n∈V) : (1:ℚ)/n = ((J i/n:ℕ):ℚ)/J i := by
    apply (div_eq_div_iff (by exact_mod_cast (hV n hn).1.ne') (by exact_mod_cast lcmUpto_ne_zero i)).mpr
    rw [one_mul]; exact_mod_cast (Nat.div_mul_cancel (hV n hn).2).symm
  rw [sum_congr rfl rat, ←sum_div, ←sub_div]
  have er : (z:ℚ) - ∑ n ∈ V, ((J i/n:ℕ):ℚ) = (p:ℚ)*b := by simpa only [Int.cast_sub,Int.cast_sum,Int.cast_natCast,Int.cast_mul] using congrArg (Int.cast : ℤ → ℚ) hb
  rw [er,hj,Nat.cast_mul]
  field_simp [show (p:ℚ) ≠ 0 by exact_mod_cast hp.ne_zero] <;> ring

lemma small {N i : ℕ} (hi : 1 < i) (hN : J i≤N) :
    desc N i ((1:ℚ)/J (i-1)-1/J i) := by
  by_cases pow : IsPrimePow i
  · obtain ⟨p,k,hp,hk,eqi⟩ := (isPrimePow_nat_iff _).mp pow
    letI : Fact p.Prime := ⟨hp⟩
    have hj := jump hp hk eqi
    have p_le : p ≤ i := by rw [←eqi]; exact Nat.le_self_pow hk.ne' _
    intro z
    let u := (z:ZMod p).val
    have hu : u<p := ZMod.val_lt _
    have hval : (u:ZMod p) = z := ZMod.natCast_zmod_val _
    have hj' : (J i:ℚ)=(p:ℚ)*J (i-1) := by exact_mod_cast hj
    have hcost : (1:ℚ)/J (i-1)-1/J i = ((p:ℚ)-1)/J i := by
      rw [hj']; field_simp [show (p:ℚ) ≠ 0 by exact_mod_cast hp.ne_zero, show (J (i-1):ℚ) ≠ 0 by exact_mod_cast lcmUpto_ne_zero _] <;> ring
    rw [hcost]
    by_cases hz : u=0
    · refine ⟨∅,empty_subset _,?_,descent hp hj z ∅ (by simp) (by simpa [hz] using hval.symm)⟩
      simp only [sum_empty]; apply div_nonneg (sub_nonneg.mpr (by exact_mod_cast hp.one_le)) (by positivity)
    · have hdu := Egyptian.ongrid (show 0<u by omega) (show u ≤ i-1 by omega)
      let n := J i/u
      have du : u∣J i := dvd_trans hdu (hj ▸ dvd_mul_left _ _)
      have hnu : n*u=J i := Nat.div_mul_cancel du
      have hn : 0<n := Nat.div_pos (Nat.le_of_dvd (lcmUpto_pos _) du) (by omega)
      have hnJ : n∣J i := ⟨u,hnu.symm⟩
      have hnot : ¬n∣J (i-1) := by
        intro hd
        obtain ⟨v,hv⟩ := hd
        have eq : n*u=n*(p*v) := by rw [hnu,hj,hv];ring
        have e := Nat.eq_of_mul_eq_mul_left hn eq
        exact ((Nat.le_of_dvd (show 0<u by omega) (show p∣u from ⟨v,e⟩))).not_gt hu
      have hmem : n∈layer N i := mem_filter.mpr
        ⟨mem_Icc.mpr ⟨hn,(Nat.le_of_dvd (lcmUpto_pos _) hnJ).trans hN⟩,hnJ,hnot⟩
      have inv : J i/n=u := by rw [←hnu];simp [hn.ne']
      refine ⟨{n},singleton_subset_iff.mpr hmem,?_,descent hp hj z {n} (by simpa using And.intro hn hnJ) ?_⟩
      · simp only [sum_singleton]
        have mass : (1:ℚ)/n = u/J i := by
          apply (div_eq_div_iff (by exact_mod_cast hn.ne') (by exact_mod_cast lcmUpto_ne_zero i)).mpr
          rw [one_mul];exact_mod_cast (show J i=u*n by simpa [Nat.mul_comm] using hnu.symm)
        rw [mass]
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h' : (u:ℚ)+1 ≤ p := by exact_mod_cast hu
        linarith
      · simp [inv,hval]
  · simpa [Egyptian.unchanged hi pow] using empty_step (N:=N) hi pow
end Mid308
end

section
open Finset Nat
open scoped Classical
namespace Mid308

/-- Every residue modulo p is a sum of at most two distinct inverse residues
whose positive representatives are at least p/16. -/
lemma residues {p : ℕ} (hp : p.Prime) (w : ZMod p) :
    ∃ U : Finset ℕ, U.card ≤ 2 ∧ (∀ u ∈ U, 0<u ∧ u<p ∧ p≤16*u) ∧
      (∑ u ∈ U, (u:ZMod p)⁻¹) = w := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hw : w=0
  · exact ⟨∅,by simp,by simp,by simpa using hw.symm⟩
  by_cases hs : p≤16
  · let u := (w⁻¹).val
    have hu : (u:ZMod p) = w⁻¹ := ZMod.natCast_zmod_val _
    have hu0 : 0<u := by
      by_contra! h
      have h' : u=0 := by omega
      simp [h'] at hu
      exact hw hu.symm
    refine ⟨{u},by simp,?_,by simp [hu]⟩
    simpa using And.intro hu0 (And.intro (ZMod.val_lt (w⁻¹)) (show p≤16*u by omega))
  let B := Ico (p/16+1) p
  let f : ℕ → ZMod p := fun u => (u:ZMod p)⁻¹
  have ib : Set.InjOn f (B : Set ℕ) := by
    intro u hu v hv hh
    have hvv := congrArg ZMod.val (inv_injective hh : (u:ZMod p)=v)
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_Ico.mp hu).2,Nat.mod_eq_of_lt (mem_Ico.mp hv).2] using hvv
  let S := B.image f
  have sc : S.card = p-(p/16+1) := by
    rw [show S = B.image f by rfl,Finset.card_image_of_injOn ib]; exact Nat.card_Ico _ _
  let T := S.erase (w/2)
  let g : ZMod p → ZMod p := fun u => w-u
  have gc : (T.image g).card=T.card := card_image_of_injective _ (by intro u v h;exact sub_right_injective h)
  have nd : ¬Disjoint T (T.image g) := by
    intro dis
    have cnt := (T ∪ T.image g).card_le_univ
    rw [card_union_of_disjoint dis,gc,ZMod.card] at cnt
    have hh : S.card ≤ T.card+1 := by
      by_cases h : w/2∈S
      · simp [T,card_erase_of_mem h];have := card_pos.mpr ⟨_,h⟩;omega
      · simp [T,h]
    omega
  obtain ⟨u,hu,hg⟩ := not_disjoint_iff.mp nd
  obtain ⟨v,hv,hev⟩ := mem_image.mp hg
  obtain ⟨hne,huS⟩ := mem_erase.mp hu
  have hvS := (mem_erase.mp hv).2
  have hp2 : (2:ZMod p)≠0 := by
    have hn := ZMod.natCast_eq_zero_iff (a:=2) (b:=p)
    change ((2:ℕ):ZMod p)≠0
    intro hh
    have := Nat.le_of_dvd (by decide : 0<2) (hn.mp hh)
    omega
  have huv : u≠v := by
    intro e
    apply hne
    apply (eq_div_iff hp2).mpr
    dsimp [g] at hev
    rw [←e] at hev
    linear_combination -hev
  obtain ⟨a,ha,ea⟩ := mem_image.mp huS
  obtain ⟨b,hb,eb⟩ := mem_image.mp hvS
  have hab : a≠b := fun e => huv (by simpa [←ea,←eb,e])
  have good {n : ℕ} (hn : n∈B) : 0<n ∧ n<p ∧ p≤16*n := by
    obtain ⟨h0,hp⟩ := mem_Ico.mp hn
    omega
  refine ⟨{a,b},by simp [hab],?_,?_⟩
  · intro n hn
    rcases mem_insert.mp hn with rfl | hn
    · exact good ha
    · exact (mem_singleton.mp hn) ▸ good hb
  · rw [sum_insert (by simpa using hab),sum_singleton]
    change f a+f b=w
    rw [ea,eb,←hev];simp [g]
end Mid308
end

section
open Finset Nat
open scoped Classical
namespace Mid308

lemma medium {N i : ℕ} (hi : 1 < i) (hn : i*i≤N) : desc N i (32 / (i:ℚ)^2) := by
  classical
  by_cases hpow : IsPrimePow i
  · obtain ⟨p,k,hp,hk,eqi⟩ := (isPrimePow_nat_iff _).mp hpow
    letI : Fact p.Prime := ⟨hp⟩
    have hi0 : 0 < i := by omega
    have pi : p∣i := eqi ▸ dvd_pow_self p hk.ne'
    have ple := Nat.le_of_dvd hi0 pi
    let D := J i/i
    have di : i*D=J i := Nat.mul_div_cancel' (Egyptian.ongrid hi0 le_rfl)
    have cop := Egyptian.complement hpow
    have pD : p.Coprime D := cop.coprime_dvd_left pi
    have dp : (D:ZMod p)≠0 := fun e => hp.coprime_iff_not_dvd.mp pD ((ZMod.natCast_eq_zero_iff _ _).mp e)
    intro z
    obtain ⟨U,hcard,hU,hsum⟩ := residues hp ((z:ZMod p)*(D:ZMod p)⁻¹)
    let m (u : ℕ) := i-p+u
    let g (u : ℕ) := i*m u
    let V := U.image g
    have inj : Function.Injective g := by intro a b e; have hh := Nat.eq_of_mul_eq_mul_left hi0 e; exact Nat.add_left_cancel hh
    have castm (u : ℕ) : (m u : ZMod p)=(u:ZMod p) := by
      dsimp [m]; rw [Nat.cast_add,Nat.cast_sub ple,(ZMod.natCast_eq_zero_iff _ _).mpr pi,ZMod.natCast_self]; ring
    have facts (u : ℕ) (hu : u∈U) : 0 < m u ∧ m u ≤ i ∧ i.Coprime (m u) ∧ i≤16*m u := by
      obtain ⟨u0,up,hu'⟩ := hU u hu
      have mc : p.Coprime (m u) := hp.coprime_iff_not_dvd.mpr (by
        intro h
        have := (ZMod.natCast_eq_zero_iff _ _).mpr h
        rw [castm] at this
        exact up.not_ge (Nat.le_of_dvd u0 ((ZMod.natCast_eq_zero_iff _ _).mp this)))
      refine ⟨by dsimp [m];omega,by dsimp [m];omega,eqi ▸ mc.pow_left k,by dsimp [m];omega⟩
    have dvd (u : ℕ) (hu : u∈U) : g u∣J i := by
      obtain ⟨hm,hmi,hcop,-⟩ := facts u hu
      exact hcop.mul_dvd_of_dvd_of_dvd (Egyptian.ongrid hi0 le_rfl) (Egyptian.ongrid hm hmi)
    have on (u : ℕ) (hu : u∈U) : g u∈layer N i := by
      obtain ⟨hm,hmi,-,-⟩ := facts u hu
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hi0 hm,(Nat.mul_le_mul_left i hmi).trans hn⟩,dvd u hu,?_⟩
      intro h
      exact pp_not_prev hp hk eqi (dvd_trans (dvd_mul_right i (m u)) h)
    have sub : V ⊆ layer N i := by simpa [V,image_subset_iff] using on
    refine ⟨V,sub,?_,descent hp (jump hp hk eqi) z V (fun n h => ⟨(mem_Icc.mp (mem_filter.mp (sub h)).1).1,(mem_filter.mp (sub h)).2.1⟩) ?_⟩
    · have each (u : ℕ) (hu : u∈U) : (1:ℚ)/g u ≤ 16/(i:ℚ)^2 := by
        obtain ⟨hm,-,-,bound⟩ := facts u hu
        have i0 : (0:ℚ) < i := by exact_mod_cast hi0
        have m0 : (0:ℚ) < m u := by exact_mod_cast hm
        dsimp only [g]; rw [Nat.cast_mul, div_le_div_iff₀ (mul_pos i0 m0) (by positivity)]
        have := mul_le_mul_of_nonneg_left (show (i:ℚ)≤16*(m u:ℚ) by exact_mod_cast bound) i0.le
        nlinarith
      dsimp only [V]; rw [sum_image (fun _ _ _ _ h => inj h)]
      calc
        _ ≤ ∑ _u ∈ U, (16:ℚ)/(i:ℚ)^2 := sum_le_sum each
        _ = (U.card:ℚ)*(16/(i:ℚ)^2) := by simp
        _ ≤ 2*(16/(i:ℚ)^2) := by gcongr;exact_mod_cast hcard
        _ = _ := by ring
    · dsimp only [V]; rw [sum_image (fun _ _ _ _ h => inj h)]
      have coef (u : ℕ) (hu : u∈U) : ((J i/g u : ℕ):ZMod p) = (D:ZMod p)*(u:ZMod p)⁻¹ := by
        have um := hU u hu
        have un : (u:ZMod p)≠0 := fun h => um.2.1.not_ge (Nat.le_of_dvd um.1 ((ZMod.natCast_eq_zero_iff _ _).mp h))
        apply (eq_mul_inv_iff_mul_eq₀ un).mpr
        rw [←castm u,←Nat.cast_mul]
        apply congrArg (Nat.cast : ℕ → ZMod p)
        apply Nat.eq_of_mul_eq_mul_left hi0
        calc
          _ = (J i/g u)*(g u) := by dsimp [g];ring
          _ = J i := Nat.div_mul_cancel (dvd u hu)
          _ = _ := di.symm
      rw [sum_congr rfl coef,←mul_sum,hsum]
      field_simp <;> ring
  · have zero := empty_step (N:=N) hi hpow
    intro z
    obtain ⟨V,hV,bound,hz⟩ := zero z
    exact ⟨V,hV,bound.trans (by positivity),hz⟩
end Mid308
end

section
open Finset Filter Real
open scoped Classical
namespace Mid308

lemma lcm_small {i N : ℕ} (hn : 0<N) (hi : (i:ℝ) ≤ log N/10) : J i ≤ N := by
  have bound := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α:=ℝ) i)
  rw [Chebyshev.psi_eq_log_lcmUpto] at bound
  have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)
  have h : log (J i:ℝ) ≤ log N := by
    change log (J i : ℝ) ≤ _ at bound
    nlinarith [mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg (α:=ℝ) i)]
  exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast Nat.lcmUpto_pos i) (by exact_mod_cast hn)).mp h

def F (L j : ℕ) : ℚ := 1/(J (min L j):ℚ) + 32/(max L j:ℕ)

lemma telescope (L m : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ Ioc 1 m, (F L (i-1)-F L i) = F L 1-F L m := by
  induction m,hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hs : Ioc 1 (m+1) = insert (m+1) (Ioc 1 m) := by ext j;simp;omega
    rw [hs,sum_insert (by simp), Nat.add_one_sub_one,ih];ring

lemma total : OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1.H2 := by
  intro ε hε
  have ht : Tendsto (fun N : ℕ => log (N:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll := (tendsto_log_atTop.comp ht).eventually_ge_atTop (640/ε+1)
  filter_upwards [ht.eventually_ge_atTop 40,hll,eventually_ge_atTop 2] with N hlog hlarge hN
  change 40 ≤ log (N:ℝ) at hlog
  change 640/ε+1 ≤ log (log N) at hlarge
  let L := ⌊log N/10⌋₊
  have hln := Nat.lt_floor_add_one (log (N:ℝ)/10)
  change log (N:ℝ)/10 < (L:ℝ)+1 at hln
  have hL0 : (0:ℝ)<L := by linarith
  have hL : 1≤L := by exact_mod_cast hL0
  have hs : 1≤N.sqrt := (Nat.sqrt_pos.mpr (by omega))
  refine ⟨fun i => F L (i-1)-F L i,?_,?_⟩
  · dsimp only
    rw [telescope L _ hs]
    have hf : 0≤F L N.sqrt := by dsimp [F]; positivity
    have hF : F L 1 = 1+32/(L:ℚ) := by simp [F, min_eq_right hL,max_eq_left hL,J,Nat.lcmUpto]
    have hn := sub_le_self (F L 1) hf
    rw [hF] at hn
    have hr : ((F L 1 - F L N.sqrt:ℚ):ℝ) ≤ 1+32/(L:ℝ) := by
      calc
        _ ≤ ((1+32/(L:ℚ):ℚ):ℝ) := (Rat.cast_le (K:=ℝ)).mpr (hF ▸ hn)
        _ = _ := by push_cast; rfl
    apply hr.trans
    apply add_le_add_right
    have hpos : 0<log (N:ℝ) := by linarith
    have big : 640≤ε*log (log N) := by
      have := (div_le_iff₀ hε).mp (show 640/ε ≤ log (log N) by linarith)
      linarith
    have one : 1≤log (log N) := by
      have hh : 0≤640/ε := by positivity
      linarith
    have big2 : 640≤ε*(log (log N))^2 := by nlinarith [mul_le_mul_of_nonneg_right one (show 0≤ε*log (log N) by linarith)]
    rw [div_le_div_iff₀ hL0 hpos]
    nlinarith only [mul_le_mul_of_nonneg_right big2 hL0.le,hln,hlog]
  · intro i hi z
    dsimp only
    obtain ⟨hil,hiu⟩ := mem_Ioc.mp hi
    by_cases h : i≤L
    · have il : (i:ℝ)≤log N/10 := (Nat.cast_le.mpr h).trans (Nat.floor_le (by linarith))
      have hJ := lcm_small (N:=N) (by omega) il
      have e : F L (i-1)-F L i = (1:ℚ)/J (i-1)-1/J i := by
        simp only [F,min_eq_right h,max_eq_left h,min_eq_right (show i-1≤L by omega),max_eq_left (show i-1≤L by omega)]
        ring
      rw [e];exact small hil hJ z
    · obtain ⟨V,hV,hc,hcan⟩ := medium hil (le_trans (Nat.mul_self_le_mul_self hiu) (Nat.sqrt_le N)) z
      refine ⟨V,hV,hc.trans ?_,hcan⟩
      simp only [F,min_eq_left (show L ≤ i-1 by omega),max_eq_right (show L ≤ i-1 by omega),
        min_eq_left (show L ≤ i by omega),max_eq_right (show L ≤ i by omega)]
      rw [Nat.cast_sub (by omega : 1 ≤ i),Nat.cast_one]
      have ip : (1:ℚ) < i := by exact_mod_cast hil
      rw [add_sub_add_left_eq_sub]
      have ip0 : (0:ℚ) < i := by linarith
      have ip1 : (0:ℚ)<(i:ℚ)-1 := by linarith
      rw [div_sub_div _ _ ip1.ne' ip0.ne', div_le_div_iff₀ (by positivity) (mul_pos ip1 ip0)]
      nlinarith
end Mid308
end
end

section

/-!
# Large prime powers in Croot's construction

The Fourier criterion, the count of exceptional primes and the prime interval
estimate are adapted from Will Howe (@H0W4RD-dev), H0W4RD-dev/croot-unit-fractions
at c58a7d45114c3af27e6abb19dcfca9d82b49b4a1, used under Apache-2.0, via
@marcusbuffett's open-math-agents proof of the corresponding Erdős 297 step.
The analytic argument originates in Croot's Lemma 1 (Acta Arithmetica 99, 2001).

For any exponent a above three, take b strictly between three and a. For
large prime powers i, inverse subset sums of primes of size (log i)^b cover
every residue modulo i. A common multiplier puts the resulting denominators
between N/6 and N. Their total cost over all layers is bounded by counting
prime powers up to the cutoff using Chebyshev's estimate and a separate bound
on proper powers. The lcm-grid identities are from @marcusbuffett's Erdős 297
and 308 proofs.
-/

section
namespace Croot

open Real Finset Filter

namespace Lemma1Aux

/-! ### Step 1: the Fourier-analytic existence criterion -/

section Fourier

variable {n : ℕ} [NeZero n]

/-- An additive character turns finite sums into products. -/
lemma stdAddChar_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) (f : ι → ZMod n) :
    ZMod.stdAddChar (∑ i ∈ T, f i) = ∏ i ∈ T, ZMod.stdAddChar (f i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- Fourier criterion: if every nontrivial frequency `h` gives a product of norm at most
`2^|R| / n`, then every residue class is a subset sum of the `u i`. -/
theorem exists_subset_sum_of_norm_prod_le {ι : Type*} [DecidableEq ι] (R : Finset ι)
    (u : ι → ZMod n)
    (hbound : ∀ h : ZMod n, h ≠ 0 →
      ‖∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i))‖ ≤ 2 ^ R.card / n)
    (c : ZMod n) : ∃ T ⊆ R, ∑ i ∈ T, u i = c := by
  by_contra hne
  push Not at hne
  set F : ZMod n → ℂ := fun h =>
    ZMod.stdAddChar (-(h * c)) * ∏ i ∈ R, (1 + ZMod.stdAddChar (h * u i)) with hF
  have hexpand : ∀ h : ZMod n,
      F h = ∑ T ∈ R.powerset, ZMod.stdAddChar (h * (∑ i ∈ T, u i - c)) := by
    intro h
    simp only [hF]
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← stdAddChar_sum T (fun i => h * u i), ← AddChar.map_add_eq_mul]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    ring
  have key : ∑ h : ZMod n, F h = 0 := by
    rw [Finset.sum_congr rfl fun h _ => hexpand h, Finset.sum_comm]
    refine Finset.sum_eq_zero fun T hT => ?_
    have hT' : ∑ i ∈ T, u i - c ≠ 0 := sub_ne_zero.2 (hne T (Finset.mem_powerset.1 hT))
    have := AddChar.sum_mulShift (ψ := (ZMod.stdAddChar : AddChar (ZMod n) ℂ))
      (∑ i ∈ T, u i - c) (ZMod.isPrimitive_stdAddChar n)
    rw [if_neg hT', Nat.cast_zero] at this
    exact this
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ (0 : ZMod n))] at key
  have h0 : F 0 = 2 ^ R.card := by
    simp only [hF, zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul, Finset.prod_const]
    norm_num
  rw [h0] at key
  set S := ∑ h ∈ Finset.univ.erase (0 : ZMod n), F h with hS
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  have hSnorm : ‖S‖ ≤ ((n : ℝ) - 1) * (2 ^ R.card / n) := by
    calc ‖S‖ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), ‖F h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.univ.erase (0 : ZMod n), (2 ^ R.card / n : ℝ) := by
        refine Finset.sum_le_sum fun h hh => ?_
        simp only [hF]
        rw [norm_mul, AddChar.norm_apply, one_mul]
        exact hbound h (Finset.ne_of_mem_erase hh)
    _ = ((n : ℝ) - 1) * (2 ^ R.card / n) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          ZMod.card, nsmul_eq_mul, Nat.cast_sub NeZero.one_le, Nat.cast_one]
  have hSeq : S = -(2 : ℂ) ^ R.card := by linear_combination key
  rw [hSeq, norm_neg, norm_pow, Complex.norm_two] at hSnorm
  have h2 : (0 : ℝ) < 2 ^ R.card := by positivity
  have hlt : ((n : ℝ) - 1) * (2 ^ R.card / n) < 2 ^ R.card := by
    rw [mul_div_assoc', div_lt_iff₀ hn]
    nlinarith
  linarith

/-- `‖1 + e(x/n)‖² ≤ 4 - 16 (t/n)²`, where `t` is the least absolute residue of `x`. -/
lemma norm_one_add_stdAddChar_sq_le (x : ZMod n) :
    ‖1 + ZMod.stdAddChar x‖ ^ 2 ≤ 4 - 16 * ((x.valMinAbs : ℝ) / n) ^ 2 := by
  set t := x.valMinAbs with ht
  have hx : ((t : ℤ) : ZMod n) = x := ZMod.coe_valMinAbs x
  have hn : (0 : ℝ) < n := by exact_mod_cast (NeZero.pos n)
  set θ : ℝ := 2 * π * t / n with hθ
  have hpsi : ZMod.stdAddChar x = Complex.exp (θ * Complex.I) := by
    rw [← hx, ZMod.stdAddChar_coe]
    congr 1
    rw [hθ]
    push_cast
    ring
  have hθbound : |θ| ≤ π := by
    obtain ⟨h1, h2⟩ := ZMod.valMinAbs_mem_Ioc x
    have h1' : -(n : ℝ) < t * 2 := by exact_mod_cast h1
    have h2' : (t : ℝ) * 2 ≤ n := by exact_mod_cast h2
    rw [abs_le]
    constructor
    · rw [hθ, le_div_iff₀ hn]
      nlinarith [pi_pos]
    · rw [hθ, div_le_iff₀ hn]
      nlinarith [pi_pos]
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθbound
  have hnorm : ‖1 + Complex.exp (θ * Complex.I)‖ ^ 2 = 2 + 2 * Real.cos θ := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [show (1 : ℂ) + (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I)
        = ↑(1 + Real.cos θ) + ↑(Real.sin θ) * Complex.I by push_cast; ring]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    linear_combination Real.sin_sq_add_cos_sq θ
  rw [hpsi, hnorm]
  have : 2 / π ^ 2 * θ ^ 2 = 8 * ((t : ℝ) / n) ^ 2 := by
    rw [hθ]
    field_simp
    ring
  linarith

end Fourier

/-! ### Step 2: few primes of size `≥ y` divide a nonzero integer -/

lemma pow_card_le_of_primes_dvd (A : Finset ℕ) (y : ℝ) (hy : 0 ≤ y)
    (hA : ∀ a ∈ A, a.Prime ∧ y ≤ a) (z : ℤ) (hz : z ≠ 0) (hdvd : ∀ a ∈ A, (a : ℤ) ∣ z) :
    y ^ A.card ≤ |(z : ℝ)| := by
  have h1 : ∏ a ∈ A, a ∣ z.natAbs := by
    apply Finset.prod_primes_dvd
    · intro a ha
      exact (hA a ha).1.prime
    · intro a ha
      exact Int.ofNat_dvd_left.1 (hdvd a ha)
  have h2 : ∏ a ∈ A, a ≤ z.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hz) h1
  calc y ^ A.card = ∏ a ∈ A, y := (Finset.prod_const y).symm
  _ ≤ ∏ a ∈ A, (a : ℝ) := Finset.prod_le_prod (fun _ _ => hy) (fun a ha => (hA a ha).2)
  _ = ((∏ a ∈ A, a : ℕ) : ℝ) := by push_cast; rfl
  _ ≤ (z.natAbs : ℝ) := by exact_mod_cast h2
  _ = |(z : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]

/-- The pigeonhole step: few `r` have `|r t_r|` small. -/
lemma card_bad_le (n H : ℕ) (hH0 : 0 < H) (hHn : H < n)
    (R : Finset ℕ) (y : ℝ) (hy : 1 ≤ y) (hR : ∀ r ∈ R, r.Prime ∧ y ≤ r)
    (t : ℕ → ℤ) (ht : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H)
    (L : ℝ) (hL : 0 ≤ L) (m : ℕ) (hm : (L + 2) * n < y ^ (m + 1)) :
    ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ) ≤ (2 * (L + 1) + 1) * m := by
  set M : ℤ := ⌊L + 1⌋ with hM
  have hM0 : 0 ≤ M := Int.floor_nonneg.2 (by linarith)
  have hML : (M : ℝ) ≤ L + 1 := Int.floor_le _
  have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hHn)
  have hHnR : (H : ℝ) < n := by exact_mod_cast hHn
  have hH0R : (0 : ℝ) < H := by exact_mod_cast hH0
  -- each fibre is small
  have hfib : ∀ v ∈ Finset.Icc (-M) M,
      (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card ≤ m := by
    intro v hv
    rw [Finset.mem_Icc] at hv
    have hvR : |(v : ℝ)| ≤ L + 1 := by
      rw [abs_le]
      have h1 : ((-M : ℤ) : ℝ) ≤ v := by exact_mod_cast hv.1
      have h2 : (v : ℝ) ≤ (M : ℝ) := by exact_mod_cast hv.2
      push_cast at h1
      constructor <;> linarith
    have hz : (H : ℤ) + n * v ≠ 0 := by
      intro h0
      have h0' : (H : ℝ) + n * v = 0 := by exact_mod_cast h0
      rcases le_or_gt 0 (v : ℝ) with hv0 | hv0
      · nlinarith
      · have : (v : ℝ) ≤ -1 := by
          have : v ≤ -1 := by
            have : v < 0 := by exact_mod_cast hv0
            omega
          exact_mod_cast this
        nlinarith
    have hzabs : |(((H : ℤ) + n * v : ℤ) : ℝ)| < (L + 2) * n := by
      push_cast
      calc |(H : ℝ) + n * v| ≤ |(H : ℝ)| + |(n : ℝ) * v| := abs_add_le _ _
      _ = H + n * |(v : ℝ)| := by
          rw [abs_mul, abs_of_nonneg hH0R.le, abs_of_nonneg hn.le]
      _ < n + n * (L + 1) := by nlinarith
      _ = (L + 2) * n := by ring
    have hpow := pow_card_le_of_primes_dvd (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) y
      (by linarith)
      (fun r hr => hR r (Finset.mem_filter.1 hr).1) _ hz (fun r hr => (Finset.mem_filter.1 hr).2)
    by_contra hcon
    push Not at hcon
    have : y ^ (m + 1) ≤ y ^ (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
      pow_le_pow_right₀ hy hcon
    linarith
  -- the bad set is covered by the fibres
  have hsub : R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) ⊆
      (Finset.Icc (-M) M).biUnion (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨hrR, hrbad⟩ := hr
    obtain ⟨v, hv⟩ := ht r hrR
    have hvR : ((r : ℝ) * t r - H) = n * v := by exact_mod_cast hv
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · have h1 : (n : ℝ) * |(v : ℝ)| < (L + 1) * n := by
        calc (n : ℝ) * |(v : ℝ)| = |(n : ℝ) * v| := by rw [abs_mul, abs_of_pos hn]
        _ = |(r : ℝ) * t r - H| := by rw [hvR]
        _ ≤ |(r : ℝ) * t r| + |(H : ℝ)| := abs_sub _ _
        _ < L * n + n := by rw [abs_of_nonneg hH0R.le]; linarith
        _ = (L + 1) * n := by ring
      have h2 : |(v : ℝ)| < L + 1 := by
        by_contra hcon
        push Not at hcon
        nlinarith
      rw [abs_lt] at h2
      rw [Finset.mem_Icc]
      constructor
      · have : -v ≤ M := Int.le_floor.2 (by push_cast; linarith)
        linarith
      · exact Int.le_floor.2 (by linarith)
    · rw [Finset.mem_filter]
      refine ⟨hrR, ⟨t r, ?_⟩⟩
      linear_combination -hv
  have hcard : (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card ≤ (2 * M.toNat + 1) * m := by
    calc (R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card
        ≤ ((Finset.Icc (-M) M).biUnion
            (fun v => R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v))).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, (R.filter (fun r : ℕ => (r : ℤ) ∣ H + n * v)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ v ∈ Finset.Icc (-M) M, m := Finset.sum_le_sum hfib
    _ = (2 * M.toNat + 1) * m := by
        rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
        congr 1
        omega
  have hMnat : ((M.toNat : ℕ) : ℝ) = (M : ℝ) := by
    have : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg hM0
    exact_mod_cast this
  calc ((R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)).card : ℝ)
      ≤ (((2 * M.toNat + 1) * m : ℕ) : ℝ) := by exact_mod_cast hcard
  _ = (2 * (M : ℝ) + 1) * m := by push_cast; rw [hMnat]
  _ ≤ (2 * (L + 1) + 1) * m := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      linarith

theorem norm_prod_general (n : ℕ) [NeZero n] (v Y L D K : ℝ)
    (hv : 0<v) (hY : 0<Y) (hL : 0<L) (hD : 0<D) (hprodYL : Y=L*D)
    (he : Real.exp 1≤Y/4) (hL2 : L+2≤n) (hn_exp : (n:ℝ)=Real.exp v)
    (hbcount : (2*(L+1)+1)*(2*v) ≤ K/2)
    (hgcount : 2*v ≤ (K/2)*(4/(9*D^2)))
    (R : Finset ℕ) (hR : ∀ r ∈ R, r.Prime ∧ ¬r∣n ∧ Y/4≤r ∧ (r:ℝ)≤3*Y)
    (hk : K≤R.card) (h : ZMod n) (hh : h≠0) :
    ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ≤ 2 ^ R.card / n := by
  have hnpos : (0 : ℝ) < n := by rw [hn_exp]; exact Real.exp_pos _
  set H := h.val with hHdef
  have hH0 : 0 < H := ZMod.val_pos.2 hh
  have hHn : H < n := ZMod.val_lt h
  set t : ℕ → ℤ := fun r => (h * ((r : ZMod n))⁻¹).valMinAbs with htdef
  have hdiv : ∀ r ∈ R, (n : ℤ) ∣ r * t r - H := by
    intro r hr
    have hcop : Nat.Coprime r n := ((hR r hr).1.coprime_iff_not_dvd).2 (hR r hr).2.1
    have h1 : (((r : ℤ) * t r : ℤ) : ZMod n) = ((H : ℤ) : ZMod n) := by
      push_cast
      simp only [htdef, ZMod.coe_valMinAbs, hHdef, ZMod.natCast_zmod_val]
      rw [mul_left_comm, ZMod.coe_mul_inv_eq_one r hcop, mul_one]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).1 h1.symm
  set B := R.filter (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n) with hBdef
  set G := R.filter (fun r : ℕ => ¬ |(r : ℝ) * t r| ≤ L * n) with hGdef
  have hBG : B.card + G.card = R.card := Finset.card_filter_add_card_filter_not _
  -- few bad primes
  have hBcard : (B.card : ℝ) ≤ (2 * (L + 1) + 1) * ⌊2 * v⌋₊ := by
    apply card_bad_le n H hH0 hHn R (Y / 4) _ _ t hdiv L (by positivity)
    · -- (L + 2) * n < y ^ (m + 1)
      have h1 : (L + 2) * n ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_right hL2 hnpos.le
      have h2 : (n : ℝ) * n = Real.exp (2 * v) := by
        rw [hn_exp, ← Real.exp_add]; ring_nf
      have h3 : Real.exp (2 * v) < Real.exp ((⌊2 * v⌋₊ + 1 : ℕ) : ℝ) := by
        rw [Real.exp_lt_exp]
        push_cast
        exact Nat.lt_floor_add_one _
      have h4 : Real.exp ((⌊2 * v⌋₊ + 1 : ℕ) : ℝ) = Real.exp 1 ^ (⌊2 * v⌋₊ + 1) :=
        (Real.exp_one_pow _).symm
      have h5 : Real.exp 1 ^ (⌊2 * v⌋₊ + 1) ≤ (Y / 4) ^ (⌊2 * v⌋₊ + 1) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he _
      linarith
    · have : (1 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 0
        simp at this
        linarith [Real.add_one_le_exp 1]
      linarith
    · intro r hr
      exact ⟨(hR r hr).1, (hR r hr).2.2.1⟩
  have hBhalf : (B.card : ℝ) ≤ R.card / 2 := by
    have h1 : (⌊2 * v⌋₊ : ℝ) ≤ 2 * v := Nat.floor_le (by positivity)
    have h2 : (2 * (L + 1) + 1) * (⌊2 * v⌋₊ : ℝ) ≤ (2 * (L + 1) + 1) * (2 * v) := by
      apply mul_le_mul_of_nonneg_left h1
      positivity
    have h3 : (2 * (L + 1) + 1) * (2 * v) ≤ K / 2 := by
      exact hbcount
    linarith
  have hGcard : K / 2 ≤ (G.card : ℝ) := by
    have : (B.card : ℝ) + G.card = R.card := by exact_mod_cast hBG
    linarith
  -- per-factor bounds
  have hfac : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 :=
    fun r _ => norm_one_add_stdAddChar_sq_le _
  set a : ℝ := 4 / (9 * D ^ 2) with hadef
  have hgood : ∀ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
      ≤ 4 * Real.exp (-a) := by
    intro r hr
    rw [hGdef, Finset.mem_filter] at hr
    obtain ⟨hrR, hrgood⟩ := hr
    push Not at hrgood
    have hr3 : (r : ℝ) ≤ 3 * Y := (hR r hrR).2.2.2
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (hR r hrR).1.pos
    have key : (n : ℝ) < 3 * D * |(t r : ℝ)| := by
      rw [abs_mul, abs_of_pos hrpos] at hrgood
      have : L * n < L * (3 * D * |(t r : ℝ)|) := by
        calc L * (n : ℝ) = L * n := rfl
        _ < r * |(t r : ℝ)| := hrgood
        _ ≤ 3 * Y * |(t r : ℝ)| := mul_le_mul_of_nonneg_right hr3 (abs_nonneg _)
        _ = L * (3 * D * |(t r : ℝ)|) := by rw [hprodYL]; ring
      exact lt_of_mul_lt_mul_left this (by positivity)
    have key2 : 1 / (9 * D ^ 2) ≤ ((t r : ℝ) / n) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (n : ℝ) ^ 2 < (3 * D * |(t r : ℝ)|) ^ 2 :=
        pow_lt_pow_left₀ key hnpos.le (by norm_num)
      calc 1 * (n : ℝ) ^ 2 ≤ (3 * D * |(t r : ℝ)|) ^ 2 := by linarith
      _ = (t r : ℝ) ^ 2 * (9 * D ^ 2) := by rw [mul_pow, mul_pow, sq_abs]; ring
    have hexp : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
    calc ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 - 16 * ((t r : ℝ) / n) ^ 2 := hfac r hrR
    _ ≤ 4 - 16 * (1 / (9 * D ^ 2)) := by linarith
    _ = 4 * (1 - a) := by rw [hadef]; ring
    _ ≤ 4 * Real.exp (-a) := by linarith
  have hbad : ∀ r ∈ R, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 := by
    intro r hr
    have := hfac r hr
    nlinarith [sq_nonneg ((t r : ℝ) / n)]
  -- the product
  have hprod : ‖∏ r ∈ R, (1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹))‖ ^ 2
      ≤ 4 ^ R.card * Real.exp (-(2 * v)) := by
    rw [norm_prod, ← Finset.prod_pow,
      ← Finset.prod_filter_mul_prod_filter_not R (fun r : ℕ => |(r : ℝ) * t r| ≤ L * n)]
    have hB' : ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ 4 ^ B.card := by
      calc ∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2 ≤ ∏ r ∈ B, (4 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => by positivity)
              (fun r hr => hbad r (Finset.mem_filter.1 hr).1)
      _ = 4 ^ B.card := Finset.prod_const _
    have hG' : ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ (4 * Real.exp (-a)) ^ G.card := by
      calc ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
          ≤ ∏ r ∈ G, (4 * Real.exp (-a)) :=
            Finset.prod_le_prod (fun _ _ => by positivity) hgood
      _ = (4 * Real.exp (-a)) ^ G.card := Finset.prod_const _
    have hexpG : Real.exp (-a) ^ G.card ≤ Real.exp (-(2 * v)) := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have ha : 0 ≤ a := by positivity
      have : 2 * v ≤ G.card * a := by
        calc 2 * v ≤ (K / 2) * a := by exact hgcount
        _ ≤ G.card * a := mul_le_mul_of_nonneg_right hGcard ha
      linarith
    calc (∏ r ∈ B, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2) *
          ∏ r ∈ G, ‖1 + ZMod.stdAddChar (h * ((r : ZMod n))⁻¹)‖ ^ 2
        ≤ 4 ^ B.card * (4 * Real.exp (-a)) ^ G.card :=
          mul_le_mul hB' hG' (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)
    _ = 4 ^ R.card * Real.exp (-a) ^ G.card := by
          rw [mul_pow, ← mul_assoc, ← pow_add, hBG]
    _ ≤ 4 ^ R.card * Real.exp (-(2 * v)) :=
          mul_le_mul_of_nonneg_left hexpG (by positivity)
  have hfinal : (2 ^ R.card / (n : ℝ)) ^ 2 = 4 ^ R.card * Real.exp (-(2 * v)) := by
    have e1 : Real.exp (v) ^ 2 = Real.exp (2 * v) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [hn_exp, div_pow, e1, Real.exp_neg, div_eq_mul_inv, ← pow_mul, mul_comm R.card 2,
      pow_mul]
    norm_num
  rw [← hfinal] at hprod
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hprod


end Lemma1Aux
end Croot
end

section
open Finset Real Filter
open scoped Topology
namespace Croot

open Real Finset Filter

/-- For every `n` and every `ε > 0`, eventually `(log x) ^ n ≤ ε √x`. -/
lemma eventually_log_pow_le_mul_sqrt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ n ≤ ε * √x := by
  have h := (isLittleO_log_rpow_rpow_atTop (n : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound hε
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  have e1 : ‖Real.log x ^ (n : ℝ)‖ = Real.log x ^ n := by
    rw [Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog n)]
  have e2 : ‖x ^ (1 / 2 : ℝ)‖ = √x := by
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hx' : ‖Real.log x ^ (n : ℝ)‖ ≤ ε * ‖x ^ (1 / 2 : ℝ)‖ := hx
  rw [e1, e2] at hx'
  exact hx'

/-- For large `x` there are at least `x / (5 log x)` primes in `(x, 2.7 x]`. -/
theorem eventually_card_primes_Ioc_ge : ∀ᶠ x : ℝ in atTop,
    x / (5 * Real.log x) ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
  filter_upwards [eventually_ge_atTop (10 : ℝ),
    eventually_log_pow_le_mul_sqrt 1 (ε := 1 / 2000) (by norm_num),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with x hx hlogx hL2
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hl2lo : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hl2hi : Real.log 2 < 7 / 10 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hfl : ⌊x⌋₊ ≤ ⌊(27 / 10 : ℝ) * x⌋₊ := Nat.floor_le_floor (by linarith)
  have hsplit : Chebyshev.theta ((27 / 10 : ℝ) * x) = Chebyshev.theta x +
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    simp only [Chebyshev.theta, Finset.sum_filter]
    rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hfl]
  have hsum : ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p ≤
      (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) *
        Real.log ((27 / 10 : ℝ) * x) := by
    have h := Finset.sum_le_card_nsmul ((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime)
      (fun p : ℕ => Real.log p) (Real.log ((27 / 10 : ℝ) * x)) (by
        intro p hp
        have hp' := Finset.mem_filter.mp hp
        have hpI := Finset.mem_Ioc.mp hp'.1
        have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
        have hp_le : (p : ℝ) ≤ (27 / 10 : ℝ) * x :=
          le_trans (by exact_mod_cast hpI.2) (Nat.floor_le (by linarith))
        exact Real.log_le_log hp_pos hp_le)
    rw [nsmul_eq_mul] at h
    exact h
  have hlow := Chebyshev.theta_ge' (x := (27 / 10 : ℝ) * x) (by linarith)
  have hup := Chebyshev.theta_le_log4_mul_x hx0
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; ring
  rw [hlog4] at hup
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have hs3 : 3 ≤ √x := Real.le_sqrt_of_sq_le (by linarith)
  have hlogx' : Real.log x ≤ 1 / 2000 * √x := by simpa using hlogx
  have hlog27 : Real.log ((27 / 10 : ℝ) * x) ≤ Real.log x + 17 / 10 := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have : Real.log (27 / 10 : ℝ) ≤ 27 / 10 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlog27' : 0 ≤ Real.log ((27 / 10 : ℝ) * x) := Real.log_nonneg (by linarith)
  have hlogx2 : Real.log ((27 / 10 : ℝ) * x + 2) ≤ Real.log x + 2 := by
    have h3x := Real.log_le_log (by linarith) (show (27 / 10 : ℝ) * x + 2 ≤ 3 * x by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3x
    have : Real.log (3 : ℝ) ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hsqrt27 : √((27 / 10 : ℝ) * x) ≤ 2 * √x := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hx0]
  have hprod : √((27 / 10 : ℝ) * x) * Real.log ((27 / 10 : ℝ) * x) ≤
      (2 * √x) * (2 * Real.log x) :=
    mul_le_mul hsqrt27 (by linarith) hlog27' (by positivity)
  have hsL : √x * Real.log x ≤ √x * (1 / 2000 * √x) := mul_le_mul_of_nonneg_left hlogx' hs0
  have hsL3 : 3 ≤ √x * Real.log x := by nlinarith
  have hLsL : Real.log x ≤ √x * Real.log x := by nlinarith
  have hx2 : 693 / 1000 * x ≤ Real.log 2 * x := mul_le_mul_of_nonneg_right hl2lo.le hx0
  have hdiff : (48 / 100 : ℝ) * x ≤
      ∑ p ∈ (Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime, Real.log p := by
    linarith [hsplit, hlow, hup, hlogx2, hprod, hsL, hss, hsL3, hLsL, hx2]
  have hcard0 : (0 : ℝ) ≤ (((Ioc ⌊x⌋₊ ⌊(27 / 10 : ℝ) * x⌋₊).filter Nat.Prime).card : ℝ) := by
    positivity
  have hc1 := mul_le_mul_of_nonneg_left hlog27 hcard0
  have hc2 := mul_nonneg hcard0 (show (0 : ℝ) ≤ 5 / 2 * Real.log x - 17 / 4 by linarith)
  rw [div_le_iff₀ (by linarith)]
  linarith [hsum, hdiff, hc1, hc2]
end Croot
namespace Big308

lemma pow_absorb (a b C : ℝ) (hab : a<b) :
    ∀ᶠ v : ℝ in atTop, C*v^a ≤ v^b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C,eventually_gt_atTop (0:ℝ)] with v hv hpos
  calc
    _ ≤ v^(b-a)*v^a := mul_le_mul_of_nonneg_right hv (rpow_nonneg hpos.le _)
    _ = _ := by rw [←rpow_add hpos];congr 1;ring

lemma primes (η : ℝ) (hη : 0<η) : ∀ᶠ i : ℕ in atTop, ∀ p : ℕ, p.Prime →
    (∀ r : ℕ, r.Prime → r∣i → r=p) →
    let Y := (log i)^(3+12*η)
    ∃ S : Finset ℕ, (S.card:ℝ) ≤ 3*Y ∧
      (∀ r ∈ S, r.Prime ∧ r≠p ∧ Y≤r ∧ (r:ℝ)≤3*Y) ∧
      ∀ z : ZMod i, ∃ T ⊆ S, ∑ r ∈ T, (r:ZMod i)⁻¹=z := by
  let b := 3+12*η
  let k := 3+11*η
  let l := 2+9*η
  let d := 1+3*η
  have hbp : 0<b := by dsimp [b];linarith
  have hkp : 0<k := by dsimp [k];linarith
  have hlp : 0<l := by dsimp [l];linarith
  have tv : Tendsto (fun i : ℕ => log (i:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ty := (tendsto_rpow_atTop hbp).comp tv
  have hab := tv.eventually (pow_absorb (l+1) k 20 (by dsimp [l,k];linarith))
  have hag := tv.eventually (pow_absorb (2*d+1) k 9 (by dsimp [d,k];linarith))
  have logsmall := tv.eventually ((isLittleO_log_rpow_atTop hη).bound
    (show 0<1/(10*b) by positivity))
  have lsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop l one_pos).bound (show (0:ℝ)<1/2 by norm_num))
  filter_upwards [eventually_ge_atTop 4,tv.eventually_ge_atTop 2,ty.eventually_ge_atTop 16,
    ty.eventually Croot.eventually_card_primes_Ioc_ge,hab,hag,logsmall,lsmall] with i hi hv hy hn ha hb hlog hLsmall
  intro p hp hall
  let v := log (i:ℝ)
  let Y := v^b
  let K := v^k
  let L := v^l
  let D := v^d
  change 2≤v at hv
  change (16:ℝ)≤Y at hy
  let X := (Ioc ⌊Y⌋₊ ⌊(27/10:ℝ)*Y⌋₊).filter Nat.Prime
  change Y/(5*log Y) ≤ (X.card:ℝ) at hn
  have vp : 0<v := by linarith
  have yp : 0<Y := by positivity
  have lp : 0<L := by positivity
  have dp : 0<D := by positivity
  have kp : 1≤K := one_le_rpow (by linarith) hkp.le
  have l1 : 1≤L := one_le_rpow (by linarith) hlp.le
  have ic : (4:ℝ) ≤ i := by exact_mod_cast hi
  have vpos := log_pos (show 1<v by linarith)
  have lo : 10*b*log v ≤ v^η := by
    change ‖log v‖ ≤ 1/(10*b)*‖v^η‖ at hlog
    rw [Real.norm_eq_abs,abs_of_pos vpos,Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos vp _)] at hlog
    field_simp at hlog
    linarith
  have bh : 2*K ≤ Y/(5*log Y) := by
    have ly : log Y=b*log v := Real.log_rpow vp _
    rw [ly, le_div_iff₀ (by positivity)]
    have yk : Y=v^η*K := by dsimp [Y,K];rw [←rpow_add vp];congr 1; dsimp [k,b];ring
    rw [yk]
    nlinarith only [mul_le_mul_of_nonneg_right lo (show 0≤K by linarith)]
  let S := X.erase p
  have sc : (K:ℝ) ≤ S.card := by
    have card : X.card ≤ S.card+1 := by
      by_cases h : p∈X
      · exact (card_erase_add_one h).ge
      · simp [S,h]
    have hh : (X.card:ℝ) ≤ S.card+1 := by exact_mod_cast card
    linarith
  have props : ∀ r∈S, r.Prime ∧ r≠p ∧ Y≤r ∧ (r:ℝ)≤3*Y := by
    intro r hr
    obtain ⟨ne,mem⟩ := mem_erase.mp hr
    obtain ⟨mem,pr⟩ := mem_filter.mp mem
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp mem
    exact ⟨pr,ne,(Nat.lt_of_floor_lt hlo).le,((Nat.le_floor_iff (by positivity)).mp hhi).trans (by linarith)⟩
  refine ⟨S,?_,props,?_⟩
  · have hsub : S ⊆ Icc 1 ⌊3*Y⌋₊ := fun r hr => mem_Icc.mpr ⟨(props r hr).1.pos,
      Nat.le_floor (props r hr).2.2.2⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Icc,Nat.add_sub_cancel] at hcard
    exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le (by positivity))
  · intro z
    letI : NeZero i := ⟨by omega⟩
    apply Croot.Lemma1Aux.exists_subset_sum_of_norm_prod_le S _ _ z
    intro h hh
    have hbcount : (2*(L+1)+1)*(2*v) ≤ K/2 := by
      change 20*v^(l+1) ≤ K at ha
      rw [rpow_add vp,rpow_one] at ha
      change 20*(L*v) ≤ K at ha
      nlinarith only [ha,mul_le_mul_of_nonneg_right l1 vp.le]
    have hgcount : 2*v ≤ (K/2)*(4/(9*D^2)) := by
      change 9*v^(2*d+1)≤K at hb
      have powD : v^(2*d+1)=D^2*v := by
        rw [rpow_add vp,rpow_one,mul_comm (2:ℝ) d,rpow_mul vp.le,rpow_two]
      rw [powD] at hb
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith only [hb]
    have lbound : L+2 ≤ (i:ℝ) := by
      change ‖L‖ ≤ (1/2)*‖(i:ℝ)^(1:ℝ)‖ at hLsmall
      rw [rpow_one,Real.norm_eq_abs,abs_of_pos lp,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)] at hLsmall
      linarith
    refine Croot.Lemma1Aux.norm_prod_general i v Y L D K vp yp lp dp ?_ (by linarith [Real.exp_one_lt_three]) lbound
      (Real.exp_log (by positivity : (0:ℝ) < i)).symm hbcount hgcount S ?_ sc h hh
    · dsimp [Y,L,D];rw [←rpow_add vp];congr 1;dsimp [l,d,b];ring
    · intro r hr
      obtain ⟨pr,ne,hlo,hhi⟩ := props r hr
      exact ⟨pr,fun hh => ne (hall r pr hh),by linarith,hhi⟩
end Big308
end

section
open Finset Real
open scoped Classical
namespace Egyptian
open Nat
lemma complement_dvd {i : ℕ} (hi : 0 < i) : lcmUpto i / i ∣ lcmUpto (i-1) := by
  apply (Nat.mul_dvd_mul_iff_left hi).mp
  rw [Nat.mul_div_cancel' (ongrid hi le_rfl)]
  apply Finset.lcm_dvd
  intro n hn
  obtain ⟨hn,hle⟩ := mem_Icc.mp hn
  by_cases e : n = i
  · subst n
    exact dvd_mul_right _ _
  · exact dvd_trans (ongrid hn (show n ≤ i-1 by omega)) (dvd_mul_left _ _)

lemma cancel {i : ℕ} (hi : 0 < i) {M : Finset ℕ}
    (adm : ∀ m ∈ M, 0 < m ∧ m ≤ i ∧ i.Coprime m)
    (hc : i.Coprime (lcmUpto i / i)) (z : ℤ)
    (res : ∑ m ∈ M, (m : ZMod i)⁻¹ = (z : ZMod i) * ((lcmUpto i / i : ℕ) : ZMod i)⁻¹) :
    ∃ a : ℤ, (a:ℚ)/lcmUpto (i-1) = (z:ℚ)/lcmUpto i - ∑ m ∈ M, (1:ℚ)/((i:ℚ)*m) := by
  let D := lcmUpto i / i
  have he : i*D = lcmUpto i := Nat.mul_div_cancel' (ongrid hi le_rfl)
  have dvd (m : ℕ) (hm : m ∈ M) : m ∣ D :=
    (adm m hm).2.2.symm.dvd_of_dvd_mul_left (he.symm ▸ ongrid (adm m hm).1 (adm m hm).2.1)
  have hmz (m : ℕ) (hm : m ∈ M) : ((D/m : ℕ) : ZMod i) = (D : ZMod i) * (m : ZMod i)⁻¹ := by
    have hh : ((D/m : ℕ):ZMod i)*(m:ZMod i) = D := by rw [← Nat.cast_mul, Nat.div_mul_cancel (dvd m hm)]
    rw [← hh, mul_assoc, ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr (adm m hm).2.2.symm), mul_one]
  have modzero : ((z - ∑ m ∈ M, ((D/m:ℕ):ℤ) : ℤ) : ZMod i) = 0 := by
    simp only [Int.cast_sub,Int.cast_sum,Int.cast_natCast]
    rw [sum_congr rfl hmz, ← mul_sum, res]
    change (z:ZMod i) - (D:ZMod i)*((z:ZMod i)*(D:ZMod i)⁻¹) = 0
    rw [mul_left_comm, ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hc.symm), mul_one, sub_self]
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp modzero
  obtain ⟨c,hc'⟩ := complement_dvd hi
  refine ⟨b*c,?_⟩
  have rat (m : ℕ) (hm : m ∈ M) : (1:ℚ)/((i:ℚ)*m) = ((D/m:ℕ):ℚ)/lcmUpto i := by
    have mm : (m:ℚ) ≠ 0 := by exact_mod_cast (adm m hm).1.ne'
    apply (div_eq_div_iff (mul_ne_zero (by exact_mod_cast hi.ne') mm) (by exact_mod_cast lcmUpto_ne_zero i)).mpr
    have ff : ((D/m:ℕ):ℚ)*(m:ℚ) = D := by exact_mod_cast Nat.div_mul_cancel (dvd m hm)
    have gg : (i:ℚ)*D = lcmUpto i := by exact_mod_cast he
    linear_combination gg*(-1) + ((i:ℚ)*ff)*(-1)
  rw [sum_congr rfl rat, ← sum_div, ← sub_div]
  have rb : (z:ℚ) - ∑ m ∈ M, ((D/m:ℕ):ℚ) = (i:ℚ)*b := by simpa only [Int.cast_sub,Int.cast_sum,Int.cast_natCast,Int.cast_mul] using congrArg (Int.cast : ℤ → ℚ) hb
  rw [rb]
  push_cast
  have eq : (i:ℚ)*D = lcmUpto i := by exact_mod_cast he
  have eq' : (lcmUpto (i-1):ℚ) = (D:ℚ)*c := by exact_mod_cast hc'
  apply (div_eq_div_iff (by exact_mod_cast lcmUpto_ne_zero (i-1)) (by exact_mod_cast lcmUpto_ne_zero i)).mpr
  rw [← eq,eq']; ring

end Egyptian
namespace Big308
private lemma multiplier297 {p : ℕ} (hp : p.Prime) (x : ℝ) (hx : 100 ≤ x) :
    ∃ u : ℕ, x ≤ u ∧ (u:ℝ) ≤ 6/5*x ∧ p.Coprime u ∧ ¬2∣u ∧ ¬3∣u := by
  let c := ⌈x/6⌉₊
  let v := 6*c+1
  let u := if p ∣ v then v+6 else v
  have vl : v ≤ u ∧ u ≤ v+6 := by dsimp [u]; split <;> omega
  have lo : x/6 ≤ (c:ℝ) := Nat.le_ceil _
  have up : (c:ℝ) < x/6+1 := Nat.ceil_lt_add_one (by linarith)
  have vdef : (v:ℝ) = 6*(c:ℝ)+1 := by dsimp [v]; push_cast; ring
  have l' : (v:ℝ) ≤ u := by exact_mod_cast vl.1
  have u' : (u:ℝ) ≤ (v:ℝ)+6 := by exact_mod_cast vl.2
  refine ⟨u,by linarith,by linarith,hp.coprime_iff_not_dvd.mpr ?_,?_,?_⟩
  · dsimp only [u]
    split_ifs with hd
    · intro h
      have hs := (Nat.dvd_add_right hd).mp h
      have hv : p ∣ 6*c := dvd_mul_of_dvd_left hs _
      exact hp.not_dvd_one ((Nat.dvd_add_right hv).mp hd)
    · exact hd
  · dsimp only [u,v]; split <;> omega
  · dsimp only [u,v]; split <;> omega


open Mid308
lemma scaled {p k i N : ℕ} (hp : p.Prime) (hk : 0<k) (eqi : p^k=i)
    (hiN : N ≤ i*i) {Y : ℝ} (hY : 0<Y) (hroom : 600*(i:ℝ)*Y ≤ N) (S : Finset ℕ)
    (hc : (S.card:ℝ)≤3*Y) (mem : ∀ r∈S, r.Prime ∧ r≠p ∧ Y≤r ∧ (r:ℝ)≤3*Y)
    (full : ∀ z : ZMod i, ∃ T ⊆ S, ∑ r ∈ T,(r:ZMod i)⁻¹=z)
    {C : ℕ} (hC : 18*Y ≤ C) : desc N i ((C:ℚ)/N) := by
  classical
  obtain rfl := eqi
  let i := p^k
  have hi : 0 < i := pow_pos hp.pos _
  have ir : (0:ℝ)<(i:ℝ) := by exact_mod_cast hi
  have ip : IsPrimePow i := (isPrimePow_nat_iff _).mpr ⟨p,k,hp,hk,rfl⟩
  change 600*(i:ℝ)*Y ≤ N at hroom
  have nreal : (0:ℝ)<N := lt_of_lt_of_le (by positivity) hroom
  let W := (N:ℝ)/(6*(i:ℝ)*Y)
  have hW : 100 ≤ W := (le_div_iff₀ (by positivity)).mpr (by linarith)
  obtain ⟨u,hul,huu,cpu,-,-⟩ := multiplier297 hp W hW
  have ureal : (0:ℝ)<u := by linarith
  have upos : 0 < u := by exact_mod_cast ureal
  let g (r : ℕ) := u*r
  have inj : Function.Injective g := fun _ _ e => Nat.eq_of_mul_eq_mul_left upos e
  have lower : (N:ℝ) ≤ 6*(i:ℝ)*(u:ℝ)*Y := by
    have := (div_le_iff₀ (by positivity : 0<6*(i:ℝ)*Y)).mp hul
    linarith
  have upper : (i:ℝ)*(u:ℝ)*(3*Y) ≤ N := by
    have hW' : W*(6*(i:ℝ)*Y)=N := div_mul_cancel₀ _ (by positivity)
    have hm := mul_le_mul_of_nonneg_right huu (show 0≤6*(i:ℝ)*Y by positivity)
    nlinarith only [hm,hW',nreal]
  have num (r : ℕ) (hr : r∈S) : 0<g r ∧ i.Coprime (g r) ∧ N≤6*(i*g r) ∧ i*g r≤N := by
    obtain ⟨pr,ne,lo,hi'⟩ := mem r hr
    have cr := (Nat.coprime_primes hp pr).mpr ne.symm
    have hm : 0≤(i:ℝ)*u := by positivity
    refine ⟨Nat.mul_pos upos pr.pos,(cpu.mul_right cr).pow_left _,?_,?_⟩
    · change N ≤ 6*(i*(u*r))
      exact_mod_cast (show (N:ℝ) ≤ 6*((i:ℝ)*((u:ℝ)*r)) by
        nlinarith only [lower,mul_le_mul_of_nonneg_left lo hm])
    · change i*(u*r) ≤ N
      exact_mod_cast (show (i:ℝ)*((u:ℝ)*r) ≤ N by nlinarith only [upper,mul_le_mul_of_nonneg_left hi' hm])
  intro z
  let Z : ZMod i := (z:ZMod i)*((Nat.lcmUpto i/i:ℕ):ZMod i)⁻¹
  obtain ⟨T,hTS,hs⟩ := full ((u:ZMod i)*Z)
  let M := T.image g
  have ms : ∀ m∈M, 0 < m ∧ m ≤ i ∧ i.Coprime m ∧ N≤6*(i*m) ∧ i*m≤N := by
    intro m hm
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hm
    obtain ⟨pos,cop,low,high⟩ := num r (hTS hr)
    exact ⟨pos,Nat.le_of_mul_le_mul_left (high.trans hiN) hi,cop,low,high⟩
  have val : ∑ m∈M,(m:ZMod i)⁻¹ = Z := by
    have uc := ZMod.coe_mul_inv_eq_one (n:=i) u (cpu.pow_left k).symm
    dsimp only [M];rw [sum_image (fun _ _ _ _ h => inj h)]
    have per (r : ℕ) (hr : r∈T) : (g r:ZMod i)⁻¹=(u:ZMod i)⁻¹*(r:ZMod i)⁻¹ := by
      obtain ⟨pr,ne,-,-⟩ := mem r (hTS hr)
      have rc := ZMod.coe_mul_inv_eq_one (n:=i) r (((Nat.coprime_primes pr hp).mpr ne).pow_right k)
      apply ZMod.inv_eq_of_mul_eq_one
      dsimp [g];push_cast
      calc
        _ = ((u:ZMod i)*(u:ZMod i)⁻¹)*((r:ZMod i)*(r:ZMod i)⁻¹) := by ring
        _ = _ := by rw [uc,rc,mul_one]
    rw [sum_congr rfl per,←mul_sum,hs,←mul_assoc,mul_comm ((u:ZMod i)⁻¹),uc,one_mul]
  let V := M.image (i*·)
  have admiss (m : ℕ) (h : m∈M) := And.intro (ms m h).1 (And.intro (ms m h).2.1 (ms m h).2.2.1)
  have sub : V ⊆ layer N i := by
    intro n hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    obtain ⟨pos,hmi,cop,-,up⟩ := ms m hm
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hi pos,up⟩,?_,?_⟩
    · exact cop.mul_dvd_of_dvd_of_dvd (Egyptian.ongrid hi le_rfl) (Egyptian.ongrid pos hmi)
    · exact fun hd => pp_not_prev hp hk rfl (dvd_trans (dvd_mul_right i m) hd)
  have imageSum : (∑ n∈V,(1:ℚ)/n) = ∑ m∈M,(1:ℚ)/((i:ℚ)*m) := by
    dsimp only [V]; rw [sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hi h)];simp
  refine ⟨V,sub,?_,?_⟩
  · rw [imageSum]
    have nr : (0:ℚ)<N := by exact_mod_cast nreal
    have count : 6*M.card ≤ C := by
      have hMC : (M.card:ℝ) ≤ S.card := by exact_mod_cast (card_image_le.trans (card_le_card hTS) : M.card ≤ S.card)
      exact_mod_cast (show 6*(M.card:ℝ)≤C by linarith)
    calc
      _ ≤ ∑ _m ∈ M, (6:ℚ)/N := by
        apply sum_le_sum
        intro m hm
        rw [div_le_div_iff₀ (by exact_mod_cast Nat.mul_pos hi (ms m hm).1) nr,one_mul]
        exact_mod_cast (ms m hm).2.2.2.1
      _ = ((6:ℚ)*M.card)/N := by simp [div_eq_mul_inv];ring
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast count) nr.le
  · rw [imageSum]
    exact Egyptian.cancel hi admiss (Egyptian.complement ip) z val
end Big308
end

section
open Finset Real Filter
open scoped Classical Topology
namespace Big308
open Cut308 (pp count_pp)
lemma count : ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ q : ℕ in atTop,
    ((((Icc 1 q).filter IsPrimePow).card : ℝ)*log q) ≤ κ*q := by
  let c := 1/log 2+1
  have l2 : 0<log 2 := log_pos (by norm_num)
  have cp : 0<c := by dsimp [c];positivity
  refine ⟨log 4+2,by positivity,?_⟩
  have ts : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall := ts.eventually ((isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1/2)).bound (inv_pos.mpr cp))
  filter_upwards [hsmall,ts.eventually (Chebyshev.eventually_primeCounting_le one_pos),
    (tendsto_log_atTop.comp ts).eventually_ge_atTop 1] with q hsq hπ hl
  change 1 ≤ log q at hl
  have lp : 0<log q := by linarith
  have qr : 0 ≤ (q:ℝ) := Nat.cast_nonneg _
  have nl : (Nat.log 2 q:ℝ) ≤ log q/log 2 := by
    rw [←Real.natFloor_logb_natCast];exact Nat.floor_le (div_nonneg lp.le l2.le)
  have nup : (Nat.log 2 q:ℝ)+1 ≤ c*log q := by
    dsimp [c];rw [add_mul,one_mul];rw [div_mul_eq_mul_div,one_mul];linarith
  have hc : ((pp q 0).card:ℝ) ≤ sqrt q*(c*log q) := by
    calc _ ≤ (q.sqrt:ℝ)*((Nat.log 2 q:ℝ)+1) := by exact_mod_cast count_pp q 0
         _ ≤ _ := mul_le_mul Real.nat_sqrt_le_real_sqrt nup (by positivity) (sqrt_nonneg _)
  change ‖log (q:ℝ)^(2:ℝ)‖ ≤ c⁻¹*‖(q:ℝ)^(1/2:ℝ)‖ at hsq
  rw [rpow_two,←sqrt_eq_rpow,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)] at hsq
  have hmul : c*log q^2 ≤ sqrt q := by
    calc _ ≤ c*(c⁻¹*sqrt q) := mul_le_mul_of_nonneg_left hsq cp.le
         _ = _ := by rw [←mul_assoc,mul_inv_cancel₀ cp.ne',one_mul]
  have hsub : (Icc 1 q).filter IsPrimePow ⊆ (Nat.primesLE q) ∪ pp q 0 := by
    intro n hn
    obtain ⟨mem,pr⟩ := mem_filter.mp hn
    obtain ⟨lo,hi⟩ := mem_Icc.mp mem
    by_cases h : n.Prime
    · exact mem_union_left _ (Nat.mem_primesLE.mpr ⟨hi,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Ioc.mpr ⟨lo,hi⟩,pr,h⟩)
  have hc' := (card_le_card hsub).trans (card_union_le _ _)
  rw [Nat.primesLE_card_eq_primeCounting] at hc'
  have cc : (((Icc 1 q).filter IsPrimePow).card:ℝ) ≤ (q.primeCounting:ℝ)+(pp q 0).card := by exact_mod_cast hc'
  change (Nat.primeCounting ⌊(q:ℝ)⌋₊:ℝ) ≤ (log 4+1)*q/log q at hπ
  rw [Nat.floor_natCast,le_div_iff₀ lp] at hπ
  nlinarith only [mul_le_mul_of_nonneg_right cc lp.le,hπ,mul_le_mul_of_nonneg_right hc lp.le,
    mul_le_mul_of_nonneg_left hmul (sqrt_nonneg (q:ℝ)),Real.sq_sqrt qr]
end Big308
end

section
open Finset Real Filter Mid308
open scoped Classical Topology
namespace Big308
lemma total {N Q C : ℕ} {κ ε a : ℝ} (nr : 0 < (N:ℝ)) (lp : 0 < log N)
    (cap : (Q:ℝ)*(log N)^a ≤ N) (cC : (C:ℝ) ≤ 19*(log N)^a)
    (hq : N.sqrt < Q → ((((Icc 1 Q).filter IsPrimePow).card:ℝ)*log Q) ≤ κ*Q)
    (kk : 0 < κ) (budget : 38*κ ≤ ε*log (log N)^2) (ep : 0<ε) :
    ((∑ i ∈ Ioc N.sqrt Q, if IsPrimePow i then (C:ℚ)/N else 0 : ℚ):ℝ)
      ≤ ε*log (log N)^2/log N := by
  by_cases h : N.sqrt < Q
  · let A := (Ioc N.sqrt Q).filter IsPrimePow
    let U := (Icc 1 Q).filter IsPrimePow
    have sub : A ⊆ U := by
      intro i hi
      obtain ⟨mem,pr⟩ := mem_filter.mp hi
      obtain ⟨lo,up⟩ := mem_Ioc.mp mem
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,up⟩,pr⟩
    have qpos : 0 < (Q:ℝ) := by exact_mod_cast (show 0<Q by omega)
    have qs : (N:ℝ) ≤ (Q:ℝ)*Q := by exact_mod_cast (Nat.sqrt_lt.mp h).le
    have ll := log_le_log nr qs
    rw [log_mul qpos.ne' qpos.ne'] at ll
    have card : (A.card:ℝ) ≤ U.card := by exact_mod_cast card_le_card sub
    have cA : (A.card:ℝ)*log N ≤ 2*κ*Q := by
      have b := hq h
      change (U.card:ℝ)*log Q ≤ κ*Q at b
      nlinarith only [mul_le_mul_of_nonneg_right card lp.le,
        mul_le_mul_of_nonneg_left ll (Nat.cast_nonneg (α:=ℝ) U.card),b]
    have main := mul_le_mul cA cC (Nat.cast_nonneg (α:=ℝ) C) (by positivity)
    rw [←sum_filter,sum_const,nsmul_eq_mul,Rat.cast_mul,Rat.cast_natCast,
      Rat.cast_div,Rat.cast_natCast,Rat.cast_natCast]
    change (A.card:ℝ)*((C:ℝ)/N) ≤ _
    rw [le_div_iff₀ lp]
    apply le_trans _ budget
    rw [←mul_div_assoc,div_mul_eq_mul_div,div_le_iff₀ nr]
    nlinarith only [main,mul_le_mul_of_nonneg_left cap (show 0≤38*κ by positivity)]
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty,Rat.cast_zero]
    positivity

lemma result (a : ℝ) (ha : 3<a) (ε : ℝ) (he : 0<ε) : ∀ᶠ N : ℕ in atTop,
    let Q := ⌊(N:ℝ)/(log N)^a⌋₊
    ∃ cost : ℕ→ℚ, ((∑ i ∈ Ioc N.sqrt Q,cost i:ℚ):ℝ) ≤ ε*(log (log N))^2/log N ∧
      ∀ i ∈ Ioc N.sqrt Q, desc N i (cost i) := by
  let η := (a-3)/24
  let b := 3+12*η
  have hη : 0<η := by dsimp [η];linarith
  have hb : 0<b := by dsimp [b];linarith
  have hba : b<a := by dsimp [b,η];linarith
  obtain ⟨i₀,ipool⟩ := eventually_atTop.1 (primes η hη)
  obtain ⟨κ,kk,hκ⟩ := count
  obtain ⟨q₀,qcount⟩ := eventually_atTop.1 hκ
  have tp : Tendsto (fun N : ℕ => log (N:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop ((max (max i₀ q₀) 2)^2),
    tp.eventually_ge_atTop 1,tp.eventually (pow_absorb b a 600 hba),
    (tendsto_log_atTop.comp tp).eventually_ge_atTop (max 1 (38*κ/ε))] with N hn hL hroom hB
  let L := log (N:ℝ)
  let Q := ⌊(N:ℝ)/L^a⌋₊
  let C := ⌈18*L^b⌉₊
  change 1 ≤ L at hL
  change 600*L^b ≤ L^a at hroom
  change max 1 (38*κ/ε) ≤ log L at hB
  have sqr := Nat.le_sqrt'.mpr hn
  have nr : 0 < (N:ℝ) := by
    have hn' : 2^2 ≤ N := (Nat.pow_le_pow_left (le_max_right _ _) 2).trans hn
    exact_mod_cast (show 0<N by omega)
  have lp : 0<L := by linarith
  have cceil := Nat.ceil_lt_add_one (show (0:ℝ)≤18*L^b by positivity)
  have lb1 := one_le_rpow hL hb.le
  have qfloor : (Q:ℝ) ≤ N/L^a := Nat.floor_le (by positivity)
  have cap := (le_div_iff₀ (rpow_pos_of_pos lp _)).mp qfloor
  have qN : Q ≤ N := by
    have hp1 := one_le_rpow hL (show 0≤a by linarith)
    exact_mod_cast (show (Q:ℝ) ≤ N by nlinarith only [cap,mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg (α:=ℝ) Q)])
  let cost (i : ℕ) : ℚ := if IsPrimePow i then (C:ℚ)/N else 0
  refine ⟨cost,?_,?_⟩
  · apply total nr lp cap (by change (C:ℝ) ≤ 19*L^a;change (C:ℝ) < 18*L^b+1 at cceil;linarith)
      (fun h => qcount Q (by omega)) kk _ he
    have y := (div_le_iff₀ he).mp ((le_max_right _ _).trans hB)
    have z : 1≤log L := (le_max_left _ _).trans hB
    change 38*κ ≤ ε*(log L)^2
    nlinarith only [y,mul_le_mul_of_nonneg_left (show log L ≤ (log L)^2 by nlinarith [sq_nonneg (log L-1)]) he.le]
  · intro i hi
    obtain ⟨low,up⟩ := mem_Ioc.mp hi
    have i₁ : 1 < i := by omega
    by_cases pp : IsPrimePow i
    · obtain ⟨p,k,pr,hk,pk⟩ := (isPrimePow_nat_iff _).mp pp
      have onlyp (r : ℕ) (hr : r.Prime) (hd : r∣i) : r=p := by
        rw [←pk] at hd
        exact ((Nat.dvd_prime pr).mp (hr.dvd_of_dvd_pow hd)).resolve_left hr.ne_one
      obtain ⟨S,card,mem,full⟩ := ipool i (by omega) p pr onlyp
      let Y := (log (i:ℝ))^b
      have il : 0<log (i:ℝ) := log_pos (by exact_mod_cast i₁)
      have ub : Y ≤ L^b := rpow_le_rpow il.le (log_le_log (by positivity) (by exact_mod_cast up.trans qN)) hb.le
      change desc N i (if IsPrimePow i then (C:ℚ)/N else 0)
      rw [if_pos pp]
      refine scaled pr hk pk (Nat.sqrt_lt.mp low).le (rpow_pos_of_pos il _) ?_ S card mem full ?_
      · calc 600*(i:ℝ)*Y ≤ (i:ℝ)*(600*L^b) := by nlinarith only [mul_le_mul_of_nonneg_left ub (Nat.cast_nonneg (α:=ℝ) i)]
             _ ≤ (i:ℝ)*L^a := mul_le_mul_of_nonneg_left hroom (Nat.cast_nonneg _)
             _ ≤ (Q:ℝ)*L^a := mul_le_mul_of_nonneg_right (by exact_mod_cast up) (by positivity)
             _ ≤ _ := cap
      · exact (mul_le_mul_of_nonneg_left ub (by norm_num)).trans (Nat.le_ceil _)
    · simpa [cost,pp] using empty_step (N:=N) i₁ pp
end Big308
end

end

theorem OMA.solution : type_of% @Erdos308.erdos_308.variants.croot :=
  OMA.R_Erdos308_erdos_308_variants_croot_R1.main
    (OMA.R_Erdos308_erdos_308_variants_croot_R1_H1_R1.main Cut308.result Mid308.total Big308.result)
    Count308.final_estimate
