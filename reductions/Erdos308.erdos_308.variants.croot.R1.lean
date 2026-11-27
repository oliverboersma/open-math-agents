import FormalConjectures.ErdosProblems.«308»
import Mathlib

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
