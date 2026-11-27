import OMAReductions.R_Erdos700_erdos_700_parts_ii_R1
import Mathlib

-- Step Erdos700.erdos_700.parts.ii.R1.H2: hypothesis H2 of reduction Erdos700.erdos_700.parts.ii.R1
-- Credit: @ivillar
-- Proof: Chebyshev's bounds in Mathlib (theta_ge, theta_le_log4_mul_x) give more than 8 * 2^s * (s+1)
-- primes in (M, 3M] for M = 4^(s+1), s >= 10. Split (M, 3M] into 8 * 2^s windows of width 2^s; by
-- pigeonhole one window holds s + 2 primes. A halving argument shows that s + 2 numbers in a window
-- of width 2^s contain p < q < r with q - p < r - q, and 2 (r - p)^2 < 2 * 4^s < M < p.


namespace OMA.E700H2

open Finset Real Chebyshev

/-- Halving: a set of `k + 2` numbers in `[lo, hi]` with no triple `a < b < c`, `b - a < c - b`,
has `2 ^ k ≤ hi - lo`. -/
theorem spread : ∀ k : ℕ, ∀ (S : Finset ℕ) (lo hi : ℕ), S.card = k + 2 →
    (∀ x ∈ S, lo ≤ x ∧ x ≤ hi) →
    (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a < b → b < c → c - b ≤ b - a) →
    2 ^ k ≤ hi - lo := by
  intro k
  induction k with
  | zero =>
    intro S lo hi hc hb _
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hc
    have h1 := hb x (by simp)
    have h2 := hb y (by simp)
    simp only [pow_zero]
    omega
  | succ k ih =>
    intro S lo hi hc hb hno
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, haS, hamin⟩ : ∃ a ∈ S, ∀ x ∈ S, a ≤ x :=
      ⟨_, S.min'_mem hne, fun x hx => S.min'_le x hx⟩
    have hc' : (S.erase a).card = k + 2 := by
      have := Finset.card_erase_of_mem haS
      omega
    have hne' : (S.erase a).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, hbS', hbmin⟩ : ∃ b ∈ S.erase a, ∀ x ∈ S.erase a, b ≤ x :=
      ⟨_, (S.erase a).min'_mem hne', fun x hx => (S.erase a).min'_le x hx⟩
    obtain ⟨c, hcS', hcmax⟩ : ∃ c ∈ S.erase a, ∀ x ∈ S.erase a, x ≤ c :=
      ⟨_, (S.erase a).max'_mem hne', fun x hx => (S.erase a).le_max' x hx⟩
    have hbS : b ∈ S := Finset.mem_of_mem_erase hbS'
    have hcS : c ∈ S := Finset.mem_of_mem_erase hcS'
    have hab : a < b := lt_of_le_of_ne (hamin b hbS) (Finset.ne_of_mem_erase hbS').symm
    obtain ⟨x, hx, hxb⟩ := Finset.exists_mem_ne (show 1 < (S.erase a).card by omega) b
    have hbc : b < c := lt_of_lt_of_le (lt_of_le_of_ne (hbmin x hx) hxb.symm) (hcmax x hx)
    have hgap := hno a haS b hbS c hcS hab hbc
    have hrec := ih (S.erase a) b c hc' (fun x hx => ⟨hbmin x hx, hcmax x hx⟩)
      (fun x hx y hy z hz => hno x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) z
        (Finset.mem_of_mem_erase hz))
    have hlo := (hb a haS).1
    have hhi := (hb c hcS).2
    rw [pow_succ]
    omega

theorem pow_bound (s : ℕ) (hs : 10 ≤ s) : 5 * s ^ 2 + 15 * s + 20 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    have h : 5 * (n + 1) ^ 2 + 15 * (n + 1) + 20 ≤ 2 * (5 * n ^ 2 + 15 * n + 20) := by
      ring_nf
      nlinarith
    omega

/-- The primes in `(M, 3M]` for `M = 4 ^ (s + 1)`. -/
def P (s : ℕ) : Finset ℕ := (Finset.Ioc (4 ^ (s + 1)) (3 * 4 ^ (s + 1))).filter Nat.Prime

theorem theta_split (M : ℕ) :
    θ ((3 * M : ℕ) : ℝ) ≤ θ (M : ℝ) +
      (((Finset.Ioc M (3 * M)).filter Nat.Prime).card : ℝ) * Real.log ((3 * M : ℕ) : ℝ) := by
  rw [theta_eq_sum_Icc, theta_eq_sum_Icc, Nat.floor_natCast, Nat.floor_natCast]
  have hU : (Finset.Icc 0 (3 * M)).filter Nat.Prime =
      (Finset.Icc 0 M).filter Nat.Prime ∪ (Finset.Ioc M (3 * M)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h0, h1⟩, hp⟩
      by_cases hpm : p ≤ M
      · exact Or.inl ⟨⟨h0, hpm⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, h1⟩, hp⟩
    · rintro (⟨⟨h0, h1⟩, hp⟩ | ⟨⟨h0, h1⟩, hp⟩)
      · exact ⟨⟨h0, by omega⟩, hp⟩
      · exact ⟨⟨by omega, h1⟩, hp⟩
  have hD : Disjoint ((Finset.Icc 0 M).filter Nat.Prime) ((Finset.Ioc M (3 * M)).filter Nat.Prime) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hx hx'
    omega
  rw [hU, Finset.sum_union hD]
  gcongr
  rw [← nsmul_eq_mul]
  apply Finset.sum_le_card_nsmul
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  exact Real.log_le_log (by exact_mod_cast hp.2.pos) (by exact_mod_cast hp.1.2)

theorem count_bound (s : ℕ) (hs : 10 ≤ s) : 8 * 2 ^ s * (s + 1) < (P s).card := by
  by_contra hcon
  push Not at hcon
  have hsplit := theta_split (4 ^ (s + 1))
  have h3 := theta_ge (3 * 4 ^ (s + 1))
  have h1 := theta_le_log4_mul_x (x := ((4 ^ (s + 1) : ℕ) : ℝ)) (by positivity)
  have hpb := pow_bound s hs
  have hKdef : ((Finset.Ioc (4 ^ (s + 1)) (3 * 4 ^ (s + 1))).filter Nat.Prime).card =
      (P s).card := rfl
  rw [hKdef] at hsplit
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = 2 ^ s := ⟨_, rfl⟩
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = s := ⟨_, rfl⟩
  have h4x : (4 : ℝ) ^ s = x ^ 2 := by
    rw [hxdef, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have hc3 : ((3 * 4 ^ (s + 1) : ℕ) : ℝ) = 12 * x ^ 2 := by
    push_cast
    rw [pow_succ, h4x]
    ring
  have hc1 : ((4 ^ (s + 1) : ℕ) : ℝ) = 4 * x ^ 2 := by
    push_cast
    rw [pow_succ, h4x]
    ring
  rw [hc3] at hsplit h3
  rw [hc1] at hsplit h1
  have hl2 := Real.log_two_gt_d9
  have hl2' : 0 < Real.log 2 := by linarith
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxb : 5 * σ ^ 2 + 15 * σ + 20 ≤ x := by
    rw [hxdef, hσdef]
    exact_mod_cast hpb
  have hσ10 : (10 : ℝ) ≤ σ := by rw [hσdef]; exact_mod_cast hs
  have hKr : ((P s).card : ℝ) ≤ 8 * x * (σ + 1) := by
    rw [hxdef, hσdef]
    exact_mod_cast hcon
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogx : Real.log x = σ * Real.log 2 := by
    rw [hxdef, Real.log_pow, hσdef]
  have h16 : Real.log (16 * x ^ 2) = 2 * (σ + 2) * Real.log 2 := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlogx,
      show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    push_cast
    ring
  have hL : Real.log (12 * x ^ 2) ≤ 2 * (σ + 2) * Real.log 2 := by
    rw [← h16]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hL0 : 0 ≤ Real.log (12 * x ^ 2) := Real.log_nonneg (by nlinarith)
  have hL1 : Real.log (12 * x ^ 2 + 1) ≤ 2 * (σ + 2) * Real.log 2 := by
    rw [← h16]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hsq : Real.sqrt (12 * x ^ 2) ≤ 3.47 * x := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hprod : Real.sqrt (12 * x ^ 2) * Real.log (12 * x ^ 2) ≤
      3.47 * x * (2 * (σ + 2) * Real.log 2) :=
    mul_le_mul hsq hL hL0 (by positivity)
  have hKL : ((P s).card : ℝ) * Real.log (12 * x ^ 2) ≤
      8 * x * (σ + 1) * (2 * (σ + 2) * Real.log 2) :=
    mul_le_mul hKr hL hL0 (by positivity)
  rw [hlog4] at h1
  have hmain : 4 * x ^ 2 * Real.log 2 ≤ (2 * (σ + 2) + 13.88 * x * (σ + 2) +
      16 * x * (σ + 1) * (σ + 2)) * Real.log 2 := by
    linarith
  have hmain' : 4 * x ^ 2 ≤ 2 * (σ + 2) + 13.88 * x * (σ + 2) + 16 * x * (σ + 1) * (σ + 2) :=
    le_of_mul_le_mul_right hmain hl2'
  have hxx : x * (5 * σ ^ 2 + 15 * σ + 20) ≤ x * x := mul_le_mul_of_nonneg_left hxb hx0.le
  nlinarith [mul_nonneg (mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ σ)) (by linarith : (0 : ℝ) ≤ σ - 10),
    mul_nonneg hx0.le (by linarith : (0 : ℝ) ≤ σ)]

theorem solution_aux : OMA.R_Erdos700_erdos_700_parts_ii_R1.H2 := by
  unfold OMA.R_Erdos700_erdos_700_parts_ii_R1.H2
  intro N
  have hs : 10 ≤ N + 10 := by omega
  have hcount := count_bound (N + 10) hs
  set s := N + 10 with hsdef
  set M := 4 ^ (s + 1) with hMdef
  set W := 2 ^ s with hWdef
  have hW0 : 0 < W := by positivity
  have hMW : M = 4 * W ^ 2 := by
    rw [hMdef, hWdef, pow_succ, ← pow_mul, mul_comm s 2, pow_mul]
    norm_num
    ring
  have hmaps : ∀ p ∈ P s, (fun p => (p - M - 1) / W) p ∈ Finset.range (8 * 2 ^ s) := by
    intro p hp
    simp only [P, Finset.mem_filter, Finset.mem_Ioc] at hp
    simp only [Finset.mem_range]
    rw [Nat.div_lt_iff_lt_mul hW0]
    have : 8 * 2 ^ s * W = 2 * M := by rw [hMW, hWdef]; ring
    rw [this]
    omega
  obtain ⟨y, -, hfib⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps
    (by rw [Finset.card_range]; exact hcount)
  set S := (P s).filter (fun p => (p - M - 1) / W = y) with hSdef
  have hScard : s + 1 < S.card := hfib
  have hSmem : ∀ x ∈ S, x.Prime ∧ M < x ∧ M + 1 + y * W ≤ x ∧ x ≤ M + 1 + y * W + (W - 1) := by
    intro x hx
    simp only [hSdef, P, Finset.mem_filter, Finset.mem_Ioc] at hx
    obtain ⟨⟨⟨hx1, hx2⟩, hxp⟩, hxy⟩ := hx
    have hdm := Nat.div_add_mod (x - M - 1) W
    have hml := Nat.mod_lt (x - M - 1) hW0
    rw [hxy] at hdm
    have hc : y * W = W * y := mul_comm _ _
    refine ⟨hxp, hx1, by omega, by omega⟩
  have key : ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a < b ∧ b < c ∧ b - a < c - b := by
    by_contra h
    push Not at h
    obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (show s + 2 ≤ S.card by omega)
    have := spread s T (M + 1 + y * W) (M + 1 + y * W + (W - 1)) hTc
      (fun x hx => ⟨(hSmem x (hTS hx)).2.2.1, (hSmem x (hTS hx)).2.2.2⟩)
      (fun a ha b hb c hc hab hbc => h a (hTS ha) b (hTS hb) c (hTS hc) hab hbc)
    rw [← hWdef] at this
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hgap⟩ := key
  obtain ⟨hap, haM, hal, hau⟩ := hSmem a ha
  obtain ⟨hbp, -, -, -⟩ := hSmem b hb
  obtain ⟨hcp, -, hcl, hcu⟩ := hSmem c hc
  have hNM : N < M := by
    have h1 : N < 4 ^ N := Nat.lt_pow_self (by norm_num)
    have h2 : 4 ^ N ≤ 4 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hca : c - a < W := by omega
  have hsq : (c - a) ^ 2 < W ^ 2 := Nat.pow_lt_pow_left hca (by norm_num)
  refine ⟨a, b, c, by omega, hap, hbp, hcp, hab, hbc, hgap, ?_⟩
  rw [hMW] at haM
  omega

end OMA.E700H2

theorem OMA.solution : OMA.R_Erdos700_erdos_700_parts_ii_R1.H2 := OMA.E700H2.solution_aux
