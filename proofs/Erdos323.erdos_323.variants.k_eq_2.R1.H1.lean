import OMAReductions.R_Erdos323_erdos_323_variants_k_eq_2_R1
import Mathlib

-- Step Erdos323.erdos_323.variants.k_eq_2.R1.H1: hypothesis H1 of reduction Erdos323.erdos_323.variants.k_eq_2.R1
-- Credit: @Genbox

/-!
# OMAMeanValue: mean values of {0,1}-like multiplicative functions (Wirsing-lite)

Elementary route (Tenenbaum III.3 / Wirsing ideas, own formalization):
* `rearr` : Dirichlet-hyperbola rearrangement of divisor sums.
* `abel`  : discrete Abel summation.
* Part Q  : for completely multiplicative `0 ≤ g ≤ 1` with `∑_{n≤N} g Λ ~ τ N` and
  `∑_{n≤N} g Λ / n = τ log N + O(1)`, the count `∑_{n≤N} g n ~ c N (log N)^(τ-1)`.
-/

open Finset Real Filter Topology ArithmeticFunction
open scoped Asymptotics

namespace OMAMeanValue

/-! ## Basic summation tools -/

theorem rearr (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, F d (n / d) =
      ∑ d ∈ Ioc 0 N, ∑ m ∈ Ioc 0 (N / d), F d m := by
  rw [Finset.sum_comm' (t' := Ioc 0 N) (s' := fun d => (Ioc 0 N).filter (d ∣ ·))]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd0 : 0 < d := by simp only [mem_Ioc] at hd; omega
    symm
    apply Finset.sum_nbij' (fun m => d * m) (fun n => n / d)
    · intro m hm
      simp only [mem_Ioc, mem_filter] at hm ⊢
      refine ⟨⟨Nat.mul_pos hd0 hm.1, ?_⟩, dvd_mul_right _ _⟩
      have := (Nat.le_div_iff_mul_le hd0).1 hm.2
      linarith [Nat.mul_comm m d]
    · intro n hn
      simp only [mem_Ioc, mem_filter] at hn ⊢
      obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
      rw [Nat.mul_div_cancel_left _ hd0]
      refine ⟨Nat.pos_of_mul_pos_left h1 |> fun h => ?_, ?_⟩
      · rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp at h1
        · exact hk
      · rw [Nat.le_div_iff_mul_le hd0]; linarith [Nat.mul_comm k d]
    · intro m _
      simp only [Nat.mul_div_cancel_left _ hd0]
    · intro n hn
      simp only [mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      simp only [Nat.mul_div_cancel_left _ hd0]
  · intro n d
    simp only [mem_Ioc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, _⟩
      exact ⟨⟨⟨h1, h2⟩, h3⟩, Nat.pos_of_dvd_of_pos h3 h1, (Nat.le_of_dvd h1 h3).trans h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, _, _⟩
      exact ⟨⟨h1, h2⟩, h3, by omega⟩

/-- Rearrangement with the cofactor as the outer variable. -/
theorem rearr' (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, F d (n / d) =
      ∑ m ∈ Ioc 0 N, ∑ d ∈ Ioc 0 (N / m), F d m := by
  have h : ∀ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, F d (n / d) =
      ∑ e ∈ n.divisors, (fun e k => F k e) e (n / e) := by
    intro n _
    rw [← Nat.sum_div_divisors n (fun e => F e (n / e))]
    apply Finset.sum_congr rfl
    intro e he
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) (Nat.ne_of_gt (Nat.pos_of_mem_divisors
      (by simpa using he) |> fun _ => by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · simp [h0] at he
        · exact h0))]
  rw [Finset.sum_congr rfl h, rearr N (fun e k => F k e)]

/-- Discrete Abel summation. -/
theorem abel (c w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, c n * w n =
      (∑ k ∈ Ioc 0 N, c k) * w N +
        ∑ n ∈ Ioc 0 (N - 1), (∑ k ∈ Ioc 0 n, c k) * (w n - w (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih, Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    · have : N + 1 - 1 = (N - 1) + 1 := by omega
      rw [this, Finset.sum_Ioc_succ_top (Nat.zero_le _), Nat.sub_add_cancel h0]
      ring

theorem sum_log_div_le (N : ℕ) : ∑ n ∈ Ioc 0 N, Real.log ((N : ℝ) / n) ≤ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    have hN : (0 : ℝ) < N := by exact_mod_cast h0
    have key : ∀ n ∈ Ioc 0 N, Real.log (((N + 1 : ℕ) : ℝ) / n) =
        Real.log ((N : ℝ) / n) + Real.log (((N : ℝ) + 1) / N) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by
        simp only [mem_Ioc] at hn; exact_mod_cast hn.1
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ioc,
      nsmul_eq_mul]
    have hl : Real.log (((N : ℝ) + 1) / N) ≤ 1 / N := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
      have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
      linarith
    have : ((N - 0 : ℕ) : ℝ) * Real.log (((N : ℝ) + 1) / N) ≤ 1 := by
      simp only [Nat.sub_zero]
      calc (N : ℝ) * Real.log (((N : ℝ) + 1) / N) ≤ N * (1 / N) :=
            mul_le_mul_of_nonneg_left hl hN.le
        _ = 1 := by field_simp
    simp only [Nat.cast_add, Nat.cast_one, div_self (by positivity : ((N : ℝ) + 1) ≠ 0),
      Real.log_one, add_zero]
    linarith

/-! ## Part Q: completely multiplicative weights -/

section PartQ

variable (g : ℕ → ℝ)

noncomputable def Gs (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, g n
noncomputable def Ls (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, g n / n
noncomputable def Js (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, g n / n * Real.log ((N : ℝ) / n)
noncomputable def Psig (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, g n * Λ n
noncomputable def S1 (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, g n * Λ n / n

variable {g}

theorem log_split {N n : ℕ} (hn : 0 < n) (hN : n ≤ N) :
    Real.log N = Real.log n + Real.log ((N : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hn hN)
  rw [← Real.log_mul hn'.ne' (by positivity)]
  congr 1; field_simp

theorem I2 (hmul : ∀ m n, g (m * n) = g m * g n) (N : ℕ) :
    Gs g N * Real.log N = ∑ n ∈ Ioc 0 N, g n * Real.log ((N : ℝ) / n) +
      ∑ m ∈ Ioc 0 N, g m * Psig g (N / m) := by
  have h1 : Gs g N * Real.log N = ∑ n ∈ Ioc 0 N, g n * Real.log n +
      ∑ n ∈ Ioc 0 N, g n * Real.log ((N : ℝ) / n) := by
    unfold Gs
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [mem_Ioc] at hn
    rw [log_split hn.1 hn.2]; ring
  have h2 : ∑ n ∈ Ioc 0 N, g n * Real.log n =
      ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, g d * Λ d * g (n / d) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [← vonMangoldt_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have : g n = g d * g (n / d) := by
      rw [← hmul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
    rw [this]; ring
  rw [h1, h2, rearr' N (fun d m => g d * Λ d * g m), add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  unfold Psig
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem I1 (hmul : ∀ m n, g (m * n) = g m * g n) (N : ℕ) :
    Ls g N * Real.log N = Js g N + ∑ m ∈ Ioc 0 N, g m / m * S1 g (N / m) := by
  have h1 : Ls g N * Real.log N = ∑ n ∈ Ioc 0 N, g n / n * Real.log n + Js g N := by
    unfold Ls Js
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [mem_Ioc] at hn
    rw [log_split hn.1 hn.2]; ring
  have h2 : ∑ n ∈ Ioc 0 N, g n / n * Real.log n =
      ∑ n ∈ Ioc 0 N, ∑ d ∈ n.divisors, g d * Λ d / d * (g (n / d) / ((n / d : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [mem_Ioc] at hn
    rw [← vonMangoldt_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_of_mem_divisors hd).ne'
    have : g n = g d * g (n / d) := by
      rw [← hmul, Nat.mul_div_cancel' hdn]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [this, Nat.cast_div hdn hd0]
    field_simp
  rw [h1, h2, rearr' N (fun d m => g d * Λ d / d * (g m / (m : ℝ))), add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  unfold S1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem div_cast_bounds {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    1 ≤ N / m ∧ ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m ∧ (N : ℝ) / m ≤ 2 * ((N / m : ℕ) : ℝ) := by
  have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).2 (by simpa using hmN)
  refine ⟨hq, Nat.cast_div_le, ?_⟩
  have hlt := Nat.lt_div_mul_add (a := N) hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hm']
  have : (N : ℝ) < ((N / m : ℕ) : ℝ) * m + m := by exact_mod_cast hlt
  have hq' : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast hq
  nlinarith

theorem log_div_cast_bounds {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    0 ≤ Real.log ((N : ℝ) / m) - Real.log ((N / m : ℕ) : ℝ) ∧
      Real.log ((N : ℝ) / m) - Real.log ((N / m : ℕ) : ℝ) ≤ Real.log 2 := by
  obtain ⟨hq, h1, h2⟩ := div_cast_bounds hm hmN
  have hq' : (0 : ℝ) < ((N / m : ℕ) : ℝ) := by exact_mod_cast hq
  constructor
  · linarith [Real.log_le_log hq' h1]
  · have := Real.log_le_log (lt_of_lt_of_le hq' h1) h2
    rw [Real.log_mul (by norm_num) hq'.ne'] at this
    linarith

theorem A1 (hmul : ∀ m n, g (m * n) = g m * g n) (hg0 : ∀ n, 0 ≤ g n) {τ C : ℝ} (hτ : 0 ≤ τ)
    (hS : ∀ n, 0 < n → |S1 g n - τ * Real.log n| ≤ C) (N : ℕ) :
    |Ls g N * Real.log N - (1 + τ) * Js g N| ≤ (C + τ * Real.log 2) * Ls g N := by
  have e : Ls g N * Real.log N - (1 + τ) * Js g N =
      ∑ m ∈ Ioc 0 N, g m / m * (S1 g (N / m) - τ * Real.log ((N : ℝ) / m)) := by
    rw [I1 hmul]
    unfold Js
    have : ∑ m ∈ Ioc 0 N, g m / m * (S1 g (N / m) - τ * Real.log ((N : ℝ) / m)) =
        ∑ m ∈ Ioc 0 N, g m / m * S1 g (N / m) -
          τ * ∑ m ∈ Ioc 0 N, g m / m * Real.log ((N : ℝ) / m) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this]; ring
  rw [e]
  unfold Ls
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro m hm
  simp only [mem_Ioc] at hm
  have hw : 0 ≤ g m / m := div_nonneg (hg0 m) (Nat.cast_nonneg _)
  rw [abs_mul, abs_of_nonneg hw, mul_comm (C + τ * Real.log 2)]
  apply mul_le_mul_of_nonneg_left _ hw
  obtain ⟨hl1, hl2⟩ := log_div_cast_bounds hm.1 hm.2
  have hq := (div_cast_bounds hm.1 hm.2).1
  have := hS (N / m) hq
  have e2 : S1 g (N / m) - τ * Real.log ((N : ℝ) / m) =
      (S1 g (N / m) - τ * Real.log ((N / m : ℕ) : ℝ)) -
        τ * (Real.log ((N : ℝ) / m) - Real.log ((N / m : ℕ) : ℝ)) := by ring
  rw [e2]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (mul_nonneg hτ hl1)]
  nlinarith

theorem A2 (hg0 : ∀ n, 0 ≤ g n) (N : ℕ) :
    Real.log 2 * Ls g N ≤ Js g (2 * N) - Js g N ∧
      Js g (2 * N) - Js g N ≤ Real.log 2 * Ls g (2 * N) := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp [Ls, Js]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have split : ∀ f : ℕ → ℝ, ∑ n ∈ Ioc 0 (2 * N), f n =
      ∑ n ∈ Ioc 0 N, f n + ∑ n ∈ Ioc N (2 * N), f n := fun f =>
    (Finset.sum_Ioc_consecutive f (Nat.zero_le N) (by omega)).symm
  have hJ2 : Js g (2 * N) = Real.log 2 * Ls g N + Js g N +
      ∑ n ∈ Ioc N (2 * N), g n / n * Real.log (((2 * N : ℕ) : ℝ) / n) := by
    unfold Js Ls
    rw [split, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simp only [mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    rw [show (((2 * N : ℕ) : ℝ) / n) = 2 * ((N : ℝ) / n) by push_cast; ring,
      Real.log_mul (by norm_num) (by positivity)]
    ring
  have hL2 : Ls g (2 * N) = Ls g N + ∑ n ∈ Ioc N (2 * N), g n / n := by
    unfold Ls; rw [split]
  have bnd : ∀ n ∈ Ioc N (2 * N), 0 ≤ g n / n * Real.log (((2 * N : ℕ) : ℝ) / n) ∧
      g n / n * Real.log (((2 * N : ℕ) : ℝ) / n) ≤ Real.log 2 * (g n / n) := by
    intro n hn
    simp only [mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hn.1)
    have hw : 0 ≤ g n / n := div_nonneg (hg0 n) hn0.le
    have h1 : (1 : ℝ) ≤ ((2 * N : ℕ) : ℝ) / n := by
      rw [le_div_iff₀ hn0]; exact_mod_cast (by omega : 1 * n ≤ 2 * N)
    have h2 : ((2 * N : ℕ) : ℝ) / n ≤ 2 := by
      rw [div_le_iff₀ hn0]; push_cast
      have : (N : ℝ) < n := by exact_mod_cast hn.1
      linarith
    constructor
    · exact mul_nonneg hw (Real.log_nonneg h1)
    · rw [mul_comm (Real.log 2)]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) h2) hw
  have s1 := Finset.sum_nonneg (fun n hn => (bnd n hn).1)
  have s2 := Finset.sum_le_sum (fun n hn => (bnd n hn).2)
  rw [← Finset.mul_sum] at s2
  constructor
  · rw [hJ2]; linarith
  · rw [hJ2, hL2]; nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

end PartQ

/-! ## The discrete ODE lemma -/

theorem ode_lower (x c σ : ℝ) (hx : 1 ≤ x) (hc : 0 ≤ c) (hσ : 0 < σ) :
    -(2 * σ * (c + σ)) / x ^ 2 ≤ σ / (x + c + σ) - σ / x := by
  have hx0 : 0 < x := by linarith
  have e : σ / (x + c + σ) - σ / x = -(σ * (c + σ)) / (x * (x + c + σ)) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ σ * (c + σ) := by positivity
  nlinarith [mul_nonneg this (mul_nonneg hx0.le (by linarith : 0 ≤ x + c + σ)),
    mul_nonneg this (mul_nonneg hx0.le hx0.le), mul_nonneg this (mul_nonneg hx0.le hc),
    mul_nonneg this (mul_nonneg hx0.le hσ.le)]

theorem ode_upper (x c σ : ℝ) (hx : 1 ≤ x) (hc : 0 ≤ c) (hσ : 0 < σ)
    (hk : 2 * (c + σ) ≤ x + 1) :
    σ / (x + 1 - c - σ) - σ / (x + 1) ≤ 2 * σ * (c + σ) / x ^ 2 := by
  have hp : 0 < x + 1 - c - σ := by linarith
  have e : σ / (x + 1 - c - σ) - σ / (x + 1) = σ * (c + σ) / ((x + 1 - c - σ) * (x + 1)) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (x + 1) / 2 ≤ x + 1 - c - σ := by linarith
  have h2 : x ^ 2 ≤ (x + 1 - c - σ) * (x + 1) * 2 := by nlinarith
  have : 0 ≤ σ * (c + σ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 this]

theorem log_succ_div_bounds (k : ℕ) (hk : 1 ≤ k) :
    1 / ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) - Real.log k ∧
      Real.log ((k : ℝ) + 1) - Real.log k ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) hk0.ne']
  constructor
  · have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((k : ℝ) + 1) / k by positivity)
    have e : 1 - (((k : ℝ) + 1) / k)⁻¹ = 1 / ((k : ℝ) + 1) := by field_simp; ring
    linarith
  · have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((k : ℝ) + 1) / k by positivity)
    have e : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
    linarith

/-- Discrete version of `u J' = σ J + O(J')`: `J(k) ~ A k^σ`. -/
theorem ode (j l : ℕ → ℝ) (σ h C : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hC : 0 ≤ C)
    (hj : ∀ k, 1 ≤ k → 0 < j k) (hl : ∀ k, 0 ≤ l k)
    (hE : ∀ k, 1 ≤ k → |l k * (k * h) - σ * j k| ≤ C * l k)
    (hD : ∀ k, 1 ≤ k → h * l k ≤ j (k + 1) - j k ∧ j (k + 1) - j k ≤ h * l (k + 1)) :
    ∃ A : ℝ, Tendsto (fun k : ℕ => Real.log (j k) - σ * Real.log k) atTop (𝓝 A) := by
  set c := C / h with hc
  have hc0 : 0 ≤ c := div_nonneg hC hh.le
  set K := 2 * σ * (c + σ) with hK
  obtain ⟨k0, hk0⟩ := exists_nat_ge (2 * (c + σ) + 1)
  have hk01 : 1 ≤ k0 := by
    have : (1 : ℝ) ≤ k0 := by linarith [show 0 ≤ 2 * (c + σ) by positivity]
    exact_mod_cast this
  set a : ℕ → ℝ := fun k => Real.log (j k) - σ * Real.log k with ha
  have step : ∀ k, k0 ≤ k → |a (k + 1) - a k| ≤ K / (k : ℝ) ^ 2 := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans hk01 hk
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkr0 : (k0 : ℝ) ≤ k := by exact_mod_cast hk
    have hjk := hj k hk1
    have hjk1 := hj (k + 1) (by omega)
    obtain ⟨hD1, hD2⟩ := hD k hk1
    have hE0 := abs_le.1 (hE k hk1)
    have hE1 := abs_le.1 (hE (k + 1) (by omega))
    push_cast at hE1
    obtain ⟨lb, ub⟩ := log_succ_div_bounds k hk1
    have eA : a (k + 1) - a k = Real.log (j (k + 1) / j k) -
        σ * (Real.log ((k : ℝ) + 1) - Real.log k) := by
      simp only [ha]; push_cast
      rw [Real.log_div hjk1.ne' hjk.ne']; ring
    rw [eA, abs_le]
    constructor
    · -- lower bound
      have hlk : σ * j k ≤ l k * (k * h + C) := by nlinarith
      have hratio : 1 + σ / (k + c) ≤ j (k + 1) / j k := by
        rw [le_div_iff₀ hjk]
        have hkc : 0 < (k : ℝ) + c := by linarith
        have : σ / (k + c) * j k ≤ h * l k := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hkc]
          have : h * l k * (k + c) = l k * (k * h + C) := by
            rw [hc]; field_simp
          rw [this]; linarith
        nlinarith
      have hpos : 0 < 1 + σ / (k + c) := by positivity
      have hlog := Real.one_sub_inv_le_log_of_pos hpos
      have hlog2 := Real.log_le_log hpos hratio
      have e1 : 1 - (1 + σ / (k + c))⁻¹ = σ / (k + c + σ) := by
        field_simp; ring
      have := ode_lower k c σ hkr hc0 hσ
      have hmul : σ * (Real.log ((k : ℝ) + 1) - Real.log k) ≤ σ / k := by
        have := mul_le_mul_of_nonneg_left ub hσ.le
        rwa [mul_one_div] at this
      rw [hK, ← neg_div]
      linarith
    · -- upper bound
      have hpos : 0 < (k : ℝ) + 1 - c - σ := by linarith
      have hl1 : l (k + 1) * (((k : ℝ) + 1) * h - C) ≤ σ * j (k + 1) := by nlinarith
      have hratio : j (k + 1) / j k ≤ ((k : ℝ) + 1 - c) / ((k : ℝ) + 1 - c - σ) := by
        rw [div_le_div_iff₀ hjk hpos]
        have hkc : 0 < (k : ℝ) + 1 - c := by linarith
        have : h * l (k + 1) * ((k : ℝ) + 1 - c) ≤ σ * j (k + 1) := by
          have e : h * l (k + 1) * ((k : ℝ) + 1 - c) = l (k + 1) * (((k : ℝ) + 1) * h - C) := by
            rw [hc]; field_simp
          rw [e]; exact hl1
        nlinarith
      have hlog := Real.log_le_sub_one_of_pos (show 0 < ((k : ℝ) + 1 - c) / ((k : ℝ) + 1 - c - σ)
        by apply div_pos <;> linarith)
      have hlog2 := Real.log_le_log (div_pos hjk1 hjk) hratio
      have e1 : ((k : ℝ) + 1 - c) / ((k : ℝ) + 1 - c - σ) - 1 = σ / ((k : ℝ) + 1 - c - σ) := by
        field_simp; ring
      have := ode_upper k c σ hkr hc0 hσ (by linarith)
      have hmul : σ / ((k : ℝ) + 1) ≤ σ * (Real.log ((k : ℝ) + 1) - Real.log k) := by
        have := mul_le_mul_of_nonneg_left lb hσ.le
        rwa [mul_one_div] at this
      rw [hK]
      linarith
  -- Cauchy
  have hsum : Summable (fun n : ℕ => K / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))
    have := this.mul_left K
    refine this.congr (fun n => ?_)
    push_cast; ring
  have hcs : CauchySeq (fun n => a (n + k0)) := by
    apply cauchySeq_of_dist_le_of_summable _ _ hsum
    intro n
    rw [Real.dist_eq, abs_sub_comm]
    have := step (n + k0) (by omega)
    rw [show n + k0 + 1 = n.succ + k0 by omega] at this
    refine this.trans ?_
    have hK0 : 0 ≤ K := by positivity
    apply div_le_div_of_nonneg_left hK0 (by positivity)
    have : (n : ℝ) + 1 ≤ ((n + k0 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : n + 1 ≤ n + k0)
    nlinarith
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete hcs
  exact ⟨A, (tendsto_add_atTop_iff_nat k0).1 hA⟩


theorem ode2 (j l : ℕ → ℝ) (σ h C : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hC : 0 ≤ C)
    (hj : ∀ k, 1 ≤ k → 0 < j k) (hl : ∀ k, 0 ≤ l k)
    (hE : ∀ k, 1 ≤ k → |l k * (k * h) - σ * j k| ≤ C * l k)
    (hD : ∀ k, 1 ≤ k → h * l k ≤ j (k + 1) - j k ∧ j (k + 1) - j k ≤ h * l (k + 1)) :
    ∃ lam : ℝ, 0 < lam ∧ Tendsto (fun k : ℕ => l k / (k : ℝ) ^ (σ - 1)) atTop (𝓝 lam) := by
  obtain ⟨A, hA⟩ := ode j l σ h C hσ hh hC hj hl hE hD
  have hJ : Tendsto (fun k : ℕ => j k / (k : ℝ) ^ σ) atTop (𝓝 (Real.exp A)) := by
    refine (Real.continuous_exp.tendsto A).comp hA |>.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [Function.comp]
    rw [Real.exp_sub, Real.exp_log (hj k hk), Real.rpow_def_of_pos hk0, mul_comm]
  have hlo : Tendsto (fun k : ℕ => σ / (h + C / k)) atTop (𝓝 (σ / h)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat C).const_add h
    rw [add_zero] at this
    exact (tendsto_const_nhds (x := σ)).div this hh.ne'
  have hhi : Tendsto (fun k : ℕ => σ / (h - C / k)) atTop (𝓝 (σ / h)) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat C).const_sub h
    rw [sub_zero] at this
    exact (tendsto_const_nhds (x := σ)).div this hh.ne'
  have hR : Tendsto (fun k : ℕ => l k * k / j k) atTop (𝓝 (σ / h)) := by
    obtain ⟨k1, hk1⟩ := exists_nat_gt (C / h)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [eventually_ge_atTop 1] with k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hjk := hj k hk
      have hE0 := abs_le.1 (hE k hk)
      have e : σ / (h + C / k) = σ * k / (k * h + C) := by field_simp
      rw [e, div_le_div_iff₀ (by positivity) hjk]
      nlinarith
    · filter_upwards [eventually_ge_atTop (max 1 k1)] with k hk
      have hk' : 1 ≤ k := le_trans (le_max_left _ _) hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk'
      have hkk : (k1 : ℝ) ≤ k := by exact_mod_cast le_trans (le_max_right _ _) hk
      have hpos : 0 < (k : ℝ) * h - C := by
        have := (div_lt_iff₀ hh).1 (lt_of_lt_of_le hk1 hkk)
        linarith
      have hjk := hj k hk'
      have hE0 := abs_le.1 (hE k hk')
      have e : σ / (h - C / k) = σ * k / (k * h - C) := by
        have : h - C / k = (k * h - C) / k := by field_simp
        rw [this]; field_simp
      rw [e, div_le_div_iff₀ hjk hpos]
      nlinarith
  refine ⟨Real.exp A * (σ / h), by positivity, (hJ.mul hR).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hjk := hj k hk
  rw [Real.rpow_sub_one hk0.ne']
  have : (0 : ℝ) < (k : ℝ) ^ σ := Real.rpow_pos_of_pos hk0 σ
  field_simp

theorem tendsto_nat_log_two : Tendsto (Nat.log 2) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨2 ^ b, fun _ hN => Nat.le_log_of_pow_le (by norm_num) hN⟩

theorem interp (F : ℕ → ℝ) (hF : Monotone F) (hF0 : ∀ n, 0 ≤ F n) (τ lam : ℝ) (hτ : 0 < τ)
    (hlim : Tendsto (fun k : ℕ => F (2 ^ k) / (k : ℝ) ^ τ) atTop (𝓝 lam)) :
    Tendsto (fun N : ℕ => F N / (Real.log N) ^ τ) atTop (𝓝 (lam / (Real.log 2) ^ τ)) := by
  set h := Real.log 2 with hhdef
  have hh : 0 < h := Real.log_pos (by norm_num)
  have hhτ : 0 < h ^ τ := Real.rpow_pos_of_pos hh τ
  have hratio : Tendsto (fun k : ℕ => (((k : ℝ) + 1) / k) ^ τ) atTop (𝓝 1) := by
    have : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / k) atTop (𝓝 1) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_add 1
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp
    simpa using this.rpow_const (Or.inl one_ne_zero)
  have hratio' : Tendsto (fun k : ℕ => ((k : ℝ) / (k + 1)) ^ τ) atTop (𝓝 1) := by
    have := hratio.inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    rw [← Real.inv_rpow (by positivity), inv_div]
  have hlim1 : Tendsto (fun k : ℕ => F (2 ^ (k + 1)) / ((k : ℝ) + 1) ^ τ) atTop (𝓝 lam) := by
    have := (tendsto_add_atTop_iff_nat 1).2 hlim
    simpa using this
  set U : ℕ → ℝ := fun k => F (2 ^ (k + 1)) / ((k : ℝ) * h) ^ τ with hU
  set W : ℕ → ℝ := fun k => F (2 ^ k) / (((k : ℝ) + 1) * h) ^ τ with hW
  have hUlim : Tendsto U atTop (𝓝 (lam / h ^ τ)) := by
    have := (hlim1.mul hratio).div_const (h ^ τ)
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [hU]
    rw [Real.mul_rpow hk0.le hh.le, Real.div_rpow (by positivity) hk0.le]
    have : (0 : ℝ) < (k : ℝ) ^ τ := Real.rpow_pos_of_pos hk0 τ
    have : (0 : ℝ) < ((k : ℝ) + 1) ^ τ := Real.rpow_pos_of_pos (by positivity) τ
    field_simp
  have hWlim : Tendsto W atTop (𝓝 (lam / h ^ τ)) := by
    have := (hlim.mul hratio').div_const (h ^ τ)
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    simp only [hW]
    rw [Real.mul_rpow (by positivity) hh.le, Real.div_rpow hk0.le (by positivity)]
    have : (0 : ℝ) < (k : ℝ) ^ τ := Real.rpow_pos_of_pos hk0 τ
    have : (0 : ℝ) < ((k : ℝ) + 1) ^ τ := Real.rpow_pos_of_pos (by positivity) τ
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hWlim.comp tendsto_nat_log_two)
    (hUlim.comp tendsto_nat_log_two)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    set k := Nat.log 2 N
    have h1 : 2 ^ k ≤ N := Nat.pow_log_le_self 2 (by omega)
    have h2 : N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlogN : Real.log N ≤ ((k : ℝ) + 1) * h := by
      have : (N : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast h2.le
      have := Real.log_le_log hN0 this
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    simp only [Function.comp, hW]
    apply div_le_div₀ (hF0 _) (hF h1) (Real.rpow_pos_of_pos hlogpos τ)
    exact Real.rpow_le_rpow hlogpos.le hlogN hτ.le
  · filter_upwards [eventually_ge_atTop 2] with N hN
    set k := Nat.log 2 N
    have hk1 : 1 ≤ k := Nat.le_log_of_pow_le (by norm_num) (by simpa using hN)
    have h1 : 2 ^ k ≤ N := Nat.pow_log_le_self 2 (by omega)
    have h2 : N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hlogN : (k : ℝ) * h ≤ Real.log N := by
      have : (2 : ℝ) ^ k ≤ (N : ℝ) := by exact_mod_cast h1
      have := Real.log_le_log (by positivity) this
      rw [Real.log_pow] at this; linarith
    simp only [Function.comp, hU]
    apply div_le_div₀ (hF0 _) (hF h2.le) (Real.rpow_pos_of_pos (by positivity) τ)
    exact Real.rpow_le_rpow (by positivity) hlogN hτ.le

section PartQ2

variable {g : ℕ → ℝ}

theorem Ls_nonneg (hg0 : ∀ n, 0 ≤ g n) (N : ℕ) : 0 ≤ Ls g N :=
  Finset.sum_nonneg fun n _ => div_nonneg (hg0 n) (Nat.cast_nonneg _)

theorem Ls_mono (hg0 : ∀ n, 0 ≤ g n) : Monotone (Ls g) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hab)
    (fun n _ _ => div_nonneg (hg0 n) (Nat.cast_nonneg _))

theorem Js_pos (hg0 : ∀ n, 0 ≤ g n) (hg1 : g 1 = 1) {N : ℕ} (hN : 2 ≤ N) : 0 < Js g N := by
  have hmem : 1 ∈ Ioc 0 N := by simp; omega
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun n => g n / n * Real.log ((N : ℝ) / n))
    ?_ hmem)
  · simp only [hg1, Nat.cast_one, div_one, one_mul]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  · intro n hn
    simp only [mem_Ioc] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
    apply mul_nonneg (div_nonneg (hg0 n) hn0.le)
    apply Real.log_nonneg
    rw [le_div_iff₀ hn0, one_mul]; exact_mod_cast hn.2

/-- Mean value of `g / n`: `∑_{n≤N} g n / n ~ λ (log N)^τ`. -/
theorem L_asymp (hmul : ∀ m n, g (m * n) = g m * g n) (hg0 : ∀ n, 0 ≤ g n) (hg1 : g 1 = 1)
    {τ C : ℝ} (hτ : 0 < τ) (hS : ∀ n, 0 < n → |S1 g n - τ * Real.log n| ≤ C) :
    ∃ lam : ℝ, 0 < lam ∧ Tendsto (fun N : ℕ => Ls g N / (Real.log N) ^ τ) atTop (𝓝 lam) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hS 1 one_pos)
  set h := Real.log 2 with hhdef
  have hh : 0 < h := Real.log_pos (by norm_num)
  obtain ⟨lam1, hlam1, hlim⟩ := ode2 (fun k => Js g (2 ^ k)) (fun k => Ls g (2 ^ k)) (1 + τ) h
    (C + τ * h) (by linarith) hh (by positivity)
    (fun k hk => Js_pos hg0 hg1 (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk))
    (fun k => Ls_nonneg hg0 _)
    (fun k _ => by
      have := A1 hmul hg0 hτ.le hS (2 ^ k)
      simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at this
      convert this using 2)
    (fun k _ => by
      have := A2 hg0 (2 ^ k)
      rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring] at this
      exact this)
  rw [show 1 + τ - 1 = τ by ring] at hlim
  exact ⟨lam1 / h ^ τ, div_pos hlam1 (Real.rpow_pos_of_pos hh τ),
    interp (Ls g) (Ls_mono hg0) (Ls_nonneg hg0) τ lam1 hτ hlim⟩

theorem Psig_mono (hg0 : ∀ n, 0 ≤ g n) : Monotone (Psig g) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right hab)
    (fun n _ _ => mul_nonneg (hg0 n) vonMangoldt_nonneg)

theorem Psig_nonneg (hg0 : ∀ n, 0 ≤ g n) (N : ℕ) : 0 ≤ Psig g N :=
  Finset.sum_nonneg fun n _ => mul_nonneg (hg0 n) vonMangoldt_nonneg

theorem Gs_le (hg1 : ∀ n, g n ≤ 1) (N : ℕ) : Gs g N ≤ N := by
  unfold Gs
  calc ∑ n ∈ Ioc 0 N, g n ≤ ∑ n ∈ Ioc 0 N, (1 : ℝ) := Finset.sum_le_sum fun n _ => hg1 n
    _ = N := by simp

/-- Key error bound behind `G(N) log N ≈ τ N L(N)`. -/
theorem G_bound (hmul : ∀ m n, g (m * n) = g m * g n) (hg0 : ∀ n, 0 ≤ g n)
    (hg1 : ∀ n, g n ≤ 1) {τ ε B0 : ℝ} {Y : ℕ} (hτ : 0 ≤ τ) (hε : 0 ≤ ε)
    (hY : ∀ q, Y ≤ q → |Psig g q - τ * q| ≤ ε * q) (hB : ∀ q, q ≤ Y → |Psig g q - τ * q| ≤ B0)
    (N : ℕ) :
    |Gs g N * Real.log N - τ * N * Ls g N| ≤ N + ε * N * Ls g N + (B0 + τ) * N := by
  rw [I2 hmul]
  have e : τ * N * Ls g N = ∑ m ∈ Ioc 0 N, g m * (τ * ((N : ℝ) / m)) := by
    unfold Ls; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
  rw [e, add_sub_assoc, ← Finset.sum_sub_distrib]
  have h1 : 0 ≤ ∑ n ∈ Ioc 0 N, g n * Real.log ((N : ℝ) / n) ∧
      ∑ n ∈ Ioc 0 N, g n * Real.log ((N : ℝ) / n) ≤ N := by
    have hl : ∀ n ∈ Ioc 0 N, 0 ≤ Real.log ((N : ℝ) / n) := by
      intro n hn; simp only [mem_Ioc] at hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.1
      apply Real.log_nonneg; rw [le_div_iff₀ hn0, one_mul]; exact_mod_cast hn.2
    constructor
    · exact Finset.sum_nonneg fun n hn => mul_nonneg (hg0 n) (hl n hn)
    · refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_log_div_le N)
      calc g n * Real.log ((N : ℝ) / n) ≤ 1 * Real.log ((N : ℝ) / n) :=
            mul_le_mul_of_nonneg_right (hg1 n) (hl n hn)
        _ = _ := one_mul _
  have hB0 : 0 ≤ B0 := le_trans (abs_nonneg _) (hB 0 (Nat.zero_le _))
  have h2 : |∑ m ∈ Ioc 0 N, (g m * Psig g (N / m) - g m * (τ * ((N : ℝ) / m)))| ≤
      ε * N * Ls g N + (B0 + τ) * N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsum : ∑ m ∈ Ioc 0 N, g m * (ε * ((N : ℝ) / m) + (B0 + τ)) ≤
        ε * N * Ls g N + (B0 + τ) * N := by
      have : ∑ m ∈ Ioc 0 N, g m * (ε * ((N : ℝ) / m) + (B0 + τ)) =
          ε * N * Ls g N + (B0 + τ) * Gs g N := by
        unfold Ls Gs
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro m _; ring
      rw [this]
      nlinarith [Gs_le hg1 N]
    refine le_trans (Finset.sum_le_sum fun m hm => ?_) hsum
    simp only [mem_Ioc] at hm
    obtain ⟨hq, hq1, hq2⟩ := div_cast_bounds hm.1 hm.2
    set q := N / m
    rw [← mul_sub, abs_mul, abs_of_nonneg (hg0 m)]
    apply mul_le_mul_of_nonneg_left _ (hg0 m)
    have hfrac : (N : ℝ) / m - q ≤ 1 := by
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm.1
      have hlt := Nat.lt_div_mul_add (a := N) hm.1
      have : (N : ℝ) < (q : ℝ) * m + m := by exact_mod_cast hlt
      rw [div_sub' hm'.ne', div_le_iff₀ hm']; linarith
    have e2 : Psig g q - τ * ((N : ℝ) / m) = (Psig g q - τ * q) - τ * ((N : ℝ) / m - q) := by ring
    rw [e2]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (mul_nonneg hτ (by linarith))]
    have hmain : |Psig g q - τ * q| ≤ ε * ((N : ℝ) / m) + B0 := by
      rcases le_total Y q with hYq | hqY
      · have := hY q hYq
        have : ε * (q : ℝ) ≤ ε * ((N : ℝ) / m) := mul_le_mul_of_nonneg_left hq1 hε
        linarith
      · have := hB q hqY
        have : 0 ≤ ε * ((N : ℝ) / m) := by positivity
        linarith
    nlinarith
  have := abs_add_le (∑ n ∈ Ioc 0 N, g n * Real.log ((N : ℝ) / n))
    (∑ m ∈ Ioc 0 N, (g m * Psig g (N / m) - g m * (τ * ((N : ℝ) / m))))
  rw [abs_of_nonneg h1.1] at this
  linarith [h1.2]

/-- Wirsing-lite: `∑_{n≤N} g n ~ τ λ N (log N)^(τ-1)`. -/
theorem G_asymp (hmul : ∀ m n, g (m * n) = g m * g n) (hg0 : ∀ n, 0 ≤ g n)
    (hg1 : ∀ n, g n ≤ 1) {τ lam : ℝ} (hτ : 0 < τ) (hlam : 0 < lam)
    (hpsi : Tendsto (fun N : ℕ => Psig g N / N) atTop (𝓝 τ))
    (hL : Tendsto (fun N : ℕ => Ls g N / (Real.log N) ^ τ) atTop (𝓝 lam)) :
    Tendsto (fun N : ℕ => Gs g N / (N * (Real.log N) ^ (τ - 1))) atTop (𝓝 (τ * lam)) := by
  have hlog : Tendsto (fun N : ℕ => (Real.log N) ^ τ) atTop atTop :=
    (tendsto_rpow_atTop hτ).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hLinf : Tendsto (fun N : ℕ => Ls g N) atTop atTop := by
    refine (hL.pos_mul_atTop hlam hlog).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have := Real.rpow_pos_of_pos this τ
    field_simp
  have hQ : Tendsto (fun N : ℕ => Gs g N * Real.log N / (N * Ls g N)) atTop (𝓝 τ) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨Y, hY⟩ := (Metric.tendsto_atTop.1 hpsi) (ε / 3) (by positivity)
    have hY' : ∀ q, Y ≤ q → |Psig g q - τ * q| ≤ ε / 3 * q := by
      intro q hq
      rcases Nat.eq_zero_or_pos q with h0 | hq0
      · subst h0; simp [Psig]
      have hq' : (0 : ℝ) < q := by exact_mod_cast hq0
      have := hY q hq
      rw [Real.dist_eq] at this
      have e : Psig g q - τ * q = (Psig g q / q - τ) * q := by field_simp
      rw [e, abs_mul, abs_of_pos hq']
      exact mul_le_mul_of_nonneg_right this.le hq'.le
    set B0 := Psig g Y + τ * Y
    have hB : ∀ q, q ≤ Y → |Psig g q - τ * q| ≤ B0 := by
      intro q hq
      have h1 := Psig_nonneg hg0 q
      have h2 := Psig_mono hg0 hq
      have h3 : (q : ℝ) ≤ Y := by exact_mod_cast hq
      have h4 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
      rw [abs_le]; constructor <;> nlinarith
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.1 ((tendsto_atTop.1 hLinf) (3 * (1 + B0 + τ) / ε + 1))
    refine ⟨max N1 1, fun N hN => ?_⟩
    have hN1' := hN1 N (le_trans (le_max_left _ _) hN)
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN))
    have hB0 : 0 ≤ B0 := by
      have := Psig_nonneg hg0 Y
      have : (0 : ℝ) ≤ Y := Nat.cast_nonneg _
      positivity
    have hLpos : 0 < Ls g N := by
      have : 0 < 3 * (1 + B0 + τ) / ε + 1 := by positivity
      linarith
    have hb := G_bound hmul hg0 hg1 hτ.le (by positivity : 0 ≤ ε / 3) hY' hB N
    rw [Real.dist_eq]
    have e : Gs g N * Real.log N / (N * Ls g N) - τ =
        (Gs g N * Real.log N - τ * N * Ls g N) / (N * Ls g N) := by field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < N * Ls g N),
      div_lt_iff₀ (by positivity)]
    have hk : 3 * (1 + B0 + τ) ≤ ε * Ls g N := by
      have := (div_le_iff₀ hε).1 (by linarith : 3 * (1 + B0 + τ) / ε ≤ Ls g N)
      linarith
    nlinarith
  refine (hQ.mul hL).congr' ?_
  filter_upwards [eventually_ge_atTop 2, hLinf.eventually_gt_atTop 0] with N hN hLp
  have hlogp : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [Real.rpow_sub_one hlogp.ne']
  have := Real.rpow_pos_of_pos hlogp τ
  field_simp

end PartQ2

/-! ## Part R: multiplicative sets `A` versus the completely multiplicative `g` -/

section PartR

variable (A : Set ℕ)

open Classical in
/-- Indicator of `A` on positive integers. -/
noncomputable def aI (n : ℕ) : ℝ := if n ≠ 0 ∧ n ∈ A then 1 else 0

open Classical in
/-- Completely multiplicative function: all prime factors in `A`. -/
noncomputable def gI (n : ℕ) : ℝ := if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∈ A then 1 else 0

noncomputable def aF : ArithmeticFunction ℝ := ⟨aI A, by simp [aI]⟩
noncomputable def gF : ArithmeticFunction ℝ := ⟨gI A, by simp [gI]⟩

theorem aF_apply (n : ℕ) : aF A n = aI A n := rfl
theorem gF_apply (n : ℕ) : gF A n = gI A n := rfl

variable {A}

theorem gI_key (m n : ℕ) :
    (m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, p ∈ A) ↔
      (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, p ∈ A) ∧ (n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∈ A) := by
  constructor
  · rintro ⟨h0, h⟩
    have hm : m ≠ 0 := left_ne_zero_of_mul h0
    have hn : n ≠ 0 := right_ne_zero_of_mul h0
    rw [Nat.primeFactors_mul hm hn] at h
    exact ⟨⟨hm, fun p hp => h p (Finset.mem_union_left _ hp)⟩,
      ⟨hn, fun p hp => h p (Finset.mem_union_right _ hp)⟩⟩
  · rintro ⟨⟨hm, h1⟩, ⟨hn, h2⟩⟩
    refine ⟨mul_ne_zero hm hn, ?_⟩
    rw [Nat.primeFactors_mul hm hn]
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · exact h1 p hp
    · exact h2 p hp

theorem gI_mul (m n : ℕ) : gI A (m * n) = gI A m * gI A n := by
  unfold gI
  rcases em (m ≠ 0 ∧ ∀ p ∈ m.primeFactors, p ∈ A) with h1 | h1 <;>
    rcases em (n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∈ A) with h2 | h2
  · rw [if_pos ((gI_key m n).2 ⟨h1, h2⟩), if_pos h1, if_pos h2]; ring
  · rw [if_neg (fun h => h2 ((gI_key m n).1 h).2), if_pos h1, if_neg h2]; ring
  · rw [if_neg (fun h => h1 ((gI_key m n).1 h).1), if_neg h1, if_pos h2]; ring
  · rw [if_neg (fun h => h1 ((gI_key m n).1 h).1), if_neg h1, if_neg h2]; ring

theorem gI_one : gI A 1 = 1 := by simp [gI]

theorem gI_nonneg (n : ℕ) : 0 ≤ gI A n := by unfold gI; split_ifs <;> norm_num
theorem gI_le_one (n : ℕ) : gI A n ≤ 1 := by unfold gI; split_ifs <;> norm_num
theorem aI_nonneg (n : ℕ) : 0 ≤ aI A n := by unfold aI; split_ifs <;> norm_num
theorem aI_le_one (n : ℕ) : aI A n ≤ 1 := by unfold aI; split_ifs <;> norm_num

theorem gI_prime {p : ℕ} (hp : p.Prime) : gI A p = aI A p := by
  unfold gI aI
  rw [hp.primeFactors]
  by_cases hpA : p ∈ A
  · rw [if_pos ⟨hp.ne_zero, fun q hq => by rw [Finset.mem_singleton.1 hq]; exact hpA⟩,
      if_pos ⟨hp.ne_zero, hpA⟩]
  · rw [if_neg (fun h => hpA (h.2 p (Finset.mem_singleton_self p))), if_neg (fun h => hpA h.2)]

theorem gF_mult : (gF A).IsMultiplicative :=
  ⟨by simp [gF_apply, gI_one], fun {m n} _ => by simp only [gF_apply]; exact gI_mul m n⟩

theorem aF_mult (h1 : 1 ∈ A)
    (hA : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → (m * n ∈ A ↔ m ∈ A ∧ n ∈ A)) :
    (aF A).IsMultiplicative := by
  refine ⟨by simp [aF_apply, aI, h1], fun {m n} hmn => ?_⟩
  simp only [aF_apply, aI]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have := hA m n hm hn hmn
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm.ne' hn.ne'
  by_cases h1 : m ∈ A <;> by_cases h2 : n ∈ A
  · rw [if_pos ⟨hmn0, this.2 ⟨h1, h2⟩⟩, if_pos ⟨hm.ne', h1⟩, if_pos ⟨hn.ne', h2⟩]; ring
  · rw [if_neg (fun h => h2 (this.1 h.2).2), if_pos ⟨hm.ne', h1⟩, if_neg (fun h => h2 h.2)]; ring
  · rw [if_neg (fun h => h1 (this.1 h.2).1), if_neg (fun h => h1 h.2)]; ring
  · rw [if_neg (fun h => h1 (this.1 h.2).1), if_neg (fun h => h1 h.2)]; ring

noncomputable def mugF (A : Set ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
    ArithmeticFunction ℝ) (gF A)

theorem mugF_apply (n : ℕ) :
    mugF A n = ((ArithmeticFunction.moebius n : ℤ) : ℝ) * gI A n := by
  rw [mugF, ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply, gF_apply]

theorem mugF_mult : (mugF A).IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_moebius.intCast).pmul gF_mult

/-- Value of `f * (μ·g)` at a prime power. -/
theorem conv_mug_prime_pow (f : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * mugF A) (p ^ (k + 1)) = f (p ^ (k + 1)) - f (p ^ k) * gI A p := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun x y => f x * mugF A y),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ i ∈ Finset.range k, f (p ^ (k + 1) / p ^ (i + 1 + 1)) * mugF A (p ^ (i + 1 + 1))
      = 0 := by
    intro i _
    rw [mugF_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp
  rw [Finset.sum_eq_zero hz, Nat.pow_div (by omega) hp.pos, mugF_apply, mugF_apply]
  simp only [zero_add, pow_one, pow_zero, Nat.div_one, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp, gI_one, Nat.add_sub_cancel]
  push_cast
  ring

theorem mug_mul_g : mugF A * gF A = 1 := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (mugF_mult.mul gF_mult) _ ArithmeticFunction.isMultiplicative_one).2 ?_
  intro p i hp
  rcases i with _ | k
  · simp only [pow_zero]
    rw [(mugF_mult.mul gF_mult).map_one, ArithmeticFunction.one_one]
  · rw [mul_comm, conv_mug_prime_pow (gF A) hp k, ArithmeticFunction.one_apply_ne
      (by have := Nat.one_lt_pow (by omega : k + 1 ≠ 0) hp.one_lt; omega)]
    simp only [gF_apply]
    rw [pow_succ, gI_mul]; ring

/-- The correction function `h = a * (μ g)`, so that `a = h * g`. -/
noncomputable def hF (A : Set ℕ) : ArithmeticFunction ℝ := aF A * mugF A

theorem hF_mul_g : hF A * gF A = aF A := by
  rw [hF, mul_assoc, mug_mul_g, mul_one]

theorem hF_mult (h1 : 1 ∈ A)
    (hA : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → (m * n ∈ A ↔ m ∈ A ∧ n ∈ A)) :
    (hF A).IsMultiplicative :=
  (aF_mult h1 hA).mul mugF_mult

theorem hF_prime (h1 : 1 ∈ A) {p : ℕ} (hp : p.Prime) : hF A p = 0 := by
  have := conv_mug_prime_pow (A := A) (aF A) hp 0
  simp only [zero_add, pow_one, pow_zero] at this
  rw [hF, this, aF_apply, aF_apply, gI_prime hp]
  simp [aI, h1]

theorem hF_prime_pow_abs {p : ℕ} (hp : p.Prime) (k : ℕ) : |hF A (p ^ k)| ≤ 1 := by
  rcases k with _ | k
  · simp only [pow_zero]
    rw [hF, ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton,
      mugF_apply]
    simp only [ArithmeticFunction.moebius_apply_one, gI_one, aF_apply, aI]
    split_ifs <;> norm_num
  · rw [hF, conv_mug_prime_pow (aF A) hp k, aF_apply, aF_apply]
    have := aI_nonneg (A := A) (p ^ (k + 1)); have := aI_le_one (A := A) (p ^ (k + 1))
    have := aI_nonneg (A := A) (p ^ k); have := aI_le_one (A := A) (p ^ k)
    have := gI_nonneg (A := A) p; have := gI_le_one (A := A) p
    rw [abs_le]; constructor <;> nlinarith

/-- `#A(N) = ∑_{d ≤ N} h(d) G(N/d)`. -/
theorem count_conv (N : ℕ) :
    ∑ n ∈ Ioc 0 N, aI A n = ∑ d ∈ Ioc 0 N, hF A d * Gs (gI A) (N / d) := by
  have : ∀ n ∈ Ioc 0 N, aI A n = ∑ d ∈ n.divisors, hF A d * gI A (n / d) := by
    intro n _
    rw [← aF_apply, ← hF_mul_g, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => hF A x * gF A y)]
    rfl
  rw [Finset.sum_congr rfl this, rearr N (fun d m => hF A d * gI A m)]
  apply Finset.sum_congr rfl
  intro d _
  rw [Gs, Finset.mul_sum]

end PartR

/-! ## Summability of the correction `h` (Euler product bound) -/

section PartR2

variable {A : Set ℕ}

theorem rpow_pow_swap (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (y : ℝ) : (x ^ k) ^ y = (x ^ y) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

theorem hF_summable (h1 : 1 ∈ A)
    (hA : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → (m * n ∈ A ↔ m ∈ A ∧ n ∈ A)) :
    Summable (fun d : ℕ => |hF A d| * (d : ℝ) ^ (-(3 / 4 : ℝ))) := by
  set F : ℕ → ℝ := fun d => |hF A d| * (d : ℝ) ^ (-(3 / 4 : ℝ)) with hFdef
  have hm := hF_mult h1 hA
  have hF0 : ∀ d, 0 ≤ F d := fun d => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by simp) _)
  have hF1 : F 1 = 1 := by simp [hFdef, hm.map_one]
  have hFmul : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n := by
    intro m n hmn
    simp only [hFdef, hm.map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  set r0 : ℝ := (2 : ℝ) ^ (-(3 / 4 : ℝ)) with hr0
  have hr0lt : r0 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hr0pos : 0 < r0 := Real.rpow_pos_of_pos (by norm_num) _
  have hloc : ∀ {p : ℕ}, p.Prime → ∀ k, F (p ^ k) ≤ ((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := by
    intro p hp k
    simp only [hFdef, Nat.cast_pow]
    rw [rpow_pow_swap _ (Nat.cast_nonneg _)]
    have := hF_prime_pow_abs (A := A) hp k
    have : 0 ≤ ((p : ℝ) ^ (-(3 / 4 : ℝ))) ^ k := pow_nonneg (Real.rpow_nonneg (by simp) _) _
    nlinarith
  have hr : ∀ {p : ℕ}, p.Prime → (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ r0 := by
    intro p hp
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by norm_num)
  have hsump : ∀ {p : ℕ}, p.Prime → Summable (fun n => ‖F (p ^ n)‖) := by
    intro p hp
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (Real.rpow_nonneg (Nat.cast_nonneg p) _)
        (lt_of_le_of_lt (hr hp) hr0lt))
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]
    exact hloc hp n
  set K0 := (1 - r0)⁻¹ with hK0
  have hK0pos : 0 < K0 := inv_pos.2 (by linarith)
  have hlocsum : ∀ {p : ℕ}, p.Prime → ∑' n, F (p ^ n) ≤ 1 + K0 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro p hp
    have hs : Summable (fun n => F (p ^ n)) := (hsump hp).of_norm
    have hs1 : Summable (fun n => F (p ^ (n + 1))) := (summable_nat_add_iff 1).2 hs
    have hs2 : Summable (fun n => F (p ^ (n + 1 + 1))) := (summable_nat_add_iff 1).2 hs1
    rw [hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
    simp only [pow_zero, hF1, zero_add, pow_one]
    have hFp : F p = 0 := by simp [hFdef, hF_prime h1 hp]
    rw [hFp]
    set r := (p : ℝ) ^ (-(3 / 4 : ℝ))
    have hrnn : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hrlt : r < 1 := lt_of_le_of_lt (hr hp) hr0lt
    have hgeo : Summable (fun n : ℕ => r ^ (n + 1 + 1)) :=
      (summable_geometric_of_lt_one hrnn hrlt).mul_left (r ^ 2) |>.congr (fun n => by ring)
    have hle : ∑' n, F (p ^ (n + 1 + 1)) ≤ ∑' n : ℕ, r ^ (n + 1 + 1) :=
      Summable.tsum_le_tsum (fun n => hloc hp _) hs2 hgeo
    have hval : ∑' n : ℕ, r ^ (n + 1 + 1) = r ^ 2 * (1 - r)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hrnn hrlt, ← tsum_mul_left]
      congr 1; ext n; ring
    have hr2 : r ^ 2 = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
    have hinv : (1 - r)⁻¹ ≤ K0 := by
      rw [hK0]; apply inv_anti₀ (by linarith) (by linarith [hr hp])
    have : r ^ 2 * (1 - r)⁻¹ ≤ K0 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [← hr2, mul_comm]; exact mul_le_mul_of_nonneg_right hinv (by positivity)
    linarith
  set T := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))
  have hTs : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.2 (by norm_num)
  refine summable_of_sum_range_le hF0 (c := Real.exp (K0 * T)) (fun n => ?_)
  obtain ⟨hsub, hhas⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hF1 hFmul hsump n
  have hsub' : Summable (fun m : n.smoothNumbers => F m) := hsub.of_norm
  have hind : Summable ((n.smoothNumbers : Set ℕ).indicator F) :=
    summable_subtype_iff_indicator.1 hsub'
  calc ∑ i ∈ Finset.range n, F i
      = ∑ i ∈ Finset.range n, (n.smoothNumbers : Set ℕ).indicator F i := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases Nat.eq_zero_or_pos i with h0 | hi0
        · subst h0
          have F0 : F 0 = 0 := by simp [hFdef]
          rw [Set.indicator_apply]; split_ifs <;> simp [F0]
        · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hi0 (Finset.mem_range.1 hi))]
    _ ≤ ∑' i, (n.smoothNumbers : Set ℕ).indicator F i :=
        hind.sum_le_tsum _ (fun i _ => Set.indicator_nonneg (fun j _ => hF0 j) i)
    _ = ∏ p ∈ n.primesBelow, ∑' k : ℕ, F (p ^ k) := by
        rw [← _root_.tsum_subtype, hhas.tsum_eq]
    _ ≤ ∏ p ∈ n.primesBelow, Real.exp (K0 * (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        apply Finset.prod_le_prod
        · intro p _; exact tsum_nonneg (fun k => hF0 _)
        · intro p hp
          have hpp := Nat.prime_of_mem_primesBelow hp
          refine (hlocsum hpp).trans ?_
          linarith [Real.add_one_le_exp (K0 * (p : ℝ) ^ (-(3 / 2 : ℝ)))]
    _ = Real.exp (K0 * ∑ p ∈ n.primesBelow, (p : ℝ) ^ (-(3 / 2 : ℝ))) := by
        rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp (K0 * T) := by
        apply Real.exp_le_exp.2
        apply mul_le_mul_of_nonneg_left _ hK0pos.le
        exact hTs.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

end PartR2

/-! ## Convolution with an absolutely summable weight (dominated convergence) -/

section Conv

/-- `D N = N / √(log N)`. -/
noncomputable def Dn (N : ℕ) : ℝ := (N : ℝ) / Real.sqrt (Real.log N)

theorem Dn_pos {N : ℕ} (hN : 2 ≤ N) : 0 < Dn N := by
  have h1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  exact div_pos (by linarith) (Real.sqrt_pos.2 (Real.log_pos h1))

theorem div_nat_ge {N e : ℕ} (he : 1 ≤ e) : (N : ℝ) / e - 1 ≤ ((N / e : ℕ) : ℝ) := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hlt := Nat.lt_div_mul_add (a := N) he
  have : (N : ℝ) < ((N / e : ℕ) : ℝ) * e + e := by exact_mod_cast hlt
  rw [div_sub_one he'.ne', div_le_iff₀ he']; linarith

theorem ratioD {e : ℕ} (he : 1 ≤ e) :
    Tendsto (fun N : ℕ => Dn (N / e) / Dn N) atTop (𝓝 (1 / e)) := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have T1 : Tendsto (fun N : ℕ => ((N / e : ℕ) : ℝ) / N) atTop (𝓝 (1 / e)) := by
    have hlo : Tendsto (fun N : ℕ => 1 / (e : ℝ) - 1 / N) atTop (𝓝 (1 / e)) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_sub (1 / (e : ℝ))
      simpa using this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have := div_nat_ge (N := N) he
      rw [le_div_iff₀ hN']
      have e1 : (1 / (e : ℝ) - 1 / N) * N = N / e - 1 := by field_simp
      linarith
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_iff₀ hN']
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := e)
      have e1 : 1 / (e : ℝ) * N = N / e := by ring
      linarith
  set c0 := Real.log (2 * e) with hc0
  have hc0pos : 0 ≤ c0 := Real.log_nonneg (by linarith [show (1 : ℝ) ≤ e by exact_mod_cast he])
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have T2 : Tendsto (fun N : ℕ => Real.log N / Real.log ((N / e : ℕ) : ℝ)) atTop (𝓝 1) := by
    have hup : Tendsto (fun N : ℕ => 1 / (1 - c0 / Real.log N)) atTop (𝓝 1) := by
      have h0 : Tendsto (fun N : ℕ => c0 / Real.log N) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hlogN
      have h1 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h0).inv₀ (by norm_num)
      simpa [one_div] using h1
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · filter_upwards [eventually_ge_atTop (4 * e)] with N hN
      have hM2 : 2 ≤ N / e := (Nat.le_div_iff_mul_le he).2 (by nlinarith)
      have hMpos : (1 : ℝ) < ((N / e : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < N / e)
      have hlM := Real.log_pos hMpos
      rw [le_div_iff₀ hlM, one_mul]
      apply Real.log_le_log (by linarith)
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := e)
      have : (N : ℝ) / e ≤ N := div_le_self (Nat.cast_nonneg _) (by exact_mod_cast he)
      linarith
    · filter_upwards [eventually_ge_atTop (4 * e), hlogN.eventually_gt_atTop (2 * c0)]
        with N hN hNl
      have hM2 : 2 ≤ N / e := (Nat.le_div_iff_mul_le he).2 (by nlinarith)
      have hMpos : (1 : ℝ) < ((N / e : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < N / e)
      have hlM := Real.log_pos hMpos
      have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      -- log M ≥ log N - c0
      have hMge : (N : ℝ) / (2 * e) ≤ ((N / e : ℕ) : ℝ) := by
        have := div_nat_ge (N := N) he
        have h4 : (4 * e : ℝ) ≤ N := by exact_mod_cast hN
        have : (N : ℝ) / (2 * e) = N / e - N / (2 * e) := by field_simp; ring
        have : (1 : ℝ) ≤ N / (2 * e) := by rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      have hlogM : Real.log N - c0 ≤ Real.log ((N / e : ℕ) : ℝ) := by
        have := Real.log_le_log (by positivity) hMge
        rw [Real.log_div hNr.ne' (by positivity)] at this
        linarith
      have hpos : 0 < Real.log N - c0 := by linarith
      have e1 : 1 / (1 - c0 / Real.log N) = Real.log N / (Real.log N - c0) := by
        have : 0 < Real.log N := by linarith
        field_simp
      rw [e1]
      exact div_le_div_of_nonneg_left (by linarith) hpos hlogM
  have T3 := T1.mul T2.sqrt
  rw [Real.sqrt_one, mul_one] at T3
  refine T3.congr' ?_
  filter_upwards [eventually_ge_atTop (2 * e)] with N hN
  have hM2 : 2 ≤ N / e := (Nat.le_div_iff_mul_le he).2 (by nlinarith)
  have hMpos : (1 : ℝ) < ((N / e : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < N / e)
  have hNpos : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlM := Real.log_pos hMpos
  have hlN := Real.log_pos hNpos
  unfold Dn
  rw [Real.sqrt_div' _ hlM.le]
  have := Real.sqrt_pos.2 hlM
  have := Real.sqrt_pos.2 hlN
  field_simp

theorem conv_limit (G : ℕ → ℝ) (c : ℝ) (hG0 : ∀ M, 0 ≤ G M) (hGle : ∀ M, G M ≤ M)
    (hG : Tendsto (fun M : ℕ => G M / Dn M) atTop (𝓝 c))
    (b : ℕ → ℝ) (e : ℕ → ℕ) (he : ∀ i, i ≤ e i) (hb0 : b 0 = 0)
    (hbs : Summable (fun i => |b i| * (e i : ℝ) ^ (-(3 / 4 : ℝ)))) :
    Tendsto (fun N : ℕ => (∑ i ∈ Ioc 0 N, b i * G (N / e i)) / Dn N) atTop
      (𝓝 (c * ∑' i, b i / e i)) := by
  have hGz : G 0 = 0 := le_antisymm (by simpa using hGle 0) (hG0 0)
  have hc : 0 ≤ c := ge_of_tendsto hG (Eventually.of_forall fun M =>
    div_nonneg (hG0 M) (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)))
  -- uniform bound G M ≤ K1 D M for M ≥ 2
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1 (hG.eventually (gt_mem_nhds (lt_add_one c)))
  set K1 := c + 1 + Real.sqrt (Real.log (max M0 2)) with hK1
  have hK1pos : 0 < K1 := by positivity
  have hGK : ∀ M, 2 ≤ M → G M ≤ K1 * Dn M := by
    intro M hM
    have hD := Dn_pos hM
    rcases le_total M0 M with h | h
    · have := hM0 M h
      rw [div_lt_iff₀ hD] at this
      nlinarith [Real.sqrt_nonneg (Real.log (max M0 2))]
    · have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
      have hl := Real.log_pos hM1
      have : G M ≤ Real.sqrt (Real.log M) * Dn M := by
        unfold Dn
        rw [mul_div_assoc', mul_div_cancel_left₀ _ (Real.sqrt_pos.2 hl).ne']
        exact hGle M
      refine this.trans (mul_le_mul_of_nonneg_right ?_ hD.le)
      have : Real.sqrt (Real.log M) ≤ Real.sqrt (Real.log (max M0 2)) :=
        Real.sqrt_le_sqrt (Real.log_le_log (by linarith)
          (by exact_mod_cast le_trans h (le_max_left _ _)))
      linarith
  set K := 2 * K1 + 3 with hK
  set f : ℕ → ℕ → ℝ := fun N i => b i * G (N / e i) / Dn N with hf
  have hsumeq : ∀ N, (∑ i ∈ Ioc 0 N, b i * G (N / e i)) / Dn N = ∑' i, f N i := by
    intro N
    rw [tsum_eq_sum (s := Ioc 0 N), Finset.sum_div]
    intro i hi
    simp only [mem_Ioc, not_and, not_le] at hi
    rcases Nat.eq_zero_or_pos i with h0 | hi0
    · simp [hf, h0, hb0]
    · have : N / e i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le (hi hi0) (he i))
      simp [hf, this, hGz]
  simp_rw [hsumeq]
  have hlim : ∀ i, Tendsto (fun N => f N i) atTop (𝓝 (c * (b i / e i))) := by
    intro i
    rcases Nat.eq_zero_or_pos i with h0 | hi0
    · subst h0; simp [hf, hb0]
    have he1 : 1 ≤ e i := le_trans hi0 (he i)
    have hcomp := (hG.comp (Nat.tendsto_div_const_atTop (by omega : e i ≠ 0))).mul (ratioD he1)
    have := hcomp.const_mul (b i)
    rw [show c * (b i / e i) = b i * (c * (1 / e i)) by ring]
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop (2 * e i)] with N hN
    have hM2 : 2 ≤ N / e i := (Nat.le_div_iff_mul_le he1).2 (by nlinarith)
    have := Dn_pos hM2
    simp only [hf, Function.comp]
    field_simp
  have hbound : ∀ᶠ N in atTop, ∀ i, ‖f N i‖ ≤ K * (|b i| * (e i : ℝ) ^ (-(3 / 4 : ℝ))) := by
    have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 16] with N hN i
    rcases Nat.eq_zero_or_pos i with h0 | hi0
    · subst h0; simp [hf, hb0]
    have he1 : 1 ≤ e i := le_trans hi0 (he i)
    set E := e i with hE
    have hEr : (1 : ℝ) ≤ E := by exact_mod_cast he1
    have hNr : (16 : ℝ) ≤ N := by exact_mod_cast hN
    have hDN := Dn_pos (by omega : 2 ≤ N)
    have hlN : 0 < Real.log N := Real.log_pos (by linarith)
    have hsN := Real.sqrt_pos.2 hlN
    rw [Real.norm_eq_abs, hf]
    simp only
    rw [abs_div, abs_mul, abs_of_nonneg (hG0 _), abs_of_pos hDN, mul_div_assoc]
    rw [mul_comm K, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [mul_comm ((E : ℝ) ^ (-(3 / 4 : ℝ))) K]
    have hE34 : (0 : ℝ) < (E : ℝ) ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have hEinv : (E : ℝ)⁻¹ ≤ (E : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hEr (by norm_num)
    rcases le_or_gt (E * E) N with hsmall | hbig
    · -- M = N / E is large
      have hEN : (E : ℝ) * E ≤ N := by exact_mod_cast hsmall
      have hM : (N : ℝ) / E - 1 ≤ ((N / E : ℕ) : ℝ) := div_nat_ge he1
      have hsq : (E : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
      have hsqN4 : (4 : ℝ) ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by nlinarith)
      have hNE : Real.sqrt N ≤ (N : ℝ) / E := by
        rw [le_div_iff₀ (by linarith)]
        have := Real.mul_self_sqrt (show (0 : ℝ) ≤ N by linarith)
        nlinarith [Real.sqrt_nonneg (N : ℝ)]
      have hM2 : 2 ≤ N / E := by
        have : (2 : ℝ) ≤ ((N / E : ℕ) : ℝ) := by linarith
        exact_mod_cast this
      have hMr : (N : ℝ) / (2 * E) ≤ ((N / E : ℕ) : ℝ) := by
        have : (N : ℝ) / (2 * E) = N / E - N / (2 * E) := by field_simp; ring
        have : (1 : ℝ) ≤ N / (2 * E) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        linarith
      -- log M ≥ log N / 4
      have hlogM : Real.log N / 4 ≤ Real.log ((N / E : ℕ) : ℝ) := by
        have h1 : Real.sqrt N / 2 ≤ (N : ℝ) / (2 * E) := by
          have : (N : ℝ) / (2 * E) = N / E / 2 := by field_simp
          rw [this]; linarith
        have h2 := Real.log_le_log (by positivity) (h1.trans hMr)
        rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by linarith)] at h2
        have h3 : Real.log 2 ≤ Real.log N / 4 := by
          have h16 : Real.log 16 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
          have : Real.log 16 = 4 * Real.log 2 := by
            rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
          linarith
        linarith
      have hGM := hGK (N / E) hM2
      have hMle : ((N / E : ℕ) : ℝ) ≤ (N : ℝ) / E := Nat.cast_div_le
      have hlM : 0 < Real.log ((N / E : ℕ) : ℝ) := by linarith
      have hsqrtM : Real.sqrt (Real.log N) / 2 ≤ Real.sqrt (Real.log ((N / E : ℕ) : ℝ)) := by
        have : Real.sqrt (Real.log N / 4) = Real.sqrt (Real.log N) / 2 := by
          rw [Real.sqrt_div' _ (by norm_num)]
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [← this]; exact Real.sqrt_le_sqrt hlogM
      have hDM : Dn (N / E) ≤ 2 * ((N : ℝ) / E) / Real.sqrt (Real.log N) := by
        unfold Dn
        rw [div_le_div_iff₀ (Real.sqrt_pos.2 hlM) hsN]
        have h0 : (0 : ℝ) ≤ ((N / E : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hsqrtM h0,
          mul_le_mul_of_nonneg_right hMle (Real.sqrt_nonneg (Real.log N))]
      have : G (N / E) / Dn N ≤ 2 * K1 * (E : ℝ)⁻¹ := by
        rw [div_le_iff₀ hDN]
        calc G (N / E) ≤ K1 * Dn (N / E) := hGM
          _ ≤ K1 * (2 * ((N : ℝ) / E) / Real.sqrt (Real.log N)) :=
              mul_le_mul_of_nonneg_left hDM hK1pos.le
          _ = 2 * K1 * (E : ℝ)⁻¹ * Dn N := by unfold Dn; field_simp
      calc G (N / E) / Dn N ≤ 2 * K1 * (E : ℝ)⁻¹ := this
        _ ≤ 2 * K1 * (E : ℝ) ^ (-(3 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hEinv (by positivity)
        _ ≤ K * (E : ℝ) ^ (-(3 / 4 : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ hE34.le; linarith
    · -- E large: trivial bound G ≤ M ≤ N / E
      have hEN : (N : ℝ) < E * E := by exact_mod_cast hbig
      have hGM : G (N / E) ≤ (N : ℝ) / E := (hGle _).trans Nat.cast_div_le
      set s := (E : ℝ) ^ (1 / 4 : ℝ) with hs
      have hs1 : 1 ≤ s := Real.one_le_rpow hEr (by norm_num)
      have hs4 : s ^ 4 = E := by
        rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      have hlogE : Real.log E ≤ 4 * s := by
        rw [← hs4, Real.log_pow]
        have := Real.log_le_sub_one_of_pos (show 0 < s by linarith)
        push_cast; linarith
      have hlogN' : Real.log N ≤ 2 * Real.log E := by
        have := Real.log_le_log (by linarith) hEN.le
        rw [Real.log_mul (by positivity) (by positivity)] at this
        linarith
      have hsqrt : Real.sqrt (Real.log N) ≤ 3 * s := by
        rw [Real.sqrt_le_iff]; constructor
        · linarith
        · nlinarith
      have hsE : s / E = (E : ℝ) ^ (-(3 / 4 : ℝ)) := by
        rw [hs, ← Real.rpow_sub_one (by linarith)]; norm_num
      have : G (N / E) / Dn N ≤ 3 * (E : ℝ) ^ (-(3 / 4 : ℝ)) := by
        rw [div_le_iff₀ hDN, ← hsE]
        calc G (N / E) ≤ (N : ℝ) / E := hGM
          _ = (N : ℝ) / Real.sqrt (Real.log N) * Real.sqrt (Real.log N) / E := by
              field_simp
          _ ≤ (N : ℝ) / Real.sqrt (Real.log N) * (3 * s) / E := by
              apply div_le_div_of_nonneg_right _ (by linarith)
              exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
          _ = 3 * (s / E) * Dn N := by unfold Dn; ring
      calc G (N / E) / Dn N ≤ 3 * (E : ℝ) ^ (-(3 / 4 : ℝ)) := this
        _ ≤ K * (E : ℝ) ^ (-(3 / 4 : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ hE34.le; linarith
  have := tendsto_tsum_of_dominated_convergence (hbs.mul_left K) hlim hbound
  rw [tsum_mul_left] at this
  exact this

end Conv

/-! ## Part T: the count of a multiplicative set -/

section PartT

variable {A : Set ℕ}

theorem sqfree_mem (h1 : 1 ∈ A)
    (hA : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → (m * n ∈ A ↔ m ∈ A ∧ n ∈ A)) (n : ℕ) :
    Squarefree n → n ≠ 0 → (∀ p ∈ n.primeFactors, p ∈ A) → n ∈ A := by
  induction n using Nat.recOnPrimeCoprime with
  | zero => intro _ h; exact absurd rfl h
  | prime_pow p k hp =>
    intro hsq _ hpf
    rcases k with _ | _ | k
    · simpa using h1
    · simp only [zero_add, pow_one] at hpf ⊢
      exact hpf p (Nat.mem_primeFactors.2 ⟨hp, dvd_refl p, hp.ne_zero⟩)
    · exfalso
      apply Nat.squarefree_iff_prime_squarefree.1 hsq p hp
      rw [← pow_two]
      exact pow_dvd_pow p (by omega)
  | coprime a b ha hb hab iha ihb =>
    intro hsq hne hpf
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    refine (hA a b (by omega) (by omega) hab).2 ⟨iha hsq.of_mul_left ha0 ?_, ihb hsq.of_mul_right hb0 ?_⟩
    · exact fun p hp => hpf p (Nat.primeFactors_mono (dvd_mul_right a b) hne hp)
    · exact fun p hp => hpf p (Nat.primeFactors_mono (dvd_mul_left b a) hne hp)

theorem sum_dvd_reindex (F : ℕ → ℝ) (N d : ℕ) (hd : 0 < d) :
    ∑ n ∈ Ioc 0 N, (if d ∣ n then F (n / d) else 0) = ∑ m ∈ Ioc 0 (N / d), F m := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij' (fun m => d * m) (fun n => n / d)
  · intro m hm
    simp only [mem_Ioc, mem_filter] at hm ⊢
    refine ⟨⟨Nat.mul_pos hd hm.1, ?_⟩, dvd_mul_right _ _⟩
    have := (Nat.le_div_iff_mul_le hd).1 hm.2
    linarith [Nat.mul_comm m d]
  · intro n hn
    simp only [mem_Ioc, mem_filter] at hn ⊢
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
    rw [Nat.mul_div_cancel_left _ hd]
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp at h1
      · exact hk
    · rw [Nat.le_div_iff_mul_le hd]; linarith [Nat.mul_comm k d]
  · intro m _; simp only [Nat.mul_div_cancel_left _ hd]
  · intro n hn
    simp only [mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _; simp only [Nat.mul_div_cancel_left _ hd]

theorem gI_eq_zero_or_one (n : ℕ) : gI A n = 0 ∨ gI A n = 1 := by
  unfold gI; split_ifs <;> simp

theorem G_le_A_add (h1 : 1 ∈ A)
    (hA : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → (m * n ∈ A ↔ m ∈ A ∧ n ∈ A)) (N : ℕ) :
    Gs (gI A) N ≤ ∑ n ∈ Ioc 0 N, aI A n + ∑ s ∈ Ioc 0 N, Gs (gI A) (N / (s + 1) ^ 2) := by
  have hpt : ∀ n ∈ Ioc 0 N, gI A n ≤ aI A n +
      ∑ s ∈ Ioc 0 N, (if (s + 1) ^ 2 ∣ n then gI A (n / (s + 1) ^ 2) else 0) := by
    intro n hn
    simp only [mem_Ioc] at hn
    have hsum0 : 0 ≤ ∑ s ∈ Ioc 0 N, (if (s + 1) ^ 2 ∣ n then gI A (n / (s + 1) ^ 2) else 0) :=
      Finset.sum_nonneg fun s _ => by split_ifs <;> simp [gI_nonneg]
    rcases gI_eq_zero_or_one (A := A) n with h0 | h1'
    · rw [h0]; linarith [aI_nonneg (A := A) n]
    by_cases hsq : Squarefree n
    · have hmem : n ∈ A := by
        refine sqfree_mem h1 hA n hsq (by omega) ?_
        unfold gI at h1'
        split_ifs at h1' with h
        · exact h.2
        · simp at h1'
      have : aI A n = 1 := by simp [aI, hmem, show n ≠ 0 by omega]
      rw [h1', this]; linarith
    · obtain ⟨p, hp, hpp⟩ : ∃ p, p.Prime ∧ p * p ∣ n := by
        by_contra hc
        push Not at hc
        exact hsq (Nat.squarefree_iff_prime_squarefree.2 fun p hp => hc p hp)
      have hpn : p ≤ N := le_trans (Nat.le_of_dvd hn.1 (dvd_trans (dvd_mul_right p p) hpp)) hn.2
      have hs : p - 1 ∈ Ioc 0 N := by
        simp only [mem_Ioc]; have := hp.two_le; omega
      have hsp : p - 1 + 1 = p := by have := hp.two_le; omega
      have hdvd : (p - 1 + 1) ^ 2 ∣ n := by rw [hsp, pow_two]; exact hpp
      have hg : gI A (n / (p - 1 + 1) ^ 2) = 1 := by
        have e := gI_mul (A := A) ((p - 1 + 1) ^ 2) (n / (p - 1 + 1) ^ 2)
        rw [Nat.mul_div_cancel' hdvd, h1'] at e
        rcases gI_eq_zero_or_one (A := A) (n / (p - 1 + 1) ^ 2) with h | h
        · rw [h, mul_zero] at e; norm_num at e
        · exact h
      have hle := Finset.single_le_sum (f := fun s =>
        (if (s + 1) ^ 2 ∣ n then gI A (n / (s + 1) ^ 2) else 0))
        (fun s _ => by split_ifs <;> simp [gI_nonneg]) hs
      simp only [if_pos hdvd, hg] at hle
      rw [h1']; linarith [aI_nonneg (A := A) n]
  unfold Gs
  refine (Finset.sum_le_sum hpt).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact sum_dvd_reindex (gI A) N ((s + 1) ^ 2) (by positivity)

theorem zeta_two_tail :
    HasSum (fun s : ℕ => (if s = 0 then (0 : ℝ) else 1) / (((s + 1) ^ 2 : ℕ) : ℝ))
      (Real.pi ^ 2 / 6 - 1) := by
  have h0 := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  have h1 : HasSum (fun s : ℕ => 1 / ((s : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    simpa using h0
  have h2 := h1.sub (hasSum_ite_eq 0 (1 : ℝ))
  have e : (fun s : ℕ => (if s = 0 then (0 : ℝ) else 1) / (((s + 1) ^ 2 : ℕ) : ℝ)) =
      (fun b : ℕ => 1 / ((b : ℝ) + 1) ^ 2 - if b = 0 then 1 else 0) := by
    funext s
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    · simp [hs.ne']
  rw [e]; exact h2

/-- Mean value of a multiplicative set, given the mean value of its prime-supported `g`. -/
theorem mean_value_set (h1 : 1 ∈ A)
    (hA : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → (m * n ∈ A ↔ m ∈ A ∧ n ∈ A)) {c : ℝ}
    (hc : 0 < c) (hG : Tendsto (fun N : ℕ => Gs (gI A) N / Dn N) atTop (𝓝 c)) :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, aI A n) / Dn N) atTop (𝓝 C) := by
  have hG0 : ∀ M, 0 ≤ Gs (gI A) M := fun M => Finset.sum_nonneg fun n _ => gI_nonneg n
  have hGle : ∀ M, Gs (gI A) M ≤ M := Gs_le gI_le_one
  -- main convolution
  have hmain := conv_limit (Gs (gI A)) c hG0 hGle hG (fun d => hF A d) id (fun i => le_rfl)
    (by simp) (by simpa using hF_summable h1 hA)
  simp only [id] at hmain
  set H := ∑' i, hF A i / (i : ℝ) with hH
  have hmain' : Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, aI A n) / Dn N) atTop (𝓝 (c * H)) := by
    refine hmain.congr (fun N => ?_)
    rw [count_conv]
  -- squares
  set b : ℕ → ℝ := fun s => if s = 0 then 0 else 1 with hb
  have hbs : Summable (fun i => |b i| * (((i + 1) ^ 2 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))) := by
    have hs := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : (-(3 / 2 : ℝ)) < -1))
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hs
    simp only [hb, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    rw [rpow_pow_swap _ (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    split_ifs <;> simp [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (i : ℝ) + 1)]
  have hsq := conv_limit (Gs (gI A)) c hG0 hGle hG b (fun s => (s + 1) ^ 2)
    (fun i => by nlinarith) (by simp [hb]) hbs
  have hS2 : ∑' i, b i / (((i + 1) ^ 2 : ℕ) : ℝ) = Real.pi ^ 2 / 6 - 1 := zeta_two_tail.tsum_eq
  rw [hS2] at hsq
  have hsq' : Tendsto (fun N : ℕ => (∑ s ∈ Ioc 0 N, Gs (gI A) (N / (s + 1) ^ 2)) / Dn N) atTop
      (𝓝 (c * (Real.pi ^ 2 / 6 - 1))) := by
    refine hsq.congr (fun N => ?_)
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    simp only [mem_Ioc] at hs
    simp [hb, show s ≠ 0 by omega]
  have hineq : c ≤ c * H + c * (Real.pi ^ 2 / 6 - 1) := by
    refine le_of_tendsto_of_tendsto' hG (hmain'.add hsq') (fun N => ?_) |> fun h => ?_
    · exact h
    · rcases Nat.lt_or_ge N 2 with hN | hN
      · interval_cases N <;> simp [Gs, Dn]
      · have hD := Dn_pos hN
        rw [← add_div]
        exact div_le_div_of_nonneg_right (G_le_A_add h1 hA N) hD.le
  have hpi : Real.pi ^ 2 / 6 - 1 < 1 := by
    have := Real.pi_lt_d2
    have := Real.pi_pos
    nlinarith
  have hHpos : 0 < H := by
    by_contra hneg
    push Not at hneg
    nlinarith
  exact ⟨c * H, mul_pos hc hHpos, hmain'⟩

end PartT

/-! ## Part P: prime input from `π_A(x) = li(x)/2 + O(x / log³ x)` -/

section PartP

theorem cesaro_Ioc {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, u n) / N) atTop (𝓝 l) := by
  have h1 := (h.cesaro.comp (tendsto_add_atTop_nat 1))
  have h2 : Tendsto (fun N : ℕ => u 0 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have := tendsto_const_div_atTop_nhds_zero_nat (u 0)
    exact (this.comp (tendsto_add_atTop_nat 1)).congr (fun N => by simp)
  have h3 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_add 1
    rw [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (0 : ℝ) < N := by exact_mod_cast hN
    field_simp
  have h4 := ((h1.sub h2).mul h3)
  rw [sub_zero, mul_one] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp]
  have e : ∑ i ∈ Finset.range (N + 1), u i = u 0 + ∑ n ∈ Ioc 0 N, u n := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    rfl
  rw [e]; push_cast
  field_simp
  ring

theorem tsum_tele_bound (N : ℕ) :
    ∑ n ∈ Ioc 2 N, 1 / ((n : ℝ) * Real.log n ^ 2) ≤ 1 / Real.log 2 := by
  have key : ∀ n ∈ Ioc 2 N, 1 / ((n : ℝ) * Real.log n ^ 2) ≤
      1 / Real.log ((n - 1 : ℕ) : ℝ) - 1 / Real.log n := by
    intro n hn
    simp only [mem_Ioc] at hn
    have hn1 : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ n - 1)
    have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hl1 : 0 < Real.log ((n - 1 : ℕ) : ℝ) := Real.log_pos (by linarith)
    have hln : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log n := Real.log_le_log (by linarith) (by linarith)
    have hd := (log_succ_div_bounds (n - 1) (by omega)).1
    rw [hcast] at hd
    have hnr : (0 : ℝ) < n := by linarith
    have hlnp : 0 < Real.log (n : ℝ) := lt_of_lt_of_le hl1 hln
    rw [div_sub_div _ _ hl1.ne' (by linarith), div_le_div_iff₀ (mul_pos hnr (pow_pos hlnp 2))
      (mul_pos hl1 hlnp)]
    have : 1 / (n : ℝ) ≤ Real.log n - Real.log ((n - 1 : ℕ) : ℝ) := hd
    rw [div_le_iff₀ hnr] at this
    have h2 : Real.log ((n - 1 : ℕ) : ℝ) * Real.log n ≤ Real.log n ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1)]
  refine (Finset.sum_le_sum key).trans ?_
  -- telescoping
  have tele : ∀ M, 2 ≤ M → ∑ n ∈ Ioc 2 M, (1 / Real.log ((n - 1 : ℕ) : ℝ) - 1 / Real.log n) =
      1 / Real.log 2 - 1 / Real.log M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hM ih =>
      rw [Finset.sum_Ioc_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      push_cast; ring
  rcases le_or_gt 2 N with hN | hN
  · rw [tele N hN]
    have : 0 ≤ 1 / Real.log N := by
      apply div_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N)))
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]; simp; positivity

variable (A : Set ℕ)

open Classical in
noncomputable def cA (n : ℕ) : ℝ := if n.Prime ∧ n ∈ A then 1 else 0

noncomputable def pc (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, cA A n

noncomputable def li (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

noncomputable def EA (n : ℕ) : ℝ := if n ≤ 1 then 0 else pc A n - 1 / 2 * li n

noncomputable def Lp (n : ℕ) : ℝ := if n ≤ 2 then 0 else li n - li ((n - 1 : ℕ) : ℝ)

variable {A}

theorem li_integrable {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const
  · exact Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have := (Set.mem_uIcc.1 ht); rcases this with h | h <;> linarith [h.1])
  · intro t ht
    have := (Set.mem_uIcc.1 ht)
    have h2 : 1 < t := by rcases this with h | h <;> linarith [h.1]
    exact (Real.log_pos h2).ne'

theorem li_step {n : ℕ} (hn : 2 ≤ n) :
    1 / Real.log ((n : ℝ) + 1) ≤ li ((n : ℝ) + 1) - li n ∧
      li ((n : ℝ) + 1) - li n ≤ 1 / Real.log n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [li, li, intervalIntegral.integral_interval_sub_left (li_integrable le_rfl (by linarith))
    (li_integrable le_rfl hn')]
  have hint := li_integrable hn' (by linarith : (2 : ℝ) ≤ n + 1)
  constructor
  · have := intervalIntegral.integral_mono_on (by linarith : (n : ℝ) ≤ n + 1)
      (intervalIntegrable_const (c := 1 / Real.log ((n : ℝ) + 1))) hint (fun t ht => by
        apply one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
        exact Real.log_le_log (by linarith [ht.1]) ht.2)
    simpa using this
  · have := intervalIntegral.integral_mono_on (by linarith : (n : ℝ) ≤ n + 1) hint
      (intervalIntegrable_const (c := 1 / Real.log (n : ℝ))) (fun t ht => by
        apply one_div_le_one_div_of_le (Real.log_pos (by linarith))
        exact Real.log_le_log (by linarith) ht.1)
    simpa using this

theorem Lp_bounds {n : ℕ} (hn : 3 ≤ n) :
    1 / Real.log n ≤ Lp n ∧ Lp n ≤ 1 / Real.log ((n - 1 : ℕ) : ℝ) := by
  have h := li_step (n := n - 1) (by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) + 1 = n := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at h
  unfold Lp
  rw [if_neg (by omega)]
  exact h

theorem cA_decomp (n : ℕ) (hn : 1 ≤ n) :
    cA A n = 1 / 2 * Lp n + (EA A n - EA A (n - 1)) := by
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
  · simp [cA, Lp, EA, Nat.not_prime_one]
  · have hpc : pc A 2 = cA A 2 := by
      rw [pc, Finset.sum_Ioc_succ_top (by norm_num : 0 ≤ 1),
        Finset.sum_Ioc_succ_top (by norm_num : 0 ≤ 0), Finset.Ioc_self, Finset.sum_empty]
      simp [cA, Nat.not_prime_one]
    simp [Lp, EA, li, hpc]
  · have hpc : pc A n = pc A (n - 1) + cA A n := by
      have := Finset.sum_Ioc_succ_top (show 0 ≤ n - 1 by omega) (cA A)
      rw [Nat.sub_add_cancel (by omega)] at this
      exact this
    simp only [Lp, EA, if_neg (show ¬ n ≤ 2 by omega), if_neg (show ¬ n ≤ 1 by omega),
      if_neg (show ¬ n - 1 ≤ 1 by omega), hpc]
    ring

theorem EA_tele (n : ℕ) : ∑ k ∈ Ioc 0 n, (EA A k - EA A (k - 1)) = EA A n := by
  induction n with
  | zero => simp [EA]
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _), ih]
    simp

theorem sum_decomp (w : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, cA A n * w n = 1 / 2 * ∑ n ∈ Ioc 0 N, Lp n * w n +
      (EA A N * w N + ∑ n ∈ Ioc 0 (N - 1), EA A n * (w n - w (n + 1))) := by
  have : ∀ n ∈ Ioc 0 N, cA A n * w n =
      1 / 2 * (Lp n * w n) + (EA A n - EA A (n - 1)) * w n := by
    intro n hn
    simp only [mem_Ioc] at hn
    rw [cA_decomp n hn.1]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum,
    abel (fun k => EA A k - EA A (k - 1)) w N]
  simp only [EA_tele]

/-- Uniform error bound from the `IsBigO` hypothesis. -/
theorem EA_bound
    (hπ : (fun x : ℕ => pc A x - (1 / 2 : ℝ) * li x) =O[atTop]
      (fun x : ℕ => (x : ℝ) / Real.log (x : ℝ) ^ 3)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, |EA A n| ≤ K * ((n : ℝ) / Real.log n ^ 3) := by
  obtain ⟨c, hc⟩ := hπ.bound
  obtain ⟨n1, hn1⟩ := Filter.eventually_atTop.1 hc
  set K := max c 0 + ∑ n ∈ Finset.range n1, |EA A n| / ((n : ℝ) / Real.log n ^ 3) with hK
  have hS : 0 ≤ ∑ n ∈ Finset.range n1, |EA A n| / ((n : ℝ) / Real.log n ^ 3) :=
    Finset.sum_nonneg fun n _ => by
      rcases le_or_gt n 1 with h | h
      · positivity
      · have : (1 : ℝ) < n := by exact_mod_cast h
        have := Real.log_pos this
        positivity
  refine ⟨K, by positivity, fun n => ?_⟩
  rcases le_or_gt n 1 with h | h
  · interval_cases n <;> simp [EA]
  have hn1' : (1 : ℝ) < n := by exact_mod_cast h
  have hl := Real.log_pos hn1'
  have hg : 0 < (n : ℝ) / Real.log n ^ 3 := by positivity
  have hEA : EA A n = pc A n - 1 / 2 * li n := by simp [EA, show ¬ n ≤ 1 by omega]
  rcases le_or_gt n1 n with h2 | h2
  · have := hn1 n h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hg] at this
    rw [hEA]
    calc |pc A n - 1 / 2 * li n| ≤ c * ((n : ℝ) / Real.log n ^ 3) := this
      _ ≤ K * ((n : ℝ) / Real.log n ^ 3) := by
          apply mul_le_mul_of_nonneg_right _ hg.le
          linarith [le_max_left c 0]
  · have hmem : n ∈ Finset.range n1 := Finset.mem_range.2 h2
    have := Finset.single_le_sum (f := fun n => |EA A n| / ((n : ℝ) / Real.log n ^ 3))
      (fun m _ => by
        rcases le_or_gt m 1 with h | h
        · positivity
        · have : (1 : ℝ) < m := by exact_mod_cast h
          have := Real.log_pos this
          positivity) hmem
    rw [div_le_iff₀ hg] at this
    calc |EA A n| ≤ (∑ n ∈ Finset.range n1, |EA A n| / ((n : ℝ) / Real.log n ^ 3)) *
          ((n : ℝ) / Real.log n ^ 3) := this
      _ ≤ K * ((n : ℝ) / Real.log n ^ 3) := by
          apply mul_le_mul_of_nonneg_right _ hg.le
          linarith [le_max_right c 0]

end PartP

section PartP2

variable {A : Set ℕ}

noncomputable def thA (A : Set ℕ) (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, cA A n * Real.log n

theorem log_two_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; norm_num at this; linarith

theorem log_ge_one_of_three {n : ℕ} (hn : 3 ≤ n) : 1 ≤ Real.log n := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  have : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- `Lp n * log n → 1`. -/
theorem Lp_log_tendsto : Tendsto (fun n : ℕ => Lp n * Real.log n) atTop (𝓝 1) := by
  have hup : Tendsto (fun n : ℕ => 1 + (1 / Real.log 2) / ((n : ℝ) - 1)) atTop (𝓝 1) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
    have := (tendsto_const_nhds (x := 1 / Real.log 2)).div_atTop h
    simpa [sub_eq_add_neg] using this.const_add 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have := (Lp_bounds hn).1
    have hl : 0 < Real.log n := lt_of_lt_of_le one_pos (log_ge_one_of_three hn)
    rw [div_le_iff₀ hl] at this; linarith
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hb := (Lp_bounds hn).2
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [hcast] at hb
    have hn1 : (2 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (3 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hl1 : Real.log 2 ≤ Real.log ((n : ℝ) - 1) := Real.log_le_log (by norm_num) hn1
    have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hl1p : 0 < Real.log ((n : ℝ) - 1) := lt_of_lt_of_le hl2 hl1
    have hd := (log_succ_div_bounds (n - 1) (by omega)).2
    have hcast2 : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [hcast]; ring
    rw [hcast2, hcast] at hd
    have hln : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    calc Lp n * Real.log n ≤ 1 / Real.log ((n : ℝ) - 1) * Real.log n :=
          mul_le_mul_of_nonneg_right hb hln
      _ = 1 + (Real.log n - Real.log ((n : ℝ) - 1)) / Real.log ((n : ℝ) - 1) := by
          field_simp; ring
      _ ≤ 1 + (1 / ((n : ℝ) - 1)) / Real.log 2 := by
          gcongr
      _ = 1 + (1 / Real.log 2) / ((n : ℝ) - 1) := by ring

theorem thA_tendsto {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ n : ℕ, |EA A n| ≤ K * ((n : ℝ) / Real.log n ^ 3)) :
    Tendsto (fun N : ℕ => thA A N / N) atTop (𝓝 (1 / 2)) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain := (cesaro_Ioc Lp_log_tendsto).const_mul (1 / 2 : ℝ)
  rw [mul_one] at hmain
  set v : ℕ → ℝ := fun n => |EA A n| * (Real.log ((n : ℝ) + 1) - Real.log n) with hv
  have hv0 : ∀ n, 0 ≤ v n := fun n => by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [hv, EA]
    · have := (log_succ_div_bounds n h).1
      exact mul_nonneg (abs_nonneg _) (le_trans (by positivity) this)
  have hvt : Tendsto v atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => K / Real.log n ^ 3) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num) |>.comp hlogN)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    · exact Eventually.of_forall hv0
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hl := Real.log_pos (by exact_mod_cast (by omega : 1 < n) : (1 : ℝ) < n)
      have hd := (log_succ_div_bounds n (by omega)).2
      calc v n ≤ K * ((n : ℝ) / Real.log n ^ 3) * (1 / n) :=
            mul_le_mul (hK n) hd (le_trans (by positivity) (log_succ_div_bounds n (by omega)).1)
              (by positivity)
        _ = K / Real.log n ^ 3 := by field_simp
  have hcv := cesaro_Ioc hvt
  have hEN : Tendsto (fun N : ℕ => EA A N * Real.log N / N) atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => K / Real.log n ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num) |>.comp hlogN)
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    · exact Eventually.of_forall fun n => abs_nonneg _
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hl := Real.log_pos (by exact_mod_cast (by omega : 1 < n) : (1 : ℝ) < n)
      simp only [Function.comp]
      rw [abs_div, abs_mul, abs_of_pos hl, abs_of_pos hnr]
      calc |EA A n| * Real.log n / n ≤ K * ((n : ℝ) / Real.log n ^ 3) * Real.log n / n := by
            gcongr; exact hK n
        _ = K / Real.log n ^ 2 := by field_simp
  -- assemble
  have hdiff : Tendsto (fun N : ℕ => (thA A N - (1 / 2 * ∑ n ∈ Ioc 0 N, Lp n * Real.log n)) / N)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    have hup := hEN.abs.add hcv
    rw [abs_zero, add_zero] at hup
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · exact Eventually.of_forall fun n => abs_nonneg _
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      simp only [Function.comp]
      rw [thA, sum_decomp (fun n => Real.log n) N]
      simp only [add_sub_cancel_left]
      rw [abs_div (EA A N * Real.log N), abs_of_pos hNr, ← add_div, abs_div, abs_of_pos hNr]
      apply div_le_div_of_nonneg_right _ hNr.le
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ioc_subset_Ioc_right (Nat.sub_le N 1)) (fun i _ _ => hv0 i))
      apply Finset.sum_le_sum
      intro n _
      have hpos : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h; simp
        · have : (0 : ℝ) < n := by exact_mod_cast h
          have := Real.log_le_log this (by linarith : (n : ℝ) ≤ n + 1); linarith
      simp only [hv]
      rw [abs_mul, abs_sub_comm]; push_cast; rw [abs_of_nonneg hpos]
  have := hmain.add hdiff
  rw [add_zero] at this
  refine this.congr (fun N => ?_)
  ring

end PartP2

section PartP3

variable {A : Set ℕ}

noncomputable def MA (A : Set ℕ) (N : ℕ) : ℝ := ∑ n ∈ Ioc 0 N, cA A n * (Real.log n / n)

theorem Lp_log_le {n : ℕ} (hn : 3 ≤ n) : Lp n * Real.log n ≤ 1 + (1 / Real.log 2) / ((n : ℝ) - 1) := by
  have hb := (Lp_bounds hn).2
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at hb
  have hn1 : (2 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hl1 : Real.log 2 ≤ Real.log ((n : ℝ) - 1) := Real.log_le_log (by norm_num) hn1
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hl1p : 0 < Real.log ((n : ℝ) - 1) := lt_of_lt_of_le hl2 hl1
  have hd := (log_succ_div_bounds (n - 1) (by omega)).2
  have hcast2 : ((n - 1 : ℕ) : ℝ) + 1 = n := by rw [hcast]; ring
  rw [hcast2, hcast] at hd
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  calc Lp n * Real.log n ≤ 1 / Real.log ((n : ℝ) - 1) * Real.log n :=
        mul_le_mul_of_nonneg_right hb hln
    _ = 1 + (Real.log n - Real.log ((n : ℝ) - 1)) / Real.log ((n : ℝ) - 1) := by
        field_simp; ring
    _ ≤ 1 + (1 / ((n : ℝ) - 1)) / Real.log 2 := by gcongr
    _ = 1 + (1 / Real.log 2) / ((n : ℝ) - 1) := by ring

theorem Lp_nonneg (n : ℕ) : 0 ≤ Lp n := by
  rcases le_or_gt n 2 with h | h
  · simp [Lp, h]
  · have := (Lp_bounds (n := n) h).1
    have : 0 ≤ 1 / Real.log n := by
      apply div_nonneg zero_le_one (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    linarith

theorem harm_bounds (N : ℕ) :
    Real.log N ≤ ∑ n ∈ Ioc 0 N, (1 : ℝ) / n ∧ ∑ n ∈ Ioc 0 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
  have e : ∑ n ∈ Ioc 0 N, (1 : ℝ) / n = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast
    rw [show (Icc 1 N : Finset ℕ) = Ioc 0 N by ext n; simp; omega]
    apply Finset.sum_congr rfl; intro n _; rw [one_div]
  rw [e]
  refine ⟨le_trans ?_ (log_add_one_le_harmonic N), harmonic_le_one_add_log N⟩
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · exact Real.log_le_log (by exact_mod_cast h) (by push_cast; linarith)

theorem main_MA_bound : ∃ C1 : ℝ, ∀ N : ℕ,
    |∑ n ∈ Ioc 0 N, Lp n * (Real.log n / n) - Real.log N| ≤ C1 := by
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ 2
  have hZs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.2 (by norm_num)
  have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  refine ⟨3 + (2 / Real.log 2) * Z, fun N => ?_⟩
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  -- termwise bounds
  have hlo : ∀ n ∈ Ioc 0 N, (if 3 ≤ n then (1 : ℝ) / n else 0) ≤ Lp n * (Real.log n / n) := by
    intro n hn
    simp only [mem_Ioc] at hn
    split_ifs with h
    · have h1 := (Lp_bounds h).1
      have hl : 0 < Real.log n := lt_of_lt_of_le one_pos (log_ge_one_of_three h)
      have hnr : (0 : ℝ) < n := by exact_mod_cast hn.1
      rw [div_le_iff₀ hl] at h1
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right hnr]; linarith
    · exact mul_nonneg (Lp_nonneg n) (div_nonneg (Real.log_nonneg
        (by exact_mod_cast hn.1)) (Nat.cast_nonneg _))
  have hhi : ∀ n ∈ Ioc 0 N, Lp n * (Real.log n / n) ≤
      (1 : ℝ) / n + (2 / Real.log 2) * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    simp only [mem_Ioc] at hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn.1
    rcases le_or_gt n 2 with h | h
    · simp only [Lp, if_pos h, zero_mul]; positivity
    · have := Lp_log_le (n := n) h
      have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast h
      have hn1 : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
      rw [← mul_div_assoc]
      calc Lp n * Real.log n / n ≤ (1 + (1 / Real.log 2) / ((n : ℝ) - 1)) / n :=
            div_le_div_of_nonneg_right this hnr.le
        _ ≤ (1 + (1 / Real.log 2) / ((n : ℝ) / 2)) / n := by
            gcongr
        _ = (1 : ℝ) / n + (2 / Real.log 2) * (1 / (n : ℝ) ^ 2) := by
            field_simp
  have s1 := Finset.sum_le_sum hlo
  have s2 := Finset.sum_le_sum hhi
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at s2
  have hz : ∑ n ∈ Ioc 0 N, 1 / (n : ℝ) ^ 2 ≤ Z :=
    hZs.sum_le_tsum _ (fun n _ => by positivity)
  obtain ⟨hh1, hh2⟩ := harm_bounds N
  have hlow : ∑ n ∈ Ioc 0 N, (if 3 ≤ n then (1 : ℝ) / n else 0) ≥
      ∑ n ∈ Ioc 0 N, (1 : ℝ) / n - 3 / 2 := by
    have : ∀ n ∈ Ioc 0 N, (1 : ℝ) / n - (if n ≤ 2 then (1 : ℝ) / n else 0) =
        (if 3 ≤ n then (1 : ℝ) / n else 0) := by
      intro n _
      by_cases h : 3 ≤ n
      · rw [if_neg (by omega), if_pos h]; ring
      · rw [if_pos (by omega), if_neg h]; ring
    rw [← Finset.sum_congr rfl this, Finset.sum_sub_distrib]
    have : ∑ n ∈ Ioc 0 N, (if n ≤ 2 then (1 : ℝ) / n else 0) ≤ 3 / 2 := by
      rw [← Finset.sum_filter]
      calc ∑ n ∈ (Ioc 0 N).filter (· ≤ 2), (1 : ℝ) / n ≤ ∑ n ∈ Ioc (0 : ℕ) 2, (1 : ℝ) / (n : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn; simp only [mem_filter, mem_Ioc] at hn ⊢; omega
            · intro n _ _; positivity
        _ = 3 / 2 := by
            rw [show (Ioc 0 2 : Finset ℕ) = {1, 2} by decide]
            norm_num
    linarith
  have hmul : 0 ≤ (2 / Real.log 2) * ∑ n ∈ Ioc 0 N, 1 / (n : ℝ) ^ 2 := by positivity
  have hmul2 : (2 / Real.log 2) * ∑ n ∈ Ioc 0 N, 1 / (n : ℝ) ^ 2 ≤ (2 / Real.log 2) * Z :=
    mul_le_mul_of_nonneg_left hz (by positivity)
  rw [abs_le]; constructor <;> linarith

theorem dw_bound {n : ℕ} (hn : 1 ≤ n) :
    |Real.log n / n - Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)| ≤
      (Real.log n + 1) / ((n : ℝ) * (n + 1)) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨b1, b2⟩ := log_succ_div_bounds n hn
  have hln : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  push_cast
  have e : Real.log n / n - Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) =
      (Real.log n - n * (Real.log ((n : ℝ) + 1) - Real.log n)) / ((n : ℝ) * (n + 1)) := by
    field_simp; ring
  have hpos : (0 : ℝ) < (n : ℝ) * (n + 1) := mul_pos hnr (by linarith)
  rw [e, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos]
  have h1 : n * (Real.log ((n : ℝ) + 1) - Real.log n) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left b2 hnr.le
    rwa [mul_one_div_cancel hnr.ne'] at this
  have h0 : 0 ≤ n * (Real.log ((n : ℝ) + 1) - Real.log n) :=
    mul_nonneg hnr.le (le_trans (by positivity) b1)
  rw [abs_le]; constructor <;> linarith

theorem MA_bound {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ n : ℕ, |EA A n| ≤ K * ((n : ℝ) / Real.log n ^ 3)) :
    ∃ C : ℝ, ∀ N : ℕ, |MA A N - 1 / 2 * Real.log N| ≤ C := by
  obtain ⟨C1, hC1⟩ := main_MA_bound
  have hl2 := log_two_gt_half
  refine ⟨C1 / 2 + 4 * K + (6 * K + 6 * K), fun N => ?_⟩
  have hdec := sum_decomp (A := A) (fun n => Real.log n / n) N
  rw [← MA] at hdec
  rw [hdec]
  -- piece (b)
  have hb : |EA A N * (Real.log N / N)| ≤ 4 * K := by
    rcases le_or_gt N 1 with h | h
    · interval_cases N <;> simp [EA] <;> positivity
    have hNr : (1 : ℝ) < N := by exact_mod_cast h
    have hl := Real.log_pos hNr
    have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast h)
    rw [abs_mul, abs_of_nonneg (div_nonneg hl.le (by linarith))]
    calc |EA A N| * (Real.log N / N) ≤ K * ((N : ℝ) / Real.log N ^ 3) * (Real.log N / N) :=
          mul_le_mul_of_nonneg_right (hK N) (div_nonneg hl.le (by linarith))
      _ = K / Real.log N ^ 2 := by field_simp
      _ ≤ K / (1 / 2) ^ 2 := by
          apply div_le_div_of_nonneg_left hK0 (by norm_num)
          nlinarith
      _ = 4 * K := by ring
  -- piece (c)
  have hc : |∑ n ∈ Ioc 0 (N - 1), EA A n * (Real.log n / n -
      Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))| ≤ 6 * K + 6 * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ n ∈ Ioc 0 N, |EA A n * (Real.log n / n -
        Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))| ≤
        (if 2 ≤ n then 3 * K / ((n : ℝ) * Real.log n ^ 2) else 0) := by
      intro n hn
      simp only [mem_Ioc] at hn
      split_ifs with h
      · have hnr : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
        have hl := Real.log_pos hnr
        have hlN : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h)
        rw [abs_mul]
        calc |EA A n| * |Real.log n / n - Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)|
            ≤ K * ((n : ℝ) / Real.log n ^ 3) * ((Real.log n + 1) / ((n : ℝ) * (n + 1))) :=
              mul_le_mul (hK n) (dw_bound hn.1) (abs_nonneg _) (by positivity)
          _ = K * (Real.log n + 1) / (Real.log n ^ 3 * (n + 1)) := by field_simp
          _ ≤ K * (3 * Real.log n) / (Real.log n ^ 3 * n) := by
              have hl12 : (1 / 2 : ℝ) ≤ Real.log n := by linarith
              have hnr0 : (0 : ℝ) < n := by linarith
              apply div_le_div₀ (mul_nonneg hK0 (by linarith))
                (mul_le_mul_of_nonneg_left (by linarith) hK0) (mul_pos (pow_pos hl 3) hnr0)
                (mul_le_mul_of_nonneg_left (by linarith) (pow_pos hl 3).le)
          _ = 3 * K / ((n : ℝ) * Real.log n ^ 2) := by field_simp
      · have : n = 1 := by omega
        subst this; simp [EA]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ioc_subset_Ioc_right (Nat.sub_le N 1)) (fun i _ _ => abs_nonneg _)) ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rcases le_or_gt N 2 with h | h
    · have : ∑ n ∈ Ioc 0 N, (if 2 ≤ n then 3 * K / ((n : ℝ) * Real.log n ^ 2) else 0) ≤
          3 * K / (2 * Real.log 2 ^ 2) := by
        interval_cases N
        · simp; positivity
        · simp
          positivity
        · rw [show (Ioc 0 2 : Finset ℕ) = {1, 2} by decide]
          norm_num
      refine this.trans ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ^ 2 ≤ Real.log 2 ^ 2 by nlinarith) hK0]
    · rw [← Finset.sum_Ioc_consecutive _ (show 0 ≤ 2 by norm_num) (show 2 ≤ N by omega)]
      have h12 : ∑ n ∈ Ioc (0 : ℕ) 2, (if 2 ≤ n then 3 * K / ((n : ℝ) * Real.log n ^ 2) else 0) =
          3 * K / (2 * Real.log 2 ^ 2) := by
        rw [show (Ioc 0 2 : Finset ℕ) = {1, 2} by decide]
        norm_num
      have hrest : ∑ n ∈ Ioc 2 N, (if 2 ≤ n then 3 * K / ((n : ℝ) * Real.log n ^ 2) else 0) ≤
          3 * K * (1 / Real.log 2) := by
        rw [Finset.sum_congr rfl (fun n hn => by
          simp only [mem_Ioc] at hn
          rw [if_pos (by omega)])]
        have := tsum_tele_bound N
        rw [show (∑ n ∈ Ioc 2 N, 3 * K / ((n : ℝ) * Real.log n ^ 2)) =
          3 * K * ∑ n ∈ Ioc 2 N, 1 / ((n : ℝ) * Real.log n ^ 2) by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro n _; ring]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      rw [h12]
      have e1 : 3 * K / (2 * Real.log 2 ^ 2) ≤ 6 * K := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ^ 2 ≤ Real.log 2 ^ 2 by nlinarith) hK0]
      have e2 : 3 * K * (1 / Real.log 2) ≤ 6 * K := by
        rw [mul_one_div, div_le_iff₀ (by linarith)]; nlinarith
      linarith
  have ha := hC1 N
  have : |1 / 2 * ∑ n ∈ Ioc 0 N, Lp n * (Real.log n / n) - 1 / 2 * Real.log N| ≤ C1 / 2 := by
    rw [← mul_sub, abs_mul]; norm_num; linarith
  have key := abs_add_le (1 / 2 * ∑ n ∈ Ioc 0 N, Lp n * (Real.log n / n) - 1 / 2 * Real.log N)
    (EA A N * (Real.log N / N) + ∑ n ∈ Ioc 0 (N - 1), EA A n * (Real.log n / n -
      Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
  have key2 := abs_add_le (EA A N * (Real.log N / N)) (∑ n ∈ Ioc 0 (N - 1), EA A n *
    (Real.log n / n - Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)))
  have e : 1 / 2 * ∑ n ∈ Ioc 0 N, Lp n * (Real.log n / n) + (EA A N * (Real.log N / N) +
      ∑ n ∈ Ioc 0 (N - 1), EA A n * (Real.log n / n -
        Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) - 1 / 2 * Real.log N =
      (1 / 2 * ∑ n ∈ Ioc 0 N, Lp n * (Real.log n / n) - 1 / 2 * Real.log N) +
      (EA A N * (Real.log N / N) + ∑ n ∈ Ioc 0 (N - 1), EA A n * (Real.log n / n -
        Real.log ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))) := by ring
  rw [e]
  linarith

/-! ### From `cA` to the completely multiplicative `g = gI A` -/

theorem gL_decomp (n : ℕ) : gI A n * Λ n = cA A n * Real.log n +
    (if n.Prime then 0 else gI A n * Λ n) := by
  by_cases hp : n.Prime
  · rw [if_pos hp, add_zero, gI_prime hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    by_cases hA' : n ∈ A <;> simp [aI, cA, hp, hp.ne_zero, hA']
  · simp [cA, hp]

theorem np_le (n : ℕ) : (if n.Prime then 0 else gI A n * Λ n) ≤ (if n.Prime then 0 else Λ n) ∧
    0 ≤ (if n.Prime then 0 else gI A n * Λ n) := by
  split_ifs
  · simp
  · exact ⟨by nlinarith [gI_le_one (A := A) n, gI_nonneg (A := A) n,
      ArithmeticFunction.vonMangoldt_nonneg (n := n)],
      mul_nonneg (gI_nonneg n) ArithmeticFunction.vonMangoldt_nonneg⟩

theorem Q1 {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ n : ℕ, |EA A n| ≤ K * ((n : ℝ) / Real.log n ^ 3)) :
    Tendsto (fun N : ℕ => Psig (gI A) N / N) atTop (𝓝 (1 / 2)) := by
  have hth := thA_tendsto hK0 hK
  set R : ℕ → ℝ := fun N => ∑ n ∈ Ioc 0 N, (if n.Prime then 0 else gI A n * Λ n)
  have hsplit : ∀ N, Psig (gI A) N = thA A N + R N := by
    intro N
    simp only [Psig, thA, R]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => gL_decomp n
  have hR : Tendsto (fun N : ℕ => R N / N) atTop (𝓝 0) := by
    have hlo : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero
    have hup := (hlo.comp tendsto_natCast_atTop_atTop).const_mul 2
    rw [mul_zero] at hup
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · exact Eventually.of_forall fun N => div_nonneg
        (Finset.sum_nonneg fun n _ => (np_le n).2) (Nat.cast_nonneg _)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have h1 : R N ≤ Chebyshev.psi N - Chebyshev.theta N := by
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
        apply Finset.sum_le_sum; intro n _
        have := (np_le (A := A) n).1
        split_ifs at this ⊢ <;> simp_all
      have h2 := Chebyshev.psi_sub_theta_le hNr
      simp only [Function.comp]
      rw [div_le_iff₀ (by linarith)]
      have hs : Real.sqrt N = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
      have hsp : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      have hss : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = N := by
        rw [← hs]; exact Real.mul_self_sqrt (by linarith)
      have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
      have hsp' : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
      have : 2 * (Real.log N / (N : ℝ) ^ (1 / 2 : ℝ)) * N = 2 * Real.sqrt N * Real.log N := by
        rw [← hs, mul_assoc, div_mul_eq_mul_div, mul_div_assoc', div_eq_iff hsp'.ne']
        linear_combination (-(2 * Real.log (N : ℝ))) * hsq
      linarith
  have := hth.add hR
  rw [add_zero] at this
  refine this.congr (fun N => ?_)
  rw [hsplit, add_div]

theorem Q2 {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ n : ℕ, |EA A n| ≤ K * ((n : ℝ) / Real.log n ^ 3)) :
    ∃ C : ℝ, ∀ n : ℕ, 0 < n → |S1 (gI A) n - 1 / 2 * Real.log n| ≤ C := by
  obtain ⟨C, hC⟩ := MA_bound hK0 hK
  have hs := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  have hres : ∀ n, ArithmeticFunction.vonMangoldt.residueClass (0 : ZMod 1) n = Λ n := by
    intro n
    simp [ArithmeticFunction.vonMangoldt.residueClass, Subsingleton.elim (n : ZMod 1) 0]
  simp only [hres] at hs
  set T := ∑' n : ℕ, (if n.Prime then 0 else Λ n) / n
  refine ⟨C + T, fun N _ => ?_⟩
  have hsplit : S1 (gI A) N = MA A N +
      ∑ n ∈ Ioc 0 N, (if n.Prime then 0 else gI A n * Λ n) / n := by
    simp only [S1, MA]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    have e := gL_decomp (A := A) n
    calc gI A n * Λ n / n = (cA A n * Real.log n + (if n.Prime then 0 else gI A n * Λ n)) / n := by
          rw [← e]
      _ = cA A n * (Real.log n / n) + (if n.Prime then 0 else gI A n * Λ n) / n := by ring
  have h0 : 0 ≤ ∑ n ∈ Ioc 0 N, (if n.Prime then 0 else gI A n * Λ n) / n :=
    Finset.sum_nonneg fun n _ => div_nonneg (np_le n).2 (Nat.cast_nonneg _)
  have h1 : ∑ n ∈ Ioc 0 N, (if n.Prime then 0 else gI A n * Λ n) / n ≤ T := by
    refine le_trans (Finset.sum_le_sum fun n _ =>
      div_le_div_of_nonneg_right (np_le (A := A) n).1 (Nat.cast_nonneg _)) ?_
    exact hs.sum_le_tsum _ (fun n _ => div_nonneg (by split_ifs <;> simp
      [ArithmeticFunction.vonMangoldt_nonneg]) (Nat.cast_nonneg _))
  have := hC N
  rw [hsplit]
  rw [abs_le] at this ⊢
  constructor <;> linarith

end PartP3

/-! ## The final mean-value theorem for multiplicative sets -/

section Final

theorem ncard_primes_eq (A : Set ℕ) (x : ℕ) :
    (({p : ℕ | p ≤ x ∧ p.Prime ∧ p ∈ A}.ncard : ℕ) : ℝ) = pc A x := by
  classical
  have hset : {p : ℕ | p ≤ x ∧ p.Prime ∧ p ∈ A} =
      ↑((Ioc 0 x).filter (fun p => p.Prime ∧ p ∈ A)) := by
    ext p
    simp only [Set.mem_ofPred_eq, coe_filter, mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h2.pos, h1⟩, h2, h3⟩
    · rintro ⟨⟨_, h1⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  rw [hset, Set.ncard_coe_finset, pc, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl; intro n _
  simp only [cA]

theorem ncard_count_eq (A : Set ℕ) (x : ℕ) :
    (({n : ℕ | 0 < n ∧ n ≤ x ∧ n ∈ A}.ncard : ℕ) : ℝ) = ∑ n ∈ Ioc 0 x, aI A n := by
  classical
  have hset : {n : ℕ | 0 < n ∧ n ≤ x ∧ n ∈ A} = ↑((Ioc 0 x).filter (fun n => n ∈ A)) := by
    ext n
    simp only [Set.mem_ofPred_eq, coe_filter, mem_Ioc]
    tauto
  rw [hset, Set.ncard_coe_finset, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl; intro n hn
  simp only [mem_Ioc] at hn
  simp only [aI]; split_ifs <;> simp_all <;> omega

/-- **Mean value theorem (Landau–Wirsing type)** for multiplicative sets whose primes have
relative density one half, with the PNT-type input `π_A(x) = li(x)/2 + O(x / log³ x)`. -/
theorem mean_value_half (A : Set ℕ) (h1 : 1 ∈ A)
    (hA : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → (m * n ∈ A ↔ m ∈ A ∧ n ∈ A))
    (hπ : (fun x : ℕ => ({p : ℕ | p ≤ x ∧ p.Prime ∧ p ∈ A}.ncard : ℝ) -
      (1 / 2 : ℝ) * (∫ t in (2 : ℝ)..(x : ℝ), 1 / Real.log t))
      =O[atTop] (fun x : ℕ => (x : ℝ) / Real.log (x : ℝ) ^ 3)) :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℕ => ({n : ℕ | 0 < n ∧ n ≤ x ∧ n ∈ A}.ncard : ℝ)) ~[atTop]
        (fun x : ℕ => c * (x : ℝ) / Real.sqrt (Real.log (x : ℝ))) := by
  have hπ' : (fun x : ℕ => pc A x - (1 / 2 : ℝ) * li x) =O[atTop]
      (fun x : ℕ => (x : ℝ) / Real.log (x : ℝ) ^ 3) := by
    refine hπ.congr_left (fun x => ?_)
    rw [ncard_primes_eq, li]
  obtain ⟨K, hK0, hK⟩ := EA_bound hπ'
  obtain ⟨C, hC⟩ := Q2 hK0 hK
  obtain ⟨lam, hlam, hL⟩ := L_asymp (g := gI A) gI_mul gI_nonneg gI_one (by norm_num : (0 : ℝ) < 1 / 2)
    hC
  have hG := G_asymp (g := gI A) gI_mul gI_nonneg gI_le_one (by norm_num : (0 : ℝ) < 1 / 2) hlam
    (Q1 hK0 hK) hL
  have hG' : Tendsto (fun N : ℕ => Gs (gI A) N / Dn N) atTop (𝓝 (1 / 2 * lam)) := by
    refine hG.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hl := Real.log_pos (by exact_mod_cast (by omega : 1 < N) : (1 : ℝ) < N)
    unfold Dn
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg hl.le, ← Real.sqrt_eq_rpow]
    field_simp
  obtain ⟨c, hc, hcount⟩ := mean_value_set h1 hA (by positivity) hG'
  refine ⟨c, hc, Asymptotics.isEquivalent_of_tendsto_one ?_⟩
  have := hcount.div_const c
  rw [div_self hc.ne'] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  simp only [Pi.div_apply]
  rw [ncard_count_eq]
  have hl := Real.log_pos (by exact_mod_cast (by omega : 1 < N) : (1 : ℝ) < N)
  have := Real.sqrt_pos.2 hl
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  unfold Dn
  field_simp

end Final


end OMAMeanValue

theorem OMA.solution : OMA.R_Erdos323_erdos_323_variants_k_eq_2_R1.H1 := by
  intro A h1 hA hpi
  exact OMAMeanValue.mean_value_half A h1 hA hpi
