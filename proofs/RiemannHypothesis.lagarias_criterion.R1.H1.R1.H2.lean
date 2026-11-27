import OMAReductions.R_RiemannHypothesis_lagarias_criterion_R1_H1_R1
import Mathlib

/-!
Step RiemannHypothesis.lagarias_criterion.R1.H1.R1.H2

The finite rational certificate: for every `2 ≤ n ≤ 5040` there is a rational `q` with
`1 ≤ q ≤ harmonic n` and `σ 1 n < q + E q * (2 * L q)`, where `E` is the 24 term exponential
sum and `L` the 12 term atanh sum of the hypothesis.

The choice is `q = ⌊256 * h⌋ / 256`, where `h = 2 ^ (-48) * ∑ i < n, ⌊2 ^ 48 / (i + 1)⌋` is a
lower bound for `harmonic n`. The sum of divisors is bounded by pairing each divisor above the
square root with its codivisor, so one value of `n` costs about `√n` steps. A recursive checker
carries the accumulator for `h` and the square root bound from `n` to `n + 1`. It is evaluated
by the kernel in six blocks of at most 840 values, each block returning the accumulator that
the next block starts from.
-/

namespace OMA.LagariasCert

open scoped ArithmeticFunction.sigma

/-- Sum over the divisors `e ≤ d` of `n` of `e + n / e`, or of `e` alone when `e * e = n`. -/
def spair (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => spair n d +
      (if (d + 1) ∣ n then (if (d + 1) * (d + 1) = n then d + 1 else d + 1 + n / (d + 1)) else 0)

lemma spair_eq (n d : ℕ) :
    spair n d = ∑ e ∈ (Finset.Ico 1 (d + 1)).filter (fun e => e ∣ n),
      (if e * e = n then e else e + n / e) := by
  induction d with
  | zero => simp [spair]
  | succ d ih =>
    rw [spair, ih, Nat.Ico_succ_right_eq_insert_Ico (by omega : 1 ≤ d + 1), Finset.filter_insert]
    by_cases h : (d + 1) ∣ n
    · rw [if_pos h, if_pos h, Finset.sum_insert (by simp), add_comm]
    · rw [if_neg h, if_neg h, Nat.add_zero]

/-- Pairing each divisor above the square root with its codivisor. -/
lemma sigma_le_aux (n s : ℕ) (hs : n < (s + 1) * (s + 1)) :
    ∑ d ∈ n.divisors, d ≤ ∑ e ∈ (Finset.Ico 1 (s + 1)).filter (fun e => e ∣ n),
      (if e * e = n then e else e + n / e) := by
  have h2 : ∑ e ∈ n.divisors, (if s < n / e then n / e else 0)
      = ∑ d ∈ n.divisors, (if s < d then d else 0) :=
    Nat.sum_div_divisors n (fun d => if s < d then d else 0)
  have key : ∑ d ∈ n.divisors, d
      = ∑ e ∈ n.divisors, ((if e ≤ s then e else 0) + (if s < n / e then n / e else 0)) := by
    rw [Finset.sum_add_distrib, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> omega
  rw [key]
  calc ∑ e ∈ n.divisors, ((if e ≤ s then e else 0) + (if s < n / e then n / e else 0))
      ≤ ∑ e ∈ n.divisors, (if e ≤ s then (if e * e = n then e else e + n / e) else 0) := by
        refine Finset.sum_le_sum fun e he => ?_
        have hdvd : e ∣ n := Nat.dvd_of_mem_divisors he
        have hmul : e * (n / e) = n := Nat.mul_div_cancel' hdvd
        have hpos : 0 < e := Nat.pos_of_mem_divisors he
        by_cases h1 : e ≤ s
        · by_cases h3 : e * e = n
          · have h4 : n / e = e := Nat.eq_of_mul_eq_mul_left hpos (hmul.trans h3.symm)
            have h5 : ¬ s < n / e := by omega
            simp only [if_pos h1, if_pos h3, if_neg h5, Nat.add_zero, le_refl]
          · simp only [if_pos h1, if_neg h3]
            by_cases h6 : s < n / e
            · simp only [if_pos h6, le_refl]
            · simp only [if_neg h6, Nat.add_zero, Nat.le_add_right]
        · have h5 : ¬ s < n / e := by
            intro h6
            have h7 : (s + 1) * (s + 1) ≤ e * (n / e) := Nat.mul_le_mul (by omega) (by omega)
            omega
          simp only [if_neg h1, if_neg h5, Nat.add_zero, le_refl]
    _ = ∑ e ∈ n.divisors.filter (fun e => e ≤ s), (if e * e = n then e else e + n / e) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ e ∈ (Finset.Ico 1 (s + 1)).filter (fun e => e ∣ n),
          (if e * e = n then e else e + n / e) := by
        refine Finset.sum_le_sum_of_subset fun e he => ?_
        rw [Finset.mem_filter] at he
        rw [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨Nat.pos_of_mem_divisors he.1, by omega⟩, Nat.dvd_of_mem_divisors he.1⟩

lemma sigma_le (n s : ℕ) (hs : n < (s + 1) * (s + 1)) : σ 1 n ≤ spair n s := by
  rw [ArithmeticFunction.sigma_one_apply, spair_eq]
  exact sigma_le_aux n s hs

/-- The right-hand side of the certificate, as a function of the rational parameter. -/
def F (q : ℚ) : ℚ :=
  q + (∑ i ∈ Finset.range 24, q^i / (i.factorial : ℚ)) *
      (2 * ∑ i ∈ Finset.range 12, ((q-1)/(q+1))^(2*i+1) / ((2*i+1 : ℕ) : ℚ))

/-- A floor-scaled lower bound for `2 ^ 48 * harmonic n`. -/
def hl : ℕ → ℕ
  | 0 => 0
  | n + 1 => hl n + 2 ^ 48 / (n + 1)

lemma hl_le (n : ℕ) : ((hl n : ℕ) : ℚ) ≤ 2 ^ 48 * harmonic n := by
  induction n with
  | zero => simp [hl]
  | succ n ih =>
    have h : ((2 ^ 48 / (n + 1) : ℕ) : ℚ) ≤ ((2 ^ 48 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ) :=
      Nat.cast_div_le
    rw [div_eq_mul_inv] at h
    rw [hl, harmonic_succ, Nat.cast_add, mul_add]
    push_cast at h ⊢
    linarith

/-- The test for a single `n`. Here `acc` stands for `hl n`, the parameter is
`q = ⌊acc / 2 ^ 40⌋ / 256`, and `s` is a bound with `n < (s + 1) ^ 2`. -/
def good (n acc s : ℕ) : Bool :=
  decide (256 ≤ acc / 2 ^ 40) && decide (n < (s + 1) * (s + 1)) &&
    decide (((spair n s : ℕ) : ℚ) < F (((acc / 2 ^ 40 : ℕ) : ℚ) / 256))

/-- Runs the test on `f` consecutive values starting from `n`, and returns the final
accumulator and square root bound when every test passes. -/
def run : ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _, acc, s => some (acc, s)
  | f + 1, n, acc, s =>
      if good n acc s = true then
        run f (n + 1) (acc + 2 ^ 48 / (n + 1)) (if (s + 1) * (s + 1) ≤ n + 1 then s + 1 else s)
      else none

lemma run_sound : ∀ f n s a t : ℕ, run f n (hl n) s = some (a, t) →
    a = hl (n + f) ∧ ∀ m, n ≤ m → m < n + f → ∃ t', good m (hl m) t' = true := by
  intro f
  induction f with
  | zero =>
    intro n s a t h
    rw [run] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, fun m h1 h2 => by omega⟩
  | succ f ih =>
    intro n s a t h
    rw [run] at h
    by_cases hg : good n (hl n) s = true
    · rw [if_pos hg] at h
      have e : hl (n + 1) = hl n + 2 ^ 48 / (n + 1) := rfl
      obtain ⟨h1, h2⟩ := ih (n + 1) _ a t (e ▸ h)
      have e2 : n + 1 + f = n + (f + 1) := by omega
      refine ⟨by rw [h1, e2], fun m hm1 hm2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hm1 with rfl | h3
      · exact ⟨s, hg⟩
      · exact h2 m h3 (by omega)
    · rw [if_neg hg] at h
      exact absurd h (by simp)

lemma chunk (f n s a t A : ℕ) (hA : A = hl n) (h : run f n A s = some (a, t)) :
    a = hl (n + f) ∧ ∀ m, n ≤ m → m < n + f → ∃ t', good m (hl m) t' = true := by
  subst hA
  exact run_sound f n s a t h

theorem cert1 : run 840 2 (hl 2) 1 = some (2058592402047273, 29) := by
  decide +kernel

theorem cert2 : run 840 842 (2058592402047273) 29 = some (2253278047399364, 41) := by
  decide +kernel

theorem cert3 : run 840 1682 (2253278047399364) 41 = some (2367266879359916, 50) := by
  decide +kernel

theorem cert4 : run 840 2522 (2367266879359916) 50 = some (2448172433481256, 57) := by
  decide +kernel

theorem cert5 : run 840 3362 (2448172433481256) 57 = some (2510939900889600, 64) := by
  decide +kernel

theorem cert6 : run 839 4202 (2510939900889600) 64 = some (2562175121705535, 71) := by
  decide +kernel

theorem all_good (m : ℕ) (h2 : 2 ≤ m) (h5 : m ≤ 5040) : ∃ t, good m (hl m) t = true := by
  have k1 := chunk _ _ _ _ _ _ rfl cert1
  have k2 := chunk _ _ _ _ _ _ k1.1 cert2
  have k3 := chunk _ _ _ _ _ _ k2.1 cert3
  have k4 := chunk _ _ _ _ _ _ k3.1 cert4
  have k5 := chunk _ _ _ _ _ _ k4.1 cert5
  have k6 := chunk _ _ _ _ _ _ k5.1 cert6
  by_cases c1 : m < 842
  · exact k1.2 m (by omega) (by omega)
  by_cases c2 : m < 1682
  · exact k2.2 m (by omega) (by omega)
  by_cases c3 : m < 2522
  · exact k3.2 m (by omega) (by omega)
  by_cases c4 : m < 3362
  · exact k4.2 m (by omega) (by omega)
  by_cases c5 : m < 4202
  · exact k5.2 m (by omega) (by omega)
  exact k6.2 m (by omega) (by omega)

end OMA.LagariasCert

theorem OMA.solution : OMA.R_RiemannHypothesis_lagarias_criterion_R1_H1_R1.H2 := by
  intro n h2 h5040
  obtain ⟨s, hg⟩ := OMA.LagariasCert.all_good n h2 h5040
  simp only [OMA.LagariasCert.good, Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hk, hs⟩, hlt⟩ := hg
  refine ⟨((OMA.LagariasCert.hl n / 2 ^ 40 : ℕ) : ℚ) / 256, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast hk
  · have h1 : ((OMA.LagariasCert.hl n / 2 ^ 40 : ℕ) : ℚ) ≤
        ((OMA.LagariasCert.hl n : ℕ) : ℚ) / ((2 ^ 40 : ℕ) : ℚ) := Nat.cast_div_le
    have h3 := OMA.LagariasCert.hl_le n
    rw [le_div_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by norm_num)]
    push_cast at h1
    linarith
  · have h4 : ((ArithmeticFunction.sigma 1 n : ℕ) : ℚ) ≤ ((OMA.LagariasCert.spair n s : ℕ) : ℚ) :=
      Nat.cast_le.mpr (OMA.LagariasCert.sigma_le n s hs)
    exact lt_of_le_of_lt h4 hlt
