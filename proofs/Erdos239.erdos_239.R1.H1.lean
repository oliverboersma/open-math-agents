import OMAReductions.R_Erdos239_erdos_239_R1
import Mathlib

-- Step Erdos239.erdos_239.R1.H1: hypothesis H1 of reduction Erdos239.erdos_239.R1
-- Credit: @ivillar

/-! Möbius inversion: `g = f * μ` is multiplicative with `|g p| = 1 - f p` and `|g (p^k)| ≤ 2`,
so `|g d| / d` is multiplicative with local factors at most `1 + (1 - f p) / p + 4 / p^2`.
The Euler product over smooth numbers bounds every partial sum of `|g d| / d` by
`exp (∑ p, ((1 - f p) / p + 4 / p^2))`, which is finite by hypothesis. -/

namespace O2E239H1
open ArithmeticFunction Finset

/-- `f` as an arithmetic function (value `0` at `0`). -/
noncomputable def Fa (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else f n, if_pos rfl⟩

lemma Fa_apply (f : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) : Fa f n = f n := by
  show (if n = 0 then (0:ℝ) else f n) = f n
  exact if_neg hn

lemma Fa_mult (f : ℕ → ℝ) (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1) :
    (Fa f).IsMultiplicative := by
  refine ⟨by rw [Fa_apply f one_ne_zero, h1], ?_⟩
  intro m n hmn
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [zero_mul, ArithmeticFunction.map_zero, zero_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [mul_zero, ArithmeticFunction.map_zero, mul_zero]
  rw [Fa_apply f (Nat.mul_ne_zero hm.ne' hn.ne'), Fa_apply f hm.ne', Fa_apply f hn.ne',
    hmul m n hmn]

/-- The Möbius transform of `f`. -/
noncomputable def G (f : ℕ → ℝ) : ArithmeticFunction ℝ :=
  Fa f * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)

lemma G_prime_pow (f : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    G f (p ^ (j + 1)) = Fa f (p ^ (j + 1)) - Fa f (p ^ j) := by
  rw [G, mul_comm, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.moebius : ArithmeticFunction ℝ) a * Fa f b),
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ x ∈ range j, (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (p ^ (x + 1 + 1)) *
      Fa f (p ^ (j + 1) / p ^ (x + 1 + 1)) = 0 := by
    intro x _
    rw [ArithmeticFunction.intCoe_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp
  rw [Finset.sum_eq_zero hz, ArithmeticFunction.intCoe_apply, ArithmeticFunction.intCoe_apply,
    zero_add, pow_zero, pow_one, ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_one, Nat.div_one, pow_succ, Nat.mul_div_cancel _ hp.pos]
  push_cast
  ring

lemma G_mult (f : ℕ → ℝ) (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1) :
    (G f).IsMultiplicative :=
  (Fa_mult f hmul h1).mul ArithmeticFunction.isMultiplicative_moebius.intCast

lemma G_inv (f : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) : f n = ∑ d ∈ n.divisors, G f d := by
  have h : G f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) = Fa f := by
    rw [G, mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  rw [← ArithmeticFunction.coe_mul_zeta_apply, h, Fa_apply f (by omega)]

lemma G_le_two (f : ℕ → ℝ) (hpm : ∀ n ≥ 1, f n = 1 ∨ f n = -1)
    (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1) {p : ℕ}
    (hp : p.Prime) (k : ℕ) : |G f (p ^ k)| ≤ 2 := by
  have hb : ∀ n, |Fa f n| ≤ 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Fa_apply f hn.ne']
      rcases hpm n hn with h | h <;> simp [h]
  rcases k with _ | j
  · have : G f 1 = 1 := (G_mult f hmul h1).map_one
    simp [this]
  · rw [G_prime_pow f hp j]
    calc |Fa f (p ^ (j + 1)) - Fa f (p ^ j)| ≤ |Fa f (p ^ (j + 1))| + |Fa f (p ^ j)| := abs_sub _ _
      _ ≤ 2 := by linarith [hb (p ^ (j + 1)), hb (p ^ j)]


/-- `|G f d| / d`. -/
noncomputable def H (f : ℕ → ℝ) (d : ℕ) : ℝ := |G f d| / d

lemma H_nonneg (f : ℕ → ℝ) (d : ℕ) : 0 ≤ H f d := div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

section
variable (f : ℕ → ℝ) (hpm : ∀ n ≥ 1, f n = 1 ∨ f n = -1)
  (hmul : ∀ m n, m.Coprime n → f (m*n) = f m * f n) (h1 : f 1 = 1)
include hmul h1

lemma H_one : H f 1 = 1 := by simp [H, (G_mult f hmul h1).map_one]

lemma H_mul {m n : ℕ} (hmn : m.Coprime n) : H f (m * n) = H f m * H f n := by
  simp only [H, (G_mult f hmul h1).map_mul_of_coprime hmn, abs_mul, Nat.cast_mul]
  rw [mul_div_mul_comm]

include hpm

lemma H_pp_le {p : ℕ} (hp : p.Prime) (k : ℕ) : H f (p ^ k) ≤ 2 * (1 / (p:ℝ)) ^ k := by
  unfold H
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpos : (0:ℝ) < (p:ℝ) ^ k := pow_pos hp0 k
  rw [Nat.cast_pow, div_le_iff₀ hpos, one_div, inv_pow, mul_assoc, inv_mul_cancel₀ hpos.ne',
    mul_one]
  exact G_le_two f hpm hmul h1 hp k

lemma H_summ {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖H f (p ^ k)‖) := by
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hr : 1 / (p:ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  have hg : Summable (fun k : ℕ => 2 * (1 / (p:ℝ)) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) hr).mul_left 2
  refine hg.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
  rw [Real.norm_of_nonneg (H_nonneg f _)]
  exact H_pp_le f hpm hmul h1 hp k

omit hmul in
lemma H_p {p : ℕ} (hp : p.Prime) : H f (p ^ (0 + 1)) = (1 - f p) / p := by
  have hg : G f (p ^ (0 + 1)) = f p - 1 := by
    rw [G_prime_pow f hp 0, pow_one, pow_zero, Fa_apply f hp.ne_zero, Fa_apply f one_ne_zero, h1]
  unfold H
  rw [hg, zero_add, pow_one]
  congr 1
  rcases hpm p hp.one_lt.le with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

lemma tail_le {p : ℕ} (hp : p.Prime) (hs2 : Summable (fun k => H f (p ^ (k + 1 + 1)))) :
    ∑' k, H f (p ^ (k + 1 + 1)) ≤ 4 / (p:ℝ) ^ 2 := by
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hr0 : 0 < 1 / (p:ℝ) := by positivity
  have hrh : 1 / (p:ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hr1 : 1 / (p:ℝ) < 1 := by linarith
  have hgs : Summable (fun k : ℕ => 2 * (1 / (p:ℝ)) ^ 2 * (1 / (p:ℝ)) ^ k) :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left _
  have htail : ∑' k, H f (p ^ (k + 1 + 1)) ≤ ∑' k : ℕ, 2 * (1 / (p:ℝ)) ^ 2 * (1 / (p:ℝ)) ^ k := by
    refine hs2.tsum_le_tsum (fun k => ?_) hgs
    calc H f (p ^ (k + 1 + 1)) ≤ 2 * (1 / (p:ℝ)) ^ (k + 1 + 1) := H_pp_le f hpm hmul h1 hp _
      _ = 2 * (1 / (p:ℝ)) ^ 2 * (1 / (p:ℝ)) ^ k := by ring
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1] at htail
  refine htail.trans ?_
  generalize hr : 1 / (p:ℝ) = r at hr0 hrh hr1
  have h4 : 4 / (p:ℝ) ^ 2 = 4 * r ^ 2 := by rw [← hr]; ring
  rw [h4]
  have h1r : 0 < 1 - r := by linarith
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ h1r (by norm_num)]; linarith
  have hr2 : 0 ≤ 2 * r ^ 2 := by positivity
  calc 2 * r ^ 2 * (1 - r)⁻¹ ≤ 2 * r ^ 2 * 2 := mul_le_mul_of_nonneg_left hinv hr2
    _ = 4 * r ^ 2 := by ring

lemma local_le {p : ℕ} (hp : p.Prime) :
    ∑' k, H f (p ^ k) ≤ 1 + ((1 - f p) / p + 4 / (p:ℝ) ^ 2) := by
  have hs : Summable (fun k => H f (p ^ k)) := (H_summ f hpm hmul h1 hp).of_norm
  have hs1 : Summable (fun k => H f (p ^ (k + 1))) :=
    (summable_nat_add_iff (f := fun k => H f (p ^ k)) 1).mpr hs
  have hs2 : Summable (fun k => H f (p ^ (k + 1 + 1))) :=
    (summable_nat_add_iff (f := fun k => H f (p ^ (k + 1))) 1).mpr hs1
  rw [hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add]
  have e0 : H f (p ^ 0) = 1 := by rw [pow_zero]; exact H_one f hmul h1
  rw [e0, H_p f hpm h1 hp]
  linarith [tail_le f hpm hmul h1 hp hs2]
end

theorem main_H1 : ∀ f : ℕ → ℝ, (∀ n ≥ 1, f n = 1 ∨ f n = -1) →
    (∀ m n, m.Coprime n → f (m*n) = f m * f n) → f 1 = 1 →
    Summable (fun p : Nat.Primes => (1 - f p) / (p.val : ℝ)) →
    ∃ g : ℕ → ℝ, Summable (fun d : ℕ => |g d| / d) ∧
      ∀ n ≥ 1, f n = ∑ d ∈ n.divisors, g d := by
  intro f hpm hmul h1 hsum
  refine ⟨G f, ?_, fun n hn => G_inv f hn⟩
  change Summable (fun d => H f d)
  have hle1 : ∀ n ≥ 1, f n ≤ 1 := fun n hn => by rcases hpm n hn with h | h <;> norm_num [h]
  let b : ℕ → ℝ := fun n => if n.Prime then (1 - f n) / n + 4 / (n:ℝ) ^ 2 else 0
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    by_cases hn : n.Prime
    · simp only [b, if_pos hn]
      have := hle1 n hn.one_lt.le
      have : 0 ≤ (1 - f n) / n := div_nonneg (by linarith) (Nat.cast_nonneg _)
      positivity
    · simp only [b, if_neg hn, le_refl]
  have hA : Summable (({p | p.Prime} : Set ℕ).indicator (fun n : ℕ => (1 - f n) / (n:ℝ))) :=
    summable_subtype_iff_indicator.mp hsum
  have hC : Summable (fun n : ℕ => 4 / (n:ℝ) ^ 2) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
    exact (this.mul_left 4).congr (fun n => by ring)
  have hbs : Summable b := by
    refine (hA.add hC).of_nonneg_of_le hb0 (fun n => ?_)
    by_cases hn : n.Prime
    · simp only [b, if_pos hn]
      rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hn)]
    · simp only [b, if_neg hn, Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hn),
        zero_add]
      positivity
  apply summable_of_sum_range_le (H_nonneg f) (c := Real.exp (∑' n, b n))
  intro N
  obtain ⟨_, hhas⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (H_one f hmul h1) (fun hmn => H_mul f hmul h1 hmn) (fun hp => H_summ f hpm hmul h1 hp) N
  have hhas' := (hasSum_subtype_iff_indicator (f := H f) (s := N.smoothNumbers)).mp hhas
  have hA1 : ∑ d ∈ range N, H f d ≤ ∏ p ∈ N.primesBelow, ∑' n, H f (p ^ n) := by
    calc ∑ d ∈ range N, H f d = ∑ d ∈ range N, (N.smoothNumbers).indicator (H f) d := by
          apply sum_congr rfl
          intro d hd
          rcases Nat.eq_zero_or_pos d with rfl | hd0
          · rw [Set.indicator_of_notMem (by simp [Nat.mem_smoothNumbers])]
            simp [H]
          · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hd0 (mem_range.mp hd))]
      _ ≤ _ := sum_le_hasSum _ (fun i _ => Set.indicator_nonneg (fun j _ => H_nonneg f j) i) hhas'
  have hA2 : ∏ p ∈ N.primesBelow, ∑' n, H f (p ^ n) ≤ Real.exp (∑' n, b n) := by
    calc ∏ p ∈ N.primesBelow, ∑' n, H f (p ^ n) ≤ ∏ p ∈ N.primesBelow, Real.exp (b p) := by
          apply prod_le_prod (fun p _ => tsum_nonneg (fun n => H_nonneg f _))
          intro p hp
          have hpr := Nat.prime_of_mem_primesBelow hp
          calc ∑' n, H f (p ^ n) ≤ 1 + ((1 - f p) / p + 4 / (p:ℝ) ^ 2) :=
                local_le f hpm hmul h1 hpr
            _ ≤ Real.exp (b p) := by
                simp only [b, if_pos hpr]
                linarith [Real.add_one_le_exp ((1 - f p) / p + 4 / (p:ℝ) ^ 2)]
      _ = Real.exp (∑ p ∈ N.primesBelow, b p) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (∑' n, b n) := Real.exp_le_exp.mpr (hbs.sum_le_tsum _ (fun i _ => hb0 i))
  linarith

end O2E239H1

theorem OMA.solution : OMA.R_Erdos239_erdos_239_R1.H1 := O2E239H1.main_H1
