import OMAReductions.R_Erdos69_erdos_69_R1

/-!
# Multiplicative transform for the Erdős 69 covariance estimate

The power transform of the large-prime count is multiplicative on positive
integers because counts add on coprime inputs. The analytical estimates
correspond to Tao and Teräväinen, arXiv:2512.01739v2, Theorem 3.1 and the
application in Section 5.14.
-/

-- Credit: @1tomaszmiller

namespace OMA.R_Erdos69_erdos_69_R1_H2_R1

open Finset

/-- Uniform one-point equidistribution, together with the count and mean bounds.
The extra cutoff constraint ensures that at most 100 distinct primes can occur. -/
def H1 : Prop :=
  ∀ d : ℝ, 0 < d → d < 1 → ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x ≥ X, ∀ y : ℝ,
    2 * (x : ℝ) < y ^ 101 →
    let w : ℤ → ℕ := fun v => (v.natAbs.primeFactors.filter fun p : ℕ => y < p).card
    let f : ℤ → ℝ := fun v => (1 - d) ^ w v
    let I := Icc (x / 2) x
    let μ := (∑ n ∈ I, f n) / (I.card : ℝ)
    let B := Real.exp (Real.sqrt (Real.log (Real.log x)))
    1 - 100 * d ≤ μ ∧ μ ≤ 1 ∧
    ∀ (Q b : ℕ) (r : ℤ), 0 < Q → (Q : ℝ) ≤ B → |(r : ℝ)| ≤ B →
      let N := I.filter (fun n => n % Q = b % Q)
      (∀ n ∈ N, w ((n : ℤ) + r) ≤ 100) ∧
      |∑ n ∈ N, (f ((n : ℤ) + r) - μ)| ≤ ε * (N.card : ℝ)

/-- Two-point decorrelation for the bounded multiplicative transform on a sequence of scales. -/
def H2 : Prop :=
  ∀ d : ℝ, 0 < d → d < 1 → ∀ ε : ℝ, 0 < ε → ∀ X : ℕ,
    ∃ x : ℕ, X ≤ x ∧ ∃ y : ℝ,
      (x : ℝ) ^ (1 / 200 : ℝ) ≤ y ∧ y ≤ (x : ℝ) ^ (1 / 50 : ℝ) ∧ 2 * (x : ℝ) < y ^ 101 ∧
      let w : ℤ → ℕ := fun v => (v.natAbs.primeFactors.filter fun p : ℕ => y < p).card
      let f : ℤ → ℝ := fun v => (1 - d) ^ w v
      let I := Icc (x / 2) x
      let μ := (∑ n ∈ I, f n) / (I.card : ℝ)
      let B := Real.exp (Real.sqrt (Real.log (Real.log x)))
      ∀ (Q b : ℕ) (r s : ℤ), 0 < Q → (Q : ℝ) ≤ B → |(r : ℝ)| ≤ B → |(s : ℝ)| ≤ B → r ≠ s →
        let N := I.filter (fun n => n % Q = b % Q)
        |∑ n ∈ N, (f ((n : ℤ) + r) - μ) * f ((n : ℤ) + s)| ≤ ε * (N.card : ℝ)

lemma bernoulli_remainder (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (k : ℕ) :
    0 ≤ (1 - t) ^ k - 1 + t * k ∧
    (1 - t) ^ k - 1 + t * k ≤ (k : ℝ) ^ 2 * t ^ 2 := by
  have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hpow (j : ℕ) : 0 ≤ (1 - t) ^ j ∧ (1 - t) ^ j ≤ 1 :=
    ⟨pow_nonneg ht0 _, pow_le_one₀ ht0 (by linarith)⟩
  have hlinear : ∀ j : ℕ, 1 - (1 - t) ^ j ≤ j * t := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Nat.cast_succ]
      have h := mul_le_mul_of_nonneg_left (hpow j).2 ht
      nlinarith only [ih, h]
  have hquad : ∀ j : ℕ, (j : ℝ) * t - (1 - (1 - t) ^ j) ≤ (j : ℝ) ^ 2 * t ^ 2 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hnext : (j.succ : ℝ) * t - (1 - (1 - t) ^ j.succ) =
          (j : ℝ) * t - (1 - (1 - t) ^ j) + t * (1 - (1 - t) ^ j) := by
        rw [pow_succ, Nat.cast_succ]
        ring
      rw [hnext, Nat.cast_succ]
      have h := mul_le_mul_of_nonneg_left (hlinear j) ht
      have hj : 0 ≤ (j : ℝ) * t ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg t)
      nlinarith only [ih, h, hj, sq_nonneg t]
  exact ⟨by linarith only [hlinear k], by linarith only [hquad k]⟩

lemma abs_product_sub_le_erdos69 (a b c d ε : ℝ) (hb : |b| ≤ 100) (hc : |c| ≤ 100)
    (hac : |a - c| ≤ ε) (hbd : |b - d| ≤ ε) : |a * b - c * d| ≤ 200 * ε := by
  have hε := (abs_nonneg (a - c)).trans hac
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by
      rw [show a * b - c * d = (a - c) * b + c * (b - d) by ring]
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ ≤ ε * 100 + 100 * ε := by
      rw [abs_mul, abs_mul]
      exact add_le_add
        (mul_le_mul hac hb (abs_nonneg b) hε)
        (mul_le_mul hc hbd (abs_nonneg (b - d)) (by norm_num))
    _ = 200 * ε := by ring

lemma abs_sum_sub_le_erdos69 {α : Type*} (s : Finset α) (u v : α → ℝ) (B : ℝ)
    (h : ∀ x ∈ s, |u x - v x| ≤ B) :
    |(∑ x ∈ s, u x) - (∑ x ∈ s, v x)| ≤ B * (s.card : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x ∈ s, (u x - v x)| ≤ ∑ x ∈ s, |u x - v x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ s, B := Finset.sum_le_sum h
    _ = B * (s.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]


lemma centered_transform (d μ : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hμlo : 1 - 100 * d ≤ μ) (hμhi : μ ≤ 1) (k : ℕ) (hk : k ≤ 100) :
    let a := (k : ℝ) - (1 - μ) / d
    let c := (μ - (1 - d) ^ k) / d
    |a| ≤ 100 ∧ |c| ≤ 100 ∧ |a - c| ≤ 10000 * d := by
  dsimp only
  have hk' : (k : ℝ) ≤ 100 := by exact_mod_cast hk
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hm0 : 0 ≤ (1 - μ) / d := div_nonneg (sub_nonneg.mpr hμhi) hd.le
  have hm100 : (1 - μ) / d ≤ 100 := (div_le_iff₀ hd).2 (by linarith)
  obtain ⟨hrem0, hrem⟩ := bernoulli_remainder d hd.le hd1 k
  have hflo : 1 - 100 * d ≤ (1 - d) ^ k := by
    have := mul_le_mul_of_nonneg_left hk' hd.le
    linarith
  have hfhi : (1 - d) ^ k ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨?_, ?_⟩, ?_⟩
  · exact (le_div_iff₀ hd).2 (by linarith)
  · exact (div_le_iff₀ hd).2 (by linarith)
  · rw [show (k : ℝ) - (1 - μ) / d - (μ - (1 - d)^k) / d =
        ((1 - d)^k - 1 + d * k) / d by field_simp [hd.ne']; ring]
    rw [abs_of_nonneg (div_nonneg hrem0 hd.le)]
    apply (div_le_iff₀ hd).2
    calc
      (1 - d)^k - 1 + d * k ≤ (k : ℝ)^2 * d^2 := hrem
      _ ≤ (100 : ℝ)^2 * d^2 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hk0 hk' 2) (sq_nonneg d)
      _ = 10000 * d * d := by ring

theorem main : H1 → H2 → OMA.R_Erdos69_erdos_69_R1.H2 := by
  intro hone htwo η hη X
  let d : ℝ := min (1 / 200) (η / 4000000)
  have hd : 0 < d := lt_min (by norm_num) (by positivity)
  have hdsmall : d ≤ 1 / 200 := min_le_left _ _
  have hderr : d ≤ η / 4000000 := min_le_right _ _
  have hd1 : d < 1 := by linarith
  let ε : ℝ := η * d ^ 2 / 4
  have hε : 0 < ε := by positivity
  obtain ⟨X₀, hlarge⟩ := hone d hd hd1 ε hε
  obtain ⟨x, hx, y, hylo, hyhi, hy, hpair⟩ := htwo d hd hd1 ε hε (max X X₀)
  let w : ℤ → ℕ := fun v => (v.natAbs.primeFactors.filter fun p : ℕ => y < p).card
  let f : ℤ → ℝ := fun v => (1 - d) ^ w v
  let I := Icc (x / 2) x
  let μ := (∑ n ∈ I, f n) / (I.card : ℝ)
  let m := (1 - μ) / d
  have hx₀ : X₀ ≤ x := (le_max_right X X₀).trans hx
  obtain ⟨hμlo, hμhi, hshift⟩ := hlarge x hx₀ y hy
  change 1 - 100 * d ≤ μ at hμlo
  change μ ≤ 1 at hμhi
  have hμ0 : 0 ≤ μ := by linarith
  have hm0 : 0 ≤ m := div_nonneg (sub_nonneg.mpr hμhi) hd.le
  have hm100 : m ≤ 100 := (div_le_iff₀ hd).2 (by linarith)
  refine ⟨x, (le_max_left X X₀).trans hx, y, m, hylo, hyhi, hm0, hm100, ?_⟩
  intro Q b r s hQ hQB hr hs hrs
  let N := I.filter (fun n => n % Q = b % Q)
  obtain ⟨hwr, hrmean⟩ := hshift Q b r hQ hQB hr
  obtain ⟨hws, _⟩ := hshift Q b s hQ hQB hs
  have hprod := hpair Q b r s hQ hQB hr hs hrs
  change ∀ n ∈ N, w ((n : ℤ) + r) ≤ 100 at hwr
  change ∀ n ∈ N, w ((n : ℤ) + s) ≤ 100 at hws
  change |∑ n ∈ N, (f ((n : ℤ) + r) - μ)| ≤ ε * (N.card : ℝ) at hrmean
  change |∑ n ∈ N, (f ((n : ℤ) + r) - μ) * f ((n : ℤ) + s)| ≤ ε * (N.card : ℝ) at hprod
  let a : ℤ → ℝ := fun v => (w v : ℝ) - m
  let c : ℤ → ℝ := fun v => (μ - f v) / d
  have hlin (v : ℤ) (hv : w v ≤ 100) :
      |a v| ≤ 100 ∧ |c v| ≤ 100 ∧ |a v - c v| ≤ 10000 * d :=
    centered_transform d μ hd hd1.le hμlo hμhi (w v) hv
  have herr : |(∑ n ∈ N, a ((n : ℤ) + r) * a ((n : ℤ) + s)) -
      (∑ n ∈ N, c ((n : ℤ) + r) * c ((n : ℤ) + s))| ≤
      (200 * (10000 * d)) * (N.card : ℝ) := by
    apply abs_sum_sub_le_erdos69
    intro n hn
    obtain ⟨_, hcr, her⟩ := hlin ((n : ℤ) + r) (hwr n hn)
    obtain ⟨has, _, hes⟩ := hlin ((n : ℤ) + s) (hws n hn)
    exact abs_product_sub_le_erdos69 _ _ _ _ _ has hcr her hes
  have hscaled : |∑ n ∈ N, (f ((n : ℤ) + r) - μ) * (f ((n : ℤ) + s) - μ)| ≤
      (2 * ε) * (N.card : ℝ) := by
    have hsplit : (∑ n ∈ N, (f ((n : ℤ) + r) - μ) * (f ((n : ℤ) + s) - μ)) =
        (∑ n ∈ N, (f ((n : ℤ) + r) - μ) * f ((n : ℤ) + s)) -
          μ * (∑ n ∈ N, (f ((n : ℤ) + r) - μ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    rw [hsplit]
    calc
      |_ - _| ≤ |∑ n ∈ N, (f ((n : ℤ) + r) - μ) * f ((n : ℤ) + s)| +
          |μ * (∑ n ∈ N, (f ((n : ℤ) + r) - μ))| := abs_sub _ _
      _ ≤ ε * (N.card : ℝ) + ε * (N.card : ℝ) := by
        rw [abs_mul, abs_of_nonneg hμ0]
        apply add_le_add hprod
        calc
          μ * |∑ n ∈ N, (f ((n : ℤ) + r) - μ)| ≤
              1 * |∑ n ∈ N, (f ((n : ℤ) + r) - μ)| :=
            mul_le_mul_of_nonneg_right hμhi (abs_nonneg _)
          _ ≤ ε * (N.card : ℝ) := by simpa only [one_mul] using hrmean
      _ = (2 * ε) * (N.card : ℝ) := by ring
  have hsmall : |∑ n ∈ N, c ((n : ℤ) + r) * c ((n : ℤ) + s)| ≤
      (η / 2) * (N.card : ℝ) := by
    have heq : (∑ n ∈ N, (f ((n : ℤ) + r) - μ) * (f ((n : ℤ) + s) - μ)) =
        d ^ 2 * (∑ n ∈ N, c ((n : ℤ) + r) * c ((n : ℤ) + s)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      dsimp only [c]
      field_simp [hd.ne']
      ring
    rw [heq, abs_mul, abs_of_nonneg (sq_nonneg d)] at hscaled
    have hd2 : 0 < d ^ 2 := by positivity
    apply le_of_mul_le_mul_left _ hd2
    calc
      d ^ 2 * |∑ n ∈ N, c ((n : ℤ) + r) * c ((n : ℤ) + s)| ≤
          (2 * ε) * (N.card : ℝ) := hscaled
      _ = d ^ 2 * ((η / 2) * (N.card : ℝ)) := by dsimp only [ε]; ring
  change |∑ n ∈ N, a ((n : ℤ) + r) * a ((n : ℤ) + s)| ≤ η * (N.card : ℝ)
  calc
    |_| ≤ |(∑ n ∈ N, a ((n : ℤ) + r) * a ((n : ℤ) + s)) -
        (∑ n ∈ N, c ((n : ℤ) + r) * c ((n : ℤ) + s))| +
        |∑ n ∈ N, c ((n : ℤ) + r) * c ((n : ℤ) + s)| := by
      simpa only [sub_add_cancel] using
        (abs_add_le ((∑ n ∈ N, a ((n : ℤ) + r) * a ((n : ℤ) + s)) -
          (∑ n ∈ N, c ((n : ℤ) + r) * c ((n : ℤ) + s)))
          (∑ n ∈ N, c ((n : ℤ) + r) * c ((n : ℤ) + s)))
    _ ≤ (200 * (10000 * d)) * (N.card : ℝ) + (η / 2) * (N.card : ℝ) := add_le_add herr hsmall
    _ ≤ (η / 2) * (N.card : ℝ) + (η / 2) * (N.card : ℝ) := by
      have hcoef : 200 * (10000 * d) ≤ η / 2 := by linarith only [hderr]
      exact add_le_add (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg N.card)) le_rfl
    _ = η * (N.card : ℝ) := by ring

end OMA.R_Erdos69_erdos_69_R1_H2_R1
