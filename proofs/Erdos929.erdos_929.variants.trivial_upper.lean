import FormalConjectures.ErdosProblems.«929»
import Mathlib.Data.Nat.Periodic

/-! The upper bound for Erdős Problem 929 follows from a periodic set of starting points. -/

open Filter
open scoped Topology

lemma OMA.periodic_hasPosDensity {p : ℕ → Prop} {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (hnonempty : ∃ n < d, p n) :
    {n : ℕ | p n}.HasPosDensity := by
  classical
  let count := Nat.count p
  let density : ℝ := (count d : ℝ) / (d : ℝ)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdensity : 0 < density := by
    have hcount : 0 < count d := Nat.pos_of_ne_zero (Nat.count_ne_iff_exists.mpr hnonempty)
    exact div_pos (by exact_mod_cast hcount) hd'
  have hdensity_le : density ≤ 1 := by
    apply (div_le_one hd').mpr
    exact_mod_cast Nat.count_le (p := p) (n := d)
  have hshift (n : ℕ) : Nat.count (fun i ↦ p (i + d)) n = count n :=
    congrArg (fun q : ℕ → Prop => Nat.count q n) (funext hp)
  have hblocks (q r : ℕ) : count (q * d + r) = q * count d + count r := by
    induction q with
    | zero => simp
    | succ q ih =>
      change Nat.count p ((q + 1) * d + r) = (q + 1) * count d + count r
      rw [Nat.succ_mul, add_right_comm (q * d) d r, Nat.count_add', hshift]
      change count (q * d + r) + count d = (q + 1) * count d + count r
      rw [ih, Nat.succ_mul, add_right_comm]
  have hncard (n : ℕ) : ({m : ℕ | p m} ∩ Set.Iio n).ncard = count n := by
    rw [show {m : ℕ | p m} ∩ Set.Iio n =
        (↑((Finset.range n).filter p) : Set ℕ) by ext m; simp [and_comm],
      Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
  have herr : ∀ᶠ n : ℕ in atTop, |(count n : ℝ) / (n : ℝ) - density| ≤ (d : ℝ) / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let r := n % d
    let q := n / d
    have hsplit : q * d + r = n := by simpa [q, r, mul_comm] using Nat.div_add_mod n d
    have hcount : q * count d + count r = count n := hsplit ▸ (hblocks q r).symm
    have hsplit' : (q : ℝ) * (d : ℝ) + (r : ℝ) = (n : ℝ) := by exact_mod_cast hsplit
    have hcount' : (q : ℝ) * (count d : ℝ) + (count r : ℝ) = (count n : ℝ) := by
      exact_mod_cast hcount
    have hd_mul : (d : ℝ) * density = (count d : ℝ) :=
      mul_div_cancel₀ _ hd'.ne'
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hr : (r : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.mod_lt n hd).le
    have hcount_r : (count r : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.count_le (p := p)
    have herror : (count n : ℝ) / (n : ℝ) - density =
        ((count r : ℝ) - (r : ℝ) * density) / (n : ℝ) := by
      apply (eq_div_iff hn'.ne').mpr
      calc
        _ = (count n : ℝ) - (n : ℝ) * density := by field_simp
        _ = _ := by rw [← hcount', ← hsplit', add_mul, mul_assoc, hd_mul]; ring
    rw [herror, abs_div, abs_of_pos hn']
    apply div_le_div_of_nonneg_right _ hn'.le
    apply abs_le.mpr
    constructor
    · have h := mul_le_mul_of_nonneg_left hdensity_le (Nat.cast_nonneg r)
      linarith [Nat.cast_nonneg (α := ℝ) (count r)]
    · have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) r) hdensity.le
      linarith
  have ht : Tendsto (fun n : ℕ ↦ (count n : ℝ) / (n : ℝ) - density) atTop (𝓝 0) := by
    have hu := tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)
    have hl : Tendsto (fun n : ℕ ↦ -((d : ℝ) / n)) atTop (𝓝 0) := by
      simpa only [neg_zero] using hu.neg
    refine hl.squeeze' hu ?_ ?_
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).1
    · exact herr.mono fun n hn ↦ (abs_le.mp hn).2
  refine ⟨density, hdensity, ?_⟩
  simpa [Set.HasDensity, Set.partialDensity, hncard] using ht.add_const density

theorem OMA.solution : type_of% @Erdos929.erdos_929.variants.trivial_upper := by
  intro k
  apply Erdos929.S_le
  let d := (k + 1).factorial
  apply OMA.periodic_hasPosDensity (d := d) (Nat.factorial_pos _)
  · intro n
    apply propext
    simp only [Erdos929.AllHaveSmallPrimeFactor]
    have period (p i : ℕ) (hp : p.Prime) (hle : p ≤ k + 1) :
        p ∣ n + i ↔ p ∣ n + d + i := by
      rw [add_right_comm n d i]
      exact Nat.dvd_add_iff_left (Nat.dvd_factorial hp.pos hle)
    constructor <;> intro h i hi <;> obtain ⟨p, hp, hle, hdvd⟩ := h i hi
    · exact ⟨p, hp, hle, (period p i hp hle).mpr hdvd⟩
    · exact ⟨p, hp, hle, (period p i hp hle).mp hdvd⟩
  · by_cases hk : k = 0
    · exact ⟨0, Nat.factorial_pos _, by simp [Erdos929.AllHaveSmallPrimeFactor, hk]⟩
    · refine ⟨1, ?_, ?_⟩
      · have hdvd : 2 ∣ d := Nat.dvd_factorial (by decide) (by omega)
        exact lt_of_lt_of_le (by decide) (Nat.le_of_dvd (Nat.factorial_pos _) hdvd)
      · intro i hi
        have hi' := Finset.mem_Icc.mp hi
        have hprime : (1 + i).minFac.Prime := Nat.minFac_prime (by omega)
        exact ⟨(1 + i).minFac, hprime,
          (Nat.minFac_le (by omega)).trans (by omega), Nat.minFac_dvd _⟩
