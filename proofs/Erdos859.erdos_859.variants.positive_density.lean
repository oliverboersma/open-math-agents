import FormalConjectures.ErdosProblems.«859»
import Mathlib.Data.Nat.Periodic

/-! The divisor-sum set is periodic away from zero, with period `t!`. -/

open Filter
open scoped Topology

lemma OMA.periodic_hasPosDensity {p : ℕ → Prop} {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic p d) (hnonempty : ∃ n < d, p n) :
    {n : ℕ | p n}.HasPosDensity := by
  classical
  let count := Nat.count p
  let density : ℝ := (count d : ℝ) / (d : ℝ)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdensity : 0 < density :=
    div_pos (by exact_mod_cast (Nat.pos_of_ne_zero (Nat.count_ne_iff_exists.mpr hnonempty))) hd'
  have hdensity_le : density ≤ 1 := by
    apply (div_le_one hd').mpr
    exact_mod_cast Nat.count_le (p := p) (n := d)
  have hshift (n : ℕ) : Nat.count (fun i ↦ p (i + d)) n = count n :=
    congrArg (fun q : ℕ → Prop => Nat.count q n) (funext hp)
  have hblocks (q r : ℕ) : count (q * d + r) = q * count d + count r := by
    induction q with
    | zero => simp
    | succ q ih =>
      dsimp only [count]
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

theorem OMA.solution : type_of% @Erdos859.erdos_859.variants.positive_density := by
  intro t
  by_cases ht : t = 0
  · rw [ht, Erdos859.erdos_859.variants.trivial_case]
    exact ⟨1, one_pos, Set.HasDensity.univ⟩
  let d := t.factorial
  let p (n : ℕ) := ∃ s : Finset ℕ, (∀ i ∈ s, 0 < i ∧ i ∣ n) ∧ t = ∑ i ∈ s, i
  have hd : 0 < d := Nat.factorial_pos _
  have hpzero : p 0 := ⟨{t}, by simp [Nat.pos_of_ne_zero ht], by simp⟩
  have hstep (n : ℕ) {s : Finset ℕ} (hs : t = ∑ i ∈ s, i)
      {i : ℕ} (hi : i ∈ s) (hi0 : 0 < i) : i ∣ n ↔ i ∣ n + d := by
    have hit : i ≤ t := hs ▸ Finset.single_le_sum (f := id) (fun _ _ ↦ Nat.zero_le _) hi
    exact Nat.dvd_add_iff_left (Nat.dvd_factorial hi0 hit)
  have hp : Function.Periodic p d := by
    intro n
    apply propext
    constructor <;> rintro ⟨s, h, hsum⟩ <;>
      refine ⟨s, fun i hi ↦ ⟨(h i hi).1, ?_⟩, hsum⟩
    · exact (hstep n hsum hi (h i hi).1).mpr (h i hi).2
    · exact (hstep n hsum hi (h i hi).1).mp (h i hi).2
  have hset : {n | p n} = insert 0 (Erdos859.DivisorSumSet t) := by
    ext n
    by_cases hn : n = 0
    · subst n
      exact iff_of_true hpzero (Set.mem_insert _ _)
    · simp only [Set.mem_setOf_eq, Set.mem_insert_iff, or_iff_right hn]
      constructor
      · rintro ⟨s, h, hsum⟩
        exact ⟨s, fun i hi ↦ Nat.mem_divisors.mpr ⟨(h i hi).2, hn⟩, hsum⟩
      · rintro ⟨s, h, hsum⟩
        refine ⟨s, fun i hi ↦ ?_, hsum⟩
        have hdiv := (Nat.mem_divisors.mp (h hi)).1
        exact ⟨Nat.pos_of_dvd_of_pos hdiv (Nat.pos_of_ne_zero hn), hdiv⟩
  have hzero : 0 ∉ Erdos859.DivisorSumSet t := by
    rintro ⟨s, hs, hsum⟩
    have hempty : s = ∅ := Finset.subset_empty.mp (by simpa using hs)
    exact ht (by simpa [hempty] using hsum)
  obtain ⟨density, hdensity, hlim⟩ := OMA.periodic_hasPosDensity hd hp ⟨0, hd, hpzero⟩
  rw [hset] at hlim
  refine ⟨density, hdensity, ?_⟩
  unfold Set.HasDensity at hlim ⊢
  have htend := hlim.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  rw [sub_zero] at htend
  refine htend.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  rw [Set.insert_inter_of_mem (Set.mem_Iio.mpr hn),
    Set.ncard_insert_of_notMem (fun h ↦ hzero h.1)]
  push_cast
  ring
