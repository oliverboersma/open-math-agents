import FormalConjectures.ErdosProblems.«980»
import Mathlib

-- Reduction of Erdős 980, quadratic case.
-- Credit: @marcusbuffett
-- The bound on the nth prime is adapted from @loremcdmx's merged Erdős 5 proof.
namespace OMA.R_Erdos980_erdos_980_variants_erdos_two_R1
open Filter Asymptotics Erdos980
open scoped Classical Topology BigOperators

private lemma leastFacts (p : ℕ)
    (hn : {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y^2 = (a : ZMod p)}.Nonempty) :
    (leastNonresidue 2 p).Prime ∧
    (¬∃ y : ZMod p, y^2 = (leastNonresidue 2 p : ZMod p)) ∧
    ∀ a < leastNonresidue 2 p, ∃ y : ZMod p, y^2 = (a : ZMod p) := by
  let n := leastNonresidue 2 p
  have hm : 0 < n ∧ ¬∃ y : ZMod p, y^2 = (n : ZMod p) := Nat.sInf_mem hn
  have hs : ∀ a < n, ∃ y : ZMod p, y^2 = (a : ZMod p) := by
    intro a ha
    by_cases hz : a = 0
    · subst a; exact ⟨0, by simp⟩
    by_contra h
    have hh : n ≤ a := Nat.sInf_le (s := {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y^2 = (a : ZMod p)}) ⟨by omega, h⟩
    omega
  refine ⟨?_, hm.2, hs⟩
  have h1 : n ≠ 1 := fun e ↦ hm.2 ⟨1, by simp [e]⟩
  by_contra h
  obtain ⟨a, b, ha, hb, e⟩ := (Nat.not_prime_iff_exists_mul_eq (n := n) (by omega)).mp h
  obtain ⟨u, hu⟩ := hs a ha
  obtain ⟨v, hv⟩ := hs b hb
  exact hm.2 ⟨u*v, by rw [mul_pow, hu, hv, ← Nat.cast_mul, e]⟩

private lemma least_eq_pattern (p i : ℕ) :
    leastNonresidue 2 p = Nat.nth Nat.Prime i ↔
    (∀ j < i, ∃ y : ZMod p, y^2 = (Nat.nth Nat.Prime j : ZMod p)) ∧
      ¬ ∃ y : ZMod p, y^2 = (Nat.nth Nat.Prime i : ZMod p) := by
  let q := Nat.nth Nat.Prime
  have hq : ∀ j, 0 < q j := fun j ↦ (Nat.prime_nth_prime j).pos
  constructor
  · intro e
    have hn : {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y^2 = (a : ZMod p)}.Nonempty := by
      by_contra! hempty
      have hz : leastNonresidue 2 p = 0 := by simp [leastNonresidue, hempty]
      have := hq i
      change 0 < Nat.nth Nat.Prime i at this
      omega
    obtain ⟨_, hbad, hsmall⟩ := leastFacts p hn
    rw [e] at hbad hsmall
    exact ⟨fun j hj ↦ hsmall _ ((Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mpr hj), hbad⟩
  · rintro ⟨hprev, hbad⟩
    have hi : q i ∈ {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y^2 = (a : ZMod p)} := ⟨hq i, hbad⟩
    have hle : leastNonresidue 2 p ≤ q i := Nat.sInf_le hi
    obtain ⟨hp, hnot, _⟩ := leastFacts p ⟨_,hi⟩
    apply le_antisymm hle
    by_contra! hlt
    have he := Nat.nth_count hp
    have hj := (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mp (he.trans_lt hlt)
    exact hnot (he ▸ hprev _ hj)

lemma key (m : ℕ) (hm : 16 ≤ m) : Nat.nth Nat.Prime m ≤ m ^ 2 := by
  have hm' : (16:ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Chebyshev.pi_ge (m ^ 2)
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hl2 : Real.log (((m ^ 2 : ℕ) : ℝ)) = 2 * Real.log m := by
    push_cast; rw [Real.log_pow]; norm_num
  have h2 := Real.log_two_gt_d9
  have hA : Real.log (m : ℝ) ≤ m / 8 + 3 := by
    have h8 : Real.log ((m:ℝ) / 8) ≤ m / 8 - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at h8
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h2' := Real.log_two_lt_d9
    linarith
  have h2' := Real.log_two_lt_d9
  have hB : Real.log (((m ^ 2 : ℕ) : ℝ) + 1) ≤ Real.log 2 + 2 * Real.log m := by
    have e : Real.log (2 * (m:ℝ) ^ 2) = Real.log 2 + 2 * Real.log m := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
    rw [← e]
    apply Real.log_le_log (by positivity)
    push_cast; nlinarith
  have hm0 : (0:ℝ) ≤ m := by linarith
  have h3 : (m:ℝ) * Real.log m ≤ (m:ℝ) * (m / 8 + 3) := mul_le_mul_of_nonneg_left hA hm0
  have h4 : (m:ℝ)^2 * 0.69 ≤ (m:ℝ)^2 * Real.log 2 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hlt : (m : ℝ) < (((m ^ 2 : ℕ) : ℝ) * Real.log 2 - Real.log (((m ^ 2 : ℕ) : ℝ) + 1)) / Real.log (((m ^ 2 : ℕ) : ℝ)) := by
    rw [hl2, lt_div_iff₀ (by linarith)]
    push_cast at hB ⊢
    nlinarith
  have hcnt : (m : ℝ) < (Nat.primeCounting (m ^ 2) : ℝ) := lt_of_lt_of_le hlt hpi
  have hcnt' : m < Nat.primeCounting (m ^ 2) := by exact_mod_cast hcnt
  have := Nat.nth_lt_of_lt_count (p := Nat.Prime) (n := m ^ 2 + 1) (k := m) hcnt'
  omega
private lemma seriesSummable :
    Summable (fun i : ℕ ↦ (Nat.nth Nat.Prime i : ℝ) / 2^(i+1)) := by
  have hg := summable_pow_mul_geometric_of_norm_lt_one 2 (r := (2:ℝ)⁻¹) (by norm_num)
  apply hg.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 16] with i hi
  rw [Real.norm_of_nonneg (by positivity), inv_pow, ← div_eq_mul_inv, pow_succ]
  have h : (Nat.nth Nat.Prime i : ℝ) ≤ (i : ℝ)^2 := by exact_mod_cast key i hi
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h (show 0 ≤ (2:ℝ)^i by positivity), mul_nonneg (sq_nonneg (i:ℝ)) (show 0 ≤ (2:ℝ)^i by positivity)]

private lemma cutoff (k p : ℕ) :
    (leastNonresidue 2 p : ℝ) =
      (∑ i ∈ Finset.range k, if leastNonresidue 2 p = Nat.nth Nat.Prime i then (Nat.nth Nat.Prime i : ℝ) else 0) +
      (if Nat.nth Nat.Prime k ≤ leastNonresidue 2 p then (leastNonresidue 2 p : ℝ) else 0) := by
  classical
  let n := leastNonresidue 2 p
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  by_cases h : Nat.nth Nat.Prime k ≤ n
  · rw [if_pos h, Finset.sum_eq_zero, zero_add]
    intro i hi
    have hlt := hmono (Finset.mem_range.mp hi)
    exact if_neg (show n ≠ _ by omega)
  rw [if_neg h, add_zero]
  by_cases hn : n = 0
  · have hall (i : ℕ) : n ≠ Nat.nth Nat.Prime i := by
      have := (Nat.prime_nth_prime i).pos
      omega
    rw [Finset.sum_eq_zero (fun i _ ↦ if_neg (hall i))]
    exact_mod_cast hn
  have hne : {a : ℕ | 0 < a ∧ ¬∃ y : ZMod p, y^2 = (a : ZMod p)}.Nonempty := by
    by_contra! he
    exact hn (by simp [n, leastNonresidue, he])
  have hp := (leastFacts p hne).1
  let j := Nat.count Nat.Prime n
  have hj : Nat.nth Nat.Prime j = n := Nat.nth_count hp
  have hjk : j < k := hmono.lt_iff_lt.mp (hj.trans_lt (by omega))
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hjk)]
  · simp [show leastNonresidue 2 p = Nat.nth Nat.Prime j from hj.symm]
  · intro i hi hij
    exact if_neg fun he ↦ hij (hmono.injective (he.symm.trans hj.symm))

/-- Density of a fixed finite quadratic character pattern at odd primes. -/
def H1 : Prop := ∀ i : ℕ, Tendsto (fun x : ℝ ↦
    (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % 2 = 1 ∧
      (∀ j < i, ∃ y : ZMod p, y ^ 2 = (Nat.nth Nat.Prime j : ZMod p)) ∧
      ¬ ∃ y : ZMod p, y ^ 2 = (Nat.nth Nat.Prime i : ZMod p)).card : ℝ) *
        (Real.log x / x)) atTop (𝓝 (1 / (2 : ℝ) ^ (i + 1)))

/-- The mean contribution from large least nonresidues tends uniformly to zero. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    (∑ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % 2 = 1 ∧
      Nat.nth Nat.Prime k ≤ leastNonresidue 2 p), (leastNonresidue 2 p : ℝ)) *
        (Real.log x / x) ≤ ε

theorem main : H1 → H2 → type_of% @Erdos980.erdos_980.variants.erdos_two := by
  classical
  intro hfreq htail
  let q := Nat.nth Nat.Prime
  let a := fun i : ℕ ↦ (q i : ℝ) / 2^(i+1)
  let C := ∑' i, a i
  let w := fun x : ℝ ↦ Real.log x / x
  let A := fun x : ℝ ↦ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % 2 = 1)
  let B := fun i (x : ℝ) ↦ ((A x).filter (fun p ↦ leastNonresidue 2 p = q i)).card
  let T := fun k (x : ℝ) ↦ ∑ p ∈ (A x).filter (fun p ↦ q k ≤ leastNonresidue 2 p), (leastNonresidue 2 p : ℝ)
  have hb (i) : Tendsto (fun x ↦ (B i x : ℝ) * w x) atTop (𝓝 (1 / (2:ℝ)^(i+1))) := by
    simpa only [B, A, w, q, Finset.filter_filter, least_eq_pattern] using hfreq i
  have ht (ε) (he : 0 < ε) : ∀ᶠ k in atTop, ∀ᶠ x in atTop, T k x * w x ≤ ε := by
    simpa only [T, A, q, w, Finset.filter_filter] using htail ε he
  have splitSum (k) (x) : residueSum 2 x =
      (∑ i ∈ Finset.range k, (q i : ℝ) * B i x) + T k x := by
    change ∑ p ∈ A x, (leastNonresidue 2 p : ℝ) = _
    calc
      _ = ∑ p ∈ A x, ((∑ i ∈ Finset.range k,
        if leastNonresidue 2 p = q i then (q i : ℝ) else 0) +
        if q k ≤ leastNonresidue 2 p then (leastNonresidue 2 p : ℝ) else 0) :=
          Finset.sum_congr rfl fun p _ ↦ cutoff k p
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.sum_filter]
          simp [B, mul_comm]
        · simp [T, Finset.sum_filter]
  have hbfin (k : ℕ) : Tendsto (fun x ↦
      (∑ i ∈ Finset.range k, (q i : ℝ) * B i x) * w x)
      atTop (𝓝 (∑ i ∈ Finset.range k, a i)) := by
    simp only [Finset.sum_mul, mul_assoc]
    apply tendsto_finsetSum
    intro i _
    simpa [a, div_eq_mul_inv] using (hb i).const_mul (q i : ℝ)
  have hsum : Summable a := seriesSummable
  have hC : 0 < C := hsum.tsum_pos (fun i ↦ by dsimp [a]; positivity) 0 (by norm_num [q,a,Nat.nth_prime_zero_eq_two])
  have hlim : Tendsto (fun x ↦ residueSum 2 x * w x) atTop (𝓝 C) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have he : 0 < ε/3 := by positivity
    obtain ⟨k, hk, htk⟩ := ((Metric.tendsto_nhds.mp hsum.hasSum.tendsto_sum_nat _ he).and (ht _ he)).exists
    filter_upwards [Metric.tendsto_nhds.mp (hbfin k) _ he, htk, eventually_gt_atTop (1 : ℝ)] with x hx tx hxp
    have hnn : 0 ≤ T k x * w x := by
      dsimp [T,w]; exact mul_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity) (div_nonneg (Real.log_nonneg hxp.le) (by linarith))
    rw [Real.dist_eq, abs_lt] at hk hx ⊢
    rw [splitSum k x, add_mul]
    constructor <;> linarith
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hd := hlim.div_const C
  rw [div_self hC.ne'] at hd
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  change (residueSum 2 x * (Real.log x / x)) / C = residueSum 2 x / (C * x / Real.log x)
  field_simp [hC.ne', (Real.log_pos hx).ne', show x ≠ 0 by linarith]

end OMA.R_Erdos980_erdos_980_variants_erdos_two_R1
