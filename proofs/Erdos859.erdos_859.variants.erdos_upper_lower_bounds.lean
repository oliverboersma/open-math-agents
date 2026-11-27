import FormalConjectures.ErdosProblems.«859»
import Mathlib

section R1Section
/- The natural density is exactly the fraction of one factorial period satisfying the
divisor sum condition. This leaves separate finite counting bounds. -/

-- Reduction Erdos859.erdos_859.variants.erdos_upper_lower_bounds.R1 of Erdős Problem 859 — erdos upper lower bounds
-- Credit: @dk8827
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.Erdos859R1

open Erdos859 Filter
open scoped Classical Topology

-- One period is the interval of positive integers from 1 through t!.
def H1 : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ t : ℕ in atTop,
    1 / Real.log t ^ c <
      (Nat.count (fun n => n + 1 ∈ DivisorSumSet t) t.factorial : ℝ) / t.factorial

def H2 : Prop :=
  ∃ c > (0 : ℝ), ∀ᶠ t : ℕ in atTop,
    (Nat.count (fun n => n + 1 ∈ DivisorSumSet t) t.factorial : ℝ) / t.factorial <
      1 / Real.log t ^ c

lemma successor_mem_periodic (t : ℕ) :
    Function.Periodic (fun n => n + 1 ∈ DivisorSumSet t) t.factorial := by
  intro n
  apply propext
  change n + t.factorial + 1 ∈ DivisorSumSet t ↔ n + 1 ∈ DivisorSumSet t
  rw [show n + t.factorial + 1 = n + 1 + t.factorial by omega]
  have dvd_shift {s : Finset ℕ} (hs : t = ∑ i ∈ s, i) {i : ℕ} (hi : i ∈ s)
      (hipos : 0 < i) : i ∣ n + 1 + t.factorial ↔ i ∣ n + 1 := by
    have hle : i ≤ t := hs ▸ Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hi
    exact (Nat.dvd_add_iff_left (Nat.dvd_factorial hipos hle)).symm
  constructor
  · rintro ⟨s, hs, hsum⟩
    refine ⟨s, fun i hi => ?_, hsum⟩
    have hdiv := (Nat.mem_divisors.mp (hs hi)).1
    have hipos := Nat.pos_of_dvd_of_pos hdiv (by omega)
    exact Nat.mem_divisors.mpr ⟨(dvd_shift hsum hi hipos).mp hdiv, by omega⟩
  · rintro ⟨s, hs, hsum⟩
    refine ⟨s, fun i hi => ?_, hsum⟩
    have hdiv := (Nat.mem_divisors.mp (hs hi)).1
    have hipos := Nat.pos_of_dvd_of_pos hdiv (by omega)
    exact Nat.mem_divisors.mpr ⟨(dvd_shift hsum hi hipos).mpr hdiv, by omega⟩

lemma periodic_count_ratio (p : ℕ → Prop) (d : ℕ)
    (hd : 0 < d) (hp : Function.Periodic p d) :
    Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop
      (𝓝 ((Nat.count p d : ℝ) / d)) := by
  let c : ℝ := Nat.count p d
  have hc : 0 ≤ c := by positivity
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hshift (k : ℕ) : Nat.count (fun i => p (i + d)) k = Nat.count p k := by
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    ext i
    simp only [Finset.mem_filter, hp i]
  have hblocks (q : ℕ) : Nat.count p (q * d) = q * Nat.count p d := by
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.succ_mul, Nat.count_add', hshift, ih, Nat.succ_mul]
  have herror : ∀ᶠ n : ℕ in atTop,
      c / d - c / n ≤ (Nat.count p n : ℝ) / n ∧
      (Nat.count p n : ℝ) / n ≤ c / d + c / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let q := n / d
    have hsplit : q * d + n % d = n := by simpa [q, Nat.mul_comm] using Nat.div_add_mod n d
    have hrem := Nat.mod_lt n hd
    have hlo : q * d ≤ n := by omega
    have hhi : n ≤ (q + 1) * d := by rw [Nat.add_mul, one_mul]; omega
    have hloR : (q : ℝ) * d ≤ n := by exact_mod_cast hlo
    have hhiR : (n : ℝ) ≤ ((q : ℝ) + 1) * d := by exact_mod_cast hhi
    have hclo := (Nat.count_monotone p) hlo
    have hchi := (Nat.count_monotone p) hhi
    rw [hblocks] at hclo hchi
    have hcloR : (q : ℝ) * c ≤ Nat.count p n := by
      dsimp [c]
      exact_mod_cast hclo
    have hchiR : (Nat.count p n : ℝ) ≤ ((q : ℝ) + 1) * c := by
      dsimp [c]
      exact_mod_cast hchi
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hloRatio : (q : ℝ) ≤ (n : ℝ) / d := (le_div_iff₀ hdR).mpr hloR
    have hhiRatio : (n : ℝ) / d ≤ (q : ℝ) + 1 := (div_le_iff₀ hdR).mpr hhiR
    have hloScaled := mul_le_mul_of_nonneg_right hloRatio hc
    have hhiScaled := mul_le_mul_of_nonneg_right hhiRatio hc
    constructor
    · apply (le_div_iff₀ hnR).2
      calc
        (c / d - c / n) * n = (n / d) * c - c := by field_simp
        _ ≤ Nat.count p n := by linarith
    · apply (div_le_iff₀ hnR).2
      calc
        (Nat.count p n : ℝ) ≤ (n / d) * c + c := by linarith
        _ = (c / d + c / n) * n := by field_simp
  have hcOverN := tendsto_const_div_atTop_nhds_zero_nat c
  have hconst : Tendsto (fun _ : ℕ => c / d) atTop (𝓝 (c / d)) := tendsto_const_nhds
  have hlower := hconst.sub hcOverN
  have hupper := hconst.add hcOverN
  rw [sub_zero] at hlower
  rw [add_zero] at hupper
  exact hlower.squeeze' hupper (herror.mono fun _ hn => hn.1) (herror.mono fun _ hn => hn.2)

lemma divisor_sum_density (t : ℕ) :
    (DivisorSumSet t).HasDensity
      ((Nat.count (fun n => n + 1 ∈ DivisorSumSet t) t.factorial : ℝ) / t.factorial) := by
  let S := DivisorSumSet t
  let p (n : ℕ) := n ∈ S
  let c : ℝ := if p 0 then 1 else 0
  have hratio := periodic_count_ratio (fun n => p (n + 1)) t.factorial
    (Nat.factorial_pos _) (successor_mem_periodic t)
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat c).comp (tendsto_add_atTop_nat 1)
  have hscale : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
    have hu := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hu
    rw [sub_zero] at hlim
    refine hlim.congr fun n => ?_
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hl := (hratio.mul hscale).add hsmall
  simp only [mul_one, add_zero] at hl
  unfold Set.HasDensity
  apply (tendsto_add_atTop_iff_nat 1).1
  refine hl.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hcount (k : ℕ) : (S ∩ Set.Iio k).ncard = Nat.count p k := by
    rw [Nat.count_eq_card_filter_range, ← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [p, and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  rw [hcount, Nat.count_succ']
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnext : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, c]
  split_ifs <;> field_simp

theorem main : H1 → H2 → type_of% @Erdos859.erdos_859.variants.erdos_upper_lower_bounds := by
  rintro ⟨c₁, hc₁, hlower⟩ ⟨c₂, hc₂, hupper⟩
  refine ⟨c₁, hc₁, c₂, hc₂, 0, ?_⟩
  filter_upwards [hlower, hupper] with t ht₁ ht₂
  exact ⟨_, divisor_sum_density t, ht₁, ht₂⟩

end OMA.Erdos859R1
end R1Section

section H1Section
/- Construct a practical divisor by requiring one prime factor from each
of two logarithmic windows at every scale. The Chinese remainder theorem
multiplies their densities. The first Mertens estimate below is adapted
from @senamakel's Romanoff proof (#2394), via @marcusbuffett's Erdős 688
step (#3586). The practical-divisor construction and counting proof are new. -/
noncomputable section
open Finset Filter Real Erdos859
open scoped Topology Classical
namespace PracticalDensity

def Covers (m : ℕ) := ∀ t ≤ m, ∃ S : Finset ℕ, (∀ s ∈ S, s ∣ m) ∧ ∑ s ∈ S, s = t

lemma coversTwo (k : ℕ) : Covers (2^k) := by
  intro t ht
  let L := t.bitIndices
  let F : Finset ℕ := ⟨L,Nat.bitIndices_nodup⟩
  refine ⟨F.image (fun i => 2^i),?_,?_⟩
  · rintro _ hs
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hs
    apply pow_dvd_pow
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp ((Nat.two_pow_le_of_mem_bitIndices hi).trans ht)
  · rw [sum_image (fun i _ j _ h => (Nat.pow_right_injective (by decide : 1<2)) h)]
    exact Nat.sum_map_two_pow_bitIndices t

lemma coversMul {m p : ℕ} (hm : Covers m) (hp : p.Prime) (hc : ¬p∣m) (hle : p ≤ m+1) :
    Covers (m*p) := by
  intro t ht
  obtain ⟨A,hA,sa⟩ := hm (t%p) (by have := Nat.mod_lt t hp.pos; omega)
  obtain ⟨B,hB,sb⟩ := hm (t/p) ((Nat.div_le_div_right ht).trans (by rw [Nat.mul_div_cancel _ hp.pos]))
  let f (b:ℕ) := p*b
  have dis : Disjoint A (B.image f) := by
    rw [Finset.disjoint_left]
    intro a ha hab
    obtain ⟨b,_,rfl⟩ := mem_image.mp hab
    exact hc (dvd_trans (dvd_mul_right _ _) (hA _ ha))
  refine ⟨A ∪ B.image f,?_,?_⟩
  · intro a ha
    rcases mem_union.mp ha with h|h
    · exact (hA _ h).trans (dvd_mul_right _ _)
    · obtain ⟨b,hb,rfl⟩ := mem_image.mp h
      simpa [f,Nat.mul_comm] using Nat.mul_dvd_mul_left p (hB _ hb)
  · rw [sum_union dis,sum_image (fun i _ j _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
    change (∑ a ∈ A,a) + ∑ b ∈ B,p*b = _
    rw [← mul_sum,sa,sb,Nat.mod_add_div]

lemma covered {m n t : ℕ} (hm : Covers m) (hd : m ∣ n) (hn : n ≠ 0) (ht : t ≤ m) :
    n ∈ DivisorSumSet t := by
  obtain ⟨S,hS,hs⟩ := hm t ht
  exact ⟨S,fun a ha => Nat.mem_divisors.mpr ⟨(hS a ha).trans hd,hn⟩,hs.symm⟩

def join {a b : ℕ} (h : a.Coprime b) (A : Finset (ZMod a)) (B : Finset (ZMod b)) :=
  (A ×ˢ B).map (ZMod.chineseRemainder h).symm.toEquiv.toEmbedding

lemma card_join {a b : ℕ} (h : a.Coprime b) (A : Finset (ZMod a)) (B : Finset (ZMod b)) :
    (join h A B).card = A.card*B.card := by simp [join]

lemma join_cast {a b n : ℕ} {h : a.Coprime b} {A : Finset (ZMod a)} {B : Finset (ZMod b)}
    (hn : (n:ZMod (a*b)) ∈ join h A B) : (n : ZMod a) ∈ A ∧ (n : ZMod b) ∈ B := by
  obtain ⟨v,hv,he⟩ := mem_map.mp hn
  have hs : v = ((n:ZMod a),(n:ZMod b)) := by
    change (ZMod.chineseRemainder h).symm v = n at he
    have hv := congrArg (ZMod.chineseRemainder h) he
    rw [RingEquiv.apply_symm_apply, map_natCast] at hv
    exact hv
  exact mem_product.mp (hs ▸ hv)

open OMA.Erdos859R1

lemma density_of_good (t d : ℕ) (hd : 0<d) (G : Finset (ZMod d))
    (hg : ∀ n : ℕ, ((n+1:ℕ):ZMod d) ∈ G → n+1 ∈ DivisorSumSet t) :
    (G.card:ℝ)/d ≤ (Nat.count (fun n => n+1 ∈ DivisorSumSet t) t.factorial : ℝ)/t.factorial := by
  letI : NeZero d := ⟨hd.ne'⟩
  let P (i : ℕ) := ((i+1:ℕ):ZMod d) ∈ G
  letI : DecidablePred P := fun i => Classical.propDecidable (P i)
  have period : Function.Periodic P d := by
    intro n; simp [P,add_assoc,add_left_comm,add_comm]
  have cnt : Nat.count P d = G.card := by
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_bij (fun i _ => ((i+1:ℕ):ZMod d))
    · intro i hi; exact (mem_filter.mp hi).2
    · intro i hi j hj he
      have e : (i:ZMod d) = (j:ZMod d) := by simpa using he
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hi).1),
        Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hj).1)] using congrArg ZMod.val e
    · intro y hy
      let x := (y-1).val
      have hxy : ((x+1:ℕ):ZMod d) = y := by simp [x]
      exact ⟨x,mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),show P x from (show ((x+1:ℕ):ZMod d) ∈ G from hxy.symm ▸ hy)⟩,hxy⟩
  have h₁ := periodic_count_ratio P d hd period
  rw [← cnt]
  apply le_of_tendsto_of_tendsto' h₁ (periodic_count_ratio _ t.factorial (Nat.factorial_pos _) (successor_mem_periodic t))
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Nat.count_mono_left (p:=P) (fun k _ => hg k) : Nat.count P n ≤ _)

end PracticalDensity

open scoped Classical

namespace OMALib.MertensH1

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

end OMALib.MertensH1
open Finset Filter Real OMALib.MertensH1
open scoped Topology Classical
namespace PracticalDensity

def W (x k : ℕ) := Nat.primesLE (x^(k+1)) \ Nat.primesLE (x^k)

lemma memW {p x k : ℕ} : p ∈ W x k ↔ p.Prime ∧ x^k < p ∧ p ≤ x^(k+1) := by
  constructor
  · intro h
    obtain ⟨hi,lo⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hu,hp⟩ := Nat.mem_primesLE.mp hi
    exact ⟨hp,lt_of_not_ge (fun hh => lo (Nat.mem_primesLE.mpr ⟨hh,hp⟩)),hu⟩
  · rintro ⟨hp,hl,hu⟩
    exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hu,hp⟩,fun hn => hl.not_ge (Nat.mem_primesLE.mp hn).1⟩
-- The weighted prime sum on this window is log x up to a bounded error.
lemma windowMass : ∀ᶠ x : ℕ in atTop, ∀ k ≤ 3, (1:ℝ)/8 ≤ ∑ p ∈ W x k, (p:ℝ)⁻¹ := by
  have grow : Tendsto (fun x : ℕ => log (x:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_ge_atTop (4*mertens1Const),eventually_ge_atTop 2] with x hlarge hx k hk
  have hxpos : 0 < log (x:ℝ) := log_pos (by exact_mod_cast (show 1<x by omega))
  have hsub : Nat.primesLE (x^k) ⊆ Nat.primesLE (x^(k+1)) := by
    intro p hp
    obtain ⟨lt,pr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨lt.trans (Nat.pow_le_pow_right (by omega) (by omega)),pr⟩
  have hs := sum_sdiff hsub (f := fun p:ℕ => log (p:ℝ)/p)
  change (∑ p ∈ W x k, _) + _ = _ at hs
  have hlo := (abs_le.mp (abs_sum_log_div_sub_log_le_nat (x^(k+1)))).1
  have hhi := (abs_le.mp (abs_sum_log_div_sub_log_le_nat (x^k))).2
  rw [Nat.cast_pow,log_pow] at hlo hhi
  push_cast at hlo
  have hbd : (∑ p ∈ W x k, log (p:ℝ)/p) ≤ (4*log x)*(∑ p ∈ W x k, (p:ℝ)⁻¹) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨pr,_,hlt⟩ := memW.mp hp
    have hh := log_le_log (show 0<(p:ℝ) by exact_mod_cast pr.pos)
      (show (p:ℝ) ≤ (x:ℝ)^(k+1) by exact_mod_cast hlt)
    rw [log_pow] at hh
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (show k+1 ≤ 4 by omega)) hxpos.le)
  apply le_of_mul_le_mul_left (a := 4*log (x:ℝ)) _ (by positivity)
  linarith only [hs,hlo,hhi,hbd,hlarge]

set_option maxHeartbeats 800000 in
lemma groupEvent (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hm : (1:ℝ)/8 ≤ ∑ p ∈ P, (p:ℝ)⁻¹) :
    ∃ G : Finset (ZMod (∏ p ∈ P,p)), (∏ p ∈ P,p) ≤ 10*G.card ∧
      ∀ n : ℕ, (n:ZMod (∏ p ∈ P,p)) ∈ G → ∃ p ∈ P, p∣n := by
  classical
  let d := ∏ p ∈ P,p
  have hd : 0<d := Finset.prod_pos fun p hp => (hP p hp).pos
  letI : NeZero d := ⟨hd.ne'⟩
  let U := (univ : Finset (ZMod d)ˣ).image (fun u : (ZMod d)ˣ => (u:ZMod d))
  let G := (univ : Finset (ZMod d)) \ U
  have cards : G.card+ d.totient = d := by
    have h := card_sdiff_add_card_eq_card (subset_univ U)
    simpa [G,U,Finset.card_image_of_injective _ Units.val_injective,ZMod.card] using h
  have frac := congrArg (fun q : ℚ => (q:ℝ)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at frac
  have fact : d.primeFactors = P := Nat.primeFactors_prod hP
  rw [fact] at frac
  have hpr : (∏ p ∈ P, (1-(p:ℝ)⁻¹)) ≤ exp (-(∑ p ∈ P, (p:ℝ)⁻¹)) := by
    rw [← sum_neg_distrib,Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have h : (1:ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ h)
    · intro p hp; linarith [Real.add_one_le_exp (-(p:ℝ)⁻¹)]
  have hsmall : exp (-(∑ p ∈ P, (p:ℝ)⁻¹)) ≤ 9/10 :=
    (Real.exp_le_exp.mpr (neg_le_neg hm)).trans (by
      rw [Real.exp_neg,inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith [Real.add_one_le_exp ((1:ℝ)/8)])
  refine ⟨G,?_,?_⟩
  · have h := mul_le_mul_of_nonneg_left (hpr.trans hsmall) (Nat.cast_nonneg (α:=ℝ) d)
    try simp only [one_div] at frac
    exact_mod_cast (show (d:ℝ) ≤ 10*(G.card:ℝ) by
      have cc : (G.card:ℝ)+d.totient=d := by exact_mod_cast cards
      linarith)
  · intro n hn
    have hnot : ¬ n.Coprime d := by
      intro hc
      obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime n d).mpr hc
      have huU : (n:ZMod d) ∈ U := by
        dsimp only [U]
        rw [Finset.mem_image]
        exact ⟨u,Finset.mem_univ _,hu⟩
      exact ((Finset.mem_sdiff.mp (show (n:ZMod d) ∈ (univ : Finset (ZMod d)) \ U from hn)).2 huU)
    obtain ⟨p,pr,pn,pd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hp : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨pr,pd,hd.ne'⟩
    exact ⟨p,fact ▸ hp,pn⟩

end PracticalDensity


noncomputable section
open Finset Filter Real Erdos859
open scoped Topology Classical
namespace PracticalDensity

-- Each favorable residue contains a practical divisor at least cap.
-- All primes used in the modulus are bounded by bound.
def Stage (bound cap cost : ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∃ G : Finset (ZMod d), d ≤ cost*G.card ∧
    (∀ p : ℕ, p.Prime → p ∣ d → p ≤ bound) ∧
    ∀ n : ℕ, (n:ZMod d) ∈ G → ∃ m : ℕ, m ∣ d ∧ m ∣ n ∧ cap ≤ m ∧ Covers m

lemma extendStage {bound cap cost top : ℕ} (h : Stage bound cap cost) (hst : bound ≤ top)
    (ht : top ≤ cap) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ bound < p ∧ p ≤ top)
    (hmass : (1:ℝ)/8 ≤ ∑ p ∈ P, (p:ℝ)⁻¹) : Stage top (cap*bound) (cost*10) := by
  obtain ⟨d,hd,G,hG,hs,cover⟩ := h
  let D := ∏ p ∈ P,p
  have pr : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hD : 0<D := Finset.prod_pos fun p hp => (pr p hp).pos
  have hfac : D.primeFactors=P := Nat.primeFactors_prod pr
  have cp (p) (hp : p ∈ P) : d.Coprime p := (Nat.Prime.coprime_iff_not_dvd (pr p hp)).mpr
    (fun pd => ((hP p hp).2.1).not_ge (hs p (pr p hp) pd)) |>.symm
  have cop : d.Coprime D := Nat.coprime_prod_right_iff.mpr cp
  obtain ⟨H,size,hit⟩ := groupEvent P pr hmass
  refine ⟨d*D,mul_pos hd hD,join cop G H,?_,?_,?_⟩
  · rw [card_join]
    calc d*D ≤ (cost*G.card)*(10*H.card) := Nat.mul_le_mul hG size
         _ = _ := by ring
  · intro p hp pd
    rcases hp.dvd_mul.mp pd with pd|pd
    · exact (hs p hp pd).trans hst
    · have hpP : p ∈ P := hfac ▸ Nat.mem_primeFactors.mpr ⟨hp,pd,hD.ne'⟩
      exact (hP p hpP).2.2
  · intro n hn
    obtain ⟨hold,hnew⟩ := join_cast hn
    obtain ⟨m,md,mn,hcap,hcov⟩ := cover n hold
    obtain ⟨p,hp,pn⟩ := hit n hnew
    have pm : ¬p∣m := fun dvd => (hP p hp).2.1.not_ge (hs _ (pr p hp) (dvd.trans md))
    exact ⟨m*p,Nat.mul_dvd_mul md (Finset.dvd_prod_of_mem id hp),
      ((pr p hp).coprime_iff_not_dvd.mpr pm).symm.mul_dvd_of_dvd_of_dvd mn pn,
      Nat.mul_le_mul hcap (hP p hp).2.1.le,
      coversMul hcov (pr p hp) pm (by have := (hP p hp).2.2; omega)⟩

def Y (Q j : ℕ) := Q^(2^j)

lemma y_succ (Q j : ℕ) : Y Q (j+1) = (Y Q j)^2 := by simp [Y,pow_succ,pow_mul]

lemma buildStages (K : ℕ) (hQ : 2 ≤ 2^K)
    (hm : ∀ x ≥ 2^K, ∀ k ≤ 3, (1:ℝ)/8 ≤ ∑ p ∈ W x k, (p:ℝ)⁻¹) (j : ℕ) :
    Stage ((Y (2^K) j)^2) ((Y (2^K) j)^4) ((2^K)^4*100^j) := by
  let Q := 2^K
  induction j with
  | zero =>
    simp only [Y,pow_zero,pow_one,mul_one]
    let d := (2^K)^4
    refine ⟨d,by dsimp [d]; positivity,{0},by simp [d],?_,?_⟩
    · intro p hp pd
      have h : p ∣ 2 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow pd)
      have he := (Nat.dvd_prime Nat.prime_two).mp h
      have hx := Nat.pow_le_pow_right (by omega : 0<2^K) (by decide : 1≤2)
      simp at hx
      rcases he with he|he <;> omega
    · intro n hn
      have hd : d ∣ n := (ZMod.natCast_eq_zero_iff _ _).mp (mem_singleton.mp hn)
      exact ⟨d,dvd_rfl,hd,le_rfl,by dsimp [d]; rw [← pow_mul]; exact coversTwo _⟩
  | succ j ih =>
    let x := Y (2^K) j
    have hx₀ : 2^K ≤ x := Nat.le_self_pow (by positivity) _
    have hx : 0<x := (by omega : 0<2^K).trans_le hx₀
    have hpow (a b : ℕ) (h : a≤b) : x^a ≤ x^b := Nat.pow_le_pow_right hx h
    have s₁ := extendStage ih (hpow 2 3 (by decide)) (hpow 3 4 (by decide))
      (W x 2) (fun p hp => memW.mp hp) (hm x hx₀ 2 (by decide))
    have s₂ := extendStage s₁ (hpow 3 4 (by decide)) (Nat.le_mul_of_pos_right _ (pow_pos hx 2))
      (W x 3) (fun p hp => memW.mp hp) (hm x hx₀ 3 (by decide))
    rw [y_succ]
    change Stage ((x^2)^2) ((x^2)^4) (_*100^(j+1))
    obtain ⟨d,hd,G,size,hs,cover⟩ := s₂
    refine ⟨d,hd,G,?_,?_,?_⟩
    · convert size using 1 <;> ring
    · convert hs using 2 <;> ring
    · intro n hn
      obtain ⟨m,md,mn,hm,hc⟩ := cover n hn
      refine ⟨m,md,mn,le_trans ?_ hm,hc⟩
      calc (x^2)^4 = x^8 := by ring
           _ ≤ x^9 := hpow 8 9 (by decide)
           _ = _ := by change _ = (x^4*x^2)*x^3; ring
end PracticalDensity

noncomputable section
open Finset Filter Real Erdos859 PracticalDensity
open scoped Topology Classical

theorem h1_proof : OMA.Erdos859R1.H1 := by
  obtain ⟨L,hL⟩ := eventually_atTop.mp windowMass
  let K := L+2
  let Q := 2^K
  have hLQ : L ≤ Q := by
    have := Nat.lt_two_pow_self (n := K); dsimp [Q,K] at *; omega
  have hQ : 4 ≤ Q := by
    exact Nat.pow_le_pow_right (by decide : 0<2) (show 2≤K by dsimp [K]; omega)
  have hQ' : (4:ℝ) ≤ Q := by exact_mod_cast hQ
  have hlogQ : 1 ≤ log Q := by
    have := Real.log_le_log (by norm_num : (0:ℝ)<4) hQ'
    have he := Real.log_two_gt_d9
    rw [show (4:ℝ) = 2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)] at this
    linarith
  have grow : Tendsto (fun t:ℕ => log (t:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨8,by norm_num,?_⟩
  filter_upwards [grow.eventually_gt_atTop ((Q:ℝ)^4),eventually_gt_atTop (Q^4)] with t hlog ht
  have ht' : 0 < t := (Nat.zero_le _).trans_lt ht
  have hex : ∃ j : ℕ, t ≤ (Y Q j)^4 := by
    refine ⟨t,?_⟩
    have h : t ≤ 2^t := Nat.lt_two_pow_self.le
    have h' : 2^t ≤ Y Q t := by
      dsimp [Y]
      exact (Nat.pow_le_pow_left (by omega : 2≤Q) _).trans (Nat.pow_le_pow_right (by omega) h)
    exact (h.trans h').trans (Nat.le_self_pow (by decide : 4 ≠ 0) _)
  let j := Nat.find hex
  obtain ⟨d,hd,G,hsize,_,hgood⟩ := buildStages K (by omega : 2≤Q)
    (fun x hx => hL x (hLQ.trans hx)) j
  have coversT := Nat.find_spec hex
  change t ≤ (Y Q j)^4 at coversT
  have hdensity := density_of_good t d hd G (fun n hn => by
    obtain ⟨m,_,mn,hcap,hc⟩ := hgood (n+1) hn
    exact covered hc mn (by omega) (coversT.trans hcap))
  have htwo : (2:ℝ)^j ≤ log t := by
    obtain ⟨k,hk⟩ : ∃ k, j=k+1 := Nat.exists_eq_succ_of_ne_zero (by
      intro hz; rw [hz] at coversT; simp [Y] at coversT; omega)
    have hprev : (Y Q k)^4 < t := lt_of_not_ge (Nat.find_min hex (show k<j by omega))
    have hpos : 0< ((Y Q k)^4:ℕ) := by dsimp [Y]; positivity
    have hb := log_le_log (show (0:ℝ) < ((Y Q k)^4:ℕ) by exact_mod_cast hpos)
      (show (((Y Q k)^4:ℕ):ℝ) ≤ t by exact_mod_cast hprev.le)
    dsimp [Y] at hb
    push_cast at hb
    rw [log_pow,log_pow] at hb
    push_cast at hb
    rw [hk,pow_succ]
    have hr : (2:ℝ)^k ≤ 2^k * log (Q:ℝ) := le_mul_of_one_le_right (by positivity) hlogQ
    linarith only [hr,hb,show (0:ℝ) ≤ 2^k by positivity]
  have hlogp : 0 < log t := (by positivity : (0:ℝ)<2^j).trans_le htwo
  have hcost : (100:ℝ)^j ≤ (log t)^7 := calc
    _ ≤ ((2:ℝ)^7)^j := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = ((2:ℝ)^j)^7 := by rw [← pow_mul, Nat.mul_comm, pow_mul]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) htwo _
  have hgap : (Q:ℝ)^4*100^j < (log t)^8 := calc
    _ ≤ (Q:ℝ)^4 * (log t)^7 := mul_le_mul_of_nonneg_left hcost (by positivity)
    _ < (log t)*(log t)^7 := mul_lt_mul_of_pos_right hlog (by positivity)
    _ = _ := by ring
  apply lt_of_lt_of_le _ hdensity
  rw [show (8:ℝ) = ((8:ℕ):ℝ) by norm_num,Real.rpow_natCast,
    div_lt_div_iff₀ (pow_pos hlogp _) (show (0:ℝ)<d by exact_mod_cast hd),one_mul]
  have hsize' : (d:ℝ) ≤ (Q:ℝ)^4*100^j*G.card := by exact_mod_cast hsize
  have hc : 0 < (G.card:ℝ) := by
    have : G.card ≠ 0 := by intro hz; rw [hz,mul_zero] at hsize; omega
    exact_mod_cast Nat.pos_of_ne_zero this
  exact hsize'.trans_lt (by simpa [mul_comm] using mul_lt_mul_of_pos_right hgap hc)
end
end
end
end H1Section

section H2Section
/- The dyadic divisor estimate is adapted from @marcusbuffett’s Erdős 692 proof (#3559), including the Mertens estimates credited there to @senamakel (#2394). -/
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

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring

theorem abs_mertensG_sub_le (N : ℕ) (hN : 2 ≤ N) :
    |mertensG N - mertensG 2| ≤ (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs := mertensG_step n hn
    calc |mertensG (n + 1) - mertensG 2|
        = |(mertensG (n + 1) - mertensG n) + (mertensG n - mertensG 2)| := by ring_nf
      _ ≤ |mertensG (n + 1) - mertensG n| + |mertensG n - mertensG 2| := abs_add_le _ _
      _ ≤ _ := add_le_add hs ih
      _ = _ := by push_cast; ring


/-- The constant in Mertens' second theorem over the naturals. -/
noncomputable def mertens2NatConst : ℝ :=
  |mertensG 2| + (2 * mertens1Const + 1) / Real.log 2

theorem mertens1Const_nonneg : 0 ≤ mertens1Const := by
  have := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertens1Const; linarith

/-- **Mertens' second theorem** over the naturals: for `N ≥ 2`,
`|∑_{p ≤ N} 1 / p - log log N| ≤ mertens2NatConst`. -/
theorem abs_sum_inv_sub_log_log_le_nat (N : ℕ) (hN : 2 ≤ N) :
    |∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N)| ≤ mertens2NatConst := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlN0 : 0 < Real.log N := by linarith
  have hG := abs_mertensG_sub_le N hN
  have hR := abs_sum_log_div_sub_log_le_nat N
  have hC := mertens1Const_nonneg
  have e : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N) =
      mertensG 2 + (mertensG N - mertensG 2) +
        ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N := by
    rw [show mertensG 2 + (mertensG N - mertensG 2) = mertensG N by ring]
    unfold mertensG; ring
  rw [e]
  have h1 : |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| ≤
      mertens1Const / Real.log 2 := by
    rw [abs_div, abs_of_pos hlN0]
    calc _ ≤ mertens1Const / Real.log N := div_le_div_of_nonneg_right hR hlN0.le
      _ ≤ mertens1Const / Real.log 2 := div_le_div_of_nonneg_left hC hl2 hlN
  have h2 : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
      (mertens1Const + 1) / Real.log 2 := by
    have : 0 ≤ 1 / Real.log N := by positivity
    have : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
        (mertens1Const + 1) * (1 / Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    rw [div_eq_mul_one_div (mertens1Const + 1)]
    exact this
  have h3 : mertens2NatConst =
      |mertensG 2| + (mertens1Const + 1) / Real.log 2 + mertens1Const / Real.log 2 := by
    unfold mertens2NatConst; ring
  rw [h3]
  calc _ ≤ |mertensG 2 + (mertensG N - mertensG 2)| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := abs_add_le _ _
    _ ≤ |mertensG 2| + |mertensG N - mertensG 2| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := by
      gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

theorem log_log_floor_le (x : ℝ) (hx : 2 ≤ x) :
    Real.log (Real.log ⌊x⌋₊) ≤ Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ Real.log (Real.log ⌊x⌋₊) + 1 := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hN2r : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN2
  have hlN : Real.log 2 ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by norm_num) hN2r
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN0 : 0 < Real.log ⌊x⌋₊ := by linarith
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x (by linarith)
  have hlx : 0 < Real.log x := by linarith
  constructor
  · exact Real.log_le_log hlN0 h1
  · have hq := Real.log_le_sub_one_of_pos (div_pos hlx hlN0)
    rw [Real.log_div hlx.ne' hlN0.ne'] at hq
    have : Real.log x / Real.log ⌊x⌋₊ - 1 ≤ 1 := by
      rw [div_sub_one hlN0.ne', div_le_iff₀ hlN0]; linarith
    linarith

/-- The constant in Mertens' second theorem over the reals. -/
noncomputable def mertens2Const : ℝ := mertens2NatConst + 1

/-- **Mertens' second theorem.** For real `x ≥ 2`,
`|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const`. -/
theorem abs_sum_inv_sub_log_log_le (x : ℝ) (hx : 2 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ mertens2Const := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h := abs_sum_inv_sub_log_log_le_nat ⌊x⌋₊ hN2
  obtain ⟨h1, h2⟩ := log_log_floor_le x hx
  unfold mertens2Const
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' second theorem**, existential form. -/
theorem mertens2 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ C :=
  ⟨mertens2Const, abs_sum_inv_sub_log_log_le⟩

theorem log_one_sub_inv_bounds {p : ℕ} (hp : p.Prime) :
    -(1 / (p : ℝ)) - Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        Real.log (1 - 1 / (p : ℝ)) ∧
      Real.log (1 - 1 / (p : ℝ)) ≤ -(1 / (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 - 1 / (p : ℝ))⁻¹ = -(1 / (p : ℝ)) - 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [e] at h
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 := by
      rw [div_div, div_le_div_iff₀ hden (by positivity)]
      nlinarith
    linarith
  · have h := Real.log_le_sub_one_of_pos hpos
    linarith

/-- **Mertens' third theorem**, explicit form. For real `z ≥ 2`,
`exp (-c) / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ exp (mertens2Const) / log z`
with `c = mertens2Const + primePowerConst / log 2`. -/
theorem prod_one_sub_inv_bounds (z : ℝ) (hz : 2 ≤ z) :
    Real.exp (-(mertens2Const + primePowerConst / Real.log 2)) / Real.log z ≤
        ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ Real.exp mertens2Const / Real.log z := by
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hne : ∀ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    intro h; linarith
  have hPpos : 0 < ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hlogP := Real.log_prod (s := Nat.primesLE ⌊z⌋₊) (f := fun p => (1 - 1 / (p : ℝ))) hne
  have hup : Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) ≤
      -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p := by
    rw [hlogP, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun p hp => (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).2
  have hlo : -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p - primePowerConst / Real.log 2 ≤
      Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) := by
    rw [hlogP]
    have hK := sum_log_div_mul_sub_one_le (Nat.primesLE ⌊z⌋₊)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK' : ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        primePowerConst / Real.log 2 := by
      rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hK hl2.le
    have hs := Finset.sum_le_sum (s := Nat.primesLE ⌊z⌋₊) fun p hp =>
      (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).1
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hs
    linarith
  have hM := abs_sum_inv_sub_log_log_le z hz
  rw [abs_le] at hM
  have hexp : ∀ t : ℝ, Real.exp t / Real.log z = Real.exp (t - Real.log (Real.log z)) := by
    intro t
    rw [Real.exp_sub, Real.exp_log hlz]
  rw [hexp, hexp, ← Real.exp_log hPpos]
  constructor
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]

/-- **Mertens' third theorem**, existential form: there are constants `0 < c₁` and `c₂` with
`c₁ / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ c₂ / log z` for all real `z ≥ 2`. -/
theorem mertens3 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℝ, 2 ≤ z →
    c₁ / Real.log z ≤ ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ c₂ / Real.log z :=
  ⟨_, _, Real.exp_pos _, Real.exp_pos _, prod_one_sub_inv_bounds⟩


/-- Upper half of Mertens' second theorem for any subset of the primes, for instance the primes
in a residue class: `∑_{p ≤ x, P p} 1 / p ≤ log log x + mertens2Const` for real `x ≥ 2`. -/
theorem sum_inv_filter_le (P : ℕ → Prop) [DecidablePred P] (x : ℝ) (hx : 2 ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      Real.log (Real.log x) + mertens2Const := by
  have h := abs_sum_inv_sub_log_log_le x hx
  rw [abs_le] at h
  have hsub : ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => by positivity)
  linarith [h.2]

end OMALib.Mertens

namespace Work692
open Finset Filter
open scoped Classical BigOperators Topology

noncomputable def ind (S : Set ℕ) (x : ℕ) : ℝ := if x∈S then 1 else 0
def wgt (P : Finset ℕ) (t : ℝ) (x : ℕ) := ∏ p ∈ P, if p∣x then t else 1
def row (P : Finset ℕ) (d : ℕ) (t : ℝ) (x : ℕ) := if d∣x then wgt P t x else 0
noncomputable def factor (d p : ℕ) (t : ℝ) : ℝ := if p∣d then t else 1+(t-1)/p
def avg (f : ℕ → ℝ) (a : ℝ) := ∀ᶠ N : ℕ in atTop,
  ∑ x ∈ range (N.factorial), f x = a*N.factorial
def boundSet (S : Set ℕ) (a : ℝ) := ∀ᶠ N : ℕ in atTop,
  ∑ x ∈ range (N.factorial), ind S x ≤ a*N.factorial

lemma w_nonneg {P : Finset ℕ} {t : ℝ} (ht : 0≤t) (x : ℕ) : 0≤wgt P t x := by
  exact prod_nonneg (fun p _ => by split_ifs <;> positivity)
lemma r_nonneg {P : Finset ℕ} {t : ℝ} (ht : 0≤t) (d x : ℕ) : 0≤row P d t x := by
  dsimp [row]; split_ifs; exact w_nonneg ht x; exact le_rfl

lemma mean_dvd (d : ℕ) (hd : 0<d) : avg (fun x => if d∣x then 1 else 0) (1/d) := by
  filter_upwards [eventually_ge_atTop d] with N hN
  have hdiv : d∣N.factorial := Nat.dvd_factorial hd hN
  have hswap : (∑ x ∈ range N.factorial, (if d∣x then (1:ℝ) else 0)) =
      ∑ x ∈ range N.factorial, (if d∣x+1 then (1:ℝ) else 0) := by
    let F (x : ℕ) : ℝ := if d∣x then 1 else 0
    have h1 := sum_range_succ F N.factorial
    have h2 := sum_range_succ' F N.factorial
    change ∑ x ∈ range N.factorial, F x = ∑ x ∈ range N.factorial, F (x+1)
    have hf : F N.factorial=F 0 := by simp [F,hdiv]
    linarith
  rw [hswap,← sum_filter,sum_const,Nat.card_multiples,nsmul_eq_mul,mul_one,
    Nat.cast_div hdiv (by exact_mod_cast hd.ne')]
  ring

lemma mean_row (P : Finset ℕ) (hP : ∀ p∈P, p.Prime) (d : ℕ) (hd : 0<d) (t : ℝ) :
    avg (row P d t) ((1/d)*∏ p ∈ P, factor d p t) := by
  induction P using Finset.induction_on generalizing d with
  | empty =>
    have h : row ∅ d t = (fun x => if d∣x then 1 else 0) := by funext x; simp [row,wgt]
    rw [h]; simpa using mean_dvd d hd
  | @insert p P hp ih =>
    have hp' := hP p (mem_insert_self _ _)
    have hP' : ∀ q∈P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have r1 := ih hP' d hd
    by_cases hpd : p∣d
    · filter_upwards [r1] with N hn
      have eq (x : ℕ) : row (insert p P) d t x=t*row P d t x := by
        by_cases h : d∣x
        · simp [row,wgt,prod_insert,hp,h,hpd.trans h]
        · simp [row,h]
      simp_rw [eq,← mul_sum,hn]
      rw [prod_insert hp,show factor d p t=t by simp [factor,hpd]]; ring
    · have hcop : d.Coprime p := (hp'.coprime_iff_not_dvd.mpr hpd).symm
      have r2 := ih hP' (d*p) (Nat.mul_pos hd hp'.pos)
      have prodEq : (∏ q ∈ P, factor (d*p) q t) = ∏ q ∈ P, factor d q t := by
        apply prod_congr rfl
        intro q hq
        have hq' := hP' q hq
        have ne : ¬q∣p := by
          intro h; have := (Nat.prime_dvd_prime_iff_eq hq' hp').mp h
          exact hp (this ▸ hq)
        simp [factor,hq'.dvd_mul,ne]
      have eq (x : ℕ) : row (insert p P) d t x=row P d t x+(t-1)*row P (d*p) t x := by
        have iff : d*p∣x ↔ d∣x ∧ p∣x := ⟨fun h => ⟨(dvd_mul_right d p).trans h,
          (dvd_mul_left p d).trans h⟩,fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
        by_cases h : d∣x <;> by_cases k : p∣x <;> simp [row,wgt,prod_insert,hp,iff,h,k] <;> ring
      filter_upwards [r1,r2] with N hn hm
      simp_rw [eq,sum_add_distrib,←mul_sum,hn,hm]
      rw [prodEq,prod_insert hp]
      simp only [factor,if_neg hpd,Nat.cast_mul]
      have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
      have hT : (p:ℝ)≠0 := by exact_mod_cast hp'.ne_zero
      field_simp <;> ring

lemma bound_mono {S T : Set ℕ} {a b : ℝ} (h : S⊆T) (hab : a≤b) (bt : boundSet T a) :
    boundSet S b := by
  filter_upwards [bt] with N hn
  exact (sum_le_sum (fun x _ => by by_cases hx : x∈S; simp [ind,hx,h hx]; simp [ind,hx]; split_ifs <;> norm_num)).trans
    (hn.trans (mul_le_mul_of_nonneg_right hab (by positivity)))

lemma bound_union {S T : Set ℕ} {a b : ℝ} (hs : boundSet S a) (ht : boundSet T b) :
    boundSet (S∪T) (a+b) := by
  filter_upwards [hs,ht] with N hn hm
  calc _ ≤ ∑ x ∈ range N.factorial, (ind S x+ind T x) := by
           apply sum_le_sum; intro x _
           by_cases h : x∈S <;> by_cases k : x∈T <;> simp [ind,h,k]
       _ ≤ _ := by rw [sum_add_distrib,add_mul]; linarith

lemma bound_iUnion (s : Finset ℕ) (T : ℕ → Set ℕ) (a : ℝ)
    (h : ∀ i∈s, boundSet (T i) a) : boundSet (⋃ i∈s, T i) (s.card*a) := by
  induction s using Finset.induction_on with
  | empty => simp [boundSet,ind]
  | @insert i s hi ih =>
    have hh := bound_union (h i (mem_insert_self _ _)) (ih (fun j hj => h j (mem_insert_of_mem hj)))
    simpa [hi,add_mul,add_comm] using hh

lemma density_bound {S : Set ℕ} {δ a : ℝ} (hs : S.HasDensity δ) (hb : boundSet S a) :
    δ≤a := by
  have tend : Tendsto Nat.factorial atTop atTop := tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  apply le_of_tendsto (hs.comp tend)
  filter_upwards [hb] with N hN
  change Set.partialDensity S Set.univ N.factorial ≤ a
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Set.ncard_Iio_nat]
  rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos N)]
  have eq : (S ∩ Set.Iio N.factorial).ncard = ((range N.factorial).filter (· ∈ S)).card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext x; simp [and_comm]
  rw [eq]
  simpa [ind,← sum_filter] using hN
end Work692


namespace Work692
open Finset Filter ArithmeticFunction Real
open scoped Classical BigOperators ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt
noncomputable section

def fw (s : ℝ) : ArithmeticFunction ℝ := ⟨fun n => if n=0 then 0 else s^n.primeFactors.card,by simp⟩
def frac (s : ℝ) : ArithmeticFunction ℝ := ⟨fun n => fw s n / n,by simp⟩

lemma fw_apply {s : ℝ} {n : ℕ} (hn : n≠0) : fw s n = s^n.primeFactors.card := by simp [fw,hn]
lemma frac_apply (s : ℝ) (n : ℕ) : frac s n = fw s n / n := rfl
lemma fw_pos {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0≤fw s n := by
  by_cases h : n=0 <;> simp [fw,h]; positivity

lemma frac_mult (s : ℝ) : (frac s).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [frac,fw],?_⟩
  intro m n hm hn cop
  simp only [frac_apply,fw_apply hm,fw_apply hn,fw_apply (mul_ne_zero hm hn),Nat.cast_mul,
    Nat.primeFactors_mul hm hn,card_union_of_disjoint cop.disjoint_primeFactors,pow_add]
  ring

lemma local_geom (p k : ℕ) (hp : p.Prime) (s : ℝ) (hs : 0 ≤ s) :
    ∑ i ∈ range (k+1), frac s (p^i) ≤ 1+s/((p:ℝ)-1) := by
  have p1 : 1<(p:ℝ) := by exact_mod_cast hp.one_lt
  have p0 : (0:ℝ)<p := by linarith
  let r := (p:ℝ)⁻¹
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hr1 : r<1 := inv_lt_one_of_one_lt₀ p1
  have eq (i : ℕ) : frac s (p^(i+1))=s*r^(i+1) := by
    simp [frac_apply,fw_apply (pow_ne_zero _ hp.ne_zero),Nat.primeFactors_prime_pow (Nat.succ_ne_zero _) hp,r,div_eq_mul_inv]
  rw [sum_range_succ']
  simp_rw [eq,pow_succ',←mul_assoc,←mul_sum]
  have ub := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (range k) (fun _ _ => pow_nonneg hr0 _)
  rw [tsum_geometric_of_lt_one hr0 hr1] at ub
  have le := mul_le_mul_of_nonneg_left ub (mul_nonneg hs hr0)
  have eq' : s*r*(1-r)⁻¹=s/((p:ℝ)-1) := by
    dsimp [r]; field_simp <;> ring
  simpa [eq',frac_apply,fw,add_comm] using add_le_add_right le 1

lemma harmonic_euler (N : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∑ n ∈ Ioc 0 N, frac s n ≤ ∏ p ∈ Nat.primesLE N, (1+s/((p:ℝ)-1)) := by
  let M := N.factorial
  have hm : M≠0 := Nat.factorial_ne_zero _
  have sub : Ioc 0 N ⊆ M.divisors := by
    intro n hn
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (mem_Ioc.mp hn).1 (mem_Ioc.mp hn).2,hm⟩
  have eq : M.primeFactors=Nat.primesLE N := by
    ext p
    simp only [Nat.mem_primeFactors,Nat.mem_primesLE,hm,not_false_eq_true,and_true]
    constructor
    · rintro ⟨hp,h⟩; exact ⟨hp.dvd_factorial.mp h.1,hp⟩
    · rintro ⟨h,hp⟩; exact ⟨hp,hp.dvd_factorial.mpr h,hm⟩
  have mult := (frac_mult s).mul ArithmeticFunction.isMultiplicative_zeta.natCast
  calc _ ≤ ∑ n ∈ M.divisors, frac s n := sum_le_sum_of_subset_of_nonneg sub
           (fun n _ _ => div_nonneg (fw_pos hs n) (Nat.cast_nonneg _))
       _ = (frac s * ζ) M := coe_mul_zeta_apply.symm
       _ = ∏ p ∈ M.primeFactors, (frac s * ζ) (p^(M.factorization p)) := by
           simpa [Finsupp.prod,Nat.support_factorization] using mult.multiplicative_factorization _ hm
       _ ≤ _ := by
           rw [eq]
           apply Finset.prod_le_prod
           · intro p _
             rw [coe_mul_zeta_apply]; exact sum_nonneg fun i _ => div_nonneg (fw_pos hs _) (Nat.cast_nonneg _)
           · intro p hp; have pr := Nat.prime_of_mem_primesLE hp
             rw [coe_mul_zeta_apply,Nat.sum_divisors_prime_pow pr]
             exact local_geom p _ pr _ hs

def zetaSq := ∑' n : ℕ, 1/(n:ℝ)^2

lemma harmonic_bound (s : ℝ) (hs : 0 ≤ s) : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 2≤N →
    ∑ n ∈ Ioc 0 N, frac s n ≤ C*(Real.log N)^s := by
  refine ⟨exp (s*OMALib.Mertens.mertens2NatConst+2*s*zetaSq),exp_pos _,?_⟩
  intro N hN
  let P := Nat.primesLE N
  have hM := (abs_le.mp (OMALib.Mertens.abs_sum_inv_sub_log_log_le_nat N hN)).2
  have hsq : ∑ p ∈ P, 1/(p:ℝ)^2 ≤ zetaSq :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).sum_le_tsum _ (fun _ _ => by positivity)
  have hp (p : ℕ) (h : p∈P) : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE h).two_le
  have hloc (p : ℕ) (h : p∈P) : s/((p:ℝ)-1) ≤ s*(1/(p:ℝ))+2*s*(1/(p:ℝ)^2) := by
    have h' := hp p h; have h1 : 0<(p:ℝ)-1 := by linarith
    have h0 : (0:ℝ)<p := by linarith
    field_simp
    nlinarith [mul_nonneg hs (sub_nonneg.mpr h'),mul_nonneg (mul_nonneg hs (sub_nonneg.mpr h')) h0.le]
  have hsum : ∑ p ∈ P, s/((p:ℝ)-1) ≤ s*Real.log (Real.log N)+s*OMALib.Mertens.mertens2NatConst+2*s*zetaSq := by
    apply (sum_le_sum hloc).trans
    rw [sum_add_distrib,←mul_sum,←mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (show ∑ p ∈ P, 1/(p:ℝ) ≤ Real.log (Real.log N)+OMALib.Mertens.mertens2NatConst by dsimp [P]; linarith) hs
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0≤2*s by positivity)]
  have hl : 0<log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  apply (harmonic_euler N s hs).trans
  calc _ ≤ ∏ p ∈ P, exp (s/((p:ℝ)-1)) := by
           apply Finset.prod_le_prod
           · intro p h; have := hp p h; exact add_nonneg zero_le_one (div_nonneg hs (by linarith))
           · intro p _; linarith [Real.add_one_le_exp (s/((p:ℝ)-1))]
       _ = exp (∑ p ∈ P, s/((p:ℝ)-1)) := (Real.exp_sum ..).symm
       _ ≤ _ := by
           rw [Real.rpow_def_of_pos hl,←Real.exp_add]
           apply exp_le_exp.mpr; linarith

end
end Work692


namespace Work692
open Finset Filter ArithmeticFunction Real
open scoped Classical BigOperators ArithmeticFunction.vonMangoldt
noncomputable section

lemma log_weight (s : ℝ) (hs : 0 ≤ s) (hs' : s≤1) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, fw s n*Real.log n ≤ (Real.log 4+4)*N*∑ n ∈ Ioc 0 N, frac s n := by
  calc _ ≤ ∑ n ∈ Ioc 0 N, (fw s * vonMangoldt) n := by
           apply sum_le_sum
           intro n hn
           have hn' : n≠0 := (mem_Ioc.mp hn).1.ne'
           rw [← vonMangoldt_sum,mul_sum,ArithmeticFunction.mul_apply,
             Nat.sum_divisorsAntidiagonal' (fun a b => fw s a * vonMangoldt b)]
           apply sum_le_sum
           intro h hh
           have dvd := Nat.dvd_of_mem_divisors hh
           have dvd' := Nat.div_dvd_of_dvd dvd
           have nd : n/h≠0 := (Nat.div_pos (Nat.le_of_dvd (by omega) dvd)
             (Nat.pos_of_mem_divisors hh)).ne'
           apply mul_le_mul_of_nonneg_right _ vonMangoldt_nonneg
           rw [fw_apply hn',fw_apply nd]
           exact pow_le_pow_of_le_one hs hs' (card_le_card (Nat.primeFactors_mono dvd' hn'))
       _ = ∑ n ∈ Ioc 0 N, fw s n*∑ m ∈ Ioc 0 (N/n), vonMangoldt m :=
            sum_Ioc_mul_eq_sum_sum _ _ _
       _ ≤ ∑ n ∈ Ioc 0 N, (Real.log 4+4)*N*frac s n := by
           apply sum_le_sum
           intro n hn
           have H := Chebyshev.psi_le_const_mul_self (x:=((N/n:ℕ):ℝ)) (by positivity)
           simp only [Chebyshev.psi,Nat.floor_natCast] at H
           have hC : 0≤Real.log 4+4 := by positivity
           have hp := (mem_Ioc.mp hn).1
           have hh := H.trans (mul_le_mul_of_nonneg_left (Nat.cast_div_le (m:=N) (n:=n) (α:=ℝ)) hC)
           exact (mul_le_mul_of_nonneg_left hh (fw_pos hs n)).trans_eq (by rw [frac_apply]; ring)
       _ = _ := (mul_sum ..).symm

lemma harmonic_interval (s : ℝ) (hs : 0 ≤ s) (hs' : s≤1) :
    ∃ K : ℝ, 0<K ∧ ∀ y : ℕ, 2≤y →
      ∑ d ∈ Icc y (2*y), frac s d ≤ K*(Real.log ((2*y:ℕ):ℝ))^(s-1) := by
  obtain ⟨C,hC,HC⟩ := harmonic_bound s hs
  refine ⟨4*(Real.log 4+4)*C,by positivity,?_⟩
  intro y hy
  let N := 2*y
  have hN : 2≤N := by dsimp [N]; omega
  have hY : (2:ℝ)≤y := by exact_mod_cast hy
  have hNcast : (N:ℝ)=2*y := by simp [N]
  have hlog : 0<Real.log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  have hYlog : Real.log (N:ℝ)≤2*Real.log y := by
    rw [hNcast,Real.log_mul (by norm_num) (by positivity)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) hY]
  have hrow (d : ℕ) (hd : d∈Icc y N) : frac s d*((y:ℝ)*Real.log N) ≤ 2*(fw s d*Real.log d) := by
    have hyd := (mem_Icc.mp hd).1
    have hd' : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
    have hleft : (y:ℝ)*Real.log N ≤ (d:ℝ)*(2*Real.log d) := by
      apply mul_le_mul (by exact_mod_cast hyd) _ hlog.le hd'.le
      exact hYlog.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by exact_mod_cast hyd)) (by norm_num))
    rw [frac_apply]
    calc _ = (fw s d / d)*((y:ℝ)*Real.log N) := rfl
         _ ≤ (fw s d / d)*((d:ℝ)*(2*Real.log d)) :=
               mul_le_mul_of_nonneg_left hleft (div_nonneg (fw_pos hs _) hd'.le)
         _ = _ := by field_simp <;> ring
  have hsub : Icc y N ⊆ Ioc 0 N := fun d hd => mem_Ioc.mpr ⟨by have := (mem_Icc.mp hd).1; omega,(mem_Icc.mp hd).2⟩
  have hall := sum_le_sum hrow
  rw [← sum_mul,← mul_sum] at hall
  have hpos (n : ℕ) (hn : n∈Ioc 0 N) : 0≤fw s n*Real.log n :=
    mul_nonneg (fw_pos hs _) (log_nonneg (by exact_mod_cast (mem_Ioc.mp hn).1))
  have h1 := sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hpos n hn)
  have H := log_weight s hs hs' N
  have h2 := mul_le_mul_of_nonneg_left (HC N hN) (show 0≤(Real.log 4+4)*N by positivity)
  have h3 : (∑ d ∈ Icc y N, frac s d)*((y:ℝ)*Real.log N) ≤ 2*((Real.log 4+4)*N*(C*(Real.log N)^s)) :=
    hall.trans (mul_le_mul_of_nonneg_left (h1.trans (H.trans h2)) (by norm_num))
  change _ ≤ _*(Real.log (N:ℝ))^(s-1)
  rw [Real.rpow_sub hlog,Real.rpow_one]
  apply (le_of_mul_le_mul_right ?_ (show 0<(y:ℝ)*Real.log N by positivity))
  apply h3.trans_eq
  rw [hNcast] at hlog ⊢; field_simp <;> ring

end
end Work692


namespace Work692
open Finset Filter Real
open scoped Classical BigOperators
noncomputable section

def momentConst (v : ℝ) := exp (|v| * OMALib.Mertens.mertens2NatConst)

lemma primeMoment {N : ℕ} (hN : 2≤N) {v : ℝ} (hv : -1≤v) :
    ∏ p ∈ N.primesLE, (1+v/p) ≤ momentConst v*(log (N:ℝ))^v := by
  have hM := OMALib.Mertens.abs_sum_inv_sub_log_log_le_nat N hN
  have hl : 0<log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  calc _ ≤ ∏ p ∈ N.primesLE, exp (v/p) := by
           apply Finset.prod_le_prod
           · intro p h
             have hp : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE h).two_le
             have hh : -1≤v/(p:ℝ) := (le_div_iff₀ (by linarith)).mpr (by linarith)
             linarith
           · intro p _; linarith [add_one_le_exp (v/p)]
       _ = exp (v * ∑ p ∈ N.primesLE, (1:ℝ)/p) := by
           rw [← exp_sum,mul_sum]; congr 1; apply sum_congr rfl; intro p _; ring
       _ ≤ _ := by
           rw [momentConst,rpow_def_of_pos hl,←exp_add]
           apply exp_le_exp.mpr
           have b : v*((∑ p ∈ N.primesLE, (1:ℝ)/p)-log (log N)) ≤ |v| * OMALib.Mertens.mertens2NatConst := (le_abs_self (v*((∑ p ∈ N.primesLE, (1:ℝ)/p)-log (log N)))).trans
             (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hM (abs_nonneg v))
           linarith

def slab (y : ℕ) : Set ℕ := {x | ∃ d∈Icc y (2*y), d∣x}

private lemma cond {N d : ℕ} (hd : 0<d) (hdN : d≤N) :
    (1/(d:ℝ))*∏ p ∈ N.primesLE, factor d p (2/3) ≤
      frac (4/5) d * ∏ p ∈ N.primesLE, (1+(-(1/3:ℝ))/p) := by
  have hF : N.primesLE.filter (· ∣ d)=d.primeFactors := by
    ext p
    simp only [mem_filter,Nat.mem_primesLE,Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_,hp⟩,h⟩; exact ⟨hp,h,hd.ne'⟩
    · rintro ⟨hp,h,_⟩; exact ⟨⟨(Nat.le_of_dvd hd h).trans hdN,hp⟩,h⟩
  have pw : (∏ p ∈ N.primesLE, (if p∣d then (4/5:ℝ) else 1))=(4/5:ℝ)^d.primeFactors.card := by
    rw [←prod_filter,hF,prod_const]
  have loc (p : ℕ) (hp : p∈N.primesLE) : factor d p (2/3) ≤
      (if p∣d then (4/5:ℝ) else 1)*(1+(-(1/3:ℝ))/p) := by
    have h : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    dsimp [factor]
    split_ifs
    · field_simp; linarith
    · ring_nf; rfl
  calc _ ≤ (1/(d:ℝ))*∏ p ∈ N.primesLE,
             ((if p∣d then (4/5:ℝ) else 1)*(1+(-(1/3:ℝ))/p)) := by
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           apply Finset.prod_le_prod _ loc
           intro p hp
           have h : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
           dsimp [factor]; split_ifs
           · norm_num
           · have h' : (-(1/3:ℝ))/(p:ℝ) ≥ -1 := (le_div_iff₀ (by linarith)).mpr (by linarith)
             norm_num at *; linarith
       _ = _ := by rw [prod_mul_distrib,pw,frac_apply,fw_apply hd.ne']; ring

lemma bound_slab : ∃ C : ℝ, 0<C ∧ ∀ y : ℕ, 2≤y →
    boundSet (slab y) (C/(log ((2*y:ℕ):ℝ))^(1/60:ℝ)) := by
  obtain ⟨K,hK,HK⟩ := harmonic_interval (4/5) (by norm_num) (by norm_num)
  let C₁ := momentConst (1/2)
  let C₂ := momentConst (-(1/3))
  have p₁ : 0<C₁ := exp_pos _
  have p₂ : 0<C₂ := exp_pos _
  refine ⟨C₁+K*C₂,by positivity,?_⟩
  intro y hy
  let N := 2*y
  let P := N.primesLE
  let D := Icc y N
  let l := log (N:ℝ)
  have hN : 2≤N := by dsimp [N]; omega
  have hl : 0<l := log_pos (by exact_mod_cast (show 1<N by omega))
  let T := l^(31/60:ℝ)
  have pT : 0<T := rpow_pos_of_pos hl _
  have pr : ∀ p∈P,p.Prime := fun _ h => Nat.prime_of_mem_primesLE h
  have Hu := mean_row P pr 1 (by decide) (3/2)
  have Heq : (∏ p ∈ P, factor 1 p (3/2))=∏ p ∈ P, (1+(1/2:ℝ)/p) := by
    apply prod_congr rfl
    intro p hp; simp [factor,(pr p hp).not_dvd_one]; ring
  have Hlo := fun d (h : d∈D) => mean_row P pr d (show 0<d by have := (mem_Icc.mp h).1; omega) (2/3)
  have Hlo' := (Filter.eventually_all_finset D).mpr Hlo
  have M1 : (∏ p ∈ P, factor 1 p (3/2)) ≤ C₁*l^(1/2:ℝ) := by
    rw [Heq]; exact primeMoment hN (by norm_num)
  have M2 : (∑ d ∈ D, (1/(d:ℝ))*∏ p ∈ P, factor d p (2/3)) ≤
      (K*l^(4/5-1:ℝ))*(C₂*l^(-(1/3):ℝ)) := by
    calc _ ≤ ∑ d ∈ D, frac (4/5) d * ∏ p ∈ P, (1+(-(1/3:ℝ))/p) := by
             apply sum_le_sum; intro d h; obtain ⟨hd,hd'⟩ := mem_Icc.mp h; exact cond (by omega) hd'
         _ = _ := sum_mul .. |>.symm
         _ ≤ _ := by
             apply mul_le_mul (HK y hy) (primeMoment hN (by norm_num)) _ (by positivity)
             apply prod_nonneg; intro p hp
             have h : (2:ℝ)≤p := by exact_mod_cast (pr p hp).two_le
             have h' : (-1:ℝ)≤(-(1/3:ℝ))/(p:ℝ) := (le_div_iff₀ (by linarith)).mpr (by linarith)
             linarith
  have inv (x : ℕ) : wgt P (3/2) x*wgt P (2/3) x=1 := by
    dsimp [wgt]; rw [←prod_mul_distrib]
    apply prod_eq_one; intro p _; split_ifs <;> norm_num
  have major (x : ℕ) : ind (slab y) x ≤ row P 1 (3/2) x/T+T*∑ d ∈ D,row P d (2/3) x := by
    have sw : 0≤∑ d ∈ D,row P d (2/3) x := sum_nonneg fun d _ => r_nonneg (by norm_num) d x
    have rw1 : row P 1 (3/2) x=wgt P (3/2) x := by simp [row]
    rw [rw1]
    by_cases h : x∈slab y
    · obtain ⟨d,hd,dvd⟩ := h
      rw [show ind (slab y) x=1 by simp [ind,show x∈slab y from ⟨d,hd,dvd⟩]]
      by_cases big : T≤wgt P (3/2) x
      · have := (one_le_div pT).mpr big
        linarith [mul_nonneg pT.le sw]
      · have single := single_le_sum (s:=D) (f:=fun k=>row P k (2/3) x)
          (fun k _ => r_nonneg (by norm_num) k x) hd
        rw [row,if_pos dvd] at single
        have a := mul_le_mul_of_nonneg_right (le_of_not_ge big) (w_nonneg (P:=P) (by norm_num : (0:ℝ)≤2/3) x)
        have b := mul_le_mul_of_nonneg_left single pT.le
        linarith [inv x,div_nonneg (w_nonneg (P:=P) (by norm_num : (0:ℝ)≤3/2) x) pT.le]
    · simp only [ind,if_neg h]
      exact add_nonneg (div_nonneg (w_nonneg (by norm_num) _) pT.le) (mul_nonneg pT.le sw)
  filter_upwards [Hu,Hlo'] with M U V
  have hh := sum_le_sum (s:=range M.factorial) (fun x _ => major x)
  rw [sum_add_distrib,←sum_div,←mul_sum,sum_comm,U] at hh
  simp only [Nat.cast_one,div_one,one_mul] at hh
  rw [sum_congr rfl V,←sum_mul] at hh
  have b1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right M1 (Nat.cast_nonneg M.factorial)) pT.le
  have b2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right M2 (Nat.cast_nonneg M.factorial)) pT.le
  apply hh.trans ((add_le_add b1 b2).trans_eq ?_)
  change C₁*l^(1/2:ℝ)*M.factorial/T+T*((K*l^(4/5-1:ℝ)*(C₂*l^(-(1/3):ℝ)))*M.factorial)=
    ((C₁+K*C₂)/l^(1/60:ℝ))*M.factorial
  have e1 : l^(1/2:ℝ)/T=l^(-(1/60):ℝ) := by
    dsimp [T]; rw [←rpow_sub hl]; norm_num
  have e2 : T*(l^(4/5-1:ℝ)*l^(-(1/3):ℝ))=l^(-(1/60):ℝ) := by
    dsimp [T]; rw [←rpow_add hl,←rpow_add hl]; norm_num
  have einv : l^(-(1/60):ℝ)=(l^(1/60:ℝ))⁻¹ := rpow_neg hl.le _
  linear_combination C₁*(M.factorial:ℝ)*(e1.trans einv) + K*C₂*(M.factorial:ℝ)*(e2.trans einv)

end
end Work692



noncomputable section
open Finset Filter Real Erdos859 Work692
open scoped Classical Topology
namespace PracticalUpper

def small (y t : ℕ) : Set ℕ := {n | t ≤ ∑ d ∈ Icc 1 y, if d ∣ n then d else 0}

lemma small_bound (y t : ℕ) (ht : 0<t) : boundSet (small y t) ((y:ℝ)/t) := by
  let D := Icc 1 y
  have hp : (0:ℝ)<t := by exact_mod_cast ht
  have means : ∀ᶠ N : ℕ in atTop, ∀ d∈D,
      ∑ n ∈ range N.factorial, (if d∣n then (1:ℝ) else 0) = (1/(d:ℝ))*N.factorial :=
    (eventually_all_finset D).mpr fun d hd => mean_dvd d (mem_Icc.mp hd).1
  filter_upwards [means] with N hN
  have hrow (n : ℕ) : ind (small y t) n * t ≤ ∑ d ∈ D, (d:ℝ)*(if d∣n then 1 else 0) := by
    by_cases hh : n ∈ small y t
    · rw [ind,if_pos hh,one_mul]
      change t ≤ ∑ d ∈ D, if d ∣ n then d else 0 at hh
      have hc : (t:ℝ) ≤ ∑ d ∈ D, if d ∣ n then (d:ℝ) else 0 := by exact_mod_cast hh
      simpa [mul_ite] using hc
    · rw [ind,if_neg hh,zero_mul]
      exact sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> norm_num))
  have h := sum_le_sum (s := range N.factorial) (fun n _ => hrow n)
  rw [←sum_mul,sum_comm] at h
  have hs (d) (hd : d∈D) : (∑ n ∈ range N.factorial, (d:ℝ)*(if d∣n then 1 else 0)) = N.factorial := by
    rw [←mul_sum,hN d hd]
    have hd' : 0 < (d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
    field_simp
  rw [sum_congr rfl hs] at h
  have hcard : D.card=y := by simp [D]
  simp only [sum_const,hcard,nsmul_eq_mul] at h
  exact (le_div_iff₀ hp).mpr h |>.trans_eq (by ring)

lemma cover {t j H : ℕ} (hj : j = Nat.log 2 t) :
    DivisorSumSet t ⊆ small (2^(j-H)) t ∪ ⋃ i∈Icc (j-H) j, slab (2^i) := by
  intro n hn
  obtain ⟨S,hS,ht⟩ := hn
  by_cases h : ∃ d∈S, 2^(j-H) ≤ d
  · obtain ⟨d,hd,hlo⟩ := h
    have dt : d≤t := ht ▸ single_le_sum (f:=id) (fun _ _ => Nat.zero_le _) hd
    have dp := Nat.pos_of_mem_divisors (hS hd)
    let i := Nat.log 2 d
    apply Or.inr
    apply Set.mem_iUnion₂.mpr
    refine ⟨i,mem_Icc.mpr ⟨(Nat.le_log_iff_pow_le (by decide) dp.ne').mpr hlo,?_⟩,?_⟩
    · rw [hj]; exact Nat.log_mono_right dt
    · exact ⟨d,mem_Icc.mpr ⟨Nat.pow_log_le_self _ dp.ne',by
        have := Nat.lt_pow_succ_log_self (by decide : 1<2) d
        simpa [i,pow_succ'] using this.le⟩,(Nat.mem_divisors.mp (hS hd)).1⟩
  · apply Or.inl
    have sub : S ⊆ Icc 1 (2^(j-H)) := fun d hd => mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors (hS hd),(lt_of_not_ge (fun hl => h ⟨d,hd,hl⟩)).le⟩
    change t ≤ _
    rw [ht]
    calc
      _ = ∑ d ∈ S, if d∣n then d else 0 := sum_congr rfl fun d hd => (if_pos (Nat.mem_divisors.mp (hS hd)).1).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset sub
end PracticalUpper

noncomputable section
open Finset Filter Real Work692 PracticalUpper
open scoped Classical Topology

theorem h2_proof : OMA.Erdos859R1.H2 := by
  obtain ⟨C,hC,hslab⟩ := Work692.bound_slab
  have grow : Tendsto (fun t : ℕ => log (t:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have grow' := (tendsto_rpow_atTop (by norm_num : 0<(1/240:ℝ))).comp grow
  refine ⟨1/240,by norm_num,?_⟩
  filter_upwards [grow.eventually_ge_atTop 16,grow'.eventually_gt_atTop (1+6*C),
    eventually_ge_atTop (2:ℕ)] with t hl hlarge ht
  let L := log (t:ℝ)
  let R := L^(1/240:ℝ)
  let T := L^(1/120:ℝ)
  let H := ⌊T⌋₊+1
  let j := Nat.log 2 t
  let y := 2^(j-H)
  change 16≤L at hl
  change 1+6*C < R at hlarge
  have hl1 : 1≤L := by linarith
  have hlp : 0<L := by linarith
  have hT : 1≤T := one_le_rpow hl1 (by norm_num)
  have pT : 0<T := by linarith
  have pR : 0<R := rpow_pos_of_pos hlp _
  have hR : R*R=T := by dsimp [R,T]; rw [←rpow_add hlp]; norm_num
  have hTT : T*T=L^(1/60:ℝ) := by dsimp [T]; rw [←rpow_add hlp]; norm_num
  have Hhi : (H:ℝ) ≤ T+1 := by dsimp [H]; push_cast; linarith [Nat.floor_le pT.le]
  have Hlo : T ≤ (H:ℝ) := by simpa [H] using (Nat.lt_floor_add_one T).le
  have hL : L≤(j:ℝ)+1 := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) t
    have hh := log_le_log (show (0:ℝ)<t by exact_mod_cast (show 0<t by omega))
      (show (t:ℝ) ≤ (2:ℝ)^(j+1) by exact_mod_cast h.le)
    rw [log_pow] at hh
    push_cast at hh
    exact hh.trans (mul_le_of_le_one_right (by positivity) (by linarith [log_two_lt_d9]))
  have hTroot : T ≤ sqrt L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num)
  have jH : 2*H ≤ j := by
    exact_mod_cast (show (2:ℝ)*H ≤ j by nlinarith [Real.sq_sqrt hlp.le,sq_nonneg (sqrt L-2)])
  have hbig {i : ℕ} (hi : i ∈ Icc (j-H) j) :
      Work692.boundSet (slab (2^i)) (2*C/(T*T)) := by
    obtain ⟨ha,hb⟩ := mem_Icc.mp hi
    have hi1 : 1 ≤ i := by dsimp [H] at *; omega
    have hip : 2≤2^i := Nat.pow_le_pow_right (by decide : 0<2) hi1
    have hlog : L ≤ 2*log ((2*2^i:ℕ):ℝ) := by
      have hj := Nat.lt_pow_succ_log_self (by decide : 1<2) t
      have hpow : j+1 ≤ (i+1)*2 := by omega
      have bound : (t:ℝ) ≤ (2:ℝ)^((i+1)*2) := by
        exact_mod_cast (hj.le.trans (Nat.pow_le_pow_right (by decide : 0<2) hpow))
      have hh := log_le_log (show (0:ℝ)<t by exact_mod_cast (show 0<t by omega)) bound
      change log (t:ℝ) ≤ _
      push_cast
      rw [← pow_succ',log_pow]
      rw [log_pow] at hh
      push_cast at hh ⊢
      linarith
    let z := log ((2*2^i:ℕ):ℝ)
    have zp : 0<z := by dsimp [z]; linarith
    have two : (2:ℝ)^(1/60:ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have q : T*T ≤ 2*z^(1/60:ℝ) := calc
      _ = L^(1/60:ℝ) := hTT
      _ ≤ (2*z)^(1/60:ℝ) := Real.rpow_le_rpow hlp.le hlog (by norm_num)
      _ = (2:ℝ)^(1/60:ℝ)*z^(1/60:ℝ) := Real.mul_rpow (by norm_num) zp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right two (by positivity)
    apply bound_mono Set.Subset.rfl _ (hslab _ hip)
    change C/z^(1/60:ℝ) ≤ _
    rw [div_le_div_iff₀ (rpow_pos_of_pos zp _) (mul_pos pT pT)]
    nlinarith only [mul_le_mul_of_nonneg_left q hC.le]
  have hfin := bound_union (small_bound y t (by omega)) (bound_iUnion (Icc (j-H) j)
    (fun i => slab (2^i)) _ (fun _ hi => hbig hi))
  have hd := density_bound (OMA.Erdos859R1.divisor_sum_density t)
    (bound_mono (PracticalUpper.cover (t:=t) (j:=j) (H:=H) rfl) le_rfl hfin)
  have hp : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hy : (y:ℝ)/t ≤ 1/T := by
    rw [div_le_div_iff₀ hp pT,one_mul]
    have hypos : 0 ≤ (y:ℝ) := Nat.cast_nonneg _
    calc (y:ℝ)*T ≤ (y:ℝ)*H := mul_le_mul_of_nonneg_left Hlo hypos
         _ ≤ (y:ℝ)*(2:ℝ)^H := by exact_mod_cast Nat.mul_le_mul_left y (Nat.lt_two_pow_self (n:=H)).le
         _ ≤ t := by
           exact_mod_cast (show y*2^H ≤ t by dsimp [y]; rw [← pow_add,Nat.sub_add_cancel (by omega)]; exact Nat.pow_log_le_self _ (by omega))
  have hc : ((Icc (j-H) j).card : ℝ) ≤ 3*T := by
    have hn : (Icc (j-H) j).card ≤ H+1 := by rw [Nat.card_Icc]; omega
    have hh : ((Icc (j-H) j).card:ℝ) ≤ (H:ℝ)+1 := by exact_mod_cast hn
    linarith
  have hs : (y:ℝ)/t + ((Icc (j-H) j).card:ℝ)*(2*C/(T*T)) ≤ (1+6*C)/T := calc
    _ ≤ 1/T+3*T*(2*C/(T*T)) := add_le_add hy (mul_le_mul_of_nonneg_right hc (by positivity))
    _ = _ := by field_simp; ring
  apply (hd.trans hs).trans_lt
  change (1+6*C)/T < 1/R
  rw [div_lt_div_iff₀ pT pR,one_mul,← hR]
  exact mul_lt_mul_of_pos_right hlarge pR
end
end
end H2Section

theorem OMA.solution : type_of% @Erdos859.erdos_859.variants.erdos_upper_lower_bounds :=
  OMA.Erdos859R1.main h1_proof h2_proof
