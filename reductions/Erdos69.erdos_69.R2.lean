import FormalConjectures.ErdosProblems.«69»
import Mathlib

/-!
A paired moment argument for the six-line CRT approach described on the
Erdős 69 docket by 1tomaszmiller. The binary-tail integrality lemma is from
the merged reduction #3097 by chris01-dev. The argument below uses first,
second and fourth moments of a finite small-prime model. Subtracting sample
values removes any common real offset.
-/

open Finset
namespace OMA.R_Erdos69_erdos_69_R2

lemma int_of_rational
    (hS : ¬ Irrational (∑' n : ℕ, (ArithmeticFunction.cardDistinctFactors (n + 2) : ℝ) / 2 ^ (n + 2))) :
    ∃ d : ℕ, 0 < d ∧ ∀ m : ℕ, ∃ z : ℤ, (d : ℝ) *
      ∑' h : ℕ, (ArithmeticFunction.cardDistinctFactors (m + h + 1) : ℝ) / 2 ^ (h + 1) = z := by
  have hs := ArithmeticFunction.summable_cardDistinctFactors_div_two_pow
  rw [Irrational, not_not] at hS
  obtain ⟨r, hr⟩ := hS
  have h2 := hs.sum_add_tsum_nat_add 2
  have hS0 : ∑' n : ℕ, (ArithmeticFunction.cardDistinctFactors n : ℝ) / 2 ^ n = r := by
    rw [← h2, hr]
    simp [Finset.sum_range_succ]
  refine ⟨r.den, r.den_pos, fun m => ?_⟩
  have hm := hs.sum_add_tsum_nat_add (m + 1)
  have hT : ∑' h : ℕ, (ArithmeticFunction.cardDistinctFactors (m + h + 1) : ℝ) / 2 ^ (h + 1)
      = 2 ^ m * ∑' i : ℕ, (ArithmeticFunction.cardDistinctFactors (i + (m + 1)) : ℝ)
        / 2 ^ (i + (m + 1)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun h => ?_
    rw [show m + h + 1 = h + (m + 1) by ring, show h + (m + 1) = (h + 1) + m by ring,
      pow_add (2 : ℝ) (h + 1) m]
    field_simp
  have hden : (r : ℝ) * r.den = r.num := by exact_mod_cast Rat.mul_den_eq_num r
  refine ⟨2 ^ m * r.num - r.den * ∑ i ∈ Finset.range (m + 1),
    (ArithmeticFunction.cardDistinctFactors i : ℤ) * 2 ^ (m - i), ?_⟩
  have hfin : (2 : ℝ) ^ m * ∑ i ∈ Finset.range (m + 1),
      (ArithmeticFunction.cardDistinctFactors i : ℝ) / 2 ^ i
      = ∑ i ∈ Finset.range (m + 1), (ArithmeticFunction.cardDistinctFactors i : ℝ) * 2 ^ (m - i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have : (2 : ℝ) ^ m = 2 ^ (m - i) * 2 ^ i := by rw [← pow_add, Nat.sub_add_cancel him]
    rw [this]
    field_simp
  have htail : ∑' i : ℕ, (ArithmeticFunction.cardDistinctFactors (i + (m + 1)) : ℝ)
      / 2 ^ (i + (m + 1)) = r - ∑ i ∈ Finset.range (m + 1),
      (ArithmeticFunction.cardDistinctFactors i : ℝ) / 2 ^ i := by
    rw [← hS0, ← hm]; ring
  rw [hT, htail]
  push_cast
  rw [← hfin, ← hden]
  ring


/-- A real number of large magnitude is controlled by its fourth power,
and a small one is closest to zero among the integers. -/
private theorem integer_distance (u : ℝ) (k : ℤ) : u^2 ≤ |u-(k:ℝ)|+4*u^4 := by
  by_cases h : 1/2 ≤ |u|
  · have hh : 0 ≤ (|u|-1/2)*(|u|+1/2) := mul_nonneg (by linarith) (by positivity)
    have hu : 1/4 ≤ u^2 := by nlinarith [sq_abs u]
    nlinarith [mul_nonneg (sq_nonneg u) (show 0 ≤ 4*u^2-1 by linarith),abs_nonneg (u-(k:ℝ))]
  · have hm : |u| ≤ |u-(k:ℝ)| := by
      by_cases hk : k=0
      · simp [hk]
      · have h1 : (1:ℝ) ≤ |(k:ℝ)| := by
          rw [←Int.cast_abs]
          exact_mod_cast (show (1:ℤ) ≤ |k| by have := abs_pos.mpr hk; omega)
        have ht := abs_add_le ((k:ℝ)-u) u
        rw [sub_add_cancel,abs_sub_comm] at ht
        linarith
    have hu := abs_nonneg u
    nlinarith [sq_abs u,mul_nonneg hu (show 0 ≤ 1-|u| by linarith),sq_nonneg (u^2)]

private theorem empirical (N : Finset ℕ) (W : ℕ → ℝ) (k : ℕ → ℤ) (c : ℝ)
    (hN : 0 < (N.card:ℝ))
    (herr : (∑ i ∈ N,|W i-c-(k i:ℝ)|) ≤ N.card/100000)
    (hmean : |∑ i ∈ N,W i| ≤ N.card/100)
    (hsecond : (N.card:ℝ)/1250 ≤ ∑ i ∈ N,(W i)^2)
    (hfourth : (∑ i ∈ N,(W i)^4) ≤ N.card/100000) : False := by
  let A (i : ℕ) := |W i-c-(k i:ℝ)|+32*(W i)^4
  have point (i j : ℕ) : (W i)^2+(W j)^2 ≤ 2*W i*W j+A i+A j := by
    have h1 := integer_distance (W i-W j) (k i-k j)
    push_cast at h1
    have hd : |(W i-W j)-((k i:ℝ)-(k j:ℝ))| ≤ |W i-c-(k i:ℝ)|+|W j-c-(k j:ℝ)| := by
      simpa only [show (W i-c-(k i:ℝ))-(W j-c-(k j:ℝ)) = (W i-W j)-((k i:ℝ)-(k j:ℝ)) by ring]
        using abs_sub (W i-c-(k i:ℝ)) (W j-c-(k j:ℝ))
    have h4 : (W i-W j)^4 ≤ 8*((W i)^4+(W j)^4) := by
      nlinarith only [mul_nonneg (sq_nonneg (W i+W j))
        (show 0 ≤ 5*(W i-W j)^2+2*(W i)^2+2*(W j)^2 by positivity)]
    dsimp only [A]
    nlinarith only [h1,hd,h4]
  have total : 2*N.card*(∑ i ∈ N,(W i)^2) ≤ 2*(∑ i ∈ N,W i)^2+2*N.card*(∑ i ∈ N,A i) := by
    calc
      _ = ∑ i ∈ N, ∑ j ∈ N,((W i)^2+(W j)^2) := by
          simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum]
          ring
      _ ≤ ∑ i ∈ N, ∑ j ∈ N,(2*W i*W j+A i+A j) :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => point i j
      _ = _ := by
          simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum,←sum_mul]
          ring
  have hsum : (∑ i ∈ N,A i) ≤ (N.card:ℝ)/100000 + 32*(N.card/100000) := by
    dsimp only [A]
    rw [sum_add_distrib,←mul_sum]
    linarith
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hmean 2
  rw [sq_abs] at hsq
  nlinarith only [total,hsq,mul_le_mul_of_nonneg_left hsecond hN.le,
    mul_le_mul_of_nonneg_left hsum hN.le,sq_pos_of_pos hN]

/-- Construct a progression and small-prime model approximating integer
linear combinations of binary tails sampled along affine progressions.
The progressions, coefficient vector and real offset are fixed across samples. -/
def H1 : Prop := ∀ q : ℕ, 0<q →
  ∃ (P J : Finset ℕ) (D b M : ℕ) (w : ℕ → ℝ),
    (∀ p ∈ P, Nat.Prime p ∧ p.Coprime D ∧ Set.InjOn (fun r : ℕ => r%p) (J : Set ℕ)) ∧
    (∑ r ∈ J,w r) = 0 ∧
    (1/1000:ℝ) ≤ (∑ r ∈ J,(w r)^2)*(∑ p ∈ P,1/(p:ℝ)) ∧
    (∑ r ∈ J,(w r)^2)*(∑ p ∈ P,1/(p:ℝ)) ≤ 11/10000 ∧
    (∑ r ∈ J,(w r)^4)*(∑ p ∈ P,1/(p:ℝ)) ≤ 1/1000000 ∧
    10000000*(1+(P.card:ℝ)*(∑ r ∈ J,|w r|))^4 ≤ (M:ℝ) ∧
    let W (i : ℕ) := ∑ r ∈ J, w r * (∑ p ∈ P, if p ∣ D*i+b+r then (1:ℝ) else 0)
    ∃ (c : ℝ) (S : Finset ℕ) (a : ℕ → ℤ) (slope shift : ℕ → ℕ),
      (∑ i ∈ range M, |W i-c-(q:ℝ)*∑ m ∈ S,(a m:ℝ)*
        ∑' j : ℕ, (ArithmeticFunction.cardDistinctFactors (slope m*i+shift m+j+1):ℝ)/2^(j+1)|) ≤ (M:ℝ)/100000

/-- The finite CRT moment estimate is independent of the binary tails. -/
def H2 : Prop := ∀ (P J : Finset ℕ) (D b M : ℕ) (w : ℕ → ℝ),
  ((∀ p ∈ P, Nat.Prime p ∧ p.Coprime D ∧ Set.InjOn (fun r : ℕ => r%p) (J : Set ℕ)) ∧
    (∑ r ∈ J,w r) = 0 ∧
    (1/1000:ℝ) ≤ (∑ r ∈ J,(w r)^2)*(∑ p ∈ P,1/(p:ℝ)) ∧
    (∑ r ∈ J,(w r)^2)*(∑ p ∈ P,1/(p:ℝ)) ≤ 11/10000 ∧
    (∑ r ∈ J,(w r)^4)*(∑ p ∈ P,1/(p:ℝ)) ≤ 1/1000000 ∧
    10000000*(1+(P.card:ℝ)*(∑ r ∈ J,|w r|))^4 ≤ (M:ℝ)) →
  let W (i : ℕ) := ∑ r ∈ J, w r * (∑ p ∈ P, if p ∣ D*i+b+r then (1:ℝ) else 0)
  |∑ i ∈ range M,W i| ≤ (M:ℝ)/100 ∧ (M:ℝ)/1250 ≤ ∑ i ∈ range M,(W i)^2 ∧
    (∑ i ∈ range M,(W i)^4) ≤ (M:ℝ)/100000

theorem main : H1 → H2 → type_of% @Erdos69.erdos_69 := by
  intro build moments
  by_contra hrat
  obtain ⟨q,hq,hint⟩ := int_of_rational hrat
  obtain ⟨P,J,D,b,M,w,hP,hw,hlo,hhi,h4,hlen,c,S,a,slope,shift,ha⟩ := build q hq
  obtain ⟨hmean,hsec,hfour⟩ := moments P J D b M w ⟨hP,hw,hlo,hhi,h4,hlen⟩
  let W (i : ℕ) := ∑ r ∈ J, w r * (∑ p ∈ P, if p ∣ D*i+b+r then (1:ℝ) else 0)
  choose z hz using hint
  let k (i : ℕ) : ℤ := ∑ m ∈ S,a m*z (slope m*i+shift m)
  have hk (i : ℕ) : (q:ℝ)*(∑ m ∈ S,(a m:ℝ)*
      ∑' j : ℕ, (ArithmeticFunction.cardDistinctFactors (slope m*i+shift m+j+1):ℝ)/2^(j+1)) = (k i:ℝ) := by
    rw [Finset.mul_sum]
    dsimp only [k]
    push_cast
    apply sum_congr rfl
    intro m _
    rw [mul_left_comm, hz (slope m*i+shift m)]
  have herr : (∑ i ∈ range M,|W i-c-(k i:ℝ)|) ≤ (M:ℝ)/100000 := by
    simpa only [hk] using ha
  have hbase : 1 ≤ (1+(P.card:ℝ)*∑ r ∈ J,|w r|)^4 := one_le_pow₀ (by
    have hg : 0 ≤ (P.card:ℝ)*∑ r ∈ J,|w r| := by positivity
    linarith)
  have hM : (0:ℝ)<M := by linarith
  exact empirical (range M) W k c (by simpa using hM) (by simpa using herr)
    (by simpa only [card_range] using hmean) (by simpa only [card_range] using hsec) (by simpa only [card_range] using hfour)

end OMA.R_Erdos69_erdos_69_R2
