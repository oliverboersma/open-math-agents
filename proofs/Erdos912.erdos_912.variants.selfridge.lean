import FormalConjectures.ErdosProblems.«912»
import Mathlib

/-!
# Erdős–Selfridge prime-exponent counting bound (Erdős Problem 912)

Proves `Erdos912.erdos_912.variants.selfridge`:
- `R1`: splits prime-exponent multiplicity counting in `n!` at `√(n * log n)`, deriving
  `h n = Θ(√(n / log n))` from Chebyshev prime counts (`H1`) and prime-pair sieve bounds (`H2`).
- `H1`: Chebyshev prime-counting bounds at `√(n * log n)` and `√n` (credit: `@dk8827`).
- `H2`: Daniel Larsen's Selberg-sieve prime-pair upper bound (formalized by Jake Mallen,
  incorporating Arend Mellendijk's Selberg sieve formalization).
-/

section R1Part

/-
Split the prime counts at the scale `√(n * log n)` from the upper-bound
sieve estimate for close pairs of primes. Large primes contribute exponents
`n / p`, and coincident exponents at the counting scale force a short gap.
The lower bound follows by a Cauchy–Schwarz count of these collisions.
See Erdős (1982), Miscellaneous problems in number theory, Theorem 1.
-/

-- Credit: @dk8827

open Finset Filter Asymptotics
open scoped BigOperators Pointwise Topology

namespace OMA.R_Erdos912_erdos_912_variants_selfridge_R1

private theorem factorization_of_large_prime {p n : ℕ} (hp : p.Prime) (hn : n < p * p) :
    n.factorial.factorization p = n / p := by
  have hl : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) (by simpa [pow_two] using hn)
  rw [Nat.factorization_factorial hp hl]
  norm_num

private theorem energy_le {α : Type} (P : Finset α) (f : α → ℕ) (Q : Finset (α × α))
    (hc : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → f p = f q → (p, q) ∈ Q) :
    P.card ^ 2 ≤ (P.image f).card * (P.card + Q.card) := by
  classical
  let F := P.image f
  let L (k : ℕ) := P.filter (fun p => f p = k)
  let C := (P ×ˢ P).filter (fun x => f x.1 = f x.2)
  have hSub : C ⊆ P.diag ∪ Q := by
    intro x hx
    obtain ⟨hpair, he⟩ := mem_filter.1 hx
    obtain ⟨hp, hq⟩ := mem_product.1 hpair
    by_cases h : x.1 = x.2
    · exact mem_union_left _ (mem_diag.2 ⟨hp, h⟩)
    · exact mem_union_right _ (hc x.1 hp x.2 hq h he)
  have hC : C.card ≤ P.card + Q.card :=
    (card_le_card hSub).trans (by simpa using card_union_le P.diag Q)
  have hsum : (∑ k ∈ F, (L k).card) = P.card := by
    rw [sum_card_fiberwise_eq_card_filter]
    congr 1
    ext x
    exact ⟨fun hx => (mem_filter.1 hx).1, fun hx => mem_filter.2 ⟨hx, mem_image_of_mem f hx⟩⟩
  have henergy : (∑ k ∈ F, (L k).card ^ 2) = C.card := by
    have hfiber (k : ℕ) :
        (C.filter (fun x => f x.1 = k)) = L k ×ˢ L k := by
      ext x
      simp only [C, L, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨hp, hq⟩, he⟩, hk⟩
        exact ⟨⟨hp, hk⟩, ⟨hq, he.symm.trans hk⟩⟩
      · rintro ⟨⟨hp, hp'⟩, ⟨hq, hq'⟩⟩
        exact ⟨⟨⟨hp, hq⟩, hp'.trans hq'.symm⟩, hp'⟩
    calc
      _ = ∑ k ∈ F, (C.filter (fun x => f x.1 = k)).card := by
        apply sum_congr rfl
        intro k _
        rw [hfiber, card_product, pow_two]
      _ = C.card := by
        rw [sum_card_fiberwise_eq_card_filter]
        congr 1
        ext x
        exact ⟨fun h => (mem_filter.1 h).1, fun h =>
          mem_filter.2 ⟨h, mem_image_of_mem f (mem_product.1 (mem_filter.1 h).1).1⟩⟩
  calc
    _ = (∑ k ∈ F, (L k).card) ^ 2 := by rw [hsum]
    _ ≤ F.card * ∑ k ∈ F, (L k).card ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by rw [henergy]; exact Nat.mul_le_mul_left _ hC

private theorem close_of_div_eq {n p q : ℕ} {X : ℝ} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q)
    (hpX : (p : ℝ) ≤ X) (hqX : (q : ℝ) ≤ X) (hX : X ^ 2 = (n : ℝ) * Real.log n)
    (h : n / p = n / q) : |(p : ℝ) - (q : ℝ)| < Real.log n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpx : (p : ℝ) ≤ X) (hqx : (q : ℝ) ≤ X)
      (he : n / p = n / q) : (q : ℝ) - p < Real.log n := by
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hlow : ((n / q : ℕ) : ℝ) ≤ (n : ℝ) / q := by
      apply (le_div_iff₀ hq').2
      exact_mod_cast Nat.div_mul_le_self n q
    have hhi : (n : ℝ) / p < ((n / p : ℕ) : ℝ) + 1 := by
      apply (div_lt_iff₀ hp').2
      exact_mod_cast (Nat.div_lt_iff_lt_mul hp).1 (Nat.lt_succ_self (n / p))
    have h' : (n : ℝ) / p - (n : ℝ) / q < 1 := by rw [he] at hhi; linarith only [hhi, hlow]
    apply (mul_lt_mul_iff_right₀ hn').1
    calc
      (n : ℝ) * ((q : ℝ) - p) = ((n : ℝ) / p - (n : ℝ) / q) * ((p : ℝ) * q) := by
        field_simp
      _ < 1 * ((p : ℝ) * q) := mul_lt_mul_of_pos_right h' (mul_pos hp' hq')
      _ ≤ (n : ℝ) * Real.log n := by
        rw [← hX, one_mul, pow_two]
        exact mul_le_mul hpx hqx hq'.le (hp'.le.trans hpx)
  exact abs_lt.2 ⟨by linarith only [hdiff hp hq hpX hqX h], hdiff hq hp hqX hpX h.symm⟩

def H1 : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    let X := √((n : ℝ) * Real.log n)
    let P := Nat.primesLE ⌊X⌋₊
    c * √((n : ℝ) / Real.log n) ≤ ((P.filter (fun p => p ≤ n ∧ n < p * p)).card : ℝ) ∧
    (P.card : ℝ) ≤ C * √((n : ℝ) / Real.log n)

def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    let P := Nat.primesLE ⌊√((n : ℝ) * Real.log n)⌋₊
    let Q := (P ×ˢ P).filter (fun x => x.1 ≠ x.2 ∧ |(x.1 : ℝ) - (x.2 : ℝ)| < Real.log n)
    (Q.card : ℝ) ≤ C * √((n : ℝ) / Real.log n)

set_option maxHeartbeats 950000 in
theorem main : H1 → H2 → type_of% @Erdos912.erdos_912.variants.selfridge := by
  classical
  intro hprime hpairs
  obtain ⟨c, C, hc, hC, hprime⟩ := hprime
  obtain ⟨D, hD, hpairs⟩ := hpairs
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      (Erdos912.h n : ℝ) ≤ (C + 1) * √((n : ℝ) / Real.log n) ∧
      √((n : ℝ) / Real.log n) ≤ ((C + D) / c ^ 2) * (Erdos912.h n : ℝ) := by
    filter_upwards [hprime, hpairs, hlog.eventually_ge_atTop 1, eventually_ge_atTop (1 : ℕ)] with
      n hprime hpairs hL hn
    let X := √((n : ℝ) * Real.log n)
    let Y := √((n : ℝ) / Real.log n)
    let P := Nat.primesLE ⌊X⌋₊
    let R := P.filter (fun p => p ≤ n ∧ n < p * p)
    let Q := (P ×ˢ P).filter (fun x => x.1 ≠ x.2 ∧ |(x.1 : ℝ) - (x.2 : ℝ)| < Real.log n)
    let e := n.factorial.factorization
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hL' : 0 < Real.log n := zero_lt_one.trans_le hL
    have hX0 : 0 < X := Real.sqrt_pos.2 (mul_pos hn' hL')
    have hY0 : 0 < Y := Real.sqrt_pos.2 (div_pos hn' hL')
    have hX : X ^ 2 = (n : ℝ) * Real.log n := Real.sq_sqrt (mul_nonneg hn'.le hL'.le)
    have hXY : X * Y = (n : ℝ) := by
      dsimp only [X, Y]
      rw [← Real.sqrt_mul (mul_nonneg hn'.le hL'.le)]
      have he : (n : ℝ) * Real.log n * ((n : ℝ) / Real.log n) = (n : ℝ) ^ 2 := by
        field_simp
      rw [he, Real.sqrt_sq hn'.le]
    obtain ⟨hlo, hhi⟩ : c * Y ≤ (R.card : ℝ) ∧ (P.card : ℝ) ≤ C * Y := hprime
    have hQ : (Q.card : ℝ) ≤ D * Y := hpairs
    constructor
    · have hs : e.frange ⊆ P.image e ∪ Icc 1 ⌊Y⌋₊ := by
        intro k hk
        obtain ⟨hk0, p, rfl⟩ := Finsupp.mem_frange.1 hk
        have hpprime : p.Prime := by
          by_contra h
          exact hk0 (Nat.factorization_eq_zero_of_not_prime _ h)
        by_cases hp : p ≤ ⌊X⌋₊
        · exact mem_union_left _ (mem_image_of_mem e (Nat.mem_primesLE.2 ⟨hp, hpprime⟩))
        · have hpX : X < (p : ℝ) := (Nat.floor_lt hX0.le).1 (lt_of_not_ge hp)
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
          have hpsq : n < p * p := by
            have h := mul_lt_mul_of_pos_right hpX hX0
            have h' := mul_le_mul_of_nonneg_left hpX.le hp0.le
            have h'' := mul_le_mul_of_nonneg_left hL hn'.le
            exact_mod_cast (show (n : ℝ) < (p : ℝ) * p by nlinarith only [h, h', h'', hX])
          have hval : ((e p : ℕ) : ℝ) ≤ Y := by
            rw [show e p = n / p from factorization_of_large_prime hpprime hpsq]
            apply (le_of_mul_le_mul_right · hp0)
            calc
              _ ≤ (n : ℝ) := by exact_mod_cast Nat.div_mul_le_self n p
              _ = X * Y := hXY.symm
              _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_right hpX.le hY0.le
          exact mem_union_right _ (mem_Icc.2 ⟨by omega, (Nat.le_floor_iff hY0.le).2 hval⟩)
      have hnat : Erdos912.h n ≤ P.card + ⌊Y⌋₊ := by
        calc
          _ ≤ (P.image e ∪ Icc 1 ⌊Y⌋₊).card := card_le_card hs
          _ ≤ (P.image e).card + (Icc 1 ⌊Y⌋₊).card := card_union_le _ _
          _ ≤ _ := by simpa using Nat.add_le_add_right card_image_le ⌊Y⌋₊
      have hcast : (Erdos912.h n : ℝ) ≤ (P.card : ℝ) + ((⌊Y⌋₊ : ℕ) : ℝ) := by exact_mod_cast hnat
      change (Erdos912.h n : ℝ) ≤ (C + 1) * Y
      linarith only [hcast, hhi, Nat.floor_le hY0.le]
    · have hsub : R.image (fun p => n / p) ⊆ e.frange := by
        intro k hk
        obtain ⟨p, hp, rfl⟩ := mem_image.1 hk
        obtain ⟨hP, hpN, hpn⟩ := mem_filter.1 hp
        have hpprime := Nat.prime_of_mem_primesLE hP
        have hh : e p = n / p := factorization_of_large_prime hpprime hpn
        exact Finsupp.mem_frange.2 ⟨(Nat.div_pos hpN hpprime.pos).ne', p, hh⟩
      have hnenergy := energy_le R (fun p => n / p) Q (fun p hp q hq hne he => by
        have hpP := (mem_filter.1 hp).1
        have hqP := (mem_filter.1 hq).1
        have hpr := Nat.mem_primesLE.1 hpP
        have hqr := Nat.mem_primesLE.1 hqP
        have hpX : (p : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).1 hpr.1
        have hqX : (q : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).1 hqr.1
        exact mem_filter.2 ⟨mem_product.2 ⟨hpP, hqP⟩, hne,
          close_of_div_eq (by omega) hpr.2.pos hqr.2.pos hpX hqX hX he⟩)
      have he' : R.card ^ 2 ≤ Erdos912.h n * (R.card + Q.card) :=
        hnenergy.trans (Nat.mul_le_mul_right _ (card_le_card hsub))
      have hE : (R.card : ℝ) ^ 2 ≤ (Erdos912.h n : ℝ) * ((R.card : ℝ) + Q.card) := by
        exact_mod_cast he'
      have hR : (R.card : ℝ) ≤ C * Y :=
        (show (R.card : ℝ) ≤ P.card by exact_mod_cast card_filter_le P _).trans hhi
      have hsum : (R.card : ℝ) + Q.card ≤ (C + D) * Y := by linarith only [hR, hQ]
      have hlow : (c * Y) ^ 2 ≤ (R.card : ℝ) ^ 2 := by gcongr
      have hmul : c ^ 2 * (Y * Y) ≤ (Erdos912.h n : ℝ) * ((C + D) * Y) := by
        rw [← show (c * Y) ^ 2 = c ^ 2 * (Y * Y) by ring]
        exact hlow.trans (hE.trans (mul_le_mul_of_nonneg_left hsum (by positivity)))
      have hcancel : c ^ 2 * Y ≤ (C + D) * (Erdos912.h n : ℝ) := by
        apply (mul_le_mul_iff_left₀ hY0).1
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      change Y ≤ ((C + D) / c ^ 2) * (Erdos912.h n : ℝ)
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ (sq_pos_of_pos hc)).2 (by simpa [mul_comm] using hcancel)
  constructor
  · refine IsBigO.of_bound (C + 1) ?_
    filter_upwards [hbound] with n hn
    simpa only [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (show (0 : ℝ) ≤ (Erdos912.h n : ℝ) by positivity)] using hn.1
  · refine IsBigO.of_bound ((C + D) / c ^ 2) ?_
    filter_upwards [hbound] with n hn
    simpa only [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (show (0 : ℝ) ≤ (Erdos912.h n : ℝ) by positivity)] using hn.2

end OMA.R_Erdos912_erdos_912_variants_selfridge_R1

end R1Part

section H1Part

/- Chebyshev's bounds at the two prime cutoffs in the Erdős–Selfridge estimate. -/

-- Credit: @dk8827

open Finset Filter
open scoped Topology

namespace OMA.SelfridgePrimeCount

private theorem log_le_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ √x := by
  have h : 0 < √x / 2 := by positivity
  have heq : Real.log (√x / 2) = Real.log x / 2 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx.le]
  linarith only [Real.log_le_sub_one_of_pos h, heq, Real.log_two_lt_d9]

private theorem prime_count_upper {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 5 * x / Real.log x := by
  have hx' : 0 < x := zero_lt_one.trans hx
  have hl : 0 < Real.log x := Real.log_pos hx
  have hroot : √x ≤ x / Real.log x := by
    apply (le_div_iff₀ hl).2
    calc
      _ ≤ √x * √x := mul_le_mul_of_nonneg_left (log_le_sqrt hx') (Real.sqrt_nonneg _)
      _ = x := by rw [← pow_two, Real.sq_sqrt hx'.le]
  have hp := Chebyshev.pi_le_log4_mul_div hx
  rw [Real.log_sqrt hx'.le] at hp
  have hl4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith only [Real.log_two_lt_d9]
  have he : Real.log 4 * x / (Real.log x / 2) = (2 * Real.log 4) * (x / Real.log x) := by ring
  rw [he] at hp
  have hmul := mul_le_mul_of_nonneg_right (show 2 * Real.log 4 ≤ 4 by linarith only [hl4])
    (div_nonneg hx'.le hl.le)
  rw [mul_div_assoc]
  linarith only [hp, hroot, hmul]

private theorem prime_count_lower {x : ℝ} (hx : 256 ≤ x) :
    x / (4 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx1 : 1 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hlogx : Real.log (x + 2) ≤ x / 8 := by
    apply (log_le_sqrt (by linarith : 0 < x + 2)).trans
    apply Real.sqrt_le_iff.2
    refine ⟨by linarith, ?_⟩
    nlinarith only [hx, mul_nonneg (show 0 ≤ x - 256 by linarith) (show 0 ≤ x by linarith)]
  have hmul := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ Real.log 2 by linarith [Real.log_two_gt_d9])
    (show 0 ≤ x - 1 by linarith)
  have hnum : x / 4 ≤ (x - 1) * Real.log 2 - Real.log (x + 2) :=
    by linarith only [hmul, hlogx, hx]
  calc
    x / (4 * Real.log x) = (x / 4) / Real.log x := by ring
    _ ≤ _ := (div_le_div_of_nonneg_right hnum hL.le).trans (Chebyshev.pi_ge' hx1)

set_option maxHeartbeats 800000 in
theorem scaled :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      let X := √((n : ℝ) * Real.log n)
      let P := Nat.primesLE ⌊X⌋₊
      c * √((n : ℝ) / Real.log n) ≤ ((P.filter (fun p => p ≤ n ∧ n < p * p)).card : ℝ) ∧
      (P.card : ℝ) ≤ C * √((n : ℝ) / Real.log n) := by
  refine ⟨1 / 8, 10, by norm_num, by norm_num, ?_⟩
  have hLtop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hLtop.eventually_ge_atTop 10000, eventually_ge_atTop (1 : ℕ)] with n hL hn
  let L := Real.log (n : ℝ)
  let X := √((n : ℝ) * L)
  let Y := √((n : ℝ) / L)
  let Z := √(n : ℝ)
  let E := √L
  let P := Nat.primesLE ⌊X⌋₊
  let Q := Nat.primesLE ⌊Z⌋₊
  let R := P.filter (fun p => p ≤ n ∧ n < p * p)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLn : L ≤ n := by linarith [Real.log_le_sub_one_of_pos hn0]
  have hZ0 : 0 < Z := Real.sqrt_pos.2 hn0
  have hY0 : 0 < Y := Real.sqrt_pos.2 (div_pos hn0 hL0)
  have hX0 : 0 < X := Real.sqrt_pos.2 (mul_pos hn0 hL0)
  have hE0 : 0 < E := Real.sqrt_pos.2 hL0
  have hElo : 100 ≤ E := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 100) hL0.le).2
    norm_num
    exact hL
  have hZlo : 100 ≤ Z := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 100) hn0.le).2
    norm_num
    exact_mod_cast (show (10000 : ℝ) ≤ L from hL).trans hLn
  have hXm : 256 ≤ X := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 256) (mul_nonneg hn0.le hL0.le)).2
    have hN : (10000 : ℝ) ≤ n := (show (10000 : ℝ) ≤ L from hL).trans hLn
    have h := mul_le_mul (show (10000 : ℝ) ≤ n from hN) (show 10000 ≤ L from hL) (by norm_num) hn0.le
    linarith only [h]
  have hZX : Z ≤ X := by
    apply Real.sqrt_le_sqrt
    nlinarith only [mul_le_mul_of_nonneg_left hL1 hn0.le]
  have hXn : X ≤ n := Real.sqrt_le_iff.2 ⟨hn0.le, by
    nlinarith only [mul_le_mul_of_nonneg_left hLn hn0.le]⟩
  have hXY : X = Y * L := by
    calc
      X = √((n : ℝ) / L * L ^ 2) := by
        apply congrArg Real.sqrt
        field_simp
      _ = _ := by rw [Real.sqrt_mul (div_nonneg hn0.le hL0.le), Real.sqrt_sq hL0.le]
  have hZY : Z = Y * E := by
    dsimp only [Z, Y, E]
    rw [← Real.sqrt_mul (div_nonneg hn0.le hL0.le), div_mul_cancel₀ _ hL0.ne']
  have hE2 : E ^ 2 = L := Real.sq_sqrt hL0.le
  have hlogXlo : L / 2 ≤ Real.log X := by
    have h := Real.log_le_log hZ0 hZX
    rwa [show Real.log Z = L / 2 from Real.log_sqrt hn0.le] at h
  have hlogXhi : Real.log X ≤ L := Real.log_le_log hX0 hXn
  have hlogX0 : 0 < Real.log X := by linarith
  have hPhi : (P.card : ℝ) ≤ 10 * Y := by
    rw [Nat.primesLE_card_eq_primeCounting]
    refine (prime_count_upper (show 1 < X by linarith only [hXm])).trans ?_
    apply (div_le_iff₀ hlogX0).2
    nlinarith only [hXY, mul_le_mul_of_nonneg_left hlogXlo hY0.le]
  have hPlo : Y / 4 ≤ (P.card : ℝ) := by
    rw [Nat.primesLE_card_eq_primeCounting]
    refine le_trans ?_ (prime_count_lower hXm)
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.log X)).2
    nlinarith only [hXY, mul_le_mul_of_nonneg_left hlogXhi hY0.le]
  have hQhi : (Q.card : ℝ) ≤ Y / 8 := by
    rw [Nat.primesLE_card_eq_primeCounting]
    refine (prime_count_upper (show 1 < Z by linarith only [hZlo])).trans ?_
    rw [show Real.log Z = L / 2 from Real.log_sqrt hn0.le, hZY]
    apply (div_le_iff₀ (by positivity : 0 < L / 2)).2
    have he : 80 * E ≤ L := by
      have h := mul_le_mul_of_nonneg_right hElo hE0.le
      nlinarith only [h, hE2, hE0]
    nlinarith only [mul_le_mul_of_nonneg_left he hY0.le]
  have hsubset : Q ⊆ P := by
    intro p hp
    obtain ⟨h, hprime⟩ := Nat.mem_primesLE.1 hp
    exact Nat.mem_primesLE.2 ⟨h.trans (Nat.floor_mono hZX), hprime⟩
  have hR : R = P \ Q := by
    ext p
    simp only [R, mem_filter, Finset.mem_sdiff]
    apply and_congr_right
    intro hp
    obtain ⟨hpX, hprime⟩ := Nat.mem_primesLE.1 hp
    have hp' : (p : ℝ) ≤ X := (Nat.le_floor_iff hX0.le).1 hpX
    have hpn : p ≤ n := by exact_mod_cast hp'.trans hXn
    rw [and_iff_right hpn, Nat.mem_primesLE, and_iff_left hprime, Nat.le_floor_iff hZ0.le, not_le]
    change n < p * p ↔ √(n : ℝ) < (p : ℝ)
    rw [Real.sqrt_lt hn0.le (by positivity), pow_two]
    exact_mod_cast Iff.rfl
  have hc := card_sdiff_add_card_eq_card hsubset
  rw [← hR] at hc
  have heq : (R.card : ℝ) + Q.card = P.card := by exact_mod_cast hc
  exact ⟨by change (1 / 8 : ℝ) * Y ≤ (R.card : ℝ); linarith only [hPlo, hQhi, heq], hPhi⟩

end OMA.SelfridgePrimeCount

end H1Part

section H2Part

/- Prime-pair sieve estimates of Daniel Larsen, formalized by Jake Mallen and adapted in PR 2505. The Selberg sieve development incorporates work by Arend Mellendijk, copyright 2023, released under the Apache 2.0 license. -/

namespace Erdos884

/-- `Real.sqrt_le_self` does not exist in Mathlib (only `Nat.sqrt_le_self`).
Reconstructed here from `Real.sqrt_le_left : 0 ≤ y → (√x ≤ y ↔ x ≤ y ^ 2)`. -/
theorem _root_.Real.sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x :=
  (Real.sqrt_le_left (by linarith)).2 (by nlinarith)

section

/- ### Vendored from PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/AuxResults.lean -/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset


namespace ArithmeticFunction.IsMultiplicative
open _root_.ArithmeticFunction.IsMultiplicative

variable {R : Type*}

theorem _root_.ArithmeticFunction.IsMultiplicative.prod_factors_of_mult (f : ArithmeticFunction ℝ)
    (h_mult : ArithmeticFunction.IsMultiplicative f) {l : ℕ} (hl : Squarefree l) :
    ∏ a ∈ l.primeFactors, f a = f l := by
  rw [←IsMultiplicative.map_prod_of_subset_primeFactors h_mult l _ Finset.Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hl]

end ArithmeticFunction.IsMultiplicative

namespace Aux
theorem _root_.Aux.sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem _root_.Aux.ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem _root_.Aux.conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero,
    ←ite_and]
  congr with d1
  congr with d2
  congr
  rw [eq_iff_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩

theorem _root_.Aux.moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)


theorem _root_.Aux.moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←Aux.moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    Aux.sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem _root_.Aux.moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply Aux.moebius_inv_dvd_lower_bound' hP l m hm

theorem _root_.Aux.multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul,
    h_mult.map_mul_of_coprime (coprime_of_squarefree_mul h_sq), h_zero]

theorem _root_.Aux.div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl

theorem _root_.Aux.inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem _root_.Aux.inv_sub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact Aux.inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem _root_.Aux.inv_antitoneOn_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  convert Aux.inv_sub_antitoneOn_gt (R:=R) 0; ring

theorem _root_.Aux.inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert Aux.inv_sub_antitoneOn_Icc a b 0 ha; ring

theorem _root_.Aux.log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply Aux.inv_antitoneOn_Icc
    norm_num

theorem _root_.Aux.log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply Aux.log_add_one_le_sum_inv

theorem _root_.Aux.sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply Aux.inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem _root_.Aux.sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply Aux.sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

-- Lemma 3.1 in Heath-Brown's notes
theorem _root_.Aux.sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_ -- do we need this one?
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_

  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [← sum_filter, Finset.sum_const, ← finMulAntidiag_eq_piFinset_divisors_filter hd.1 hd.2,
      card_finMulAntidiag_of_squarefree <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]; exact fun _ => rfl
      · intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · gcongr with i hi
      rw [if_pos]
      apply le_trans _ h
      norm_cast
      rw [←prod_erase_mul (a:=i) (h:= hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d; rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]; exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff hx_pos.le]
          exact hd.2
      · norm_num
    apply Aux.sum_inv_le_log_real
    linarith

theorem _root_.Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply Aux.sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP


end Aux

/- ### Vendored from PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Basic.lean -/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/



noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve
open _root_.SelbergSieve

variable (s : BoundingSieve)

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound
def _root_.SelbergSieve.selbergTerms : ArithmeticFunction ℝ :=
  s.nu.pmul (.prodPrimeFactors fun p =>  1 / (1 - s.nu p))


theorem _root_.SelbergSieve.selbergTerms_apply (d : ℕ) :
    (SelbergSieve.selbergTerms s) d = s.nu d * ∏ p ∈ d.primeFactors, 1/(1 - s.nu p) := by
  unfold SelbergSieve.selbergTerms
  by_cases h : d=0
  · rw [h]; simp
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply h]

section UpperBoundSieve

structure _root_.SelbergSieve.UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus

instance _root_.SelbergSieve.ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

def _root_.SelbergSieve.IsLowerMoebius (μMinus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, ∑ d ∈ n.divisors, μMinus d ≤ (if n=1 then 1 else 0)

structure _root_.SelbergSieve.LowerBoundSieve where mk ::
  μMinus : ℕ → ℝ
  hμMinus : IsLowerMoebius μMinus

instance _root_.SelbergSieve.lbToμMinus : CoeFun LowerBoundSieve fun _ => ℕ → ℝ where coe lb := lb.μMinus

end UpperBoundSieve

section SieveLemmas

theorem _root_.SelbergSieve.nu_ne_zero_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors s.prodPrimes) : s.nu d ≠ 0 := by
  apply _root_.ne_of_gt
  rw [mem_divisors] at hd
  apply nu_pos_of_dvd_prodPrimes hd.left

def _root_.SelbergSieve.delta (n : ℕ) : ℝ := if n=1 then 1 else 0


theorem _root_.SelbergSieve.siftedSum_as_delta : siftedSum (s := s) = ∑ d ∈ s.support, s.weights d * delta (Nat.gcd s.prodPrimes d) :=
  by
  rw [siftedSum_eq_sum_support_mul_ite]
  simp only [delta]

-- Unused ?
theorem _root_.SelbergSieve.nu_lt_self_of_dvd_prodPrimes (d : ℕ) (hdP : d ∣ s.prodPrimes) (hd_ne_one : d ≠ 1) : s.nu d < 1 :=
  nu_lt_one_of_dvd_prodPrimes hdP hd_ne_one

-- Facts about g
theorem _root_.SelbergSieve.selbergTerms_pos (l : ℕ) (hl : l ∣ s.prodPrimes) : 0 < (SelbergSieve.selbergTerms s) l := by
  rw [SelbergSieve.selbergTerms_apply]
  apply mul_pos
  · exact nu_pos_of_dvd_prodPrimes hl
  apply prod_pos
  intro p hp
  rw [one_div_pos]
  have hp_prime : p.Prime := prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ s.prodPrimes := (Nat.dvd_of_mem_primeFactors hp).trans hl
  linarith only [s.nu_lt_one_of_prime p hp_prime hp_dvd]

theorem _root_.SelbergSieve.selbergTerms_mult : ArithmeticFunction.IsMultiplicative (SelbergSieve.selbergTerms s) := by
  unfold SelbergSieve.selbergTerms
  arith_mult

theorem _root_.SelbergSieve.one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : s.nu l ≠ 0) : 1 / (SelbergSieve.selbergTerms s) l = ∑ d ∈ l.divisors, (μ <| l / d) * (s.nu d)⁻¹ :=
  by
  rw [SelbergSieve.selbergTerms_apply]
  simp only [one_div, prod_inv_distrib, mul_inv, inv_inv]
  rw [(s.nu_mult).prodPrimeFactors_one_sub_of_squarefree _ hl]
  rw [mul_sum]
  apply symm
  rw [← Nat.sum_divisorsAntidiagonal' fun d e : ℕ => ↑(μ d) * (s.nu e)⁻¹]
  rw [Nat.sum_divisorsAntidiagonal fun d e : ℕ => ↑(μ d) * (s.nu e)⁻¹]
  apply sum_congr rfl; intro d hd
  have hd_dvd : d ∣ l := dvd_of_mem_divisors hd
  rw [←Aux.div_mult_of_dvd_squarefree s.nu s.nu_mult l d (dvd_of_mem_divisors hd) hl, inv_div]
  · ring
  revert hnu_nonzero; contrapose!
  exact Aux.multiplicative_zero_of_zero_dvd s.nu s.nu_mult hl hd_dvd

theorem _root_.SelbergSieve.nu_eq_conv_one_div_selbergTerms (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    (s.nu d)⁻¹ = ∑ l ∈ divisors s.prodPrimes, if l ∣ d then 1 / (SelbergSieve.selbergTerms s) l else 0 := by
  apply symm
  rw [←sum_filter, Nat.divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  revert hdP; revert d
  apply (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on _ (fun _ _ => Nat.dvd_trans)).mpr
  intro l _ hlP
  rw [sum_divisorsAntidiagonal' (f:=fun x y => (μ <| x) * (s.nu y)⁻¹) (n:=l)]
  apply symm
  exact one_div_selbergTerms_eq_conv_moebius_nu _ l
    (Squarefree.squarefree_of_dvd hlP s.prodPrimes_squarefree)
    (_root_.ne_of_gt <| nu_pos_of_dvd_prodPrimes hlP)

theorem _root_.SelbergSieve.conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then (SelbergSieve.selbergTerms s) l else 0) = (SelbergSieve.selbergTerms s) d * (s.nu d)⁻¹ := by
  calc
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then (SelbergSieve.selbergTerms s) l else 0) =
        ∑ l ∈ divisors s.prodPrimes, if l ∣ d then (SelbergSieve.selbergTerms s) (d / l) else 0 := by
      rw [← Aux.sum_over_dvd_ite prodPrimes_ne_zero hd,
        ← Nat.sum_divisorsAntidiagonal fun x _ => (SelbergSieve.selbergTerms s) x,
        Nat.sum_divisorsAntidiagonal' fun x _ => (SelbergSieve.selbergTerms s) x, Aux.sum_over_dvd_ite prodPrimes_ne_zero hd]
    _ = (SelbergSieve.selbergTerms s) d * ∑ l ∈ divisors s.prodPrimes, if l ∣ d then 1 / (SelbergSieve.selbergTerms s) l else 0 := by
      rw [mul_sum]; apply sum_congr rfl; intro l hl
      rw [mul_ite_zero]; apply if_ctx_congr Iff.rfl _ (fun _ => rfl); intro h
      rw [← Aux.div_mult_of_dvd_squarefree (SelbergSieve.selbergTerms s) (SelbergSieve.selbergTerms_mult s) d l h]
      · ring
      · apply Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree
      · apply _root_.ne_of_gt; rw [mem_divisors] at hl; apply SelbergSieve.selbergTerms_pos; exact hl.left
    _ = (SelbergSieve.selbergTerms s) d * (s.nu d)⁻¹ := by rw [← nu_eq_conv_one_div_selbergTerms s d hd]

theorem _root_.SelbergSieve.upper_bound_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ ∑ d ∈ divisors s.prodPrimes, μPlus d * multSum (s := s) d :=
  siftedSum_le_sum_of_upperMoebius _ μPlus.hμPlus

theorem _root_.SelbergSieve.siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ s.totalMass * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

end SieveLemmas

-- Results about Lambda Squared Sieves
section LambdaSquared

def _root_.SelbergSieve.lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
    if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

private theorem _root_.SelbergSieve.lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem _root_.SelbergSieve.lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    SelbergSieve.lambdaSquared w d = 0 := by
  dsimp only [SelbergSieve.lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem _root_.SelbergSieve.upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius <| SelbergSieve.lambdaSquared weights := by
  dsimp [IsUpperMoebius, SelbergSieve.lambdaSquared]
  intro n
  have h_sq :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0) =
      (∑ d ∈ n.divisors, weights d) ^ 2 := by
    rw [sq, mul_sum, Aux.conv_lambda_sq_larger_sum _ n, sum_comm]
    apply sum_congr rfl; intro d1 hd1
    rw [sum_mul, sum_comm]
    apply sum_congr rfl; intro d2 hd2
    rw [sum_ite_eq_of_mem']
    · ring
    rw [mem_divisors, Nat.lcm_dvd_iff]
    exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩
  rw [h_sq]
  split_ifs with hn
  · rw [hn]; simp [hw]
  · apply sq_nonneg

-- set_option quotPrecheck false
-- variable (s : Sieve)

-- local notation3 "ν" => Sieve.nu s
-- local notation3 "P" => Sieve.prodPrimes s
-- local notation3 "a" => Sieve.weights s
-- local notation3 "X" => Sieve.totalMass s
-- local notation3 "R" => Sieve.rem s
-- local notation3 "g" => Sieve.selbergTerms s

theorem _root_.SelbergSieve.lambdaSquared_mainSum_eq_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (SelbergSieve.lambdaSquared w) =
      ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
        s.nu d1 * w d1 * s.nu d2 * w d2 * (s.nu (d1.gcd d2))⁻¹ := by
  dsimp only [mainSum, SelbergSieve.lambdaSquared]
  trans (∑ d ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0)
  · rw [sum_congr rfl]; intro d _
    rw [sum_mul, sum_congr rfl]; intro d1 _
    rw [sum_mul, sum_congr rfl]; intro d2 _
    rw [ite_zero_mul]

  trans (∑ d ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0)
  · apply Aux.conv_lambda_sq_larger_sum
  rw [sum_comm, sum_congr rfl]; intro d1 hd1
  rw [sum_comm, sum_congr rfl]; intro d2 hd2
  have h : d1.lcm d2 ∣ s.prodPrimes :=
    Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
  rw [sum_ite_eq_of_mem' (divisors s.prodPrimes) (d1.lcm d2) _ (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩)]
  rw [s.nu_mult.map_lcm]
  · ring
  refine _root_.ne_of_gt (nu_pos_of_dvd_prodPrimes ?_)
  trans d1
  · exact Nat.gcd_dvd_left d1 d2
  · exact dvd_of_mem_divisors hd1

theorem _root_.SelbergSieve.lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (SelbergSieve.lambdaSquared w) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms s) l * (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 :=
  by
  rw [SelbergSieve.lambdaSquared_mainSum_eq_quad_form s w]
  trans (∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes, (∑ l ∈ divisors s.prodPrimes,
          if l ∣ d1.gcd d2 then 1 / (SelbergSieve.selbergTerms s) l * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0))
  · apply sum_congr rfl; intro d1 hd1; apply sum_congr rfl; intro d2 _
    have hgcd_dvd: d1.gcd d2 ∣ s.prodPrimes := Trans.trans (Nat.gcd_dvd_left d1 d2) (dvd_of_mem_divisors hd1)
    rw [SelbergSieve.nu_eq_conv_one_div_selbergTerms s _ hgcd_dvd, mul_sum]
    apply sum_congr rfl; intro l _
    rw [mul_ite_zero]; apply if_congr Iff.rfl _ rfl
    ring
  trans (∑ l ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
        if l ∣ Nat.gcd d1 d2 then 1 / SelbergSieve.selbergTerms s l * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0)
  · apply symm; rw [sum_comm, sum_congr rfl]; intro d1 _
    rw [sum_comm]
  apply sum_congr rfl; intro l _
  rw [sq, sum_mul, mul_sum, sum_congr rfl]; intro d1 _
  rw [mul_sum, mul_sum, sum_congr rfl]; intro d2 _
  rw [ite_zero_mul_ite_zero, mul_ite_zero]
  apply if_congr (Nat.dvd_gcd_iff) _ rfl;
  ring

end LambdaSquared

end SelbergSieve

/- ### Vendored from PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Selberg.lean -/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/



/-
# The Selberg Sieve

This file proves `selberg_bound_simple`, the main theorem of the Selberg.
-/


noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve

variable (s : SelbergSieve)

@[simp]
def _root_.SelbergSieve.selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors s.prodPrimes, if l ^ 2 ≤ (SelbergSieve.level (self := s)) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l else 0


theorem _root_.SelbergSieve.selbergBoundingSum_pos :
    0 < (SelbergSieve.selbergBoundingSum s) := by
  dsimp only [SelbergSieve.selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply SelbergSieve.selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem _root_.SelbergSieve.selbergBoundingSum_ne_zero : (SelbergSieve.selbergBoundingSum s) ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem _root_.SelbergSieve.selbergBoundingSum_nonneg : 0 ≤ (SelbergSieve.selbergBoundingSum s) := _root_.le_of_lt s.selbergBoundingSum_pos

def _root_.SelbergSieve.selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) d * μ d * (SelbergSieve.selbergBoundingSum s)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ (SelbergSieve.level (self := s)) ∧ m.Coprime d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean

theorem _root_.SelbergSieve.selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ s.prodPrimes) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  rw [SelbergSieve.selbergWeights, if_neg hd]

theorem _root_.SelbergSieve.selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ (SelbergSieve.level (self := s))) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  dsimp only [SelbergSieve.selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

theorem _root_.SelbergSieve.selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ (SelbergSieve.selbergWeights s) d * μ d := by
  dsimp only [SelbergSieve.selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) d * (SelbergSieve.selbergBoundingSum s)⁻¹ * ∑ m ∈ divisors s.prodPrimes,
          if (d * m) ^ 2 ≤ (SelbergSieve.level (self := s)) ∧ Coprime m d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| SelbergSieve.selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| SelbergSieve.selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

lemma _root_.SelbergSieve.sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

--Important facts about the selberg weights
theorem _root_.SelbergSieve.selbergWeights_eq_dvds_sum (d : ℕ) :
    s.nu d * (SelbergSieve.selbergWeights s) d =
      (SelbergSieve.selbergBoundingSum s)⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes, if d ∣ l ∧ l ^ 2 ≤ (SelbergSieve.level (self := s)) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l else 0 := by
  by_cases h_dvd : d ∣ s.prodPrimes
  swap
  · dsimp only [SelbergSieve.selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [SelbergSieve.selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  -- change of variables l=m*d
  apply symm
  rw [SelbergSieve.sum_mul_subst d s.prodPrimes]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((s.nu d)⁻¹ * (s.nu d) * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) d * μ d / (SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (SelbergSieve.selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem _root_.SelbergSieve.selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
      if l ^ 2 ≤ (SelbergSieve.level (self := s)) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
        ∑ d ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ (SelbergSieve.level (self := s)) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) k * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [SelbergSieve.selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors s.prodPrimes, if k ^ 2 ≤ (SelbergSieve.level (self := s)) then
            (∑ d ∈ divisors s.prodPrimes, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) k * (SelbergSieve.selbergBoundingSum s)⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ (SelbergSieve.level (self := s)) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors s.prodPrimes) l (fun _ => if l^2 ≤ (SelbergSieve.level (self := s)) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def _root_.SelbergSieve.selbergMuPlus : ℕ → ℝ :=
  SelbergSieve.lambdaSquared (SelbergSieve.selbergWeights s)


theorem _root_.SelbergSieve.weight_one_of_selberg : (SelbergSieve.selbergWeights s) 1 = 1 := by
  dsimp only [SelbergSieve.selbergWeights]
  rw [if_pos (one_dvd s.prodPrimes), s.nu_mult.left, (SelbergSieve.selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, SelbergSieve.selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero

theorem _root_.SelbergSieve.selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ (SelbergSieve.level (self := s))) : (SelbergSieve.selbergMuPlus s) d = 0 := by
  apply SelbergSieve.lambdaSquared_eq_zero_of_support _ (SelbergSieve.level (self := s)) _ d hd
  apply s.selbergWeights_eq_zero

def _root_.SelbergSieve.selbergUbSieve : SelbergSieve.UpperBoundSieve :=
  ⟨(SelbergSieve.selbergMuPlus s), SelbergSieve.upperMoebius_of_lambda_sq (SelbergSieve.selbergWeights s) (s.weight_one_of_selberg)⟩

-- proved for general lambda squared sieves
theorem _root_.SelbergSieve.mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l *
          (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) ^ 2 :=
  by apply SelbergSieve.lambdaSquared_mainSum_eq_diag_quad_form

theorem _root_.SelbergSieve.selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) = (SelbergSieve.selbergBoundingSum s)⁻¹ := by
  rw [SelbergSieve.mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors s.prodPrimes, (if l ^ 2 ≤ (SelbergSieve.level (self := s)) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/(SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l * (μ l:ℝ)^2  * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| SelbergSieve.selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [SelbergSieve.selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply SelbergSieve.selbergBoundingSum_pos

lemma _root_.SelbergSieve.eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _root_.SelbergSieve._helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors s.prodPrimes) (hm : m ∈ divisors s.prodPrimes) :
    k * m ∣ s.prodPrimes ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ (SelbergSieve.level (self := s)) ↔
    (k * m) ^ 2 ≤ (SelbergSieve.level (self := s)) ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact SelbergSieve.eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem _root_.SelbergSieve.selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    (SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
  calc
  _ = (∑ k ∈ divisors s.prodPrimes, ∑ l ∈ divisors s.prodPrimes, if k = d.gcd l ∧ l ^ 2 ≤ (SelbergSieve.level (self := s)) then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) l else 0) := by
    dsimp only [SelbergSieve.selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) k * ∑ m ∈ divisors s.prodPrimes, if (k * m) ^ 2 ≤ (SelbergSieve.level (self := s)) ∧ m.Coprime d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [SelbergSieve.sum_mul_subst k s.prodPrimes, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (SelbergSieve.selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors s.prodPrimes, if k ∣ d
          then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) k * ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ (SelbergSieve.level (self := s)) ∧ m.Coprime d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| SelbergSieve.selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| SelbergSieve.selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| SelbergSieve.selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, SelbergSieve.conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans ((SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) d * (∑ m ∈ divisors s.prodPrimes, if (d*m) ^ 2 ≤ (SelbergSieve.level (self := s)) ∧
      Coprime m d then (SelbergSieve.selbergTerms (SelbergSieve.toBoundingSieve (self := s))) m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [SelbergSieve.selbergWeights]; rw [if_pos hdP]
    ring

theorem _root_.SelbergSieve.selberg_bound_weights (d : ℕ) : |(SelbergSieve.selbergWeights s) d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*(SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : (SelbergSieve.selbergWeights s) d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]


theorem _root_.SelbergSieve.selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors s.prodPrimes) :
    |(SelbergSieve.selbergMuPlus s) n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [SelbergSieve.selbergMuPlus, SelbergSieve.lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| (SelbergSieve.selbergWeights s) d2)
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem _root_.SelbergSieve.selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) ≤
      ∑ d ∈ divisors s.prodPrimes, if (d : ℝ) ≤ (SelbergSieve.level (self := s)) then (3:ℝ) ^ ω d * |s.rem d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| s.rem d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem _root_.SelbergSieve.selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      s.totalMass / (SelbergSieve.selbergBoundingSum s) +
        ∑ d ∈ divisors s.prodPrimes, if (d : ℝ) ≤ (SelbergSieve.level (self := s)) then (3:ℝ) ^ ω d * |s.rem d| else 0 := by
  let μPlus := SelbergSieve.selbergUbSieve s
  calc
    siftedSum ≤ s.totalMass * mainSum μPlus + errSum μPlus :=
      SelbergSieve.siftedSum_le_mainSum_errSum_of_UpperBoundSieve _ μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve

/- ### Vendored from PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean -/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/





/-
# Bounds for the Selberg sieve
This file proves a number of results to help bound `Sieve.selbergSum`

## Main Results
* `selbergBoundingSum_ge_sum_div`: If `ν` is completely multiplicative then `S ≥ ∑_{n ≤ √y}, ν n`
* `boundingSum_ge_log`: If `ν n = 1 / n` then `S ≥ log y / 2`
* `rem_sum_le_of_const`: If `R_d ≤ C` then the error term is at most `C * y * (1 + log y)^3`
-/


open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

noncomputable section
namespace Sieve

lemma _root_.Sieve.prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)]
      at h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| symm <| (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd this
    have heq : p = q := by
      rw [←Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1

lemma _root_.Sieve.primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply Sieve.prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter];
  exact fun _ h => h.2

theorem _root_.Sieve.prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    obtain ⟨q, hq⟩ : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      hp.prime.exists_mem_finset_dvd h
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

theorem _root_.Sieve.siftedSum_eq (s : SelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1) (z : ℝ)
    (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    siftedSum (s := s.toBoundingSieve) =
    (s.support.filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr
  · rw [hP]
    ext d; constructor
    · intro hd
      rw [Finset.mem_filter] at *
      constructor
      · exact hd.1
      · intro p hpp hpy
        rw [←Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.Coprime.coprime_dvd_left _ hd.2
        rw [Sieve.prime_dvd_primorial_iff _ _ hpp]
        apply Nat.le_floor hpy
    · intro h
      rw [Finset.mem_filter] at *
      constructor
      · exact h.1
      refine Nat.coprime_of_dvd ?_
      intro p hp
      erw [Sieve.prime_dvd_primorial_iff _ _ hp]
      intro hpy
      apply h.2 p hp
      trans ↑(Nat.floor z)
      · norm_cast
      · apply Nat.floor_le
        linarith only [hz]
  simp_rw [Nat.cast_one]
  intro x hx
  simp only [Finset.mem_filter] at hx
  apply hw x hx.1

theorem _root_.Sieve.prod_primes_dvd_of_dvd (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

end Sieve
end

end
end
end

end

section
/-
# Erdős 884 — Lemma B auxiliary sums (TauBound and B.4)

Exports:
* `sum_inv_le_one_add_log` : `∑_{1 ≤ e ≤ y} 1/e ≤ 1 + log y`
* `sum_pow_primeFactors_le` : `∑_{1 ≤ d ≤ y} c^{ω(d)} ≤ y (1 + log y)^{c-1}` for `c ≥ 1`
* `sum_totient_ratio_sq_le` : `∑_{1 ≤ h ≤ N} (h/φ(h))² ≤ 200 N`
-/


/- ### Harmonic sum: `∑_{e ≤ y} 1/e ≤ 1 + log y` -/

lemma one_add_log_natCast_nonneg (y : ℕ) : (0:ℝ) ≤ 1 + Real.log y := by
  have := Real.log_natCast_nonneg y
  linarith

theorem sum_inv_le_one_add_log (y : ℕ) :
    ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹ ≤ 1 + Real.log y := by
  have h1 : ((harmonic y : ℚ) : ℝ) = ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [← h1]
  exact_mod_cast harmonic_le_one_add_log y

/- ### Telescoping: `∑_{2 ≤ n ≤ M} 2/(n-1)² ≤ 4 - 4/M` -/

lemma sum_two_div_sq_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 2 M, 2 / (((n:ℝ) - 1) ^ 2) ≤ 4 - 4 / (M:ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega)]
    norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1)]
    have hM' : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    have hM0 : (0:ℝ) < (M:ℝ) := by linarith
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by linarith
    have key : 2 / ((M:ℝ)) ^ 2 ≤ 4 / (M:ℝ) - 4 / ((M:ℝ) + 1) := by
      rw [div_sub_div _ _ hM0.ne' hM1.ne']
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((M:ℝ) - 1)]
    push_cast
    have e1 : (M:ℝ) + 1 - 1 = (M:ℝ) := by ring
    rw [e1]
    linarith [ih]

/- ### Pointwise bound `(c+1)^{ω d} ≤ ∑_{e ∣ d} c^{ω e}` -/

lemma pow_card_powerset_expand (c : ℕ) (P : Finset ℕ) :
    ((c:ℝ) + 1) ^ P.card = ∑ S ∈ P.powerset, (c:ℝ) ^ S.card := by
  classical
  calc ((c:ℝ) + 1) ^ P.card
      = ∏ _p ∈ P, ((c:ℝ) + 1) := by rw [Finset.prod_const]
    _ = ∑ S ∈ P.powerset, (∏ _p ∈ S, (c:ℝ)) * ∏ _p ∈ P \ S, 1 := Finset.prod_add _ _ _
    _ = ∑ S ∈ P.powerset, (c:ℝ) ^ S.card := by simp [Finset.prod_const]

lemma pow_omega_le_sum_divisors (c : ℕ) {d : ℕ} (hd : d ≠ 0) :
    ((c:ℝ) + 1) ^ d.primeFactors.card
      ≤ ∑ e ∈ d.divisors, (c:ℝ) ^ e.primeFactors.card := by
  classical
  have hprime : ∀ S ∈ d.primeFactors.powerset, ∀ p ∈ S, Nat.Prime p := fun S hS p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hS hp)
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p) ↑d.primeFactors.powerset := by
    intro S hS T hT hST
    rw [Finset.mem_coe] at hS hT
    have h1 := Nat.primeFactors_prod (hprime S hS)
    have h2 := Nat.primeFactors_prod (hprime T hT)
    dsimp only at hST
    rw [← h1, ← h2, hST]
  calc ((c:ℝ) + 1) ^ d.primeFactors.card
      = ∑ S ∈ d.primeFactors.powerset, (c:ℝ) ^ S.card := pow_card_powerset_expand c _
    _ = ∑ S ∈ d.primeFactors.powerset, (c:ℝ) ^ (∏ p ∈ S, p).primeFactors.card :=
        Finset.sum_congr rfl fun S hS => by rw [Nat.primeFactors_prod (hprime S hS)]
    _ = ∑ e ∈ d.primeFactors.powerset.image (fun S => ∏ p ∈ S, p),
          (c:ℝ) ^ e.primeFactors.card :=
        (Finset.sum_image (f := fun e => (c:ℝ) ^ e.primeFactors.card) hinj).symm
    _ ≤ ∑ e ∈ d.divisors, (c:ℝ) ^ e.primeFactors.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          rw [Finset.mem_image] at he
          obtain ⟨S, hS, rfl⟩ := he
          rw [Nat.mem_divisors]
          exact ⟨(Finset.prod_dvd_prod_of_subset S d.primeFactors (fun p => p)
            (Finset.mem_powerset.mp hS)).trans (Nat.prod_primeFactors_dvd d), hd⟩
        · intro e _ _
          positivity

/- ### Hyperbola-style swap for `∑_{d ≤ y} ∑_{ef = d}` -/

lemma sum_sum_divisorsAntidiagonal_le (F : ℕ → ℝ) (_hF : ∀ n, 0 ≤ F n) (y : ℕ) :
    ∑ d ∈ Finset.Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p.2
      ≤ ∑ e ∈ Finset.Icc 1 y, ∑ f ∈ Finset.Icc 1 (y / e), F f := by
  classical
  have swap : ∑ d ∈ Finset.Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p.2
      = ∑ p ∈ (Finset.Icc 1 y ×ˢ Finset.Icc 1 y).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ y),
          ∑ _d ∈ ({p.1 * p.2} : Finset ℕ), F p.2 := by
    apply Finset.sum_comm'
    intro d p
    simp only [Nat.mem_divisorsAntidiagonal, Finset.mem_Icc, Finset.mem_filter,
      Finset.mem_product, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd1, hd2⟩, heq, hne⟩
      have hp1 : 1 ≤ p.1 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← heq, h, zero_mul])
      have hp2 : 1 ≤ p.2 := Nat.one_le_iff_ne_zero.mpr fun h => hne (by rw [← heq, h, mul_zero])
      have hle1 : p.1 ≤ y :=
        le_trans (le_trans (le_mul_of_one_le_right (Nat.zero_le _) hp2) heq.le) hd2
      have hle2 : p.2 ≤ y :=
        le_trans (le_trans (le_mul_of_one_le_left (Nat.zero_le _) hp1) heq.le) hd2
      exact ⟨heq.symm, ⟨⟨hp1, hle1⟩, hp2, hle2⟩, le_of_eq_of_le heq hd2⟩
    · rintro ⟨hdeq, ⟨⟨hp11, hp12⟩, hp21, hp22⟩, hmul⟩
      subst hdeq
      refine ⟨⟨?_, hmul⟩, rfl, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · exact Nat.mul_ne_zero (by omega) (by omega)
  have hdisj : (↑(Finset.Icc 1 y) : Set ℕ).PairwiseDisjoint
      (fun e => ({e} : Finset ℕ) ×ˢ Finset.Icc 1 (y / e)) := by
    intro e1 _ e2 _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton] at h1 h2
    exact hne (h1.1.symm.trans h2.1)
  have hTU : (Finset.Icc 1 y ×ˢ Finset.Icc 1 y).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ y)
      = (Finset.Icc 1 y).biUnion (fun e => ({e} : Finset ℕ) ×ˢ Finset.Icc 1 (y / e)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨ha1, ha2⟩, hb1, hb2⟩, hab⟩
      exact ⟨a, ⟨ha1, ha2⟩, rfl,
        hb1, (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr (by rw [mul_comm]; exact hab)⟩
    · rintro ⟨e, ⟨he1, he2⟩, rfl, hb1, hb2⟩
      have hba : b * a ≤ y := (Nat.le_div_iff_mul_le (by omega : 0 < a)).mp hb2
      exact ⟨⟨⟨he1, he2⟩, hb1, le_trans hb2 (Nat.div_le_self y a)⟩,
        by rw [mul_comm]; exact hba⟩
  rw [swap]
  simp only [Finset.sum_singleton]
  rw [hTU, Finset.sum_biUnion hdisj]
  apply le_of_eq
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_product]
  simp

/- ### TauBound: `∑_{d ≤ y} c^{ω(d)} ≤ y (1 + log y)^{c-1}` -/

theorem sum_pow_primeFactors_le (c y : ℕ) (hc : 1 ≤ c) :
    ∑ d ∈ Finset.Icc 1 y, (c:ℝ) ^ (d.primeFactors.card) ≤ (y:ℝ) * (1 + Real.log y)^(c-1) := by
  induction c, hc using Nat.le_induction generalizing y with
  | base => simp [Nat.card_Icc]
  | succ c hc ih =>
    have step1 : ∑ d ∈ Finset.Icc 1 y, ((c:ℝ) + 1) ^ d.primeFactors.card
        ≤ ∑ d ∈ Finset.Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, (c:ℝ) ^ p.2.primeFactors.card := by
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hconv : ∑ p ∈ d.divisorsAntidiagonal, (c:ℝ) ^ p.2.primeFactors.card
          = ∑ e ∈ d.divisors, (c:ℝ) ^ e.primeFactors.card := by
        rw [Nat.sum_divisorsAntidiagonal (M := ℝ)
          (fun _ j => (c:ℝ) ^ j.primeFactors.card) (n := d)]
        exact Nat.sum_div_divisors (α := ℝ) d (fun e => (c:ℝ) ^ e.primeFactors.card)
      rw [hconv]
      exact pow_omega_le_sum_divisors c (by omega)
    have step2 := sum_sum_divisorsAntidiagonal_le (fun n => (c:ℝ) ^ n.primeFactors.card)
      (fun n => by positivity) y
    have step3 : ∑ e ∈ Finset.Icc 1 y, ∑ f ∈ Finset.Icc 1 (y / e), (c:ℝ) ^ f.primeFactors.card
        ≤ ∑ e ∈ Finset.Icc 1 y, (y:ℝ) / e * (1 + Real.log y) ^ (c - 1) := by
      apply Finset.sum_le_sum
      intro e he
      rw [Finset.mem_Icc] at he
      have h1 : (((y / e : ℕ)):ℝ) ≤ (y:ℝ) / e := Nat.cast_div_le
      have hde : 1 ≤ y / e := (Nat.one_le_div_iff (by omega)).mpr he.2
      have h2 : Real.log ((y / e : ℕ):ℝ) ≤ Real.log (y:ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hde
        · exact_mod_cast Nat.div_le_self y e
      have h3 : (0:ℝ) ≤ 1 + Real.log ((y / e : ℕ):ℝ) := one_add_log_natCast_nonneg _
      calc ∑ f ∈ Finset.Icc 1 (y / e), (c:ℝ) ^ f.primeFactors.card
          ≤ ((y / e : ℕ):ℝ) * (1 + Real.log ((y / e : ℕ):ℝ)) ^ (c - 1) := ih (y / e)
        _ ≤ (y:ℝ) / e * (1 + Real.log (y:ℝ)) ^ (c - 1) := by
            apply mul_le_mul h1 _ (pow_nonneg h3 _) (by positivity)
            exact pow_le_pow_left₀ h3 (by linarith) _
    have step5 : ∑ e ∈ Finset.Icc 1 y, (y:ℝ) / e * (1 + Real.log y) ^ (c - 1)
        ≤ (y:ℝ) * (1 + Real.log y) ^ c := by
      have h0 : (0:ℝ) ≤ 1 + Real.log y := one_add_log_natCast_nonneg y
      have hb : (0:ℝ) ≤ (y:ℝ) * (1 + Real.log y) ^ (c - 1) :=
        mul_nonneg (Nat.cast_nonneg y) (pow_nonneg h0 _)
      have hrw : ∑ e ∈ Finset.Icc 1 y, (y:ℝ) / e * (1 + Real.log y) ^ (c - 1)
          = (y:ℝ) * (1 + Real.log y) ^ (c - 1) * ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [div_eq_mul_inv]
        ring
      rw [hrw]
      calc (y:ℝ) * (1 + Real.log y) ^ (c - 1) * ∑ e ∈ Finset.Icc 1 y, ((e:ℝ))⁻¹
          ≤ (y:ℝ) * (1 + Real.log y) ^ (c - 1) * (1 + Real.log y) :=
            mul_le_mul_of_nonneg_left (sum_inv_le_one_add_log y) hb
        _ = (y:ℝ) * (1 + Real.log y) ^ (c - 1 + 1) := by rw [pow_succ]; ring
        _ = (y:ℝ) * (1 + Real.log y) ^ c := by rw [Nat.sub_add_cancel hc]
    rw [Nat.add_sub_cancel]
    push_cast
    exact le_trans step1 (le_trans step2 (le_trans step3 step5))

/- ### B.4: `∑_{h ≤ N} (h/φ(h))² ≤ 200 N` -/

/-- The weight `(2p-1)/(p-1)²`, so that `(p/(p-1))² = 1 + totientWeight p`. -/
noncomputable def totientWeight (p : ℕ) : ℝ := (2 * (p:ℝ) - 1) / ((p:ℝ) - 1) ^ 2

lemma totientWeight_nonneg {p : ℕ} (hp : 2 ≤ p) : 0 ≤ totientWeight p := by
  have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  unfold totientWeight
  apply div_nonneg
  · linarith
  · positivity

/-- Expansion of a product of `1 + g p` as a sum over subsets. -/
lemma prod_one_add_expand (P : Finset ℕ) (g : ℕ → ℝ) :
    ∏ p ∈ P, (1 + g p) = ∑ S ∈ P.powerset, ∏ p ∈ S, g p := by
  classical
  calc ∏ p ∈ P, (1 + g p)
      = ∏ p ∈ P, (g p + 1) := Finset.prod_congr rfl fun p _ => add_comm 1 (g p)
    _ = ∑ S ∈ P.powerset, (∏ p ∈ S, g p) * ∏ p ∈ P \ S, 1 := Finset.prod_add _ _ _
    _ = ∑ S ∈ P.powerset, ∏ p ∈ S, g p := by simp

/-- `(h/φ(h))² = ∏_{p ∣ h} (1 + (2p-1)/(p-1)²)`. -/
lemma totient_ratio_sq_eq_prod {h : ℕ} (hh : 1 ≤ h) :
    ((h:ℝ) / (Nat.totient h)) ^ 2 = ∏ p ∈ h.primeFactors, (1 + totientWeight p) := by
  have hφpos : 0 < Nat.totient h := Nat.totient_pos.mpr (by omega)
  have hφ : (0:ℝ) < (Nat.totient h : ℝ) := by exact_mod_cast hφpos
  have hfac : ∀ p ∈ h.primeFactors, (2:ℝ) ≤ (p:ℝ) := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hprodpos : (0:ℝ) < ∏ p ∈ h.primeFactors, ((p:ℝ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have := hfac p hp
    linarith
  have hkeyR : (Nat.totient h : ℝ) * ∏ p ∈ h.primeFactors, (p:ℝ)
      = (h:ℝ) * ∏ p ∈ h.primeFactors, ((p:ℝ) - 1) := by
    have hcast : ∏ p ∈ h.primeFactors, ((p:ℝ) - 1)
        = ((∏ p ∈ h.primeFactors, (p - 1) : ℕ) : ℝ) := by
      push_cast
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.cast_pred (Nat.prime_of_mem_primeFactors hp).pos]
    have hcast2 : ∏ p ∈ h.primeFactors, (p:ℝ) = ((∏ p ∈ h.primeFactors, p : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [hcast, hcast2]
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Nat.totient_mul_prod_primeFactors h)
  have hratio : (h:ℝ) / (Nat.totient h : ℝ)
      = ∏ p ∈ h.primeFactors, ((p:ℝ) / ((p:ℝ) - 1)) := by
    rw [Finset.prod_div_distrib]
    rw [div_eq_div_iff hφ.ne' hprodpos.ne']
    linear_combination -hkeyR
  rw [hratio, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h2 := hfac p hp
  have hne : (p:ℝ) - 1 ≠ 0 := by linarith
  unfold totientWeight
  field_simp
  ring

/-- Swap the sum over `h` and over subsets of prime factors of `h`. -/
lemma totient_powerset_swap (N : ℕ) (g : Finset ℕ → ℝ) :
    ∑ h ∈ Finset.Icc 1 N, ∑ S ∈ h.primeFactors.powerset, g S
      = ∑ S ∈ ((Finset.Icc 1 N).filter Nat.Prime).powerset,
          ∑ _h ∈ (Finset.Icc 1 N).filter (fun h => (∏ p ∈ S, p) ∣ h), g S := by
  classical
  apply Finset.sum_comm'
  intro h S
  simp only [Finset.mem_Icc, Finset.mem_powerset, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, h2⟩, hS⟩
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, ?_⟩
    · exact (Finset.prod_dvd_prod_of_subset S h.primeFactors (fun p => p) hS).trans
        (Nat.prod_primeFactors_dvd h)
    · intro p hp
      have hp' := hS hp
      rw [Nat.mem_primeFactors] at hp'
      obtain ⟨hpp, hpd, -⟩ := hp'
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpp.one_lt.le, (Nat.le_of_dvd (by omega) hpd).trans h2⟩, hpp⟩
  · rintro ⟨⟨⟨h1, h2⟩, hdvd⟩, hS⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    intro p hp
    have hpP := hS hp
    rw [Finset.mem_filter] at hpP
    rw [Nat.mem_primeFactors]
    exact ⟨hpP.2, dvd_trans (Finset.dvd_prod_of_mem (fun p => p) hp) hdvd, by omega⟩

lemma exp_four_le_55 : Real.exp 4 ≤ 55 := by
  have h1 : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [Real.exp_one_pow]
    norm_num
  rw [h4]
  calc Real.exp 1 ^ 4 ≤ (2.7182818286:ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h1 4
    _ ≤ 55 := by norm_num

theorem sum_totient_ratio_sq_le (N : ℕ) :
    ∑ h ∈ Finset.Icc 1 N, ((h:ℝ) / (Nat.totient h))^2 ≤ 200 * N := by
  classical
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  set P := (Finset.Icc 1 N).filter Nat.Prime with hPdef
  have hPprime : ∀ p ∈ P, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have hSprime : ∀ S ∈ P.powerset, ∀ p ∈ S, Nat.Prime p := fun S hS p hp =>
    hPprime p (Finset.mem_powerset.mp hS hp)
  have hwtS : ∀ S ∈ P.powerset, 0 ≤ ∏ p ∈ S, totientWeight p := fun S hS =>
    Finset.prod_nonneg fun p hp => totientWeight_nonneg (hSprime S hS p hp).two_le
  -- the exponent bound
  have hexp4 : ∑ p ∈ P, totientWeight p / (p:ℝ) ≤ 4 := by
    have hstep : ∀ p ∈ P, totientWeight p / (p:ℝ) ≤ 2 / (((p:ℝ) - 1) ^ 2) := by
      intro p hp
      have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast (hPprime p hp).two_le
      have hp1 : (0:ℝ) < (p:ℝ) - 1 := by linarith
      have hp0 : (0:ℝ) < (p:ℝ) := by linarith
      unfold totientWeight
      rw [div_div, div_le_div_iff₀ (mul_pos (pow_pos hp1 2) hp0) (pow_pos hp1 2)]
      nlinarith [sq_nonneg ((p:ℝ) - 1)]
    calc ∑ p ∈ P, totientWeight p / (p:ℝ)
        ≤ ∑ p ∈ P, 2 / (((p:ℝ) - 1) ^ 2) := Finset.sum_le_sum hstep
      _ ≤ ∑ n ∈ Finset.Icc 2 N, 2 / (((n:ℝ) - 1) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            rw [Finset.mem_Icc]
            exact ⟨(hPprime p hp).two_le, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩
          · intro n _ _
            positivity
      _ ≤ 4 - 4 / (N:ℝ) := sum_two_div_sq_le N hN
      _ ≤ 4 := by
          have : (0:ℝ) ≤ 4 / (N:ℝ) := by positivity
          linarith
  -- rewrite the summand and swap
  have hstep1 : ∑ h ∈ Finset.Icc 1 N, ((h:ℝ) / (Nat.totient h)) ^ 2
      = ∑ S ∈ P.powerset, ∑ h ∈ (Finset.Icc 1 N).filter (fun h => (∏ p ∈ S, p) ∣ h),
          ∏ p ∈ S, totientWeight p := by
    rw [← totient_powerset_swap N (fun S => ∏ p ∈ S, totientWeight p)]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [totient_ratio_sq_eq_prod (Finset.mem_Icc.mp hh).1, prod_one_add_expand]
  -- count multiples of ∏ S
  have hcount : ∀ S ∈ P.powerset,
      ∑ h ∈ (Finset.Icc 1 N).filter (fun h => (∏ p ∈ S, p) ∣ h), ∏ p ∈ S, totientWeight p
        = ((N / ∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p := by
    intro S _
    rw [Finset.sum_const]
    rw [show Finset.Icc 1 N = Finset.Ioc 0 N from rfl, Nat.Ioc_filter_dvd_card_eq_div]
    rw [nsmul_eq_mul]
  rw [hstep1, Finset.sum_congr rfl hcount]
  calc ∑ S ∈ P.powerset, ((N / ∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p
      ≤ ∑ S ∈ P.powerset, (N:ℝ) * ∏ p ∈ S, (totientWeight p / (p:ℝ)) := by
        apply Finset.sum_le_sum
        intro S hS
        have h1 : ((N / ∏ p ∈ S, p : ℕ) : ℝ) ≤ (N:ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) :=
          Nat.cast_div_le
        calc ((N / ∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p
            ≤ (N:ℝ) / ((∏ p ∈ S, p : ℕ) : ℝ) * ∏ p ∈ S, totientWeight p :=
              mul_le_mul_of_nonneg_right h1 (hwtS S hS)
          _ = (N:ℝ) * ∏ p ∈ S, (totientWeight p / (p:ℝ)) := by
              rw [Nat.cast_prod, Finset.prod_div_distrib]
              ring
    _ = (N:ℝ) * ∑ S ∈ P.powerset, ∏ p ∈ S, (totientWeight p / (p:ℝ)) := by
        rw [Finset.mul_sum]
    _ = (N:ℝ) * ∏ p ∈ P, (1 + totientWeight p / (p:ℝ)) := by
        rw [prod_one_add_expand]
    _ ≤ (N:ℝ) * ∏ p ∈ P, Real.exp (totientWeight p / (p:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hN0
        apply Finset.prod_le_prod
        · intro p hp
          have hw := totientWeight_nonneg (hPprime p hp).two_le
          have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (hPprime p hp).pos
          positivity
        · intro p hp
          have := Real.add_one_le_exp (totientWeight p / (p:ℝ))
          linarith
    _ = (N:ℝ) * Real.exp (∑ p ∈ P, totientWeight p / (p:ℝ)) := by
        rw [Real.exp_sum]
    _ ≤ (N:ℝ) * Real.exp 4 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp4) hN0
    _ ≤ 200 * (N:ℝ) := by
        nlinarith [exp_four_le_55, hN0, Real.exp_pos (4:ℝ)]


end

section
/-
# Erdős 884 — Lemma B.3: lower bound for the weighted sum over squarefree numbers
coprime to `m`.

Exports `Erdos884.coprime_squarefree_sum_lower`:
`∃ c₀ > 0, ∃ w₀, ∀ w ≥ w₀, ∀ m ≥ 1 with m ≤ (log w)³,`
`  c₀ · (φ(m)/m)² · (log w)² ≤ Σ_{ℓ ≤ w, squarefree, coprime to m} 2^ω(ℓ)/ℓ`.
-/


open Finset

/- ## Counting integers coprime to `m` in intervals -/

/-- A general "sum over an injection" helper. -/
lemma cs_sum_le_sum_inj {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    (e : α → β) (f : α → ℝ) (g : β → ℝ)
    (hmaps : ∀ a ∈ s, e a ∈ t) (hinj : Set.InjOn e ↑s)
    (hval : ∀ a ∈ s, f a ≤ g (e a)) (hg : ∀ b ∈ t, 0 ≤ g b) :
    ∑ a ∈ s, f a ≤ ∑ b ∈ t, g b := by
  calc ∑ a ∈ s, f a ≤ ∑ a ∈ s, g (e a) := Finset.sum_le_sum hval
    _ = ∑ b ∈ s.image e, g b := (Finset.sum_image hinj).symm
    _ ≤ ∑ b ∈ t, g b := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.image_subset_iff.mpr hmaps) (fun b hb _ => hg b hb)

/-- Exact count of integers coprime to `m` in a run of `q` full blocks of length `m`. -/
lemma cs_cnt_blocks (m n q : ℕ) :
    ((Finset.Ico n (n + q * m)).filter (fun a => Nat.Coprime a m)).card = q * m.totient := by
  induction q with
  | zero => simp
  | succ k ih =>
    have hblock : ((Finset.Ico (n + k * m) (n + k * m + m)).filter
        (fun a => Nat.Coprime a m)).card = m.totient := by
      rw [show (Finset.filter (fun a => Nat.Coprime a m)
            (Finset.Ico (n + k * m) (n + k * m + m)))
          = (Finset.filter (fun x => Nat.Coprime m x)
            (Finset.Ico (n + k * m) (n + k * m + m))) from
        Finset.filter_congr (fun x _ => Nat.coprime_comm)]
      exact Nat.filter_coprime_Ico_eq_totient m (n + k * m)
    have hkey : n + (k + 1) * m = (n + k * m) + m := by ring
    rw [hkey, ← Finset.Ico_union_Ico_eq_Ico (a := n) (b := n + k * m) (c := n + k * m + m)
        (by omega) (by omega), Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)),
      ih, hblock]
    ring

/-- Upper bound for the number of integers coprime to `m` in any interval of length `L`. -/
lemma cs_cnt_upper (m : ℕ) (hm : 0 < m) (n L : ℕ) :
    ((Finset.Ico n (n + L)).filter (fun a => Nat.Coprime a m)).card
      ≤ (L / m + 1) * m.totient := by
  have hL : L < (L / m + 1) * m := by
    have h1 := Nat.div_add_mod L m
    have h2 : L % m < m := Nat.mod_lt L hm
    calc L = m * (L / m) + L % m := h1.symm
      _ < m * (L / m) + m := by omega
      _ = (L / m + 1) * m := by ring
  have hsub : Finset.Ico n (n + L) ⊆ Finset.Ico n (n + (L / m + 1) * m) :=
    Finset.Ico_subset_Ico le_rfl (by omega)
  exact le_of_le_of_eq (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
    (cs_cnt_blocks m n (L / m + 1))

/-- Lower bound for the number of integers coprime to `m` in the block `(v, 2v]`. -/
lemma cs_cnt_lower (m v : ℕ) :
    (v / m) * m.totient ≤ ((Finset.Ioc v (2 * v)).filter (fun a => Nat.Coprime a m)).card := by
  have hsub : Finset.Ico (v + 1) (v + 1 + (v / m) * m) ⊆ Finset.Ioc v (2 * v) := by
    intro a ha
    simp only [Finset.mem_Ico] at ha
    simp only [Finset.mem_Ioc]
    have := Nat.div_mul_le_self v m
    omega
  calc (v / m) * m.totient
      = ((Finset.Ico (v + 1) (v + 1 + (v / m) * m)).filter (fun a => Nat.Coprime a m)).card :=
        (cs_cnt_blocks m (v + 1) (v / m)).symm
    _ ≤ _ := Finset.card_le_card (Finset.filter_subset_filter _ hsub)

lemma cs_two_mul_div_le (A c : ℕ) (hc : 0 < c) : 2 * A / c ≤ 2 * (A / c) + 1 := by
  rw [two_mul, Nat.add_div hc]
  split <;> omega

/-- Count of multiples of `c = p²` coprime to `m` in the block `(v, 2v]`. -/
lemma cs_cnt_sq_dvd (m : ℕ) (hm : 0 < m) (v p : ℕ) (hp : 0 < p) :
    ((Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card
      ≤ (v / (p * p) / m + 2) * m.totient := by
  set c := p * p with hcdef
  have hc0 : 0 < c := Nat.mul_pos hp hp
  have hle : v / c ≤ 2 * v / c := Nat.div_le_div_right (by omega)
  -- Step 1: inject `a ↦ a / c` into the coprime elements of `Ioc (v/c) (2v/c)`.
  have hcard : ((Finset.Ioc v (2 * v)).filter (fun a => c ∣ a ∧ Nat.Coprime a m)).card
      ≤ ((Finset.Ioc (v / c) (2 * v / c)).filter (fun b => Nat.Coprime b m)).card := by
    apply Finset.card_le_card_of_injOn (fun a => a / c)
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at ha ⊢
      obtain ⟨⟨hva, ha2v⟩, hdvd, hcop⟩ := ha
      refine ⟨⟨?_, Nat.div_le_div_right ha2v⟩, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hc0, Nat.div_mul_cancel hdvd]
        exact hva
      · exact Nat.Coprime.coprime_dvd_left ⟨c, (Nat.div_mul_cancel hdvd).symm⟩ hcop
    · intro a₁ h₁ a₂ h₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at h₁ h₂
      have e₁ : c * (a₁ / c) = a₁ := Nat.mul_div_cancel' h₁.2.1
      have e₂ : c * (a₂ / c) = a₂ := Nat.mul_div_cancel' h₂.2.1
      simp only at heq
      rw [← e₁, ← e₂, heq]
  -- Step 2: bound the target cardinality.
  have hIoc : Finset.Ioc (v / c) (2 * v / c)
      = Finset.Ico (v / c + 1) ((v / c + 1) + (2 * v / c - v / c)) := by
    ext y
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  have h2 : ((Finset.Ioc (v / c) (2 * v / c)).filter (fun b => Nat.Coprime b m)).card
      ≤ ((2 * v / c - v / c) / m + 1) * m.totient := by
    rw [hIoc]
    exact cs_cnt_upper m hm _ _
  have h3 : (2 * v / c - v / c) / m + 1 ≤ v / c / m + 2 := by
    have hlen : 2 * v / c - v / c ≤ v / c + 1 := by
      have := cs_two_mul_div_le v c hc0
      omega
    have : (2 * v / c - v / c) / m ≤ (v / c + 1) / m := Nat.div_le_div_right hlen
    have h4 : (v / c + 1) / m ≤ (v / c + m) / m := Nat.div_le_div_right (by omega)
    rw [Nat.add_div_right _ hm] at h4
    omega
  calc ((Finset.Ioc v (2 * v)).filter (fun a => c ∣ a ∧ Nat.Coprime a m)).card
      ≤ ((2 * v / c - v / c) / m + 1) * m.totient := le_trans hcard h2
    _ ≤ (v / c / m + 2) * m.totient := Nat.mul_le_mul_right _ h3

/- ## Inverse-square sums via telescoping -/

lemma cs_telescope_le (B : ℕ) (f : ℕ → ℝ) (hfB : 0 ≤ f B) :
    ∑ i ∈ Finset.range B, (f i - f (i + 1)) ≤ f 0 := by
  rw [Finset.sum_range_sub' f B]
  linarith

lemma cs_real_ineq1 (x : ℝ) (hx : 0 ≤ x) :
    1 / ((x + 3) * (x + 3)) ≤ 1 / (x + 2) - 1 / (x + 1 + 2) := by
  have h1 : (0:ℝ) < x + 2 := by linarith
  have h2 : (0:ℝ) < x + 3 := by linarith
  have key : 1 / (x + 2) - 1 / (x + 1 + 2) = 1 / ((x + 2) * (x + 3)) := by
    rw [show x + 1 + 2 = x + 3 by ring]
    field_simp
    ring
  rw [key]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

lemma cs_real_ineq2 (x : ℝ) (hx : 0 ≤ x) :
    1 / ((2 * x + 3) * (2 * x + 3)) ≤ 1 / (4 * (x + 1)) - 1 / (4 * (x + 1 + 1)) := by
  have key : 1 / (4 * (x + 1)) - 1 / (4 * (x + 1 + 1)) = 1 / (4 * ((x + 1) * (x + 2))) := by
    rw [show x + 1 + 1 = x + 2 by ring]
    field_simp
    ring
  rw [key]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

/-- Sum of `1/g²` over a finite set of naturals all `≥ 3` is at most `1/2`. -/
lemma cs_inv_sq_sum_ge3 (Q : Finset ℕ) (hQ : ∀ g ∈ Q, 3 ≤ g) :
    ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g) ≤ 1 / 2 := by
  set B := Q.sup id + 1 with hB
  set F : ℕ → ℝ := fun i => (1:ℝ) / ((i:ℝ) + 2) with hF
  have hchain : ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g)
      ≤ ∑ i ∈ Finset.range B, (F i - F (i + 1)) := by
    apply cs_sum_le_sum_inj (fun g => g - 3)
    · intro g hg
      simp only [Finset.mem_range]
      have := Finset.le_sup (f := id) hg
      simp only [id_eq] at this
      omega
    · intro g₁ h₁ g₂ h₂ heq
      simp only [Finset.mem_coe] at h₁ h₂
      have := hQ g₁ h₁
      have := hQ g₂ h₂
      simp only at heq
      omega
    · intro g hg
      obtain ⟨d, rfl⟩ : ∃ d, g = d + 3 := ⟨g - 3, by have := hQ g hg; omega⟩
      simp only [Nat.add_sub_cancel, hF]
      push_cast
      exact cs_real_ineq1 (d:ℝ) (Nat.cast_nonneg d)
    · intro b _
      simp only [hF, sub_nonneg]
      apply one_div_le_one_div_of_le
      · positivity
      · push_cast
        linarith
  have hend : ∑ i ∈ Finset.range B, (F i - F (i + 1)) ≤ F 0 :=
    cs_telescope_le B F (by simp only [hF]; positivity)
  have hF0 : F 0 = 1/2 := by simp only [hF]; norm_num
  exact hchain.trans (hend.trans hF0.le)

/-- Sum of `1/g²` over a finite set of odd naturals all `≥ 3` is at most `1/4`. -/
lemma cs_inv_sq_sum_odd (Q : Finset ℕ) (hQ : ∀ g ∈ Q, 3 ≤ g ∧ g % 2 = 1) :
    ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g) ≤ 1 / 4 := by
  set B := Q.sup id + 1 with hB
  set F : ℕ → ℝ := fun i => (1:ℝ) / (4 * ((i:ℝ) + 1)) with hF
  have hchain : ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g)
      ≤ ∑ i ∈ Finset.range B, (F i - F (i + 1)) := by
    apply cs_sum_le_sum_inj (fun g => (g - 3) / 2)
    · intro g hg
      simp only [Finset.mem_range]
      have := Finset.le_sup (f := id) hg
      simp only [id_eq] at this
      omega
    · intro g₁ h₁ g₂ h₂ heq
      simp only [Finset.mem_coe] at h₁ h₂
      have := hQ g₁ h₁
      have := hQ g₂ h₂
      simp only at heq
      omega
    · intro g hg
      obtain ⟨d, rfl⟩ : ∃ d, g = 2 * d + 3 :=
        ⟨(g - 3) / 2, by have := hQ g hg; omega⟩
      have hidx : (2 * d + 3 - 3) / 2 = d := by omega
      rw [hidx]
      simp only [hF]
      push_cast
      exact cs_real_ineq2 (d:ℝ) (Nat.cast_nonneg d)
    · intro b _
      simp only [hF, sub_nonneg]
      apply one_div_le_one_div_of_le
      · positivity
      · push_cast
        linarith
  have hend : ∑ i ∈ Finset.range B, (F i - F (i + 1)) ≤ F 0 :=
    cs_telescope_le B F (by simp only [hF]; positivity)
  have hF0 : F 0 = 1/4 := by simp only [hF]; norm_num
  exact hchain.trans (hend.trans hF0.le)

/-- Sum of `1/p²` over a finite set of primes is at most `1/2`. -/
lemma cs_prime_inv_sq_sum (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) * p) ≤ 1 / 2 := by
  have hodd : ∀ p ∈ P.erase 2, 3 ≤ p ∧ p % 2 = 1 := by
    intro p hp
    obtain ⟨hne, hp'⟩ := Finset.mem_erase.mp hp
    have hprime := hP p hp'
    have h1 : p % 2 = 1 := Nat.odd_iff.mp (hprime.odd_of_ne_two hne)
    have h2 := hprime.two_le
    omega
  by_cases h2 : 2 ∈ P
  · rw [← Finset.sum_erase_add P _ h2]
    have herase := cs_inv_sq_sum_odd _ hodd
    have hval : (1:ℝ) / (((2:ℕ):ℝ) * ((2:ℕ):ℝ)) = 1/4 := by norm_num
    rw [hval]
    linarith
  · have hall : ∀ p ∈ P, 3 ≤ p ∧ p % 2 = 1 := fun p hp =>
      hodd p (Finset.mem_erase.mpr ⟨fun e => h2 (e ▸ hp), hp⟩)
    have := cs_inv_sq_sum_odd P hall
    linarith

/-- Sum of `1/g²` over a finite set of naturals all `≥ 2` is at most `3/4`. -/
lemma cs_inv_sq_sum_ge2 (Q : Finset ℕ) (hQ : ∀ g ∈ Q, 2 ≤ g) :
    ∑ g ∈ Q, (1 : ℝ) / ((g : ℝ) * g) ≤ 3 / 4 := by
  have hge3 : ∀ g ∈ Q.erase 2, 3 ≤ g := by
    intro g hg
    obtain ⟨hne, hg'⟩ := Finset.mem_erase.mp hg
    have := hQ g hg'
    omega
  by_cases h2 : 2 ∈ Q
  · rw [← Finset.sum_erase_add Q _ h2]
    have herase := cs_inv_sq_sum_ge3 _ hge3
    have hval : (1:ℝ) / (((2:ℕ):ℝ) * ((2:ℕ):ℝ)) = 1/4 := by norm_num
    rw [hval]
    linarith
  · have hall : ∀ g ∈ Q, 3 ≤ g := fun g hg =>
      hge3 g (Finset.mem_erase.mpr ⟨fun e => h2 (e ▸ hg), hg⟩)
    have := cs_inv_sq_sum_ge3 Q hall
    linarith

/- ## Squarefree numbers coprime to `m` in dyadic blocks -/

/-- Non-squarefree coprime elements of `(v, 2v]` are covered by multiples of `p²`, `p ≤ √(2v)`. -/
lemma cs_nonsq_subset (m v : ℕ) :
    (Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m) ⊆
      ((Finset.Icc 2 (Nat.sqrt (2 * v))).filter Nat.Prime).biUnion
        (fun p => (Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)) := by
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_Ioc] at ha
  obtain ⟨⟨hva, ha2v⟩, hnsq, hcop⟩ := ha
  rw [Nat.squarefree_iff_prime_squarefree] at hnsq
  push Not at hnsq
  obtain ⟨p, hp, hpd⟩ := hnsq
  have hpa : p * p ≤ a := Nat.le_of_dvd (by omega) hpd
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  exact ⟨p, ⟨⟨hp.two_le, Nat.le_sqrt.mpr (by omega)⟩, hp⟩, ⟨hva, ha2v⟩, hpd, hcop⟩

/-- Real bound on the number of non-squarefree coprime elements of `(v, 2v]`. -/
lemma cs_nonsq_card (m v : ℕ) (hm : 0 < m) :
    (((Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card : ℝ)
      ≤ (v : ℝ) * m.totient / (2 * m) + 2 * (Nat.sqrt (2 * v) : ℝ) * m.totient := by
  set P := (Finset.Icc 2 (Nat.sqrt (2 * v))).filter Nat.Prime with hPdef
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hcards : ((Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card
      ≤ ∑ p ∈ P, ((Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card :=
    le_trans (Finset.card_le_card (cs_nonsq_subset m v)) Finset.card_biUnion_le
  have hterm : ∀ p ∈ P,
      (((Finset.Ioc v (2 * v)).filter (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ)
        ≤ (v:ℝ) * m.totient / m * (1 / ((p:ℝ) * p)) + 2 * m.totient := by
    intro p hp
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hp0 : 0 < p := hprime.pos
    have hpR : (0:ℝ) < p := by exact_mod_cast hp0
    have h1 := cs_cnt_sq_dvd m hm v p hp0
    have h1R : (((Finset.Ioc v (2 * v)).filter
          (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ)
        ≤ (((v / (p * p) / m : ℕ) : ℝ) + 2) * (m.totient : ℝ) := by
      exact_mod_cast h1
    have h2 : ((v / (p * p) / m : ℕ) : ℝ) ≤ (v:ℝ) / ((p:ℝ) * p * m) := by
      rw [Nat.div_div_eq_div_mul]
      calc ((v / (p * p * m) : ℕ) : ℝ) ≤ (v:ℝ) / ((p * p * m : ℕ) : ℝ) := Nat.cast_div_le
        _ = (v:ℝ) / ((p:ℝ) * p * m) := by push_cast; ring
    calc (((Finset.Ioc v (2 * v)).filter
          (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ)
        ≤ (((v / (p * p) / m : ℕ) : ℝ) + 2) * (m.totient : ℝ) := h1R
      _ ≤ ((v:ℝ) / ((p:ℝ) * p * m) + 2) * (m.totient : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (v:ℝ) * m.totient / m * (1 / ((p:ℝ) * p)) + 2 * m.totient := by
          field_simp
  have hPcard : (P.card : ℝ) ≤ (Nat.sqrt (2 * v) : ℝ) := by
    have h1 : P.card ≤ (Finset.Icc 2 (Nat.sqrt (2 * v))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Nat.card_Icc] at h1
    have : P.card ≤ Nat.sqrt (2 * v) := by omega
    exact_mod_cast this
  have hsum := cs_prime_inv_sq_sum P (fun p hp => (Finset.mem_filter.mp hp).2)
  calc (((Finset.Ioc v (2 * v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card : ℝ)
      ≤ ∑ p ∈ P, (((Finset.Ioc v (2 * v)).filter
          (fun a => p * p ∣ a ∧ Nat.Coprime a m)).card : ℝ) := by exact_mod_cast hcards
    _ ≤ ∑ p ∈ P, ((v:ℝ) * m.totient / m * (1 / ((p:ℝ) * p)) + 2 * m.totient) :=
        Finset.sum_le_sum hterm
    _ = (v:ℝ) * m.totient / m * (∑ p ∈ P, 1 / ((p:ℝ) * p)) + P.card * (2 * m.totient) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (v:ℝ) * m.totient / m * (1/2) + (Nat.sqrt (2 * v) : ℝ) * (2 * m.totient) := by
        have hnn : (0:ℝ) ≤ (v:ℝ) * m.totient / m := by positivity
        have h1 := mul_le_mul_of_nonneg_left hsum hnn
        have h2 := mul_le_mul_of_nonneg_right hPcard
          (show (0:ℝ) ≤ 2 * m.totient by positivity)
        linarith
    _ = (v : ℝ) * m.totient / (2 * m) + 2 * (Nat.sqrt (2 * v) : ℝ) * m.totient := by ring

/-- The pure real-arithmetic core of the block-count bound. -/
lemma cs_real_block_core (mR vR D s : ℝ) (hm : 1 ≤ mR)
    (hv : 256 * mR^2 ≤ vR) (hD : vR - mR ≤ D * mR) (hs : s ≤ Real.sqrt 2 * Real.sqrt vR) :
    vR/(4*mR) + vR/(2*mR) + 2*s ≤ D := by
  have hm0 : (0:ℝ) < mR := by linarith
  have hv0 : (0:ℝ) ≤ vR := by nlinarith
  set x := Real.sqrt vR with hx
  have hxnn : (0:ℝ) ≤ x := Real.sqrt_nonneg vR
  have hxx : x * x = vR := Real.mul_self_sqrt hv0
  have hx16 : 16 * mR ≤ x := by
    rw [hx]
    rw [show vR = vR from rfl]
    refine (Real.le_sqrt (by positivity) hv0).mpr ?_
    nlinarith
  have hsqrt2 : Real.sqrt 2 ≤ 3/2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs' : s ≤ (3/2) * x := by
    calc s ≤ Real.sqrt 2 * x := hs
      _ ≤ (3/2) * x := mul_le_mul_of_nonneg_right hsqrt2 hxnn
  set u := vR / (4 * mR) with hu
  have h4x : 4 * x ≤ u := by
    rw [hu, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx16) hxnn]
  have hx1 : (1:ℝ) ≤ x := by nlinarith
  have e2 : vR / (2 * mR) = 2 * u := by
    rw [hu]; field_simp; ring
  have hDm : 4 * u - 1 ≤ D := by
    have h5 : (vR - mR) / mR ≤ D := (div_le_iff₀ hm0).mpr hD
    have e4 : (vR - mR) / mR = 4 * u - 1 := by
      rw [hu]; field_simp
    linarith [e4 ▸ h5]
  have hkey : 1 + 2 * s ≤ u := by
    calc 1 + 2*s ≤ 1 + 3*x := by linarith
      _ ≤ 4*x := by linarith
      _ ≤ u := h4x
  linarith

/-- Core counting bound: the block `(v, 2v]` contains at least `v·φ(m)/(4m)` squarefree
numbers coprime to `m`, provided `v ≥ 256·m²`. -/
lemma cs_block_count (m v : ℕ) (hm : 1 ≤ m) (hv : 256 * m^2 ≤ v) :
    (v : ℝ) * m.totient / (4 * m)
      ≤ (((Finset.Ioc v (2 * v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)).card : ℝ) := by
  have hm0 : 0 < m := hm
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hφ : 0 < m.totient := Nat.totient_pos.mpr hm0
  have hφR : (0:ℝ) < (m.totient : ℝ) := by exact_mod_cast hφ
  -- partition of the coprime elements into squarefree / non-squarefree
  have e1 : (Finset.Ioc v (2*v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)
      = ((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).filter Squarefree := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => and_comm)
  have e2 : (Finset.Ioc v (2*v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)
      = ((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).filter
          (fun a => ¬ Squarefree a) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun x _ => and_comm)
  have hpart : ((Finset.Ioc v (2*v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)).card
      + ((Finset.Ioc v (2*v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card
      = ((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).card := by
    rw [e1, e2]
    exact Finset.card_filter_add_card_filter_not _
  have hcast : (((Finset.Ioc v (2*v)).filter (fun a => Squarefree a ∧ Nat.Coprime a m)).card : ℝ)
      = (((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).card : ℝ)
        - (((Finset.Ioc v (2*v)).filter (fun a => ¬ Squarefree a ∧ Nat.Coprime a m)).card : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hpart
    push_cast at h
    linarith
  -- lower bound for the coprime count
  have hDR : ((v / m : ℕ) : ℝ) * (m.totient : ℝ)
      ≤ (((Finset.Ioc v (2*v)).filter (fun a => Nat.Coprime a m)).card : ℝ) := by
    exact_mod_cast cs_cnt_lower m v
  -- upper bound for the non-squarefree coprime count
  have hNS := cs_nonsq_card m v hm0
  -- the real core
  have hD' : (v:ℝ) - m ≤ ((v / m : ℕ) : ℝ) * m := by
    have h1 := Nat.div_add_mod v m
    have h2 : v % m < m := Nat.mod_lt v hm0
    have h3 : (m:ℝ) * ((v / m : ℕ) : ℝ) + ((v % m : ℕ) : ℝ) = (v:ℝ) := by exact_mod_cast h1
    have h4 : ((v % m : ℕ) : ℝ) < m := by exact_mod_cast h2
    nlinarith [mul_comm ((v / m : ℕ) : ℝ) ((m:ℕ) : ℝ)]
  have hs' : ((Nat.sqrt (2 * v) : ℕ) : ℝ) ≤ Real.sqrt 2 * Real.sqrt v := by
    have h1 : (Nat.sqrt (2 * v))^2 ≤ 2 * v := Nat.sqrt_le' (2 * v)
    have h2 : ((Nat.sqrt (2 * v) : ℕ) : ℝ) ≤ Real.sqrt ((2 * v : ℕ) : ℝ) := by
      refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
      exact_mod_cast h1
    have h3 : Real.sqrt ((2 * v : ℕ) : ℝ) = Real.sqrt 2 * Real.sqrt v := by
      rw [show ((2 * v : ℕ) : ℝ) = 2 * (v:ℝ) by push_cast; ring]
      exact Real.sqrt_mul (by norm_num) _
    linarith [h3 ▸ h2]
  have hvR : 256 * (m:ℝ)^2 ≤ (v:ℝ) := by exact_mod_cast hv
  have hcore := cs_real_block_core (m:ℝ) (v:ℝ) ((v / m : ℕ) : ℝ)
    ((Nat.sqrt (2 * v) : ℕ) : ℝ) hmR hvR hD' hs'
  -- combine everything
  have hmul := mul_le_mul_of_nonneg_right hcore hφR.le
  have r1 : ((v:ℝ)/(4*(m:ℝ)) + (v:ℝ)/(2*(m:ℝ)) + 2*((Nat.sqrt (2 * v) : ℕ) : ℝ))
        * (m.totient : ℝ)
      = (v:ℝ) * m.totient / (4*m) + (v:ℝ) * m.totient / (2*m)
        + 2 * ((Nat.sqrt (2 * v) : ℕ) : ℝ) * m.totient := by ring
  linarith [hmul, r1, hcast, hDR, hNS]

/- ## The dyadic harmonic sum -/

/-- Each dyadic block `(2^j, 2^{j+1}]` with `2^j ≥ 256·m²` contributes at least
`φ(m)/(8m)` to the harmonic sum over squarefree numbers coprime to `m`. -/
lemma cs_block_harmonic (m j : ℕ) (hm : 1 ≤ m) (hv : 256 * m^2 ≤ 2^j) :
    (m.totient : ℝ) / (8 * m)
      ≤ ∑ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter (fun a => Squarefree a ∧ Nat.Coprime a m),
          (1:ℝ)/a := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hpow : (2:ℕ)^(j+1) = 2 * 2^j := by rw [pow_succ]; ring
  have hcount := cs_block_count m (2^j) hm hv
  rw [show (2:ℕ) * 2^j = 2^(j+1) from hpow.symm] at hcount
  have hterm : ∀ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter
      (fun a => Squarefree a ∧ Nat.Coprime a m),
      (1:ℝ)/((2^(j+1) : ℕ) : ℝ) ≤ (1:ℝ)/(a : ℝ) := by
    intro a ha
    obtain ⟨hmem, -⟩ := Finset.mem_filter.mp ha
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hmem
    have ha0 : 0 < a := by
      have := pow_pos (show 0 < 2 by norm_num) j
      omega
    apply one_div_le_one_div_of_le
    · exact_mod_cast ha0
    · exact_mod_cast h2
  have h5 : ((((Finset.Ioc (2^j) (2^(j+1))).filter
        (fun a => Squarefree a ∧ Nat.Coprime a m)).card : ℝ)) * (1/((2^(j+1) : ℕ) : ℝ))
      ≤ ∑ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter
          (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hterm
  have heq : ((2^j : ℕ) : ℝ) * m.totient / (4 * m) * (1/((2^(j+1) : ℕ) : ℝ))
      = (m.totient : ℝ) / (8 * m) := by
    have c1 : ((2^j : ℕ) : ℝ) = (2:ℝ)^j := by push_cast; ring
    have c2 : ((2^(j+1) : ℕ) : ℝ) = 2 * (2:ℝ)^j := by
      rw [hpow]; push_cast; ring
    rw [c1, c2]
    have hne : ((2:ℝ))^j ≠ 0 := by positivity
    have hmne : ((m:ℕ) : ℝ) ≠ 0 := ne_of_gt hmR
    field_simp
    ring
  have h6 := mul_le_mul_of_nonneg_right hcount
    (show (0:ℝ) ≤ 1/((2^(j+1) : ℕ) : ℝ) by positivity)
  calc (m.totient : ℝ)/(8*m)
      = ((2^j : ℕ) : ℝ) * m.totient / (4 * m) * (1/((2^(j+1) : ℕ) : ℝ)) := heq.symm
    _ ≤ _ := h6
    _ ≤ _ := h5

/-- Dyadic decomposition: `j₁ - j₀ + 1` disjoint blocks each contribute `φ(m)/(8m)`. -/
lemma cs_dyadic (m x : ℕ) (hm : 1 ≤ m) (j₀ j₁ : ℕ) (hj : j₀ ≤ j₁)
    (h₀ : 256 * m^2 ≤ 2^j₀) (h₁ : 2^(j₁+1) ≤ x) :
    ((j₁ - j₀ + 1 : ℕ) : ℝ) * m.totient / (8 * m)
      ≤ ∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
  have hdisj : (↑(Finset.Icc j₀ j₁) : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.Ioc (2^j) (2^(j+1))).filter
        (fun a => Squarefree a ∧ Nat.Coprime a m)) := by
    have key : ∀ i' j' : ℕ, i' < j' → Disjoint
        ((Finset.Ioc (2^i') (2^(i'+1))).filter (fun a => Squarefree a ∧ Nat.Coprime a m))
        ((Finset.Ioc (2^j') (2^(j'+1))).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) := by
      intro i' j' hij
      apply Finset.disjoint_filter_filter
      rw [Finset.Ioc_disjoint_Ioc]
      calc min (2^(i'+1)) (2^(j'+1)) ≤ 2^(i'+1) := min_le_left _ _
        _ ≤ 2^j' := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ max (2^i') (2^j') := le_max_right _ _
    intro i _ j _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i j h
    · exact (key j i h).symm
  have hsub : (Finset.Icc j₀ j₁).biUnion
      (fun j => (Finset.Ioc (2^j) (2^(j+1))).filter
        (fun a => Squarefree a ∧ Nat.Coprime a m))
      ⊆ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) := by
    intro a ha
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at ha ⊢
    obtain ⟨j, ⟨_, hjj1⟩, ⟨hja, haj⟩, hprops⟩ := ha
    refine ⟨⟨?_, ?_⟩, hprops⟩
    · have := pow_pos (show 0 < 2 by norm_num) j
      omega
    · calc a ≤ 2^(j+1) := haj
        _ ≤ 2^(j₁+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ x := h₁
  calc ((j₁ - j₀ + 1 : ℕ) : ℝ) * m.totient / (8 * m)
      = ∑ _j ∈ Finset.Icc j₀ j₁, (m.totient : ℝ) / (8 * m) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
          show j₁ + 1 - j₀ = j₁ - j₀ + 1 from by omega]
        ring
    _ ≤ ∑ j ∈ Finset.Icc j₀ j₁, ∑ a ∈ (Finset.Ioc (2^j) (2^(j+1))).filter
          (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
        apply Finset.sum_le_sum
        intro j hjmem
        have hj0 : j₀ ≤ j := (Finset.mem_Icc.mp hjmem).1
        exact cs_block_harmonic m j hm
          (le_trans h₀ (Nat.pow_le_pow_right (by norm_num) hj0))
    _ = ∑ a ∈ (Finset.Icc j₀ j₁).biUnion (fun j => (Finset.Ioc (2^j) (2^(j+1))).filter
          (fun a => Squarefree a ∧ Nat.Coprime a m)), (1:ℝ)/a :=
        (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro a _ _
        positivity

/- ## From coprime pairs to the weighted sum over products -/

/-- The sum of `1/(ab)` over coprime pairs of squarefree numbers `≤ x` coprime to `m` is
dominated by the sum of `2^ω(ℓ)/ℓ` over squarefree `ℓ ≤ w` coprime to `m`, when `x² ≤ w`. -/
lemma cs_pairs_to_sum (m x w : ℕ) (hxx : x * x ≤ w) :
    ∑ q ∈ (((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) ×ˢ
          ((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m))).filter
          (fun q => Nat.Coprime q.1 q.2), (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ ∑ ℓ ∈ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ m),
          (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
  classical
  set T := (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) with hT
  set Q := (T ×ˢ T).filter (fun q : ℕ × ℕ => Nat.Coprime q.1 q.2) with hQ
  have hmem : ∀ q ∈ Q, (1 ≤ q.1 ∧ q.1 ≤ x ∧ Squarefree q.1 ∧ Nat.Coprime q.1 m) ∧
      (1 ≤ q.2 ∧ q.2 ≤ x ∧ Squarefree q.2 ∧ Nat.Coprime q.2 m) ∧ Nat.Coprime q.1 q.2 := by
    intro q hq
    simp only [hQ, hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
    tauto
  have himg : Q.image (fun q : ℕ × ℕ => q.1 * q.2)
      ⊆ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ m) := by
    intro ℓ hℓ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
    obtain ⟨⟨h11, h1x, h1sq, h1m⟩, ⟨h21, h2x, h2sq, h2m⟩, h12⟩ := hmem q hq
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact le_trans (Nat.mul_le_mul h1x h2x) hxx
    · exact (Nat.squarefree_mul h12).mpr ⟨h1sq, h2sq⟩
    · exact Nat.Coprime.mul_left h1m h2m
  have hfiber : ∀ ℓ ∈ Q.image (fun q : ℕ × ℕ => q.1 * q.2),
      ((Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card : ℝ)
        ≤ (2:ℝ)^(ℓ.primeFactors.card) := by
    intro ℓ hℓ
    have hℓ0 : ℓ ≠ 0 := by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hℓ
      obtain ⟨⟨h11, _, _, _⟩, ⟨h21, _, _, _⟩, _⟩ := hmem q hq
      exact Nat.mul_ne_zero (by omega) (by omega)
    have hcard : (Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card
        ≤ (ℓ.primeFactors.powerset).card := by
      apply Finset.card_le_card_of_injOn (fun q : ℕ × ℕ => q.1.primeFactors)
      · intro q hq
        simp only [Finset.mem_coe, Finset.mem_filter] at hq
        obtain ⟨hqQ, hqℓ⟩ := hq
        simp only [Finset.mem_coe, Finset.mem_powerset]
        exact Nat.primeFactors_mono ⟨q.2, hqℓ.symm⟩ hℓ0
      · intro q hq q' hq' heq
        simp only [Finset.mem_coe, Finset.mem_filter] at hq hq'
        obtain ⟨hqQ, hqℓ⟩ := hq
        obtain ⟨hq'Q, hq'ℓ⟩ := hq'
        obtain ⟨⟨h11, _, h1sq, _⟩, ⟨h21, _, _, _⟩, _⟩ := hmem q hqQ
        obtain ⟨⟨h11', _, h1sq', _⟩, ⟨h21', _, _, _⟩, _⟩ := hmem q' hq'Q
        have e1 : q.1 = q'.1 := by
          have p1 := Nat.prod_primeFactors_of_squarefree h1sq
          have p2 := Nat.prod_primeFactors_of_squarefree h1sq'
          rw [← p1, ← p2]
          exact Finset.prod_congr heq (fun _ _ => rfl)
        have e2 : q.2 = q'.2 := by
          have h := hqℓ.trans hq'ℓ.symm
          rw [e1] at h
          exact Nat.eq_of_mul_eq_mul_left (by omega) h
        exact Prod.ext e1 e2
    rw [Finset.card_powerset] at hcard
    calc ((Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card : ℝ)
        ≤ ((2^(ℓ.primeFactors.card) : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = (2:ℝ)^(ℓ.primeFactors.card) := by push_cast; ring
  calc ∑ q ∈ Q, (1:ℝ)/((q.1 : ℝ) * q.2)
      = ∑ q ∈ Q, (fun ℓ : ℕ => (1:ℝ)/(ℓ:ℝ)) (q.1 * q.2) := by
        apply Finset.sum_congr rfl
        intro q _
        push_cast
        ring
    _ = ∑ ℓ ∈ Q.image (fun q : ℕ × ℕ => q.1 * q.2),
          (Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card • ((1:ℝ)/(ℓ:ℝ)) :=
        Finset.sum_comp (fun ℓ : ℕ => (1:ℝ)/(ℓ:ℝ)) (fun q : ℕ × ℕ => q.1 * q.2)
    _ ≤ ∑ ℓ ∈ Q.image (fun q : ℕ × ℕ => q.1 * q.2), (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        rw [nsmul_eq_mul]
        have h1 := hfiber ℓ hℓ
        have h2 : (0:ℝ) ≤ 1/(ℓ:ℝ) := by positivity
        calc ((Q.filter (fun q : ℕ × ℕ => q.1 * q.2 = ℓ)).card : ℝ) * ((1:ℝ)/(ℓ:ℝ))
            ≤ (2:ℝ)^(ℓ.primeFactors.card) * ((1:ℝ)/(ℓ:ℝ)) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by rw [mul_one_div]
    _ ≤ ∑ ℓ ∈ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ Nat.Coprime ℓ m),
          (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himg
        intro ℓ _ _
        positivity

/-- Pairs with a common factor contribute at most `(3/4)·S²`. -/
lemma cs_noncop_bound (m x : ℕ) :
    ∑ q ∈ (((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) ×ˢ
          ((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m))).filter
          (fun q => ¬ Nat.Coprime q.1 q.2), (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ 3/4 * ((∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m),
            (1:ℝ)/a)
          * (∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m),
            (1:ℝ)/a)) := by
  classical
  set T := (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) with hT
  set S := ∑ a ∈ T, (1:ℝ)/a with hS
  have hbound : ∑ q ∈ (T ×ˢ T).filter (fun q : ℕ × ℕ => ¬ Nat.Coprime q.1 q.2),
        (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
          (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ))) := by
    apply cs_sum_le_sum_inj (fun q : ℕ × ℕ =>
      (Nat.gcd q.1 q.2, (q.1 / Nat.gcd q.1 q.2, q.2 / Nat.gcd q.1 q.2)))
    · -- maps to
      intro q hq
      simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      obtain ⟨⟨⟨⟨h11, h1x⟩, h1sq, h1m⟩, ⟨h21, h2x⟩, h2sq, h2m⟩, hncop⟩ := hq
      have hd0 : 0 < Nat.gcd q.1 q.2 := by
        rcases Nat.eq_zero_or_pos (Nat.gcd q.1 q.2) with h | h
        · rw [Nat.gcd_eq_zero_iff] at h
          omega
        · exact h
      have hd2 : 2 ≤ Nat.gcd q.1 q.2 := by
        rcases Nat.lt_or_ge (Nat.gcd q.1 q.2) 2 with h | h
        · have h1 : Nat.gcd q.1 q.2 = 1 := by omega
          exact absurd h1 hncop
        · exact h
      have hdx : Nat.gcd q.1 q.2 ≤ x :=
        le_trans (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) h1x
      have ha1 : q.1 / Nat.gcd q.1 q.2 ∣ q.1 :=
        ⟨Nat.gcd q.1 q.2, (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm⟩
      have hb1 : q.2 / Nat.gcd q.1 q.2 ∣ q.2 :=
        ⟨Nat.gcd q.1 q.2, (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm⟩
      simp only [hT, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hd2, hdx⟩, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hd0
      · exact le_trans (Nat.div_le_self _ _) h1x
      · exact Squarefree.squarefree_of_dvd ha1 h1sq
      · exact Nat.Coprime.coprime_dvd_left ha1 h1m
      · exact Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hd0
      · exact le_trans (Nat.div_le_self _ _) h2x
      · exact Squarefree.squarefree_of_dvd hb1 h2sq
      · exact Nat.Coprime.coprime_dvd_left hb1 h2m
    · -- injective
      intro q hq q' hq' heq
      simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc] at hq hq'
      obtain ⟨⟨⟨⟨h11, _⟩, _, _⟩, ⟨h21, _⟩, _, _⟩, _⟩ := hq
      obtain ⟨⟨⟨⟨h11', _⟩, _, _⟩, ⟨h21', _⟩, _, _⟩, _⟩ := hq'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hd, h1, h2⟩ := heq
      have a1 : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have a2 : Nat.gcd q'.1 q'.2 * (q'.1 / Nat.gcd q'.1 q'.2) = q'.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have b1 : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have b2 : Nat.gcd q'.1 q'.2 * (q'.2 / Nat.gcd q'.1 q'.2) = q'.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have e1 : q.1 = q'.1 := by
        calc q.1 = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) := a1.symm
          _ = Nat.gcd q'.1 q'.2 * (q'.1 / Nat.gcd q'.1 q'.2) := by rw [h1, hd]
          _ = q'.1 := a2
      have e2 : q.2 = q'.2 := by
        calc q.2 = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) := b1.symm
          _ = Nat.gcd q'.1 q'.2 * (q'.2 / Nat.gcd q'.1 q'.2) := by rw [h2, hd]
          _ = q'.2 := b2
      exact Prod.ext e1 e2
    · -- value inequality (in fact equality)
      intro q hq
      simp only [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
      obtain ⟨⟨⟨⟨h11, _⟩, _, _⟩, ⟨h21, _⟩, _, _⟩, _⟩ := hq
      have hd0 : 0 < Nat.gcd q.1 q.2 := by
        rcases Nat.eq_zero_or_pos (Nat.gcd q.1 q.2) with h | h
        · rw [Nat.gcd_eq_zero_iff] at h
          omega
        · exact h
      have ha : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hb : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have ha0 : 0 < q.1 / Nat.gcd q.1 q.2 :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)) hd0
      have hb0 : 0 < q.2 / Nat.gcd q.1 q.2 :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)) hd0
      have haR : (q.1 : ℝ) = (Nat.gcd q.1 q.2 : ℝ) * ((q.1 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by
        exact_mod_cast ha.symm
      have hbR : (q.2 : ℝ) = (Nat.gcd q.1 q.2 : ℝ) * ((q.2 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by
        exact_mod_cast hb.symm
      have hdR : (0:ℝ) < (Nat.gcd q.1 q.2 : ℝ) := by exact_mod_cast hd0
      have haR0 : (0:ℝ) < ((q.1 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by exact_mod_cast ha0
      have hbR0 : (0:ℝ) < ((q.2 / Nat.gcd q.1 q.2 : ℕ) : ℝ) := by exact_mod_cast hb0
      apply le_of_eq
      rw [haR, hbR]
      field_simp
    · -- nonnegativity on the target
      intro r _
      positivity
  have hinner : ∑ p ∈ T ×ˢ T, ((1:ℝ)/(p.1:ℝ)) * ((1:ℝ)/(p.2:ℝ)) = S * S := by
    calc ∑ p ∈ T ×ˢ T, ((1:ℝ)/(p.1:ℝ)) * ((1:ℝ)/(p.2:ℝ))
        = ∑ a ∈ T, ∑ b ∈ T, ((1:ℝ)/(a:ℝ)) * ((1:ℝ)/(b:ℝ)) := Finset.sum_product _ _ _
      _ = S * S := (Finset.sum_mul_sum T T (fun a => (1:ℝ)/(a:ℝ)) (fun b => (1:ℝ)/(b:ℝ))).symm
  have hteval : ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
        (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ)))
      = (∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ)*d)) * (S * S) := by
    calc ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
          (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ)))
        = ∑ d ∈ Finset.Icc 2 x, ∑ p ∈ T ×ˢ T,
            (1:ℝ)/((d:ℝ) * d) * (((1:ℝ)/(p.1:ℝ)) * ((1:ℝ)/(p.2:ℝ))) := Finset.sum_product _ _ _
      _ = ∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ) * d) * (S * S) := by
          apply Finset.sum_congr rfl
          intro d _
          rw [← Finset.mul_sum, hinner]
      _ = (∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ)*d)) * (S * S) :=
          (Finset.sum_mul (Finset.Icc 2 x) (fun d => (1:ℝ)/((d:ℝ)*d)) (S * S)).symm
  have hd34 := cs_inv_sq_sum_ge2 (Finset.Icc 2 x) (fun d hd => (Finset.mem_Icc.mp hd).1)
  have hSS : (0:ℝ) ≤ S * S := mul_self_nonneg S
  calc ∑ q ∈ (T ×ˢ T).filter (fun q : ℕ × ℕ => ¬ Nat.Coprime q.1 q.2),
        (1:ℝ)/((q.1 : ℝ) * q.2)
      ≤ ∑ r ∈ (Finset.Icc 2 x) ×ˢ (T ×ˢ T),
          (1:ℝ)/((r.1:ℝ) * r.1) * ((1:ℝ)/((r.2.1:ℝ)) * ((1:ℝ)/(r.2.2:ℝ))) := hbound
    _ = (∑ d ∈ Finset.Icc 2 x, (1:ℝ)/((d:ℝ)*d)) * (S * S) := hteval
    _ ≤ 3/4 * (S * S) := mul_le_mul_of_nonneg_right hd34 hSS

/-- The coprime-pair sum is at least a quarter of the squared harmonic sum. -/
lemma cs_coprime_pairs_lower (m x : ℕ) :
    (∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a)
    * (∑ a ∈ (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a) / 4
      ≤ ∑ q ∈ (((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m)) ×ˢ
            ((Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m))).filter
            (fun q => Nat.Coprime q.1 q.2), (1:ℝ)/((q.1 : ℝ) * q.2) := by
  classical
  set T := (Finset.Icc 1 x).filter (fun a => Squarefree a ∧ Nat.Coprime a m) with hT
  set S := ∑ a ∈ T, (1:ℝ)/a with hS
  have htotal : ∑ q ∈ T ×ˢ T, (1:ℝ)/((q.1:ℝ) * q.2) = S * S := by
    calc ∑ q ∈ T ×ˢ T, (1:ℝ)/((q.1:ℝ) * q.2)
        = ∑ a ∈ T, ∑ b ∈ T, (1:ℝ)/((a:ℝ) * b) := Finset.sum_product _ _ _
      _ = ∑ a ∈ T, ∑ b ∈ T, ((1:ℝ)/(a:ℝ)) * ((1:ℝ)/(b:ℝ)) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          rw [div_mul_div_comm, one_mul]
      _ = S * S := (Finset.sum_mul_sum T T (fun a => (1:ℝ)/(a:ℝ)) (fun b => (1:ℝ)/(b:ℝ))).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (T ×ˢ T)
    (fun q : ℕ × ℕ => Nat.Coprime q.1 q.2) (fun q : ℕ × ℕ => (1:ℝ)/((q.1:ℝ) * q.2))
  have hnon := cs_noncop_bound m x
  rw [← hT, ← hS] at hnon
  linarith [hsplit, htotal, hnon]

/- ## Choice of dyadic parameters -/

/-- `log y ≤ 2√y - 2` for positive `y`. -/
lemma cs_log_le_two_sqrt (y : ℝ) (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y - 2 := by
  have h1 : Real.log (Real.sqrt y) ≤ Real.sqrt y - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
  have h2 : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy.le
  linarith

/-- For `w ≥ 2^15000` and `1 ≤ m ≤ (log w)³` there is a long run of dyadic blocks
between `256·m²` and `√w`. -/
lemma cs_params (w m : ℕ) (hw : 2^15000 ≤ w) (hm : 1 ≤ m)
    (hmw : (m:ℝ) ≤ (Real.log w)^3) :
    ∃ j₀ j₁ : ℕ, j₀ ≤ j₁ ∧ 256 * m^2 ≤ 2^j₀ ∧ 2^(j₁+1) ≤ Nat.sqrt w ∧
      Real.log w / 8 ≤ ((j₁ - j₀ + 1 : ℕ) : ℝ) := by
  set x := Nat.sqrt w with hxdef
  set a := Nat.log 2 (256 * m^2) with hadef
  set b := Nat.log 2 x with hbdef
  set L := Real.log w with hLdef
  have hw1 : 1 ≤ w := le_trans Nat.one_le_two_pow hw
  have hwR : (1:ℝ) ≤ (w:ℝ) := by exact_mod_cast hw1
  have hwR0 : (0:ℝ) < (w:ℝ) := by linarith
  have hx1 : 1 ≤ x := by
    rw [hxdef]
    exact Nat.le_sqrt.mpr (by omega)
  have hxR0 : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx1
  have hmR1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hlog2pos : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h256 : 0 < 256 * m^2 := Nat.mul_pos (by norm_num) (pow_pos hm 2)
  -- `L` is large
  have hL : 10397 ≤ L := by
    have h1 : ((2:ℝ))^(15000:ℕ) ≤ (w:ℝ) := by exact_mod_cast hw
    have h2 : Real.log ((2:ℝ)^(15000:ℕ)) ≤ L := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith [Real.log_two_gt_d9]
  have hL0 : (0:ℝ) < L := by linarith
  -- `log x > L/2 - log 2`
  have hXlow : L/2 - Real.log 2 < Real.log x := by
    have h1 := Nat.lt_succ_sqrt w
    simp only [Nat.succ_eq_add_one] at h1
    rw [← hxdef] at h1
    have hxx : w < 4*(x*x) := by
      calc w < (x+1)*(x+1) := h1
        _ ≤ (2*x)*(2*x) := Nat.mul_le_mul (by omega) (by omega)
        _ = 4*(x*x) := by ring
    have hcast : (w:ℝ) < 4*((x:ℝ)*(x:ℝ)) := by exact_mod_cast hxx
    have hxne : (x:ℝ) ≠ 0 := ne_of_gt hxR0
    have h3 : L < Real.log (4*((x:ℝ)*(x:ℝ))) := Real.log_lt_log hwR0 hcast
    rw [Real.log_mul (by norm_num) (mul_ne_zero hxne hxne), Real.log_mul hxne hxne] at h3
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2^(2:ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  -- upper bound on `a·log 2`
  have haR : (a:ℝ) * Real.log 2 ≤ 8 * Real.log 2 + 6 * Real.log L := by
    have h1 : (2:ℕ)^(Nat.log 2 (256 * m^2)) ≤ 256 * m^2 := Nat.pow_log_le_self 2 h256.ne'
    rw [← hadef] at h1
    have h2 : ((2:ℝ))^a ≤ ((256 * m^2 : ℕ):ℝ) := by exact_mod_cast h1
    have h3 : Real.log ((2:ℝ)^a) ≤ Real.log ((256*m^2 : ℕ):ℝ) :=
      Real.log_le_log (by positivity) h2
    rw [Real.log_pow] at h3
    have hmne : (m:ℝ) ≠ 0 := by linarith
    have h4 : Real.log ((256*m^2 : ℕ):ℝ) = 8*Real.log 2 + 2*Real.log m := by
      have hc : ((256*m^2 : ℕ):ℝ) = 256 * (m:ℝ)^2 := by push_cast; ring
      rw [hc, Real.log_mul (by norm_num) (pow_ne_zero 2 hmne), Real.log_pow,
        show (256:ℝ) = 2^(8:ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    have h5 : Real.log (m:ℝ) ≤ 3 * Real.log L := by
      have h6 : Real.log (m:ℝ) ≤ Real.log (L^(3:ℕ)) :=
        Real.log_le_log (by linarith) hmw
      rwa [Real.log_pow, show ((3:ℕ):ℝ) = 3 by norm_num] at h6
    linarith
  -- lower bound on `b·log 2`
  have hbR : Real.log x < (b:ℝ) * Real.log 2 + Real.log 2 := by
    have h1 := Nat.lt_pow_succ_log_self (show (1:ℕ) < 2 by norm_num) x
    simp only [Nat.succ_eq_add_one] at h1
    rw [← hbdef] at h1
    have h2 : (x:ℝ) < (2:ℝ)^(b+1) := by exact_mod_cast h1
    have h3 : Real.log x < Real.log ((2:ℝ)^(b+1)) := Real.log_lt_log hxR0 h2
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  -- `√L` bounds
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hsq101 : (101:ℝ) ≤ Real.sqrt L := by
    refine (Real.le_sqrt (by norm_num) hL0.le).mpr ?_
    norm_num
    linarith
  have hsqL : Real.sqrt L ≤ L / 101 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [hsq, hsq101, Real.sqrt_nonneg L]
  have hlogL : Real.log L ≤ 2 * Real.sqrt L - 2 := cs_log_le_two_sqrt L hL0
  have hLlog2 : L * Real.log 2 ≤ 0.6931471808 * L := by
    have := mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) hL0.le
    linarith
  -- `b - a` is large
  have hba : (a:ℝ) + 3 < (b:ℝ) := by
    by_contra hcon
    push Not at hcon
    have h1 : (b:ℝ) * Real.log 2 ≤ ((a:ℝ) + 3) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hcon hlog2pos.le
    have h2 : ((a:ℝ)+3) * Real.log 2 = (a:ℝ)*Real.log 2 + 3*Real.log 2 := by ring
    linarith [Real.log_two_lt_d9]
  have hban : a + 3 < b := by exact_mod_cast hba
  -- the block count is large
  have hcnt : L/8 + 1 ≤ (b:ℝ) - a := by
    by_contra hcon
    push Not at hcon
    have h1 : ((b:ℝ) - a) * Real.log 2 ≤ (L/8 + 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_right (le_of_lt hcon) hlog2pos.le
    have h2 : ((b:ℝ) - a) * Real.log 2 = (b:ℝ)*Real.log 2 - (a:ℝ)*Real.log 2 := by ring
    have h3 : (L/8 + 1) * Real.log 2 = L*Real.log 2/8 + Real.log 2 := by ring
    linarith [Real.log_two_lt_d9]
  refine ⟨a + 1, b - 1, by omega, ?_, ?_, ?_⟩
  · have h1 := Nat.lt_pow_succ_log_self (show (1:ℕ) < 2 by norm_num) (256*m^2)
    simp only [Nat.succ_eq_add_one] at h1
    rw [← hadef] at h1
    exact h1.le
  · rw [show b - 1 + 1 = b from by omega, hbdef]
    exact Nat.pow_log_le_self 2 (by omega)
  · rw [show (b - 1) - (a + 1) + 1 = b - a - 1 from by omega]
    have hc : ((b - a - 1 : ℕ):ℝ) = (b:ℝ) - a - 1 := by
      rw [show b - a - 1 = b - (a + 1) from by omega,
        Nat.cast_sub (by omega : a + 1 ≤ b)]
      push_cast
      ring
    rw [hc]
    linarith

/- ## The exported theorem -/

/-- **Lemma B.3** (blueprint): for all large `w` and all `1 ≤ m ≤ (log w)³`,
`Σ_{ℓ ≤ w, squarefree, coprime to m} 2^ω(ℓ)/ℓ ≥ c₀·(φ(m)/m)²·(log w)²`. -/
theorem coprime_squarefree_sum_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w → ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ (Real.log w)^3 →
      c₀ * ((Nat.totient m : ℝ)/m)^2 * (Real.log w)^2
        ≤ ∑ ℓ ∈ (Finset.Icc 1 w).filter (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime m),
            (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
  refine ⟨1/16384, by norm_num, 2^15000, ?_⟩
  intro w hw m hm hmw
  obtain ⟨j₀, j₁, hj, h0, h1, hcount⟩ := cs_params w m hw hm hmw
  have hxx : Nat.sqrt w * Nat.sqrt w ≤ w := by
    have := Nat.sqrt_le' w
    rwa [pow_two] at this
  have hS := cs_dyadic m (Nat.sqrt w) hm j₀ j₁ hj h0 h1
  have hpair := cs_coprime_pairs_lower m (Nat.sqrt w)
  have hsum := cs_pairs_to_sum m (Nat.sqrt w) w hxx
  set S := ∑ a ∈ (Finset.Icc 1 (Nat.sqrt w)).filter
      (fun a => Squarefree a ∧ Nat.Coprime a m), (1:ℝ)/a with hSdef
  set L := Real.log w with hLdef
  set φ := (m.totient : ℝ) with hφdef
  set M := (m : ℝ) with hMdef
  have hM1 : (1:ℝ) ≤ M := by
    rw [hMdef]
    exact_mod_cast hm
  have hM0 : (0:ℝ) < M := by linarith
  have hMne : M ≠ 0 := ne_of_gt hM0
  have hφ0 : (0:ℝ) < φ := by
    rw [hφdef]
    exact_mod_cast Nat.totient_pos.mpr hm
  have hL0 : (0:ℝ) ≤ L := by
    rw [hLdef]
    apply Real.log_nonneg
    have hw1 : 1 ≤ w := le_trans Nat.one_le_two_pow hw
    exact_mod_cast hw1
  have hS0 : (0:ℝ) ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun a _ => by positivity)
  have hφM : (0:ℝ) ≤ φ/(8*M) := div_nonneg hφ0.le (by linarith)
  -- S is large
  have hc1 : L/8 * (φ/(8*M)) ≤ ((j₁ - j₀ + 1 : ℕ):ℝ) * (φ/(8*M)) :=
    mul_le_mul_of_nonneg_right hcount hφM
  have he : ((j₁ - j₀ + 1 : ℕ):ℝ) * (φ/(8*M)) = ((j₁ - j₀ + 1 : ℕ):ℝ) * φ/(8*M) := by
    ring
  have hSlow : L/8 * (φ/(8*M)) ≤ S := by linarith [hS, hc1, he]
  have hSlow0 : (0:ℝ) ≤ L/8 * (φ/(8*M)) :=
    mul_nonneg (div_nonneg hL0 (by norm_num)) hφM
  have hsq := mul_self_le_mul_self hSlow0 hSlow
  have heq : 1/16384 * (φ/M)^2 * L^2
      = (L/8 * (φ/(8*M))) * (L/8 * (φ/(8*M))) / 4 := by
    field_simp
    ring
  calc 1/16384 * (φ/M)^2 * L^2
      = (L/8 * (φ/(8*M))) * (L/8 * (φ/(8*M))) / 4 := heq
    _ ≤ S * S / 4 := by linarith [hsq]
    _ ≤ _ := hpair
    _ ≤ _ := hsum


end

/- ═════ MODULE: PairSieveCore884.lean ═════ -/
section
/-
# Erdős 884 — the pair sieve (Lemma B, bullets 1–5)

A Selberg sieve detecting prime pairs `(n, n+h)`: we sieve the values `n(n+h)` for
`n ∈ [1, M]` by the primes up to `z`.  The density is `ν(d) = ρ_h(d)/d` where `ρ_h` is
multiplicative with `ρ_h(p) = 1` if `p ∣ 2h` and `2` otherwise (the number of roots of
`X(X+h) mod p` for even `h`; using `2h` instead of `h` makes `ν(2) = 1/2 < 1`
unconditionally, and agrees with the root count whenever `h` is even).
-/


open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega

/-- `ρ_h`: the multiplicative function with `ρ_h(p) = 1` if `p ∣ 2h` and `2` otherwise. -/
noncomputable def rhoFun (h : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.prodPrimeFactors (fun p => if p ∣ 2 * h then (1 : ℝ) else 2)

lemma rhoFun_apply_prime {p : ℕ} (hp : p.Prime) (h : ℕ) :
    rhoFun h p = if p ∣ 2 * h then (1 : ℝ) else 2 := by
  rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
    Finset.prod_singleton]

/-- The density function of the pair sieve: `ν(d) = ρ_h(d)/d`. -/
noncomputable def pairNu (h : ℕ) : ArithmeticFunction ℝ := (rhoFun h).pdiv .id

lemma pairNu_apply (h d : ℕ) : pairNu h d = rhoFun h d / d := by
  simp [pairNu, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply]

/-- The Selberg sieve detecting prime pairs `(n, n+h)`, `n ∈ [1,M]`, sieving by primes
`≤ z`.  Support: the values `n(n+h)`; weights `1`; total mass `M`; level `z`. -/
noncomputable def pairSieve (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.Icc 1 M).image (fun n => n * (n + h))
  prodPrimes := primorial ⌊z⌋₊
  prodPrimes_squarefree := Sieve.primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (M : ℝ)
  nu := pairNu h
  nu_mult := by unfold pairNu rhoFun; arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp only [pairNu, ArithmeticFunction.pdiv_apply, rhoFun_apply_prime hp,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    split_ifs <;> positivity
  nu_lt_one_of_prime := fun p hp _ => by
    simp only [pairNu, ArithmeticFunction.pdiv_apply, rhoFun_apply_prime hp,
      ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    rw [div_lt_one hp0]
    split_ifs with hdvd
    · exact_mod_cast hp.one_lt
    · have hp2 : p ≠ 2 := fun h2 => hdvd (h2 ▸ ⟨h, rfl⟩)
      have h3 : 3 ≤ p := by have := hp.two_le; omega
      exact_mod_cast (by omega : 2 < p)
  level := z
  one_le_level := hz

@[simp] lemma pairSieve_prodPrimes (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).prodPrimes = primorial ⌊z⌋₊ := rfl

@[simp] lemma pairSieve_level (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).level = z := rfl

@[simp] lemma pairSieve_nu (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).nu = pairNu h := rfl

@[simp] lemma pairSieve_totalMass (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).totalMass = (M : ℝ) := rfl

/-- Positivity of the Selberg bounding sum of the pair sieve (re-export of
`SelbergSieve.selbergBoundingSum_pos` for downstream use). -/
theorem pairSieve_boundingSum_pos (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).selbergBoundingSum > 0 :=
  SelbergSieve.selbergBoundingSum_pos _

/- ## Counting the roots of `X(X+h)` modulo `d` -/

/-- The number of residues `r < d` with `d ∣ r(r+h)`. -/
def nroots (h d : ℕ) : ℕ := ((Finset.range d).filter (fun r => d ∣ r * (r + h))).card

lemma nroots_zero (h : ℕ) : nroots h 0 = 0 := by simp [nroots]

lemma nroots_one (h : ℕ) : nroots h 1 = 1 := by simp [nroots]

/-- Divisibility of `n(n+h)` by `d` only depends on `n mod d`. -/
lemma dvd_shift_iff_mod (d h n : ℕ) : d ∣ n * (n + h) ↔ d ∣ (n % d) * (n % d + h) := by
  have h1 : (n % d) * (n % d + h) ≡ n * (n + h) [MOD d] :=
    (Nat.mod_modEq n d).mul ((Nat.mod_modEq n d).add_right h)
  constructor
  · intro hdvd
    exact Nat.modEq_zero_iff_dvd.mp (h1.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  · intro hdvd
    exact Nat.modEq_zero_iff_dvd.mp (h1.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

/-- The root count as the size of the zero set of `x(x+h)` in `ZMod d`. -/
lemma nroots_eq_card_zmod (h d : ℕ) [NeZero d] :
    nroots h d =
      (Finset.univ.filter (fun x : ZMod d => x * (x + (h : ZMod d)) = 0)).card := by
  unfold nroots
  apply Finset.card_bij (fun (r : ℕ) _ => (r : ZMod d))
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hc : ((r * (r + h) : ℕ) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hr.2
    push_cast at hc
    exact hc
  · intro r₁ hr₁ r₂ hr₂ heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
    have := congrArg ZMod.val heq
    rwa [ZMod.val_cast_of_lt hr₁.1, ZMod.val_cast_of_lt hr₂.1] at this
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hval : x.val ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt x, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
      push_cast
      rw [ZMod.natCast_rightInverse x]
      exact hx
    exact ⟨x.val, hval, ZMod.natCast_rightInverse x⟩

/-- CRT: the root count is multiplicative. -/
lemma nroots_mul (h : ℕ) {m n : ℕ} (hcop : Nat.Coprime m n) :
    nroots h (m * n) = nroots h m * nroots h n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hn1 : n = 1 := by simpa using hcop
    subst hn1; simp [nroots_zero, nroots_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm1 : m = 1 := by simpa using hcop
    subst hm1; simp [nroots_zero, nroots_one]
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero (m * n) := ⟨by positivity⟩
  rw [nroots_eq_card_zmod, nroots_eq_card_zmod, nroots_eq_card_zmod,
    ← Finset.card_product, ← Finset.filter_product, Finset.univ_product_univ]
  have crt := ZMod.chineseRemainder hcop
  have hiff : ∀ x : ZMod (m * n),
      (x * (x + (h : ZMod (m * n))) = 0) ↔
        ((crt x).1 * ((crt x).1 + (h : ZMod m)) = 0 ∧
          (crt x).2 * ((crt x).2 + (h : ZMod n)) = 0) := by
    intro x
    rw [← EmbeddingLike.map_eq_zero_iff (f := crt), map_mul, map_add, map_natCast,
      Prod.ext_iff]
    simp [Prod.fst_mul, Prod.fst_add, Prod.snd_mul, Prod.snd_add]
  apply Finset.card_bij (fun x _ => crt x)
  · intro x hxmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxmem ⊢
    exact (hiff x).mp hxmem
  · intro x₁ _ x₂ _ heq
    exact crt.injective heq
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨crt.symm y, ?_, crt.apply_symm_apply y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hiff (crt.symm y), crt.apply_symm_apply y]
    exact hy

/-- Root count at a prime: `1` root if `p ∣ 2h`, else `2` (`h` even). -/
lemma nroots_prime {p : ℕ} (hp : p.Prime) {h : ℕ} (heven : 2 ∣ h) :
    nroots h p = if p ∣ 2 * h then 1 else 2 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  rw [nroots_eq_card_zmod]
  have hset : (Finset.univ.filter (fun x : ZMod p => x * (x + (h : ZMod p)) = 0))
      = {0, -(h : ZMod p)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      rcases mul_eq_zero.mp hx with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    · rintro (rfl | rfl)
      · simp
      · simp
  rw [hset]
  by_cases hph : p ∣ h
  · have h0 : (h : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hph
    rw [if_pos (hph.mul_left 2), h0, neg_zero]
    simp
  · have h0 : (h : ZMod p) ≠ 0 := fun hc => hph ((ZMod.natCast_eq_zero_iff _ _).mp hc)
    have hnodvd : ¬ p ∣ 2 * h := by
      intro hc
      rcases (Nat.Prime.dvd_mul hp).mp hc with h2 | hh
      · have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        exact hph (hp2 ▸ heven)
      · exact hph hh
    rw [if_neg hnodvd]
    have hne : (0 : ZMod p) ∉ ({-(h : ZMod p)} : Finset (ZMod p)) := by
      simp only [Finset.mem_singleton]
      intro hc
      exact h0 (neg_eq_zero.mp hc.symm)
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]

/- ## `ρ_h` equals the root count on squarefree numbers (for even `h`) -/

/-- The root count as an arithmetic function. -/
def nrootsA (h : ℕ) : ArithmeticFunction ℕ := ⟨nroots h, nroots_zero h⟩

@[simp] lemma nrootsA_apply (h d : ℕ) : nrootsA h d = nroots h d := rfl

lemma nrootsA_isMultiplicative (h : ℕ) : (nrootsA h).IsMultiplicative := by
  constructor
  · exact nroots_one h
  · intro m n hcop
    exact nroots_mul h hcop

lemma nroots_eq_prod_primeFactors (h : ℕ) {d : ℕ} (hd : Squarefree d) :
    nroots h d = ∏ p ∈ d.primeFactors, nroots h p := by
  have hmap := (nrootsA_isMultiplicative h).map_prod_of_subset_primeFactors d
    d.primeFactors Finset.Subset.rfl
  simp only [nrootsA_apply] at hmap
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact hmap

lemma rhoFun_eq_nroots {h : ℕ} (heven : 2 ∣ h) {d : ℕ} (hd : Squarefree d) :
    rhoFun h d = (nroots h d : ℝ) := by
  rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hd.ne_zero,
    nroots_eq_prod_primeFactors h hd]
  push_cast
  apply Finset.prod_congr rfl
  intro p hp
  rw [nroots_prime (Nat.prime_of_mem_primeFactors hp) heven]
  split_ifs <;> norm_num

lemma rhoFun_nonneg (h d : ℕ) : 0 ≤ rhoFun h d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hd.ne']
    apply Finset.prod_nonneg
    intro p _
    split_ifs <;> norm_num

lemma rhoFun_le_two_pow (h : ℕ) {d : ℕ} (hd : d ≠ 0) :
    rhoFun h d ≤ 2 ^ d.primeFactors.card := by
  rw [rhoFun, ArithmeticFunction.prodPrimeFactors_apply hd]
  calc ∏ p ∈ d.primeFactors, (if p ∣ 2 * h then (1:ℝ) else 2)
      ≤ ∏ p ∈ d.primeFactors, (2:ℝ) := by
        apply Finset.prod_le_prod
        · intro p _; split_ifs <;> norm_num
        · intro p _; split_ifs <;> norm_num
    _ = 2 ^ d.primeFactors.card := by rw [Finset.prod_const]

/- ## Counting a residue class in `[1, M]` -/

lemma range_succ_eq_insert_Icc (M : ℕ) :
    Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
  ext n
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

/-- The number of `n ∈ [1, M]` in a fixed residue class mod `d` is within `1`
of `M/d`. -/
lemma card_Icc_filter_mod (M : ℕ) {d r : ℕ} (hd : 0 < d) (hr : r < d) :
    |(((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) - M / d| ≤ 1 := by
  have hcount : ((Finset.range (M + 1)).filter (fun n => n % d = r)).card
      = (M + 1) / d + if r < (M + 1) % d then 1 else 0 := by
    have h1 : (Finset.range (M + 1)).filter (fun n => n % d = r)
        = (Finset.range (M + 1)).filter (fun x => x ≡ r [MOD d]) := by
      apply Finset.filter_congr
      intro n _
      simp [Nat.ModEq, Nat.mod_eq_of_lt hr]
    rw [h1, ← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hd r,
      Nat.mod_eq_of_lt hr]
  have hsplit : ((Finset.range (M + 1)).filter (fun n => n % d = r)).card
      = ((Finset.Icc 1 M).filter (fun n => n % d = r)).card
        + if r = 0 then 1 else 0 := by
    rw [range_succ_eq_insert_Icc, Finset.filter_insert]
    by_cases hr0 : r = 0
    · rw [if_pos (show (0:ℕ) % d = r by rw [Nat.zero_mod, hr0]), if_pos hr0,
        Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg (show ¬ (0:ℕ) % d = r by
        rw [Nat.zero_mod]; exact fun hc => hr0 hc.symm), if_neg hr0, add_zero]
  have hkey : ((Finset.Icc 1 M).filter (fun n => n % d = r)).card
        + (if r = 0 then 1 else 0)
      = (M + 1) / d + if r < (M + 1) % d then 1 else 0 := by
    rw [← hsplit, hcount]
  have hdm : d * ((M + 1) / d) + (M + 1) % d = M + 1 := Nat.div_add_mod (M + 1) d
  have hsd : (M + 1) % d < d := Nat.mod_lt _ hd
  set c := ((Finset.Icc 1 M).filter (fun n => n % d = r)).card with hcdef
  set a := (M + 1) / d with hadef
  set s := (M + 1) % d with hsdef
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hdmR : (d:ℝ) * a + s = M + 1 := by exact_mod_cast hdm
  have hsdR : (s:ℝ) + 1 ≤ d := by exact_mod_cast hsd
  have hs0 : (0:ℝ) ≤ s := by positivity
  have hub : (M:ℝ) / d ≤ c + 1 := by
    rw [div_le_iff₀ hdR]
    rcases eq_or_ne r 0 with hr0 | hr0
    · rw [if_pos hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hs0' : s = 0 := by omega
        have hca : (c:ℝ) + 1 = a := by exact_mod_cast hkey
        have : (s:ℝ) = 0 := by exact_mod_cast hs0'
        nlinarith
    · rw [if_neg hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hca : (c:ℝ) = a + 1 := by exact_mod_cast hkey
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
  have hlb : (c:ℝ) - 1 ≤ M / d := by
    rw [le_div_iff₀ hdR]
    rcases eq_or_ne r 0 with hr0 | hr0
    · rw [if_pos hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hs1 : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hca : (c:ℝ) + 1 = a := by exact_mod_cast hkey
        nlinarith
    · rw [if_neg hr0] at hkey
      by_cases hε : r < s
      · rw [if_pos hε] at hkey
        have hs1 : (1:ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
        have hca : (c:ℝ) = a + 1 := by exact_mod_cast hkey
        rw [hca]; nlinarith
      · rw [if_neg hε] at hkey
        have hca : (c:ℝ) = a := by exact_mod_cast (by omega : c = a)
        rw [hca]; nlinarith
  rw [abs_le]
  constructor <;> linarith

/- ## The multiplicity sum and remainder of the pair sieve -/

@[simp] lemma pairSieve_support (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).support = (Finset.Icc 1 M).image (fun n => n * (n + h)) := rfl

@[simp] lemma pairSieve_weights (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    (pairSieve M h z hz).weights = fun _ => 1 := rfl

lemma mul_shift_injOn (h M : ℕ) :
    Set.InjOn (fun n => n * (n + h)) ((Finset.Icc 1 M : Finset ℕ) : Set ℕ) := by
  intro a ha b hb heq
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  dsimp only at heq
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · exact absurd heq
      (Nat.ne_of_lt (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)))
  · exact hab
  · exact absurd heq.symm
      (Nat.ne_of_lt (mul_lt_mul'' hab (by omega) (Nat.zero_le _) (Nat.zero_le _)))

lemma pairSieve_multSum (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (d : ℕ) :
    BoundingSieve.multSum (s := (pairSieve M h z hz).toBoundingSieve) d
      = (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).card : ℝ) := by
  unfold BoundingSieve.multSum
  simp only [pairSieve_support, pairSieve_weights]
  rw [Finset.sum_image (mul_shift_injOn h M)]
  simp only [Finset.sum_boole]

/-- The key remainder estimate: for squarefree `d` and even `h`,
`|multSum d − ν(d)·M| ≤ 2^ω(d)`. -/
lemma pairSieve_abs_rem_le (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (heven : 2 ∣ h)
    {d : ℕ} (hd : Squarefree d) :
    |BoundingSieve.rem (s := (pairSieve M h z hz).toBoundingSieve) d|
      ≤ 2 ^ d.primeFactors.card := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd.ne_zero
  have hmaps : Set.MapsTo (fun n => n % d)
      (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h)) : Finset ℕ) : Set ℕ)
      (((Finset.range d).filter (fun r => d ∣ r * (r + h)) : Finset ℕ) : Set ℕ) := by
    intro n hn
    rw [Finset.mem_coe, Finset.mem_filter] at hn
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.mod_lt n hd0, (dvd_shift_iff_mod d h n).mp hn.2⟩
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
      (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).filter
          (fun n => n % d = r))
        = (Finset.Icc 1 M).filter (fun n => n % d = r) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro n _
    constructor
    · exact fun hx => hx.2
    · intro hx
      exact ⟨(dvd_shift_iff_mod d h n).mpr (by rw [hx]; exact hr.2), hx⟩
  have hdecomp' : (((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).card : ℝ)
      = ∑ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
          (((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) := by
    rw [hdecomp, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hfib r hr]
  have hnu : pairNu h d * (M : ℝ)
      = ∑ _r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)), (M : ℝ) / d := by
    rw [Finset.sum_const, nsmul_eq_mul, pairNu_apply, rhoFun_eq_nroots heven hd]
    have hcard : (((Finset.range d).filter (fun r => d ∣ r * (r + h))).card : ℝ)
        = (nroots h d : ℝ) := rfl
    rw [hcard]
    ring
  unfold BoundingSieve.rem
  rw [pairSieve_multSum, pairSieve_nu, pairSieve_totalMass]
  calc |(((Finset.Icc 1 M).filter (fun n => d ∣ n * (n + h))).card : ℝ)
        - pairNu h d * (M : ℝ)|
      = |∑ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
          ((((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) - (M : ℝ) / d)| := by
        rw [hdecomp', hnu, Finset.sum_sub_distrib]
    _ ≤ ∑ r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)),
          |(((Finset.Icc 1 M).filter (fun n => n % d = r)).card : ℝ) - (M : ℝ) / d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ (Finset.range d).filter (fun r => d ∣ r * (r + h)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr
        exact card_Icc_filter_mod M hd0 hr.1
    _ = (nroots h d : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rfl
    _ = rhoFun h d := (rhoFun_eq_nroots heven hd).symm
    _ ≤ 2 ^ d.primeFactors.card := rhoFun_le_two_pow h hd.ne_zero

/- ## The error sum bound -/

lemma omega_eq_card_primeFactors (d : ℕ) :
    ArithmeticFunction.cardDistinctFactors d = d.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset]
  rfl

/- ## Prime pairs land in the sifted set -/

open scoped Classical in
lemma pairs_card_le_siftedSum_add (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (hh : 0 < h)
    (_hM : 1 ≤ M) :
    (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      ≤ BoundingSieve.siftedSum (s := (pairSieve M h z hz).toBoundingSieve) + (z + 1) := by
  have hsift := Sieve.siftedSum_eq (pairSieve M h z hz) (fun _ _ => rfl) z hz rfl
  set A := (Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h)) with hA
  have hsplit : A.card = (A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card
      + (A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card :=
    (Finset.card_filter_add_card_filter_not (fun n : ℕ => (n:ℝ) ≤ z)).symm
  have h1 : (A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card ≤ ⌊z⌋₊ := by
    have hsub : A.filter (fun n : ℕ => (n:ℝ) ≤ z) ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro n hn
      rw [Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      exact ⟨hn.1.1.1, Nat.le_floor hn.2⟩
    calc (A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card ≤ (Finset.Icc 1 ⌊z⌋₊).card :=
          Finset.card_le_card hsub
      _ = ⌊z⌋₊ := by rw [Nat.card_Icc]; omega
  have h2 : (A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card
      ≤ (((pairSieve M h z hz).support).filter
          (fun d => ∀ p : ℕ, p.Prime → (p:ℝ) ≤ z → ¬ p ∣ d)).card := by
    apply Finset.card_le_card_of_injOn (fun n => n * (n + h))
    · intro n hn
      have hn' : n ∈ A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z)) := hn
      rw [Finset.mem_filter, hA, Finset.mem_filter, Finset.mem_Icc] at hn'
      obtain ⟨⟨⟨hn1, hnM⟩, hp, hq⟩, hzn⟩ := hn'
      have hgoal : n * (n + h) ∈ ((pairSieve M h z hz).support).filter
          (fun d => ∀ p : ℕ, p.Prime → (p:ℝ) ≤ z → ¬ p ∣ d) := by
        rw [Finset.mem_filter]
        constructor
        · rw [pairSieve_support]
          exact Finset.mem_image_of_mem _ (Finset.mem_Icc.mpr ⟨hn1, hnM⟩)
        · intro p hpp hpz hpdvd
          rcases (Nat.Prime.dvd_mul hpp).mp hpdvd with hd | hd
          · rcases (Nat.prime_dvd_prime_iff_eq hpp hp).mp hd with rfl
            exact hzn hpz
          · have hpn : p = n + h := (Nat.prime_dvd_prime_iff_eq hpp hq).mp hd
            apply hzn
            have hle : ((n + h : ℕ) : ℝ) ≤ z := by rw [← hpn]; exact hpz
            push_cast at hle
            have hh0 : (0:ℝ) ≤ h := by positivity
            linarith
      exact hgoal
    · apply (mul_shift_injOn h M).mono
      intro n hn
      have hn' : n ∈ A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z)) := hn
      have hnA : n ∈ A := Finset.mem_of_mem_filter _ hn'
      rw [hA] at hnA
      exact Finset.mem_coe.mpr (Finset.mem_of_mem_filter _ hnA)
  rw [hsift]
  have hfloor : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le (by linarith)
  have h1R : ((A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card : ℝ) ≤ z :=
    le_trans (by exact_mod_cast h1) hfloor
  have h2R : ((A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card : ℝ)
      ≤ ((((pairSieve M h z hz).support).filter
          (fun d => ∀ p : ℕ, p.Prime → (p:ℝ) ≤ z → ¬ p ∣ d)).card : ℝ) := by
    exact_mod_cast h2
  have hAR : (A.card : ℝ) = ((A.filter (fun n : ℕ => (n:ℝ) ≤ z)).card : ℝ)
      + ((A.filter (fun n : ℕ => ¬ ((n:ℝ) ≤ z))).card : ℝ) := by
    exact_mod_cast hsplit
  rw [hAR]
  linarith

/- ## The main sieve bound for prime pairs -/

theorem pairSieve_pairs_le (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (heven : 2 ∣ h) (hh : 0 < h)
    (hM : 1 ≤ M) :
    (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n+h))).card : ℝ)
      ≤ (M : ℝ) / (pairSieve M h z hz).selbergBoundingSum
        + ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) + (z + 1) := by
  have hpairs := pairs_card_le_siftedSum_add M h z hz hh hM
  refine hpairs.trans ?_
  have hb := SelbergSieve.selberg_bound_simple (pairSieve M h z hz)
  simp only [pairSieve_totalMass, pairSieve_prodPrimes, pairSieve_level] at hb
  refine ((add_le_add_iff_right (z + 1)).mpr hb).trans ?_
  refine (add_le_add_iff_right (z + 1)).mpr ?_
  refine (add_le_add_iff_left _).mpr ?_
  -- error sum ≤ ∑_{d ≤ ⌊z⌋} 6^ω(d)
  refine le_trans (Finset.sum_le_sum
    (g := fun d : ℕ => if (d:ℝ) ≤ z then (6:ℝ) ^ d.primeFactors.card else 0) ?_) ?_
  · intro d hd
    have hsq : Squarefree d :=
      (Sieve.primorial_squarefree _).squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
    change (if (d : ℝ) ≤ z then
      (3 : ℝ) ^ (ω d) * |(pairSieve M h z hz).toBoundingSieve.rem d| else 0) ≤
      (if (d : ℝ) ≤ z then (6 : ℝ) ^ d.primeFactors.card else 0)
    by_cases hdz : (d : ℝ) ≤ z
    · rw [if_pos hdz, if_pos hdz]
      calc (3:ℝ) ^ (ω d)
            * |BoundingSieve.rem (s := (pairSieve M h z hz).toBoundingSieve) d|
          ≤ (3:ℝ) ^ (ω d) * 2 ^ d.primeFactors.card := by
            apply mul_le_mul_of_nonneg_left (pairSieve_abs_rem_le M h z hz heven hsq)
            positivity
        _ = (6:ℝ) ^ d.primeFactors.card := by
            rw [omega_eq_card_primeFactors, ← mul_pow]
            norm_num
    · simp [hdz]
  · rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [Finset.mem_filter] at hd
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_mem_divisors hd.1, Nat.le_floor hd.2⟩
    · intro d _ _
      positivity

/- ## Lower bound for the Selberg bounding sum -/

theorem pairSieve_boundingSum_ge (M h : ℕ) (z : ℝ) (hz : 1 ≤ z) (_heven : 2 ∣ h)
    (_hh : 0 < h) :
    ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
        (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
        (2:ℝ)^(ℓ.primeFactors.card) / ℓ
      ≤ (pairSieve M h z hz).selbergBoundingSum := by
  have hz0 : (0:ℝ) ≤ z := by linarith
  -- every ℓ in the index set is a divisor of the primorial with ℓ² ≤ z
  have hmem : ∀ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
      (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
      ℓ ∈ (primorial ⌊z⌋₊).divisors.filter (fun l : ℕ => (l:ℝ)^2 ≤ z) := by
    intro ℓ hℓ
    rw [Finset.mem_filter, Finset.mem_Icc] at hℓ
    obtain ⟨⟨hℓ1, hℓsqrt⟩, hℓsq, hℓcop⟩ := hℓ
    have hℓR : (ℓ:ℝ) ≤ Real.sqrt z :=
      le_trans (Nat.cast_le.mpr hℓsqrt) (Nat.floor_le (Real.sqrt_nonneg z))
    have hsq : ((ℓ:ℝ))^2 ≤ z := by
      calc ((ℓ:ℝ))^2 ≤ (Real.sqrt z)^2 := by gcongr
        _ = z := Real.sq_sqrt hz0
    have hdvd : ℓ ∣ primorial ⌊z⌋₊ := by
      rw [← Nat.prod_primeFactors_of_squarefree hℓsq]
      apply Sieve.prod_primes_dvd_of_dvd
      · intro p hp
        rw [Sieve.prime_dvd_primorial_iff _ _ (Nat.prime_of_mem_primeFactors hp)]
        have hpl : p ≤ ℓ := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
        have hsz : Real.sqrt z ≤ z := Real.sqrt_le_self z hz
        exact le_trans hpl (le_trans hℓsqrt (Nat.floor_mono hsz))
      · intro p hp
        exact Nat.prime_of_mem_primeFactors hp
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdvd, (Sieve.primorial_squarefree _).ne_zero⟩, hsq⟩
  -- termwise: 2^ω(ℓ)/ℓ = ν(ℓ) ≤ g(ℓ)
  have hterm : ∀ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
      (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
      (2:ℝ)^(ℓ.primeFactors.card) / ℓ
        ≤ SelbergSieve.selbergTerms (pairSieve M h z hz).toBoundingSieve ℓ := by
    intro ℓ hℓ
    have hℓdvd : ℓ ∣ primorial ⌊z⌋₊ := by
      have hm := hmem ℓ hℓ
      rw [Finset.mem_filter, Nat.mem_divisors] at hm
      exact hm.1.1
    rw [Finset.mem_filter, Finset.mem_Icc] at hℓ
    obtain ⟨⟨hℓ1, _⟩, hℓsq, hℓcop⟩ := hℓ
    have hnu_eq : pairNu h ℓ = (2:ℝ)^(ℓ.primeFactors.card) / ℓ := by
      rw [pairNu_apply, rhoFun, ArithmeticFunction.prodPrimeFactors_apply hℓsq.ne_zero]
      congr 1
      calc (∏ p ∈ ℓ.primeFactors, if p ∣ 2*h then (1:ℝ) else 2)
          = ∏ _p ∈ ℓ.primeFactors, (2:ℝ) := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [if_neg]
            intro hpdvd
            have hpp := Nat.prime_of_mem_primeFactors hp
            have hone : p ∣ 1 :=
              hℓcop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpdvd
            exact hpp.ne_one (Nat.dvd_one.mp hone)
        _ = (2:ℝ) ^ ℓ.primeFactors.card := by rw [Finset.prod_const]
    rw [SelbergSieve.selbergTerms_apply, pairSieve_nu, ← hnu_eq]
    have hν : 0 ≤ pairNu h ℓ := by rw [hnu_eq]; positivity
    have hfac : ∀ p ∈ ℓ.primeFactors, (1:ℝ) ≤ 1 / (1 - pairNu h p) := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpP : p ∣ primorial ⌊z⌋₊ := (Nat.dvd_of_mem_primeFactors hp).trans hℓdvd
      have h1 : 0 < pairNu h p := by
        have hpos := BoundingSieve.nu_pos_of_dvd_prodPrimes
          (s := (pairSieve M h z hz).toBoundingSieve) (d := p) hpP
        simpa [pairSieve_nu] using hpos
      have h2 : pairNu h p < 1 := by
        have hlt := (pairSieve M h z hz).nu_lt_one_of_prime p hpp hpP
        simpa [pairSieve_nu] using hlt
      have hpos : 0 < 1 - pairNu h p := by linarith
      rw [le_div_iff₀ hpos, one_mul]
      linarith
    have hprod : (1:ℝ) ≤ ∏ p ∈ ℓ.primeFactors, 1 / (1 - pairNu h p) := by
      have hle : ∏ _p ∈ ℓ.primeFactors, (1:ℝ)
          ≤ ∏ p ∈ ℓ.primeFactors, 1 / (1 - pairNu h p) := by
        apply Finset.prod_le_prod
        · intro p _
          norm_num
        · intro p hp
          exact hfac p hp
      simpa using hle
    linarith [mul_le_mul_of_nonneg_left hprod hν]
  calc ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
        (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
        (2:ℝ)^(ℓ.primeFactors.card) / ℓ
      ≤ ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
          (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
          SelbergSieve.selbergTerms (pairSieve M h z hz).toBoundingSieve ℓ :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ l ∈ (primorial ⌊z⌋₊).divisors.filter (fun l : ℕ => (l:ℝ)^2 ≤ z),
          SelbergSieve.selbergTerms (pairSieve M h z hz).toBoundingSieve l := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => hmem ℓ hℓ)
        intro l hl _
        apply le_of_lt
        apply SelbergSieve.selbergTerms_pos
        rw [Finset.mem_filter, Nat.mem_divisors] at hl
        exact hl.1.1
    _ = (pairSieve M h z hz).selbergBoundingSum := by
        rw [Finset.sum_filter]
        simp only [SelbergSieve.selbergBoundingSum, pairSieve_prodPrimes, pairSieve_level]
        apply Finset.sum_congr rfl
        intro l _
        by_cases hl : (l : ℝ) ^ 2 ≤ z <;> simp [hl]


end

section
/-
# Erdős 884 — Lemma B: counting prime pairs with small gap

Exports `Erdos884.prime_pairs_bound`: the number of prime pairs `(p, q)` with
`p < q ≤ 9t` and `q - p ≤ N ≤ (log t)²` is at most `C_B · N · t / (log t)²`.

Route: fiber the pairs over the gap `h = q - p`.  Odd gaps contribute at most `1`
each (`p = 2` forced).  Even gaps are handled by the Selberg pair sieve
(`pairSieve_pairs_le`), whose bounding sum is bounded below via
`pairSieve_boundingSum_ge` + `coprime_squarefree_sum_lower`; the sum of the
resulting `(2h/φ(2h))²` weights is controlled by `sum_totient_ratio_sq_le`.
-/


/- ## Fibering the pair count over the gap `h` -/

lemma pc_pair_fiber (M N : ℕ) :
    ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card
      ≤ ∑ h ∈ Finset.Icc 1 N,
          ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card := by
  have hsub : (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)
      ⊆ (Finset.Icc 1 N).biUnion (fun h =>
          ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).image
            (fun p => (p, p + h))) := by
    intro pq hpq
    obtain ⟨a, b⟩ := pq
    rw [Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨h1, h2⟩, hp, hq, hlt, hle⟩ := hpq
    rw [Finset.mem_Icc] at h1 h2
    rw [Finset.mem_biUnion]
    refine ⟨b - a, Finset.mem_Icc.mpr ⟨by omega, hle⟩, ?_⟩
    rw [Finset.mem_image]
    have he : a + (b - a) = b := by omega
    refine ⟨a, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨h1.1, h1.2⟩, hp, by rw [he]; exact hq⟩
    · rw [he]
  calc ((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card
      ≤ ((Finset.Icc 1 N).biUnion (fun h =>
          ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).image
            (fun p => (p, p + h)))).card := Finset.card_le_card hsub
    _ ≤ ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).image (fun p => (p, p + h))).card :=
        Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun h _ => Finset.card_image_le)

/- ## Odd gaps: at most one pair -/

lemma pc_odd_card (M h : ℕ) (hodd : ¬ 2 ∣ h) :
    ((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card ≤ 1 := by
  have hmem : ∀ n ∈ (Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h)),
      n = 2 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨-, hp, hq⟩ := hn
    by_contra hne
    have hn3 : 3 ≤ n := by have := hp.two_le; omega
    have hnodd : n % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hne)
    have hdvd : 2 ∣ n + h := by omega
    rcases hq.eq_one_or_self_of_dvd 2 hdvd with h1 | h1 <;> omega
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [hmem a ha, hmem b hb]

/- ## The error-sum bound -/

lemma pc_err_sum (z : ℝ) (hz : 1 ≤ z) :
    ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) ≤ z * (1 + Real.log z)^5 := by
  have h0 := sum_pow_primeFactors_le 6 ⌊z⌋₊ (by norm_num)
  norm_num at h0
  have h1 : (1:ℝ) ≤ ((⌊z⌋₊ : ℕ) : ℝ) := by
    have : (1:ℕ) ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz)
    exact_mod_cast this
  have h2 : ((⌊z⌋₊ : ℕ) : ℝ) ≤ z := Nat.floor_le (by linarith)
  have h3 : Real.log ((⌊z⌋₊ : ℕ) : ℝ) ≤ Real.log z := Real.log_le_log (by linarith) h2
  have h4 : (0:ℝ) ≤ 1 + Real.log ((⌊z⌋₊ : ℕ) : ℝ) := by
    have := Real.log_nonneg h1
    linarith
  refine h0.trans ?_
  exact mul_le_mul h2 (pow_le_pow_left₀ h4 (by linarith) 5) (pow_nonneg h4 5) (by linarith)

/- ## The totient-ratio sum over even gaps -/

lemma pc_totient_sum (N : ℕ) :
    ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
        (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2 ≤ 400 * N := by
  have h1 : ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
        (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
      ≤ ∑ h' ∈ Finset.Icc 1 (2*N), ((h' : ℝ) / (Nat.totient h' : ℝ))^2 := by
    apply cs_sum_le_sum_inj (fun h => 2*h)
    · intro a ha
      rw [Finset.mem_filter, Finset.mem_Icc] at ha
      rw [Finset.mem_Icc]
      omega
    · intro a _ b _ hab
      simp only at hab
      omega
    · intro a _
      exact le_rfl
    · intro b _
      positivity
  have h2 := sum_totient_ratio_sq_le (2*N)
  have h3 : (200:ℝ) * ((2*N : ℕ) : ℝ) = 400 * N := by push_cast; ring
  linarith

/- ## Junk-term absorption: `4√t(1+log t)⁵ ≤ t/(log t)²` for large `t` -/

lemma pc_sqrt_lower (t : ℝ) (ht : 1 ≤ t) (hL : (2:ℝ)^40 ≤ Real.log t) :
    4 * (1 + Real.log t)^5 * (Real.log t)^2 ≤ Real.sqrt t := by
  set L := Real.log t with hLdef
  have hL1 : (1:ℝ) ≤ L := le_trans (by norm_num) hL
  have hL0 : (0:ℝ) < L := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  -- `√t = exp (L/2) ≥ (L/16)⁸`
  have hlogs : Real.log (Real.sqrt t) = L / 2 := by
    rw [Real.log_sqrt ht0.le]
  have hs_eq : Real.sqrt t = Real.exp (L / 2) := by
    rw [← hlogs, Real.exp_log hspos]
  have hexp8 : Real.exp (L/16) ^ 8 = Real.exp (L / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have he3 : L/16 ≤ Real.exp (L/16) := by
    linarith [Real.add_one_le_exp (L/16)]
  have hexp_low : (L/16)^8 ≤ Real.exp (L / 2) := by
    calc (L/16)^8 ≤ Real.exp (L/16) ^ 8 := pow_le_pow_left₀ (by positivity) he3 8
      _ = Real.exp (L / 2) := hexp8
  have hmid : 128 * L^7 ≤ (L/16)^8 := by
    have hpow : (L/16)^8 = L^8 / 16^8 := by
      rw [div_pow]
    rw [hpow, le_div_iff₀ (by positivity : (0:ℝ) < 16^8)]
    have hLbig : (128:ℝ) * 16^8 ≤ L := by
      norm_num at hL ⊢
      linarith
    calc 128 * L^7 * 16^8 = (128 * 16^8) * L^7 := by ring
      _ ≤ L * L^7 := mul_le_mul_of_nonneg_right hLbig (by positivity)
      _ = L^8 := by ring
  calc 4 * (1 + L)^5 * L^2
      ≤ 4 * (2*L)^5 * L^2 := by
        have h5 : (1 + L)^5 ≤ (2*L)^5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h5 (by norm_num : (0:ℝ) ≤ 4))
          (by positivity : (0:ℝ) ≤ L^2)
        linarith
    _ = 128 * L^7 := by ring
    _ ≤ (L/16)^8 := hmid
    _ ≤ Real.exp (L / 2) := hexp_low
    _ = Real.sqrt t := hs_eq.symm

lemma pc_junk_le (t : ℝ) (ht : 1 ≤ t) (hL : (2:ℝ)^40 ≤ Real.log t) :
    4 * Real.sqrt t * (1 + Real.log t)^5 ≤ t / (Real.log t)^2 := by
  set L := Real.log t with hLdef
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hL
  have key := pc_sqrt_lower t ht hL
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
  rw [le_div_iff₀ (by positivity : (0:ℝ) < L^2)]
  calc 4 * Real.sqrt t * (1 + L)^5 * L^2
      = Real.sqrt t * (4 * (1 + L)^5 * L^2) := by ring
    _ ≤ Real.sqrt t * Real.sqrt t :=
        mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg t)
    _ = t := hs

/- ## The main theorem -/

theorem prime_pairs_bound :
    ∃ C_B : ℝ, 1 ≤ C_B ∧ ∃ T_B : ℝ, 3 ≤ T_B ∧ ∀ t : ℝ, T_B ≤ t → ∀ N : ℕ, 2 ≤ N →
      (N:ℝ) ≤ (Real.log t)^2 →
      (((Finset.Icc 1 ⌊9*t⌋₊ ×ˢ Finset.Icc 1 ⌊9*t⌋₊).filter
          (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card : ℝ)
        ≤ C_B * N * t / (Real.log t)^2 := by
  obtain ⟨c₀, hc₀, w₀, hlower⟩ := coprime_squarefree_sum_lower
  have hCB1 : (1:ℝ) ≤ 90000 / c₀ + 1 := by
    have : (0:ℝ) ≤ 90000 / c₀ := by positivity
    linarith
  have hTB3 : (3:ℝ) ≤ max (Real.exp ((2:ℝ)^40)) (((w₀:ℝ)+1)^4) := by
    have h1 : (3:ℝ) ≤ Real.exp ((2:ℝ)^40) := by
      have h2 := Real.add_one_le_exp ((2:ℝ)^40)
      have h3 : (3:ℝ) ≤ (2:ℝ)^40 + 1 := by norm_num
      linarith
    exact le_trans h1 (le_max_left _ _)
  refine ⟨90000 / c₀ + 1, hCB1, max (Real.exp ((2:ℝ)^40)) (((w₀:ℝ)+1)^4), hTB3, ?_⟩
  intro t ht N hN2 hNlog
  -- basic facts about `t`
  have htexp : Real.exp ((2:ℝ)^40) ≤ t := le_trans (le_max_left _ _) ht
  have htw : ((w₀:ℝ)+1)^4 ≤ t := le_trans (le_max_right _ _) ht
  have hL : (2:ℝ)^40 ≤ Real.log t := by
    have h1 := Real.log_le_log (Real.exp_pos _) htexp
    rwa [Real.log_exp] at h1
  set L := Real.log t with hLdef
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le (by norm_num) hL
  have hL250 : (250:ℝ) ≤ L := le_trans (by norm_num) hL
  have ht16 : (16:ℝ) ≤ t := by
    have h1 := Real.add_one_le_exp ((2:ℝ)^40)
    have h2 : (16:ℝ) ≤ (2:ℝ)^40 + 1 := by norm_num
    linarith
  have ht1 : (1:ℝ) ≤ t := by linarith
  have ht0 : (0:ℝ) < t := by linarith
  -- the sieve level `z = √t`
  set z := Real.sqrt t with hzdef
  have hz : (1:ℝ) ≤ z := by
    rw [hzdef]
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    norm_num
    linarith
  have hz4 : (4:ℝ) ≤ z := by
    rw [hzdef]
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    norm_num
    linarith
  have hlogz : Real.log z = L / 2 := by
    rw [hzdef, Real.log_sqrt ht0.le]
  -- the total mass `M = ⌊9t⌋₊`
  set M := ⌊9*t⌋₊ with hMdef
  have hM1 : 1 ≤ M := Nat.le_floor (by push_cast; linarith)
  have hM9t : (M:ℝ) ≤ 9*t := Nat.floor_le (by linarith)
  -- the fourth-root scale `w = ⌊√z⌋₊`
  have hu2 : (2:ℝ) ≤ Real.sqrt z := by
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    norm_num
    linarith
  have hfloorw : Real.sqrt z / 2 ≤ ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) := by
    have h1 := Nat.lt_floor_add_one (Real.sqrt z)
    linarith
  have hw₀w : w₀ ≤ ⌊Real.sqrt z⌋₊ := by
    apply Nat.le_floor
    have hx4 : (((w₀:ℝ)+1)^2)^2 ≤ t := by
      calc (((w₀:ℝ)+1)^2)^2 = ((w₀:ℝ)+1)^4 := by ring
        _ ≤ t := htw
    have hx2 : ((w₀:ℝ)+1)^2 ≤ z := by
      rw [hzdef]
      exact (Real.le_sqrt (by positivity) (by linarith)).mpr hx4
    have hx1 : (w₀:ℝ)+1 ≤ Real.sqrt z :=
      (Real.le_sqrt (by positivity) (by linarith)).mpr hx2
    linarith
  have hw1R : (1:ℝ) ≤ ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) := by linarith
  have hlogw : L/5 ≤ Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) := by
    have hlogu : Real.log (Real.sqrt z) = L/4 := by
      rw [Real.log_sqrt (by linarith : (0:ℝ) ≤ z), hlogz]
      ring
    have h1 : Real.log (Real.sqrt z / 2) ≤ Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) hfloorw
    have h2 : Real.log (Real.sqrt z / 2) = L/4 - Real.log 2 := by
      rw [Real.log_div (ne_of_gt (by linarith : (0:ℝ) < Real.sqrt z)) (by norm_num), hlogu]
    have h3 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  -- the per-`h` bound for even gaps
  have hkey : ∀ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
      (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ 225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
          + (z * (1 + L)^5 + (z + 1)) := by
    intro h hh
    rw [Finset.mem_filter, Finset.mem_Icc] at hh
    obtain ⟨⟨hh1, hhN⟩, heven⟩ := hh
    have hh0 : 0 < h := hh1
    have hbound := pairSieve_pairs_le M h z hz heven hh0 hM1
    have hSpos := pairSieve_boundingSum_pos M h z hz
    have hge := pairSieve_boundingSum_ge M h z hz heven hh0
    -- lower bound on the Selberg bounding sum
    have hm1 : 1 ≤ 2*h := by omega
    have hmw : ((2*h : ℕ) : ℝ) ≤ (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^3 := by
      have h1 : ((2*h : ℕ) : ℝ) ≤ 2*(N:ℝ) := by
        push_cast
        have : (h:ℝ) ≤ (N:ℝ) := by exact_mod_cast hhN
        linarith
      have h2 : 2*(N:ℝ) ≤ 2*L^2 := by linarith
      have h3 : 2*L^2 ≤ (L/5)^3 := by
        have h4 := mul_le_mul_of_nonneg_right hL250 (sq_nonneg L)
        nlinarith [h4]
      have h5 : (L/5)^3 ≤ (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^3 :=
        pow_le_pow_left₀ (by linarith) hlogw 3
      linarith
    have hlow := hlower ⌊Real.sqrt z⌋₊ hw₀w (2*h) hm1 hmw
    have hφpos : (0:ℝ) < (Nat.totient (2*h) : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < 2*h)
    have hmpos : (0:ℝ) < ((2*h : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 2*h)
    have hlow2 : c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2 * (L/5)^2
        ≤ (pairSieve M h z hz).selbergBoundingSum := by
      have hsq : (L/5)^2 ≤ (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^2 :=
        pow_le_pow_left₀ (by linarith) hlogw 2
      calc c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2 * (L/5)^2
          ≤ c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2
              * (Real.log ((⌊Real.sqrt z⌋₊ : ℕ) : ℝ))^2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ ≤ ∑ ℓ ∈ (Finset.Icc 1 ⌊Real.sqrt z⌋₊).filter
              (fun ℓ => Squarefree ℓ ∧ ℓ.Coprime (2*h)),
              (2:ℝ)^(ℓ.primeFactors.card) / ℓ := hlow
        _ ≤ _ := hge
    -- `M / S ≤ 225·t·(2h/φ(2h))²/(c₀ L²)`
    have hX0 : (0:ℝ) ≤ 225 * t / (c₀ * L^2)
        * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2 := by positivity
    have hXlow : (225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2)
          * (c₀ * ((Nat.totient (2*h) : ℝ) / ((2*h : ℕ) : ℝ))^2 * (L/5)^2) = 9 * t := by
      field_simp
      ring
    have hMX : (M:ℝ) / (pairSieve M h z hz).selbergBoundingSum
        ≤ 225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2 := by
      rw [div_le_iff₀ hSpos]
      calc (M:ℝ) ≤ 9 * t := hM9t
        _ = _ := hXlow.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow2 hX0
    -- the error term
    have herr : ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) ≤ z * (1 + L)^5 := by
      have h1 := pc_err_sum z hz
      have h2 : (0:ℝ) ≤ 1 + Real.log z := by
        have := Real.log_nonneg hz
        linarith
      calc ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card)
          ≤ z * (1 + Real.log z)^5 := h1
        _ ≤ z * (1 + L)^5 := by
            have h3 : (1 + Real.log z)^5 ≤ (1 + L)^5 :=
              pow_le_pow_left₀ h2 (by rw [hlogz]; linarith) 5
            exact mul_le_mul_of_nonneg_left h3 (by linarith)
    calc (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ (M:ℝ) / (pairSieve M h z hz).selbergBoundingSum
          + ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, (6:ℝ)^(d.primeFactors.card) + (z + 1) := hbound
      _ ≤ 225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
          + (z * (1 + L)^5 + (z + 1)) := by linarith
  -- assemble: fiber the pair count over the gap
  have hfiberR : (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ) := by
    exact_mod_cast pc_pair_fiber M N
  have hsplit : ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
        (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      = ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h), (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        + ∑ h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h), (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun h => 2 ∣ h) _).symm
  -- even gaps
  have hJ0 : (0:ℝ) ≤ z * (1 + L)^5 + (z + 1) := by
    have := mul_nonneg (show (0:ℝ) ≤ z by linarith)
      (pow_nonneg (show (0:ℝ) ≤ 1 + L by linarith) 5)
    linarith
  have heven_sum : ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
        (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      ≤ 225 * t / (c₀ * L^2) * (400 * N) + (N:ℝ) * (z * (1 + L)^5 + (z + 1)) := by
    calc ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
          (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ ∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
            (225 * t / (c₀ * L^2) * (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2
              + (z * (1 + L)^5 + (z + 1))) := Finset.sum_le_sum hkey
      _ = 225 * t / (c₀ * L^2) * (∑ h ∈ (Finset.Icc 1 N).filter (fun h => 2 ∣ h),
            (((2*h : ℕ) : ℝ) / (Nat.totient (2*h) : ℝ))^2)
          + (((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card : ℝ)
            * (z * (1 + L)^5 + (z + 1)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 225 * t / (c₀ * L^2) * (400 * N) + (N:ℝ) * (z * (1 + L)^5 + (z + 1)) := by
          have hE400 := pc_totient_sum N
          have hEcard : ((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card ≤ N := by
            calc ((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card
                ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
              _ = N := by rw [Nat.card_Icc]; omega
          have hEcardR : (((Finset.Icc 1 N).filter (fun h => 2 ∣ h)).card : ℝ) ≤ (N:ℝ) := by
            exact_mod_cast hEcard
          have t1 := mul_le_mul_of_nonneg_left hE400
            (show (0:ℝ) ≤ 225 * t / (c₀ * L^2) by positivity)
          have t2 := mul_le_mul_of_nonneg_right hEcardR hJ0
          linarith
  -- odd gaps
  have hodd_sum : ∑ h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h),
        (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
      ≤ (N:ℝ) := by
    calc ∑ h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h),
          (((Finset.Icc 1 M).filter (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ)
        ≤ ∑ _h ∈ (Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h), (1:ℝ) := by
          apply Finset.sum_le_sum
          intro h hh
          rw [Finset.mem_filter] at hh
          exact_mod_cast pc_odd_card M h hh.2
      _ = (((Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ (N:ℝ) := by
          have h1 : ((Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h)).card ≤ N := by
            calc ((Finset.Icc 1 N).filter (fun h => ¬ 2 ∣ h)).card
                ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
              _ = N := by rw [Nat.card_Icc]; omega
          exact_mod_cast h1
  -- absorb the junk terms
  have hjunk := pc_junk_le t ht1 hL
  rw [← hzdef] at hjunk
  have hp1 : (1:ℝ) ≤ (1 + L)^5 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ 1 + L) 5
    simpa using this
  have h1z : (1:ℝ) ≤ z * (1 + L)^5 := by
    have := mul_le_mul hz hp1 (by norm_num) (by linarith)
    linarith
  have hzz : z ≤ z * (1 + L)^5 :=
    le_mul_of_one_le_right (by linarith) hp1
  have hjunk2 : (N:ℝ) * (z * (1 + L)^5 + (z + 1)) + (N:ℝ) ≤ (N:ℝ) * (t / L^2) := by
    have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    have hchain : z * (1 + L)^5 + (z + 1) + 1 ≤ 4 * (z * (1 + L)^5) := by linarith
    calc (N:ℝ) * (z * (1 + L)^5 + (z + 1)) + (N:ℝ)
        = (N:ℝ) * (z * (1 + L)^5 + (z + 1) + 1) := by ring
      _ ≤ (N:ℝ) * (4 * (z * (1 + L)^5)) := mul_le_mul_of_nonneg_left hchain hN0
      _ ≤ (N:ℝ) * (t / L^2) := by
          apply mul_le_mul_of_nonneg_left _ hN0
          linarith [hjunk]
  -- conclusion
  have hmain : 225 * t / (c₀ * L^2) * (400 * (N:ℝ)) = 90000/c₀ * ((N:ℝ) * (t / L^2)) := by
    field_simp
    ring
  have hfinal : 90000/c₀ * ((N:ℝ) * (t / L^2)) + (N:ℝ) * (t / L^2)
      = (90000 / c₀ + 1) * (N:ℝ) * t / L^2 := by
    ring
  calc (((Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ N)).card : ℝ)
      ≤ ∑ h ∈ Finset.Icc 1 N, (((Finset.Icc 1 M).filter
          (fun n => Nat.Prime n ∧ Nat.Prime (n + h))).card : ℝ) := hfiberR
    _ ≤ 225 * t / (c₀ * L^2) * (400 * N) + (N:ℝ) * (z * (1 + L)^5 + (z + 1)) + (N:ℝ) := by
        rw [hsplit]
        linarith
    _ ≤ 90000/c₀ * ((N:ℝ) * (t / L^2)) + (N:ℝ) * (t / L^2) := by
        rw [← hmain]
        linarith
    _ = (90000 / c₀ + 1) * (N:ℝ) * t / L^2 := hfinal


end

end Erdos884

open Real Filter Finset

theorem close_prime_pairs
    (sieve : ∃ C : ℝ, 1 ≤ C ∧ ∃ T : ℝ, 3 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ D : ℕ, 2 ≤ D →
      (D : ℝ) ≤ (log t)^2 →
      (((Icc 1 ⌊9*t⌋₊ ×ˢ Icc 1 ⌊9*t⌋₊).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ D)).card : ℝ)
        ≤ C * D * t / (log t)^2) :
    OMA.R_Erdos912_erdos_912_variants_selfridge_R1.H2 := by
  classical
  obtain ⟨C,hC,T,hT,sieve⟩ := sieve
  refine ⟨8*C, by linarith, ?_⟩
  have hg : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hg.eventually_ge_atTop 4, (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (T^2),
    eventually_ge_atTop 2] with n hn hnT hn2
  let L := log (n : ℝ)
  let t := √((n : ℝ)*L)
  let D := ⌊L⌋₊
  let P := Nat.primesLE ⌊t⌋₊
  let Q := (P ×ˢ P).filter fun x => x.1 ≠ x.2 ∧ |(x.1 : ℝ)-x.2| < L
  let F := ((Icc 1 ⌊9*t⌋₊ ×ˢ Icc 1 ⌊9*t⌋₊).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 < pq.2 ∧ pq.2 - pq.1 ≤ D))
  have hL : 4 ≤ L := hn
  have hLpos : 0 < L := by linarith
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have htpos : 0 < t := Real.sqrt_pos.mpr (mul_pos hnpos hLpos)
  have ht2 : t^2 = (n : ℝ)*L := Real.sq_sqrt (by positivity)
  have htT : T ≤ t := by nlinarith only [ht2,hnT, mul_le_mul_of_nonneg_left (show 1 ≤ L by linarith) hnpos.le, htpos, hT]
  have hlog : L/2 ≤ log t := by
    dsimp [t]
    rw [Real.log_sqrt (by positivity), Real.log_mul hnpos.ne' hLpos.ne']
    have := Real.log_nonneg (by linarith : 1 ≤ L)
    dsimp [L] at *
    linarith
  have hD : (D : ℝ) ≤ L := Nat.floor_le hLpos.le
  have hD2 : 2 ≤ D := Nat.le_floor (by norm_num; linarith)
  have hsquare : L^2 ≤ 4*(log t)^2 := by nlinarith [sq_nonneg (log t - L/2), mul_nonneg (sub_nonneg.mpr hlog) hLpos.le]
  have hDlog : (D : ℝ) ≤ (log t)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hL) hLpos.le]
  have hF : (F.card : ℝ) ≤ C*D*t/(log t)^2 := sieve t htT D hD2 hDlog
  have hpoint {p : ℕ} (hp : p ∈ P) : p.Prime ∧ p ∈ Icc 1 ⌊9*t⌋₊ := by
    have h := Nat.mem_primesLE.mp hp
    exact ⟨h.2, mem_Icc.mpr ⟨h.2.one_lt.le, h.1.trans (Nat.floor_mono (by linarith))⟩⟩
  have gain {a b : ℕ} (ha : a ∈ P) (hb : b ∈ P) (hab : a < b) (hd : |(a : ℝ)-b| < L) :
      (a,b) ∈ F := by
    have ha' := hpoint ha
    have hb' := hpoint hb
    have hle : (a : ℝ) ≤ b := by exact_mod_cast hab.le
    rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hd
    exact mem_filter.mpr ⟨mem_product.mpr ⟨ha'.2,hb'.2⟩,ha'.1,hb'.1,hab,
      Nat.le_floor (by rw [Nat.cast_sub hab.le]; linarith)⟩
  have sub : Q ⊆ F ∪ F.image Prod.swap := by
    rintro ⟨a,b⟩ h
    obtain ⟨prod,hne,hd⟩ := mem_filter.mp h
    obtain ⟨ha,hb⟩ := mem_product.mp prod
    rcases lt_or_gt_of_ne hne with h|h
    · exact mem_union_left _ (gain ha hb h hd)
    · exact mem_union_right _ (mem_image.mpr ⟨(b,a), gain hb ha h (by rwa [abs_sub_comm]), rfl⟩)
  have hq : Q.card ≤ 2*F.card := by
    have := card_le_card sub
    have := card_union_le F (F.image Prod.swap)
    have := card_image_le (f := Prod.swap) (s := F)
    omega
  have hlogpos : 0 < log t := by linarith
  have hby : C*D*t/(log t)^2 ≤ 4*C*(t/L) := by
    apply (div_le_iff₀ (by positivity : 0 < (log t)^2)).mpr
    rw [show 4*C*(t/L)*(log t)^2 = C*t * (4*(log t)^2/L) by ring]
    have hratio : L ≤ 4*(log t)^2/L := (le_div_iff₀ hLpos).mpr (by nlinarith only [hsquare])
    calc C*D*t = C*t*D := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (hD.trans hratio) (by positivity)
  have hroot : t/L = √((n : ℝ)/L) := by
    rw [Real.sqrt_div hnpos.le, show t = √(n : ℝ) * √L from Real.sqrt_mul hnpos.le L]
    field_simp [hLpos.ne', (Real.sqrt_pos.mpr hLpos).ne']
    nlinarith [Real.sq_sqrt hLpos.le]
  change (Q.card : ℝ) ≤ 8*C*√((n : ℝ)/L)
  rw [← hroot]
  have hqr : (Q.card : ℝ) ≤ 2*F.card := by exact_mod_cast hq
  linarith

end H2Part

theorem OMA.solution : type_of% @Erdos912.erdos_912.variants.selfridge :=
  OMA.R_Erdos912_erdos_912_variants_selfridge_R1.main
    OMA.SelfridgePrimeCount.scaled
    (close_prime_pairs Erdos884.prime_pairs_bound)
