import FormalConjectures.ErdosProblems.«420»
import Mathlib

/-!
# The four-ninths factorial window

Split the logarithm of each integer in the interval by prime-factor size.
The two estimates are the small-prime and middle-prime bounds in the proof of
Lemma 3 of Erdős, Graham, Ivić and Pomerance. A large prime factor forces
an explicit gain in the divisor function when this integer enters the factorial.
-/

namespace OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1

open Filter Finset Real
open scoped ArithmeticFunction.sigma Classical

/-- The small primes contribute at most (4/9+o(1)) times the logarithmic mass. -/
def H1 : Prop := ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
  let h := ⌊(n:ℝ)^((4:ℝ)/9)⌋₊
  (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ (n:ℝ)^((4:ℝ)/9)),
    ((n+i+1).factorization p : ℝ)*log p) ≤ (4/9+η)*(h:ℝ)*log n

/-- The exponent-pair estimate saves a fixed amount on intermediate primes. -/
def H2 : Prop := ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
  let h := ⌊(n:ℝ)^((4:ℝ)/9)⌋₊
  (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ =>
    (n:ℝ)^((4:ℝ)/9) < p ∧ (p:ℝ) ≤ (n:ℝ)^((5:ℝ)/9+1/10000)),
    ((n+i+1).factorization p : ℝ)*log p) ≤ (5/9-η)*(h:ℝ)*log n

lemma divisors_mul_prime (a p : ℕ) (ha : a ≠ 0) (hp : p.Prime) :
    σ 0 (p*a) * (a.factorization p + 1) = σ 0 a * (a.factorization p + 2) := by
  let k := a.factorization p
  let b := a / p^k
  have hcop : p.Coprime b := Nat.coprime_ordCompl hp ha
  have hab : p^k*b = a := Nat.ordProj_mul_ordCompl_eq_self a p
  have hnext : p^(k+1)*b = p*a := by rw [← hab]; ring
  have h1 : σ 0 a = (k+1)*σ 0 b := by
    rw [← hab,ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left k),
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  have h2 : σ 0 (p*a) = (k+2)*σ 0 b := by
    rw [← hnext,ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop.pow_left (k+1)),
      ArithmeticFunction.sigma_zero_apply_prime_pow hp]
  rw [h1,h2]
  change _ * (k+1) = _ * (k+2)
  ring

lemma gain (n p : ℕ) (hp : p.Prime) (hd : p ∣ n+1) :
    (σ 0 n.factorial : ℝ) * (1+(p:ℝ)/(4*(n+1:ℝ))) ≤ σ 0 (n+1).factorial := by
  let a := n.factorial.factorization p
  let T := (σ 0 n.factorial : ℝ)
  let U := (σ 0 (p*n.factorial) : ℝ)
  have hpos : 0 < a+1 := by omega
  have hval : a*(p-1) ≤ n := (Nat.le_div_iff_mul_le (by have := hp.two_le; omega)).mp
    (Nat.factorization_factorial_le_div_pred hp n)
  have hpLE := Nat.le_of_dvd (Nat.succ_pos n) hd
  have hp2 := hp.two_le
  have hbound : p*(a+1) ≤ 4*(n+1) := by
    have h := Nat.mul_le_mul_left a (show p ≤ 2*(p-1) by omega)
    nlinarith
  have hboundR : (p:ℝ)*((a:ℝ)+1) ≤ 4*((n:ℝ)+1) := by exact_mod_cast hbound
  have heq : U*((a:ℝ)+1) = T*((a:ℝ)+2) := by
    dsimp [U,T,a]
    exact_mod_cast divisors_mul_prime n.factorial p (Nat.factorial_ne_zero _) hp
  have hr : (p:ℝ)/(4*((n:ℝ)+1)) ≤ 1/((a:ℝ)+1) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by linarith)
  have hU : T*(1+1/((a:ℝ)+1)) = U := by
    field_simp
    nlinarith
  have hmono : σ 0 (p*n.factorial) ≤ σ 0 (n+1).factorial := by
    simp only [ArithmeticFunction.sigma_zero_apply]
    apply card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _) ?_)
    rw [Nat.factorial_succ]
    exact Nat.mul_dvd_mul hd (dvd_refl _)
  calc
    _ ≤ T*(1+1/((a:ℝ)+1)) := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    _ = U := hU
    _ ≤ _ := by dsimp [U]; exact_mod_cast hmono

lemma log_factors (m : ℕ) (hm : 0 < m) :
    log (m:ℝ) = ∑ p ∈ m.primeFactors, (m.factorization p : ℝ)*log p := by
  have h : (m:ℝ) = ∏ p ∈ m.primeFactors, (p:ℝ)^(m.factorization p) := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hm.ne'
  calc
    _ = log (∏ p ∈ m.primeFactors, (p:ℝ)^(m.factorization p)) := congrArg log h
    _ = _ := by rw [Real.log_prod (fun p hp => pow_ne_zero _
        (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero))]; simp only [Real.log_pow]
lemma count_large (n h : ℕ) (hn : 2 ≤ n) (hh : h ≤ n) (A B η : ℝ)
    (hs : (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ A),
      ((n+i+1).factorization p : ℝ)*log p) ≤ (4/9+η/2)*(h:ℝ)*log n)
    (hm : (∑ i ∈ range h, ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => A < (p:ℝ) ∧ (p:ℝ) ≤ B),
      ((n+i+1).factorization p : ℝ)*log p) ≤ (5/9-η)*(h:ℝ)*log n) :
    η*h ≤ 4*((((range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))).card : ℕ):ℝ) := by
  let w (i p : ℕ) := ((n+i+1).factorization p : ℝ)*log p
  let small (i : ℕ) := ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ A), w i p
  let mid (i : ℕ) := ∑ p ∈ (n+i+1).primeFactors.filter (fun p : ℕ => A < (p:ℝ) ∧ (p:ℝ) ≤ B), w i p
  let Hit (i : ℕ) := ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ)
  let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
  change η*h ≤ 4*(G.card:ℝ)
  change (∑ i ∈ range h, small i) ≤ _ at hs
  change (∑ i ∈ range h, mid i) ≤ _ at hm
  have hln : 0 < log (n:ℝ) := log_pos (by exact_mod_cast hn)
  have hw i p (hp : p ∈ (n+i+1).primeFactors) : 0 ≤ w i p := by
    apply mul_nonneg (Nat.cast_nonneg _) (log_nonneg _)
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
  have each i (hi : i ∈ range h) :
      log (n:ℝ) ≤ small i + mid i + (if Hit i then 2*log n else 0) := by
    have hm0 : 0 < n+i+1 := by omega
    by_cases he : Hit i
    · simp only [if_pos he]
      have hp1 : 0 ≤ small i := sum_nonneg (fun p hp => hw _ _ (mem_filter.mp hp).1)
      have hp2 : 0 ≤ mid i := sum_nonneg (fun p hp => hw _ _ (mem_filter.mp hp).1)
      linarith
    · simp only [if_neg he,add_zero]
      calc
        _ ≤ log ((n+i+1 : ℕ):ℝ) := log_le_log (by positivity) (by exact_mod_cast (show n ≤ n+i+1 by omega))
        _ = ∑ p ∈ (n+i+1).primeFactors, w i p := log_factors _ hm0
        _ = small i + mid i := by
          rw [← sum_filter_add_sum_filter_not (n+i+1).primeFactors (fun p => (p:ℝ) ≤ A)]
          dsimp only [small,mid]
          congr 1
          apply sum_congr _ (fun _ _ => rfl)
          ext p
          simp only [mem_filter, not_le]
          exact ⟨fun h => ⟨h.1,h.2,le_of_not_gt (fun h' => he ⟨p,h.1,h'⟩)⟩,
            fun h => ⟨h.1,h.2.1⟩⟩
  have hsum := sum_le_sum each
  have hconst : (∑ i ∈ range h, if Hit i then 2*log n else 0) = (G.card:ℝ)*(2*log n) := by
    rw [← Finset.sum_filter]; simp [G,Hit]
  simp only [sum_const,card_range,nsmul_eq_mul,sum_add_distrib,hconst] at hsum
  exact le_of_mul_le_mul_right (by nlinarith : (η*h)*log n ≤ (4*(G.card:ℝ))*log n) hln

lemma gain_window (n h : ℕ) (hn : 1 ≤ n) (hh : h ≤ n) (B : ℝ) (hB : 0 ≤ B) :
    let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
    (σ 0 n.factorial:ℝ)*(1+(G.card:ℝ)*(B/(8*n))) ≤ σ 0 (n+h).factorial := by
  let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
  have memG {i : ℕ} : i ∈ G ↔ i ∈ range h ∧ ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ) := by simp [G]
  let T (i : ℕ) := (σ 0 (n+i).factorial : ℝ)
  let u := B/(8*n)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hT : Monotone T := by
    intro a b hab
    dsimp [T]
    exact_mod_cast (show σ 0 (n+a).factorial ≤ σ 0 (n+b).factorial by
      simp only [ArithmeticFunction.sigma_zero_apply]
      exact card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _)
        (Nat.factorial_dvd_factorial (by omega))))
  have hinc (i : ℕ) (hi : i ∈ range h) :
      (if i ∈ G then T 0 * u else 0) ≤ T (i+1) - T i := by
    by_cases h : i ∈ G
    · simp only [if_pos h]
      obtain ⟨p,hp,hpB⟩ := (memG.mp h).2
      have hr := mem_range.mp hi
      have hnum : (n:ℝ)+i+1 ≤ 2*n := by exact_mod_cast (show n+i+1 ≤ 2*n by omega)
      have hstep := gain (n+i) p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
      push_cast at hstep
      have hfrac : u ≤ (p:ℝ)/(4*((n:ℝ)+i+1)) := by
        dsimp [u]
        exact div_le_div₀ (by positivity) hpB.le (by positivity) (by linarith)
      have h := (mul_le_mul_of_nonneg_left (add_le_add_right hfrac 1) (show 0 ≤ T i from Nat.cast_nonneg _))
      change T i * (1+(p:ℝ)/(4*((n:ℝ)+i+1))) ≤ T (i+1) at hstep
      have h0 := mul_le_mul_of_nonneg_right (hT (Nat.zero_le i)) hu
      linarith
    · simp only [if_neg h]
      exact sub_nonneg.mpr (hT (by omega))
  have ht := sum_le_sum hinc
  have hsub : ((range h).filter (· ∈ G)) = G := by
    ext i
    exact ⟨fun hi => (mem_filter.mp hi).2, fun hi => mem_filter.mpr ⟨(memG.mp hi).1,hi⟩⟩
  rw [← Finset.sum_filter, hsub, sum_const, nsmul_eq_mul, sum_range_sub] at ht
  change T 0*(1+(G.card:ℝ)*u) ≤ T h
  linarith
theorem main : H1 → H2 → type_of% @Erdos420.erdos_420.variants.pow_four_ninths := by
  intro hsmall hmiddle
  obtain ⟨η,hη,hmiddle⟩ := hmiddle
  have growth (r : ℝ) (hr : 0 < r) : Tendsto (fun n : ℕ => (n:ℝ)^r) atTop atTop :=
    (tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
  filter_upwards [hsmall (η/2) (by positivity),hmiddle,eventually_ge_atTop (2:ℕ),
      (growth (4/9) (by norm_num)).eventually_ge_atTop 2,
      (growth (1/10000) (by norm_num)).eventually_ge_atTop (64/η)]
    with n hs hm hn hpow hbig
  let A := (n:ℝ)^((4:ℝ)/9)
  let B := (n:ℝ)^((5:ℝ)/9+1/10000)
  let h := ⌊A⌋₊
  let G := (range h).filter (fun i => ∃ p ∈ (n+i+1).primeFactors, B < (p:ℝ))
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 2 ≤ A := hpow
  have hfloor : A < (h:ℝ)+1 := Nat.lt_floor_add_one _
  have hh : h ≤ n := by
    have hA' : A ≤ (n:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rw [Real.rpow_one] at hA'
    exact_mod_cast (Nat.floor_le (show 0 ≤ A by linarith)).trans hA'
  have hc : η*h ≤ 4*(G.card:ℝ) := count_large n h hn hh A B η hs hm
  have hsave : η*A ≤ 8*(G.card:ℝ) := by
    have he : A ≤ 2*(h:ℝ) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left he hη.le]
  have hAB : A*B = (n:ℝ)*(n:ℝ)^((1:ℝ)/10000) := by
    dsimp [A,B]
    rw [← Real.rpow_add hnR,show (4:ℝ)/9 + (5/9+1/10000) = 1+1/10000 by ring,
      Real.rpow_add hnR, Real.rpow_one]
  have hηb : 64 ≤ η*(n:ℝ)^((1:ℝ)/10000) := by
    have h' := (div_le_iff₀ hη).mp hbig
    linarith
  have htotal : 8*(n:ℝ) ≤ (G.card:ℝ)*B := by
    have h' := mul_le_mul_of_nonneg_right hsave hB.le
    rw [mul_assoc η A B,hAB] at h'
    nlinarith [mul_le_mul_of_nonneg_left hηb hnR.le]
  have hgain := gain_window n h (by omega) hh B hB.le
  change (σ 0 n.factorial:ℝ)*(1+(G.card:ℝ)*(B/(8*n))) ≤ σ 0 (n+h).factorial at hgain
  have hhg : 1 ≤ (G.card:ℝ)*(B/(8*n)) := by
    rw [← mul_div_assoc]
    exact (one_le_div (by positivity)).mpr htotal
  have ht : (0:ℝ) < σ 0 n.factorial := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)
  change 2 ≤ (σ 0 (n+h).factorial:ℝ)/(σ 0 n.factorial:ℝ)
  apply (le_div_iff₀ ht).mpr
  exact (by nlinarith [mul_le_mul_of_nonneg_left (by linarith : (2:ℝ) ≤ 1+(G.card:ℝ)*(B/(8*n))) ht.le] :
    2 * (σ 0 n.factorial:ℝ) ≤ (σ 0 n.factorial:ℝ)*(1+(G.card:ℝ)*(B/(8*n)))).trans hgain

end OMA.R_Erdos420_erdos_420_variants_pow_four_ninths_R1
