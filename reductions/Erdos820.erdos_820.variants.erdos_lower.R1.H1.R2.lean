import OMAReductions.R_Erdos820_erdos_820_variants_erdos_lower_R1
import Mathlib

/-!
A finite form of Prachar's averaging argument. Each prime p ≤ x gives
gcd(k,p-1) explicit positive multipliers t ≤ x such that p-1 divides k*t.
Summing first over the primes and then over the multipliers gives a single
integer containing many shifted primes. The divisor-totient expansion
expresses the remaining analytic input entirely through counts of primes
in arithmetic progressions. Compared with the dyadic cofactor argument in
R1, the totient weight treats all moduli together. See Fan and Pollack,
arXiv:2510.14167, §2, and Alford, Granville and Pomerance, (1.3).
-/
namespace OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R2

open Finset Filter

/-- The exponent 1/10 case of Alford, Granville and Pomerance, (1.3),
with a = 1 and y = x. Choose one prime factor of each exceptional modulus. -/
def H1 : Prop := ∃ B : ℕ, ∀ᶠ x : ℕ in atTop, ∃ E : Finset ℕ,
  E.card ≤ B ∧ (∀ p ∈ E, Nat.Prime p) ∧ ∀ d : ℕ, 0 < d → d^10 ≤ x →
    (∀ p ∈ E, ¬p ∣ d) →
    (Nat.primesLE x).card ≤ 2 * d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card

/-- Finite averaging with a positive multiplier at most x. -/
def H2 : Prop := ∀ k x : ℕ, 0 < k → 0 < x → ∃ t ∈ Icc 1 x,
  (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card) ≤
    x * ((range (k*t+2)).filter (fun p => p.Prime ∧ p-1 ∣ k*t)).card

theorem weight_eq (k x : ℕ) (hk : 0 < k) :
    (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card) =
      ∑ p ∈ Nat.primesLE x, k.gcd (p-1) := by
  classical
  calc
    _ = ∑ d ∈ k.divisors, ∑ p ∈ Nat.primesLE x, if d ∣ p-1 then d.totient else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter]
      simp [Nat.mul_comm]
    _ = ∑ p ∈ Nat.primesLE x, ∑ d ∈ k.divisors, if d ∣ p-1 then d.totient else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      rw [← sum_filter, ← Nat.sum_totient (k.gcd (p-1))]
      congr 1
      ext d
      simp [Nat.mem_divisors, hk.ne', (Nat.gcd_pos_of_pos_left (p-1) hk).ne', Nat.dvd_gcd_iff]

theorem manyMultipliers (k x p : ℕ) (hp : p ∈ Nat.primesLE x) :
    k.gcd (p-1) ≤ ((Icc 1 x).filter (fun t => p-1 ∣ k*t)).card := by
  obtain ⟨px, prime⟩ := mem_filter.mp hp
  have ple : p ≤ x := by simpa only [mem_range, Nat.lt_succ_iff] using px
  have pmpos : 0 < p-1 := by have := prime.two_le; omega
  let g := k.gcd (p-1)
  let q := (p-1)/g
  have divide : g ∣ p-1 := Nat.gcd_dvd_right ..
  have level : q*g = p-1 := Nat.div_mul_cancel divide
  have qpos : 0 < q := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at level; omega
  have gk : g ∣ k := Nat.gcd_dvd_left ..
  have incl : ∀ i ∈ Icc 1 g, q*i ∈ (Icc 1 x).filter (fun t => p-1 ∣ k*t) := by
    intro i hi
    obtain ⟨hi1,hig⟩ := mem_Icc.mp hi
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by exact Nat.mul_pos qpos hi1, ?_⟩, ?_⟩
    · have h := Nat.mul_le_mul_left q hig
      omega
    · obtain ⟨u,hu⟩ := gk
      refine ⟨u*i, ?_⟩
      rw [hu, ← level]
      ring
  have card := card_le_card_of_injOn (fun i : ℕ => q*i) incl
    (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left qpos h)
  simpa [Nat.card_Icc, g] using card

theorem finiteAverage : H2 := by
  let weight (k x : ℕ) := (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card)
  let shifted (n : ℕ) := (range (n+2)).filter (fun p => p.Prime ∧ p-1 ∣ n)
  classical
  intro k x hk hx
  let T := Icc 1 x
  have ne : T.Nonempty := ⟨1,mem_Icc.mpr ⟨le_rfl,hx⟩⟩
  obtain ⟨t,ht,hmax⟩ := T.exists_max_image (fun u => (shifted (k*u)).card) ne
  refine ⟨t,ht,?_⟩
  calc
    weight k x = ∑ p ∈ Nat.primesLE x, k.gcd (p-1) := weight_eq k x hk
    _ ≤ ∑ p ∈ Nat.primesLE x, (T.filter (fun u => p-1 ∣ k*u)).card :=
      sum_le_sum (fun p hp => manyMultipliers k x p hp)
    _ = ∑ u ∈ T, ((Nat.primesLE x).filter (fun p => p-1 ∣ k*u)).card := by
      have count {s : Finset ℕ} (f : ℕ → Prop) [DecidablePred f] :
          (s.filter f).card = ∑ i ∈ s, if f i then 1 else 0 := by
        simp
      simp_rw [count]
      rw [sum_comm]
    _ ≤ ∑ u ∈ T, (shifted (k*t)).card := by
      apply sum_le_sum
      intro u hu
      apply le_trans _ (hmax u hu)
      apply card_le_card
      intro p hp
      obtain ⟨hp,div⟩ := mem_filter.mp hp
      have prime := (mem_filter.mp hp).2
      have ku : 0 < k*u := Nat.mul_pos hk (mem_Icc.mp hu).1
      have small := Nat.le_of_dvd ku div
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),prime,div⟩
    _ = x * (shifted (k*t)).card := by simp [T, Nat.card_Icc]

theorem ofMass : (∃ c : ℝ, 0 < c ∧ ∃ᶠ k : ℕ in atTop, ∃ x : ℕ,
    0 < x ∧ (x : ℝ) * ((k*x : ℕ) : ℝ) ^ (c / Real.log (Real.log (k : ℝ)) ^ 2) ≤
      (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card)) → H2 → OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1.H1 := by
  let weight (k x : ℕ) := (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card)
  let shifted (n : ℕ) := (range (n+2)).filter (fun p => p.Prime ∧ p-1 ∣ n)
  rintro ⟨c,hc,hmass⟩ havg
  refine ⟨c,hc,frequently_atTop.mpr ?_⟩
  intro N
  obtain ⟨k,hlarge,x,hx,hm⟩ := frequently_atTop.mp hmass (max N 16)
  have k16 : 16 ≤ k := le_trans (le_max_right ..) hlarge
  obtain ⟨t,ht,hcount⟩ := havg k x (by omega) hx
  obtain ⟨ht1,htx⟩ := mem_Icc.mp ht
  have kl : k ≤ k*t := by simpa using Nat.mul_le_mul_left k ht1
  have ku : k*t ≤ k*x := Nat.mul_le_mul_left k htx
  refine ⟨k*t,le_trans (le_trans (le_max_left ..) hlarge) kl,?_⟩
  have kr : (16 : ℝ) ≤ k := by exact_mod_cast k16
  have lr : (k : ℝ) ≤ ((k*t : ℕ) : ℝ) := by exact_mod_cast kl
  have ur : ((k*t : ℕ) : ℝ) ≤ ((k*x : ℕ) : ℝ) := by exact_mod_cast ku
  have lk : 1 < Real.log (k : ℝ) := (Real.lt_log_iff_exp_lt (by linarith)).mpr
    (lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 16)) kr)
  have pos := Real.log_pos lk
  have mono := Real.log_le_log (by linarith : (0 : ℝ) < Real.log (k : ℝ))
    (Real.log_le_log (by linarith) lr)
  have frac : c / Real.log (Real.log ((k*t : ℕ) : ℝ)) ^ 2 ≤ c / Real.log (Real.log (k : ℝ)) ^ 2 :=
    div_le_div_of_nonneg_left hc.le (sq_pos_of_pos pos) (by nlinarith [sq_nonneg (Real.log (Real.log ((k*t : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)))])
  have hcr : (weight k x : ℝ) ≤ (x : ℝ) * (shifted (k*t)).card := by exact_mod_cast hcount
  change ((k*t : ℕ) : ℝ) ^ _ ≤ ((shifted (k*t)).card : ℝ)
  calc
    _ ≤ ((k*t : ℕ) : ℝ) ^ (c / Real.log (Real.log (k : ℝ)) ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) frac
    _ ≤ ((k*x : ℕ) : ℝ) ^ (c / Real.log (Real.log (k : ℝ)) ^ 2) :=
      Real.rpow_le_rpow (by positivity) ur (div_nonneg hc.le (sq_nonneg _))
    _ ≤ _ := (le_of_mul_le_mul_left (hm.trans hcr) (by exact_mod_cast hx : (0 : ℝ) < x))

/-- Removing at most B primes leaves all subset products of the others
available as distinct progression moduli. -/
theorem subsetWeight {y k x B : ℕ} (hk : 0 < k) (divides : primorial y ∣ k)
    (limit : k^10 ≤ x) {E : Finset ℕ} (eb : E.card ≤ B)
    (ep : ∀ p ∈ E, Nat.Prime p)
    (ap : ∀ d : ℕ, 0 < d → d^10 ≤ x → (∀ p ∈ E, ¬p ∣ d) →
      (Nat.primesLE x).card ≤ 2 * d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card) :
    2^((Nat.primesLE y).card-B) * (Nat.primesLE x).card ≤
      2 * (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card) := by
  let weight (k x : ℕ) := (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card)
  classical
  let P := Nat.primesLE y \ E
  let f := fun S : Finset ℕ => ∏ p ∈ S, p
  let D := P.powerset.image f
  have primes {S : Finset ℕ} (hS : S ∈ P.powerset) :
      ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    exact (mem_filter.mp (mem_sdiff.mp (mem_powerset.mp hS hp)).1).2
  have identity {S : Finset ℕ} (hS : S ∈ P.powerset) :
      (f S).primeFactors = S := Nat.primeFactors_prod (primes hS)
  have inj : (P.powerset : Set (Finset ℕ)).InjOn f := by
    intro A hA C hC eqn
    rw [← identity hA, ← identity hC, eqn]
  have dc : D.card = 2^P.card := by
    rw [show D = P.powerset.image f from rfl,card_image_of_injOn inj,card_powerset]
  have cP : (Nat.primesLE y).card-B ≤ P.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := Nat.primesLE y) (t := E)
    dsimp [P]; omega
  have ds : D ⊆ k.divisors := by
    intro d hd
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
    have incl : S ⊆ Nat.primesLE y := (mem_powerset.mp hS).trans sdiff_subset
    exact Nat.mem_divisors.mpr ⟨(Finset.prod_dvd_prod_of_subset S (Nat.primesLE y) (fun p => p) incl).trans divides,hk.ne'⟩
  have each (d : ℕ) (hd : d ∈ D) :
      (Nat.primesLE x).card ≤ 2 * d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card := by
    obtain ⟨dv,_⟩ := Nat.mem_divisors.mp (ds hd)
    apply ap d (Nat.pos_of_dvd_of_pos dv hk) ((Nat.pow_le_pow_left (Nat.le_of_dvd hk dv) _).trans limit)
    intro p hp pd
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hd
    have hmem : p ∈ (f S).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨ep p hp,pd,(Nat.pos_of_dvd_of_pos dv hk).ne'⟩
    rw [identity hS] at hmem
    exact (mem_sdiff.mp (mem_powerset.mp hS hmem)).2 hp
  calc
    _ ≤ 2^P.card * (Nat.primesLE x).card := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) cP)
    _ = ∑ _d ∈ D, (Nat.primesLE x).card := by simp [dc]
    _ ≤ ∑ d ∈ D, 2 * (d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card) :=
      sum_le_sum fun d hd => by simpa only [Nat.mul_assoc] using each d hd
    _ ≤ ∑ d ∈ k.divisors, 2 * (d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card) :=
      Finset.sum_le_sum_of_subset ds
    _ = 2 * weight k x := by simp only [weight,Finset.mul_sum]

theorem cube_le_two_pow (m : ℕ) (h : 10 ≤ m) : m^3 ≤ 2^m := by
  induction m, h using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have a := Nat.mul_le_mul_right (m^2) (by omega : 5 ≤ m)
    have b := Nat.mul_le_mul_right m (by omega : 5 ≤ m)
    have step : (m+1)^3 ≤ 2*m^3 := by nlinarith only [a,b,hm]
    rw [pow_succ 2]; omega

/-- Chebyshev's explicit estimate at a power of two. -/
theorem dyadicPrimeCount (m : ℕ) (hm : 10 ≤ m) :
    2^m ≤ 2 * (Nat.primesLE (2^m)).card * m := by
  let y := 2^m
  have big : 1 < y := one_lt_pow₀ (by decide) (by omega)
  have hy : (1:ℝ) < y := by exact_mod_cast big
  have atY := (div_le_iff₀ (Real.log_pos hy)).mp (Chebyshev.pi_ge y)
  have logY : Real.log (y:ℝ) = (m:ℝ)*Real.log 2 := by simp [y,Real.log_pow]
  have up : Real.log ((y:ℝ)+1) ≤ ((m:ℝ)+1)*Real.log 2 := calc
    _ ≤ Real.log ((2:ℝ)^(m+1)) := by
      apply Real.log_le_log (by positivity)
      rw [pow_succ]
      have eqy : (y:ℝ)=(2:ℝ)^m := by simp [y]
      linarith [hy,eqy]
    _ = _ := by rw [Real.log_pow]; push_cast; rfl
  rw [logY] at atY
  have hr : (y:ℝ) ≤ (y.primeCounting:ℝ)*m+(m+1) := by
    apply le_of_mul_le_mul_right _ (Real.log_pos (by norm_num : (1:ℝ)<2))
    nlinarith only [atY,up]
  have hn : y ≤ y.primeCounting*m+(m+1) := by exact_mod_cast hr
  have cube := cube_le_two_pow m hm
  have tiny : 2*(m+1) ≤ m^3 := by nlinarith [sq_nonneg (m:ℤ), Nat.mul_le_mul_right (m^2) hm]
  change y ≤ 2 * (Nat.primesLE y).card * m
  rw [Nat.primesLE_card_eq_primeCounting]
  change m^3 ≤ y at cube
  rw [Nat.mul_assoc]
  omega

/-- A set of exceptional integer moduli can be replaced by at most as
many exceptional primes by selecting a prime factor of each modulus. -/
theorem ofExceptionalModuli (h : ∃ B : ℕ, ∀ᶠ x : ℕ in atTop, ∃ F : Finset ℕ,
    F.card ≤ B ∧ (∀ e ∈ F, 2 ≤ e) ∧ ∀ d : ℕ, 0 < d → d^10 ≤ x →
    (∀ e ∈ F, ¬e ∣ d) →
    (Nat.primesLE x).card ≤ 2 * d.totient * ((Nat.primesLE x).filter (fun p => Nat.ModEq d 1 p)).card) : H1 := by
  obtain ⟨B,hB⟩ := h
  refine ⟨B,hB.mono ?_⟩
  rintro x ⟨F,fb,large,estimate⟩
  refine ⟨F.image Nat.minFac,card_image_le.trans fb,?_,?_⟩
  · intro p hp
    obtain ⟨e,he,rfl⟩ := mem_image.mp hp
    exact Nat.minFac_prime (by have := large e he; omega)
  · intro d hd cutoff good
    have eqFilter : (Nat.primesLE x).filter (fun p => Nat.ModEq d 1 p) =
        (Nat.primesLE x).filter (fun p => d ∣ p-1) := by
      apply filter_congr
      intro p hp
      exact Nat.modEq_iff_dvd' (Nat.prime_of_mem_primesLE hp).one_le
    rw [← eqFilter]
    apply estimate d hd cutoff
    intro e he bad
    exact good e.minFac (mem_image_of_mem _ he) ((Nat.minFac_dvd e).trans bad)

theorem dyadicCounting {B m y h x P Q W r : ℕ}
    (hm : 100 ≤ m) (Bm : B+100 ≤ m) (hr : r=P/2) (hy : y=2^m) (hh : h=40*y)
    (py : y ≤ 2*P*m) (px : x ≤ 2*Q*h) (cube : m^3 ≤ y) (mass : 2^(P-B)*Q ≤ 2*W) :
    y ≤ 6*m*r ∧ x*2^r ≤ W := by
  have many : 10*m ≤ P := by
    by_contra! small
    have psmall := Nat.mul_le_mul_right m (by omega : 2*P ≤ 20*m)
    have mbig := Nat.mul_le_mul_right (m^2) hm
    nlinarith only [psmall,mbig,py,cube,hm]
  have rpos : 1 ≤ r := by rw [hr]; omega
  have pr : P ≤ 3*r := by rw [hr]; omega
  have reserved : m+8+r ≤ P-B := by rw [hr]; omega
  have yr : y ≤ 6*m*r := by
    have u := Nat.mul_le_mul_right m pr
    nlinarith only [u,py]
  have overhead : 4*h ≤ 2^(m+8) := by
    rw [pow_add]
    rw [hh,hy]
    omega
  have budget : 4*h*2^r ≤ 2^(P-B) := calc
    _ ≤ 2^(m+8)*2^r := Nat.mul_le_mul_right _ overhead
    _ = 2^(m+8+r) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) reserved
  have integerBound : x*2^r ≤ W := by
    have a := Nat.mul_le_mul_right (2^r) px
    have b := Nat.mul_le_mul_right Q budget
    nlinarith only [a,b,mass]
  exact ⟨yr,integerBound⟩

theorem dyadicScale {m y k x r : ℕ} (hm : 100 ≤ m) (hy : y=2^m) (y0 : 0 < y)
    (k0 : 0 < k) (x0 : 0 < x) (yr : y ≤ 6*m*r) (lower : 2^(2*y) ≤ k)
    (endpt : k*x ≤ 2^(44*y)) :
    ((k*x : ℕ):ℝ) ^ ((1/1000:ℝ)/Real.log (Real.log (k:ℝ))^2) ≤ (2:ℝ)^r := by
  have lr : (1/2:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have mR : (100:ℝ) ≤ m := by exact_mod_cast hm
  have yR : (y:ℝ) ≤ 6*(m:ℝ)*r := by exact_mod_cast yr
  have logY : Real.log (y:ℝ) = m*Real.log 2 := by rw [hy]; simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have lowR : (2:ℝ)^(2*y) ≤ k := by exact_mod_cast lower
  have logK := Real.log_le_log (by positivity) lowR
  rw [Real.log_pow] at logK
  push_cast at logK
  have yK : (y:ℝ) ≤ Real.log (k:ℝ) := by
    nlinarith only [logK,mul_nonneg (by positivity : (0:ℝ) ≤ y) (by linarith : 0 ≤ Real.log 2 - 1/2)]
  have ll := Real.log_le_log (by exact_mod_cast y0) yK
  rw [logY] at ll
  have half : (m:ℝ)/2 ≤ Real.log (Real.log (k:ℝ)) := by
    linarith only [ll,mul_le_mul_of_nonneg_left lr.le (by positivity : (0:ℝ) ≤ m)]
  have denom : (m:ℝ) ≤ Real.log (Real.log (k:ℝ))^2 := calc
    _ ≤ ((m:ℝ)/2)^2 := by nlinarith only [mR,mul_nonneg (by positivity : (0:ℝ) ≤ m) (by linarith : 0 ≤ (m:ℝ)-4)]
    _ ≤ _ := by gcongr
  have endR : ((k*x : ℕ):ℝ) ≤ (2:ℝ)^(44*y) := by exact_mod_cast endpt
  have leLog := Real.log_le_log (by exact_mod_cast Nat.mul_pos k0 x0) endR
  rw [Real.log_pow] at leLog
  push_cast at leLog
  have scale : ((k*x : ℕ):ℝ) ^ ((1/1000:ℝ)/Real.log (Real.log (k:ℝ))^2) ≤ (2:ℝ)^r := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast Nat.mul_pos k0 x0),
      ← Real.exp_log (show (0:ℝ)<2^r by positivity),Real.exp_le_exp,Real.log_pow,
      ← mul_div_assoc,div_le_iff₀ (by linarith : 0 < Real.log (Real.log (k:ℝ))^2)]
    have numer := mul_le_mul_of_nonneg_right yR (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))
    have term := mul_le_mul_of_nonneg_left denom (mul_nonneg (Nat.cast_nonneg r) (by linarith : 0 ≤ Real.log 2))
    push_cast
    nlinarith only [leLog,numer,term, mul_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)*r) (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))]
  exact scale

set_option maxHeartbeats 400000 in
/-- A padded primorial gives both a lower bound for log log k and
exponentially many squarefree moduli dividing k. -/
theorem distributionGivesMass : H1 → (∃ c : ℝ, 0 < c ∧ ∃ᶠ k : ℕ in atTop, ∃ x : ℕ,
    0 < x ∧ (x : ℝ) * ((k*x : ℕ) : ℝ) ^ (c / Real.log (Real.log (k : ℝ)) ^ 2) ≤
      (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card)) := by
  let weight (k x : ℕ) := (∑ d ∈ k.divisors, d.totient * ((Nat.primesLE x).filter (fun p => d ∣ p-1)).card)
  rintro ⟨B,dist⟩
  obtain ⟨X,hX⟩ := eventually_atTop.mp dist
  refine ⟨1/1000,by norm_num,frequently_atTop.mpr ?_⟩
  intro N
  let m := N+X+B+100
  let y := 2^m
  let k := 4^y * primorial y
  let h := 40*y
  let x := 2^h
  let P := (Nat.primesLE y).card
  let r := P/2
  have hm : 100 ≤ m := by dsimp [m]; omega
  have Bm : B+100 ≤ m := by dsimp [m]; omega
  have my : m ≤ y := (Nat.lt_two_pow_self (n := m)).le
  have y0 : 0 < y := pow_pos (by decide) _
  have x0 : 0 < x := pow_pos (by decide) _
  have k0 : 0 < k := Nat.mul_pos (pow_pos (by decide) _) (primorial_pos _)
  have h10 : 10 ≤ h := by dsimp [h]; omega
  have lower : 2^(2*y) ≤ k := by
    rw [pow_mul]
    change 4^y ≤ 4^y * primorial y
    simpa using Nat.mul_le_mul_left (4^y) (primorial_pos y)
  have upper : k ≤ 2^(4*y) := calc
    _ ≤ 4^y*4^y := Nat.mul_le_mul_left _ (primorial_le_four_pow y)
    _ = 2^(4*y) := by rw [← mul_pow, pow_mul]; rfl
  have kN : N ≤ k := by
    have a := Nat.lt_two_pow_self (n := 2*y)
    have Nm : N ≤ m := by dsimp [m]; omega
    omega
  have Xx : X ≤ x := by
    have xm : X ≤ m := by dsimp [m]; omega
    have a := Nat.lt_two_pow_self (n := h)
    have yh : y ≤ h := by dsimp [h]; omega
    change X ≤ 2^h
    omega
  have lim : k^10 ≤ x := calc
    _ ≤ (2^(4*y))^10 := Nat.pow_le_pow_left upper _
    _ = 2^(4*y*10) := (pow_mul ..).symm
    _ = x := congrArg (fun a : ℕ => 2^a) (show 4*y*10=40*y by ring)
  have endpt : k*x ≤ 2^(44*y) := calc
    _ ≤ 2^(4*y)*2^h := Nat.mul_le_mul_right x upper
    _ = 2^(4*y+h) := (pow_add ..).symm
    _ = _ := congrArg (fun a : ℕ => 2^a) (show 4*y+40*y=44*y by ring)
  obtain ⟨E,eb,ep,uniformAP⟩ := hX x Xx
  have mass := subsetWeight k0 (show primorial y ∣ k from dvd_mul_left _ _) lim eb ep uniformAP
  have py : y ≤ 2 * P * m := dyadicPrimeCount m (by omega)
  have px : x ≤ 2 * (Nat.primesLE x).card * h := dyadicPrimeCount h h10
  have cube : m^3 ≤ y := cube_le_two_pow m (by omega)
  obtain ⟨yr,integerBound⟩ := dyadicCounting hm Bm (rfl : r=P/2) (rfl : y=2^m) (rfl : h=40*y) py px cube mass
  refine ⟨k,kN,x,x0,?_⟩
  have scale := dyadicScale hm rfl y0 k0 x0 yr lower endpt
  calc
    _ ≤ (x:ℝ)*(2:ℝ)^r := mul_le_mul_of_nonneg_left scale (by positivity)
    _ ≤ _ := by exact_mod_cast integerBound

theorem main : H1 → H2 → OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1.H1 :=
  fun distribution averaging => ofMass (distributionGivesMass distribution) averaging

end OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1_H1_R2
