import FormalConjectures.ErdosProblems.«971»
import Mathlib

/-! # Primes in residue classes and consecutive prime gaps (Erdős Problem 971) -/

namespace OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1

open Finset Filter Real Erdos971
open scoped Topology Classical

/-- A positive density of ordered prime pairs in the same coprime class,
for infinitely many moduli with bounded ratio d / phi(d). -/
def H1 : Prop :=
  let residues := fun (d : ℕ) => (range d).filter fun a => a.Coprime d
  let hits := fun (d : ℕ) (y : ℝ) (a : ℕ) =>
    ((Nat.primesLE ⌊y⌋₊).filter fun p => p % d = a).card
  let scale := fun (d : ℕ) => d.totient * log d
  ∃ M > (0:ℝ), ∃ δ > (0:ℝ), ∃ᶠ d : ℕ in atTop,
    (d:ℝ)  ≤  M*d.totient ∧ δ*d.totient  ≤ 
      ((∑ a ∈ residues d, hits d (scale d) a * (hits d (scale d) a-1) : ℕ):ℝ)

/-- The third moment of the counts in coprime classes at phi(d) log d. -/
def H2 : Prop :=
  let residues := fun (d : ℕ) => (range d).filter fun a => a.Coprime d
  let hits := fun (d : ℕ) (y : ℝ) (a : ℕ) =>
    ((Nat.primesLE ⌊y⌋₊).filter fun p => p % d = a).card
  let scale := fun (d : ℕ) => d.totient * log d
  ∀ M > (0:ℝ), ∃ V > (0:ℝ), ∀ᶠ d : ℕ in atTop,
    (d:ℝ)  ≤  M*d.totient →
      ((∑ a ∈ residues d, hits d (scale d) a ^ 3 : ℕ):ℝ)  ≤  V*d.totient

/-- Upper half of the prime number theorem at real cutoffs. -/
def H3 : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
  (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (1+ε)*(x/log x)

private lemma clip (K n : ℕ) : n*(n-1)*K  ≤  K^2*(n-1)+n^3 := by
  by_cases h : n ≤ K
  · have hh := Nat.mul_le_mul_right ((n-1)*K) h
    nlinarith only [hh, Nat.zero_le (n^3)]
  · have hh := Nat.mul_le_mul (Nat.sub_le n 1) (by omega : K ≤ n)
    nlinarith only [Nat.mul_le_mul_left n hh, Nat.zero_le (K^2*(n-1))]

theorem main : H1 → H2 → H3 → type_of% @Erdos971.erdos_971.variants.infinite_sequence := by
  rintro ⟨M,hM,δ,hδ,hpair⟩ hthird hprimeNumber
  let residues := fun (d : ℕ) => (range d).filter fun a => a.Coprime d
  let hits := fun (d : ℕ) (y : ℝ) (a : ℕ) =>
    ((Nat.primesLE ⌊y⌋₊).filter fun p => p % d = a).card
  let scale := fun (d : ℕ) => d.totient * log d
  let extra := fun (d : ℕ) (y : ℝ) => ∑ a ∈ residues d, (hits d y a-1)
  have clip_sum (d K : ℕ) (y : ℝ) :
      (∑ a ∈ residues d, hits d y a * (hits d y a-1))*K  ≤ 
      K^2*extra d y + ∑ a ∈ residues d, hits d y a^3 := by
    simpa only [extra, sum_mul, mul_sum, sum_add_distrib] using
      sum_le_sum (s:=residues d) (fun a _ => clip K (hits d y a))

  have total (d : ℕ) (y : ℝ) :
      ∑ a ∈ residues d, hits d y a  ≤  Nat.primeCounting ⌊y⌋₊ := by
    dsimp only [hits]
    rw [sum_card_fiberwise_eq_card_filter, ← Nat.primesLE_card_eq_primeCounting]
    exact card_filter_le ..

  have missing (d : ℕ) (hd : 0<d) (y : ℝ) :
      d.totient + extra d y  ≤ 
        ((range d).filter fun a => a.Coprime d ∧ (leastCongruentPrime a d : ℝ)>y).card +
        Nat.primeCounting ⌊y⌋₊ := by
    let miss := (residues d).filter fun a => hits d y a = 0
    have hs : miss ⊆ (range d).filter (fun a => a.Coprime d ∧ (leastCongruentPrime a d : ℝ)>y) := by
      intro a ha
      obtain ⟨ha,hz⟩ := mem_filter.mp ha
      obtain ⟨ha,hc⟩ := mem_filter.mp ha
      refine mem_filter.mpr ⟨ha,hc,?_⟩
      by_contra! h
      obtain ⟨p,_,hp,he⟩ := Nat.forall_exists_prime_gt_and_modEq 0 hd.ne' hc
      have hmem := Nat.sInf_mem (show Set.Nonempty {p : ℕ | p.Prime ∧ p ≡ a [MOD d]} from ⟨p,hp,he⟩)
      change (leastCongruentPrime a d).Prime ∧ leastCongruentPrime a d ≡ a [MOD d] at hmem
      have hmod := hmem.2
      change leastCongruentPrime a d % d = a%d at hmod
      rw [Nat.mod_eq_of_lt (mem_range.mp ha)] at hmod
      have hpos : 0<hits d y a := card_pos.mpr ⟨_,mem_filter.mpr
        ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor h,hmem.1⟩,hmod⟩⟩
      omega
    have he : d.totient = (residues d).card := by simp [Nat.totient_eq_card_coprime,residues,Nat.coprime_comm]
    have hsum : (residues d).card + extra d y = miss.card + ∑ a ∈ residues d, hits d y a := by
      dsimp only [extra]
      rw [card_eq_sum_ones (residues d), ←sum_add_distrib]
      change _ = ((residues d).filter _).card + _
      rw [card_filter, ←sum_add_distrib]
      apply sum_congr rfl
      intro a _
      split_ifs <;> omega
    rw [he,hsum]
    exact Nat.add_le_add (card_le_card hs) (total ..)

  have extra_mono (d : ℕ) {x y : ℝ} (h : x ≤ y) : extra d x  ≤  extra d y := by
    apply sum_le_sum
    intro a _
    apply Nat.sub_le_sub_right
    apply card_le_card
    intro p hp
    obtain ⟨hm,he⟩ := mem_filter.mp hp
    obtain ⟨hl,hp'⟩ := Nat.mem_primesLE.mp hm
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hl.trans (Nat.floor_mono h),hp'⟩,he⟩


  obtain ⟨V,hV,h3⟩ := hthird M hM
  let K := ⌈2*V/δ⌉₊ + 1
  have hK : (0:ℝ)<K := by dsimp [K]; positivity
  have hKV : 2*V  ≤  δ*K := by
    have h := Nat.le_ceil (2*V/δ)
    have hh := (div_le_iff₀ hδ).mp h
    dsimp [K]; push_cast; nlinarith
  let c := min (1/2:ℝ) (δ/(8*K))
  have hc : 0<c := lt_min (by norm_num) (by positivity)
  have hcK : 8*c*K ≤ δ := by
    have h := (le_div_iff₀ (by positivity : 0<(8:ℝ)*K)).mp (min_le_right _ _ : c  ≤  δ/(8*K))
    linarith
  refine ⟨c,hc,c,hc,Nat.frequently_atTop_iff_infinite.mp ?_⟩
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (hprimeNumber c hc)
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop M)
  apply (hpair.and_eventually (h3.and (hlog.and ((tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop Y)).and (eventually_ge_atTop 2))))).mono
  rintro d ⟨⟨hMd,hP⟩,hVd,hl,hYd,hd⟩
  have hd' : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  have hφ : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr (show 0<d by omega)
  change M ≤ log (d:ℝ) at hl
  change Y ≤ (d:ℝ) at hYd
  let y := (1+c)*scale d
  have hlogpos : 0<log (d:ℝ) := by linarith
  have hs : (d:ℝ) ≤ scale d := hMd.trans (by dsimp [scale]; nlinarith [mul_le_mul_of_nonneg_left hl hφ.le])
  have hy : scale d ≤ y := by dsimp [y]; nlinarith [mul_nonneg hc.le (hd'.le.trans hs)]
  have hqy := hY y (hYd.trans (hs.trans hy))
  have hlogy : log (d:ℝ)  ≤  log y := log_le_log hd' (hs.trans hy)
  have hyφ : y/log y  ≤  (1+c)*d.totient := by
    apply (div_le_iff₀ (hlogpos.trans_le hlogy)).mpr
    calc y = ((1+c)*d.totient)*log d := by dsimp [y,scale]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hlogy (by positivity)
  have hprime : (Nat.primeCounting ⌊y⌋₊ : ℝ)  ≤  (1+3*c)*d.totient := by
    have hc1 : c ≤ 1 := (min_le_left ..).trans (by norm_num : (1/2:ℝ) ≤ 1)
    refine hqy.trans ((mul_le_mul_of_nonneg_left hyφ (by positivity)).trans ?_)
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc1 hc.le) hφ.le]
  let A := extra d (scale d)
  have ht := hVd hMd
  have hu := clip_sum d K (scale d)
  have hr : ((∑ a ∈ residues d, hits d (scale d) a * (hits d (scale d) a-1) : ℕ):ℝ)*K  ≤ 
      (K:ℝ)^2*(A:ℝ) + ((∑ a ∈ residues d, hits d (scale d) a^3 : ℕ):ℝ) := by exact_mod_cast hu
  have hA : 4*c*d.totient  ≤  (A:ℝ) := by
    apply le_of_mul_le_mul_left (a:=(K:ℝ)^2) _ (by positivity)
    nlinarith only [hr,ht,mul_le_mul_of_nonneg_right hP hK.le,
      mul_le_mul_of_nonneg_right hKV hφ.le,
      mul_le_mul_of_nonneg_right hcK (mul_nonneg hK.le hφ.le)]
  let S := (range d).filter fun a => a.Coprime d ∧ (leastCongruentPrime a d : ℝ)>y
  have hmis : (d.totient:ℝ)+(extra d y:ℕ)  ≤  (S.card:ℝ)+Nat.primeCounting ⌊y⌋₊ := by
    exact_mod_cast missing d (by omega) y
  have hmono : (A:ℝ)  ≤  extra d y := by exact_mod_cast extra_mono d hy
  rw [Nat.Iio_eq_range]
  change c*d.totient  ≤  ((range d).filter fun a => a.Coprime d ∧ (leastCongruentPrime a d : ℝ) > (1+c)*d.totient*log d).card
  have he : (1+c)*d.totient*log d=y := by dsimp [y,scale]; ring
  rw [he]
  change c*d.totient  ≤  (S.card:ℝ)
  linarith

end OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1


section
section
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


open scoped Classical
open Finset

namespace OMALib.Sieve

variable {ι : Type*} [DecidableEq ι]

/-- The Selberg function `h(p) = g(p)/(1 - g(p))` attached to a local density `g`. -/
noncomputable def hFun (g : ι → ℝ) (p : ι) : ℝ := g p / (1 - g p)

/-- Selberg's normaliser `G = Σ_{S ∈ D} Π_{p ∈ S} h(p)` for a support family `D`. -/
noncomputable def selbergG (g : ι → ℝ) (D : Finset (Finset ι)) : ℝ :=
  ∑ S ∈ D, ∏ p ∈ S, hFun g p

/-- The optimal Selberg weights
`λ_S = (-1)^{|S|} (Π_{p∈S} g(p)⁻¹) G⁻¹ Σ_{T ∈ D, S ⊆ T} Π_{p∈T} h(p)`. -/
noncomputable def selbergWeight (g : ι → ℝ) (D : Finset (Finset ι)) (S : Finset ι) : ℝ :=
  (-1) ^ S.card * (∏ p ∈ S, (g p)⁻¹) / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p

/-- Inclusion-exclusion over an interval `[U, T]` of the subset lattice. -/
theorem sum_interval_neg_one_pow {U T : Finset ι} (hUT : U ⊆ T) :
    ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card = if T = U then (-1) ^ U.card else 0 := by
  have h1 : ∑ S ∈ T.powerset with U ⊆ S, ((-1 : ℝ)) ^ S.card
      = ∑ V ∈ (T \ U).powerset, (-1 : ℝ) ^ U.card * (-1) ^ V.card := by
    refine Finset.sum_nbij' (fun S => S \ U) (fun V => U ∪ V) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS ⊢
      exact sdiff_subset_sdiff hS.1 le_rfl
    · intro V hV
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hV ⊢
      refine ⟨union_subset hUT (hV.trans sdiff_subset), subset_union_left⟩
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      exact union_sdiff_of_subset hS.2
    · intro V hV
      simp only [mem_powerset, mem_coe] at hV
      have : Disjoint U V := by
        rw [disjoint_iff_ne]; intro a ha b hb hab; subst hab
        have := hV hb; simp at this; exact this.2 ha
      exact union_sdiff_cancel_left this
    · intro S hS
      simp only [mem_filter, mem_powerset, coe_filter, mem_coe] at hS
      rw [← pow_add, add_comm, card_sdiff_add_card_eq_card hS.2]
  have h2 : ∑ V ∈ (T \ U).powerset, ((-1 : ℝ)) ^ V.card = if T \ U = ∅ then 1 else 0 := by
    have := congrArg (Int.cast : ℤ → ℝ) (sum_powerset_neg_one_pow_card (x := T \ U))
    push_cast at this
    rw [this]
  rw [h1, ← mul_sum, h2]
  have : T \ U = ∅ ↔ T = U := by
    constructor
    · intro h; exact Subset.antisymm (sdiff_eq_empty_iff_subset.mp h) hUT
    · intro h; subst h; simp
  by_cases hT : T = U
  · simp [hT]
  · rw [if_neg (by rwa [this]), if_neg hT, mul_zero]

section Abstract

variable {Q : Finset ι} {g : ι → ℝ} {D : Finset (Finset ι)}

theorem hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {p : ι} (hp : p ∈ Q) :
    0 < hFun g p := div_pos (hg0 p hp) (by linarith [hg1 p hp])

theorem prod_hFun_pos (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S : Finset ι}
    (hS : S ⊆ Q) : 0 < ∏ p ∈ S, hFun g p :=
  prod_pos fun p hp => hFun_pos hg0 hg1 (hS hp)

/-- `G ≥ 1`, since the empty set contributes `1`. -/
theorem one_le_selbergG (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : 1 ≤ selbergG g D := by
  unfold selbergG
  have := single_le_sum (f := fun S => ∏ p ∈ S, hFun g p)
    (fun S hS => (prod_hFun_pos hg0 hg1 (hDQ S hS)).le) hemp
  simpa using this

theorem selbergWeight_mul_prod (hg0 : ∀ p ∈ Q, 0 < g p) {S : Finset ι} (hS : S ⊆ Q) :
    selbergWeight g D S * ∏ p ∈ S, g p
      = (-1) ^ S.card / selbergG g D * ∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p := by
  unfold selbergWeight
  have h : (∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p = 1 := by
    rw [← prod_mul_distrib]
    exact prod_eq_one fun p hp => inv_mul_cancel₀ (hg0 p (hS hp)).ne'
  calc _ = (-1) ^ S.card / selbergG g D * (∑ T ∈ D with S ⊆ T, ∏ p ∈ T, hFun g p) *
        ((∏ p ∈ S, (g p)⁻¹) * ∏ p ∈ S, g p) := by ring
    _ = _ := by rw [h, mul_one]

/-- The diagonalising variables `y_U = Σ_{S ∈ D, U ⊆ S} λ_S g(S)` of the Selberg weights. -/
theorem selbergY (hg0 : ∀ p ∈ Q, 0 < g p) (hDQ : ∀ S ∈ D, S ⊆ Q)
    (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (U : Finset ι) :
    ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / selbergG g D else 0 := by
  set G := selbergG g D
  set hS : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have e1 : ∑ S ∈ D with U ⊆ S, selbergWeight g D S * ∏ p ∈ S, g p
      = ∑ S ∈ D, ∑ T ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0 := by
    rw [sum_filter]
    refine sum_congr rfl fun S hSD => ?_
    by_cases hU : U ⊆ S
    · rw [if_pos hU, selbergWeight_mul_prod hg0 (hDQ S hSD), mul_sum, sum_filter]
      refine sum_congr rfl fun T _ => ?_
      by_cases hST : S ⊆ T <;> simp [hU, hST, hS, G]
    · rw [if_neg hU]; symm
      exact sum_eq_zero fun T _ => by simp [hU]
  rw [e1, sum_comm]
  have e2 : ∀ T ∈ D, (∑ S ∈ D, if U ⊆ S ∧ S ⊆ T then (-1) ^ S.card / G * hS T else 0)
      = if T = U then (-1) ^ U.card / G * hS U else 0 := by
    intro T hT
    rw [← sum_filter]
    by_cases hUT : U ⊆ T
    · have hf : D.filter (fun S => U ⊆ S ∧ S ⊆ T) = T.powerset.filter (fun S => U ⊆ S) := by
        ext S; simp only [mem_filter, mem_powerset]
        constructor
        · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h2, h1⟩; exact ⟨hdown T hT S h2, h1, h2⟩
      rw [hf, ← sum_mul, ← sum_div, sum_interval_neg_one_pow hUT]
      by_cases hTU : T = U
      · subst hTU; simp
      · simp [hTU]
    · have hTU : T ≠ U := by rintro rfl; exact hUT le_rfl
      rw [if_neg hTU]
      refine sum_eq_zero fun S hS' => ?_
      simp only [mem_filter] at hS'
      exact absurd (hS'.2.1.trans hS'.2.2) hUT
  rw [sum_congr rfl e2, sum_ite_eq']
  split_ifs <;> ring

theorem prod_union_eq (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1) {S₁ S₂ : Finset ι}
    (h₁ : S₁ ⊆ Q) (h₂ : S₂ ⊆ Q) :
    ∏ p ∈ S₁ ∪ S₂, g p = (∏ p ∈ S₁, g p) * (∏ p ∈ S₂, g p) *
      ∑ U ∈ Q.powerset, if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0 := by
  have hinv : (∏ p ∈ S₁ ∩ S₂, g p)⁻¹ = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← prod_inv_distrib]
    have : ∀ p ∈ S₁ ∩ S₂, (g p)⁻¹ = 1 + (hFun g p)⁻¹ := by
      intro p hp
      have hp' : p ∈ Q := h₁ (mem_inter.mp hp).1
      have a := hg0 p hp'; have b := hg1 p hp'
      unfold hFun; rw [inv_div]; field_simp; ring
    rw [prod_congr rfl this, prod_one_add]
    exact sum_congr rfl fun U _ => by rw [prod_inv_distrib]
  have hsum : ∑ U ∈ Q.powerset, (if U ⊆ S₁ ∧ U ⊆ S₂ then (∏ p ∈ U, hFun g p)⁻¹ else 0)
      = ∑ U ∈ (S₁ ∩ S₂).powerset, (∏ p ∈ U, hFun g p)⁻¹ := by
    rw [← sum_filter]
    congr 1
    ext U; simp only [mem_filter, mem_powerset, subset_inter_iff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.1.trans h₁, h⟩
  have hne : (∏ p ∈ S₁ ∩ S₂, g p) ≠ 0 :=
    (prod_pos fun p hp => hg0 p (h₁ (mem_inter.mp hp).1)).ne'
  rw [hsum, ← hinv, ← prod_union_inter (s₁ := S₁) (s₂ := S₂)]
  field_simp

/-- The Selberg quadratic form evaluated at the optimal weights equals `1 / G`. -/
theorem selberg_mainTerm (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D) :
    ∑ S₁ ∈ D, ∑ S₂ ∈ D, selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
      = 1 / selbergG g D := by
  set G := selbergG g D with hG
  set a : Finset ι → ℝ := fun S => selbergWeight g D S * ∏ p ∈ S, g p
  set w : Finset ι → ℝ := fun U => (∏ p ∈ U, hFun g p)⁻¹
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have e1 : ∀ S₁ ∈ D, ∀ S₂ ∈ D,
      selbergWeight g D S₁ * selbergWeight g D S₂ * ∏ p ∈ S₁ ∪ S₂, g p
        = ∑ U ∈ Q.powerset, w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0)) := by
    intro S₁ h₁ S₂ h₂
    rw [prod_union_eq hg0 hg1 (hDQ _ h₁) (hDQ _ h₂), mul_sum, mul_sum]
    refine sum_congr rfl fun U _ => ?_
    by_cases u1 : U ⊆ S₁ <;> by_cases u2 : U ⊆ S₂ <;> simp [u1, u2, a, w] <;> ring
  rw [sum_congr rfl fun S₁ h₁ => sum_congr rfl fun S₂ h₂ => e1 S₁ h₁ S₂ h₂]
  have eswap : ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∑ U ∈ Q.powerset,
      w U * ((if U ⊆ S₁ then a S₁ else 0) * (if U ⊆ S₂ then a S₂ else 0))
      = ∑ U ∈ Q.powerset, w U * ((∑ S ∈ D with U ⊆ S, a S) * (∑ S ∈ D with U ⊆ S, a S)) := by
    simp_rw [sum_filter, sum_mul_sum, mul_sum]
    conv_lhs => arg 2; ext S₁; rw [sum_comm]
    rw [sum_comm]
  rw [eswap]
  have hy : ∀ U, ∑ S ∈ D with U ⊆ S, a S
      = if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0 :=
    selbergY hg0 hDQ hdown
  simp_rw [hy]
  have e3 : ∀ U ∈ Q.powerset, w U * ((if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0) *
      (if U ∈ D then (-1) ^ U.card * (∏ p ∈ U, hFun g p) / G else 0))
      = if U ∈ D then (∏ p ∈ U, hFun g p) / G ^ 2 else 0 := by
    intro U hU
    split_ifs with hUD
    · have hpos := prod_hFun_pos hg0 hg1 (hDQ U hUD)
      simp only [w]
      field_simp
      rw [← pow_mul, mul_comm (U.card) 2, pow_mul]; simp
    · simp
  rw [sum_congr rfl e3, ← sum_filter]
  have : Q.powerset.filter (fun U => U ∈ D) = D := by
    ext U; simp only [mem_filter, mem_powerset]
    exact ⟨fun h => h.2, fun h => ⟨hDQ U h, h⟩⟩
  rw [this, ← sum_div]
  change G / G ^ 2 = 1 / G
  field_simp

/-- The optimal Selberg weights satisfy `|λ_S| ≤ 1`. -/
theorem abs_selbergWeight_le (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    {S : Finset ι} (hS : S ∈ D) : |selbergWeight g D S| ≤ 1 := by
  set G := selbergG g D with hG
  set hp : Finset ι → ℝ := fun T => ∏ p ∈ T, hFun g p
  have hG1 : 1 ≤ G := one_le_selbergG hg0 hg1 hDQ hemp
  have hSQ := hDQ S hS
  have hnn : ∀ T ⊆ Q, 0 ≤ hp T := fun T hT => (prod_hFun_pos hg0 hg1 hT).le
  have hginv : 0 < ∏ p ∈ S, (g p)⁻¹ := prod_pos fun p h => inv_pos.mpr (hg0 p (hSQ h))
  have habs : |selbergWeight g D S|
      = (∏ p ∈ S, (g p)⁻¹) * (∑ T ∈ D with S ⊆ T, hp T) / G := by
    unfold selbergWeight
    rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hginv, abs_of_pos (by linarith : (0:ℝ) < G),
      abs_of_nonneg (sum_nonneg fun T hT => hnn T (hDQ T (mem_filter.mp hT).1))]
    ring
  rw [habs, div_le_one (by linarith)]
  have key : ∀ T ∈ D.filter (fun T => S ⊆ T),
      (∏ p ∈ S, (g p)⁻¹) * hp T = ∑ W ∈ S.powerset, hp (W ∪ (T \ S)) := by
    intro T hT
    have hST := (mem_filter.mp hT).2
    have h1 : hp T = hp S * hp (T \ S) := by
      simp only [hp]; rw [mul_comm, prod_sdiff hST]
    have h2 : (∏ p ∈ S, (g p)⁻¹) * hp S = ∏ p ∈ S, (1 + hFun g p) := by
      simp only [hp]; rw [← prod_mul_distrib]
      refine prod_congr rfl fun p h => ?_
      have a := hg0 p (hSQ h); have b := hg1 p (hSQ h)
      have c : 1 - g p ≠ 0 := by linarith
      unfold hFun; field_simp; ring
    rw [h1, ← mul_assoc, h2, prod_one_add, sum_mul]
    refine sum_congr rfl fun W hW => ?_
    simp only [hp]
    rw [prod_union]
    exact disjoint_of_subset_left (mem_powerset.mp hW) disjoint_sdiff
  rw [mul_sum, sum_congr rfl key, sum_comm, ← sum_product']
  rw [← sum_image (s := S.powerset ×ˢ D.filter (fun T => S ⊆ T)) (g := fun x => x.1 ∪ (x.2 \ S))
    (f := hp)]
  · apply sum_le_sum_of_subset_of_nonneg
    · intro U hU
      simp only [mem_image, mem_product, mem_powerset, mem_filter] at hU
      obtain ⟨⟨W, T⟩, ⟨hW, hT, _⟩, rfl⟩ := hU
      exact hdown T hT _ (union_subset (hW.trans (by assumption)) sdiff_subset)
    · intro U hU _
      exact hnn U (hDQ U hU)
  · intro x hx y hy hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_powerset, mem_filter] at hx hy
    simp only at hxy
    have e1 : x.1 = (x.1 ∪ (x.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hx.1]
    have e2 : y.1 = (y.1 ∪ (y.2 \ S)) ∩ S := by
      rw [union_inter_distrib_right, sdiff_inter_self, union_empty, inter_eq_left.mpr hy.1]
    have f1 : x.2 = S ∪ (x.1 ∪ (x.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hx.1, union_sdiff_of_subset hx.2.2]
    have f2 : y.2 = S ∪ (y.1 ∪ (y.2 \ S)) := by
      rw [← union_assoc, union_eq_left.mpr hy.1, union_sdiff_of_subset hy.2.2]
    exact Prod.ext (by rw [e1, e2, hxy]) (by rw [f1, f2, hxy])

theorem selbergWeight_empty (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hemp : ∅ ∈ D) : selbergWeight g D ∅ = 1 := by
  have hG1 : 1 ≤ selbergG g D := one_le_selbergG hg0 hg1 hDQ hemp
  unfold selbergWeight
  simp only [card_empty, pow_zero, prod_empty, one_mul, empty_subset, filter_true_of_mem,
    implies_true]
  change 1 / selbergG g D * selbergG g D = 1
  field_simp

/-- **Selberg's upper-bound sieve, abstract form.**

`A` is a finite family of objects, `E a` is the set of primes dividing `a`, `Q` is the finite
set of sieving primes, and `D` is any down-closed family of subsets of `Q` containing `∅` (the
support of the Selberg weights; for the classical sieve, the sets of primes with product `< z`).
If for every `S ⊆ Q` the number of `a` divisible by all of `S` is `X * Π_{p∈S} g p + r S`, with
`0 < g p < 1`, then the number of `a` free of all primes of `Q` is at most
`X / G + Σ_{S₁, S₂ ∈ D} |r (S₁ ∪ S₂)|`, where `G = selbergG g D`. -/
theorem selberg_sieve_abstract {α : Type*} (A : Finset α) (E : α → Finset ι)
    (hg0 : ∀ p ∈ Q, 0 < g p) (hg1 : ∀ p ∈ Q, g p < 1)
    (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D) (hemp : ∅ ∈ D)
    (X : ℝ) (r : Finset ι → ℝ)
    (hr : ∀ S ⊆ Q, ((A.filter (fun a => S ⊆ E a)).card : ℝ) = X * ∏ p ∈ S, g p + r S) :
    ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
  set lam := selbergWeight g D
  have step1 : ((A.filter (fun a => Disjoint Q (E a))).card : ℝ)
      ≤ ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2 := by
    rw [card_filter]; push_cast
    refine sum_le_sum fun a _ => ?_
    split_ifs with hd
    · have : (∑ S ∈ D, if S ⊆ E a then lam S else 0) = lam ∅ := by
        have e := sum_ite_eq' D ∅ lam
        rw [if_pos hemp] at e
        rw [← e]
        refine sum_congr rfl fun S hS => ?_
        by_cases hS0 : S = ∅
        · subst hS0; simp
        · have : ¬ S ⊆ E a := by
            intro h
            apply hS0
            exact subset_empty.mp fun x hx =>
              (disjoint_left.mp hd (hDQ S hS hx) (h hx)).elim
          simp [this, hS0, Ne.symm hS0]
      have e1 : lam ∅ = 1 := selbergWeight_empty hg0 hg1 hDQ hemp
      rw [this, e1]; norm_num
    · positivity
  have step2 : ∑ a ∈ A, (∑ S ∈ D, if S ⊆ E a then lam S else 0) ^ 2
      = ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ) := by
    simp_rw [sq, sum_mul_sum, card_filter]
    push_cast
    rw [sum_comm]
    refine sum_congr rfl fun S₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun S₂ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    by_cases h1 : S₁ ⊆ E a <;> by_cases h2 : S₂ ⊆ E a <;> simp [h1, h2, union_subset_iff]
  have step3 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ *
          ((A.filter (fun a => S₁ ∪ S₂ ⊆ E a)).card : ℝ)
      = X * (∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * ∏ p ∈ S₁ ∪ S₂, g p)
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₁ h₁ => ?_
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun S₂ h₂ => ?_
    rw [hr _ (union_subset (hDQ _ h₁) (hDQ _ h₂))]; ring
  have step4 : ∑ S₁ ∈ D, ∑ S₂ ∈ D, lam S₁ * lam S₂ * r (S₁ ∪ S₂)
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have a1 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₁
    have a2 := abs_selbergWeight_le hg0 hg1 hDQ hdown hemp h₂
    calc lam S₁ * lam S₂ * r (S₁ ∪ S₂) ≤ |lam S₁ * lam S₂ * r (S₁ ∪ S₂)| := le_abs_self _
      _ = |lam S₁| * |lam S₂| * |r (S₁ ∪ S₂)| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * 1 * |r (S₁ ∪ S₂)| := by gcongr
      _ = _ := by ring
  rw [selberg_mainTerm hg0 hg1 hDQ hdown hemp] at step3
  calc _ ≤ _ := step1
    _ = _ := step2
    _ = _ := step3
    _ ≤ X / selbergG g D + ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)| := by
      rw [mul_one_div]; linarith

end Abstract

/-! ## Counting residue conditions -/


theorem count_periodic_mul (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hper : ∀ n, P n ↔ P (n % m)) (q : ℕ) :
    Nat.count P (m * q) = q * Nat.count P m := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hfun : (fun k => P (m * q + k)) = P := by
      funext k; apply propext
      rw [hper (m * q + k), hper k, Nat.mul_add_mod]
    rw [Nat.mul_succ, Nat.count_add, ih]
    have : Nat.count (fun k => P (m * q + k)) m = Nat.count P m := by
      simp_rw [hfun]
    rw [this]; ring

/-- Counting a periodic set in an initial segment: if `P` is `m`-periodic with `K` solutions
in `[0, m)`, then the number of solutions in `[0, N)` is `N K / m` up to an error of at most `K`. -/
theorem card_filter_range_periodic (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hm : 0 < m)
    (hper : ∀ n, P n ↔ P (n % m)) (N : ℕ) :
    |(((range N).filter P).card : ℝ) - N * ((range m).filter P).card / m|
      ≤ ((range m).filter P).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  set K := Nat.count P m
  have hN : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
  have hc : Nat.count P N = (N / m) * K + Nat.count P (N % m) := by
    conv_lhs => rw [hN]
    rw [Nat.count_add, count_periodic_mul P hper]
    congr 1
    congr 1
    funext k; apply propext
    rw [hper (m * (N / m) + k), hper k, Nat.mul_add_mod]
  have hle : Nat.count P (N % m) ≤ K := Nat.count_monotone P (Nat.mod_lt N hm).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : ((N % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt N hm
  have hNR : (N : ℝ) = m * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by exact_mod_cast hN
  rw [hc, abs_le]
  push_cast
  have hleR : ((Nat.count P (N % m) : ℕ) : ℝ) ≤ K := by exact_mod_cast hle
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have e : (N : ℝ) * K / m = ((N / m : ℕ) : ℝ) * K + ((N % m : ℕ) : ℝ) * K / m := by
    rw [hNR]; field_simp
  have h2 : ((N % m : ℕ) : ℝ) * K / m ≤ K := by
    rw [div_le_iff₀ hmR]; nlinarith
  have h3 : 0 ≤ ((N % m : ℕ) : ℝ) * K / m := by positivity
  rw [e]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.count P (N % m))]


theorem card_filter_range_mul (F : ℕ → Prop) [DecidablePred F] {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ((range (p * m)).filter F).card
      = ∑ j ∈ range p, ((range m).filter (fun t => F (j + p * t))).card := by
  have : ((range (p * m)).filter F).card
      = ((range p ×ˢ range m).filter (fun x => F (x.1 + p * x.2))).card := by
    refine Finset.card_nbij' (fun r => (r % p, r / p)) (fun x => x.1 + p * x.2) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hr ⊢
      refine ⟨⟨Nat.mod_lt _ hp, ?_⟩, by rw [Nat.mod_add_div]; exact hr.2⟩
      exact Nat.div_lt_of_lt_mul hr.1
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx ⊢
      refine ⟨?_, hx.2⟩
      calc x.1 + p * x.2 < p + p * x.2 := by omega
        _ = p * (x.2 + 1) := by ring
        _ ≤ p * m := Nat.mul_le_mul_left _ hx.1.2
    · intro r _
      simp only [Nat.mod_add_div]
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_setOf_eq, mem_product] at hx
      simp only
      refine Prod.ext ?_ ?_
      · simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1.1]
      · simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx.1.1, zero_add]
  rw [this, card_filter, sum_product]
  refine sum_congr rfl fun j _ => ?_
  rw [card_filter]

theorem card_filter_range_shift (P : ℕ → Prop) [DecidablePred P] {m p : ℕ} (hm : 0 < m) (hpm : Nat.Coprime p m)
    (hper : ∀ n, P n ↔ P (n % m)) (j : ℕ) :
    ((range m).filter (fun t => P (j + p * t))).card = ((range m).filter P).card := by
  set f : ℕ → ℕ := fun t => (j + p * t) % m
  have hinj : Set.InjOn f (range m) := by
    intro t ht t' ht' h
    simp only [coe_range, Set.mem_Iio] at ht ht'
    have h1 : j + p * t ≡ j + p * t' [MOD m] := h
    have h2 := Nat.ModEq.add_left_cancel' j h1
    have h3 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hpm) h2
    have := Nat.mod_eq_of_lt ht; have := Nat.mod_eq_of_lt ht'
    unfold Nat.ModEq at h3; omega
  have himg : (range m).image f = range m := by
    apply eq_of_subset_of_card_le
    · intro u hu
      simp only [mem_image, mem_range] at hu ⊢
      obtain ⟨t, _, rfl⟩ := hu
      exact Nat.mod_lt _ hm
    · rw [card_image_of_injOn hinj]
  have hfilt : (range m).filter (fun t => P (j + p * t)) = (range m).filter (fun t => P (f t)) := by
    refine filter_congr fun t _ => ?_
    simp only [f]; exact hper _
  have himg2 : (range m).filter P = ((range m).filter (fun t => P (f t))).image f := by
    ext u
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hu, hP⟩
      rw [← himg] at hu
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
      exact ⟨t, ⟨ht, hP⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hP⟩, rfl⟩
      exact ⟨mem_range.mpr (Nat.mod_lt _ hm), hP⟩
  rw [hfilt, himg2, card_image_of_injOn (hinj.mono (filter_subset _ _))]

/-- Chinese remainder count: if each condition `C p` is `p`-periodic, the number of residues
modulo `Π_{p∈S} p` satisfying all of them is `Π_{p∈S} ω(p)`. -/
theorem card_filter_range_prod (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ((range (∏ p ∈ S, p)).filter (fun r => ∀ p ∈ S, C p r)).card
      = ∏ p ∈ S, ((range p).filter (C p)).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp := hS p (mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hm : 0 < ∏ q ∈ S, q := prod_pos fun q hq => (hS' q hq).pos
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp (hS' q hq)).mpr (fun h => hpS (h ▸ hq))
    rw [prod_insert hpS, prod_insert hpS, card_filter_range_mul (fun r => ∀ q ∈ insert p S, C q r) hp.pos, ← ih hS']
    have hperS : ∀ n, (∀ q ∈ S, C q n) ↔ (∀ q ∈ S, C q (n % ∏ q ∈ S, q)) := by
      intro n
      refine forall₂_congr fun q hq => ?_
      have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
      rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
    have step : ∀ j ∈ range p,
        ((range (∏ q ∈ S, q)).filter (fun t => ∀ q ∈ insert p S, C q (j + p * t))).card
          = if C p j then ((range (∏ q ∈ S, q)).filter (fun r => ∀ q ∈ S, C q r)).card else 0 := by
      intro j hj
      have hj' : ∀ t, C p (j + p * t) ↔ C p j := by
        intro t
        rw [hper p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp hj)]
      simp_rw [forall_mem_insert, hj']
      split_ifs with hc
      · simp only [hc, true_and]
        convert card_filter_range_shift (fun n => ∀ q ∈ S, C q n) hm hcop hperS j using 2 <;> (ext; simp)
      · simp [hc]
    rw [sum_congr rfl step, ← sum_filter, sum_const, smul_eq_mul]

/-! ## Selberg's sieve for residue conditions -/

/-- The number `ω(p)` of residues `r ∈ [0, p)` that are removed by the local condition `C p`. -/
noncomputable def omega (C : ℕ → ℕ → Prop) (p : ℕ) : ℕ := ((range p).filter (C p)).card

/-- The classical Selberg support: sets of primes from `Q` whose product is `< z`. -/
noncomputable def levelFamily (Q : Finset ℕ) (z : ℕ) : Finset (Finset ℕ) :=
  Q.powerset.filter (fun S => ∏ p ∈ S, p < z)

/-- The number of `n < N` meeting every condition `C p`, `p ∈ S`, is `N Π_{p∈S} ω(p)/p` up to an
error of at most `Π_{p∈S} ω(p)`. -/
theorem card_residue_error (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    |(((range N).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
        - N * ∏ p ∈ S, ((omega C p : ℝ) / p)| ≤ ∏ p ∈ S, (omega C p : ℝ) := by
  have hm : 0 < ∏ p ∈ S, p := prod_pos fun p hp => (hS p hp).pos
  have hper' : ∀ n, (∀ p ∈ S, C p n) ↔ (∀ p ∈ S, C p (n % ∏ q ∈ S, q)) := by
    intro n
    refine forall₂_congr fun q hq => ?_
    have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
    rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
  have hcount := card_filter_range_periodic (fun n => ∀ p ∈ S, C p n) hm hper' N
  have hK := card_filter_range_prod C hper S hS
  have hK' : (((range (∏ p ∈ S, p)).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
      = ∏ p ∈ S, (omega C p : ℝ) := by
    have e : ∏ i ∈ S, omega C i = ∏ p ∈ S, ((range p).filter (C p)).card := rfl
    rw [← Nat.cast_prod, e, ← hK]
  rw [hK'] at hcount
  convert hcount using 3
  rw [prod_div_distrib]; push_cast; ring

/-- **Selberg's sieve for residue conditions.** For each prime `p ∈ Q` let `C p` be a
`p`-periodic condition on `ℕ` holding for `ω(p)` residues, with `0 < ω(p) < p`. Then the number
of `n < N` satisfying no condition `C p`, `p ∈ Q`, is at most
`N / G + Σ_{S₁,S₂ ∈ D} Π_{p ∈ S₁ ∪ S₂} ω(p)`, with `G = selbergG (ω/p) D`, for any down-closed
support family `D ∋ ∅` of subsets of `Q`. -/
theorem selberg_residue (N : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p)
    (D : Finset (Finset ℕ)) (hDQ : ∀ S ∈ D, S ⊆ Q) (hdown : ∀ S ∈ D, ∀ T ⊆ S, T ∈ D)
    (hemp : ∅ ∈ D) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) D
        + ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
  set g : ℕ → ℝ := fun p => (omega C p : ℝ) / p
  have hg0 : ∀ p ∈ Q, 0 < g p := fun p hp =>
    div_pos (by exact_mod_cast hω0 p hp) (by exact_mod_cast (hQ p hp).pos)
  have hg1 : ∀ p ∈ Q, g p < 1 := fun p hp => by
    have : (0 : ℝ) < p := by exact_mod_cast (hQ p hp).pos
    simp only [g]; rw [div_lt_one this]; exact_mod_cast hω1 p hp
  set E : ℕ → Finset ℕ := fun n => Q.filter (fun p => C p n)
  set r : Finset ℕ → ℝ := fun S =>
    (((range N).filter (fun n => S ⊆ E n)).card : ℝ) - N * ∏ p ∈ S, g p
  have key := selberg_sieve_abstract (range N) E hg0 hg1 hDQ hdown hemp (N : ℝ) r
    (fun S _ => by simp only [r]; rw [add_sub_cancel])
  have hrem : ∑ S₁ ∈ D, ∑ S₂ ∈ D, |r (S₁ ∪ S₂)|
      ≤ ∑ S₁ ∈ D, ∑ S₂ ∈ D, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) := by
    refine sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => ?_
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset (hDQ _ h₁) (hDQ _ h₂)
    have hc : ((range N).filter (fun n => S₁ ∪ S₂ ⊆ E n)).card
        = ((range N).filter (fun n => ∀ p ∈ S₁ ∪ S₂, C p n)).card := by
      congr 1; ext n
      simp only [E, mem_filter, subset_iff]
      exact ⟨fun h => ⟨h.1, fun p hp => (h.2 hp).2⟩, fun h => ⟨h.1, fun p hp => ⟨hSQ hp, h.2 p hp⟩⟩⟩
    have := card_residue_error C hper (S₁ ∪ S₂) (fun p hp => hQ p (hSQ hp)) N
    simp only [r]; rw [hc]
    exact this
  have k2 := key.trans (add_le_add le_rfl hrem)
  have hc : ((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card
      = ((range N).filter (fun n => Disjoint Q (E n))).card := by
    congr 1; ext n
    simp only [E, disjoint_left, mem_filter, not_and]
    exact ⟨fun h => ⟨h.1, fun p hp _ => h.2 p hp⟩, fun h => ⟨h.1, fun p hp => h.2 hp hp⟩⟩
  have hc' : (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      = (((range N).filter (fun n => Disjoint Q (E n))).card : ℝ) := by
    exact_mod_cast hc
  rw [hc']
  exact k2

theorem levelFamily_subset {Q : Finset ℕ} {z : ℕ} : ∀ S ∈ levelFamily Q z, S ⊆ Q :=
  fun S hS => mem_powerset.mp (mem_filter.mp hS).1

theorem levelFamily_down {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) {z : ℕ} :
    ∀ S ∈ levelFamily Q z, ∀ T ⊆ S, T ∈ levelFamily Q z := by
  intro S hS T hT
  simp only [levelFamily, mem_filter, mem_powerset] at hS ⊢
  refine ⟨hT.trans hS.1, lt_of_le_of_lt ?_ hS.2⟩
  exact prod_le_prod_of_subset_of_one_le' hT fun p hp _ => (hQ p (hS.1 hp)).one_lt.le

theorem empty_mem_levelFamily {Q : Finset ℕ} {z : ℕ} (hz : 2 ≤ z) : ∅ ∈ levelFamily Q z := by
  simp only [levelFamily, mem_filter, empty_mem_powerset, prod_empty, true_and]; omega

theorem card_levelFamily_le {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime) (z : ℕ) :
    (levelFamily Q z).card ≤ z := by
  have := card_le_card_of_injOn (s := levelFamily Q z) (t := range z) (fun S => ∏ p ∈ S, p)
    (fun S hS => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS
      simp only [coe_range, Set.mem_Iio]; exact hS.2)
    (fun S hS T hT h => by
      simp only [levelFamily, coe_filter, mem_powerset, Set.mem_setOf_eq] at hS hT
      have h1 := Nat.primeFactors_prod (s := S) fun p hp => hQ p (hS.1 hp)
      have h2 := Nat.primeFactors_prod (s := T) fun p hp => hQ p (hT.1 hp)
      simp only at h
      rw [← h1, ← h2, h])
  simpa using this

/-- **Selberg's sieve at level `z`, with a crude explicit remainder.** With the classical support
`levelFamily Q z` (products of primes `< z`), the number of `n < N` meeting no condition `C p`,
`p ∈ Q`, is at most `N / G + z ^ 4`. -/
theorem selberg_residue_level (N z : ℕ) (hz : 2 ≤ z) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (hω0 : ∀ p ∈ Q, 0 < omega C p) (hω1 : ∀ p ∈ Q, omega C p < p) :
    (((range N).filter (fun n => ∀ p ∈ Q, ¬ C p n)).card : ℝ)
      ≤ N / selbergG (fun p => (omega C p : ℝ) / p) (levelFamily Q z) + (z : ℝ) ^ 4 := by
  have key := selberg_residue N Q hQ C hper hω0 hω1 (levelFamily Q z) levelFamily_subset
    (levelFamily_down hQ) (empty_mem_levelFamily hz)
  refine key.trans (add_le_add le_rfl ?_)
  have hterm : ∀ S₁ ∈ levelFamily Q z, ∀ S₂ ∈ levelFamily Q z,
      ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ (z : ℝ) ^ 2 := by
    intro S₁ h₁ S₂ h₂
    have h₁' := h₁; have h₂' := h₂
    simp only [levelFamily, mem_filter, mem_powerset] at h₁' h₂'
    have hSQ : S₁ ∪ S₂ ⊆ Q := union_subset h₁'.1 h₂'.1
    have a : ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ) ≤ ∏ p ∈ S₁ ∪ S₂, (p : ℝ) :=
      prod_le_prod (fun p _ => by positivity)
        (fun p hp => by exact_mod_cast (hω1 p (hSQ hp)).le)
    have b : ∏ p ∈ S₁ ∪ S₂, p ≤ (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p := by
      rw [← prod_union_inter]
      exact Nat.le_mul_of_pos_right _ (prod_pos fun p hp => (hQ p (h₁'.1 (mem_inter.mp hp).1)).pos)
    have c : (∏ p ∈ S₁, p) * ∏ p ∈ S₂, p ≤ z * z :=
      Nat.mul_le_mul h₁'.2.le h₂'.2.le
    have : ((∏ p ∈ S₁ ∪ S₂, p : ℕ) : ℝ) ≤ (z : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast b.trans c
    push_cast at this
    linarith
  calc ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, ∏ p ∈ S₁ ∪ S₂, (omega C p : ℝ)
      ≤ ∑ S₁ ∈ levelFamily Q z, ∑ S₂ ∈ levelFamily Q z, (z : ℝ) ^ 2 :=
        sum_le_sum fun S₁ h₁ => sum_le_sum fun S₂ h₂ => hterm S₁ h₁ S₂ h₂
    _ = ((levelFamily Q z).card : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        simp only [sum_const, nsmul_eq_mul]; ring
    _ ≤ (z : ℝ) ^ 2 * (z : ℝ) ^ 2 := by
        have h1 : ((levelFamily Q z).card : ℝ) ≤ z := by exact_mod_cast card_levelFamily_le hQ z
        have h0 : (0 : ℝ) ≤ ((levelFamily Q z).card : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h1 2) (by positivity)
    _ = (z : ℝ) ^ 4 := by ring

/-- `selbergG` only depends on `g` on the primes of `Q`. -/
theorem selbergG_congr {Q : Finset ℕ} {D : Finset (Finset ℕ)} (hDQ : ∀ S ∈ D, S ⊆ Q)
    {g g' : ℕ → ℝ} (h : ∀ p ∈ Q, g p = g' p) : selbergG g D = selbergG g' D := by
  unfold selbergG hFun
  exact sum_congr rfl fun S hS => prod_congr rfl fun p hp => by rw [h p (hDQ S hS hp)]

/-! ## Prime pairs `p, p + d` -/

/-- The local condition of the prime-pair sieve: `p ∣ n (n + d)`. -/
def pairCond (d : ℕ) (p n : ℕ) : Prop := p ∣ n * (n + d)

/-- The number of residues removed modulo `p` in the prime-pair sieve:
`1` if `p ∣ d`, otherwise `2`. -/
def pairOmega (d p : ℕ) : ℕ := if p ∣ d then 1 else 2

/-- Selberg's `G(z)` for the prime-pair sieve with difference `d`:
`G_d(z) = Σ_{m < z, m ∣ P(z)} Π_{p ∣ m} ω_d(p)/(p - ω_d(p))`, written over sets of primes
`< z` with product `< z`. -/
noncomputable def pairG (d z : ℕ) : ℝ :=
  selbergG (fun p => (pairOmega d p : ℝ) / p) (levelFamily (Nat.primesBelow z) z)

theorem pairCond_periodic (d p n : ℕ) : pairCond d p n ↔ pairCond d p (n % p) := by
  unfold pairCond
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

theorem pairCond_iff_of_lt {d p r : ℕ} (hp : p.Prime) (hr : r < p) :
    pairCond d p r ↔ r = 0 ∨ r + d % p = p := by
  unfold pairCond
  rw [hp.dvd_mul]
  have hk : d % p < p := Nat.mod_lt _ hp.pos
  have e1 : p ∣ r ↔ r = 0 := ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hr, fun h => h ▸ dvd_zero p⟩
  have e2 : p ∣ r + d ↔ p ∣ r + d % p := by
    have : r + d = (r + d % p) + p * (d / p) := by
      have := Nat.mod_add_div d p; omega
    rw [this, Nat.dvd_add_left (dvd_mul_right p _)]
  have e3 : p ∣ r + d % p ↔ r + d % p = 0 ∨ r + d % p = p := by
    constructor
    · rintro ⟨m, hm⟩
      have : m < 2 := by
        by_contra h; push_neg at h
        have : p * 2 ≤ p * m := Nat.mul_le_mul_left _ h
        omega
      interval_cases m <;> simp_all
    · rintro (h | h) <;> rw [h]
      · exact dvd_zero p
  rw [e1, e2, e3]
  omega

theorem omega_pairCond {d p : ℕ} (hp : p.Prime) : omega (pairCond d) p = pairOmega d p := by
  unfold omega pairOmega
  have hk : d % p < p := Nat.mod_lt _ hp.pos
  split_ifs with hd
  · have : (range p).filter (pairCond d p) = {0} := by
      ext r
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hr, h⟩
        rw [pairCond_iff_of_lt hp hr, Nat.mod_eq_zero_of_dvd hd] at h
        omega
      · rintro rfl; exact ⟨hp.pos, (pairCond_iff_of_lt hp hp.pos).mpr (Or.inl rfl)⟩
    rw [this, card_singleton]
  · have hk0 : d % p ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
    have : (range p).filter (pairCond d p) = {0, p - d % p} := by
      ext r
      simp only [mem_filter, mem_range, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hr, h⟩
        rw [pairCond_iff_of_lt hp hr] at h
        omega
      · intro h
        have hr : r < p := by omega
        refine ⟨hr, (pairCond_iff_of_lt hp hr).mpr ?_⟩
        omega
    rw [this, card_insert_of_notMem (by simp; omega), card_singleton]

theorem pairOmega_pos (d p : ℕ) : 0 < pairOmega d p := by
  unfold pairOmega; split_ifs <;> norm_num

theorem pairOmega_lt {d p : ℕ} (hd : Even d) (hp : p.Prime) : pairOmega d p < p := by
  unfold pairOmega
  split_ifs with h
  · exact hp.one_lt
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have := hp.two_le; omega

/-- **Selberg upper bound for prime pairs, explicit form.** For even `d` and any level
`z ≥ 2`, the number of primes `p ≤ x` with `p + d` prime is at most
`z + (x + 1) / G_d(z) + z ^ 4`. -/
theorem card_prime_pairs_le_sieve (d x z : ℕ) (hd : Even d) (hz : 2 ≤ z) :
    (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
      ≤ z + (x + 1) / pairG d z + (z : ℝ) ^ 4 := by
  set Q := Nat.primesBelow z
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesBelow.mp hp).2
  have hsub : (range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)
      ⊆ range z ∪ (range (x + 1)).filter (fun n => ∀ p ∈ Q, ¬ pairCond d p n) := by
    intro n hn
    simp only [mem_filter, mem_range] at hn
    simp only [mem_union, mem_range, mem_filter]
    by_cases hnz : n < z
    · exact Or.inl hnz
    · right
      refine ⟨hn.1, fun q hq hdiv => ?_⟩
      have hq' := Nat.mem_primesBelow.mp hq
      unfold pairCond at hdiv
      rcases (hq'.2.dvd_mul).mp hdiv with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hq'.2 hn.2.1).mp h; omega
      · have := (Nat.prime_dvd_prime_iff_eq hq'.2 hn.2.2).mp h; omega
  have hω0 : ∀ p ∈ Q, 0 < omega (pairCond d) p := fun p hp => by
    rw [omega_pairCond (hQ p hp)]; exact pairOmega_pos d p
  have hω1 : ∀ p ∈ Q, omega (pairCond d) p < p := fun p hp => by
    rw [omega_pairCond (hQ p hp)]; exact pairOmega_lt hd (hQ p hp)
  have hsieve := selberg_residue_level (x + 1) z hz Q hQ (pairCond d) (pairCond_periodic d) hω0 hω1
  have hG : selbergG (fun p => (omega (pairCond d) p : ℝ) / p) (levelFamily Q z) = pairG d z :=
    selbergG_congr levelFamily_subset fun p hp => by rw [omega_pairCond (hQ p hp)]
  rw [hG] at hsieve
  push_cast at hsieve
  have hcard := card_le_card hsub
  have hu := card_union_le (range z) ((range (x + 1)).filter (fun n => ∀ p ∈ Q, ¬ pairCond d p n))
  rw [card_range] at hu
  have : (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
      ≤ z + (((range (x + 1)).filter (fun n => ∀ p ∈ Q, ¬ pairCond d p n)).card : ℝ) := by
    exact_mod_cast hcard.trans hu
  linarith

/-- Choice of the sieve level: for `x ≥ 2^16` there is `z ≥ 2` with
`(z + z^4) (log x)^2 ≤ 32 x` and `log x ≤ 16 log z` (take `z = ⌊x^{1/8}⌋`). -/
theorem exists_level (x : ℕ) (hx : 65536 ≤ x) :
    ∃ z : ℕ, 2 ≤ z ∧ ((z : ℝ) + (z : ℝ) ^ 4) * Real.log x ^ 2 ≤ 32 * x ∧
      Real.log x ≤ 16 * Real.log z := by
  set y : ℝ := (x : ℝ) ^ ((1 : ℝ) / 8) with hydef
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hy0 : 0 ≤ y := Real.rpow_nonneg hx0 _
  have hy8 : y ^ 8 = x := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
  have hxR : (65536 : ℝ) ≤ x := by exact_mod_cast hx
  have hy4 : 4 ≤ y := by
    by_contra h; push_neg at h
    have : y ^ 8 < 4 ^ 8 := pow_lt_pow_left₀ h hy0 (by norm_num)
    rw [hy8] at this; norm_num at this; linarith
  set z := ⌊y⌋₊
  have hzle : (z : ℝ) ≤ y := Nat.floor_le hy0
  have hzgt : y < z + 1 := Nat.lt_floor_add_one y
  have hz3 : (3 : ℝ) < z := by linarith
  have hz2 : 2 ≤ z := by
    have : (2 : ℝ) < z := by linarith
    exact_mod_cast this.le
  have hzpos : (0 : ℝ) < z := by linarith
  have hlogx : Real.log x = 8 * Real.log y := by
    rw [← hy8, Real.log_pow]; norm_num
  have hlogy : Real.log y ≤ y := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  refine ⟨z, hz2, ?_, ?_⟩
  · have h1 : (z : ℝ) + (z : ℝ) ^ 4 ≤ 2 * y ^ 4 := by
      have : (z : ℝ) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hzpos.le hzle 4
      have : y ≤ y ^ 4 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) ≤ y) 3]
      linarith
    have h2 : Real.log x ^ 2 ≤ 64 * y ^ 2 := by
      rw [hlogx]; nlinarith
    have h3 : (16 : ℝ) ≤ y ^ 2 := by nlinarith
    have h4 : 0 ≤ Real.log x ^ 2 := sq_nonneg _
    calc ((z : ℝ) + (z : ℝ) ^ 4) * Real.log x ^ 2 ≤ (2 * y ^ 4) * (64 * y ^ 2) := by
          apply mul_le_mul h1 h2 h4 (by positivity)
      _ = 128 * (y ^ 4 * y ^ 2) := by ring
      _ ≤ 8 * (y ^ 4 * y ^ 2 * y ^ 2) := by nlinarith [pow_nonneg hy0 4, pow_nonneg hy0 2]
      _ = 8 * y ^ 8 := by ring
      _ ≤ 32 * x := by rw [hy8]; linarith
  · have hzy : y / 2 ≤ z := by linarith
    have h1 : Real.log (y / 2) ≤ Real.log z := Real.log_le_log (by linarith) hzy
    rw [Real.log_div (by linarith) (by norm_num)] at h1
    have h2 : Real.log 4 ≤ Real.log y := Real.log_le_log (by norm_num) hy4
    have h3 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [hlogx]; linarith

/-- The singular-series factor `Π_{p ∣ d, p > 2} (1 + 1/p)` of the prime-pair bound. -/
noncomputable def pairSingularProduct (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors with 2 < p, (1 + 1 / (p : ℝ))

theorem one_le_pairSingularProduct (d : ℕ) : 1 ≤ pairSingularProduct d := by
  unfold pairSingularProduct
  have := prod_le_prod (s := d.primeFactors.filter (fun p => 2 < p)) (f := fun _ : ℕ => (1 : ℝ))
    (g := fun p : ℕ => 1 + 1 / (p : ℝ)) (fun _ _ => zero_le_one)
    (fun p _ => by
      have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
      linarith)
  simpa using this

/-- **Mertens-type input for the prime-pair sieve** (an explicit hypothesis, to be discharged
by a Mertens library): `c log² z ≤ G_d(z) · Π_{p ∣ d, p > 2} (1 + 1/p)` for all even `d > 0`
and all `z ≥ 2`. Classically this holds for some absolute `c > 0`. -/
def PairGLowerBound (c : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → Even d → ∀ z : ℕ, 2 ≤ z →
    c * Real.log z ^ 2 ≤ pairG d z * pairSingularProduct d

/-- **Upper bound for prime pairs with a given difference (Romanoff-ready).**
Given the Mertens-type lower bound `PairGLowerBound c`, there is an absolute `C` such that for
every even `d > 0` and every `x ≥ 2`,
`#{p ≤ x : p and p + d prime} ≤ C · x / log² x · Π_{p ∣ d, p > 2} (1 + 1/p)`. -/
theorem prime_pairs_upper_bound {c : ℝ} (hc : 0 < c) (hG : PairGLowerBound c) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → Even d → ∀ x : ℕ, 2 ≤ x →
      (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
        ≤ C * ((x : ℝ) / Real.log x ^ 2) * pairSingularProduct d := by
  refine ⟨320 + 512 / c, by positivity, fun d hd0 hd x hx => ?_⟩
  set PP := pairSingularProduct d
  have hPP : 1 ≤ PP := one_le_pairSingularProduct d
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hL2 : 0 < Real.log x ^ 2 := by positivity
  set cnt := (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
  have hcnt0 : cnt ≤ x + 1 := by
    have := card_filter_le (range (x + 1)) (fun p => p.Prime ∧ (p + d).Prime)
    rw [card_range] at this
    simp only [cnt]; exact_mod_cast this
  by_cases hbig : 65536 ≤ x
  · obtain ⟨z, hz2, hzrem, hlogz⟩ := exists_level x hbig
    have hs := card_prime_pairs_le_sieve d x z hd hz2
    have hGz := hG d hd0 hd z hz2
    have hGpos : 0 < pairG d z := by
      have := one_le_selbergG (Q := Nat.primesBelow z)
        (g := fun p => (pairOmega d p : ℝ) / p) (D := levelFamily (Nat.primesBelow z) z)
        (fun p hp => div_pos (by exact_mod_cast pairOmega_pos d p)
          (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos))
        (fun p hp => by
          have hp' := (Nat.mem_primesBelow.mp hp).2
          rw [div_lt_one (by exact_mod_cast hp'.pos)]; exact_mod_cast pairOmega_lt hd hp')
        levelFamily_subset (empty_mem_levelFamily hz2)
      unfold pairG; linarith
    have hlz : Real.log x ^ 2 ≤ 256 * Real.log z ^ 2 := by nlinarith
    have hlz0 : 0 < Real.log z ^ 2 := by nlinarith
    -- main term
    have hmain : ((x : ℝ) + 1) / pairG d z ≤ (512 / c) * ((x : ℝ) / Real.log x ^ 2) * PP := by
      rw [div_le_iff₀ hGpos]
      have e : (512 / c) * ((x : ℝ) / Real.log x ^ 2) * PP * pairG d z
          = (512 * x) / (c * Real.log x ^ 2) * (pairG d z * PP) := by
        field_simp
      rw [e]
      have h1 : (512 * (x : ℝ)) / (c * Real.log x ^ 2) * (c * Real.log z ^ 2)
          ≤ (512 * x) / (c * Real.log x ^ 2) * (pairG d z * PP) :=
        mul_le_mul_of_nonneg_left hGz (by positivity)
      refine le_trans ?_ h1
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have k1 : ((x : ℝ) + 1) * Real.log x ^ 2 ≤ (2 * x) * (256 * Real.log z ^ 2) :=
        mul_le_mul (by linarith) hlz hL2.le (by linarith)
      have k2 := mul_le_mul_of_nonneg_left k1 hc.le
      nlinarith
    have hrem : (z : ℝ) + (z : ℝ) ^ 4 ≤ 32 * ((x : ℝ) / Real.log x ^ 2) * PP := by
      have : (z : ℝ) + (z : ℝ) ^ 4 ≤ 32 * ((x : ℝ) / Real.log x ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ hL2]; exact hzrem
      have h0 : 0 ≤ 32 * ((x : ℝ) / Real.log x ^ 2) := by positivity
      nlinarith
    have h0 : 0 ≤ ((x : ℝ) / Real.log x ^ 2) * PP := by positivity
    calc cnt ≤ z + (x + 1) / pairG d z + (z : ℝ) ^ 4 := hs
      _ ≤ 32 * ((x : ℝ) / Real.log x ^ 2) * PP + (512 / c) * ((x : ℝ) / Real.log x ^ 2) * PP := by
        linarith
      _ ≤ (320 + 512 / c) * ((x : ℝ) / Real.log x ^ 2) * PP := by nlinarith
  · push_neg at hbig
    have hxs : (x : ℝ) < 65536 := by exact_mod_cast hbig
    have hlog : Real.log x < 12 := by
      have h1 : Real.log x < Real.log 65536 := Real.log_lt_log (by linarith) hxs
      have h2 : Real.log (65536 : ℝ) = 16 * Real.log 2 := by
        rw [show (65536 : ℝ) = 2 ^ 16 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9
      linarith
    have hLsq : Real.log x ^ 2 ≤ 144 := by nlinarith
    have h1 : cnt ≤ 288 * ((x : ℝ) / Real.log x ^ 2) := by
      rw [mul_div_assoc', le_div_iff₀ hL2]; nlinarith
    have h0 : 0 ≤ ((x : ℝ) / Real.log x ^ 2) := by positivity
    have h2 : 0 ≤ 512 / c * ((x : ℝ) / Real.log x ^ 2) * PP := by positivity
    nlinarith

/-! ## Brun–Titchmarsh -/

/-- The sieving primes for an arithmetic progression modulo `q`: primes `< z` not dividing `q`. -/
noncomputable def apPrimes (q z : ℕ) : Finset ℕ := (Nat.primesBelow z).filter (fun p => ¬ p ∣ q)

/-- Selberg's `G(z)` for an arithmetic progression modulo `q`:
`Σ_{m < z, m ∣ P(z), (m, q) = 1} Π_{p ∣ m} 1/(p - 1)`. -/
noncomputable def apG (q z : ℕ) : ℝ :=
  selbergG (fun p : ℕ => (1 : ℝ) / p) (levelFamily (apPrimes q z) z)

/-- The local condition of the progression sieve: `p ∣ b + q t`. -/
def apCond (b q : ℕ) (p t : ℕ) : Prop := p ∣ b + q * t

theorem apCond_periodic (b q p t : ℕ) : apCond b q p t ↔ apCond b q p (t % p) := by
  unfold apCond
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

theorem omega_apCond {b q p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) : omega (apCond b q) p = 1 := by
  unfold omega apCond
  have hcop : Nat.Coprime q p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq).symm
  have := card_filter_range_shift (fun u => p ∣ u) hp.pos hcop
    (fun n => by simp only [Nat.dvd_iff_mod_eq_zero, Nat.mod_mod]) b
  have h0 : (range p).filter (fun u => p ∣ u) = {0} := by
    ext u; simp only [mem_filter, mem_range, mem_singleton]
    exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h.2 h.1, fun h => h ▸ ⟨hp.pos, dvd_zero p⟩⟩
  have h2 : ((range p).filter (fun u => p ∣ u)).card = 1 := by rw [h0, card_singleton]
  convert this.trans h2 using 2
  ext t; simp

/-- **Brun–Titchmarsh, explicit sieve form.** For `q ≥ 1`, any `a`, `x` and level `z ≥ 2`,
the number of primes `p ≤ x` with `p ≡ a [MOD q]` is at most
`z + (x / q + 1) / G_q(z) + z ^ 4`. -/
theorem card_primes_ap_le_sieve (q a x z : ℕ) (hq : 0 < q) (hz : 2 ≤ z) :
    (((range (x + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])).card : ℝ)
      ≤ z + ((x / q + 1 : ℕ) : ℝ) / apG q z + (z : ℝ) ^ 4 := by
  set b := a % q
  set Q := apPrimes q z
  have hQ : ∀ p ∈ Q, p.Prime := fun p hp =>
    (Nat.mem_primesBelow.mp (mem_filter.mp hp).1).2
  have hQq : ∀ p ∈ Q, ¬ p ∣ q := fun p hp => (mem_filter.mp hp).2
  have hω0 : ∀ p ∈ Q, 0 < omega (apCond b q) p := fun p hp => by
    rw [omega_apCond (hQ p hp) (hQq p hp)]; norm_num
  have hω1 : ∀ p ∈ Q, omega (apCond b q) p < p := fun p hp => by
    rw [omega_apCond (hQ p hp) (hQq p hp)]; exact (hQ p hp).one_lt
  have hsieve := selberg_residue_level (x / q + 1) z hz Q hQ (apCond b q) (apCond_periodic b q)
    hω0 hω1
  have hG : selbergG (fun p => (omega (apCond b q) p : ℝ) / p) (levelFamily Q z) = apG q z := by
    show _ = selbergG (fun p : ℕ => (1 : ℝ) / p) (levelFamily Q z)
    refine selbergG_congr levelFamily_subset fun p hp => ?_
    rw [omega_apCond (hQ p hp) (hQq p hp)]; norm_num
  rw [hG] at hsieve
  set P := (range (x + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q])
  have hsplit : P.card ≤ (P.filter (fun p => p < z)).card + (P.filter (fun p => ¬ p < z)).card := by
    rw [card_filter_add_card_filter_not]
  have h1 : (P.filter (fun p => p < z)).card ≤ z := by
    have := card_le_card (s := P.filter (fun p => p < z)) (t := range z)
      (fun p hp => mem_range.mpr (mem_filter.mp hp).2)
    simpa using this
  have h2 : (P.filter (fun p => ¬ p < z)).card
      ≤ ((range (x / q + 1)).filter (fun t => ∀ p ∈ Q, ¬ apCond b q p t)).card := by
    refine card_le_card_of_injOn (fun n => n / q) ?_ ?_
    · intro n hn
      simp only [P, coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at hn
      simp only [coe_filter, mem_range, Set.mem_setOf_eq]
      have hnb : n % q = b := hn.1.2.2
      have hdecomp : b + q * (n / q) = n := by rw [← hnb]; exact Nat.mod_add_div n q
      refine ⟨Nat.lt_succ_of_le (Nat.div_le_div_right (by omega)), fun p hp hdiv => ?_⟩
      unfold apCond at hdiv
      rw [hdecomp] at hdiv
      have hp' := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
      have := (Nat.prime_dvd_prime_iff_eq hp'.2 hn.1.2.1).mp hdiv
      omega
    · intro n hn m hm h
      simp only [P, coe_filter, mem_filter, mem_range, Set.mem_setOf_eq] at hn hm
      simp only at h
      have e1 : n % q = m % q := hn.1.2.2.trans hm.1.2.2.symm
      rw [← Nat.mod_add_div n q, ← Nat.mod_add_div m q, e1, h]
  have hcard : (P.card : ℝ) ≤ z
      + (((range (x / q + 1)).filter (fun t => ∀ p ∈ Q, ¬ apCond b q p t)).card : ℝ) := by
    exact_mod_cast hsplit.trans (Nat.add_le_add h1 h2)
  linarith

/-! ## A lower bound for `G` (Rankin's trick) -/

/-- **Rankin lower bound for Selberg's `G`.** If `Q ⊆ Qbig` consists of primes and `h ≥ 0`
on `Qbig`, then for every `ε ≥ 0`,
`Π_{p∈Q} (1 + h p) - z^{-ε} Π_{p∈Q} (1 + h p · p^ε) ≤ G` (support `levelFamily Qbig z`). -/
theorem selbergG_ge_rankin (g : ℕ → ℝ) (Q Qbig : Finset ℕ) (hQQ : Q ⊆ Qbig)
    (hQ : ∀ p ∈ Q, p.Prime) (hh : ∀ p ∈ Qbig, 0 ≤ hFun g p) (z : ℕ) (hz : 1 ≤ z)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∏ p ∈ Q, (1 + hFun g p) - (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + hFun g p * (p : ℝ) ^ ε)
      ≤ selbergG g (levelFamily Qbig z) := by
  have hzR : (1 : ℝ) ≤ z := by exact_mod_cast hz
  have hz0 : (0 : ℝ) < z := by linarith
  have hnn : ∀ S ∈ Q.powerset, 0 ≤ ∏ p ∈ S, hFun g p := fun S hS =>
    prod_nonneg fun p hp => hh p (hQQ (mem_powerset.mp hS hp))
  rw [prod_one_add, prod_one_add]
  rw [← sum_filter_add_sum_filter_not Q.powerset (fun S => ∏ p ∈ S, p < z)]
  have h1 : ∑ S ∈ Q.powerset with ∏ p ∈ S, p < z, ∏ p ∈ S, hFun g p
      ≤ selbergG g (levelFamily Qbig z) := by
    unfold selbergG
    apply sum_le_sum_of_subset_of_nonneg
    · intro S hS
      simp only [mem_filter, mem_powerset] at hS
      simp only [levelFamily, mem_filter, mem_powerset]
      exact ⟨hS.1.trans hQQ, hS.2⟩
    · intro S hS _
      simp only [levelFamily, mem_filter, mem_powerset] at hS
      exact prod_nonneg fun p hp => hh p (hS.1 hp)
  have h2 : ∑ S ∈ Q.powerset with ¬ ∏ p ∈ S, p < z, ∏ p ∈ S, hFun g p
      ≤ (z : ℝ) ^ (-ε) * ∑ S ∈ Q.powerset, ∏ p ∈ S, hFun g p * (p : ℝ) ^ ε := by
    rw [mul_sum]
    refine (sum_le_sum_of_subset_of_nonneg (filter_subset (fun S : Finset ℕ => ¬ ∏ p ∈ S, p < z) Q.powerset) ?_).trans' ?_
    · intro S hS _
      have := hnn S hS
      rw [prod_mul_distrib]
      exact mul_nonneg (Real.rpow_nonneg hz0.le _)
        (mul_nonneg this (prod_nonneg fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _))
    · refine sum_le_sum fun S hS => ?_
      simp only [mem_filter, not_lt] at hS
      have hpos := hnn S hS.1
      rw [prod_mul_distrib, Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p)]
      have hge : (z : ℝ) ^ ε ≤ (∏ p ∈ S, (p : ℝ)) ^ ε := by
        apply Real.rpow_le_rpow hz0.le _ hε
        have := hS.2
        rw [← Nat.cast_prod]; exact_mod_cast this
      have hzz : (z : ℝ) ^ (-ε) * (z : ℝ) ^ ε = 1 := by
        rw [Real.rpow_neg hz0.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hz0 ε).ne']
      have : 1 ≤ (z : ℝ) ^ (-ε) * (∏ p ∈ S, (p : ℝ)) ^ ε := by
        rw [← hzz]
        exact mul_le_mul_of_nonneg_left hge (Real.rpow_nonneg hz0.le _)
      nlinarith
  linarith

/-- Weierstrass product inequality: `Π (1 - a i) ≥ 1 - Σ a i` for `0 ≤ a i ≤ 1`. -/
theorem one_sub_sum_le_prod (s : Finset ℕ) (a : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have a0 := h0 j (mem_insert_self j s); have a1 := h1 j (mem_insert_self j s)
    have hP : 0 ≤ ∏ i ∈ s, (1 - a i) :=
      prod_nonneg fun i hi => by linarith [h1 i (mem_insert_of_mem hi)]
    have hS : 0 ≤ ∑ i ∈ s, a i := sum_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    nlinarith

theorem sum_Icc_three_inv_sq_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Icc 3 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / 2 - 1 / N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : (1 : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / N - 1 / ((N + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith
    linarith

/-- `Π_{p ∣ d, p > 2} (1 - 1/p) · Π_{p ∣ d, p > 2} (1 + 1/p) ≥ 1/2`. -/
theorem prod_odd_one_sub_mul_ge (d : ℕ) (hd : 0 < d) :
    1 / 2 ≤ (∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ))) * pairSingularProduct d := by
  unfold pairSingularProduct
  set T := d.primeFactors.filter (fun p => 2 < p)
  rw [← prod_mul_distrib]
  have e : ∀ p ∈ T, (1 - 1 / (p : ℝ)) * (1 + 1 / p) = 1 - 1 / (p : ℝ) ^ 2 := by
    intro p _; ring
  rw [prod_congr rfl e]
  have hT : ∀ p ∈ T, 3 ≤ p := fun p hp => (mem_filter.mp hp).2
  refine le_trans ?_ (one_sub_sum_le_prod T _ (fun p _ => by positivity) (fun p hp => by
    have : (3 : ℝ) ≤ p := by exact_mod_cast hT p hp
    rw [div_le_one (by positivity)]; nlinarith))
  have hsub : T ⊆ Icc 3 d := fun p hp => by
    have h1 := hT p hp
    have h2 : p ≤ d := Nat.le_of_dvd hd (Nat.dvd_of_mem_primeFactors (mem_filter.mp hp).1)
    exact mem_Icc.mpr ⟨h1, h2⟩
  have hle : ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ∑ n ∈ Icc 3 d, (1 : ℝ) / (n : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  rcases lt_or_ge d 2 with h | h
  · have : T = ∅ := by
      ext p; simp only [notMem_empty, iff_false]; intro hp
      have := hsub hp; simp at this; omega
    simp [this]; norm_num
  · have := sum_Icc_three_inv_sq_le d h
    have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
    linarith

theorem pair_hFun (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    hFun (fun p => (pairOmega d p : ℝ) / p) p
      = (pairOmega d p : ℝ) / ((p : ℝ) - pairOmega d p) := by
  have hlt : (pairOmega d p : ℝ) < p := by exact_mod_cast pairOmega_lt hd hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold hFun
  have : (p : ℝ) - pairOmega d p ≠ 0 := by linarith
  field_simp

theorem pair_hFun_nonneg (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    0 ≤ hFun (fun p => (pairOmega d p : ℝ) / p) p := by
  rw [pair_hFun d hd hp]
  have hlt : (pairOmega d p : ℝ) < p := by exact_mod_cast pairOmega_lt hd hp
  exact div_nonneg (Nat.cast_nonneg _) (by linarith)

theorem pair_hFun_le (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    hFun (fun p => (pairOmega d p : ℝ) / p) p ≤ 6 / p := by
  rw [pair_hFun d hd hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold pairOmega
  split_ifs with h
  · push_cast
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    push_cast
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith

theorem pair_one_add_hFun_ge (d : ℕ) {p : ℕ} (hd : Even d) (hp : p.Prime) :
    (1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ d then 1 - 1 / (p : ℝ) else 1)
      ≤ 1 + hFun (fun p => (pairOmega d p : ℝ) / p) p := by
  rw [pair_hFun d hd hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have e : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
  rw [e, inv_div]
  unfold pairOmega
  split_ifs with h
  · push_cast
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    rw [div_pow, div_mul_div_comm, div_le_iff₀ (by positivity)]
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp; nlinarith
  · have h2 : p ≠ 2 := by rintro rfl; exact h (even_iff_two_dvd.mp hd)
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
    push_cast
    rw [mul_one, div_pow, div_le_iff₀ (by nlinarith)]
    have : (p : ℝ) - 2 ≠ 0 := by linarith
    rw [show (1 : ℝ) + 2 / ((p : ℝ) - 2) = p / ((p : ℝ) - 2) by field_simp; ring]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith

/-- Rankin step for the prime-pair sieve: with `Y ≤ z^{1/37}`, `G_d(z) ≥ ½ Π_{p ≤ Y} (1 + h(p))`. -/
theorem pair_rankin_half (d z Y : ℕ) (hd : Even d) (hY3 : 3 ≤ Y) (hYz : Y < z)
    (hlYup : Real.log Y ≤ Real.log z / 37)
    (hM1 : ∀ N : ℕ, ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4) :
    (1 / 2) * ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (pairOmega d p : ℝ) / p) p)
      ≤ pairG d z := by
  set g : ℕ → ℝ := fun p => (pairOmega d p : ℝ) / p
  have hYR : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast (show 2 ≤ z by omega)

  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hQQ : Q ⊆ Nat.primesBelow z := fun p hp => by
    have := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, this.2⟩
  set ε : ℝ := 1 / Real.log Y
  have hε : 0 ≤ ε := by positivity
  have hrank := selbergG_ge_rankin g Q (Nat.primesBelow z) hQQ hQp
    (fun p hp => pair_hFun_nonneg d hd (Nat.mem_primesBelow.mp hp).2) z (by omega) hε
  change _ ≤ pairG d z at hrank
  set H : ℕ → ℝ := fun p => hFun g p
  have hH0 : ∀ p ∈ Q, 0 ≤ H p := fun p hp => pair_hFun_nonneg d hd (hQp p hp)
  -- the Rankin tail
  have hpe : ∀ p ∈ Q, (p : ℝ) ^ ε - 1 ≤ 2 * (Real.log p / Real.log Y) := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have hlpY : Real.log p ≤ Real.log Y :=
      Real.log_le_log (by linarith) (by exact_mod_cast (Nat.mem_primesLE.mp hp).1)
    have ht : |Real.log p * ε| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      simp only [ε]; rw [mul_one_div, div_le_one hlY]; exact hlpY
    rw [Real.rpow_def_of_pos (by linarith)]
    have := (abs_le.mp (Real.abs_exp_sub_one_le ht)).2
    rw [abs_of_nonneg (by positivity)] at this
    have e : Real.log p * ε = Real.log p / Real.log Y := by simp only [ε]; ring
    rw [← e]; exact this
  have hsumtail : ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1) ≤ 36 := by
    calc ∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1)
        ≤ ∑ p ∈ Q, (6 / (p : ℝ)) * (2 * (Real.log p / Real.log Y)) := by
          refine sum_le_sum fun p hp => ?_
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
          have : (0 : ℝ) ≤ (p : ℝ) ^ ε - 1 := by
            have := Real.one_le_rpow hp1 hε; linarith
          exact mul_le_mul (pair_hFun_le d hd (hQp p hp)) (hpe p hp) this (by positivity)
      _ = (12 / Real.log Y) * ∑ p ∈ Q, Real.log p / p := by
          rw [mul_sum]; refine sum_congr rfl fun p _ => by ring
      _ ≤ (12 / Real.log Y) * (Real.log Y + Real.log 4) :=
          mul_le_mul_of_nonneg_left (hM1 Y) (by positivity)
      _ ≤ 36 := by
          have h4 : Real.log 4 ≤ 2 * Real.log Y := by
            have : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
            have : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) (by linarith)
            linarith
          rw [div_mul_eq_mul_div, div_le_iff₀ hlY]; nlinarith
  have hprod_tail : ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
      ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 36 := by
    calc ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
        ≤ ∏ p ∈ Q, ((1 + H p) * Real.exp (H p * ((p : ℝ) ^ ε - 1))) := by
          refine prod_le_prod (fun p hp => by
            have := hH0 p hp; positivity) fun p hp => ?_
          have h0 := hH0 p hp
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
          have hb : 1 ≤ (p : ℝ) ^ ε := Real.one_le_rpow hp1 hε
          have := Real.add_one_le_exp (H p * ((p : ℝ) ^ ε - 1))
          nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ (p : ℝ) ^ ε - 1)]
      _ = (∏ p ∈ Q, (1 + H p)) * Real.exp (∑ p ∈ Q, H p * ((p : ℝ) ^ ε - 1)) := by
          rw [prod_mul_distrib, Real.exp_sum]
      _ ≤ (∏ p ∈ Q, (1 + H p)) * Real.exp 36 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsumtail)
            (prod_nonneg fun p hp => by have := hH0 p hp; linarith)
  have hzeps : (z : ℝ) ^ (-ε) ≤ Real.exp (-37) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp]
    simp only [ε]
    rw [mul_neg, mul_one_div, neg_le_neg_iff, le_div_iff₀ hlY]; linarith
  have hP0 : 0 ≤ ∏ p ∈ Q, (1 + H p) := prod_nonneg fun p hp => by have := hH0 p hp; linarith
  have hhalf : (1 / 2) * ∏ p ∈ Q, (1 + H p) ≤ pairG d z := by
    have he : Real.exp (-37) * Real.exp 36 ≤ 1 / 2 := by
      rw [← Real.exp_add]; norm_num
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
    have ht : (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
        ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := by
      calc (z : ℝ) ^ (-ε) * ∏ p ∈ Q, (1 + H p * (p : ℝ) ^ ε)
          ≤ Real.exp (-37) * ((∏ p ∈ Q, (1 + H p)) * Real.exp 36) :=
            mul_le_mul hzeps hprod_tail (prod_nonneg fun p hp => by
              have := hH0 p hp; positivity) (Real.exp_pos _).le
        _ = (Real.exp (-37) * Real.exp 36) * ∏ p ∈ Q, (1 + H p) := by ring
        _ ≤ (1 / 2) * ∏ p ∈ Q, (1 + H p) := mul_le_mul_of_nonneg_right he hP0
    linarith
  exact hhalf

/-- Euler-product lower bound: `Π_{p ≤ Y} (1 + h(p)) ≥ (Π_{p ≤ Y} (1 - 1/p))⁻² Π_{p ∣ d} (1 - 1/p)`. -/
theorem pair_euler_ge (d Y : ℕ) (hd0 : 0 < d) (hd : Even d) :
    ((∏ p ∈ Nat.primesLE Y, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 * ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ Nat.primesLE Y, (1 + hFun (fun p => (pairOmega d p : ℝ) / p) p) := by
  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  set H : ℕ → ℝ := fun p => hFun (fun p => (pairOmega d p : ℝ) / p) p

  -- Mertens lower bound for the Euler product
  have hE : ((∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 * ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      ≤ ∏ p ∈ Q, (1 + H p) := by
    have hf : ∀ p ∈ Q, 0 ≤ 1 - 1 / (p : ℝ) := fun p hp => by
      have : (1 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).one_lt.le
      rw [sub_nonneg, div_le_one (by linarith)]; exact this
    have step1 : ∏ p ∈ Q, ((1 - 1 / (p : ℝ))⁻¹ ^ 2 * (if p ∣ d then 1 - 1 / (p : ℝ) else 1))
        ≤ ∏ p ∈ Q, (1 + H p) :=
      prod_le_prod (fun p hp => by
        have := hf p hp
        split_ifs <;> positivity) fun p hp => pair_one_add_hFun_ge d hd (hQp p hp)
    rw [prod_mul_distrib, prod_pow, prod_inv_distrib] at step1
    refine le_trans ?_ step1
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← prod_filter]
    have hsub : Q.filter (fun p => p ∣ d) ⊆ d.primeFactors := fun p hp => by
      simp only [mem_filter] at hp
      exact Nat.mem_primeFactors.mpr ⟨hQp p hp.1, hp.2, hd0.ne'⟩
    rw [← prod_sdiff hsub]
    have h0 : 0 ≤ ∏ p ∈ Q.filter (fun p => p ∣ d), (1 - 1 / (p : ℝ)) :=
      prod_nonneg fun p hp => hf p (mem_filter.mp hp).1
    have h1 : ∏ p ∈ d.primeFactors \ Q.filter (fun p => p ∣ d), (1 - 1 / (p : ℝ)) ≤ 1 := by
      refine prod_le_one (fun p hp => ?_) (fun p hp => ?_)
      · have hp' := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
        rw [sub_nonneg, div_le_one (by linarith)]; exact this
      · have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
        linarith
    nlinarith
  exact hE

/-- **Discharging `PairGLowerBound` from Mertens' theorems.** The inputs are Mertens' first
theorem (upper half) and the upper half of Mertens' product theorem, in exactly the form proved
in `OMALib.Mertens` (`sum_log_div_le_nat`, `prod_one_sub_inv_bounds`). -/
theorem pairGLowerBound_of_mertens {M : ℝ} (hM : 0 < M)
    (hM1 : ∀ N : ℕ, ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4)
    (hM3 : ∀ N : ℕ, 2 ≤ N → ∏ p ∈ Nat.primesLE N, (1 - 1 / (p : ℝ)) ≤ M / Real.log N) :
    PairGLowerBound (min (1 / 2700) (1 / (43808 * M ^ 2))) := by
  intro d hd0 hd z hz
  set g : ℕ → ℝ := fun p => (pairOmega d p : ℝ) / p
  have hgQ0 : ∀ p ∈ Nat.primesBelow z, 0 < g p := fun p hp =>
    div_pos (by exact_mod_cast pairOmega_pos d p)
      (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos)
  have hgQ1 : ∀ p ∈ Nat.primesBelow z, g p < 1 := fun p hp => by
    have hp' := (Nat.mem_primesBelow.mp hp).2
    simp only [g]; rw [div_lt_one (by exact_mod_cast hp'.pos)]; exact_mod_cast pairOmega_lt hd hp'
  have hG1 : 1 ≤ pairG d z :=
    one_le_selbergG hgQ0 hgQ1 levelFamily_subset (empty_mem_levelFamily hz)
  have hPP := one_le_pairSingularProduct d
  have hzR : (2 : ℝ) ≤ z := by exact_mod_cast hz
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmin1 : min (1 / 2700) (1 / (43808 * M ^ 2)) ≤ 1 / 2700 := min_le_left _ _
  have hmin2 : min (1 / 2700) (1 / (43808 * M ^ 2)) ≤ 1 / (43808 * M ^ 2) := min_le_right _ _
  have hmin0 : 0 < min (1 / 2700) (1 / (43808 * M ^ 2)) := lt_min (by norm_num) (by positivity)
  set c := min (1 / 2700) (1 / (43808 * M ^ 2))
  have hGP : 1 ≤ pairG d z * pairSingularProduct d := by nlinarith
  by_cases hbig : 74 * Real.log 2 ≤ Real.log z
  swap
  · push_neg at hbig
    have : Real.log z ^ 2 ≤ 2700 := by nlinarith
    calc c * Real.log z ^ 2 ≤ (1 / 2700) * 2700 := by
          apply mul_le_mul hmin1 this (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num
      _ ≤ _ := hGP
  -- large z
  set y : ℝ := (z : ℝ) ^ ((1 : ℝ) / 37) with hydef
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by linarith) _
  have hlogy : Real.log y = Real.log z / 37 := by
    rw [hydef, Real.log_rpow (by linarith)]; ring
  have hy4 : Real.log 4 ≤ Real.log y := by
    rw [hlogy, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hy4' : 4 ≤ y := by
    have := Real.exp_le_exp.mpr hy4
    rwa [Real.exp_log (by norm_num), Real.exp_log hy0] at this
  set Y := ⌊y⌋₊
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hYgt : y < Y + 1 := Nat.lt_floor_add_one y
  have hY3 : 3 ≤ Y := by
    have : (3 : ℝ) < Y := by linarith
    exact_mod_cast this.le
  have hYR : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlYup : Real.log Y ≤ Real.log z / 37 := by
    rw [← hlogy]; exact Real.log_le_log (by linarith) hYle
  have hlYlo : Real.log z / 74 ≤ Real.log Y := by
    have h1 : Real.log (y / 2) ≤ Real.log Y := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_div hy0.ne' (by norm_num), hlogy] at h1
    linarith
  have hYz : Y < z := by
    have h1 : Real.log Y < Real.log z := by linarith
    have := (Real.log_lt_log_iff (by linarith) (by linarith)).mp h1
    exact_mod_cast this
  set Q := Nat.primesLE Y
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  set H : ℕ → ℝ := fun p => hFun g p
  have hhalf := pair_rankin_half d z Y hd hY3 hYz hlYup hM1
  have hE := pair_euler_ge d Y hd0 hd
  have hM3Y := hM3 Y (by omega)
  have hQpos : 0 < ∏ p ∈ Q, (1 - 1 / (p : ℝ)) := prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hQp p hp).two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
    linarith
  have hinv : Real.log Y / M ≤ (∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hQpos, inv_div]; exact hM3Y
  -- the factor at the primes dividing d
  have h2d : 2 ∈ d.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.prime_two, even_iff_two_dvd.mp hd, hd0.ne'⟩
  have hsplit2 : ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
      = (1 / 2) * ∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ)) := by
    have : d.primeFactors.filter (fun p => 2 < p) = d.primeFactors.erase 2 := by
      ext p; simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, by have := (Nat.prime_of_mem_primeFactors h2).two_le; omega⟩
    rw [this, ← mul_prod_erase _ _ h2d]; norm_num
  have hodd := prod_odd_one_sub_mul_ge d hd0
  have hD : 1 / 4 ≤ (∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))) * pairSingularProduct d := by
    rw [hsplit2]
    have : 1 / 2 * (∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ))) * pairSingularProduct d
        = 1 / 2 * ((∏ p ∈ d.primeFactors with 2 < p, (1 - 1 / (p : ℝ))) * pairSingularProduct d) := by
      ring
    linarith
  -- assemble
  have hY2 : (Real.log z / 74) ^ 2 / M ^ 2 ≤ ((∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹) ^ 2 := by
    have : Real.log z / 74 / M ≤ (∏ p ∈ Q, (1 - 1 / (p : ℝ)))⁻¹ :=
      le_trans (div_le_div_of_nonneg_right hlYlo hM.le) hinv
    rw [← div_pow]; exact pow_le_pow_left₀ (by positivity) this 2
  have hDpos : 0 ≤ ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ)) := prod_nonneg fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [sub_nonneg, div_le_one (by linarith)]; exact this
  have hfinal : (Real.log z / 74) ^ 2 / M ^ 2 * (1 / 8) ≤ pairG d z * pairSingularProduct d := by
    set A := (Real.log z / 74) ^ 2 / M ^ 2
    set P := ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ))
    set E := ∏ p ∈ Q, (1 + H p)
    set PP := pairSingularProduct d
    have hA0 : 0 ≤ A := by positivity
    have hPP0 : 0 ≤ PP := by linarith
    have a1 : A * P ≤ E := le_trans (mul_le_mul_of_nonneg_right hY2 hDpos) hE
    have a2 : A * (1 / 4) ≤ A * (P * PP) := mul_le_mul_of_nonneg_left hD hA0
    have a3 : A * P * PP ≤ E * PP := mul_le_mul_of_nonneg_right a1 hPP0
    have a4 : 1 / 2 * E * PP ≤ pairG d z * PP := mul_le_mul_of_nonneg_right hhalf hPP0
    have e1 : A * P * PP = A * (P * PP) := by ring
    have e2 : 1 / 2 * E * PP = 1 / 2 * (E * PP) := by ring
    linarith
  have hc : c * Real.log z ^ 2 ≤ (Real.log z / 74) ^ 2 / M ^ 2 * (1 / 8) := by
    have : (Real.log z / 74) ^ 2 / M ^ 2 * (1 / 8) = (1 / (43808 * M ^ 2)) * Real.log z ^ 2 := by
      field_simp; ring
    rw [this]; exact mul_le_mul_of_nonneg_right hmin2 (sq_nonneg _)
  linarith

end OMALib.Sieve


/-!
Unconditional prime-pair bound: `Sieve.lean` combined with `Mertens.lean`.

This file is meant to be appended after the contents of `Mertens.lean` (namespace
`OMALib.Mertens`) and `Sieve.lean` (namespace `OMALib.Sieve`); it uses
`OMALib.Mertens.sum_log_div_le_nat` and `OMALib.Mertens.prod_one_sub_inv_bounds` to discharge
the Mertens-type hypothesis `OMALib.Sieve.PairGLowerBound`.
-/

open scoped Classical
open Finset

namespace OMALib.Sieve

/-- The Mertens-type input `PairGLowerBound c` holds for an explicit absolute `c > 0`. -/
theorem exists_pairGLowerBound : ∃ c : ℝ, 0 < c ∧ PairGLowerBound c := by
  set M := Real.exp OMALib.Mertens.mertens2Const
  have hM : 0 < M := Real.exp_pos _
  refine ⟨min (1 / 2700) (1 / (43808 * M ^ 2)), lt_min (by norm_num) (by positivity),
    pairGLowerBound_of_mertens hM OMALib.Mertens.sum_log_div_le_nat ?_⟩
  intro N hN
  have h := (OMALib.Mertens.prod_one_sub_inv_bounds (N : ℝ) (by exact_mod_cast hN)).2
  rwa [Nat.floor_natCast] at h

/-- **Upper bound for prime pairs with a given difference, unconditional (Romanoff-ready).**
There is an absolute `C > 0` such that for every even `d > 0` and every `x ≥ 2`,
`#{p ≤ x : p and p + d prime} ≤ C · x / log² x · Π_{p ∣ d, p > 2} (1 + 1/p)`. -/
theorem prime_pairs_upper_bound' :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d → Even d → ∀ x : ℕ, 2 ≤ x →
      (((range (x + 1)).filter (fun p => p.Prime ∧ (p + d).Prime)).card : ℝ)
        ≤ C * ((x : ℝ) / Real.log x ^ 2) * pairSingularProduct d := by
  obtain ⟨c, hc, hG⟩ := exists_pairGLowerBound
  exact prime_pairs_upper_bound hc hG

end OMALib.Sieve
end

section
namespace SmallPrimes

open Finset OMALib.Sieve
open scoped BigOperators

private lemma tot_eq (d : ℕ) :
    (d.totient : ℝ) = d*∏ p ∈ d.primeFactors, (1-1/(p:ℝ)) := by
  have h := congrArg (fun z : ℚ => (z : ℝ)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at h
  simpa [one_div] using h

lemma phi_lower : ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
    c*d ≤ (d.totient:ℝ)*Real.log d := by
  obtain ⟨c,c',hc,_,h⟩ := OMALib.Mertens.mertens3
  refine ⟨c,hc,?_⟩
  intro d hd
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hp := (h d hdR).1
  rw [Nat.floor_natCast] at hp
  have hs : d.primeFactors ⊆ Nat.primesLE d := fun p h => Nat.mem_primesLE.mpr
    ⟨Nat.le_of_mem_primeFactors h,Nat.prime_of_mem_primeFactors h⟩
  have he := hp.trans (Finset.prod_le_prod_of_subset_of_le_one hs (fun p hp => by
    have p2 : (2:ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
    have : 1/(p:ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith) (fun p hp _ => by linarith [show 0 ≤ 1/(p:ℝ) by positivity]))
  have hl : 0 < Real.log (d:ℝ) := Real.log_pos (by linarith)
  have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hl).mp he) (Nat.cast_nonneg d)
  rw [tot_eq]
  linarith only [hh]

lemma weight_phi (d : ℕ) : pairSingularProduct d * d.totient ≤ (d:ℝ) := by
  let g (p : ℕ) := 1+1/(p:ℝ)
  have hg : ∀ p, 1 ≤ g p := fun p => by dsimp [g]; linarith [show 0 ≤ 1/(p:ℝ) by positivity]
  have hle : pairSingularProduct d ≤ ∏ p ∈ d.primeFactors, g p :=
    Finset.prod_le_prod_of_subset_of_one_le (filter_subset _ _)
      (fun p _ => zero_le_one.trans (hg p)) (fun p _ _ => hg p)
  have hlocal (p : ℕ) (hp : p ∈ d.primeFactors) :
      0 ≤ 1-1/(p:ℝ) := by
    have : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
  have hprod : (∏ p ∈ d.primeFactors, g p) * (∏ p ∈ d.primeFactors, (1-1/(p:ℝ))) ≤ 1 := by
    rw [← prod_mul_distrib]
    apply Finset.prod_le_one
    · intro p hp; exact mul_nonneg (zero_le_one.trans (hg p)) (hlocal p hp)
    · intro p _; dsimp [g]; nlinarith [sq_nonneg (1/(p:ℝ))]
  have h' := mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg d.totient)
  rw [tot_eq] at h' ⊢
  nlinarith only [h',mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg d)]

lemma factor_count (d : ℕ) (hd : 0 < d) : (d.primeFactors.card:ℝ) ≤ 2*Real.log d := by
  have h : 2^d.primeFactors.card ≤ d :=
    (Finset.pow_card_le_prod d.primeFactors id 2 (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)).trans
      (Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d))
  have h' := Real.log_le_log (by positivity : (0:ℝ) < 2^d.primeFactors.card)
    (show (2:ℝ)^d.primeFactors.card ≤ d by exact_mod_cast h)
  rw [Real.log_pow] at h'
  nlinarith [mul_nonneg (Nat.cast_nonneg d.primeFactors.card) (show 0 ≤ Real.log 2-1/2 by linarith [Real.log_two_gt_d9])]

lemma weight_mul (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
    pairSingularProduct (k*d) ≤ pairSingularProduct k * pairSingularProduct d := by
  let pf (n : ℕ) := n.primeFactors.filter (2 < ·)
  let g (p : ℕ) : ℝ := 1+1/(p:ℝ)
  have hg (p : ℕ) : 1 ≤ g p := by dsimp [g]; linarith [show (0:ℝ) ≤ 1/p by positivity]
  change ∏ p ∈ pf (k*d), g p ≤ (∏ p ∈ pf k, g p)*(∏ p ∈ pf d, g p)
  have sub : pf (k*d) ⊆ pf k ∪ pf d := by
    intro p hp
    obtain ⟨hp',h2⟩ := mem_filter.mp hp
    obtain ⟨pr,dvd,_⟩ := Nat.mem_primeFactors.mp hp'
    rcases pr.dvd_mul.mp dvd with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pr,h,hk.ne'⟩,h2⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pr,h,hd.ne'⟩,h2⟩)
  refine (Finset.prod_le_prod_of_subset_of_one_le sub (fun p _ => zero_le_one.trans (hg p))
    (fun p _ _ => hg p)).trans ?_
  rw [← Finset.prod_union_inter]
  exact le_mul_of_one_le_right (Finset.prod_nonneg fun p _ => zero_le_one.trans (hg p))
    (Finset.one_le_prod fun p _ => hg p)

private lemma weight_le_sum (k : ℕ) (hk : k ≠ 0) :
    pairSingularProduct k ≤ ∑ a ∈ k.divisors, 1/(a:ℝ) := by
  let S := k.primeFactors.filter (2 < ·)
  let f (T : Finset ℕ) := ∏ p ∈ T, p
  have divs : S.powerset.image f ⊆ k.divisors := by
    intro a ha
    obtain ⟨T,hT,rfl⟩ := mem_image.mp ha
    exact Nat.mem_divisors.mpr ⟨(Finset.prod_dvd_prod_of_subset _ _ _
      ((mem_powerset.mp hT).trans (filter_subset _ _))).trans (Nat.prod_primeFactors_dvd k),hk⟩
  have primes (T : Finset ℕ) (hT : T ∈ S.powerset) : (f T).primeFactors = T :=
    Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors
      (mem_filter.mp (mem_powerset.mp hT hp)).1)
  change (∏ p ∈ S, (1+1/(p:ℝ))) ≤ _
  rw [Finset.prod_one_add]
  calc _ = ∑ a ∈ S.powerset.image f, 1/(a:ℝ) := by
         rw [sum_image (fun T hT U hU he => (primes T hT).symm.trans ((congrArg Nat.primeFactors he).trans (primes U hU)))]
         apply sum_congr rfl
         intro T _
         simp only [f,one_div,Nat.cast_prod,prod_inv_distrib]
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg divs (fun _ _ _ => by positivity)

lemma mean_weight : ∃ B : ℝ, 0 < B ∧ ∀ K : ℕ,
    ∑ k ∈ Ioc 0 K, pairSingularProduct k ≤ B*K := by
  let Z := ∑' a : ℕ, 1/(a:ℝ)^2
  have hZ : Summable fun a : ℕ => 1/(a:ℝ)^2 := Real.summable_one_div_nat_pow.mpr (by decide)
  have hZ0 : 0 ≤ Z := tsum_nonneg fun a => by positivity
  refine ⟨Z+1,by linarith,?_⟩
  intro K
  have hrow (k : ℕ) (hk : k ∈ Ioc 0 K) :
      pairSingularProduct k ≤ ∑ a ∈ Ioc 0 K, (if a ∣ k then 1/(a:ℝ) else 0) := by
    rw [← sum_filter]
    apply (weight_le_sum k (ne_of_gt (mem_Ioc.mp hk).1)).trans
    apply sum_le_sum_of_subset_of_nonneg
    · intro a ha
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors ha,
        (Nat.divisor_le ha).trans (mem_Ioc.mp hk).2⟩,Nat.dvd_of_mem_divisors ha⟩
    · intro a _ _; positivity
  apply (sum_le_sum hrow).trans
  rw [sum_comm]
  calc _ ≤ ∑ a ∈ Ioc 0 K, (K:ℝ)*(1/(a:ℝ)^2) := by
         apply sum_le_sum
         intro a ha
         rw [← sum_filter,sum_const,Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul]
         have ha0 : (0:ℝ) < a := by exact_mod_cast (mem_Ioc.mp ha).1
         calc _ ≤ ((K:ℝ)/a)*(1/(a:ℝ)) :=
                mul_le_mul_of_nonneg_right (Nat.cast_div_le) (by positivity)
              _ = _ := by ring
       _ ≤ (Z+1)*K := by
         rw [← mul_sum]
         have h := hZ.sum_le_tsum (Ioc 0 K) (fun a _ => by positivity)
         nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg K)]

end SmallPrimes
end

section
namespace Freq971
open Finset
def pool (x : ℕ) := (Nat.primesLE x).erase 2
def run (x h : ℕ) := (pool x).filter fun p => p+h∈pool x
def box (x d : ℕ) := ((pool x) ×ˢ (pool x)).filter fun v => v.1<v.2 ∧ v.1%d=v.2%d
def cell (P : Finset ℕ) (d a : ℕ) := P.filter fun p => p%d=a

lemma run_box (x d K : ℕ) (hd : 0<d) (hK : x/d ≤ K) :
    ∑ k∈Ioc 0 K,(run x (k*d)).card = (box x d).card := by
  rw [←card_sigma]
  apply card_bij (fun z _ => (z.2,z.2+z.1*d))
  · rintro ⟨k,p⟩ h
    obtain ⟨hk,hp⟩ := mem_sigma.mp h
    obtain ⟨hp,hq⟩ := mem_filter.mp hp
    have hpos := Nat.mul_pos (mem_Ioc.mp hk).1 hd
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hp,hq⟩,by change p<p+k*d; exact Nat.lt_add_of_pos_right (show 0<k*d from hpos),by simp⟩
  · rintro ⟨k,p⟩ _ ⟨l,q⟩ _ eq
    obtain ⟨rfl,H⟩ := Prod.mk.inj eq
    have E : k=l := Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel H)
    subst l; rfl
  · rintro ⟨p,q⟩ h
    obtain ⟨hpq,hlt,heq⟩ := mem_filter.mp h
    obtain ⟨hp,hq⟩ := mem_product.mp hpq
    obtain ⟨k,hk⟩ := (show p ≡ q [MOD d] from heq).dvd'
    change q-p=d*k at hk
    change p<q at hlt
    have eq : p+k*d=q := by rw [Nat.mul_comm k,←hk]; omega
    have hp0 : 0<k := by by_contra! H; simp [show k=0 by omega] at eq; omega
    have hqx := (Nat.mem_primesLE.mp (mem_of_mem_erase hq)).1
    have hle : k ≤ K := ((Nat.le_div_iff_mul_le hd).mpr (by omega : k*d ≤ x)).trans hK
    exact ⟨⟨k,p⟩,mem_sigma.mpr ⟨mem_Ioc.mpr ⟨hp0,hle⟩,mem_filter.mpr ⟨hp,eq ▸ hq⟩⟩,Prod.ext rfl eq⟩

lemma box_parts {x d : ℕ} (hd : 0<d) : ∑ a∈range d,(cell (pool x) d a).card^2 ≤
    2*(box x d).card+(pool x).card := by
  classical
  let P := pool x
  let U := ((range d).sigma fun a => cell P d a ×ˢ cell P d a)
  have hU : U.card=∑ a∈range d,(cell P d a).card^2 := by simp [U,card_sigma,pow_two]
  let D := P.image fun p => (p,p)
  let A := box x d
  have h : U.image (fun z => z.2) ⊆ A ∪ A.image Prod.swap ∪ D := by
    rintro _ hm
    obtain ⟨⟨a,p,q⟩,hz,rfl⟩ := mem_image.mp hm
    obtain ⟨hp,hq⟩ := mem_product.mp (mem_sigma.mp hz).2
    obtain ⟨hp,ep⟩ := mem_filter.mp hp
    obtain ⟨hq,eq⟩ := mem_filter.mp hq
    rcases lt_trichotomy p q with lt|rfl|lt
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨hp,hq⟩,lt,ep.trans eq.symm⟩))
    · exact mem_union_right _ (mem_image.mpr ⟨_,hp,rfl⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨(q,p),mem_filter.mpr ⟨mem_product.mpr ⟨hq,hp⟩,lt,eq.trans ep.symm⟩,rfl⟩))
  have hi : Set.InjOn (fun z : (_ : ℕ) × (ℕ×ℕ) => z.2) (U:Set _) := by
    rintro ⟨a,v⟩ hv ⟨b,w⟩ hw rfl
    have h1 := (mem_filter.mp (mem_product.mp (mem_sigma.mp hv).2).1).2
    have h2 := (mem_filter.mp (mem_product.mp (mem_sigma.mp hw).2).1).2
    change v.1%d=a at h1
    change v.1%d=b at h2
    subst a; subst b; rfl
  have h1 := card_le_card h
  rw [card_image_of_injOn hi,hU] at h1
  have h2 := card_union_le (A ∪ A.image Prod.swap) D
  have h3 := card_union_le A (A.image Prod.swap)
  have h4 : (A.image Prod.swap).card ≤ A.card := card_image_le
  have h5 : D.card ≤ P.card := card_image_le
  change (∑ a∈range d,(cell P d a).card^2) ≤ 2*A.card+P.card
  omega

lemma lower (x d K m : ℕ) (hd : 0<d) (hK : x/d ≤ K) (hm : d ≤ 2*m)
    (hP : 4*m ≤ (pool x).card) : (pool x).card^2 ≤ 8*m*∑ k∈Ioc 0 K,(run x (k*d)).card := by
  rw [run_box x d K hd hK]
  let P := pool x
  have H := sq_sum_le_card_mul_sum_sq (s:=range d) (f:=fun a => (cell P d a).card)
  have hsum : ∑ a∈range d,(cell P d a).card=P.card := by
    unfold cell; rw [sum_card_fiberwise_eq_card_filter,filter_eq_self.mpr (fun a _ => mem_range.mpr (Nat.mod_lt a hd))]
  rw [hsum,card_range] at H
  have H' := (Nat.mul_le_mul_left d (box_parts (x:=x) hd)).trans (Nat.mul_le_mul_right _ hm)
  change P.card^2 ≤ 8*m*(box x d).card
  change 4*m ≤ P.card at hP
  nlinarith only [H,H',Nat.mul_le_mul_right P.card hP]

lemma upper (x d : ℕ) (hd : 0<d) (y : ℝ) (hxy : (x:ℝ) ≤ y) :
    (box x d).card ≤ ∑ a∈((range d).filter fun a => a.Coprime d),
        (cell (Nat.primesLE ⌊y⌋₊) d a).card*((cell (Nat.primesLE ⌊y⌋₊) d a).card-1) := by
  classical
  let S := (range d).filter fun a => a.Coprime d
  let C := cell (Nat.primesLE ⌊y⌋₊) d
  have E (a : ℕ) : (C a).offDiag.card=(C a).card*((C a).card-1) := by rw [offDiag_card,Nat.mul_sub_one]
  change _ ≤ ∑ a∈S,(C a).card*((C a).card-1)
  simp_rw [← E]
  rw [←card_sigma]
  apply card_le_card_of_injOn (fun v => (⟨v.1%d,v⟩ : (_ : ℕ) × (ℕ×ℕ)))
  · rintro ⟨p,q⟩ hv
    obtain ⟨hm,hlt,hres⟩ := mem_filter.mp hv
    obtain ⟨hp,hq⟩ := mem_product.mp hm
    obtain ⟨hpN,hpr⟩ := Nat.mem_primesLE.mp (mem_of_mem_erase hp)
    obtain ⟨hqN,hqr⟩ := Nat.mem_primesLE.mp (mem_of_mem_erase hq)
    change p<q at hlt
    have hcop : p.Coprime d := hpr.coprime_iff_not_dvd.mpr (by
      intro hpd
      have he := (show p ≡ q [MOD d] from hres).of_dvd hpd
      have hdiv : p∣q := Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using he.symm)
      exact hlt.ne ((Nat.prime_dvd_prime_iff_eq hpr hqr).mp hdiv))
    have hmod : (p%d).Coprime d := by change Nat.gcd (p%d) d=1; rw [←Nat.gcd_rec]; exact hcop.symm
    have hfloor := Nat.le_floor hxy
    exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hd),hmod⟩,mem_offDiag.mpr
      ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpN.trans hfloor,hpr⟩,rfl⟩,
       mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hqN.trans hfloor,hqr⟩,hres.symm⟩,hlt.ne⟩⟩
  · exact fun _ _ _ _ h => congrArg Sigma.snd h
end Freq971
end

section
namespace Freq971
open Finset OMALib.Sieve Real
noncomputable def W (c : ℝ) (n : ℕ) := ∏ p∈n.primeFactors, (1+c/(p:ℝ))

theorem meanW (c : ℝ) (hc : 0 ≤ c) : ∃ B>0, ∀ D : ℕ,
    ∑ n∈Ioc 0 D,W c n ≤ B*D := by
  let Z := ∑' a : ℕ, 1/(a:ℝ)^2
  have hz : Summable fun a : ℕ => 1/(a:ℝ)^2 := Real.summable_one_div_nat_pow.mpr (by decide)
  refine ⟨exp (c*Z),exp_pos _,?_⟩
  intro D
  let Q := Nat.primesLE D
  let m (T : Finset ℕ) := ∏ p∈T,p
  let v (T : Finset ℕ) := ∏ p∈T, c/(p:ℝ)
  have hv (T : Finset ℕ) : 0 ≤ v T := prod_nonneg (fun _ _ => by positivity)
  have lo (n : ℕ) (hn : n∈Ioc 0 D) :
      W c n ≤ ∑ T∈Q.powerset, if m T∣n then v T else 0 := by
    rw [←sum_filter,W,prod_one_add]
    apply sum_le_sum_of_subset_of_nonneg
    · intro T hT
      have ht := mem_powerset.mp hT
      exact mem_filter.mpr ⟨mem_powerset.mpr (ht.trans (fun p hp => Nat.mem_primesLE.mpr
        ⟨(Nat.le_of_mem_primeFactors hp).trans (mem_Ioc.mp hn).2,Nat.prime_of_mem_primeFactors hp⟩)),
        (prod_dvd_prod_of_subset _ _ _ ht).trans (Nat.prod_primeFactors_dvd n)⟩
    · exact fun T _ _ => hv T
  apply (sum_le_sum lo).trans
  rw [sum_comm]
  have main (T : Finset ℕ) (hT : T∈Q.powerset) :
      (∑ n∈Ioc 0 D,if m T∣n then v T else 0) ≤ (D:ℝ)*∏ p∈T,c/(p:ℝ)^2 := by
    have hp (p : ℕ) (hp : p∈T) : p.Prime := (Nat.mem_primesLE.mp (mem_powerset.mp hT hp)).2
    rw [←sum_filter,sum_const,Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul]
    apply (mul_le_mul_of_nonneg_right (Nat.cast_div_le (m:=D) (n:=m T)) (hv T)).trans_eq
    change (D:ℝ)/((∏ p∈T,p:ℕ):ℝ)*(∏ p∈T,c/(p:ℝ)) = _
    rw [Nat.cast_prod,div_eq_mul_inv,mul_assoc,←prod_inv_distrib,←prod_mul_distrib]
    congr 1
    apply prod_congr rfl; intro p _
    ring
  apply (sum_le_sum main).trans
  rw [←mul_sum,←prod_one_add,mul_comm (exp _)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg D)
  have E := Real.prod_one_add_le_exp_sum Q (f:=fun p => c/(p:ℝ)^2) (fun p => by positivity)
  apply E.trans (exp_le_exp.mpr ?_)
  have h := hz.sum_le_tsum Q (fun a _ => by positivity)
  calc _ = c*∑ p∈Q,1/(p:ℝ)^2 := by rw [mul_sum]; apply sum_congr rfl; intro _ _; ring
       _ ≤ c*Z := mul_le_mul_of_nonneg_left h hc

lemma large_phi_loss (d : ℕ) : pairSingularProduct d * (d:ℝ) ≤ W 5 d * d.totient := by
  have htot := congrArg (fun z : ℚ => (z:ℝ)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at htot
  have htot' : (d.totient:ℝ) = d*∏ p∈d.primeFactors,(1-1/(p:ℝ)) := by simpa [one_div] using htot
  rw [htot',mul_left_comm,←mul_assoc,mul_comm (pairSingularProduct _)]
  unfold W
  rw [mul_assoc,←prod_mul_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change (∏ p∈d.primeFactors.filter (2<·), (1+1/(p:ℝ))) ≤ _
  apply (prod_le_prod_of_subset_of_one_le (filter_subset _ _) (f:= fun p : ℕ => 1+1/(p:ℝ))
    (fun _ _ => by positivity) (fun p _ _ => by linarith [show 0 ≤ 1/(p:ℝ) by positivity])).trans
  apply prod_le_prod (fun _ _ => by positivity)
  intro p hp
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  field_simp
  nlinarith
end Freq971
end

section
namespace Freq971
open Finset Real OMALib.Sieve
noncomputable abbrev w := pairSingularProduct
def good (D A : ℕ) := (Ioc 0 D).filter fun d => D/A < d ∧ d ≤ A*d.totient
noncomputable def count (x j d : ℕ) : ℝ := (run x (j*d)).card

lemma constants : ∃ B : ℝ, 1 ≤ B ∧
    (∀ K : ℕ, ∑ k∈Ioc 0 K,w k ≤ B*K) ∧ (∀ K : ℕ, ∑ k∈Ioc 0 K,W 5 k ≤ B*K) ∧
    ∀ (x j d : ℕ), 2 ≤ x → 0<j → 0<d → count x j d ≤ B*(x/(log x)^2)*w j*w d := by
  obtain ⟨B1,h1,H1⟩ := SmallPrimes.mean_weight
  obtain ⟨B2,h2,H2⟩ := meanW 5 (by norm_num)
  obtain ⟨C,hC,H⟩ := prime_pairs_upper_bound'
  let B := 1+B1+B2+C
  have b1 : B1 ≤ B := by dsimp [B]; linarith
  have b2 : B2 ≤ B := by dsimp [B]; linarith
  have bC : C ≤ B := by dsimp [B]; linarith
  refine ⟨B,by dsimp [B]; linarith,fun K => (H1 K).trans (by gcongr),fun K => (H2 K).trans (by gcongr),?_⟩
  intro x j d hx hj hd
  have hB : 0≤B := hC.le.trans bC
  have hj' := zero_le_one.trans (one_le_pairSingularProduct j)
  have hd' := zero_le_one.trans (one_le_pairSingularProduct d)
  change ((run x (j*d)).card:ℝ) ≤ _
  by_cases hev : Even (j*d)
  · have hsub : run x (j*d) ⊆ (range (x+1)).filter (fun p => p.Prime ∧ (p+j*d).Prime) := by
      intro p hp
      obtain ⟨hp,hq⟩ := mem_filter.mp hp
      obtain ⟨hpx,hp⟩ := Nat.mem_primesLE.mp (mem_of_mem_erase hp)
      exact mem_filter.mpr ⟨mem_range.mpr (by omega),hp,(Nat.mem_primesLE.mp (mem_of_mem_erase hq)).2⟩
    apply (Nat.cast_le (α:=ℝ)).mpr (card_le_card hsub) |>.trans
    apply (H _ (Nat.mul_pos hj hd) hev x hx).trans
    rw [mul_assoc (B*_)]
    exact mul_le_mul (mul_le_mul_of_nonneg_right bC (by positivity)) (SmallPrimes.weight_mul d j hd hj)
      (zero_le_one.trans (one_le_pairSingularProduct _)) (by positivity)
  · have hem : run x (j*d)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp; obtain ⟨hp,hq⟩ := mem_filter.mp hp
      have o (k : ℕ) (h : k∈pool x) := (Nat.mem_primesLE.mp (mem_of_mem_erase h)).2.odd_of_ne_two (ne_of_mem_erase h)
      have h1 := Nat.not_even_iff_odd.mpr (o p hp)
      have h2 := Nat.not_even_iff_odd.mpr (o _ hq)
      exact h2 (Nat.even_add.mpr ⟨fun h => (h1 h).elim,fun h => (hev h).elim⟩)
    rw [hem,card_empty,Nat.cast_zero]; positivity

lemma bad_weight {D A : ℕ} (ha : 0<A) {B : ℝ} (hB : 0≤B)
    (H1 : ∀ K : ℕ, ∑ k∈Ioc 0 K,w k ≤ B*K) (H2 : ∀ K : ℕ, ∑ k∈Ioc 0 K,W 5 k ≤ B*K) :
    ∑ d∈((Ioc 0 D) \ good D A),w d ≤ 2*B*D/A := by
  have ha' : (0:ℝ)<A := by exact_mod_cast ha
  let bad := (Ioc 0 D) \ good D A
  have hW (d : ℕ) : 0 ≤ W 5 d := prod_nonneg fun _ _ => by positivity
  have step (d : ℕ) (hd : d∈bad) :
      w d ≤ (if d ≤ D/A then w d else 0) + W 5 d/A := by
    split_ifs with h
    · linarith [div_nonneg (hW d) ha'.le]
    rw [zero_add,le_div_iff₀ ha']
    obtain ⟨hD,hnot⟩ := mem_sdiff.mp hd
    have hlt : A*d.totient < d := by
      by_contra! H; exact hnot (mem_filter.mpr ⟨hD,by omega,H⟩)
    have hphi : 0 < (d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (mem_Ioc.mp hD).1
    have hlt' : (A:ℝ)*d.totient ≤ d := by exact_mod_cast hlt.le
    apply (mul_le_mul_iff_left₀ hphi).mp
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hlt' (zero_le_one.trans (one_le_pairSingularProduct d))).trans (large_phi_loss d)
  apply (sum_le_sum step).trans
  rw [sum_add_distrib,←sum_filter,←sum_div]
  have hsub : bad.filter (fun d => d ≤ D/A) ⊆ Ioc 0 (D/A) := fun d hd =>
    mem_Ioc.mpr ⟨(mem_Ioc.mp (mem_sdiff.mp (mem_filter.mp hd).1).1).1,(mem_filter.mp hd).2⟩
  have h1 := (sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => zero_le_one.trans (one_le_pairSingularProduct d))).trans (H1 _)
  have h2 := (sum_le_sum_of_subset_of_nonneg (show bad⊆Ioc 0 D from sdiff_subset) (fun d _ _ => hW d)).trans (H2 _)
  have h1' := h1.trans (mul_le_mul_of_nonneg_left (Nat.cast_div_le (m:=D) (n:=A)) hB)
  exact (add_le_add h1' (div_le_div_of_nonneg_right h2 ha'.le)).trans_eq (by ring)

lemma total_lower (D m : ℕ) (hm : 0 < m) (hP : 4*m ≤ (pool (m*D)).card) :
    ((pool (m*D)).card:ℝ)^2 ≤ 8*∑ j∈Ioc m (2*m), ∑ d∈Ioc 0 D,count (m*D) j d := by
  let S := Ioc m (2*m)
  have single (j : ℕ) (hj : j∈S) := lower (m*D) j D m (hm.trans (mem_Ioc.mp hj).1)
    (show m*D/j ≤ D by
      have q := Nat.div_mul_le_self (m*D) j
      have jpos := hm.trans (mem_Ioc.mp hj).1
      exact Nat.le_of_mul_le_mul_right (q.trans (Nat.mul_le_mul_right D (mem_Ioc.mp hj).1.le |>.trans_eq (Nat.mul_comm ..))) jpos) (mem_Ioc.mp hj).2 hP
  have H := sum_le_sum single
  rw [sum_const,nsmul_eq_mul,←mul_sum] at H
  have hcard : S.card=m := by simp [S]; omega
  rw [hcard] at H
  change m*(pool (m*D)).card^2 ≤ 8*m*_ at H
  rw [Nat.mul_comm 8 m,Nat.mul_assoc] at H
  have HH := Nat.le_of_mul_le_mul_left H hm
  unfold count
  norm_cast
  simpa only [S,Nat.mul_comm] using HH

lemma total_bad {x m D A : ℕ} {B : ℝ} (hx : 2 ≤ x) (hm : 0 < m) (ha : 0<A) (hB : 1 ≤ B)
    (H1 : ∀ K : ℕ, ∑ k∈Ioc 0 K,w k ≤ B*K) (H2 : ∀ K : ℕ, ∑ k∈Ioc 0 K,W 5 k ≤ B*K)
    (HC : ∀ (x j d : ℕ), 2 ≤ x → 0<j → 0<d → count x j d ≤ B*(x/(log x)^2)*w j*w d) :
    ∑ j∈Ioc m (2*m), ∑ d∈((Ioc 0 D) \ good D A),count x j d ≤
      B*(x/(log x)^2)*(B*(2*m))*(2*B*D/A) := by
  let u := B*((x:ℝ)/(log x)^2)
  have hu : 0≤u := by dsimp [u]; positivity
  have Wbad := bad_weight (D:=D) ha (zero_le_one.trans hB) H1 H2
  have ha' : 0<(A:ℝ) := by exact_mod_cast ha
  have hb : 0 ≤ 2*B*(D:ℝ)/A := by positivity
  have Hrow (j : ℕ) (hj : j∈Ioc m (2*m)) :
      ∑ d∈((Ioc 0 D) \ good D A),count x j d ≤ u*w j*(2*B*D/A) := by
    apply (sum_le_sum (fun d hd => HC x j d hx (hm.trans (mem_Ioc.mp hj).1) (mem_Ioc.mp (mem_sdiff.mp hd).1).1)).trans
    rw [←mul_sum]; exact mul_le_mul_of_nonneg_left Wbad (mul_nonneg hu (zero_le_one.trans (one_le_pairSingularProduct j)))
  apply (sum_le_sum Hrow).trans
  rw [←sum_mul,←mul_sum]
  have hj : ∑ j∈Ioc m (2*m),w j ≤ B*(2*m) := by
    apply (sum_le_sum_of_subset_of_nonneg (show Ioc m (2*m) ⊆ Ioc 0 (2*m) from Ioc_subset_Ioc_left hm.le)
      (fun j _ _ => zero_le_one.trans (one_le_pairSingularProduct j))).trans
    simpa using H1 (2*m)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj hu) hb
end Freq971
end

section
namespace Freq971
open Finset Filter Real
-- Extract one modulus with a positive density of prime pairs after discarding
-- the very small moduli and the moduli with unusually small totient.
theorem select {m D A : ℕ} {B F : ℝ} (hm : 0 < m) (hD : 0 < D) (ha : 0<A) (hB : 1 ≤ B)
    (hF : 0<F) (hA : 4096*B^3 ≤ (A:ℝ))
    (H1 : ∀ K : ℕ, ∑ k∈Ioc 0 K,w k ≤ B*K) (H2 : ∀ K : ℕ, ∑ k∈Ioc 0 K,W 5 k ≤ B*K)
    (HC : ∀ (x j d : ℕ), 2 ≤ x → 0<j → 0<d → count x j d ≤ B*(x/(log x)^2)*w j*w d)
    (hx : 2 ≤ m*D) (hP : 4*m ≤ (pool (m*D)).card) (hπ : (m*D:ℕ)/log (m*D:ℕ) ≤ 4*(pool (m*D)).card)
    (hl : log (m*D:ℕ) ≤ (m:ℝ)*F) :
    ∃ d∈good D A, (D:ℝ)/(512*F^2) ≤ ∑ j∈Ioc m (2*m),count (m*D) j d := by
  let x := m*D
  let v := (x:ℝ)/log x
  have hx' : (1:ℝ)<x := by exact_mod_cast (show 1<x from hx)
  have hlog := log_pos hx'
  have hv : 0<v := div_pos (by linarith only [hx']) hlog
  have ha' : (0:ℝ)<A := by exact_mod_cast ha
  have hb := total_bad (m:=m) (D:=D) hx hm ha hB H1 H2 HC
  change (∑ j∈Ioc m (2*m),∑ d∈(Ioc 0 D) \ good D A,count x j d) ≤ B*((x:ℝ)/(log x)^2)*(B*(2*m))*(2*B*D/A) at hb
  have norm : B*((x:ℝ)/(log x)^2)*(B*(2*m))*(2*B*D/A)=v^2*(4*B^3/A) := by
    dsimp [x,v]; push_cast; ring
  have coef : 4*B^3/(A:ℝ) ≤ 1/1024 := (div_le_iff₀ ha').mpr (by linarith)
  have hbad := hb.trans (norm ▸ mul_le_mul_of_nonneg_left coef (sq_nonneg v))
  let S := Ioc m (2*m)
  have split (j : ℕ) : ∑ d∈Ioc 0 D,count x j d =
      (∑ d∈(Ioc 0 D) \ good D A,count x j d) + ∑ d∈good D A,count x j d :=
    (sum_sdiff (filter_subset _ _ : good D A ⊆ Ioc 0 D)).symm
  have H := total_lower D m hm hP
  change ((pool x).card:ℝ)^2 ≤ 8*∑ j∈S, ∑ d∈Ioc 0 D,count x j d at H
  simp_rw [split,sum_add_distrib] at H
  change v ≤ 4*((pool x).card:ℝ) at hπ
  have Hsq := pow_le_pow_left₀ hv.le hπ 2
  change (∑ j∈S,∑ d∈(Ioc 0 D) \ good D A,count x j d) ≤ _ at hbad
  have hgood : v^2/256 ≤ ∑ j∈S,∑ d∈good D A,count x j d := by nlinarith only [H,Hsq,hbad]
  rw [sum_comm] at hgood
  change log (x:ℝ) ≤ m*F at hl
  have hdv : (D:ℝ) ≤ v*F := by
    have H' := mul_le_mul_of_nonneg_left hl (show 0≤(D:ℝ) by positivity)
    dsimp [v]
    rw [div_mul_eq_mul_div,le_div_iff₀ hlog]
    dsimp [x] at H' ⊢; push_cast at H' ⊢; nlinarith only [H']
  by_contra! h
  have hsum := sum_le_sum (fun d hd => (h d hd).le)
  change (∑ d∈good D A,∑ j∈S,count x j d) ≤ ∑ _d∈good D A,(D:ℝ)/(512*F^2) at hsum
  rw [sum_const,nsmul_eq_mul] at hsum
  have hc : ((good D A).card:ℝ) ≤ D := by exact_mod_cast (show (good D A).card ≤ D by simpa [good] using card_le_card (filter_subset _ (Ioc 0 D) : good D A ⊆ _))
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  have hdiv := (div_le_iff₀ hF).mpr hdv
  have hs := pow_le_pow_left₀ (show (0:ℝ)≤D/F by positivity) hdiv 2
  have eq : (D:ℝ)*(D/(512*F^2))=(D/F)^2/512 := by ring
  rw [eq] at hsum'
  nlinarith only [hgood,hsum',hs,sq_pos_of_pos hv]
end Freq971
end

section
namespace Freq971
open Finset Filter Real
theorem pi_lower : ∃ y0 : ℕ, ∀ y : ℕ, y0 ≤ y → (y : ℝ) / 3 ≤ (Nat.primesLE y).card * Real.log y := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp
    (Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 4 by norm_num))
  refine ⟨max ⌈a⌉₊ 3, fun y hy => ?_⟩
  have hy3 : (3 : ℝ) ≤ y := by exact_mod_cast (le_max_right _ _).trans hy
  have hya : a ≤ (y : ℝ) + 1 := by
    have : (⌈a⌉₊ : ℝ) ≤ y := by exact_mod_cast (le_max_left _ _).trans hy
    linarith [Nat.le_ceil a]
  have h1 := ha _ hya
  simp only [Real.norm_eq_abs, id] at h1
  have h1' : Real.log ((y : ℝ) + 1) ≤ 1 / 4 * ((y : ℝ) + 1) := by
    have := le_abs_self (Real.log ((y : ℝ) + 1))
    rw [abs_of_pos (by linarith : (0 : ℝ) < y + 1)] at h1
    linarith
  have h2 := Chebyshev.psi_le_primeCounting_mul_log y
  have h3 := Chebyshev.psi_ge y
  have h4 := Real.log_two_gt_d9
  rw [Nat.primesLE_card_eq_primeCounting]
  nlinarith

lemma square_bound (m : ℕ) (hm : 4 ≤ m) : m^2 ≤ 2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ m hm ih => rw [pow_succ 2]; nlinarith [Nat.mul_le_mul_left m hm]

set_option maxHeartbeats 1200000 in
theorem main :
    ∃ M > (0:ℝ), ∃ δ > (0:ℝ), ∃ᶠ d : ℕ in atTop, (d:ℝ) ≤ M*d.totient ∧
      δ*d.totient ≤ ((∑ a∈((range d).filter fun a => a.Coprime d),
        (cell (Nat.primesLE ⌊(d.totient:ℝ)*log d⌋₊) d a).card*
        ((cell (Nat.primesLE ⌊(d.totient:ℝ)*log d⌋₊) d a).card-1):ℕ):ℝ) := by
  obtain ⟨B,hB,H1,H2,HC⟩ := constants
  let A := ⌈4096*B^3⌉₊+1
  have hA : 4096*B^3 ≤ (A:ℝ) := by dsimp [A]; push_cast; linarith [Nat.le_ceil (4096*B^3)]
  have hA0 : 0<A := Nat.succ_pos _
  let L := 4*A^2+1
  let F : ℝ := L+1
  have hF : 0<F := by dsimp [F]; positivity
  refine ⟨A,by exact_mod_cast hA0,1/(512*F^2),by positivity,frequently_atTop.mpr ?_⟩
  intro K
  obtain ⟨Y,hπ⟩ := pi_lower
  let m := K+Y+100*(L+1)+A+4
  have hm : 4 ≤ m := by dsimp [m]; omega
  have hm' : 0 < m := by omega
  have hL : 1 ≤ L := Nat.le_add_left _ _
  let D := 2^(L*m)
  let x := m*D
  have hmL : m ≤ L*m := by simpa using Nat.mul_le_mul_right m hL
  have hD2 : m^2 ≤ D := (square_bound m hm).trans (Nat.pow_le_pow_right (by decide) hmL)
  have hxD : m ≤ D := by nlinarith only [hm,hD2]
  have hx : 2 ≤ x := by dsimp [x]; nlinarith only [hm,hxD]
  have hmx : m ≤ x := by dsimp [x]; nlinarith only [hm,hxD]
  have hy : Y ≤ x := (show Y ≤ m by dsimp [m]; omega).trans hmx
  have hM : (0:ℝ) < m := by exact_mod_cast hm'
  have hx' : 1 < (x:ℝ) := by exact_mod_cast (show 1 < x from hx)
  have hlog := log_pos hx'
  have hl : log (x:ℝ) ≤ (m:ℝ)*F := by
    change log ((m*D:ℕ):ℝ) ≤ _
    rw [Nat.cast_mul,log_mul hM.ne' (by dsimp [D]; positivity)]
    simp only [D,Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_mul]
    have h1 := log_le_sub_one_of_pos hM
    have h2 := log_two_lt_d9
    dsimp [F]; nlinarith [mul_nonneg (show (0:ℝ) ≤ (L:ℝ)*m by positivity) (show 0 ≤ 1-log 2 by linarith)]
  have hdF : 100*(L+1)*m ≤ D := (Nat.mul_le_mul_right m (show 100*(L+1) ≤ m by dsimp [m]; omega)).trans (by simpa [sq] using hD2)
  have hv : 100*(m:ℝ) ≤ x/log x := by
    apply (le_div_iff₀ hlog).mpr
    apply (mul_le_mul_of_nonneg_left hl (by positivity : 0≤100*(m:ℝ))).trans
    have h : 100*F*(m:ℝ) ≤ D := by dsimp [F]; exact_mod_cast hdF
    have hh := mul_le_mul_of_nonneg_left h hM.le
    change _ ≤ ((m*D:ℕ):ℝ)
    push_cast; nlinarith only [hh]
  have hp := hπ x hy
  have hp' : (x:ℝ)/log x ≤ 3*(Nat.primesLE x).card := (div_le_iff₀ hlog).mpr (by linarith)
  have he : (Nat.primesLE x).card ≤ (pool x).card+1 := by
    unfold pool; by_cases h : 2∈Nat.primesLE x
    · rw [card_erase_of_mem h]; omega
    · simp [erase_eq_of_notMem h]
  have he' : ((Nat.primesLE x).card:ℝ) ≤ (pool x).card+1 := by exact_mod_cast he
  have hp4 : 4*m ≤ (pool x).card := by exact_mod_cast (show 4*(m:ℝ) ≤ (pool x).card by linarith only [hv,hp',he',show (4:ℝ) ≤ m by exact_mod_cast hm])
  have hpR : (x:ℝ)/log x ≤ 4*(pool x).card := by
    have h1 : 4*(m:ℝ) ≤ (pool x).card := by exact_mod_cast hp4
    have h2 : (4:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨d,hd,hpair⟩ := select hm' (by omega : 0<D) hA0 hB hF hA H1 H2 HC hx hp4 hpR hl
  obtain ⟨hd0,hDsmall,hphi⟩ := mem_filter.mp hd
  obtain ⟨hdpos,hdD⟩ := mem_Ioc.mp hd0
  have hbig : D < A*d := (Nat.div_lt_iff_lt_mul hA0).mp hDsmall |>.trans_eq (Nat.mul_comm ..)
  let E := 2^(4*A^2*m)
  have Epos : 0 < E := by dsimp [E]; positivity
  have hEs : E < d := by
    have eq : D=E*2^m := by dsimp [D,L,E]; rw [Nat.add_mul,Nat.one_mul,pow_add]
    have hAm : A ≤ 2^m := (show A ≤ m by dsimp [m]; omega).trans (Nat.lt_two_pow_self (n:=m)).le
    by_contra! h
    have bad := Nat.mul_le_mul hAm h
    rw [Nat.mul_comm (2^m) E,←eq] at bad; omega
  have hmE : m ≤ E := by
    apply (Nat.lt_two_pow_self (n:=m)).le.trans (Nat.pow_le_pow_right (by decide) ?_)
    have : 0 < 4*A^2 := by positivity
    simpa using Nat.mul_le_mul_right m this
  have hs : (x:ℝ) ≤ d.totient*log d := by
    have hlogd := log_le_log (show (0:ℝ) < E by exact_mod_cast Epos) (show (E:ℝ) ≤ d by exact_mod_cast hEs.le)
    simp only [E,Nat.cast_pow,Nat.cast_ofNat,log_pow,Nat.cast_mul] at hlogd
    have hlog' : (A:ℝ)^2*m ≤ log d := by
      have hg := mul_le_mul_of_nonneg_left (show (1:ℝ)/2 ≤ log 2 by linarith only [log_two_gt_d9])
        (show (0:ℝ) ≤ 4*(A:ℝ)^2*m by positivity)
      nlinarith only [hg,hlogd,mul_nonneg (sq_nonneg (A:ℝ)) hM.le]
    have hDA : D ≤ A*(A*d.totient) := hbig.le.trans (Nat.mul_le_mul_left _ hphi)
    have hreal : (m:ℝ)*D ≤ m*((A:ℝ)*(A*d.totient)) := by exact_mod_cast Nat.mul_le_mul_left m hDA
    change ((m*D:ℕ):ℝ) ≤ _
    push_cast
    nlinarith only [hreal,mul_le_mul_of_nonneg_left hlog' (Nat.cast_nonneg d.totient)]
  refine ⟨d,(show K ≤ m by dsimp [m]; omega).trans (hmE.trans hEs.le),by exact_mod_cast hphi,?_⟩
  have sub : Ioc m (2*m) ⊆ Ioc 0 (max (x/d) (2*m)) :=
    Ioc_subset_Ioc hm'.le (le_max_right ..)
  have hu := sum_le_sum_of_subset_of_nonneg sub (f:=fun j => (run x (j*d)).card) (fun _ _ _ => Nat.zero_le _)
  rw [run_box x d _ hdpos (le_max_left ..)] at hu
  have hpairs : (∑ j∈Ioc m (2*m),count x j d) ≤ ((box x d).card:ℝ) := by
    unfold count; exact_mod_cast hu
  have hfinal := hpair.trans (hpairs.trans (Nat.cast_le.mpr (upper x d hdpos _ hs)))
  have hsmall : (d.totient:ℝ) ≤ D := by exact_mod_cast (Nat.totient_le d).trans hdD
  rw [one_div_mul_eq_div]
  exact (div_le_div_of_nonneg_right hsmall (by positivity)).trans hfinal
end Freq971
end

private theorem h1_proof : OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1.H1 := Freq971.main
end

section
open Finset
open scoped Classical
namespace Third971

lemma cube_le (h : ℕ) : h^3 ≤ 27*h+27*h.choose 3 := by
  obtain hsmall | hbig := lt_or_ge h 3
  · interval_cases h <;> decide
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hbig
  have hc := Nat.descFactorial_eq_factorial_mul_choose (3+m) 3
  simp [Nat.descFactorial_succ,Nat.factorial] at hc
  rw [show 3+m-2 = m+1 by omega] at hc
  nlinarith only [hc, Nat.zero_le m, Nat.zero_le (m^2), Nat.zero_le (m^3)]

lemma sorted_three {T : Finset ℕ} (hc : T.card=3) :
    ∃ p q r : ℕ, p<q ∧ q<r ∧ T={p,q,r} := by
  let f := T.orderEmbOfFin hc
  refine ⟨f 0,f 1,f 2,f.strictMono (by decide),f.strictMono (by decide),?_⟩
  have h : (univ : Finset (Fin 3)) = {0,1,2} := by decide
  have hh := T.image_orderEmbOfFin_univ hc
  change image f univ = T at hh
  simpa [h] using hh.symm

lemma finite_moment (X d J : ℕ) (hd : 0<d) (hX : X < (J+1)*d)
    (A : Finset ℕ) :
    let P := Nat.primesLE X
    let H (a : ℕ) := P.filter fun p => p%d=a
    let U := ((Icc 1 J) ×ˢ (Icc 1 J)).filter fun v => v.1<v.2
    let T (v : ℕ×ℕ) := P.filter fun p => (p+v.1*d).Prime ∧ (p+v.2*d).Prime
    ∑ a ∈ A, (H a).card^3 ≤ 27*P.card + 27*∑ v ∈ U, (T v).card := by
  classical
  intro P H U T
  have hone : ∑ a ∈ A, (H a).card ≤ P.card := by
    dsimp only [H]
    rw [sum_card_fiberwise_eq_card_filter]
    exact card_filter_le _ _
  let f (z : (v : ℕ×ℕ) × ℕ) : (a : ℕ) × Finset ℕ :=
    ⟨z.2%d,{z.2,z.2+z.1.1*d,z.2+z.1.2*d}⟩
  have hsub : (A.sigma (fun a => (H a).powersetCard 3)) ⊆ (U.sigma T).image f := by
    rintro ⟨a,E⟩ ha
    obtain ⟨_,hE,hcard⟩ := (mem_sigma.mp ha).1, (mem_powersetCard.mp (mem_sigma.mp ha).2)
    change E ⊆ H a at hE
    change E.card = 3 at hcard
    obtain ⟨p,q,r,hpq,hqr,hset⟩ := sorted_three hcard
    have hp : p ∈ H a := hE (by simp [hset])
    have hq : q ∈ H a := hE (by simp [hset])
    have hr : r ∈ H a := hE (by simp [hset])
    have hpd := (mem_filter.mp hp).2
    have hqd := (mem_filter.mp hq).2
    have hrd := (mem_filter.mp hr).2
    have hPp : p ∈ P := (mem_filter.mp hp).1
    have hQp : q.Prime := (Nat.mem_primesLE.mp (mem_filter.mp hq).1).2
    have hRp := Nat.mem_primesLE.mp (mem_filter.mp hr).1
    obtain ⟨i,hi⟩ := (Nat.modEq_iff_dvd' hpq.le).mp (hpd.trans hqd.symm)
    obtain ⟨j,hj⟩ := (Nat.modEq_iff_dvd' (hpq.trans hqr).le).mp (hpd.trans hrd.symm)
    have qi : q=p+i*d := by rw [mul_comm] at hi; omega
    have rj : r=p+j*d := by rw [mul_comm] at hj; omega
    have ip : 0 < i := by
      by_contra! hh
      have hz : i=0 := by omega
      simp [hz] at qi
      omega
    have ij : i<j := by
      by_contra! hh
      have := Nat.mul_le_mul_right d hh
      omega
    have jb : j≤J := by
      by_contra! hh
      have hb := Nat.mul_le_mul_right d (show J+1 ≤ j by omega)
      have hrX := hRp.1
      omega
    refine mem_image.mpr ⟨⟨(i,j),p⟩,mem_sigma.mpr ⟨mem_filter.mpr
      ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨ip,ij.le.trans jb⟩,mem_Icc.mpr ⟨ip.trans ij,jb⟩⟩,ij⟩,
      mem_filter.mpr ⟨hPp,by simpa [← qi,← rj] using And.intro hQp hRp.2⟩⟩,?_⟩
    simp only [f,hpd,← qi,← rj,hset]
  have htwo := (card_le_card hsub).trans card_image_le
  simp only [card_sigma,card_powersetCard] at htwo
  calc
    _ ≤ ∑ a ∈ A, (27*(H a).card + 27*((H a).card.choose 3)) :=
      sum_le_sum fun a _ => cube_le _
    _ = 27*(∑ a ∈ A, (H a).card) + 27*(∑ a ∈ A, (H a).card.choose 3) := by
      rw [sum_add_distrib,mul_sum,mul_sum]
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left _ hone) (Nat.mul_le_mul_left _ htwo)

end Third971


namespace Third971
open Finset Real
open scoped Classical

noncomputable def loss (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, ((p:ℝ)/(p-1:ℝ))^3

lemma loss_pos (n : ℕ) : 0 < loss n := by
  apply prod_pos
  intro p hp
  have h : 1 < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  exact pow_pos (div_pos (by linarith) (by linarith)) _

lemma recip_sq (J : ℕ) :
    (∑ n ∈ Ioc 0 J, (1:ℝ)/(n:ℝ)^2) ≤ 2-2/(J+1:ℝ) := by
  induction J with
  | zero => norm_num
  | succ j ih =>
    rw [sum_Ioc_succ_top (by omega)]
    push_cast
    have e : (1:ℝ)/((j:ℝ)+1)^2 ≤ 2/((j:ℝ)+1)-2/((j:ℝ)+1+1) := by
      field_simp
      nlinarith [Nat.cast_nonneg (α:=ℝ) j]
    linarith

lemma mean_product (J : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ n ∈ Ioc 0 J, (∏ p ∈ n.primeFactors, (1+c/(p:ℝ))) ≤ J * exp (2*c) := by
  classical
  let P := Nat.primesLE J
  let w (T : Finset ℕ) := ∏ p ∈ T, (c/(p:ℝ))
  let v (T : Finset ℕ) := ∏ p ∈ T, p
  have hw (T : Finset ℕ) : 0 ≤ w T := prod_nonneg fun p _ => div_nonneg hc (Nat.cast_nonneg p)
  have hsub (n) (hn : n ∈ Ioc 0 J) : n.primeFactors ⊆ P := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (mem_Ioc.mp hn).1 (Nat.dvd_of_mem_primeFactors hp)).trans
      (mem_Ioc.mp hn).2,Nat.prime_of_mem_primeFactors hp⟩
  have hcard (T : Finset ℕ) : ((Ioc 0 J).filter (fun n => T ⊆ n.primeFactors)).card ≤ J / v T := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div]
    apply card_le_card
    intro n hn
    refine mem_filter.mpr ⟨(mem_filter.mp hn).1,?_⟩
    exact (prod_dvd_prod_of_subset T n.primeFactors (fun p => p) (mem_filter.mp hn).2).trans
      (Nat.prod_primeFactors_dvd n)
  have hloc (n) (hn : n ∈ Ioc 0 J) :
      (∏ p ∈ n.primeFactors, (1+c/(p:ℝ))) =
      ∑ T ∈ P.powerset, (if T ⊆ n.primeFactors then w T else 0) := by
    rw [prod_one_add,← sum_filter]
    have h : P.powerset.filter (fun T => T ⊆ n.primeFactors) = n.primeFactors.powerset := by
      ext T
      simp only [mem_filter,mem_powerset]
      exact ⟨And.right,fun h => ⟨h.trans (hsub n hn),h⟩⟩
    rw [h]
  have hsum : (∑ p ∈ P, (1:ℝ)/(p:ℝ)^2) ≤ 2 := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (t:=Ioc 0 J) (fun p hp =>
      mem_Ioc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos,(Nat.mem_primesLE.mp hp).1⟩)
      (fun p _ _ => by positivity))
    exact (recip_sq J).trans (sub_le_self _ (by positivity))
  calc
    _ = ∑ T ∈ P.powerset, ∑ n ∈ Ioc 0 J, (if T ⊆ n.primeFactors then w T else 0) := by
      rw [sum_congr rfl hloc,sum_comm]
    _ ≤ ∑ T ∈ P.powerset, ((J:ℝ)/(v T:ℝ))*w T := by
      apply sum_le_sum
      intro T hT
      rw [← sum_filter,sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (hw T)
      exact (show ((((Ioc 0 J).filter (fun n => T ⊆ n.primeFactors)).card : ℕ):ℝ) ≤
        (J/v T:ℕ) by exact_mod_cast hcard T).trans Nat.cast_div_le
    _ = (J:ℝ) * ∏ p ∈ P, (1+c/(p:ℝ)^2) := by
      rw [prod_one_add,mul_sum]
      apply sum_congr rfl
      intro T _
      dsimp only [w,v]
      push_cast
      rw [show (∏ i ∈ T, c/(i:ℝ)^2) = (∏ i ∈ T, c/(i:ℝ)) / (∏ i ∈ T, (i:ℝ)) by
        rw [← prod_div_distrib]; exact prod_congr rfl fun i _ => by ring]
      ring
    _ ≤ (J:ℝ)*exp (∑ p ∈ P, c/(p:ℝ)^2) := by
      rw [Real.exp_sum]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg J)
      exact prod_le_prod (fun p _ => by positivity) (fun p _ => by linarith [Real.add_one_le_exp (c/(p:ℝ)^2)])
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg J)
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hsum hc
      rw [mul_sum] at hh
      simpa only [mul_one_div,mul_comm 2 c] using hh

lemma local_ninth (t : ℝ) (ht : 2 ≤ t) : (t/(t-1))^9 ≤ 1+4608/t := by
  let v := t/(t-1)
  have hden : 0 < t-1 := by linarith
  have ht0 : 0 < t := by linarith
  have h1 : 1 ≤ v := (le_div_iff₀ hden).mpr (by linarith)
  have h2 : v ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  have hv : v-1 ≤ 2/t := by
    dsimp [v]
    field_simp
    nlinarith
  have hsum : ∑ i ∈ range 9, v^i ≤ 2304 := by
    calc
      _ ≤ ∑ _i ∈ range 9, (2:ℝ)^8 := sum_le_sum fun i hi =>
        (pow_le_pow_left₀ (by linarith) h2 i).trans
          (pow_le_pow_right₀ (by norm_num) (show i ≤ 8 by have := mem_range.mp hi; omega))
      _ = _ := by norm_num
  have he := mul_le_mul hsum hv (sub_nonneg.mpr h1) (by norm_num)
  rw [geom_sum_mul] at he
  change v^9 ≤ _
  rw [show 2304 * (2/t) = 4608/t by ring] at he
  linarith

lemma mean_loss_cube (J : ℕ) : ∑ n ∈ Ioc 0 J, (loss n)^3 ≤ J*exp (2*4608) := by
  apply le_trans _ (mean_product J 4608 (by norm_num))
  refine sum_le_sum fun n _ => ?_
  unfold loss
  rw [← prod_pow]
  apply prod_le_prod
  · intro p hp
    have h : 1 < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    positivity
  · intro p hp
    rw [← pow_mul]
    exact local_ninth p (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)

end Third971


open Finset Real OMALib.Sieve
open scoped Classical
namespace Third971

lemma weighted_log (Q : Finset ℕ) (h v : ℕ → ℝ) (hh : ∀ p ∈ Q, 0 ≤ h p) :
    ∑ T ∈ Q.powerset, (∏ p ∈ T, h p)*(∑ p ∈ T, v p) =
      (∏ p ∈ Q, (1+h p))*(∑ p ∈ Q, (h p/(1+h p))*v p) := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert a Q ha ih =>
    have hQ (p) (hp : p ∈ Q) := hh p (mem_insert_of_mem hp)
    have hab : 0 < 1+h a := by linarith [hh a (mem_insert_self _ _)]
    rw [sum_powerset_insert ha,prod_insert ha,sum_insert ha]
    have hstep : (∑ T ∈ Q.powerset, (∏ p ∈ insert a T, h p)*(∑ p ∈ insert a T, v p)) =
      h a * v a * (∑ T ∈ Q.powerset, ∏ p ∈ T, h p) +
      h a * (∑ T ∈ Q.powerset, (∏ p ∈ T, h p)*(∑ p ∈ T, v p)) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl
      intro T hT
      have hnot : a ∉ T := fun hm => ha (mem_powerset.mp hT hm)
      rw [prod_insert hnot,sum_insert hnot]; ring
    rw [hstep,← prod_one_add,ih hQ]
    field_simp
    ring

lemma normalizer_half (Q : Finset ℕ) (z : ℕ) (hz : 1<z) (g : ℕ → ℝ)
    (hp : ∀ p ∈ Q, p.Prime) (hg : ∀ p ∈ Q, 0 < g p ∧ g p < 1)
    (hsmall : ∑ p ∈ Q, g p * log p ≤ log z / 2) :
    (∏ p ∈ Q, (1+hFun g p)) / 2 ≤ selbergG g (levelFamily Q z) := by
  classical
  let h := hFun g
  let w (T : Finset ℕ) := ∏ p ∈ T, h p
  let E := ∏ p ∈ Q, (1+h p)
  let A := levelFamily Q z
  let B := Q.powerset \ A
  have hpos (p) (hq : p ∈ Q) : 0 < h p := div_pos (hg p hq).1 (sub_pos.mpr (hg p hq).2)
  have hE : 0 ≤ E := prod_nonneg fun p hq => by linarith [hpos p hq]
  have hA : A ⊆ Q.powerset := filter_subset _ _
  have hw (T) (hT : T ∈ Q.powerset) : 0 ≤ w T := prod_nonneg fun p hp' => (hpos p (mem_powerset.mp hT hp')).le
  have hl (T) (hT : T ∈ Q.powerset) :
      log ((∏ p ∈ T, p : ℕ):ℝ) = (∑ p ∈ T, log (p:ℝ)) := by
    push_cast
    rw [Real.log_prod]
    intro p hh
    exact_mod_cast (hp p (mem_powerset.mp hT hh)).ne_zero
  have heq (p) (hq : p ∈ Q) : h p / (1+h p) = g p := by
    change (g p/(1-g p)) / (1+g p/(1-g p)) = g p
    have hd : 0 < 1-g p := sub_pos.mpr (hg p hq).2
    have hden : 0 < 1+g p/(1-g p) := by positivity [ (hg p hq).1, hd ]
    apply (div_eq_iff hden.ne').mpr
    field_simp [hd.ne']
    ring
  have hweight : (∑ T ∈ Q.powerset, w T*(∑ p ∈ T, log (p:ℝ))) ≤ E*(log z/2) := by
    rw [show (∑ T ∈ Q.powerset, w T*(∑ p ∈ T, log (p:ℝ))) =
      E*(∑ p ∈ Q, (h p/(1+h p))*log p) from weighted_log Q h (fun p => log p)
        (fun p hq => (hpos p hq).le)]
    rw [sum_congr rfl (fun p hq => by rw [heq p hq])]
    exact mul_le_mul_of_nonneg_left hsmall hE
  have hzR : 1<(z:ℝ) := by exact_mod_cast hz
  have hb : (∑ T ∈ B, w T)*log z ≤ E*(log z/2) := by
    rw [sum_mul]
    apply le_trans _ hweight
    apply le_trans _ (sum_le_sum_of_subset_of_nonneg (s:=B) (t:=Q.powerset) (sdiff_subset) ?_)
    · apply sum_le_sum
      intro T ht
      obtain ⟨htQ,htA⟩ := mem_sdiff.mp ht
      have hn : z ≤ ∏ p ∈ T, p := by
        by_contra! h'
        exact htA (mem_filter.mpr ⟨htQ,h'⟩)
      apply mul_le_mul_of_nonneg_left _ (hw T htQ)
      rw [← hl T htQ]
      exact log_le_log (by linarith) (by exact_mod_cast hn)
    · intro T hT _
      exact mul_nonneg (hw T hT) (sum_nonneg fun p hh => log_nonneg
        (by exact_mod_cast (hp p (mem_powerset.mp hT hh)).one_lt.le))
  have hlz := Real.log_pos hzR
  have hb' : (∑ T ∈ B, w T) ≤ E / 2 := by
    apply (le_of_mul_le_mul_right (a := log z) ?_ hlz)
    linarith only [hb]
  have htotal : (∑ T ∈ B, w T)+(∑ T ∈ A, w T)=E := by
    rw [sum_sdiff hA]
    exact (prod_one_add Q).symm
  change E/2 ≤ ∑ T ∈ A, w T
  linarith

end Third971


open Finset Real OMALib.Sieve
open scoped Classical
namespace Third971

def pairCond (d : ℕ) (p n : ℕ) : Prop := p ∣ n * (n + d)

theorem pairCond_periodic (d p n : ℕ) : pairCond d p n ↔ pairCond d p (n % p) := by
  unfold pairCond
  simp only [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod, Nat.mod_mod]

theorem pairCond_iff_of_lt {d p r : ℕ} (hp : p.Prime) (hr : r < p) :
    pairCond d p r ↔ r = 0 ∨ r + d % p = p := by
  unfold pairCond
  rw [hp.dvd_mul]
  have hk : d % p < p := Nat.mod_lt _ hp.pos
  have e1 : p ∣ r ↔ r = 0 := ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hr, fun h => h ▸ dvd_zero p⟩
  have e2 : p ∣ r + d ↔ p ∣ r + d % p := by
    have : r + d = (r + d % p) + p * (d / p) := by
      have := Nat.mod_add_div d p; omega
    rw [this, Nat.dvd_add_left (dvd_mul_right p _)]
  have e3 : p ∣ r + d % p ↔ r + d % p = 0 ∨ r + d % p = p := by
    constructor
    · rintro ⟨m, hm⟩
      have : m < 2 := by
        by_contra h; push_neg at h
        have : p * 2 ≤ p * m := Nat.mul_le_mul_left _ h
        omega
      interval_cases m <;> simp_all
    · rintro (h | h) <;> rw [h]
      · exact dvd_zero p
  rw [e1, e2, e3]
  omega



def badResidue (a b q n : ℕ) : Prop := pairCond a q n ∨ pairCond b q n

lemma bad_periodic (a b q n : ℕ) : badResidue a b q n ↔ badResidue a b q (n%q) := by
  unfold badResidue; rw [pairCond_periodic a q n,pairCond_periodic b q n]

lemma bad_omega (a b q : ℕ) (hq : q.Prime) (ha : ¬q ∣ a) (hb : ¬q ∣ b)
    (hdiff : a%q ≠ b%q) : OMALib.Sieve.omega (badResidue a b) q = 3 := by
  classical
  have ha' : a%q ≠ 0 := fun h => ha (Nat.dvd_of_mod_eq_zero h)
  have hb' : b%q ≠ 0 := fun h => hb (Nat.dvd_of_mod_eq_zero h)
  have haq := Nat.mod_lt a hq.pos
  have hbq := Nat.mod_lt b hq.pos
  have hs : (range q).filter (badResidue a b q) = {0,q-a%q,q-b%q} := by
    ext n
    simp only [mem_filter,mem_range,mem_insert,mem_singleton]
    constructor
    · rintro ⟨hn,h⟩
      simp only [badResidue,pairCond_iff_of_lt hq hn] at h
      omega
    · intro h
      have hn : n<q := by omega
      refine ⟨hn,?_⟩
      simp only [badResidue,pairCond_iff_of_lt hq hn]
      omega
  unfold OMALib.Sieve.omega
  rw [hs,card_insert_of_notMem (by simp; omega),card_insert_of_notMem (by simp; omega),card_singleton]

lemma shift_sieve (X Y z a b : ℕ) (Q : Finset ℕ) (hz : 2≤z)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 3<q ∧ q≤Y ∧ ¬q ∣ a ∧ ¬q ∣ b ∧ a%q≠b%q) :
    (((Nat.primesLE X).filter fun p => (p+a).Prime ∧ (p+b).Prime).card:ℝ) ≤
    (Y+1:ℝ)+(X+1:ℝ)/selbergG (fun q : ℕ => 3/(q:ℝ)) (levelFamily Q z)+(z:ℝ)^4 := by
  classical
  have hω (q) (hq : q ∈ Q) : OMALib.Sieve.omega (badResidue a b) q = 3 :=
    bad_omega a b q (hQ q hq).1 (hQ q hq).2.2.2.1 (hQ q hq).2.2.2.2.1 (hQ q hq).2.2.2.2.2
  have hs := selberg_residue_level (X+1) z hz Q (fun q hq => (hQ q hq).1)
    (badResidue a b) (bad_periodic a b)
    (fun q hq => by rw [hω q hq]; decide)
    (fun q hq => by rw [hω q hq]; exact (hQ q hq).2.1)
  rw [selbergG_congr levelFamily_subset (fun q hq => show
    (OMALib.Sieve.omega (badResidue a b) q:ℝ)/q = 3/(q:ℝ) by rw [hω q hq]; norm_num)] at hs
  let F := (range (X+1)).filter fun n => ∀ q ∈ Q, ¬badResidue a b q n
  have hsub : ((Nat.primesLE X).filter fun p => (p+a).Prime ∧ (p+b).Prime) ⊆ range (Y+1) ∪ F := by
    intro n hn
    obtain ⟨hnp,hna,hnb⟩ := mem_filter.mp hn
    obtain ⟨hnX,hprime⟩ := Nat.mem_primesLE.mp hnp
    by_cases hnY : n≤Y
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (by omega),?_⟩
      intro q hq hd
      obtain ⟨hqp,_,hqY,_⟩ := hQ q hq
      have hne (r : ℕ) (hr : r.Prime) (hnr : n≤r) : ¬ q ∣ r := by
        intro hdiv
        have := (Nat.prime_dvd_prime_iff_eq hqp hr).mp hdiv
        omega
      rcases hd with hh | hh
      · rcases hqp.dvd_mul.mp hh with hh | hh
        · exact hne _ hprime le_rfl hh
        · exact hne _ hna (by omega) hh
      · rcases hqp.dvd_mul.mp hh with hh | hh
        · exact hne _ hprime le_rfl hh
        · exact hne _ hnb (by omega) hh
  have hl := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_range] at hl
  have hh : (((Nat.primesLE X).filter fun p => (p+a).Prime ∧ (p+b).Prime).card:ℝ)
      ≤ (Y+1:ℝ)+(F.card:ℝ) := by exact_mod_cast hl
  change (F.card:ℝ) ≤ _ at hs
  push_cast at hs
  linarith

end Third971


open Finset Real OMALib.Sieve OMALib.Mertens
open scoped Classical
namespace Third971

lemma local_one {p : ℕ} (hp : p.Prime) : 1 ≤ ((p:ℝ)/(p-1:ℝ))^3 := by
  have h : 1 < (p:ℝ) := by exact_mod_cast hp.one_lt
  apply one_le_pow₀
  exact (le_div_iff₀ (sub_pos.mpr h)).mpr (by linarith)

lemma loss_ge (n : ℕ) : 1 ≤ loss n :=
  Finset.one_le_prod fun p hp => local_one (Nat.prime_of_mem_primeFactors hp)

lemma loss_mul (a b : ℕ) (ha : 0<a) (hb : 0<b) :
    loss (a*b) ≤ loss a * loss b := by
  let w (p : ℕ) := ((p:ℝ)/(p-1:ℝ))^3
  have h := prod_union_inter (s₁:=a.primeFactors) (s₂:=b.primeFactors) (f:=w)
  have h1 : 1 ≤ ∏ p ∈ a.primeFactors ∩ b.primeFactors, w p :=
    Finset.one_le_prod fun p hp => local_one (Nat.prime_of_mem_primeFactors (mem_inter.mp hp).1)
  unfold loss
  rw [Nat.primeFactors_mul ha.ne' hb.ne']
  change (∏ p ∈ a.primeFactors ∪ b.primeFactors, w p) ≤ _
  rw [← h]
  apply le_mul_of_one_le_right _ h1
  apply prod_nonneg
  intro p hp
  have pr : p.Prime := (mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  exact zero_le_one.trans (local_one pr)

lemma loss_eq_ratio (n : ℕ) (hn : 0<n) : loss n = ((n:ℝ)/n.totient)^3 := by
  unfold loss
  rw [prod_pow,prod_div_distrib]
  congr 1
  have hp : ∀ p ∈ n.primeFactors, 1 < (p:ℝ) := fun p h => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_lt
  have hp0 : 0 < ∏ p ∈ n.primeFactors, ((p:ℝ)-1) := prod_pos fun p h => sub_pos.mpr (hp p h)
  have hφ : 0 < (n.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  apply (div_eq_div_iff hp0.ne' hφ.ne').mpr
  have hh := congrArg (Nat.cast : ℕ → ℝ) (Nat.totient_mul_prod_primeFactors n)
  push_cast at hh
  rw [mul_comm]
  convert hh using 2
  apply prod_congr rfl
  intro p h
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors h).one_lt.le,Nat.cast_one]

lemma product_bound (Y D : ℕ) (hY : 4≤Y) (P : Finset ℕ) (hP : P=Nat.primesLE Y)
    (Q : Finset ℕ) (hq : Q=P \ D.primeFactors) (hgood : ∀ p ∈ Q, 3<p) :
    (∏ p ∈ Q, (1-3/(p:ℝ))) ≤ (exp mertens2Const/log Y)^3 * loss D := by
  classical
  let b (p : ℕ) := (1-1/(p:ℝ))^3
  have hprime {p} (hp : p ∈ P) : p.Prime := (Nat.mem_primesLE.mp (hP ▸ hp)).2
  have hlocal (p) (hp : p ∈ P) : 0 < 1-1/(p:ℝ) := by
    have h1 : 1 < (p:ℝ) := by exact_mod_cast (hprime hp).one_lt
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr h1)
  have hQ : Q ⊆ P := hq ▸ sdiff_subset
  have hprod : (∏ p ∈ Q, b p) =
      (∏ p ∈ P, b p) * (∏ p ∈ P \ Q, ((p:ℝ)/(p-1:ℝ))^3) := by
    rw [← prod_sdiff hQ, mul_right_comm,← prod_mul_distrib]
    have hh : (∏ p ∈ P \ Q, b p * ((p:ℝ)/(p-1:ℝ))^3) = 1 := by
      apply prod_eq_one
      intro p hp
      have h1 : 1<(p:ℝ) := by exact_mod_cast (hprime (mem_sdiff.mp hp).1).one_lt
      dsimp [b]
      have hcalc : (1-1/(p:ℝ))*((p:ℝ)/(p-1))=1 := by
        field_simp [sub_ne_zero.mpr h1.ne',show (p:ℝ) ≠ 0 by linarith]
      rw [← mul_pow,hcalc,one_pow]
    rw [hh,one_mul]
  have hn : P \ Q ⊆ D.primeFactors := by
    intro p hp
    obtain ⟨h1,h2⟩ := mem_sdiff.mp hp
    by_contra h
    exact h2 (hq ▸ mem_sdiff.mpr ⟨h1,h⟩)
  have hM := (prod_one_sub_inv_bounds (Y:ℝ) (by exact_mod_cast (show 2≤Y by omega))).2
  rw [Nat.floor_natCast,← hP] at hM
  calc
    _ ≤ ∏ p ∈ Q, b p := by
      apply prod_le_prod
      · intro p hp
        have h3 : 3<(p:ℝ) := by exact_mod_cast hgood p hp
        exact (sub_nonneg.mpr ((div_le_one (by linarith)).mpr h3.le))
      · intro p hp
        have h1 := hlocal p (hQ hp)
        have hv : 0≤(1:ℝ)/p := by positivity
        dsimp [b]
        nlinarith only [mul_nonneg (sq_nonneg ((1:ℝ)/p)) (show 0≤3-1/(p:ℝ) by linarith),
          show 3/(p:ℝ) = 3*(1/p) by ring]
    _ = _ := hprod
    _ ≤ _ := by
      apply mul_le_mul _ _ (prod_nonneg fun p hp =>
        zero_le_one.trans (local_one (hprime (mem_sdiff.mp hp).1))) (by positivity)
      · dsimp [b]; rw [prod_pow]
        exact pow_le_pow_left₀ (prod_nonneg fun p hp => (hlocal p hp).le) hM _
      · exact prod_le_prod_of_subset_of_one_le hn (fun p hp => zero_le_one.trans (local_one (Nat.prime_of_mem_primeFactors (hn hp)))) (fun p hp _ => local_one (Nat.prime_of_mem_primeFactors hp))

lemma sieve_main (Y D : ℕ) (hY : 4≤Y) (Q : Finset ℕ)
    (hq : Q=Nat.primesLE Y \ D.primeFactors) (hgood : ∀ p ∈ Q, 3<p) :
    let g (p : ℕ) := 3/(p:ℝ)
    let G := selbergG g (levelFamily Q (Y^12))
    0 < G ∧ 1/G ≤ 2*(exp mertens2Const/log Y)^3*loss D := by
  classical
  intro g G
  have sub : Q ⊆ Nat.primesLE Y := hq ▸ sdiff_subset
  have pr (p) (hp : p ∈ Q) := (Nat.mem_primesLE.mp (sub hp)).2
  have hg (p) (hp : p ∈ Q) : 0< g p ∧ g p<1 := by
    have h3 : 3<(p:ℝ) := by exact_mod_cast hgood p hp
    exact ⟨div_pos (by norm_num) (by linarith),(div_lt_one (by linarith)).mpr h3⟩
  have hsm : ∑ p ∈ Q, g p*log p ≤ log (Y^12:ℕ)/2 := by
    have hu := (sum_le_sum_of_subset_of_nonneg sub (f:=fun p : ℕ => log p / p)
      (fun p hp _ => div_nonneg (log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le))
        (Nat.cast_nonneg p))).trans (sum_log_div_le_nat Y)
    have h4 : log 4 ≤ log Y := log_le_log (by norm_num) (by exact_mod_cast hY)
    rw [show (∑ p ∈ Q, g p*log p) = 3*∑ p ∈ Q, log p/p by
      rw [mul_sum]; exact sum_congr rfl fun p _ => by dsimp [g]; ring]
    push_cast
    rw [Real.log_pow]
    linarith
  have hz : 1<Y^12 := one_lt_pow₀ (by omega) (by decide)
  have hh := normalizer_half Q (Y^12) hz g pr hg hsm
  let V := ∏ p ∈ Q, (1-g p)
  have hV : 0<V := prod_pos fun p hp => sub_pos.mpr (hg p hp).2
  have he : (∏ p ∈ Q, (1+hFun g p))=1/V := by
    change _ = 1/(∏ p ∈ Q, (1-g p))
    rw [one_div,← prod_inv_distrib]
    apply prod_congr rfl
    intro p hp
    unfold hFun
    have hd := sub_pos.mpr (hg p hp).2
    field_simp [hd.ne']
    ring
  rw [he] at hh
  change (1/V)/2 ≤ G at hh
  have hG : 0<G := lt_of_lt_of_le (by positivity) hh
  have hv := product_bound Y D hY (Nat.primesLE Y) rfl Q hq hgood
  change V ≤ _ at hv
  refine ⟨hG,le_trans ?_ (show 2*V ≤ _ by linarith only [hv])⟩
  apply (div_le_iff₀ hG).2
  have := (div_le_iff₀ hV).mp (show 1/V ≤ 2*G by linarith)
  linarith only [this,show 2*V*G = 2*G*V by ring]

end Third971


open Finset Real
open scoped Classical
namespace Third971

lemma triple_average (J : ℕ) :
    let U := ((Icc 1 J) ×ˢ (Icc 1 J)).filter fun v => v.1<v.2
    ∑ v ∈ U, loss v.1*loss v.2*loss (v.2-v.1) ≤ 3*(J:ℝ)^2*exp (2*4608) := by
  classical
  intro U
  let I := Ioc 0 J
  let V := I ×ˢ I
  let w (i : ℕ) := (loss i)^3
  have wp (i) : 0 ≤ w i := pow_nonneg (loss_pos i).le _
  have hI : Icc 1 J = I := by ext; simp [I]; omega
  have hU : U ⊆ V := by simpa only [U,V,hI] using
    (filter_subset (fun v : ℕ×ℕ => v.1<v.2) ((Icc 1 J) ×ˢ Icc 1 J))
  have hl (v) (hv : v ∈ U) : v.1 < v.2 := (mem_filter.mp hv).2
  let f (v : ℕ×ℕ) := (v.1,v.2-v.1)
  have hf : Set.InjOn f U := by
    rintro ⟨i,j⟩ h ⟨i',j'⟩ h' e
    have h1 : i=i' := congrArg Prod.fst e
    have h2 : j-i=j'-i' := congrArg Prod.snd e
    have a : i<j := hl _ h
    have b : i'<j' := hl _ h'
    congr 1 <;> omega
  have hV : U.image f ⊆ V := by
    rintro _ ht
    obtain ⟨⟨i,j⟩,hm,rfl⟩ := mem_image.mp ht
    obtain ⟨hi,hj⟩ := mem_product.mp (hU hm)
    obtain ⟨_,hjb⟩ := mem_Ioc.mp hj
    have hij : i<j := hl _ hm
    exact mem_product.mpr ⟨hi,mem_Ioc.mpr ⟨Nat.sub_pos_of_lt hij,(Nat.sub_le j i).trans hjb⟩⟩
  let L := (J:ℝ)^2 * exp (2*4608)
  have hb : (J:ℝ)*(∑ n ∈ I,w n) ≤ L := by
    have := mul_le_mul_of_nonneg_left (mean_loss_cube J) (Nat.cast_nonneg (α:=ℝ) J)
    dsimp only [L,w,I]
    linarith only [this,show (J:ℝ)*(J*exp (2*4608)) = (J:ℝ)^2*exp (2*4608) by ring]
  have hcard : I.card=J := by simp [I]
  have hfst : (∑ v ∈ V, w v.1) ≤ L := by
    dsimp only [V]
    simp only [sum_product,sum_const,hcard,nsmul_eq_mul,← mul_sum]; exact hb
  have hsnd : (∑ v ∈ V, w v.2) ≤ L := by
    dsimp only [V]
    simp only [sum_product,sum_const,hcard,nsmul_eq_mul]; exact hb
  have hdf : (∑ v ∈ U, w (v.2-v.1)) ≤ L := by
    have hh := (sum_le_sum_of_subset_of_nonneg hV (f:=fun v : ℕ×ℕ => w v.2)
      (fun v _ _ => wp v.2)).trans hsnd
    rwa [sum_image (fun _ a _ b e => hf a b e)] at hh
  have h1 := (sum_le_sum_of_subset_of_nonneg hU (f:=fun v : ℕ×ℕ => w v.1)
    (fun v _ _ => wp v.1)).trans hfst
  have h2 := (sum_le_sum_of_subset_of_nonneg hU (f:=fun v : ℕ×ℕ => w v.2)
    (fun v _ _ => wp v.2)).trans hsnd
  have ham (a b c : ℕ) : loss a*loss b*loss c ≤ w a+w b+w c := by
    let u := max (loss a) (max (loss b) (loss c))
    have hA : loss a ≤ u := le_max_left .. 
    have hB : loss b ≤ u := (le_max_left ..).trans (le_max_right ..)
    have hC : loss c ≤ u := (le_max_right ..).trans (le_max_right ..)
    have hprod : loss a*loss b*loss c ≤ u*u*u :=
      mul_le_mul (mul_le_mul hA hB (loss_pos b).le ((loss_pos a).le.trans hA)) hC (loss_pos c).le
        (mul_nonneg ((loss_pos a).le.trans hA) ((loss_pos a).le.trans hA))
    rcases le_total (loss a) (max (loss b) (loss c)) with h | h
    · rw [show u=max (loss b) (loss c) from max_eq_right h] at hprod
      rcases le_total (loss b) (loss c) with h | h
      · rw [max_eq_right h] at hprod; dsimp [w] at *; nlinarith only [hprod,wp a,wp b]
      · rw [max_eq_left h] at hprod; dsimp [w] at *; nlinarith only [hprod,wp a,wp c]
    · rw [show u=loss a from max_eq_left h] at hprod; dsimp [w] at *; nlinarith only [hprod,wp b,wp c]
  apply (sum_le_sum fun v (_ : v ∈ U) => ham v.1 v.2 (v.2-v.1)).trans
  rw [sum_add_distrib,sum_add_distrib]
  change _ ≤ 3*(J:ℝ)^2*exp (2*4608)
  dsimp only [L] at hdf h1 h2
  linarith

end Third971


open Finset Filter Real
namespace Third971

lemma scales : ∀ᶠ d : ℕ in atTop,
    let t := log (d:ℝ)
    let Y := ⌊exp (t/100)⌋₊
    let J := ⌊t⌋₊+1
    let X := ⌊(d.totient:ℝ)*t⌋₊
    0<d ∧ 1≤t ∧ 4≤Y ∧ t ≤ 200*log Y ∧ (J:ℝ) ≤ 2*t ∧ X<(J+1)*d ∧
      (X+1:ℝ) ≤ 2*d*t ∧ ((Y+1:ℝ)+(Y:ℝ)^48)*t^2 ≤ 3*d ∧
      ((Nat.primesLE X).card:ℝ) ≤ (log 4+1)*d := by
  have htend := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hyend : Tendsto (fun d : ℕ => (d:ℝ)*log d) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ htend
  have hpi := hyend.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
  filter_upwards [eventually_ge_atTop 2,htend.eventually_ge_atTop 1000,hpi] with d hd hlg hp
  let t := log (d:ℝ)
  let Y := ⌊exp (t/100)⌋₊
  let J := ⌊t⌋₊+1
  let X := ⌊(d.totient:ℝ)*t⌋₊
  have ht : 1000 ≤ t := hlg
  have hdR : 2 ≤ (d:ℝ) := by exact_mod_cast hd
  have hdn : 0<d := by omega
  have hpos : 0<t := by linarith
  have hex := Real.exp_log (show 0<(d:ℝ) by positivity)
  change exp t = d at hex
  have hu : 6 ≤ exp (t/200) := by linarith [Real.add_one_le_exp (t/200)]
  have hsq : exp (t/200)*exp (t/200)=exp (t/100) := by rw [← Real.exp_add]; congr 1; ring
  have hfloor := Nat.lt_floor_add_one (exp (t/100))
  change exp (t/100)<(Y:ℝ)+1 at hfloor
  have hYlo : exp (t/200) ≤ (Y:ℝ) := by nlinarith [hsq,hu,hfloor]
  have hY : 4≤Y := by exact_mod_cast (show (4:ℝ) ≤ Y by linarith)
  have hlogY := Real.log_le_log (Real.exp_pos _) hYlo
  rw [Real.log_exp] at hlogY
  have hYhi : (Y:ℝ) ≤ exp (t/100) := Nat.floor_le (Real.exp_pos _).le
  have hhalf : (Y:ℝ)^48 ≤ exp (t/2) := by
    calc
      _ ≤ exp (t/100)^48 := pow_le_pow_left₀ (Nat.cast_nonneg Y) hYhi _
      _ = exp ((48:ℕ)*(t/100)) := (Real.exp_nat_mul _ _).symm
      _ ≤ exp (t/2) := Real.exp_le_exp.mpr (by norm_num; linarith)
  have hlin : (Y:ℝ) ≤ exp (t/2) := hYhi.trans (Real.exp_le_exp.mpr (by linarith))
  have he1 : 1≤exp (t/2) := Real.one_le_exp (by linarith)
  have he2 := Real.pow_div_factorial_le_exp (t/2) (by linarith) 3
  norm_num at he2
  have ht2 : t^2 ≤ exp (t/2) := by
    nlinarith only [he2,mul_nonneg (show 0≤t-48 by linarith) (sq_nonneg t)]
  have herr := mul_le_mul (show (Y+1:ℝ)+(Y:ℝ)^48 ≤ 3*exp (t/2) by linarith) ht2
    (sq_nonneg t) (by positivity)
  rw [mul_assoc,← Real.exp_add,show t/2+t/2=t by ring,hex] at herr
  have hjhi : (J:ℝ) ≤ t+1 := by dsimp [J]; push_cast; linarith [Nat.floor_le hpos.le]
  have hjlo : t < (J:ℝ) := by simpa [J] using Nat.lt_floor_add_one t
  have hXhi : (X:ℝ) ≤ (d:ℝ)*t := (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) hpos.le)).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le d) hpos.le)
  have hXn : X<(J+1)*d := by
    have hJ := mul_lt_mul_of_pos_left hjlo (show 0<(d:ℝ) by positivity)
    exact_mod_cast (show (X:ℝ)<((J:ℝ)+1)*(d:ℝ) by nlinarith only [hXhi,hJ,hdR])
  have hpi' : (Nat.primeCounting X:ℝ) ≤ (log 4+1)*((d:ℝ)*t)/log ((d:ℝ)*t) := by
    apply le_trans _ hp
    exact_mod_cast Nat.monotone_primeCounting (Nat.le_floor hXhi)
  have hdle : (d:ℝ) ≤ (d:ℝ)*t := le_mul_of_one_le_right (by positivity) (by linarith)
  have hlog := Real.log_le_log (show 0<(d:ℝ) by positivity) hdle
  change t ≤ _ at hlog
  have hscale : ((Nat.primesLE X).card:ℝ) ≤ (log 4+1)*d := by
    rw [Nat.primesLE_card_eq_primeCounting]
    apply hpi'.trans
    apply (div_le_iff₀ (hpos.trans_le hlog)).mpr
    calc
      _ = ((log 4+1)*(d:ℝ))*t := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity [Real.log_nonneg (by norm_num : 1≤(4:ℝ))])
  refine ⟨hdn,by linarith,hY,by linarith,by linarith,hXn,?_,herr,hscale⟩
  nlinarith only [hXhi,hdle,hdR]

end Third971


open Finset OMALib.Sieve OMALib.Mertens Real
open scoped Classical
namespace Third971

lemma sieve_triple (X Y d i j : ℕ) (hY : 4≤Y) (hd : 0<d) (hi : 0 < i) (hij : i<j) :
    (((Nat.primesLE X).filter fun p => (p+i*d).Prime ∧ (p+j*d).Prime).card:ℝ) ≤
    (Y+1:ℝ)+(X+1:ℝ)*(2*(exp mertens2Const/log Y)^3*
      (loss 6*loss d*loss i*loss j*loss (j-i)))+(Y:ℝ)^48 := by
  classical
  let D := 6*d*i*j*(j-i)
  have hj : 0 < j := hi.trans hij
  have hg : 0 < j-i := Nat.sub_pos_of_lt hij
  have hD : 0 < D := by dsimp [D]; positivity
  let Q := Nat.primesLE Y \ D.primeFactors
  have info (q) (hq : q ∈ Q) : q.Prime ∧ 3<q ∧ q≤Y ∧ ¬q ∣ i*d ∧ ¬q ∣ j*d ∧ (i*d)%q≠(j*d)%q := by
    obtain ⟨hmem,hn⟩ := mem_sdiff.mp hq
    obtain ⟨hqY,hpr⟩ := Nat.mem_primesLE.mp hmem
    have hnd : ¬ q ∣ D := fun h => hn (Nat.mem_primeFactors.mpr ⟨hpr,h,hD.ne'⟩)
    have h6 : ¬q ∣ 6 := fun h => hnd (h.trans (show 6 ∣ D from ⟨d*i*j*(j-i),by dsimp [D]; ring⟩))
    have hq3 : 3<q := by
      by_contra! hq3
      interval_cases q <;> norm_num at *
    have hai : i*d ∣ D := ⟨6*j*(j-i),by dsimp [D]; ring⟩
    have haj : j*d ∣ D := ⟨6*i*(j-i),by dsimp [D]; ring⟩
    refine ⟨hpr,hq3,hqY,fun h => hnd (h.trans hai),fun h => hnd (h.trans haj),?_⟩
    intro hh
    have hh' := (Nat.modEq_iff_dvd' (Nat.mul_le_mul_right d hij.le)).mp hh
    rw [← Nat.sub_mul] at hh'
    exact hnd (hh'.trans ⟨6*i*j,by dsimp [D]; ring⟩)
  have hz : 2 ≤ Y^12 := one_lt_pow₀ (show 1<Y by omega) (show (12:ℕ) ≠ 0 by decide)
  have hs := shift_sieve X Y (Y^12) (i*d) (j*d) Q hz info
  obtain ⟨_,hmain⟩ := sieve_main Y D hY Q rfl (fun q hq => (info q hq).2.1)
  have hloss : loss D ≤ loss 6*loss d*loss i*loss j*loss (j-i) := by
    have hG0 := (loss_pos (j-i)).le
    have hJ0 := (loss_pos j).le
    have hI0 := (loss_pos i).le
    dsimp only [D]
    calc
      _ ≤ loss (6*d*i*j)*loss (j-i) := loss_mul _ _ (by positivity) hg
      _ ≤ loss (6*d*i)*loss j*loss (j-i) := by
        exact mul_le_mul_of_nonneg_right (loss_mul (6*d*i) j (by positivity) hj) hG0
      _ ≤ loss (6*d)*loss i*loss j*loss (j-i) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (loss_mul (6*d) i (by positivity) hi) hJ0) hG0
      _ ≤ _ := by exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (loss_mul 6 d (by decide) hd) hI0) hJ0) hG0
  have hlog : 0 < log (Y:ℝ) := Real.log_pos (by exact_mod_cast (show 1<Y by omega))
  have h1 := hmain.trans (mul_le_mul_of_nonneg_left hloss (by positivity))
  apply hs.trans
  push_cast
  rw [← pow_mul,show 12*4=48 by decide]
  gcongr 2
  rw [div_eq_mul_inv,← one_div]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

end Third971


open Filter Finset Real OMALib.Mertens
open scoped Classical
namespace Third971

lemma triple_bound (M t : ℝ) (hM : 0<M) (ht : 1≤t) (X Y d i j : ℕ) (hY : 4≤Y)
    (hd : 0<d) (hi : 0 < i) (hij : i<j) (hr : (d:ℝ) ≤ M*d.totient)
    (hlY : t ≤ 200*log Y) (hX : (X+1:ℝ) ≤ 2*d*t)
    (hE : ((Y+1:ℝ)+(Y:ℝ)^48)*t^2 ≤ 3*d) :
    let K := 3+4*(200*exp mertens2Const)^3*loss 6*M^3
    (((Nat.primesLE X).filter fun p => (p+i*d).Prime ∧ (p+j*d).Prime).card:ℝ) ≤
      K*d/t^2 * (loss i*loss j*loss (j-i)) := by
  intro K
  let W := loss i*loss j*loss (j-i)
  let C := exp mertens2Const
  have hW : 1≤W := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (loss_ge i) (loss_ge j)) (loss_ge _)
  have hW0 : 0≤W := zero_le_one.trans hW
  have hC : 0<C := exp_pos _
  have hlog : 0<log (Y:ℝ) := log_pos (by exact_mod_cast (show 1<Y by omega))
  have ht0 : 0<t := by linarith
  have hφ : 0<(d.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hloss : loss d ≤ M^3 := by
    rw [loss_eq_ratio d hd]
    exact pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hφ).mpr hr) _
  have hsmall : (C*t/log Y)^3 ≤ (200*C)^3 := by
    apply pow_le_pow_left₀ (by positivity)
    apply (div_le_iff₀ hlog).mpr
    linarith only [mul_le_mul_of_nonneg_left hlY hC.le]
  have hd0 := (loss_pos d).le
  have h6 := (loss_pos 6).le
  have hs := sieve_triple X Y d i j hY hd hi hij
  have hm : ((X+1:ℝ)*(2*(C/log Y)^3*(loss 6*loss d*loss i*loss j*loss (j-i))))*t^2 ≤
      4*(200*C)^3*loss 6*M^3*d*W := by
    calc
      _ ≤ (2*d*t)*(2*(C/log Y)^3*(loss 6*loss d*W))*t^2 := by
        rw [show loss 6*loss d*loss i*loss j*loss (j-i) = loss 6*loss d*W by dsimp [W]; ring]
        gcongr <;> positivity
      _ = 4*(C*t/log Y)^3*loss 6*loss d*d*W := by ring
      _ ≤ _ := by
        have hl := (loss_pos d).le
        gcongr
  have he := mul_le_mul_of_nonneg_left hW (show 0≤3*(d:ℝ) by positivity)
  have hb := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
  change (((Nat.primesLE X).filter fun p => (p+i*d).Prime ∧ (p+j*d).Prime).card:ℝ) ≤ K*d/t^2*W
  rw [div_mul_eq_mul_div,le_div_iff₀ (sq_pos_of_pos ht0)]
  dsimp only [K]
  change _ ≤ (3+4*(200*C)^3*loss 6*M^3)*d*W
  change _ ≤ ((Y+1:ℝ)+(X+1:ℝ)*(2*(C/log Y)^3*(loss 6*loss d*loss i*loss j*loss (j-i)))+
    (Y:ℝ)^48)*t^2 at hb
  linarith only [hb,hE,hm,he]

theorem third_moment : OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1.H2 := by
  classical
  intro M hM
  let K := 3+4*(200*exp mertens2Const)^3*loss 6*M^3
  let B := exp (2*4608 : ℝ)
  let V := 27*(log 4+1)+27*12*K*B
  have hK : 0<K := by dsimp [K]; positivity [loss_pos 6]
  have hB : 0<B := exp_pos _
  have hV : 0<V := by dsimp [V]; positivity [log_nonneg (by norm_num : 1≤(4:ℝ))]
  refine ⟨V*M,mul_pos hV hM,?_⟩
  filter_upwards [scales] with d hs
  intro hr
  let t := log (d:ℝ)
  let X := ⌊(d.totient:ℝ)*t⌋₊
  let Y := ⌊exp (t/100)⌋₊
  let J := ⌊t⌋₊+1
  let A := (range d).filter fun a => a.Coprime d
  let U := ((Icc 1 J) ×ˢ (Icc 1 J)).filter fun v => v.1<v.2
  let T (v : ℕ×ℕ) := (Nat.primesLE X).filter fun p => (p+v.1*d).Prime ∧ (p+v.2*d).Prime
  let w (v : ℕ×ℕ) := loss v.1*loss v.2*loss (v.2-v.1)
  obtain ⟨hd,ht,hY,hlY,hJ,hXd,hX,hE,hP⟩ := hs
  have ht0 : 0<t := by change 1≤t at ht; linarith
  have main := finite_moment X d J hd hXd A
  have htr (v : ℕ×ℕ) (hv : v ∈ U) : ((T v).card:ℝ) ≤ K*d/t^2*w v := by
    obtain ⟨hh,hij⟩ := mem_filter.mp hv
    exact triple_bound M t hM ht X Y d v.1 v.2 hY hd
      (mem_Icc.mp (mem_product.mp hh).1).1 hij hr hlY hX hE
  have hs1 := sum_le_sum htr
  rw [← mul_sum] at hs1
  have hs2 : (∑ v ∈ U, w v) ≤ 3*(J:ℝ)^2*B := triple_average J
  have hj2 : (J:ℝ)^2 ≤ (2*t)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hJ _
  have hs3 : (∑ v ∈ U, ((T v).card:ℝ)) ≤ 12*K*B*d := by
    calc
      _ ≤ (K*d/t^2)*(3*(J:ℝ)^2*B) := hs1.trans (mul_le_mul_of_nonneg_left hs2 (by positivity))
      _ ≤ (K*d/t^2)*(3*(2*t)^2*B) := by gcongr
      _ = _ := by field_simp; ring
  have he : (↑(∑ a ∈ A, (((Nat.primesLE X).filter fun p => p%d=a).card)^3):ℝ) ≤
    27*((Nat.primesLE X).card:ℝ)+27*∑ v ∈ U, ((T v).card:ℝ) := by exact_mod_cast main
  apply he.trans
  apply le_trans _ (show V*(d:ℝ) ≤ (V*M)*d.totient by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hr hV.le)
  change 27*((Nat.primesLE X).card:ℝ)+27*∑ v ∈ U, ((T v).card:ℝ) ≤
    (27*(log 4+1)+27*12*K*B)*d
  linarith only [hP,hs3]

end Third971


private theorem h2_proof : OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1.H2 := by
  exact Third971.third_moment
end

section
section PNTX_Base

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function


open Filter Topology

namespace Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Asymptotics


open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith

end PNTX_Base

-- Ported from PrimeNumberTheoremAnd: Sobolev.lean
section PNTX_Sobolev

open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun

theorem CS.ext {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : CS n E}
    (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1

structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)

abbrev W21 := W1 2 ℂ

section lemmas

noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)

lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const

omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)

end lemmas

namespace CS

variable {f : CS n E} {R x v : ℝ}

instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun

instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩

def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2

instance : Neg (CS n E) where neg := neg

@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl

def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩

instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul

@[simp] lemma smul_apply : (R • f) x = R • f x := rfl

lemma continuous (f : CS n E) : Continuous f := f.h1.continuous

noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv

lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt

lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl

lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  refine CS.ext (funext fun x => ?_) ; exact (f.hasDerivAt x |>.const_smul R).deriv

noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)

lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  refine CS.ext (funext fun v => ?_) ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv

lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]

lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl

lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]

lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩

end CS

namespace trunc

instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun

instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS

lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)

lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x

lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))

@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds

end trunc

namespace W1

instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun

lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous

lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)

lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]

noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)

lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt

def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)

instance : Sub (W1 n E) where sub := sub

lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)

noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz

end W1

namespace W21

variable {f : W21}

noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun

noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz

def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv

instance : Coe (CS 2 ℂ) W21 where coe := ofCS2

instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩

instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f

lemma hf (f : W21) : Integrable f := f.integrable zero_le_two

lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two

lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl

end W21

theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by

  -- Definitions
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv

  -- Properties of h
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)

  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4

  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]

    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

end PNTX_Sobolev

-- Ported from PrimeNumberTheoremAnd: Fourier.lean
section PNTX_Fourier

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])

@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _ -- `scomp` introduces ℝ-smul on ℂ, which we undo
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable (ae_of_all _ e.norm_coe_le_norm)

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

/-- If, eventually in `T`, the integrand `f T` is bounded on `uIoc lo hi` by `B T`
and `B T * |hi - lo| → 0`, then the interval integral `∫ x in lo..hi, f T x → 0`. -/
lemma tendsto_intervalIntegral_zero_of_uniform_norm_bound
    {f : ℝ → ℝ → ℂ} {lo hi : ℝ} {B : ℝ → ℝ}
    (hB : Filter.Tendsto (fun T : ℝ => B T * |hi - lo|) Filter.atTop (nhds 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ x ∈ Set.uIoc lo hi, ‖f T x‖ ≤ B T) :
    Filter.Tendsto (fun T : ℝ => ∫ x in lo..hi, f T x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [hf] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hT x hx)

/-- The decay `K * (log (T + 2) / (T + 2)) → 0` as `T → ∞`, for any constant `K`. -/
lemma tendsto_const_mul_log_add_two_div_add_two_atTop (K : ℝ) :
    Filter.Tendsto (fun T : ℝ => K * (Real.log (T + 2) / (T + 2)))
      Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0))
  have hshift : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2))
      Filter.atTop (nhds 0) := by
    have := h0.comp (tendsto_atTop_add_const_right Filter.atTop 2 tendsto_id)
    simpa [Function.comp_def] using this
  simpa using hshift.const_mul K

/-- Fourier-transform decay from an integrable derivative: for integrable,
differentiable `g` with integrable derivative, `‖𝓕 g w‖ ≤ (∫ ‖deriv g x‖) / (2π·|w|)`. -/
lemma norm_fourier_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {w : ℝ} (hw : w ≠ 0) :
    ‖𝓕 g w‖ ≤ (∫ x, ‖deriv g x‖ ∂volume) / ((2 * Real.pi) * |w|) := by
  have hmul :
      𝓕 (deriv g) w = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w := by
    have h := congrFun (Real.fourier_deriv hg hdiff hg') w
    simpa [smul_eq_mul, mul_assoc] using h
  have h_fourier :
      ‖𝓕 (deriv g) w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      (deriv g) w
  have hleft :
      ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ =
        ‖(2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w‖ := by
    have htwopi : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le]
    have hwc : ‖(w : ℂ)‖ = |w| := by rw [norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_mul, htwopi, norm_I, hwc]
    ring
  have hmain : ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    rw [hleft, ← hmul]
    exact h_fourier
  have hpos : 0 < (2 * Real.pi) * |w| := by
    positivity
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)

/-- The oscillatory-integral form of the decay bound: for `0 < T`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / T`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : 0 < T) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / T := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT.ne') (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = T := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    have hneg : -T / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hT) htwopi_pos
    rw [abs_of_neg hneg]
    field_simp [Real.pi_ne_zero]
  rw [hden]

/-- The `|T|` variant of the oscillatory-integral decay bound: for `T ≠ 0`,
`‖∫ g y · exp(T·i·y)‖ ≤ (∫ ‖deriv g x‖) / |T|`. -/
lemma norm_oscillatory_integral_le_integral_deriv_div_abs
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : T ≠ 0) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / |T| := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT) (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = |T| := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    rw [abs_div, abs_neg, abs_of_pos htwopi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hden]

end PNTX_Fourier

-- Ported from PrimeNumberTheoremAnd: SmoothExistence.lean
section PNTX_Smooth

open MeasureTheory Set Real
open scoped ContDiff

lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]



lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith

end PNTX_Smooth

-- Ported from PrimeNumberTheoremAnd: Wiener.lean (up to and including theorem WeakPNT)
section PNTX_Wiener

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]



noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'

lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]

theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s

lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]

instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)


lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop

lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]

lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group

lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by

  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp



lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩


lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    -- `Multiplicative.ofAdd x` is definitionally `x`; unfold it by `change` since `fun_prop`
    -- does not see through it.
    change Measurable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
      (𝐞 (-(a * (u / (2 * π)))) : ℂ) • ψ a)
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2

lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith

lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring

lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by

  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  simp_rw [← mul_assoc]
  rw [integral_mul_const]
  congr 1
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      -↑u * (↑σ' - 1) + 2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx



lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)

theorem prelim_decay (ψ : ℝ → ℂ) (u : ℝ) : ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ ∫ t, ‖ψ t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm ..

lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm

lemma decay_bounds_aux {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h

theorem decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply decay_bounds_aux f.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply decay_bounds_aux f.deriv.deriv.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA'
  apply decay_bounds_key f u |>.trans
  change W21.norm _ * _ ≤ _
  simp_rw [W21.norm, div_eq_mul_inv, add_mul, l0] ; gcongr

lemma decay_bounds (ψ : CS 2 ℂ) (hA : ∀ t, ‖ψ t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv^[2] ψ t‖ ≤ A / (1 + t ^ 2)) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  exact decay_bounds_W21 ψ hA hA' u

lemma decay_bounds_cor_aux (ψ : CS 2 ℂ) : ∃ C : ℝ, ∀ u, ‖ψ u‖ ≤ C / (1 + u ^ 2) := by
  have l1 : HasCompactSupport (fun u : ℝ => ((1 + u ^ 2) : ℝ) * ψ u) := by exact ψ.h2.mul_left
  have := ψ.h1.continuous
  obtain ⟨C, hC⟩ := l1.exists_bound_of_continuous (by fun_prop)
  refine ⟨C, fun u => ?_⟩
  specialize hC u
  simp only [norm_mul, Complex.norm_real, norm_of_nonneg (one_add_sq_pos u).le] at hC
  rwa [le_div_iff₀' (one_add_sq_pos _)]

lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩

lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf

lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)





lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by

  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))

-- Here compact support is used but perhaps it is not necessary
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left

  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]

section nabla

variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}

def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i

def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n

/- `nnabla` is the backward difference `u n - u (n+1)`; kept alongside `nabla`
   for summation-by-parts identities that prefer that orientation. -/
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)

def shift (u : α → E) (n : α) : E := u (n + 1)

@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]

lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]

@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]

lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])

lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)

omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]

omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]

omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]

lemma nnabla_cast (u : ℝ → E) [Sub E] : nnabla u ∘ ((↑) : ℕ → ℝ) = nnabla (u ∘ (↑)) := by
  ext n ; simp [nnabla]

end nabla

lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl

lemma Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front

lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]

lemma Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by
  ext n ; apply Finset.sum_shift_back

lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel

lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)

lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'

lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1

lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO

lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]

lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }

lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩

lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]

lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1

lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h

lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]

lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp

lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)

lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]

lemma isBigO_pow_pow_of_le {m n : ℕ} (h : m ≤ n) :
    (fun x : ℝ => x ^ m) =O[atTop] (fun x : ℝ => x ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with x l1
  simpa [abs_eq_self.mpr (zero_le_one.trans l1)] using pow_le_pow_right₀ l1 h

lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)

lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1

lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp

lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp

lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)

lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h

lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring

lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le

lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1

lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring

lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by

  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)

  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))

lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb

lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)

lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)

/-- Should this be a gcongr lemma? -/
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith

lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by

  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _

  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]

  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    exact norm_lt_norm_of_nonneg _ _ (inv_nonneg.mpr e2.le) (inv_anti₀ e1 e3)

  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)

  apply EventuallyEq.trans_isBigO l1

  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp

lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx

def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n

def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f

lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n

lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by

  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO

  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]

  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp

theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le

theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict

theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by

  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity

theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by

  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh

  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖

  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]

  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])

lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by

  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)




lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by

  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf

  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))

  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext x
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1; ext t
    rw [smul_eq_mul, mul_comm (f t)]
    congr 2
    push_cast
    field_simp
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)

lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm





lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by

  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩



noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩

lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }

lemma quadratic_pos (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) :
    0 < a * x ^ 2 + b * x + c := by
  have l1 : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
    simp only [discrim]; field_simp; ring
  have l2 : 0 < - discrim a b c := by linarith
  rw [l1, sub_eq_add_neg, ← neg_div] ; positivity

noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)

noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))

lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity

lemma pp_deriv (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa using hasDerivAt_id x |>.add_const 1 |>.pow 2 |>.const_mul _

lemma pp_deriv_eq (a : ℝ) : deriv (pp a) = pp' a := by
  ext x ; exact pp_deriv a x |>.deriv

lemma pp'_deriv (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  simpa using! hasDerivAt_id x |>.add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)

lemma pp'_deriv_eq (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  ext x ; exact pp'_deriv a x |>.deriv

noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹

noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2

lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity

lemma hh_le (a t : ℝ) (ht : 0 ≤ t) : |hh a t| ≤ t⁻¹ := by
  by_cases h0 : t = 0
  · simp [hh, h0]
  replace ht : 0 < t := lt_of_le_of_ne ht (by tauto)
  unfold hh
  rw [abs_inv, inv_le_inv₀ (by positivity) ht, abs_mul, abs_eq_self.mpr ht.le]
  convert_to! t * 1 ≤ _
  · simp
  apply mul_le_mul le_rfl ?_ zero_le_one ht.le
  rw [abs_eq_self.mpr (by positivity)]
  simp only [le_add_iff_nonneg_right]
  positivity

lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring

lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt

lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity

lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)

noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹

lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp

lemma gg_l1 {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  simp only [gg_of_hh hx.ne.symm, one_div, mul_inv_rev, abs_mul]
  apply mul_le_mul le_rfl (hh_le _ _ (by positivity)) (by positivity) (by positivity) |>.trans
    (le_of_eq ?_)
  simp [abs_inv, abs_eq_self.mpr hx.le] ; field_simp

lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)

lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi

lemma sum_telescopic (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  apply Finset.sum_range_sub

lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by

  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf

  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf

lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring

lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring

lemma cancel_main {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  convert! cancel_aux' hf hg hf' hg' n using 1
  match n with
  | n + 2 => simp only [cumsum_succ] ; push_cast ; ring

lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring

theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by

  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]

  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp

  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp

  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith

  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)

  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3

  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp

lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring

lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1

lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2

lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring

lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i

  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1

  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))

  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv

  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self

  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp

  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]

  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa using! this.mono_set Ioi_subset_Ici_self

lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by

  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx

lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx

variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
    ring

lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))

lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by

  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6

lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by

  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)

lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by

  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; have := continuous_FourierIntegral ψ ; fun_prop
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl

lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by

  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring


lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by

  -- Shorter notation for clarity
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)

  -- Build the truncation
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'

  -- Choose the truncation radius
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key

  -- Apply the compact support case
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key

  -- Control the tail term
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp

  -- Conclude the proof
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]

  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using! this

  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict

  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)

lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'





-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead

lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f




noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2

@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl

lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))

lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus

lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2

theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩

lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by

  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this

theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε

  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi

  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]

  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε

  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]



lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by

  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)

  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]

  have key := limiting_cor_schwartz g hf hcheby hG hG'

  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp

  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx

  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus

  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4



lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal

lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by

  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key

lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by

  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by

  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp

lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩

lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)

lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith

lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx

lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith

lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]

lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]

theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this



lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by

  -- Take care of the trivial case `a = b`
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab

  -- Notation to make the proof more readable
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'

  -- A few facts about the indicator function of `Icc a b`
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le

  -- Bound from above by a smooth function
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Bound from below by a smooth function
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx

  -- Combine the two bounds
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith



lemma le_floor_mul_iff (hb : 0 ≤ b) (hx : 0 < x) : n ≤ ⌊b * x⌋₊ ↔ n / x ≤ b := by
  rw [div_le_iff₀ hx, Nat.le_floor_iff] ; positivity

lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]

lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]

lemma mem_Icc_iff_div (hb : 0 ≤ b) (hx : 0 < x) : n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, mem_Icc, ceil_mul_le_iff hx, le_floor_mul_iff hb hx]

lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]

lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]

lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]

lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop

-- TODO with `Ico`



/-- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/

lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring

noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N

lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]

lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1

theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by

  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A

theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith



-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)

theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_setOf_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2

end PNTX_Wiener

-- Ported from PrimeNumberTheoremAnd: Consequences.lean (selected lemmas up to chebyshev_asymptotic), followed by the new proof of H1
section PNTX_Conseq

section PNTConseq
open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

/-- If u ~ v and u-w = o(v) then w ~ v. -/
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu

theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _

  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have := Real.tendsto_pow_log_div_pow_atTop 1 1 Real.zero_lt_one
  simp only [rpow_one] at this
  exact Tendsto.comp this tendsto_natCast_atTop_atTop

/-- An alternate form of the Weak PNT. -/
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_setOf_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'

/-- `√x · log x = o(x)` as `x → ∞`. -/
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this

theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2

end PNTConseq
end PNTX_Conseq

open Filter Real Asymptotics MeasureTheory
open scoped Chebyshev
lemma primeCounting_upper_of_theta
    (hp : Chebyshev.theta ~[atTop] id) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (1+ε)*(x/log x) := by
  have hδ : 0 < ε/2 := by positivity
  filter_upwards [eventually_ge_atTop (2:ℝ),hp.isLittleO.bound hδ,
    Chebyshev.integral_theta_div_log_sq_isLittleO.bound hδ] with x hx hθ hI
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 < log x := Real.log_pos (by linarith)
  change ‖Chebyshev.theta x-x‖ ≤ ε/2*‖x‖ at hθ
  rw [Real.norm_of_nonneg hx0] at hθ
  have hu : Chebyshev.theta x ≤ x+ε/2*x := by linarith [(le_norm_self (Chebyshev.theta x-x)).trans hθ]
  change ‖∫ t in 2..x, Chebyshev.theta t / (t*log t^2)‖ ≤ ε/2*‖x/log x‖ at hI
  rw [Real.norm_of_nonneg (div_nonneg hx0 hlog.le)] at hI
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx]
  calc
    _ ≤ (x+ε/2*x)/log x + ε/2*(x/log x) :=
      add_le_add (div_le_div_of_nonneg_right hu hlog.le) ((le_norm_self _).trans hI)
    _ = _ := by ring

private theorem h3_proof : OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1.H3 := by
  exact primeCounting_upper_of_theta chebyshev_asymptotic
end

theorem OMA.solution : type_of% @Erdos971.erdos_971.variants.infinite_sequence :=
  OMA.R_Erdos971_erdos_971_variants_infinite_sequence_R1.main h1_proof h2_proof h3_proof
