import FormalConjectures.ErdosProblems.«699»
import Mathlib

/-! Strict common prime factors of binomial coefficients.
The power bound adapts Paul Lee, Paulee314/erdos699-lean, revision
814f545f5f64, under Apache-2.0. Copyright 2026 Paul Lee, and copyright
2025 The Formal Conjectures Authors. The relative-prime-interval argument
and its combination with the prime-counting estimate are new. -/
open Filter Finset Asymptotics
open scoped Topology BigOperators
namespace StrictCommonPrime
private theorem descFactorial_mul_pow_le {j n : ℕ} (hjn : j ≤ n) :
    ∀ i : ℕ, j.descFactorial i * n ^ i ≤ n.descFactorial i * j ^ i
  | 0 => by simp
  | i + 1 => by
    have ih := descFactorial_mul_pow_le hjn i
    have key : (j - i) * n ≤ (n - i) * j := by
      rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_comm n j]
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hjn) _
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    calc (j - i) * j.descFactorial i * (n ^ i * n)
        = ((j - i) * n) * (j.descFactorial i * n ^ i) := by ring
      _ ≤ ((n - i) * j) * (n.descFactorial i * j ^ i) := Nat.mul_le_mul key ih
      _ = (n - i) * n.descFactorial i * (j ^ i * j) := by ring

/-- For `j ≤ n`: `C(j, i) · n^i ≤ C(n, i) · j^i`, i.e. `C(n, i) / C(j, i) ≥ (n / j)^i`. -/
private theorem choose_mul_pow_le {i j n : ℕ} (hjn : j ≤ n) :
    j.choose i * n ^ i ≤ n.choose i * j ^ i := by
  have h := descFactorial_mul_pow_le hjn i
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.mul_assoc, Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos i)

/-- The identity `C(n, j) C(j, i) = C(n, i) C(n - i, j - i)` gives
`C(n, i) ∣ gcd(C(n, i), C(n, j)) · C(j, i)` (Erdős and Szekeres). -/
private theorem choose_dvd_gcd_mul {n i j : ℕ} (hij : i ≤ j) :
    n.choose i ∣ Nat.gcd (n.choose i) (n.choose j) * j.choose i := by
  rw [← Nat.gcd_mul_right]
  refine Nat.dvd_gcd (Nat.dvd_mul_right _ _) ?_
  rw [Nat.choose_mul (n := n) hij]
  exact Nat.dvd_mul_right _ _

/-- A divisor `g` of `C(n, i)`, with `i ≤ n`, is at most `n ^ ω(g)`, because
`p ^ v_p(C(n, i)) ≤ n` for every prime `p` (Kummer). -/
private theorem le_pow_card_of_dvd_choose {g n i : ℕ} (hn : n ≠ 0) (hg : g ≠ 0) (hin : i ≤ n)
    (hdvd : g ∣ n.choose i) : g ≤ n ^ g.primeFactors.card := by
  have hc : n.choose i ≠ 0 := (Nat.choose_pos hin).ne'
  calc g = g.factorization.prod (fun p k => p ^ k) := (Nat.prod_factorization_pow_eq_self hg).symm
    _ = ∏ p ∈ g.primeFactors, p ^ g.factorization p := by
        rw [Finsupp.prod, Nat.support_factorization]
    _ ≤ ∏ _p ∈ g.primeFactors, n := by
        refine Finset.prod_le_prod (by intros; exact Nat.zero_le _) (fun p hp => ?_)
        have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
        calc p ^ g.factorization p ≤ p ^ (n.choose i).factorization p :=
              Nat.pow_le_pow_right hp'.pos ((Nat.factorization_le_iff_dvd hg hc).2 hdvd p)
          _ ≤ p ^ Nat.log p n := Nat.pow_le_pow_right hp'.pos Nat.factorization_choose_le_log
          _ ≤ n := Nat.pow_log_le_self p hn
    _ = n ^ g.primeFactors.card := Finset.prod_const n

/-- A set of primes below `i` has at most `i / 2` elements: `p ↦ (p - 1) / 2` is injective on
primes and maps those below `i` into `[0, i / 2)`. -/
private theorem two_mul_card_le {s : Finset ℕ} {i : ℕ} (hs : ∀ p ∈ s, p.Prime ∧ p < i) :
    2 * s.card ≤ i := by
  have h : s.card ≤ (Finset.range (i / 2)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p - 1) / 2) ?_ ?_
    · intro p hp
      have hp' : p ∈ s := by simpa using hp
      obtain ⟨hpp, hpi⟩ := hs p hp'
      have := hpp.two_le
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro p hp q hq hpq
      have hp' : p ∈ s := by simpa using hp
      have hq' : q ∈ s := by simpa using hq
      obtain ⟨hpp, -⟩ := hs p hp'
      obtain ⟨hqp, -⟩ := hs q hq'
      have h2p := hpp.two_le
      have h2q := hqp.two_le
      have hop := hpp.eq_two_or_odd
      have hoq := hqp.eq_two_or_odd
      simp only at hpq
      omega
  simp only [Finset.card_range] at h
  omega


private def Obstruction (n i j : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → i < p → ¬ p ∣ Nat.gcd (n.choose i) (n.choose j)

private theorem bounds {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n / 2)
    (bad : Obstruction n i j) :
    n ≤ j^3 ∧ n^i ≤ n^(Nat.primeCounting i)*j^i := by
  let g := Nat.gcd (n.choose i) (n.choose j)
  let c := g.primeFactors.card
  have hn : 0 < n := by omega
  have hB : 0 < j.choose i := Nat.choose_pos hij.le
  have gpos : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.choose_pos (by omega))
  have hpi {p : ℕ} (hp : p ∈ g.primeFactors) : p ≤ i := by
    by_contra! hk
    exact bad p (Nat.prime_of_mem_primeFactors hp) hk (Nat.dvd_of_mem_primeFactors hp)
  have hc : 3*c ≤ 2*i := by
    have hh := two_mul_card_le (s:=g.primeFactors) (i:=i+1)
      (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp,by have := hpi hp; omega⟩)
    change 2*c ≤ i+1 at hh
    by_cases he : i=1
    · have hem : g.primeFactors = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        have := hpi hp
        omega
      simp [c,hem]
    · omega
  have hgc : g ≤ n^c := le_pow_card_of_dvd_choose hn.ne' gpos.ne' (by omega) (Nat.gcd_dvd_left _ _)
  have h1 : n.choose i ≤ g * j.choose i :=
    Nat.le_of_dvd (Nat.mul_pos gpos hB) (choose_dvd_gcd_mul hij.le)
  have hb : n^i ≤ n^c*j^i := by
    refine Nat.le_of_mul_le_mul_left ?_ hB
    calc j.choose i*n^i ≤ n.choose i*j^i := choose_mul_pow_le (by omega)
         _ ≤ (n^c*j.choose i)*j^i := Nat.mul_le_mul_right _ (h1.trans (Nat.mul_le_mul_right _ hgc))
         _ = _ := by ring
  have hpcount : c ≤ Nat.primeCounting i := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card fun p hp => Nat.mem_primesLE.mpr ⟨hpi hp,Nat.prime_of_mem_primeFactors hp⟩
  refine ⟨?_,hb.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn hpcount))⟩
  have hh : n^(2*i)*n^i ≤ n^(2*i)*(j^3)^i := by
    calc n^(2*i)*n^i = (n^i)^3 := by ring
         _ ≤ (n^c*j^i)^3 := Nat.pow_le_pow_left hb 3
         _ = n^(3*c)*(j^3)^i := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn hc)
  exact (Nat.pow_le_pow_iff_left (by omega : i ≠ 0)).1 (Nat.le_of_mul_le_mul_left hh (Nat.pow_pos hn))

private theorem interval_empty {n i j : ℕ} (hij : i < j) (hj : j ≤ n/2)
    (hbad : Obstruction n i j) :
    Nat.primesLE n = Nat.primesLE (n-i) := by
  ext p
  rw [Nat.mem_primesLE,Nat.mem_primesLE]
  constructor
  · rintro ⟨hp,hp'⟩
    refine ⟨?_,hp'⟩
    by_contra! hbig
    apply hbad p hp' (by omega)
    exact Nat.dvd_gcd (hp'.dvd_choose (by omega) hbig hp) (hp'.dvd_choose (by omega) (by omega) hp)
  · rintro ⟨hp,hp'⟩
    exact ⟨by omega,hp'⟩

private theorem gap_bound (pnt : Chebyshev.theta ~[atTop] (id : ℝ → ℝ)) (A : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ i j : ℕ, i < j → j ≤ n/2 → Obstruction n i j → A*i < n := by
  let e : ℝ := 1/(4*((A:ℝ)+1))
  have he : 0 < e := by dsimp [e]; positivity
  have est : ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ e*x := by
    filter_upwards [pnt.isLittleO.bound he,eventually_ge_atTop (0:ℝ)] with x h hx
    simpa [Real.norm_eq_abs,abs_of_nonneg hx] using h
  obtain ⟨C,hC⟩ := eventually_atTop.mp est
  obtain ⟨M,hM⟩ := exists_nat_ge C
  filter_upwards [eventually_ge_atTop (2*M+1)] with n hn
  intro i j hi hj hb
  have hθ : Chebyshev.theta (n:ℝ) = Chebyshev.theta ((n-i:ℕ):ℝ) := by
    simp only [Chebyshev.theta_eq_sum_primesLE_log,interval_empty hi hj hb]
  have hx := hC (n:ℝ) (hM.trans (by exact_mod_cast (show M≤n by omega)))
  have hy := hC ((n-i:ℕ):ℝ) (hM.trans (by exact_mod_cast (show M≤n-i by omega)))
  rw [Nat.cast_sub (by omega : i≤n)] at hθ hy
  have h₂ : (i:ℝ) ≤ 2*e*(n:ℝ) := by
    rw [← hθ] at hy
    have hA := (abs_le.mp hx).1
    have hB := (abs_le.mp hy).2
    nlinarith [mul_nonneg he.le (Nat.cast_nonneg i)]
  have hA0 : 0 ≤ (A:ℝ) := by positivity
  have hpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have heq : (4*((A:ℝ)+1))*e=1 := by dsimp [e]; field_simp
  have h := mul_le_mul_of_nonneg_left h₂ (show 0 ≤ 4*((A:ℝ)+1) by positivity)
  have hre : (A:ℝ)*(i:ℝ)<n := by nlinarith [mul_nonneg hA0 (Nat.cast_nonneg i),congrArg (· * (n:ℝ)) heq]
  exact_mod_cast hre


private theorem finite_strip (pnt : Chebyshev.theta ~[atTop] (id : ℝ → ℝ)) (B : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n/2 → j ≤ B*i → ¬ Obstruction n i j := by
  let A := ⌈Real.exp 18 * (B:ℝ)⌉₊
  have hA : Real.exp 18 * (B:ℝ) ≤ A := Nat.le_ceil _
  have hpi : ∀ᶠ i : ℕ in atTop, (Nat.primeCounting i : ℝ) * Real.log i ≤ 3*i := by
    have H := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
      (Chebyshev.eventually_primeCounting_le (ε:=1) (by norm_num))
    filter_upwards [H,eventually_ge_atTop (2:ℕ)] with i hh hi
    change (Nat.primeCounting ⌊(i:ℝ)⌋₊ : ℝ) ≤ _ at hh
    rw [Nat.floor_natCast] at hh
    have hlog : 0 < Real.log (i:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < i by omega))
    have h4 : Real.log 4 ≤ 2 := by
      rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_two_lt_d9]
    exact ((le_div_iff₀ hlog).mp hh).trans (by nlinarith [mul_nonneg (sub_nonneg.mpr h4) (Nat.cast_nonneg i)])
  obtain ⟨I,hI⟩ := eventually_atTop.mp hpi
  let K := max (max B I) 2
  filter_upwards [eventually_gt_atTop ((B*K)^3),gap_bound pnt A] with n hn hgap
  intro i j hi hij hj hB bad
  obtain ⟨hcube,hpower⟩ := bounds hi hij hj bad
  have hK : K ≤ i := by
    by_contra! h
    have H := (Nat.pow_le_pow_left (hB.trans (Nat.mul_le_mul_left B h.le)) 3)
    omega
  have h₂ : 2 ≤ i := (le_max_right _ _).trans hK
  have hI' : I ≤ i := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hB' : B ≤ i := (le_max_left _ _).trans ((le_max_left _ _).trans hK)
  have hj0 : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hi0 : (0:ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hj2 : j ≤ i^2 := hB.trans (by simpa [pow_two] using Nat.mul_le_mul_right i hB')
  have hn6 : n ≤ i^6 := hcube.trans (by simpa [←pow_mul] using Nat.pow_le_pow_left hj2 3)
  have hlog6 := Real.log_le_log hn0 (show (n:ℝ) ≤ (i:ℝ)^6 by exact_mod_cast hn6)
  rw [Real.log_pow] at hlog6
  have hr : (n:ℝ)^i ≤ (n:ℝ)^(Nat.primeCounting i)*(j:ℝ)^i := by exact_mod_cast hpower
  have hlog := Real.log_le_log (pow_pos hn0 _) hr
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow,Real.log_pow] at hlog
  have hprod := mul_le_mul_of_nonneg_left hlog6 (Nat.cast_nonneg (Nat.primeCounting i) : (0:ℝ)≤_)
  norm_num only [Nat.cast_ofNat] at hprod
  have h18 : (i:ℝ)*(Real.log n-Real.log j) ≤ (i:ℝ)*18 := by
    nlinarith [hI i hI']
  have h18' := (mul_le_mul_iff_right₀ hi0).1 h18
  have hexp := Real.exp_le_exp.mpr h18'
  rw [Real.exp_sub,Real.exp_log hn0,Real.exp_log hj0] at hexp
  have hrn : (n:ℝ) ≤ (A:ℝ)*(i:ℝ) := calc
    (n:ℝ) ≤ Real.exp 18*(j:ℝ) := (div_le_iff₀ hj0).mp hexp
    _ ≤ Real.exp 18*((B:ℝ)*(i:ℝ)) := mul_le_mul_of_nonneg_left (by exact_mod_cast hB) (Real.exp_pos _).le
    _ ≤ (A:ℝ)*(i:ℝ) := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hA hi0.le
  exact (not_le_of_gt (hgap i j hij hj bad)) (by exact_mod_cast hrn)


private theorem dvd_choose_of_digit {n k p e : ℕ} (hp : p.Prime) (hk : k ≤ n)
    (he : 0 < e) (hw : n % p ^ e < k % p ^ e) : p ∣ n.choose k := by
  have hc : p ^ e ≤ k % p ^ e + (n-k) % p ^ e := by
    by_contra! h
    have hr := Nat.add_mod k (n-k) (p ^ e)
    rw [Nat.add_sub_of_le hk, Nat.mod_eq_of_lt h] at hr
    exact (Nat.not_le_of_lt hw) (hr ▸ Nat.le_add_right _ _)
  apply Nat.dvd_of_factorization_pos
  rw [Nat.factorization_choose hp hk (b := max e (Nat.log p n) + 1) (by omega)]
  apply Nat.ne_of_gt
  apply Finset.card_pos.mpr
  exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨he, by omega⟩, hc⟩⟩

end StrictCommonPrime

namespace OMA.R_Erdos699_erdos_szekeres_strengthening_R1
open Filter Finset
/-- For each fixed index, only the residual cubically bounded prime-gap region. -/
def H1 : Prop := ∀ i : ℕ, 2 ≤ i → ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, i < j → j ≤ n/2 → n ≤ j^3 →
    n^i ≤ n^(Nat.primeCounting i)*j^i →
    Nat.primesLE n = Nat.primesLE (n-i) →
    ∃ p a b : ℕ, p.Prime ∧ i < p ∧ 0 < a ∧ 0 < b ∧
      n % p^a < i % p^a ∧ n % p^b < j % p^b
/-- The unbounded-index regime beyond a fixed multiplicative strip. -/
def H2 : Prop := ∃ B : ℕ, 1 ≤ B ∧ ∀ n i j : ℕ, B ≤ i → B*i < j → i < j → j ≤ n/2 → n ≤ j^3 →
    n^i ≤ n^(Nat.primeCounting i)*j^i →
    Nat.primesLE n = Nat.primesLE (n-i) →
    ∃ p a b : ℕ, p.Prime ∧ i < p ∧ 0 < a ∧ 0 < b ∧
      n % p^a < i % p^a ∧ n % p^b < j % p^b


/-- The standard Chebyshev prime number theorem, used only to exclude proportional prime gaps. -/
def H3 : Prop := Chebyshev.theta ~[atTop] (id : ℝ → ℝ)

theorem main : H1 → H2 → H3 → type_of% @Erdos699.erdos_szekeres_strengthening := by
  classical
  intro fixed tail pnt
  obtain ⟨B,hB,hwide⟩ := tail
  have hsmall : ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range B, 2 ≤ i →
      ∀ j : ℕ, i < j → j ≤ n/2 → n ≤ j^3 →
    n^i ≤ n^(Nat.primeCounting i)*j^i →
    Nat.primesLE n = Nat.primesLE (n-i) →
    ∃ p a b : ℕ, p.Prime ∧ i < p ∧ 0 < a ∧ 0 < b ∧
      n % p^a < i % p^a ∧ n % p^b < j % p^b := by
    apply (Finset.eventually_all _).mpr
    intro i hi
    by_cases h : 2 ≤ i
    · exact (fixed i h).mono fun n H _ => H
    · exact Filter.Eventually.of_forall fun _ hi => (h hi).elim
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hsmall.and (StrictCommonPrime.finite_strip pnt B))
  let S := Finset.range N
  refine ⟨S ×ˢ (S ×ˢ S),?_⟩
  intro n i j hi hij hj hn
  have hnN : N≤n := by
    by_contra! hh
    exact hn (Finset.mem_product.mpr ⟨Finset.mem_range.mpr hh,Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (show i < N by omega),Finset.mem_range.mpr (show j < N by omega)⟩⟩)
  by_contra hh
  push_neg at hh
  have bad : StrictCommonPrime.Obstruction n i j := hh
  obtain ⟨hc,hp⟩ := StrictCommonPrime.bounds hi hij hj bad
  have he := StrictCommonPrime.interval_empty hij hj bad
  have hi₂ : 2 ≤ i := by
    by_contra! hs
    have h : i=1 := by omega
    subst i
    have hp1 : Nat.primeCounting 1 = 0 := by decide
    simp [hp1] at hp
    omega
  have H := hN n hnN
  have hcert : ∃ p a b : ℕ, p.Prime ∧ i < p ∧ 0 < a ∧ 0 < b ∧
      n % p^a < i % p^a ∧ n % p^b < j % p^b := by
    by_cases h : i<B
    · exact H.1 i (Finset.mem_range.mpr h) hi₂ j hij hj hc hp he
    have hratio : B*i < j := by
      by_contra! hr
      exact H.2 i j hi hij hj hr bad
    exact hwide n i j (by omega) hratio hij hj hc hp he
  obtain ⟨p,a,b,hprime,hpi,ha,hb,hia,hjb⟩ := hcert
  exact bad p hprime hpi (Nat.dvd_gcd (StrictCommonPrime.dvd_choose_of_digit hprime (by omega) ha hia)
    (StrictCommonPrime.dvd_choose_of_digit hprime (by omega) hb hjb))
end OMA.R_Erdos699_erdos_szekeres_strengthening_R1
