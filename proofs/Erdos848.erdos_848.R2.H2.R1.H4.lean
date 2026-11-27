import OMAReductions.R_Erdos848_erdos_848_R2_H2_R1
import Mathlib
/-!
# Erdős 848 above 1.5 billion
For a pivot b and a large square divisor p² of bn+1, the complementary divisor
d satisfies d ≡ 1 modulo each of 2, 3 or 6 which divides b. Encoding d in that
progression bounds large-square exceptions uniformly. Separate diagonal sieves
account for the absence of pivots divisible by six or fourteen. The all-odd
case and the previous effective five-billion threshold are used below.
Sources: https://www.erdosproblems.com/848 and
https://github.com/crabsatellite/erdos-848-squarefree-product.
-/


/- # The asymptotic bound for squarefree products

Sawhney's stability theorem implies the conjectured bound for every sufficiently
large N. This port adapts Raymond Jung's Apache-2.0 Lean formalization, with
the original contributors Claude Opus 4.5, GPT-5.2 Pro/xHigh, Gemini 3.0 and
Aristotle. Source: https://github.com/The-Obstacle-Is-The-Way/erdos-banger
at 1cc2ac8e9d70516e979733c6ea5c4d2eb652d1f5, formal/lean/Erdos/848.lean.
Port, certified finite prime sums, elementary large-prime estimates, and optimized
stability parameters by @Deldor14. For p>N/360 the diagonal bound uses gaps between Pell solutions and the mixed bound
uses complementary divisor pairs with gcd at most two. Counting their prime supports
controls the number of roots. Two Chebyshev estimates bound the small-prime error.
The diagonal sieve counts the two opposite
roots together; when p² ≥ 2N, at most one lies in [0,N). With δ = 1/2300,
the critical density is at most 46/1795 + 326/25000 + 3δ + 1/40000.
-/
open scoped BigOperators

open scoped Finset

open scoped Nat.Prime

namespace Erdos848Gap

/-- Two different positive solutions of x² + 1 = d p² cannot have
their p-coordinates in the same multiplicative interval [p,2p]. -/
theorem diagonal_gap {d n m p q : ℕ} (pp : 2 ≤ p) (pq : p < q) (narrow : q ≤ 2*p)
    (hn : n^2+1=d*p^2) (hm : m^2+1=d*q^2) : False := by
  have dp : 0 < d := by
    cases d with
    | zero => simp at hn
    | succ d => omega
  have coord {k t : ℕ} (hk : 2 ≤ k) (eq : t^2+1=d*k^2) : k ≤ t := by
    have pd : k^2 ≤ d*k^2 := by simpa using Nat.mul_le_mul_right (k^2) dp
    have sq2 : 4 ≤ k^2 := Nat.pow_le_pow_left hk 2
    have pos : 0 < t := by
      cases t with
      | zero => simp at eq; omega
      | succ t => omega
    by_contra! h
    have sq := Nat.pow_le_pow_left (show t+1 ≤ k by omega) 2
    nlinarith only [sq,pd,eq,pos]
  have pm := coord pp hn
  have prod : (m*p)^2+ p^2 = (n*q)^2+ q^2 := by
    have a := congrArg (· * p^2) hm
    have b := congrArg (· * q^2) hn
    nlinarith only [a,b]
  have sq_lt := Nat.pow_lt_pow_left pq (by decide : 2 ≠ 0)
  have det : n*q < m*p := by
    by_contra! h
    have leq := Nat.pow_le_pow_left h 2
    omega
  have detsq := Nat.pow_le_pow_left (show n*q + 1 ≤ m*p by omega) 2
  have hmul := Nat.mul_le_mul_right q pm
  have qt := Nat.mul_le_mul_right q narrow
  nlinarith only [detsq,prod,qt,hmul]

private theorem count_keys (S : Finset ℕ) (key : ℕ → ℕ × ℕ) (cols rows : ℕ)
    (bound : ∀ n∈S, (key n).1 < cols ∧ (key n).2 < rows) (injective : Set.InjOn key S) :
    S.card ≤ cols*rows := by
  let labels := (Finset.range cols) ×ˢ (Finset.range rows)
  have maps : (S : Set ℕ).MapsTo key labels := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (bound n hn).1,Finset.mem_range.mpr (bound n hn).2⟩
  simpa [labels] using Finset.card_le_card_of_injOn key maps injective

private theorem count_by_theta (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ Finset.Icc 1 M := by
    intro q hq
    obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, hle⟩
  have hsmall : small.card ≤ M := by simpa using Finset.card_le_card sub
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


private theorem log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num

/-- Assign the full logarithmic weight beyond 2³², and retain the
first 27 units of that weight already beyond 2²⁷. -/
private theorem count_two_cuts (X : ℕ) :
    32*X.primeCounting ≤ 2*X + 32*(2^27).primeCounting + 5*(2^32).primeCounting := by
  let l := Real.log 2
  have pos : 0 < l := Real.log_pos (by norm_num)
  have count (b : ℕ) : (X.primesLE.filter (·≤b)).card ≤ b.primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hx,pb⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨pb,(Nat.mem_primesLE.mp hx).2⟩
  have logs (k p : ℕ) (hp : 2^k ≤ p) : k*l ≤ Real.log p := by
    rw [← log_nat_two_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hp)
  have step (p : ℕ) (hp : p∈X.primesLE) :
      32*l ≤ Real.log p + (if p ≤ 2^27 then 32*l else 0) + (if p ≤ 2^32 then 5*l else 0) := by
    by_cases a : p ≤ 2^27
    · have b : p≤2^32 := a.trans (by decide : 2^27 ≤ 2^32)
      simp only [if_pos a,if_pos b]
      have lp := Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le)
      linarith
    · by_cases b : p≤2^32
      · simp only [if_neg a,if_pos b]
        have h : (27 : ℝ)*l ≤ Real.log p := logs 27 p (by omega)
        linarith only [h]
      · simp only [if_neg a,if_neg b,add_zero]
        exact logs 32 p (by omega)
  have sum_indicator (b : ℕ) (t : ℝ) :
      (∑ p∈X.primesLE, if p≤b then t else 0) = ((X.primesLE.filter (·≤b)).card:ℝ)*t := by
    rw [← Finset.sum_filter]
    simp
  have total := Finset.sum_le_sum step
  rw [Finset.sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting,
    Finset.sum_add_distrib,Finset.sum_add_distrib,← Chebyshev.theta_eq_sum_primesLE_log,
    sum_indicator,sum_indicator] at total
  have c27 : (((X.primesLE.filter (·≤2^27)).card : ℕ):ℝ) ≤ ((2^27 : ℕ).primeCounting:ℝ) := by exact_mod_cast count (2^27)
  have c32 : (((X.primesLE.filter (·≤2^32)).card : ℕ):ℝ) ≤ ((2^32 : ℕ).primeCounting:ℝ) := by exact_mod_cast count (2^32)
  have th := Chebyshev.theta_le_log4_mul_x (x := (X:ℝ)) (Nat.cast_nonneg X)
  have l4 : Real.log 4 = 2*l := by simpa [l] using log_nat_two_pow 2
  rw [l4] at th
  have bound : 32*(X.primeCounting:ℝ) ≤ 2*(X:ℝ) + 32*((2^27 : ℕ).primeCounting:ℝ) + 5*((2^32 : ℕ).primeCounting:ℝ) := by
    apply (mul_le_mul_iff_left₀ pos).mp
    linarith only [total,th,mul_le_mul_of_nonneg_left c27 pos.le,mul_le_mul_of_nonneg_left c32 pos.le]
  exact_mod_cast bound

theorem small_primes_360 {N : ℕ} (big : 10^13 ≤ N) (Q : Finset ℕ)
    (primes : ∀ p∈Q, p.Prime) (cut : ∀ p∈Q, 360*p ≤ N) : 5500*Q.card ≤ N := by
  have sub : Q ⊆ (N/360).primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by have := cut p hp; omega,primes p hp⟩
  have c := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at c
  have a := count_by_theta (2^27) (2^20) 20 (by decide) (log_nat_two_pow 20)
  have b := count_by_theta (2^32) (2^24) 24 (by decide) (log_nat_two_pow 24)
  have h := count_two_cuts (N/360)
  norm_num1 at big a b h
  omega


theorem large_diagonal_360 {N : ℕ} (big : 4665600000 ≤ N) (S : Finset ℕ)
    (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 360*p ∧ p^2 ∣ n^2+1) :
    4000*S.card ≤ N := by
  classical
  let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
  let d (n : ℕ) := (n^2+1)/(p n)^2
  have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 360*p n ∧ (p n)^2 ∣ n^2+1 := by
    simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
  have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = n^2+1 := Nat.div_mul_cancel (info n hn).2.2
  have divisorBound (n : ℕ) (hn : n∈S) : d n < 129600 := by
    by_contra! h
    have h1 := Nat.mul_le_mul_right ((p n)^2) h
    have h2 := Nat.pow_lt_pow_left (choosePrime n hn).1 (by decide : 2≠0)
    have h3 := Nat.pow_lt_pow_left (info n hn).2.1 (by decide : 2≠0)
    nlinarith only [h1,eq n hn,h2,h3]
  let key (n : ℕ) := (d n, Nat.log 2 (N / p n))
  have posp (n : ℕ) (hn : n∈S) : 0<p n := by have h := (info n hn).2.1; omega
  have labels (n : ℕ) (hn : n∈S) : (key n).1 < 129600 ∧ (key n).2 < 9 := by
    refine ⟨divisorBound n hn,?_⟩
    change Nat.log 2 (N / p n) < 9
    apply Nat.log_lt_of_lt_pow' (by decide : (9:ℕ) ≠ 0)
    have co := (info n hn).2.1
    have up := (Nat.div_lt_iff_lt_mul (posp n hn)).mpr co
    norm_num
    omega
  have pair {x y : ℕ} (hx : x∈S) (hy : y∈S) (k : key x=key y) (lt : p x < p y) : False := by
    have de := congrArg Prod.fst k
    change d x = d y at de
    have label := congrArg Prod.snd k
    change Nat.log 2 (N / p x) = Nat.log 2 (N / p y) at label
    have nonzero : N / p y ≠ 0 := (Nat.div_pos (info y hy).1 (posp y hy)).ne'
    have high := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (N / p x)
    rw [label,pow_succ] at high
    have high' := (Nat.div_lt_iff_lt_mul (posp x hx)).mp high
    have low := (Nat.le_div_iff_mul_le (posp y hy)).mp (Nat.pow_log_le_self 2 nonzero)
    let C := 2 ^ Nat.log 2 (N / p y)
    change C*p y ≤ N at low
    change N < (C*2)*p x at high'
    have col : 0<C := pow_pos (by decide) _
    have gap : p y ≤ 2*p x := by
      by_contra! no
      have h := Nat.mul_le_mul_left C no.le
      nlinarith only [high',low,h]
    have sm : 2 ≤ p x := by have h := (info x hx).2.1; omega
    exact diagonal_gap sm lt gap (eq x hx).symm (de ▸ (eq y hy).symm)
  have inj : Set.InjOn key S := by
    intro x hx y hy hk
    rcases lt_trichotomy (p x) (p y) with h | h | h
    · exact (pair hx hy hk h).elim
    · have de := congrArg Prod.fst hk
      change d x = d y at de
      have xx := eq x hx
      have yy := eq y hy
      rw [de,h] at xx
      have sq : x^2=y^2 := by omega
      exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp sq
    · exact (pair hy hx hk.symm h).elim
  have bound := count_keys S key 129600 9 labels inj
  omega

end Erdos848Gap

/- Counting square roots in complementary divisor classes for Erdős problem 848. -/

/- Divisors corresponding to a square root of a unit have at most two common factors with their complementary divisor. -/
namespace Erdos848Unitary

private theorem coprime_factor_ext {a c a' c' : ℕ}
    (pos : 0 < a*c) (eq : a*c=a'*c') (ha : a.Coprime c) (ha' : a'.Coprime c')
    (hs : a.primeFactors=a'.primeFactors) : a=a' := by
  have pos' : 0 < a'*c' := eq ▸ pos
  have ac := Nat.pos_of_mul_pos_right pos
  have av := Nat.pos_of_mul_pos_left pos
  have ac' := Nat.pos_of_mul_pos_right pos'
  have av' := Nat.pos_of_mul_pos_left pos'
  have h : a.Coprime c' := (Nat.disjoint_primeFactors (by positivity) (by positivity)).mp
    (hs ▸ ha'.disjoint_primeFactors)
  have h' : a'.Coprime c := (Nat.disjoint_primeFactors (by positivity) (by positivity)).mp
    (hs ▸ ha.disjoint_primeFactors)
  apply Nat.dvd_antisymm
  · exact h.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right a c)
  · exact h'.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right a' c')

/-- Count divisors of b with gcd at most two with the complementary factor. -/
theorem count_unitary_keys (b : ℕ) (bpos : 0 < b) :
    (b.divisors.filter (fun g => (Nat.gcd g (b/g)) ∣ 2)).card ≤ 2 * 2^b.primeFactors.card := by
  classical
  let k (g : ℕ) := Nat.gcd g (b/g)
  let a (g : ℕ) := g/k g
  let c (g : ℕ) := (b/g)/k g
  let D := b.divisors.filter (fun g => k g ∣ 2)
  let K := (Finset.Icc 1 2).product b.primeFactors.powerset
  let code (g : ℕ) := (k g, (a g).primeFactors)
  have gd {g : ℕ} (hg : g ∈ D) : g ∣ b := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
  have kg {g : ℕ} (hg : g ∈ D) : 0 < k g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (gd hg) bpos)
  have ag (g : ℕ) : a g*k g=g := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have cg (g : ℕ) : c g*k g=b/g := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have B {g : ℕ} (hg : g ∈ D) : (a g*c g)*(k g*k g)=b := calc
    _ = (a g*k g)*(c g*k g) := by ring
    _ = b := by rw [ag,cg,Nat.mul_div_cancel' (gd hg)]
  have count : D.card ≤ K.card := by
    apply Finset.card_le_card_of_injOn code
    · intro g hg
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨kg hg,?_⟩, Finset.mem_powerset.mpr ?_⟩
      · exact Nat.le_of_dvd (by decide) (Finset.mem_filter.mp hg).2
      · exact Nat.primeFactors_mono ((Nat.div_dvd_of_dvd (Nat.gcd_dvd_left ..)).trans (gd hg)) bpos.ne'
    · intro x hx y hy he
      have hk : k x=k y := congrArg Prod.fst he
      have hs : (a x).primeFactors=(a y).primeFactors := congrArg Prod.snd he
      have e : a x*c x=a y*c y := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (kg hx) (kg hx))
        rw [B hx,hk,B hy]
      have pp : 0 < a x*c x := Nat.pos_of_mul_pos_right (show 0 < (a x*c x)*(k x*k x) by rw [B hx]; exact bpos)
      have ax := coprime_factor_ext pp e (Nat.coprime_div_gcd_div_gcd (kg hx)) (Nat.coprime_div_gcd_div_gcd (kg hy)) hs
      rw [← ag x,← ag y,ax,hk]
  simpa [K, Finset.card_product] using count

end Erdos848Unitary

/- Root counting for the complementary divisor range in Erdős problem 848. -/

namespace Erdos848RootRefined

private theorem root_factor {B D R X T U : ℤ}
    (hr : D*R^2=B*T+1) (hx : D*X^2=B*U+1) : B ∣ (X-R)*(X+R) := by
  refine ⟨R^2*U-X^2*T, ?_⟩
  linear_combination R^2*hx - X^2*hr

private theorem gcd_times_sum {B R X : ℤ} (hx : B ∣ (X-R)*(X+R)) :
    B ∣ (Int.gcd B (X-R) : ℤ)*(X+R) := by
  obtain ⟨q,hq⟩ := hx
  refine ⟨Int.gcdA B (X-R)*(X+R)+Int.gcdB B (X-R)*q, ?_⟩
  rw [Int.gcd_eq_gcd_ab]
  linear_combination Int.gcdB B (X-R)*hq

theorem roots_in_class {B D R X Y T U V : ℤ}
    (hr : D*R^2=B*T+1) (hx : D*X^2=B*U+1) (hy : D*Y^2=B*V+1)
    (hg : Int.gcd B (X-R) = Int.gcd B (Y-R)) : B ∣ 2*(Y-X) := by
  let g : ℤ := Int.gcd B (X-R)
  have h₁ : B ∣ g*(X+R) := gcd_times_sum (root_factor hr hx)
  have h₂ : B ∣ g*(Y+R) := by simpa only [g,hg] using gcd_times_sum (root_factor hr hy)
  have h₃ : B ∣ g*(Y-X) := by
    convert! dvd_sub h₂ h₁ using 1
    ring
  have gx : g ∣ X-R := Int.gcd_dvd_right ..
  have gy : g ∣ Y-R := by simpa only [g,hg] using Int.gcd_dvd_right B (Y-R)
  have gxy : g ∣ Y-X := by
    convert! dvd_sub gy gx using 1
    ring
  have plus : B ∣ (Y-X)*(X+R) := h₁.trans (mul_dvd_mul_right gxy _)
  have minus : B ∣ (Y-X)*(X-R) := by
    rw [mul_comm (Y-X) (X-R)]
    exact h₃.trans (mul_dvd_mul_right gx _)
  have twice : B ∣ 2*R*(Y-X) := by
    convert! dvd_sub plus minus using 1
    ring
  obtain ⟨k,hk⟩ := twice
  refine ⟨D*R*k-2*(Y-X)*T,?_⟩
  linear_combination D*R*hk-2*(Y-X)*hr

theorem root_key_valid {b : ℕ} (bpos : 0 < b) {D R X T U : ℤ}
    (hr : D*R^2=(b : ℤ)*T+1) (hx : D*X^2=(b : ℤ)*U+1) :
    let g := Int.gcd (b : ℤ) (X-R)
    Nat.gcd g (b/g) ∣ 2 := by
  let g := Int.gcd (b : ℤ) (X-R)
  let h := b/g
  let k := Nat.gcd g h
  change k ∣ 2
  have gb : g ∣ b := by exact_mod_cast Int.gcd_dvd_left (b : ℤ) (X-R)
  have gpos := Nat.pos_of_dvd_of_pos gb bpos
  have gh : (g : ℤ)*(h : ℤ)=(b : ℤ) := by exact_mod_cast Nat.mul_div_cancel' gb
  have gs : (b : ℤ) ∣ (g : ℤ)*(X+R) := gcd_times_sum (root_factor hr hx)
  obtain ⟨q,hq⟩ := gs
  have hs : (h : ℤ) ∣ X+R := by
    refine ⟨q,mul_left_cancel₀ (show (g : ℤ) ≠ 0 by exact_mod_cast gpos.ne') ?_⟩
    rw [← mul_assoc,gh,hq]
  have kg : (k : ℤ) ∣ (g : ℤ) := by exact_mod_cast Nat.gcd_dvd_left g h
  have kh : (k : ℤ) ∣ (h : ℤ) := by exact_mod_cast Nat.gcd_dvd_right g h
  have km : (k : ℤ) ∣ X-R := kg.trans (Int.gcd_dvd_right ..)
  have kp : (k : ℤ) ∣ X+R := kh.trans hs
  have kr := dvd_sub kp km
  rw [show X+R-(X-R)=2*R by ring] at kr
  have kb : (k : ℤ) ∣ (b : ℤ) := kg.trans (by exact_mod_cast gb)
  have old : (k : ℤ) ∣ (2*R)*(D*R)-2*((b : ℤ)*T) :=
    dvd_sub (dvd_mul_of_dvd_left kr _) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left kb _) _)
  have two : (2 : ℤ) = (2*R)*(D*R)-2*((b : ℤ)*T) := by linear_combination -2*hr
  rw [← two] at old
  exact_mod_cast old

end Erdos848RootRefined

/- Root counting using the prime factors of b. -/
namespace Erdos848Gap

/-- Count solutions using a divisor of b and the interval of length b containing 2p. -/
theorem count_mixed_divisors_unitary {N b C U : ℕ} (bpos : 0 < b) (bN : b ≤ N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n ∈ S, d n * (p n)^2 = b*n+1)
    (pr : ∀ n ∈ S, p n ≤ U) (dr : ∀ n ∈ S, d n*N < C*b) :
    S.card ≤ (C*b/N)*(2*2^b.primeFactors.card)*(2*U/b+1) := by
  classical
  let anchor (j : ℕ) : ℕ := if h : ∃ t ∈ S, d t = j then h.choose else 0
  have anchor_spec (n : ℕ) (hn : n ∈ S) :
      anchor (d n) ∈ S ∧ d (anchor (d n)) = d n := by
    have h : ∃ t ∈ S, d t = d n := ⟨n,hn,rfl⟩
    simpa only [anchor,dif_pos h] using h.choose_spec
  let r (j : ℕ) := p (anchor j)
  let g (n : ℕ) := Int.gcd (b : ℤ) ((p n : ℤ) - (r (d n) : ℤ))
  let code (n : ℕ) := (d n, g n, 2*p n/b)
  let keys := b.divisors.filter (fun j => Nat.gcd j (b/j) ∣ 2)
  let T := (Finset.Icc 1 (C*b/N)).product (keys.product (Finset.range (2*U/b+1)))
  have eqz (n : ℕ) (hn : n ∈ S) :
      (d n : ℤ)*(p n : ℤ)^2=(b : ℤ)*(n : ℤ)+1 := by exact_mod_cast eq n hn
  have Npos := bpos.trans_le bN
  have count : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn code
    · intro n hn
      have hdn : 0 < d n := by
        by_contra! h
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have hdv : g n ∣ b := by
        have hz : (g n : ℤ) ∣ (b : ℤ) := Int.gcd_dvd_left ..
        exact_mod_cast hz
      have hbnd : 2*p n/b ≤ 2*U/b := Nat.div_le_div_right (by have := pr n hn; omega)
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hdn,?_⟩, Finset.mem_product.mpr ⟨?_,?_⟩⟩
      · exact (Nat.le_div_iff_mul_le Npos).mpr (dr n hn).le
      · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdv,bpos.ne'⟩,?_⟩
        have ha := anchor_spec n hn
        have er := eqz _ ha.1
        rw [ha.2] at er
        exact Erdos848RootRefined.root_key_valid bpos er (eqz n hn)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hbnd)
    · intro x hx y hy hc
      have hd : d x = d y := congrArg Prod.fst hc
      have hg : g x = g y := congrArg (fun u => u.2.1) hc
      have hq : 2*p x/b=2*p y/b := congrArg (fun u => u.2.2) hc
      have ha := anchor_spec x hx
      have er := eqz _ ha.1
      rw [ha.2] at er
      have ey := eqz y hy
      rw [← hd] at ey
      change Int.gcd _ ((p x : ℤ) - (r (d x) : ℤ)) = Int.gcd _ ((p y : ℤ) - (r (d y) : ℤ)) at hg
      rw [← hd] at hg
      have hu := Erdos848RootRefined.roots_in_class er (eqz x hx) ey hg
      have hm : 2*p x ≡ 2*p y [MOD b] := by
        apply Int.natCast_modEq_iff.mp
        rw [Int.modEq_iff_dvd]
        convert! hu using 1
        push_cast
        ring
      have ex := Nat.mod_add_div (2*p x) b
      have ey' := Nat.mod_add_div (2*p y) b
      change (2*p x)%b=(2*p y)%b at hm
      rw [hm,hq] at ex
      have hp : p x=p y := by omega
      have et := eq x hx
      rw [hd,hp,eq y hy] at et
      exact Nat.eq_of_mul_eq_mul_left bpos (by omega)
  have bound : S.card ≤ (C*b/N)*keys.card*(2*U/b+1) := by
    simpa [T, Finset.card_product, mul_assoc] using count
  exact bound.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Erdos848Unitary.count_unitary_keys b bpos)))

end Erdos848Gap

/- An effective estimate for the number of choices of unitary divisor. -/
namespace Erdos848Gap
open Finset

theorem support_fourth (b : ℕ) (bp : 0<b) :
    (2*2^b.primeFactors.card)^4 ≤ 8944*b := by
  classical
  let s : Finset ℕ := {2,3,5,7,11,13}
  let weight (p : ℕ) : ℚ := if p∈s then 16 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (16:ℚ) ≤ weight p * p^(b.factorization p) := by
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 16 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 16≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (16:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 559 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 559 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (16:ℚ)^b.primeFactors.card ≤ 559*b := by
    calc _ = ∏ _∈b.primeFactors,(16:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 16^b.primeFactors.card ≤ 559*b := by exact_mod_cast comparison
  rw [mul_pow,←pow_mul,Nat.mul_comm b.primeFactors.card 4,pow_mul]
  change 16*16^b.primeFactors.card ≤ _
  omega
end Erdos848Gap

namespace Erdos848Gap
open Finset

/-- Counting in two prime ranges separates the high-quotient and the long-interval errors. -/
theorem mixed360_count {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<360*p n) : S.card ≤ 140880*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 40*p n≤N)
  let large := S.filter (fun n => ¬ 40*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/40 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<129600*b := by
    exact link n (smallS hn) 360 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<1600*b := by
    exact link n (largeS hn) 40 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 129600*b/N
  let W := 2*(N/40)/b
  have pd : P*N ≤ 129600*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/40) := Nat.div_mul_le_self _ _
  have u : 40*(N/40)≤N := by omega
  have num : 20*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤129600 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤6480 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 129600*b*W=129600*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 6480 num)
    have l1 : (P*W)*N ≤ 6480*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 136080 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 136080*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 1600*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 1600*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤1600 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 3200 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 1600 kd
    have mul : (Q*K)*N ≤ 3200*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 4800 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 4800*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

/-- The fourth-power divisor estimate pays for the sieve error at N ≥ 10^13. -/
theorem mixed360_error {N b : ℕ} (big : 10000000000000 ≤ N) (bp : 0<b) (bn : b≤N)
    {z : ℕ} (bound : z ≤ 140880*(2*2^b.primeFactors.card)) : 4000*z ≤ N := by
  have powb := support_fourth b bp
  have h : 4000*z ≤ 563520000*(2*2^b.primeFactors.card) := by omega
  apply h.trans
  by_contra! bad
  have lo := Nat.pow_lt_pow_left bad (by decide : 4≠0)
  rw [mul_pow] at lo
  have hi := Nat.mul_le_mul_left (563520000^4) (powb.trans (Nat.mul_le_mul_left 8944 bn))
  have cutoff := Nat.pow_le_pow_left big 3
  have mc := Nat.mul_le_mul_right N cutoff
  nlinarith only [lo,hi,mc,Nat.zero_le N]
end Erdos848Gap

namespace Erdos848Gap
theorem large_mixed_360 {N b : ℕ} (big : 10^13 ≤ N) (bN : b < N)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 360*p ∧ p^2 ∣ b*n+1) :
    4000*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 360*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    exact mixed360_error big bp bN.le (mixed360_count bp bN.le S p d eq (fun n hn => (info n hn).1) link
      (fun n hn => (info n hn).2.1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp
end Erdos848Gap
namespace Erdos848Port

def NonSquarefreeProductProp (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b + 1)

def A₇ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 7)

def A₁₈ (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n => n % 25 = 18)

lemma dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv
    {p a b : ℕ} (hp : Nat.Prime p) (ha : ¬p ∣ a) :
    p ^ 2 ∣ (a * b + 1) ↔ (b : ZMod (p ^ 2)) = -((a : ZMod (p ^ 2))⁻¹) := by
  set n : ℕ := p ^ 2
  have hcop : Nat.Coprime a n := by
    simpa [n] using hp.coprime_pow_of_not_dvd (m := 2) ha
  have haUnit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).2 hcop
  constructor
  · intro hdiv
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_eq_zero_iff (a * b + 1) n).2 hdiv
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz
    have hprod : (a : ZMod n) * (b : ZMod n) = (-1 : ZMod n) := by
      simpa using (eq_neg_of_add_eq_zero_left hz')
    have hb : (b : ZMod n) = (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
      have hb0 := congrArg (fun x : ZMod n => (a : ZMod n)⁻¹ * x) hprod
      have hb1 :
          ((a : ZMod n)⁻¹ * (a : ZMod n)) * (b : ZMod n) =
            (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
        simpa [mul_assoc] using hb0
      simpa [ZMod.inv_mul_of_unit (a : ZMod n) haUnit] using hb1
    simpa [n, mul_comm, mul_left_comm, mul_assoc] using hb
  · intro hb
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simp [hb, ZMod.mul_inv_of_unit (a : ZMod n) haUnit]
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz'
    exact (ZMod.natCast_eq_zero_iff (a * b + 1) n).1 hz

lemma prime_sq_divides_implies_one_mod_four (p n : ℕ) (hp : Nat.Prime p) (hp2 : p > 2)
    (hdiv : p ^ 2 ∣ n ^ 2 + 1) : p % 4 = 1 := by
  have hp_ne_two : p ≠ 2 := by omega
  have hp_dvd : p ∣ n ^ 2 + 1 := by
    have hp_div_p2 : p ∣ p ^ 2 := by simp [pow_two]
    exact Nat.dvd_trans hp_div_p2 hdiv
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) p).2 hp_dvd
  have hsq : (n : ZMod p) ^ 2 = (-1 : ZMod p) := by
    have : (n : ZMod p) ^ 2 + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
    simpa using (eq_neg_of_add_eq_zero_left this)
  have hne3 : p % 4 ≠ 3 :=
    ZMod.mod_four_ne_three_of_sq_eq_neg_one (p := p) (y := (n : ZMod p)) hsq
  have hp_mod2 : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).2 hp_ne_two
  have hp_mod4 : p % 4 = 1 ∨ p % 4 = 3 := (Nat.odd_mod_four_iff).1 hp_mod2
  cases hp_mod4 with
  | inl h1 => exact h1
  | inr h3 => exact (hne3 h3).elim

lemma two_roots_mod_p_squared (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) :
    ∃ r₁ r₂ : ZMod (p ^ 2),
      r₂ = -r₁ ∧ r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧
        ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : ZMod (p ^ 2), r₁ ^ 2 = -1 := by
    have h_quad_res : ∃ x : ℕ, x ^ 2 ≡ -1 [ZMOD p ^ 2] := by
      have h_hensel : ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 → ∃ x : ℕ, x ^ 2 ≡ -1 [ZMOD p] := by
        intro p hp hmod
        have := Fact.mk hp
        norm_num [← ZMod.intCast_eq_intCast_iff]
        obtain ⟨x, hx⟩ := ZMod.exists_sq_eq_neg_one_iff (p := p)
        exact Exists.elim (hx (by rw [hmod]; decide)) fun x hx =>
          ⟨x.val, by simpa [sq, ← ZMod.intCast_eq_intCast_iff] using hx.symm⟩
      obtain ⟨x, hx⟩ := @h_hensel p hp hmod
      obtain ⟨k, hk⟩ : ∃ k : ℤ, x ^ 2 = k * p - 1 := by
        exact hx.symm.dvd.imp fun k hk => by linarith
      obtain ⟨y, hy⟩ : ∃ y : ℤ, 2 * x * y ≡ -k [ZMOD p] := by
        obtain ⟨y, hy⟩ : ∃ y : ℤ, 2 * x * y ≡ 1 [ZMOD p] := by
          have h_inv : Int.gcd (2 * x) p = 1 := by
            refine' Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr _)
            norm_num [Int.natAbs_mul, Nat.Prime.dvd_mul hp]
            exact
              ⟨Nat.not_dvd_of_pos_of_lt (by norm_num) (by
                    contrapose! hmod
                    interval_cases p <;> trivial),
                fun h => by
                  have :=
                    Int.modEq_zero_iff_dvd.mp
                      (hx.symm.trans
                        (Int.modEq_zero_iff_dvd.mpr <| dvd_pow (Int.natCast_dvd_natCast.mpr h) two_ne_zero))
                  norm_num at this
                  norm_cast at this
                  have := Nat.le_of_dvd (by norm_num) this
                  interval_cases p <;> trivial⟩
          exact Int.mod_coprime h_inv
        exact ⟨y * -k, by simpa [mul_assoc] using hy.mul_right (-k)⟩
      use Int.natAbs (x + y * p)
      rw [Int.modEq_iff_dvd] at *
      obtain ⟨z, hz⟩ := hy
      use z - y ^ 2
      cases abs_cases (x + y * p : ℤ) <;> push_cast [*] <;> nlinarith
    obtain ⟨x, hx⟩ := h_quad_res
    refine ⟨x, ?_⟩
    erw [← ZMod.intCast_eq_intCast_iff] at hx
    simpa using hx
  refine' ⟨r₁, -r₁, rfl, _, _, _, _⟩ <;> simp_all +decide [sq]
  · rw [eq_neg_iff_add_eq_zero]
    by_contra h_contra
    have h_r1_zero : r₁ = 0 := by
      have h_r1_zero : (2 : ℕ) * r₁.val ≡ 0 [MOD p ^ 2] := by
        simp_all +decide [← ZMod.natCast_eq_natCast_iff]
        grind
      have h_r1_zero : p ^ 2 ∣ r₁.val := by
        exact
          (Nat.Coprime.dvd_of_dvd_mul_left
              (show Nat.Coprime (p ^ 2) 2 from by
                exact
                  Nat.Coprime.pow_left 2 <|
                    hp.coprime_iff_not_dvd.mpr fun h => by
                      have := Nat.le_of_dvd (by decide) h
                      interval_cases p <;> trivial)
              <| Nat.dvd_of_mod_eq_zero h_r1_zero)
      have := Fact.mk hp
      rw [← ZMod.natCast_eq_zero_iff] at h_r1_zero
      aesop
    norm_num [h_r1_zero] at hr₁
    rcases p with (_ | _ | _ | p) <;>
      (cases hr₁; all_goals contradiction)
  · have h_solutions : ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = -r₁ := by
      intro r hr
      have h_eq : (r - r₁) * (r + r₁) = 0 := by grind
      have h_coprime :
          Nat.gcd (p ^ 2) (r - r₁).val = 1 ∨ Nat.gcd (p ^ 2) (r + r₁).val = 1 := by
        have h_coprime : ¬(p ∣ (r - r₁).val ∧ p ∣ (r + r₁).val) := by
          have := Fact.mk hp
          simp_all +decide [← ZMod.natCast_eq_zero_iff]
          intro h
          have := Fact.mk hp
          simp_all +decide [sub_eq_iff_eq_add, add_eq_zero_iff_eq_neg]
          rw [eq_neg_iff_add_eq_zero]
          have := congr_arg (fun x : ZMod (p ^ 2) => x.val) hr₁
          norm_num [ZMod.val_add, ZMod.val_mul] at this ⊢
          replace this := congr_arg (· % p) this
          norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at this
          simp_all +decide [← sq, ← ZMod.natCast_eq_natCast_iff']
          intro H
          rw [← two_mul] at H
          replace H := congr_arg (fun x : ZMod p => x ^ 2) H
          simp_all +decide [mul_pow]
          rcases p with (_ | _ | _ | p) <;> cases H <;> contradiction
        simp_all +decide [Nat.Prime.coprime_iff_not_dvd]
        tauto
      have h_div : (p ^ 2 : ℕ) ∣ (r - r₁).val ∨ (p ^ 2 : ℕ) ∣ (r + r₁).val := by
        have h_div : (p ^ 2 : ℕ) ∣ ((r - r₁).val * (r + r₁).val) := by
          have := Fact.mk hp
          simp_all +decide [← ZMod.natCast_eq_zero_iff]
        cases h_coprime with
        | inl hc => exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left hc h_div)
        | inr hc => exact Or.inl (Nat.Coprime.dvd_of_dvd_mul_right hc h_div)
      have := Fact.mk hp
      simp_all +decide [← ZMod.natCast_eq_zero_iff, sub_eq_iff_eq_add, add_eq_zero_iff_eq_neg]
    simpa only [sq] using h_solutions

lemma cross_residue_not_div_25_of_residue (r a b : ℕ) (hr : r * r % 25 = 24) (ha : a % 25 = r)
    (hb : b % 25 ≠ r) : ¬ (25 ∣ a * b + 1) := by
  intro hdiv
  have hr_lt : r < 25 := by
    have : a % 25 < 25 := Nat.mod_lt a (by decide : 0 < 25)
    simpa [ha] using this
  have h0 : ((a * b + 1 : ℕ) : ZMod 25) = 0 :=
    (ZMod.natCast_eq_zero_iff (a * b + 1) 25).2 hdiv
  have haZ : (a : ZMod 25) = (r : ZMod 25) := by
    have ha_mod : a % 25 = r % 25 := by
      have h := congrArg (fun x => x % 25) ha
      have hleft : (a % 25) % 25 = a % 25 :=
        Nat.mod_eq_of_lt (Nat.mod_lt a (by decide : 0 < 25))
      simpa [hleft] using h
    exact (ZMod.natCast_eq_natCast_iff' a r 25).2 ha_mod
  have h1 : (r : ZMod 25) * (b : ZMod 25) + 1 = 0 := by
    have : (a : ZMod 25) * (b : ZMod 25) + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using h0
    simpa [haZ] using this
  have h2 : (r : ZMod 25) * (b : ZMod 25) = (-1 : ZMod 25) := by
    simpa using (eq_neg_of_add_eq_zero_left h1)
  have hrZ : (r : ZMod 25) * (r : ZMod 25) = (-1 : ZMod 25) := by
    have hrr : ((r * r : ℕ) : ZMod 25) = (24 : ZMod 25) := by
      have : (r * r) % 25 = 24 % 25 := by
        simpa [Nat.mod_eq_of_lt (by decide : 24 < 25)] using hr
      exact (ZMod.natCast_eq_natCast_iff' (r * r) 24 25).2 this
    have hrr' : (r : ZMod 25) * (r : ZMod 25) = (24 : ZMod 25) := by simpa using hrr
    exact hrr'.trans (by decide : (24 : ZMod 25) = (-1 : ZMod 25))
  have hr_inv : (-(r : ZMod 25)) * (r : ZMod 25) = (1 : ZMod 25) := by
    calc
      (-(r : ZMod 25)) * (r : ZMod 25) = -((r : ZMod 25) * (r : ZMod 25)) := by simp
      _ = -(-1 : ZMod 25) := by simp [hrZ]
      _ = (1 : ZMod 25) := by simp
  have hbZ : (b : ZMod 25) = (r : ZMod 25) := by
    have hmul : (-(r : ZMod 25)) * ((r : ZMod 25) * (b : ZMod 25)) =
        (-(r : ZMod 25)) * (-1 : ZMod 25) := by
      simpa [mul_assoc] using congrArg (fun x => (-(r : ZMod 25)) * x) h2
    have hmul' : ((-(r : ZMod 25)) * (r : ZMod 25)) * (b : ZMod 25) =
        (-(r : ZMod 25)) * (-1 : ZMod 25) := by
      simpa [mul_assoc] using hmul
    have hmul'' : ((-(r : ZMod 25)) * (r : ZMod 25)) * (b : ZMod 25) = (r : ZMod 25) := by
      simpa using hmul'
    have : (1 : ZMod 25) * (b : ZMod 25) = (r : ZMod 25) := by
      simpa [hr_inv] using hmul''
    simpa using this
  have hbmod : b % 25 = r := by
    have hb' : b % 25 = r % 25 := (ZMod.natCast_eq_natCast_iff' b r 25).1 hbZ
    simpa [Nat.mod_eq_of_lt hr_lt] using hb'
  exact hb hbmod

lemma cross_residue_not_div_25 (a b : ℕ) (ha : a % 25 = 7)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) : ¬ (25 ∣ a * b + 1) := by
  exact cross_residue_not_div_25_of_residue 7 a b (by norm_num) ha hb.1

lemma cross_residue_not_div_25_18 (a b : ℕ) (ha : a % 25 = 18)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) : ¬ (25 ∣ a * b + 1) := by
  exact cross_residue_not_div_25_of_residue 18 a b (by norm_num) ha hb.2

lemma must_have_other_prime_square_of_residue (r a b : ℕ) (hr : r * r % 25 = 24) (ha : a % 25 = r)
    (hb : b % 25 ≠ r) (hnsq : ¬ Squarefree (a * b + 1)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ a * b + 1 := by
  classical
  have hnot : ¬ ∀ p : ℕ, Nat.Prime p → ¬p * p ∣ a * b + 1 := by
    intro hall
    exact hnsq ((Nat.squarefree_iff_prime_squarefree).2 hall)
  push Not at hnot
  rcases hnot with ⟨p, hp, hpp⟩
  have h25 : ¬ (25 ∣ a * b + 1) := cross_residue_not_div_25_of_residue r a b hr ha hb
  have hp2 : p ^ 2 ∣ a * b + 1 := by simpa [pow_two] using hpp
  refine ⟨p, hp, ?_, hp2⟩
  intro hp5
  subst hp5
  have : 25 ∣ a * b + 1 := by simpa [pow_two] using hp2
  exact (h25 this).elim

lemma must_have_other_prime_square (a b : ℕ) (ha : a % 25 = 7)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) (hnsq : ¬ Squarefree (a * b + 1)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p^2 ∣ a * b + 1 := by
  exact must_have_other_prime_square_of_residue 7 a b (by norm_num) ha hb.1 hnsq

lemma must_have_other_prime_square_18 (a b : ℕ) (ha : a % 25 = 18)
    (hb : b % 25 ≠ 7 ∧ b % 25 ≠ 18) (hnsq : ¬ Squarefree (a * b + 1)) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ a * b + 1 := by
  exact must_have_other_prime_square_of_residue 18 a b (by norm_num) ha hb.2 hnsq

noncomputable section DensityLemmas

lemma card_filter_mod_eq_le (N m r : ℕ) :
    ((Finset.range N).filter (fun n => n ≡ r [MOD m])).card ≤ N / m + 1 := by
  have h_set :
      Finset.filter (fun n => n ≡ r [MOD m]) (Finset.range N) ⊆
        Finset.image (fun q => q * m + (r % m)) (Finset.range (N / m + 1)) := by
    intro n hn
    obtain ⟨hnlt,heq⟩ := Finset.mem_filter.mp hn
    have hnN := Finset.mem_range.mp hnlt
    refine Finset.mem_image.mpr ⟨n/m, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN.le)), ?_⟩
    change n % m = r % m at heq
    rw [← heq, Nat.mul_comm (n/m) m, Nat.add_comm, Nat.mod_add_div]
  exact le_trans (Finset.card_le_card h_set) (Finset.card_image_le.trans (by norm_num))

lemma card_filter_modEq_and_modEq_le (N m n a b : ℕ) (hcop : Nat.Coprime m n) :
    ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤ N / (m * n) + 1 := by
  classical
  have hsub :
      (Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n]) ⊆
        (Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n]) := by
    intro x hx
    simp [Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨hx.1, ?_⟩
    exact Nat.chineseRemainder_modEq_unique (co := hcop) hx.2.1 hx.2.2
  have hcard :
      ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤
        ((Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n])).card :=
    Finset.card_le_card hsub
  exact le_trans hcard (card_filter_mod_eq_le N (m * n) (Nat.chineseRemainder hcop a b))

end DensityLemmas

lemma zmod25_sq_eq_neg_one_iff :
    ∀ x : ZMod 25, x ^ 2 = (-1 : ZMod 25) ↔ x = (7 : ZMod 25) ∨ x = (18 : ZMod 25) := by
  decide

lemma mod25_eq_7_or_18_of_dvd_sq_add_one {n : ℕ} (h : 25 ∣ n ^ 2 + 1) :
    n % 25 = 7 ∨ n % 25 = 18 := by
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod 25) = 0 :=
    (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) 25).2 h
  have hsq : (n : ZMod 25) ^ 2 = (-1 : ZMod 25) := by
    have : (n : ZMod 25) ^ 2 + 1 = 0 := by
      simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
    simpa using (eq_neg_of_add_eq_zero_left this)
  have hx : (n : ZMod 25) = (7 : ZMod 25) ∨ (n : ZMod 25) = (18 : ZMod 25) :=
    (zmod25_sq_eq_neg_one_iff (n : ZMod 25)).1 hsq
  cases hx with
  | inl h7 =>
      left
      have hn : n % 25 = 7 % 25 := (ZMod.natCast_eq_natCast_iff' n 7 25).1 h7
      simpa [Nat.mod_eq_of_lt (by decide : 7 < 25)] using hn
  | inr h18 =>
      right
      have hn : n % 25 = 18 % 25 := (ZMod.natCast_eq_natCast_iff' n 18 25).1 h18
      simpa [Nat.mod_eq_of_lt (by decide : 18 < 25)] using hn

lemma not_dvd_25_sq_add_one_of_mod_ne (n : ℕ) (h : n % 25 ≠ 7 ∧ n % 25 ≠ 18) :
    ¬ (25 ∣ n ^ 2 + 1) := by
  intro h25
  have := mod25_eq_7_or_18_of_dvd_sq_add_one (n := n) h25
  cases this with
  | inl h7 => exact h.1 h7
  | inr h18 => exact h.2 h18

lemma not_dvd_four_sq_add_one (n : ℕ) : ¬ (4 ∣ n ^ 2 + 1) := by
  intro h4
  have hmod : (n ^ 2 + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
  have hrewrite : (n ^ 2 + 1) % 4 = ((n % 4) ^ 2 + 1) % 4 := by
      calc
      (n ^ 2 + 1) % 4 = (n ^ 2 % 4 + 1 % 4) % 4 := by
        simp [Nat.add_mod]
      _ = (((n % 4) ^ 2 % 4) + 1) % 4 := by
        simp [Nat.pow_mod]
      _ = ((n % 4) ^ 2 + 1) % 4 := by
        simp [Nat.add_mod]
  have hmod' : ((n % 4) ^ 2 + 1) % 4 = 0 := by simpa [hrewrite] using hmod
  have hn4 : n % 4 ≤ 3 := by
    have hn4lt : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
    have : n % 4 < 3 + 1 := by simpa using hn4lt
    exact (Nat.lt_succ_iff).1 this
  interval_cases hcase : n % 4 <;> simp at hmod'

def SawhneyMainAt (η : ℝ) (N₀ : ℕ) : Prop :=
  0 < η ∧ η < (1 / 25 : ℝ) ∧
    ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.range N →
      NonSquarefreeProductProp A →
      (A.card : ℝ) ≥ (1/25 - η) * (N : ℝ) →
      (A ⊆ A₇ N ∨ A ⊆ A₁₈ N)

def Problem848Statement (N : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Finset.range N → NonSquarefreeProductProp A →
    A.card ≤ (A₇ N).card

lemma card_range_filter_mod25_eq (r : ℕ) (hr : r ≤ 24) (N : ℕ) :
    ((Finset.range N).filter (fun n => n % 25 = r)).card = (N + (24 - r)) / 25 := by
  classical
  have hr_lt : r < 25 := lt_of_le_of_lt hr (by decide : 24 < 25)
  set K : ℕ := (N + (24 - r)) / 25
  have hbij :
      ((Finset.range N).filter (fun n => n % 25 = r)).card = (Finset.range K).card := by
    refine (Finset.card_bij (s := Finset.range K) (t := (Finset.range N).filter (fun n => n % 25 = r))
      (i := fun k _hk => 25 * k + r) ?_ ?_ ?_).symm
    · intro k hk
      have hk' : k < K := by simpa [Finset.mem_range] using hk
      have hk1 : k + 1 ≤ K := Nat.succ_le_iff.2 hk'
      have hmul : 25 * (k + 1) ≤ 25 * K := Nat.mul_le_mul_left 25 hk1
      have hK : 25 * K ≤ N + (24 - r) := by
        simpa [K] using Nat.mul_div_le (N + (24 - r)) 25
      have hmul' : 25 * (k + 1) ≤ N + (24 - r) := le_trans hmul hK
      have hlt : 25 * k + r < N := by omega
      simp [Finset.mem_filter, Finset.mem_range, hlt, Nat.add_mod, hr_lt]
    · intro k₁ _hk₁ k₂ _hk₂ h
      have h' : 25 * k₁ = 25 * k₂ := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by decide : 0 < 25) h'
    · intro a ha
      have ha' : a < N ∧ a % 25 = r := by
        simpa [Finset.mem_filter, Finset.mem_range] using ha
      have ha_eq : 25 * (a / 25) + r = a := by
        have h := Nat.mod_add_div a 25
        simpa [ha'.2, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      refine ⟨a / 25, ?_, ?_⟩
      · have hlt : 25 * (a / 25) + r < N := by simpa [ha_eq] using ha'.1
        have hmul : 25 * ((a / 25) + 1) ≤ N + (24 - r) := by omega
        have hle : a / 25 + 1 ≤ K := by
          have hmul' : (a / 25 + 1) * 25 ≤ N + (24 - r) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
          have := (Nat.le_div_iff_mul_le (k0 := (by decide : 0 < 25))).2 hmul'
          simpa [K] using this
        have hltK : a / 25 < K := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle
        simpa [Finset.mem_range] using hltK
      · exact ha_eq
  simpa [Finset.card_range, K] using hbij

lemma A₇_card (N : ℕ) : (A₇ N).card = (N + 17) / 25 := by
  simpa [A₇, Nat.sub_sub] using (card_range_filter_mod25_eq 7 (by decide) N)

lemma A₁₈_card (N : ℕ) : (A₁₈ N).card = (N + 6) / 25 := by
  simpa [A₁₈, Nat.sub_sub] using (card_range_filter_mod25_eq 18 (by decide) N)

lemma A₁₈_card_le_A₇ (N : ℕ) : (A₁₈ N).card ≤ (A₇ N).card := by
  have h : N + 6 ≤ N + 17 := Nat.add_le_add_left (by decide : 6 ≤ 17) N
  simpa [A₇_card, A₁₈_card] using Nat.div_le_div_right h

lemma card_gt_A₇_implies_dense {η : ℝ} (hη : 0 < η) {N : ℕ} {A : Finset ℕ}
    (hgt : (A₇ N).card < A.card) :
    (A.card : ℝ) ≥ (1/25 - η) * (N : ℝ) := by
  have hsucc : (A₇ N).card + 1 ≤ A.card := Nat.succ_le_iff.2 hgt
  have hA : ((A₇ N).card + 1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hsucc
  have hA7 : ((N + 17 : ℝ) / 25) < ((A₇ N).card + 1 : ℝ) := by
    have hq : (25 : ℝ) * ((A₇ N).card + 1 : ℝ) > (N + 17 : ℝ) := by
      have hq_nat : 25 * ((A₇ N).card + 1) > N + 17 := by
        have hcard : (A₇ N).card = (N + 17) / 25 := A₇_card N
        have hdiv : 25 * ((N + 17) / 25) + (N + 17) % 25 = N + 17 := Nat.div_add_mod (N + 17) 25
        have hmod : (N + 17) % 25 < 25 := Nat.mod_lt _ (by decide : 0 < 25)
        omega
      exact_mod_cast hq_nat
    nlinarith
  have hN17 : (N + 17 : ℝ) / 25 ≥ (1 / 25 - η) * (N : ℝ) := by nlinarith
  have : (A.card : ℝ) ≥ (N + 17 : ℝ) / 25 := by
    have : (N + 17 : ℝ) / 25 ≤ (A.card : ℝ) := le_trans hA7.le hA
    exact this
  exact le_trans hN17 this

theorem problem_848_large_of_sawhney {η : ℝ} {N₀ : ℕ} (h : SawhneyMainAt η N₀) :
    ∀ N ≥ N₀, Problem848Statement N := by
  classical
  rcases h with ⟨hη, _hηsmall, hmain⟩
  intro N hN A hAsub hAprop
  by_contra hle
  have hgt : (A₇ N).card < A.card := lt_of_not_ge hle
  have hdense : (A.card : ℝ) ≥ (1/25 - η) * (N : ℝ) := card_gt_A₇_implies_dense hη hgt
  have hstruct := hmain N hN A hAsub hAprop hdense
  cases hstruct with
  | inl hsub7 => exact (not_le_of_gt hgt) (Finset.card_le_card hsub7)
  | inr hsub18 =>
      have hcard18 : A.card ≤ (A₁₈ N).card := Finset.card_le_card hsub18
      have h18le7 : (A₁₈ N).card ≤ (A₇ N).card := A₁₈_card_le_A₇ N
      exact (not_le_of_gt hgt) (le_trans hcard18 h18le7)

open Filter Finset

def primeCutoff : ℕ := 2000

lemma primeCutoff_pos : 0 < primeCutoff := by decide

def primesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime

def diagPrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p % 4 = 1 ∧ 13 ≤ p)

def offPrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p ≠ 2 ∧ p ≠ 5)

def no5PrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p ≠ 5)

/-- Each prime passes all trial divisions, including trial division by itself. -/
private def sievePass (p : ℕ) : Bool :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43].all fun d =>
    decide (d = 1 ∨ d = p ∨ ¬ d ∣ p)

private theorem prime_sievePass {p : ℕ} (hp : p.Prime) : sievePass p = true := by
  apply List.all_eq_true.mpr
  intro d _
  apply decide_eq_true
  by_cases hd : d ∣ p
  · rcases (Nat.dvd_prime hp).mp hd with eq | eq
    · exact Or.inl eq
    · exact Or.inr (Or.inl eq)
  · exact Or.inr (Or.inr hd)

/-- Round each reciprocal square upward in units of 10⁻¹⁰. -/
private def upperWeight (p : ℕ) : ℕ := 10000000000 / (p*p) + 1

private def sieveTerm (keep : ℕ → Bool) (p : ℕ) : ℕ :=
  if 2 ≤ p ∧ keep p = true ∧ sievePass p = true then upperWeight p else 0

private def accumulate (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => accumulate f i + f i

private theorem accumulate_eq (f : ℕ → ℕ) (n : ℕ) :
    accumulate f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [accumulate]
  | succ n ih => rw [accumulate, Finset.sum_range_succ, ih]

private theorem sum_reciprocal_bound (P : Finset ℕ) (pos : ∀ p ∈ P, 0 < p) :
    ∑ p ∈ P, (1:ℚ)/(p:ℚ)^2 ≤ ((∑ p ∈ P, upperWeight p : ℕ):ℚ) / 10000000000 := by
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have strict := Nat.lt_mul_div_succ 10000000000 (Nat.mul_pos (pos p hp) (pos p hp))
  have h : (10000000000 : ℚ) ≤ ((p*p:ℕ):ℚ) * (upperWeight p : ℚ) := by
    exact_mod_cast strict.le
  push_cast at h
  apply (div_le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast pos p hp)) (by norm_num)).mpr
  linarith only [show (10000000000 : ℚ) ≤ (p:ℚ)^2 * (upperWeight p : ℚ) by simpa [sq] using h]

private theorem sieve_bound (P : Finset ℕ) (keep : ℕ → Bool)
    (member : ∀ p ∈ P, p ∈ Finset.range 2001 ∧ p.Prime ∧ keep p = true) :
    (∑ p ∈ P, (1:ℚ)/(p:ℚ)^2) ≤ (accumulate (sieveTerm keep) 2001 : ℚ) / 10000000000 := by
  have subset : P ⊆ Finset.range 2001 := fun p hp => (member p hp).1
  have total : ∑ p ∈ P, upperWeight p ≤ accumulate (sieveTerm keep) 2001 := by
    rw [accumulate_eq]
    calc
      ∑ p ∈ P, upperWeight p = ∑ p ∈ P, sieveTerm keep p := by
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨_, pr, hkeep⟩ := member p hp
        simp only [sieveTerm, pr.two_le, hkeep, prime_sievePass pr, and_self, if_true]
      _ ≤ ∑ p ∈ Finset.range 2001, sieveTerm keep p :=
        Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)
  apply (sum_reciprocal_bound P (fun p hp => (member p hp).2.1.pos)).trans
  exact div_le_div_of_nonneg_right (by exact_mod_cast total) (by norm_num)

private def diagKeep (p : ℕ) : Bool := decide (p % 4 = 1 ∧ 13 ≤ p)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem diagSumCertificate :
    accumulate (sieveTerm diagKeep) 2001 = 137847261 := by decide +kernel

private def diagPrimeSumCoarse : ℚ :=
  ∑ p ∈ diagPrimesCoarse, (1:ℚ)/(p:ℚ)^2

private theorem diagPrimesCoarse_sum_eq :
    (∑ p ∈ diagPrimesCoarse, (1:ℚ)/(p:ℚ)^2) = diagPrimeSumCoarse := rfl

private theorem diagPrimeSumCoarse_bound :
    diagPrimeSumCoarse + (1:ℚ)/7984 ≤ (1:ℚ) / (359/5) := by
  have estimate := sieve_bound diagPrimesCoarse diagKeep (fun p hp => by
    obtain ⟨hpr, pass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrange, prime⟩ := Finset.mem_filter.mp hpr
    exact ⟨hrange, prime, decide_eq_true pass⟩)
  rw [diagSumCertificate] at estimate
  exact (add_le_add_left estimate ((1:ℚ)/7984) : _).trans (by norm_num [primeCutoff])

private def offKeep (p : ℕ) : Bool := decide (p ≠ 2 ∧ p ≠ 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem offSumCertificate :
    accumulate (sieveTerm offKeep) 2001 = 1621891203 := by decide +kernel

private def offPrimeSumCoarse : ℚ :=
  ∑ p ∈ offPrimesCoarse, (1:ℚ)/(p:ℚ)^2

private theorem offPrimesCoarse_sum_eq :
    (∑ p ∈ offPrimesCoarse, (1:ℚ)/(p:ℚ)^2) = offPrimeSumCoarse := rfl

private theorem offPrimeSumCoarse_bound :
    offPrimeSumCoarse + (1:ℚ)/primeCutoff ≤ (163:ℚ) / 1000 := by
  have estimate := sieve_bound offPrimesCoarse offKeep (fun p hp => by
    obtain ⟨hpr, pass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrange, prime⟩ := Finset.mem_filter.mp hpr
    exact ⟨hrange, prime, decide_eq_true pass⟩)
  rw [offSumCertificate] at estimate
  exact (add_le_add_left estimate ((1:ℚ)/2000) : _).trans (by norm_num [primeCutoff])

private def no5Keep (p : ℕ) : Bool := decide (p ≠ 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem no5SumCertificate :
    accumulate (sieveTerm no5Keep) 2001 = 4121891204 := by decide +kernel

private def no5PrimeSumCoarse : ℚ :=
  ∑ p ∈ no5PrimesCoarse, (1:ℚ)/(p:ℚ)^2

private theorem no5PrimesCoarse_sum_eq :
    (∑ p ∈ no5PrimesCoarse, (1:ℚ)/(p:ℚ)^2) = no5PrimeSumCoarse := rfl

private theorem no5PrimeSumCoarse_bound :
    no5PrimeSumCoarse + (1:ℚ)/primeCutoff ≤ (413:ℚ) / 1000 := by
  have estimate := sieve_bound no5PrimesCoarse no5Keep (fun p hp => by
    obtain ⟨hpr, pass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrange, prime⟩ := Finset.mem_filter.mp hpr
    exact ⟨hrange, prime, decide_eq_true pass⟩)
  rw [no5SumCertificate] at estimate
  exact (add_le_add_left estimate ((1:ℚ)/2000) : _).trans (by norm_num [primeCutoff])

lemma sum_Ioc_inv_sq_le_inv (B N : ℕ) (hB : B ≠ 0) :
    (∑ i ∈ Finset.Ioc B N, (1 : ℚ) / (i ^ 2 : ℚ)) ≤ (1 : ℚ) / B := by
  by_cases hBN : B < N
  · have hle : B ≤ N := Nat.le_of_lt hBN
    have hsub := sum_Ioc_inv_sq_le_sub (α := ℚ) (k := B) (n := N) hB hle
    have hnonneg : 0 ≤ (N : ℚ)⁻¹ := by positivity
    have hsub' : (B : ℚ)⁻¹ - (N : ℚ)⁻¹ ≤ (B : ℚ)⁻¹ := sub_le_self _ hnonneg
    simpa [one_div] using hsub.trans hsub'
  · have hIoc : (Finset.Ioc B N) = ∅ := by
      apply Finset.Ioc_eq_empty
      exact not_lt.2 (Nat.le_of_not_gt hBN)
    simp [hIoc, one_div]

def diagPrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p % 4 = 1 ∧ 13 ≤ p)

def offPrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p ≠ 2 ∧ p ≠ 5)

def no5PrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p ≠ 5)

lemma sq_pred_add_one_lt_sq (N : ℕ) (hN : 100 ≤ N) : (N - 1) * (N - 1) + 1 < N ^ 2 := by
  have h2 : 2 ≤ N := le_trans (by norm_num : 2 ≤ 100) hN
  have h1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 2) h2
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel h1
  have hpos : 0 < N - 1 := by omega
  calc (N - 1) * (N - 1) + 1
      < (N - 1) * (N - 1) + 2 * (N - 1) + 1 := by omega
    _ = (N - 1 + 1) * (N - 1 + 1) := by ring
    _ = N * N := by rw [hsub]
    _ = N ^ 2 := by rw [Nat.pow_two]

/-- Only one out of four integers can occur in the diagonal prime tail.
Send 4j+1 to j and majorize its reciprocal square by 1/(16j²). -/
private theorem diag_progression_tail (N : ℕ) :
    (∑ p ∈ (Finset.Ioc primeCutoff N).filter (fun p => p%4=1), (1 : ℚ)/(p:ℚ)^2)
      ≤ 1/7984 := by
  classical
  let P := (Finset.Ioc primeCutoff N).filter (fun p => p%4=1)
  let f (j : ℕ) : ℚ := 1/(j:ℚ)^2
  have bounds (p : ℕ) (hp : p ∈ P) : 2000<p ∧ p≤N ∧ p%4=1 := by
    obtain ⟨hr,hm⟩ := Finset.mem_filter.mp hp
    exact ⟨(Finset.mem_Ioc.mp hr).1,(Finset.mem_Ioc.mp hr).2,hm⟩
  have inj : Set.InjOn (fun p : ℕ => p/4) P := by
    intro i hi j hj eq
    have bi := bounds i hi
    have bj := bounds j hj
    dsimp at eq
    omega
  have sub : P.image (·/4) ⊆ Finset.Ioc 499 N := by
    rintro j hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hj
    have b := bounds p hp
    exact Finset.mem_Ioc.mpr ⟨by omega,by omega⟩
  have point (p : ℕ) (hp : p ∈ P) : f p ≤ (1/16 : ℚ)*f (p/4) := by
    have b := bounds p hp
    have pos : 0 < ((p/4:ℕ):ℚ) := by exact_mod_cast (show 0 < p/4 by omega)
    have ppos : 0 < (p:ℚ) := by exact_mod_cast (show 0 < p by omega)
    have ord : 4*((p/4:ℕ):ℚ) ≤ (p:ℚ) := by exact_mod_cast (show 4*(p/4)≤p by omega)
    dsimp [f]
    have square := mul_le_mul ord ord (by positivity) ppos.le
    field_simp
    nlinarith only [square]
  have major := Finset.sum_le_sum point
  rw [← Finset.mul_sum,← Finset.sum_image inj] at major
  have mon : ∑ j ∈ P.image (·/4), f j ≤ ∑ j ∈ Finset.Ioc 499 N, f j :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun i _ _ => by dsimp [f]; positivity)
  have tail : ∑ j ∈ Finset.Ioc 499 N, f j ≤ 1/499 := sum_Ioc_inv_sq_le_inv 499 N (by decide)
  change (∑ p ∈ P, f p) ≤ _
  linarith only [major,mon,tail]

set_option maxRecDepth 10000 in
lemma sum_diagPrimesUpTo_le (N : ℕ) :
    (∑ p ∈ diagPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (1 : ℚ) / (359/5) := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  let tailP := (Finset.Ioc primeCutoff N).filter (fun p => p%4=1)
  have hsubset : diagPrimesUpTo N ⊆ diagPrimesCoarse ∪ tailP := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p % 4 = 1 ∧ 13 ≤ p := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ diagPrimesCoarse := by
        simp [diagPrimesCoarse, hp_mem_cutoff, hp_cond.1, hp_cond.2]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.mpr ⟨this,hp_cond.1⟩))
  have hdisj : Disjoint diagPrimesCoarse tailP := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 (Finset.mem_filter.mp hp_Ioc).1).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤ ∑ p ∈ diagPrimesCoarse ∪ tailP, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤
        diagPrimeSumCoarse + (∑ i ∈ tailP, f i) := by
    calc
      (∑ p ∈ diagPrimesUpTo N, f p) ≤
          ∑ p ∈ diagPrimesCoarse ∪ tailP, f p := hsum_le_union
      _ = (∑ p ∈ diagPrimesCoarse, f p) + (∑ i ∈ tailP, f i) := by
          simp [Finset.sum_union hdisj]
      _ = diagPrimeSumCoarse + (∑ i ∈ tailP, f i) := by
          simp only [f, diagPrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ tailP, f i) ≤ (1 : ℚ) / 7984 := by
    exact diag_progression_tail N
  have hsum_le' :
      (∑ p ∈ diagPrimesUpTo N, f p) ≤ diagPrimeSumCoarse + (1 : ℚ) / 7984 := by
    exact hsum_le.trans (add_le_add_right htail diagPrimeSumCoarse)
  exact hsum_le'.trans diagPrimeSumCoarse_bound

set_option maxRecDepth 10000 in
lemma sum_offPrimesUpTo_le (N : ℕ) :
    (∑ p ∈ offPrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (163 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : offPrimesUpTo N ⊆ offPrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p ≠ 2 ∧ p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ offPrimesCoarse := by
        simp [offPrimesCoarse, hp_mem_cutoff, hp_cond.1, hp_cond.2]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint offPrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ offPrimesUpTo N, f p) ≤ ∑ p ∈ offPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ offPrimesUpTo N, f p) ≤
        offPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ offPrimesUpTo N, f p) ≤
          ∑ p ∈ offPrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ offPrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = offPrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, offPrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ offPrimesUpTo N, f p) ≤ offPrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail offPrimeSumCoarse)
  exact hsum_le'.trans offPrimeSumCoarse_bound

set_option maxRecDepth 10000 in
lemma sum_no5PrimesUpTo_le (N : ℕ) :
    (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (413 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : no5PrimesUpTo N ⊆ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ no5PrimesCoarse := by
        simp [no5PrimesCoarse, hp_mem_cutoff, hp_cond]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint no5PrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
        no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
          ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ no5PrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, no5PrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ no5PrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail no5PrimeSumCoarse)
  exact hsum_le'.trans no5PrimeSumCoarse_bound

def residues25 : Finset ℕ :=
  (Finset.range 25).filter (fun t => t ≠ 7 ∧ t ≠ 18)

lemma residues25_card : residues25.card = 23 := by
  decide

def residues50odd : Finset ℕ :=
  (Finset.range 50).filter (fun t => t % 2 = 1 ∧ t % 25 ≠ 7 ∧ t % 25 ≠ 18)

lemma residues50odd_card : residues50odd.card = 23 := by
  decide

lemma primesUpTo_card (B : ℕ) : (primesUpTo B).card = B.primeCounting := by
  classical
  simp [primesUpTo, Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

lemma prime_eq_of_dvd_2 (p : ℕ) (hp : Nat.Prime p) (h : p ∣ 2) : p = 2 := by
  have hp_le2 : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) h
  have hp_ge2 : 2 ≤ p := hp.two_le
  omega

lemma prime_eq_of_dvd_5 (p : ℕ) (hp : Nat.Prime p) (h : p ∣ 5) : p = 5 := by
  have hp_le5 : p ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) h
  have hp_ge2 : 2 ≤ p := hp.two_le
  interval_cases p <;> simp_all

lemma coprime_25_pow_two_of_prime_ne5 (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    Nat.Coprime 25 (p ^ 2) := by
  have hnot : ¬ p ∣ 25 := by
    intro h
    have hpow : p ∣ 5 ^ 2 := by
      have : (5 ^ 2 : ℕ) = 25 := by rfl
      simpa [this] using h
    have h5 : p ∣ 5 := hp.dvd_of_dvd_pow hpow
    exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 25) (m := 2) hnot

lemma coprime_100_pow_two_of_prime_ne2_ne5 (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    Nat.Coprime 100 (p ^ 2) := by
  have hnot : ¬ p ∣ 100 := by
    intro h
    have hpow : p ∣ 10 ^ 2 := by
      have : (10 ^ 2 : ℕ) = 100 := by rfl
      simpa [this] using h
    have h10 : p ∣ 10 := hp.dvd_of_dvd_pow hpow
    have hmul : p ∣ 2 ∨ p ∣ 5 := by
      have : 10 = 2 * 5 := by rfl
      simpa [this] using (hp.dvd_mul.1 (by simpa [this] using h10))
    cases hmul with
    | inl h2 => exact hp2 (prime_eq_of_dvd_2 p hp h2)
    | inr h5 => exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 100) (m := 2) hnot

lemma prime_square_exists {n : ℕ} (hn : ¬ Squarefree n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ n := by
  classical
  have hnot : ¬ ∀ p : ℕ, Nat.Prime p → ¬ p * p ∣ n := by
    intro hall
    exact hn ((Nat.squarefree_iff_prime_squarefree).2 hall)
  push Not at hnot
  rcases hnot with ⟨p, hp, hpp⟩
  refine ⟨p, hp, ?_⟩
  simpa [pow_two] using hpp

lemma prime_square_exists_ne5 {n : ℕ} (hn : ¬ Squarefree n) (h25 : ¬ 25 ∣ n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ n := by
  obtain ⟨p, hp, hp2⟩ := prime_square_exists (n := n) hn
  refine ⟨p, hp, ?_, hp2⟩
  intro hp5
  subst hp5
  have : 25 ∣ n := by simpa [pow_two] using hp2
  exact (h25 this).elim

lemma cross_residue_7_18_not_div_25 (a b : ℕ) (ha : a % 25 = 7) (hb : b % 25 = 18) :
    ¬ (25 ∣ a * b + 1) := by
  have hb_ne : b % 25 ≠ 7 := by
    intro hb7
    have : (18 : ℕ) = 7 := hb.symm.trans hb7
    exact (by decide : (18 : ℕ) ≠ 7) this
  exact cross_residue_not_div_25_of_residue 7 a b (by norm_num) ha hb_ne

lemma cross_residue_18_7_not_div_25 (a b : ℕ) (ha : a % 25 = 18) (hb : b % 25 = 7) :
    ¬ (25 ∣ a * b + 1) := by
  simpa [Nat.mul_comm] using cross_residue_7_18_not_div_25 b a hb ha

lemma off_count_modEq25_le (N p b t : ℕ) (hp : Nat.Prime p) (hb : ¬ p ∣ b) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  classical
  have hcop : Nat.Coprime 25 (p ^ 2) := coprime_25_pow_two_of_prime_ne5 p hp hp5
  have hp0 : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let r : ℕ := rZ.val
  have hrZ : (r : ZMod (p ^ 2)) = rZ := by
    have : NeZero (p ^ 2) := ⟨hp0⟩
    simp [r, rZ]
  have hsubset :
      (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ a ≡ r [MOD p ^ 2]) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.1, ?_⟩
    have hdiv : p ^ 2 ∣ b * a + 1 := ha.2.2
    have hEq : (a : ZMod (p ^ 2)) = -((b : ZMod (p ^ 2))⁻¹) := by
      have : p ^ 2 ∣ b * a + 1 := by simpa [Nat.mul_comm] using hdiv
      exact (dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv (p := p) (a := b) (b := a) hp hb).1 this
    have : (a : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
      simpa [rZ, hrZ] using hEq
    exact (ZMod.natCast_eq_natCast_iff a r (p ^ 2)).1 this
  have hcard := Finset.card_le_card hsubset
  exact le_trans hcard (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r hcop)

private lemma not_sq_dvd_mul_add_one_of_prime_dvd_left
    {p b a : ℕ} (hp : Nat.Prime p) (hb : p ∣ b) : ¬ p ^ 2 ∣ b * a + 1 := by
  intro hp2
  have hp1 : p ∣ b * a + 1 := Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) hp2
  have hpa : p ∣ b * a := dvd_mul_of_dvd_left hb a
  have : p ∣ 1 := (Nat.dvd_add_right hpa).mp hp1
  exact hp.not_dvd_one this

lemma filter_empty_of_prime_dvd_left_of_pred
    {N p b : ℕ} (hp : Nat.Prime p) (hb : p ∣ b)
    (pred : ℕ → Prop) [DecidablePred pred] :
    (Finset.range N).filter (fun a => pred a ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
  classical
  ext a
  simp [not_sq_dvd_mul_add_one_of_prime_dvd_left (p := p) (b := b) (a := a) hp hb]

lemma off_count_modEq25_le' (N p b t : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  by_cases hb : p ∣ b
  · 
    have hempty :
        (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
      simpa using
        (filter_empty_of_prime_dvd_left_of_pred (N := N) (p := p) (b := b) hp hb
          (pred := fun a => a ≡ t [MOD 25]))
    simp [hempty]
  · exact off_count_modEq25_le N p b t hp hb hp5

lemma off_count_modEq100_le (N p b t25 t4 : ℕ) (hp : Nat.Prime p) (hb : ¬ p ∣ b)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (100 * p ^ 2) + 1 := by
  classical
  have hcop25_4 : Nat.Coprime 25 4 := by decide
  have hsub :
      (Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ?_, ha.2.2.2⟩
    exact Nat.chineseRemainder_modEq_unique (co := hcop25_4) ha.2.1 ha.2.2.1
  have hcard :
      ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
        ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1)).card :=
    Finset.card_le_card hsub
  have hcop : Nat.Coprime 100 (p ^ 2) := coprime_100_pow_two_of_prime_ne2_ne5 p hp hp2 hp5
  have hp0 : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let r : ℕ := rZ.val
  have hrZ : (r : ZMod (p ^ 2)) = rZ := by
    have : NeZero (p ^ 2) := ⟨hp0⟩
    simp [r, rZ]
  have hsubset2 :
      (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ a ≡ r [MOD p ^ 2]) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.1, ?_⟩
    have hdiv : p ^ 2 ∣ b * a + 1 := ha.2.2
    have hEq : (a : ZMod (p ^ 2)) = -((b : ZMod (p ^ 2))⁻¹) := by
      have : p ^ 2 ∣ b * a + 1 := by simpa [Nat.mul_comm] using hdiv
      exact (dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv (p := p) (a := b) (b := a) hp hb).1 this
    have : (a : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
      simpa [rZ, hrZ] using hEq
    exact (ZMod.natCast_eq_natCast_iff a r (p ^ 2)).1 this
  have hcard2 :
      ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ p ^ 2 ∣ b * a + 1)).card ≤
        ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ a ≡ r [MOD p ^ 2])).card :=
    Finset.card_le_card hsubset2
  have hfinal :
      ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_4 t25 t4 [MOD 100] ∧ a ≡ r [MOD p ^ 2])).card ≤
        N / (100 * p ^ 2) + 1 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 100 (p ^ 2) (Nat.chineseRemainder hcop25_4 t25 t4) r hcop)
  exact le_trans (le_trans hcard hcard2) hfinal

lemma off_count_modEq100_le' (N p b t25 t4 : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (100 * p ^ 2) + 1 := by
  by_cases hb : p ∣ b
  · 
    have hempty :
        (Finset.range N).filter
            (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4] ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
      simpa [and_assoc] using
        (filter_empty_of_prime_dvd_left_of_pred (N := N) (p := p) (b := b) hp hb
          (pred := fun a => a ≡ t25 [MOD 25] ∧ a ≡ t4 [MOD 4]))
    simp [hempty]
  · exact off_count_modEq100_le N p b t25 t4 hp hb hp2 hp5

lemma prime_ge_13_of_mod4_one_ne5 (p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp5 : p ≠ 5) :
    13 ≤ p := by
  have hp_ge2 : 2 ≤ p := hp.two_le
  by_contra h
  have hp_le12 : p ≤ 12 := by
    have hp_lt13 : p < 13 := lt_of_not_ge h
    have : p < 12 + 1 := by simpa using hp_lt13
    exact (Nat.lt_succ_iff).1 this
  interval_cases p <;> simp_all +decide

lemma coprime_50_pow_two_of_prime_ne2_ne5 (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    Nat.Coprime 50 (p ^ 2) := by
  have hnot : ¬ p ∣ 50 := by
    intro h
    have hmul : p ∣ 2 * 25 := by
      have : 2 * 25 = 50 := by rfl
      simpa [this] using h
    have hdiv : p ∣ 2 ∨ p ∣ 25 := hp.dvd_mul.1 hmul
    cases hdiv with
    | inl h2 => exact hp2 (prime_eq_of_dvd_2 p hp h2)
    | inr h25 =>
        have hpow : p ∣ 5 ^ 2 := by
          have : (5 ^ 2 : ℕ) = 25 := by rfl
          simpa [this] using h25
        have h5 : p ∣ 5 := hp.dvd_of_dvd_pow hpow
        exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 50) (m := 2) hnot

lemma diag_count_modEq25_le (N p t : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      2 * (N / (25 * p ^ 2) + 1) := by
  classical
  have hcop : Nat.Coprime 25 (p ^ 2) := coprime_25_pow_two_of_prime_ne5 p hp hp5
  obtain ⟨r₁, r₂, hr⟩ :
      ∃ r₁ r₂ : ZMod (p ^ 2),
        r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧ ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
    obtain ⟨r,t,_,rest⟩ := two_roots_mod_p_squared p hp hmod
    exact ⟨r,t,rest⟩
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  let S₁ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ n ≡ r₁.val [MOD p ^ 2])
  let S₂ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ n ≡ r₂.val [MOD p ^ 2])
  have hsubset : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    simp [S, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hdiv : (p ^ 2 : ℕ) ∣ n ^ 2 + 1 := hn.2.2
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) (p ^ 2)).2 hdiv
    have hsq : (n : ZMod (p ^ 2)) ^ 2 = (-1 : ZMod (p ^ 2)) := by
      have : (n : ZMod (p ^ 2)) ^ 2 + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
      simpa using (eq_neg_of_add_eq_zero_left this)
    have hcases : (n : ZMod (p ^ 2)) = r₁ ∨ (n : ZMod (p ^ 2)) = r₂ := hr.2.2.2 _ hsq
    cases hcases with
    | inl hn1 =>
        refine Or.inl ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₁.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₁ := hn1
            _ = (r₁.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₁.val (p ^ 2)).1 hcast
    | inr hn2 =>
        refine Or.inr ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₂.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₂ := hn2
            _ = (r₂.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₂.val (p ^ 2)).1 hcast
  have hcard : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsubset
  have hunion : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
  have hS₁ : S₁.card ≤ N / (25 * p ^ 2) + 1 := by
    simpa [S₁, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r₁.val hcop)
  have hS₂ : S₂.card ≤ N / (25 * p ^ 2) + 1 := by
    simpa [S₂, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r₂.val hcop)
  have : S.card ≤ (N / (25 * p ^ 2) + 1) + (N / (25 * p ^ 2) + 1) :=
    le_trans (le_trans hcard hunion) (add_le_add hS₁ hS₂)
  simpa [S, two_mul] using this

lemma diag_count_modEq50_le (N p t : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      2 * (N / (50 * p ^ 2) + 1) := by
  classical
  have hcop : Nat.Coprime 50 (p ^ 2) := coprime_50_pow_two_of_prime_ne2_ne5 p hp hp2 hp5
  obtain ⟨r₁, r₂, hr⟩ :
      ∃ r₁ r₂ : ZMod (p ^ 2),
        r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧ ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
    obtain ⟨r,t,_,rest⟩ := two_roots_mod_p_squared p hp hmod
    exact ⟨r,t,rest⟩
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  let S₁ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ n ≡ r₁.val [MOD p ^ 2])
  let S₂ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ n ≡ r₂.val [MOD p ^ 2])
  have hsubset : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    simp [S, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hdiv : (p ^ 2 : ℕ) ∣ n ^ 2 + 1 := hn.2.2
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) (p ^ 2)).2 hdiv
    have hsq : (n : ZMod (p ^ 2)) ^ 2 = (-1 : ZMod (p ^ 2)) := by
      have : (n : ZMod (p ^ 2)) ^ 2 + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
      simpa using (eq_neg_of_add_eq_zero_left this)
    have hcases : (n : ZMod (p ^ 2)) = r₁ ∨ (n : ZMod (p ^ 2)) = r₂ := hr.2.2.2 _ hsq
    cases hcases with
    | inl hn1 =>
        refine Or.inl ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₁.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₁ := hn1
            _ = (r₁.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₁.val (p ^ 2)).1 hcast
    | inr hn2 =>
        refine Or.inr ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₂.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₂ := hn2
            _ = (r₂.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₂.val (p ^ 2)).1 hcast
  have hcard : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsubset
  have hunion : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
  have hS₁ : S₁.card ≤ N / (50 * p ^ 2) + 1 := by
    simpa [S₁, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 50 (p ^ 2) t r₁.val hcop)
  have hS₂ : S₂.card ≤ N / (50 * p ^ 2) + 1 := by
    simpa [S₂, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 50 (p ^ 2) t r₂.val hcop)
  have : S.card ≤ (N / (50 * p ^ 2) + 1) + (N / (50 * p ^ 2) + 1) :=
    le_trans (le_trans hcard hunion) (add_le_add hS₁ hS₂)
  simpa [S, two_mul] using this

lemma diag_count_mod25_ne_7_18_le (N p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      46 * (N / (25 * p ^ 2) + 1) := by
  classical
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  have hsubset :
      S ⊆ residues25.biUnion (fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
    intro n hn
    simp [S, Finset.mem_filter, Finset.mem_range] at hn
    set t : ℕ := n % 25
    have ht : t ∈ residues25 := by
      have htlt : t < 25 := Nat.mod_lt n (by decide : 0 < 25)
      have htne : t ≠ 7 ∧ t ≠ 18 := by
        refine ⟨?_, ?_⟩
        · simpa [t] using hn.2.1
        · simpa [t] using hn.2.2.1
      simp [residues25, Finset.mem_filter, Finset.mem_range, t, htlt, htne]
    refine (Finset.mem_biUnion).2 ?_
    refine ⟨t, ht, ?_⟩
    simp [Finset.mem_filter, Finset.mem_range, hn.1, hn.2.2.2]
    simpa [t] using (Nat.mod_modEq n 25).symm
  have hcard : S.card ≤ (residues25.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_le_card hsubset
  have hsum :
      (residues25.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
        ∑ t ∈ residues25,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_biUnion_le
  have hper :
      ∀ t ∈ residues25,
        ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
          2 * (N / (25 * p ^ 2) + 1) := by
    intro t ht
    exact diag_count_modEq25_le N p t hp hmod hp5
  have hsum' :
      (∑ t ∈ residues25,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 25] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card) ≤
        ∑ _t ∈ residues25, 2 * (N / (25 * p ^ 2) + 1) :=
    Finset.sum_le_sum fun t ht => hper t ht
  have hconst :
      (∑ _t ∈ residues25, 2 * (N / (25 * p ^ 2) + 1)) = 46 * (N / (25 * p ^ 2) + 1) := by
    classical
    have h46 : (46 : ℕ) = 23 * 2 := by rfl
    calc
      (∑ _t ∈ residues25, 2 * (N / (25 * p ^ 2) + 1)) = residues25.card * (2 * (N / (25 * p ^ 2) + 1)) := by
        simp
      _ = 23 * (2 * (N / (25 * p ^ 2) + 1)) := by
        simp [residues25_card]
      _ = (23 * 2) * (N / (25 * p ^ 2) + 1) := by
        exact (mul_assoc 23 2 (N / (25 * p ^ 2) + 1)).symm
      _ = 46 * (N / (25 * p ^ 2) + 1) := by
        simp [h46.symm]
  exact le_trans (le_trans hcard hsum) (le_trans hsum' (le_of_eq hconst))

lemma diag_count_mod50odd_ne_7_18_le (N p : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun n => n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      46 * (N / (50 * p ^ 2) + 1) := by
  classical
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n % 2 = 1 ∧ n % 25 ≠ 7 ∧ n % 25 ≠ 18 ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  have hsubset :
      S ⊆ residues50odd.biUnion (fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)) := by
    intro n hn
    simp [S, Finset.mem_filter, Finset.mem_range] at hn
    set t : ℕ := n % 50
    have ht : t ∈ residues50odd := by
      have htlt : t < 50 := Nat.mod_lt n (by decide : 0 < 50)
      have htodd : t % 2 = 1 := by
        have : (n % 50) % 2 = n % 2 := by
          simp [show 50 = 25 * 2 by rfl]
        simpa [t, this] using hn.2.1
      have htne7 : t % 25 ≠ 7 := by
        have : (n % 50) % 25 = n % 25 := by
          simp [show 50 = 25 * 2 by rfl]
        have hnne7 : n % 25 ≠ 7 := hn.2.2.1
        simpa [t, this] using hnne7
      have htne18 : t % 25 ≠ 18 := by
        have : (n % 50) % 25 = n % 25 := by
          simp [show 50 = 25 * 2 by rfl]
        have hnne18 : n % 25 ≠ 18 := hn.2.2.2.1
        simpa [t, this] using hnne18
      refine Finset.mem_filter.2 ?_
      refine ⟨?_, ?_⟩
      · exact Finset.mem_range.2 htlt
      · exact ⟨htodd, htne7, htne18⟩
    refine (Finset.mem_biUnion).2 ?_
    refine ⟨t, ht, ?_⟩
    simp [Finset.mem_filter, Finset.mem_range, hn.1, hn.2.2.2.2]
    simpa [t] using (Nat.mod_modEq n 50).symm
  have hcard : S.card ≤ (residues50odd.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_le_card hsubset
  have hsum :
      (residues50odd.biUnion fun t =>
        (Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
        ∑ t ∈ residues50odd,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card :=
    Finset.card_biUnion_le
  have hper :
      ∀ t ∈ residues50odd,
        ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
          2 * (N / (50 * p ^ 2) + 1) := by
    intro t ht
    exact diag_count_modEq50_le N p t hp hmod hp2 hp5
  have hsum' :
      (∑ t ∈ residues50odd,
          ((Finset.range N).filter (fun n => n ≡ t [MOD 50] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card) ≤
        ∑ _t ∈ residues50odd, 2 * (N / (50 * p ^ 2) + 1) :=
    Finset.sum_le_sum fun t ht => hper t ht
  have hconst :
      (∑ _t ∈ residues50odd, 2 * (N / (50 * p ^ 2) + 1)) = 46 * (N / (50 * p ^ 2) + 1) := by
    classical
    have h46 : (46 : ℕ) = 23 * 2 := by rfl
    calc
      (∑ _t ∈ residues50odd, 2 * (N / (50 * p ^ 2) + 1)) = residues50odd.card * (2 * (N / (50 * p ^ 2) + 1)) := by
        simp
      _ = 23 * (2 * (N / (50 * p ^ 2) + 1)) := by
        simp [residues50odd_card]
      _ = (23 * 2) * (N / (50 * p ^ 2) + 1) := by
        exact (mul_assoc 23 2 (N / (50 * p ^ 2) + 1)).symm
      _ = 46 * (N / (50 * p ^ 2) + 1) := by
        simp [h46.symm]
  exact le_trans (le_trans hcard hsum) (le_trans hsum' (le_of_eq hconst))

lemma prime_le_of_sq_dvd_lt_sq {p N X : ℕ} (hXpos : 0 < X) (hXlt : X < N ^ 2) (hp2 : p ^ 2 ∣ X) : p ≤ N := by
  have hp2_le : p ^ 2 ≤ X := Nat.le_of_dvd hXpos hp2
  have hp2_lt : p ^ 2 < N ^ 2 := lt_of_le_of_lt hp2_le hXlt
  by_contra hp_le
  have hNp : N ≤ p := le_of_lt (Nat.not_le.mp hp_le)
  have hN2le : N ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hNp 2
  exact (not_lt_of_ge hN2le) hp2_lt

lemma prime_ne_two_of_sq_dvd_odd {p n : ℕ} (hn : n % 2 = 1) (hp2 : p ^ 2 ∣ n) : p ≠ 2 := by
  intro hp
  subst hp
  have h4 : 4 ∣ n := by simpa using hp2
  have h2 : 2 ∣ n := dvd_trans (by decide : 2 ∣ 4) h4
  have h0 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  omega

lemma sum_div_add_one_le_real (N : ℕ) (P : Finset ℕ) (k : ℕ) :
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hsplit :
      ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := by
    have :
        (∑ p ∈ P, (N / (k * p ^ 2) + 1 : ℕ)) =
          (∑ p ∈ P, (N / (k * p ^ 2) : ℕ)) + P.card := by
      simp [Finset.sum_add_distrib]
    exact_mod_cast this
  have hterm :
      ∀ p ∈ P, ((N / (k * p ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    intro p hp
    have h := (Nat.cast_div_le (α := ℝ) (m := N) (n := k * p ^ 2))
    simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h
  have hdiv' :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        ∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    exact_mod_cast (Finset.sum_le_sum fun p hp => hterm p hp)
  have hdiv :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
    have :
        (∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2)) =
          (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
      simp [div_eq_mul_inv, mul_sum, mul_comm]
    exact hdiv'.trans (le_of_eq this)
  have h := add_le_add_right hdiv (P.card : ℝ)
  calc
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := hsplit
    _ ≤ (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
        simpa [add_comm, add_left_comm, add_assoc] using h

lemma sieve_set_card_bound
    (N k : ℕ) (P S : Finset ℕ) (pred : ℕ → ℕ → Prop) [∀ p, DecidablePred (pred p)]
    (hsubset :
      S ⊆ P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n)))
    (hper : ∀ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card ≤ N / (k * p ^ 2) + 1) :
    (S.card : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hcard : S.card ≤ (∑ p ∈ P, (N / (k * p ^ 2) + 1)) := by
    calc
      S.card ≤
          ((P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n))).card) :=
        Finset.card_le_card hsubset
      _ ≤ ∑ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ p ∈ P, (N / (k * p ^ 2) + 1) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hper p hp
  have hcard_real :
      (S.card : ℝ) ≤ ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact hcard_real.trans (sum_div_add_one_le_real (N := N) (P := P) (k := k))


end Erdos848Port


/- Quantitative bounds on prime-square errors in cross-residue bipartite graphs. -/


/- Quantitative bounds on prime-square errors in cross-residue bipartite graphs. -/
namespace Erdos848Pure
open Erdos848Gap Finset
private theorem count_by_theta (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ Finset.Icc 1 M := by
    intro q hq
    obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, hle⟩
  have hsmall : small.card ≤ M := by simpa using Finset.card_le_card sub
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


private theorem log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num

private theorem mixed24_count {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<24*p n) : S.card ≤ 876*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 6*p n≤N)
  let large := S.filter (fun n => ¬ 6*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/6 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<576*b := by
    exact link n (smallS hn) 24 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<36*b := by
    exact link n (largeS hn) 6 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 576*b/N
  let W := 2*(N/6)/b
  have pd : P*N ≤ 576*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/6) := Nat.div_mul_le_self _ _
  have u : 6*(N/6)≤N := by omega
  have num : 3*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤576 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤192 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 576*b*W=576*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 192 num)
    have l1 : (P*W)*N ≤ 192*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 768 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 768*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 36*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 36*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤36 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 72 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 36 kd
    have mul : (Q*K)*N ≤ 72*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 108 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 108*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

private theorem mixed24_error {N b : ℕ} (big : 400000000 ≤ N) (bp : 0<b) (bn : b≤N)
    {z : ℕ} (bound : z ≤ 876*(2*2^b.primeFactors.card)) : 330*z ≤ N := by
  have powb := support_fourth b bp
  have h : 330*z ≤ 289080*(2*2^b.primeFactors.card) := by omega
  apply h.trans
  by_contra! bad
  have lo := Nat.pow_lt_pow_left bad (by decide : 4≠0)
  rw [mul_pow] at lo
  have hi := Nat.mul_le_mul_left (289080^4) (powb.trans (Nat.mul_le_mul_left 8944 bn))
  have cutoff := Nat.pow_le_pow_left big 3
  have mc := Nat.mul_le_mul_right N cutoff
  nlinarith only [lo,hi,mc,Nat.zero_le N]
theorem large_mixed_24 {N b : ℕ} (big : 400000000 ≤ N) (bN : b < N)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 24*p ∧ p^2 ∣ b*n+1) :
    330*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 24*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    exact mixed24_error big bp bN.le (mixed24_count bp bN.le S p d eq (fun n hn => (info n hn).1) link
      (fun n hn => (info n hn).2.1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp

theorem small_primes_24 {N : ℕ} (big : 400000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 24*p ≤ N) :
    190 * Q.card ≤ N := by
  let X := N/24
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta X (2^17) 17 (by decide) (log_nat_two_pow 17)
  have trunc : 24*X≤N := by dsimp [X]; omega
  norm_num at weight
  omega

end Erdos848Pure


/- Uniform bounds on nonsquarefree products along either residue class. -/
namespace Erdos848Pure
open Finset Erdos848Port

private theorem prime_sum (N b : ℕ) (P : Finset ℕ) (no5 : P ⊆ no5PrimesUpTo N)
    (no2 : 2 ∣ b → P ⊆ offPrimesUpTo N) :
    (∑ p ∈ P, (1:ℝ)/(25*(p:ℝ)^2)) ≤ (if 2 ∣ b then 163 else 413)/25000 := by
  have h : (∑ p ∈ P,(1:ℚ)/(p:ℚ)^2) ≤ (if 2 ∣ b then 163 else 413)/1000 := by
    by_cases h : 2 ∣ b
    · rw [if_pos h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (no2 h) (fun i _ _ => by positivity)).trans
        (sum_offPrimesUpTo_le N)
    · rw [if_neg h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg no5 (fun i _ _ => by positivity)).trans
        (sum_no5PrimesUpTo_le N)
  have cast := (Rat.cast_le (K:=ℝ)).mpr h
  simp only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,
    apply_ite Rat.cast,Rat.cast_ofNat] at cast
  have f (p : ℕ) : (1:ℝ)/(25*(p:ℝ)^2) = (1/25) * (1/(p:ℝ)^2) := by ring
  simp only [f,←Finset.mul_sum]
  by_cases z : 2 ∣ b <;> simp [z] at cast ⊢ <;> linarith only [cast]

private theorem weighted_bound {N b r C lo hi : ℕ} (largeN : 100 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1)
    (small : ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q,C*p≤N) → lo*Q.card≤N)
    (large : ∀ T : Finset ℕ, (∀ n∈T,n<N ∧ ∃ p : ℕ,p≤N ∧ N<C*p ∧ p^2∣b*n+1) → hi*T.card≤N)
    (lop : 0<lo) (hip : 0<hi) (w : ℝ)
    (limit : ∀ Q : Finset ℕ, Q ⊆ no5PrimesUpTo N → (2∣b → Q ⊆ offPrimesUpTo N) →
      (3∣b → 3∉Q) → ∑ p∈Q,(1:ℝ)/(25*(p:ℝ)^2) ≤ w) :
    (S.card:ℝ) ≤ N*w + (N:ℝ)/lo + (N:ℝ)/hi := by
  classical
  let P := (no5PrimesUpTo N).filter (fun p => ¬p∣b)
  let Q := P.filter (fun p => C*p≤N)
  let R := P.filter (fun p => N<C*p)
  let B (p : ℕ) := (range N).filter (fun n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
  have no5 : P ⊆ no5PrimesUpTo N := Finset.filter_subset .. 
  have no2 (ev : 2 ∣ b) : P ⊆ offPrimesUpTo N := by
    intro p hp
    obtain ⟨mem,div⟩ := Finset.mem_filter.mp hp
    obtain ⟨pm,p5⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨pm,fun h => div (h ▸ ev),p5⟩
  have prime {p : ℕ} (h : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).2
  have bound {p : ℕ} (h : p ∈ P) : p ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).1)
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    obtain ⟨p,hp,p5,pdv⟩ := prime_square_exists_ne5 (bad n hn) (h25 n hn)
    have nN := Finset.mem_range.mp (inRange hn)
    have pred := Nat.mul_le_mul (Nat.le_pred_of_lt bn) (Nat.le_pred_of_lt nN)
    have le := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) ((Nat.add_le_add_right pred 1).trans_lt
      (sq_pred_add_one_lt_sq N largeN)) pdv
    have pnd : ¬p∣b := by
      intro h
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left h n)).mp
        (Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) pdv))
    have mem : p ∈ P := by
      simp [P,no5PrimesUpTo,primesUpTo,hp,Nat.lt_succ_of_le le,p5,pnd]
    have nb : n ∈ B p := Finset.mem_filter.mpr ⟨inRange hn,res n hn,pdv⟩
    by_cases h : C*p ≤ N
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,h⟩,nb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,Nat.lt_of_not_ge h⟩,nb⟩)
  have cards : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (card_le_card cover).trans (card_union_le ..)
  have sub : Q ⊆ P := Finset.filter_subset ..
  have lc := small Q (fun _ h => prime (sub h)) (fun _ h => (mem_filter.mp h).2)
  have hc := large (R.biUnion B) (by
    intro n hn
    obtain ⟨p,hp,nb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨nN,pdv⟩ := Finset.mem_filter.mp nb
    exact ⟨Finset.mem_range.mp nN,p,bound (mem_filter.mp hp).1,(mem_filter.mp hp).2,pdv.2⟩)
  have first := sieve_set_card_bound N 25 Q (Q.biUnion B) (fun p n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
    Subset.rfl (fun p hp => off_count_modEq25_le' N p b r (prime (sub hp)) (mem_filter.mp (no5 (sub hp))).2)
  have est := limit Q (sub.trans no5) (fun he => sub.trans (no2 he)) (fun dv h => (mem_filter.mp (sub h)).2 dv)
  have weight := mul_le_mul_of_nonneg_left est (show 0 ≤ (N:ℝ) by positivity)
  have countR : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast cards
  have lcr : (Q.card:ℝ) ≤ (N:ℝ)/lo := by
    apply (le_div_iff₀ (by exact_mod_cast lop)).mpr
    rw [mul_comm]
    exact_mod_cast lc
  have hcr : ((R.biUnion B).card:ℝ) ≤ (N:ℝ)/hi := by
    apply (le_div_iff₀ (by exact_mod_cast hip)).mpr
    rw [mul_comm]
    exact_mod_cast hc
  linarith only [first,weight,countR,lcr,hcr]

private theorem uniform_bound {N b r C lo hi : ℕ} (largeN : 100 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1)
    (small : ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q,C*p≤N) → lo*Q.card≤N)
    (large : ∀ T : Finset ℕ, (∀ n∈T,n<N ∧ ∃ p : ℕ,p≤N ∧ N<C*p ∧ p^2∣b*n+1) → hi*T.card≤N)
    (lop : 0<lo) (hip : 0<hi) :
    (S.card:ℝ) ≤ N*((if 2 ∣ b then 163 else 413)/25000:ℝ) + (N:ℝ)/lo + (N:ℝ)/hi :=
  weighted_bound largeN bn S inRange res bad h25 small large lop hip _
    (fun Q no5 no2 _ => prime_sum N b Q no5 no2)

theorem bad_bound_400M {N b r : ℕ} (big : 400000000 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1) :
    (S.card:ℝ) ≤ (N:ℝ)*((if 2 ∣ b then 163 else 413)/25000:ℝ) + (N:ℝ)/120 := by
  have h := uniform_bound (by omega : 100≤N) bn S inRange res bad h25
    (small_primes_24 big) (large_mixed_24 big bn) (by decide) (by decide)
  norm_num at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]

end Erdos848Pure


/- Hall's inequality between the two exceptional classes, for endpoints above
400 million. A potential empty rectangle with an even vertex can use the
stronger sieve omitting the square of two. Two odd-only sets together contain
at most one vertex per quotient by 25. -/

namespace Erdos848Pure
open Finset Erdos848Port

private theorem odd_rectangle (k : ℕ) (X Y : Finset ℕ)
    (xs : ∀ n ∈ X, n < 25*k+7 ∧ n%25=18 ∧ ¬2∣n)
    (ys : ∀ n ∈ Y, n < 25*k+7 ∧ n%25=7 ∧ ¬2∣n) :
    X.card+Y.card ≤ k := by
  classical
  have info (x : ℕ) (hx : x ∈ X ∪ Y) : x < 25*k+7 ∧ (x%25=18 ∨ x%25=7) ∧ ¬2∣x := by
    rcases Finset.mem_union.mp hx with h|h
    · obtain ⟨lo,r,o⟩ := xs x h
      exact ⟨lo,Or.inl r,o⟩
    · obtain ⟨lo,r,o⟩ := ys x h
      exact ⟨lo,Or.inr r,o⟩
  have dis : Disjoint X Y := Finset.disjoint_left.mpr (by
    intro x xX xY
    have := (xs x xX).2.1
    have := (ys x xY).2.1
    omega)
  have inj : (X∪Y).card ≤ (range k).card := Finset.card_le_card_of_injOn (fun x => x/25)
    (by intro x h; obtain ⟨lo,r,_⟩ := info x h; apply Finset.mem_range.mpr; change x/25 < k; rcases r with h|h <;> omega)
    (by
      intro x hx y hy eq
      obtain ⟨_,rx,ox⟩ := info x hx
      obtain ⟨_,ry,oy⟩ := info y hy
      change x/25 = y/25 at eq
      rcases rx with h|h <;> rcases ry with h|h <;> omega)
  simpa [card_union_of_disjoint dis] using inj

theorem hall_400M (k : ℕ) (big : 400000000 ≤ 25*k+7) (X : Finset ℕ)
    (xs : X ⊆ (range (25*k+7)).filter (fun n => n%25=18)) :
    X.card ≤ ((Erdos848.A₇ (25*k+7)).filter (fun a => ∃ b∈X, Squarefree (a*b+1))).card := by
  classical
  let N := 25*k+7
  let Γ := (Erdos848.A₇ N).filter (fun a => ∃ b∈X, Squarefree (a*b+1))
  let Y := Erdos848.A₇ N \ Γ
  have xin (x : ℕ) (h : x∈X) : x<N ∧ x%25=18 := by
    have e := Finset.mem_filter.mp (xs h)
    exact ⟨Finset.mem_range.mp e.1,e.2⟩
  have yin (y : ℕ) (h : y∈Y) : y<N ∧ y%25=7 := by
    have e := Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1
    exact ⟨Finset.mem_range.mp e.1,e.2⟩
  have conflict {x y : ℕ} (xh : x∈X) (yh : y∈Y) : ¬Squarefree (y*x+1) := by
    intro sq
    exact (Finset.mem_sdiff.mp yh).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp yh).1,x,xh,sq⟩)
  have base : (Erdos848.A₇ N).card = k := by change (Erdos848Port.A₇ N).card = k; rw [A₇_card]; dsimp [N]; omega
  have parts : Y.card + Γ.card = k := by
    rw [←base]
    exact Finset.card_sdiff_add_card_eq_card (Finset.filter_subset ..)
  change X.card ≤ Γ.card
  by_cases xe : X.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp xe]
    simp
  by_cases ye : Y.Nonempty
  swap
  · have empty := Finset.not_nonempty_iff_eq_empty.mp ye
    rw [empty,card_empty,zero_add] at parts
    rw [parts]
    have bound : X.card ≤ (A₁₈ N).card := Finset.card_le_card xs
    rw [A₁₈_card] at bound
    dsimp [N] at bound
    omega
  have fromX (x : ℕ) (xh : x∈X) : (Y.card:ℝ) ≤
      (N:ℝ)*((if 2∣x then 163 else 413)/25000:ℝ)+(N:ℝ)/120 := by
    apply bad_bound_400M big (xin x xh).1 Y (r:=7)
      (fun y h => Finset.mem_range.mpr (yin y h).1) (fun y h => (yin y h).2)
    · intro y yh
      simpa [Nat.mul_comm x y] using conflict xh yh
    · intro y yh
      exact cross_residue_18_7_not_div_25 x y (xin x xh).2 (yin y yh).2
  have fromY (y : ℕ) (yh : y∈Y) : (X.card:ℝ) ≤
      (N:ℝ)*((if 2∣y then 163 else 413)/25000:ℝ)+(N:ℝ)/120 := by
    apply bad_bound_400M big (yin y yh).1 X (r:=18)
      (fun x h => Finset.mem_range.mpr (xin x h).1) (fun x h => (xin x h).2)
    · intro x xh
      exact conflict xh yh
    · intro x xh
      exact cross_residue_7_18_not_div_25 y x (yin y yh).2 (xin x xh).2
  have count (x y : ℕ) (xh : x∈X) (yh : y∈Y) (even : 2∣x ∨ 2∣y) : X.card+Y.card ≤ k := by
    have a := fromX x xh
    have b := fromY y yh
    have kbig : (100:ℝ) ≤ k := by exact_mod_cast (show 100 ≤ k by omega)
    dsimp [N] at a b
    push_cast at a b
    exact_mod_cast (show (X.card:ℝ)+(Y.card:ℝ) ≤ k by
      by_cases xE : 2∣x <;> by_cases yE : 2∣y <;> simp [xE,yE] at a b even <;> linarith)
  by_cases ex : ∃ x∈X, 2∣x
  · obtain ⟨x,hx,h⟩ := ex
    obtain ⟨y,hy⟩ := ye
    have := count x y hx hy (Or.inl h)
    omega
  by_cases ey : ∃ y∈Y, 2∣y
  · obtain ⟨y,hy,h⟩ := ey
    obtain ⟨x,hx⟩ := xe
    have := count x y hx hy (Or.inr h)
    omega
  have bound := odd_rectangle k X Y (fun x h => ⟨(xin x h).1,(xin x h).2,fun e => ex ⟨x,h,e⟩⟩)
    (fun y h => ⟨(yin y h).1,(yin y h).2,fun e => ey ⟨y,h,e⟩⟩)
  omega

end Erdos848Pure

/- Uniform prime-square errors above 50 billion. Below 200 billion the
number of distinct prime factors is bounded by the first two relevant
primorials, and above this cutoff the fourth-moment bound applies. -/
namespace Erdos848Lower
open Erdos848Gap Finset
set_option maxHeartbeats 2000000 in
theorem support10 (b : ℕ) (bp : 0<b) (size : b≤200000000000) :
    2*2^b.primeFactors.card ≤ 2048 := by
  classical
  let s : Finset ℕ := {2,3,5,7,11,13,17,19,23,29}
  let weight (p : ℕ) : ℚ := if p∈s then 31 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 ∨ p=29 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (31:ℚ) ≤ weight p * p^(b.factorization p) := by
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 31 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 31≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (31:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 126688 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 126688 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (31:ℚ)^b.primeFactors.card ≤ 126688*b := by
    calc _ = ∏ _∈b.primeFactors,(31:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 31^b.primeFactors.card ≤ 126688*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 10 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<31) (show 11≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
private theorem count_by_theta (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ Finset.Icc 1 M := by
    intro q hq
    obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, hle⟩
  have hsmall : small.card ≤ M := by simpa using Finset.card_le_card sub
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


private theorem log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num

private theorem mixed112_count {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<112*p n) : S.card ≤ 14924*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 14*p n≤N)
  let large := S.filter (fun n => ¬ 14*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/14 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<12544*b := by
    exact link n (smallS hn) 112 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<196*b := by
    exact link n (largeS hn) 14 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 12544*b/N
  let W := 2*(N/14)/b
  have pd : P*N ≤ 12544*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/14) := Nat.div_mul_le_self _ _
  have u : 14*(N/14)≤N := by omega
  have num : 7*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤12544 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤1792 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 12544*b*W=12544*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 1792 num)
    have l1 : (P*W)*N ≤ 1792*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 14336 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 14336*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 196*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 196*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤196 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 392 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 196 kd
    have mul : (Q*K)*N ≤ 392*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 588 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 588*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

private theorem old_error {N b : ℕ} (big : 200000000000 ≤ N) (bp : 0<b) (bn : b≤N)
    {z : ℕ} (bound : z ≤ 14924*(2*2^b.primeFactors.card)) : 1635*z ≤ N := by
  have powb := support_fourth b bp
  have h : 1635*z ≤ 24400740*(2*2^b.primeFactors.card) := by omega
  apply h.trans
  by_contra! bad
  have lo := Nat.pow_lt_pow_left bad (by decide : 4≠0)
  rw [mul_pow] at lo
  have hi := Nat.mul_le_mul_left (24400740^4) (powb.trans (Nat.mul_le_mul_left 8944 bn))
  have cutoff := Nat.pow_le_pow_left big 3
  have mc := Nat.mul_le_mul_right N cutoff
  nlinarith only [lo,hi,mc,Nat.zero_le N]
private theorem mixed112_error {N b : ℕ} (big : 50000000000 ≤ N) (bp : 0<b) (bn : b≤N)
    {z : ℕ} (bound : z ≤ 14924*(2*2^b.primeFactors.card)) : 1635*z ≤ N := by
  by_cases high : 200000000000 ≤ N
  · exact old_error high bp bn bound
  · have h := support10 b bp (by omega)
    omega
theorem large_mixed_112 {N b : ℕ} (big : 50000000000 ≤ N) (bN : b < N)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 112*p ∧ p^2 ∣ b*n+1) :
    1635*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 112*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    exact mixed112_error big bp bN.le (mixed112_count bp bN.le S p d eq (fun n hn => (info n hn).1) link
      (fun n hn => (info n hn).2.1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp

theorem small_primes_112 {N : ℕ} (big : 50000000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 112*p ≤ N) :
    1120 * Q.card ≤ N := by
  let X := N/112
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta X (2^21) 21 (by decide) (log_nat_two_pow 21)
  have trunc : 112*X≤N := by dsimp [X]; omega
  norm_num at weight
  omega

theorem small_primes_360 {N : ℕ} (big : 50000000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 360*p ≤ N) :
    3250 * Q.card ≤ N := by
  let X := N/360
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta X (2^19) 19 (by decide) (log_nat_two_pow 19)
  have trunc : 360*X≤N := by dsimp [X]; omega
  norm_num at weight
  omega

end Erdos848Lower

namespace Deldor14.Erdos848Tenth
open Finset
def side (N r : ℕ) := (range N).filter (fun x=>x%25=r)
def hood (N : ℕ) (X : Finset ℕ) := (side N 7).filter (fun a=>∃b∈X,Squarefree (a*b+1))
theorem side_card (k r : ℕ) (hr : r=7 ∨ r=18) : (side (25*k+7) r).card=k := by
  rw [side,Erdos848Port.card_range_filter_mod25_eq _ (by omega)]
  rcases hr with rfl|rfl <;> omega
end Deldor14.Erdos848Tenth

/- Complementary-divisor errors in the interval from 10 to 50 billion. -/
namespace Erdos848Ten
open Erdos848Gap Finset
set_option maxHeartbeats 2000000 in
theorem without2 (b : ℕ) (bp : 0<b) (size : b≤50000000000) (omitted : ¬2∣b) :
    2*2^b.primeFactors.card ≤ 1024 := by
  classical
  let s : Finset ℕ := {3,5,7,11,13,17,19,23,29}
  let weight (p : ℕ) : ℚ := if p∈s then 31 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 ∨ p=29 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (31:ℚ) ≤ weight p * p^(b.factorization p) := by
    have px : p ≠ 2 := fun e => omitted (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 31 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 31≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (31:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 8174 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 8174 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (31:ℚ)^b.primeFactors.card ≤ 8174*b := by
    calc _ = ∏ _∈b.primeFactors,(31:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 31^b.primeFactors.card ≤ 8174*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 9 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<31) (show 10≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
set_option maxHeartbeats 2000000 in
theorem without3 (b : ℕ) (bp : 0<b) (size : b≤50000000000) (omitted : ¬3∣b) :
    2*2^b.primeFactors.card ≤ 1024 := by
  classical
  let s : Finset ℕ := {2,5,7,11,13,17,19,23,29}
  let weight (p : ℕ) : ℚ := if p∈s then 31 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=2 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 ∨ p=29 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (31:ℚ) ≤ weight p * p^(b.factorization p) := by
    have px : p ≠ 3 := fun e => omitted (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 31 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 31≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (31:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 12261 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 12261 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (31:ℚ)^b.primeFactors.card ≤ 12261*b := by
    calc _ = ∏ _∈b.primeFactors,(31:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 31^b.primeFactors.card ≤ 12261*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 9 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<31) (show 10≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
private theorem count_by_theta_refined (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M.primeCounting+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ M.primesLE := by
    intro q hq
    obtain ⟨hp,hle⟩ := Finset.mem_filter.mp hq
    exact Nat.mem_primesLE.mpr ⟨hle,(Nat.mem_primesLE.mp hp).2⟩
  have hsmall := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at hsmall
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M.primeCounting := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M.primeCounting : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


private theorem log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num


set_option maxRecDepth 1500 in
private theorem count_by_theta (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ Finset.Icc 1 M := by
    intro q hq
    obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, hle⟩
  have hsmall : small.card ≤ M := by simpa using Finset.card_le_card sub
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


theorem mixed72_count {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<72*p n) : S.card ≤ 6480*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 12*p n≤N)
  let large := S.filter (fun n => ¬ 12*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/12 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<5184*b := by
    exact link n (smallS hn) 72 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<144*b := by
    exact link n (largeS hn) 12 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 5184*b/N
  let W := 2*(N/12)/b
  have pd : P*N ≤ 5184*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/12) := Nat.div_mul_le_self _ _
  have u : 12*(N/12)≤N := by omega
  have num : 6*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤5184 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤864 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 5184*b*W=5184*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 864 num)
    have l1 : (P*W)*N ≤ 864*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 6048 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 6048*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 144*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 144*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤144 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 288 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 144 kd
    have mul : (Q*K)*N ≤ 288*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 432 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 432*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

private theorem mixed72_error {N b : ℕ} (big : 10000000000≤N) (upper : N≤50000000000) (bp : 0<b) (bn : b≤N)
    {z : ℕ} (bound : z≤6480*(2*2^b.primeFactors.card)) : (if 6∣b then 753 else 1506)*z≤N := by
  split_ifs with six
  · have h := Erdos848Lower.support10 b bp (by omega)
    omega
  · by_cases even : 2∣b
    · have n3 : ¬3∣b := fun d=>six ((by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd even d)
      have h := without3 b bp (bn.trans upper) n3
      omega
    · have h := without2 b bp (bn.trans upper) even
      omega
theorem large_mixed_72 {N b : ℕ} (big : 10000000000 ≤ N) (upper : N≤50000000000) (bN : b < N)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 72*p ∧ p^2 ∣ b*n+1) :
    (if 6∣b then 753 else 1506)*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 72*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    exact mixed72_error big upper bp bN.le (mixed72_count bp bN.le S p d eq (fun n hn => (info n hn).1) link
      (fun n hn => (info n hn).2.1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp

theorem small_primes_72 {N : ℕ} (big : 10000000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 72*p ≤ N) :
    746 * Q.card ≤ N := by
  let X := N/72
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta_refined X (2^22) 22 (by decide) (log_nat_two_pow 22)
  have inner := count_by_theta (2^22) (2^11) 11 (by decide) (log_nat_two_pow 11)
  have trunc : 72*X≤N := by dsimp [X]; omega
  norm_num only [Nat.reducePow] at weight inner
  omega

theorem small_primes_360 {N : ℕ} (big : 10000000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 360*p ≤ N) :
    3100 * Q.card ≤ N := by
  let X := N/360
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta_refined X (2^20) 20 (by decide) (log_nat_two_pow 20)
  have inner := count_by_theta (2^20) (2^11) 11 (by decide) (log_nat_two_pow 11)
  have trunc : 360*X≤N := by dsimp [X]; omega
  norm_num only [Nat.reducePow] at weight inner
  omega

theorem large_mixed_72_all {N b : ℕ} (big : 10000000000≤N) (bn : b<N)
    (S : Finset ℕ) (found : ∀n∈S,n<N ∧ ∃p : ℕ,p≤N ∧ N<72*p ∧ p^2∣b*n+1) :
    (if 6∣b then 753 else 1506)*S.card≤N := by
  by_cases low : N≤50000000000
  · exact large_mixed_72 big low bn S found
  · have h := Erdos848Lower.large_mixed_112 (by omega : 50000000000≤N) bn S (by
      intro n hn
      obtain ⟨nr,p,pn,cut,div⟩ := found n hn
      exact ⟨nr,p,pn,by omega,div⟩)
    split_ifs <;> omega
end Erdos848Ten

/- Arithmetic pieces used for the three parts of a mixed admissible set. -/
namespace Deldor14.Erdos848Tenth
open Finset Erdos848

def slice (A : Finset ℕ) (r : ℕ) := A.filter (fun x=>x%25=r)
def outside (A : Finset ℕ) := A.filter (fun x=>x%25≠7 ∧ x%25≠18)

theorem total_parts (A : Finset ℕ) : (A.card:ℝ) ≤ ((slice A 7).card:ℝ)+((slice A 18).card:ℝ)+((outside A).card:ℝ) := by
  have sub : A ⊆ (slice A 7 ∪ slice A 18) ∪ outside A := by
    intro x hx
    by_cases h7 : x%25=7
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx,h7⟩))
    by_cases h18 : x%25=18
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hx,h18⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨hx,h7,h18⟩)
  have c := (card_le_card sub).trans (card_union_le ..)
  have d := card_union_le (slice A 7) (slice A 18)
  exact_mod_cast (by omega : A.card≤(slice A 7).card+(slice A 18).card+(outside A).card)

theorem between_not25 {b x r : ℕ} (base : r=7 ∨ r=18) (different : b%25≠r) (xr : x%25=r) :
    ¬25∣b*x+1 := by
  intro div
  have mod := Nat.mod_eq_zero_of_dvd div
  rw [Nat.add_mod,Nat.mul_mod,xr] at mod
  rcases base with rfl|rfl <;> omega

end Deldor14.Erdos848Tenth

/- Counts for a congruence conditioned on an independent modulus. -/
namespace Deldor14.Erdos848Phase
open Finset Erdos848Port

def prog (N m r : ℕ) := (range N).filter (fun x=>x ≡ r [MOD m])
theorem lower_prog (N m r : ℕ) (pos : 0 < m) : N/m ≤ (prog N m r).card := by
  let f (x : ℕ) := m*x+r%m
  have inc (x) (hx : x∈range (N/m)) : f x∈prog N m r := by
    have small := Nat.mod_lt r pos
    have le := Nat.mul_le_mul_left m (Nat.succ_le_of_lt (mem_range.mp hx))
    have cap := Nat.mul_div_le N m
    refine mem_filter.mpr ⟨mem_range.mpr ?_,?_⟩
    · dsimp [f]
      rw [Nat.mul_succ] at le
      omega
    · dsimp [Nat.ModEq,f]; simp
  have inj : Function.Injective f := by
    intro a b eq
    apply Nat.eq_of_mul_eq_mul_left pos
    exact Nat.add_right_cancel eq
  simpa using (card_le_card_of_injOn f inc inj.injOn)

theorem prog_bounds (N m r : ℕ) (pos : 0 < m) :
    (N:ℝ)/(m:ℝ)-1 ≤ ((prog N m r).card:ℝ) ∧ ((prog N m r).card:ℝ) ≤ (N:ℝ)/m+1 := by
  have lo := lower_prog N m r pos
  have hi := card_filter_mod_eq_le N m r
  change (prog N m r).card ≤ N/m+1 at hi
  have l : (N/m:ℕ) ≤ (prog N m r).card := lo
  have res := Nat.mod_lt N pos
  have eq := Nat.mod_add_div N m
  have imp : N < m*((prog N m r).card+1) := by
    have h := Nat.mul_le_mul_left m l
    rw [Nat.mul_succ]
    omega
  have rr : (N:ℝ) < (m:ℝ)*(((prog N m r).card:ℝ)+1) := by exact_mod_cast imp
  have quot := (div_lt_iff₀ (by exact_mod_cast pos : (0:ℝ) < m)).mpr (by linarith only [rr] : (N:ℝ) < (((prog N m r).card:ℝ)+1)*m)
  have hR : ((prog N m r).card:ℝ) ≤ ((N/m:ℕ):ℝ)+1 := by exact_mod_cast hi
  have nc := Nat.cast_div_le (α:=ℝ) (m:=N) (n:=m)
  exact ⟨by linarith only [quot],by linarith only [hR,nc]⟩

theorem crt_prog {N m k r s : ℕ} (co : Nat.Coprime m k) :
    prog N m r ∩ prog N k s = prog N (m*k) (Nat.chineseRemainder co r s) := by
  ext x
  simp only [prog,mem_inter,mem_filter,mem_range]
  constructor
  · rintro ⟨⟨xn,a⟩,_,b⟩
    exact ⟨xn,Nat.chineseRemainder_modEq_unique co a b⟩
  · rintro ⟨xn,t⟩
    have a := (Nat.chineseRemainder co r s).prop
    exact ⟨⟨xn,(t.of_dvd (dvd_mul_right ..)).trans a.1⟩,xn,(t.of_dvd (dvd_mul_left ..)).trans a.2⟩

theorem crt_bounds {N m k r s : ℕ} (co : Nat.Coprime m k) (mp : 0 < m) (kp : 0 < k) :
    (N:ℝ)/(m*k)-1 ≤ ((prog N m r ∩ prog N k s).card:ℝ) ∧
    ((prog N m r ∩ prog N k s).card:ℝ) ≤ (N:ℝ)/(m*k)+1 := by
  rw [crt_prog co]
  simpa only [Nat.cast_mul] using prog_bounds N (m*k) (Nat.chineseRemainder co r s) (Nat.mul_pos mp kp)

end Deldor14.Erdos848Phase

/- Discrepancy for a single odd class modulo four outside the two exceptional classes. -/
namespace Deldor14.Erdos848Phase
open Finset Erdos848Port
theorem odd_phase {N p u s : ℕ} (pp : p.Prime) (big : 13 ≤ p) :
    let S := prog N (p^2) u
    ((S.filter (fun x => x ≡ s [MOD 4] ∧ x%25≠7 ∧ x%25≠18)).card:ℝ) ≤
        (23/100:ℝ)*((N:ℝ)/(p:ℝ)^2)+3 := by
  classical
  let q:=p^2
  let S:=prog N q u
  let U := S ∩ prog N 4 s
  let A := U ∩ prog N 25 7
  let B := U ∩ prog N 25 18
  let G := S.filter (fun x => x ≡ s [MOD 4] ∧ x%25≠7 ∧ x%25≠18)
  have pos : 0<q := pow_pos pp.pos _
  have cp4 : q.Coprime 4 := ((pp.coprime_iff_not_dvd.mpr (fun dv=>(not_le_of_gt (by omega : 4<p)) (Nat.le_of_dvd (by decide : 0<4) dv))).symm.pow_right 2).symm
  have cp25 : q.Coprime 25 := (coprime_25_pow_two_of_prime_ne5 p pp (by omega)).symm
  have part (r) : ((N:ℝ)/(q:ℝ))/100-1 ≤ ((U∩prog N 25 r).card:ℝ) := by
    change _ ≤ (((S∩prog N 4 s)∩prog N 25 r).card:ℝ)
    rw [inter_assoc,crt_prog (by decide : Nat.Coprime 4 25)]
    have z := (crt_bounds (N:=N) (r:=u) (s:=Nat.chineseRemainder (by decide : Nat.Coprime 4 25) s r)
      (cp4.mul_right cp25) pos (by decide)).1
    simpa only [Nat.reduceMul,Nat.cast_ofNat,div_div] using z
  have up := (crt_bounds (N:=N) (r:=u) (s:=s) cp4 pos (by decide)).2
  have h7 := part 7
  have h18 := part 18
  have ab : Disjoint A B := by
    apply disjoint_left.mpr
    intro x a b
    have z := (mem_filter.mp (mem_inter.mp a).2).2
    have t := (mem_filter.mp (mem_inter.mp b).2).2
    change x%25=7 at z; change x%25=18 at t; omega
  have split : G∪(A∪B)=U := by
    ext x
    simp only [G,A,B,U,prog,mem_union,mem_inter,mem_filter,mem_range]
    change ((x∈S ∧ x ≡ s [MOD 4] ∧ x%25≠7 ∧ x%25≠18) ∨
      ((x∈S ∧ x<N ∧ x≡s [MOD 4]) ∧ x<N ∧ x%25=7) ∨
      ((x∈S ∧ x<N ∧ x≡s [MOD 4]) ∧ x<N ∧ x%25=18)) ↔ (x∈S ∧ x<N ∧ x≡s [MOD 4])
    have xn : x∈S → x<N := fun h=>mem_range.mp (mem_filter.mp h).1
    tauto
  have dis : Disjoint G (A∪B) := by
    apply disjoint_left.mpr
    intro x hx h
    have g := (mem_filter.mp hx).2
    rcases mem_union.mp h with h|h
    · exact g.2.1 (mem_filter.mp (mem_inter.mp h).2).2
    · exact g.2.2 (mem_filter.mp (mem_inter.mp h).2).2
  have eq := congrArg Finset.card split
  rw [card_union_of_disjoint dis,card_union_of_disjoint ab] at eq
  have cr : (G.card:ℝ)+((A.card:ℝ)+(B.card:ℝ))=(U.card:ℝ) := by exact_mod_cast eq
  change (G.card:ℝ) ≤ (23/100)*((N:ℝ)/(p:ℝ)^2)+3
  change (U.card:ℝ)≤(N:ℝ)/((q:ℝ)*(4:ℕ))+1 at up
  change (N:ℝ)/(q:ℝ)/100-1≤(A.card:ℝ) at h7
  change (N:ℝ)/(q:ℝ)/100-1≤(B.card:ℝ) at h18
  have pq : (q:ℝ)=(p:ℝ)^2 := by simp [q]
  rw [←pq]
  norm_num only [Nat.cast_ofNat] at up
  rw [←div_div] at up
  linarith only [cr,h7,h18,up]
end Deldor14.Erdos848Phase

/- Refined errors when the distinguished pivot is odd. -/
namespace Erdos848Odd400
open Finset Erdos848Gap
set_option maxHeartbeats 2000000 in
theorem odd_not3_small (b : ℕ) (bp : 0<b) (size : b≤1000000000) (missing2 : ¬2∣b) (missing3 : ¬3∣b)  :
    2*2^b.primeFactors.card ≤ 256 := by
  classical
  let s : Finset ℕ := {5,7,11,13,17,19,23}
  let weight (p : ℕ) : ℚ := if p∈s then 29 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (29:ℚ) ≤ weight p * p^(b.factorization p) := by
    have miss2 : p ≠ 2 := fun e=>missing2 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have miss3 : p ≠ 3 := fun e=>missing3 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 29 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 29≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (29:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 464 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 464 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (29:ℚ)^b.primeFactors.card ≤ 464*b := by
    calc _ = ∏ _∈b.primeFactors,(29:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 29^b.primeFactors.card ≤ 464*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 7 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<29) (show 8≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
set_option maxHeartbeats 2000000 in
theorem odd_not3_wide (b : ℕ) (bp : 0<b) (size : b≤10000000000) (missing2 : ¬2∣b) (missing3 : ¬3∣b)  :
    2*2^b.primeFactors.card ≤ 512 := by
  classical
  let s : Finset ℕ := {5,7,11,13,17,19,23,29}
  let weight (p : ℕ) : ℚ := if p∈s then 31 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 ∨ p=29 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (31:ℚ) ≤ weight p * p^(b.factorization p) := by
    have miss2 : p ≠ 2 := fun e=>missing2 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have miss3 : p ≠ 3 := fun e=>missing3 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 31 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 31≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (31:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 791 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 791 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (31:ℚ)^b.primeFactors.card ≤ 791*b := by
    calc _ = ∏ _∈b.primeFactors,(31:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 31^b.primeFactors.card ≤ 791*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 8 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<31) (show 9≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
set_option maxHeartbeats 2000000 in
theorem odd_with3 (b : ℕ) (bp : 0<b) (size : b≤3000000000) (missing2 : ¬2∣b)  :
    2*2^b.primeFactors.card ≤ 512 := by
  classical
  let s : Finset ℕ := {3,5,7,11,13,17,19,23}
  let weight (p : ℕ) : ℚ := if p∈s then 29 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (29:ℚ) ≤ weight p * p^(b.factorization p) := by
    have miss2 : p ≠ 2 := fun e=>missing2 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 29 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 29≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (29:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 4485 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 4485 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (29:ℚ)^b.primeFactors.card ≤ 4485*b := by
    calc _ = ∏ _∈b.primeFactors,(29:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 29^b.primeFactors.card ≤ 4485*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 8 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<29) (show 9≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
private theorem count_by_theta_refined (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M.primeCounting+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ M.primesLE := by
    intro q hq
    obtain ⟨hp,hle⟩ := Finset.mem_filter.mp hq
    exact Nat.mem_primesLE.mpr ⟨hle,(Nat.mem_primesLE.mp hp).2⟩
  have hsmall := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at hsmall
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M.primeCounting := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M.primeCounting : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


private theorem log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num


set_option maxRecDepth 1500 in
private theorem count_by_theta (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ Finset.Icc 1 M := by
    intro q hq
    obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, hle⟩
  have hsmall : small.card ≤ M := by simpa using Finset.card_le_card sub
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


theorem mixed36_count {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<36*p n) : S.card ≤ 1812*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 8*p n≤N)
  let large := S.filter (fun n => ¬ 8*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/8 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<1296*b := by
    exact link n (smallS hn) 36 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<64*b := by
    exact link n (largeS hn) 8 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 1296*b/N
  let W := 2*(N/8)/b
  have pd : P*N ≤ 1296*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/8) := Nat.div_mul_le_self _ _
  have u : 8*(N/8)≤N := by omega
  have num : 4*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤1296 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤324 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 1296*b*W=1296*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 324 num)
    have l1 : (P*W)*N ≤ 324*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 1620 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 1620*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 64*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 64*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤64 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 128 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 64 kd
    have mul : (Q*K)*N ≤ 128*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 192 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 192*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

private theorem mixed36_error {N b : ℕ} (big : 400000000≤N) (upper : N≤10000000000) (bp : 0<b) (bn : b≤N) (odd : ¬2∣b)
    {z : ℕ} (bound : z≤1812*(2*2^b.primeFactors.card)) : (if 3∣b then 431 else 862)*z≤N := by
  by_cases tri : 3∣b
  · rw [if_pos tri]
    by_cases small : N≤3000000000
    · have h := odd_with3 b bp (bn.trans small) odd
      omega
    · have h := Erdos848Ten.without2 b bp ((bn.trans upper).trans (by decide)) odd
      omega
  · rw [if_neg tri]
    by_cases small : N≤1000000000
    · have h := odd_not3_small b bp (bn.trans small) odd tri
      omega
    · have h := odd_not3_wide b bp (bn.trans upper) odd tri
      omega
theorem large_mixed_36 {N b : ℕ} (big : 400000000 ≤ N) (upper : N≤10000000000) (bN : b < N) (odd : ¬2∣b)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 36*p ∧ p^2 ∣ b*n+1) :
    (if 3∣b then 431 else 862)*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 36*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    exact mixed36_error big upper bp bN.le odd (mixed36_count bp bN.le S p d eq (fun n hn => (info n hn).1) link
      (fun n hn => (info n hn).2.1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp

theorem small_primes_36 {N : ℕ} (big : 400000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 36*p ≤ N) :
    315 * Q.card ≤ N := by
  let X := N/36
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta_refined X (2^19) 19 (by decide) (log_nat_two_pow 19)
  have inner := count_by_theta (2^19) (2^11) 11 (by decide) (log_nat_two_pow 11)
  have trunc : 36*X≤N := by dsimp [X]; omega
  norm_num only [Nat.reducePow] at weight inner
  omega

theorem small_primes_128 {N : ℕ} (big : 400000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 128*p ≤ N) :
    1014 * Q.card ≤ N := by
  let X := N/128
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta_refined X (2^17) 17 (by decide) (log_nat_two_pow 17)
  have inner := count_by_theta (2^17) (2^11) 11 (by decide) (log_nat_two_pow 11)
  have trunc : 128*X≤N := by dsimp [X]; omega
  norm_num only [Nat.reducePow] at weight inner
  omega

theorem large_odd_36 {N b : ℕ} (big : 400000000≤N) (bn : b<N) (odd : ¬2∣b)
    (S : Finset ℕ) (found : ∀n∈S,n<N ∧ ∃p : ℕ,p≤N ∧ N<36*p ∧ p^2∣b*n+1) :
    (if 3∣b then 431 else 862)*S.card≤N := by
  by_cases low : N≤10000000000
  · exact large_mixed_36 big low bn odd S found
  · have h := Erdos848Ten.large_mixed_72_all (by omega : 10000000000≤N) bn S (by
      intro n hn
      obtain ⟨nr,p,pn,cut,div⟩ := found n hn
      exact ⟨nr,p,pn,by omega,div⟩)
    have ns : ¬6∣b := fun dv=>odd ((by decide : 2∣6).trans dv)
    rw [if_neg ns] at h
    split_ifs <;> omega
end Erdos848Odd400

/- Mixed-class degree bound after specifying the residue modulo four. -/
namespace Erdos848Odd400
open Finset Erdos848Port

theorem bad_ten_100 {N b r s : ℕ} (big : 400000000≤N) (bn : b < N) (odd : ¬2∣b)
    (S : Finset ℕ) (inRange : S ⊆ range N)
    (res : ∀ n∈S, n ≡ r [MOD 25]) (res4 : ∀ n∈S, n ≡ s [MOD 4])
    (bad : ∀ n∈S, ¬Squarefree (b*n+1))
    (h4 : ∀ n∈S, ¬4∣b*n+1) (h25 : ∀ n∈S, ¬25∣b*n+1) :
    (S.card:ℝ) ≤ (603/100000)*(N:ℝ) := by
  classical
  let P := (offPrimesUpTo N).filter (fun p=>¬p∣b)
  let Q := P.filter (fun p => 36*p≤N)
  let R := P.filter (fun p => N<36*p)
  let B (p : ℕ) := (range N).filter (fun n => n ≡ r [MOD 25] ∧ n ≡ s [MOD 4] ∧ p^2∣b*n+1)
  have prime {p : ℕ} (h : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).2
  have bound {p : ℕ} (h : p ∈ P) : p ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).1)
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    obtain ⟨p,hp,p5,pdv⟩ := prime_square_exists_ne5 (bad n hn) (h25 n hn)
    have nN := Finset.mem_range.mp (inRange hn)
    have pred := Nat.mul_le_mul (Nat.le_pred_of_lt bn) (Nat.le_pred_of_lt nN)
    have le := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) ((Nat.add_le_add_right pred 1).trans_lt
      (sq_pred_add_one_lt_sq N (by omega))) pdv
    have p2 : p ≠ 2 := fun e => h4 n hn (by simpa [e] using pdv)
    have pnd : ¬p∣b := by
      intro h
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left h n)).mp (Nat.dvd_of_pow_dvd (by decide : 1≤2) pdv))
    have mem : p ∈ P := by simp [P,offPrimesUpTo,primesUpTo,hp,Nat.lt_succ_of_le le,p5,p2,pnd]
    have nb : n ∈ B p := Finset.mem_filter.mpr ⟨inRange hn,res n hn,res4 n hn,pdv⟩
    by_cases h : 36*p ≤ N
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,h⟩,nb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,Nat.lt_of_not_ge h⟩,nb⟩)
  have cards : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (card_le_card cover).trans (card_union_le ..)
  have sub : Q ⊆ P := Finset.filter_subset ..
  have lc := small_primes_36 big Q (fun _ h => prime (sub h)) (fun _ h => (mem_filter.mp h).2)
  have hc := large_odd_36 big bn odd (R.biUnion B) (by
    intro n hn
    obtain ⟨p,hp,nb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨nN,pdv⟩ := Finset.mem_filter.mp nb
    exact ⟨Finset.mem_range.mp nN,p,bound (mem_filter.mp hp).1,(mem_filter.mp hp).2,pdv.2.2⟩)
  have first := sieve_set_card_bound N 100 Q (Q.biUnion B) (fun p n => n ≡ r [MOD 25] ∧ n ≡ s [MOD 4] ∧ p^2∣b*n+1)
    Subset.rfl (fun p hp => off_count_modEq100_le' N p b r s (prime (sub hp)) (mem_filter.mp (mem_filter.mp (sub hp)).1).2.1 (mem_filter.mp (mem_filter.mp (sub hp)).1).2.2)
  have off : Q ⊆ offPrimesUpTo N := sub.trans (filter_subset ..)
  have est : (∑ p∈Q,(1:ℝ)/(100*(p:ℝ)^2)) ≤ 163/100000 - (if 3∣b then 1/900 else 0) := by
    have general (G : Finset ℕ) (inc : G ⊆ offPrimesUpTo N) : (∑p∈G,(1:ℝ)/(100*(p:ℝ)^2)) ≤ 163/100000 := by
      have sumRat : (∑ p∈G,(1:ℚ)/(p:ℚ)^2) ≤ 163/1000 :=
        (Finset.sum_le_sum_of_subset_of_nonneg inc (fun p _ _ => by positivity)).trans (sum_offPrimesUpTo_le N)
      have cast := (Rat.cast_le (K:=ℝ)).mpr sumRat
      simp only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] at cast
      have f (p : ℕ) : (1:ℝ)/(100*(p:ℝ)^2) = (1/100)*(1/(p:ℝ)^2) := by ring
      simp only [f,←Finset.mul_sum]
      linarith only [cast]
    by_cases tri : 3∣b
    · have missing : 3∉Q := fun h=>(mem_filter.mp (sub h)).2 tri
      have h3 : 3∈primesUpTo N := by simp [primesUpTo,Nat.prime_three,show 3<N+1 by omega]
      have ins := general (insert 3 Q) (insert_subset (mem_filter.mpr ⟨h3,by decide⟩) off)
      rw [sum_insert missing] at ins
      rw [if_pos tri]
      norm_num only [Nat.cast_ofNat] at ins
      linarith only [ins]
    · rw [if_neg tri,sub_zero]
      exact general _ off
  have weight := mul_le_mul_of_nonneg_left est (show 0 ≤ (N:ℝ) by positivity)
  have countR : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast cards
  have lcr : (Q.card:ℝ) ≤ (N:ℝ)/315 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    rw [mul_comm]
    exact_mod_cast lc
  by_cases tri : 3∣b
  · rw [if_pos tri] at hc weight
    have hcr : 431*((R.biUnion B).card:ℝ)≤(N:ℝ) := by exact_mod_cast hc
    linarith only [first,weight,countR,lcr,hcr,Nat.cast_nonneg (α:=ℝ) N]
  · rw [if_neg tri] at hc weight
    have hcr : 862*((R.biUnion B).card:ℝ)≤(N:ℝ) := by exact_mod_cast hc
    linarith only [first,weight,countR,lcr,hcr,Nat.cast_nonneg (α:=ℝ) N]
end Erdos848Odd400


/- Diagonal estimates for the all-odd case, including a single residue modulo four. -/
namespace Erdos848Odd400
open Erdos848Gap Finset
private theorem count_keys (S : Finset ℕ) (key : ℕ → ℕ × ℕ) (cols rows : ℕ)
    (bound : ∀ n∈S, (key n).1 < cols ∧ (key n).2 < rows) (injective : Set.InjOn key S) :
    S.card ≤ cols*rows := by
  let labels := (Finset.range cols) ×ˢ (Finset.range rows)
  have maps : (S : Set ℕ).MapsTo key labels := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (bound n hn).1,Finset.mem_range.mpr (bound n hn).2⟩
  simpa [labels] using Finset.card_le_card_of_injOn key maps injective

theorem large_diagonal_128 {N : ℕ} (big : 400000000 ≤ N) (S : Finset ℕ)
    (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 128*p ∧ p^2 ∣ n^2+1) :
    3480*S.card ≤ N := by
  classical
  let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
  let d (n : ℕ) := (n^2+1)/(p n)^2
  have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 128*p n ∧ (p n)^2 ∣ n^2+1 := by
    simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
  have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = n^2+1 := Nat.div_mul_cancel (info n hn).2.2
  have divisorBound (n : ℕ) (hn : n∈S) : d n < 16384 := by
    by_contra! h
    have h1 := Nat.mul_le_mul_right ((p n)^2) h
    have h2 := Nat.pow_lt_pow_left (choosePrime n hn).1 (by decide : 2≠0)
    have h3 := Nat.pow_lt_pow_left (info n hn).2.1 (by decide : 2≠0)
    nlinarith only [h1,eq n hn,h2,h3]
  let key (n : ℕ) := (d n, Nat.log 2 (N / p n))
  have posp (n : ℕ) (hn : n∈S) : 0<p n := by have h := (info n hn).2.1; omega
  have labels (n : ℕ) (hn : n∈S) : (key n).1 < 16384 ∧ (key n).2 < 7 := by
    refine ⟨divisorBound n hn,?_⟩
    change Nat.log 2 (N / p n) < 7
    apply Nat.log_lt_of_lt_pow' (by decide : (7:ℕ) ≠ 0)
    have co := (info n hn).2.1
    have up := (Nat.div_lt_iff_lt_mul (posp n hn)).mpr co
    norm_num
    omega
  have pair {x y : ℕ} (hx : x∈S) (hy : y∈S) (k : key x=key y) (lt : p x < p y) : False := by
    have de := congrArg Prod.fst k
    change d x = d y at de
    have label := congrArg Prod.snd k
    change Nat.log 2 (N / p x) = Nat.log 2 (N / p y) at label
    have nonzero : N / p y ≠ 0 := (Nat.div_pos (info y hy).1 (posp y hy)).ne'
    have high := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (N / p x)
    rw [label,pow_succ] at high
    have high' := (Nat.div_lt_iff_lt_mul (posp x hx)).mp high
    have low := (Nat.le_div_iff_mul_le (posp y hy)).mp (Nat.pow_log_le_self 2 nonzero)
    let C := 2 ^ Nat.log 2 (N / p y)
    change C*p y ≤ N at low
    change N < (C*2)*p x at high'
    have col : 0<C := pow_pos (by decide) _
    have gap : p y ≤ 2*p x := by
      by_contra! no
      have h := Nat.mul_le_mul_left C no.le
      nlinarith only [high',low,h]
    have sm : 2 ≤ p x := by have h := (info x hx).2.1; omega
    exact diagonal_gap sm lt gap (eq x hx).symm (de ▸ (eq y hy).symm)
  have inj : Set.InjOn key S := by
    intro x hx y hy hk
    rcases lt_trichotomy (p x) (p y) with h | h | h
    · exact (pair hx hy hk h).elim
    · have de := congrArg Prod.fst hk
      change d x = d y at de
      have xx := eq x hx
      have yy := eq y hy
      rw [de,h] at xx
      have sq : x^2=y^2 := by omega
      exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp sq
    · exact (pair hy hx hk.symm h).elim
  have bound := count_keys S key 16384 7 labels inj
  omega

end Erdos848Odd400

/- Uniform diagonal sieve on a restricted set of residue classes. The
large-square argument is the Pell spacing estimate of Erdős848Gap; the
two-root split is the diagonal sieve of Erdos848Port. -/
namespace Deldor14.Erdos848OddPart
open Finset Erdos848Port
private theorem at_most_one_large_diagonal_root (N p : ℕ) (hp : p.Prime) (hmod : p%4=1)
    (large : 2*N ≤ p^2) (S : Finset ℕ) (inside : ∀ n ∈ S, n < N ∧ p^2 ∣ n^2+1) :
    S.card ≤ 1 := by
  obtain ⟨r,t,opposite,_,_,_,allRoots⟩ := two_roots_mod_p_squared p hp hmod
  have nz : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have root (n : ℕ) (hn : n ∈ S) : (n : ZMod (p^2)) = r ∨ (n : ZMod (p^2)) = -r := by
    have eq0 := (ZMod.natCast_eq_zero_iff (n^2+1) (p^2)).mpr (inside n hn).2
    have eq1 : (n : ZMod (p^2))^2+1 = 0 := by exact_mod_cast eq0
    simpa only [opposite] using allRoots _ (eq_neg_of_add_eq_zero_left eq1)
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have xb := (inside x hx).1
  have yb := (inside y hy).1
  have cases : (x : ZMod (p^2)) = y ∨ (x : ZMod (p^2)) + y = 0 := by
    rcases root x hx with h | h <;> rcases root y hy with g | g <;> simp [h,g]
  rcases cases with h | h
  · have eq := (ZMod.natCast_eq_natCast_iff x y (p^2)).mp h
    change x%(p^2)=y%(p^2) at eq
    simpa only [Nat.mod_eq_of_lt (show x<p^2 by omega),
      Nat.mod_eq_of_lt (show y<p^2 by omega)] using eq
  · have eq : (p^2) ∣ x+y := (ZMod.natCast_eq_zero_iff (x+y) (p^2)).mp (by simpa using h)
    have h0 := Nat.mod_eq_zero_of_dvd eq
    rw [Nat.mod_eq_of_lt (by omega)] at h0
    omega

private theorem diagonal_partial (N k d : ℕ) (P S : Finset ℕ) (B : ℕ → Finset ℕ)
    (primes : P ⊆ diagPrimesUpTo N) (covered : S ⊆ P.biUnion B)
    (old : ∀ p ∈ P, (B p).card ≤ d*(N/(k*p^2)+1))
    (inside : ∀ p, ∀n∈B p, n < N ∧ p^2 ∣ n^2+1) :
    (S.card : ℝ) ≤ (d:ℝ)*((N : ℝ) * (∑ p ∈ P, (1 : ℝ)/(k*(p:ℝ)^2))) +
      (P.card : ℝ) + (d:ℝ)*(((2*N).sqrt : ℝ)/4+2) := by
  classical
  let small := P.filter (· ≤ (2*N).sqrt)
  have point (p : ℕ) (hp : p ∈ P) :
      ((B p).card : ℝ) ≤ ((d:ℝ)*(N : ℝ))*((1 : ℝ)/(k*(p:ℝ)^2)) +
        (if p ≤ (2*N).sqrt then (d : ℝ) else 0) + 1 := by
    by_cases cut : p ≤ (2*N).sqrt
    · rw [if_pos cut]
      have denom := Nat.cast_div_le (α := ℝ) (m := N) (n := k*p^2)
      push_cast at denom
      have o : ((B p).card : ℝ) ≤ (d:ℝ)*(((N/(k*p^2) : ℕ):ℝ)+1) := by exact_mod_cast old p hp
      simp only [div_eq_mul_inv,one_mul] at denom ⊢
      have weighted := mul_le_mul_of_nonneg_left denom (Nat.cast_nonneg (α:=ℝ) d)
      linarith only [o,weighted]
    · rw [if_neg cut]
      have prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (primes hp)).1).2
      have mod4 : p%4=1 := (Finset.mem_filter.mp (primes hp)).2.1
      have lim : 2*N ≤ p^2 := (Nat.sqrt_lt'.mp (lt_of_not_ge cut)).le
      have o : ((B p).card : ℝ) ≤ 1 := by exact_mod_cast at_most_one_large_diagonal_root N p prime mod4 lim (B p) (inside p)
      have hpos : 0 ≤ ((d:ℝ)*(N : ℝ))*((1 : ℝ)/(k*(p:ℝ)^2)) := by positivity
      linarith only [o,hpos]
  have total : S.card ≤ ∑ p ∈ P, (B p).card :=
    (Finset.card_le_card covered).trans Finset.card_biUnion_le
  have totalR : (S.card : ℝ) ≤ ∑ p ∈ P, ((B p).card : ℝ) := by exact_mod_cast total
  have upper := totalR.trans (Finset.sum_le_sum point)
  have count : (∑ p ∈ P, if p ≤ (2*N).sqrt then (d : ℝ) else 0) = (small.card : ℝ)*(d:ℝ) := by
    rw [← Finset.sum_filter]
    simp [small]
  have sub : small ⊆ (range ((2*N).sqrt+1)).filter (fun p=>p ≡ 1 [MOD 4]) := by
    intro p hp
    obtain ⟨pm,lim⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le lim),(mem_filter.mp (primes pm)).2.1⟩
  have cs := (card_le_card sub).trans (card_filter_mod_eq_le ((2*N).sqrt+1) 4 1)
  have cs' : 4*small.card≤(2*N).sqrt+5 := by omega
  have cR : 4*(small.card:ℝ)≤((2*N).sqrt:ℝ)+5 := by exact_mod_cast cs'
  have csr : (small.card:ℝ)≤((2*N).sqrt:ℝ)/4+2 := by linarith only [cR]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,count,Finset.sum_const, nsmul_eq_mul,
    mul_one] at upper
  linarith only [upper,mul_le_mul_of_nonneg_left csr (Nat.cast_nonneg (α:=ℝ) d)]


private lemma diag_by_mod (N M p t : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hcop : Nat.Coprime M (p^2)) :
    ((Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      2 * (N / (M * p ^ 2) + 1) := by
  classical
  obtain ⟨r₁, r₂, hr⟩ :
      ∃ r₁ r₂ : ZMod (p ^ 2),
        r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧ ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
    obtain ⟨r,t,_,rest⟩ := two_roots_mod_p_squared p hp hmod
    exact ⟨r,t,rest⟩
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  let S₁ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ n ≡ r₁.val [MOD p ^ 2])
  let S₂ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ n ≡ r₂.val [MOD p ^ 2])
  have hsubset : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    simp [S, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hdiv : (p ^ 2 : ℕ) ∣ n ^ 2 + 1 := hn.2.2
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) (p ^ 2)).2 hdiv
    have hsq : (n : ZMod (p ^ 2)) ^ 2 = (-1 : ZMod (p ^ 2)) := by
      have : (n : ZMod (p ^ 2)) ^ 2 + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
      simpa using (eq_neg_of_add_eq_zero_left this)
    have hcases : (n : ZMod (p ^ 2)) = r₁ ∨ (n : ZMod (p ^ 2)) = r₂ := hr.2.2.2 _ hsq
    cases hcases with
    | inl hn1 =>
        refine Or.inl ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₁.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₁ := hn1
            _ = (r₁.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₁.val (p ^ 2)).1 hcast
    | inr hn2 =>
        refine Or.inr ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₂.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₂ := hn2
            _ = (r₂.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₂.val (p ^ 2)).1 hcast
  have hcard : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsubset
  have hunion : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
  have hS₁ : S₁.card ≤ N / (M * p ^ 2) + 1 := by
    simpa [S₁, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N M (p ^ 2) t r₁.val hcop)
  have hS₂ : S₂.card ≤ N / (M * p ^ 2) + 1 := by
    simpa [S₂, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N M (p ^ 2) t r₂.val hcop)
  have : S.card ≤ (N / (M * p ^ 2) + 1) + (N / (M * p ^ 2) + 1) :=
    le_trans (le_trans hcard hunion) (add_le_add hS₁ hS₂)
  simpa [S, two_mul] using this

private theorem diagonal_prime {N x : ℕ} (big : 100≤N) (hx : x<N)
    (x7 : x%25≠7) (x18 : x%25≠18) (diag : ¬Squarefree (x*x+1)) :
    ∃p∈diagPrimesUpTo N, p^2 ∣ x^2+1 := by
  obtain ⟨p,prime,sq⟩ := prime_square_exists_ne5 (n:=x^2+1) (by simpa [pow_two] using diag)
    (not_dvd_25_sq_add_one_of_mod_ne x ⟨x7,x18⟩)
  obtain ⟨not5,div⟩ := sq
  have not2 : p≠2 := by
    rintro rfl
    exact not_dvd_four_sq_add_one x div
  have mod4 := prime_sq_divides_implies_one_mod_four p x prime (by have := prime.two_le; omega) div
  have ge := prime_ge_13_of_mod4_one_ne5 p prime mod4 not5
  have lt : x^2+1 < N^2 := (Nat.add_le_add_right (Nat.pow_le_pow_left (show x≤N-1 by omega) 2) 1).trans_lt
    (by simpa only [pow_two] using sq_pred_add_one_lt_sq N big)
  have pn := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) lt div
  exact ⟨p,by simp [diagPrimesUpTo,primesUpTo,Nat.lt_succ_of_le pn,prime,mod4,ge],div⟩

/-- A class-restricted diagonal estimate, with the very-large-prime
remainder paid only once across all permitted residue classes. -/
theorem diagonal_budget {N M t : ℕ} (big : 400000000≤N) (mchoice : M=25 ∨ M=50 ∨ M=150 ∨ (0<M ∧ M≤6))
    (T S : Finset ℕ) (size : T.card≤t)
    (info : ∀ x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1) ∧ x%M∈T) :
    (S.card:ℝ) ≤ (2*(t:ℝ))*(N:ℝ)*(5/359)/(M:ℝ) +
       (N:ℝ)/1014 + (2*(t:ℝ))*(N:ℝ)/55000 + (N:ℝ)/3480 := by
  classical
  let P := (diagPrimesUpTo N).filter (fun p=>128*p≤N)
  let B (p : ℕ) := S.filter (fun x=>p^2∣x^2+1)
  let low := P.biUnion B
  let high := S \ low
  have inp (p) (hp : p∈P) := (mem_filter.mp hp).1
  have prime (p) (hp : p∈P) : p.Prime := (mem_filter.mp (mem_filter.mp (inp p hp)).1).2
  have prop (p) (hp : p∈P) : p%4=1 ∧ 13≤p := (mem_filter.mp (inp p hp)).2
  have inside (p n) (hn : n∈B p) : n<N ∧ p^2∣n^2+1 :=
    ⟨(info n (mem_filter.mp hn).1).1,(mem_filter.mp hn).2⟩
  have capHigh := Erdos848Odd400.large_diagonal_128 big high (by
    intro x hx
    obtain ⟨xS,xL⟩ := mem_sdiff.mp hx
    obtain ⟨xn,x7,x18,di,_⟩ := info x xS
    obtain ⟨p,mem,div⟩ := diagonal_prime (by omega) xn x7 x18 di
    have pn := mem_range.mp (mem_filter.mp (mem_filter.mp mem).1).1
    refine ⟨xn,p,by omega,?_,div⟩
    by_contra! small
    exact xL (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,small⟩,mem_filter.mpr ⟨xS,div⟩⟩))
  have capP := Erdos848Odd400.small_primes_128 big P prime (by
    intro p hp
    have h := (mem_filter.mp hp).2
    omega)
  have points (p) (hp : p∈P) : (B p).card ≤ (2*t)*(N/(M*p^2)+1) := by
    let frac (r) := (range N).filter (fun x=>x ≡ r [MOD M] ∧ p^2∣x^2+1)
    have each (r) (_ : r∈T) : (frac r).card≤2*(N/(M*p^2)+1) := by
      have pp := prop p hp
      apply diag_by_mod _ _ _ _ (prime p hp) pp.1
      rcases mchoice with rfl|rfl|rfl|⟨pos,small⟩
      · exact coprime_25_pow_two_of_prime_ne5 p (prime p hp) (by omega)
      · exact coprime_50_pow_two_of_prime_ne2_ne5 p (prime p hp) (by omega) (by omega)
      · have cp6 := ((prime p hp).coprime_iff_not_dvd.mpr (fun dv=>(not_le_of_gt (by omega : 6<p)) (Nat.le_of_dvd (by decide : 0<6) dv))).symm.pow_right 2
        exact Nat.Coprime.mul_left cp6 (coprime_25_pow_two_of_prime_ne5 p (prime p hp) (by omega))
      · exact ((prime p hp).coprime_iff_not_dvd.mpr (fun dv=>(not_le_of_gt (by omega : M<p)) (Nat.le_of_dvd pos dv))).symm.pow_right _
    have subset : B p ⊆ T.biUnion frac := by
      intro x hx
      obtain ⟨sx,div⟩ := mem_filter.mp hx
      obtain ⟨xn,_,_,_,xr⟩ := info x sx
      exact mem_biUnion.mpr ⟨x%M,xr,mem_filter.mpr ⟨mem_range.mpr xn,by simp [Nat.ModEq],div⟩⟩
    simpa only [←Nat.mul_assoc,Nat.mul_comm t 2] using
      ((card_le_card subset).trans (card_biUnion_le_card_mul T frac _ each)).trans
        (Nat.mul_le_mul_right _ size)
  have est : (low.card:ℝ) ≤ (2*(t:ℝ))*((N:ℝ)*(∑p∈P,(1:ℝ)/(M*(p:ℝ)^2)))+
        (P.card:ℝ)+(2*(t:ℝ))*(((2*N).sqrt:ℝ)/4+2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      diagonal_partial N M (2*t) P low B (fun p hp=>inp p hp) Subset.rfl points inside
  have primeSum : (∑p∈P,(1:ℝ)/(p:ℝ)^2) ≤ 5/359 := by
    have sq : (∑p∈P,(1:ℚ)/(p:ℚ)^2) ≤ 5/359 := by
      calc _ ≤ ∑p∈diagPrimesUpTo N,(1:ℚ)/(p:ℚ)^2 := sum_le_sum_of_subset_of_nonneg (fun p hp=>inp p hp) (by intros; positivity)
           _ ≤ _ := by convert sum_diagPrimesUpTo_le N using 1; norm_num
    have cast := (Rat.cast_le (K:=ℝ)).mpr sq
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using cast
  have rest : (∑p∈P,(1:ℝ)/(M*(p:ℝ)^2))= (∑p∈P,(1:ℝ)/(p:ℝ)^2)/(M:ℝ) := by
    rw [sum_div]; apply sum_congr rfl; intro p hp; ring
  rw [rest] at est
  have soft : (2*(t:ℝ))*((N:ℝ)*((∑p∈P,(1:ℝ)/(p:ℝ)^2)/(M:ℝ))) ≤
       (2*(t:ℝ))*(N:ℝ)*(5/359)/(M:ℝ) := by
    rw [mul_div_assoc',←mul_div_assoc,←mul_assoc]
    gcongr
  have grow : 28000^2 ≤ 2*N := by norm_num; omega
  have le := Nat.le_sqrt'.mpr grow
  have bound := (Nat.mul_le_mul_right (2*N).sqrt le).trans (by simpa only [←pow_two] using Nat.sqrt_le' (2*N))
  have sr : 28000*((2*N).sqrt:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast bound
  have nR : 400000000≤(N:ℝ) := by exact_mod_cast big
  have sqrtR : (2*(t:ℝ))*(((2*N).sqrt:ℝ)/4+2)≤(2*(t:ℝ))*(N:ℝ)/55000 := by
    rw [mul_div_assoc]; gcongr; linarith only [sr,nR]
  have highR : 3480*(high.card:ℝ)≤(N:ℝ) := by exact_mod_cast capHigh
  have pR : 1014*(P.card:ℝ)≤(N:ℝ) := by exact_mod_cast capP
  have comb : S.card≤low.card+high.card := by
    have e := card_sdiff_add_card_inter S low
    have sub := card_le_card (inter_subset_right (s₁:=S) (s₂:=low))
    change S.card≤low.card+(S\low).card
    omega
  have combR : (S.card:ℝ)≤(low.card:ℝ)+(high.card:ℝ) := by exact_mod_cast comb
  linarith only [combR,est,soft,sqrtR,highR,pR]
private theorem phase_partial (N : ℕ) (P S : Finset ℕ) (B : ℕ → Finset ℕ)
    (primes : P ⊆ diagPrimesUpTo N) (covered : S ⊆ P.biUnion B)
    (old : ∀ p ∈ P, ((B p).card:ℝ) ≤ (23/50:ℝ)*((N:ℝ)/(p:ℝ)^2)+6)
    (inside : ∀ p, ∀n∈B p, n < N ∧ p^2 ∣ n^2+1) :
    (S.card : ℝ) ≤ (23/50:ℝ)*((N : ℝ) * (∑ p ∈ P, (1 : ℝ)/((p:ℝ)^2))) +
      (P.card : ℝ) + (6:ℝ)*(((2*N).sqrt : ℝ)/4+2) := by
  classical
  let small := P.filter (· ≤ (2*N).sqrt)
  have point (p : ℕ) (hp : p ∈ P) :
      ((B p).card : ℝ) ≤ ((23/50:ℝ)*(N : ℝ))*((1 : ℝ)/((p:ℝ)^2)) +
        (if p ≤ (2*N).sqrt then (6:ℝ) else 0) + 1 := by
    by_cases cut : p ≤ (2*N).sqrt
    · rw [if_pos cut]
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using
        (old p hp).trans (le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num))
    · rw [if_neg cut]
      have prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (primes hp)).1).2
      have mod4 : p%4=1 := (Finset.mem_filter.mp (primes hp)).2.1
      have lim : 2*N ≤ p^2 := (Nat.sqrt_lt'.mp (lt_of_not_ge cut)).le
      have o : ((B p).card : ℝ) ≤ 1 := by exact_mod_cast at_most_one_large_diagonal_root N p prime mod4 lim (B p) (inside p)
      have hpos : 0 ≤ ((23/50:ℝ)*(N : ℝ))*((1 : ℝ)/((p:ℝ)^2)) := by positivity
      linarith only [o,hpos]
  have total : S.card ≤ ∑ p ∈ P, (B p).card :=
    (Finset.card_le_card covered).trans Finset.card_biUnion_le
  have totalR : (S.card : ℝ) ≤ ∑ p ∈ P, ((B p).card : ℝ) := by exact_mod_cast total
  have upper := totalR.trans (Finset.sum_le_sum point)
  have count : (∑ p ∈ P, if p ≤ (2*N).sqrt then (6:ℝ) else 0) = (small.card : ℝ)*(6:ℝ) := by
    rw [← Finset.sum_filter]
    simp [small]
  have sub : small ⊆ (range ((2*N).sqrt+1)).filter (fun p=>p ≡ 1 [MOD 4]) := by
    intro p hp
    obtain ⟨pm,lim⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le lim),(mem_filter.mp (primes pm)).2.1⟩
  have cs := (card_le_card sub).trans (card_filter_mod_eq_le ((2*N).sqrt+1) 4 1)
  have cs' : 4*small.card≤(2*N).sqrt+5 := by omega
  have cR : 4*(small.card:ℝ)≤((2*N).sqrt:ℝ)+5 := by exact_mod_cast cs'
  have csr : (small.card:ℝ)≤((2*N).sqrt:ℝ)/4+2 := by linarith only [cR]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,count,Finset.sum_const, nsmul_eq_mul,
    mul_one] at upper
  linarith only [upper,mul_le_mul_of_nonneg_left csr (show (0:ℝ)≤6 by norm_num)]


private theorem phase_two {N p : ℕ} (s : ℕ) (S : Finset ℕ) (hp : p.Prime) (mod4 : p%4=1) (ge : 13≤p)
    (info : ∀x∈S,x<N ∧ x ≡ s [MOD 4] ∧ x%25≠7 ∧ x%25≠18 ∧ p^2∣x^2+1) :
    (S.card:ℝ)≤(23/50:ℝ)*((N:ℝ)/(p:ℝ)^2)+6 := by
  classical
  have nz : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let G (r : ZMod (p^2)) := (Deldor14.Erdos848Phase.prog N (p^2) r.val).filter
    (fun x=>x ≡ s [MOD 4] ∧ x%25≠7 ∧ x%25≠18)
  have one (r : ZMod (p^2)) : ((G r).card:ℝ)≤(23/100:ℝ)*((N:ℝ)/(p:ℝ)^2)+3 :=
    Deldor14.Erdos848Phase.odd_phase (N:=N) (u:=r.val) (s:=s) hp ge
  obtain ⟨r,t,_,_,_,_,root⟩ := two_roots_mod_p_squared p hp mod4
  have subset : S ⊆ G r ∪ G t := by
    intro x hx
    obtain ⟨xn,x4,x7,x18,div⟩ := info x hx
    have eq0 := (ZMod.natCast_eq_zero_iff (x^2+1) (p^2)).mpr div
    have eq1 : (x:ZMod (p^2))^2+1=0 := by exact_mod_cast eq0
    have lift (z : ZMod (p^2)) (eq : (x:ZMod (p^2))=z) : x∈G z := by
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr xn,(ZMod.natCast_eq_natCast_iff x z.val (p^2)).mp (by simpa using eq)⟩,x4,x7,x18⟩
    exact (root _ (eq_neg_of_add_eq_zero_left eq1)).elim (fun e=>mem_union_left _ (lift _ e)) (fun e=>mem_union_right _ (lift _ e))
  have leR : (S.card:ℝ)≤((G r).card:ℝ)+((G t).card:ℝ) := by
    exact_mod_cast (card_le_card subset).trans (card_union_le ..)
  linarith only [leR,one r,one t]

theorem outside_single_mod_four {N : ℕ} (s : ℕ) (big : 400000000≤N) (S : Finset ℕ)
    (info : ∀x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1) ∧ x ≡ s [MOD 4]) :
    (S.card:ℝ) ≤ (781/100000)*(N:ℝ) := by
  classical
  let P := (diagPrimesUpTo N).filter (fun p=>128*p≤N)
  let B (p : ℕ) := S.filter (fun x=>p^2∣x^2+1)
  let low := P.biUnion B
  let high := S \ low
  have inp (p) (hp : p∈P) := (mem_filter.mp hp).1
  have prime (p) (hp : p∈P) : p.Prime := (mem_filter.mp (mem_filter.mp (inp p hp)).1).2
  have prop (p) (hp : p∈P) : p%4=1 ∧ 13≤p := (mem_filter.mp (inp p hp)).2
  have inside (p n) (hn : n∈B p) : n<N ∧ p^2∣n^2+1 :=
    ⟨(info n (mem_filter.mp hn).1).1,(mem_filter.mp hn).2⟩
  have capHigh := Erdos848Odd400.large_diagonal_128 big high (by
    intro x hx
    obtain ⟨xS,xL⟩ := mem_sdiff.mp hx
    obtain ⟨xn,x7,x18,di,_⟩ := info x xS
    obtain ⟨p,mem,div⟩ := diagonal_prime (by omega) xn x7 x18 di
    have pn := mem_range.mp (mem_filter.mp (mem_filter.mp mem).1).1
    refine ⟨xn,p,by omega,?_,div⟩
    by_contra! small
    exact xL (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,small⟩,mem_filter.mpr ⟨xS,div⟩⟩))
  have capP := Erdos848Odd400.small_primes_128 big P prime (by
    intro p hp
    have h := (mem_filter.mp hp).2
    omega)
  have points (p) (hp : p∈P) : ((B p).card:ℝ) ≤ (23/50:ℝ)*((N:ℝ)/(p:ℝ)^2)+6 := by
    apply phase_two s _ (prime p hp) (prop p hp).1 (prop p hp).2
    intro x hx
    obtain ⟨sx,dv⟩ := mem_filter.mp hx
    obtain ⟨xn,x7,x18,_,x4⟩ := info x sx
    exact ⟨xn,x4,x7,x18,dv⟩
  have est := phase_partial N P low B (fun p hp=>inp p hp) Subset.rfl points inside
  have primeSum : (∑p∈P,(1:ℝ)/(p:ℝ)^2) ≤ 5/359 := by
    have sq : (∑p∈P,(1:ℚ)/(p:ℚ)^2) ≤ 5/359 := by
      calc _ ≤ ∑p∈diagPrimesUpTo N,(1:ℚ)/(p:ℚ)^2 := sum_le_sum_of_subset_of_nonneg (fun p hp=>inp p hp) (by intros; positivity)
           _ ≤ _ := by convert sum_diagPrimesUpTo_le N using 1; norm_num
    have cast := (Rat.cast_le (K:=ℝ)).mpr sq
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using cast
  have grow : 28000^2 ≤ 2*N := by norm_num; omega
  have le := Nat.le_sqrt'.mpr grow
  have bound := (Nat.mul_le_mul_right (2*N).sqrt le).trans (by simpa only [←pow_two] using Nat.sqrt_le' (2*N))
  have sr : 28000*((2*N).sqrt:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast bound
  have nR : 400000000≤(N:ℝ) := by exact_mod_cast big
  have sr' : (6:ℝ)*(((2*N).sqrt:ℝ)/4+2) ≤ 6*(N:ℝ)/55000 := by linarith only [sr,nR]
  have highR : 3480*(high.card:ℝ)≤(N:ℝ) := by exact_mod_cast capHigh
  have pR : 1014*(P.card:ℝ)≤(N:ℝ) := by exact_mod_cast capP
  have comb : S.card≤low.card+high.card := by
    have e := card_sdiff_add_card_inter S low
    have sub := card_le_card (inter_subset_right (s₁:=S) (s₂:=low))
    change S.card≤low.card+(S\low).card
    omega
  have combR : (S.card:ℝ)≤(low.card:ℝ)+(high.card:ℝ) := by exact_mod_cast comb
  have weighted := mul_le_mul_of_nonneg_left primeSum (Nat.cast_nonneg (α:=ℝ) N)
  linarith only [combR,est,weighted,sr',highR,pR,Nat.cast_nonneg (α:=ℝ) N]
end Deldor14.Erdos848OddPart

/- Mixed sets of odd integers, with separate bounds when one or both odd residues modulo four occur outside the exceptional base classes. -/
namespace Deldor14.Erdos848OddPart
open Finset Erdos848
abbrev slice (A : Finset ℕ) (r : ℕ) := A.filter (fun x=>x%25=r)
abbrev outside (A : Finset ℕ) := A.filter (fun x=>x%25≠7 ∧ x%25≠18)
def block (A : Finset ℕ) (r b : ℕ) := (slice A r).filter (fun x=>x%4=b%4)

theorem odd_block {N b r : ℕ} {A : Finset ℕ} (big : 400000000≤N) (inside : A ⊆ range N)
    (adm : NonSquarefreeProductProp A) (odd : ∀x∈A,x%2=1) (br : b∈outside A)
    (base : r=7 ∨ r=18) : ((block A r b).card:ℝ) ≤ (603/100000)*(N:ℝ) := by
  obtain ⟨ba,b7,b18⟩ := mem_filter.mp br
  have diff : b%25≠r := by omega
  have left (x) (hx : x∈block A r b) : x∈A ∧ x%25=r ∧ x%4=b%4 :=
    ⟨(mem_filter.mp (mem_filter.mp hx).1).1,(mem_filter.mp (mem_filter.mp hx).1).2,(mem_filter.mp hx).2⟩
  apply Erdos848Odd400.bad_ten_100 (r:=r) (s:=b) big (mem_range.mp (inside ba)) (by have h:=odd b ba; omega)
    _ (fun x hx=>inside (left x hx).1)
  · intro x hx; change x%25=r%25; rw [(left x hx).2.1,Nat.mod_eq_of_lt (by omega : r<25)]
  · exact fun x hx=>(left x hx).2.2
  · exact fun x hx=>adm b ba x (left x hx).1
  · intro x hx div
    have mod := Nat.mod_eq_zero_of_dvd div
    rw [Nat.add_mod,Nat.mul_mod,(left x hx).2.2] at mod
    rcases (show b%4=1 ∨ b%4=3 by have h:=odd b ba; omega) with e|e <;> rw [e] at mod <;> contradiction
  · exact fun x hx=>Deldor14.Erdos848Tenth.between_not25 base diff (left x hx).2.1

theorem one_block {N b r : ℕ} {A : Finset ℕ} (big : 400000000≤N) (inside : A ⊆ range N)
    (adm : NonSquarefreeProductProp A) (odd : ∀x∈A,x%2=1) (br : b∈outside A)
    (base : r=7 ∨ r=18) : ((slice A r).card:ℝ) ≤ (1603/100000)*(N:ℝ)+1 := by
  let L := block A r b
  let F := slice A r \ L
  have ang := odd_block big inside adm odd br base
  have parts : (slice A r).card=F.card+L.card := (card_sdiff_add_card_eq_card (filter_subset .. : L⊆slice A r)).symm
  have sub : F ⊆ (range N).filter (fun x=>x ≡ r [MOD 25] ∧ x ≡ 4-b%4 [MOD 4]) := by
    intro x hx
    obtain ⟨sx,ne⟩ := mem_sdiff.mp hx
    obtain ⟨xa,xr⟩ := mem_filter.mp sx
    have mis : x%4≠b%4 := fun eq=>ne (mem_filter.mpr ⟨sx,eq⟩)
    refine mem_filter.mpr ⟨inside xa,?_,?_⟩
    · change x%25=r%25; rw [xr,Nat.mod_eq_of_lt (by omega : r<25)]
    · have xo:=odd x xa; have bo:=odd b (mem_filter.mp br).1
      change x%4=(4-b%4)%4; omega
  have far := (card_le_card sub).trans (Erdos848Port.card_filter_modEq_and_modEq_le N 25 4 r (4-b%4) (by decide))
  have fx : F.card ≤ N/100+1 := far
  have bound : 100*F.card≤N+100 := by omega
  have fR : 100*(F.card:ℝ) ≤ (N:ℝ)+100 := by exact_mod_cast bound
  have pR : ((slice A r).card:ℝ)=(F.card:ℝ)+(L.card:ℝ) := by exact_mod_cast parts
  change (L.card:ℝ)≤_ at ang
  linarith only [ang,pR,fR]

theorem two_blocks {N b c r : ℕ} {A : Finset ℕ} (big : 400000000≤N) (inside : A ⊆ range N)
    (adm : NonSquarefreeProductProp A) (odd : ∀x∈A,x%2=1) (br : b∈outside A) (cr : c∈outside A)
    (different : b%4≠c%4) (base : r=7 ∨ r=18) : ((slice A r).card:ℝ) ≤ (1206/100000)*(N:ℝ) := by
  have sub : slice A r ⊆ block A r b ∪ block A r c := by
    intro x hx
    have xo:=odd x (mem_filter.mp hx).1
    have bo:=odd b (mem_filter.mp br).1
    have co:=odd c (mem_filter.mp cr).1
    by_cases eq : x%4=b%4
    · exact mem_union_left _ (mem_filter.mpr ⟨hx,eq⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hx,by omega⟩)
  have cnt : ((slice A r).card:ℝ) ≤ ((block A r b).card:ℝ)+((block A r c).card:ℝ) := by
    exact_mod_cast (card_le_card sub).trans (card_union_le ..)
  linarith only [cnt,odd_block big inside adm odd br base,odd_block big inside adm odd cr base]

theorem odd_mixed {k : ℕ} (big : 400000000≤25*k+7) (A : Finset ℕ) (inside : A⊆range (25*k+7))
    (adm : NonSquarefreeProductProp A) (odd : ∀x∈A,x%2=1) (mixed : (outside A).Nonempty) : A.card≤k := by
  let N:=25*k+7
  let R:=outside A
  have info (x) (hx : x∈R) : x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1) := by
    obtain ⟨xa,x7,x18⟩ := mem_filter.mp hx
    exact ⟨mem_range.mp (inside xa),x7,x18,adm x xa x xa⟩
  have total := Deldor14.Erdos848Tenth.total_parts A
  change (A.card:ℝ) ≤ ((slice A 7).card:ℝ)+((slice A 18).card:ℝ)+(R.card:ℝ) at total
  have endp : (N:ℝ)=25*(k:ℝ)+7 := by dsimp [N]; push_cast; ring
  have nr : 400000000≤(N:ℝ) := by exact_mod_cast big
  by_contra! bad
  have more : (k:ℝ)+1≤(A.card:ℝ) := by exact_mod_cast (show k+1≤A.card by omega)
  obtain ⟨b,rb⟩ := mixed
  by_cases same : ∀x∈R,x%4=b%4
  · have diag := outside_single_mod_four b big R (fun x hx=>by
      obtain ⟨a,c,d,e⟩ := info x hx
      exact ⟨a,c,d,e,same x hx⟩)
    have h7 := one_block big inside adm odd rb (Or.inl (rfl : 7=7))
    have h18 := one_block big inside adm odd rb (Or.inr (rfl : 18=18))
    change ((slice A 7).card:ℝ)≤(1603/100000)*(N:ℝ)+1 at h7
    change ((slice A 18).card:ℝ)≤(1603/100000)*(N:ℝ)+1 at h18
    linarith only [diag,h7,h18,total,more,endp,nr]
  · push Not at same
    obtain ⟨c,rc,diff⟩ := same
    let T:=(range 50).filter (fun q=>q%2=1 ∧ q%25≠7 ∧ q%25≠18)
    have size : T.card≤23 := by decide
    have diag := diagonal_budget (M:=50) (t:=23) big (by decide) T R size (by
      intro x hx
      obtain ⟨a,b,c,d⟩ := info x hx
      have o := odd x (mem_filter.mp hx).1
      exact ⟨a,b,c,d,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),by omega,by omega,by omega⟩⟩)
    push_cast at diag
    have h7 := two_blocks big inside adm odd rb rc diff.symm (Or.inl (rfl : 7=7))
    have h18 := two_blocks big inside adm odd rb rc diff.symm (Or.inr (rfl : 18=18))
    change ((slice A 7).card:ℝ)≤(1206/100000)*(N:ℝ) at h7
    change ((slice A 18).card:ℝ)≤(1206/100000)*(N:ℝ) at h18
    linarith only [diag,h7,h18,total,more,endp,nr]
end Deldor14.Erdos848OddPart

/- Counts for even arguments in one base class, using arithmetic progression modulo fifty. -/
namespace Erdos848Parity400
open Finset Erdos848Port Erdos848Pure

lemma off_count_modEq50_le (N p b t25 t2 : ℕ) (hp : Nat.Prime p) (hb : ¬ p ∣ b)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t2 [MOD 2] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (50 * p ^ 2) + 1 := by
  classical
  have hcop25_2 : Nat.Coprime 25 2 := by decide
  have hsub :
      (Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t2 [MOD 2] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_2 t25 t2 [MOD 50] ∧ p ^ 2 ∣ b * a + 1) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ?_, ha.2.2.2⟩
    exact Nat.chineseRemainder_modEq_unique (co := hcop25_2) ha.2.1 ha.2.2.1
  have hcard :
      ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t2 [MOD 2] ∧ p ^ 2 ∣ b * a + 1)).card ≤
        ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_2 t25 t2 [MOD 50] ∧ p ^ 2 ∣ b * a + 1)).card :=
    Finset.card_le_card hsub
  have hcop : Nat.Coprime 50 (p ^ 2) := coprime_50_pow_two_of_prime_ne2_ne5 p hp hp2 hp5
  have hp0 : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let r : ℕ := rZ.val
  have hrZ : (r : ZMod (p ^ 2)) = rZ := by
    have : NeZero (p ^ 2) := ⟨hp0⟩
    simp [r, rZ]
  have hsubset2 :
      (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_2 t25 t2 [MOD 50] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_2 t25 t2 [MOD 50] ∧ a ≡ r [MOD p ^ 2]) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.1, ?_⟩
    have hdiv : p ^ 2 ∣ b * a + 1 := ha.2.2
    have hEq : (a : ZMod (p ^ 2)) = -((b : ZMod (p ^ 2))⁻¹) := by
      have : p ^ 2 ∣ b * a + 1 := by simpa [Nat.mul_comm] using hdiv
      exact (dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv (p := p) (a := b) (b := a) hp hb).1 this
    have : (a : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
      simpa [rZ, hrZ] using hEq
    exact (ZMod.natCast_eq_natCast_iff a r (p ^ 2)).1 this
  have hcard2 :
      ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_2 t25 t2 [MOD 50] ∧ p ^ 2 ∣ b * a + 1)).card ≤
        ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_2 t25 t2 [MOD 50] ∧ a ≡ r [MOD p ^ 2])).card :=
    Finset.card_le_card hsubset2
  have hfinal :
      ((Finset.range N).filter (fun a => a ≡ Nat.chineseRemainder hcop25_2 t25 t2 [MOD 50] ∧ a ≡ r [MOD p ^ 2])).card ≤
        N / (50 * p ^ 2) + 1 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N 50 (p ^ 2) (Nat.chineseRemainder hcop25_2 t25 t2) r hcop)
  exact le_trans (le_trans hcard hcard2) hfinal

lemma off_count_modEq50_le' (N p b t25 t2 : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t2 [MOD 2] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (50 * p ^ 2) + 1 := by
  by_cases hb : p ∣ b
  · 
    have hempty :
        (Finset.range N).filter
            (fun a => a ≡ t25 [MOD 25] ∧ a ≡ t2 [MOD 2] ∧ p ^ 2 ∣ b * a + 1) = ∅ := by
      simpa [and_assoc] using
        (filter_empty_of_prime_dvd_left_of_pred (N := N) (p := p) (b := b) hp hb
          (pred := fun a => a ≡ t25 [MOD 25] ∧ a ≡ t2 [MOD 2]))
    simp [hempty]
  · exact off_count_modEq50_le N p b t25 t2 hp hb hp2 hp5

theorem bad_bound_mod50 {N b r s : ℕ} (big : 400000000 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N)
    (res : ∀ n∈S, n ≡ r [MOD 25]) (res2 : ∀ n∈S, n ≡ s [MOD 2])
    (bad : ∀ n∈S, ¬Squarefree (b*n+1))
    (h4 : ∀ n∈S, ¬4∣b*n+1) (h25 : ∀ n∈S, ¬25∣b*n+1) :
    (S.card:ℝ) ≤ (N:ℝ)*(163/50000)+(N:ℝ)/120 := by
  classical
  let P := offPrimesUpTo N
  let Q := P.filter (fun p => 24*p≤N)
  let R := P.filter (fun p => N<24*p)
  let B (p : ℕ) := (range N).filter (fun n => n ≡ r [MOD 25] ∧ n ≡ s [MOD 2] ∧ p^2∣b*n+1)
  have prime {p : ℕ} (h : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
  have bound {p : ℕ} (h : p ∈ P) : p ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1)
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    obtain ⟨p,hp,p5,pdv⟩ := prime_square_exists_ne5 (bad n hn) (h25 n hn)
    have nN := Finset.mem_range.mp (inRange hn)
    have pred := Nat.mul_le_mul (Nat.le_pred_of_lt bn) (Nat.le_pred_of_lt nN)
    have le := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) ((Nat.add_le_add_right pred 1).trans_lt
      (sq_pred_add_one_lt_sq N (by omega))) pdv
    have p2 : p ≠ 2 := fun e => h4 n hn (by simpa [e] using pdv)
    have mem : p ∈ P := by simp [P,offPrimesUpTo,primesUpTo,hp,Nat.lt_succ_of_le le,p5,p2]
    have nb : n ∈ B p := Finset.mem_filter.mpr ⟨inRange hn,res n hn,res2 n hn,pdv⟩
    by_cases h : 24*p ≤ N
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,h⟩,nb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,Nat.lt_of_not_ge h⟩,nb⟩)
  have cards : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (card_le_card cover).trans (card_union_le ..)
  have sub : Q ⊆ P := Finset.filter_subset ..
  have lc := small_primes_24 big Q (fun _ h => prime (sub h)) (fun _ h => (mem_filter.mp h).2)
  have hc := large_mixed_24 big bn (R.biUnion B) (by
    intro n hn
    obtain ⟨p,hp,nb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨nN,pdv⟩ := Finset.mem_filter.mp nb
    exact ⟨Finset.mem_range.mp nN,p,bound (mem_filter.mp hp).1,(mem_filter.mp hp).2,pdv.2.2⟩)
  have first := sieve_set_card_bound N 50 Q (Q.biUnion B) (fun p n => n ≡ r [MOD 25] ∧ n ≡ s [MOD 2] ∧ p^2∣b*n+1)
    Subset.rfl (fun p hp => off_count_modEq50_le' N p b r s (prime (sub hp)) (mem_filter.mp (sub hp)).2.1 (mem_filter.mp (sub hp)).2.2)
  have sumRat : (∑ p∈Q,(1:ℚ)/(p:ℚ)^2) ≤ 163/1000 :=
    (Finset.sum_le_sum_of_subset_of_nonneg sub (fun p _ _ => by positivity)).trans (sum_offPrimesUpTo_le N)
  have cast := (Rat.cast_le (K:=ℝ)).mpr sumRat
  simp only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] at cast
  have est : (∑ p∈Q,(1:ℝ)/(50*(p:ℝ)^2)) ≤ 163/50000 := by
    have f (p : ℕ) : (1:ℝ)/(50*(p:ℝ)^2) = (1/50)*(1/(p:ℝ)^2) := by ring
    simp only [f,←Finset.mul_sum]
    linarith only [cast]
  have weight := mul_le_mul_of_nonneg_left est (show 0 ≤ (N:ℝ) by positivity)
  have countR : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast cards
  have lcr : (Q.card:ℝ) ≤ (N:ℝ)/190 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    rw [mul_comm]
    exact_mod_cast lc
  have hcr : ((R.biUnion B).card:ℝ) ≤ (N:ℝ)/330 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    rw [mul_comm]
    exact_mod_cast hc
  linarith only [first,weight,countR,lcr,hcr,Nat.cast_nonneg (α:=ℝ) N]

end Erdos848Parity400

/- Arbitrary sets whose elements outside the exceptional base classes occupy a single even residue modulo four. -/
namespace Deldor14.Erdos848OddPart
open Finset Erdos848

theorem even_row {N b r : ℕ} {A : Finset ℕ} (big : 400000000 ≤ N) (inside : A ⊆ range N)
    (adm : NonSquarefreeProductProp A) (br : b ∈ outside A) (even : 2 ∣ b)
    (base : r=7 ∨ r=18) : ((slice A r).card:ℝ) ≤ (14854/1000000)*(N:ℝ) := by
  obtain ⟨ba,b7,b18⟩ := mem_filter.mp br
  have diff : b%25 ≠ r := by omega
  have h := Erdos848Pure.bad_bound_400M (r:=r) big (mem_range.mp (inside ba)) (slice A r)
    ((filter_subset ..).trans inside) (by
      intro x hx
      change x%25=r%25
      rw [(mem_filter.mp hx).2,Nat.mod_eq_of_lt (by omega : r < 25)]) (by
      intro x hx; exact adm b ba x (mem_filter.mp hx).1) (by
      intro x hx; exact Deldor14.Erdos848Tenth.between_not25 base diff (mem_filter.mp hx).2)
  rw [if_pos even] at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]

theorem even_outside_mixed {k : ℕ} (big : 400000000 ≤ 25*k+7) (A : Finset ℕ)
    (inside : A ⊆ range (25*k+7)) (adm : NonSquarefreeProductProp A)
    (mixed : (outside A).Nonempty) (s : ℕ) (ev : 2 ∣ s) (same : ∀x∈outside A, x ≡ s [MOD 4]) :
    A.card ≤ k := by
  let N := 25*k+7
  let R := outside A
  obtain ⟨b,rb⟩ := mixed
  have bs := same b rb
  change b%4=s%4 at bs
  have be : 2 ∣ b := by omega
  have h7 := even_row big inside adm rb be (Or.inl (rfl : 7=7))
  have h18 := even_row big inside adm rb be (Or.inr (rfl : 18=18))
  have diag := outside_single_mod_four s big R (by
    intro x hx
    obtain ⟨xa,x7,x18⟩ := mem_filter.mp hx
    exact ⟨mem_range.mp (inside xa),x7,x18,adm x xa x xa,same x hx⟩)
  have total := Deldor14.Erdos848Tenth.total_parts A
  change (A.card:ℝ) ≤ ((slice A 7).card:ℝ)+((slice A 18).card:ℝ)+(R.card:ℝ) at total
  change ((slice A 7).card:ℝ) ≤ (14854/1000000)*(N:ℝ) at h7
  change ((slice A 18).card:ℝ) ≤ (14854/1000000)*(N:ℝ) at h18
  have endp : (N:ℝ)=25*(k:ℝ)+7 := by dsimp [N]; push_cast; ring
  have nr : 400000000 ≤ (N:ℝ) := by exact_mod_cast big
  by_contra! bad
  have more : (k:ℝ)+1 ≤ (A.card:ℝ) := by exact_mod_cast (show k+1 ≤ A.card by omega)
  linarith only [diag,h7,h18,total,more,endp,nr]

theorem even_halfrow {N b r : ℕ} {A : Finset ℕ} (big : 400000000 ≤ N) (inside : A ⊆ range N)
    (adm : NonSquarefreeProductProp A) (br : b ∈ outside A) (even : ∀x∈A,2∣x)
    (base : r=7 ∨ r=18) : ((slice A r).card:ℝ) ≤ (116/10000)*(N:ℝ) := by
  obtain ⟨ba,b7,b18⟩ := mem_filter.mp br
  have diff : b%25 ≠ r := by omega
  have h := Erdos848Parity400.bad_bound_mod50 (r:=r) (s:=0) big (mem_range.mp (inside ba)) (slice A r)
    ((filter_subset ..).trans inside) (by
      intro x hx
      change x%25=r%25
      rw [(mem_filter.mp hx).2,Nat.mod_eq_of_lt (by omega : r < 25)]) (by
      intro x hx; exact Nat.mod_eq_zero_of_dvd (even x (mem_filter.mp hx).1)) (by
      intro x hx; exact adm b ba x (mem_filter.mp hx).1) (by
      intro x hx dv
      have two : 2∣b*x := (even b ba).mul_right x
      have two2 : 2∣b*x+1 := (by decide : 2∣4).trans dv
      omega) (by
      intro x hx; exact Deldor14.Erdos848Tenth.between_not25 base diff (mem_filter.mp hx).2)
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]

theorem all_even_mixed {k : ℕ} (big : 400000000 ≤ 25*k+7) (A : Finset ℕ)
    (inside : A ⊆ range (25*k+7)) (adm : NonSquarefreeProductProp A)
    (mixed : (outside A).Nonempty) (even : ∀x∈A, 2∣x) :
    A.card ≤ k := by
  let N := 25*k+7
  let R := outside A
  obtain ⟨b,rb⟩ := mixed
  have h7 := even_halfrow big inside adm rb even (Or.inl (rfl : 7=7))
  have h18 := even_halfrow big inside adm rb even (Or.inr (rfl : 18=18))
  let T:=(range 50).filter (fun q=>q%2=0 ∧ q%25≠7 ∧ q%25≠18)
  have size : T.card≤23 := by decide
  have diag := diagonal_budget (M:=50) (t:=23) big (by decide) T R size (by
    intro x hx
    obtain ⟨xa,x7,x18⟩ := mem_filter.mp hx
    have ev := even x xa
    exact ⟨mem_range.mp (inside xa),x7,x18,adm x xa x xa,mem_filter.mpr
      ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),by omega,by omega,by omega⟩⟩)
  push_cast at diag
  have total := Deldor14.Erdos848Tenth.total_parts A
  change (A.card:ℝ) ≤ ((slice A 7).card:ℝ)+((slice A 18).card:ℝ)+(R.card:ℝ) at total
  change ((slice A 7).card:ℝ) ≤ (116/10000)*(N:ℝ) at h7
  change ((slice A 18).card:ℝ) ≤ (116/10000)*(N:ℝ) at h18
  have endp : (N:ℝ)=25*(k:ℝ)+7 := by dsimp [N]; push_cast; ring
  have nr : 400000000 ≤ (N:ℝ) := by exact_mod_cast big
  by_contra! bad
  have more : (k:ℝ)+1 ≤ (A.card:ℝ) := by exact_mod_cast (show k+1 ≤ A.card by omega)
  linarith only [diag,h7,h18,total,more,endp,nr]

end Deldor14.Erdos848OddPart

/- An unconditional threshold for Erdős 848 for all-odd sets for every N ≥ 400 million.
Mixed sets use the restricted diagonal and row sieves. Pure sets use the
Hall matching between the two exceptional residue classes. -/
namespace Deldor14.Erdos848OddPart
open Finset Erdos848
theorem endpoint_structured_400M (k : ℕ) (big : 400000000≤25*k+7) (A : Finset ℕ)
    (inside : A⊆range (25*k+7)) (adm : NonSquarefreeProductProp A) (shape : (∀x∈A,x%2=1) ∨ (∀x∈A,2∣x) ∨ (∃s, 2∣s ∧ ∀x∈outside A,x ≡ s [MOD 4])) : A.card≤k := by
  classical
  by_cases mixed : (outside A).Nonempty
  · rcases shape with odd | even | ⟨s,ev,same⟩
    · exact odd_mixed big A inside adm odd mixed
    · exact all_even_mixed big A inside adm mixed even
    · exact even_outside_mixed big A inside adm mixed s ev same
  let N := 25*k+7
  let X := slice A 18
  let Y := slice A 7
  let Γ := Deldor14.Erdos848Tenth.hood N X
  have baseX : X⊆Deldor14.Erdos848Tenth.side N 18 := by
    intro x hx
    obtain ⟨xa,eq⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨inside xa,eq⟩
  have hall : X.card≤Γ.card := Erdos848Pure.hall_400M k (by omega) X baseX
  have dis : Disjoint Γ Y := by
    apply disjoint_left.mpr
    intro a ag ay
    obtain ⟨_,b,bx,edge⟩ := mem_filter.mp ag
    exact adm a (mem_filter.mp ay).1 b (mem_filter.mp bx).1 edge
  have sub : Γ∪Y⊆Deldor14.Erdos848Tenth.side N 7 := union_subset (filter_subset ..) (by
    intro y hy
    obtain ⟨ya,eq⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨inside ya,eq⟩)
  have cap := card_le_card sub
  rw [card_union_of_disjoint dis,Deldor14.Erdos848Tenth.side_card k 7 (by decide)] at cap
  have no : outside A=∅ := not_nonempty_iff_eq_empty.mp mixed
  have q := Deldor14.Erdos848Tenth.total_parts A
  change (A.card:ℝ) ≤ (Y.card:ℝ)+(X.card:ℝ)+((outside A).card:ℝ) at q
  rw [no,card_empty,Nat.cast_zero,add_zero] at q
  have qr : A.card ≤ Y.card+X.card := by exact_mod_cast q
  omega

theorem effective_structured_400M (N : ℕ) (big : 400000000≤N) : ∀A⊆range N, NonSquarefreeProductProp A → ((∀x∈A,x%2=1) ∨ (∀x∈A,2∣x) ∨ (∃s, 2∣s ∧ ∀x∈outside A,x ≡ s [MOD 4])) → A.card ≤ (A₇ N).card := by
  intro A inside adm shape
  let k := (N+17)/25
  have up : N ≤ 25*k+7 := by dsimp [k]; omega
  have incl : A⊆range (25*k+7) := fun x hx=>mem_range.mpr ((mem_range.mp (inside hx)).trans_le up)
  have valid := endpoint_structured_400M k (big.trans up) A incl adm shape
  have size : (A₇ N).card=k := Erdos848Port.card_range_filter_mod25_eq 7 (by decide) N
  rw [size]
  exact valid
theorem effective_odd_400M (N : ℕ) (big : 400000000 ≤ N) : ∀A⊆range N, NonSquarefreeProductProp A → (∀x∈A,x%2=1) → A.card ≤ (A₇ N).card := by
  intro A inside adm odd
  exact effective_structured_400M N big A inside adm (Or.inl odd)
end Deldor14.Erdos848OddPart


namespace Deldor14.Erdos848Fifth
open Finset
def side (N r : ℕ) := (range N).filter (fun x=>x%25=r)
def hood (N : ℕ) (X : Finset ℕ) := (side N 7).filter (fun a=>∃b∈X,Squarefree (a*b+1))
theorem side_card (k r : ℕ) (hr : r=7 ∨ r=18) : (side (25*k+7) r).card=k := by
  rw [side,Erdos848Port.card_range_filter_mod25_eq _ (by omega)]
  rcases hr with rfl|rfl <;> omega
end Deldor14.Erdos848Fifth

/- The two-term inclusion-exclusion bound for four excluded classes. -/
namespace Deldor14.Erdos848Phase
open Finset
private theorem sieve_four {α : Type*} (S : Finset α) (A B C D : α→Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C] [DecidablePred D]
    (separate : ∀x∈S,A x → ¬B x) :
    ((S.filter (fun x=>¬A x ∧ ¬B x ∧ ¬C x ∧ ¬D x)).card:ℝ) +
      (S.filter A).card+(S.filter B).card+(S.filter C).card+(S.filter D).card ≤ 
      (S.card:ℝ)+(S.filter (fun x=>A x ∧ C x)).card+(S.filter (fun x=>B x ∧ C x)).card+
      (S.filter (fun x=>A x ∧ D x)).card+(S.filter (fun x=>B x ∧ D x)).card+
      (S.filter (fun x=>C x ∧ D x)).card := by
  classical
  have point (x) (hx : x∈S) :
      (if ¬A x ∧ ¬B x ∧ ¬C x ∧ ¬D x then 1 else 0) + (if A x then 1 else 0) +
      (if B x then 1 else 0) + (if C x then 1 else 0) + (if D x then 1 else 0) ≤ 
      (1:ℕ)+(if A x ∧ C x then 1 else 0)+(if B x ∧ C x then 1 else 0)+
      (if A x ∧ D x then 1 else 0)+(if B x ∧ D x then 1 else 0)+(if C x ∧ D x then 1 else 0) := by
    have dis := separate x hx
    by_cases a : A x <;> by_cases b : B x <;> by_cases c : C x <;> by_cases d : D x <;> simp_all
  have sum := Finset.sum_le_sum point
  simp only [sum_add_distrib,sum_boole,sum_const,smul_eq_mul,mul_one] at sum
  exact_mod_cast sum

theorem phase_one {N p u : ℕ} (hp : p.Prime) (large : 13 ≤ p) :
    let S := prog N (p^2) u
    ((S.filter (fun x=>x%25≠7 ∧ x%25≠18 ∧ ¬6∣x ∧ ¬14∣x)).card:ℝ) ≤ 
      (761/1050:ℝ)*((N:ℝ)/(p:ℝ)^2) + 10 := by
  classical
  let q:=p^2
  have qp : 0 < q := pow_pos hp.pos _
  let S := prog N q u
  let F (m r : ℕ) := S.filter (fun x=>x ≡ r [MOD m])
  have fdef (m r) : F m r = S ∩ prog N m r := by
    ext x
    simp only [F,S,prog,mem_inter,mem_filter,mem_range]
    tauto
  have cop {m : ℕ} (hm : ¬p∣m) : q.Coprime m := by
    exact (hp.coprime_iff_not_dvd.mpr hm).pow_left 2
  have small (m : ℕ) (pos : 0 < m) (less : m < p) := cop (fun dv : p∣m=>less.not_ge (Nat.le_of_dvd pos dv))
  have c2 := small 2 (by decide) (by omega)
  have c3 := small 3 (by decide) (by omega)
  have c5 := small 5 (by decide) (by omega)
  have c7 := small 7 (by decide) (by omega)
  have c6 : q.Coprime 6 := c2.mul_right c3
  have c14 : q.Coprime 14 := c2.mul_right c7
  have c25 : q.Coprime 25 := c5.mul_right c5
  have one (m r) (pos : 0 < m) (co : q.Coprime m) :
      ((N:ℝ)/(q:ℝ))/(m:ℝ)-1 ≤ ((F m r).card:ℝ) ∧
      ((F m r).card:ℝ) ≤ ((N:ℝ)/(q:ℝ))/(m:ℝ)+1 := by
    rw [fdef]
    simpa only [div_div] using crt_bounds (N:=N) (r:=u) (s:=r) co qp pos
  have sx := (prog_bounds N q u qp).2
  have lower7 := (one 25 7 (by decide) c25).1
  have lower18 := (one 25 18 (by decide) c25).1
  have lower6 := (one 6 0 (by decide) c6).1
  have lower14 := (one 14 0 (by decide) c14).1
  have pair (m r n t) (mn : Nat.Coprime m n) (c : q.Coprime (m*n)) (pos : 0 < m*n) :
      ((S.filter (fun x=>x ≡ r [MOD m] ∧ x ≡ t [MOD n])).card:ℝ) ≤ ((N:ℝ)/(q:ℝ))/(m*n:ℕ)+1 := by
    have sub : S.filter (fun x=>x ≡ r [MOD m] ∧ x ≡ t [MOD n]) ⊆ F (m*n) (Nat.chineseRemainder mn r t) := by
      intro x hx
      obtain ⟨xs,a,b⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨xs,Nat.chineseRemainder_modEq_unique mn a b⟩
    exact (Nat.cast_le.mpr (card_le_card sub)).trans (one (m*n) (Nat.chineseRemainder mn r t) pos c).2
  have a := pair 25 7 6 0 (by decide) (c25.mul_right c6) (by decide)
  have b := pair 25 18 6 0 (by decide) (c25.mul_right c6) (by decide)
  have c := pair 25 7 14 0 (by decide) (c25.mul_right c14) (by decide)
  have d := pair 25 18 14 0 (by decide) (c25.mul_right c14) (by decide)
  have meet : S.filter (fun x=>x ≡ 0 [MOD 6] ∧ x ≡ 0 [MOD 14]) ⊆ F 42 0 := by
    intro x hx
    obtain ⟨xs,hh,jj⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨xs,by change x%6=0 at hh; change x%14=0 at jj; change x%42=0; omega⟩
  have e := (Nat.cast_le (α:=ℝ)).mpr (card_le_card meet) |>.trans (one 42 0 (by decide) (c6.mul_right c7)).2
  have comb := sieve_four S (fun x=>x≡7 [MOD 25]) (fun x=>x≡18 [MOD 25]) (fun x=>x≡0 [MOD 6]) (fun x=>x≡0 [MOD 14])
    (fun x _ h1 h2=>by change x%25=7 at h1; change x%25=18 at h2; omega)
  have good : S.filter (fun x=>¬(x≡7 [MOD 25]) ∧ ¬(x≡18 [MOD 25]) ∧ ¬(x≡0 [MOD 6]) ∧ ¬(x≡0 [MOD 14])) =
              S.filter (fun x=>x%25≠7 ∧ x%25≠18 ∧ ¬6∣x ∧ ¬14∣x) := by
    ext x; simp only [mem_filter,Nat.modEq_zero_iff_dvd]; rfl
  rw [good] at comb
  change ((S.filter _).card:ℝ)+(F 25 7).card+(F 25 18).card+(F 6 0).card+(F 14 0).card ≤ _ at comb
  change ((S.filter _).card:ℝ) ≤ (761/1050)*((N:ℝ)/(p:ℝ)^2)+10
  have pq : (q:ℝ)=(p:ℝ)^2 := by simp [q]
  rw [←pq]
  change (S.card:ℝ) ≤ (N:ℝ)/(q:ℝ)+1 at sx
  norm_num only [Nat.reduceMul,Nat.cast_ofNat] at a b c d
  linarith only [sx,lower7,lower18,lower6,lower14,a,b,c,d,e,comb]
end Deldor14.Erdos848Phase

/- Complementary-divisor estimates for the 5 to 10 billion interval. -/
namespace Erdos848Five
open Erdos848Gap Finset
private theorem count_by_theta_refined (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M.primeCounting+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ M.primesLE := by
    intro q hq
    obtain ⟨hp,hle⟩ := Finset.mem_filter.mp hq
    exact Nat.mem_primesLE.mpr ⟨hle,(Nat.mem_primesLE.mp hp).2⟩
  have hsmall := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at hsmall
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M.primeCounting := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M.primeCounting : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


private theorem log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num


set_option maxRecDepth 1500 in
private theorem count_by_theta (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ Finset.Icc 1 M := by
    intro q hq
    obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, hle⟩
  have hsmall : small.card ≤ M := by simpa using Finset.card_le_card sub
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


theorem mixed60_count {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<60*p n) : S.card ≤ 4620*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 10*p n≤N)
  let large := S.filter (fun n => ¬ 10*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/10 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<3600*b := by
    exact link n (smallS hn) 60 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<100*b := by
    exact link n (largeS hn) 10 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 3600*b/N
  let W := 2*(N/10)/b
  have pd : P*N ≤ 3600*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/10) := Nat.div_mul_le_self _ _
  have u : 10*(N/10)≤N := by omega
  have num : 5*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤3600 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤720 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 3600*b*W=3600*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 720 num)
    have l1 : (P*W)*N ≤ 720*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 4320 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 4320*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 100*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 100*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤100 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 200 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 100 kd
    have mul : (Q*K)*N ≤ 200*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 300 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 300*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

private theorem mixed60_error {N b : ℕ} (big : 5000000000≤N) (upper : N≤10000000000) (bp : 0<b) (bn : b≤N)
    {z : ℕ} (bound : z≤4620*(2*2^b.primeFactors.card)) : (if 6∣b then 528 else 1056)*z≤N := by
  split_ifs with six
  · have h := Erdos848Lower.support10 b bp (by omega)
    omega
  · by_cases even : 2∣b
    · have n3 : ¬3∣b := fun d=>six ((by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd even d)
      have h := Erdos848Ten.without3 b bp ((bn.trans upper).trans (by decide)) n3
      omega
    · have h := Erdos848Ten.without2 b bp ((bn.trans upper).trans (by decide)) even
      omega
theorem large_mixed_60 {N b : ℕ} (big : 5000000000 ≤ N) (upper : N≤10000000000) (bN : b < N)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 60*p ∧ p^2 ∣ b*n+1) :
    (if 6∣b then 528 else 1056)*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 60*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    exact mixed60_error big upper bp bN.le (mixed60_count bp bN.le S p d eq (fun n hn => (info n hn).1) link
      (fun n hn => (info n hn).2.1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp

theorem small_primes_60 {N : ℕ} (big : 5000000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 60*p ≤ N) :
    600 * Q.card ≤ N := by
  let X := N/60
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta_refined X (2^21) 21 (by decide) (log_nat_two_pow 21)
  have inner := count_by_theta (2^21) (2^11) 11 (by decide) (log_nat_two_pow 11)
  have trunc : 60*X≤N := by dsimp [X]; omega
  norm_num only [Nat.reducePow] at weight inner
  omega

theorem small_primes_360 {N : ℕ} (big : 5000000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 360*p ≤ N) :
    3100 * Q.card ≤ N := by
  let X := N/360
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta_refined X (2^19) 19 (by decide) (log_nat_two_pow 19)
  have inner := count_by_theta (2^19) (2^11) 11 (by decide) (log_nat_two_pow 11)
  have trunc : 360*X≤N := by dsimp [X]; omega
  norm_num only [Nat.reducePow] at weight inner
  omega

theorem large_mixed_60_all {N b : ℕ} (big : 5000000000≤N) (bn : b<N)
    (S : Finset ℕ) (found : ∀n∈S,n<N ∧ ∃p : ℕ,p≤N ∧ N<60*p ∧ p^2∣b*n+1) :
    (if 6∣b then 528 else 1056)*S.card≤N := by
  by_cases low : N≤10000000000
  · exact large_mixed_60 big low bn S found
  · have h := Erdos848Ten.large_mixed_72_all (by omega : 10000000000≤N) bn S (by
      intro n hn
      obtain ⟨nr,p,pn,cut,div⟩ := found n hn
      exact ⟨nr,p,pn,by omega,div⟩)
    split_ifs at h ⊢ <;> omega
end Erdos848Five

/- Uniform bounds on nonsquarefree products along either residue class. -/
namespace Erdos848Five
open Finset Erdos848Port

private theorem prime_sum (N b : ℕ) (P : Finset ℕ) (no5 : P ⊆ no5PrimesUpTo N)
    (no2 : 2 ∣ b → P ⊆ offPrimesUpTo N) :
    (∑ p ∈ P, (1:ℝ)/(25*(p:ℝ)^2)) ≤ (if 2 ∣ b then 163 else 413)/25000 := by
  have h : (∑ p ∈ P,(1:ℚ)/(p:ℚ)^2) ≤ (if 2 ∣ b then 163 else 413)/1000 := by
    by_cases h : 2 ∣ b
    · rw [if_pos h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (no2 h) (fun i _ _ => by positivity)).trans
        (sum_offPrimesUpTo_le N)
    · rw [if_neg h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg no5 (fun i _ _ => by positivity)).trans
        (sum_no5PrimesUpTo_le N)
  have cast := (Rat.cast_le (K:=ℝ)).mpr h
  simp only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,
    apply_ite Rat.cast,Rat.cast_ofNat] at cast
  have f (p : ℕ) : (1:ℝ)/(25*(p:ℝ)^2) = (1/25) * (1/(p:ℝ)^2) := by ring
  simp only [f,←Finset.mul_sum]
  by_cases z : 2 ∣ b <;> simp [z] at cast ⊢ <;> linarith only [cast]

private theorem weighted_bound {N b r C lo hi : ℕ} (largeN : 100 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1)
    (small : ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q,C*p≤N) → lo*Q.card≤N)
    (large : ∀ T : Finset ℕ, (∀ n∈T,n<N ∧ ∃ p : ℕ,p≤N ∧ N<C*p ∧ p^2∣b*n+1) → hi*T.card≤N)
    (lop : 0<lo) (hip : 0<hi) (w : ℝ)
    (limit : ∀ Q : Finset ℕ, Q ⊆ no5PrimesUpTo N → (2∣b → Q ⊆ offPrimesUpTo N) →
      (3∣b → 3∉Q) → (7∣b → 7∉Q) → ∑ p∈Q,(1:ℝ)/(25*(p:ℝ)^2) ≤ w) :
    (S.card:ℝ) ≤ N*w + (N:ℝ)/lo + (N:ℝ)/hi := by
  classical
  let P := (no5PrimesUpTo N).filter (fun p => ¬p∣b)
  let Q := P.filter (fun p => C*p≤N)
  let R := P.filter (fun p => N<C*p)
  let B (p : ℕ) := (range N).filter (fun n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
  have no5 : P ⊆ no5PrimesUpTo N := Finset.filter_subset .. 
  have no2 (ev : 2 ∣ b) : P ⊆ offPrimesUpTo N := by
    intro p hp
    obtain ⟨mem,div⟩ := Finset.mem_filter.mp hp
    obtain ⟨pm,p5⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨pm,fun h => div (h ▸ ev),p5⟩
  have prime {p : ℕ} (h : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).2
  have bound {p : ℕ} (h : p ∈ P) : p ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).1)
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    obtain ⟨p,hp,p5,pdv⟩ := prime_square_exists_ne5 (bad n hn) (h25 n hn)
    have nN := Finset.mem_range.mp (inRange hn)
    have pred := Nat.mul_le_mul (Nat.le_pred_of_lt bn) (Nat.le_pred_of_lt nN)
    have le := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) ((Nat.add_le_add_right pred 1).trans_lt
      (sq_pred_add_one_lt_sq N largeN)) pdv
    have pnd : ¬p∣b := by
      intro h
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left h n)).mp
        (Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) pdv))
    have mem : p ∈ P := by
      simp [P,no5PrimesUpTo,primesUpTo,hp,Nat.lt_succ_of_le le,p5,pnd]
    have nb : n ∈ B p := Finset.mem_filter.mpr ⟨inRange hn,res n hn,pdv⟩
    by_cases h : C*p ≤ N
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,h⟩,nb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,Nat.lt_of_not_ge h⟩,nb⟩)
  have cards : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (card_le_card cover).trans (card_union_le ..)
  have sub : Q ⊆ P := Finset.filter_subset ..
  have lc := small Q (fun _ h => prime (sub h)) (fun _ h => (mem_filter.mp h).2)
  have hc := large (R.biUnion B) (by
    intro n hn
    obtain ⟨p,hp,nb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨nN,pdv⟩ := Finset.mem_filter.mp nb
    exact ⟨Finset.mem_range.mp nN,p,bound (mem_filter.mp hp).1,(mem_filter.mp hp).2,pdv.2⟩)
  have first := sieve_set_card_bound N 25 Q (Q.biUnion B) (fun p n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
    Subset.rfl (fun p hp => off_count_modEq25_le' N p b r (prime (sub hp)) (mem_filter.mp (no5 (sub hp))).2)
  have est := limit Q (sub.trans no5) (fun he => sub.trans (no2 he)) (fun dv h => (mem_filter.mp (sub h)).2 dv) (fun dv h => (mem_filter.mp (sub h)).2 dv)
  have weight := mul_le_mul_of_nonneg_left est (show 0 ≤ (N:ℝ) by positivity)
  have countR : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast cards
  have lcr : (Q.card:ℝ) ≤ (N:ℝ)/lo := by
    apply (le_div_iff₀ (by exact_mod_cast lop)).mpr
    rw [mul_comm]
    exact_mod_cast lc
  have hcr : ((R.biUnion B).card:ℝ) ≤ (N:ℝ)/hi := by
    apply (le_div_iff₀ (by exact_mod_cast hip)).mpr
    rw [mul_comm]
    exact_mod_cast hc
  linarith only [first,weight,countR,lcr,hcr]


theorem bad_five {N b r : ℕ} (big : 5000000000≤N) (bn : b<N)
    (S : Finset ℕ) (inRange : S⊆range N) (res : ∀n∈S,n ≡ r [MOD 25])
    (bad : ∀n∈S,¬Squarefree (b*n+1)) (h25 : ∀n∈S,¬25∣b*n+1) :
    (S.card:ℝ) ≤ (N:ℝ)*((if 2∣b then 163 else 413)/25000 - (if 3∣b then 1/225 else 0)) +
       (N:ℝ)/(if 6∣b then 280 else 382) := by
  have bound := weighted_bound (by omega : 100≤N) bn S inRange res bad h25
    (small_primes_60 big) (large_mixed_60_all big bn) (by decide)
    (by split_ifs <;> decide)
    (((if 2∣b then 163 else 413)/25000:ℝ) - (if 3∣b then 1/225 else 0)) (by
      intro Q no5 no2 no3 _
      by_cases tri : 3∣b
      · rw [if_pos tri]
        have h3 : 3∈primesUpTo N := by simp [primesUpTo,Nat.prime_three,show 3<N+1 by omega]
        have in5 : insert 3 Q ⊆ no5PrimesUpTo N := Finset.insert_subset (mem_filter.mpr ⟨h3,by decide⟩) no5
        have in2 (ev : 2∣b) : insert 3 Q ⊆ offPrimesUpTo N := Finset.insert_subset (mem_filter.mpr ⟨h3,by decide⟩) (no2 ev)
        have e := prime_sum N b (insert 3 Q) in5 in2
        rw [sum_insert (no3 tri)] at e
        norm_num only [Nat.cast_ofNat] at e
        linarith only [e]
      · rw [if_neg tri,sub_zero]
        exact prime_sum N b Q no5 no2)
  by_cases six : 6∣b <;> simp only [six,if_true,if_false,Nat.cast_ofNat] at bound ⊢ <;>
    linarith only [bound,Nat.cast_nonneg (α:=ℝ) N]
theorem bad_five_fourteen {N b r : ℕ} (big : 5000000000≤N) (bn : b<N)
    (S : Finset ℕ) (inRange : S⊆range N) (res : ∀n∈S,n ≡ r [MOD 25])
    (bad : ∀n∈S,¬Squarefree (b*n+1)) (h25 : ∀n∈S,¬25∣b*n+1)
    (fourteen : 14∣b) (not6 : ¬6∣b) :
    (S.card:ℝ)≤(833/100000)*(N:ℝ) := by
  have even : 2∣b := (by decide : 2∣14).trans fourteen
  have seven : 7∣b := (by decide : 7∣14).trans fourteen
  have h := weighted_bound (by omega : 100≤N) bn S inRange res bad h25
    (small_primes_60 big) (large_mixed_60_all big bn) (by decide) (by split_ifs; decide)
    (163/25000-1/1225) (by
      intro Q no5 no2 _ no7
      have h7 : 7∈primesUpTo N := by simp [primesUpTo,show Nat.Prime 7 by decide,show 7<N+1 by omega]
      have in5 : insert 7 Q ⊆ no5PrimesUpTo N := insert_subset (mem_filter.mpr ⟨h7,by decide⟩) no5
      have in2 : insert 7 Q ⊆ offPrimesUpTo N := insert_subset (mem_filter.mpr ⟨h7,by decide⟩) (no2 even)
      have z := prime_sum N b (insert 7 Q) in5 (fun _=>in2)
      rw [sum_insert (no7 seven),if_pos even] at z
      norm_num only [Nat.cast_ofNat] at z
      linarith only [z])
  rw [if_neg not6] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]
end Erdos848Five

/- Mixed-class degree bound after specifying the residue modulo four. -/
namespace Erdos848Five
open Finset Erdos848Port

theorem bad_five_100 {N b r s : ℕ} (big : 5000000000≤N) (bn : b < N) (odd : ¬2∣b)
    (S : Finset ℕ) (inRange : S ⊆ range N)
    (res : ∀ n∈S, n ≡ r [MOD 25]) (res4 : ∀ n∈S, n ≡ s [MOD 4])
    (bad : ∀ n∈S, ¬Squarefree (b*n+1))
    (h4 : ∀ n∈S, ¬4∣b*n+1) (h25 : ∀ n∈S, ¬25∣b*n+1) :
    (S.card:ℝ) ≤ (N:ℝ)*(163/100000 - (if 3∣b then 1/900 else 0))+(N:ℝ)/382 := by
  classical
  let P := (offPrimesUpTo N).filter (fun p=>¬p∣b)
  let Q := P.filter (fun p => 60*p≤N)
  let R := P.filter (fun p => N<60*p)
  let B (p : ℕ) := (range N).filter (fun n => n ≡ r [MOD 25] ∧ n ≡ s [MOD 4] ∧ p^2∣b*n+1)
  have prime {p : ℕ} (h : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).2
  have bound {p : ℕ} (h : p ∈ P) : p ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1).1)
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    obtain ⟨p,hp,p5,pdv⟩ := prime_square_exists_ne5 (bad n hn) (h25 n hn)
    have nN := Finset.mem_range.mp (inRange hn)
    have pred := Nat.mul_le_mul (Nat.le_pred_of_lt bn) (Nat.le_pred_of_lt nN)
    have le := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) ((Nat.add_le_add_right pred 1).trans_lt
      (sq_pred_add_one_lt_sq N (by omega))) pdv
    have p2 : p ≠ 2 := fun e => h4 n hn (by simpa [e] using pdv)
    have pnd : ¬p∣b := by
      intro h
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left h n)).mp (Nat.dvd_of_pow_dvd (by decide : 1≤2) pdv))
    have mem : p ∈ P := by simp [P,offPrimesUpTo,primesUpTo,hp,Nat.lt_succ_of_le le,p5,p2,pnd]
    have nb : n ∈ B p := Finset.mem_filter.mpr ⟨inRange hn,res n hn,res4 n hn,pdv⟩
    by_cases h : 60*p ≤ N
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,h⟩,nb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,Nat.lt_of_not_ge h⟩,nb⟩)
  have cards : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (card_le_card cover).trans (card_union_le ..)
  have sub : Q ⊆ P := Finset.filter_subset ..
  have lc := small_primes_60 big Q (fun _ h => prime (sub h)) (fun _ h => (mem_filter.mp h).2)
  have hc := large_mixed_60_all big bn (R.biUnion B) (by
    intro n hn
    obtain ⟨p,hp,nb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨nN,pdv⟩ := Finset.mem_filter.mp nb
    exact ⟨Finset.mem_range.mp nN,p,bound (mem_filter.mp hp).1,(mem_filter.mp hp).2,pdv.2.2⟩)
  have first := sieve_set_card_bound N 100 Q (Q.biUnion B) (fun p n => n ≡ r [MOD 25] ∧ n ≡ s [MOD 4] ∧ p^2∣b*n+1)
    Subset.rfl (fun p hp => off_count_modEq100_le' N p b r s (prime (sub hp)) (mem_filter.mp (mem_filter.mp (sub hp)).1).2.1 (mem_filter.mp (mem_filter.mp (sub hp)).1).2.2)
  have off : Q ⊆ offPrimesUpTo N := sub.trans (filter_subset ..)
  have est : (∑ p∈Q,(1:ℝ)/(100*(p:ℝ)^2)) ≤ 163/100000 - (if 3∣b then 1/900 else 0) := by
    have general (G : Finset ℕ) (inc : G ⊆ offPrimesUpTo N) : (∑p∈G,(1:ℝ)/(100*(p:ℝ)^2)) ≤ 163/100000 := by
      have sumRat : (∑ p∈G,(1:ℚ)/(p:ℚ)^2) ≤ 163/1000 :=
        (Finset.sum_le_sum_of_subset_of_nonneg inc (fun p _ _ => by positivity)).trans (sum_offPrimesUpTo_le N)
      have cast := (Rat.cast_le (K:=ℝ)).mpr sumRat
      simp only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] at cast
      have f (p : ℕ) : (1:ℝ)/(100*(p:ℝ)^2) = (1/100)*(1/(p:ℝ)^2) := by ring
      simp only [f,←Finset.mul_sum]
      linarith only [cast]
    by_cases tri : 3∣b
    · have missing : 3∉Q := fun h=>(mem_filter.mp (sub h)).2 tri
      have h3 : 3∈primesUpTo N := by simp [primesUpTo,Nat.prime_three,show 3<N+1 by omega]
      have ins := general (insert 3 Q) (insert_subset (mem_filter.mpr ⟨h3,by decide⟩) off)
      rw [sum_insert missing] at ins
      rw [if_pos tri]
      norm_num only [Nat.cast_ofNat] at ins
      linarith only [ins]
    · rw [if_neg tri,sub_zero]
      exact general _ off
  have weight := mul_le_mul_of_nonneg_left est (show 0 ≤ (N:ℝ) by positivity)
  have countR : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast cards
  have lcr : (Q.card:ℝ) ≤ (N:ℝ)/600 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    rw [mul_comm]
    exact_mod_cast lc
  have notsix : ¬6∣b := fun h=>odd ((by decide : 2∣6).trans h)
  rw [if_neg notsix] at hc
  have hcr : ((R.biUnion B).card:ℝ) ≤ (N:ℝ)/1056 := by
    apply (le_div_iff₀ (by norm_num)).mpr
    rw [mul_comm]
    exact_mod_cast hc
  linarith only [first,weight,countR,lcr,hcr,Nat.cast_nonneg (α:=ℝ) N]

end Erdos848Five


/- Uniform diagonal sieve on a restricted set of residue classes. The
large-square argument is the Pell spacing estimate of Erdős848Gap; the
two-root split is the diagonal sieve of Erdos848Port. -/
namespace Deldor14.Erdos848Fifth
open Finset Erdos848Port
private theorem at_most_one_large_diagonal_root (N p : ℕ) (hp : p.Prime) (hmod : p%4=1)
    (large : 2*N ≤ p^2) (S : Finset ℕ) (inside : ∀ n ∈ S, n < N ∧ p^2 ∣ n^2+1) :
    S.card ≤ 1 := by
  obtain ⟨r,t,opposite,_,_,_,allRoots⟩ := two_roots_mod_p_squared p hp hmod
  have nz : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have root (n : ℕ) (hn : n ∈ S) : (n : ZMod (p^2)) = r ∨ (n : ZMod (p^2)) = -r := by
    have eq0 := (ZMod.natCast_eq_zero_iff (n^2+1) (p^2)).mpr (inside n hn).2
    have eq1 : (n : ZMod (p^2))^2+1 = 0 := by exact_mod_cast eq0
    simpa only [opposite] using allRoots _ (eq_neg_of_add_eq_zero_left eq1)
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have xb := (inside x hx).1
  have yb := (inside y hy).1
  have cases : (x : ZMod (p^2)) = y ∨ (x : ZMod (p^2)) + y = 0 := by
    rcases root x hx with h | h <;> rcases root y hy with g | g <;> simp [h,g]
  rcases cases with h | h
  · have eq := (ZMod.natCast_eq_natCast_iff x y (p^2)).mp h
    change x%(p^2)=y%(p^2) at eq
    simpa only [Nat.mod_eq_of_lt (show x<p^2 by omega),
      Nat.mod_eq_of_lt (show y<p^2 by omega)] using eq
  · have eq : (p^2) ∣ x+y := (ZMod.natCast_eq_zero_iff (x+y) (p^2)).mp (by simpa using h)
    have h0 := Nat.mod_eq_zero_of_dvd eq
    rw [Nat.mod_eq_of_lt (by omega)] at h0
    omega

private theorem diagonal_partial (N k d : ℕ) (P S : Finset ℕ) (B : ℕ → Finset ℕ)
    (primes : P ⊆ diagPrimesUpTo N) (covered : S ⊆ P.biUnion B)
    (old : ∀ p ∈ P, (B p).card ≤ d*(N/(k*p^2)+1))
    (inside : ∀ p, ∀n∈B p, n < N ∧ p^2 ∣ n^2+1) :
    (S.card : ℝ) ≤ (d:ℝ)*((N : ℝ) * (∑ p ∈ P, (1 : ℝ)/(k*(p:ℝ)^2))) +
      (P.card : ℝ) + (d:ℝ)*(((2*N).sqrt : ℝ)/4+2) := by
  classical
  let small := P.filter (· ≤ (2*N).sqrt)
  have point (p : ℕ) (hp : p ∈ P) :
      ((B p).card : ℝ) ≤ ((d:ℝ)*(N : ℝ))*((1 : ℝ)/(k*(p:ℝ)^2)) +
        (if p ≤ (2*N).sqrt then (d : ℝ) else 0) + 1 := by
    by_cases cut : p ≤ (2*N).sqrt
    · rw [if_pos cut]
      have denom := Nat.cast_div_le (α := ℝ) (m := N) (n := k*p^2)
      push_cast at denom
      have o : ((B p).card : ℝ) ≤ (d:ℝ)*(((N/(k*p^2) : ℕ):ℝ)+1) := by exact_mod_cast old p hp
      simp only [div_eq_mul_inv,one_mul] at denom ⊢
      have weighted := mul_le_mul_of_nonneg_left denom (Nat.cast_nonneg (α:=ℝ) d)
      linarith only [o,weighted]
    · rw [if_neg cut]
      have prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (primes hp)).1).2
      have mod4 : p%4=1 := (Finset.mem_filter.mp (primes hp)).2.1
      have lim : 2*N ≤ p^2 := (Nat.sqrt_lt'.mp (lt_of_not_ge cut)).le
      have o : ((B p).card : ℝ) ≤ 1 := by exact_mod_cast at_most_one_large_diagonal_root N p prime mod4 lim (B p) (inside p)
      have hpos : 0 ≤ ((d:ℝ)*(N : ℝ))*((1 : ℝ)/(k*(p:ℝ)^2)) := by positivity
      linarith only [o,hpos]
  have total : S.card ≤ ∑ p ∈ P, (B p).card :=
    (Finset.card_le_card covered).trans Finset.card_biUnion_le
  have totalR : (S.card : ℝ) ≤ ∑ p ∈ P, ((B p).card : ℝ) := by exact_mod_cast total
  have upper := totalR.trans (Finset.sum_le_sum point)
  have count : (∑ p ∈ P, if p ≤ (2*N).sqrt then (d : ℝ) else 0) = (small.card : ℝ)*(d:ℝ) := by
    rw [← Finset.sum_filter]
    simp [small]
  have sub : small ⊆ (range ((2*N).sqrt+1)).filter (fun p=>p ≡ 1 [MOD 4]) := by
    intro p hp
    obtain ⟨pm,lim⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le lim),(mem_filter.mp (primes pm)).2.1⟩
  have cs := (card_le_card sub).trans (card_filter_mod_eq_le ((2*N).sqrt+1) 4 1)
  have cs' : 4*small.card≤(2*N).sqrt+5 := by omega
  have cR : 4*(small.card:ℝ)≤((2*N).sqrt:ℝ)+5 := by exact_mod_cast cs'
  have csr : (small.card:ℝ)≤((2*N).sqrt:ℝ)/4+2 := by linarith only [cR]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,count,Finset.sum_const, nsmul_eq_mul,
    mul_one] at upper
  linarith only [upper,mul_le_mul_of_nonneg_left csr (Nat.cast_nonneg (α:=ℝ) d)]


private lemma diag_by_mod (N M p t : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hcop : Nat.Coprime M (p^2)) :
    ((Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      2 * (N / (M * p ^ 2) + 1) := by
  classical
  obtain ⟨r₁, r₂, hr⟩ :
      ∃ r₁ r₂ : ZMod (p ^ 2),
        r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧ ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
    obtain ⟨r,t,_,rest⟩ := two_roots_mod_p_squared p hp hmod
    exact ⟨r,t,rest⟩
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  let S₁ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ n ≡ r₁.val [MOD p ^ 2])
  let S₂ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ n ≡ r₂.val [MOD p ^ 2])
  have hsubset : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    simp [S, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hdiv : (p ^ 2 : ℕ) ∣ n ^ 2 + 1 := hn.2.2
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) (p ^ 2)).2 hdiv
    have hsq : (n : ZMod (p ^ 2)) ^ 2 = (-1 : ZMod (p ^ 2)) := by
      have : (n : ZMod (p ^ 2)) ^ 2 + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
      simpa using (eq_neg_of_add_eq_zero_left this)
    have hcases : (n : ZMod (p ^ 2)) = r₁ ∨ (n : ZMod (p ^ 2)) = r₂ := hr.2.2.2 _ hsq
    cases hcases with
    | inl hn1 =>
        refine Or.inl ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₁.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₁ := hn1
            _ = (r₁.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₁.val (p ^ 2)).1 hcast
    | inr hn2 =>
        refine Or.inr ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₂.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₂ := hn2
            _ = (r₂.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₂.val (p ^ 2)).1 hcast
  have hcard : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsubset
  have hunion : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
  have hS₁ : S₁.card ≤ N / (M * p ^ 2) + 1 := by
    simpa [S₁, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N M (p ^ 2) t r₁.val hcop)
  have hS₂ : S₂.card ≤ N / (M * p ^ 2) + 1 := by
    simpa [S₂, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N M (p ^ 2) t r₂.val hcop)
  have : S.card ≤ (N / (M * p ^ 2) + 1) + (N / (M * p ^ 2) + 1) :=
    le_trans (le_trans hcard hunion) (add_le_add hS₁ hS₂)
  simpa [S, two_mul] using this

private theorem diagonal_prime {N x : ℕ} (big : 100≤N) (hx : x<N)
    (x7 : x%25≠7) (x18 : x%25≠18) (diag : ¬Squarefree (x*x+1)) :
    ∃p∈diagPrimesUpTo N, p^2 ∣ x^2+1 := by
  obtain ⟨p,prime,sq⟩ := prime_square_exists_ne5 (n:=x^2+1) (by simpa [pow_two] using diag)
    (not_dvd_25_sq_add_one_of_mod_ne x ⟨x7,x18⟩)
  obtain ⟨not5,div⟩ := sq
  have not2 : p≠2 := by
    rintro rfl
    exact not_dvd_four_sq_add_one x div
  have mod4 := prime_sq_divides_implies_one_mod_four p x prime (by have := prime.two_le; omega) div
  have ge := prime_ge_13_of_mod4_one_ne5 p prime mod4 not5
  have lt : x^2+1 < N^2 := (Nat.add_le_add_right (Nat.pow_le_pow_left (show x≤N-1 by omega) 2) 1).trans_lt
    (by simpa only [pow_two] using sq_pred_add_one_lt_sq N big)
  have pn := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) lt div
  exact ⟨p,by simp [diagPrimesUpTo,primesUpTo,Nat.lt_succ_of_le pn,prime,mod4,ge],div⟩

/-- A class-restricted diagonal estimate, with the very-large-prime
remainder paid only once across all permitted residue classes. -/
theorem diagonal_budget {N M t : ℕ} (big : 5000000000≤N) (mchoice : M=25 ∨ M=50 ∨ M=150 ∨ (0<M ∧ M≤6))
    (T S : Finset ℕ) (size : T.card≤t)
    (info : ∀ x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1) ∧ x%M∈T) :
    (S.card:ℝ) ≤ (2*(t:ℝ))*(N:ℝ)*(5/359)/(M:ℝ) +
       (N:ℝ)/3100 + (2*(t:ℝ))*(N:ℝ)/198000 + (N:ℝ)/4000 := by
  classical
  let P := (diagPrimesUpTo N).filter (fun p=>360*p≤N)
  let B (p : ℕ) := S.filter (fun x=>p^2∣x^2+1)
  let low := P.biUnion B
  let high := S \ low
  have inp (p) (hp : p∈P) := (mem_filter.mp hp).1
  have prime (p) (hp : p∈P) : p.Prime := (mem_filter.mp (mem_filter.mp (inp p hp)).1).2
  have prop (p) (hp : p∈P) : p%4=1 ∧ 13≤p := (mem_filter.mp (inp p hp)).2
  have inside (p n) (hn : n∈B p) : n<N ∧ p^2∣n^2+1 :=
    ⟨(info n (mem_filter.mp hn).1).1,(mem_filter.mp hn).2⟩
  have capHigh := Erdos848Gap.large_diagonal_360 (by omega : 4665600000≤N) high (by
    intro x hx
    obtain ⟨xS,xL⟩ := mem_sdiff.mp hx
    obtain ⟨xn,x7,x18,di,_⟩ := info x xS
    obtain ⟨p,mem,div⟩ := diagonal_prime (by omega) xn x7 x18 di
    have pn := mem_range.mp (mem_filter.mp (mem_filter.mp mem).1).1
    refine ⟨xn,p,by omega,?_,div⟩
    by_contra! small
    exact xL (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,small⟩,mem_filter.mpr ⟨xS,div⟩⟩))
  have capP := Erdos848Five.small_primes_360 big P prime (by
    intro p hp
    have h := (mem_filter.mp hp).2
    omega)
  have points (p) (hp : p∈P) : (B p).card ≤ (2*t)*(N/(M*p^2)+1) := by
    let frac (r) := (range N).filter (fun x=>x ≡ r [MOD M] ∧ p^2∣x^2+1)
    have each (r) (_ : r∈T) : (frac r).card≤2*(N/(M*p^2)+1) := by
      have pp := prop p hp
      apply diag_by_mod _ _ _ _ (prime p hp) pp.1
      rcases mchoice with rfl|rfl|rfl|⟨pos,small⟩
      · exact coprime_25_pow_two_of_prime_ne5 p (prime p hp) (by omega)
      · exact coprime_50_pow_two_of_prime_ne2_ne5 p (prime p hp) (by omega) (by omega)
      · have cp6 := ((prime p hp).coprime_iff_not_dvd.mpr (fun dv=>(not_le_of_gt (by omega : 6<p)) (Nat.le_of_dvd (by decide : 0<6) dv))).symm.pow_right 2
        exact Nat.Coprime.mul_left cp6 (coprime_25_pow_two_of_prime_ne5 p (prime p hp) (by omega))
      · exact ((prime p hp).coprime_iff_not_dvd.mpr (fun dv=>(not_le_of_gt (by omega : M<p)) (Nat.le_of_dvd pos dv))).symm.pow_right _
    have subset : B p ⊆ T.biUnion frac := by
      intro x hx
      obtain ⟨sx,div⟩ := mem_filter.mp hx
      obtain ⟨xn,_,_,_,xr⟩ := info x sx
      exact mem_biUnion.mpr ⟨x%M,xr,mem_filter.mpr ⟨mem_range.mpr xn,by simp [Nat.ModEq],div⟩⟩
    simpa only [←Nat.mul_assoc,Nat.mul_comm t 2] using
      ((card_le_card subset).trans (card_biUnion_le_card_mul T frac _ each)).trans
        (Nat.mul_le_mul_right _ size)
  have est : (low.card:ℝ) ≤ (2*(t:ℝ))*((N:ℝ)*(∑p∈P,(1:ℝ)/(M*(p:ℝ)^2)))+
        (P.card:ℝ)+(2*(t:ℝ))*(((2*N).sqrt:ℝ)/4+2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      diagonal_partial N M (2*t) P low B (fun p hp=>inp p hp) Subset.rfl points inside
  have primeSum : (∑p∈P,(1:ℝ)/(p:ℝ)^2) ≤ 5/359 := by
    have sq : (∑p∈P,(1:ℚ)/(p:ℚ)^2) ≤ 5/359 := by
      calc _ ≤ ∑p∈diagPrimesUpTo N,(1:ℚ)/(p:ℚ)^2 := sum_le_sum_of_subset_of_nonneg (fun p hp=>inp p hp) (by intros; positivity)
           _ ≤ _ := by convert sum_diagPrimesUpTo_le N using 1; norm_num
    have cast := (Rat.cast_le (K:=ℝ)).mpr sq
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using cast
  have rest : (∑p∈P,(1:ℝ)/(M*(p:ℝ)^2))= (∑p∈P,(1:ℝ)/(p:ℝ)^2)/(M:ℝ) := by
    rw [sum_div]; apply sum_congr rfl; intro p hp; ring
  rw [rest] at est
  have soft : (2*(t:ℝ))*((N:ℝ)*((∑p∈P,(1:ℝ)/(p:ℝ)^2)/(M:ℝ))) ≤
       (2*(t:ℝ))*(N:ℝ)*(5/359)/(M:ℝ) := by
    rw [mul_div_assoc',←mul_div_assoc,←mul_assoc]
    gcongr
  have grow : 100000^2 ≤ 2*N := by norm_num; omega
  have le := Nat.le_sqrt'.mpr grow
  have bound := (Nat.mul_le_mul_right (2*N).sqrt le).trans (by simpa only [←pow_two] using Nat.sqrt_le' (2*N))
  have sr : 100000*((2*N).sqrt:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast bound
  have nR : 5000000000≤(N:ℝ) := by exact_mod_cast big
  have sqrtR : (2*(t:ℝ))*(((2*N).sqrt:ℝ)/4+2)≤(2*(t:ℝ))*(N:ℝ)/198000 := by
    rw [mul_div_assoc]; gcongr; linarith only [sr,nR]
  have highR : 4000*(high.card:ℝ)≤(N:ℝ) := by exact_mod_cast capHigh
  have pR : 3100*(P.card:ℝ)≤(N:ℝ) := by exact_mod_cast capP
  have comb : S.card≤low.card+high.card := by
    have e := card_sdiff_add_card_inter S low
    have sub := card_le_card (inter_subset_right (s₁:=S) (s₂:=low))
    change S.card≤low.card+(S\low).card
    omega
  have combR : (S.card:ℝ)≤(low.card:ℝ)+(high.card:ℝ) := by exact_mod_cast comb
  linarith only [combR,est,soft,sqrtR,highR,pR]
private theorem phase_partial (N : ℕ) (P S : Finset ℕ) (B : ℕ → Finset ℕ)
    (primes : P ⊆ diagPrimesUpTo N) (covered : S ⊆ P.biUnion B)
    (old : ∀ p ∈ P, ((B p).card:ℝ) ≤ (761/525:ℝ)*((N:ℝ)/(p:ℝ)^2)+20)
    (inside : ∀ p, ∀n∈B p, n < N ∧ p^2 ∣ n^2+1) :
    (S.card : ℝ) ≤ (761/525:ℝ)*((N : ℝ) * (∑ p ∈ P, (1 : ℝ)/((p:ℝ)^2))) +
      (P.card : ℝ) + (20:ℝ)*(((2*N).sqrt : ℝ)/4+2) := by
  classical
  let small := P.filter (· ≤ (2*N).sqrt)
  have point (p : ℕ) (hp : p ∈ P) :
      ((B p).card : ℝ) ≤ ((761/525:ℝ)*(N : ℝ))*((1 : ℝ)/((p:ℝ)^2)) +
        (if p ≤ (2*N).sqrt then (20:ℝ) else 0) + 1 := by
    by_cases cut : p ≤ (2*N).sqrt
    · rw [if_pos cut]
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using
        (old p hp).trans (le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num))
    · rw [if_neg cut]
      have prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (primes hp)).1).2
      have mod4 : p%4=1 := (Finset.mem_filter.mp (primes hp)).2.1
      have lim : 2*N ≤ p^2 := (Nat.sqrt_lt'.mp (lt_of_not_ge cut)).le
      have o : ((B p).card : ℝ) ≤ 1 := by exact_mod_cast at_most_one_large_diagonal_root N p prime mod4 lim (B p) (inside p)
      have hpos : 0 ≤ ((761/525:ℝ)*(N : ℝ))*((1 : ℝ)/((p:ℝ)^2)) := by positivity
      linarith only [o,hpos]
  have total : S.card ≤ ∑ p ∈ P, (B p).card :=
    (Finset.card_le_card covered).trans Finset.card_biUnion_le
  have totalR : (S.card : ℝ) ≤ ∑ p ∈ P, ((B p).card : ℝ) := by exact_mod_cast total
  have upper := totalR.trans (Finset.sum_le_sum point)
  have count : (∑ p ∈ P, if p ≤ (2*N).sqrt then (20:ℝ) else 0) = (small.card : ℝ)*(20:ℝ) := by
    rw [← Finset.sum_filter]
    simp [small]
  have sub : small ⊆ (range ((2*N).sqrt+1)).filter (fun p=>p ≡ 1 [MOD 4]) := by
    intro p hp
    obtain ⟨pm,lim⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le lim),(mem_filter.mp (primes pm)).2.1⟩
  have cs := (card_le_card sub).trans (card_filter_mod_eq_le ((2*N).sqrt+1) 4 1)
  have cs' : 4*small.card≤(2*N).sqrt+5 := by omega
  have cR : 4*(small.card:ℝ)≤((2*N).sqrt:ℝ)+5 := by exact_mod_cast cs'
  have csr : (small.card:ℝ)≤((2*N).sqrt:ℝ)/4+2 := by linarith only [cR]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,count,Finset.sum_const, nsmul_eq_mul,
    mul_one] at upper
  linarith only [upper,mul_le_mul_of_nonneg_left csr (show (0:ℝ)≤20 by norm_num)]


private theorem phase_two {N p : ℕ} (S : Finset ℕ) (hp : p.Prime) (mod4 : p%4=1) (ge : 13≤p)
    (info : ∀x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬6∣x ∧ ¬14∣x ∧ p^2∣x^2+1) :
    (S.card:ℝ)≤(761/525:ℝ)*((N:ℝ)/(p:ℝ)^2)+20 := by
  classical
  have nz : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let G (r : ZMod (p^2)) := (Deldor14.Erdos848Phase.prog N (p^2) r.val).filter
    (fun x=>x%25≠7 ∧ x%25≠18 ∧ ¬6∣x ∧ ¬14∣x)
  have one (r : ZMod (p^2)) : ((G r).card:ℝ)≤(761/1050:ℝ)*((N:ℝ)/(p:ℝ)^2)+10 :=
    Deldor14.Erdos848Phase.phase_one (N:=N) (u:=r.val) hp ge
  obtain ⟨r,t,_,_,_,_,root⟩ := two_roots_mod_p_squared p hp mod4
  have subset : S ⊆ G r ∪ G t := by
    intro x hx
    obtain ⟨xn,x7,x18,x6,x14,div⟩ := info x hx
    have eq0 := (ZMod.natCast_eq_zero_iff (x^2+1) (p^2)).mpr div
    have eq1 : (x:ZMod (p^2))^2+1=0 := by exact_mod_cast eq0
    have lift (z : ZMod (p^2)) (eq : (x:ZMod (p^2))=z) : x∈G z := by
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr xn,(ZMod.natCast_eq_natCast_iff x z.val (p^2)).mp (by simpa using eq)⟩,x7,x18,x6,x14⟩
    exact (root _ (eq_neg_of_add_eq_zero_left eq1)).elim (fun e=>mem_union_left _ (lift _ e)) (fun e=>mem_union_right _ (lift _ e))
  have leR : (S.card:ℝ)≤((G r).card:ℝ)+((G t).card:ℝ) := by
    exact_mod_cast (card_le_card subset).trans (card_union_le ..)
  linarith only [leR,one r,one t]

theorem all_avoids_six_fourteen {N : ℕ} (big : 5000000000≤N) (S : Finset ℕ)
    (info : ∀x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1) ∧ ¬6∣x ∧ ¬14∣x) :
    (S.card:ℝ) ≤ (21/1000)*(N:ℝ) := by
  classical
  let P := (diagPrimesUpTo N).filter (fun p=>360*p≤N)
  let B (p : ℕ) := S.filter (fun x=>p^2∣x^2+1)
  let low := P.biUnion B
  let high := S \ low
  have inp (p) (hp : p∈P) := (mem_filter.mp hp).1
  have prime (p) (hp : p∈P) : p.Prime := (mem_filter.mp (mem_filter.mp (inp p hp)).1).2
  have prop (p) (hp : p∈P) : p%4=1 ∧ 13≤p := (mem_filter.mp (inp p hp)).2
  have inside (p n) (hn : n∈B p) : n<N ∧ p^2∣n^2+1 :=
    ⟨(info n (mem_filter.mp hn).1).1,(mem_filter.mp hn).2⟩
  have capHigh := Erdos848Gap.large_diagonal_360 (by omega : 4665600000≤N) high (by
    intro x hx
    obtain ⟨xS,xL⟩ := mem_sdiff.mp hx
    obtain ⟨xn,x7,x18,di,_⟩ := info x xS
    obtain ⟨p,mem,div⟩ := diagonal_prime (by omega) xn x7 x18 di
    have pn := mem_range.mp (mem_filter.mp (mem_filter.mp mem).1).1
    refine ⟨xn,p,by omega,?_,div⟩
    by_contra! small
    exact xL (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,small⟩,mem_filter.mpr ⟨xS,div⟩⟩))
  have capP := Erdos848Five.small_primes_360 big P prime (by
    intro p hp
    have h := (mem_filter.mp hp).2
    omega)
  have points (p) (hp : p∈P) : ((B p).card:ℝ) ≤ (761/525:ℝ)*((N:ℝ)/(p:ℝ)^2)+20 := by
    apply phase_two _ (prime p hp) (prop p hp).1 (prop p hp).2
    intro x hx
    obtain ⟨sx,dv⟩ := mem_filter.mp hx
    obtain ⟨xn,x7,x18,_,x6,x14⟩ := info x sx
    exact ⟨xn,x7,x18,x6,x14,dv⟩
  have est := phase_partial N P low B (fun p hp=>inp p hp) Subset.rfl points inside
  have primeSum : (∑p∈P,(1:ℝ)/(p:ℝ)^2) ≤ 5/359 := by
    have sq : (∑p∈P,(1:ℚ)/(p:ℚ)^2) ≤ 5/359 := by
      calc _ ≤ ∑p∈diagPrimesUpTo N,(1:ℚ)/(p:ℚ)^2 := sum_le_sum_of_subset_of_nonneg (fun p hp=>inp p hp) (by intros; positivity)
           _ ≤ _ := by convert sum_diagPrimesUpTo_le N using 1; norm_num
    have cast := (Rat.cast_le (K:=ℝ)).mpr sq
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using cast
  have grow : 100000^2 ≤ 2*N := by norm_num; omega
  have le := Nat.le_sqrt'.mpr grow
  have bound := (Nat.mul_le_mul_right (2*N).sqrt le).trans (by simpa only [←pow_two] using Nat.sqrt_le' (2*N))
  have sr : 100000*((2*N).sqrt:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast bound
  have nR : 5000000000≤(N:ℝ) := by exact_mod_cast big
  have sr' : (20:ℝ)*(((2*N).sqrt:ℝ)/4+2) ≤ 20*(N:ℝ)/198000 := by linarith only [sr,nR]
  have highR : 4000*(high.card:ℝ)≤(N:ℝ) := by exact_mod_cast capHigh
  have pR : 3100*(P.card:ℝ)≤(N:ℝ) := by exact_mod_cast capP
  have comb : S.card≤low.card+high.card := by
    have e := card_sdiff_add_card_inter S low
    have sub := card_le_card (inter_subset_right (s₁:=S) (s₂:=low))
    change S.card≤low.card+(S\low).card
    omega
  have combR : (S.card:ℝ)≤(low.card:ℝ)+(high.card:ℝ) := by exact_mod_cast comb
  have weighted := mul_le_mul_of_nonneg_left primeSum (Nat.cast_nonneg (α:=ℝ) N)
  linarith only [combR,est,weighted,sr',highR,pR,Nat.cast_nonneg (α:=ℝ) N]
end Deldor14.Erdos848Fifth

/- Cardinality consequences of the diagonal sieve for three types of residual sets. -/
namespace Deldor14.Erdos848Fifth
open Finset

def outsideInfo (N : ℕ) (R : Finset ℕ) := ∀x∈R, x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1)

theorem outside_all {N : ℕ} (big : 5000000000≤N) (R : Finset ℕ) (info : outsideInfo N R) :
    (R.card:ℝ) ≤ (285/10000)*(N:ℝ) := by
  have h := diagonal_budget (M:=1) (t:=1) big (by decide) {0} R (by decide) (by
    intro x hx
    obtain ⟨a,b,c,d⟩ := info x hx
    exact ⟨a,b,c,d,mem_singleton.mpr (by omega)⟩)
  push_cast at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]

theorem outside_avoids_six {N : ℕ} (big : 5000000000≤N) (R : Finset ℕ) (info : outsideInfo N R)
    (no : ∀x∈R, ¬6∣x) : (R.card:ℝ) ≤ (232/10000)*(N:ℝ) := by
  let T := (range 150).filter (fun x=>x%6≠0 ∧ x%25≠7 ∧ x%25≠18)
  have size : T.card≤115 := by decide
  have h := diagonal_budget (M:=150) (t:=115) big (by decide) T R size (by
    intro x hx
    obtain ⟨a,b,c,d⟩ := info x hx
    have n := no x hx
    exact ⟨a,b,c,d,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),by omega,by omega,by omega⟩⟩)
  push_cast at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]

theorem outside_odd {N : ℕ} (big : 5000000000≤N) (R : Finset ℕ) (info : outsideInfo N R)
    (odd : ∀x∈R,x%2=1) : (R.card:ℝ) ≤ (1363/100000)*(N:ℝ) := by
  let T := (range 50).filter (fun q=>q%2=1 ∧ q%25≠7 ∧ q%25≠18)
  have size : T.card≤23 := by decide
  have h := diagonal_budget (M:=50) (t:=23) big (by decide) T R size (by
    intro x hx
    obtain ⟨a,b,c,d⟩ := info x hx
    have o := odd x hx
    exact ⟨a,b,c,d,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),by omega,by omega,by omega⟩⟩)
  push_cast at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]


theorem outside_odd_no3 {N : ℕ} (big : 5000000000≤N) (R : Finset ℕ) (info : outsideInfo N R)
    (odd : ∀x∈R,x%2=1) (no : ∀x∈R,¬3∣x) : (R.card:ℝ) ≤ (99/10000)*(N:ℝ) := by
  have h := diagonal_budget (M:=6) (t:=2) big (by decide) {1,5} R (by decide) (by
    intro x hx
    obtain ⟨a,b,c,d⟩ := info x hx
    have n := no x hx
    have o := odd x hx
    exact ⟨a,b,c,d,by simp; omega⟩)
  push_cast at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]
end Deldor14.Erdos848Fifth

/- Arithmetic pieces used for the three parts of a mixed admissible set. -/
namespace Deldor14.Erdos848Fifth
open Finset Erdos848

def slice (A : Finset ℕ) (r : ℕ) := A.filter (fun x=>x%25=r)
def outside (A : Finset ℕ) := A.filter (fun x=>x%25≠7 ∧ x%25≠18)

theorem total_parts (A : Finset ℕ) : (A.card:ℝ) ≤ ((slice A 7).card:ℝ)+((slice A 18).card:ℝ)+((outside A).card:ℝ) := by
  have sub : A ⊆ (slice A 7 ∪ slice A 18) ∪ outside A := by
    intro x hx
    by_cases h7 : x%25=7
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx,h7⟩))
    by_cases h18 : x%25=18
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hx,h18⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨hx,h7,h18⟩)
  have c := (card_le_card sub).trans (card_union_le ..)
  have d := card_union_le (slice A 7) (slice A 18)
  exact_mod_cast (by omega : A.card≤(slice A 7).card+(slice A 18).card+(outside A).card)

theorem between_not25 {b x r : ℕ} (base : r=7 ∨ r=18) (different : b%25≠r) (xr : x%25=r) :
    ¬25∣b*x+1 := by
  intro div
  have mod := Nat.mod_eq_zero_of_dvd div
  rw [Nat.add_mod,Nat.mul_mod,xr] at mod
  rcases base with rfl|rfl <;> omega

theorem slice_bound {N b r : ℕ} {A : Finset ℕ} (big : 5000000000≤N) (inside : A⊆range N)
    (adm : NonSquarefreeProductProp A) (ba : b∈A) (base : r=7 ∨ r=18) (different : b%25≠r) :
    let s := ((slice A r).card:ℝ)
    s ≤ (1915/100000)*(N:ℝ) ∧ (2∣b → s ≤ (915/100000)*(N:ℝ)) ∧
    (3∣b → s ≤ (1470/100000)*(N:ℝ)) ∧ (6∣b → s ≤ (565/100000)*(N:ℝ)) := by
  have h := Erdos848Five.bad_five (r:=r) big (mem_range.mp (inside ba))
    (slice A r) ((filter_subset ..).trans inside) (by
      intro x hx
      change x%25=r%25
      rw [(mem_filter.mp hx).2,Nat.mod_eq_of_lt (by omega : r<25)]) (by
      intro x hx
      exact adm b ba x (mem_filter.mp hx).1) (by
      intro x hx
      exact between_not25 base different (mem_filter.mp hx).2)
  dsimp
  by_cases six : 6∣b
  · have ev : 2∣b := (by decide : 2∣6).trans six
    have tr : 3∣b := (by decide : 3∣6).trans six
    rw [if_pos six,if_pos ev,if_pos tr] at h
    constructor
    · linarith only [h,Nat.cast_nonneg (α:=ℝ) N]
    refine ⟨fun _=>?_,fun _=>?_,fun _=>?_⟩ <;> linarith only [h,Nat.cast_nonneg (α:=ℝ) N]
  · rw [if_neg six] at h
    by_cases ev : 2∣b <;> by_cases tr : 3∣b <;> simp only [ev,tr,if_true,if_false] at h
    all_goals refine ⟨?_,fun e=>?_,fun t=>?_,fun t=>(six t).elim⟩
    all_goals first | contradiction | linarith only [h,Nat.cast_nonneg (α:=ℝ) N]
end Deldor14.Erdos848Fifth

namespace Deldor14.Erdos848Fifth
open Finset Erdos848
theorem slice_fourteen {N b r : ℕ} {A : Finset ℕ} (big : 5000000000≤N) (inside : A⊆range N)
    (adm : NonSquarefreeProductProp A) (ba : b∈A) (fourteen : 14∣b) (not6 : ¬6∣b)
    (base : r=7 ∨ r=18) (diff : b%25≠r) : ((slice A r).card:ℝ) ≤ (833/100000)*(N:ℝ) := by
  apply Erdos848Five.bad_five_fourteen (r:=r) big (mem_range.mp (inside ba)) _ ((filter_subset ..).trans inside) _ _ _ fourteen not6
  · intro x hx
    change x%25=r%25
    rw [(mem_filter.mp hx).2,Nat.mod_eq_of_lt (by omega : r<25)]
  · intro x hx
    exact adm b ba x (mem_filter.mp hx).1
  · intro x hx
    exact between_not25 base diff (mem_filter.mp hx).2

theorem slice_odd {N b r : ℕ} {A : Finset ℕ} (big : 5000000000≤N) (inside : A⊆range N)
    (adm : NonSquarefreeProductProp A) (odd : ∀x∈A,x%2=1) (br : b∈outside A)
    (base : r=7 ∨ r=18) : ((slice A r).card:ℝ)≤((if 3∣b then 1315 else 1426)/100000:ℝ)*(N:ℝ) := by
  classical
  obtain ⟨ba,b7,b18⟩ := mem_filter.mp br
  have diff : b%25≠r := by omega
  let S := slice A r
  let L := S.filter (fun x=>x%4=b%4)
  let F := S\L
  have parts : S.card=F.card+L.card := (card_sdiff_add_card_eq_card (filter_subset .. : L⊆S)).symm
  have left (x) (hx : x∈L) : x∈A ∧ x%25=r ∧ x%4=b%4 :=
    ⟨(mem_filter.mp (mem_filter.mp hx).1).1,(mem_filter.mp (mem_filter.mp hx).1).2,(mem_filter.mp hx).2⟩
  have bd := Erdos848Five.bad_five_100 (r:=r) (s:=b) big (mem_range.mp (inside ba)) (by have := odd b ba; omega)
    L (fun x hx=>inside (left x hx).1)
    (by intro x hx; change x%25=r%25; rw [(left x hx).2.1,Nat.mod_eq_of_lt (by omega : r<25)])
    (fun x hx=>(left x hx).2.2)
    (fun x hx=>adm b ba x (left x hx).1)
    (by
      intro x hx div
      have mod := Nat.mod_eq_zero_of_dvd div
      rw [Nat.add_mod,Nat.mul_mod,(left x hx).2.2] at mod
      have ob := odd b ba
      rcases (show b%4=1 ∨ b%4=3 by omega) with e|e <;> rw [e] at mod <;> contradiction)
    (fun x hx=>between_not25 base diff (left x hx).2.1)
  have sub : F ⊆ (range N).filter (fun x=>x ≡ r [MOD 25] ∧ x ≡ 4-b%4 [MOD 4]) := by
    intro x hx
    obtain ⟨sx,ne⟩ := mem_sdiff.mp hx
    obtain ⟨xa,xr⟩ := mem_filter.mp sx
    have mis : x%4≠b%4 := fun eq=>ne (mem_filter.mpr ⟨sx,eq⟩)
    refine mem_filter.mpr ⟨inside xa,?_,?_⟩
    · change x%25=r%25
      rw [xr,Nat.mod_eq_of_lt (by omega : r<25)]
    · have xb := odd x xa
      have bb := odd b ba
      change x%4=(4-b%4)%4
      omega
  have far := (card_le_card sub).trans (Erdos848Port.card_filter_modEq_and_modEq_le N 25 4 r (4-b%4) (by decide))
  have fx : F.card ≤ N/100+1 := far
  have bound : 100*F.card≤N+100 := by omega
  have fR : 100*(F.card:ℝ) ≤ (N:ℝ)+100 := by exact_mod_cast bound
  have pR : (S.card:ℝ)=(F.card:ℝ)+(L.card:ℝ) := by exact_mod_cast parts
  have large : 5000000000≤(N:ℝ) := by exact_mod_cast big
  change (S.card:ℝ) ≤ _
  by_cases tri : 3∣b <;> simp only [tri,if_true,if_false] at bd ⊢ <;> linarith only [large,pR,bd,fR]
end Deldor14.Erdos848Fifth

/- The mixed-set estimate at the remaining large endpoints. -/
namespace Deldor14.Erdos848Fifth
open Finset Erdos848
theorem mixed_size {k : ℕ} (big : 5000000000≤25*k+7) (A : Finset ℕ)
    (inside : A⊆range (25*k+7)) (adm : NonSquarefreeProductProp A)
    (mixed : (outside A).Nonempty)
    : A.card≤k := by
  let N := 25*k+7
  let R := outside A
  have info : outsideInfo N R := by
    intro x hx
    obtain ⟨xa,x7,x18⟩ := mem_filter.mp hx
    exact ⟨mem_range.mp (inside xa),x7,x18,adm x xa x xa⟩
  have total := total_parts A
  change (A.card:ℝ) ≤ ((slice A 7).card:ℝ)+((slice A 18).card:ℝ)+(R.card:ℝ) at total
  have endpoint : (N:ℝ)=25*(k:ℝ)+7 := by dsimp [N]; push_cast; ring
  by_contra! bad
  have more : (k:ℝ)+1 ≤ (A.card:ℝ) := by exact_mod_cast (show k+1≤A.card by omega)
  have positiveN : 5000000000 ≤ (N:ℝ) := by exact_mod_cast big
  by_cases even : ∃e∈R,2∣e
  · obtain ⟨e,er,ev⟩ := even
    obtain ⟨ea,e7,e18⟩ := mem_filter.mp er
    have h7 := (slice_bound big inside adm ea (Or.inl (rfl : 7=7)) e7).2.1 ev
    have h18 := (slice_bound big inside adm ea (Or.inr (rfl : 18=18)) e18).2.1 ev
    by_cases six : ∃d∈R,6∣d
    · obtain ⟨d,dr,d6⟩ := six
      obtain ⟨da,d7,d18⟩ := mem_filter.mp dr
      have b7 := (slice_bound big inside adm da (Or.inl (rfl : 7=7)) d7).2.2.2 d6
      have b18 := (slice_bound big inside adm da (Or.inr (rfl : 18=18)) d18).2.2.2 d6
      have diag := outside_all big R info
      change ((slice A 7).card:ℝ) ≤ (565/100000)*(N:ℝ) at b7
      change ((slice A 18).card:ℝ) ≤ (565/100000)*(N:ℝ) at b18
      linarith only [b7,b18,diag,total,more,endpoint,positiveN]
    · by_cases fourteen : ∃x∈R,14∣x
      · obtain ⟨f,fr,f14⟩ := fourteen
        obtain ⟨fa,f7,f18⟩ := mem_filter.mp fr
        have diag := outside_avoids_six big R info (fun x hx d=>six ⟨x,hx,d⟩)
        have fnot : ¬6∣f := fun d=>six ⟨f,fr,d⟩
        have row7 := slice_fourteen big inside adm fa f14 fnot (Or.inl (rfl : 7=7)) f7
        have row18 := slice_fourteen big inside adm fa f14 fnot (Or.inr (rfl : 18=18)) f18
        change ((slice A 7).card:ℝ) ≤ (833/100000)*(N:ℝ) at row7
        change ((slice A 18).card:ℝ) ≤ (833/100000)*(N:ℝ) at row18
        linarith only [row7,row18,diag,total,more,endpoint,positiveN]
      · have diag := all_avoids_six_fourteen big R (by
          intro x hx
          obtain ⟨xn,x7,x18,dg⟩ := info x hx
          exact ⟨xn,x7,x18,dg,fun t=>six ⟨x,hx,t⟩,fun t=>fourteen ⟨x,hx,t⟩⟩)
        change ((slice A 7).card:ℝ) ≤ (915/100000)*(N:ℝ) at h7
        change ((slice A 18).card:ℝ) ≤ (915/100000)*(N:ℝ) at h18
        linarith only [h7,h18,diag,total,more,endpoint,positiveN]
  · have allR (x) (hx : x∈R) : x%2=1 := by
      have h : ¬2∣x := fun d=>even ⟨x,hx,d⟩
      omega
    obtain ⟨b,br,chosen⟩ : ∃b∈R,3∣b ∨ ∀x∈R,¬3∣x := by
      by_cases found : ∃b∈R,3∣b
      · obtain ⟨x,hx,m⟩ := found
        exact ⟨x,hx,Or.inl m⟩
      · obtain ⟨x,hx⟩ := mixed
        exact ⟨x,hx,Or.inr (fun t ht div=>found ⟨t,ht,div⟩)⟩
    have diag : (R.card:ℝ) ≤ ((if 3∣b then 1363 else 990)/100000:ℝ)*(N:ℝ) := by
      by_cases tri : 3∣b
      · rw [if_pos tri]; exact outside_odd big R info allR
      · rw [if_neg tri]
        have z := outside_odd_no3 big R info allR (chosen.resolve_left tri)
        linarith only [z]
    obtain ⟨ba,b7,b18⟩ := mem_filter.mp br
    have row (r) (hr : r=7 ∨ r=18) (diff : b%25≠r) :
        ((slice A r).card:ℝ) ≤ ((if 3∣b then 1470 else 1915)/100000:ℝ)*(N:ℝ) := by
      have q := slice_bound big inside adm ba hr diff
      by_cases tri : 3∣b
      · rw [if_pos tri]; exact q.2.2.1 tri
      · rw [if_neg tri]; exact q.1
    by_cases someEven : ∃e∈A,2∣e
    · obtain ⟨e,ea,ev⟩ := someEven
      by_cases e7 : e%25=7
      · have r7 := row 7 (by decide) b7
        have r18 := (slice_bound big inside adm ea (Or.inr (rfl : 18=18)) (by omega)).2.1 ev
        change ((slice A 18).card:ℝ)≤(915/100000)*(N:ℝ) at r18
        split_ifs at r7 diag <;> linarith only [r7,r18,diag,total,more,endpoint,positiveN]
      · have r18 := row 18 (by decide) b18
        have r7 := (slice_bound big inside adm ea (Or.inl (rfl : 7=7)) e7).2.1 ev
        change ((slice A 7).card:ℝ)≤(915/100000)*(N:ℝ) at r7
        split_ifs at r18 diag <;> linarith only [r7,r18,diag,total,more,endpoint,positiveN]
    · have allodd (x) (hx : x∈A) : x%2=1 := by
        have h : ¬2∣x := fun ev=>someEven ⟨x,hx,ev⟩
        omega
      have r7 := slice_odd big inside adm allodd br (Or.inl (rfl : 7=7))
      have r18 := slice_odd big inside adm allodd br (Or.inr (rfl : 18=18))
      change ((slice A 7).card:ℝ)≤((if 3∣b then 1315 else 1426)/100000:ℝ)*(N:ℝ) at r7
      change ((slice A 18).card:ℝ)≤((if 3∣b then 1315 else 1426)/100000:ℝ)*(N:ℝ) at r18
      split_ifs at r7 r18 diag <;> linarith only [r7,r18,diag,total,more,endpoint,positiveN]
end Deldor14.Erdos848Fifth

/- An unconditional threshold for Erdős 848 for every N ≥ 250 billion.
Mixed sets use the restricted diagonal and row sieves. Pure sets use the
Hall matching between the two exceptional residue classes. -/
namespace Deldor14.Erdos848Fifth
open Finset Erdos848
theorem endpoint_5B (k : ℕ) (big : 5000000000≤25*k+7) (A : Finset ℕ)
    (inside : A⊆range (25*k+7)) (adm : NonSquarefreeProductProp A) : A.card≤k := by
  classical
  by_cases mixed : (outside A).Nonempty
  · exact mixed_size big A inside adm mixed
  let N := 25*k+7
  let X := slice A 18
  let Y := slice A 7
  let Γ := hood N X
  have baseX : X⊆side N 18 := by
    intro x hx
    obtain ⟨xa,eq⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨inside xa,eq⟩
  have hall : X.card≤Γ.card := Erdos848Pure.hall_400M k (by omega) X baseX
  have dis : Disjoint Γ Y := by
    apply disjoint_left.mpr
    intro a ag ay
    obtain ⟨_,b,bx,edge⟩ := mem_filter.mp ag
    exact adm a (mem_filter.mp ay).1 b (mem_filter.mp bx).1 edge
  have sub : Γ∪Y⊆side N 7 := union_subset (filter_subset ..) (by
    intro y hy
    obtain ⟨ya,eq⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨inside ya,eq⟩)
  have cap := card_le_card sub
  rw [card_union_of_disjoint dis,side_card k 7 (by decide)] at cap
  have no : outside A=∅ := not_nonempty_iff_eq_empty.mp mixed
  have q := total_parts A
  rw [no,card_empty,Nat.cast_zero,add_zero] at q
  have qr : A.card ≤ Y.card+X.card := by exact_mod_cast q
  omega

theorem effective_5B (N : ℕ) (big : 5000000000≤N) : Erdos848For N := by
  intro A inside adm
  let k := (N+17)/25
  have up : N ≤ 25*k+7 := by dsimp [k]; omega
  have incl : A⊆range (25*k+7) := fun x hx=>mem_range.mpr ((mem_range.mp (inside hx)).trans_le up)
  have valid := endpoint_5B k (big.trans up) A incl adm
  have size : (A₇ N).card=k := Erdos848Port.card_range_filter_mod25_eq 7 (by decide) N
  rw [size]
  exact valid
end Deldor14.Erdos848Fifth

/- Encoding the complementary divisor in a single congruence class. -/
namespace Erdos848Progression
open Erdos848Gap Finset
theorem count_mixed_divisors_progression {N b C U K a : ℕ} (bpos : 0 < b) (bN : b ≤ N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n ∈ S, d n * (p n)^2 = b*n+1)
    (key : ∀ n∈S, d n ≡ a [MOD K]) (pr : ∀ n ∈ S, p n ≤ U) (dr : ∀ n ∈ S, d n*N < C*b) :
    S.card ≤ (C*b/N/K+1)*(2*2^b.primeFactors.card)*(2*U/b+1) := by
  classical
  let anchor (j : ℕ) : ℕ := if h : ∃ t ∈ S, d t = j then h.choose else 0
  have anchor_spec (n : ℕ) (hn : n ∈ S) :
      anchor (d n) ∈ S ∧ d (anchor (d n)) = d n := by
    have h : ∃ t ∈ S, d t = d n := ⟨n,hn,rfl⟩
    simpa only [anchor,dif_pos h] using h.choose_spec
  let r (j : ℕ) := p (anchor j)
  let g (n : ℕ) := Int.gcd (b : ℤ) ((p n : ℤ) - (r (d n) : ℤ))
  let code (n : ℕ) := (d n/K, g n, 2*p n/b)
  let keys := b.divisors.filter (fun j => Nat.gcd j (b/j) ∣ 2)
  let T := (Finset.range (C*b/N/K+1)).product (keys.product (Finset.range (2*U/b+1)))
  have eqz (n : ℕ) (hn : n ∈ S) :
      (d n : ℤ)*(p n : ℤ)^2=(b : ℤ)*(n : ℤ)+1 := by exact_mod_cast eq n hn
  have Npos := bpos.trans_le bN
  have count : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn code
    · intro n hn
      have hdv : g n ∣ b := by
        have hz : (g n : ℤ) ∣ (b : ℤ) := Int.gcd_dvd_left ..
        exact_mod_cast hz
      have hbnd : 2*p n/b ≤ 2*U/b := Nat.div_le_div_right (by have := pr n hn; omega)
      refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_product.mpr ⟨?_,?_⟩⟩
      · exact Nat.lt_succ_of_le (Nat.div_le_div_right ((Nat.le_div_iff_mul_le Npos).mpr (dr n hn).le))
      · refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdv,bpos.ne'⟩,?_⟩
        have ha := anchor_spec n hn
        have er := eqz _ ha.1
        rw [ha.2] at er
        exact Erdos848RootRefined.root_key_valid bpos er (eqz n hn)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hbnd)
    · intro x hx y hy hc
      have hqxy : d x/K=d y/K := congrArg Prod.fst hc
      have hmxy := (key x hx).trans (key y hy).symm
      change d x%K=d y%K at hmxy
      have hd : d x = d y := by
        have ex := Nat.mod_add_div (d x) K
        have ey := Nat.mod_add_div (d y) K
        rw [hmxy,hqxy] at ex
        exact ex.symm.trans ey
      have hg : g x = g y := congrArg (fun u => u.2.1) hc
      have hq : 2*p x/b=2*p y/b := congrArg (fun u => u.2.2) hc
      have ha := anchor_spec x hx
      have er := eqz _ ha.1
      rw [ha.2] at er
      have ey := eqz y hy
      rw [← hd] at ey
      change Int.gcd _ ((p x : ℤ) - (r (d x) : ℤ)) = Int.gcd _ ((p y : ℤ) - (r (d y) : ℤ)) at hg
      rw [← hd] at hg
      have hu := Erdos848RootRefined.roots_in_class er (eqz x hx) ey hg
      have hm : 2*p x ≡ 2*p y [MOD b] := by
        apply Int.natCast_modEq_iff.mp
        rw [Int.modEq_iff_dvd]
        convert! hu using 1
        push_cast
        ring
      have ex := Nat.mod_add_div (2*p x) b
      have ey' := Nat.mod_add_div (2*p y) b
      change (2*p x)%b=(2*p y)%b at hm
      rw [hm,hq] at ex
      have hp : p x=p y := by omega
      have et := eq x hx
      rw [hd,hp,eq y hy] at et
      exact Nat.eq_of_mul_eq_mul_left bpos (by omega)
  have bound : S.card ≤ (C*b/N/K+1)*keys.card*(2*U/b+1) := by
    simpa [T, Finset.card_product, mul_assoc] using count
  exact bound.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Erdos848Unitary.count_unitary_keys b bpos)))


theorem unit_square_six {K b n d p : ℕ} (choice : K=2 ∨ K=3 ∨ K=6)
    (factor : K∣b) (equation : d*p^2=b*n+1) : d ≡ 1 [MOD K] := by
  have h : d*p^2 ≡ 1 [MOD K] := by
    rw [equation]
    exact (Nat.modEq_zero_iff_dvd.mpr (factor.mul_right n)).add (Nat.ModEq.refl 1)
  change (d*p^2)%K=1%K at h
  rw [Nat.mul_mod,Nat.pow_mod] at h
  change d%K=1%K
  rcases choice with rfl|rfl|rfl
  · have dr := Nat.mod_lt d (by decide : 0 < 2)
    have pr := Nat.mod_lt p (by decide : 0 < 2)
    generalize d % 2 = dx at h dr ⊢
    generalize p % 2 = px at h pr
    interval_cases dx <;> interval_cases px <;> norm_num at *
  · have dr := Nat.mod_lt d (by decide : 0 < 3)
    have pr := Nat.mod_lt p (by decide : 0 < 3)
    generalize d % 3 = dx at h dr ⊢
    generalize p % 3 = px at h pr
    interval_cases dx <;> interval_cases px <;> norm_num at *
  · have dr := Nat.mod_lt d (by decide : 0 < 6)
    have pr := Nat.mod_lt p (by decide : 0 < 6)
    generalize d % 6 = dx at h dr ⊢
    generalize p % 6 = px at h pr
    interval_cases dx <;> interval_cases px <;> norm_num at *
end Erdos848Progression

/- Large-prime errors with a small pivot or restricted complementary divisor. -/
namespace Erdos848Progression
open Finset Erdos848Gap
theorem mixed48_count {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<48*p n) : S.card ≤ 3072*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 8*p n≤N)
  let large := S.filter (fun n => ¬ 8*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/8 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<2304*b := by
    exact link n (smallS hn) 48 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<64*b := by
    exact link n (largeS hn) 8 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 2304*b/N
  let W := 2*(N/8)/b
  have pd : P*N ≤ 2304*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/8) := Nat.div_mul_le_self _ _
  have u : 8*(N/8)≤N := by omega
  have num : 4*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤2304 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤576 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 2304*b*W=2304*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 576 num)
    have l1 : (P*W)*N ≤ 576*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 2880 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 2880*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 64*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 64*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤64 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 128 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 64 kd
    have mul : (Q*K)*N ≤ 128*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 192 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 192*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

theorem mixed48_small {N b : ℕ} (bp : 0<b) (bn : b≤N)
    (smallB : 20*b≤N) (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N)
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<48*p n) : S.card ≤ 822*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 8*p n≤N)
  let large := S.filter (fun n => ¬ 8*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/8 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<2304*b := by
    exact link n (smallS hn) 48 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<64*b := by
    exact link n (largeS hn) 8 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_unitary bp bn small p d (fun n h => eq n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_unitary bp bn large p d (fun n h => eq n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 2304*b/N
  let W := 2*(N/8)/b
  have pd : P*N ≤ 2304*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/8) := Nat.div_mul_le_self _ _
  have u : 8*(N/8)≤N := by omega
  have num : 4*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤115 := by
    have big := Nat.mul_le_mul_left P smallB
    have bound : (P*20)*b≤2304*b := by nlinarith only [big,pd]
    have h := Nat.le_of_mul_le_mul_right bound bp
    omega
  /- Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np -/
  have pw : P*W≤576 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 2304*b*W=2304*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 576 num)
    have l1 : (P*W)*N ≤ 576*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 691 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have sa : small.card ≤ 691*(2*2^b.primeFactors.card) := by
    refine s.trans ?_
    calc _ = (P*(W+1))*(2*2^b.primeFactors.card) := by dsimp only [P,W]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ sum
  let Q := 64*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 64*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤3 := by
    have big := Nat.mul_le_mul_left Q smallB
    have bound : (Q*20)*b≤64*b := by nlinarith only [big,qd]
    have h := Nat.le_of_mul_le_mul_right bound bp
    omega
  have qk : Q*K ≤ 128 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 64 kd
    have mul : (Q*K)*N ≤ 128*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 131 := by rw [Nat.mul_add,Nat.mul_one]; omega
  have l : large.card ≤ 131*(2*2^b.primeFactors.card) := by
    refine lraw.trans ?_
    calc _ = (Q*(K+1))*(2*2^b.primeFactors.card) := by dsimp only [Q,K]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ qsum
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  omega

theorem mixed48_progression {N b m a : ℕ} (bp : 0<b) (bn : b≤N)
    (S : Finset ℕ) (p d : ℕ → ℕ)
    (eq : ∀ n∈S,d n*(p n)^2=b*n+1) (pr : ∀ n∈S,p n≤N) (key : ∀ n∈S,d n ≡ a [MOD m])
    (link : ∀ n∈S, ∀ c : ℕ, N<c*p n → d n*N < c^2*b)
    (cut : ∀ n∈S,N<48*p n) : m*S.card ≤ (3072+2*m*(2*N/b+1))*(2*2^b.primeFactors.card) := by
  classical
  let small := S.filter (fun n => 8*p n≤N)
  let large := S.filter (fun n => ¬ 8*p n≤N)
  have smallS : small ⊆ S := Finset.filter_subset _ _
  have largeS : large ⊆ S := Finset.filter_subset _ _
  have pr' (n) (hn : n∈small) : p n≤N/8 := by
    have := (Finset.mem_filter.mp hn).2
    omega
  have d1 (n) (hn : n∈small) : d n*N<2304*b := by
    exact link n (smallS hn) 48 (cut n (smallS hn))
  have d2 (n) (hn : n∈large) : d n*N<64*b := by
    exact link n (largeS hn) 8 (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  have s := count_mixed_divisors_progression bp bn small p d (fun n h => eq n (smallS h)) (fun n h=>key n (smallS h)) pr' d1
  have lraw := count_mixed_divisors_progression bp bn large p d (fun n h => eq n (largeS h)) (fun n h=>key n (largeS h))
    (fun n h => pr n (largeS h)) d2
  let P := 2304*b/N
  let W := 2*(N/8)/b
  have pd : P*N ≤ 2304*b := Nat.div_mul_le_self _ _
  have wd : W*b ≤ 2*(N/8) := Nat.div_mul_le_self _ _
  have u : 8*(N/8)≤N := by omega
  have num : 4*(W*b) ≤ N := by omega
  have Np : 0<N := bp.trans_le bn
  have p250 : P≤2304 := by
    exact Nat.le_of_mul_le_mul_right (pd.trans (Nat.mul_le_mul_left _ bn)) Np
  have pw : P*W≤576 := by
    have z := (Nat.mul_le_mul_right W pd).trans_eq (show 2304*b*W=2304*(W*b) by ring)
    have a := (Nat.mul_le_mul_left 576 num)
    have l1 : (P*W)*N ≤ 576*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right l1 Np
  have sum : P*(W+1) ≤ 2880 := by rw [Nat.mul_add,Nat.mul_one]; omega
  let Q := 64*b/N
  let K := 2*N/b
  have qd : Q*N ≤ 64*b := Nat.div_mul_le_self _ _
  have kd : K*b ≤ 2*N := Nat.div_mul_le_self _ _
  have q1600 : Q≤64 := Nat.le_of_mul_le_mul_right (qd.trans (Nat.mul_le_mul_left _ bn)) Np
  have qk : Q*K ≤ 128 := by
    have z := Nat.mul_le_mul_right K qd
    have a := Nat.mul_le_mul_left 64 kd
    have mul : (Q*K)*N ≤ 128*N := by nlinarith only [z,a]
    exact Nat.le_of_mul_le_mul_right mul Np
  have qsum : Q*(K+1) ≤ 192 := by rw [Nat.mul_add,Nat.mul_one]; omega
  let L:=2*2^b.primeFactors.card
  have single (D V : ℕ) : m*(D/m+1)*(V+1) ≤ D*(V+1)+m*(V+1) := by
    calc m*(D/m+1)*(V+1) = (m*(D/m)+m)*(V+1) := by ring
         _ ≤ (D+m)*(V+1) := Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_div_le D m) m)
         _ = _ := Nat.add_mul ..
  have sa : m*small.card ≤ (P*(W+1)+m*(W+1))*L := by
    calc m*small.card ≤ m*((P/m+1)*L*(W+1)) := Nat.mul_le_mul_left _ s
         _ = (m*(P/m+1)*(W+1))*L := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ (single P W)
  have la : m*large.card ≤ (Q*(K+1)+m*(K+1))*L := by
    calc m*large.card ≤ m*((Q/m+1)*L*(K+1)) := Nat.mul_le_mul_left _ lraw
         _ = (m*(Q/m+1)*(K+1))*L := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ (single Q K)
  have smallW : W ≤ K := Nat.div_le_div_right (Nat.mul_le_mul_left 2 (Nat.div_le_self N 8))
  have smallW' := Nat.mul_le_mul_left m (Nat.succ_le_succ smallW)
  change m * (W+1) ≤ m * (K+1) at smallW'
  have cap : P*(W+1)+m*(W+1)+(Q*(K+1)+m*(K+1)) ≤ 3072+2*m*(K+1) := by
    rw [show 2*m*(K+1)=m*(K+1)+m*(K+1) by ring]; omega
  have parts : small.card+large.card=S.card := Finset.card_filter_add_card_filter_not _
  change m*S.card ≤ (3072+2*m*(K+1))*L
  rw [←parts,Nat.mul_add]
  have cs := Nat.mul_le_mul_right L cap
  rw [Nat.add_mul] at cs
  exact (Nat.add_le_add sa la).trans cs 
end Erdos848Progression

/- The two-term inclusion-exclusion bound for four excluded classes. -/
namespace Deldor14.Erdos848Phase
open Finset
private theorem sieve_three {α : Type*} (S : Finset α) (A B C : α→Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C]
    (separate : ∀x∈S,A x → ¬B x) :
    ((S.filter (fun x=>¬A x ∧ ¬B x ∧ ¬C x)).card:ℝ) +
      (S.filter A).card+(S.filter B).card+(S.filter C).card ≤ 
      (S.card:ℝ)+(S.filter (fun x=>A x ∧ C x)).card+(S.filter (fun x=>B x ∧ C x)).card := by
  classical
  have point (x) (hx : x∈S) :
      (if ¬A x ∧ ¬B x ∧ ¬C x then 1 else 0) + (if A x then 1 else 0) +
      (if B x then 1 else 0) + (if C x then 1 else 0) ≤ 
      (1:ℕ)+(if A x ∧ C x then 1 else 0)+(if B x ∧ C x then 1 else 0) := by
    have dis := separate x hx
    by_cases a : A x <;> by_cases b : B x <;> by_cases c : C x <;> simp_all
  have sum := Finset.sum_le_sum point
  simp only [sum_add_distrib,sum_boole,sum_const,smul_eq_mul,mul_one] at sum
  exact_mod_cast sum

theorem phase_no_six {N p u : ℕ} (hp : p.Prime) (large : 13 ≤ p) :
    let S := prog N (p^2) u
    ((S.filter (fun x=>x%25≠7 ∧ x%25≠18 ∧ ¬6∣x)).card:ℝ) ≤ 
      (23/30:ℝ)*((N:ℝ)/(p:ℝ)^2) + 6 := by
  classical
  let q:=p^2
  have qp : 0 < q := pow_pos hp.pos _
  let S := prog N q u
  let F (m r : ℕ) := S.filter (fun x=>x ≡ r [MOD m])
  have fdef (m r) : F m r = S ∩ prog N m r := by
    ext x
    simp only [F,S,prog,mem_inter,mem_filter,mem_range]
    tauto
  have cop {m : ℕ} (hm : ¬p∣m) : q.Coprime m := by
    exact (hp.coprime_iff_not_dvd.mpr hm).pow_left 2
  have small (m : ℕ) (pos : 0 < m) (less : m < p) := cop (fun dv : p∣m=>less.not_ge (Nat.le_of_dvd pos dv))
  have c2 := small 2 (by decide) (by omega)
  have c3 := small 3 (by decide) (by omega)
  have c5 := small 5 (by decide) (by omega)
  have c6 : q.Coprime 6 := c2.mul_right c3
  have c25 : q.Coprime 25 := c5.mul_right c5
  have one (m r) (pos : 0 < m) (co : q.Coprime m) :
      ((N:ℝ)/(q:ℝ))/(m:ℝ)-1 ≤ ((F m r).card:ℝ) ∧
      ((F m r).card:ℝ) ≤ ((N:ℝ)/(q:ℝ))/(m:ℝ)+1 := by
    rw [fdef]
    simpa only [div_div] using crt_bounds (N:=N) (r:=u) (s:=r) co qp pos
  have sx := (prog_bounds N q u qp).2
  have lower7 := (one 25 7 (by decide) c25).1
  have lower18 := (one 25 18 (by decide) c25).1
  have lower6 := (one 6 0 (by decide) c6).1
  have pair (m r n t) (mn : Nat.Coprime m n) (c : q.Coprime (m*n)) (pos : 0 < m*n) :
      ((S.filter (fun x=>x ≡ r [MOD m] ∧ x ≡ t [MOD n])).card:ℝ) ≤ ((N:ℝ)/(q:ℝ))/(m*n:ℕ)+1 := by
    have sub : S.filter (fun x=>x ≡ r [MOD m] ∧ x ≡ t [MOD n]) ⊆ F (m*n) (Nat.chineseRemainder mn r t) := by
      intro x hx
      obtain ⟨xs,a,b⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨xs,Nat.chineseRemainder_modEq_unique mn a b⟩
    exact (Nat.cast_le.mpr (card_le_card sub)).trans (one (m*n) (Nat.chineseRemainder mn r t) pos c).2
  have a := pair 25 7 6 0 (by decide) (c25.mul_right c6) (by decide)
  have b := pair 25 18 6 0 (by decide) (c25.mul_right c6) (by decide)
  have comb := sieve_three S (fun x=>x≡7 [MOD 25]) (fun x=>x≡18 [MOD 25]) (fun x=>x≡0 [MOD 6])
    (fun x _ h1 h2=>by change x%25=7 at h1; change x%25=18 at h2; omega)
  have good : S.filter (fun x=>¬(x≡7 [MOD 25]) ∧ ¬(x≡18 [MOD 25]) ∧ ¬(x≡0 [MOD 6])) =
              S.filter (fun x=>x%25≠7 ∧ x%25≠18 ∧ ¬6∣x) := by
    ext x; simp only [mem_filter,Nat.modEq_zero_iff_dvd]; rfl
  rw [good] at comb
  change ((S.filter _).card:ℝ)+(F 25 7).card+(F 25 18).card+(F 6 0).card ≤ _ at comb
  change ((S.filter _).card:ℝ) ≤ (23/30)*((N:ℝ)/(p:ℝ)^2)+6
  have pq : (q:ℝ)=(p:ℝ)^2 := by simp [q]
  rw [←pq]
  change (S.card:ℝ) ≤ (N:ℝ)/(q:ℝ)+1 at sx
  norm_num only [Nat.reduceMul,Nat.cast_ofNat] at a b
  linarith only [sx,lower7,lower18,lower6,a,b,comb]
end Deldor14.Erdos848Phase

/- Error bounds with prescribed small prime factors of the pivot. -/
namespace Erdos848Fifteen
open Erdos848Progression Finset Erdos848Gap
set_option maxHeartbeats 2000000 in
theorem universal_wide (b : ℕ) (bp : 0<b) (size : b≤5000000000)  :
    2*2^b.primeFactors.card ≤ 1024 := by
  classical
  let s : Finset ℕ := {2,3,5,7,11,13,17,19,23}
  let weight (p : ℕ) : ℚ := if p∈s then 29 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (29:ℚ) ≤ weight p * p^(b.factorization p) := by

    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 29 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 29≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (29:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 65028 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 65028 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (29:ℚ)^b.primeFactors.card ≤ 65028*b := by
    calc _ = ∏ _∈b.primeFactors,(29:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 29^b.primeFactors.card ≤ 65028*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 9 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<29) (show 10≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
set_option maxHeartbeats 2000000 in
theorem universal_small (b : ℕ) (bp : 0<b) (size : b≤200000000)  :
    2*2^b.primeFactors.card ≤ 512 := by
  classical
  let s : Finset ℕ := {2,3,5,7,11,13,17,19}
  let weight (p : ℕ) : ℚ := if p∈s then 23 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (23:ℚ) ≤ weight p * p^(b.factorization p) := by

    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 23 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 23≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (23:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 8074 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 8074 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (23:ℚ)^b.primeFactors.card ≤ 8074*b := by
    calc _ = ∏ _∈b.primeFactors,(23:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 23^b.primeFactors.card ≤ 8074*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 8 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<23) (show 9≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
set_option maxHeartbeats 2000000 in
theorem missing_three_short (b : ℕ) (bp : 0<b) (size : b≤2000000000) (missing3 : ¬3∣b)  :
    2*2^b.primeFactors.card ≤ 512 := by
  classical
  let s : Finset ℕ := {2,5,7,11,13,17,19,23}
  let weight (p : ℕ) : ℚ := if p∈s then 29 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=2 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (29:ℚ) ≤ weight p * p^(b.factorization p) := by
    have miss3 : p ≠ 3 := fun e=>missing3 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 29 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 29≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (29:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 6727 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 6727 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (29:ℚ)^b.primeFactors.card ≤ 6727*b := by
    calc _ = ∏ _∈b.primeFactors,(29:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 29^b.primeFactors.card ≤ 6727*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 8 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<29) (show 9≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
set_option maxHeartbeats 2000000 in
theorem missing_three_seven (b : ℕ) (bp : 0<b) (size : b≤5000000000) (missing3 : ¬3∣b) (missing7 : ¬7∣b)  :
    2*2^b.primeFactors.card ≤ 512 := by
  classical
  let s : Finset ℕ := {2,5,11,13,17,19,23,29}
  let weight (p : ℕ) : ℚ := if p∈s then 31 / (p:ℚ) else 1
  have nums (p : ℕ) (hp : p∈s) : p=2 ∨ p=5 ∨ p=11 ∨ p=13 ∨ p=17 ∨ p=19 ∨ p=23 ∨ p=29 := by simpa [s] using hp
  have ge (p : ℕ) : 1≤weight p := by
    by_cases hp : p∈s
    · rcases nums p hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [weight,s]
    · simp [weight,hp]
  have per (p : ℕ) (hp : p∈b.primeFactors) : (31:ℚ) ≤ weight p * p^(b.factorization p) := by
    have miss3 : p ≠ 3 := fun e=>missing3 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have miss7 : p ≠ 7 := fun e=>missing7 (e ▸ Nat.dvd_of_mem_primeFactors hp)
    have prime := Nat.prime_of_mem_primeFactors hp
    have nz : p∈b.factorization.support := by simpa only [Nat.support_factorization] using hp
    have expo : 0<b.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp nz)
    have qpos : (1:ℚ) ≤ p := by exact_mod_cast prime.one_le
    have factor : (p:ℚ) ≤ p^(b.factorization p) := by
      simpa using pow_le_pow_right₀ qpos (show 1≤b.factorization p from expo)
    by_cases h : p∈s
    · simp only [weight,if_pos h]
      exact (div_mul_cancel₀ 31 (show (p:ℚ)≠0 by positivity)).symm.le.trans
        (mul_le_mul_of_nonneg_left factor (by positivity))
    · have bound : 31≤p := by
        by_contra! small
        interval_cases p <;> norm_num [s] at *
      simp only [weight,if_neg h,one_mul]
      exact (show (31:ℚ)≤p by exact_mod_cast bound).trans factor
  have wTotal : ∏ p∈b.primeFactors,weight p ≤ 2769 := by
    rw [← Finset.prod_subset (s₁:=b.primeFactors ∩ s) (s₂:=b.primeFactors) (f:=weight) Finset.inter_subset_left (by
      intro p hp hn
      exact if_neg (fun h => hn (Finset.mem_inter.mpr ⟨hp,h⟩)))]
    calc _ ≤ ∏ p∈s,weight p := Finset.prod_le_prod_of_subset_of_one_le Finset.inter_subset_right
          (fun p _ => (by linarith [ge p] : 0≤weight p)) (fun p _ _ => ge p)
         _ ≤ 2769 := by norm_num [weight,s,Finset.prod_insert]
  have prod : (∏ p∈b.primeFactors,(p:ℚ)^(b.factorization p))=b := by
    exact_mod_cast Nat.prod_factorization_pow_eq_self bp.ne'
  have comparison : (31:ℚ)^b.primeFactors.card ≤ 2769*b := by
    calc _ = ∏ _∈b.primeFactors,(31:ℚ) := by simp
         _ ≤ ∏ p∈b.primeFactors,weight p*p^(b.factorization p) :=
           Finset.prod_le_prod (fun _ _ => by norm_num) per
         _ ≤ _ := by rw [Finset.prod_mul_distrib,prod]; gcongr
  have n : 31^b.primeFactors.card ≤ 2769*b := by exact_mod_cast comparison
  have cnt : b.primeFactors.card ≤ 8 := by
    by_contra! large
    have pows := Nat.pow_le_pow_right (by decide : 0<31) (show 9≤b.primeFactors.card by omega)
    norm_num at pows
    omega
  have pows := Nat.pow_le_pow_right (by decide : 0<2) cnt
  norm_num at pows
  omega
private theorem count_by_theta_refined (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M.primeCounting+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ M.primesLE := by
    intro q hq
    obtain ⟨hp,hle⟩ := Finset.mem_filter.mp hq
    exact Nat.mem_primesLE.mpr ⟨hle,(Nat.mem_primesLE.mp hp).2⟩
  have hsmall := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at hsmall
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M.primeCounting := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M.primeCounting : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


private theorem log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num


set_option maxRecDepth 1500 in
private theorem count_by_theta (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ Finset.Icc 1 M := by
    intro q hq
    obtain ⟨hp, hle⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.pos, hle⟩
  have hsmall : small.card ≤ M := by simpa using Finset.card_le_card sub
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])


theorem small_primes_48 {N : ℕ} (big : 1500000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 48*p ≤ N) :
    450 * Q.card ≤ N := by
  let X := N/48
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta_refined X (2^20) 20 (by decide) (log_nat_two_pow 20)
  have inner := count_by_theta (2^20) (2^11) 11 (by decide) (log_nat_two_pow 11)
  have trunc : 48*X≤N := by dsimp [X]; omega
  norm_num only [Nat.reducePow] at weight inner
  omega

theorem small_primes_224 {N : ℕ} (big : 1500000000 ≤ N) (Q : Finset ℕ)
    (prime : ∀ p ∈ Q, p.Prime) (small : ∀ p ∈ Q, 224*p ≤ N) :
    1880 * Q.card ≤ N := by
  let X := N/224
  have sub : Q ⊆ X.primesLE := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨by dsimp [X]; have := small p hp; omega,prime p hp⟩
  have count := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at count
  have weight := count_by_theta_refined X (2^18) 18 (by decide) (log_nat_two_pow 18)
  have inner := count_by_theta (2^18) (2^11) 11 (by decide) (log_nat_two_pow 11)
  have trunc : 224*X≤N := by dsimp [X]; omega
  norm_num only [Nat.reducePow] at weight inner
  omega

def noise (b : ℕ) : ℕ := if 6∣b then 2350 else if 2∣b then (if 7∣b then 1230 else 1770) else if 3∣b then 2440 else 950

private theorem budget {N b z : ℕ} (big : 1500000000 ≤ N) (upper : N ≤ 5000000000) (bp : 0 < b) (bn : b ≤ N)
    (short : 20*b≤N → z≤822*(2*2^b.primeFactors.card))
    (plain : z ≤ 3072*(2*2^b.primeFactors.card))
    (save : ∀ k, (k=2 ∨ k=3 ∨ k=6) → k∣b → k*z≤(3072+2*k*(2*N/b+1))*(2*2^b.primeFactors.card)) :
    noise b * z ≤ N := by
  have support := universal_wide b bp (bn.trans upper)
  by_cases little : 20*b≤N
  · have zc := short little
    by_cases tiny : b≤200000000
    · have small := universal_small b bp tiny
      unfold noise
      split_ifs <;> omega
    · unfold noise
      split_ifs <;> omega
  have logb : 2*N/b≤39 := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul bp).mpr (by omega))
  have cut (m : ℕ) : 3072+2*m*(2*N/b+1) ≤ 3072+80*m := by
    have e := Nat.mul_le_mul_left (2*m) (Nat.succ_le_succ logb)
    nlinarith only [e]
  have tight (hu : 2000000000 < b) : 2*N/b≤4 := by
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul bp).mpr (by omega))
  by_cases six : 6∣b
  · rw [noise,if_pos six]
    have hs := save 6 (by decide) six
    have q := hs.trans (Nat.mul_le_mul (cut 6) support)
    omega
  rw [noise,if_neg six]
  by_cases ev : 2∣b
  · rw [if_pos ev]
    have no3 : ¬3∣b := fun t=>six (by omega)
    have hs := save 2 (by decide) ev
    by_cases sev : 7∣b
    · rw [if_pos sev]
      by_cases shortb : b≤2000000000
      · have le := missing_three_short b bp shortb no3
        have q := hs.trans (Nat.mul_le_mul (cut 2) le)
        omega
      · have shr := tight (by omega)
        have cu : 3072+2*2*(2*N/b+1)≤3092 := by omega
        have q := hs.trans (Nat.mul_le_mul cu support)
        omega
    · rw [if_neg sev]
      have le := missing_three_seven b bp (bn.trans upper) no3 sev
      have q := hs.trans (Nat.mul_le_mul (cut 2) le)
      omega
  rw [if_neg ev]
  by_cases tri : 3∣b
  · rw [if_pos tri]
    have hs := save 3 (by decide) tri
    by_cases shortb : b≤3000000000
    · have le := Erdos848Odd400.odd_with3 b bp shortb ev
      have q := hs.trans (Nat.mul_le_mul (cut 3) le)
      omega
    · have shr := tight (by omega)
      have cu : 3072+2*3*(2*N/b+1)≤3102 := by omega
      have q := hs.trans (Nat.mul_le_mul cu support)
      omega
  · rw [if_neg tri]
    have le := Erdos848Odd400.odd_not3_wide b bp ((bn.trans upper).trans (by decide)) ev tri
    omega
theorem large_mixed_48 {N b : ℕ} (big : 1500000000 ≤ N) (upper : N≤5000000000) (bN : b < N)
    (S : Finset ℕ) (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 48*p ∧ p^2 ∣ b*n+1) :
    noise b*S.card ≤ N := by
  classical
  by_cases non : S.Nonempty
  · let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
    let d (n : ℕ) := (b*n+1)/(p n)^2
    have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 48*p n ∧ (p n)^2 ∣ b*n+1 := by
      simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
    have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2.2
    obtain ⟨v,hv⟩ := non
    have bp : 0 < b := by
      by_contra! h
      have bz : b=0 := by omega
      have hd := (info v hv).2.2
      simp only [bz,zero_mul,zero_add,Nat.dvd_one] at hd
      have hq := (info v hv).2.1
      have pq : 2 ≤ p v := by omega
      have sq := Nat.pow_le_pow_left pq 2
      omega
    have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
      have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
      rw [Nat.mul_add,Nat.mul_one] at h
      omega
    have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
      have positive : 0<d n := by
        by_contra! dz
        have e := eq n hn
        rw [show d n=0 by omega,zero_mul] at e
        omega
      have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
      have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
      have scaled := congrArg (c^2*·) (eq n hn)
      have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
      exact Nat.lt_of_mul_lt_mul_right cmp
    have pr (n) (hn : n∈S) := (info n hn).1
    have cut (n) (hn : n∈S) := (info n hn).2.1
    exact budget big upper bp bN.le (fun small=>mixed48_small bp bN.le small S p d eq pr link cut)
      (mixed48_count bp bN.le S p d eq pr link cut)
      (fun k choice kb=>mixed48_progression bp bN.le S p d eq pr
        (fun n hn=>unit_square_six choice kb (eq n hn)) link cut)
  · rw [Finset.not_nonempty_iff_eq_empty.mp non]
    simp

end Erdos848Fifteen

/- Uniform bounds on nonsquarefree products along either residue class. -/
namespace Erdos848Fifteen
open Finset Erdos848Port

private theorem prime_sum (N b : ℕ) (P : Finset ℕ) (no5 : P ⊆ no5PrimesUpTo N)
    (no2 : 2 ∣ b → P ⊆ offPrimesUpTo N) :
    (∑ p ∈ P, (1:ℝ)/(25*(p:ℝ)^2)) ≤ (if 2 ∣ b then 163 else 413)/25000 := by
  have h : (∑ p ∈ P,(1:ℚ)/(p:ℚ)^2) ≤ (if 2 ∣ b then 163 else 413)/1000 := by
    by_cases h : 2 ∣ b
    · rw [if_pos h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (no2 h) (fun i _ _ => by positivity)).trans
        (sum_offPrimesUpTo_le N)
    · rw [if_neg h]
      exact (Finset.sum_le_sum_of_subset_of_nonneg no5 (fun i _ _ => by positivity)).trans
        (sum_no5PrimesUpTo_le N)
  have cast := (Rat.cast_le (K:=ℝ)).mpr h
  simp only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,
    apply_ite Rat.cast,Rat.cast_ofNat] at cast
  have f (p : ℕ) : (1:ℝ)/(25*(p:ℝ)^2) = (1/25) * (1/(p:ℝ)^2) := by ring
  simp only [f,←Finset.mul_sum]
  by_cases z : 2 ∣ b <;> simp [z] at cast ⊢ <;> linarith only [cast]

private theorem weighted_bound {N b r C lo hi : ℕ} (largeN : 100 ≤ N) (bn : b < N)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n ∈ S, n ≡ r [MOD 25])
    (bad : ∀ n ∈ S, ¬ Squarefree (b*n+1)) (h25 : ∀ n ∈ S, ¬25 ∣ b*n+1)
    (small : ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → (∀ p ∈ Q,C*p≤N) → lo*Q.card≤N)
    (large : ∀ T : Finset ℕ, (∀ n∈T,n<N ∧ ∃ p : ℕ,p≤N ∧ N<C*p ∧ p^2∣b*n+1) → hi*T.card≤N)
    (lop : 0<lo) (hip : 0<hi) (w : ℝ)
    (limit : ∀ Q : Finset ℕ, Q ⊆ no5PrimesUpTo N → (2∣b → Q ⊆ offPrimesUpTo N) →
      (3∣b → 3∉Q) → (7∣b → 7∉Q) → ∑ p∈Q,(1:ℝ)/(25*(p:ℝ)^2) ≤ w) :
    (S.card:ℝ) ≤ N*w + (N:ℝ)/lo + (N:ℝ)/hi := by
  classical
  let P := (no5PrimesUpTo N).filter (fun p => ¬p∣b)
  let Q := P.filter (fun p => C*p≤N)
  let R := P.filter (fun p => N<C*p)
  let B (p : ℕ) := (range N).filter (fun n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
  have no5 : P ⊆ no5PrimesUpTo N := Finset.filter_subset .. 
  have no2 (ev : 2 ∣ b) : P ⊆ offPrimesUpTo N := by
    intro p hp
    obtain ⟨mem,div⟩ := Finset.mem_filter.mp hp
    obtain ⟨pm,p5⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨pm,fun h => div (h ▸ ev),p5⟩
  have prime {p : ℕ} (h : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).2
  have bound {p : ℕ} (h : p ∈ P) : p ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).1)
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    obtain ⟨p,hp,p5,pdv⟩ := prime_square_exists_ne5 (bad n hn) (h25 n hn)
    have nN := Finset.mem_range.mp (inRange hn)
    have pred := Nat.mul_le_mul (Nat.le_pred_of_lt bn) (Nat.le_pred_of_lt nN)
    have le := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) ((Nat.add_le_add_right pred 1).trans_lt
      (sq_pred_add_one_lt_sq N largeN)) pdv
    have pnd : ¬p∣b := by
      intro h
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left h n)).mp
        (Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) pdv))
    have mem : p ∈ P := by
      simp [P,no5PrimesUpTo,primesUpTo,hp,Nat.lt_succ_of_le le,p5,pnd]
    have nb : n ∈ B p := Finset.mem_filter.mpr ⟨inRange hn,res n hn,pdv⟩
    by_cases h : C*p ≤ N
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,h⟩,nb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,Nat.lt_of_not_ge h⟩,nb⟩)
  have cards : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (card_le_card cover).trans (card_union_le ..)
  have sub : Q ⊆ P := Finset.filter_subset ..
  have lc := small Q (fun _ h => prime (sub h)) (fun _ h => (mem_filter.mp h).2)
  have hc := large (R.biUnion B) (by
    intro n hn
    obtain ⟨p,hp,nb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨nN,pdv⟩ := Finset.mem_filter.mp nb
    exact ⟨Finset.mem_range.mp nN,p,bound (mem_filter.mp hp).1,(mem_filter.mp hp).2,pdv.2⟩)
  have first := sieve_set_card_bound N 25 Q (Q.biUnion B) (fun p n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
    Subset.rfl (fun p hp => off_count_modEq25_le' N p b r (prime (sub hp)) (mem_filter.mp (no5 (sub hp))).2)
  have est := limit Q (sub.trans no5) (fun he => sub.trans (no2 he)) (fun dv h => (mem_filter.mp (sub h)).2 dv) (fun dv h => (mem_filter.mp (sub h)).2 dv)
  have weight := mul_le_mul_of_nonneg_left est (show 0 ≤ (N:ℝ) by positivity)
  have countR : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast cards
  have lcr : (Q.card:ℝ) ≤ (N:ℝ)/lo := by
    apply (le_div_iff₀ (by exact_mod_cast lop)).mpr
    rw [mul_comm]
    exact_mod_cast lc
  have hcr : ((R.biUnion B).card:ℝ) ≤ (N:ℝ)/hi := by
    apply (le_div_iff₀ (by exact_mod_cast hip)).mpr
    rw [mul_comm]
    exact_mod_cast hc
  linarith only [first,weight,countR,lcr,hcr]


theorem bad_middle {N b r : ℕ} (big : 1500000000≤N) (upper : N≤5000000000) (bn : b<N)
    (S : Finset ℕ) (inRange : S⊆range N) (res : ∀n∈S,n ≡ r [MOD 25])
    (bad : ∀n∈S,¬Squarefree (b*n+1)) (h25 : ∀n∈S,¬25∣b*n+1) :
    (S.card:ℝ) ≤ (N:ℝ)*((if 2∣b then 163 else 413)/25000 - (if 3∣b then 1/225 else 0)) +
       (N:ℝ)/450+(N:ℝ)/(noise b) := by
  have bound := weighted_bound (by omega : 100≤N) bn S inRange res bad h25
    (small_primes_48 big) (large_mixed_48 big upper bn) (by decide)
    (by unfold noise; split_ifs <;> decide)
    (((if 2∣b then 163 else 413)/25000:ℝ) - (if 3∣b then 1/225 else 0)) (by
      intro Q no5 no2 no3 _
      by_cases tri : 3∣b
      · rw [if_pos tri]
        have h3 : 3∈primesUpTo N := by simp [primesUpTo,Nat.prime_three,show 3<N+1 by omega]
        have in5 : insert 3 Q ⊆ no5PrimesUpTo N := Finset.insert_subset (mem_filter.mpr ⟨h3,by decide⟩) no5
        have in2 (ev : 2∣b) : insert 3 Q ⊆ offPrimesUpTo N := Finset.insert_subset (mem_filter.mpr ⟨h3,by decide⟩) (no2 ev)
        have e := prime_sum N b (insert 3 Q) in5 in2
        rw [sum_insert (no3 tri)] at e
        norm_num only [Nat.cast_ofNat] at e
        linarith only [e]
      · rw [if_neg tri,sub_zero]
        exact prime_sum N b Q no5 no2)
  exact bound

theorem bad_middle_fourteen {N b r : ℕ} (big : 1500000000≤N) (upper : N≤5000000000) (bn : b<N)
    (S : Finset ℕ) (inRange : S⊆range N) (res : ∀n∈S,n ≡ r [MOD 25])
    (bad : ∀n∈S,¬Squarefree (b*n+1)) (h25 : ∀n∈S,¬25∣b*n+1)
    (fourteen : 14∣b) (not6 : ¬6∣b) :
    (S.card:ℝ)≤(875/100000)*(N:ℝ) := by
  have even : 2∣b := (by decide : 2∣14).trans fourteen
  have seven : 7∣b := (by decide : 7∣14).trans fourteen
  have h := weighted_bound (by omega : 100≤N) bn S inRange res bad h25
    (small_primes_48 big) (large_mixed_48 big upper bn) (by decide) (by simp [noise,not6,even,seven])
    (163/25000-1/1225) (by
      intro Q no5 no2 _ no7
      have h7 : 7∈primesUpTo N := by simp [primesUpTo,show Nat.Prime 7 by decide,show 7<N+1 by omega]
      have in5 : insert 7 Q ⊆ no5PrimesUpTo N := insert_subset (mem_filter.mpr ⟨h7,by decide⟩) no5
      have in2 : insert 7 Q ⊆ offPrimesUpTo N := insert_subset (mem_filter.mpr ⟨h7,by decide⟩) (no2 even)
      have z := prime_sum N b (insert 7 Q) in5 (fun _=>in2)
      rw [sum_insert (no7 seven),if_pos even] at z
      norm_num only [Nat.cast_ofNat] at z
      linarith only [z])
  simp only [noise,not6,if_false,even,if_true,seven,Nat.cast_ofNat] at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]
end Erdos848Fifteen
namespace Deldor14.Erdos848Middle
open Finset Erdos848
abbrev slice (A : Finset ℕ) (r : ℕ) := Deldor14.Erdos848Tenth.slice A r
abbrev outside (A : Finset ℕ) := Deldor14.Erdos848Tenth.outside A
theorem row_bound {N b r : ℕ} {A : Finset ℕ} (big : 1500000000≤N) (upper : N≤5000000000)
    (inside : A⊆range N) (adm : NonSquarefreeProductProp A) (ba : b∈A)
    (base : r=7 ∨ r=18) (diff : b%25≠r) :
    let z:=((slice A r).card:ℝ)
    z≤(1980/100000)*(N:ℝ) ∧ (2∣b → z≤(957/100000)*(N:ℝ)) ∧ (3∣b → z≤(1471/100000)*(N:ℝ)) ∧
    (6∣b → z≤(475/100000)*(N:ℝ)) ∧ (2∣b → ¬3∣b → ¬7∣b → z≤(932/100000)*(N:ℝ)) := by
  have h := Erdos848Fifteen.bad_middle (r:=r) big upper (mem_range.mp (inside ba))
    (slice A r) ((filter_subset ..).trans inside) (by
      intro x hx
      change x%25=r%25
      rw [(mem_filter.mp hx).2,Nat.mod_eq_of_lt (by omega : r < 25)]) (by
      intro x hx; exact adm b ba x (mem_filter.mp hx).1) (by
      intro x hx; exact Deldor14.Erdos848Tenth.between_not25 base diff (mem_filter.mp hx).2)
  dsimp only
  by_cases six : 6∣b
  · have d0 : 2∣b := by omega
    have d1 : 3∣b := by omega
    have d2 : 6∣b := by omega
    simp only [Erdos848Fifteen.noise,if_pos d0,if_pos d1,if_pos d2,Nat.cast_ofNat] at h
    exact ⟨by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun _=>by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun _=>by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun _=>by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun _ no _=>(no d1).elim⟩
  by_cases even7 : 2∣b ∧ 7∣b
  · have d0 : 2∣b := by omega
    have d1 : ¬3∣b := by omega
    have d2 : ¬6∣b := by omega
    have d3 : 7∣b := by omega
    simp only [Erdos848Fifteen.noise,if_pos d0,if_neg d1,if_neg d2,if_pos d3,Nat.cast_ofNat] at h
    exact ⟨by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun _=>by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun eq=>(d1 eq).elim,
      fun eq=>(d2 eq).elim,
      fun _ _ no=>(no d3).elim⟩
  by_cases even : 2∣b
  · have d0 : 2∣b := by omega
    have d1 : ¬3∣b := by omega
    have d2 : ¬6∣b := by omega
    have d3 : ¬7∣b := by omega
    simp only [Erdos848Fifteen.noise,if_pos d0,if_neg d1,if_neg d2,if_neg d3,Nat.cast_ofNat] at h
    exact ⟨by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun _=>by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun eq=>(d1 eq).elim,
      fun eq=>(d2 eq).elim,
      fun _ _ _=>by linarith only [h,Nat.cast_nonneg (α:=ℝ) N]⟩
  by_cases tri : 3∣b
  · have d0 : ¬2∣b := by omega
    have d1 : 3∣b := by omega
    have d2 : ¬6∣b := by omega
    simp only [Erdos848Fifteen.noise,if_neg d0,if_pos d1,if_neg d2,Nat.cast_ofNat] at h
    exact ⟨by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun eq=>(d0 eq).elim,
      fun _=>by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
      fun eq=>(d2 eq).elim,
      fun ev _ _=>(d0 ev).elim⟩
  have d0 : ¬2∣b := by omega
  have d1 : ¬3∣b := by omega
  have d2 : ¬6∣b := by omega
  simp only [Erdos848Fifteen.noise,if_neg d0,if_neg d1,if_neg d2,Nat.cast_ofNat] at h
  exact ⟨by linarith only [h,Nat.cast_nonneg (α:=ℝ) N],
    fun eq=>(d0 eq).elim,
    fun eq=>(d1 eq).elim,
    fun eq=>(d2 eq).elim,
    fun ev _ _=>(d0 ev).elim⟩

theorem row_fourteen {N b r : ℕ} {A : Finset ℕ} (big : 1500000000≤N) (upper : N≤5000000000)
    (inside : A⊆range N) (adm : NonSquarefreeProductProp A) (ba : b∈A) (fourteen : 14∣b) (not6 : ¬6∣b)
    (base : r=7 ∨ r=18) (diff : b%25≠r) : ((slice A r).card:ℝ) ≤ (875/100000)*(N:ℝ) := by
  apply Erdos848Fifteen.bad_middle_fourteen (r:=r) big upper (mem_range.mp (inside ba)) _ ((filter_subset ..).trans inside) _ _ _ fourteen not6
  · intro x hx
    change x%25=r%25
    rw [(mem_filter.mp hx).2,Nat.mod_eq_of_lt (by omega : r < 25)]
  · intro x hx
    exact adm b ba x (mem_filter.mp hx).1
  · intro x hx
    exact Deldor14.Erdos848Tenth.between_not25 base diff (mem_filter.mp hx).2
end Deldor14.Erdos848Middle

/- Diagonal estimates for the all-odd case, including a single residue modulo four. -/
namespace Erdos848Fifteen
open Erdos848Gap Finset
private theorem count_keys (S : Finset ℕ) (key : ℕ → ℕ × ℕ) (cols rows : ℕ)
    (bound : ∀ n∈S, (key n).1 < cols ∧ (key n).2 < rows) (injective : Set.InjOn key S) :
    S.card ≤ cols*rows := by
  let labels := (Finset.range cols) ×ˢ (Finset.range rows)
  have maps : (S : Set ℕ).MapsTo key labels := by
    intro n hn
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (bound n hn).1,Finset.mem_range.mpr (bound n hn).2⟩
  simpa [labels] using Finset.card_le_card_of_injOn key maps injective

theorem large_diagonal_224 {N : ℕ} (big : 1500000000 ≤ N) (S : Finset ℕ)
    (choosePrime : ∀n∈S, n < N ∧ ∃p : ℕ, p≤N ∧ N < 224*p ∧ p^2 ∣ n^2+1) :
    3700*S.card ≤ N := by
  classical
  let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
  let d (n : ℕ) := (n^2+1)/(p n)^2
  have info (n : ℕ) (hn : n ∈ S) : p n ≤ N ∧ N < 224*p n ∧ (p n)^2 ∣ n^2+1 := by
    simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
  have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = n^2+1 := Nat.div_mul_cancel (info n hn).2.2
  have divisorBound (n : ℕ) (hn : n∈S) : d n < 50176 := by
    by_contra! h
    have h1 := Nat.mul_le_mul_right ((p n)^2) h
    have h2 := Nat.pow_lt_pow_left (choosePrime n hn).1 (by decide : 2≠0)
    have h3 := Nat.pow_lt_pow_left (info n hn).2.1 (by decide : 2≠0)
    nlinarith only [h1,eq n hn,h2,h3]
  let key (n : ℕ) := (d n, Nat.log 2 (N / p n))
  have posp (n : ℕ) (hn : n∈S) : 0<p n := by have h := (info n hn).2.1; omega
  have labels (n : ℕ) (hn : n∈S) : (key n).1 < 50176 ∧ (key n).2 < 8 := by
    refine ⟨divisorBound n hn,?_⟩
    change Nat.log 2 (N / p n) < 8
    apply Nat.log_lt_of_lt_pow' (by decide : (8:ℕ) ≠ 0)
    have co := (info n hn).2.1
    have up := (Nat.div_lt_iff_lt_mul (posp n hn)).mpr co
    norm_num
    omega
  have pair {x y : ℕ} (hx : x∈S) (hy : y∈S) (k : key x=key y) (lt : p x < p y) : False := by
    have de := congrArg Prod.fst k
    change d x = d y at de
    have label := congrArg Prod.snd k
    change Nat.log 2 (N / p x) = Nat.log 2 (N / p y) at label
    have nonzero : N / p y ≠ 0 := (Nat.div_pos (info y hy).1 (posp y hy)).ne'
    have high := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (N / p x)
    rw [label,pow_succ] at high
    have high' := (Nat.div_lt_iff_lt_mul (posp x hx)).mp high
    have low := (Nat.le_div_iff_mul_le (posp y hy)).mp (Nat.pow_log_le_self 2 nonzero)
    let C := 2 ^ Nat.log 2 (N / p y)
    change C*p y ≤ N at low
    change N < (C*2)*p x at high'
    have col : 0<C := pow_pos (by decide) _
    have gap : p y ≤ 2*p x := by
      by_contra! no
      have h := Nat.mul_le_mul_left C no.le
      nlinarith only [high',low,h]
    have sm : 2 ≤ p x := by have h := (info x hx).2.1; omega
    exact diagonal_gap sm lt gap (eq x hx).symm (de ▸ (eq y hy).symm)
  have inj : Set.InjOn key S := by
    intro x hx y hy hk
    rcases lt_trichotomy (p x) (p y) with h | h | h
    · exact (pair hx hy hk h).elim
    · have de := congrArg Prod.fst hk
      change d x = d y at de
      have xx := eq x hx
      have yy := eq y hy
      rw [de,h] at xx
      have sq : x^2=y^2 := by omega
      exact (Nat.pow_left_inj (by decide : 2 ≠ 0)).mp sq
    · exact (pair hy hx hk.symm h).elim
  have bound := count_keys S key 50176 8 labels inj
  omega

end Erdos848Fifteen

/- Uniform diagonal sieve on a restricted set of residue classes. The
large-square argument is the Pell spacing estimate of Erdős848Gap; the
two-root split is the diagonal sieve of Erdos848Port. -/
namespace Deldor14.Erdos848Middle
open Finset Erdos848Port
private theorem at_most_one_large_diagonal_root (N p : ℕ) (hp : p.Prime) (hmod : p%4=1)
    (large : 2*N ≤ p^2) (S : Finset ℕ) (inside : ∀ n ∈ S, n < N ∧ p^2 ∣ n^2+1) :
    S.card ≤ 1 := by
  obtain ⟨r,t,opposite,_,_,_,allRoots⟩ := two_roots_mod_p_squared p hp hmod
  have nz : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have root (n : ℕ) (hn : n ∈ S) : (n : ZMod (p^2)) = r ∨ (n : ZMod (p^2)) = -r := by
    have eq0 := (ZMod.natCast_eq_zero_iff (n^2+1) (p^2)).mpr (inside n hn).2
    have eq1 : (n : ZMod (p^2))^2+1 = 0 := by exact_mod_cast eq0
    simpa only [opposite] using allRoots _ (eq_neg_of_add_eq_zero_left eq1)
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have xb := (inside x hx).1
  have yb := (inside y hy).1
  have cases : (x : ZMod (p^2)) = y ∨ (x : ZMod (p^2)) + y = 0 := by
    rcases root x hx with h | h <;> rcases root y hy with g | g <;> simp [h,g]
  rcases cases with h | h
  · have eq := (ZMod.natCast_eq_natCast_iff x y (p^2)).mp h
    change x%(p^2)=y%(p^2) at eq
    simpa only [Nat.mod_eq_of_lt (show x<p^2 by omega),
      Nat.mod_eq_of_lt (show y<p^2 by omega)] using eq
  · have eq : (p^2) ∣ x+y := (ZMod.natCast_eq_zero_iff (x+y) (p^2)).mp (by simpa using h)
    have h0 := Nat.mod_eq_zero_of_dvd eq
    rw [Nat.mod_eq_of_lt (by omega)] at h0
    omega

private theorem diagonal_partial (N k d : ℕ) (P S : Finset ℕ) (B : ℕ → Finset ℕ)
    (primes : P ⊆ diagPrimesUpTo N) (covered : S ⊆ P.biUnion B)
    (old : ∀ p ∈ P, (B p).card ≤ d*(N/(k*p^2)+1))
    (inside : ∀ p, ∀n∈B p, n < N ∧ p^2 ∣ n^2+1) :
    (S.card : ℝ) ≤ (d:ℝ)*((N : ℝ) * (∑ p ∈ P, (1 : ℝ)/(k*(p:ℝ)^2))) +
      (P.card : ℝ) + (d:ℝ)*(((2*N).sqrt : ℝ)/4+2) := by
  classical
  let small := P.filter (· ≤ (2*N).sqrt)
  have point (p : ℕ) (hp : p ∈ P) :
      ((B p).card : ℝ) ≤ ((d:ℝ)*(N : ℝ))*((1 : ℝ)/(k*(p:ℝ)^2)) +
        (if p ≤ (2*N).sqrt then (d : ℝ) else 0) + 1 := by
    by_cases cut : p ≤ (2*N).sqrt
    · rw [if_pos cut]
      have denom := Nat.cast_div_le (α := ℝ) (m := N) (n := k*p^2)
      push_cast at denom
      have o : ((B p).card : ℝ) ≤ (d:ℝ)*(((N/(k*p^2) : ℕ):ℝ)+1) := by exact_mod_cast old p hp
      simp only [div_eq_mul_inv,one_mul] at denom ⊢
      have weighted := mul_le_mul_of_nonneg_left denom (Nat.cast_nonneg (α:=ℝ) d)
      linarith only [o,weighted]
    · rw [if_neg cut]
      have prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (primes hp)).1).2
      have mod4 : p%4=1 := (Finset.mem_filter.mp (primes hp)).2.1
      have lim : 2*N ≤ p^2 := (Nat.sqrt_lt'.mp (lt_of_not_ge cut)).le
      have o : ((B p).card : ℝ) ≤ 1 := by exact_mod_cast at_most_one_large_diagonal_root N p prime mod4 lim (B p) (inside p)
      have hpos : 0 ≤ ((d:ℝ)*(N : ℝ))*((1 : ℝ)/(k*(p:ℝ)^2)) := by positivity
      linarith only [o,hpos]
  have total : S.card ≤ ∑ p ∈ P, (B p).card :=
    (Finset.card_le_card covered).trans Finset.card_biUnion_le
  have totalR : (S.card : ℝ) ≤ ∑ p ∈ P, ((B p).card : ℝ) := by exact_mod_cast total
  have upper := totalR.trans (Finset.sum_le_sum point)
  have count : (∑ p ∈ P, if p ≤ (2*N).sqrt then (d : ℝ) else 0) = (small.card : ℝ)*(d:ℝ) := by
    rw [← Finset.sum_filter]
    simp [small]
  have sub : small ⊆ (range ((2*N).sqrt+1)).filter (fun p=>p ≡ 1 [MOD 4]) := by
    intro p hp
    obtain ⟨pm,lim⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le lim),(mem_filter.mp (primes pm)).2.1⟩
  have cs := (card_le_card sub).trans (card_filter_mod_eq_le ((2*N).sqrt+1) 4 1)
  have cs' : 4*small.card≤(2*N).sqrt+5 := by omega
  have cR : 4*(small.card:ℝ)≤((2*N).sqrt:ℝ)+5 := by exact_mod_cast cs'
  have csr : (small.card:ℝ)≤((2*N).sqrt:ℝ)/4+2 := by linarith only [cR]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,count,Finset.sum_const, nsmul_eq_mul,
    mul_one] at upper
  linarith only [upper,mul_le_mul_of_nonneg_left csr (Nat.cast_nonneg (α:=ℝ) d)]


private lemma diag_by_mod (N M p t : ℕ) (hp : Nat.Prime p) (hmod : p % 4 = 1) (hcop : Nat.Coprime M (p^2)) :
    ((Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)).card ≤
      2 * (N / (M * p ^ 2) + 1) := by
  classical
  obtain ⟨r₁, r₂, hr⟩ :
      ∃ r₁ r₂ : ZMod (p ^ 2),
        r₁ ≠ r₂ ∧ r₁ ^ 2 = -1 ∧ r₂ ^ 2 = -1 ∧ ∀ r : ZMod (p ^ 2), r ^ 2 = -1 → r = r₁ ∨ r = r₂ := by
    obtain ⟨r,t,_,rest⟩ := two_roots_mod_p_squared p hp hmod
    exact ⟨r,t,rest⟩
  let S : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ (p ^ 2 : ℕ) ∣ n ^ 2 + 1)
  let S₁ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ n ≡ r₁.val [MOD p ^ 2])
  let S₂ : Finset ℕ :=
    (Finset.range N).filter (fun n => n ≡ t [MOD M] ∧ n ≡ r₂.val [MOD p ^ 2])
  have hsubset : S ⊆ S₁ ∪ S₂ := by
    intro n hn
    simp [S, S₁, S₂, Finset.mem_filter, Finset.mem_range] at hn ⊢
    have hdiv : (p ^ 2 : ℕ) ∣ n ^ 2 + 1 := hn.2.2
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff (n ^ 2 + 1) (p ^ 2)).2 hdiv
    have hsq : (n : ZMod (p ^ 2)) ^ 2 = (-1 : ZMod (p ^ 2)) := by
      have : (n : ZMod (p ^ 2)) ^ 2 + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using h0
      simpa using (eq_neg_of_add_eq_zero_left this)
    have hcases : (n : ZMod (p ^ 2)) = r₁ ∨ (n : ZMod (p ^ 2)) = r₂ := hr.2.2.2 _ hsq
    cases hcases with
    | inl hn1 =>
        refine Or.inl ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₁.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₁ := hn1
            _ = (r₁.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₁.val (p ^ 2)).1 hcast
    | inr hn2 =>
        refine Or.inr ?_
        refine ⟨hn.1, hn.2.1, ?_⟩
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        have hcast : (n : ZMod (p ^ 2)) = (r₂.val : ZMod (p ^ 2)) := by
          calc
            (n : ZMod (p ^ 2)) = r₂ := hn2
            _ = (r₂.val : ZMod (p ^ 2)) := by simp
        exact (ZMod.natCast_eq_natCast_iff n r₂.val (p ^ 2)).1 hcast
  have hcard : S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsubset
  have hunion : (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le _ _
  have hS₁ : S₁.card ≤ N / (M * p ^ 2) + 1 := by
    simpa [S₁, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N M (p ^ 2) t r₁.val hcop)
  have hS₂ : S₂.card ≤ N / (M * p ^ 2) + 1 := by
    simpa [S₂, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (card_filter_modEq_and_modEq_le N M (p ^ 2) t r₂.val hcop)
  have : S.card ≤ (N / (M * p ^ 2) + 1) + (N / (M * p ^ 2) + 1) :=
    le_trans (le_trans hcard hunion) (add_le_add hS₁ hS₂)
  simpa [S, two_mul] using this

private theorem diagonal_prime {N x : ℕ} (big : 100≤N) (hx : x<N)
    (x7 : x%25≠7) (x18 : x%25≠18) (diag : ¬Squarefree (x*x+1)) :
    ∃p∈diagPrimesUpTo N, p^2 ∣ x^2+1 := by
  obtain ⟨p,prime,sq⟩ := prime_square_exists_ne5 (n:=x^2+1) (by simpa [pow_two] using diag)
    (not_dvd_25_sq_add_one_of_mod_ne x ⟨x7,x18⟩)
  obtain ⟨not5,div⟩ := sq
  have not2 : p≠2 := by
    rintro rfl
    exact not_dvd_four_sq_add_one x div
  have mod4 := prime_sq_divides_implies_one_mod_four p x prime (by have := prime.two_le; omega) div
  have ge := prime_ge_13_of_mod4_one_ne5 p prime mod4 not5
  have lt : x^2+1 < N^2 := (Nat.add_le_add_right (Nat.pow_le_pow_left (show x≤N-1 by omega) 2) 1).trans_lt
    (by simpa only [pow_two] using sq_pred_add_one_lt_sq N big)
  have pn := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) lt div
  exact ⟨p,by simp [diagPrimesUpTo,primesUpTo,Nat.lt_succ_of_le pn,prime,mod4,ge],div⟩

/-- A class-restricted diagonal estimate, with the very-large-prime
remainder paid only once across all permitted residue classes. -/
theorem diagonal_budget {N M t : ℕ} (big : 1500000000≤N) (mchoice : M=25 ∨ M=50 ∨ M=150 ∨ (0<M ∧ M≤6))
    (T S : Finset ℕ) (size : T.card≤t)
    (info : ∀ x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1) ∧ x%M∈T) :
    (S.card:ℝ) ≤ (2*(t:ℝ))*(N:ℝ)*(5/359)/(M:ℝ) +
       (N:ℝ)/1880 + (2*(t:ℝ))*(N:ℝ)/108000 + (N:ℝ)/3700 := by
  classical
  let P := (diagPrimesUpTo N).filter (fun p=>224*p≤N)
  let B (p : ℕ) := S.filter (fun x=>p^2∣x^2+1)
  let low := P.biUnion B
  let high := S \ low
  have inp (p) (hp : p∈P) := (mem_filter.mp hp).1
  have prime (p) (hp : p∈P) : p.Prime := (mem_filter.mp (mem_filter.mp (inp p hp)).1).2
  have prop (p) (hp : p∈P) : p%4=1 ∧ 13≤p := (mem_filter.mp (inp p hp)).2
  have inside (p n) (hn : n∈B p) : n<N ∧ p^2∣n^2+1 :=
    ⟨(info n (mem_filter.mp hn).1).1,(mem_filter.mp hn).2⟩
  have capHigh := Erdos848Fifteen.large_diagonal_224 big high (by
    intro x hx
    obtain ⟨xS,xL⟩ := mem_sdiff.mp hx
    obtain ⟨xn,x7,x18,di,_⟩ := info x xS
    obtain ⟨p,mem,div⟩ := diagonal_prime (by omega) xn x7 x18 di
    have pn := mem_range.mp (mem_filter.mp (mem_filter.mp mem).1).1
    refine ⟨xn,p,by omega,?_,div⟩
    by_contra! small
    exact xL (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,small⟩,mem_filter.mpr ⟨xS,div⟩⟩))
  have capP := Erdos848Fifteen.small_primes_224 big P prime (by
    intro p hp
    have h := (mem_filter.mp hp).2
    omega)
  have points (p) (hp : p∈P) : (B p).card ≤ (2*t)*(N/(M*p^2)+1) := by
    let frac (r) := (range N).filter (fun x=>x ≡ r [MOD M] ∧ p^2∣x^2+1)
    have each (r) (_ : r∈T) : (frac r).card≤2*(N/(M*p^2)+1) := by
      have pp := prop p hp
      apply diag_by_mod _ _ _ _ (prime p hp) pp.1
      rcases mchoice with rfl|rfl|rfl|⟨pos,small⟩
      · exact coprime_25_pow_two_of_prime_ne5 p (prime p hp) (by omega)
      · exact coprime_50_pow_two_of_prime_ne2_ne5 p (prime p hp) (by omega) (by omega)
      · have cp6 := ((prime p hp).coprime_iff_not_dvd.mpr (fun dv=>(not_le_of_gt (by omega : 6<p)) (Nat.le_of_dvd (by decide : 0<6) dv))).symm.pow_right 2
        exact Nat.Coprime.mul_left cp6 (coprime_25_pow_two_of_prime_ne5 p (prime p hp) (by omega))
      · exact ((prime p hp).coprime_iff_not_dvd.mpr (fun dv=>(not_le_of_gt (by omega : M<p)) (Nat.le_of_dvd pos dv))).symm.pow_right _
    have subset : B p ⊆ T.biUnion frac := by
      intro x hx
      obtain ⟨sx,div⟩ := mem_filter.mp hx
      obtain ⟨xn,_,_,_,xr⟩ := info x sx
      exact mem_biUnion.mpr ⟨x%M,xr,mem_filter.mpr ⟨mem_range.mpr xn,by simp [Nat.ModEq],div⟩⟩
    simpa only [←Nat.mul_assoc,Nat.mul_comm t 2] using
      ((card_le_card subset).trans (card_biUnion_le_card_mul T frac _ each)).trans
        (Nat.mul_le_mul_right _ size)
  have est : (low.card:ℝ) ≤ (2*(t:ℝ))*((N:ℝ)*(∑p∈P,(1:ℝ)/(M*(p:ℝ)^2)))+
        (P.card:ℝ)+(2*(t:ℝ))*(((2*N).sqrt:ℝ)/4+2) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      diagonal_partial N M (2*t) P low B (fun p hp=>inp p hp) Subset.rfl points inside
  have primeSum : (∑p∈P,(1:ℝ)/(p:ℝ)^2) ≤ 5/359 := by
    have sq : (∑p∈P,(1:ℚ)/(p:ℚ)^2) ≤ 5/359 := by
      calc _ ≤ ∑p∈diagPrimesUpTo N,(1:ℚ)/(p:ℚ)^2 := sum_le_sum_of_subset_of_nonneg (fun p hp=>inp p hp) (by intros; positivity)
           _ ≤ _ := by convert sum_diagPrimesUpTo_le N using 1; norm_num
    have cast := (Rat.cast_le (K:=ℝ)).mpr sq
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using cast
  have rest : (∑p∈P,(1:ℝ)/(M*(p:ℝ)^2))= (∑p∈P,(1:ℝ)/(p:ℝ)^2)/(M:ℝ) := by
    rw [sum_div]; apply sum_congr rfl; intro p hp; ring
  rw [rest] at est
  have soft : (2*(t:ℝ))*((N:ℝ)*((∑p∈P,(1:ℝ)/(p:ℝ)^2)/(M:ℝ))) ≤
       (2*(t:ℝ))*(N:ℝ)*(5/359)/(M:ℝ) := by
    rw [mul_div_assoc',←mul_div_assoc,←mul_assoc]
    gcongr
  have grow : 54700^2 ≤ 2*N := by norm_num; omega
  have le := Nat.le_sqrt'.mpr grow
  have bound := (Nat.mul_le_mul_right (2*N).sqrt le).trans (by simpa only [←pow_two] using Nat.sqrt_le' (2*N))
  have sr : 54700*((2*N).sqrt:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast bound
  have nR : 1500000000≤(N:ℝ) := by exact_mod_cast big
  have sqrtR : (2*(t:ℝ))*(((2*N).sqrt:ℝ)/4+2)≤(2*(t:ℝ))*(N:ℝ)/108000 := by
    rw [mul_div_assoc]; gcongr; linarith only [sr,nR]
  have highR : 3700*(high.card:ℝ)≤(N:ℝ) := by exact_mod_cast capHigh
  have pR : 1880*(P.card:ℝ)≤(N:ℝ) := by exact_mod_cast capP
  have comb : S.card≤low.card+high.card := by
    have e := card_sdiff_add_card_inter S low
    have sub := card_le_card (inter_subset_right (s₁:=S) (s₂:=low))
    change S.card≤low.card+(S\low).card
    omega
  have combR : (S.card:ℝ)≤(low.card:ℝ)+(high.card:ℝ) := by exact_mod_cast comb
  linarith only [combR,est,soft,sqrtR,highR,pR]
private theorem phase_partial (N : ℕ) (P S : Finset ℕ) (B : ℕ → Finset ℕ)
    (primes : P ⊆ diagPrimesUpTo N) (covered : S ⊆ P.biUnion B)
    (old : ∀ p ∈ P, ((B p).card:ℝ) ≤ (761/525:ℝ)*((N:ℝ)/(p:ℝ)^2)+20)
    (inside : ∀ p, ∀n∈B p, n < N ∧ p^2 ∣ n^2+1) :
    (S.card : ℝ) ≤ (761/525:ℝ)*((N : ℝ) * (∑ p ∈ P, (1 : ℝ)/((p:ℝ)^2))) +
      (P.card : ℝ) + (20:ℝ)*(((2*N).sqrt : ℝ)/4+2) := by
  classical
  let small := P.filter (· ≤ (2*N).sqrt)
  have point (p : ℕ) (hp : p ∈ P) :
      ((B p).card : ℝ) ≤ ((761/525:ℝ)*(N : ℝ))*((1 : ℝ)/((p:ℝ)^2)) +
        (if p ≤ (2*N).sqrt then (20:ℝ) else 0) + 1 := by
    by_cases cut : p ≤ (2*N).sqrt
    · rw [if_pos cut]
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using
        (old p hp).trans (le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num))
    · rw [if_neg cut]
      have prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (primes hp)).1).2
      have mod4 : p%4=1 := (Finset.mem_filter.mp (primes hp)).2.1
      have lim : 2*N ≤ p^2 := (Nat.sqrt_lt'.mp (lt_of_not_ge cut)).le
      have o : ((B p).card : ℝ) ≤ 1 := by exact_mod_cast at_most_one_large_diagonal_root N p prime mod4 lim (B p) (inside p)
      have hpos : 0 ≤ ((761/525:ℝ)*(N : ℝ))*((1 : ℝ)/((p:ℝ)^2)) := by positivity
      linarith only [o,hpos]
  have total : S.card ≤ ∑ p ∈ P, (B p).card :=
    (Finset.card_le_card covered).trans Finset.card_biUnion_le
  have totalR : (S.card : ℝ) ≤ ∑ p ∈ P, ((B p).card : ℝ) := by exact_mod_cast total
  have upper := totalR.trans (Finset.sum_le_sum point)
  have count : (∑ p ∈ P, if p ≤ (2*N).sqrt then (20:ℝ) else 0) = (small.card : ℝ)*(20:ℝ) := by
    rw [← Finset.sum_filter]
    simp [small]
  have sub : small ⊆ (range ((2*N).sqrt+1)).filter (fun p=>p ≡ 1 [MOD 4]) := by
    intro p hp
    obtain ⟨pm,lim⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le lim),(mem_filter.mp (primes pm)).2.1⟩
  have cs := (card_le_card sub).trans (card_filter_mod_eq_le ((2*N).sqrt+1) 4 1)
  have cs' : 4*small.card≤(2*N).sqrt+5 := by omega
  have cR : 4*(small.card:ℝ)≤((2*N).sqrt:ℝ)+5 := by exact_mod_cast cs'
  have csr : (small.card:ℝ)≤((2*N).sqrt:ℝ)/4+2 := by linarith only [cR]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,count,Finset.sum_const, nsmul_eq_mul,
    mul_one] at upper
  linarith only [upper,mul_le_mul_of_nonneg_left csr (show (0:ℝ)≤20 by norm_num)]


private theorem phase_two {N p : ℕ} (S : Finset ℕ) (hp : p.Prime) (mod4 : p%4=1) (ge : 13≤p)
    (info : ∀x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬6∣x ∧ ¬14∣x ∧ p^2∣x^2+1) :
    (S.card:ℝ)≤(761/525:ℝ)*((N:ℝ)/(p:ℝ)^2)+20 := by
  classical
  have nz : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let G (r : ZMod (p^2)) := (Deldor14.Erdos848Phase.prog N (p^2) r.val).filter
    (fun x=>x%25≠7 ∧ x%25≠18 ∧ ¬6∣x ∧ ¬14∣x)
  have one (r : ZMod (p^2)) : ((G r).card:ℝ)≤(761/1050:ℝ)*((N:ℝ)/(p:ℝ)^2)+10 :=
    Deldor14.Erdos848Phase.phase_one (N:=N) (u:=r.val) hp ge
  obtain ⟨r,t,_,_,_,_,root⟩ := two_roots_mod_p_squared p hp mod4
  have subset : S ⊆ G r ∪ G t := by
    intro x hx
    obtain ⟨xn,x7,x18,x6,x14,div⟩ := info x hx
    have eq0 := (ZMod.natCast_eq_zero_iff (x^2+1) (p^2)).mpr div
    have eq1 : (x:ZMod (p^2))^2+1=0 := by exact_mod_cast eq0
    have lift (z : ZMod (p^2)) (eq : (x:ZMod (p^2))=z) : x∈G z := by
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr xn,(ZMod.natCast_eq_natCast_iff x z.val (p^2)).mp (by simpa using eq)⟩,x7,x18,x6,x14⟩
    exact (root _ (eq_neg_of_add_eq_zero_left eq1)).elim (fun e=>mem_union_left _ (lift _ e)) (fun e=>mem_union_right _ (lift _ e))
  have leR : (S.card:ℝ)≤((G r).card:ℝ)+((G t).card:ℝ) := by
    exact_mod_cast (card_le_card subset).trans (card_union_le ..)
  linarith only [leR,one r,one t]

theorem all_avoids_six_fourteen {N : ℕ} (big : 1500000000≤N) (S : Finset ℕ)
    (info : ∀x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1) ∧ ¬6∣x ∧ ¬14∣x) :
    (S.card:ℝ) ≤ (2118/100000)*(N:ℝ) := by
  classical
  let P := (diagPrimesUpTo N).filter (fun p=>224*p≤N)
  let B (p : ℕ) := S.filter (fun x=>p^2∣x^2+1)
  let low := P.biUnion B
  let high := S \ low
  have inp (p) (hp : p∈P) := (mem_filter.mp hp).1
  have prime (p) (hp : p∈P) : p.Prime := (mem_filter.mp (mem_filter.mp (inp p hp)).1).2
  have prop (p) (hp : p∈P) : p%4=1 ∧ 13≤p := (mem_filter.mp (inp p hp)).2
  have inside (p n) (hn : n∈B p) : n<N ∧ p^2∣n^2+1 :=
    ⟨(info n (mem_filter.mp hn).1).1,(mem_filter.mp hn).2⟩
  have capHigh := Erdos848Fifteen.large_diagonal_224 big high (by
    intro x hx
    obtain ⟨xS,xL⟩ := mem_sdiff.mp hx
    obtain ⟨xn,x7,x18,di,_⟩ := info x xS
    obtain ⟨p,mem,div⟩ := diagonal_prime (by omega) xn x7 x18 di
    have pn := mem_range.mp (mem_filter.mp (mem_filter.mp mem).1).1
    refine ⟨xn,p,by omega,?_,div⟩
    by_contra! small
    exact xL (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,small⟩,mem_filter.mpr ⟨xS,div⟩⟩))
  have capP := Erdos848Fifteen.small_primes_224 big P prime (by
    intro p hp
    have h := (mem_filter.mp hp).2
    omega)
  have points (p) (hp : p∈P) : ((B p).card:ℝ) ≤ (761/525:ℝ)*((N:ℝ)/(p:ℝ)^2)+20 := by
    apply phase_two _ (prime p hp) (prop p hp).1 (prop p hp).2
    intro x hx
    obtain ⟨sx,dv⟩ := mem_filter.mp hx
    obtain ⟨xn,x7,x18,_,x6,x14⟩ := info x sx
    exact ⟨xn,x7,x18,x6,x14,dv⟩
  have est := phase_partial N P low B (fun p hp=>inp p hp) Subset.rfl points inside
  have primeSum : (∑p∈P,(1:ℝ)/(p:ℝ)^2) ≤ 5/359 := by
    have sq : (∑p∈P,(1:ℚ)/(p:ℚ)^2) ≤ 5/359 := by
      calc _ ≤ ∑p∈diagPrimesUpTo N,(1:ℚ)/(p:ℚ)^2 := sum_le_sum_of_subset_of_nonneg (fun p hp=>inp p hp) (by intros; positivity)
           _ ≤ _ := by convert sum_diagPrimesUpTo_le N using 1; norm_num
    have cast := (Rat.cast_le (K:=ℝ)).mpr sq
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using cast
  have grow : 54700^2 ≤ 2*N := by norm_num; omega
  have le := Nat.le_sqrt'.mpr grow
  have bound := (Nat.mul_le_mul_right (2*N).sqrt le).trans (by simpa only [←pow_two] using Nat.sqrt_le' (2*N))
  have sr : 54700*((2*N).sqrt:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast bound
  have nR : 1500000000≤(N:ℝ) := by exact_mod_cast big
  have sr' : (20:ℝ)*(((2*N).sqrt:ℝ)/4+2) ≤ 20*(N:ℝ)/108000 := by linarith only [sr,nR]
  have highR : 3700*(high.card:ℝ)≤(N:ℝ) := by exact_mod_cast capHigh
  have pR : 1880*(P.card:ℝ)≤(N:ℝ) := by exact_mod_cast capP
  have comb : S.card≤low.card+high.card := by
    have e := card_sdiff_add_card_inter S low
    have sub := card_le_card (inter_subset_right (s₁:=S) (s₂:=low))
    change S.card≤low.card+(S\low).card
    omega
  have combR : (S.card:ℝ)≤(low.card:ℝ)+(high.card:ℝ) := by exact_mod_cast comb
  have weighted := mul_le_mul_of_nonneg_left primeSum (Nat.cast_nonneg (α:=ℝ) N)
  linarith only [combR,est,weighted,sr',highR,pR,Nat.cast_nonneg (α:=ℝ) N]
private theorem six_partial (N : ℕ) (P S : Finset ℕ) (B : ℕ → Finset ℕ)
    (primes : P ⊆ diagPrimesUpTo N) (covered : S ⊆ P.biUnion B)
    (old : ∀ p ∈ P, ((B p).card:ℝ) ≤ (23/15:ℝ)*((N:ℝ)/(p:ℝ)^2)+12)
    (inside : ∀ p, ∀n∈B p, n < N ∧ p^2 ∣ n^2+1) :
    (S.card : ℝ) ≤ (23/15:ℝ)*((N : ℝ) * (∑ p ∈ P, (1 : ℝ)/((p:ℝ)^2))) +
      (P.card : ℝ) + (12:ℝ)*(((2*N).sqrt : ℝ)/4+2) := by
  classical
  let small := P.filter (· ≤ (2*N).sqrt)
  have point (p : ℕ) (hp : p ∈ P) :
      ((B p).card : ℝ) ≤ ((23/15:ℝ)*(N : ℝ))*((1 : ℝ)/((p:ℝ)^2)) +
        (if p ≤ (2*N).sqrt then (12:ℝ) else 0) + 1 := by
    by_cases cut : p ≤ (2*N).sqrt
    · rw [if_pos cut]
      simpa only [div_eq_mul_inv,one_mul,mul_assoc] using
        (old p hp).trans (le_add_of_nonneg_right (show (0:ℝ) ≤ 1 by norm_num))
    · rw [if_neg cut]
      have prime : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp (primes hp)).1).2
      have mod4 : p%4=1 := (Finset.mem_filter.mp (primes hp)).2.1
      have lim : 2*N ≤ p^2 := (Nat.sqrt_lt'.mp (lt_of_not_ge cut)).le
      have o : ((B p).card : ℝ) ≤ 1 := by exact_mod_cast at_most_one_large_diagonal_root N p prime mod4 lim (B p) (inside p)
      have hpos : 0 ≤ ((23/15:ℝ)*(N : ℝ))*((1 : ℝ)/((p:ℝ)^2)) := by positivity
      linarith only [o,hpos]
  have total : S.card ≤ ∑ p ∈ P, (B p).card :=
    (Finset.card_le_card covered).trans Finset.card_biUnion_le
  have totalR : (S.card : ℝ) ≤ ∑ p ∈ P, ((B p).card : ℝ) := by exact_mod_cast total
  have upper := totalR.trans (Finset.sum_le_sum point)
  have count : (∑ p ∈ P, if p ≤ (2*N).sqrt then (12:ℝ) else 0) = (small.card : ℝ)*(12:ℝ) := by
    rw [← Finset.sum_filter]
    simp [small]
  have sub : small ⊆ (range ((2*N).sqrt+1)).filter (fun p=>p ≡ 1 [MOD 4]) := by
    intro p hp
    obtain ⟨pm,lim⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le lim),(mem_filter.mp (primes pm)).2.1⟩
  have cs := (card_le_card sub).trans (card_filter_mod_eq_le ((2*N).sqrt+1) 4 1)
  have cs' : 4*small.card≤(2*N).sqrt+5 := by omega
  have cR : 4*(small.card:ℝ)≤((2*N).sqrt:ℝ)+5 := by exact_mod_cast cs'
  have csr : (small.card:ℝ)≤((2*N).sqrt:ℝ)/4+2 := by linarith only [cR]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,count,Finset.sum_const, nsmul_eq_mul,
    mul_one] at upper
  linarith only [upper,mul_le_mul_of_nonneg_left csr (show (0:ℝ)≤12 by norm_num)]


private theorem six_two {N p : ℕ} (S : Finset ℕ) (hp : p.Prime) (mod4 : p%4=1) (ge : 13≤p)
    (info : ∀x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬6∣x ∧ p^2∣x^2+1) :
    (S.card:ℝ)≤(23/15:ℝ)*((N:ℝ)/(p:ℝ)^2)+12 := by
  classical
  have nz : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let G (r : ZMod (p^2)) := (Deldor14.Erdos848Phase.prog N (p^2) r.val).filter
    (fun x=>x%25≠7 ∧ x%25≠18 ∧ ¬6∣x)
  have one (r : ZMod (p^2)) : ((G r).card:ℝ)≤(23/30:ℝ)*((N:ℝ)/(p:ℝ)^2)+6 :=
    Deldor14.Erdos848Phase.phase_no_six (N:=N) (u:=r.val) hp ge
  obtain ⟨r,t,_,_,_,_,root⟩ := two_roots_mod_p_squared p hp mod4
  have subset : S ⊆ G r ∪ G t := by
    intro x hx
    obtain ⟨xn,x7,x18,x6,div⟩ := info x hx
    have eq0 := (ZMod.natCast_eq_zero_iff (x^2+1) (p^2)).mpr div
    have eq1 : (x:ZMod (p^2))^2+1=0 := by exact_mod_cast eq0
    have lift (z : ZMod (p^2)) (eq : (x:ZMod (p^2))=z) : x∈G z := by
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr xn,(ZMod.natCast_eq_natCast_iff x z.val (p^2)).mp (by simpa using eq)⟩,x7,x18,x6⟩
    exact (root _ (eq_neg_of_add_eq_zero_left eq1)).elim (fun e=>mem_union_left _ (lift _ e)) (fun e=>mem_union_right _ (lift _ e))
  have leR : (S.card:ℝ)≤((G r).card:ℝ)+((G t).card:ℝ) := by
    exact_mod_cast (card_le_card subset).trans (card_union_le ..)
  linarith only [leR,one r,one t]

theorem all_avoids_six {N : ℕ} (big : 1500000000≤N) (S : Finset ℕ)
    (info : ∀x∈S,x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1) ∧ ¬6∣x) :
    (S.card:ℝ) ≤ (2227/100000)*(N:ℝ) := by
  classical
  let P := (diagPrimesUpTo N).filter (fun p=>224*p≤N)
  let B (p : ℕ) := S.filter (fun x=>p^2∣x^2+1)
  let low := P.biUnion B
  let high := S \ low
  have inp (p) (hp : p∈P) := (mem_filter.mp hp).1
  have prime (p) (hp : p∈P) : p.Prime := (mem_filter.mp (mem_filter.mp (inp p hp)).1).2
  have prop (p) (hp : p∈P) : p%4=1 ∧ 13≤p := (mem_filter.mp (inp p hp)).2
  have inside (p n) (hn : n∈B p) : n<N ∧ p^2∣n^2+1 :=
    ⟨(info n (mem_filter.mp hn).1).1,(mem_filter.mp hn).2⟩
  have capHigh := Erdos848Fifteen.large_diagonal_224 big high (by
    intro x hx
    obtain ⟨xS,xL⟩ := mem_sdiff.mp hx
    obtain ⟨xn,x7,x18,di,_⟩ := info x xS
    obtain ⟨p,mem,div⟩ := diagonal_prime (by omega) xn x7 x18 di
    have pn := mem_range.mp (mem_filter.mp (mem_filter.mp mem).1).1
    refine ⟨xn,p,by omega,?_,div⟩
    by_contra! small
    exact xL (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,small⟩,mem_filter.mpr ⟨xS,div⟩⟩))
  have capP := Erdos848Fifteen.small_primes_224 big P prime (by
    intro p hp
    have h := (mem_filter.mp hp).2
    omega)
  have points (p) (hp : p∈P) : ((B p).card:ℝ) ≤ (23/15:ℝ)*((N:ℝ)/(p:ℝ)^2)+12 := by
    apply six_two _ (prime p hp) (prop p hp).1 (prop p hp).2
    intro x hx
    obtain ⟨sx,dv⟩ := mem_filter.mp hx
    obtain ⟨xn,x7,x18,_,x6⟩ := info x sx
    exact ⟨xn,x7,x18,x6,dv⟩
  have est := six_partial N P low B (fun p hp=>inp p hp) Subset.rfl points inside
  have primeSum : (∑p∈P,(1:ℝ)/(p:ℝ)^2) ≤ 5/359 := by
    have sq : (∑p∈P,(1:ℚ)/(p:ℚ)^2) ≤ 5/359 := by
      calc _ ≤ ∑p∈diagPrimesUpTo N,(1:ℚ)/(p:ℚ)^2 := sum_le_sum_of_subset_of_nonneg (fun p hp=>inp p hp) (by intros; positivity)
           _ ≤ _ := by convert sum_diagPrimesUpTo_le N using 1; norm_num
    have cast := (Rat.cast_le (K:=ℝ)).mpr sq
    simpa only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using cast
  have grow : 54700^2 ≤ 2*N := by norm_num; omega
  have le := Nat.le_sqrt'.mpr grow
  have bound := (Nat.mul_le_mul_right (2*N).sqrt le).trans (by simpa only [←pow_two] using Nat.sqrt_le' (2*N))
  have sr : 54700*((2*N).sqrt:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast bound
  have nR : 1500000000≤(N:ℝ) := by exact_mod_cast big
  have sr' : (12:ℝ)*(((2*N).sqrt:ℝ)/4+2) ≤ 12*(N:ℝ)/108000 := by linarith only [sr,nR]
  have highR : 3700*(high.card:ℝ)≤(N:ℝ) := by exact_mod_cast capHigh
  have pR : 1880*(P.card:ℝ)≤(N:ℝ) := by exact_mod_cast capP
  have comb : S.card≤low.card+high.card := by
    have e := card_sdiff_add_card_inter S low
    have sub := card_le_card (inter_subset_right (s₁:=S) (s₂:=low))
    change S.card≤low.card+(S\low).card
    omega
  have combR : (S.card:ℝ)≤(low.card:ℝ)+(high.card:ℝ) := by exact_mod_cast comb
  have weighted := mul_le_mul_of_nonneg_left primeSum (Nat.cast_nonneg (α:=ℝ) N)
  linarith only [combR,est,weighted,sr',highR,pR,Nat.cast_nonneg (α:=ℝ) N]
end Deldor14.Erdos848Middle

/- Cardinality consequences of the diagonal sieve for three types of residual sets. -/
namespace Deldor14.Erdos848Middle
open Finset Erdos848

def outsideInfo (N : ℕ) (R : Finset ℕ) := ∀x∈R, x<N ∧ x%25≠7 ∧ x%25≠18 ∧ ¬Squarefree (x*x+1)

theorem outside_all {N : ℕ} (big : 1500000000≤N) (R : Finset ℕ) (info : outsideInfo N R) :
    (R.card:ℝ) ≤ (2868/100000)*(N:ℝ) := by
  have h := diagonal_budget (M:=1) (t:=1) big (by decide) {0} R (by decide) (by
    intro x hx
    obtain ⟨a,b,c,d⟩ := info x hx
    exact ⟨a,b,c,d,mem_singleton.mpr (by omega)⟩)
  push_cast at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]

theorem outside_odd {N : ℕ} (big : 1500000000≤N) (R : Finset ℕ) (info : outsideInfo N R)
    (odd : ∀x∈R,x%2=1) : (R.card:ℝ) ≤ (1405/100000)*(N:ℝ) := by
  let T := (range 50).filter (fun q=>q%2=1 ∧ q%25≠7 ∧ q%25≠18)
  have size : T.card≤23 := by decide
  have h := diagonal_budget (M:=50) (t:=23) big (by decide) T R size (by
    intro x hx
    obtain ⟨a,b,c,d⟩ := info x hx
    have o := odd x hx
    exact ⟨a,b,c,d,mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (by decide)),by omega,by omega,by omega⟩⟩)
  push_cast at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]


theorem outside_odd_no3 {N : ℕ} (big : 1500000000≤N) (R : Finset ℕ) (info : outsideInfo N R)
    (odd : ∀x∈R,x%2=1) (no : ∀x∈R,¬3∣x) : (R.card:ℝ) ≤ (1013/100000)*(N:ℝ) := by
  have h := diagonal_budget (M:=6) (t:=2) big (by decide) {1,5} R (by decide) (by
    intro x hx
    obtain ⟨a,b,c,d⟩ := info x hx
    have n := no x hx
    have o := odd x hx
    exact ⟨a,b,c,d,by simp; omega⟩)
  push_cast at h
  linarith only [h,Nat.cast_nonneg (α:=ℝ) N]

theorem mixed_size {k : ℕ} (big : 1500000000≤25*k+7) (upper : 25*k+7≤5000000000) (A : Finset ℕ)
    (inside : A⊆range (25*k+7)) (adm : NonSquarefreeProductProp A)
    (mixed : (outside A).Nonempty)
    : A.card≤k := by
  let N := 25*k+7
  let R := outside A
  have info : outsideInfo N R := by
    intro x hx
    obtain ⟨xa,x7,x18⟩ := mem_filter.mp hx
    exact ⟨mem_range.mp (inside xa),x7,x18,adm x xa x xa⟩
  have total := Deldor14.Erdos848Tenth.total_parts A
  change (A.card:ℝ) ≤ ((slice A 7).card:ℝ)+((slice A 18).card:ℝ)+(R.card:ℝ) at total
  have endpoint : (N:ℝ)=25*(k:ℝ)+7 := by dsimp [N]; push_cast; ring
  by_contra! bad
  have more : (k:ℝ)+1 ≤ (A.card:ℝ) := by exact_mod_cast (show k+1≤A.card by omega)
  have positiveN : 1500000000 ≤ (N:ℝ) := by exact_mod_cast big
  by_cases even : ∃e∈R,2∣e
  · obtain ⟨e,er,ev⟩ := even
    obtain ⟨ea,e7,e18⟩ := mem_filter.mp er
    by_cases six : ∃d∈R,6∣d
    · obtain ⟨d,dr,d6⟩ := six
      obtain ⟨da,d7,d18⟩ := mem_filter.mp dr
      have b7 := (row_bound big upper inside adm da (Or.inl (rfl : 7=7)) d7).2.2.2.1 d6
      have b18 := (row_bound big upper inside adm da (Or.inr (rfl : 18=18)) d18).2.2.2.1 d6
      have diag := outside_all big R info
      change ((slice A 7).card:ℝ) ≤ (475/100000)*(N:ℝ) at b7
      change ((slice A 18).card:ℝ) ≤ (475/100000)*(N:ℝ) at b18
      linarith only [b7,b18,diag,total,more,endpoint,positiveN]
    · by_cases fourteen : ∃x∈R,14∣x
      · obtain ⟨f,fr,f14⟩ := fourteen
        obtain ⟨fa,f7,f18⟩ := mem_filter.mp fr
        have diag := all_avoids_six big R (by
          intro x hx
          obtain ⟨xn,x7,x18,dg⟩ := info x hx
          exact ⟨xn,x7,x18,dg,fun t=>six ⟨x,hx,t⟩⟩)
        have fnot : ¬6∣f := fun d=>six ⟨f,fr,d⟩
        have row7 := row_fourteen big upper inside adm fa f14 fnot (Or.inl (rfl : 7=7)) f7
        have row18 := row_fourteen big upper inside adm fa f14 fnot (Or.inr (rfl : 18=18)) f18
        change ((slice A 7).card:ℝ) ≤ (875/100000)*(N:ℝ) at row7
        change ((slice A 18).card:ℝ) ≤ (875/100000)*(N:ℝ) at row18
        linarith only [row7,row18,diag,total,more,endpoint,positiveN]
      · have diag := all_avoids_six_fourteen big R (by
          intro x hx
          obtain ⟨xn,x7,x18,dg⟩ := info x hx
          exact ⟨xn,x7,x18,dg,fun t=>six ⟨x,hx,t⟩,fun t=>fourteen ⟨x,hx,t⟩⟩)
        have no3 : ¬3∣e := fun u=>six ⟨e,er,by omega⟩
        have no7 : ¬7∣e := fun u=>fourteen ⟨e,er,by omega⟩
        have h7 := (row_bound big upper inside adm ea (Or.inl (rfl : 7=7)) e7).2.2.2.2 ev no3 no7
        have h18 := (row_bound big upper inside adm ea (Or.inr (rfl : 18=18)) e18).2.2.2.2 ev no3 no7
        change ((slice A 7).card:ℝ) ≤ (932/100000)*(N:ℝ) at h7
        change ((slice A 18).card:ℝ) ≤ (932/100000)*(N:ℝ) at h18
        linarith only [h7,h18,diag,total,more,endpoint,positiveN]
  · have allR (x) (hx : x∈R) : x%2=1 := by
      have h : ¬2∣x := fun d=>even ⟨x,hx,d⟩
      omega
    obtain ⟨b,br,chosen⟩ : ∃b∈R,3∣b ∨ ∀x∈R,¬3∣x := by
      by_cases found : ∃b∈R,3∣b
      · obtain ⟨x,hx,m⟩ := found
        exact ⟨x,hx,Or.inl m⟩
      · obtain ⟨x,hx⟩ := mixed
        exact ⟨x,hx,Or.inr (fun t ht div=>found ⟨t,ht,div⟩)⟩
    have diag : (R.card:ℝ) ≤ ((if 3∣b then 1405 else 1013)/100000:ℝ)*(N:ℝ) := by
      by_cases tri : 3∣b
      · rw [if_pos tri]; exact outside_odd big R info allR
      · rw [if_neg tri]
        have z := outside_odd_no3 big R info allR (chosen.resolve_left tri)
        linarith only [z]
    obtain ⟨ba,b7,b18⟩ := mem_filter.mp br
    have row (r) (hr : r=7 ∨ r=18) (diff : b%25≠r) :
        ((slice A r).card:ℝ) ≤ ((if 3∣b then 1471 else 1980)/100000:ℝ)*(N:ℝ) := by
      have q := row_bound big upper inside adm ba hr diff
      by_cases tri : 3∣b
      · rw [if_pos tri]; exact q.2.2.1 tri
      · rw [if_neg tri]; exact q.1
    by_cases someEven : ∃e∈A,2∣e
    · obtain ⟨e,ea,ev⟩ := someEven
      by_cases e7 : e%25=7
      · have r7 := row 7 (by decide) b7
        have r18 := (row_bound big upper inside adm ea (Or.inr (rfl : 18=18)) (by omega)).2.1 ev
        change ((slice A 18).card:ℝ)≤(957/100000)*(N:ℝ) at r18
        split_ifs at r7 diag <;> linarith only [r7,r18,diag,total,more,endpoint,positiveN]
      · have r18 := row 18 (by decide) b18
        have r7 := (row_bound big upper inside adm ea (Or.inl (rfl : 7=7)) e7).2.1 ev
        change ((slice A 7).card:ℝ)≤(957/100000)*(N:ℝ) at r7
        split_ifs at r18 diag <;> linarith only [r7,r18,diag,total,more,endpoint,positiveN]
    · have allodd (x) (hx : x∈A) : x%2=1 := by
        have h : ¬2∣x := fun ev=>someEven ⟨x,hx,ev⟩
        omega
      exact (not_lt_of_ge (Deldor14.Erdos848OddPart.odd_mixed (by omega) A inside adm allodd mixed)) bad

theorem effective_from_upper (high : ∀ k : ℕ, 5000000000≤25*k+7 → ∀A⊆range (25*k+7), NonSquarefreeProductProp A → A.card≤k)
    (N : ℕ) (big : 1500000000≤N) : Erdos848For N := by
  intro A inside adm
  let k := (N+17)/25
  have up : N ≤ 25*k+7 := by dsimp [k]; omega
  have incl : A⊆range (25*k+7) := fun x hx=>mem_range.mpr ((mem_range.mp (inside hx)).trans_le up)
  have count : A.card≤k := by
    by_cases upper : 25*k+7≤5000000000
    · by_cases mixed : (outside A).Nonempty
      · exact mixed_size (big.trans up) upper A incl adm mixed
      · apply Deldor14.Erdos848OddPart.endpoint_structured_400M k (by omega) A incl adm
        exact Or.inr (Or.inr ⟨0,dvd_zero 2,fun x hx=>(mixed ⟨x,hx⟩).elim⟩)
    · exact high k (by omega) A incl adm
  have size : (A₇ N).card=k := Erdos848Port.card_range_filter_mod25_eq 7 (by decide) N
  rw [size]
  exact count
end Deldor14.Erdos848Middle

namespace Deldor14.Erdos848Middle
open Erdos848
theorem effective_1500M (N : ℕ) (big : 1500000000≤N) : Erdos848For N :=
  effective_from_upper (fun k h A inside adm=>Deldor14.Erdos848Fifth.endpoint_5B k h A inside adm) N big
end Deldor14.Erdos848Middle
theorem OMA.solution : OMA.R_Erdos848_erdos_848_R2_H2_R1.H4 := by
  intro N hN
  exact Deldor14.Erdos848Middle.effective_1500M N ((by decide : 1500000000≤10^13).trans hN)
