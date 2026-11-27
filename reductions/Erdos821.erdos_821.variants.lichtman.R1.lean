import FormalConjectures.ErdosProblems.«821»
import Mathlib

/-! Theorem 1.1 of J. D. Lichtman, arXiv:2211.09641, allows any
smoothness exponent greater than 15/(32 sqrt(e)). Use 284312/1000000
and choose products of t^(284312+1) primes. Counting the possible
totients loses at most a factor of t to the power of the subset size.

The finite pigeonhole formulation and the binomial bound are adapted
from OpenAI, OAI/NumberTheory/TotientFibers/FiniteFiber.lean,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, under Apache-2.0. -/
namespace OMA.R_Erdos821_erdos_821_variants_lichtman_R1
open Finset Filter Erdos821
open scoped Classical

/-- A fixed-exponent consequence of Lichtman's smooth shifted prime theorem. -/
def H1 : Prop := ∀ᶠ x : ℕ in atTop, ∃ P : Finset ℕ,
  (x:ℝ)^((999999:ℝ)/1000000) ≤ P.card ∧ ∀ p ∈ P, p.Prime ∧ p≤x ∧
    ∀ q : ℕ, q.Prime → q ∣ p-1 → (q:ℝ) ≤ (x:ℝ)^((284312:ℝ)/1000000)

/-- Count products of distinct primes by the range of their totient. -/
def H2 : Prop := ∀ (P : Finset ℕ) (X B k : ℕ) (z : ℝ),
  (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p≤X) →
  (∀ p ∈ P, ∀ q : ℕ, q.Prime → q ∣ p-1 → q≤B) → 0≤z →
  ((Nat.log 2 (X^k)+1:ℕ):ℝ)^B*z < (P.card.choose k : ℝ) →
  ∃ n : ℕ, 0<n ∧ n≤X^k ∧ z < g n

theorem binomial_ge_ratio {M k : ℕ} (hkM : k ≤ M) :
    ((M : ℝ) / k) ^ k ≤ (M.choose k : ℝ) := by
  have hid : (∏ j ∈ Finset.range k, ((M - j : ℕ) : ℝ) / (k - j : ℕ)) =
      (M.choose k : ℝ) := by
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
      ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have hfact : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    exact mul_div_cancel_left₀ _ hfact
  calc
    ((M : ℝ) / k) ^ k = ∏ j ∈ Finset.range k, ((M : ℝ) / k) := by simp [div_pow]
    _ ≤ ∏ j ∈ Finset.range k, ((M - j : ℕ) : ℝ) / (k - j : ℕ) := by
      apply Finset.prod_le_prod (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hjM : j ≤ M := hjk.le.trans hkM
      have hjk' : (j : ℝ) < k := by exact_mod_cast hjk
      have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_le j).trans_lt hjk
      rw [Nat.cast_sub hjM, Nat.cast_sub hjk.le, div_le_div_iff₀ hkpos (sub_pos.mpr hjk')]
      nlinarith [mul_nonneg (sub_nonneg.mpr hkM') (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    _ = (M.choose k : ℝ) := hid



lemma encoded_totients {t a b : ℕ} (ha : a ≤ t) (hb : b+4 ≤ t) :
    (Nat.log 2 ((t^a)^(t^(b+1)))+1)^(t^b) ≤ t^(t^(b+1)) := by
  let k := t^(b+1)
  have t2 : 2 ≤ t := by omega
  have t1 : 1 ≤ t := by omega
  have power : (t^a)^k ≤ 2^(t*(a*k)) := by
    calc
      _ ≤ ((2^t)^a)^k := Nat.pow_le_pow_left (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _) _
      _ = _ := by simp only [←pow_mul,Nat.mul_assoc]
  have logle := Nat.log_mono_right (b:=2) power
  rw [Nat.log_pow (by decide)] at logle
  have base : Nat.log 2 ((t^a)^k)+1 ≤ t^(b+4) := by
    have mt : t*(a*k) ≤ t*(t*k) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ ha)
    have eq : t*(t*k) = t^(b+3) := by dsimp [k]; rw [show b+3=b+1+1+1 by omega,pow_succ t (b+1+1),pow_succ t (b+1)]; ring
    have hpos : 1 ≤ t^(b+3) := one_le_pow₀ t1
    have hmul := Nat.mul_le_mul_left (t^(b+3)) t2
    rw [show b+4=b+3+1 by omega,pow_succ]
    omega
  calc
    _ ≤ (t^(b+4))^(t^b) := Nat.pow_le_pow_left base _
    _ = t^((b+4)*t^b) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ t1 (by rw [pow_succ]; simpa [Nat.mul_comm] using Nat.mul_le_mul_right (t^b) hb)

lemma grid_power (t a m : ℕ) (ha : 0<a) :
    ((t^a:ℕ):ℝ)^((m:ℝ)/a) = ((t^m:ℕ):ℝ) := by
  rw [Nat.cast_pow,Nat.cast_pow,← Real.rpow_natCast_mul (Nat.cast_nonneg t)]
  have az : (a:ℝ)≠0 := by exact_mod_cast ha.ne'
  rw [show (a:ℝ)*((m:ℝ)/a) = m by field_simp,Real.rpow_natCast]

theorem main : H1 → H2 → type_of% @Erdos821.erdos_821.variants.lichtman := by
  intro supply count
  let a : ℕ := 1000000
  let b : ℕ := 284312
  let c : ℕ := 715684
  let m : ℕ := 999999
  have apos : 0<a := by decide
  have cpos : 0<c := by decide
  have bc : b+4≤a := by decide
  have exactExp : (c+2)+(b+1)=m := by decide
  refine ⟨(c:ℝ)/a,by norm_num [a,c],?_⟩
  apply Set.Infinite.of_image g
  apply Set.infinite_of_forall_exists_gt
  intro Z
  obtain ⟨N,hN⟩ := eventually_atTop.1 supply
  let t := max (max (Z+2) N) a
  have htA : a≤t := le_max_right _ _
  have htN : N≤t := (le_max_right _ _).trans (le_max_left _ _)
  have htZ : Z+2 ≤ t := (le_max_left _ _).trans (le_max_left _ _)
  have t2 : 1<t := by omega
  have tpos : 0<t := by omega
  have tR : (1:ℝ)<t := by exact_mod_cast t2
  have tp := Nat.cast_nonneg (α:=ℝ) t
  let k := t^(b+1)
  let X := t^a
  let B := t^b
  have kp : 0<k := Nat.pow_pos tpos
  have kr : 0<(k:ℝ) := by exact_mod_cast kp
  have hX : t ≤ X := by exact Nat.le_self_pow apos.ne' _
  obtain ⟨P,hcard,pr⟩ := hN X (htN.trans hX)
  change (X:ℝ)^((m:ℝ)/a) ≤ P.card at hcard
  rw [show X=t^a from rfl,grid_power t a m apos] at hcard
  have cardN : t^m ≤ P.card := by exact_mod_cast hcard
  have hkM : k ≤ P.card := (pow_le_pow_right₀ (by omega : 1≤t)
    (by decide : b+1 ≤ m)).trans cardN
  have ratio : (t:ℝ)^(c+2) ≤ P.card/(k:ℝ) := by
    apply (le_div_iff₀ kr).2
    change (t:ℝ)^(c+2) * ((t^(b+1):ℕ):ℝ) ≤ _
    rw [Nat.cast_pow,←pow_add,exactExp]
    exact_mod_cast cardN
  have chooseBound : (t:ℝ)^((c+2)*k) ≤ P.card.choose k := by
    rw [pow_mul]
    exact (pow_le_pow_left₀ (by positivity) ratio _).trans (binomial_ge_ratio hkM)
  have encodeN := encoded_totients htA (bc.trans htA)
  have encode : ((Nat.log 2 (X^k)+1:ℕ):ℝ)^B ≤ (t:ℝ)^k := by exact_mod_cast encodeN
  let z := (t:ℝ)^(c*k)
  have large : ((Nat.log 2 (X^k)+1:ℕ):ℝ)^B*z < (P.card.choose k : ℝ) := by
    refine (mul_le_mul_of_nonneg_right encode (by dsimp [z]; positivity)).trans_lt (lt_of_lt_of_le ?_ chooseBound)
    dsimp only [z]
    rw [←pow_add]
    apply pow_lt_pow_right₀ tR
    have : (c+2)*k = c*k+2*k := by ring
    omega
  have smooth (p : ℕ) (hp : p∈P) (q : ℕ) (hq : q.Prime) (hd : q∣p-1) : q ≤ B := by
    have H := (pr p hp).2.2 q hq hd
    change (q:ℝ) ≤ ((t^a:ℕ):ℝ)^((b:ℝ)/a) at H
    rw [grid_power t a b apos] at H
    exact_mod_cast H
  obtain ⟨n,hn,nmax,fiber⟩ := count P X B k z (fun p hp => (pr p hp).1)
    (fun p hp => (pr p hp).2.1) smooth (by dsimp [z]; positivity) large
  have np : (0:ℝ)<n := by exact_mod_cast hn
  have nr : (n:ℝ) ≤ (X^k:ℕ) := by exact_mod_cast nmax
  have nsmall : (n:ℝ)^((c:ℝ)/a) ≤ z := by
    refine (Real.rpow_le_rpow np.le nr (by positivity)).trans_eq ?_
    change (((t^a)^k:ℕ):ℝ)^((c:ℝ)/a) = (t:ℝ)^(c*k)
    rw [show (t^a)^k=(t^k)^a by rw [←pow_mul,←pow_mul,Nat.mul_comm a k],grid_power (t^k) a c apos]
    simp only [Nat.cast_pow,←pow_mul,Nat.mul_comm k c]
  have tz : (t:ℝ) ≤ z := by
    simpa only [pow_one] using pow_le_pow_right₀ tR.le (show 1 ≤ c*k from Nat.mul_pos cpos kp)
  refine ⟨g n,⟨n,nsmall.trans_lt fiber,rfl⟩,?_⟩
  have : (t:ℝ) < (g n:ℝ) := tz.trans_lt fiber
  have : t < g n := by exact_mod_cast this
  omega

end OMA.R_Erdos821_erdos_821_variants_lichtman_R1
