import FormalConjectures.OEIS.«1146»
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
# Local prime-power obstructions in Hasler's divisibility conjecture

Reduction by @Deldor14. We classify powers of two in H1. For other candidates
we prove that four divides the number, remove all small square divisors of
k^4-1, and replace the exponent k by gcd(k,p-1) at each prime power p^j.
H2 asks for one obstruction among these smaller local tests.

The unconditional factor four comes from quadratic reciprocity at the primes
dividing k^2+1. If k is twice an odd number, both -1 and 2 are squares modulo
each such prime, forcing k^2+1 to be 1 modulo 8. Direct expansion gives 5.

References: M. F. Hasler, OEIS A001146 (2015), https://oeis.org/A001146.
S. Fried, On Several Conjectures Stated in A000215, theorem 1,
https://oeis.org/A000215/a000215_1.pdf.
-/

namespace OMA.Hasler

open scoped Nat

theorem mersenneIff (a b : ℕ) : 2^a-1 ∣ 2^b-1 ↔ a∣b := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.pow_sub_one_mod_pow_sub_one, Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h
    by_contra hn
    have hbig : 1 < 2^(b%a) := Nat.one_lt_two_pow (by omega)
    omega
  · intro h
    simp [h]

private theorem avoidPred {p a : ℕ} (hp : p.Prime) (ha : 0<a) (hd : p∣a) : ¬p∣a-1 := by
  intro hh
  have hx := Nat.dvd_sub hd hh
  rw [show a-(a-1)=1 by omega] at hx
  exact hp.not_dvd_one hx

theorem localIff {k : ℕ} (hk : 1<k) : (k^4-1 ∣ 2^k-1) ↔ (∀ p j : ℕ, p.Prime → p^j ∣ k^4-1 → p^j ∣ 2^(k.gcd (p-1))-1) := by
  constructor
  · intro h p j hp hpd
    cases j with
    | zero => simp
    | succ j =>
      have hp0 : p∣p^(j+1) := by rw [pow_succ]; exact dvd_mul_left p _
      have hd := hp0.trans hpd
      have h2 := hpd.trans h
      have hkp : k.Coprime p := (hp.coprime_iff_not_dvd.mpr (fun hpk =>
        avoidPred hp (by positivity : 0<k^4) (hpk.trans (dvd_pow_self k (by decide : 4≠0))) hd)).symm
      have hp2 : 2≠p := by
        rintro rfl
        exact avoidPred Nat.prime_two (by positivity) (dvd_pow_self 2 (by omega : k≠0)) (hp0.trans h2)
      have hbase := ((Nat.coprime_primes Nat.prime_two hp).mpr hp2).pow_right (j+1)
      have heu := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ 2 (by decide) : 1 ≤ 2^(p^(j+1)).totient)).mp
        (Nat.ModEq.pow_totient hbase).symm
      have hg := Nat.dvd_gcd h2 heu
      rw [Nat.pow_sub_one_gcd_pow_sub_one] at hg
      apply hg.trans
      apply (mersenneIff _ _).mpr
      apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
      have hdT := Nat.gcd_dvd_right k (p^(j+1)).totient
      have hcop := (hkp.pow_right j).of_dvd_left (Nat.gcd_dvd_left k (p^(j+1)).totient)
      apply hcop.dvd_of_dvd_mul_left
      rwa [← Nat.totient_prime_pow_succ hp j]
  · intro h
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p j hp hpd
    exact (h p j hp hpd).trans ((mersenneIff _ _).mpr (Nat.gcd_dvd_left _ _))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
private theorem smallData : (List.range 1093).all (fun q =>
    decide (q<2 ∨ (2^(q-1)-1)%(q^2)≠0)) = true := by decide +kernel

theorem noSmallWieferich : ∀ q : Fin 1093, q.val.Prime → ¬q.val^2 ∣ 2^(q.val-1)-1 := by
  intro q hq
  have h := List.all_eq_true.mp smallData q.val (List.mem_range.mpr q.isLt)
  simp only [decide_eq_true_eq] at h
  rw [Nat.dvd_iff_mod_eq_zero]
  exact h.resolve_left (not_lt.mpr hq.two_le)

theorem excludeSquares {k : ℕ} (hk : 1<k) (h : (k^4-1 ∣ 2^k-1)) {p : ℕ}
    (hp : p.Prime) (hsmall : p<1093) : ¬p^2∣k^4-1 := by
  intro hd
  have hx := (localIff hk).mp h p 2 hp hd
  exact noSmallWieferich ⟨p,hsmall⟩ hp
    (hx.trans ((mersenneIff _ _).mpr (Nat.gcd_dvd_right _ _)))

private theorem powEq {p e : ℕ} (h : p∣2^e-1) : (2 : ZMod p)^e=1 := by
  have hx := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast [show 1≤(2:ℕ)^e from Nat.one_le_pow e 2 (by decide)] at hx
  exact sub_eq_zero.mp hx

private theorem productOne (l : List ℕ) (h : ∀ x∈l, x%8=1) : l.prod%8=1 := by
  induction l with
  | nil => decide
  | cons a l ih =>
    rw [List.prod_cons, Nat.mul_mod, h a (by simp), ih (fun _ h' => h _ (by simp [h']))]

private theorem factorClass {k m p : ℕ} (hk : k=4*m+2) (hp : p.Prime) (hd : p∣k^2+1)
    (he : (2 : ZMod p)^k=1) : p%8=1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp2 : p≠2 := by
    rintro rfl
    have hr : k^2+1=2*(8*m^2+8*m+2)+1 := by rw [hk]; ring
    rw [hr] at hd
    omega
  have hkz : (k : ZMod p)^2 = -1 := by
    have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    push_cast at hz
    linear_combination hz
  have hN : IsSquare (-1 : ZMod p) := ⟨(k : ZMod p), by rw [←sq,hkz]⟩
  let y : ZMod p := 2^(2*m+1)
  have hy : y^2=1 := by
    dsimp [y]; rw [← pow_mul, show (2*m+1)*2=k by omega, he]
  have hsq : ((2 : ZMod p)^(m+1))^2=2*y := by
    dsimp [y]; rw [←pow_mul, ←pow_succ']; congr 1; omega
  have hT : IsSquare (2 : ZMod p) := by
    rcases sq_eq_one_iff.mp hy with h | h
    · exact ⟨2^(m+1),by rw [←sq,hsq,h,mul_one]⟩
    · refine ⟨(k : ZMod p) * 2^(m+1), ?_⟩
      rw [←sq,mul_pow,hkz,hsq,h]; ring
  have h1 := (ZMod.exists_sq_eq_neg_one_iff (p:=p)).mp hN
  have h2 := (ZMod.exists_sq_eq_two_iff hp2).mp hT
  omega

theorem fourDvd {k : ℕ} (hk : 1<k) (h : k^4-1 ∣ 2^k-1) : 4∣k := by
  have hkEven : Even k := by
    by_contra hn
    obtain ⟨a,ha⟩ := (show Odd (k^4) from (Nat.not_even_iff_odd.mp hn).pow)
    have hs : 2∣k^4-1 := ⟨a,by omega⟩
    have hx := hs.trans h
    have hy := dvd_pow_self 2 (by omega : k≠0)
    have hpos : 0<2^k := by positivity
    omega
  by_contra hf
  obtain ⟨u,hu⟩ := hkEven
  let m:=k/4
  have hm : k=4*m+2 := by dsimp [m]; omega
  have he : k^4-1=(k^2+1)*(k^2-1) := by
    have h2 : 1≤k^2 := Nat.one_le_pow 2 k (by omega)
    have h4 : 1≤k^4 := Nat.one_le_pow 4 k (by omega)
    zify [h2,h4]
    ring
  have allp (p : ℕ) (hp : p.Prime) (hd : p∣k^2+1) : p%8=1 := by
    apply factorClass hm hp hd
    apply powEq
    rw [he] at h
    exact (hd.trans (dvd_mul_right _ _)).trans h
  have hr : (k^2+1)%8=1 := by
    rw [← Nat.prod_primeFactorsList (by positivity : k^2+1 ≠0)]
    apply productOne
    intro p hp
    exact allp p (Nat.prime_of_mem_primeFactorsList hp) (Nat.dvd_of_mem_primeFactorsList hp)
  have hval : k^2+1=8*(2*m^2+2*m)+5 := by rw [hm]; ring
  rw [hval] at hr
  omega

end OMA.Hasler

namespace OMA.R_OeisA1146_conjecture_R1
open OMA.Hasler

theorem cubicFilter {k : ℕ} (hk : 1<k) (h : (k^4-1 ∣ 2^k-1)) (h3 : ¬3∣k) :
    ∀ p ∈ ([7,13,19,37,61,67,73,79,97,103,139,151,163,181,193,199] : List ℕ), ¬p∣k^4-1 := by
  have cert : ([7,13,19,37,61,67,73,79,97,103,139,151,163,181,193,199] : List ℕ).all (fun p => decide (p.Prime ∧ 3 ∣ p-1 ∧ ¬p ∣ 2^((p-1)/3)-1)) = true := by
    decide +kernel
  intro p hm hd
  have hdata := (List.all_eq_true.mp cert) p hm
  simp only [decide_eq_true_eq] at hdata
  obtain ⟨hp,h3p,hn⟩ := hdata
  have hp1 := (localIff hk).mp h p 1 hp (by simpa using hd)
  simp only [pow_one] at hp1
  have hc := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm.of_dvd_left (Nat.gcd_dvd_left k (p-1))
  have hg : k.gcd (p-1) ∣ (p-1)/3 := hc.dvd_of_dvd_mul_left
    (by rw [Nat.mul_div_cancel' h3p]; apply Nat.gcd_dvd_right)
  exact hn (hp1.trans ((mersenneIff _ _).mpr hg))

/-- A power of two passes the original test exactly at the exponents 2^t for t≥2. -/
def H1 : Prop :=
  ∀ m : ℕ, (2^m)^4-1 ∣ 2^(2^m)-1 ↔ ∃ t : ℕ, 2≤t ∧ m=2^t

/-- For the remaining mixed even numbers, find a prime-power obstruction with
an exponent at most p-1. The two hypotheses on factors discard square factors
below the first Wieferich prime and sixteen classes of cubic nonresidues. -/
def H2 : Prop :=
  ∀ e u : ℕ, 2≤e → 1<u → Odd u →
    let k := 2^e*u
    (∀ q : ℕ, q.Prime → q<1093 → ¬q^2 ∣ k^4-1) →
    (3∣k ∨ ∀ p ∈ ([7,13,19,37,61,67,73,79,97,103,139,151,163,181,193,199] : List ℕ),
      ¬p ∣ k^4-1) →
    ∃ p j : ℕ, p.Prime ∧ 0<j ∧ p^j ∣ k^4-1 ∧ ¬p^j ∣ 2^(k.gcd (p-1))-1

theorem main : H1 → H2 → type_of% @OeisA1146.conjecture := by
  intro hPower hMixed k h hk
  obtain ⟨e,u,hu,he⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k≠0)
  rcases eq_or_ne u 1 with rfl | hn
  · rw [mul_one] at he
    subst k
    obtain ⟨t,ht,he⟩ := (hPower e).mp h
    exact ⟨t,ht,by simp [OeisA1146.a,he]⟩
  · have hfour := fourDvd hk h
    have hx : 2≤e := by
      by_contra hlt
      have : e=0 ∨ e=1 := by omega
      obtain ⟨v,hv⟩ := hu
      rcases this with rfl | rfl <;> norm_num at he <;> omega
    have hu1 : 1<u := by obtain ⟨v,hv⟩ := hu; omega
    have hc : 3∣k ∨ ∀ p∈([7,13,19,37,61,67,73,79,97,103,139,151,163,181,193,199] : List ℕ), ¬p∣k^4-1 :=
      or_iff_not_imp_left.mpr (cubicFilter hk h)
    have hm := hMixed e u hx hu1 hu
    rw [← he] at hm
    obtain ⟨p,j,hp,_,hdiv,hnot⟩ := hm (fun q hq hqsmall => excludeSquares hk h hq hqsmall) hc
    exact (hnot ((localIff hk).mp h p j hp hdiv)).elim

end OMA.R_OeisA1146_conjecture_R1
