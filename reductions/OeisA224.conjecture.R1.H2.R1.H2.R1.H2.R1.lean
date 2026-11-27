import OMAReductions.R_OeisA224_conjecture_R1_H2_R1_H2_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite prime-power extensions for the square-residue congruence

Thomas Ordowski posed the conjecture in OEIS A000224. The prime-power
square-count identity and multiplicativity come from the merged parent
reductions in this repository.
Source: https://oeis.org/A000224
Credit: @Hennyrick
-/

namespace OMA.CofactorSieve

/-- Eliminating the prime power from its square-count formula gives a divisibility test. -/
theorem local_sieve {m p x c s : ℕ} (cleared : 2*(p+1)*s = p*x+c)
    (h : (m*x)^2 ≡ 1 [MOD s]) : s ∣ (m*c)^2-p^2 := by
  have hn := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  push_cast at hn
  have hf := congrArg (fun z : ℕ => (z : ZMod s)) cleared
  push_cast at hf
  rw [ZMod.natCast_self, mul_zero] at hf
  have hx : (p : ZMod s)*x = -c := eq_neg_of_add_eq_zero_left hf.symm
  apply Nat.ModEq.dvd'
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  calc
    (p : ZMod s)^2 = p^2 * ((m : ZMod s)*x)^2 := by rw [hn, mul_one]
    _ = ((m : ZMod s)*(p*x))^2 := by ring
    _ = ((m : ZMod s)*c)^2 := by rw [hx]; ring

/-- After cancelling p², the remaining power is bounded by a function of the cofactor. -/
theorem relative_bound {m p e s c : ℕ} (hm : 1 < m) (hp : 3 ≤ p)
    (hc : p < c) (hc' : c ≤ 3*p) (hf : 2*(p+1)*s = p*p^e+c)
    (h : (m*p^e)^2 ≡ 1 [MOD s]) : p^e ≤ 27*m^2*p^2 := by
  have div := local_sieve hf h
  have hgt : p < m*c := by nlinarith only [Nat.mul_le_mul_right c (show 1 ≤ m by omega), hc]
  have hs := Nat.le_of_dvd (Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hgt (by decide : 2 ≠ 0))) div
  have hs' : s ≤ 9*m^2*p^2 := by
    have hm' := Nat.mul_le_mul_left m hc'
    have hpow := Nat.pow_le_pow_left hm' 2
    calc
      s ≤ (m*c)^2 := hs.trans (Nat.sub_le ..)
      _ ≤ (m*(3*p))^2 := hpow
      _ = _ := by ring
  have hx : p^e ≤ 3*s := by
    apply Nat.le_of_mul_le_mul_left (c := p) _ (by omega)
    nlinarith only [hf, Nat.mul_le_mul_right s (show 2 ≤ p by omega)]
  nlinarith only [hs',hx]

/-- For exponents at least three the sieve simultaneously bounds the prime and exponent. -/
theorem high_exponent_bound {m p e s c : ℕ} (hm : 1 < m) (hp : 3 ≤ p) (he : 3 ≤ e)
    (hc : p < c) (hc' : c ≤ 3*p) (hf : 2*(p+1)*s = p*p^e+c)
    (h : (m*p^e)^2 ≡ 1 [MOD s]) : p^e ≤ (27*m^2)^3 := by
  have hx2 := relative_bound hm hp hc hc' hf h
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le he
  have hsplit : p^(3+k) = p^(1+k)*p^2 := by rw [← pow_add]; congr 1; omega
  rw [hsplit] at hx2 ⊢
  have hpk : p^(1+k) ≤ 27*m^2 := Nat.le_of_mul_le_mul_right hx2 (by positivity)
  have hple : p ≤ 27*m^2 := (Nat.le_pow (by omega : 0 < 1+k)).trans hpk
  have hfinal := Nat.mul_le_mul hpk (Nat.pow_le_pow_left hple 2)
  calc
    _ ≤ _ := hfinal
    _ = _ := by ring

theorem first_power_div {m p s : ℕ}
    (hf : 2*(p+1)*s = p*p+(2*p+1))
    (h : (m*p)^2 ≡ 1 [MOD s]) : s ∣ m^2-1 := by
  have h1 : 2*s = p+1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p+1) (by nlinarith only [hf])
  have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have h2 := congrArg (fun z : ℕ => (z : ZMod s)) h1
  push_cast at hh h2
  rw [ZMod.natCast_self, mul_zero] at h2
  have h3 : (p : ZMod s) = -1 := eq_neg_of_add_eq_zero_left h2.symm
  rw [h3] at hh
  have hdiv : s ∣ m^2-1 := by
    apply Nat.ModEq.dvd'
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    calc
      (1 : ZMod s) = ((m : ZMod s)* -1)^2 := hh.symm
      _ = (m : ZMod s)^2 := by ring
  exact hdiv

theorem first_power_bound {m p s : ℕ} (hm : 1 < m)
    (hf : 2*(p+1)*s = p*p+(2*p+1))
    (h : (m*p)^2 ≡ 1 [MOD s]) : p ≤ 2*m^2 := by
  have h1 : 2*s = p+1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p+1) (by nlinarith only [hf])
  have hdiv := first_power_div hf h
  have hpos := Nat.pow_lt_pow_left hm (by decide : 2 ≠ 0)
  have hle := Nat.le_of_dvd (by simpa using Nat.sub_pos_of_lt hpos) hdiv
  omega

theorem second_power_bound {m p s : ℕ} (hp : 3 ≤ p)
    (hf : 2*(p+1)*s = p*p^2+(p+2))
    (h : (m*p^2)^2 ≡ 1 [MOD s]) : p ≤ 6*m^2+1 := by
  have h2 : 2*s+p = p^2+2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p+1) (by nlinarith only [hf])
  have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  have hc := congrArg (fun z : ℕ => (z : ZMod s)) h2
  push_cast at hh hc
  rw [ZMod.natCast_self, mul_zero, zero_add] at hc
  let P : ZMod s := p
  let M : ZMod s := m
  change P = P^2 + 2 at hc
  change (M*P^2)^2 = 1 at hh
  have hx : P^2 = P-2 := eq_sub_of_add_eq hc.symm
  have h4 : P^4 = 2-3*P := by
    calc
      P^4 = (P^2)^2 := by ring
      _ = (P-2)^2 := by rw [hx]
      _ = P^2-4*P+4 := by ring
      _ = _ := by rw [hx]; ring
  have hdiv : s ∣ 3*m^2*p+1-2*m^2 := by
    apply Nat.ModEq.dvd'
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    push_cast
    change 2*M^2 = 3*M^2*P+1
    calc
      2*M^2 = 3*M^2*P + M^2*(2-3*P) := by ring
      _ = 3*M^2*P + (M*P^2)^2 := by rw [← h4]; ring
      _ = _ := by rw [hh]
  have hl := Nat.mul_le_mul_left (m^2) hp
  have pos : 2*m^2 < 3*m^2*p+1 := by nlinarith only [hl]
  have hs := Nat.le_of_dvd (Nat.sub_pos_of_lt pos) hdiv
  have hs' : s ≤ 3*m^2*p+1 := hs.trans (Nat.sub_le ..)
  apply Nat.le_of_mul_le_mul_right (c := p) _ (by omega)
  nlinarith only [hs', h2]

theorem bound_of_cleared {m p e s : ℕ} (hm : 1 < m) (hp : 3 ≤ p) (he : 0 < e)
    (hf : 2*(p+1)*s = p*p^e + (if Even e then p+2 else 2*p+1))
    (ht : (m*p^e)^2 ≡ 1 [MOD s]) : p^e ≤ (27*m^2)^3 := by
  have hM : 1 ≤ m^2 := Nat.one_le_pow _ _ (by omega)
  by_cases he1 : e=1
  · subst e
    simp only [show ¬Even (1 : ℕ) by decide, if_false, pow_one] at hf ht ⊢
    have h := first_power_bound hm hf ht
    exact (show p ≤ 27*m^2 by omega).trans (Nat.le_pow (by decide : 0 < 3))
  by_cases he2 : e=2
  · subst e
    simp only [even_two, if_true] at hf
    have h := second_power_bound hp hf ht
    have hl : p ≤ 27*m^2 := by omega
    exact (Nat.pow_le_pow_left hl 2).trans (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3))
  apply high_exponent_bound hm hp (by omega) _ _ hf ht
  · split <;> omega
  · split <;> omega

open OeisA224

/-- Every possible prime-power extension of a fixed nontrivial cofactor lies in a finite range. -/
theorem bound {m p e : ℕ} (hm : 1 < m) (hp : p.Prime) (hpo : Odd p) (he : 0 < e)
    (ht : (m * p^e)^2 ≡ 1 [MOD a (p^e)]) : p^e ≤ (27*m^2)^3 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; obtain ⟨k,hk⟩ := hpo; omega
  exact bound_of_cleared hm hp3 he (OMA.RoughSquares.cleared p e hp hpo) ht

/-- A candidate with a prime appearing exactly once must satisfy a divisor test in its cofactor. -/
theorem prime_dvd {m p : ℕ} (hp : p.Prime) (hpo : Odd p)
    (ht : (m*p)^2 ≡ 1 [MOD a p]) : (p+1)/2 ∣ m^2-1 := by
  have hc := OMA.RoughSquares.cleared p 1 hp hpo
  simp only [show ¬Even (1 : ℕ) by decide, if_false, pow_one] at hc
  have hs : 2*a p = p+1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p+1) (by nlinarith only [hc])
  rw [show (p+1)/2 = a p by omega]
  exact first_power_div hc ht

/-- For exponent two the local count divides an integer depending only on the cofactor. -/
theorem square_dvd {m p : ℕ} (hp : p.Prime) (hpo : Odd p)
    (ht : (m*p^2)^2 ≡ 1 [MOD a (p^2)]) : a (p^2) ∣ 16*m^4+1-m^2 := by
  let s := a (p^2)
  have hf := OMA.RoughSquares.cleared p 2 hp hpo
  simp only [even_two, if_true] at hf
  have h2 : 2*s+p = p^2+2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p+1)
    (by dsimp only [s]; nlinarith only [hf])
  have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht
  have hc := congrArg (fun z : ℕ => (z : ZMod s)) h2
  push_cast at hh hc
  rw [ZMod.natCast_self, mul_zero, zero_add] at hc
  let P : ZMod s := p
  let M : ZMod s := m
  change P = P^2+2 at hc
  change (M*P^2)^2 = 1 at hh
  have hx : P^2 = P-2 := eq_sub_of_add_eq hc.symm
  have h4 : P^4 = 2-3*P := by
    calc
      P^4 = (P^2)^2 := by ring
      _ = (P-2)^2 := by rw [hx]
      _ = P^2-4*P+4 := by ring
      _ = _ := by rw [hx]; ring
  have hlin : 2*M^2-1 = 3*M^2*P := by
    apply sub_eq_of_eq_add
    calc
      2*M^2 = 3*M^2*P+M^2*(2-3*P) := by ring
      _ = 3*M^2*P+(M*P^2)^2 := by rw [← h4]; ring
      _ = _ := by rw [hh]
  apply Nat.ModEq.dvd'
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  change M^2 = 16*M^4+1
  symm
  apply sub_eq_zero.mp
  calc
    16*M^4+1-M^2 = (2*M^2-1)^2-3*M^2*(2*M^2-1)+2*(3*M^2)^2 := by ring
    _ = (3*M^2)^2*(P^2+2-P) := by rw [hlin]; ring
    _ = 0 := by rw [← hc]; ring

/-- Eliminating the cubed prime leaves a local congruence in the cofactor alone. -/
theorem cube_sieve {m p : ℕ} (hp : p.Prime) (hpo : Odd p)
    (ht : (m*p^3)^2 ≡ 1 [MOD a (p^3)]) :
    m^6+11*m^2 ≡ 39*m^4+1 [MOD a (p^3)] := by
  let s := a (p^3)
  have hf := OMA.RoughSquares.cleared p 3 hp hpo
  simp only [show ¬Even (3 : ℕ) by decide, if_false] at hf
  have h3 : 2*s+p^2 = p^3+p+1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p+1)
    (by dsimp only [s]; nlinarith only [hf])
  have hh := (ZMod.natCast_eq_natCast_iff _ _ _).mpr ht
  have hc := congrArg (fun z : ℕ => (z : ZMod s)) h3
  push_cast at hh hc
  rw [ZMod.natCast_self, mul_zero, zero_add] at hc
  let P : ZMod s := p
  let M : ZMod s := m
  let T := M^2
  change P^2 = P^3+P+1 at hc
  change (M*P^3)^2 = 1 at hh
  have f : P^3-P^2+P+1 = 0 := by
    calc
      _ = (P^3+P+1)-P^2 := by ring
      _ = 0 := by rw [← hc, sub_self]
  have g : T*P^6-1 = 0 := by
    calc
      _ = (M*P^3)^2-1 := by dsimp [T]; ring
      _ = 0 := by rw [hh, sub_self]
  have r : -(3*P^2*T)+2*P*T+2*T-1 = 0 := by
    calc
      _ = (T*P^6-1)-(P^3*T+P^2*T-2*T)*(P^3-P^2+P+1) := by ring
      _ = 0 := by rw [g,f]; ring
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  change M^6+11*M^2 = 39*M^4+1
  apply sub_eq_zero.mp
  calc
    _ = T^3-39*T^2+11*T-1 := by dsimp [T]; ring
    _ = (39*P*T^3-9*P*T^2-47*T^3+3*T^2)*(P^3-P^2+P+1) +
        (13*P^2*T^2-3*P^2*T-20*P*T^2+2*P*T+24*T^2-9*T+1)*
        (-(3*P^2*T)+2*P*T+2*T-1) := by ring
    _ = 0 := by rw [f,r]; ring

end OMA.CofactorSieve

namespace OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H2_R1

open OeisA224

/-- The largest prime occurs once. For a fixed cofactor, enumerate the divisors
of m² − 1 to generate every possible prime p = 2t − 1. -/
def H1 : Prop :=
  ∀ m p : ℕ, 1 < m → p.Prime → m.Coprime p → Odd (m*p) →
    5 ≤ (m*p).primeFactors.card → (∀ q ∈ (m*p).primeFactors, q ≤ p) →
    (∃ q ∈ (m*p).primeFactors, q < 16*(2^(m*p).primeFactors.card)^3) →
    (p+1)/2 ∣ m^2-1 →
    (m*p)^2 ≡ 1 [MOD a m * a p] → ¬ (m*p)^2 ≡ 1 [MOD a m * a p - 1]

/-- The largest prime occurs at least twice. For fixed m the prime power
ranges over a bounded interval, including when the exponent varies. -/
def H2 : Prop :=
  ∀ m p e : ℕ, 1 < m → p.Prime → m.Coprime p → 2 ≤ e → Odd (m*p^e) →
    5 ≤ (m*p^e).primeFactors.card → (∀ q ∈ (m*p^e).primeFactors, q ≤ p) →
    (∃ q ∈ (m*p^e).primeFactors, q < 16*(2^(m*p^e).primeFactors.card)^3) →
    p^e ≤ (27*m^2)^3 → p^e ≤ 27*m^2*p^2 →
    (e = 2 → a (p^2) ∣ 16*m^4+1-m^2) →
    (e = 3 → m^6+11*m^2 ≡ 39*m^4+1 [MOD a (p^3)]) →
    (m*p^e)^2 ≡ 1 [MOD a m * a (p^e)] →
    ¬ (m*p^e)^2 ≡ 1 [MOD a m * a (p^e) - 1]

theorem main : H1 → H2 → OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1.H2 := by
  intro single repeated n hn hr hs test
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hr
  let p := n.primeFactors.max' (Finset.card_pos.mp (by omega))
  have hmem : p ∈ n.primeFactors := Finset.max'_mem _ _
  have hp := Nat.prime_of_mem_primeFactors hmem
  have hd := Nat.dvd_of_mem_primeFactors hmem
  have hodd : Odd p := Odd.of_dvd_nat hn hd
  have hmax : ∀ q ∈ n.primeFactors, q ≤ p := fun q hq => Finset.le_max' _ q hq
  let e := n.factorization p
  let m := n / p^e
  have he : 0 < e := hp.factorization_pos_of_dvd hn0 hd
  have hm0 : 0 < m := Nat.ordCompl_pos p hn0
  have hmp : m.Coprime p := (Nat.coprime_ordCompl hp hn0).symm
  have eqn : m*p^e = n := Nat.div_mul_cancel (Nat.ordProj_dvd n p)
  have hm : 1 < m := by
    by_contra! h
    have hm1 : m = 1 := by omega
    have hpow : p^e = n := by simpa only [hm1, one_mul] using eqn
    rw [← hpow, Nat.primeFactors_prime_pow he.ne' hp] at hr
    simp at hr
  have counts := OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime hm0 (pow_pos hp.pos e) (hmp.pow_right e)
  have both := test
  rw [← eqn, counts] at both
  have first := both.of_dvd (dvd_mul_right (a m * a (p^e)) (a m * a (p^e) - 1))
  have second := both.of_dvd (dvd_mul_left (a m * a (p^e) - 1) (a m * a (p^e)))
  have loc := first.of_dvd (dvd_mul_left (a (p^e)) (a m))
  have hp3 : 3 ≤ p := by have := hp.two_le; obtain ⟨k,hk⟩ := hodd; omega
  rw [← eqn] at hn hr hs hmax
  by_cases one : e = 1
  · simp only [one, pow_one] at hn hr hs hmax loc first second
    exact single m p hm hp hmp hn hr hmax hs (OMA.CofactorSieve.prime_dvd hp hodd loc) first second
  · exact repeated m p e hm hp hmp (by omega) hn hr hmax hs
      (OMA.CofactorSieve.bound hm hp hodd he loc)
      (OMA.CofactorSieve.relative_bound hm hp3
        (by split <;> omega) (by split <;> omega) (OMA.RoughSquares.cleared p e hp hodd) loc)
      (fun eq2 => OMA.CofactorSieve.square_dvd hp hodd (by simpa only [eq2] using loc))
      (fun eq3 => OMA.CofactorSieve.cube_sieve hp hodd (by simpa only [eq3] using loc))
      first second

end OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H2_R1
