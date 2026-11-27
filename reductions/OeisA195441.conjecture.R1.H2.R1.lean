import OMAReductions.R_OeisA195441_conjecture_R1
import Mathlib

/-!
For the prime case q ≡ 1 mod 30, a large prime factor of q+1 or q+2
already supplies the digit-sum witness. The reduction isolates the residual
smooth-neighbour case from the simultaneous semiprime case.
-/

namespace OMA.R_OeisA195441_conjecture_R1_H2_R1

private theorem digit_sum_mul_sub {p a m : ℕ} (hp : 2 ≤ p)
    (ha : 2 ≤ a) (hap : a ≤ p) (hm : a+1 ≤ m) (hmp : m ≤ p) :
    p ≤ (p.digits (m*p-a)).sum := by
  have hm' : m = (m-1)+1 := by omega
  have hdecomp : m*p-a = p*(m-1)+(p-a) := by
    have hmul : m*p = (m-1)*p+p := by
      calc
        m*p = ((m-1)+1)*p := congrArg (fun x : ℕ => x*p) hm'
        _ = (m-1)*p+p := by rw [Nat.add_mul, Nat.one_mul]
    calc
      m*p-a = (m-1)*p+p-a := by rw [hmul]
      _ = p*(m-1)+(p-a) := by rw [Nat.mul_comm (m-1) p]; omega
  have hpos : 0 < m*p-a := by
    have hp' : 0 < p := by omega
    have hm'' : 0 < m-1 := by omega
    have hmul : 0 < p*(m-1) := Nat.mul_pos hp' hm''
    rw [hdecomp]
    omega
  have hmod : (m*p-a)%p = p-a := by
    rw [hdecomp, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hdiv : (m*p-a)/p = m-1 := by
    have hpPos : 0 < p := by omega
    have hrem : p-a < p := Nat.sub_lt hpPos (by omega)
    rw [hdecomp, Nat.mul_add_div hpPos]
    simp [Nat.div_eq_of_lt hrem]
  rw [Nat.digits_eq_cons_digits_div (by omega) hpos.ne', hmod, hdiv,
    Nat.digits_of_lt p (m-1) (by omega) (by omega)]
  simp only [List.sum_cons]
  omega

private theorem factor_witness {q a p : ℕ} (hq : 61 < q)
    (ha : 3 ≤ a) (hap : a ≤ p) (hp : p.Prime)
    (hdiv : p ∣ q+a-2) (hmlo : a+1 ≤ (q+a-2)/p)
    (hmhi : (q+a-2)/p ≤ p) :
    ∃ r : ℕ, r.Prime ∧ ¬r ∣ q-1 ∧ r ≤ (r.digits (q-2)).sum := by
  let m := (q+a-2)/p
  have hmp : m*p = q+a-2 := Nat.div_mul_cancel hdiv
  have hmass : p ≤ (p.digits (q-2)).sum := by
    have hrel : q-2+a = m*p := by rw [hmp]; omega
    have : q-2 = m*p-a := by omega
    rw [this]
    exact digit_sum_mul_sub (by omega : 2 ≤ p) (by omega : 2 ≤ a)
      (by omega) (by simpa [m] using hmlo) (by simpa [m] using hmhi)
  have hnot : ¬p ∣ q-1 := by
    intro hqdiv
    have hd : p ∣ a-1 := by
      have h := Nat.dvd_sub hdiv hqdiv
      have heq : q+a-2-(q-1) = a-1 := by omega
      rw [heq] at h
      exact h
    have hpbound := Nat.le_of_dvd (by omega : 0 < a-1) hd
    omega
  exact ⟨p,hp,hnot,hmass⟩

def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 61 < q → q % 30 = 1 →
    (Nat.maxPrimeFac (q+1))^2 < q+1 ∨ (Nat.maxPrimeFac (q+2))^2 < q+2 →
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q-1 ∧ p ≤ (p.digits (q-2)).sum

def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 61 < q → q % 30 = 1 →
    (∃ p r : ℕ, p.Prime ∧ r.Prime ∧ q+1 = 2*p ∧ q+2 = 3*r) →
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q-1 ∧ p ≤ (p.digits (q-2)).sum

theorem main : H1 → H2 → OMA.R_OeisA195441_conjecture_R1.H2 := by
  intro hsmooth hsem
  intro q hq hq61 hqmod
  have hqodd : q % 2 = 1 := by omega
  have hqmod3 : q % 3 = 1 := by omega
  by_cases hplus : ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ p ∣ q+1 ∧
      4 ≤ (q+1)/p ∧ (q+1)/p ≤ p
  · obtain ⟨p,hp,hp3,hpd,hmlo,hmhi⟩ := hplus
    have hEq : q+3-2=q+1 := by omega
    have hdiv : p ∣ q+3-2 := by rw [hEq]; exact hpd
    have hmlo' : 4 ≤ (q+3-2)/p := by rw [hEq]; exact hmlo
    have hmhi' : (q+3-2)/p ≤ p := by rw [hEq]; exact hmhi
    simpa using factor_witness (q:=q) (a:=3) (p:=p) hq61 (by norm_num)
      (by omega) hp hdiv hmlo' hmhi'
  by_cases hplus2 : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ q+2 ∧
      5 ≤ (q+2)/p ∧ (q+2)/p ≤ p
  · obtain ⟨p,hp,hp5,hpd,hmlo,hmhi⟩ := hplus2
    have hEq : q+4-2=q+2 := by omega
    have hdiv : p ∣ q+4-2 := by rw [hEq]; exact hpd
    have hmlo' : 5 ≤ (q+4-2)/p := by rw [hEq]; exact hmlo
    have hmhi' : (q+4-2)/p ≤ p := by rw [hEq]; exact hmhi
    simpa using factor_witness (q:=q) (a:=4) (p:=p) hq61 (by norm_num)
      (by omega) hp hdiv hmlo' hmhi'
  let p := Nat.maxPrimeFac (q+1)
  let r := Nat.maxPrimeFac (q+2)
  have hp : p.Prime := by dsimp [p]; exact Nat.prime_maxPrimeFac_of_one_lt _ (by omega)
  have hr : r.Prime := by dsimp [r]; exact Nat.prime_maxPrimeFac_of_one_lt _ (by omega)
  have hpd : p ∣ q+1 := by dsimp [p]; exact Nat.maxPrimeFac_dvd
  have hrd : r ∣ q+2 := by dsimp [r]; exact Nat.maxPrimeFac_dvd
  by_cases hs1 : p^2 < q+1
  · exact hsmooth q hq hq61 hqmod (Or.inl hs1)
  by_cases hs2 : r^2 < q+2
  · exact hsmooth q hq hq61 hqmod (Or.inr hs2)
  have hp3 : 3 ≤ p := by
    by_contra! h
    have hp2 : p = 2 := by have := hp.two_le; omega
    have hlt : p^2 < q+1 := by rw [hp2]; omega
    exact hs1 hlt
  have hq2bound : q+2 ≤ r^2 := by omega
  have hr5 : 5 ≤ r := by nlinarith
  have hpm : (q+1)/p ≤ p := by
    have hprod : ((q+1)/p)*p = q+1 := Nat.div_mul_cancel hpd
    by_contra! h
    nlinarith
  have hrm : (q+2)/r ≤ r := by
    have hprod : ((q+2)/r)*r = q+2 := Nat.div_mul_cancel hrd
    by_contra! h
    nlinarith
  have hpmlo : (q+1)/p < 4 := by
    by_contra! hm
    exact hplus ⟨p,hp,hp3,hpd,hm,hpm⟩
  have hrmlo : (q+2)/r < 5 := by
    by_contra! hm
    exact hplus2 ⟨r,hr,hr5,hrd,hm,hrm⟩
  have hp2 : p ≠ 2 := by omega
  have hpodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hN1even : (q+1)%2=0 := by omega
  have hm1even : ((q+1)/p)%2=0 := by
    have hprod : ((q+1)/p)*p = q+1 := Nat.div_mul_cancel hpd
    have hmodprod := congrArg (fun n : ℕ => n%2) hprod
    rw [Nat.mul_mod, hpodd] at hmodprod
    omega
  have hm1pos : 0 < (q+1)/p := Nat.div_pos (Nat.le_of_dvd (by omega) hpd) hp.pos
  have hm1 : (q+1)/p = 2 := by omega
  have hrrodd : r ≠ 2 := by omega
  have hrodd : r % 2 = 1 := (hr.eq_two_or_odd).resolve_left hrrodd
  have hN2odd : (q+2)%2=1 := by omega
  have hm2odd : ((q+2)/r)%2=1 := by
    have hprod : ((q+2)/r)*r = q+2 := Nat.div_mul_cancel hrd
    have hmodprod := congrArg (fun n : ℕ => n%2) hprod
    rw [Nat.mul_mod, hrodd] at hmodprod
    omega
  have hm2notone : (q+2)/r ≠ 1 := by
    intro he
    have hprod : ((q+2)/r)*r = q+2 := Nat.div_mul_cancel hrd
    have hdiv3 : 3 ∣ q+2 := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    have hdiv3prod : 3 ∣ ((q+2)/r)*r := by rw [hprod]; exact hdiv3
    rcases (by norm_num : Nat.Prime 3).dvd_mul.mp hdiv3prod with hleft | hright
    · simpa [he] using hleft
    · have heq : r = 3 := (Nat.Prime.dvd_iff_eq hr (by decide : 3 ≠ 1)).mp hright
      omega
  have hm2pos : 0 < (q+2)/r := Nat.div_pos (Nat.le_of_dvd (by omega) hrd) hr.pos
  have hm2 : (q+2)/r = 3 := by omega
  have hsemiprime : (∃ u v : ℕ, u.Prime ∧ v.Prime ∧ q+1=2*u ∧ q+2=3*v) := by
    refine ⟨p,r,hp,hr,?_,?_⟩
    · have hprod : ((q+1)/p)*p = q+1 := Nat.div_mul_cancel hpd
      rw [hm1] at hprod
      simpa [Nat.mul_comm] using hprod.symm
    · have hprod : ((q+2)/r)*r = q+2 := Nat.div_mul_cancel hrd
      rw [hm2] at hprod
      simpa [Nat.mul_comm] using hprod.symm
  exact hsem q hq hq61 hqmod hsemiprime

end OMA.R_OeisA195441_conjecture_R1_H2_R1
