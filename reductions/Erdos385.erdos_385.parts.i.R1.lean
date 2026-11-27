import FormalConjectures.ErdosProblems.«385»

/-! Ported the prime-quotient criterion and elementary exception tests from
Aafi Khan Malek, Aafimalek/erdos-385-almost-all at b4097a3b184a.
The argument at the first missing prime and the progressions mod six are added here.

MIT License

Copyright (c) 2026 Aafi Khan Malek

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
open Erdos385 Filter
namespace OMA.R_Erdos385_erdos_385_parts_i_R1

private lemma le_indexed {n m : ℕ} (hm : m < n) (hm1 : 1 < m) (hc : ¬ m.Prime) :
    m + m.minFac ≤ F n := by
  apply le_csSup _ (show m + m.minFac ∈ {m + m.minFac | (m < n) (_ : m.Composite)} from ⟨m,hm,⟨hm1,hc⟩,rfl⟩)
  refine ⟨n+n, ?_⟩
  rintro _ ⟨a,ha,ha',rfl⟩
  have := Nat.minFac_le (show 0 < a by have := ha'.1; omega)
  omega

theorem lt_F_of_witness {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (hpp : p * p < n)
    (hmin : p ≤ (n / p).minFac) : n < F n := by
  have hp2 := hp.two_le
  have hk : p ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr hpp.le
  set k := n / p with hkdef
  have hk1 : k ≠ 1 := by omega
  have hminfac : (p * k).minFac = p := by
    apply le_antisymm (Nat.minFac_le_of_dvd hp2 (dvd_mul_right p k))
    have hq := Nat.minFac_prime (show p * k ≠ 1 by
      intro h; exact absurd (Nat.eq_one_of_mul_eq_one_right h) (by omega))
    rcases (Nat.Prime.dvd_mul hq).mp (Nat.minFac_dvd (p * k)) with h | h
    · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).ge
    · exact hmin.trans (Nat.minFac_le_of_dvd hq.two_le h)
  have hlt : p * k < n := by
    have hle : p * k ≤ n := Nat.mul_div_le n p
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd ⟨k, h.symm⟩ hpn
  have hval := le_indexed (m := p*k) hlt (by nlinarith) (Nat.not_prime_mul (by omega) hk1)
  rw [hminfac] at hval
  have hsucc : n < p * (k+1) := Nat.lt_mul_div_succ n hp.pos
  nlinarith
theorem lt_F_of_odd {n : ℕ} (hn : 7 ≤ n) (hodd : n % 2 = 1) : n < F n := by
  apply lt_F_of_witness Nat.prime_two (by omega) (by omega)
  exact (Nat.minFac_prime (by omega)).two_le

private lemma lt_F_of_not_prime_pred {n : ℕ} (hn : 5 ≤ n) (hnp : ¬ (n-1).Prime) : n < F n := by
  have := le_indexed (m := n-1) (n := n) (by omega) (by omega) hnp
  have := (Nat.minFac_prime (show n-1 ≠ 1 by omega)).two_le
  omega

/-- At an exception, subtracting the first prime not dividing n gives another prime
as soon as the difference exceeds one. -/
private lemma prime_at_first_missing {n q : ℕ} (hF : F n ≤ n) (hq : q.Prime)
    (hqn : q+1 < n) (hnd : ¬ q ∣ n) (hearly : ∀ r : ℕ, r.Prime → r < q → r ∣ n) :
    (n-q).Prime := by
  by_contra hnq
  let r := (n-q).minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hd : r ∣ n-q := Nat.minFac_dvd _
  have hqpos := hq.pos
  have hsmall : r ≤ q := by
    have hle := le_indexed (n := n) (m := n-q) (by omega) (by omega) hnq
    change n-q + r ≤ F n at hle
    omega
  by_cases he : r = q
  · have hdiv : q ∣ n-q := he ▸ hd
    exact hnd (by simpa only [Nat.sub_add_cancel (by omega : q ≤ n)] using Nat.dvd_add hdiv (dvd_refl q))
  · have hrn := hearly r hr (by omega)
    have hdq : r ∣ q := by
      have hh := Nat.dvd_sub hrn hd
      simpa only [show n - (n - q) = q by omega] using hh
    exact he ((Nat.prime_dvd_prime_iff_eq hr hq).1 hdq)

/-- Prime successors divisible by six, after the least-missing-prime test. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, 6 ∣ n → (n-1).Prime →
  (∀ q : ℕ, q.Prime → q+1 < n → ¬ q ∣ n →
     (∀ r : ℕ, r.Prime → r < q → r ∣ n) → (n-q).Prime) →
  ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n ∧ p*p < n ∧ p ≤ (n/p).minFac

/-- The complementary progression only needs the case of a twin prime pair. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop, n % 6 = 2 → (n-3).Prime → (n-1).Prime →
  ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n ∧ p*p < n ∧ p ≤ (n/p).minFac

theorem main : H1 → H2 → type_of% @Erdos385.erdos_385.parts.i := by
  intro h₀ h₂
  filter_upwards [h₀,h₂,eventually_ge_atTop (10 : ℕ)] with n h₀ h₂ hn
  by_contra! hbad
  have heven : n % 2 = 0 := by
    by_contra h
    exact (lt_F_of_odd (by omega) (by omega)).not_ge hbad
  have hp : (n-1).Prime := by
    by_contra h
    exact (lt_F_of_not_prime_pred (by omega) h).not_ge hbad
  have hfirst := fun q => prime_at_first_missing (q := q) hbad
  suffices ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n ∧ p*p < n ∧ p ≤ (n/p).minFac by
    obtain ⟨p,hpr,hpn,hpp,hm⟩ := this
    exact (lt_F_of_witness hpr hpn hpp hm).not_ge hbad
  by_cases h6 : 6 ∣ n
  · exact h₀ h6 hp hfirst
  · have hmod : n % 6 = 2 := by
      by_contra h
      have hd : 3 ∣ n-1 := by omega
      have he := hp.eq_one_or_self_of_dvd 3 hd
      omega
    apply h₂ hmod _ hp
    apply hfirst 3 Nat.prime_three (by omega) (by omega)
    intro r hr hlt
    have := hr.two_le
    have htwo : r = 2 := by omega
    subst r
    omega
end OMA.R_Erdos385_erdos_385_parts_i_R1
