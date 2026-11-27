import FormalConjectures.ErdosProblems.«385»

/-! A one-sided gap criterion among products of two balanced primes.
The prime-product witness and least-factor calculation are adapted from
Aafi Khan Malek, Aafimalek/erdos-385-almost-all at
b4097a3b184ad80aaae869beb1d144a8f8f9096b, Erdos430Sqrt/Witness.lean.
The reduction to the next balanced product, the prime-square and distinct
factor tests, and the construction of the pointwise error term are new.

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
-- Credit: @marcusbuffett
open Erdos385 Filter Real Asymptotics
open scoped Topology
namespace OMA.R_Erdos385_erdos_385_variants_lb_R1

private def balanced (δ : ℝ) (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ q ∧ p*q=m ∧ (1-δ)*√(m:ℝ) ≤ p

private def previous (δ : ℝ) (B : ℕ) : Prop := ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a ≤ b ∧
  a*b < B ∧ (B:ℝ)-δ*√(B:ℝ) ≤ (a:ℝ)*b ∧ (1-δ)*√(B:ℝ) ≤ a

/-- Just below a large prime square, a close symmetric pair of primes already
gives a witness. The remaining squares require a balanced semiprime in the
one-sided window of width δ times the square root. -/
def H1 : Prop := ∀ δ : ℝ, 0 < δ → δ < 1/4 →
  ∀ᶠ p : ℕ in atTop, p.Prime →
  (¬ ∃ t : ℕ, 0 < t ∧ t < p ∧ (p-t).Prime ∧ (p+t).Prime ∧ (t:ℝ)^2 ≤ δ*p) →
  previous δ (p*p)

/-- For a large product of two distinct balanced primes, fill the preceding
window unless an opposite shift of the two factors already does so. -/
def H2 : Prop := ∀ δ : ℝ, 0 < δ → δ < 1/4 → ∀ᶠ B : ℕ in atTop,
  ∀ p q : ℕ, p.Prime → q.Prime → p < q → p*q=B → (1-δ)*√(B:ℝ) ≤ p →
  (¬ ∃ t : ℕ, 0 < t ∧ t < p ∧ (p-t).Prime ∧ (q+t).Prime ∧
      (t:ℝ)*((q:ℝ)-p+t) ≤ δ*√(B:ℝ) ∧ (1-δ)*√(B:ℝ) ≤ (p:ℝ)-t) →
  previous δ B

section
private lemma le_indexed {n m : ℕ} (hm : m < n) (hm1 : 1 < m) (hc : ¬ m.Prime) :
    m + m.minFac ≤ F n := by
  apply le_csSup _ (show m + m.minFac ∈ {m + m.minFac | (m < n) (_ : m.Composite)} from ⟨m,hm,⟨hm1,hc⟩,rfl⟩)
  refine ⟨n+n, ?_⟩
  rintro _ ⟨a,ha,ha',rfl⟩
  have := Nat.minFac_le (show 0 < a by have := ha'.1; omega)
  omega


private theorem minFac_mul_primes {p k : ℕ} (hp : p.Prime) (hk : k.Prime) (hpk : p ≤ k) :
    (p * k).minFac = p := by
  apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p k))
  have hq := Nat.minFac_prime (show p * k ≠ 1 by
    intro h; exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h))
  rcases (Nat.Prime.dvd_mul hq).mp (Nat.minFac_dvd (p * k)) with h | h
  · exact ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).ge
  · exact hpk.trans ((Nat.prime_dvd_prime_iff_eq hq hk).mp h).ge

private lemma shifted {δ : ℝ} {p q t : ℕ} (hpq : p ≤ q) (ht : 0 < t) (htp : t < p)
    (ha : (p-t).Prime) (hb : (q+t).Prime)
    (hgap : (t:ℝ)*((q:ℝ)-p+t) ≤ δ*√((p*q:ℕ):ℝ))
    (hlo : (1-δ)*√((p*q:ℕ):ℝ) ≤ (p:ℝ)-t) : previous δ (p*q) := by
  refine ⟨p-t,q+t,ha,hb,by omega,?_,?_,?_⟩
  · have hpos : (0:ℝ) < t := by exact_mod_cast ht
    have hle : (p:ℝ) ≤ q := by exact_mod_cast hpq
    have hpos' : 0 < (t:ℝ)*((q:ℝ)-p+t) := mul_pos hpos (by linarith)
    have he : (((p-t)*(q+t):ℕ):ℝ) < ((p*q:ℕ):ℝ) := by
      push_cast [Nat.cast_sub htp.le]
      linarith only [hpos']
    exact_mod_cast he
  · push_cast [Nat.cast_sub htp.le]
    push_cast at hgap
    linarith only [hgap]
  · simpa [Nat.cast_sub htp.le] using hlo

private lemma sqprev {δ : ℝ} {p t : ℕ} (ht : 0 < t) (htp : t < p)
    (ha : (p-t).Prime) (hb : (p+t).Prime) (hd : (t:ℝ)^2 ≤ δ*p) : previous δ (p*p) := by
  have hs : √((p*p:ℕ):ℝ) = p := by rw [Nat.cast_mul,Real.sqrt_mul_self (by positivity)]
  have ht1 : (1:ℝ) ≤ t := by exact_mod_cast ht
  apply shifted le_rfl ht htp ha hb
  · simpa [hs,pow_two] using hd
  · rw [hs]
    nlinarith [mul_nonneg (show 0 ≤ (t:ℝ) by positivity) (sub_nonneg.mpr ht1)]

private lemma prev_all (h₁ : H1) (h₂ : H2) {δ : ℝ} (hd : 0 < δ) (hd' : δ < 1/4) :
    ∀ᶠ m : ℕ in atTop, balanced δ m → previous δ m := by
  obtain ⟨P,hP⟩ := eventually_atTop.mp (h₁ δ hd hd')
  filter_upwards [h₂ δ hd hd',eventually_ge_atTop (P*P)] with m hm hlarge
  rintro ⟨p,q,hp,hq,hpq,rfl,hlo⟩
  rcases hpq.eq_or_lt with rfl | hlt
  · by_cases H : ∃ t : ℕ, 0<t ∧ t<p ∧ (p-t).Prime ∧ (p+t).Prime ∧ (t:ℝ)^2 ≤ δ*p
    · obtain ⟨t,ht,htp,ha,hb,he⟩ := H
      exact sqprev ht htp ha hb he
    · exact hP p (by nlinarith) hp H
  · by_cases H : ∃ t : ℕ, 0<t ∧ t<p ∧ (p-t).Prime ∧ (q+t).Prime ∧
        (t:ℝ)*((q:ℝ)-p+t) ≤ δ*√((p*q:ℕ):ℝ) ∧ (1-δ)*√((p*q:ℕ):ℝ) ≤ (p:ℝ)-t
    · obtain ⟨t,ht,htp,ha,hb,he,hbnd⟩ := H
      exact shifted hlt.le ht htp ha hb he hbnd
    · exact hm p q hp hq hlt rfl hlo H

private lemma quantitative (h₁ : H1) (h₂ : H2) {δ : ℝ} (hd : 0 < δ) (hd' : δ < 1/4) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ) + (1-2*δ)*√(n:ℝ) ≤ F n := by
  classical
  obtain ⟨M,hM⟩ := eventually_atTop.mp (prev_all h₁ h₂ hd hd')
  filter_upwards [eventually_ge_atTop M] with n hn
  have ex : ∃ B : ℕ, n ≤ B ∧ balanced δ B := by
    obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes n
    have hs : √((p*p:ℕ):ℝ) = p := by rw [Nat.cast_mul,Real.sqrt_mul_self (by positivity)]
    refine ⟨p*p,hp.trans (Nat.le_mul_self _),p,p,hprime,hprime,le_rfl,rfl,?_⟩
    rw [hs]
    nlinarith [mul_nonneg hd.le (show (0:ℝ) ≤ p by positivity)]
  let B := Nat.find ex
  have hB : n ≤ B ∧ balanced δ B := Nat.find_spec ex
  obtain ⟨a,b,ha,hb,hab,hm,hgap,hlo⟩ := hM B (hn.trans hB.1) hB.2
  have hbal : balanced δ (a*b) := ⟨a,b,ha,hb,hab,rfl,
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hm.le)) (by linarith)).trans hlo⟩
  have hlt : a*b<n := by
    by_contra! h
    exact (Nat.not_le_of_lt hm) (Nat.find_min' ex ⟨h,hbal⟩)
  have hf := le_indexed hlt (Nat.one_lt_mul_iff.mpr ⟨ha.pos,hb.pos,Or.inl ha.one_lt⟩)
    (Nat.not_prime_mul ha.one_lt.ne' hb.one_lt.ne')
  rw [minFac_mul_primes ha hb hab] at hf
  have hf' : (a:ℝ)*b+a ≤ F n := by exact_mod_cast hf
  have hnB : (n:ℝ) ≤ B := by exact_mod_cast hB.1
  have hrad := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnB) (show 0 ≤ 1-2*δ by linarith)
  linarith only [hgap,hlo,hf',hnB,hrad]

end

theorem main : H1 → H2 → type_of% @Erdos385.erdos_385.variants.lb := by
  intro h₁ h₂
  let e (n : ℕ) := 1 - ((F n:ℝ)-n)/√(n:ℝ)
  refine ⟨e,(Asymptotics.isLittleO_one_iff ℝ).mpr ?_,?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := min (ε/4) (1/8)
    have hd : 0<δ := lt_min (by positivity) (by norm_num)
    have hd' : δ<1/4 := (min_le_right _ _).trans_lt (by norm_num)
    have heps : 2*δ<ε := by have := min_le_left (ε/4) (1/8); dsimp [δ]; linarith
    filter_upwards [quantitative h₁ h₂ hd hd',eventually_ge_atTop (1:ℕ)] with n hl hn
    have hs : 0 < √(n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hu := Erdos385.trivial_ub n
    have hr : ((F n:ℕ):ℝ) ≤ (n:ℝ)+√(n:ℝ) := by exact_mod_cast hu
    rw [dist_zero_right,Real.norm_eq_abs,abs_lt]
    dsimp [e]
    constructor
    · have hdiv : ((F n:ℝ)-n)/√(n:ℝ) ≤ 1 := (div_le_iff₀ hs).mpr (by linarith)
      linarith
    · have hdiv : 1-2*δ ≤ ((F n:ℝ)-n)/√(n:ℝ) := (le_div_iff₀ hs).mpr (by linarith)
      linarith
  · intro n
    by_cases hn : n=0
    · subst n; simp
    · have hs : √(n:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn)).ne'
      dsimp [e]
      rw [sub_sub_cancel,div_mul_cancel₀ _ hs]
      linarith
end OMA.R_Erdos385_erdos_385_variants_lb_R1
