import OMAReductions.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2
import Mathlib.Data.ZMod.Basic

/-!
# The three-versus-five cases of the A056777 reduction

Prime-factor counts include multiplicity. An even three-factor endpoint and a
prime-cube endpoint cannot pair with a five-factor endpoint. For an odd squarefree
three-factor endpoint, only the larger orientation survives, with the five-factor
endpoint of shape p⁴q and the displayed bounds on its two primes. For an odd
repeated-prime three-factor endpoint, the two endpoints must be coprime and the
five-factor endpoint must be nonsquarefree with at least two distinct prime bases.

This reduces the original second hypothesis to higher factor counts and these two
odd five-factor cases. The parent reduction provides the small-factor framework
for the conjecture of Choudhury and Wei (arXiv:2606.10331).
-/

namespace OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1

open OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2

section
namespace A056777SquarefreeFiveMoments

private theorem pow_five_bounds (p q X Z : ℤ)
    (hp : 7 ≤ p) (hq : 3 ≤ q) (hX : 0 ≤ X)
    (hXup : 2*X ≤ q+2*p+1) (hZ : p^2*q-12 ≤ Z) (hcyc : Z^3 ≤ X^5) : 64*p<q := by
  have hp0 : 0<p := by omega
  have hq0 : 0<q := by omega
  have hp2 := pow_le_pow_left₀ (by decide : (0:ℤ) ≤ 7) hp 2
  have hp4 := pow_le_pow_left₀ (by decide : (0:ℤ) ≤ 7) hp 4
  have hpq : 147 ≤ p^2*q := by
    have h := mul_le_mul hp2 hq (by decide : (0:ℤ) ≤ 3) (sq_nonneg p)
    nlinarith only [h]
  have hZ0 : 0 ≤ Z := by omega
  have hZ9 : 9*(p^2*q) ≤ 10*Z := by omega
  have hcub := pow_le_pow_left₀ (show 0 ≤ 9*(p^2*q) by positivity) hZ9 3
  have hpScale := mul_le_mul_of_nonneg_right hp4 (show 0 ≤ p^2*q^3 by positivity)
  by_contra! hq64
  by_cases hqP : q<p
  · have hX2 : X ≤ 2*p := by omega
    have hx := pow_le_pow_left₀ hX hX2 5
    have hZ2 : 2*p^2 ≤ Z := by
      have hh := mul_nonneg (sq_nonneg p) (show 0 ≤ q-3 by omega)
      nlinarith only [hh,hZ,hp2]
    have hz := pow_le_pow_left₀ (show 0 ≤ 2*p^2 by positivity) hZ2 3
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ p^5 by positivity)
    have hh' : 0<p^5 := by positivity
    nlinarith only [hx,hz,hh,hh',hcyc]
  by_cases hq4 : q ≤ 4*p
  · have hX2 : X ≤ 2*q := by omega
    have hx := pow_le_pow_left₀ hX hX2 5
    have hqle := pow_le_pow_left₀ hq0.le hq4 2
    have hh := mul_le_mul_of_nonneg_right hqle (show 0 ≤ q^3 by positivity)
    have hpos : 0<p^2*q^3 := by positivity
    nlinarith only [hcub,hx,hh,hpScale,hcyc,hpos]
  · have hx4 : 5*X ≤ 4*q := by omega
    have hx := pow_le_pow_left₀ (show 0 ≤ 5*X by positivity) hx4 5
    have hqle := pow_le_pow_left₀ hq0.le hq64 2
    have hh := mul_le_mul_of_nonneg_right hqle (show 0 ≤ q^3 by positivity)
    have hpos : 0<p^2*q^3 := by positivity
    nlinarith only [hcub,hx,hh,hpScale,hcyc,hpos]

/-- The moment inequalities for a squarefree quintic cannot hold at the values
required by a repeated square-times-prime endpoint. -/
theorem moments_impossible (p q X A Y Z : ℤ)
    (hp : 7 ≤ p) (hq : 3 ≤ q) (hA : 0 ≤ A) (hY : 0 ≤ Y) (hX : 0 ≤ X)
    (hK : 2*(X+A)=q+2*p+1)
    (hYup : 2*Y ≤ 2*p^2+(2*p+1)*q+1)
    (hZ : p^2*q-12 ≤ Z)
    (hcyc : Z^3 ≤ X^5) (hXA : 30*A ≤ X) (hNew : 5*X*Z ≤ 2*Y^2) : False := by
  have hp0 : 0<p := by omega
  have hq0 : 0<q := by omega
  have hq64 : 64*p<q := pow_five_bounds p q X Z hp hq hX (by omega) hZ hcyc
  have hY' : 11*Y ≤ 12*p*q := by
    have hh := mul_nonneg (show 0 ≤ 2*p-11 by omega) (show 0 ≤ q-64*p by omega)
    have hp2 := pow_le_pow_left₀ (by decide : (0:ℤ) ≤ 7) hp 2
    have h2 := mul_nonneg hp0.le (show 0 ≤ p-7 by omega)
    nlinarith only [hh,hYup,h2,hp2]
  have hX' : 31*X ≥ 15*q := by omega
  have hZ' : 100*Z ≥ 99*p^2*q := by
    have hp2 := pow_le_pow_left₀ (by decide : (0:ℤ) ≤ 7) hp 2
    have hq' : 448 ≤ q := by omega
    have hh := mul_le_mul hp2 hq' (by decide : (0:ℤ) ≤ 448) (sq_nonneg p)
    nlinarith only [hh,hZ]
  have hZ0 : 0 ≤ Z := by
    have hh : 0 ≤ 99*p^2*q := by positivity
    omega
  have hXprod := mul_le_mul hX' hZ' (show 0 ≤ 99*p^2*q by positivity)
    (show 0 ≤ 31*X by positivity)
  have hYsq := pow_le_pow_left₀ (show 0 ≤ 11*Y by positivity) hY' 2
  have hpos : 0<p^2*q^2 := by positivity
  nlinarith only [hXprod,hYsq,hNew,hpos]

end A056777SquarefreeFiveMoments
end

section
open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777ThreeSquarefreeFive

private theorem squarefree_five_shape {m : ℕ} (hm : m.primeFactorsList.length=5)
    (hs : Squarefree m) :
    ∃ a b c d e : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧ e.Prime ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ m=a*b*c*d*e := by
  obtain ⟨a,b,c,d,e,he⟩ : ∃ a b c d e, m.primeFactorsList=[a,b,c,d,e] := by
    generalize hl : m.primeFactorsList = l at hm ⊢
    rcases l with _ | ⟨a,l⟩
    · simp at hm
    rcases l with _ | ⟨b,l⟩
    · simp at hm
    rcases l with _ | ⟨c,l⟩
    · simp at hm
    rcases l with _ | ⟨d,l⟩
    · simp at hm
    rcases l with _ | ⟨e,l⟩
    · simp at hm
    rcases l with _ | ⟨f,l⟩
    · exact ⟨a,b,c,d,e,rfl⟩
    · simp at hm
  have ha := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=a) (by simp [he])
  have hb := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=b) (by simp [he])
  have hc := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=c) (by simp [he])
  have hd := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=d) (by simp [he])
  have hp := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=e) (by simp [he])
  have hn := hs.nodup_primeFactorsList
  simp only [he,List.nodup_cons,List.mem_cons,not_or,List.not_mem_nil,not_false_eq_true,
    List.nodup_nil,and_true] at hn
  have hf := (Nat.prod_primeFactorsList hs.ne_zero).symm
  exact ⟨a,b,c,d,e,ha,hb,hc,hd,hp,hn.1.1,hn.1.2.1,hn.1.2.2.1,hn.1.2.2.2,
    hn.2.1.1,hn.2.1.2.1,hn.2.1.2.2,hn.2.2.1.1,hn.2.2.1.2,hn.2.2.2,
    by simpa [he,mul_assoc] using hf⟩

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p=p+1 := by
  simpa using sigma_one_apply_prime_pow (i:=1) hp

private theorem quintic_formulas {a b c d e : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime) (he : e.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    (σ 1 (a*b*c*d*e)+(a*b*c*d*e).totient =
      2*(a*b*c*d*e)+2*(a*b*c+a*b*d+a*b*e+a*c*d+a*c*e+a*d*e+
        b*c*d+b*c*e+b*d*e+c*d*e+a+b+c+d+e)) ∧
    ((a*b*c*d*e).totient+(a*b*c*d+a*b*c*e+a*b*d*e+a*c*d*e+b*c*d*e)+
        (a*b+a*c+a*d+a*e+b*c+b*d+b*e+c*d+c*e+d*e)+1 =
      a*b*c*d*e+(a*b*c+a*b*d+a*b*e+a*c*d+a*c*e+a*d*e+b*c*d+b*c*e+b*d*e+c*d*e)+
        (a+b+c+d+e)) := by
  have h₁ := (Nat.coprime_primes ha hb).mpr hab
  have h₂ := ((Nat.coprime_primes ha hc).mpr hac).mul_left ((Nat.coprime_primes hb hc).mpr hbc)
  have h₃ := (((Nat.coprime_primes ha hd).mpr had).mul_left
    ((Nat.coprime_primes hb hd).mpr hbd)).mul_left ((Nat.coprime_primes hc hd).mpr hcd)
  have h₄ := ((((Nat.coprime_primes ha he).mpr hae).mul_left
    ((Nat.coprime_primes hb he).mpr hbe)).mul_left ((Nat.coprime_primes hc he).mpr hce)).mul_left
      ((Nat.coprime_primes hd he).mpr hde)
  rw [Nat.totient_mul h₄,Nat.totient_mul h₃,Nat.totient_mul h₂,Nat.totient_mul h₁,
    Nat.totient_prime ha,Nat.totient_prime hb,Nat.totient_prime hc,Nat.totient_prime hd,
    Nat.totient_prime he,isMultiplicative_sigma.map_mul_of_coprime h₄,
    isMultiplicative_sigma.map_mul_of_coprime h₃,isMultiplicative_sigma.map_mul_of_coprime h₂,
    isMultiplicative_sigma.map_mul_of_coprime h₁,sigma_prime ha,sigma_prime hb,sigma_prime hc,
    sigma_prime hd,sigma_prime he]
  have ha1 := ha.pos
  have hb1 := hb.pos
  have hc1 := hc.pos
  have hd1 := hd.pos
  have he1 := he.pos
  zify [ha1,hb1,hc1,hd1,he1]
  constructor <;> ring

private theorem cube_excess {p : ℕ} (hp : p.Prime) :
    σ 1 (p^3)+(p^3).totient=2*p^3+p+1 := by
  have hσ : σ 1 (p^3)=1+p+p^2+p^3 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  rw [hσ,show (p^3).totient=p^2*(p-1) from Nat.totient_prime_pow_succ hp 2]
  have hp1 := hp.pos
  zify [hp1]
  ring

private theorem product_three_far_below_cube {p a b c : ℕ} (hp : 3 ≤ p)
    (ha : a < p) (hb : b < p) (hc : c < p) : a*b*c+12 < p^3 := by
  have h₁ : a ≤ p-1 := by omega
  have h₂ : b ≤ p-1 := by omega
  have h₃ : c ≤ p-1 := by omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
  have hp₁ : 1 ≤ p := by omega
  zify [hp₁] at hprod hp ⊢
  have hh : 9 ≤ (p : ℤ)*p := calc
    9 = (3 : ℤ)*3 := by decide
    _ ≤ _ := mul_le_mul hp hp (by decide) (by omega)
  have hq := mul_nonneg (show 0 ≤ (p : ℤ) by omega) (show 0 ≤ (p : ℤ)-3 by omega)
  nlinarith only [hprod,hh,hq]

/-- A prime cube cannot be paired with a squarefree five-factor endpoint. -/
theorem no_cube_squarefree_five_pair {p m : ℕ}
    (hp : p.Prime) (hm : m.primeFactorsList.length=5) (hs : Squarefree m)
    (hgap : p^3+12=m ∨ m+12=p^3)
    (hφ : (p^3).totient+m=m.totient+p^3) (hσ : σ 1 (p^3)+m=σ 1 m+p^3) : False := by
  by_cases hp2 : p=2
  · subst p
    have ht : 4 ∣ m := by norm_num at hgap; omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) ht
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨a,b,c,d,e,ha,hb,hc,hd,he,hab,hac,had,hae,hbc,hbd,hbe,hcd,hce,hde,rfl⟩ :=
    squarefree_five_shape hm hs
  have hq := (quintic_formulas ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde).1
  have hpc := cube_excess hp
  have hlt1 : a*b*c < p := by omega
  have hlt2 : d*e < p := by
    have ha1 : 1 ≤ a := ha.pos
    have ht := Nat.mul_le_mul_right (d*e) ha1
    simp only [one_mul] at ht
    have hprod : a*(d*e)=a*d*e := by ring
    rw [hprod] at ht
    omega
  have hlt := product_three_far_below_cube hp3 hlt1 hlt2 (show 1<p by omega)
  have hf : a*b*c*d*e=(a*b*c)*(d*e)*1 := by ring
  rw [hf] at hgap
  omega

/-- With a squarefree five-factor partner, a three-factor endpoint must be odd
and of the form p²q with two distinct odd primes. -/
theorem remaining_three_squarefree_five {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5) (hs : Squarefree m)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ Odd p ∧ Odd q ∧ Odd m ∧ n=p^2*q := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hns : ¬Squarefree n := by
    intro hfree
    have hc {x : ℕ} (hsx : Squarefree x) (hx : 3 ≤ x.primeFactorsList.length) :
        3 ≤ x.primeFactors.card := by
      rwa [← Nat.toFinset_factors,List.toFinset_card_of_nodup hsx.nodup_primeFactorsList]
    by_cases he : Even n
    · have hmE : Even m := Nat.even_iff.mpr (by have := Nat.even_iff.mp he; omega)
      have hg' := hgap
      rcases hg' with h|h
      · rw [← h] at hs hφ hσ
        exact A056777Squarefree.no_even_squarefree_pair he hfree hs (by omega) (by omega)
      · rw [← h] at hfree hφ hσ
        exact A056777Squarefree.no_even_squarefree_pair hmE hs hfree (by omega) (by omega)
    · have ho := Nat.not_even_iff_odd.mp he
      have hom : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
      exact A056777FourFour.no_odd_three_distinct_pair ho hom (hc hfree (by omega)) (hc hs (by omega))
        hgap hφ
  obtain ⟨p,q,hp,hq,hform⟩ :=
    A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hn hns
  have hpq : p ≠ q := by
    rintro rfl
    have hf : n=p^3 := by rw [hform]; ring
    rw [hf] at hgap hφ hσ
    exact no_cube_squarefree_five_pair hp hm hs hgap hφ hσ
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hdm : 4∣m := by
      have hn4 : 4∣n := hform ▸ (dvd_mul_right ((2:ℕ)^2) q)
      omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) hdm
  have hq2 : q ≠ 2 := by
    rintro rfl
    have hshape : ∃ p:ℕ, n=2*p^2 := ⟨p,by rw [hform,mul_comm]⟩
    rcases hgap with hh|hh
    · have hstep : σ 1 (n+12)=σ 1 n+12 := by rw [hh]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hn0 hstep).1 (Or.inr hshape)
    · have hstep : σ 1 (m+12)=σ 1 m+12 := by rw [hh]; omega
      obtain ⟨p,hp'⟩ := hshape
      exact (A056777Parity.no_square_shapes_of_sigma_step hs.ne_zero hstep).2
        (Or.inr ⟨p,hh.trans hp'⟩)
  have hop : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hoq : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  have hon : Odd n := by rw [hform]; exact (hop.pow).mul hoq
  have hom : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hon; omega)
  exact ⟨p,q,hp,hq,hpq,hop,hoq,hom,hform⟩

private theorem squarefree_four_large_totient_defect {m : ℕ}
    (hm : m.primeFactorsList.length=4) (hs : Squarefree m) :
    m.totient+8 ≤ m := by
  rcases A056777CubeFour.four_factor_shape hm with ⟨k,hk⟩ | ⟨p,q,hp,hq,hne,he⟩ |
    ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,he⟩ | ⟨a,b,c,d,ha,hb,hc,hd,hab,hac,had,hbc,hbd,hcd,rfl⟩
  · have hD : k*k∣m := by rw [hk,pow_two]
    have hk1 := Nat.isUnit_iff.mp (hs k hD)
    simp [hk,hk1] at hm
  · exact ((Nat.squarefree_iff_prime_squarefree.mp hs p hp) ⟨p*q,by rw [he]; ring⟩).elim
  · exact ((Nat.squarefree_iff_prime_squarefree.mp hs p hp) ⟨q*r,by rw [he]; ring⟩).elim
  · have h₁ := (Nat.coprime_primes ha hb).mpr hab
    have h₂ := ((Nat.coprime_primes ha hc).mpr hac).mul_left ((Nat.coprime_primes hb hc).mpr hbc)
    have h₃ := (((Nat.coprime_primes ha hd).mpr had).mul_left
      ((Nat.coprime_primes hb hd).mpr hbd)).mul_left ((Nat.coprime_primes hc hd).mpr hcd)
    rw [Nat.totient_mul h₃,Nat.totient_mul h₂,Nat.totient_mul h₁,
      Nat.totient_prime ha,Nat.totient_prime hb,Nat.totient_prime hc,Nat.totient_prime hd]
    have hbnd := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl (a-1))
      (Nat.sub_le b 1)) (Nat.sub_le c 1)) (Nat.sub_le d 1)
    have h8 := Nat.mul_le_mul (Nat.mul_le_mul hb.two_le hc.two_le) hd.two_le
    have ha1 := ha.pos
    zify [ha1] at hbnd h8 ⊢
    nlinarith only [hbnd,h8]

private theorem no_base_three_squarefree_five {q m : ℕ}
    (hq : q.Prime) (hq3 : q ≠ 3) (hm : m.primeFactorsList.length=5) (hs : Squarefree m)
    (hgap : 3^2*q+12=m ∨ m+12=3^2*q)
    (hφ : (3^2*q).totient+m=m.totient+3^2*q) : False := by
  have hm3 : 3∣m := by norm_num at hgap; omega
  obtain ⟨M,hM⟩ := hm3
  have hms : Squarefree (3*M) := hM ▸ hs
  have hM0 : M ≠ 0 := fun h => hs.ne_zero (by simp [hM,h])
  have hcop := Nat.coprime_of_squarefree_mul hms
  have hMfree := hms.squarefree_of_dvd (dvd_mul_left M 3)
  have hal := (Nat.perm_primeFactorsList_mul (by decide : (3:ℕ) ≠ 0) hM0).length_eq
  rw [← hM,Nat.primeFactorsList_prime Nat.prime_three,
    List.length_append,List.length_singleton,hm] at hal
  have hbig := squarefree_four_large_totient_defect (by omega : M.primeFactorsList.length=4) hMfree
  have hc := ((Nat.coprime_primes Nat.prime_three hq).mpr hq3.symm).pow_left 2
  rw [hM,Nat.totient_mul hc,Nat.totient_mul hcop,
    show ((3:ℕ)^2).totient=6 by decide,Nat.totient_prime hq,Nat.totient_prime Nat.prime_three] at hφ
  rw [hM] at hgap
  norm_num at hφ hgap
  have := hq.two_le
  omega

/-- The residual odd p²q endpoint for a squarefree five-factor partner
has the indicated two residue classes and a repeated prime of at least seven. -/
theorem three_squarefree_five_residues {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hop : Odd p) (hoq : Odd q) (hom : Odd m)
    (hm : m.primeFactorsList.length=5) (hs : Squarefree m)
    (hgap : p^2*q+12=m ∨ m+12=p^2*q)
    (hφ : (p^2*q).totient+m=m.totient+p^2*q) (hσ : σ 1 (p^2*q)+m=σ 1 m+p^2*q) :
    7 ≤ p ∧ p%4=3 ∧ q%8=3 := by
  have hcard : 3 ≤ m.primeFactors.card := by
    rw [← Nat.toFinset_factors,List.toFinset_card_of_nodup hs.nodup_primeFactorsList,hm]
    decide
  have hdφ : 8∣m.totient := (pow_dvd_pow 2 hcard).trans
    (A056777OddFour.two_pow_card_dvd_totient hom)
  have hfilt : (m.primeFactors.filter fun x => x ≠ 2 ∧ Odd (m.factorization x)) = m.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    have ⟨hxP,hxD,hx0⟩ := Nat.mem_primeFactors.mp hx
    have hx2 : x ≠ 2 := by
      rintro rfl
      have := Nat.odd_iff.mp hom
      omega
    have hx1 := hxP.factorization_pos_of_dvd hx0 hxD
    have hxle := hs.natFactorization_le_one x
    have he : m.factorization x=1 := by omega
    exact ⟨hx2,he ▸ (by decide : Odd 1)⟩
  have hdσ := A056777Squarefree.two_pow_card_odd_exponents_dvd_sigma hs.ne_zero
  rw [hfilt] at hdσ
  have hdσ' : 8∣σ 1 m := (pow_dvd_pow 2 hcard).trans hdσ
  have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hφp : (p^2).totient=p*(p-1) := by simpa using Nat.totient_prime_pow_succ hp 1
  have hσp : σ 1 (p^2)=1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact no_base_three_squarefree_five hq hpq.symm hm hs hgap hφ
  rw [Nat.totient_mul hc,hφp,Nat.totient_prime hq] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,hσp,sigma_prime hq] at hσ
  have hpo := Nat.odd_iff.mp hop
  have hqo := Nat.odd_iff.mp hoq
  have hnd : ¬8∣p*(p-1)*(q-1) := by omega
  have hp4 : p%4=3 := by
    by_contra h
    have hpD : 4∣p-1 := by omega
    have hqD : 2∣q-1 := by omega
    exact hnd (mul_dvd_mul (dvd_mul_of_dvd_right hpD p) hqD)
  have hq4 : q%4=3 := by
    by_contra h
    have hpD : 2∣p-1 := by omega
    have hqD : 4∣q-1 := by omega
    exact hnd (mul_dvd_mul (dvd_mul_of_dvd_right hpD p) hqD)
  have hq8 : q%8=3 := by
    by_contra h
    have hd : 8∣q+1 := by omega
    have hh := dvd_mul_of_dvd_right hd (1+p+p^2)
    omega
  exact ⟨by omega,hp4,hq8⟩

private theorem distinct_odd_pair_ge_fifteen {a b : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hoa : Odd a) (hob : Odd b) (hne : a ≠ b) :
    15 ≤ a*b := by
  have ha2 := ha.two_le
  have hb2 := hb.two_le
  have haO := Nat.odd_iff.mp hoa
  have hbO := Nat.odd_iff.mp hob
  by_cases h : a=3
  · exact Nat.mul_le_mul (by omega : 3 ≤ a) (by omega : 5 ≤ b)
  · exact Nat.mul_le_mul (by omega : 5 ≤ a) (by omega : 3 ≤ b)

set_option maxHeartbeats 1200000 in
private theorem quintic_moment_bounds (a b c d e : ℤ)
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hc : 3 ≤ c) (hd : 3 ≤ d) (he : 3 ≤ e)
    (hab : 15 ≤ a*b) (hac : 15 ≤ a*c) (had : 15 ≤ a*d) (hae : 15 ≤ a*e) (hbc : 15 ≤ b*c) (hbd : 15 ≤ b*d) (hbe : 15 ≤ b*e) (hcd : 15 ≤ c*d) (hce : 15 ≤ c*e) (hde : 15 ≤ d*e) :
    let A := a+b+c+d+e
    let E := a*b+a*c+a*d+a*e+b*c+b*d+b*e+c*d+c*e+d*e
    let X := a*b*c+a*b*d+a*b*e+a*c*d+a*c*e+a*d*e+b*c*d+b*c*e+b*d*e+c*d*e
    let Y := a*b*c*d+a*b*c*e+a*b*d*e+a*c*d*e+b*c*d*e
    let Z := a*b*c*d*e
    30*A ≤ X ∧ A ≤ E ∧ Z^3 ≤ X^5 ∧ 5*X*Z ≤ 2*Y^2 := by
  intro A E X Y Z
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [A,X]
    have ha' := mul_nonneg (show 0 ≤ a by omega) (show 0 ≤ b*c + b*d + b*e + c*d + c*e + d*e-90 by omega)
    have hb' := mul_nonneg (show 0 ≤ b by omega) (show 0 ≤ a*c + a*d + a*e + c*d + c*e + d*e-90 by omega)
    have hc' := mul_nonneg (show 0 ≤ c by omega) (show 0 ≤ a*b + a*d + a*e + b*d + b*e + d*e-90 by omega)
    have hd' := mul_nonneg (show 0 ≤ d by omega) (show 0 ≤ a*b + a*c + a*e + b*c + b*e + c*e-90 by omega)
    have he' := mul_nonneg (show 0 ≤ e by omega) (show 0 ≤ a*b + a*c + a*d + b*c + b*d + c*d-90 by omega)
    nlinarith only [ha',hb',hc',hd',he']
  · dsimp [A,E]
    have h₁ := mul_nonneg (show 0 ≤ a-2 by omega) (show 0 ≤ b-1 by omega)
    have h₂ := mul_nonneg (show 0 ≤ c-2 by omega) (show 0 ≤ d-1 by omega)
    have h₃ := mul_nonneg (show 0 ≤ a-1 by omega) (show 0 ≤ e by omega)
    nlinarith only [h₁,h₂,h₃,hb,hd,hac,had,hbc,hbd,hbe,hce,hde]
  · have ha0 : 0 ≤ a := by omega
    have hb0 : 0 ≤ b := by omega
    have hc0 : 0 ≤ c := by omega
    have hd0 : 0 ≤ d := by omega
    have he0 : 0 ≤ e := by omega
    have hX0 : 0 ≤ X := by dsimp [X]; positivity
    have habc : 0 ≤ a*b*c := by positivity
    have habd : 0 ≤ a*b*d := by positivity
    have habe : 0 ≤ a*b*e := by positivity
    have hacd : 0 ≤ a*c*d := by positivity
    have hace : 0 ≤ a*c*e := by positivity
    have hade : 0 ≤ a*d*e := by positivity
    have hbcd : 0 ≤ b*c*d := by positivity
    have hbce : 0 ≤ b*c*e := by positivity
    have hbde : 0 ≤ b*d*e := by positivity
    have hcde : 0 ≤ c*d*e := by positivity
    have htabc : a*b*c ≤ X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have htbcd : b*c*d ≤ X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have htcde : c*d*e ≤ X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have htade : a*d*e ≤ X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have htabe : a*b*e ≤ X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have h₁ := mul_le_mul htabc htbcd hbcd hX0
    have h₂ := mul_le_mul h₁ htcde hcde (mul_nonneg hX0 hX0)
    have h₃ := mul_le_mul h₂ htade hade (by positivity : 0 ≤ X*X*X)
    have h₄ := mul_le_mul h₃ htabe habe (by positivity : 0 ≤ X*X*X*X)
    calc
      Z^3 = (a*b*c)*(b*c*d)*(c*d*e)*(a*d*e)*(a*b*e) := by dsimp [Z]; ring
      _ ≤ X*X*X*X*X := h₄
      _ = X^5 := by ring
  · let L₁ := a*b*c*d
    let L₂ := a*b*c*e
    let L₃ := a*b*d*e
    let L₄ := a*c*d*e
    let L₅ := b*c*d*e
    have hN : 5*(L₁*L₂+L₁*L₃+L₁*L₄+L₁*L₅+L₂*L₃+L₂*L₄+L₂*L₅+L₃*L₄+L₃*L₅+L₄*L₅) ≤ 2*(L₁+L₂+L₃+L₄+L₅)^2 := by
      nlinarith only [sq_nonneg (L₁-L₂),
        sq_nonneg (L₁-L₃),
        sq_nonneg (L₁-L₄),
        sq_nonneg (L₁-L₅),
        sq_nonneg (L₂-L₃),
        sq_nonneg (L₂-L₄),
        sq_nonneg (L₂-L₅),
        sq_nonneg (L₃-L₄),
        sq_nonneg (L₃-L₅),
        sq_nonneg (L₄-L₅)]
    calc
      5*X*Z = 5*(L₁*L₂+L₁*L₃+L₁*L₄+L₁*L₅+L₂*L₃+L₂*L₄+L₂*L₅+L₃*L₄+L₃*L₅+L₄*L₅) := by dsimp [X,Z,L₁,L₂,L₃,L₄,L₅]; ring
      _ ≤ 2*(L₁+L₂+L₃+L₄+L₅)^2 := hN
      _ = 2*Y^2 := by dsimp [Y,L₁,L₂,L₃,L₄,L₅]

set_option maxHeartbeats 1200000 in
/-- No three-factor endpoint has a squarefree five-factor partner in A056777.
The orientation of the twelve-step is arbitrary. -/
theorem no_three_squarefree_five_pair {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5) (hs : Squarefree m)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) : False := by
  obtain ⟨p,q,hp,hq,hpq,hop,hoq,hom,hform⟩ := remaining_three_squarefree_five hn hm hs hgap hφ hσ
  rw [hform] at hgap hφ hσ
  have hp7 := (three_squarefree_five_residues hp hq hpq hop hoq hom hm hs hgap hφ hσ).1
  obtain ⟨a,b,c,d,e,ha,hb,hc,hd,he,hab,hac,had,hae,hbc,hbd,hbe,hcd,hce,hde,hM⟩ :=
    squarefree_five_shape hm hs
  rw [hM] at hgap hφ hσ hom
  simp only [Nat.odd_mul] at hom
  have hoa := hom.1.1.1.1
  have hob := hom.1.1.1.2
  have hoc := hom.1.1.2
  have hod := hom.1.2
  have hoe := hom.2
  have odd_three {x : ℕ} (hx : x.Prime) (ho : Odd x) : 3 ≤ x := by
    have := hx.two_le
    have := Nat.odd_iff.mp ho
    omega
  have hq3 := odd_three hq hoq
  have ha3 := odd_three ha hoa
  have hb3 := odd_three hb hob
  have hc3 := odd_three hc hoc
  have hd3 := odd_three hd hod
  have he3 := odd_three he hoe
  have hab15 := distinct_odd_pair_ge_fifteen ha hb hoa hob hab
  have hac15 := distinct_odd_pair_ge_fifteen ha hc hoa hoc hac
  have had15 := distinct_odd_pair_ge_fifteen ha hd hoa hod had
  have hae15 := distinct_odd_pair_ge_fifteen ha he hoa hoe hae
  have hbc15 := distinct_odd_pair_ge_fifteen hb hc hob hoc hbc
  have hbd15 := distinct_odd_pair_ge_fifteen hb hd hob hod hbd
  have hbe15 := distinct_odd_pair_ge_fifteen hb he hob hoe hbe
  have hcd15 := distinct_odd_pair_ge_fifteen hc hd hoc hod hcd
  have hce15 := distinct_odd_pair_ge_fifteen hc he hoc hoe hce
  have hde15 := distinct_odd_pair_ge_fifteen hd he hod hoe hde
  have ⟨hFn,hKn⟩ := A056777EvenFourFour.square_prime_formulas hp hq hpq
  have ⟨hKm,hFm⟩ := quintic_formulas ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde
  have hpq1 : 1 ≤ p+q := by omega
  have hg : p^2*q ≤ a*b*c*d*e+12 := by
    rcases hgap with h|h
    · rw [← h]
      exact (Nat.le_add_right (p^2*q) 12).trans (Nat.le_add_right (p^2*q+12) 12)
    · rw [h]
  zify [hpq1] at hφ hσ hFn hKn hKm hFm hg hp7 hq3 ha3 hb3 hc3 hd3 he3
  zify at hab15 hac15 had15 hae15 hbc15 hbd15 hbe15 hcd15 hce15 hde15
  have ha0 : (0:ℤ) ≤ a := by positivity
  have hb0 : (0:ℤ) ≤ b := by positivity
  have hc0 : (0:ℤ) ≤ c := by positivity
  have hd0 : (0:ℤ) ≤ d := by positivity
  have he0 : (0:ℤ) ≤ e := by positivity
  let A : ℤ := a+b+c+d+e
  let E : ℤ := a*b+a*c+a*d+a*e+b*c+b*d+b*e+c*d+c*e+d*e
  let X : ℤ := a*b*c+a*b*d+a*b*e+a*c*d+a*c*e+a*d*e+b*c*d+b*c*e+b*d*e+c*d*e
  let Y : ℤ := a*b*c*d+a*b*c*e+a*b*d*e+a*c*d*e+b*c*d*e
  let Z : ℤ := a*b*c*d*e
  obtain ⟨hXA,hAE,hcyc,hNew⟩ :=
    quintic_moment_bounds a b c d e ha3 hb3 hc3 hd3 he3
      hab15 hac15 had15 hae15 hbc15 hbd15 hbe15 hcd15 hce15 hde15
  have hK : 2*(X+A)=(q:ℤ)+2*p+1 := by
    dsimp [X,A]
    nlinarith only [hφ,hσ,hKn,hKm]
  have hF : Y+E+1=X+A+(p:ℤ)*((p:ℤ)+q-1) := by
    dsimp [Y,E,X,A]
    nlinarith only [hφ,hFn,hFm]
  have hYup : 2*Y ≤ 2*(p:ℤ)^2+(2*(p:ℤ)+1)*q+1 := by
    have hAE' : A ≤ E := hAE
    have hA0 : 0 ≤ A := by dsimp [A]; positivity
    nlinarith only [hF,hAE',hK,hA0]
  exact A056777SquarefreeFiveMoments.moments_impossible p q X A Y Z hp7 hq3
    (by dsimp [A]; positivity) (by dsimp [Y]; positivity) (by dsimp [X]; positivity)
    hK hYup (by dsimp [Z]; linarith only [hg]) hcyc hXA hNew

end A056777ThreeSquarefreeFive
end

section
open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777OddSquarefreeThreeFive

private theorem odd_prime_factor {n p : ℕ} (hn : Odd n) (hp : p.Prime)
    (hd : p∣n) : Odd p := by
  rcases hp.eq_two_or_odd' with rfl|h
  · have hm := Nat.odd_iff.mp hn
    omega
  · exact h

private theorem odd_square_mod_four {p : ℕ} (h : Odd p) : p^2%4=1 := by
  have hov := Nat.odd_iff.mp h
  have hres : p%4=1 ∨ p%4=3 := by omega
  rw [Nat.pow_mod]
  rcases hres with h|h <;> rw [h]

private theorem sigma_fifth_not_four_mod_eight {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hφ : (p^5).totient%8=4) : σ 1 (p^5)%8 ≠ 4 := by
  have hd : 4∣(p^5).totient := by omega
  have hφp : (p^5).totient=p^4*(p-1) := Nat.totient_prime_pow_succ hp 4
  rw [hφp] at hd
  have hc := (ho.coprime_two_left.pow_left 2).pow_right 4
  have hp4 : 4∣p-1 := hc.dvd_of_dvd_mul_left hd
  have hp1 : 1 ≤ p := hp.pos
  have hpplus : (p+1)%4=2 := by omega
  have hpp := odd_square_mod_four ho
  have hpiv : p^4%4=1 := by
    rw [show p^4=(p^2)^2 by ring,Nat.pow_mod, hpp]
  have hgeom : (p^4+p^2+1)%4=3 := by omega
  have hs : σ 1 (p^5)=(p+1)*(p^4+p^2+1) := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
    ring
  have hs4 : σ 1 (p^5)%4=2 := by rw [hs,Nat.mul_mod,hpplus,hgeom]
  omega

private theorem odd_bases_mod_four {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hop : Odd p) (hoq : Odd q) (ha : 0<a) (hb : 0<b)
    (hnd : ¬8∣(p^a*q^b).totient) : p%4=3 ∧ q%4=3 := by
  have hoc := (((Nat.coprime_primes hp hq).mpr hne).pow_left a).pow_right b
  have hφ : (p^a*q^b).totient=(p^(a-1)*(p-1))*(q^(b-1)*(q-1)) := by
    rw [Nat.totient_mul hoc,Nat.totient_prime_pow hp ha,Nat.totient_prime_pow hq hb]
  have hp2 := Nat.odd_iff.mp hop
  have hq2 := Nat.odd_iff.mp hoq
  constructor
  · by_contra h
    have h4 : 4∣p-1 := by omega
    have h2 : 2∣q-1 := by omega
    exact hnd (hφ ▸ mul_dvd_mul (dvd_mul_of_dvd_right h4 _) (dvd_mul_of_dvd_right h2 _))
  · by_contra h
    have h2 : 2∣p-1 := by omega
    have h4 : 4∣q-1 := by omega
    exact hnd (hφ ▸ mul_dvd_mul (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h4 _))

private theorem cube_square_sigma_eight {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (h4 : p%4=3)
    (ho : Odd p) : 8∣σ 1 (p^3*q^2) := by
  have hc := (((Nat.coprime_primes hp hq).mpr hne).pow_left 3).pow_right 2
  have h : σ 1 (p^3)=(p+1)*(p^2+1) := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
    ring
  have hpD : 4∣p+1 := by omega
  have hpD' : 2∣p^2+1 := by have := odd_square_mod_four ho; omega
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,h]
  exact dvd_mul_of_dvd_left (mul_dvd_mul hpD hpD') _

private theorem quintic_shape {m : ℕ}
    (hm : Odd m) (hlen : m.primeFactorsList.length=5)
    (hφ : m.totient%8=4) (hσ : σ 1 m%8=4) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p%4=3 ∧ q%8=3 ∧ m=p^4*q := by
  have hm0 : m ≠ 0 := by have := Nat.odd_iff.mp hm; omega
  have hnd : ¬8∣m.totient := by omega
  have hcard : m.primeFactors.card ≤ 2 := by
    by_contra! h
    exact hnd ((pow_dvd_pow 2 h).trans (A056777OddFour.two_pow_card_dvd_totient hm))
  have hpos : 0 < m.primeFactors.card := by
    by_contra! h
    have he : m.primeFactors=∅ := Finset.card_eq_zero.mp (by omega)
    rcases Nat.primeFactors_eq_empty.mp he with rfl|rfl <;> simp at hlen
  have hprod := Nat.prod_factorization_pow_eq_self hm0
  rw [Finsupp.prod,Nat.support_factorization] at hprod
  rcases (show m.primeFactors.card=1 ∨ m.primeFactors.card=2 by omega) with h₁|h₂
  · obtain ⟨p,hpF⟩ := Finset.card_eq_one.mp h₁
    have hmem : p∈m.primeFactors := by simp [hpF]
    have hp := Nat.prime_of_mem_primeFactors hmem
    have hop := odd_prime_factor hm hp (Nat.mem_primeFactors.mp hmem).2.1
    rw [hpF,Finset.prod_singleton] at hprod
    rw [← hprod,hp.primeFactorsList_pow,List.length_replicate] at hlen
    rw [hlen] at hprod
    rw [←hprod] at hφ hσ
    exact (sigma_fifth_not_four_mod_eight hp hop hφ hσ).elim
  · obtain ⟨p,q,hne,hpF⟩ := Finset.card_eq_two.mp h₂
    have hpm : p∈m.primeFactors := by simp [hpF]
    have hqm : q∈m.primeFactors := by simp [hpF]
    have hp := Nat.prime_of_mem_primeFactors hpm
    have hq := Nat.prime_of_mem_primeFactors hqm
    have hop := odd_prime_factor hm hp (Nat.mem_primeFactors.mp hpm).2.1
    have hoq := odd_prime_factor hm hq (Nat.mem_primeFactors.mp hqm).2.1
    let a := m.factorization p
    let b := m.factorization q
    have ha : 0<a := hp.factorization_pos_of_dvd hm0 (Nat.mem_primeFactors.mp hpm).2.1
    have hb : 0<b := hq.factorization_pos_of_dvd hm0 (Nat.mem_primeFactors.mp hqm).2.1
    rw [hpF,Finset.prod_insert (by simpa using hne),Finset.prod_singleton] at hprod
    change p^a*q^b=m at hprod
    have hlen' := (Nat.perm_primeFactorsList_mul (pow_ne_zero a hp.ne_zero)
      (pow_ne_zero b hq.ne_zero)).length_eq
    rw [hprod,hlen,hp.primeFactorsList_pow,hq.primeFactorsList_pow,
      List.length_append,List.length_replicate,List.length_replicate] at hlen'
    have hnd' : ¬8∣(p^a*q^b).totient := by rw [hprod]; exact hnd
    obtain ⟨hp4,hq4⟩ := odd_bases_mod_four hp hq hne hop hoq ha hb hnd'
    have rcase : (a=4 ∧ b=1) ∨ (a=1 ∧ b=4) ∨ (a=3 ∧ b=2) ∨ (a=2 ∧ b=3) := by omega
    have residue_of_four_mul {u v : ℕ} (hu : u.Prime) (hv : v.Prime)
        (hneq : u ≠ v) (hv4 : v%4=3) (he : u^4*v=m) : v%8=3 := by
      have hc := ((Nat.coprime_primes hu hv).mpr hneq).pow_left 4
      have hsigv : σ 1 v=v+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hv
      by_contra hn
      have hvD : 8∣v+1 := by omega
      rw [←he,isMultiplicative_sigma.map_mul_of_coprime hc,hsigv] at hσ
      have hd := dvd_mul_of_dvd_right hvD (σ 1 (u^4))
      omega
    rcases rcase with ⟨ha',hb'⟩ | ⟨ha',hb'⟩ | ⟨ha',hb'⟩ | ⟨ha',hb'⟩ <;>
      rw [ha',hb'] at hprod
    · rw [pow_one] at hprod
      exact ⟨p,q,hp,hq,hne,hp4,residue_of_four_mul hp hq hne hq4 hprod,hprod.symm⟩
    · rw [pow_one,mul_comm] at hprod
      exact ⟨q,p,hq,hp,hne.symm,hq4,residue_of_four_mul hq hp hne.symm hp4 hprod,hprod.symm⟩
    · rw [←hprod] at hσ
      have hd := cube_square_sigma_eight hp hq hne hp4 hop
      omega
    · rw [mul_comm] at hprod
      rw [←hprod] at hσ
      have hd := cube_square_sigma_eight hq hp hne.symm hq4 hoq
      omega

/-- An odd squarefree three-factor endpoint can only be paired with an odd p⁴q
endpoint on the five-factor side. The two jump equalities impose the displayed
residues on the repeated prime and the other prime. -/
theorem remaining_odd_squarefree_three_five {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (ho : Odd n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p%4=3 ∧ q%8=3 ∧ m=p^4*q := by
  have hom : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
  have hncard : 3 ≤ n.primeFactors.card := by
    rw [← Nat.toFinset_factors,List.toFinset_card_of_nodup hs.nodup_primeFactorsList,hn]
  have hdφ : 8∣n.totient := (pow_dvd_pow 2 hncard).trans
    (A056777OddFour.two_pow_card_dvd_totient ho)
  have hfilt : (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p))=n.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have ⟨hpp,hpd,hzero⟩ := Nat.mem_primeFactors.mp hp
    have ho' := odd_prime_factor ho hpp hpd
    have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬Odd 2) ho'
    have hpos := hpp.factorization_pos_of_dvd hzero hpd
    have hle := hs.natFactorization_le_one p
    have h1 : n.factorization p=1 := by omega
    exact ⟨hp2,h1 ▸ (by decide : Odd 1)⟩
  have hd := A056777Squarefree.two_pow_card_odd_exponents_dvd_sigma hs.ne_zero
  rw [hfilt] at hd
  have hdσ : 8∣σ 1 n := (pow_dvd_pow 2 hncard).trans hd
  exact quintic_shape hom hm (by omega) (by omega)

end A056777OddSquarefreeThreeFive
end

section
open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777OddSquarefreeThreeFive

private theorem squarefree_triple_shape {n : ℕ}
    (hn : n.primeFactorsList.length=3) (hs : Squarefree n) :
    ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ n=a*b*c := by
  obtain ⟨a,b,c,he⟩ : ∃ a b c, n.primeFactorsList = [a,b,c] := by
    generalize hl : n.primeFactorsList = l at hn ⊢
    rcases l with _ | ⟨a,l⟩
    · simp at hn
    rcases l with _ | ⟨b,l⟩
    · simp at hn
    rcases l with _ | ⟨c,l⟩
    · simp at hn
    rcases l with _ | ⟨d,l⟩
    · exact ⟨a,b,c,rfl⟩
    · simp at hn
  have ha := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=a) (by simp [he])
  have hb := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=b) (by simp [he])
  have hc := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=c) (by simp [he])
  have hnd := hs.nodup_primeFactorsList
  simp only [he,List.nodup_cons,List.mem_cons,not_or,List.not_mem_nil,not_false_eq_true,
    List.nodup_nil,and_true] at hnd
  exact ⟨a,b,c,ha,hb,hc,hnd.1.1,hnd.1.2,hnd.2,
    by simpa [he,mul_assoc] using (Nat.prod_primeFactorsList hs.ne_zero).symm⟩

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p=p+1 := by
  simpa using sigma_one_apply_prime_pow (i:=1) hp

private theorem triple_formulas {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a*b*c).totient+(a*b+a*c+b*c)+1=a*b*c+(a+b+c) ∧
      σ 1 (a*b*c)+(a*b*c).totient=2*(a*b*c)+2*(a+b+c) := by
  have h₁ := (Nat.coprime_primes ha hb).mpr hab
  have h₂ := ((Nat.coprime_primes ha hc).mpr hac).mul_left ((Nat.coprime_primes hb hc).mpr hbc)
  rw [Nat.totient_mul h₂,Nat.totient_mul h₁,Nat.totient_prime ha,Nat.totient_prime hb,
    Nat.totient_prime hc,isMultiplicative_sigma.map_mul_of_coprime h₂,
    isMultiplicative_sigma.map_mul_of_coprime h₁,sigma_prime ha,sigma_prime hb,sigma_prime hc]
  have ha1 := ha.pos
  have hb1 := hb.pos
  have hc1 := hc.pos
  zify [ha1,hb1,hc1]
  constructor <;> ring

private theorem fourth_times_prime_formulas {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) :
    (p^4*q).totient+p^3*(p+q-1)=p^4*q ∧
      σ 1 (p^4*q)+(p^4*q).totient=2*(p^4*q)+(p^2+p+1)*(q+1)+2*p^3 := by
  have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 4
  have hsig : σ 1 (p^4)=1+p+p^2+p^3+p^4 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  rw [Nat.totient_mul hc,show (p^4).totient=p^3*(p-1) from Nat.totient_prime_pow_succ hp 3,
    Nat.totient_prime hq,isMultiplicative_sigma.map_mul_of_coprime hc,hsig,sigma_prime hq]
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hpq1 : 1 ≤ p+q := by omega
  zify [hp1,hq1,hpq1]
  constructor <;> ring

private def twiceSum (p q : ℤ) : ℤ := (p^2+p+1)*(q+1)+2*p^3
private def twicePairSum (p q : ℤ) : ℤ := 2*p^3*(p+q-1)+twiceSum p q-2

private def scaledDiscriminant (p q D : ℤ) : ℤ :=
  let L := twiceSum p q
  let M := twicePairSum p q
  let Z := p^4*q+D
  16*L^2*M^2-128*M^3-128*L^3*Z-6912*Z^2+1152*L*M*Z

private theorem negative_cubic_plus (p q : ℤ) (hp : 4 ≤ p) (hq : p ≤ 2*q) :
    scaledDiscriminant p q (12) < 0 := by
  let U := p-4
  let V := 2*q-p
  have hU : 0 ≤ U := by dsimp [U]; omega
  have hV : 0 ≤ V := by dsimp [V]; omega
  let c0 : ℤ := 45450586608+U*(151269655936+U*(237320663240+U*(231465309744+U*(156079495591+U*(76680177212+U*(28220821398+U*(7886565180+U*(1679079177+U*(270726024+U*(32515910+U*(2819452+U*(166767+U*(6020+U*(100))))))))))))))
  let c1 : ℤ := 58430090880+U*(186815798768+U*(275986987392+U*(249166894932+U*(153250173200+U*(67766232432+U*(22154623152+U*(5420113236+U*(992076744+U*(134155248+U*(13025848+U*(859860+U*(34584+U*(640)))))))))))))
  let c2 : ℤ := 8711949896+U*(25465819824+U*(34106887762+U*(27658865496+U*(15119219492+U*(5867108552+U*(1656955142+U*(343082072+U*(51683492+U*(5523792+U*(397538+U*(17296+U*(344))))))))))))
  let c3 : ℤ := 476170592+U*(1250465508+U*(1491138928+U*(1065569808+U*(506973776+U*(168622804+U*(40009560+U*(6772528+U*(801544+U*(63172+U*(2984+U*(64)))))))))))
  let c4 : ℤ := 9175887+U*(21161196+U*(21952614+U*(13495932+U*(5446985+U*(1508544+U*(290422+U*(38388+U*(3335+U*(172+U*(4))))))))))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4)))) := by dsimp [c0, c1, c2, c3, c4]; positivity
  have he : -scaledDiscriminant p q (12) = c0+V*(c1+V*(c2+V*(c3+V*(c4)))) := by
    dsimp [scaledDiscriminant, twiceSum, twicePairSum, U, V, c0, c1, c2, c3, c4]
    ring
  rw [←he] at hpos
  exact neg_pos.mp hpos

private theorem negative_cubic_minus (p q : ℤ) (hp : 4 ≤ p) (hq : p ≤ 2*q) :
    scaledDiscriminant p q (-12) < 0 := by
  let U := p-4
  let V := 2*q-p
  have hU : 0 ≤ U := by dsimp [U]; omega
  have hV : 0 ≤ V := by dsimp [V]; omega
  let c0 : ℤ := 28253174256+U*(113486935936+U*(200507752136+U*(210590123952+U*(148488609319+U*(74845082684+U*(27925988886+U*(7856221500+U*(1677264777+U*(270678024+U*(32515910+U*(2819452+U*(166767+U*(6020+U*(100))))))))))))))
  let c1 : ℤ := 55491509376+U*(181214714864+U*(271321109760+U*(246949079508+U*(152592613904+U*(67641780720+U*(22139948976+U*(5419128276+U*(992047944+U*(134155248+U*(13025848+U*(859860+U*(34584+U*(640)))))))))))))
  let c2 : ℤ := 8539509320+U*(25188341040+U*(33915677650+U*(27585708888+U*(15102436004+U*(5864799944+U*(1656778886+U*(343076312+U*(51683492+U*(5523792+U*(397538+U*(17296+U*(344))))))))))))
  let c3 : ℤ := 472614368+U*(1245893220+U*(1488671344+U*(1064854416+U*(506856272+U*(168612436+U*(40009176+U*(6772528+U*(801544+U*(63172+U*(2984+U*(64)))))))))))
  let c4 : ℤ := 9175887+U*(21161196+U*(21952614+U*(13495932+U*(5446985+U*(1508544+U*(290422+U*(38388+U*(3335+U*(172+U*(4))))))))))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4)))) := by dsimp [c0, c1, c2, c3, c4]; positivity
  have he : -scaledDiscriminant p q (-12) = c0+V*(c1+V*(c2+V*(c3+V*(c4)))) := by
    dsimp [scaledDiscriminant, twiceSum, twicePairSum, U, V, c0, c1, c2, c3, c4]
    ring
  rw [←he] at hpos
  exact neg_pos.mp hpos

private theorem discriminant_nonnegative (p q a b c D : ℤ)
    (hL : 2*(a+b+c)=twiceSum p q) (hM : 2*(a*b+a*c+b*c)=twicePairSum p q)
    (hZ : a*b*c=p^4*q+D) :
    0 ≤ scaledDiscriminant p q D := by
  unfold scaledDiscriminant
  dsimp only
  rw [←hL,←hM,←hZ]
  have he :
      16*(2*(a+b+c))^2*(2*(a*b+a*c+b*c))^2-128*(2*(a*b+a*c+b*c))^3-
      128*(2*(a+b+c))^3*(a*b*c)-6912*(a*b*c)^2+
      1152*(2*(a+b+c))*(2*(a*b+a*c+b*c))*(a*b*c) =
      256*(a-b)^2*(a-c)^2*(b-c)^2 := by ring
  rw [he]
  positivity

private theorem second_newton (a b c : ℤ) :
    3*(a+b+c)*(a*b*c) ≤ (a*b+a*c+b*c)^2 := by
  nlinarith only [sq_nonneg (a*b-a*c),sq_nonneg (a*b-b*c),sq_nonneg (a*c-b*c)]

private theorem no_repeated_base_three (q a b c D : ℤ)
    (hq : 11 ≤ q) (hD : D=12∨D=-12)
    (hL : 2*(a+b+c)=twiceSum 3 q) (hM : 2*(a*b+a*c+b*c)=twicePairSum 3 q)
    (hZ : a*b*c=3^4*q+D) : False := by
  have hn := second_newton a b c
  have hmargin : 0 < 4*(3*(a+b+c)*(a*b*c)-(a*b+a*c+b*c)^2) := by
    have hq2 : 121 ≤ q^2 := by
      have h := mul_nonneg (show 0 ≤ q-11 by omega) (show 0 ≤ q+11 by omega)
      nlinarith only [h]
    have hL' := congrArg (fun x : ℤ => (3^4*q+D)*x) hL
    have hM' := congrArg (fun x : ℤ => x^2) hM
    have he : 4*(3*(a+b+c)*(a*b*c)-(a*b+a*c+b*c)^2) =
        6*twiceSum 3 q*(3^4*q+D)-(twicePairSum 3 q)^2 := by
      rw [hZ]
      linear_combination 6*hL'-hM'
    rw [he]
    dsimp [twicePairSum,twiceSum]
    rcases hD with rfl|rfl <;> nlinarith only [hq,hq2]
  nlinarith only [hn,hmargin]

private theorem no_unrepeated_base_three {p a b c : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hc : c.Prime) (hp : 3 ≤ p)
    (hgap : p^4*3+12=a*b*c ∨ a*b*c+12=p^4*3)
    (hL : 2*(a+b+c)=(p^2+p+1)*(3+1)+2*p^3)
    (hM : a*b+a*c+b*c+1=p^3*(p+3-1)+(a+b+c)) : False := by
  have hdiv : 3∣a*b*c := by omega
  simp only [Nat.prime_three.dvd_mul] at hdiv
  have hex {x : ℕ} (hx : x.Prime) (hh : 3∣x) : x=3 := by
    rcases (Nat.dvd_prime hx).mp hh with h|h
    · omega
    · exact h.symm
  have hP : 1 ≤ p+3 := by omega
  have hp2 : 9 ≤ p^2 := Nat.pow_le_pow_left hp 2
  rcases hdiv with (h|h)|h
  · obtain rfl := hex ha h
    zify [hP] at hgap hL hM hp hp2
    rcases hgap with hg|hg <;> nlinarith only [hg,hL,hM,hp,hp2]
  · obtain rfl := hex hb h
    zify [hP] at hgap hL hM hp hp2
    rcases hgap with hg|hg <;> nlinarith only [hg,hL,hM,hp,hp2]
  · obtain rfl := hex hc h
    zify [hP] at hgap hL hM hp hp2
    rcases hgap with hg|hg <;> nlinarith only [hg,hL,hM,hp,hp2]

/-- In addition to its forced p⁴q shape, the quintic endpoint must have q ≥ 11
and the repeated prime strictly larger than 2q. -/
theorem narrowed_odd_squarefree_three_five {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (ho : Odd n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p%4=3 ∧ q%8=3 ∧
      11 ≤ q ∧ 2*q<p ∧ m=p^4*q := by
  obtain ⟨p,q,hp,hq,hpq,hp4,hq8,hm'⟩ :=
    remaining_odd_squarefree_three_five hn hm hs ho hgap hφ hσ
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,hn'⟩ := squarefree_triple_shape hn hs
  rw [hn',hm'] at hgap hφ hσ
  have hgap' : p^4*q+12=a*b*c ∨ a*b*c+12=p^4*q := hgap.symm
  have ⟨hF,hK⟩ := fourth_times_prime_formulas hp hq hpq
  have ⟨hF',hK'⟩ := triple_formulas ha hb hc hab hac hbc
  have hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 := by omega
  have hM : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c) := by omega
  have hp3 : 3 ≤ p := by omega
  have hq3 : q ≠ 3 := by
    rintro rfl
    exact no_unrepeated_base_three ha hb hc hp3 hgap' hL hM
  have hq11 : 11 ≤ q := by omega
  let D : ℤ := (a:ℤ)*b*c-(p:ℤ)^4*q
  have hD : D=12∨D=-12 := by zify at hgap'; dsimp [D]; omega
  have hpq1 : 1 ≤ p+q := by omega
  zify [hpq1] at hL hM
  have hL' : 2*((a:ℤ)+b+c)=twiceSum p q := hL
  have hM' : 2*((a:ℤ)*b+(a:ℤ)*c+(b:ℤ)*c)=twicePairSum p q := by
    dsimp [twicePairSum,twiceSum]
    linarith only [hL,hM]
  have hZ : (a:ℤ)*b*c=(p:ℤ)^4*q+D := by dsimp [D]; ring
  have hp' : p ≠ 3 := by
    rintro rfl
    exact no_repeated_base_three q a b c D (by exact_mod_cast hq11) hD hL' hM' hZ
  have hpZ : (4:ℤ) ≤ p := by
    exact_mod_cast (show 4 ≤ p by omega)
  have hqP : 2*q<p := by
    by_contra! h
    have hqZ : (p:ℤ) ≤ 2*q := by exact_mod_cast h
    have hnn := discriminant_nonnegative p q a b c D hL' hM' hZ
    rcases hD with hd|hd
    · rw [hd] at hnn
      exact (not_lt_of_ge hnn) (negative_cubic_plus p q hpZ hqZ)
    · rw [hd] at hnn
      exact (not_lt_of_ge hnn) (negative_cubic_minus p q hpZ hqZ)
  exact ⟨p,q,hp,hq,hpq,hp4,hq8,hq11,hqP,hm'⟩

private theorem zmod_three_moments :
    ∀ p q a b c : ZMod 3, p ≠ 0 → q ≠ 0 →
      2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 → a*b*c=p^4*q → p ≠ q := by
  decide

/-- The two prime bases in the remaining p⁴q case also have different
residues modulo three. -/
theorem narrowed_odd_squarefree_three_five_mod_three {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (ho : Odd n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p%4=3 ∧ q%8=3 ∧
      11 ≤ q ∧ 2*q<p ∧ p%3 ≠ q%3 ∧ m=p^4*q := by
  obtain ⟨p,q,hp,hq,hpq,hp4,hq8,hq11,h2qp,hm'⟩ :=
    narrowed_odd_squarefree_three_five hn hm hs ho hgap hφ hσ
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,hn'⟩ := squarefree_triple_shape hn hs
  rw [hn',hm'] at hgap hφ hσ
  have hK := (fourth_times_prime_formulas hp hq hpq).2
  have hK' := (triple_formulas ha hb hc hab hac hbc).2
  have hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 := by omega
  have hL' := congrArg (fun x : ℕ => (x : ZMod 3)) hL
  push_cast at hL'
  have hZ : (a : ZMod 3)*b*c=(p : ZMod 3)^4*q := by
    have hz : (12 : ZMod 3)=0 := by decide
    rcases hgap with h|h
    · have H := congrArg (fun x : ℕ => (x : ZMod 3)) h
      push_cast at H
      simpa only [hz,add_zero] using H
    · have H := congrArg (fun x : ℕ => (x : ZMod 3)) h
      push_cast at H
      simpa only [hz,add_zero] using H.symm
  have hnonzero {x : ℕ} (hx : x.Prime) (hx' : 3<x) : (x : ZMod 3) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff x 3).mp h
    rcases (Nat.dvd_prime hx).mp hd with hd | hd <;> omega
  have hnon := zmod_three_moments p q a b c (hnonzero hp (by omega))
    (hnonzero hq (by omega)) hL' hZ
  have hmod : p%3 ≠ q%3 := by
    intro h
    apply hnon
    rw [←ZMod.natCast_mod p 3,←ZMod.natCast_mod q 3,h]
  exact ⟨p,q,hp,hq,hpq,hp4,hq8,hq11,h2qp,hmod,hm'⟩

private theorem five_cubic_negative (p q D : ℤ) (hp : 23 ≤ p) (hq : 11 ≤ q) (hD : -12 ≤ D) :
    250-25*twiceSum p q+5*twicePairSum p q-2*(p^4*q+D) < 0 := by
  let U := p-23
  let V := q-11
  let W := D+12
  have hU : 0 ≤ U := by dsimp [U]; omega
  have hV : 0 ≤ V := by dsimp [V]; omega
  have hW : 0 ≤ W := by dsimp [W]; omega
  let P := 2*U^4*V+12*U^4+174*U^3*V+1044*U^3+5678*U^2*V+34188*U^2+
    82406*U*V+500076*U+449072*V+2760528+2*W
  have hpos : 0<P := by dsimp [P]; positivity
  have he : -(250-25*twiceSum p q+5*twicePairSum p q-2*(p^4*q+D))=P := by
    dsimp [twiceSum,twicePairSum,P,U,V,W]
    ring
  rw [←he] at hpos
  exact neg_pos.mp hpos

private theorem triple_root_not_five (p q a b c D : ℤ)
    (hp : 23 ≤ p) (hq : 11 ≤ q) (hD : -12 ≤ D)
    (hL : 2*(a+b+c)=twiceSum p q) (hM : 2*(a*b+a*c+b*c)=twicePairSum p q)
    (hZ : a*b*c=p^4*q+D) : a ≠ 5 ∧ b ≠ 5 ∧ c ≠ 5 := by
  have he : 250-25*twiceSum p q+5*twicePairSum p q-2*(p^4*q+D) =
      2*(5-a)*(5-b)*(5-c) := by
    rw [←hL,←hM,←hZ]
    ring
  have hneg := five_cubic_negative p q D hp hq hD
  rw [he] at hneg
  refine ⟨?_,?_,?_⟩
  all_goals
    intro h
    rw [h] at hneg
    norm_num at hneg

set_option maxHeartbeats 2000000 in
private theorem zmod_five_minus :
    ∀ p q a b c : ZMod 5, p ≠ 0 → q ≠ 0 → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 →
      2*(a*b+a*c+b*c)=2*p^3*(p+q-1)+((p^2+p+1)*(q+1)+2*p^3)-2 →
      a*b*c=p^4*q-12 → False := by
  decide

set_option maxHeartbeats 2000000 in
private theorem zmod_five_plus :
    ∀ p q a b c : ZMod 5, p ≠ 0 → q ≠ 0 → a ≠ 0 → b ≠ 0 → c ≠ 0 →
      2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 →
      2*(a*b+a*c+b*c)=2*p^3*(p+q-1)+((p^2+p+1)*(q+1)+2*p^3)-2 →
      a*b*c=p^4*q+12 → (p=2 ∨ p=3) ∧ q=2 := by
  decide

private theorem cubic_gap_bound (p q a b c : ℤ) (hp : 2*q<p) (hq : 11 ≤ q)
    (hqa : q+1 ≠ a) (hqb : q+1 ≠ b) (hqc : q+1 ≠ c)
    (hL : 2*(a+b+c)=twiceSum p q) (hM : 2*(a*b+a*c+b*c)=twicePairSum p q)
    (hZ : a*b*c=p^4*q+12) : p^2<q^3 := by
  by_contra! hpow
  have hp23 : 23 ≤ p := by omega
  let f (x : ℤ) := 2*x^3-twiceSum p q*x^2+twicePairSum p q*x-2*(p^4*q+12)
  have hfac (x : ℤ) : f x=2*(x-a)*(x-b)*(x-c) := by
    dsimp [f]
    rw [←hL,←hM,←hZ]
    ring
  have hneg : f q<0 := by
    have he : f q= -(p^2+p-1)*(q^3-q)-24 := by dsimp [f,twiceSum,twicePairSum]; ring
    rw [he]
    have hprod := mul_nonneg (show 0 ≤ p^2+p-1 by nlinarith [sq_nonneg p]) (show 0 ≤ q^3-q by
      nlinarith [sq_nonneg q, mul_nonneg (show 0 ≤ q by omega) (show 0 ≤ q^2-1 by nlinarith)])
    linarith
  have hpos : 0<f (q+2) := by
    have he : f (q+2)=4*p^3*(p-q-2)-(p^2+p)*(q^3+4*q^2+5*q+2)+
        (q^3+8*q^2+17*q-14) := by dsimp [f,twiceSum,twicePairSum]; ring
    rw [he]
    have h₁ := mul_le_mul_of_nonneg_left (show 5*p ≤ 12*(p-q-2) by omega)
      (show 0 ≤ p^3 by positivity)
    have h₂ : 2*(q^3+4*q^2+5*q+2) ≤ 3*q^3 := by
      have hh := mul_nonneg (show 0 ≤ q-11 by omega) (show 0 ≤ q^2 by positivity)
      nlinarith [sq_nonneg (q-5)]
    have h₃ := mul_le_mul_of_nonneg_left (h₂.trans (mul_le_mul_of_nonneg_left hpow (by decide)))
      (show 0 ≤ p^2+p by positivity)
    have h₄ := mul_le_mul_of_nonneg_right (show 12*(p^2+p) ≤ 13*p^2 by
      nlinarith [mul_nonneg (show 0 ≤ p by omega) (show 0 ≤ p-12 by omega)])
      (show 0 ≤ 3*p^2 by positivity)
    have h₅ : 0<p^4 := by positivity
    have h₆ : 0 ≤ q^3+8*q^2+17*q-14 := by
      have : 0 ≤ q^3 := by positivity
      nlinarith
    nlinarith only [h₁,h₃,h₄,h₅,h₆]
  let s (x y : ℤ) : ℤ := if x<y then -1 else 1
  have hs0 (x y : ℤ) (hxy : x ≠ y) : 0<s x y*(x-y) := by
    unfold s
    split <;> omega
  have hs1 (y : ℤ) (hy : q ≠ y) (hy' : q+1 ≠ y) (hy'' : q+2 ≠ y) :
      s q y=s (q+2) y := by
    unfold s
    by_cases h : q<y
    · have h' : q+2<y := by omega
      simp [h,h']
    · have h' : ¬q+2<y := by omega
      simp [h,h']
  rw [hfac] at hneg hpos
  have hn₁ : q ≠ a ∧ q ≠ b ∧ q ≠ c := by
    refine ⟨?_,?_,?_⟩ <;> intro h <;> rw [←h] at hneg <;> norm_num at hneg
  have hn₂ : q+2 ≠ a ∧ q+2 ≠ b ∧ q+2 ≠ c := by
    refine ⟨?_,?_,?_⟩ <;> intro h <;> rw [←h] at hpos <;> norm_num at hpos
  have t₁ := mul_pos (mul_pos (hs0 q a hn₁.1) (hs0 q b hn₁.2.1)) (hs0 q c hn₁.2.2)
  have t₂ := mul_pos (mul_pos (hs0 (q+2) a hn₂.1) (hs0 (q+2) b hn₂.2.1))
    (hs0 (q+2) c hn₂.2.2)
  rw [←hs1 a hn₁.1 hqa hn₂.1,←hs1 b hn₁.2.1 hqb hn₂.2.1,←hs1 c hn₁.2.2 hqc hn₂.2.2] at t₂
  have e (x : ℤ) : (s q a*(x-a))*(s q b*(x-b))*(s q c*(x-c)) =
      (s q a*s q b*s q c)*((x-a)*(x-b)*(x-c)) := by ring
  rw [e] at t₁ t₂
  have hz₁ : (q-a)*(q-b)*(q-c)<0 := by linarith
  have hz₂ : 0<(q+2-a)*(q+2-b)*(q+2-c) := by linarith
  have hv := pos_of_mul_pos_left t₂ hz₂.le
  have := mul_neg_of_pos_of_neg hv hz₁
  exact (not_lt_of_ge t₁.le this)

set_option maxHeartbeats 1200000 in
/-- The squarefree triple can only be the larger endpoint in the remaining odd
p⁴q case. The two prime bases also satisfy the displayed residues modulo five. -/
theorem odd_squarefree_three_five_orientation_mod_five {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (ho : Odd n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    m+12=n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
      p%4=3 ∧ q%8=3 ∧ 11 ≤ q ∧ 2*q<p ∧ p%3 ≠ q%3 ∧ p^2<q^3 ∧
      (p%5=2 ∨ p%5=3) ∧ q%5=2 ∧ m=p^4*q := by
  obtain ⟨p,q,hp,hq,hpq,hp4,hq8,hq11,h2q,hpq3,hm'⟩ :=
    narrowed_odd_squarefree_three_five_mod_three hn hm hs ho hgap hφ hσ
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc,hn'⟩ := squarefree_triple_shape hn hs
  have hg := hgap
  rw [hn',hm'] at hg hφ hσ
  have ⟨hF,hK⟩ := fourth_times_prime_formulas hp hq hpq
  have ⟨hF',hK'⟩ := triple_formulas ha hb hc hab hac hbc
  have hL : 2*(a+b+c)=(p^2+p+1)*(q+1)+2*p^3 := by omega
  have hP : a*b+a*c+b*c+1=p^3*(p+q-1)+(a+b+c) := by omega
  have hpq1 : 1 ≤ p+q := by omega
  let D : ℤ := (a:ℤ)*b*c-(p:ℤ)^4*q
  have hD : -12 ≤ D := by
    zify at hg
    dsimp [D]
    omega
  have hz : (a:ℤ)*b*c=(p:ℤ)^4*q+D := by dsimp [D]; ring
  have hp23 : (23:ℤ) ≤ p := by exact_mod_cast (show 23 ≤ p by omega)
  have hq11' : (11:ℤ) ≤ q := by exact_mod_cast hq11
  have hLZ := hL
  have hPZ := hP
  zify [hpq1] at hLZ hPZ
  have hMZ : 2*((a:ℤ)*b+(a:ℤ)*c+(b:ℤ)*c)=twicePairSum p q := by
    dsimp [twicePairSum,twiceSum]
    linarith only [hLZ,hPZ]
  obtain ⟨ha5,hb5,hc5⟩ := triple_root_not_five p q a b c D hp23 hq11' hD hLZ hMZ hz
  have nozero {x : ℕ} (hx : x.Prime) (hx5 : x ≠ 5) : (x:ZMod 5) ≠ 0 := by
    intro he
    have hd := (ZMod.natCast_eq_zero_iff x 5).mp he
    rcases (Nat.dvd_prime hx).mp hd with hd|hd <;> omega
  have hp0 := nozero hp (by omega)
  have hq0 := nozero hq (by omega)
  have ha0 := nozero ha (fun h => ha5 (by exact_mod_cast h))
  have hb0 := nozero hb (fun h => hb5 (by exact_mod_cast h))
  have hc0 := nozero hc (fun h => hc5 (by exact_mod_cast h))
  have hL5 := congrArg (fun x : ℕ => (x : ZMod 5)) hL
  push_cast at hL5
  have hM5 := congrArg (fun x : ℤ => (x : ZMod 5)) hMZ
  simp only [twicePairSum,twiceSum] at hM5
  push_cast at hM5
  rcases hgap with h|h
  · have hg' : a*b*c+12=p^4*q := by simpa only [hn',hm'] using h
    have H := congrArg (fun x : ℕ => (x:ZMod 5)) hg'
    push_cast at H
    have hZ5 : (a:ZMod 5)*b*c=(p:ZMod 5)^4*q-12 := eq_sub_of_add_eq H
    exact (zmod_five_minus p q a b c hp0 hq0 ha0 hb0 hc0 hL5 hM5 hZ5).elim
  · have hg' : p^4*q+12=a*b*c := by simpa only [hn',hm'] using h
    have H := congrArg (fun x : ℕ => (x:ZMod 5)) hg'
    push_cast at H
    have hpqZ := zmod_five_plus p q a b c hp0 hq0 ha0 hb0 hc0 hL5 hM5 H.symm
    have htwo : (2:ZMod 5).val=2 := by decide
    have hthree : (3:ZMod 5).val=3 := by decide
    have hq5 : q%5=2 := by
      have hv := congrArg ZMod.val hpqZ.2
      simpa only [ZMod.val_natCast,htwo,hthree] using hv
    have hp5 : p%5=2 ∨ p%5=3 := by
      rcases hpqZ.1 with h|h
      · left
        have hv := congrArg ZMod.val h
        simpa only [ZMod.val_natCast,htwo,hthree] using hv
      · right
        have hv := congrArg ZMod.val h
        simpa only [ZMod.val_natCast,htwo,hthree] using hv
    have rootne {x : ℕ} (hx : x∣n) : (q:ℤ)+1 ≠ x := by
      obtain ⟨y,hy⟩ := hx
      intro heq
      have heq' : q+1=x := by exact_mod_cast heq
      have hxodd := Nat.odd_iff.mp (Nat.odd_mul.mp (hy ▸ ho)).1
      omega
    have hda : a∣n := by rw [hn']; exact ⟨b*c, by ring⟩
    have hdb : b∣n := by rw [hn']; exact ⟨a*c, by ring⟩
    have hdc : c∣n := by rw [hn']; exact ⟨a*b, by ring⟩
    have hzplus : (a:ℤ)*b*c=(p:ℤ)^4*q+12 := by exact_mod_cast hg'.symm
    have hbound := cubic_gap_bound p q a b c (by exact_mod_cast h2q) hq11'
      (rootne hda) (rootne hdb) (rootne hdc) hLZ hMZ hzplus
    exact ⟨h,p,q,hp,hq,hpq,hp4,hq8,hq11,h2q,hpq3,by exact_mod_cast hbound,hp5,hq5,hm'⟩

end A056777OddSquarefreeThreeFive
end

section
open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777EvenSquarefreeThreeFive

private theorem cube_excess {p : ℕ} (hp : p.Prime) :
    σ 1 (p^3)+(p^3).totient=2*p^3+p+1 := by
  have hsigma : σ 1 (p^3)=1+p+p^2+p^3 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  rw [hsigma,show (p^3).totient=p^2*(p-1) from Nat.totient_prime_pow_succ hp 2]
  have hp1 := hp.pos
  zify [hp1]
  ring

private theorem mul_prime_excess_lower {a p k : ℕ} (ha : a ≠ 0) (hp : p.Prime)
    (hc : a.Coprime p) (h : 2*a+k ≤ σ 1 a+a.totient) :
    2*(a*p)+p*k ≤ σ 1 (a*p)+(a*p).totient := by
  have hsigma : a ≤ σ 1 a := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (f:=id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨by simp,ha⟩)
  have hφ := Nat.totient_le a
  have hsigmap : σ 1 p=p+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hp
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,hsigmap,Nat.totient_mul hc,Nat.totient_prime hp]
  have hp1 := hp.pos
  have hh := Nat.mul_le_mul_left p h
  zify [hp1] at hh hsigma hφ ⊢
  nlinarith only [hh,hsigma,hφ]

private theorem odd_core_excess_not_six_or_negative {m : ℕ} (ho : Odd m)
    (hm : m.primeFactorsList.length=4) :
    ¬(σ 1 m+m.totient=2*m+6 ∨ σ 1 m+m.totient+2=2*m) := by
  intro he
  rcases A056777CubeFour.four_factor_shape hm with ⟨k,hk⟩ | ⟨p,q,hp,hq,hpq,rfl⟩ |
    ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,rfl⟩ | ⟨p,q,r,s,hp,hq,hr,hs,hpq,hpr,hps,hqr,hqs,hrs,rfl⟩
  · have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have hlarge : 2 < m := by
      by_contra! h
      interval_cases m <;> simp at hm
    have hsigma := Nat.odd_iff.mp ((A056777Parity.odd_sigma_iff_square_or_twice_square hm0).mpr
      (Or.inl ⟨k,hk⟩))
    have hφ := Nat.even_iff.mp (Nat.totient_even hlarge)
    omega
  · have hqodd := (Nat.odd_mul.mp ho).2
    have hq3 : 3 ≤ q := by have := hq.two_le; have := Nat.odd_iff.mp hqodd; omega
    have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 3
    have hk : 2*p^3+(p+1) ≤ σ 1 (p^3)+(p^3).totient := by have hh := cube_excess hp; omega
    have h := mul_prime_excess_lower (pow_ne_zero _ hp.ne_zero) hq hc hk
    have hp2 := hp.two_le
    have hmul : 9 ≤ q*(p+1) := Nat.mul_le_mul hq3 (by omega : 3 ≤ p+1)
    omega
  · have hc := (((Nat.coprime_primes hp hr).mpr hpr).pow_left 2).mul_left
      ((Nat.coprime_primes hq hr).mpr hqr)
    have hb := (A056777EvenFourFour.square_prime_formulas hp hq hpq).2
    have hk : 2*(p^2*q)+(q+2*p+1) ≤ σ 1 (p^2*q)+(p^2*q).totient := by omega
    have hh := mul_prime_excess_lower (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero) hr hc hk
    have hp2 := hp.two_le
    have hq2 := hq.two_le
    have hmul : 14 ≤ r*(q+2*p+1) := Nat.mul_le_mul hr.two_le (by omega : 7 ≤ q+2*p+1)
    omega
  · have hc₁ := (Nat.coprime_primes hp hq).mpr hpq
    have hc₂ := ((Nat.coprime_primes hp hr).mpr hpr).mul_left ((Nat.coprime_primes hq hr).mpr hqr)
    have hc₃ := (((Nat.coprime_primes hp hs).mpr hps).mul_left
      ((Nat.coprime_primes hq hs).mpr hqs)).mul_left ((Nat.coprime_primes hr hs).mpr hrs)
    have hfree : Squarefree (p*q*r*s) := Nat.squarefree_mul_iff.mpr ⟨hc₃,Nat.squarefree_mul_iff.mpr
      ⟨hc₂,Nat.squarefree_mul_iff.mpr ⟨hc₁,hp.squarefree,hq.squarefree⟩,hr.squarefree⟩,hs.squarefree⟩
    have h := A056777Closure.low_excess_of_odd_squarefree (p*q*r*s) ho hfree
    omega

private theorem length_mul_two {n : ℕ} (hn : n ≠ 0) :
    (2*n).primeFactorsList.length=1+n.primeFactorsList.length := by
  have hh := (Nat.perm_primeFactorsList_mul (by decide : (2:ℕ) ≠ 0) hn).length_eq
  rwa [Nat.primeFactorsList_two,List.length_append,List.length_singleton] at hh

/-- An even squarefree three-factor endpoint has no five-factor partner in either orientation. -/
theorem no_even_squarefree_three_five_pair {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (he : Even n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) : False := by
  have hnd : ¬4∣n := Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two
  have hme : Even m := Nat.even_iff.mpr (by have := Nat.even_iff.mp he; omega)
  obtain ⟨a,ha⟩ := he
  obtain ⟨b,hb⟩ := hme
  have hna : n=2*a := by omega
  have hmb : m=2*b := by omega
  have hoa : Odd a := Nat.odd_iff.mpr (by omega)
  have hob : Odd b := Nat.odd_iff.mpr (by omega)
  have ha0 : a ≠ 0 := by have := Nat.odd_iff.mp hoa; omega
  have hb0 : b ≠ 0 := by have := Nat.odd_iff.mp hob; omega
  have hal : a.primeFactorsList.length=2 := by rw [hna,length_mul_two ha0] at hn; omega
  have hbl : b.primeFactorsList.length=4 := by rw [hmb,length_mul_two hb0] at hm; omega
  have hsf' : Squarefree (2*a) := hna ▸ hs
  have hsa := hsf'.squarefree_of_dvd (dvd_mul_left a 2)
  have ha1 : 1<a := by
    by_contra! h
    interval_cases a <;> simp at hal
  have hap : ¬a.Prime := by intro h; simp [Nat.primeFactorsList_prime h] at hal
  have hsem : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ a=p*q := by
    by_contra h
    have hh := A056777Closure.factor_count_of_nonsemiprime ha1 hap h
    omega
  obtain ⟨p,q,hp,hq,hapq⟩ := hsem
  have hpq : p ≠ q := by
    rintro rfl
    exact Nat.squarefree_iff_prime_squarefree.mp hsa p hp ⟨1,by simp [hapq]⟩
  have hsmall := (A056777Closure.excess_two_iff a).mpr ⟨p,q,hp,hq,hpq,hapq⟩
  have hca := hoa.coprime_two_left
  have hcb := hob.coprime_two_left
  rw [hna,hmb,Nat.totient_mul hca,Nat.totient_mul hcb,Nat.totient_prime Nat.prime_two] at hφ
  norm_num at hφ
  rw [hna,hmb,isMultiplicative_sigma.map_mul_of_coprime hca,
    isMultiplicative_sigma.map_mul_of_coprime hcb,show σ 1 2=3 by decide] at hσ
  exact odd_core_excess_not_six_or_negative hob hbl (by omega)

end A056777EvenSquarefreeThreeFive
end

section
open scoped ArithmeticFunction.sigma

namespace A056777CubeFive

/-- A prime cube has no five-factor partner at distance twelve with the same totient and sigma jumps. -/
theorem no_cube_five_pair {p m : ℕ} (hp : p.Prime) (hm : m.primeFactorsList.length = 5)
    (hgap : p^3+12=m ∨ m+12=p^3)
    (hφ : (p^3).totient+m=m.totient+p^3) (hσ : σ 1 (p^3)+m=σ 1 m+p^3) :
    False := by
  by_cases hs : Squarefree m
  · have hlength : (p^3).primeFactorsList.length=3 := by
      rw [hp.primeFactorsList_pow]
      simp
    exact A056777ThreeSquarefreeFive.no_three_squarefree_five_pair hlength hm hs hgap hφ hσ
  · rw [Nat.squarefree_iff_prime_squarefree] at hs
    push Not at hs
    obtain ⟨r,hr,hrs⟩ := hs
    have hrs : r^2∣m := by simpa only [pow_two] using hrs
    have hrm : r∣m := (dvd_pow_self r (by decide : 2 ≠ 0)).trans hrs
    have hrt : r∣m.totient := by
      apply dvd_trans _ (Nat.totient_dvd_of_dvd hrs)
      rw [show (r^2).totient=r*(r-1) by simpa using Nat.totient_prime_pow_succ hr 1]
      exact dvd_mul_right _ _
    have hdef : (p^3).totient+p^2=p^3 := by
      rw [show (p^3).totient=p^2*(p-1) from Nat.totient_prime_pow_succ hp 2]
      have hp1 := hp.pos
      zify [hp1]
      ring
    have hh : m.totient+p^2=m := by omega
    have hrp : r=p := by
      have H : r∣m.totient+p^2 := by rwa [hh]
      have hdiv : r∣p^2 := (Nat.dvd_add_iff_right hrt).mpr H
      have hpr := hr.dvd_of_dvd_pow hdiv
      exact (Nat.dvd_prime hp).mp hpr |>.resolve_left hr.ne_one
    subst r
    have h12 : p∣12 := by
      have hcube := dvd_pow_self p (by decide : 3 ≠ 0)
      rcases hgap with h|h
      · have H : p∣p^3+12 := by rwa [h]
        exact (Nat.dvd_add_iff_right hcube).mpr H
      · have H : p∣m+12 := by rwa [h]
        exact (Nat.dvd_add_iff_right hrm).mpr H
    have hsmall : p=2 ∨ p=3 := by
      have he : p∣2^2*3 := h12
      rcases hp.dvd_mul.mp he with h|h
      · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
      · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one)
    have len_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
        (a*b).primeFactorsList.length=a.primeFactorsList.length+b.primeFactorsList.length := by
      simpa using (Nat.perm_primeFactorsList_mul ha hb).length_eq
    rcases hsmall with rfl|rfl
    · have he : m=20 := by norm_num at hgap; omega
      subst m
      change (2^2*5).primeFactorsList.length=5 at hm
      rw [len_mul (by decide) (by decide),Nat.prime_two.primeFactorsList_pow,
        Nat.primeFactorsList_prime (by decide : Nat.Prime 5)] at hm
      simp at hm
    · have he : m=39 ∨ m=15 := by norm_num at hgap; omega
      rcases he with rfl|rfl
      · change (3*13).primeFactorsList.length=5 at hm
        rw [len_mul (by decide) (by decide),Nat.primeFactorsList_prime Nat.prime_three,
          Nat.primeFactorsList_prime (by decide : Nat.Prime 13)] at hm
        simp at hm
      · change (3*5).primeFactorsList.length=5 at hm
        rw [len_mul (by decide) (by decide),Nat.primeFactorsList_prime Nat.prime_three,
          Nat.primeFactorsList_prime (by decide : Nat.Prime 5)] at hm
        simp at hm

end A056777CubeFive
end

section
open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace A056777EvenRepeatedThreeFive

private theorem len_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a*b).primeFactorsList.length=a.primeFactorsList.length+b.primeFactorsList.length := by
  simpa using (Nat.perm_primeFactorsList_mul ha hb).length_eq

theorem phi_lower_defect {r u : ℕ} (hr : r.Prime) :
    (r*u).totient+u ≤ r*u := by
  by_cases h : r∣u
  · obtain ⟨v,rfl⟩ := h
    rw [Nat.totient_mul_of_prime_of_dvd hr (dvd_mul_right r v)]
    have haux : (r*v).totient ≤ (r-1)*v := by
      by_cases hd : r∣v
      · -- Prove the bound along the chain of powers of r.
        clear hd
        induction v using Nat.strong_induction_on with
        | h v ih =>
          by_cases hv : v=0
          · simp [hv]
          by_cases hd : r∣v
          · obtain ⟨w,rfl⟩ := hd
            have hw0 : 0<w := by by_contra! h; simp [show w=0 by omega] at hv
            have hlt : w<r*w := by nlinarith [hr.two_le]
            rw [Nat.totient_mul_of_prime_of_dvd hr (dvd_mul_right r w)]
            calc
              r*(r*w).totient ≤ r*((r-1)*w) := Nat.mul_le_mul_left _ (ih w hlt)
              _ = (r-1)*(r*w) := by ring
          · rw [Nat.totient_mul_of_prime_of_not_dvd hr hd]
            exact Nat.mul_le_mul_left _ (Nat.totient_le v)
      · rw [Nat.totient_mul_of_prime_of_not_dvd hr hd]
        exact Nat.mul_le_mul_left _ (Nat.totient_le v)
    have H := Nat.mul_le_mul_left r haux
    have h1 := hr.pos
    zify [h1] at H ⊢
    nlinarith
  · rw [Nat.totient_mul_of_prime_of_not_dvd hr h]
    have H := Nat.mul_le_mul_left (r-1) (Nat.totient_le u)
    have h1 := hr.pos
    zify [h1] at H ⊢
    nlinarith

theorem four_odd_core {u : ℕ} (hu : Odd u) (hl : u.primeFactorsList.length=4) :
    81 ≤ u ∧ u^3 ≤ (u-u.totient)^4 := by
  have hu0 : u ≠ 0 := by have := Nat.odd_iff.mp hu; omega
  have hlist : ∃ a b c d, u.primeFactorsList=[a,b,c,d] := by
    cases he : u.primeFactorsList with
    | nil => simp [he] at hl
    | cons a l =>
      rcases l with _ | ⟨b,l⟩
      · simp [he] at hl
      rcases l with _ | ⟨c,l⟩
      · simp [he] at hl
      rcases l with _ | ⟨d,l⟩
      · simp [he] at hl
      rcases l with _ | ⟨e,l⟩
      · exact ⟨a,b,c,d,rfl⟩
      · simp [he] at hl
  obtain ⟨a,b,c,d,he⟩ := hlist
  have ha := Nat.prime_of_mem_primeFactorsList (n := u) (p := a) (by simp [he])
  have hsort := (Nat.primeFactorsList_sorted u).pairwise
  simp only [he,List.pairwise_cons,List.mem_cons,List.not_mem_nil,or_false] at hsort
  have hab := hsort.1 b (Or.inl rfl)
  have hac := hsort.1 c (Or.inr (Or.inl rfl))
  have had := hsort.1 d (Or.inr (Or.inr rfl))
  have hu' : u=a*(b*c*d) := by simpa [he,mul_assoc] using (Nat.prod_primeFactorsList hu0).symm
  have hao : Odd a := (Nat.odd_mul.mp (hu' ▸ hu)).1
  have ha3 : 3 ≤ a := by have := ha.two_le; have := Nat.odd_iff.mp hao; omega
  have hprod : a^3 ≤ b*c*d := by
    simpa only [pow_succ,pow_zero,one_mul] using Nat.mul_le_mul (Nat.mul_le_mul hab hac) had
  have hlow := Nat.mul_le_mul ha3 (show 27 ≤ b*c*d from (Nat.pow_le_pow_left ha3 3).trans hprod)
  have hdef := phi_lower_defect (u:=b*c*d) ha
  rw [←hu'] at hdef
  have hdef' : b*c*d ≤ u-u.totient := by omega
  refine ⟨by omega,?_⟩
  conv_lhs => rw [hu',mul_pow]
  exact (Nat.mul_le_mul_right _ hprod).trans ((by ring : (b*c*d)*(b*c*d)^3=(b*c*d)^4) ▸
    Nat.pow_le_pow_left hdef' 4)

theorem no_two_times_prime_square_five {p m : ℕ} (hp : p.Prime) (hop : Odd p)
    (hm : m.primeFactorsList.length=5) (hg : 2*p^2+12=m ∨ m+12=2*p^2)
    (hφ : (2*p^2).totient+m=m.totient+2*p^2) : False := by
  have hme : Even m := Nat.even_iff.mpr (by omega)
  obtain ⟨u,hu⟩ := hme
  have hmu : m=2*u := by omega
  have hp2odd := hop.pow (n:=2)
  have huo : Odd u := by
    apply Nat.odd_iff.mpr
    have hpmod := Nat.odd_iff.mp hp2odd
    omega
  have hu0 : u ≠ 0 := by have := Nat.odd_iff.mp huo; omega
  have hl : u.primeFactorsList.length=4 := by
    rw [hmu,len_mul (by decide) hu0,Nat.primeFactorsList_two,List.length_singleton] at hm
    omega
  obtain ⟨hlarge,hpow⟩ := four_odd_core huo hl
  rw [hmu,Nat.totient_two_mul_of_odd hp2odd,Nat.totient_two_mul_of_odd huo,
    show (p^2).totient=p*(p-1) by simpa using Nat.totient_prime_pow_succ hp 1] at hφ
  have hp1 := hp.pos
  have hP : 9 ≤ p := by
    by_contra! h
    interval_cases p <;> norm_num at hφ hg hp <;> omega
  have hdef : u-u.totient ≤ p+6 := by
    have eq : p*(p-1)+p=p^2 := by zify [hp1]; ring
    omega
  have hu' : (p-1)^2 ≤ u := by
    have he : (p-1)^2+2*p=p^2+1 := by zify [hp1]; ring
    omega
  have hp' : p+6 ≤ 2*(p-1) := by omega
  have hi : (p+6)^4 ≤ (2*(p-1))^4 := Nat.pow_le_pow_left hp' 4
  have hj : (2*(p-1))^4<((p-1)^2)^3 := by
    have ha : 16<(p-1)^2 := by
      have H := Nat.pow_le_pow_left (show 8 ≤ p-1 by omega) 2
      omega
    have H := Nat.mul_lt_mul_of_pos_right ha
      (show 0<(p-1)^4 from Nat.pow_pos (show 0<p-1 by omega))
    calc
      (2*(p-1))^4 = 16*(p-1)^4 := by ring
      _ < (p-1)^2*(p-1)^4 := H
      _ = ((p-1)^2)^3 := by ring
  exact (not_lt_of_ge (Nat.le_trans hpow (Nat.pow_le_pow_left hdef 4)))
    (hi.trans_lt (hj.trans_le (Nat.pow_le_pow_left hu' 3)))

private theorem sigma_four_times_prime {q : ℕ} (hq : q.Prime) (ho : Odd q) :
    σ 1 (4*q)=7*(q+1) := by
  have hc := (ho.coprime_two_left).pow_left 2
  rw [show (4:ℕ)=2^2 by decide,isMultiplicative_sigma.map_mul_of_coprime hc]
  rw [show σ 1 (2^2)=7 by decide]
  have hs : σ 1 q=q+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hq
  rw [hs]

theorem no_four_times_prime_five {q m : ℕ} (hq : q.Prime) (ho : Odd q)
    (hm : m.primeFactorsList.length=5) (hg : 4*q+12=m ∨ m+12=4*q)
    (hφ : (4*q).totient+m=m.totient+4*q) (hσ : σ 1 (4*q)+m=σ 1 m+4*q) : False := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨k,u,hu,hmu⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have hu0 : u ≠ 0 := by have := Nat.odd_iff.mp hu; omega
  have hl : k+u.primeFactorsList.length=5 := by
    rw [hmu,len_mul (pow_ne_zero _ (by decide)) hu0,Nat.prime_two.primeFactorsList_pow,
      List.length_replicate] at hm
    exact hm
  have hqmod := Nat.odd_iff.mp ho
  have humod := Nat.odd_iff.mp hu
  have hk : 3 ≤ k := by
    by_contra! h
    interval_cases k <;> norm_num at hmu <;> omega
  have hq2 := hq.two_le
  have hφq : (4*q).totient=2*(q-1) := by
    rw [show (4:ℕ)=2^2 by decide,Nat.totient_mul (ho.coprime_two_left.pow_left 2),
      Nat.totient_prime hq,show (2^2:ℕ).totient=2 by decide]
  rw [hφq] at hφ
  rw [sigma_four_times_prime hq ho] at hσ
  have hlow : m+12=4*q := by
    have hm2 : ∃ v, m=2*v := ⟨m/2,by omega⟩
    obtain ⟨v,hv⟩ := hm2
    have hbound := phi_lower_defect (u:=v) Nat.prime_two
    rw [←hv] at hbound
    omega
  have hFm (j : ℕ) (hj : 0<j) :
      (2^j*u).totient=2^(j-1)*u.totient := by
    rw [Nat.totient_mul (hu.coprime_two_left.pow_left j),Nat.totient_prime_pow Nat.prime_two hj]
    norm_num
  rcases (show k=3 ∨ k=4 ∨ k=5 by omega) with rfl|rfl|rfl
  · have h := hFm 3 (by decide)
    norm_num at h hmu
    rw [hmu,h] at hφ
    have hu1 : 1<u := by by_contra! hh; interval_cases u <;> simp at hl
    have hφeven := Nat.even_iff.mp (Nat.totient_even (show 2<u by omega))
    omega
  · have h := hFm 4 (by decide)
    norm_num at h hmu
    rw [hmu,h] at hφ
    have hlu : u.primeFactorsList.length=1 := by omega
    have hup : u.Prime := by
      obtain ⟨r,hr⟩ : ∃ r, u.primeFactorsList=[r] := by
        cases he : u.primeFactorsList with
        | nil => simp [he] at hlu
        | cons r l =>
          obtain rfl : l=[] := List.length_eq_zero_iff.mp (by simpa [he] using hlu)
          exact ⟨r,rfl⟩
      have hp := Nat.prime_of_mem_primeFactorsList (n:=u) (p:=r) (by simp [hr])
      have he : u=r := by simpa [hr] using (Nat.prod_primeFactorsList hu0).symm
      exact he ▸ hp
    have hs : σ 1 m=31*(u+1) := by
      rw [hmu,show (16:ℕ)=2^4 by decide,
        isMultiplicative_sigma.map_mul_of_coprime (hu.coprime_two_left.pow_left 4)]
      rw [show σ 1 (2^4)=31 by decide]
      have he : σ 1 u=u+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hup
      rw [he]
    omega
  · have hh : u.primeFactorsList=[] := List.length_eq_zero_iff.mp (by omega)
    have he : u=1 := by simpa [hh] using (Nat.prod_primeFactorsList hu0).symm
    subst u
    have h : m=32 := by simpa using hmu
    subst m
    norm_num at hg hσ hφ
    have hs : σ 1 (32:ℕ)=63 := by decide
    omega

private theorem three_shape {n : ℕ} (hn : n.primeFactorsList.length=3) :
    Squarefree n ∨ (∃ p : ℕ, p.Prime ∧ n=p^3) ∨
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n=p^2*q) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨a,b,c,hl⟩ : ∃ a b c, n.primeFactorsList=[a,b,c] := by
    cases he : n.primeFactorsList with
    | nil => simp [he] at hn
    | cons a l =>
      rcases l with _ | ⟨b,l⟩
      · simp [he] at hn
      rcases l with _ | ⟨c,l⟩
      · simp [he] at hn
      obtain rfl : l=[] := List.length_eq_zero_iff.mp (by simpa [he] using hn)
      exact ⟨a,b,c,rfl⟩
  have ha := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=a) (by simp [hl])
  have hb := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=b) (by simp [hl])
  have hc := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=c) (by simp [hl])
  have he : n=a*b*c := by simpa [hl,mul_assoc] using (Nat.prod_primeFactorsList hn0).symm
  by_cases hab : a=b
  · subst b
    by_cases hac : a=c
    · subst c
      exact Or.inr (Or.inl ⟨a,ha,by rw [he]; ring⟩)
    · exact Or.inr (Or.inr ⟨a,c,ha,hc,hac,by rw [he]; ring⟩)
  · by_cases hac : a=c
    · subst c
      exact Or.inr (Or.inr ⟨a,b,ha,hb,hab,by rw [he]; ring⟩)
    · by_cases hbc : b=c
      · subst c
        exact Or.inr (Or.inr ⟨b,a,hb,ha,Ne.symm hab,by rw [he]; ring⟩)
      · left
        rw [he]
        exact Nat.squarefree_mul_iff.mpr
          ⟨((Nat.coprime_primes ha hc).mpr hac).mul_left ((Nat.coprime_primes hb hc).mpr hbc),
            Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes ha hb).mpr hab,ha.squarefree,hb.squarefree⟩,
            hc.squarefree⟩

/-- All even three-versus-five pairs are excluded under the two jump conditions. -/
theorem no_even_three_five_pair {n m : ℕ} (hn : n.primeFactorsList.length=3)
    (hm : m.primeFactorsList.length=5) (he : Even n) (hg : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) : False := by
  rcases three_shape hn with hs | ⟨p,hp,rfl⟩ | ⟨p,q,hp,hq,hpq,rfl⟩
  · exact A056777EvenSquarefreeThreeFive.no_even_squarefree_three_five_pair hn hm hs he hg hφ hσ
  · exact A056777CubeFive.no_cube_five_pair hp hm hg hφ hσ
  · rcases hp.eq_two_or_odd with rfl|hpo
    · have hqo := hq.eq_two_or_odd.resolve_left (Ne.symm hpq)
      exact no_four_times_prime_five hq (Nat.odd_iff.mpr hqo) hm hg hφ hσ
    · rcases hq.eq_two_or_odd with rfl|hqo
      · rw [mul_comm (p^2) 2] at hg hφ
        exact no_two_times_prime_square_five hp (Nat.odd_iff.mpr hpo) hm hg hφ
      · exact (Nat.not_even_iff_odd.mpr (((Nat.odd_iff.mpr hpo).pow (n:=2)).mul (Nat.odd_iff.mpr hqo))) he

/-- A three-versus-five pair reduces to two odd configurations. -/
theorem remaining_three_five_pair {n m : ℕ} (hn : n.primeFactorsList.length=3)
    (hm : m.primeFactorsList.length=5) (hg : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    (m+12=n ∧ Squarefree n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
      p%4=3 ∧ q%8=3 ∧ 11 ≤ q ∧ 2*q<p ∧ p%3 ≠ q%3 ∧ p^2<q^3 ∧
      (p%5=2 ∨ p%5=3) ∧ q%5=2 ∧ m=p^4*q) ∨
    (Odd m ∧ ¬Squarefree m ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      Odd p ∧ Odd q ∧ p ≠ q ∧ n=p^2*q) := by
  have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => no_even_three_five_pair hn hm he hg hφ hσ)
  rcases three_shape hn with hs | ⟨p,hp,rfl⟩ | ⟨p,q,hp,hq,hpq,hshape⟩
  · obtain ⟨h,hr⟩ := A056777OddSquarefreeThreeFive.odd_squarefree_three_five_orientation_mod_five
      hn hm hs ho hg hφ hσ
    exact Or.inl ⟨h,hs,hr⟩
  · exact (A056777CubeFive.no_cube_five_pair hp hm hg hφ hσ).elim
  · right
    have hmO : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
    have hmN : ¬Squarefree m := fun hmS =>
      A056777ThreeSquarefreeFive.no_three_squarefree_five_pair hn hm hmS hg hφ hσ
    have hodd := Nat.odd_mul.mp (hshape ▸ ho)
    have hpo := (odd_pow_iff (by decide : 2 ≠ 0)).mp hodd.1
    exact ⟨hmO,hmN,p,q,hp,hq,hpo,hodd.2,hpq,hshape⟩

end A056777EvenRepeatedThreeFive
end

section
open scoped ArithmeticFunction.sigma

namespace A056777OddRepeatedThreeFive

/-- An odd square times a distinct prime cannot pair with a prime fifth power.
The totient jump alone excludes this case. -/
theorem no_square_prime_fifth_power {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpo : Odd p) (hpq : p ≠ q)
    (hg : p^2*q+12=r^5 ∨ r^5+12=p^2*q)
    (hφ : (p^2*q).totient+r^5=(r^5).totient+p^2*q) : False := by
  have hF := (A056777EvenFourFour.square_prime_formulas hp hq hpq).1
  have hF' : (r^5).totient+r^4=r^5 := by
    rw [show (r^5).totient=r^4*(r-1) from Nat.totient_prime_pow_succ hr 4]
    have hr1 := hr.pos
    zify [hr1]
    ring
  have he : p*(p+q-1)=r^4 := by omega
  have hd : p∣r^4 := ⟨p+q-1,he.symm⟩
  have hpr : p=r := (Nat.dvd_prime hr).mp (hp.dvd_of_dvd_pow hd) |>.resolve_left hp.ne_one
  subst r
  have HH : p*(p+q-1)=p*p^3 := he.trans (by ring)
  have hq' : p+q-1=p^3 := Nat.eq_of_mul_eq_mul_left hp.pos HH
  have hp1 := hp.pos
  have HP : p^5=p^2*q+p^2*(p-1) := by
    have hh : p+q=p^3+1 := by omega
    zify [hp1]
    have hhz : (p:ℤ)+(q:ℤ)=(p:ℤ)^3+1 := by exact_mod_cast hh
    nlinarith only [congrArg (fun x : ℤ => (p:ℤ)^2*x) hhz]
  have hp3 : 3 ≤ p := by have := hp.two_le; have := Nat.odd_iff.mp hpo; omega
  have hbound : 18 ≤ p^2*(p-1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hp3 2) (by omega : 2 ≤ p-1)
  omega

open Nat ArithmeticFunction
open A056777EvenRepeatedThreeFive (phi_lower_defect four_odd_core)

private theorem core_length {k u : ℕ} (hu : Odd u)
    (hm : (3^k*u).primeFactorsList.length=5) :
    k+u.primeFactorsList.length=5 := by
  have hu0 : u ≠ 0 := by have := Nat.odd_iff.mp hu; omega
  have hh := (Nat.perm_primeFactorsList_mul
    (pow_ne_zero k (by decide : (3:ℕ) ≠ 0)) hu0).length_eq
  simpa [hm,Nat.prime_three.primeFactorsList_pow] using hh.symm

private theorem three_core_phi {k u : ℕ} (hk : 0<k) (hu : ¬3∣u) :
    (3^k*u).totient=2*3^(k-1)*u.totient := by
  have hc := (Nat.coprime_or_dvd_of_prime Nat.prime_three u).resolve_right hu
  rw [Nat.totient_mul (hc.pow_left k),Nat.totient_prime_pow Nat.prime_three hk]
  norm_num [mul_comm]

private theorem no_shared_three_at_square {q m : ℕ} (hq : q.Prime) (hqo : Odd q) (hq3 : q ≠ 3)
    (hm : m.primeFactorsList.length=5) (h3m : 3∣m)
    (hg : 9*q+12=m ∨ m+12=9*q)
    (hφ : (9*q).totient+m=m.totient+9*q) : False := by
  obtain ⟨u,hu⟩ := h3m
  have hu3 : ¬3∣u := by
    rintro ⟨t,ht⟩
    rw [hu,ht] at hg
    omega
  have huo := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hqo; omega : u%2=1)
  have hL := core_length (k:=1) huo (by simpa [hu] using hm)
  obtain ⟨hlarge,hpow⟩ := four_odd_core huo (by omega : u.primeFactorsList.length=4)
  have hmφ := three_core_phi (k:=1) (by decide) hu3
  have hf := (A056777EvenFourFour.square_prime_formulas Nat.prime_three hq (Ne.symm hq3)).1
  norm_num at hmφ hf
  rw [hu,hmφ] at hφ
  have hb : u-u.totient ≤ 5 := by omega
  have H := Nat.pow_le_pow_left hb 4
  have J := Nat.pow_le_pow_left hlarge 3
  omega

private theorem no_shared_three_at_single {p m : ℕ} (hp : p.Prime) (hpo : Odd p) (hp3 : p ≠ 3)
    (hm : m.primeFactorsList.length=5) (h3m : 3∣m)
    (hg : p^2*3+12=m ∨ m+12=p^2*3)
    (hφ : (p^2*3).totient+m=m.totient+p^2*3) : False := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  obtain ⟨k,u,hu3,hmu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by decide)
  have hk : k ≠ 0 := by rintro rfl; apply hu3; simpa [hmu] using h3m
  have huO : Odd u := by
    have hmO : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp (hpo.pow (n:=2)); omega)
    exact (Nat.odd_mul.mp (hmu ▸ hmO)).2
  have hL := core_length huO (by simpa [hmu] using hm)
  have hM := three_core_phi (Nat.pos_of_ne_zero hk) hu3
  have hF := (A056777EvenFourFour.square_prime_formulas hp Nat.prime_three hp3).1
  have hp1 := hp.pos
  have hp5 : 5 ≤ p := by have := hp.two_le; have := Nat.odd_iff.mp hpo; omega
  have hpdiv : ¬3∣p := fun h => hp3 ((Nat.dvd_prime hp).mp h |>.resolve_left (by decide)).symm
  have hpmod : p^2%3=1 := by
    have hh := Nat.pow_mod p 2 3
    have hne : p%3 ≠ 0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hpdiv
    have ht : p%3=1 ∨ p%3=2 := by omega
    rcases ht with h|h <;> norm_num [h] at hh <;> omega
  rw [hmu,hM] at hφ
  rw [hmu] at hg
  by_cases hk1 : k=1
  · subst k
    norm_num at hg hφ
    have hup : u=p^2+4 := by
      by_contra hn
      apply hu3
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    obtain ⟨_,hpow⟩ := four_odd_core huO (by omega : u.primeFactorsList.length=4)
    have hE : p*(p+3-1)=p^2+2*p := by rw [show p+3-1=p+2 by omega]; ring
    have hbound : u-u.totient ≤ p := by omega
    have hJ := Nat.pow_le_pow_left hbound 4
    have hKill : p^4<(p^2)^3 := by
      have H := Nat.mul_lt_mul_of_pos_left (show 1<p^2 by nlinarith) (pow_pos hp1 4)
      simpa [show p^4*p^2=(p^2)^3 by ring] using H
    have hPP : (p^2)^3 ≤ u^3 := Nat.pow_le_pow_left (by omega) 3
    omega
  · have hcase : k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
    let C := 3^(k-1)
    have hC3 : 3∣C := by
      have H : 1 ≤ k-1 := by omega
      exact pow_dvd_pow 3 H
    have hC0 : 0<C := by positivity
    have hC : 3^k=3*C := by
      dsimp [C]
      conv_lhs => rw [show k=k-1+1 by omega,pow_succ,mul_comm]
    rw [hC] at hg hφ
    change _ + _ = 2*C*u.totient + _ at hφ
    rw [show 3*C*u=3*(C*u) by ring,show 2*C*u.totient=2*(C*u.totient) by ring] at hφ
    have hcore : C*u+4=p^2 := by
      have h3Cu : 3∣C*u := hC3.trans (dvd_mul_right _ _)
      rw [Nat.dvd_iff_mod_eq_zero] at h3Cu
      have hge : p^2+4=C*u ∨ C*u+4=p^2 := by
        have he : 3*C*u=3*(C*u) := by ring
        rw [he] at hg
        omega
      omega
    have hE : p*(p+3-1)=p^2+2*p := by rw [show p+3-1=p+2 by omega]; ring
    have hdef : C*(u-u.totient)=p+2 := by
      have htu := Nat.totient_le u
      rw [Nat.mul_sub_left_distrib]
      omega
    let v := u-u.totient
    have hv : C*v=p+2 := hdef
    have hu' : u=(p-2)*v := by
      apply Nat.eq_of_mul_eq_mul_left hC0
      calc
        C*u = p^2-4 := by omega
        _ = (p-2)*(p+2) := by zify [show 4 ≤ p^2 by nlinarith,show 2 ≤ p by omega]; ring
        _ = C*((p-2)*v) := by rw [←hv]; ring
    have hv1 : v=1 := by
      have hv0 : 0<v := by by_contra! h; simp [show v=0 by omega] at hv
      by_contra h
      obtain ⟨r,hr,⟨w,hw⟩⟩ := Nat.exists_prime_and_dvd (show v ≠ 1 from h)
      have he : u=r*((p-2)*w) := by rw [hu',hw]; ring
      have hdefr := phi_lower_defect (u:=(p-2)*w) hr
      rw [←he] at hdefr
      have hw0 : 1 ≤ w := by by_contra! h; simp [show w=0 by omega] at hw; omega
      have HB := Nat.mul_le_mul_left (p-2) hw0
      have HC : 3*v ≤ p+2 := (Nat.mul_le_mul_right _ (Nat.le_of_dvd hC0 hC3)).trans_eq hv
      have : v < p-2 := by omega
      dsimp [v] at this
      omega
    rw [hv1,mul_one] at hv
    rcases hcase with rfl|rfl|rfl|rfl
    · norm_num [C] at hv
      omega
    · norm_num [C] at hv
      have hP : p=7 := by omega
      subst p
      have hU : u=5 := by norm_num [hv1] at hu'; exact hu'
      rw [hU] at hL
      rw [Nat.primeFactorsList_prime (by decide : Nat.Prime 5)] at hL
      simp at hL
    · norm_num [C] at hv
      have hP : p=25 := by omega
      subst p
      exact (by decide : ¬Nat.Prime 25) hp
    · norm_num [C] at hv
      have hP : p=79 := by omega
      subst p
      have hU : u=77 := by norm_num [hv1] at hu'; exact hu'
      rw [hU] at hL
      have hf77 := (Nat.perm_primeFactorsList_mul
        (by decide : (7:ℕ) ≠ 0) (by decide : (11:ℕ) ≠ 0)).length_eq
      rw [Nat.primeFactorsList_prime (by decide : Nat.Prime 7),
        Nat.primeFactorsList_prime (by decide : Nat.Prime 11)] at hf77
      change (77:ℕ).primeFactorsList.length=2 at hf77
      omega

/-- Any odd square-prime endpoint in a three-versus-five pair is coprime to its partner. -/
theorem coprime_square_prime_five {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (hm : m.primeFactorsList.length=5)
    (hg : p^2*q+12=m ∨ m+12=p^2*q)
    (hφ : (p^2*q).totient+m=m.totient+p^2*q) : (p^2*q).Coprime m := by
  rw [Nat.coprime_mul_iff_left]
  have neither {r : ℕ} (hr : r.Prime) (hro : Odd r) (hrn : r∣p^2*q) : r∣m → r=3 := by
    intro hrm
    have hd : r∣12 := by
      rcases hg with h|h
      · exact (Nat.dvd_add_iff_right hrn).mpr (by rwa [h])
      · exact (Nat.dvd_add_iff_right hrm).mpr (by rwa [h])
    have hd' : r∣2^2*3 := hd
    rcases hr.dvd_mul.mp hd' with h|h
    · have hr2 := (Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow h) |>.resolve_left hr.ne_one
      subst r
      have := Nat.odd_iff.mp hro
      omega
    · exact (Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hr.ne_one
  have hpn : p∣p^2*q := (dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _)
  have hqn : q∣p^2*q := dvd_mul_left _ _
  constructor
  · apply Nat.Coprime.pow_left
    refine (Nat.coprime_or_dvd_of_prime hp m).resolve_right fun h => ?_
    have h3 := neither hp hpo hpn h
    subst p
    exact no_shared_three_at_square hq hqo (Ne.symm hpq) hm h hg hφ
  · refine (Nat.coprime_or_dvd_of_prime hq m).resolve_right fun h => ?_
    have h3 := neither hq hqo hqn h
    subst q
    exact no_shared_three_at_single hp hpo hpq hm h hg hφ

/-- Every divisor shared by the larger-factor-count endpoint and its totient divides
the sum of the two prime bases of the three-factor endpoint, minus one. -/
theorem common_totient_divisor_square_prime_five {p q m d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (hm : m.primeFactorsList.length=5)
    (hg : p^2*q+12=m ∨ m+12=p^2*q)
    (hφ : (p^2*q).totient+m=m.totient+p^2*q)
    (hdm : d∣m) (hdφ : d∣m.totient) :
    d∣p+q-1 ∧ d∣(p^2*(p-1)+12) * (p^2*(p-1)-12) := by
  have hc := coprime_square_prime_five hp hq hpo hqo hpq hm hg hφ
  have hpd : p.Coprime d :=
    (hc.coprime_dvd_left ((dvd_pow_self p (by decide : 2 ≠ 0)).trans (dvd_mul_right _ _))).coprime_dvd_right hdm
  have hf := (A056777EvenFourFour.square_prime_formulas hp hq hpq).1
  have hdef : m=m.totient+p*(p+q-1) := by omega
  have hD : d∣p*(p+q-1) := (Nat.dvd_add_iff_right hdφ).mpr (hdef ▸ hdm)
  have hsum := hpd.symm.dvd_of_dvd_mul_left hD
  refine ⟨hsum,?_⟩
  have H : p^2*q+p^2*(p-1)=p^2*(p+q-1) := by
    rw [←Nat.mul_add]
    congr 1
    have := hp.pos
    omega
  have hdSum : d∣p^2*q+p^2*(p-1) := H ▸ dvd_mul_of_dvd_right hsum _
  rcases hg with h|h
  · have he : p^2*q+p^2*(p-1)=(p^2*q+12)+(p^2*(p-1)-12) := by
      have hp3 : 3 ≤ p := by have := hp.two_le; have := Nat.odd_iff.mp hpo; omega
      have hge : 18 ≤ p^2*(p-1) := Nat.mul_le_mul (Nat.pow_le_pow_left hp3 2) (by omega : 2 ≤ p-1)
      omega
    rw [he,h] at hdSum
    exact dvd_mul_of_dvd_right ((Nat.dvd_add_iff_right hdm).mpr hdSum) _
  · have he : p^2*q+p^2*(p-1)=m+(p^2*(p-1)+12) := by omega
    rw [he] at hdSum
    exact dvd_mul_of_dvd_left ((Nat.dvd_add_iff_right hdm).mpr hdSum) _

end A056777OddRepeatedThreeFive
end

open Nat OeisA56777
open scoped ArithmeticFunction.sigma

/-- Exclude partners with at least six prime factors counted with multiplicity. -/
def H1 : Prop :=
  ∀ n : ℕ, A n →
    ((n.primeFactorsList.length = 3 ∧ 6 ≤ (n + 12).primeFactorsList.length) ∨
      ((n + 12).primeFactorsList.length = 3 ∧ 6 ≤ n.primeFactorsList.length)) →
    (¬ Squarefree n ∨ ¬ Squarefree (n + 12)) →
    1 ≤ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card →
    1 ≤ ((n + 12).primeFactors.filter fun p =>
      p ≠ 2 ∧ Odd ((n + 12).factorization p)).card →
    ((n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 ∨
      ((n + 12).primeFactors.filter fun p =>
        p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2) →
    False

/-- Exclude the remaining odd squarefree-three configuration. -/
def H2 : Prop :=
  ∀ n m : ℕ, n.primeFactorsList.length = 3 → m.primeFactorsList.length = 5 →
    Odd n → Squarefree n → m + 12 = n →
    n.totient + m = m.totient + n → σ 1 n + m = σ 1 m + n →
    (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧
      p % 4 = 3 ∧ q % 8 = 3 ∧ 11 ≤ q ∧ 2*q < p ∧ p % 3 ≠ q % 3 ∧ p^2 < q^3 ∧
      (p % 5 = 2 ∨ p % 5 = 3) ∧ q % 5 = 2 ∧ m = p^4*q) → False

/-- Exclude the remaining odd repeated-prime three-factor configuration. -/
def H3 : Prop :=
  ∀ p q m : ℕ, p.Prime → q.Prime → Odd p → Odd q → p ≠ q →
    m.primeFactorsList.length = 5 → Odd m → ¬ Squarefree m →
    (p^2*q + 12 = m ∨ m + 12 = p^2*q) →
    (p^2*q).totient + m = m.totient + p^2*q → σ 1 (p^2*q) + m = σ 1 m + p^2*q →
    (p^2*q).Coprime m → (∀ r : ℕ, r.Prime → m ≠ r^5) →
    (∀ d : ℕ, d ∣ m → d ∣ m.totient →
      d ∣ p+q-1 ∧ d ∣ (p^2*(p-1)+12) * (p^2*(p-1)-12)) → False

theorem eliminate_five (hsq : H2) (hrep : H3) {n m : ℕ}
    (hn : n.primeFactorsList.length = 3) (hm : m.primeFactorsList.length = 5)
    (hg : n + 12 = m ∨ m + 12 = n)
    (hφ : n.totient + m = m.totient + n) (hσ : σ 1 n + m = σ 1 m + n) : False := by
  rcases A056777EvenRepeatedThreeFive.remaining_three_five_pair hn hm hg hφ hσ with
    ⟨hgap, hsf, hshape⟩ | ⟨hmo, hms, p, q, hp, hq, hpo, hqo, hpq, rfl⟩
  · have hno : Odd n := Nat.not_even_iff_odd.mp (fun he =>
      A056777EvenRepeatedThreeFive.no_even_three_five_pair hn hm he hg hφ hσ)
    exact hsq n m hn hm hno hsf hgap hφ hσ hshape
  · refine hrep p q m hp hq hpo hqo hpq hm hmo hms hg hφ hσ
      (A056777OddRepeatedThreeFive.coprime_square_prime_five hp hq hpo hqo hpq hm hg hφ)
      ?_ (fun d => A056777OddRepeatedThreeFive.common_totient_divisor_square_prime_five
        hp hq hpo hqo hpq hm hg hφ)
    intro r hr he
    subst m
    exact A056777OddRepeatedThreeFive.no_square_prime_fifth_power hp hq hr hpo hpq hg hφ

theorem main : H1 → H2 → H3 → OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2.H2 := by
  intro hlarge hsq hrep n ha hcounts hsf hodd₁ hodd₂ hsupport
  have ht := ha.2.2.1
  have hs := ha.2.2.2
  rcases hcounts with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · by_cases hm : (n+12).primeFactorsList.length = 5
    · exact eliminate_five hsq hrep h₁ hm (Or.inl rfl) (by omega) (by omega)
    · exact hlarge n ha (Or.inl ⟨h₁,by omega⟩) hsf hodd₁ hodd₂ hsupport
  · by_cases hm : n.primeFactorsList.length = 5
    · exact eliminate_five hsq hrep h₁ hm (Or.inr rfl) (by omega) (by omega)
    · exact hlarge n ha (Or.inr ⟨h₁,by omega⟩) hsf hodd₁ hodd₂ hsupport

end OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1
