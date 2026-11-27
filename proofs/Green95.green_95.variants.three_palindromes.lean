import FormalConjectures.GreensOpenProblems.«95»
import Mathlib

/-! # Every positive integer is a sum of three base-`g` palindromes (Cilleruelo, Luca, Baxter) -/

namespace OMA.R_Green95_green_95_variants_three_palindromes_R1

open Green95

/-- The single-digit case: every `n` with `0 < n < g` is a sum of three base-`g` palindromes. -/
def H1 : Prop :=
  ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, 0 < n → n < g →
    ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p + q + r = n

/-- The induction step: every `n ≥ g` is a sum of three base-`g` palindromes. -/
def H2 : Prop :=
  ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, g ≤ n →
    ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p + q + r = n

theorem main : H1 → H2 → type_of% @Green95.green_95.variants.three_palindromes := by
  intro h1 h2 g hg n hn
  by_cases h : n < g
  · exact h1 g hg n hn h
  · exact h2 g hg n (by omega)

end OMA.R_Green95_green_95_variants_three_palindromes_R1

private theorem h1_proof : OMA.R_Green95_green_95_variants_three_palindromes_R1.H1 := by
  unfold OMA.R_Green95_green_95_variants_three_palindromes_R1.H1
  intro g hg n hn hng
  refine ⟨n, 0, 0, ?_, ?_, ?_, by simp⟩
  · unfold Green95.IsPalindrome
    rw [Nat.digits_of_lt g n (by omega) hng]
    rfl
  · simp [Green95.IsPalindrome]
  · simp [Green95.IsPalindrome]

namespace OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1
open Green95

private lemma zeroPal (g : ℕ) : IsPalindrome g 0 := by simp [IsPalindrome]

private lemma one {g a : ℕ} (hg : 5 ≤ g) (hu : a < g) :
    IsPalindrome g (a) := by
  by_cases hz : a=0
  · simpa [hz] using zeroPal g
  have eq : Nat.ofDigits g [a] = a := by simp [Nat.ofDigits]
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all)]
  rfl

private lemma two {g a : ℕ} (hg : 5 ≤ g) (hu : a < g) :
    IsPalindrome g (a*(g+1)) := by
  by_cases hz : a=0
  · simpa [hz] using zeroPal g
  have eq : Nat.ofDigits g [a,a] = a*(g+1) := by simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all)]
  rfl

private lemma three {g a b : ℕ} (hg : 5 ≤ g) (ha : 0 < a) (hu : a < g) (hb : b < g) :
    IsPalindrome g (a*(g^2+1)+b*g) := by
  have eq : Nat.ofDigits g [a,b,a] = a*(g^2+1)+b*g := by simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all; omega)]
  rfl

private lemma four {g a b : ℕ} (hg : 5 ≤ g) (ha : 0 < a) (hu : a < g) (hb : b < g) :
    IsPalindrome g (a*(g^3+1)+b*g*(g+1)) := by
  have eq : Nat.ofDigits g [a,b,b,a] = a*(g^3+1)+b*g*(g+1) := by simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all; omega)]
  rfl

private lemma shortClass {g a b c : ℕ} (hg : 5 ≤ g) (ha : a<g) (hb : b<g) (hc : c<g) :
    let n := a*g^2+b*g+c
    (∃ p q, IsPalindrome g p ∧ IsPalindrome g q ∧ p+q=n) ∨
    (∃ u, 1 ≤ u ∧ u < g ∧ n+1 = u*(g+1)) ∨ n=2*g^2+1 := by
  dsimp only
  by_cases h0 : a=0
  · subst a
    simp only [zero_mul,zero_add]
    by_cases hbc : b ≤ c
    · left
      refine ⟨_,_,two hg hb,one hg (show c-b < g by omega),?_⟩
      rw [Nat.mul_add, Nat.mul_one]; omega
    · by_cases edge : c+1=b
      · right; left; exact ⟨b,by omega,hb,by rw [Nat.mul_add,Nat.mul_one]; omega⟩
      · left
        obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
        refine ⟨_,_,two hg (show j < g by omega),one hg (show g+c-j < g by omega),?_⟩
        rw [Nat.succ_mul,Nat.mul_add,Nat.mul_one]; omega
  by_cases ca : a ≤ c
  · left
    refine ⟨_,_,three hg (by omega) ha hb,one hg (show c-a < g by omega),?_⟩
    rw [Nat.mul_add,Nat.mul_one]; omega
  by_cases b0 : b=0
  · subst b
    simp only [zero_mul,add_zero]
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    by_cases j0 : j=0
    · subst j; have : c=0 := by omega
      subst c; left
      refine ⟨_,_,two hg (show g-1<g by omega),one hg (show 1<g by omega),?_⟩
      zify [show 1≤g by omega]; ring
    by_cases edge : c=j
    · subst c
      by_cases j1 : j=1
      · right; right; simp [j1]
      · left
        obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero j0
        refine ⟨_,_,three hg (by decide : 0<1) (by omega) (by omega : 1<g),
          three hg (by omega : 0<u) (by omega) (show g-1<g by omega),?_⟩
        zify [show 1≤g by omega]; ring
    · left
      refine ⟨_,_,three hg (by omega : 0<j) (by omega) (show g-1<g by omega),
        one hg (show g+c-j<g by omega),?_⟩
      zify [show 1≤g by omega,show j≤g+c by omega]; ring
  · left
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero b0
    refine ⟨_,_,three hg (by omega) ha (show j<g by omega),
      one hg (show g+c-a<g by omega),?_⟩
    zify [show a≤g+c by omega]; ring

private lemma classify {g n : ℕ} (hg : 5 ≤ g) (hn : n<g^3) :
    (∃ p q, IsPalindrome g p ∧ IsPalindrome g q ∧ p+q=n) ∨
    (∃ u, 1 ≤ u ∧ u < g ∧ n+1 = u*(g+1)) ∨ n=2*g^2+1 := by
  let a := n/g/g
  let b := n/g%g
  let c := n%g
  have ha : a<g := by
    dsimp [a]; rw [Nat.div_lt_iff_lt_mul (by omega),Nat.div_lt_iff_lt_mul (by omega)]
    simpa [pow_succ] using hn
  have e1 : c+g*(n/g)=n := Nat.mod_add_div _ _
  have e2 : b+g*a=n/g := Nat.mod_add_div _ _
  have e : a*g^2+b*g+c=n := by linear_combination e1 + g*e2
  rw [←e]
  exact shortClass hg ha (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))

private lemma remainder {g p t : ℕ} (hg : 5≤g) (hp : IsPalindrome g p) (ht : t ≤ g) :
    ∃ x y z, IsPalindrome g x ∧ IsPalindrome g y ∧ IsPalindrome g z ∧ x+y+z=p+t := by
  by_cases h : t<g
  · exact ⟨_,_,_,hp,one hg h,zeroPal g,by omega⟩
  · exact ⟨_,_,_,hp,one hg (show g-1<g by omega),one hg (show 1<g by omega),by omega⟩

private lemma short {g n : ℕ} (hg : 5≤g) (hn : n<g^4) :
    ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p+q+r=n := by
  let a := n/g^3
  let z := n%g^3
  have ha : a<g := by dsimp [a]; rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa [pow_succ,mul_comm] using hn
  have hz : z<g^3 := Nat.mod_lt _ (by positivity)
  have eq : z+g^3*a=n := Nat.mod_add_div _ _
  clear_value a z
  by_cases a0 : a=0
  · have nz : n=z := by simpa [a0] using eq.symm
    rcases classify hg (nz ▸ hz) with ⟨p,q,hp,hq,h⟩ | ⟨u,hu,hug,h⟩ | h
    · exact ⟨_,_,_,hp,hq,zeroPal g,by omega⟩
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u≠0)
      have e : n=j*(g+1)+g := by rw [Nat.succ_mul] at h; omega
      rw [e]; exact remainder hg (two hg (by omega)) le_rfl
    · refine ⟨_,_,_,three hg (by decide : 0<1) (by omega) (show g-1<g by omega),one hg (show g-1<g by omega),one hg (show 1<g by omega),?_⟩
      rw [h]; zify [show 1≤g by omega]; ring
  by_cases za : z<a
  · by_cases a1 : a=1
    · have zn : n=g^3 := by
        have hzero : z=0 := by omega
        simpa [hzero,a1] using eq.symm
      refine ⟨_,_,_,three hg (show 0<g-1 by omega) (by omega) (show g-1<g by omega),one hg (show 1<g by omega),zeroPal g,?_⟩
      rw [zn]; zify [show 1≤g by omega]; ring
    · have e : n = (a-1)*(g^3+1)+(g-1)*g*(g+1)+(g+z-(a-1)) := by
        rw [←eq]; zify [show 1≤a by omega,show 1≤g by omega,show a-1≤g+z by omega]; ring
      rw [e]
      exact remainder hg (four hg (by omega) (by omega) (by omega)) (by omega)
  let m := z-a
  have hm : m+a=z := by dsimp [m]; omega
  clear_value m
  have en : n=a*(g^3+1)+m := by rw [←eq, ←hm]; ring
  rcases classify hg (show m<g^3 by omega) with ⟨p,q,hp,hq,h⟩ | ⟨u,hu,hug,h⟩ | h
  · refine ⟨_,_,_,four hg (by omega) ha (show 0<g by omega),hp,hq,?_⟩
    rw [en, ←h]; ring
  · by_cases a1 : a=1
    · refine ⟨_,_,_,three hg (show 0<g-1 by omega) (by omega) (show g-1<g by omega),two hg hug,one hg (show 1<g by omega),?_⟩
      rw [en,a1]; zify [show 1≤g by omega] at h ⊢; linarith
    · refine ⟨_,_,_,four hg (show 0<a-1 by omega) (by omega) (show g-2<g by omega),
        three hg (by decide : 0<1) (by omega) (show 3<g by omega),two hg (show u-1<g by omega),?_⟩
      rw [en]; zify [show 1≤a by omega,show 2≤g by omega,hu] at h ⊢; linarith
  · by_cases a1 : a=1
    · refine ⟨_,_,_,four hg (by decide : 0<1) (by omega) (show 1<g by omega),two hg (show g-2<g by omega),one hg (show 3<g by omega),?_⟩
      rw [en,h,a1]; zify [show 2≤g by omega]; ring
    · refine ⟨_,_,_,four hg (show 0<a-1 by omega) (by omega) (show g-1<g by omega),
        three hg (by decide : 0<2) (by omega) (show 1<g by omega),zeroPal g,?_⟩
      rw [en,h]; zify [show 1≤a by omega,show 1≤g by omega]; ring

def H1 : Prop := ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, g^4 ≤ n → n < g^6 →
  ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p+q+r=n

def H2 : Prop := ∀ g : ℕ, 5 ≤ g → ∀ n : ℕ, g^6 ≤ n →
  ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p+q+r=n

theorem main : H1 → H2 → OMA.R_Green95_green_95_variants_three_palindromes_R1.H2 := by
  intro medium large g hg n _
  by_cases shortN : n<g^4
  · exact short hg shortN
  by_cases mediumN : n<g^6
  · exact medium g hg n (by omega) mediumN
  · exact large g hg n (by omega)
end OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1

section
namespace G95Med
open Green95

private lemma zeroPal (g : ℕ) : IsPalindrome g 0 := by simp [IsPalindrome]

private lemma one {g a : ℕ} (hg : 5 ≤ g) (hu : a < g) :
    IsPalindrome g (a) := by
  by_cases hz : a=0
  · simpa [hz] using zeroPal g
  have eq : Nat.ofDigits g [a] = a := by simp [Nat.ofDigits]
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all)]
  rfl

private lemma two {g a : ℕ} (hg : 5 ≤ g) (hu : a < g) :
    IsPalindrome g (a*(g+1)) := by
  by_cases hz : a=0
  · simpa [hz] using zeroPal g
  have eq : Nat.ofDigits g [a,a] = a*(g+1) := by simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all)]
  rfl

private lemma three {g a b : ℕ} (hg : 5 ≤ g) (ha : 0 < a) (hu : a < g) (hb : b < g) :
    IsPalindrome g (a*(g^2+1)+b*g) := by
  have eq : Nat.ofDigits g [a,b,a] = a*(g^2+1)+b*g := by simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all; omega)]
  rfl

private lemma four {g a b : ℕ} (hg : 5 ≤ g) (ha : 0 < a) (hu : a < g) (hb : b < g) :
    IsPalindrome g (a*(g^3+1)+b*g*(g+1)) := by
  have eq : Nat.ofDigits g [a,b,b,a] = a*(g^3+1)+b*g*(g+1) := by simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all; omega)]
  rfl

private lemma shortClass {g a b c : ℕ} (hg : 5 ≤ g) (ha : a<g) (hb : b<g) (hc : c<g) :
    let n := a*g^2+b*g+c
    (∃ p q, IsPalindrome g p ∧ IsPalindrome g q ∧ p+q=n) ∨
    (∃ u, 1 ≤ u ∧ u < g ∧ n+1 = u*(g+1)) ∨ n=2*g^2+1 := by
  dsimp only
  by_cases h0 : a=0
  · subst a
    simp only [zero_mul,zero_add]
    by_cases hbc : b ≤ c
    · left
      refine ⟨_,_,two hg hb,one hg (show c-b < g by omega),?_⟩
      rw [Nat.mul_add, Nat.mul_one]; omega
    · by_cases edge : c+1=b
      · right; left; exact ⟨b,by omega,hb,by rw [Nat.mul_add,Nat.mul_one]; omega⟩
      · left
        obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
        refine ⟨_,_,two hg (show j < g by omega),one hg (show g+c-j < g by omega),?_⟩
        rw [Nat.succ_mul,Nat.mul_add,Nat.mul_one]; omega
  by_cases ca : a ≤ c
  · left
    refine ⟨_,_,three hg (by omega) ha hb,one hg (show c-a < g by omega),?_⟩
    rw [Nat.mul_add,Nat.mul_one]; omega
  by_cases b0 : b=0
  · subst b
    simp only [zero_mul,add_zero]
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
    by_cases j0 : j=0
    · subst j; have : c=0 := by omega
      subst c; left
      refine ⟨_,_,two hg (show g-1<g by omega),one hg (show 1<g by omega),?_⟩
      zify [show 1≤g by omega]; ring
    by_cases edge : c=j
    · subst c
      by_cases j1 : j=1
      · right; right; simp [j1]
      · left
        obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero j0
        refine ⟨_,_,three hg (by decide : 0<1) (by omega) (by omega : 1<g),
          three hg (by omega : 0<u) (by omega) (show g-1<g by omega),?_⟩
        zify [show 1≤g by omega]; ring
    · left
      refine ⟨_,_,three hg (by omega : 0<j) (by omega) (show g-1<g by omega),
        one hg (show g+c-j<g by omega),?_⟩
      zify [show 1≤g by omega,show j≤g+c by omega]; ring
  · left
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero b0
    refine ⟨_,_,three hg (by omega) ha (show j<g by omega),
      one hg (show g+c-a<g by omega),?_⟩
    zify [show a≤g+c by omega]; ring

private lemma classify {g n : ℕ} (hg : 5 ≤ g) (hn : n<g^3) :
    (∃ p q, IsPalindrome g p ∧ IsPalindrome g q ∧ p+q=n) ∨
    (∃ u, 1 ≤ u ∧ u < g ∧ n+1 = u*(g+1)) ∨ n=2*g^2+1 := by
  let a := n/g/g
  let b := n/g%g
  let c := n%g
  have ha : a<g := by
    dsimp [a]; rw [Nat.div_lt_iff_lt_mul (by omega),Nat.div_lt_iff_lt_mul (by omega)]
    simpa [pow_succ] using hn
  have e1 : c+g*(n/g)=n := Nat.mod_add_div _ _
  have e2 : b+g*a=n/g := Nat.mod_add_div _ _
  have e : a*g^2+b*g+c=n := by linear_combination e1 + g*e2
  rw [←e]
  exact shortClass hg ha (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))

private lemma five {g a b c : ℕ} (hg : 5 ≤ g) (ha : 0 < a) (hu : a < g) (hb : b < g)
    (hc : c < g) : IsPalindrome g (a*(g^4+1)+b*(g^3+g)+c*g^2) := by
  have eq : Nat.ofDigits g [a,b,c,b,a] = a*(g^4+1)+b*(g^3+g)+c*g^2 := by
    simp [Nat.ofDigits]; ring
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all) (by simp_all; omega)]
  rfl

private abbrev SumThree (g n : ℕ) :=
  ∃ p q r, IsPalindrome g p ∧ IsPalindrome g q ∧ IsPalindrome g r ∧ p+q+r=n

private lemma fill {g n p : ℕ} (hg : 5 ≤ g) (hp : IsPalindrome g p)
    (lo : p+g^2 ≤ n) (hi : n < p+g^3) (ne : n≠p+2*g^2+1) : SumThree g n := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le (show p ≤ n by omega)
  rcases classify hg (show r < g^3 by omega) with ⟨x,y,hx,hy,h⟩ | ⟨u,hu,hug,h⟩ | h
  · exact ⟨p,x,y,hp,hx,hy,by omega⟩
  · have le := Nat.mul_le_mul_right (g+1) (show u ≤ g-1 by omega)
    zify [show 1≤g by omega] at le h lo hr
    nlinarith
  · omega

private lemma fiveDigits {g n : ℕ} (hg : 5 ≤ g) (hn₁ : g^4 ≤ n) (hn₂ : n < g^5) :
    SumThree g n := by
  let a := n/g^4
  let b := (n%g^4)/g^3
  let t := (n%g^4)%g^3
  have ha : 0<a := by dsimp [a]; exact Nat.div_pos hn₁ (by positivity)
  have ha' : a<g := by
    dsimp [a]; rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa [pow_succ,mul_comm] using hn₂
  have hb : b<g := by
    dsimp [b]; rw [Nat.div_lt_iff_lt_mul (by positivity)]
    simpa [pow_succ,mul_comm] using Nat.mod_lt n (show 0<g^4 by positivity)
  have ht : t<g^3 := Nat.mod_lt _ (by positivity)
  have e1 : n%g^4+g^4*a=n := Nat.mod_add_div _ _
  have e2 : t+g^3*b=n%g^4 := Nat.mod_add_div _ _
  have en : n=a*g^4+b*g^3+t := by linear_combination -e1-e2
  clear_value a b t
  clear e1 e2 hn₁ hn₂
  let p := a*(g^4+1)+b*(g^3+g)
  have hp : IsPalindrome g p := by simpa [p] using five hg ha ha' hb (show 0<g by omega)
  by_cases big : p+g^2 ≤ n
  · by_cases ex : n=p+2*g^2+1
    · exact ⟨_,_,_,five hg ha ha' hb (show 1<g by omega),
        three hg (show 0<1 by decide) (by omega) (show 0<g by omega),zeroPal g,
        by rw [ex]; dsimp [p]; ring⟩
    · apply fill hg hp big _ ex
      dsimp [p]; nlinarith
  have hbase : 4*g^2+g+2 < g^3 := by
    nlinarith [Nat.mul_le_mul_right (g^2) hg,
      Nat.mul_le_mul_right g hg]
  have hab : b*g+a < g^2 := by
    have le := Nat.mul_le_mul_right g (show b+1 ≤ g by omega)
    nlinarith
  dsimp [p] at big
  by_cases bz : b=0
  · subst b
    by_cases az : a=1
    · subst a
      apply fill hg (four hg (show 0<g-1 by omega) (by omega) (show g-3<g by omega))
      all_goals zify [show 1≤g by omega,show 3≤g by omega] at *; nlinarith
    · apply fill hg (five hg (show 0<a-1 by omega) (by omega) (show g-1<g by omega)
        (show g-3<g by omega))
      all_goals zify [show 1≤a by omega,show 1≤g by omega,show 3≤g by omega] at *; nlinarith
  · apply fill hg (five hg ha ha' (show b-1<g by omega) (show g-3<g by omega))
    all_goals zify [show 1≤b by omega,show 3≤g by omega] at *; nlinarith

private abbrev digit (g x : ℤ) := 0 ≤ x ∧ x < g
private abbrev dbl (g x : ℤ) := 0 ≤ x ∧ x ≤ 2*g-2

private lemma splitPair {g v : ℤ} (l : ℤ)
    (hv : 2*l ≤ v ∧ v ≤ 2*g-2) :
    ∃ a b, l ≤ a ∧ a < g ∧ l ≤ b ∧ b < g ∧ a+b=v := by
  by_cases h : v-l<g
  · exact ⟨l,v-l,by omega,by omega,by omega,by omega,by omega⟩
  · exact ⟨g-1,v-(g-1),by omega,by omega,by omega,by omega,by omega⟩

private def p5 (g a b c : ℤ) := a*(g^4+1)+b*(g^3+g)+c*g^2
private def p6 (g a b c : ℤ) := a*(g^5+1)+b*(g^4+g)+c*(g^3+g^2)
private def num (g a b c d e f : ℤ) := a*g^5+b*g^4+c*g^3+d*g^2+e*g+f
private abbrev ThreeI (g : ℕ) (v : ℤ) := ∃ n : ℕ, (n : ℤ)=v ∧ SumThree g n

private lemma pal5I {g : ℕ} (hg : 5≤g) {a b c : ℤ} (ha : 0<a ∧ a<g)
    (hb : digit g b) (hc : digit g c) :
    ∃ n : ℕ, (n : ℤ)=p5 g a b c ∧ IsPalindrome g n := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤a by omega)
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  obtain ⟨c,rfl⟩ := Int.eq_ofNat_of_zero_le hc.1
  exact ⟨a*(g^4+1)+b*(g^3+g)+c*g^2,by simp [p5],five hg (by omega) (by omega) (by have := hb.2; omega) (by have := hc.2; omega)⟩

private lemma pal6I {g : ℕ} (hg : 5≤g) {a b c : ℤ} (ha : 0<a ∧ a<g)
    (hb : digit g b) (hc : digit g c) :
    ∃ n : ℕ, (n : ℤ)=p6 g a b c ∧ IsPalindrome g n := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤a by omega)
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  obtain ⟨c,rfl⟩ := Int.eq_ofNat_of_zero_le hc.1
  have eq : Nat.ofDigits g [a,b,c,c,b,a] = a*(g^5+1)+b*(g^4+g)+c*(g^3+g^2) := by
    simp [Nat.ofDigits]; ring
  refine ⟨a*(g^5+1)+b*(g^4+g)+c*(g^3+g^2),by simp [p6],?_⟩
  rw [← eq, IsPalindrome, Nat.digits_ofDigits _ (by omega) _ (by simp_all [digit])
    (by simp_all [digit]; omega)]
  rfl

private lemma twoFives {g : ℕ} (hg : 5≤g) {a b c : ℤ} (ha : 2≤a ∧ a≤2*g-2)
    (hb : dbl g b) (hc : dbl g c) :
    ∃ p q : ℕ, (p:ℤ)+q=p5 g a b c ∧ IsPalindrome g p ∧ IsPalindrome g q := by
  obtain ⟨a₁,a₂,ha₁,ha₁',ha₂,ha₂',rfl⟩ := splitPair 1 ha
  obtain ⟨b₁,b₂,hb₁,hb₁',hb₂,hb₂',rfl⟩ := splitPair 0 hb
  obtain ⟨c₁,c₂,hc₁,hc₁',hc₂,hc₂',rfl⟩ := splitPair 0 hc
  obtain ⟨p,hp,hP⟩ := pal5I hg ⟨ha₁,ha₁'⟩ ⟨hb₁,hb₁'⟩ ⟨hc₁,hc₁'⟩
  obtain ⟨q,hq,hQ⟩ := pal5I hg ⟨ha₂,ha₂'⟩ ⟨hb₂,hb₂'⟩ ⟨hc₂,hc₂'⟩
  exact ⟨p,q,by rw [hp,hq]; dsimp [p5]; ring,hP,hQ⟩

private lemma residue {g : ℤ} (hg : 0<g) (lo x : ℤ) :
    ∃ y k : ℤ, lo ≤ y ∧ y < lo+g ∧ y=x+k*g := by
  refine ⟨lo+(x-lo)%g,-((x-lo)/g),?_,?_,?_⟩
  · have := Int.emod_nonneg (x-lo) (by omega : g≠0); omega
  · have := Int.emod_lt_of_pos (x-lo) hg; omega
  · linarith [Int.emod_add_mul_ediv (x-lo) g]

private lemma boundsCarry {g s d k : ℤ} (hg : 0<g) (hs : 0 ≤ s ∧ s < 3*g)
    (hd : digit g d) (h : s=d+k*g) : 0≤k ∧ k≤2 := by
  obtain ⟨hd₁,hd₂⟩ := hd
  constructor
  · by_contra! bad
    have := mul_le_mul_of_nonneg_right (show k≤ -1 by omega) hg.le
    linarith
  · by_contra! bad
    have := mul_le_mul_of_nonneg_right (show 3≤k by omega) hg.le
    linarith

private lemma center {g t d k : ℤ} (hg : 5≤g) (ht : 1≤t ∧ t≤g) (hd : digit g d)
    (hk : 0≤k ∧ k≤2) :
    ∃ c z j : ℤ, digit g c ∧ dbl g z ∧ c+j=t ∧ c+z+k=d+j*g := by
  obtain ⟨hd₁,hd₂⟩ := hd
  by_cases lo : 0≤d+g-t+1-k
  · by_cases hi : d+g-t+1-k≤2*g-2
    · exact ⟨t-1,d+g-t+1-k,1,by constructor <;> omega,⟨lo,hi⟩,by omega,by ring⟩
    · refine ⟨t,d-t-k,0,⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,by ring⟩
  · refine ⟨t-2,d+2*g-t+2-k,2,⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,by ring⟩

private lemma finish655 {g : ℕ} (hg : 5≤g) {a b c d e f x y X k₁ k₅ : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) (hf : digit g f)
    (hx : 0<x ∧ x<g) (hy : digit g y) (hX : 2≤X ∧ X≤2*g-2)
    (h₀ : x+X=f+k₁*g) (h₄ : y+X+1=b+k₅*g) (h₅ : x+k₅=a) :
    ThreeI g (num g a b c d e f) := by
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hy₁,hy₂⟩ := hy
  obtain ⟨he₁,he₂⟩ := he
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  have hk₁ := boundsCarry (by omega) ⟨by omega,by omega⟩ hf h₀
  obtain ⟨Y,k₂,hY₁,hY₂,hY⟩ := residue (g:=(g:ℤ)) (by omega) c (e-y-k₁)
  have h₁ : y+Y+k₁=e+k₂*g := by linarith
  have hk₂ := boundsCarry (by omega) ⟨by omega,by omega⟩ ⟨he₁,he₂⟩ h₁
  obtain ⟨z,Z,k₃,hz,hZ,hz',h₂⟩ := center hg' (t:=c+g-Y) ⟨by omega,by omega⟩ hd hk₂
  obtain ⟨p,hp,hP⟩ := pal6I hg hx ⟨hy₁,hy₂⟩ hz
  obtain ⟨q,r,hqr,hQ,hR⟩ := twoFives hg (b:=Y) hX ⟨by omega,by omega⟩ hZ
  refine ⟨p+q+r,?_,p,q,r,hP,hQ,hR,rfl⟩
  push_cast
  rw [add_assoc,hp,hqr]
  dsimp [p6,p5,num]
  linear_combination h₀ + (g:ℤ)*h₁ + (g:ℤ)^2*h₂ + (g:ℤ)^3*hz' + (g:ℤ)^4*h₄ + (g:ℤ)^5*h₅

private lemma pal3I {g : ℕ} (hg : 5≤g) {a b : ℤ} (ha : 0<a ∧ a<g) (hb : digit g b) :
    ∃ n : ℕ, (n : ℤ)=a*(g^2+1)+b*g ∧ IsPalindrome g n := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤a by omega)
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  exact ⟨a*(g^2+1)+b*g,by simp,three hg (by omega) (by omega) (by have := hb.2; omega)⟩

private lemma general553 {g : ℕ} (hg : 5≤g) {b c d e f z k₁ : ℤ}
    (hb : digit g b) (hc : digit g c) (hd : digit g d) (he : digit g e) (hf : digit g f)
    (hz : 0<z ∧ z<g) (safe : z+2≤g ∨ 0<d)
    (h₀ : (g:ℤ)+b-1+z=f+k₁*g) : ThreeI g (num g 1 b c d e f) := by
  obtain ⟨hb₁,hb₂⟩ := hb
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  have hk₁ := boundsCarry (by omega) ⟨by omega,by omega⟩ hf h₀
  obtain ⟨w,k₂,hw₁,hw₂,hw⟩ := residue (g:=(g:ℤ)) (by omega) 0 (e-(g+c-1)-k₁)
  have h₁ : (g:ℤ)+c-1+w+k₁=e+k₂*g := by linarith
  have hk₂ := boundsCarry (by omega) ⟨by omega,by omega⟩ he h₁
  obtain ⟨p,q,hpq,hP,hQ⟩ := twoFives hg (a:=(g:ℤ)+b-1) (b:=(g:ℤ)+c-1)
    (c:=(g:ℤ)+d-k₂-z) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  obtain ⟨r,hr,hR⟩ := pal3I hg hz ⟨hw₁,by omega⟩
  refine ⟨p+q+r,?_,p,q,r,hP,hQ,hR,rfl⟩
  push_cast; rw [hpq,hr]; dsimp [num,p5]
  linear_combination h₀ + (g:ℤ)*h₁

private def edgeOne (g b d f : ℤ) : Prop :=
  (b ≤ 3 ∧ (f=b-1 ∨ f=g+b-1)) ∨ (b ≤ 4 ∧ d=0 ∧ (f=b-2 ∨ f=g+b-2))
private def edgeTwo (b f : ℤ) : Prop :=
  (b=0 ∧ (f=1 ∨ f=2)) ∨ (b=1 ∧ f=2)

private lemma leadingOne {g : ℕ} (hg : 5≤g) {b c d e f : ℤ}
    (hb : digit g b) (hc : digit g c) (hd : digit g d) (he : digit g e) (hf : digit g f)
    (good : ¬edgeOne g b d f) : ThreeI g (num g 1 b c d e f) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨z,k,hz₁,hz₂,hz⟩ := residue (g:=(g:ℤ)) (by omega) 0 (f-(g+b-1))
  have h₀ : (g:ℤ)+b-1+z=f+k*g := by linarith
  by_cases ok : 0<z ∧ (z+2≤g ∨ 0<d)
  · exact general553 hg hb hc hd he hf ⟨ok.1,by omega⟩ ok.2 h₀
  obtain ⟨hb₁,hb₂⟩ := hb
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨hf₁,hf₂⟩ := hf
  have hk := boundsCarry (by omega) ⟨by omega,by omega⟩ ⟨hf₁,hf₂⟩ h₀
  have hcase : 2≤f-1 ∧ f≤b := by
    dsimp [edgeOne] at good
    obtain ⟨kl,ku⟩ := hk
    interval_cases k <;> simp_all <;> omega
  exact finish655 hg hc ⟨hd₁,hd₂⟩ he ⟨hf₁,hf₂⟩ (x:=1) (y:=b-f) (X:=f-1)
    (k₁:=0) (k₅:=0) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    ⟨by omega,by omega⟩ (by ring) (by ring) (by ring)

private lemma leadingMany {g : ℕ} (hg : 5≤g) {a b c d e f : ℤ}
    (ha : 2≤a ∧ a<g) (hb : digit g b) (hc : digit g c) (hd : digit g d)
    (he : digit g e) (hf : digit g f) (good : a≠2 ∨ ¬edgeTwo b f) :
    ThreeI g (num g a b c d e f) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hb₁,hb₂⟩ := hb
  obtain ⟨X,k,hX₁,hX₂,hX⟩ := residue (g:=(g:ℤ)) (by omega) b (f-(a-1))
  by_cases h : 2≤X
  · exact finish655 hg hc hd he hf (x:=a-1) (y:=b+g-X-1) (X:=X) (k₁:=k) (k₅:=1)
      ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨h,by omega⟩ (by linarith) (by ring) (by ring)
  have h₀ : a-1+X=f+k*g := by linarith
  obtain ⟨hf₁,hf₂⟩ := hf
  have hk := boundsCarry (by omega) ⟨by omega,by omega⟩ ⟨hf₁,hf₂⟩ h₀
  have a₂ : 2<a := by
    dsimp [edgeTwo] at good
    obtain ⟨kl,ku⟩ := hk
    interval_cases k <;> simp_all <;> omega
  exact finish655 hg hc hd he ⟨hf₁,hf₂⟩ (x:=a-2) (y:=b+g-X-2) (X:=X+g+1)
    (k₁:=k+1) (k₅:=2) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    ⟨by omega,by omega⟩ (by linarith) (by ring) (by ring)

private lemma pal4I {g : ℕ} (hg : 5≤g) {a b : ℤ} (ha : 0<a ∧ a<g) (hb : digit g b) :
    ∃ n : ℕ, (n : ℤ)=a*(g^3+1)+b*g*(g+1) ∧ IsPalindrome g n := by
  obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le (show 0≤a by omega)
  obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hb.1
  exact ⟨a*(g^3+1)+b*g*(g+1),by simp,four hg (by omega) (by omega) (by have := hb.2; omega)⟩

private lemma form553 {g : ℕ} (hg : 5≤g) {v X Y Z z w : ℤ}
    (hX : 2≤X ∧ X≤2*g-2) (hY : dbl g Y) (hZ : dbl g Z)
    (hz : 0<z ∧ z<g) (hw : digit g w) (eq : p5 g X Y Z + z*(g^2+1)+w*g=v) :
    ThreeI g v := by
  obtain ⟨p,q,hpq,hP,hQ⟩ := twoFives hg hX hY hZ
  obtain ⟨r,hr,hR⟩ := pal3I hg hz hw
  exact ⟨p+q+r,by push_cast; rw [hpq,hr]; linarith,p,q,r,hP,hQ,hR,rfl⟩

private lemma form554 {g : ℕ} (hg : 5≤g) {v X Y Z z w : ℤ}
    (hX : 2≤X ∧ X≤2*g-2) (hY : dbl g Y) (hZ : dbl g Z)
    (hz : 0<z ∧ z<g) (hw : digit g w) (eq : p5 g X Y Z + z*(g^3+1)+w*g*(g+1)=v) :
    ThreeI g v := by
  obtain ⟨p,q,hpq,hP,hQ⟩ := twoFives hg hX hY hZ
  obtain ⟨r,hr,hR⟩ := pal4I hg hz hw
  exact ⟨p+q+r,by push_cast; rw [hpq,hr]; linarith,p,q,r,hP,hQ,hR,rfl⟩

/- In a 6+5+4 digit pattern, the free middle digit w must fit the three
digit intervals for S-w, T-w and U+2*w as well as its own interval. -/
private lemma form654 {g : ℕ} (hg : 5≤g) {v x y z B S T U : ℤ}
    (hx : 0<x ∧ x<g) (hy : 0<y ∧ y<g) (hz : 0<z ∧ z<g) (hB : digit g B)
    (hS : dbl g S) (hT : dbl g T) (hST : S-T<g ∧ T-S<g)
    (hu₁ : 0≤2*((g:ℤ)-1)+U ∧ 0≤2*S+U ∧ 0≤2*T+U)
    (hu₂ : U<g ∧ 2*(S-g+1)+U<g ∧ 2*(T-g+1)+U<g)
    (eq : ∀ w : ℤ, p6 g x B (T-w)+p5 g y w (U+2*w)+
      (z*(g^3+1)+(S-w)*g*(g+1))=v) : ThreeI g v := by
  obtain ⟨hs₁,hs₂⟩ := hS
  obtain ⟨ht₁,ht₂⟩ := hT
  let w := max 0 (max (S-g+1) (max (T-g+1) ((1-U)/2)))
  have hw : digit g w := by dsimp [w,digit]; constructor <;> omega
  have hsw : digit g (S-w) := by dsimp [w,digit]; constructor <;> omega
  have htw : digit g (T-w) := by dsimp [w,digit]; constructor <;> omega
  have huw : digit g (U+2*w) := by dsimp [w,digit]; constructor <;> omega
  obtain ⟨p,hp,hP⟩ := pal6I hg hx hB htw
  obtain ⟨q,hq,hQ⟩ := pal5I hg hy hw huw
  obtain ⟨r,hr,hR⟩ := pal4I hg hz hsw
  exact ⟨p+q+r,by push_cast; rw [hp,hq,hr]; exact eq w,p,q,r,hP,hQ,hR,rfl⟩

private lemma exceptional0 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (1) (0) (c) (d) (e) ((g:ℤ) - 1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ - c + e ∧ 0 ≤ c - 1) ∨
      (0 ≤ c - e - 1) ∨
      (0 ≤ - c ∧ 0 ≤ (g:ℤ) + c - e - 3 ∧ 0 ≤ (g:ℤ) + c + d - e - 4) ∨
      (0 ≤ - (g:ℤ) - c + e + 2 ∧ 0 ≤ - c) ∨
      (0 ≤ - c ∧ 0 ≤ - d + 1 ∧ 0 ≤ (g:ℤ) + c - e - 3) := by omega
  rcases h with h | h | h | h | h
  · apply form553 hg (X:=(g:ℤ)) (Y:=c - 1) (Z:=d + 1) (z:=(g:ℤ) - 1) (w:=- c + e)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ)) (Y:=c - 1) (Z:=d) (z:=(g:ℤ) - 1) (w:=(g:ℤ) - c + e)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 2) (Y:=2*(g:ℤ) + c - 2) (Z:=(g:ℤ) + c + d - e - 4) (z:=1) (w:=- c + e + 2)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 2) (Y:=2*(g:ℤ) + c - 2) (Z:=2*(g:ℤ) + c + d - e - 3) (z:=1) (w:=- (g:ℤ) - c + e + 2)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ) - 2) (Y:=2*(g:ℤ) + c - 2) (Z:=2*(g:ℤ) + d - 3) (z:=1) (w:=- c + e + 2)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional1 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (1) (1) (c) (d) (e) (0)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ c - e ∧ 0 ≤ c - 1) ∨
      (0 ≤ - c + e - 1 ∧ 0 ≤ c - 1) ∨
      (0 ≤ - c ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ (g:ℤ) + c + d - e - 3) ∨
      (0 ≤ - (g:ℤ) - c + e + 1) ∨
      (0 ≤ - c ∧ 0 ≤ - d + 1 ∧ 0 ≤ (g:ℤ) + c - e - 2) := by omega
  rcases h with h | h | h | h | h
  · apply form553 hg (X:=(g:ℤ) + 1) (Y:=c - 1) (Z:=d) (z:=(g:ℤ) - 1) (w:=(g:ℤ) - c + e - 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ) + 1) (Y:=c - 1) (Z:=d + 1) (z:=(g:ℤ) - 1) (w:=- c + e - 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 1) (Y:=2*(g:ℤ) + c - 2) (Z:=(g:ℤ) + c + d - e - 3) (z:=1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 1) (Y:=2*(g:ℤ) + c - 2) (Z:=2*(g:ℤ) + c + d - e - 2) (z:=1) (w:=- (g:ℤ) - c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ) - 1) (Y:=2*(g:ℤ) + c - 2) (Z:=2*(g:ℤ) + d - 3) (z:=1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional2 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (1) (2) (c) (d) (e) (1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ e - 1 ∧ 0 ≤ c - d + e - 2) ∨
      (0 ≤ c - e) ∨
      (0 ≤ - c + d + e - 2 ∧ 0 ≤ e - 1 ∧ 0 ≤ c + d - e + 2) ∨
      (0 ≤ - c ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ (g:ℤ) + c + d - e - 3) := by omega
  rcases h with h | h | h | h
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=0) (S:=e - 1) (T:=c) (U:=(g:ℤ) - c + d - e + 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=0) (S:=(g:ℤ) + e - 1) (T:=c) (U:=- c + d - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=0) (S:=e - 1) (T:=c + 1) (U:=- c + d - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ)) (Y:=2*(g:ℤ) + c - 2) (Z:=(g:ℤ) + c + d - e - 3) (z:=1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional3 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (1) (3) (c) (d) (e) (2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ e - 1 ∧ 0 ≤ c - d + e - 2) ∨
      (0 ≤ c - e) ∨
      (0 ≤ - c + d + e - 2 ∧ 0 ≤ e - 1 ∧ 0 ≤ c + d - e + 2) ∨
      (0 ≤ - c ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ (g:ℤ) + c + d - e - 3) := by omega
  rcases h with h | h | h | h
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=0) (S:=e - 1) (T:=c) (U:=(g:ℤ) - c + d - e + 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=0) (S:=(g:ℤ) + e - 1) (T:=c) (U:=- c + d - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=0) (S:=e - 1) (T:=c + 1) (U:=- c + d - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) + 1) (Y:=2*(g:ℤ) + c - 2) (Z:=(g:ℤ) + c + d - e - 3) (z:=1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional4 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (0) (c) (0) (e) ((g:ℤ) - 2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ - c + e + 1 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ c - e - 1) ∨
      (0 ≤ - c + e - 1) := by omega
  rcases h with h | h | h
  · apply form553 hg (X:=(g:ℤ) - 1) (Y:=(g:ℤ) + c - 2) (Z:=(g:ℤ)) (z:=(g:ℤ) - 1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ)) (Y:=c - 1) (Z:=1) (z:=(g:ℤ) - 2) (w:=(g:ℤ) - c + e)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ) - 1) (Y:=c) (Z:=(g:ℤ) + c - e + 1) (z:=(g:ℤ) - 1) (w:=- c + e - 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional5 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (1) (c) (0) (e) ((g:ℤ) - 1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ - c + e + 1 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ c - e - 1) ∨
      (0 ≤ - c + e - 1) := by omega
  rcases h with h | h | h
  · apply form553 hg (X:=(g:ℤ)) (Y:=(g:ℤ) + c - 2) (Z:=(g:ℤ)) (z:=(g:ℤ) - 1) (w:=- c + e + 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form553 hg (X:=(g:ℤ) + 1) (Y:=c - 1) (Z:=1) (z:=(g:ℤ) - 2) (w:=(g:ℤ) - c + e)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)
  · apply form554 hg (X:=(g:ℤ)) (Y:=c) (Z:=(g:ℤ) + c - e + 1) (z:=(g:ℤ) - 1) (w:=- c + e - 1)
    all_goals first | (dsimp [p5,num]; ring) | (constructor <;> omega)

private lemma exceptional6 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (2) (c) (0) (e) (0)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ e - 1 ∧ 0 ≤ (g:ℤ) - c + e - 3) ∨
      (0 ≤ c - e + 1 ∧ 0 ≤ 2*(g:ℤ) - c - e - 3) := by omega
  rcases h with h | h
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 2) (B:=0) (S:=e - 1) (T:=c + 1) (U:=(g:ℤ) - c - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 2) (B:=0) (S:=(g:ℤ) + e - 1) (T:=c + 1) (U:=- c - e - 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional7 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (3) (c) (0) (e) (1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ (g:ℤ) - c + e - 2 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ e - 2 ∧ 0 ≤ c + e - 3) ∨
      (0 ≤ - (g:ℤ) + c - e + 2 ∧ 0 ≤ - (g:ℤ) + c + 1) := by omega
  rcases h with h | h | h
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=0) (S:=(g:ℤ) + e - 1) (T:=(g:ℤ) + c - 1) (U:=- c - e + 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=1) (z:=(g:ℤ) - 1) (B:=1) (S:=e - 2) (T:=c) (U:=(g:ℤ) - c - e + 2)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 2) (B:=1) (S:=(g:ℤ) + e - 2) (T:=- (g:ℤ) + c + 1) (U:=(g:ℤ) - c - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional8 {g : ℕ} (hg : 5≤g) {c e : ℤ}
    (hc : digit g c) (he : digit g e) :
    ThreeI g (num g (1) (4) (c) (0) (e) (2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ (g:ℤ) - c + e - 2 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ e - 2 ∧ 0 ≤ c + e - 3) ∨
      (0 ≤ - (g:ℤ) + c - e + 2 ∧ 0 ≤ - (g:ℤ) + c + 1) := by omega
  rcases h with h | h | h
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=0) (S:=(g:ℤ) + e - 1) (T:=(g:ℤ) + c - 1) (U:=- c - e + 1)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=1) (S:=e - 2) (T:=c) (U:=(g:ℤ) - c - e + 2)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=3) (z:=(g:ℤ) - 2) (B:=1) (S:=(g:ℤ) + e - 2) (T:=- (g:ℤ) + c + 1) (U:=(g:ℤ) - c - e)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional9 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (2) (0) (c) (d) (e) (1)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ c - d + e + 7 ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ 3*(g:ℤ) - c + d - e - 10) ∨
      (0 ≤ - c + e ∧ 0 ≤ e - 1 ∧ 0 ≤ (g:ℤ) - c - d + e - 2 ∧ 0 ≤ (g:ℤ) + c - d + e - 4) ∨
      (0 ≤ (g:ℤ) - c + d - e + 2 ∧ 0 ≤ (g:ℤ) + c - e - 2) ∨
      (0 ≤ (g:ℤ) - c + d - e + 6 ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ 2*(g:ℤ) + c - d + e - 9) := by omega
  rcases h with h | h | h | h
  · apply form654 hg (x:=1) (y:=4) (z:=(g:ℤ) - 4) (B:=(g:ℤ) - 5) (S:=e + 4) (T:=c + 3) (U:=(g:ℤ) - c + d - e - 8)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 1) (z:=1) (B:=0) (S:=e - 1) (T:=(g:ℤ) + c - 2) (U:=- c + d - e + 3)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 2) (z:=2) (B:=1) (S:=(g:ℤ) + e - 2) (T:=(g:ℤ) + c - 3) (U:=- (g:ℤ) - c + d - e + 4)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 4) (z:=4) (B:=3) (S:=(g:ℤ) + e - 4) (T:=(g:ℤ) + c - 5) (U:=- (g:ℤ) - c + d - e + 8)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional10 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (2) (0) (c) (d) (e) (2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ c - d + e + 6 ∧ 0 ≤ (g:ℤ) + c - e - 3 ∧ 0 ≤ 3*(g:ℤ) - c + d - e - 9) ∨
      (0 ≤ - c + e + 2 ∧ 0 ≤ (g:ℤ) - c - 2 ∧ 0 ≤ 2*(g:ℤ) - c + d - e - 6) ∨
      (0 ≤ - (g:ℤ) + e + 2 ∧ 0 ≤ - (g:ℤ) + c - d + e + 1) ∨
      (0 ≤ (g:ℤ) - c + d - e + 5 ∧ 0 ≤ (g:ℤ) + c - e - 3 ∧ 0 ≤ 2*(g:ℤ) + c - d + e - 8) := by omega
  rcases h with h | h | h | h
  · apply form654 hg (x:=1) (y:=4) (z:=(g:ℤ) - 3) (B:=(g:ℤ) - 5) (S:=e + 4) (T:=c + 2) (U:=(g:ℤ) - c + d - e - 7)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=(g:ℤ) - 4) (S:=e + 3) (T:=(g:ℤ) + c) (U:=- c + d - e - 4)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=(g:ℤ) - 3) (S:=- (g:ℤ) + e + 2) (T:=c) (U:=2*(g:ℤ) - c + d - e - 2)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 3) (z:=4) (B:=2) (S:=(g:ℤ) + e - 3) (T:=(g:ℤ) + c - 5) (U:=- (g:ℤ) - c + d - e + 7)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)

private lemma exceptional11 {g : ℕ} (hg : 5≤g) {c d e : ℤ}
    (hc : digit g c) (hd : digit g d) (he : digit g e) :
    ThreeI g (num g (2) (1) (c) (d) (e) (2)) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  have h : (0 ≤ (g:ℤ) - c + d - e + 6 ∧ 0 ≤ (g:ℤ) + c - e - 2 ∧ 0 ≤ 2*(g:ℤ) + c - d + e - 9) ∨
      (0 ≤ - c + e + 1 ∧ 0 ≤ (g:ℤ) - c - 2 ∧ 0 ≤ 2*(g:ℤ) - c + d - e - 5) ∨
      (0 ≤ c - d + e + 3 ∧ 0 ≤ (g:ℤ) + c - e - 2) := by omega
  rcases h with h | h | h
  · apply form654 hg (x:=1) (y:=(g:ℤ) - 3) (z:=4) (B:=3) (S:=(g:ℤ) + e - 4) (T:=(g:ℤ) + c - 5) (U:=- (g:ℤ) - c + d - e + 8)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=2) (z:=(g:ℤ) - 1) (B:=(g:ℤ) - 3) (S:=e + 2) (T:=(g:ℤ) + c) (U:=- c + d - e - 3)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
  · apply form654 hg (x:=1) (y:=3) (z:=(g:ℤ) - 2) (B:=(g:ℤ) - 3) (S:=e + 2) (T:=c + 1) (U:=(g:ℤ) - c + d - e - 4)
    all_goals first | (intro w; dsimp [p5,p6,num]; ring) | (repeat' constructor <;> omega)
private lemma allSix {g : ℕ} (hg : 5≤g) {a b c d e f : ℤ}
    (ha : 0<a ∧ a<g) (hb : digit g b) (hc : digit g c) (hd : digit g d)
    (he : digit g e) (hf : digit g f) : ThreeI g (num g a b c d e f) := by
  have hg' : (5:ℤ)≤g := by exact_mod_cast hg
  have hb₁ := hb.1
  have hf₁ := hf.1
  have hf₂ := hf.2
  by_cases h₁ : a=1
  · subst a
    by_cases good : ¬edgeOne g b d f
    · exact leadingOne hg hb hc hd he hf good
    · have h := Classical.not_not.mp good
      rcases h with ⟨hle,hlast⟩ | ⟨hle,rfl,hlast⟩
      · interval_cases b
        all_goals first
          | (convert exceptional0 hg hc hd he using 2 <;> omega)
          | (convert exceptional1 hg hc hd he using 2 <;> omega)
          | (convert exceptional2 hg hc hd he using 2 <;> omega)
          | (convert exceptional3 hg hc hd he using 2 <;> omega)
      · interval_cases b
        all_goals first
          | (convert exceptional4 hg hc he using 2 <;> omega)
          | (convert exceptional5 hg hc he using 2 <;> omega)
          | (convert exceptional6 hg hc he using 2 <;> omega)
          | (convert exceptional7 hg hc he using 2 <;> omega)
          | (convert exceptional8 hg hc he using 2 <;> omega)
  · by_cases good : a≠2 ∨ ¬edgeTwo b f
    · exact leadingMany hg ⟨by omega,ha.2⟩ hb hc hd he hf good
    · push Not at good
      obtain ⟨rfl,hh⟩ := good
      rcases hh with ⟨rfl,rfl|rfl⟩ | ⟨rfl,rfl⟩
      · exact exceptional9 hg hc hd he
      · exact exceptional10 hg hc hd he
      · exact exceptional11 hg hc hd he

private lemma sixDigits {g n : ℕ} (hg : 5≤g) (lo : g^5≤n) (hi : n<g^6) : SumThree g n := by
  let n₁ := n/g
  let n₂ := n₁/g
  let n₃ := n₂/g
  let n₄ := n₃/g
  let a := n₄/g
  let b := n₄%g
  let c := n₃%g
  let d := n₂%g
  let e := n₁%g
  let f := n%g
  have r₀ : f+g*n₁=n := Nat.mod_add_div _ _
  have r₁ : e+g*n₂=n₁ := Nat.mod_add_div _ _
  have r₂ : d+g*n₃=n₂ := Nat.mod_add_div _ _
  have r₃ : c+g*n₄=n₃ := Nat.mod_add_div _ _
  have r₄ : b+g*a=n₄ := Nat.mod_add_div _ _
  have en : a*g^5+b*g^4+c*g^3+d*g^2+e*g+f=n := by
    linear_combination r₀ + g*r₁ + g^2*r₂ + g^3*r₃ + g^4*r₄
  have adiv : a=n/g^5 := by dsimp [a,n₁,n₂,n₃,n₄]; rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul]; congr 1; ring
  have ha : 0<a := by rw [adiv]; exact Nat.div_pos lo (by positivity)
  have ha' : a<g := by
    rw [adiv,Nat.div_lt_iff_lt_mul (by positivity)]
    simpa [pow_succ,mul_comm] using hi
  have digitMod (x : ℕ) : digit g (x%g : ℕ) := ⟨by positivity,by exact_mod_cast Nat.mod_lt x (show 0<g by omega)⟩
  obtain ⟨m,hm,hM⟩ := allSix hg (a:=(a:ℤ)) ⟨by exact_mod_cast ha,by exact_mod_cast ha'⟩
    (digitMod n₄) (digitMod n₃) (digitMod n₂) (digitMod n₁) (digitMod n)
  have hn : (n:ℤ)=num g a b c d e f := by dsimp [num]; exact_mod_cast en.symm
  have heq : m=n := by exact_mod_cast hm.trans hn.symm
  rwa [←heq]

end G95Med

private theorem h2_h1_proof : OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1.H1 := by
  intro g hg n lo hi
  by_cases h : n<g^5
  · exact G95Med.fiveDigits hg lo h
  · exact G95Med.sixDigits hg (by omega) hi

end

section
namespace G95Long
open Green95

def Pad (g l : ℕ) (v : ℤ) : Prop :=
  ∃ w : List ℕ, w.length=l ∧ w.reverse=w ∧ (∀ d ∈ w, d<g) ∧ ((Nat.ofDigits g w : ℕ) : ℤ)=v

def actual (g : ℕ) (v : ℤ) := ∃ n : ℕ, (n:ℤ)=v ∧ IsPalindrome g n

def triple (f h k : ℤ → Prop) (n : ℤ) := ∃ a b c, f a ∧ h b ∧ k c ∧ a+b+c=n

def wt (g : ℕ) (i : ℕ) : ℤ := (g:ℤ)^(i+1)+1

lemma wrap {g i : ℕ} (hg : 5≤g) {v x : ℤ} (h : Pad g i v) (hx : 0≤x ∧ x<g) :
    Pad g (i+2) (x*wt g i+g*v) ∧ (0<x → actual g (x*wt g i+g*v)) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  obtain ⟨w,hw,rev,ds,rfl⟩ := h
  let W := x :: (w ++ [x])
  have len : W.length=i+2 := by simp [W,hw]
  have symm : W.reverse=W := by simp [W,rev]
  have valid : ∀ d ∈ W, d<g := by
    simp only [W,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
    rintro d (rfl|h|rfl)
    · omega
    · exact ds _ h
    · omega
  have eq : ((Nat.ofDigits g W : ℕ) : ℤ)=(x:ℤ)*wt g i+g*Nat.ofDigits g w := by
    simp only [W,Nat.ofDigits_cons,Nat.ofDigits_append,List.length_cons,hw,Nat.ofDigits_nil,
      mul_zero,add_zero,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,wt,pow_succ]
    ring
  refine ⟨⟨W,len,symm,valid,eq⟩,fun pos => ⟨Nat.ofDigits g W,eq,?_⟩⟩
  rw [IsPalindrome,Nat.digits_ofDigits _ (by omega) _ valid (by simp [W]; omega)]
  exact symm

def inside (g a b c : ℕ) := triple (Pad g a) (Pad g b) (Pad g c)
def done (g : ℕ) := triple (actual g) (actual g) (actual g)

lemma wrapThree {g a b c : ℕ} (hg : 5≤g) {q x y z : ℤ} (iq : inside g a b c q)
    (hx : 0≤x ∧ x<g) (hy : 0≤y ∧ y<g) (hz : 0≤z ∧ z<g) :
    let n := x*wt g a+y*wt g b+z*wt g c+g*q
    inside g (a+2) (b+2) (c+2) n ∧ (0<x → 0<y → 0<z → done g n) := by
  obtain ⟨u,v,w,hu,hv,hw,rfl⟩ := iq
  have h1 := wrap hg hu hx
  have h2 := wrap hg hv hy
  have h3 := wrap hg hw hz
  exact ⟨⟨_,_,_,h1.1,h2.1,h3.1,by ring⟩,
    fun X Y Z => ⟨_,_,_,h1.2 X,h2.2 Y,h3.2 Z,by ring⟩⟩

private lemma align {g m : ℤ} (hg : 5≤g) (hm : m=0 ∨ m=1) (n x y : ℤ) :
    ∃ Y Z k : ℤ, y-m ≤ Y ∧ Y ≤ y+m ∧ (m≤y ∧ y<g → m≤Y ∧ Y<g) ∧
      m ≤ Z ∧ Z<g ∧ x+Y+Z=n+k*g := by
  let r := (n-x-y)%g
  let k := -((n-x-y)/g)
  have hr₁ : 0≤r := Int.emod_nonneg _ (by omega)
  have hr₂ : r<g := Int.emod_lt_of_pos _ (by omega)
  have eq : x+y+r=n+k*g := by
    dsimp [r,k]; linarith [Int.emod_add_mul_ediv (n-x-y) g]
  by_cases h : m≤r
  · exact ⟨y,r,k,by omega,by omega,id,h,hr₂,eq⟩
  · have rz : r=0 := by omega
    by_cases endrow : y=g-1
    · exact ⟨y-1,1,k,by omega,by omega,by omega,by omega,by omega,by linarith⟩
    · exact ⟨y+1,g-1,k+1,by omega,by omega,by omega,by omega,by omega,by linarith⟩

private lemma walk {a b : ℤ} {P : ℤ → Prop} (h : a≤b) (base : P a)
    (step : ∀ j, a≤j → j<b → P j → P (j+1)) : P b := by
  obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le (show 0≤b-a by omega)
  have aux : ∀ i : ℕ, i≤k → P (a+i) := by
    intro i; induction i with
    | zero => intro _; simpa using base
    | succ i ih =>
      intro hi
      simpa [Nat.cast_succ,add_assoc] using step (a+i) (by omega) (by omega) (ih (by omega))
  simpa [show a+(k:ℤ)=b by omega] using aux k le_rfl

/-- For each pair of outer digits choose the third to match the units column.
The intervals of possible inner quotients overlap along each row and at the
transition to the next row. All three digit lengths may be different. -/
theorem grid {g m A B C lo hi L U n : ℤ} (hg : 5≤g) (hm : m=0 ∨ m=1) (hlh : lo≤hi)
    (hB : 0≤B) (hC : 0≤C) (a' b' c' : ℤ)
    (hA' : A=g*a'+1) (hB' : B=g*b'+1) (hC' : C=g*c'+1)
    (dy : (1+2*m)*B+(g-1-m)*C ≤ g*(U-L+1))
    (dx : lo=hi ∨ A+(3*m+1-g)*B+(g-1-m)*C ≤ g*(U-L+1))
    (start : lo*A+2*m*B+(g-1)*C+g*L ≤ n)
    (stop : n ≤ hi*A+(g-1-m)*B+m*C+g*U) :
    ∃ x y z q, lo≤x ∧ x≤hi ∧ m≤y ∧ y<g ∧ m≤z ∧ z<g ∧ L≤q ∧ q≤U ∧
      n=x*A+y*B+z*C+g*q := by
  choose Y Z K Yn Yp Yv Zn Zp E using align hg hm n
  let Q (x y : ℤ) := -(K x y+x*a'+Y x y*b'+Z x y*c')
  have eq (x y : ℤ) : n=x*A+Y x y*B+Z x y*C+g*(Q x y) := by
    dsimp [Q]; rw [hA',hB',hC']; linear_combination -(E x y)
  by_contra fail
  have jump (x y : ℤ) (hx : lo≤x ∧ x≤hi) (hy : m≤y ∧ y<g)
      (hL : L≤Q x y) : U<Q x y := by
    by_contra! h
    exact fail ⟨x,Y x y,Z x y,Q x y,hx.1,hx.2,(Yv x y hy).1,(Yv x y hy).2,
      Zn x y,Zp x y,hL,h,eq x y⟩
  have hop (x y x' y' : ℤ) (h : U<Q x y)
      (diff : x'*A+Y x' y'*B+Z x' y'*C-(x*A+Y x y*B+Z x y*C) ≤ g*(U-L+1)) :
      L≤Q x' y' := by
    by_contra! bad
    have le := mul_le_mul_of_nonneg_left (show U-L+2 ≤ Q x y-Q x' y' by omega) (show 0≤g by omega)
    linarith [eq x y,eq x' y']
  have bottom (x : ℤ) (hx : lo≤x ∧ x≤hi) (h : U<Q x m) : U<Q x (g-1) := by
    apply walk (P:=fun j => U<Q x j) (show m≤g-1 by omega) h
    intro y hy hy' old
    apply jump _ _ hx ⟨by omega,by omega⟩
    apply hop x y _ _ old
    have h1 := mul_le_mul_of_nonneg_right
      (show Y x (y+1)-Y x y≤1+2*m by linarith [Yp x (y+1),Yn x y]) hB
    have h2 := mul_le_mul_of_nonneg_right
      (show Z x (y+1)-Z x y≤g-1-m by have := Zp x (y+1); have := Zn x y; omega) hC
    linarith
  have first : U<Q lo m := by
    apply jump _ _ ⟨le_rfl,hlh⟩ ⟨le_rfl,by omega⟩
    by_contra! bad
    have h1 := mul_le_mul_of_nonneg_right (show Y lo m≤2*m by linarith [Yp lo m]) hB
    have h2 := mul_le_mul_of_nonneg_right (show Z lo m≤g-1 by have := Zp lo m; omega) hC
    have h3 := mul_le_mul_of_nonneg_left (show Q lo m≤L-1 by omega) (show 0≤g by omega)
    linarith [eq lo m]
  have last : U<Q hi m := by
    apply walk (P:=fun j => U<Q j m) hlh first
    intro x hx hx' old
    apply jump _ _ ⟨by omega,by omega⟩ ⟨le_rfl,by omega⟩
    apply hop x (g-1) _ _ (bottom x ⟨hx,by omega⟩ old)
    have h1 := mul_le_mul_of_nonneg_right (show Y (x+1) m-Y x (g-1) ≤ 3*m+1-g by
      linarith [Yp (x+1) m,Yn x (g-1)]) hB
    have h2 := mul_le_mul_of_nonneg_right (show Z (x+1) m-Z x (g-1) ≤ g-1-m by
      have := Zp (x+1) m; have := Zn x (g-1); omega) hC
    rcases dx with h | h
    · omega
    · linarith
  have high := bottom hi ⟨hlh,le_rfl⟩ last
  have h1 := mul_le_mul_of_nonneg_right (Yn hi (g-1)) hB
  have h2 := mul_le_mul_of_nonneg_right (Zn hi (g-1)) hC
  have h3 := mul_le_mul_of_nonneg_left (show U+1≤Q hi (g-1) by omega) (show 0≤g by omega)
  linarith [eq hi (g-1)]

def cov (g a b c : ℕ) (L U : ℤ) := ∀ n : ℤ, L≤n → n≤U → inside g a b c n
def LA (g : ℤ) (k : ℕ) := 2*g^k
def UA (g : ℤ) (k : ℕ) := g^(k+2)+g^(k+1)-g^k-3
def LB (g : ℤ) (k : ℕ) := g^(k+1)
def UB (g : ℤ) (k : ℕ) := g^(k+3)+g^k-3
def A (g k : ℕ) := cov g (k+2) (k+1) k (LA g k) (UA g k)
def B (g k : ℕ) := cov g (k+3) (k+1) k (LB g k) (UB g k)

def bottom (g m lo a b c l : ℤ) := lo*a+2*m*b+(g-1)*c+g*l
def top (g m hi a b c u : ℤ) := hi*a+(g-1-m)*b+m*c+g*u

theorem liftGrid {g a b c : ℕ} (hg : 5≤g) {m lo hi L U n : ℤ}
    (cv : cov g a b c L U) (hm : m=0 ∨ m=1) (hlim : m≤lo ∧ lo≤hi ∧ hi<g)
    (dy : (1+2*m)*wt g b+(g-1-m)*wt g c ≤ g*(U-L+1))
    (dx : lo=hi ∨ wt g a+(3*m+1-g)*wt g b+(g-1-m)*wt g c ≤ g*(U-L+1))
    (s : bottom g m lo (wt g a) (wt g b) (wt g c) L ≤ n)
    (t : n ≤ top g m hi (wt g a) (wt g b) (wt g c) U) :
    inside g (a+2) (b+2) (c+2) n ∧ (m=1 → done g n) := by
  obtain ⟨x,y,z,q,hx₁,hx₂,hy₁,hy₂,hz₁,hz₂,hL,hU,rfl⟩ := grid (by exact_mod_cast hg)
    hm hlim.2.1 (show 0≤wt g b by dsimp [wt]; positivity) (show 0≤wt g c by dsimp [wt]; positivity)
    ((g:ℤ)^a) ((g:ℤ)^b) ((g:ℤ)^c) (by simp [wt,pow_succ']) (by simp [wt,pow_succ'])
    (by simp [wt,pow_succ']) dy dx s t
  have ans := wrapThree hg (cv q hL hU) (x:=x) (y:=y) (z:=z)
    ⟨by omega,by omega⟩ ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
  exact ⟨ans.1,fun _ => ans.2 (by omega) (by omega) (by omega)⟩

/- Polynomial endpoint comparisons. Write the base as five plus a nonnegative
integer and its common power as one plus a nonnegative integer. -/
theorem stepA {g : ℕ} (hg : 5≤g) (j : ℕ) (old : A g (j+1)) : A g (j+3) := by
  intro n low high
  obtain ⟨s,hs⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)-5 by omega)
  have hbase : (g:ℤ)=5+s := by omega
  have hpos : 0<(g:ℤ)^j := by positivity
  obtain ⟨t,ht⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)^j-1 by omega)
  have hpw : (g:ℤ)^j=1+t := by omega
  apply (liftGrid hg (a:=j+1+2) (b:=j+1+1) (c:=j+1) (m:=0) (lo:=0) (hi:=(g:ℤ)-1) old
    (Or.inl rfl) ⟨by omega,by omega,by omega⟩ ?_ (Or.inr ?_) ?_ ?_).1
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans _ low; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans high; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))

theorem stepB {g : ℕ} (hg : 5≤g) (j : ℕ) (old : B g (j+2)) : B g (j+4) := by
  intro n low high
  obtain ⟨s,hs⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)-5 by omega)
  have hbase : (g:ℤ)=5+s := by omega
  have hpos : 0<(g:ℤ)^j := by positivity
  obtain ⟨t,ht⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)^j-1 by omega)
  have hpw : (g:ℤ)^j=1+t := by omega
  apply (liftGrid hg (a:=j+2+3) (b:=j+2+1) (c:=j+2) (m:=0) (lo:=0) (hi:=(g:ℤ)-1) old
    (Or.inl rfl) ⟨by omega,by omega,by omega⟩ ?_ (Or.inr ?_) ?_ ?_).1
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans _ low; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans high; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))

theorem allA {g : ℕ} (hg : 5≤g) (base1 : A g 1) (base2 : A g 2) : ∀ k, A g (k+1) := by
  intro k; induction k using Nat.twoStepInduction with
  | zero => exact base1
  | one => exact base2
  | more j ih _ => exact stepA hg j ih

theorem allB {g : ℕ} (hg : 5≤g) (base2 : B g 2) (base3 : B g 3) : ∀ k, B g (k+2) := by
  intro k; induction k using Nat.twoStepInduction with
  | zero => exact base2
  | one => exact base3
  | more j ih _ => exact stepB hg j ih

theorem longFromBases {g : ℕ} (hg : 5≤g) (hA₁ : A g 1) (hA₂ : A g 2)
    (hB₂ : B g 2) (hB₃ : B g 3) (j : ℕ) (n : ℤ) (lo : (g:ℤ)^(j+6)≤n)
    (hi : n<(g:ℤ)^(j+7)) : done g n := by
  obtain ⟨s,hs⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)-5 by omega)
  have hbase : (g:ℤ)=5+s := by omega
  have hpos : 0<(g:ℤ)^j := by positivity
  obtain ⟨t,ht⟩ := Int.eq_ofNat_of_zero_le (show 0≤(g:ℤ)^j-1 by omega)
  have hpw : (g:ℤ)^j=1+t := by omega
  by_cases s₀ : n≤top g 1 ((g:ℤ)-1) (wt g (j+2+2)) (wt g (j+2+1)) (wt g (j+2)) (UA g (j+2))
  · apply (liftGrid hg (m:=1) (lo:=1) (hi:=(g:ℤ)-1) (allA hg hA₁ hA₂ (j+1))
      (Or.inr rfl) ⟨le_rfl,by omega,by omega⟩ ?_ (Or.inr ?_) ?_ s₀).2 rfl
    · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
    · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
    · apply le_trans _ lo; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  by_cases s₁ : n≤top g 1 1 (wt g (j+2+3)) (wt g (j+2+1)) (wt g (j+2)) (UB g (j+2))
  · apply (liftGrid hg (m:=1) (lo:=1) (hi:=1) (allB hg hB₂ hB₃ j)
      (Or.inr rfl) ⟨le_rfl,le_rfl,by omega⟩ ?_ (Or.inl rfl) ?_ s₁).2 rfl
    · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
    · apply le_trans _ (le_of_not_ge s₀); (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  apply (liftGrid hg (m:=1) (lo:=1) (hi:=(g:ℤ)-1) (allA hg hA₁ hA₂ (j+2))
    (Or.inr rfl) ⟨le_rfl,by omega,by omega⟩ ?_ (Or.inr ?_) ?_ ?_).2 rfl
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans _ (le_of_not_ge s₁); (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))
  · apply le_trans hi.le; (simp only [bottom,top,wt,LA,UA,LB,UB,pow_add]; (try norm_num1); try (apply sub_nonneg.mp; rw [hpw,hbase]; ring_nf; positivity))

theorem fromBases (ba₁ : ∀ g, 5≤g → A g 1) (ba₂ : ∀ g, 5≤g → A g 2)
    (bb₂ : ∀ g, 5≤g → B g 2) (bb₃ : ∀ g, 5≤g → B g 3) :
    OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1.H2 := by
  intro g hg n lo
  let l := (Nat.digits g n).length
  have big : 6<l := (Nat.lt_digits_length_iff (by omega) n).mpr lo
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 7≤l by omega)
  have hj' : l=j+7 := by omega
  have lb : g^(j+6)≤n := (Nat.lt_digits_length_iff (by omega) n).mp (by change j+6<l; omega)
  have ub : n<g^(j+7) := hj' ▸ Nat.lt_base_pow_length_digits (m:=n) (by omega : 1<g)
  obtain ⟨x,y,z,⟨p,hp,hP⟩,⟨q,hq,hQ⟩,⟨r,hr,hR⟩,eq⟩ :=
    longFromBases hg (ba₁ g hg) (ba₂ g hg) (bb₂ g hg) (bb₃ g hg) j n (by exact_mod_cast lb) (by exact_mod_cast ub)
  exact ⟨p,q,r,hP,hQ,hR,by omega⟩

abbrev dig (g a : ℤ) := 0≤a ∧ a<g

def coreA (g n : ℤ) := ∃ b c d e : ℤ, dig g b ∧ dig g c ∧ dig g d ∧ dig g e ∧
  b*(g^2+g)+c*(g^2+1)+d*g+e*(g+1)=n
def coreB (g n : ℤ) := ∃ b c d e : ℤ, dig g b ∧ dig g c ∧ dig g d ∧ dig g e ∧
  b*g^2+c*(g^2+1)+d*g+e*(g+1)=n
def coreC (g n : ℤ) := ∃ z a b c d : ℤ,
  dig g z ∧ dig g a ∧ dig g b ∧ dig g c ∧ dig g d ∧
  z*(g^3+g^2)+a*(g^3+1)+b*(g^2+g)+c*(g^2+1)+d*g=n

private def loW (g S T : ℤ) := max 0 (max (S-g+1) (T-g+1))
private def hiW (g S T : ℤ) := min (g-1) (min S T)

/-- A free digit w contributes with coefficient two to one middle column. -/
private lemma chooseW {l h a b u : ℤ} (hh : l≤h) (hab : a<b)
    (hl : 2*l+u≤b) (hu : a≤2*h+u) :
    ∃ w : ℤ, l≤w ∧ w≤h ∧ a≤2*w+u ∧ 2*w+u≤b := by
  exact ⟨max l ((a-u+1)/2),by omega,by omega,by omega,by omega⟩

private lemma buildA {g n S T U : ℤ} (hg : 5≤g)
    (h1 : loW g S T ≤ hiW g S T) (h2 : 2*loW g S T+U<g)
    (h3 : 0≤2*hiW g S T+U)
    (eq : ∀ w : ℤ, (T-w)*(g^2+g)+w*(g^2+1)+(U+2*w)*g+(S-w)*(g+1)=n) :
    coreA g n := by
  obtain ⟨w,wl,wh,el,eh⟩ := chooseW h1 (show 0<g-1 by omega) (by omega : 2*loW g S T+U≤g-1) h3
  dsimp [loW,hiW] at wl wh
  exact ⟨T-w,w,U+2*w,S-w,⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    ⟨by omega,by omega⟩,⟨by omega,by omega⟩,eq w⟩

private lemma buildB {g n S T U : ℤ}
    (h : max (loW g S T) (-U) ≤ min (hiW g S T) (g-1-U))
    (eq : ∀ w : ℤ, (T-w)*g^2+w*(g^2+1)+(U+w)*g+(S-w)*(g+1)=n) : coreB g n := by
  let w := max (loW g S T) (-U)
  have wl : loW g S T ≤ w := le_max_left _ _
  have wh : w ≤ hiW g S T := le_trans h (min_le_left _ _)
  have hU : dig g (U+w) := by
    dsimp [w]; have := le_trans h (min_le_right _ _); constructor <;> omega
  dsimp [loW,hiW] at wl wh
  exact ⟨T-w,w,U+w,S-w,⟨by omega,by omega⟩,⟨by omega,by omega⟩,hU,
    ⟨by omega,by omega⟩,eq w⟩

private lemma buildC {g n S T U V : ℤ}
    (h1 : loW g S T ≤ hiW g S T) (h2 : max 0 (V-g+1) < min (g-1) V)
    (h3 : 2*loW g S T+U ≤ min (g-1) V)
    (h4 : max 0 (V-g+1) ≤ 2*hiW g S T+U)
    (eq : ∀ w : ℤ, (T-w)*(g^3+g^2)+w*(g^3+1)+(U+2*w)*(g^2+g)+
      (S-w)*(g^2+1)+(V-U-2*w)*g=n) : coreC g n := by
  obtain ⟨w,wl,wh,el,eh⟩ := chooseW h1 h2 h3 h4
  dsimp [loW,hiW] at wl wh
  exact ⟨T-w,w,U+2*w,S-w,V-U-2*w,⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    ⟨by omega,by omega⟩,⟨by omega,by omega⟩,⟨by omega,by omega⟩,eq w⟩

theorem digitsA {g c e f : ℤ} (hg : 5≤g) (hc : 2≤c ∧ c≤g+2)
    (he : dig g e) (hf : dig g f) : coreA g (c*g^2+e*g+f) := by
  obtain ⟨he₁,he₂⟩ := he
  obtain ⟨hf₁,hf₂⟩ := hf
  have h : (0 ≤ - c + e + f ∧ 0 ≤ c + e - f) ∨
      (0 ≤ c - e + f - 2 ∧ 0 ≤ g - c + f ∧ 0 ≤ 2*g - c - e + f - 2) ∨
      (0 ≤ c - f - 2 ∧ 0 ≤ g - f - 2 ∧ 0 ≤ 2*g - c + e - f - 2) := by omega
  rcases h with h | h | h
  · apply buildA hg (S:=f) (T:=c) (U:=- c + e - f)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildA hg (S:=f) (T:=c - 1) (U:=g - c + e - f + 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildA hg (S:=g + f) (T:=c - 1) (U:=- c + e - f)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega

theorem digitsB {g c e f : ℤ} (hg : 5≤g) (hc : 1≤c ∧ c≤g+1)
    (he : dig g e) (hf : dig g f) : coreB g (c*g^2+e*g+f) := by
  obtain ⟨he₁,he₂⟩ := he
  obtain ⟨hf₁,hf₂⟩ := hf
  have h : (0 ≤ c + e - f ∧ 0 ≤ g - c + f - 1) ∨
      (0 ≤ - e + f - 1 ∧ 0 ≤ g - c - e + f - 1) ∨
      (0 ≤ c - f - 2 ∧ 0 ≤ g - f - 2) := by omega
  rcases h with h | h | h
  · apply buildB (S:=f) (T:=c) (U:=e - f)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildB (S:=f) (T:=c - 1) (U:=g + e - f)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildB (S:=g + f) (T:=c - 1) (U:=e - f - 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega

theorem digitsC {g c d e f : ℤ} (hg : 5≤g) (hc : 2≤c ∧ c≤g+2)
    (hd : dig g d) (he : dig g e) (hf : dig g f) : coreC g (c*g^3+d*g^2+e*g+f) := by
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  obtain ⟨hf₁,hf₂⟩ := hf
  have h : (0 ≤ - c + d + f ∧ 0 ≤ e - 1 ∧ 0 ≤ c - d + e + f ∧ 0 ≤ c + d - f) ∨
      (0 ≤ - g + c - d + e + f - 1 ∧ 0 ≤ e - 1 ∧ 0 ≤ g - c - d + e + f - 1 ∧ 0 ≤ g - c + f) ∨
      (0 ≤ - c + d - e + f - 2 ∧ 0 ≤ c + d - e - f - 2) ∨
      (0 ≤ c - d + f - 1 ∧ 0 ≤ g - c + f ∧ 0 ≤ g - c + d - e + f - 1 ∧ 0 ≤ g - e - 3 ∧ 0 ≤ g + c + d - e - f - 3) ∨
      (0 ≤ e - 2 ∧ 0 ≤ c - d + e - f - 4 ∧ 0 ≤ c - f - 2 ∧ 0 ≤ g - f - 2 ∧ 0 ≤ 2*g - c - d + e + f - 2 ∧ 0 ≤ 2*g - c + d - f - 1) ∨
      (0 ≤ c - f - 2 ∧ 0 ≤ c + d - e - f - 2 ∧ 0 ≤ g - e - 2 ∧ 0 ≤ g - f - 2 ∧ 0 ≤ 2*g - c + d - e - f - 2) ∨
      (0 ≤ c - d - f - 4 ∧ 0 ≤ g - e - 2) := by omega
  rcases h with h | h | h | h | h | h | h
  · apply buildC (S:=f) (T:=c) (U:=- c + d - f) (V:=e)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=f) (T:=c - 1) (U:=g - c + d - f + 1) (V:=e)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=f) (T:=c) (U:=- c + d - f - 1) (V:=g + e)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=f) (T:=c - 1) (U:=g - c + d - f) (V:=g + e)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=g + f) (T:=c - 1) (U:=- c + d - f + 1) (V:=e - 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=g + f) (T:=c - 1) (U:=- c + d - f) (V:=g + e - 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega
  · apply buildC (S:=g + f) (T:=c - 2) (U:=g - c + d - f + 1) (V:=g + e - 1)
    all_goals first | (intro w; ring) | (dsimp [loW,hiW]; omega) | omega

private lemma splitBlock {b n l u : ℤ} (hb : 0<b) (lo : l*b ≤ n) (hi : n<(u+1)*b) :
    ∃ q r : ℤ, l≤q ∧ q≤u ∧ 0≤r ∧ r<b ∧ n=q*b+r := by
  have eq := Int.emod_add_ediv_mul n b
  have r₁ := Int.emod_nonneg n (by omega : b≠0)
  have r₂ := Int.emod_lt_of_pos n hb
  refine ⟨n/b,n%b,?_,?_,r₁,r₂,by linarith⟩
  · by_contra! h
    have := mul_le_mul_of_nonneg_right (show n/b≤l-1 by omega) hb.le
    linarith
  · by_contra! h
    have := mul_le_mul_of_nonneg_right (show u+1≤n/b by omega) hb.le
    linarith

private lemma twoLow {g r : ℤ} (hg : 5≤g) (h : 0≤r ∧ r<g^2) :
    ∃ e f, dig g e ∧ dig g f ∧ r=e*g+f := by
  obtain ⟨e,f,he,he',hf,hf',eq⟩ := splitBlock (b:=g) (l:=0) (u:=g-1) (by omega)
    (by simpa using h.1) (by nlinarith [h.2])
  exact ⟨e,f,⟨he,by omega⟩,⟨hf,hf'⟩,eq⟩

private lemma coreArange {g n : ℤ} (hg : 5≤g) (lo : 2*g^2≤n) (hi : n<(g+3)*g^2) :
    coreA g n := by
  obtain ⟨c,r,h₁,h₂,hr,hr',eq⟩ := splitBlock (b:=g^2) (u:=g+2) (by positivity) lo (by linarith)
  obtain ⟨e,f,he,hf,rfl⟩ := twoLow hg ⟨hr,hr'⟩
  rw [eq,←add_assoc]; exact digitsA hg ⟨h₁,h₂⟩ he hf

private lemma coreBrange {g n : ℤ} (hg : 5≤g) (lo : g^2≤n) (hi : n<(g+2)*g^2) :
    coreB g n := by
  obtain ⟨c,r,h₁,h₂,hr,hr',eq⟩ := splitBlock (b:=g^2) (l:=1) (u:=g+1) (by positivity)
    (by simpa using lo) (by linarith)
  obtain ⟨e,f,he,hf,rfl⟩ := twoLow hg ⟨hr,hr'⟩
  rw [eq,←add_assoc]; exact digitsB hg ⟨h₁,h₂⟩ he hf

private lemma coreCrange {g n : ℤ} (hg : 5≤g) (lo : 2*g^3≤n) (hi : n<(g+3)*g^3) :
    coreC g n := by
  obtain ⟨c,r,h₁,h₂,hr,hr',eq⟩ := splitBlock (b:=g^3) (l:=2) (u:=g+2) (by positivity) lo (by linarith)
  obtain ⟨d,r',hd,hd',hh,hh',er⟩ := splitBlock (b:=g^2) (l:=0) (u:=g-1) (by positivity)
    (by simpa using hr) (by nlinarith)
  obtain ⟨e,f,he,hf,er'⟩ := twoLow hg ⟨hh,hh'⟩
  rw [eq,er,er']; simp only [←add_assoc]
  exact digitsC hg ⟨h₁,h₂⟩ ⟨hd,by omega⟩ he hf

private def maxCoreA (g : ℤ) := (g-1)*((g^2+g)+(g^2+1)+g+(g+1))
private lemma coreAwide {g n : ℤ} (hg : 5≤g) (lo : 2*g^2≤n) (hi : n ≤ maxCoreA g-2*g^2) :
    coreA g n := by
  by_cases h : n<(g+3)*g^2
  · exact coreArange hg lo h
  have hm : maxCoreA g-n<(g+3)*g^2 := by dsimp [maxCoreA] at *; nlinarith [sq_nonneg g]
  obtain ⟨b,c,d,e,hb,hc,hd,he,eq⟩ := coreArange hg (n:=maxCoreA g-n) (by omega) hm
  obtain ⟨hb₁,hb₂⟩ := hb
  obtain ⟨hc₁,hc₂⟩ := hc
  obtain ⟨hd₁,hd₂⟩ := hd
  obtain ⟨he₁,he₂⟩ := he
  exact ⟨g-1-b,g-1-c,g-1-d,g-1-e,⟨by omega,by omega⟩,⟨by omega,by omega⟩,
    ⟨by omega,by omega⟩,⟨by omega,by omega⟩,by dsimp [maxCoreA] at eq; linarith⟩

private lemma coin {g w l u n : ℤ} (hg : 5≤g) (hw : 0<w) (space : w≤u-l+1)
    (lo : l≤n) (hi : n≤u+(g-1)*w) : ∃ a q, dig g a ∧ l≤q ∧ q≤u ∧ n=a*w+q := by
  let a := (n-l)/w
  have ad : 0≤a := Int.ediv_nonneg (by omega) hw.le
  have r₁ := Int.emod_nonneg (n-l) (by omega : w≠0)
  have r₂ := Int.emod_lt_of_pos (n-l) hw
  have eq : (n-l)%w+a*w=n-l := Int.emod_add_ediv_mul _ _
  by_cases h : a<g
  · exact ⟨a,l+(n-l)%w,⟨ad,h⟩,by omega,by omega,by linarith⟩
  · have le := mul_le_mul_of_nonneg_right (show g-1≤a by omega) hw.le
    exact ⟨g-1,n-(g-1)*w,⟨by omega,by omega⟩,by linarith,by linarith,by ring⟩

private lemma pad1 {g : ℕ} {x : ℤ} (hx : dig g x) :
    Pad g 1 (x) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  exact ⟨[x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]⟩

private lemma pad2 {g : ℕ} {x : ℤ} (hx : dig g x) :
    Pad g 2 (x*(g+1)) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  exact ⟨[x,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

private lemma pad3 {g : ℕ} {x y : ℤ} (hx : dig g x) (hy : dig g y) :
    Pad g 3 (x*(g^2+1)+y*g) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy.1
  have hy' : y<g := by exact_mod_cast hy.2
  exact ⟨[x,y,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

private lemma pad4 {g : ℕ} {x y : ℤ} (hx : dig g x) (hy : dig g y) :
    Pad g 4 (x*(g^3+1)+y*(g^2+g)) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy.1
  have hy' : y<g := by exact_mod_cast hy.2
  exact ⟨[x,y,y,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

private lemma pad5 {g : ℕ} {x y z : ℤ} (hx : dig g x) (hy : dig g y) (hz : dig g z) :
    Pad g 5 (x*(g^4+1)+y*(g^3+g)+z*g^2) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy.1
  have hy' : y<g := by exact_mod_cast hy.2
  obtain ⟨z,rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
  have hz' : z<g := by exact_mod_cast hz.2
  exact ⟨[x,y,z,y,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

private lemma pad6 {g : ℕ} {x y z : ℤ} (hx : dig g x) (hy : dig g y) (hz : dig g z) :
    Pad g 6 (x*(g^5+1)+y*(g^4+g)+z*(g^3+g^2)) := by
  obtain ⟨x,rfl⟩ := Int.eq_ofNat_of_zero_le hx.1
  have hx' : x<g := by exact_mod_cast hx.2
  obtain ⟨y,rfl⟩ := Int.eq_ofNat_of_zero_le hy.1
  have hy' : y<g := by exact_mod_cast hy.2
  obtain ⟨z,rfl⟩ := Int.eq_ofNat_of_zero_le hz.1
  have hz' : z<g := by exact_mod_cast hz.2
  exact ⟨[x,y,z,z,y,x],rfl,rfl,by simp_all,by simp [Nat.ofDigits]; ring⟩

theorem smallA1 (g : ℕ) (hg : 5≤g) : A g 1 := by
  intro n lo hi
  let G : ℤ := g
  have hg' : 5≤G := by dsimp [G]; exact_mod_cast hg
  obtain ⟨j,hj⟩ := Int.eq_ofNat_of_zero_le (show 0≤G-5 by omega)
  have H : G=5+j := by omega
  change LA G 1 ≤ n at lo
  change n ≤ UA G 1 at hi
  obtain ⟨a,s,ha,ls,hs,eq₁⟩ := coin (g:=G) (l:=0) (u:=2*G^2-2) (w:=G^2+1) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) (le_trans (by dsimp [LA]; positivity) lo)
    (le_trans hi (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨c,t,hc,lt,ht,eq₂⟩ := coin (g:=G) (l:=0) (u:=G^2-1) (w:=G+1) hg'
    (by omega) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) ls (le_trans hs (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨b,d,hb,ld,hd,eq₃⟩ := coin (g:=G) (l:=0) (u:=G-1) (w:=G) hg'
    (by omega) (by omega) lt (le_trans ht (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  exact ⟨_,_,_,pad3 (g:=g) ha hb,pad2 hc,pad1 ⟨ld,by omega⟩,by change a*(G^2+1)+b*G+c*(G+1)+d=n; linarith⟩

theorem smallA2 (g : ℕ) (hg : 5≤g) : A g 2 := by
  intro n lo hi
  let G : ℤ := g
  have hg' : 5≤G := by dsimp [G]; exact_mod_cast hg
  obtain ⟨j,hj⟩ := Int.eq_ofNat_of_zero_le (show 0≤G-5 by omega)
  have H : G=5+j := by omega
  change n≤UA G 2 at hi
  obtain ⟨a,r,ha,lr,hr,eq⟩ := coin (g:=G) (l:=2*G^2) (u:=maxCoreA G-2*G^2) (w:=G^3+1) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) lo (le_trans hi (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨b,c,d,e,hb,hc,hd,he,h⟩ := coreAwide hg' lr hr
  exact ⟨_,_,_,pad4 (g:=g) ha hb,pad3 hc hd,pad2 he,
    by change a*(G^3+1)+b*(G^2+G)+(c*(G^2+1)+d*G)+e*(G+1)=n; linarith⟩

theorem smallB2 (g : ℕ) (hg : 5≤g) : B g 2 := by
  intro n lo hi
  let G : ℤ := g
  have hg' : 5≤G := by dsimp [G]; exact_mod_cast hg
  obtain ⟨j,hj⟩ := Int.eq_ofNat_of_zero_le (show 0≤G-5 by omega)
  have H : G=5+j := by omega
  change LB G 2 ≤ n at lo
  change n ≤ UB G 2 at hi
  obtain ⟨x,s,hx,ls,hs,eq₁⟩ := coin (g:=G) (l:=(G^2)) (u:=((G+2)*G^2-1+(G-1)*(G^3+G))) (w:=G^4+1) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) (le_trans (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) lo) (le_trans hi (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨y,r,hy,lr,hr,eq₂⟩ := coin (g:=G) (l:=(G^2)) (u:=(G+2)*G^2-1) (w:=(G^3+G)) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) ls hs
  obtain ⟨z,b,c,d,hz,hb,hc,hd,eq₃⟩ := coreBrange hg' lr (by omega)
  exact ⟨_,_,_,pad5 (g:=g) hx hy hz,pad3 hb hc,pad2 hd,
    by change x*(G^4+1)+y*(G^3+G)+z*G^2+(b*(G^2+1)+c*G)+d*(G+1)=n; linarith⟩

theorem smallB3 (g : ℕ) (hg : 5≤g) : B g 3 := by
  intro n lo hi
  let G : ℤ := g
  have hg' : 5≤G := by dsimp [G]; exact_mod_cast hg
  obtain ⟨j,hj⟩ := Int.eq_ofNat_of_zero_le (show 0≤G-5 by omega)
  have H : G=5+j := by omega
  change LB G 3 ≤ n at lo
  change n ≤ UB G 3 at hi
  obtain ⟨x,s,hx,ls,hs,eq₁⟩ := coin (g:=G) (l:=(2*G^3)) (u:=((G+3)*G^3-1+(G-1)*(G^4+G))) (w:=G^5+1) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) (le_trans (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) lo) (le_trans hi (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)))
  obtain ⟨y,r,hy,lr,hr,eq₂⟩ := coin (g:=G) (l:=(2*G^3)) (u:=(G+3)*G^3-1) (w:=(G^4+G)) hg'
    (by positivity) (by ((try simp only [LA,UA,LB,UB,maxCoreA]); apply sub_nonneg.mp; rw [H]; ring_nf <;> positivity)) ls hs
  obtain ⟨z,b,c,d,e,hz,hb,hc,hd,he,eq₃⟩ := coreCrange hg' lr (by omega)
  exact ⟨_,_,_,pad6 (g:=g) hx hy hz,pad4 hb hc,pad3 hd he,
    by change x*(G^5+1)+y*(G^4+G)+z*(G^3+G^2)+(b*(G^3+1)+c*(G^2+G))+(d*(G^2+1)+e*G)=n; linarith⟩

end G95Long

private theorem h2_h2_proof : OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1.H2 :=
  G95Long.fromBases G95Long.smallA1 G95Long.smallA2 G95Long.smallB2 G95Long.smallB3
end

private theorem h2_proof : OMA.R_Green95_green_95_variants_three_palindromes_R1.H2 :=
  OMA.R_Green95_green_95_variants_three_palindromes_R1_H2_R1.main h2_h1_proof h2_h2_proof

theorem OMA.solution : type_of% @Green95.green_95.variants.three_palindromes :=
  OMA.R_Green95_green_95_variants_three_palindromes_R1.main h1_proof h2_proof
