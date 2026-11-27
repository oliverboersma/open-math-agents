import FormalConjectures.ErdosProblems.«372»
import Mathlib

/-! Sungjin Kim, *Two remarks on the largest prime factors of n and n+1*,
Lemmas 2.1, 3.1 and §4.1. A pair of primes in a system of linear forms
produces the first two largest factors. The common multiplier also forces
the third integer to factor into two strictly smaller pieces. -/
namespace OMA.R_Erdos372_erdos_372_R1
open Finset

/-- The two-prime case of Maynard–Tao–Polymath8b for the admissible linear
forms a*r+1. Admissibility at every prime follows by taking r=0. -/
def H1 : Prop := ∀ A : Finset ℕ, A.card = 50 → (∀ a ∈ A, 0 < a) →
    ∀ X : ℕ, ∃ r > X, ∃ a ∈ A, ∃ b ∈ A, a < b ∧ (a*r+1).Prime ∧ (b*r+1).Prime

/-- Heath-Brown's divisibility sets (Kim, Lemma 3.1). -/
def H2 : Prop := ∀ k : ℕ, ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 0 < a) ∧
    ∀ a ∈ A, ∀ b ∈ A, a < b → b-a ∣ a

lemma largest (v p : ℕ) (v0 : 0 < v) (vp : v ≤ p) (hp : p.Prime) :
    (v*p).maxPrimeFac = p := by
  rw [Nat.maxPrimeFac_mul v0.ne' hp.ne_zero,hp.maxPrimeFac_eq_self,max_eq_right]
  exact Nat.maxPrimeFac_le.trans vp

lemma triple (a b s u c : ℕ) (ha : 0 < a) (hu : 0 < u) (hc : 0 < c)
    (hs : s=(u+2)*c) (hab : a<b) (he : u*b=(u+1)*a)
    (hsize : u+2 < a*s+1) (hp : (a*s+1).Prime) (hq : (b*s+1).Prime) :
    let n := u*(b*s+1)
    n.maxPrimeFac > (n+1).maxPrimeFac ∧ (n+1).maxPrimeFac > (n+2).maxPrimeFac := by
  dsimp only
  have ord : a*s+1 < b*s+1 := by
    apply Nat.add_lt_add_right
    exact Nat.mul_lt_mul_of_pos_right hab (by rw [hs]; positivity)
  have next : u*(b*s+1)+1=(u+1)*(a*s+1) := by nlinarith only [congrArg (·*s) he]
  let w := 1+(u+1)*a*c
  have next2 : u*(b*s+1)+2=(u+2)*w := by
    rw [show u*(b*s+1)+2=(u*(b*s+1)+1)+1 by omega,next,hs]
    dsimp [w]; ring
  have wpos : 0<w := by dsimp [w]; omega
  have wlt : w<a*s+1 := by
    rw [hs]; dsimp [w]; nlinarith only [Nat.mul_pos ha hc]
  rw [next,next2,largest _ _ hu (by omega) hq,largest _ _ (by omega) (by omega) hp,
    Nat.maxPrimeFac_mul (by omega) wpos.ne']
  exact ⟨ord,max_lt (Nat.maxPrimeFac_le.trans_lt hsize) (Nat.maxPrimeFac_le.trans_lt wlt)⟩

theorem main : H1 → H2 → type_of% @Erdos372.erdos_372 := by
  classical
  intro pairs family
  obtain ⟨A,hcard,hpos,hdiff⟩ := family 50
  let B := A.sup id
  let M := (B+2).factorial
  have Mp : 0<M := Nat.factorial_pos _
  let S := A.image (M*·)
  have Scard : S.card=50 := by
    rw [show S=A.image (M*·) by rfl,card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left Mp h),hcard]
  apply Set.infinite_of_not_bddAbove
  rintro ⟨X,hX⟩
  obtain ⟨r,hr,x,hx,y,hy,hxy,p,q⟩ := pairs S Scard
    (by intro x hx; obtain ⟨a,haa,rfl⟩ := mem_image.mp hx; exact Nat.mul_pos Mp (hpos _ haa)) (X+B+4)
  obtain ⟨a,haa,rfl⟩ := mem_image.mp hx
  obtain ⟨b,hbb,rfl⟩ := mem_image.mp hy
  have hab : a<b := by exact Nat.lt_of_mul_lt_mul_left hxy
  have ap := hpos _ haa
  have bp := hpos _ hbb
  obtain ⟨u,eu⟩ := hdiff _ haa _ hbb hab
  have up : 0<u := by
    by_contra! hz
    have e : u=0 := by omega
    simp [e] at eu
    omega
  have dp : 0<b-a := by omega
  have usmall : u ≤ a := eu ▸ Nat.le_mul_of_pos_left _ dp
  have ab : a ≤ B := le_sup (f:=id) haa
  have mdvd : u+2 ∣ M := Nat.dvd_factorial (by omega) (by omega)
  let s := M*r
  have sdvd : u+2 ∣ s := dvd_mul_of_dvd_left mdvd r
  obtain ⟨c,ec⟩ := sdvd
  have sp : r ≤ s := Nat.le_mul_of_pos_left _ Mp
  have cp : 0<c := by
    by_contra! hz
    have e : c=0 := by omega
    simp [e] at ec
    omega
  have hp : (a*s+1).Prime := by simpa [s,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using p
  have hq : (b*s+1).Prime := by simpa [s,Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using q
  have he : u*b=(u+1)*a := by
    have eb : b=a+(b-a) := by omega
    calc
      u*b = u*(a+(b-a)) := congrArg (u*·) eb
      _ = (u+1)*a := by rw [Nat.mul_add,Nat.mul_comm u (b-a),←eu]; ring
  have big : s ≤ a*s := Nat.le_mul_of_pos_left _ ap
  have good := triple a b s u c ap up cp ec hab he (by omega) hp hq
  have cap := hX (a:=u*(b*s+1)) good
  have small := Nat.le_mul_of_pos_left (b*s+1) up
  have big' := Nat.le_mul_of_pos_left s bp
  omega
end OMA.R_Erdos372_erdos_372_R1
