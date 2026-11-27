import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1
import Mathlib

/-!
# Rankin integral and toric trace for the signed winding square

The first step pairs the level-32 eta product with the quadratic ideal theta
series, with one common nonzero period. The second identifies the odd Fourier
contribution of the traced theta products. The third evaluates the winding
calibrations at 1 and 17 and exhibits a class of discriminant −136.
-/
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1
open Finset Polynomial MeasureTheory MatrixGroups ModularGroup CongruenceSubgroup
open scoped UpperHalfPlane Classical ComplexConjugate

def H1 : Prop :=
  let i : GaussianInt := ⟨0,1⟩
  let rot (k : ℤ) := if k%4=0 then 1 else if k%4=1 then i else if k%4=2 then -1 else -i
  let S := Nat.rec (motive:=fun _ => ℤ → ℕ → GaussianInt) (fun _ _ => 1)
    (fun _ f a n => let r := a.bmod n
                    rot (a.bdiv n)*(if r=0 then 1 else if 2*r=-(n:ℤ) then 1-i else
                      1-f (if 0≤r then -(n:ℤ) else (n:ℤ)) (2*r.natAbs)))
  let w (d j : ℕ) : ℤ := if Odd j then jacobiSym (2*d:ℕ) j else 0
  let W (d : ℕ) (hd : 0<d) : ℤ :=
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    let c (j : ℕ) : ℤ[X] := (X^(16*d-j)-X^j)*X^(4*d)
    let R := c (2*d)*∏ k∈range (4*d-1),c (k+1)
    let G := ∑ j : ZMod (4*(2*d)), C (w d j.val)*X^(2*j.val)
    (if (G-R) %ₘ cyclotomic (16*d) ℤ = 0 then 1 else -1)*
      ∑ j : ZMod (4*(2*d)), w d j.val*(S (2*d) j.val (2*d)).re
  let h (d : ℕ) : ℕ :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    let s := (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
    (s.filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)).card
  let θ (d : ℕ) (z : ℂ) := (h d:ℂ) + 2*∑' m : ℕ,
    (∑ e ∈ m.divisors, ((if Odd e then jacobiSym (-((2*d:ℕ):ℤ)) e else 0 : ℤ):ℂ))*Function.Periodic.qParam 1 z^m
  let A (d : ℕ) (z : ℍ) := (z.im:ℂ)^2*(ModularForm.eta (4*(z:ℂ))^2*ModularForm.eta (8*(z:ℂ))^2)*
    conj (θ d z*θ d (4*(z:ℂ)))
  let J (d : ℕ) := ∑' q : SL(2,ℤ) ⧸ Gamma0 (32*d), ∫ z in fdo, A d (q.out⁻¹ • z)
  ∃ C : ℂ, C≠0 ∧ ∀ d : ℕ, Squarefree d → (hd : d%4=1) → J d=(W d (by omega):ℂ)*C

def H2 : Prop :=
  let P (d : ℕ) : ℤ :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    let s := (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
    ((s.filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%8=0)).card:ℤ)-
      (s.filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%4=0 ∧
        (v.1+v.2.1+2*(v.2.2/4))%4=0)).card
  let h (d : ℕ) : ℕ :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    let s := (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
    (s.filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)).card
  let θ (d : ℕ) (z : ℂ) := (h d:ℂ) + 2*∑' m : ℕ,
    (∑ e ∈ m.divisors, ((if Odd e then jacobiSym (-((2*d:ℕ):ℤ)) e else 0 : ℤ):ℂ))*Function.Periodic.qParam 1 z^m
  let A (d : ℕ) (z : ℍ) := (z.im:ℂ)^2*(ModularForm.eta (4*(z:ℂ))^2*ModularForm.eta (8*(z:ℂ))^2)*
    conj (θ d z*θ d (4*(z:ℂ)))
  let J (d : ℕ) := ∑' q : SL(2,ℤ) ⧸ Gamma0 (32*d), ∫ z in fdo, A d (q.out⁻¹ • z)
  ∀ d : ℕ, Squarefree d → d%4=1 →
    (h 17:ℂ)^2*(4*J d-(P d:ℂ)^2*J 1)=(4*(h d:ℂ)^2-(P d:ℂ)^2*(h 1:ℂ)^2)*J 17

def H3 : Prop :=
  let i : GaussianInt := ⟨0,1⟩
  let rot (k : ℤ) := if k%4=0 then 1 else if k%4=1 then i else if k%4=2 then -1 else -i
  let S := Nat.rec (motive:=fun _ => ℤ → ℕ → GaussianInt) (fun _ _ => 1)
    (fun _ f a n => let r := a.bmod n
                    rot (a.bdiv n)*(if r=0 then 1 else if 2*r=-(n:ℤ) then 1-i else
                      1-f (if 0≤r then -(n:ℤ) else (n:ℤ)) (2*r.natAbs)))
  let w (d j : ℕ) : ℤ := if Odd j then jacobiSym (2*d:ℕ) j else 0
  let W (d : ℕ) (hd : 0<d) : ℤ :=
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    let c (j : ℕ) : ℤ[X] := (X^(16*d-j)-X^j)*X^(4*d)
    let R := c (2*d)*∏ k∈range (4*d-1),c (k+1)
    let G := ∑ j : ZMod (4*(2*d)), C (w d j.val)*X^(2*j.val)
    (if (G-R) %ₘ cyclotomic (16*d) ℤ = 0 then 1 else -1)*
      ∑ j : ZMod (4*(2*d)), w d j.val*(S (2*d) j.val (2*d)).re
  let h (d : ℕ) : ℕ :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    let s := (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
    (s.filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)).card
  ∀ k : ℕ, (hk : k%4=1) → (k=1 → W k (by omega)=4) ∧
    (k=17 → W k (by omega)=0 ∧ 0<h k)

lemma combine (W : (d : ℕ) → 0<d → ℤ) (P : ℕ→ℤ) (h : ℕ→ℕ) (J : ℕ→ℂ)
    (hW : ∃ C : ℂ, C≠0 ∧ ∀ d : ℕ, Squarefree d → (hd : d%4=1) → J d=(W d (by omega):ℂ)*C)
    (hJ : ∀ d : ℕ, Squarefree d → d%4=1 →
      (h 17:ℂ)^2*(4*J d-(P d:ℂ)^2*J 1)=(4*(h d:ℂ)^2-(P d:ℂ)^2*(h 1:ℂ)^2)*J 17)
    (hS : ∀ k : ℕ, (hk : k%4=1) → (k=1 → W k (by omega)=4) ∧ (k=17 → W k (by omega)=0 ∧ 0<h k)) :
    ∀ d : ℕ, Squarefree d → (hd : d%4=1) → W d (by omega)=P d^2 := by
  rintro d hs hd
  obtain ⟨C,hC,H⟩ := hW
  have e₁ := (hS 1 (by decide)).1 rfl
  have e₁₇ := (hS 17 (by decide)).2 rfl
  have E := hJ d hs hd
  rw [H d hs hd,H 1 squarefree_one (by decide),H 17 (by decide : Nat.Prime 17).squarefree (by decide),e₁,e₁₇.1] at E
  push_cast at E
  have e : (4*(h 17:ℂ)^2*C)*((W d (by omega):ℂ)-(P d:ℂ)^2)=0 := by linear_combination E
  have hp : (h 17:ℂ)≠0 := by exact_mod_cast e₁₇.2.ne'
  have q := sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp)) hC))
  exact_mod_cast q

theorem main : H1 → H2 → H3 → OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1.H1 := by
  intro a b c
  let i : GaussianInt := ⟨0,1⟩
  let rot (k : ℤ) := if k%4=0 then 1 else if k%4=1 then i else if k%4=2 then -1 else -i
  let S := Nat.rec (motive:=fun _ => ℤ → ℕ → GaussianInt) (fun _ _ => 1)
    (fun _ f a n => let r := a.bmod n
                    rot (a.bdiv n)*(if r=0 then 1 else if 2*r=-(n:ℤ) then 1-i else
                      1-f (if 0≤r then -(n:ℤ) else (n:ℤ)) (2*r.natAbs)))
  let w (d j : ℕ) : ℤ := if Odd j then jacobiSym (2*d:ℕ) j else 0
  let W (d : ℕ) (hd : 0<d) : ℤ :=
    haveI : NeZero (4*(2*d)) := ⟨by omega⟩
    let c (j : ℕ) : ℤ[X] := (X^(16*d-j)-X^j)*X^(4*d)
    let R := c (2*d)*∏ k∈range (4*d-1),c (k+1)
    let G := ∑ j : ZMod (4*(2*d)), C (w d j.val)*X^(2*j.val)
    (if (G-R) %ₘ cyclotomic (16*d) ℤ = 0 then 1 else -1)*
      ∑ j : ZMod (4*(2*d)), w d j.val*(S (2*d) j.val (2*d)).re
  let P (d : ℕ) : ℤ :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    let s := (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
    ((s.filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%8=0)).card:ℤ)-
      (s.filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%4=0 ∧
        (v.1+v.2.1+2*(v.2.2/4))%4=0)).card
  let h (d : ℕ) : ℕ :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    let s := (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
    (s.filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)).card
  let θ (d : ℕ) (z : ℂ) := (h d:ℂ) + 2*∑' m : ℕ,
    (∑ e ∈ m.divisors, ((if Odd e then jacobiSym (-((2*d:ℕ):ℤ)) e else 0 : ℤ):ℂ))*Function.Periodic.qParam 1 z^m
  let A (d : ℕ) (z : ℍ) := (z.im:ℂ)^2*(ModularForm.eta (4*(z:ℂ))^2*ModularForm.eta (8*(z:ℂ))^2)*
    conj (θ d z*θ d (4*(z:ℂ)))
  let J (d : ℕ) := ∑' q : SL(2,ℤ) ⧸ Gamma0 (32*d), ∫ z in fdo, A d (q.out⁻¹ • z)
  exact combine W P h J a b c

end OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1
