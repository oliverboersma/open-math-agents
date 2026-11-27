import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-!
# Universal elliptic-unit norms in the Gaussian division fields

The coordinates of the primitive point with complex parameter ω/qʳ generate
the r-th division field. A nonzero rational logarithmic derivative produces,
at arbitrarily large split primes, a unit of the first field which is a norm
of a unit at every higher level. Its difference from a ground-field value
generates the local maximal ideal. A rational point of infinite order excludes
that combination for all sufficiently large primes.
-/
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1
open Complex NumberField IsDedekindDomain IntermediateField IsLocalRing Set MeasureTheory
open scoped Classical NumberField

def H1 : Prop :=
  ∀ (n : ℕ) (hn : 0<n),
  letI : NeZero (4*n) := ⟨Nat.ne_of_gt (Nat.mul_pos (by decide) hn)⟩
  let a := 1+3*(4*n)
  let ω : ℝ := (∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹)
  let b (v : ZMod (4*n) × ZMod (4*n)) : GaussianInt := ⟨v.1.val,v.2.val⟩
  let χ (v : ZMod (4*n) × ZMod (4*n)) : ℤ :=
    let m := (b v).norm.natAbs
    if (⟨2,2⟩:GaussianInt) ∣ b v-1 then (if Odd m then jacobiSym n m else 0) else 0
  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=Complex.I*(ω:ℂ) →
  let t (j : Fin a × Fin a) : ℂ := ((j.1.val:ℂ)*M.ω₁+(j.2.val:ℂ)*M.ω₂)/(a:ℂ)
  let D (z : ℂ) := ∏ j ∈ Finset.univ.filter (fun j => t j ∉ M.lattice),
    (M.weierstrassP z-M.weierstrassP (t j))
  let G (z : ℂ) := ∏ v ∈ Finset.univ.filter (fun v => χ v≠0),
    D (z+((ω/(4*n):ℝ):ℂ)*(b v:ℂ))^χ v
  n%8=2 → 2<n → ∀ c : ℚ, c≠0 → logDeriv G 0=(c:ℂ) → ∀ B : ℕ,
  ∃ p : ℕ, p.Prime ∧ B<p ∧ 3<p ∧ p%4=1 ∧ ¬p∣2*n ∧ ∃ q : GaussianInt, q.norm.natAbs=p ∧
  let K:=ℚ⟮I⟯
  let Ω:=algebraicClosure K ℂ
  let A (r : ℕ) :=
    let t:=M.ω₁/(q:ℂ)^r
    (adjoin K {M.weierstrassP t,M.derivWeierstrassP t/2}).comap (algebraicClosure K ℂ).val
  let T:=A 1
  let V (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : F) :=
    let O:=v.adicCompletionIntegers F
    let L:=v.adicCompletion F
    ∃ u b : Oˣ, ((u:O):L)=algebraMap F L x ∧ ((b:O):L)=algebraMap F L y ∧
      maximalIdeal O=Ideal.span {(u:O)-(b:O)}
  ∃ hT : NumberField T, letI:=hT;
    ∃ (w : HeightOneSpectrum (𝓞 T)) (z : 𝓞 T), z∈w.asIdeal ∧ (((z:T):Ω):ℂ)=(q:ℂ) ∧
    ∃ (a : (𝓞 T)ˣ) (b : K), @V T _ hT w a.val.val (algebraMap K T b) ∧
      ∀ r : ℕ, ∃ h : T≤A (r+1), letI : Algebra T (A (r+1)):=(IntermediateField.inclusion h).toAlgebra;
        ∃ x : (𝓞 (A (r+1)))ˣ, Algebra.norm T x.val.val=a.val.val

def H2 : Prop :=
  ∀ (n : ℕ) (hn : 0<n), let ω : ℝ := ∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹;
  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=I*(ω:ℂ) →
  ∀ P : (⟨0,0,0,-(n:ℚ)^2,0⟩ : WeierstrassCurve ℚ).toAffine.Point, ¬IsOfFinAddOrder P →
  ∃ B : ℕ, ∀ p : ℕ, p.Prime → B<p → p%4=1 → ¬p∣2*n → ∀ q : GaussianInt, q.norm.natAbs=p → ¬(
  let K:=ℚ⟮I⟯
  let Ω:=algebraicClosure K ℂ
  let A (r : ℕ) :=
    let t:=M.ω₁/(q:ℂ)^r
    (adjoin K {M.weierstrassP t,M.derivWeierstrassP t/2}).comap (algebraicClosure K ℂ).val
  let T:=A 1
  let V (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : F) :=
    let O:=v.adicCompletionIntegers F
    let L:=v.adicCompletion F
    ∃ u b : Oˣ, ((u:O):L)=algebraMap F L x ∧ ((b:O):L)=algebraMap F L y ∧
      maximalIdeal O=Ideal.span {(u:O)-(b:O)}
  ∃ hT : NumberField T, letI:=hT;
    ∃ (w : HeightOneSpectrum (𝓞 T)) (z : 𝓞 T), z∈w.asIdeal ∧ (((z:T):Ω):ℂ)=(q:ℂ) ∧
    ∃ (a : (𝓞 T)ˣ) (b : K), @V T _ hT w a.val.val (algebraMap K T b) ∧
      ∀ r : ℕ, ∃ h : T≤A (r+1), letI : Algebra T (A (r+1)):=(IntermediateField.inclusion h).toAlgebra;
        ∃ x : (𝓞 (A (r+1)))ˣ, Algebra.norm T x.val.val=a.val.val)

theorem main : H1 → H2 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro production exclusion
  refine fun n hn M h₁ h₂ hmod hlarge P hP ⟨c,hc,hder⟩ => ?_
  obtain ⟨B,hB⟩:=exclusion n hn M h₁ h₂ P hP
  obtain ⟨p,hp,hb,_,hs,hg,q,hq,witness⟩:=production n hn M h₁ h₂ hmod hlarge c hc hder B
  exact hB p hp hb hs hg q hq witness

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1
