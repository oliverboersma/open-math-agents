import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# The first derivative of the translated elliptic unit

Integer multiplication on the period lattice expresses the finite zeta trace
as a logarithmic derivative of a product of Weierstrass functions. The
arithmetic input excludes a nonzero rational derivative in the presence
of a point of infinite order on the congruent-number curve.
-/
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1
open Complex MeasureTheory Set
open scoped Classical ComplexConjugate

lemma square_period (x : ℝ) (hx : x≠0) : ∃ M : PeriodPair, M.ω₁=(x:ℂ) ∧ M.ω₂=I*(x:ℂ) := by
  refine ⟨⟨(x:ℂ),I*(x:ℂ),?_⟩,rfl,rfl⟩
  apply LinearIndependent.pair_iff.mpr
  intro u v h
  have hr:=congrArg re h
  have hi:=congrArg im h
  simp [Complex.mul_re,Complex.mul_im,hx] at hr hi
  exact ⟨hr,hi⟩

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
  let f : ℂ := (4*n:ℕ)
  let Λ : Submodule ℤ ℂ := Submodule.span ℤ {f,f*Complex.I}
  let ζ (z : ℂ) := ∑' w : Λ, ((z-(w:ℂ))⁻¹+(w:ℂ)⁻¹+z/(w:ℂ)^2)
  let U := ∑ v : ZMod (4*n) × ZMod (4*n), (χ v:ℂ)*(-conj
    ((a:ℂ)*ζ ((a:ℂ)*(b v:ℂ))-(a:ℂ)^2*ζ (b v:ℂ)))
  ∀ r : ℚ, r≠0 → ((a:ℂ)^2-(a:ℂ))*((r:ℂ)*(ω:ℂ))=U → ∃ c : ℚ, c≠0 ∧ logDeriv G 0=(c:ℂ)

def H2 : Prop :=
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
  n%8=2 → 2<n → ∀ P : (⟨0,0,0,-(n:ℚ)^2,0⟩ : WeierstrassCurve ℚ).toAffine.Point,
    ¬IsOfFinAddOrder P → ¬(∃ c : ℚ, c≠0 ∧ logDeriv G 0=(c:ℂ))

theorem main : H1 → H2 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1.H2 := by
  intro hG hP
  refine fun n hn h8 hlarge P hInf r hv => ?_
  by_contra hr
  have hpos:=TunnellCoates.realPeriod_pos (show (0:ℝ)<n by exact_mod_cast hn)
  obtain ⟨M,h₁,h₂⟩:=square_period _ hpos.ne'
  exact hP n hn M h₁ h₂ h8 hlarge P hInf (hG n hn M h₁ h₂ r hr hv)

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1
