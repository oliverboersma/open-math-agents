import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.AlgebraicClosure
/-!
# Circle and arithmetic restrictions on a critical diameter pentagon
A circle exceeding half the configuration by more than seventeen points forces algebraic
coordinates up to similarity. The normalized distance field of a critical diameter pentagon
admits no embedding into the dyadic numbers, and any finite such field has even degree.
The second-largest distance is at least the diameter divided by the golden ratio and
has multiplicity at most n+10, and at most n+7 above that ratio. Three equal short chords
force all five to agree. The missing diameter at the other points forces at least
9n−30 more ordered bases with two bisector centers than with none. The remaining geometric cases separate configurations according to their largest circle.
-/
open EuclideanGeometry
namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1

/-- Threshold for all circles, algebraic coordinates for a large circle, and the sharper bound for commensurable squared distances. -/
def H1 : Prop := ∀A : Finset ℝ²,NonTrilinear (A:Set ℝ²) → A.card=2*distinctDistances A+2 → (∀c:ℝ²,∀r:ℝ,let b := (A.filter fun x => dist x c=r).card; let N := A.card-1; 2*b≤N+36 ∨ (2*b-N)^2≤36*N) ∧ ((∀c:ℝ²,∀r:ℝ,2*(A.filter fun x => dist x c=r).card≤A.card+35) ∨ (∃f:ℝ²→ℂ,∃s:ℝ,0<s ∧ (∀x y,dist (f x) (f y)=s*dist x y) ∧ ∀x∈A,IsAlgebraic ℚ (f x))) ∧ ((∃s:ℝ,0<s ∧ ∀x∈A,∀y∈A,∃q:ℚ,dist x y^2=s*q) → (∀c:ℝ²,∀r:ℝ,(A.filter fun x => dist x c=r).card≤A.card/2+2))

/-- Dyadic and degree restrictions on normalized lengths. Sharp lower bound for the second-largest distance and an additive upper bound on its multiplicity. -/
def H2 : Prop := ∀A : Finset ℝ²,NonTrilinear (A:Set ℝ²) → A.card=2*distinctDistances A+2 → ∀M:ℝ,0<M → (∀u∈distanceSet A,u≤M) → (∃ a b c d e : A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧
      dist d.1 e.1=M ∧ dist e.1 a.1=M) → distanceMultiplicity A M≤5 → (∀K:Subfield ℝ,(∀d∈distanceSet A,d/M∈K) → IsEmpty (K→+*ℚ_[2]) ∧ Even (Module.finrank ℚ K)) ∧ (∀d∈(distanceSet A).erase M,(∀u∈(distanceSet A).erase M,u≤d) → (3-Real.sqrt 5)*M^2≤2*d^2 ∧ distanceMultiplicity A d≤A.card+10 ∧ ((3-Real.sqrt 5)*M^2<2*d^2 → distanceMultiplicity A d≤A.card+7)) ∧ (∀z:Fin 5→A,Function.Injective z → (∀i,dist (z i).1 (z (i+1)).1=M) → ∀r:ℝ,let g:=fun i=>dist (z i).1 (z (i+2)).1; 3≤(Finset.univ.filter fun i=>g i=r).card → ∀i,g i=r) ∧ (let k := fun b : ℝ²×ℝ² => (A.filter fun p => dist p b.1=dist p b.2).card
    (9*A.card-30)+(A.offDiag.filter fun b => k b=0).card ≤ (A.offDiag.filter fun b => k b=2).card)

/-- All circles contain at most half the set plus seventeen points, subject to the arithmetic restrictions. -/
def H3 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) →
    A.card=2*distinctDistances A+2 → 5≤distinctDistances A →
    (∀ (c : ℝ²) (r : ℝ), 3*(A.filter (fun z => dist z c=r)).card≤4*distinctDistances A+2) →
    (let k := fun b : ℝ²×ℝ² => (A.filter fun p => dist p b.1=dist p b.2).card
    (9*A.card-30)+(A.offDiag.filter fun b => k b=0).card ≤ (A.offDiag.filter fun b => k b=2).card) → (∀ (T : Finset Circle) (G : Subgroup Circle) (m : ℕ) (P : Finset ℂ) (f : ℂ→ℝ²) (s : ℝ),
      (G:Set Circle)=T → 2 ≤ m → m.Coprime T.card → 0<s →
      (∀ x y, dist (f x) (f y)=s*dist x y) → (∀ z∈T, f (z:ℂ)∈A) → (∀ p∈P, f p∈A) →
      (∀ p∈P, p≠0 ∧ ‖p‖≠1) → Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ) →
      P.card*T.card+(2*min m 9)*P.card ≤ 2*distinctDistances A+(2*min m 9)*P.card*P.card) →
    ∀ M∈distanceSet A, (∀ d∈distanceSet A, d≤M) →
    (∃ B⊆A, A.card/2≤B.card ∧ ∀ x∈B, ∀ y∈B, dist x y<M) →
    (∃ d∈(distanceSet A).erase M, A.card+4≤distanceMultiplicity A d) →
    distanceMultiplicity A M≤5 → (∃ a b c d e : A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧
      dist d.1 e.1=M ∧ dist e.1 a.1=M) →
    (∀c:ℝ²,∀r:ℝ,2*(A.filter fun x => dist x c=r).card≤A.card+35) → (∀K:Subfield ℝ,(∀d∈distanceSet A,d/M∈K) → IsEmpty (K→+*ℚ_[2]) ∧ Even (Module.finrank ℚ K)) → (∀d∈(distanceSet A).erase M,(∀u∈(distanceSet A).erase M,u≤d) → (3-Real.sqrt 5)*M^2≤2*d^2 ∧ distanceMultiplicity A d≤A.card+10 ∧ ((3-Real.sqrt 5)*M^2<2*d^2 → distanceMultiplicity A d≤A.card+7)) → (∀z:Fin 5→A,Function.Injective z → (∀i,dist (z i).1 (z (i+1)).1=M) → ∀r:ℝ,let g:=fun i=>dist (z i).1 (z (i+2)).1; 3≤(Finset.univ.filter fun i=>g i=r).card → ∀i,g i=r) → ((∃s:ℝ,0<s ∧ ∀x∈A,∀y∈A,∃q:ℚ,dist x y^2=s*q) → (∀c:ℝ²,∀r:ℝ,(A.filter fun x => dist x c=r).card≤A.card/2+2)) → ∃ x∈A, ∃ y∈A.erase x, ∃ d∈distanceSet A, d∉distanceSet ((A.erase x).erase y)

/-- A larger circle exists. The configuration has algebraic coordinates up to similarity and its squared distances are incommensurable. -/
def H4 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) →
    A.card=2*distinctDistances A+2 → 5≤distinctDistances A →
    (∀ (c : ℝ²) (r : ℝ), 3*(A.filter (fun z => dist z c=r)).card≤4*distinctDistances A+2) →
    (let k := fun b : ℝ²×ℝ² => (A.filter fun p => dist p b.1=dist p b.2).card
    (9*A.card-30)+(A.offDiag.filter fun b => k b=0).card ≤ (A.offDiag.filter fun b => k b=2).card) → (∀ (T : Finset Circle) (G : Subgroup Circle) (m : ℕ) (P : Finset ℂ) (f : ℂ→ℝ²) (s : ℝ),
      (G:Set Circle)=T → 2 ≤ m → m.Coprime T.card → 0<s →
      (∀ x y, dist (f x) (f y)=s*dist x y) → (∀ z∈T, f (z:ℂ)∈A) → (∀ p∈P, f p∈A) →
      (∀ p∈P, p≠0 ∧ ‖p‖≠1) → Set.InjOn (fun p : ℂ => ‖p‖) (P:Set ℂ) →
      P.card*T.card+(2*min m 9)*P.card ≤ 2*distinctDistances A+(2*min m 9)*P.card*P.card) →
    ∀ M∈distanceSet A, (∀ d∈distanceSet A, d≤M) →
    (∃ B⊆A, A.card/2≤B.card ∧ ∀ x∈B, ∀ y∈B, dist x y<M) →
    (∃ d∈(distanceSet A).erase M, A.card+4≤distanceMultiplicity A d) →
    distanceMultiplicity A M≤5 → (∃ a b c d e : A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧
      dist d.1 e.1=M ∧ dist e.1 a.1=M) →
    (∃c:ℝ²,∃r:ℝ,A.card+35<2*(A.filter fun x => dist x c=r).card) → (∃f:ℝ²→ℂ,∃s:ℝ,0<s ∧ (∀x y,dist (f x) (f y)=s*dist x y) ∧ ∀x∈A,IsAlgebraic ℚ (f x)) → (∀c:ℝ²,∀r:ℝ,let b := (A.filter fun x => dist x c=r).card; let N := A.card-1; 2*b≤N+36 ∨ (2*b-N)^2≤36*N) → ¬(∃s:ℝ,0<s ∧ ∀x∈A,∀y∈A,∃q:ℚ,dist x y^2=s*q) → (∀K:Subfield ℝ,(∀d∈distanceSet A,d/M∈K) → IsEmpty (K→+*ℚ_[2]) ∧ Even (Module.finrank ℚ K)) → (∀d∈(distanceSet A).erase M,(∀u∈(distanceSet A).erase M,u≤d) → (3-Real.sqrt 5)*M^2≤2*d^2 ∧ distanceMultiplicity A d≤A.card+10 ∧ ((3-Real.sqrt 5)*M^2<2*d^2 → distanceMultiplicity A d≤A.card+7)) → (∀z:Fin 5→A,Function.Injective z → (∀i,dist (z i).1 (z (i+1)).1=M) → ∀r:ℝ,let g:=fun i=>dist (z i).1 (z (i+2)).1; 3≤(Finset.univ.filter fun i=>g i=r).card → ∀i,g i=r) → ∃ x∈A, ∃ y∈A.erase x, ∃ d∈distanceSet A, d∉distanceSet ((A.erase x).erase y)

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1.H2 := by
  classical
  intro hcircle hfields hthin hrich A hn hcard hD hcir strongBis horb M hM hmax hB hrep hmult hcyc
  have hm : 0<M := by
    obtain ⟨⟨x,y⟩,hp,e⟩ := Finset.mem_image.mp hM
    exact e ▸ dist_pos.mpr (Finset.mem_offDiag.mp hp).2.2
  obtain ⟨hbound,halt,hsquare⟩ := hcircle A hn hcard
  obtain ⟨hK,hsecond,hrigid,strongBis⟩ := hfields A hn hcard M hm hmax hcyc hmult
  by_cases small : (∀c:ℝ²,∀r:ℝ,2*(A.filter fun x => dist x c=r).card≤A.card+35)
  · exact hthin A hn hcard hD hcir strongBis horb M hM hmax hB hrep hmult hcyc small hK hsecond hrigid hsquare
  · have large := small
    push Not at large
    obtain ⟨c,r,hcr⟩ := large
    apply hrich A hn hcard hD hcir strongBis horb M hM hmax hB hrep hmult hcyc ⟨c,r,hcr⟩
      (halt.resolve_left small) hbound _ hK hsecond hrigid
    intro hq
    have h := hsquare hq c r
    omega
end OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1
