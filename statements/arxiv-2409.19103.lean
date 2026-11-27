import Mathlib

/-!
Source: https://arxiv.org/abs/2409.19103
Credit: @my-other-github-account

Definitions adapted from OpenAI's openai/math, Apache-2.0,
commit 3344da59991ed94f9ba711217b29c1d760badfa6,
lean/OAI/Analysis/CircleDomains/LengthArea.lean.
Licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0
Distributed on an AS IS basis, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.
Modifications: standalone namespace; no analytic helper theorems;
removability quantifies over all homeomorphisms as in Rajala's paper.

The survey explicitly states Koebe's conjecture for domains in the Riemann
sphere (Introduction and Section 2). IsConnected includes nonemptiness.
The charts are the finite complex coordinate and reciprocal coordinate at
infinity. A nonzero complex derivative gives holomorphic conformality.
Möbius images of the unit closed disk include disks containing infinity.
This file states the conjecture only; it does not assert a completed proof.
-/

namespace OMA.S_arxiv_2409_19103
open Set Classical
open scoped OnePoint

abbrev Sphere := OnePoint ℂ
abbrev Mobius := Matrix.GeneralLinearGroup (Fin 2) ℂ

noncomputable def sphereInv (p : Sphere) : Sphere :=
  p.elim (0 : ℂ) (fun z ↦ if z = 0 then ∞ else (z⁻¹ : ℂ))

noncomputable def finiteCoord (p : Sphere) : ℂ := p.elim 0 id

noncomputable def chart (p q : Sphere) : ℂ :=
  if p = ∞ then finiteCoord (sphereInv q) else finiteCoord q

noncomputable def chartSymm (p : Sphere) (z : ℂ) : Sphere :=
  if p = ∞ then sphereInv (z : Sphere) else (z : Sphere)

def IsConformalAt (f : Sphere → Sphere) (p : Sphere) : Prop :=
  ContinuousAt f p ∧ ∃ d : ℂ, d ≠ 0 ∧
    HasDerivAt (fun z ↦ chart (f p) (f (chartSymm p z))) d (chart p p)

def IsConformalOn (f : Sphere → Sphere) (U : Set Sphere) : Prop :=
  ∀ p ∈ U, IsConformalAt f p

def IsConformalEquivalence (f : Sphere → Sphere) (U V : Set Sphere) : Prop :=
  IsConformalOn f U ∧ MapsTo f U V ∧ ∃ g : Sphere → Sphere,
    IsConformalOn g V ∧ MapsTo g V U ∧
    (∀ z ∈ U, g (f z) = z) ∧ (∀ w ∈ V, f (g w) = w)

def IsRoundClosedDisk (K : Set Sphere) : Prop :=
  ∃ M : Mobius,
    K = (fun p : Sphere ↦ M • p) ''
      (((↑) : ℂ → Sphere) '' Metric.closedBall (0 : ℂ) 1)

def IsCircleDomain (U : Set Sphere) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ∀ p ∈ Uᶜ, (∃ q : Sphere, connectedComponentIn Uᶜ p = {q}) ∨
      IsRoundClosedDisk (connectedComponentIn Uᶜ p)

-- The paper quantifies over every sphere homeomorphism conformal off E.
-- No additional orientation hypothesis is imposed in this definition.
def IsConformallyRemovable (E : Set Sphere) : Prop :=
  IsCompact E ∧ ∀ h : Sphere ≃ₜ Sphere,
    IsConformalOn h Eᶜ → ∃ M : Mobius, ∀ p : Sphere, h p = M • p

theorem main :
    ∀ (U V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain U → IsCircleDomain V →
      IsConformallyRemovable (frontier U) → IsConformalEquivalence f U V →
      ∃ M : Mobius, ∀ p ∈ U, f p = M • p := by
  sorry

end OMA.S_arxiv_2409_19103
