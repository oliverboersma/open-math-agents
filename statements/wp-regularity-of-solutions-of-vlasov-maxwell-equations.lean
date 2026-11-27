import Mathlib

/-!
# Regularity of solutions of Vlasov–Maxwell equations

Source: https://en.wikipedia.org/wiki/Vlasov–Maxwell_equations
(section "The Vlasov–Maxwell system of equations" of the article "Vlasov equation").
Credit: @my-other-github-account

The source lists "regularity of solutions of Vlasov–Maxwell equations" as unsolved and states the
system for finitely many particle species `α` with charge `q α`, rest mass `m α`, relativistic
velocity `v_α(p) = (p / m_α) / √(1 + |p|² / (m_α c)²)`, and one shared self-consistent
electromagnetic field, with `ρ = ∑ α q α ∫ f α dp`, `j = ∑ α q α ∫ f α v_α dp` and SI Maxwell
equations (`μ₀ ε₀ c² = 1`).

The source does not spell out the regularity question. We use the standard reading of the open
problem in three space dimensions, as stated e.g. by G. Rein, *Global weak solutions to the
relativistic Vlasov–Maxwell system revisited*, Comm. Math. Sci. 2 (2004), §1
(arXiv:math-ph/0403002): "Global existence and uniqueness of sufficiently smooth solutions to
this initial value problem is an open problem", for smooth, compactly supported particle data whose
fields satisfy the constraint equations. (Global *weak* solutions are known by DiPerna–Lions, so
the question concerns classical solutions.)

Precisely: for every finite set of species with arbitrary nonzero charges and positive masses,
every smooth, compactly supported, nonnegative family of initial densities and smooth initial fields
with all derivatives bounded and finite energy (`L²`) satisfying `∇·E₀ = ρ₀/ε₀`, `∇·B₀ = 0`,
there is a global-in-time classical solution for `t ≥ 0`, it is `C^∞` on every finite time slab,
and it is the unique classical solution. A classical solution is `C¹`, solves the system pointwise,
has nonnegative densities, fields continuous in time with values in `L²`, and phase-space support
contained in a compact set on each finite time interval (the solution class of Glassey–Strauss).
No size, symmetry or neutrality restriction is imposed on the data.
-/

namespace OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations

noncomputable section
open MeasureTheory Set
open scoped ContDiff

abbrev Vec := EuclideanSpace ℝ (Fin 3)
/-- Phase space: position `x` and momentum `p`. -/
abbrev Phase := Vec × Vec
abbrev Density := ℝ × Phase → ℝ
abbrev Field := ℝ × Vec → Vec

def basis (i : Fin 3) : Vec := EuclideanSpace.single i 1

def cross (a b : Vec) : Vec := WithLp.toLp 2
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- The `i`-th partial derivative of a scalar function on `ℝ³`. -/
def partialDeriv (g : Vec → ℝ) (x : Vec) (i : Fin 3) : ℝ := fderiv ℝ g x (basis i)

def divergence (F : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i : Fin 3, partialDeriv (fun y => F y i) x i

def curl (F : Vec → Vec) (x : Vec) : Vec := WithLp.toLp 2
  ![partialDeriv (fun y => F y 2) x 1 - partialDeriv (fun y => F y 1) x 2,
    partialDeriv (fun y => F y 0) x 2 - partialDeriv (fun y => F y 2) x 0,
    partialDeriv (fun y => F y 1) x 0 - partialDeriv (fun y => F y 0) x 1]

/-- Physical constants and the species of the plasma (finitely many, indexed by `ι`). -/
structure Plasma (ι : Type) [Fintype ι] where
  c : ℝ
  ε₀ : ℝ
  μ₀ : ℝ
  charge : ι → ℝ
  mass : ι → ℝ
  c_pos : 0 < c
  ε₀_pos : 0 < ε₀
  μ₀_pos : 0 < μ₀
  maxwell_const : μ₀ * ε₀ * c ^ 2 = 1
  mass_pos : ∀ α, 0 < mass α
  charge_ne : ∀ α, charge α ≠ 0

variable {ι : Type} [Fintype ι]

/-- Relativistic velocity `v_α(p) = (p / m_α) / √(1 + |p|² / (m_α c)²)`. -/
def velocity (P : Plasma ι) (α : ι) (p : Vec) : Vec :=
  (Real.sqrt (1 + ‖p‖ ^ 2 / (P.mass α * P.c) ^ 2))⁻¹ • ((P.mass α)⁻¹ • p)

/-- Charge density `ρ = ∑ α q_α ∫ f_α dp` of a family of phase-space densities. -/
def chargeDensity (P : Plasma ι) (g : ι → Phase → ℝ) (x : Vec) : ℝ :=
  ∑ α, P.charge α * ∫ p : Vec, g α (x, p)

/-- Current density `j = ∑ α q_α ∫ f_α v_α dp`. -/
def currentDensity (P : Plasma ι) (g : ι → Phase → ℝ) (x : Vec) : Vec :=
  ∑ α, P.charge α • ∫ p : Vec, g α (x, p) • velocity P α p

structure Datum (ι : Type) where
  f₀ : ι → Phase → ℝ
  E₀ : Vec → Vec
  B₀ : Vec → Vec

def BoundedSmooth (F : Vec → Vec) : Prop :=
  ContDiff ℝ ∞ F ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ x : Vec, ‖iteratedFDeriv ℝ n F x‖ ≤ C

/-- Smooth admissible initial data. -/
def Admissible (P : Plasma ι) (d : Datum ι) : Prop :=
  (∀ α, ContDiff ℝ ∞ (d.f₀ α) ∧ HasCompactSupport (d.f₀ α) ∧ ∀ z, 0 ≤ d.f₀ α z) ∧
  BoundedSmooth d.E₀ ∧ BoundedSmooth d.B₀ ∧
  MemLp d.E₀ 2 volume ∧ MemLp d.B₀ 2 volume ∧
  (∀ x, divergence d.E₀ x = chargeDensity P d.f₀ x / P.ε₀) ∧
  (∀ x, divergence d.B₀ x = 0)

structure Solution (ι : Type) where
  f : ι → Density
  E : Field
  B : Field

def densityHalfSpace : Set (ℝ × Phase) := {z | 0 ≤ z.1}
def fieldHalfSpace : Set (ℝ × Vec) := {z | 0 ≤ z.1}
def densitySlab (T : ℝ) : Set (ℝ × Phase) := {z | z.1 ∈ Icc 0 T}
def fieldSlab (T : ℝ) : Set (ℝ × Vec) := {z | z.1 ∈ Icc 0 T}

/-- `t ↦ F(t, ·)` is continuous from `[0, ∞)` into `L²(ℝ³)`. -/
def TimeContinuousL2 (F : Field) : Prop :=
  ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec),
    ContinuousOn F₂ (Ici 0) ∧ ∀ t, 0 ≤ t → (F₂ t : Vec → Vec) =ᵐ[volume] fun x => F (t, x)

/-- The Vlasov–Maxwell system, pointwise for `t ≥ 0` (one-sided time derivative at `t = 0`). -/
def Equations (P : Plasma ι) (s : Solution ι) : Prop := ∀ t, 0 ≤ t →
  (∀ α x p,
    derivWithin (fun t' => s.f α (t', x, p)) (Ici 0) t +
    (∑ i : Fin 3, velocity P α p i * partialDeriv (fun y => s.f α (t, y, p)) x i) +
    P.charge α * (∑ i : Fin 3, (s.E (t, x) + cross (velocity P α p) (s.B (t, x))) i *
      partialDeriv (fun p' => s.f α (t, x, p')) p i) = 0) ∧
  (∀ x, curl (fun y => s.B (t, y)) x =
    P.μ₀ • currentDensity P (fun α z => s.f α (t, z)) x +
      (P.μ₀ * P.ε₀) • derivWithin (fun t' => s.E (t', x)) (Ici 0) t) ∧
  (∀ x, curl (fun y => s.E (t, y)) x = -derivWithin (fun t' => s.B (t', x)) (Ici 0) t) ∧
  (∀ x, divergence (fun y => s.E (t, y)) x =
    chargeDensity P (fun α z => s.f α (t, z)) x / P.ε₀) ∧
  (∀ x, divergence (fun y => s.B (t, y)) x = 0)

def CompactOnFiniteHorizons (s : Solution ι) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ K : Set Phase, IsCompact K ∧
    ∀ α, ∀ t ∈ Icc 0 T, tsupport (fun z => s.f α (t, z)) ⊆ K

/-- A global classical solution with initial datum `d`. -/
def Classical (P : Plasma ι) (d : Datum ι) (s : Solution ι) : Prop :=
  (∀ α, ContDiffOn ℝ 1 (s.f α) densityHalfSpace) ∧
  ContDiffOn ℝ 1 s.E fieldHalfSpace ∧ ContDiffOn ℝ 1 s.B fieldHalfSpace ∧
  (∀ α t, 0 ≤ t → ∀ z, 0 ≤ s.f α (t, z)) ∧
  TimeContinuousL2 s.E ∧ TimeContinuousL2 s.B ∧
  CompactOnFiniteHorizons s ∧ Equations P s ∧
  (∀ α z, s.f α (0, z) = d.f₀ α z) ∧
  (∀ x, s.E (0, x) = d.E₀ x) ∧ (∀ x, s.B (0, x) = d.B₀ x)

def SmoothOnFiniteHorizons (s : Solution ι) : Prop := ∀ T : ℝ, 0 ≤ T →
  (∀ α, ContDiffOn ℝ ∞ (s.f α) (densitySlab T)) ∧
  ContDiffOn ℝ ∞ s.E (fieldSlab T) ∧ ContDiffOn ℝ ∞ s.B (fieldSlab T)

def SameNonnegativeTime (s s' : Solution ι) : Prop := ∀ t, 0 ≤ t →
  (∀ α z, s.f α (t, z) = s'.f α (t, z)) ∧
  (∀ x, s.E (t, x) = s'.E (t, x)) ∧ (∀ x, s.B (t, x) = s'.B (t, x))

/-- Smooth data for the three-dimensional relativistic Vlasov–Maxwell system with finitely many
species generate a unique global classical solution, smooth on every finite time interval. -/
theorem main :
    ∀ (ι : Type) [Fintype ι] (P : Plasma ι) (d : Datum ι), Admissible P d →
      ∃ s : Solution ι, Classical P d s ∧ SmoothOnFiniteHorizons s ∧
        ∀ s' : Solution ι, Classical P d s' → SameNonnegativeTime s s' := by
  sorry

end

end OMA.S_wp_regularity_of_solutions_of_vlasov_maxwell_equations
