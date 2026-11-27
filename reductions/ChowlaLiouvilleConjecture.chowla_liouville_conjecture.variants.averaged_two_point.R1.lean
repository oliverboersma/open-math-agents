import FormalConjectures.Wikipedia.ChowlaLiouvilleConjecture
import Mathlib

/-! The averaged two-point Chowla statement in iterated form (first H large, then N large)
from the form that is uniform along every H = H(N) tending to infinity with H(N) ≤ N. The
uniform form is the theorem of Matomäki, Radziwiłł and Tao, An averaged form of Chowla's
conjecture, Algebra Number Theory 9 (2015), and is the catalogue's
chowla_liouville_conjecture.variants.averaged_two_point_uniform. The passage to the iterated
form is a diagonal argument about an arbitrary double sequence of real numbers. -/

namespace OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_R1
open Filter Topology

/-- Matomäki, Radziwiłł and Tao: the averaged two-point correlation tends to 0 along every
H(N) tending to infinity with H(N) ≤ N. -/
def H1 : Prop := ∀ H : ℕ → ℕ, Tendsto H atTop atTop → (∀ᶠ N : ℕ in atTop, H N ≤ N) →
  Tendsto
    (fun N : ℕ ↦
      (∑ h ∈ Finset.Icc 1 (H N),
        |∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h) : ℝ)| /
            (N : ℝ)) / (H N : ℝ))
    atTop (𝓝 0)

/-- A double sequence that tends to 0 along every diagonal H(N) tending to infinity with
H(N) ≤ N is eventually small in the iterated sense. -/
def H2 : Prop := ∀ g : ℕ → ℕ → ℝ,
  (∀ H : ℕ → ℕ, Tendsto H atTop atTop → (∀ᶠ N : ℕ in atTop, H N ≤ N) →
    Tendsto (fun N : ℕ ↦ g (H N) N) atTop (𝓝 0)) →
  ∀ ε : ℝ, 0 < ε → ∀ᶠ H : ℕ in atTop, ∀ᶠ N : ℕ in atTop, g H N < ε

theorem main : H1 → H2 →
    type_of% @ChowlaLiouvilleConjecture.chowla_liouville_conjecture.variants.averaged_two_point := by
  intro h1 h2 ε hε
  exact h2 (fun H N : ℕ ↦
    (∑ h ∈ Finset.Icc 1 H,
      |∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.liouville n * ArithmeticFunction.liouville (n + h) : ℝ)| /
          (N : ℝ)) / (H : ℝ)) h1 ε hε

end OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_R1
