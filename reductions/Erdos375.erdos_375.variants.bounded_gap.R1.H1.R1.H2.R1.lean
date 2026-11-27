import OMAReductions.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1

/-! Short-interval smooth numbers. We remove the prime restriction in one
variable by Cauchy–Schwarz on blocks of width N^40. Van der Corput's
second-derivative estimate applies to the reciprocal phase for each pair
from the same block. A truncated Fourier bound for the periodic second
Bernoulli polynomial recovers the centered floor error. -/

namespace OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1
open Filter Finset

/-- Off-diagonal estimate on the full integer interval, for nearby denominators. -/
def H1 : Prop :=
  ∀ N t h : ℕ, 2 ≤ N → N^1000 ≤ t → t ≤ N^1001 → 1 ≤ h → h ≤ N^20 →
    let J := Ioc (N^251) (N^252)
    let u (p q : ℕ) := (t:ℝ)/((p*q:ℕ):ℝ)
    let e (u : ℝ) := Complex.exp (((2*Real.pi*u : ℝ) : ℂ)*Complex.I)
    ∀ a ∈ J, ∀ b ∈ J, a < b → b-a ≤ N^40 →
      ‖∑ p ∈ J, e ((h:ℝ)*(u p a - u p b))‖ ≤ 16*(N:ℝ)^188

/-- Squaring on blocks and completing the first variable to all integers. -/
def H2 : Prop :=
  ∀ N t h : ℕ, 2 ≤ N → N^1000 ≤ t → t ≤ N^1001 → 1 ≤ h → h ≤ N^20 →
    let J := Ioc (N^251) (N^252)
    let u (p q : ℕ) := (t:ℝ)/((p*q:ℕ):ℝ)
    let e (u : ℝ) := Complex.exp (((2*Real.pi*u : ℝ) : ℂ)*Complex.I)
    let P := J.filter Nat.Prime
    (∀ a ∈ J, ∀ b ∈ J, a < b → b-a ≤ N^40 →
      ‖∑ p ∈ J, e ((h:ℝ)*(u p a - u p b))‖ ≤ 16*(N:ℝ)^188) →
      ‖∑ w ∈ P ×ˢ P, e ((h:ℝ)*u w.1 w.2)‖ ≤ 10*(N:ℝ)^484

/-- Truncated Fourier smoothing of the centered quotient error. -/
def H3 : Prop :=
  ∀ N t : ℕ, 2 ≤ N →
    let J := Ioc (N^251) (N^252)
    let P := J.filter Nat.Prime
    let u (p q : ℕ) := (t:ℝ)/((p*q:ℕ):ℝ)
    let e (u : ℝ) := Complex.exp (((2*Real.pi*u : ℝ) : ℂ)*Complex.I)
    (∀ h : ℕ, 1 ≤ h → h ≤ N^20 → ‖∑ w ∈ P ×ˢ P, e ((h:ℝ)*u w.1 w.2)‖ ≤ 10*(N:ℝ)^484) →
    |∑ w ∈ P ×ˢ P, ((((t/(w.1*w.2):ℕ):ℝ) - u w.1 w.2) + 1/2)| ≤ 1000*(N:ℝ)^498

theorem main : H1 → H2 → H3 → OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1.H2 := by
  intro estimate blocks smooth ε hε
  obtain ⟨n₀,hn₀⟩ := exists_nat_ge (1000/ε)
  filter_upwards [eventually_ge_atTop (max 2 n₀)] with N hN
  have two : 2 ≤ N := (le_max_left _ _).trans hN
  have hn : n₀ ≤ N := (le_max_right _ _).trans hN
  intro t ht ht'
  have bound := smooth N t two (fun h hp hmax =>
    blocks N t h two ht ht' hp hmax (estimate N t h two ht ht' hp hmax))
  apply bound.trans
  have rat : 1000/ε ≤ (N:ℝ) := hn₀.trans (Nat.cast_le.mpr hn)
  have coeff := (div_le_iff₀ hε).mp rat
  calc
    1000*(N:ℝ)^498 ≤ ((N:ℝ)*ε)*(N:ℝ)^498 := by gcongr
    _ = ε*(N:ℝ)^499 := by ring

end OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1_H2_R1
