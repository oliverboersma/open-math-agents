import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R2

-- Reduction Erdos1160.erdos_1160.variants.sum.R2.H1.R1 of step Erdos1160.erdos_1160.variants.sum.R2.H1
-- Credit: @gertjanvdgoot

/-!
Split the two-power terms g(2^k), k < m, at 4k ≤ 3m.

* H1 (low powers, k ≤ 3m/4): elementary. The pc-presentation bound g(2^k)^6 ≤ 2^(k^3) gives
  g(2^k) ≤ 2^((27/64) m^3 / 6) ≈ 2^(0.0703 m^3), while Higman's lower bound gives
  g(2^m) ≥ 2^((2 m^3 - 12 m^2)/27) ≈ 2^(0.0741 m^3). The cubic margin absorbs the factor 4m.
* H2 (high powers, 3m/4 < k < m): needs growth of g(2^k) between k and m with m - k < m/4,
  i.e. the sharp two-group enumeration (Li and Qiao, arXiv:2610.14509). This is the hard range.

main adds the two halves.
-/

open Filter Finset Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1

/-- Four times the low two-power terms stay below g(2^m). -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  4 * ∑ k ∈ (Finset.range m).filter (fun k => 4 * k ≤ 3 * m), g (2 ^ k) ≤ g (2 ^ m)

/-- Four times the high two-power terms stay below g(2^m). -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  4 * ∑ k ∈ (Finset.range m).filter (fun k => ¬ 4 * k ≤ 3 * m), g (2 ^ k) ≤ g (2 ^ m)

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R2.H1 := by
  intro low high
  filter_upwards [low, high] with m hl hh
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range m) (fun k => 4 * k ≤ 3 * m)]
  omega

end OMA.R_Erdos1160_erdos_1160_variants_sum_R2_H1_R1
