import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1

namespace OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1

open Filter Finset

def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  let N := 8*m+3
  ((N : ℝ) ^ (3 / 10 : ℝ)) < ((((range (N+1)) ×ˢ ((range (N+1)) ×ˢ (range (N+1)))).filter (fun v : ℕ × ℕ × ℕ => v.1^2 + v.2.1^2 + v.2.2^2 = N)).card : ℝ)

def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let N := 8*m+3
  (3 * N.sqrt.sqrt : ℝ) < (N : ℝ) ^ (3 / 10 : ℝ)

theorem main : H1 → H2 → OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1.H1 := by
  intro hdeep hcomp
  unfold H1 at hdeep
  unfold H2 at hcomp
  unfold OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1.H1
  filter_upwards [hdeep, hcomp] with m hd hc
  dsimp only at hd hc ⊢
  exact_mod_cast hc.trans hd

end OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1
