import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1

/-!
# Extension certificates for three-distance bases, family 1

The pattern classes have independent squared-distance compatibility graphs. Each step
checks four-colorability of the graphs for its specified codes, or excludes the base by a
noncollinearity identity.
-/

open EuclideanGeometry

namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H2_R1

/-- First set of explicit algebraic five-point base patterns. -/
def H1 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) → A.card=10 → distinctDistances A=4 →
    ∀ M∈distanceSet A, ∀ B⊆A, B.card=5 → (∀ a∈B, ∀ b∈B, dist a b<M) → distinctDistances B=3 → ∀ (p : Fin 5≃B) (r : Fin 3≃(distanceSet B)) (c : Fin 10→Fin 3),
    (let e : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]; ∀ k, dist (p (e k).1).1 (p (e k).2).1=(r (c k)).1) →
    ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈([3440,3197]:List ℕ) → False

/-- Second set of explicit algebraic five-point base patterns. -/
def H2 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) → A.card=10 → distinctDistances A=4 →
    ∀ M∈distanceSet A, ∀ B⊆A, B.card=5 → (∀ a∈B, ∀ b∈B, dist a b<M) → distinctDistances B=3 → ∀ (p : Fin 5≃B) (r : Fin 3≃(distanceSet B)) (c : Fin 10→Fin 3),
    (let e : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]; ∀ k, dist (p (e k).1).1 (p (e k).2).1=(r (c k)).1) →
    ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈([3233,3074]:List ℕ) → False

theorem main : H1 → H2 → OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1.H2 := by
  intro h1 h2 A hn hA hd M hM B hBA hB hf hthree p r c hc hh
  change ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈(([3440,3197]:List ℕ) ++ ([3233,3074]:List ℕ):List ℕ) at hh
  rcases List.mem_append.mp hh with h|h
  · exact h1 A hn hA hd M hM B hBA hB hf hthree p r c hc h
  · exact h2 A hn hA hd M hM B hBA hB hf hthree p r c hc h

end OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H2_R1
