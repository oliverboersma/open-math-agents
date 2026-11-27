import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1

/-!
# Three-distance five-point bases in a four-distance set

Encode the ten edges of the ordered base by the three distances they realize. The order of
the edges is lexicographic in their vertex indices. The ternary code distinguishes patterns
after an ordering of vertices and colors has been chosen. Gram identities classify the bases.
The three extension families collect the resulting number-field cases.
-/

open EuclideanGeometry

namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1

/-- A diameter-free five-vertex base with three distances has one of the listed three-color patterns. -/
def H1 : Prop := ∀ B : Finset ℝ², NonTrilinear (B:Set ℝ²) → B.card=5 → distinctDistances B=3 → ∃ (p : Fin 5≃B) (r : Fin 3≃(distanceSet B)) (c : Fin 10→Fin 3),
    (let e : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]; ∀ k, dist (p (e k).1).1 (p (e k).2).1=(r (c k)).1) ∧
    ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈([3440,3197,3233,3074,835,3072,3203,157,123,401,824,834,853,3194,3231]:List ℕ)

/-- Five further points cannot extend the base patterns in family 1 to a four-distance ten-set. -/
def H2 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) → A.card=10 → distinctDistances A=4 →
    ∀ M∈distanceSet A, ∀ B⊆A, B.card=5 → (∀ a∈B, ∀ b∈B, dist a b<M) → distinctDistances B=3 → ∀ (p : Fin 5≃B) (r : Fin 3≃(distanceSet B)) (c : Fin 10→Fin 3),
    (let e : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]; ∀ k, dist (p (e k).1).1 (p (e k).2).1=(r (c k)).1) →
    ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈([3440,3197,3233,3074]:List ℕ) → False

/-- Five further points cannot extend the base patterns in family 2 to a four-distance ten-set. -/
def H3 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) → A.card=10 → distinctDistances A=4 →
    ∀ M∈distanceSet A, ∀ B⊆A, B.card=5 → (∀ a∈B, ∀ b∈B, dist a b<M) → distinctDistances B=3 → ∀ (p : Fin 5≃B) (r : Fin 3≃(distanceSet B)) (c : Fin 10→Fin 3),
    (let e : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]; ∀ k, dist (p (e k).1).1 (p (e k).2).1=(r (c k)).1) →
    ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈([835,3072,3203,157,123]:List ℕ) → False

/-- Five further points cannot extend the base patterns in family 3 to a four-distance ten-set. -/
def H4 : Prop := ∀ A : Finset ℝ², NonTrilinear (A:Set ℝ²) → A.card=10 → distinctDistances A=4 →
    ∀ M∈distanceSet A, ∀ B⊆A, B.card=5 → (∀ a∈B, ∀ b∈B, dist a b<M) → distinctDistances B=3 → ∀ (p : Fin 5≃B) (r : Fin 3≃(distanceSet B)) (c : Fin 10→Fin 3),
    (let e : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]; ∀ k, dist (p (e k).1).1 (p (e k).2).1=(r (c k)).1) →
    ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈([401,824,834,853,3194,3231]:List ℕ) → False

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1.H2 := by
  classical
  intro hs h1 h2 h3 A hn hA hd M hM B hBA hB hf hthree
  have hnc : NonTrilinear (B:Set ℝ²) := by
    intro a ha b hb d hd ab bd ad
    exact hn (hBA ha) (hBA hb) (hBA hd) ab bd ad
  obtain ⟨p,r,c,hc,hh⟩ := hs B hnc hB hthree
  change ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈(([3440,3197,3233,3074]:List ℕ) ++ ([835,3072,3203,157,123]:List ℕ) ++ ([401,824,834,853,3194,3231]:List ℕ):List ℕ) at hh
  rcases List.mem_append.mp hh with h|h
  · rcases List.mem_append.mp h with h|h
    · exact h1 A hn hA hd M hM B hBA hB hf hthree p r c hc h
    · exact h2 A hn hA hd M hM B hBA hB hf hthree p r c hc h
  · exact h3 A hn hA hd M hM B hBA hB hf hthree p r c hc h

end OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1
