import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1

/-!
# Symmetry and Gram classification for a five-point base

A labeling with minimum ternary code among vertex and color permutations gives one of 142
representatives. The squared-distance Gram identities for the last two vertices exclude the
inconsistent representatives. A base with exactly three distances uses all three colors.
-/

open EuclideanGeometry

namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H1_R1

/-- Every three-distance five-point set has a representative among these 142 vertex- and color-permutation classes. -/
def H1 : Prop := ∀ B : Finset ℝ², NonTrilinear (B:Set ℝ²) → B.card=5 → distinctDistances B=3 → ∃ (p : Fin 5≃B) (r : Fin 3≃(distanceSet B)) (c : Fin 10→Fin 3),
    (let e : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]; ∀ k, dist (p (e k).1).1 (p (e k).2).1=(r (c k)).1) ∧
    ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈([3440,3197,3233,3074,835,3072,3203,157,123,401,824,834,853,3194,3231,0,1,4,5,13,14,31,32,36,37,38,40,41,44,45,46,49,50,53,120,121,122,124,125,132,133,151,156,364,365,368,377,400,761,764,765,766,767,770,773,774,775,776,779,782,792,793,794,796,797,800,822,823,825,826,827,836,849,851,852,854,855,857,858,860,861,862,863,879,880,881,882,883,885,886,887,888,889,890,912,913,939,941,942,943,969,970,1062,1064,1070,1071,1072,1073,1075,1076,1079,1100,1106,1124,1125,1126,1127,1129,1130,1152,1153,1155,1157,1158,1159,1185,1212,1213,1395,1396,3048,3050,3075,3195,3206,3234,3236,3237,3399,3437,3801,3961]:List ℕ)

/-- The Gram equations exclude this first set of color patterns. -/
def H2 : Prop := ∀ B : Finset ℝ², NonTrilinear (B:Set ℝ²) → B.card=5 → distinctDistances B=3 → ∀ (p : Fin 5≃B) (r : Fin 3≃(distanceSet B)) (c : Fin 10→Fin 3),
    (let e : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]; ∀ k, dist (p (e k).1).1 (p (e k).2).1=(r (c k)).1) →
    ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈([0,1,4,5,13,14,31,32,36,37,38,40,41,44,45,46,49,50,53,120,121,122,124,125,132,133,151,156,364,365,368,377,400,761,764,765,766,767,770,773,774,775,776,779,782,792,793,794,796,797,800,822,823,825,826,827,836,849,851,852,854,855,857]:List ℕ) → False

/-- The Gram equations exclude this second set of color patterns, including the two-distance pentagon for a three-distance base. -/
def H3 : Prop := ∀ B : Finset ℝ², NonTrilinear (B:Set ℝ²) → B.card=5 → distinctDistances B=3 → ∀ (p : Fin 5≃B) (r : Fin 3≃(distanceSet B)) (c : Fin 10→Fin 3),
    (let e : Fin 10→Fin 5×Fin 5 := ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]; ∀ k, dist (p (e k).1).1 (p (e k).2).1=(r (c k)).1) →
    ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈([858,860,861,862,863,879,880,881,882,883,885,886,887,888,889,890,912,913,939,941,942,943,969,970,1062,1064,1070,1071,1072,1073,1075,1076,1079,1100,1106,1124,1125,1126,1127,1129,1130,1152,1153,1155,1157,1158,1159,1185,1212,1213,1395,1396,3048,3050,3075,3195,3206,3234,3236,3237,3399,3437,3801,3961]:List ℕ) → False

theorem main : H1 → H2 → H3 → OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1.H1 := by
  intro h0 h1 h2 B hn hB ht
  obtain ⟨p,r,c,hc,hh⟩ := h0 B hn hB ht
  change ((c 0).val*19683 + (c 1).val*6561 + (c 2).val*2187 + (c 3).val*729 + (c 4).val*243 + (c 5).val*81 + (c 6).val*27 + (c 7).val*9 + (c 8).val*3 + (c 9).val*1)∈(([3440,3197,3233,3074,835,3072,3203,157,123,401,824,834,853,3194,3231]:List ℕ) ++ ([0,1,4,5,13,14,31,32,36,37,38,40,41,44,45,46,49,50,53,120,121,122,124,125,132,133,151,156,364,365,368,377,400,761,764,765,766,767,770,773,774,775,776,779,782,792,793,794,796,797,800,822,823,825,826,827,836,849,851,852,854,855,857]:List ℕ) ++ ([858,860,861,862,863,879,880,881,882,883,885,886,887,888,889,890,912,913,939,941,942,943,969,970,1062,1064,1070,1071,1072,1073,1075,1076,1079,1100,1106,1124,1125,1126,1127,1129,1130,1152,1153,1155,1157,1158,1159,1185,1212,1213,1395,1396,3048,3050,3075,3195,3206,3234,3236,3237,3399,3437,3801,3961]:List ℕ):List ℕ) at hh
  rcases List.mem_append.mp hh with h|h
  · rcases List.mem_append.mp h with h|h
    · exact ⟨p,r,c,hc,h⟩
    · exact False.elim (h1 B hn hB ht p r c hc h)
  · exact False.elim (h2 B hn hB ht p r c hc h)

end OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H4_R1_H2_R1_H1_R1
