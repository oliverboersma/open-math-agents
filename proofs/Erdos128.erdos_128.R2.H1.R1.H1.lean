import OMAReductions.R_Erdos128_erdos_128_R2_H1_R1

/-!
# Proof of `Erdos128.erdos_128.R2.H1.R1.H1`

In a maximal triangle-free graph `G` with `14 * δ(G) ≥ 5 * n`, dense half-sets (`50 * e(V') > n^2`),
no homomorphic image of the Grötzsch graph, no homomorphic image of `And(4)`, and containing a
homomorphic image of `V_8 - (2, 6)`, we derive a contradiction by proving that `G` admits a
homomorphism to `V_8` (`And(3)`) and then applying `not_hom_andrasfai` from reduction `R2`:

1. **Substep 1 (`no_026` / `no_426`)**: No vertex hits `{v 0, v 2, v 6}` or `{v 4, v 2, v 6}`
   (via a `K_{2,2}` of Grötzsch obstructions yielding `15 * n ≤ 14 * n`).
2. **Substep 2 (`exists_full_v8`)**: Upgrade `V_8 - (2, 6)` to a full `V_8` homomorphism
   (via maximality + fractional clique bounds `85 * n ≤ 84 * n`).
3. **Substep 3 (`no_hit_v8_edge`, `u_complete`)**: For any full `V_8` image `v`, no vertex hits both
   `U v i` and `U v j` for an edge `(i, j)` of `V_8` (orbit `(0, 1)` via `And(4)` giving `85 * n ≤ 84 * n`;
   orbit `(0, 4)` via Grötzsch giving `100 * n ≤ 98 * n`). By maximality, `U v 0, ..., U v 7` form a
   complete blow-up of `V_8`.
4. **Substep 4 (`no_101`)**: For any full `V_8` image `v`, any vertex adjacent to both `v (c + 1)` and
   `v (c + 7)` is also adjacent to `v (c + 4)` (via a 4-cycle of Grötzsch obstructions giving `85 * n ≤ 84 * n`).
5. **Substep 5 (`B = ∅`)**: Choosing a full `V_8` image `v` maximizing `∑ j, #(U v j)`, every vertex
   `x ∈ B := V \ ⋃ U v j` has `cls x = c` and misses either all of `U v (c + 1)` or all of `U v (c + 7)`.
   A sharp 5-weight vertex count gives `14 * |N_G(x) ∩ U| + 7 * #B < 5 * n` for every `x ∈ B`, which
   combined with Mantel's theorem on `G[B]` forces `B = ∅`.
6. **Conclusion**: `cls` is a homomorphism `G → V_8`, contradicting `not_hom_andrasfai` (`d = 3`).
-/

namespace Erdos128_R2_H1_R1_H1

open Finset SimpleGraph OMA.R_Erdos128_erdos_128_R2

abbrev IsV8MinusE {V : Type} (G : SimpleGraph V) (v : Fin 8 → V) : Prop :=
  ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
    ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j)

abbrev IsFullV8 {V : Type} (G : SimpleGraph V) (v : Fin 8 → V) : Prop :=
  ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) → G.Adj (v i) (v j)

abbrev NoGrotzsch {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ ∃ (o m : Fin 5 → V) (z : V), ∀ i : Fin 5,
    G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧
    G.Adj (m i) (o (i + 4)) ∧ G.Adj z (m i)

abbrev NoAnd4 {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ ∃ φ : Fin 11 → V, ∀ i j : Fin 11,
    (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) → G.Adj (φ i) (φ j)

private lemma mkGrotzsch {V : Type} (G : SimpleGraph V) (hnoG : NoGrotzsch G)
    (o0 o1 o2 o3 o4 m0 m1 m2 m3 m4 z : V)
    (e01 : G.Adj o0 o1) (e12 : G.Adj o1 o2) (e23 : G.Adj o2 o3) (e34 : G.Adj o3 o4) (e40 : G.Adj o4 o0)
    (a01 : G.Adj m0 o1) (a04 : G.Adj m0 o4)
    (a12 : G.Adj m1 o2) (a10 : G.Adj m1 o0)
    (a23 : G.Adj m2 o3) (a21 : G.Adj m2 o1)
    (a34 : G.Adj m3 o4) (a32 : G.Adj m3 o2)
    (a40 : G.Adj m4 o0) (a43 : G.Adj m4 o3)
    (z0 : G.Adj z m0) (z1 : G.Adj z m1) (z2 : G.Adj z m2) (z3 : G.Adj z m3) (z4 : G.Adj z m4) : False := by
  apply hnoG
  let o : Fin 5 → V := ![o0, o1, o2, o3, o4]
  let m : Fin 5 → V := ![m0, m1, m2, m3, m4]
  refine ⟨o, m, z, fun i => ?_⟩
  fin_cases i
  · exact ⟨e01, a01, a04, z0⟩
  · exact ⟨e12, a12, a10, z1⟩
  · exact ⟨e23, a23, a21, z2⟩
  · exact ⟨e34, a34, a32, z3⟩
  · exact ⟨e40, a40, a43, z4⟩

private lemma mkAnd4 {V : Type} (G : SimpleGraph V) (hnoA : NoAnd4 G)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : V)
    (e0_1 : G.Adj p0 p1) (e1_2 : G.Adj p1 p2) (e2_3 : G.Adj p2 p3) (e3_4 : G.Adj p3 p4)
    (e4_5 : G.Adj p4 p5) (e5_6 : G.Adj p5 p6) (e6_7 : G.Adj p6 p7) (e7_8 : G.Adj p7 p8)
    (e8_9 : G.Adj p8 p9) (e9_10 : G.Adj p9 p10) (e10_0 : G.Adj p10 p0)
    (e0_4 : G.Adj p0 p4) (e1_5 : G.Adj p1 p5) (e2_6 : G.Adj p2 p6) (e3_7 : G.Adj p3 p7)
    (e4_8 : G.Adj p4 p8) (e5_9 : G.Adj p5 p9) (e6_10 : G.Adj p6 p10) (e7_0 : G.Adj p7 p0)
    (e8_1 : G.Adj p8 p1) (e9_2 : G.Adj p9 p2) (e10_3 : G.Adj p10 p3) : False := by
  apply hnoA
  let φ : Fin 11 → V := ![p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
  refine ⟨φ, fun i j hij => ?_⟩
  rcases hij with rfl | rfl | rfl | rfl
  · fin_cases i
    · exact e0_1
    · exact e1_2
    · exact e2_3
    · exact e3_4
    · exact e4_5
    · exact e5_6
    · exact e6_7
    · exact e7_8
    · exact e8_9
    · exact e9_10
    · exact e10_0
  · fin_cases i
    · exact e0_4
    · exact e1_5
    · exact e2_6
    · exact e3_7
    · exact e4_8
    · exact e5_9
    · exact e6_10
    · exact e7_0
    · exact e8_1
    · exact e9_2
    · exact e10_3
  · fin_cases i
    · exact e7_0.symm
    · exact e8_1.symm
    · exact e9_2.symm
    · exact e10_3.symm
    · exact e0_4.symm
    · exact e1_5.symm
    · exact e2_6.symm
    · exact e3_7.symm
    · exact e4_8.symm
    · exact e5_9.symm
    · exact e6_10.symm
  · fin_cases i
    · exact e10_0.symm
    · exact e0_1.symm
    · exact e1_2.symm
    · exact e2_3.symm
    · exact e3_4.symm
    · exact e4_5.symm
    · exact e5_6.symm
    · exact e6_7.symm
    · exact e7_8.symm
    · exact e8_9.symm
    · exact e9_10.symm

private lemma weighted_deg_contra {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    {k : ℕ} (pts : Fin k → V) (wts : Fin k → ℕ) (cap : ℕ)
    (hgt : 14 * cap < 5 * ∑ i : Fin k, wts i)
    (hcap : ∀ w : V, (∑ i : Fin k, if G.Adj w (pts i) then wts i else 0) ≤ cap)
    (hne : Nonempty V) : False := by
  set n := Fintype.card V
  have hn : 0 < n := Fintype.card_pos_iff.mpr hne
  have hsum_le : ∑ w : V, (∑ i : Fin k, if G.Adj w (pts i) then wts i else 0) ≤ cap * n := by
    calc _ ≤ ∑ _w : V, cap := Finset.sum_le_sum (fun w _ => hcap w)
      _ = cap * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hsum_eq : ∑ w : V, (∑ i : Fin k, if G.Adj w (pts i) then wts i else 0) =
      ∑ i : Fin k, wts i * #(univ.filter (G.Adj (pts i))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 2; ext w; simp [G.adj_comm]
  have hsum_ge : 5 * (∑ i : Fin k, wts i) * n ≤
      14 * ∑ i : Fin k, wts i * #(univ.filter (G.Adj (pts i))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum; intro i _
    have hdi := h14 (pts i)
    have hmul := Nat.mul_le_mul_left (wts i) hdi
    have h1 : 5 * wts i * n = wts i * (5 * n) := by ring
    have h2 : 14 * (wts i * #(univ.filter (G.Adj (pts i)))) = wts i * (14 * #(univ.filter (G.Adj (pts i)))) := by ring
    omega
  have hcap_ge : 5 * (∑ i : Fin k, wts i) * n ≤ 14 * cap * n := by
    have : 14 * (cap * n) = 14 * cap * n := by ring
    omega
  have : 5 * (∑ i : Fin k, wts i) ≤ 14 * cap := Nat.le_of_mul_le_mul_right hcap_ge hn
  omega

private lemma decide_not_both {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) {p q w : V} (hpq : G.Adj p q) :
    (decide (G.Adj w p) && decide (G.Adj w q)) = false := by
  by_cases h1 : G.Adj w p <;> by_cases h2 : G.Adj w q
  · exact (not_adj_of_cliqueFree_three hTF h1 hpq h2).elim
  all_goals simp [h1, h2]

private lemma decide_not_triple {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q r w : V} (h : ¬ (G.Adj w p ∧ G.Adj w q ∧ G.Adj w r)) :
    (decide (G.Adj w p) && decide (G.Adj w q) && decide (G.Adj w r)) = false := by
  by_cases h1 : G.Adj w p <;> by_cases h2 : G.Adj w q <;> by_cases h3 : G.Adj w r
  · exact (h ⟨h1, h2, h3⟩).elim
  all_goals simp [h1, h2, h3]

private lemma decide_not_quad {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q r s w : V} (h : ¬ (G.Adj w p ∧ G.Adj w q ∧ G.Adj w r ∧ G.Adj w s)) :
    (decide (G.Adj w p) && decide (G.Adj w q) && decide (G.Adj w r) && decide (G.Adj w s)) = false := by
  by_cases h1 : G.Adj w p <;> by_cases h2 : G.Adj w q <;> by_cases h3 : G.Adj w r <;> by_cases h4 : G.Adj w s
  · exact (h ⟨h1, h2, h3, h4⟩).elim
  all_goals simp [h1, h2, h3, h4]

private lemma adj_term_eq {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    {w u v : V} {a b : ℕ} (hu : u = v) (ha : a = b) :
    (if G.Adj w u then a else 0) = b * (decide (G.Adj w v)).toNat := by
  subst hu; subst ha; by_cases h1 : G.Adj w u <;> simp [h1]

private lemma sum_fin9 (f : Fin 9 → ℕ) :
    ∑ i : Fin 9, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]; rfl

private lemma sum_fin10 (f : Fin 10 → ℕ) :
    ∑ i : Fin 10, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]; rfl

private lemma sum_fin11 (f : Fin 11 → ℕ) :
    ∑ i : Fin 11, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]; rfl

/- Finite Boolean weight-cap lemmas (each ≤ 2^11 cases, checked by kernel `decide`). -/

private theorem bool_hno026_A : ∀ b1 b2 b3 b5 b6 b7 : Bool,
    (!(b1 && b2) && !(b2 && b3) && !(b5 && b6) && !(b6 && b7) && !(b1 && b5) && !(b3 && b7) &&
     !(b1 && b3 && b6) && !(b2 && b5 && b7)) = true →
    b1.toNat + b2.toNat + b3.toNat + b5.toNat + b6.toNat + b7.toNat ≤ 2 := by decide

private theorem bool_hno026_B : ∀ b2 b3 b4 b5 b6 b8 : Bool,
    (!(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) && !(b2 && b8) && !(b6 && b8) &&
     !(b2 && b4 && b6) && !(b3 && b5 && b8)) = true →
    b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat + b8.toNat ≤ 2 := by decide

private theorem bool_upgrade_1a : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b3 && b7) &&
     !(b2 && b8) && !(b6 && b8) &&
     !(b1 && b9) && !(b4 && b9) && !(b7 && b9) && !(b8 && b9) &&
     !(b0 && b10) && !(b3 && b10) && !(b5 && b10) && !(b8 && b10) &&
     !(b0 && b2 && b6) && !(b4 && b2 && b6)) = true →
    1 * b0.toNat + 2 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 1 * b4.toNat + 2 * b5.toNat +
      2 * b6.toNat + 2 * b7.toNat + 1 * b8.toNat + 1 * b9.toNat + 1 * b10.toNat ≤ 6 := by decide

private theorem bool_upgrade_1b : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b3 && b7) &&
     !(b2 && b8) && !(b6 && b8) &&
     !(b0 && b2 && b6) && !(b4 && b2 && b6) && !(b1 && b4 && b7 && b8)) = true →
    2 * b0.toNat + 2 * b1.toNat + 3 * b2.toNat + 1 * b3.toNat + 1 * b4.toNat + 1 * b5.toNat +
      3 * b6.toNat + 2 * b7.toNat + 2 * b8.toNat ≤ 6 := by decide

private theorem bool_edge01_A : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b9) && !(b8 && b10) &&
     !(b9 && b1) && !(b9 && b4) && !(b9 && b7) &&
     !(b10 && b2) && !(b10 && b5) && !(b10 && b0) &&
     !(b3 && b6 && b9 && b10) && !(b2 && b4 && b7 && b8)) = true →
    1 * b0.toNat + 1 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 2 * b4.toNat + 1 * b5.toNat +
      1 * b6.toNat + 1 * b7.toNat + 2 * b8.toNat + 2 * b9.toNat + 2 * b10.toNat ≤ 6 := by decide

private theorem bool_edge01_B : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b9) && !(b8 && b10) &&
     !(b9 && b1) && !(b9 && b4) && !(b9 && b7) &&
     !(b10 && b2) && !(b10 && b5) && !(b10 && b0) &&
     !(b3 && b6 && b9 && b10) && !(b2 && b5 && b7 && b8)) = true →
    1 * b0.toNat + 1 * b1.toNat + 1 * b2.toNat + 1 * b3.toNat + 1 * b4.toNat + 2 * b5.toNat +
      2 * b6.toNat + 2 * b7.toNat + 2 * b8.toNat + 2 * b9.toNat + 2 * b10.toNat ≤ 6 := by decide

private theorem bool_edge04_A : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b9) && !(b8 && b10) &&
     !(b9 && b1) && !(b9 && b4) && !(b9 && b7) &&
     !(b10 && b5) && !(b10 && b0) && !(b10 && b3) &&
     !(b1 && b3 && b6 && b8) && !(b2 && b9 && b10)) = true →
    1 * b0.toNat + 2 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 1 * b4.toNat + 1 * b5.toNat +
      1 * b6.toNat + 1 * b7.toNat + 3 * b8.toNat + 3 * b9.toNat + 3 * b10.toNat ≤ 7 := by decide

private theorem bool_hno101_A : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b1) && !(b8 && b7) && !(b9 && b4) && !(b8 && b9) &&
     !(b2 && b4 && b8) && !(b1 && b3 && b6 && b9)) = true →
    1 * b0.toNat + 2 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 3 * b4.toNat + 1 * b5.toNat +
      1 * b6.toNat + 1 * b7.toNat + 2 * b8.toNat + 2 * b9.toNat ≤ 6 := by decide

/- Step 1: No vertex hits `{v 0, v 2, v 6}` or `{v 4, v 2, v 6}` in `V_8 - (2, 6)`. -/

private lemma no_026 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) :
    ∀ z : V, ¬ (G.Adj z (v 0) ∧ G.Adj z (v 2) ∧ G.Adj z (v 6)) := by
  rintro z ⟨hz0, hz2, hz6⟩
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide) (by decide) (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide) (by decide) (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide) (by decide) (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide) (by decide) (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide) (by decide) (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide) (by decide) (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide) (by decide) (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide) (by decide) (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide) (by decide) (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide) (by decide) (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide) (by decide) (by decide)
  by_cases hA : (∃ a : V, G.Adj a (v 1) ∧ G.Adj a (v 3) ∧ G.Adj a (v 6)) ∨
                (∃ a : V, G.Adj a (v 2) ∧ G.Adj a (v 5) ∧ G.Adj a (v 7))
  · have hno246 : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 4) ∧ G.Adj b (v 6)) := by
      rintro b ⟨hb2, hb4, hb6⟩
      rcases hA with ⟨a, ha1, ha3, ha6⟩ | ⟨a, ha2, ha5, ha7⟩
      · exact mkGrotzsch G hnoG (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) z a b (v 7) (v 6)
          e01 e12 e23 e34 e04.symm e15.symm e45.symm hz2 hz0 ha3 ha1 hb4 hb2 e70 e37.symm
          e56.symm hz6.symm ha6.symm hb6.symm e67
      · exact mkGrotzsch G hnoG (v 0) (v 4) (v 5) (v 6) (v 7) (v 3) (v 1) b a z (v 2)
          e04 e45 e56 e67 e70 e34 e37 e15 e01.symm hb6 hb4 ha7 ha5 hz0 hz6
          e23 e12.symm hb2.symm ha2.symm hz2.symm
    have hno35z : ∀ b : V, ¬ (G.Adj b (v 3) ∧ G.Adj b (v 5) ∧ G.Adj b z) := by
      rintro b ⟨hb3, hb5, hbz⟩
      rcases hA with ⟨a, ha1, ha3, ha6⟩ | ⟨a, ha2, ha5, ha7⟩
      · exact mkGrotzsch G hnoG (v 0) (v 1) (v 5) (v 6) z (v 2) (v 4) a b (v 7) (v 3)
          e01 e15 e56 hz6.symm hz0 e12.symm hz2.symm e45 e04.symm ha6 ha1 hbz hb5 e70 e67.symm
          e23.symm e34 ha3.symm hb3.symm e37
      · exact mkGrotzsch G hnoG (v 0) (v 7) (v 3) (v 2) z (v 6) (v 4) a b (v 1) (v 5)
          e70.symm e37.symm e23.symm hz2.symm hz0 e67 hz6.symm e34.symm e04.symm ha2 ha7 hbz hb3 e01.symm e12
          e56 e45.symm ha5.symm hb5.symm e15.symm
    let pts : Fin 6 → V := ![v 2, v 3, v 4, v 5, v 6, z]
    let wts : Fin 6 → ℕ := ![1, 1, 1, 1, 1, 1]
    refine weighted_deg_contra G h14 pts wts 2 (by decide) (fun w => ?_) ⟨z⟩
    have key := bool_hno026_B (decide (G.Adj w (v 2))) (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4)))
      (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6))) (decide (G.Adj w z))
      (by rw [decide_not_both G hTF e23, decide_not_both G hTF e34, decide_not_both G hTF e45,
              decide_not_both G hTF e56, decide_not_both G hTF hz2.symm, decide_not_both G hTF hz6.symm,
              decide_not_triple G (hno246 w), decide_not_triple G (hno35z w)]; rfl)
    rw [Fin.sum_univ_six,
      adj_term_eq G (show pts 0 = v 2 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 3 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 4 from rfl) (show wts 2 = 1 from rfl),
      adj_term_eq G (show pts 3 = v 5 from rfl) (show wts 3 = 1 from rfl),
      adj_term_eq G (show pts 4 = v 6 from rfl) (show wts 4 = 1 from rfl),
      adj_term_eq G (show pts 5 = z from rfl) (show wts 5 = 1 from rfl)]
    omega
  · push Not at hA
    let pts : Fin 6 → V := ![v 1, v 2, v 3, v 5, v 6, v 7]
    let wts : Fin 6 → ℕ := ![1, 1, 1, 1, 1, 1]
    refine weighted_deg_contra G h14 pts wts 2 (by decide) (fun w => ?_) ⟨z⟩
    have key := bool_hno026_A (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2))) (decide (G.Adj w (v 3)))
      (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6))) (decide (G.Adj w (v 7)))
      (by rw [decide_not_both G hTF e12, decide_not_both G hTF e23, decide_not_both G hTF e56,
              decide_not_both G hTF e67, decide_not_both G hTF e15, decide_not_both G hTF e37,
              decide_not_triple G (fun ⟨h1, h3, h6⟩ => hA.1 w h1 h3 h6),
              decide_not_triple G (fun ⟨h2, h5, h7⟩ => hA.2 w h2 h5 h7)]; rfl)
    rw [Fin.sum_univ_six,
      adj_term_eq G (show pts 0 = v 1 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 2 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 3 from rfl) (show wts 2 = 1 from rfl),
      adj_term_eq G (show pts 3 = v 5 from rfl) (show wts 3 = 1 from rfl),
      adj_term_eq G (show pts 4 = v 6 from rfl) (show wts 4 = 1 from rfl),
      adj_term_eq G (show pts 5 = v 7 from rfl) (show wts 5 = 1 from rfl)]
    omega

private lemma isV8MinusE_refl4 {V : Type} {G : SimpleGraph V} {v : Fin 8 → V} (hv : IsV8MinusE G v) :
    IsV8MinusE G (fun i => v (4 - i)) := by
  intro i j hij h26 h62
  apply hv (4 - i) (4 - j)
  · rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)
  · intro h; apply h26; fin_cases i <;> fin_cases j <;> simp_all
  · intro h; apply h62; fin_cases i <;> fin_cases j <;> simp_all

private lemma no_426 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) :
    ∀ z : V, ¬ (G.Adj z (v 4) ∧ G.Adj z (v 2) ∧ G.Adj z (v 6)) := by
  intro z ⟨hz4, hz2, hz6⟩
  exact no_026 G hTF h14 hnoG (fun i => v (4 - i)) (isV8MinusE_refl4 hv) z ⟨hz4, hz2, hz6⟩

/- Step 2: Upgrade `V_8 - (2, 6)` to a full `V_8` homomorphism. -/

private lemma upgrade_no_147z {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) (z : V)
    (hz2 : G.Adj z (v 2)) (hz6 : G.Adj z (v 6))
    (hno147z : ∀ w : V, ¬ (G.Adj w (v 1) ∧ G.Adj w (v 4) ∧ G.Adj w (v 7) ∧ G.Adj w z)) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide) (by decide) (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide) (by decide) (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide) (by decide) (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide) (by decide) (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide) (by decide) (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide) (by decide) (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide) (by decide) (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide) (by decide) (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide) (by decide) (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide) (by decide) (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide) (by decide) (by decide)
  have h026 := no_026 G hTF h14 hnoG v hv
  have h426 := no_426 G hTF h14 hnoG v hv
  let pts : Fin 9 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, z]
  let wts : Fin 9 → ℕ := ![2, 2, 3, 1, 1, 1, 3, 2, 2]
  refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨z⟩
  have key := bool_upgrade_1b (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
    (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
    (decide (G.Adj w (v 7))) (decide (G.Adj w z))
    (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
            decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
            decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
            decide_not_both G hTF e15, decide_not_both G hTF e37,
            decide_not_both G hTF hz2.symm, decide_not_both G hTF hz6.symm,
            decide_not_triple G (h026 w), decide_not_triple G (h426 w),
            decide_not_quad G (hno147z w)]; rfl)
  rw [sum_fin9,
    adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 2 from rfl),
    adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
    adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 3 from rfl),
    adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 1 from rfl),
    adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
    adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
    adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 3 from rfl),
    adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 2 from rfl),
    adj_term_eq G (show pts 8 = z from rfl) (show wts 8 = 2 from rfl)]
  omega

private lemma exists_full_v8 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) :
    IsFullV8 G v := by
  have h26 : G.Adj (v 2) (v 6) := by
    by_contra hnot
    have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide) (by decide) (by decide)
    have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide) (by decide) (by decide)
    have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide) (by decide) (by decide)
    have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide) (by decide) (by decide)
    have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide) (by decide) (by decide)
    have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide) (by decide) (by decide)
    have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide) (by decide) (by decide)
    have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide) (by decide) (by decide)
    have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide) (by decide) (by decide)
    have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide) (by decide) (by decide)
    have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide) (by decide) (by decide)
    have hne26 : v 2 ≠ v 6 := by
      intro heq
      rw [← heq] at e56
      exact not_adj_of_cliqueFree_three hTF e12.symm e15 e56.symm
    obtain ⟨z, hz2, hz6⟩ := hmax (v 2) (v 6) hne26 hnot
    by_cases hy1 : ∃ y1 : V, G.Adj y1 (v 1) ∧ G.Adj y1 (v 4) ∧ G.Adj y1 (v 7) ∧ G.Adj y1 z
    · by_cases hy2 : ∃ y2 : V, G.Adj y2 (v 0) ∧ G.Adj y2 (v 3) ∧ G.Adj y2 (v 5) ∧ G.Adj y2 z
      · obtain ⟨y1, h11, h14', h17, h1z⟩ := hy1
        obtain ⟨y2, h20, h23, h25, h2z⟩ := hy2
        have h026 := no_026 G hTF h14 hnoG v hv
        have h426 := no_426 G hTF h14 hnoG v hv
        let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, z, y1, y2]
        let wts : Fin 11 → ℕ := ![1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1]
        refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨z⟩
        have key := bool_upgrade_1a (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
          (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
          (decide (G.Adj w (v 7))) (decide (G.Adj w z)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
          (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
                  decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
                  decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
                  decide_not_both G hTF e15, decide_not_both G hTF e37,
                  decide_not_both G hTF hz2, decide_not_both G hTF hz6,
                  decide_not_both G hTF h11.symm, decide_not_both G hTF h14'.symm,
                  decide_not_both G hTF h17.symm, decide_not_both G hTF h1z.symm,
                  decide_not_both G hTF h20.symm, decide_not_both G hTF h23.symm,
                  decide_not_both G hTF h25.symm, decide_not_both G hTF h2z.symm,
                  decide_not_triple G (h026 w), decide_not_triple G (h426 w)]; rfl)
        rw [sum_fin11,
          adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
          adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
          adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
          adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
          adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
          adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 2 from rfl),
          adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 2 from rfl),
          adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 2 from rfl),
          adj_term_eq G (show pts 8 = z from rfl) (show wts 8 = 1 from rfl),
          adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 1 from rfl),
          adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 1 from rfl)]
        omega
      · push Not at hy2
        exact upgrade_no_147z G hTF h14 hnoG (fun i => v (4 - i)) (isV8MinusE_refl4 hv) z
          hz2.symm hz6.symm (fun w ⟨h1, h4, h7, hz⟩ => hy2 w h4 h1 h7 hz)
    · push Not at hy1
      exact upgrade_no_147z G hTF h14 hnoG v hv z hz2.symm hz6.symm
        (fun w ⟨h1, h4, h7, hz⟩ => hy1 w h1 h4 h7 hz)
  intro i j hij
  by_cases h1 : i = 2 ∧ j = 6
  · rw [h1.1, h1.2]; exact h26
  · by_cases h2 : i = 6 ∧ j = 2
    · rw [h2.1, h2.2]; exact h26.symm
    · exact hv i j hij h1 h2

/- Full `V_8` symmetries and `U v j` definition. -/

private def Uset {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : Fin 8 → V) (j : Fin 8) : Finset V :=
  univ.filter (fun w => G.Adj w (v (j + 1)) ∧ G.Adj w (v (j + 4)) ∧ G.Adj w (v (j + 7)))

private lemma isFullV8_rot {V : Type} {G : SimpleGraph V} {v : Fin 8 → V}
    (hv : IsFullV8 G v) (s : Fin 8) : IsFullV8 G (fun k => v (s + k)) := by
  intro i j hij
  apply hv (s + i) (s + j)
  rcases hij with rfl | rfl | rfl <;> (fin_cases s <;> fin_cases i <;> decide)

private lemma isFullV8_neg {V : Type} {G : SimpleGraph V} {v : Fin 8 → V}
    (hv : IsFullV8 G v) : IsFullV8 G (fun k => v (-k)) := by
  intro i j hij
  apply hv (-i) (-j)
  rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)

/- Step 3: No vertex hits both `U v i` and `U v j` for an edge `(i, j)` of `V_8`. -/

private lemma no_hit_edge_01 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoA : NoAnd4 G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x y1 y2 : V) (hy1 : y1 ∈ Uset G v 0) (hy2 : y2 ∈ Uset G v 1)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have ⟨h9_1', h9_4', h9_7'⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨h10_2', h10_5', h10_0'⟩ := (Finset.mem_filter.mp hy2).2
  have h9_1 : G.Adj y1 (v 1) := h9_1'
  have h9_4 : G.Adj y1 (v 4) := h9_4'
  have h9_7 : G.Adj y1 (v 7) := h9_7'
  have h10_2 : G.Adj y2 (v 2) := h10_2'
  have h10_5 : G.Adj y2 (v 5) := h10_5'
  have h10_0 : G.Adj y2 (v 0) := h10_0'
  have hno36910 : ∀ w : V, ¬ (G.Adj w (v 3) ∧ G.Adj w (v 6) ∧ G.Adj w y1 ∧ G.Adj w y2) := by
    rintro w ⟨hw3, hw6, hw9, hw10⟩
    exact mkAnd4 G hnoA (v 0) (v 7) (v 6) (v 5) (v 4) (v 3) (v 2) (v 1) y1 w y2
      e70.symm e67.symm e56.symm e45.symm e34.symm e23.symm e12.symm h9_1.symm hw9.symm hw10 h10_0
      e04 e37.symm e26.symm e15.symm h9_4.symm hw3.symm h10_2.symm e01.symm h9_7 hw6 h10_5
  by_cases hA : ∃ a : V, G.Adj a (v 2) ∧ G.Adj a (v 4) ∧ G.Adj a (v 7) ∧ G.Adj a x
  · obtain ⟨a, ha2, ha4, ha7, hax⟩ := hA
    have hnoB : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 5) ∧ G.Adj b (v 7) ∧ G.Adj b x) := by
      rintro b ⟨hb2, hb5, hb7, hbx⟩
      exact mkAnd4 G hnoA (v 0) (v 7) b (v 5) (v 4) a (v 2) (v 1) y1 x y2
        e70.symm hb7.symm hb5 e45.symm ha4.symm ha2 e12.symm h9_1.symm hxy1.symm hxy2 h10_0
        e04 ha7.symm hb2 e15.symm h9_4.symm hax h10_2.symm e01.symm h9_7 hbx.symm h10_5
    let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, y1, y2]
    let wts : Fin 11 → ℕ := ![1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
    refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨x⟩
    have key := bool_edge01_B (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
      (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
      (decide (G.Adj w (v 7))) (decide (G.Adj w x)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
      (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
              decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
              decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
              decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
              decide_not_both G hTF hxy1, decide_not_both G hTF hxy2,
              decide_not_both G hTF h9_1, decide_not_both G hTF h9_4, decide_not_both G hTF h9_7,
              decide_not_both G hTF h10_2, decide_not_both G hTF h10_5, decide_not_both G hTF h10_0,
              decide_not_quad G (hno36910 w), decide_not_quad G (hnoB w)]; rfl)
    rw [sum_fin11,
      adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 1 from rfl),
      adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 1 from rfl),
      adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
      adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 2 from rfl),
      adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 2 from rfl),
      adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 2 from rfl),
      adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 2 from rfl),
      adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 2 from rfl),
      adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 2 from rfl)]
    omega
  · push Not at hA
    let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, y1, y2]
    let wts : Fin 11 → ℕ := ![1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2]
    refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨x⟩
    have key := bool_edge01_A (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
      (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
      (decide (G.Adj w (v 7))) (decide (G.Adj w x)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
      (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
              decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
              decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
              decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
              decide_not_both G hTF hxy1, decide_not_both G hTF hxy2,
              decide_not_both G hTF h9_1, decide_not_both G hTF h9_4, decide_not_both G hTF h9_7,
              decide_not_both G hTF h10_2, decide_not_both G hTF h10_5, decide_not_both G hTF h10_0,
              decide_not_quad G (hno36910 w),
              decide_not_quad G (fun ⟨h2, h4, h7, hx⟩ => hA w h2 h4 h7 hx)]; rfl)
    rw [sum_fin11,
      adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
      adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
      adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 2 from rfl),
      adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
      adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 1 from rfl),
      adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 1 from rfl),
      adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 2 from rfl),
      adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 2 from rfl),
      adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 2 from rfl)]
    omega

private lemma no_hit_edge_04_caseA {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x y1 y2 : V) (hy1 : y1 ∈ Uset G v 0) (hy2 : y2 ∈ Uset G v 4)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2)
    (hno1 : ∀ w : V, ¬ (G.Adj w (v 1) ∧ G.Adj w (v 3) ∧ G.Adj w (v 6) ∧ G.Adj w x))
    (hno2 : ∀ w : V, ¬ (G.Adj w (v 2) ∧ G.Adj w y1 ∧ G.Adj w y2)) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have ⟨h9_1', h9_4', h9_7'⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨h10_5', h10_0', h10_3'⟩ := (Finset.mem_filter.mp hy2).2
  have h9_1 : G.Adj y1 (v 1) := h9_1'
  have h9_4 : G.Adj y1 (v 4) := h9_4'
  have h9_7 : G.Adj y1 (v 7) := h9_7'
  have h10_5 : G.Adj y2 (v 5) := h10_5'
  have h10_0 : G.Adj y2 (v 0) := h10_0'
  have h10_3 : G.Adj y2 (v 3) := h10_3'
  let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, y1, y2]
  let wts : Fin 11 → ℕ := ![1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3]
  refine weighted_deg_contra G h14 pts wts 7 (by decide) (fun w => ?_) ⟨x⟩
  have key := bool_edge04_A (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
    (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
    (decide (G.Adj w (v 7))) (decide (G.Adj w x)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
    (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
            decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
            decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
            decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
            decide_not_both G hTF hxy1, decide_not_both G hTF hxy2,
            decide_not_both G hTF h9_1, decide_not_both G hTF h9_4, decide_not_both G hTF h9_7,
            decide_not_both G hTF h10_5, decide_not_both G hTF h10_0, decide_not_both G hTF h10_3,
            decide_not_quad G (hno1 w), decide_not_triple G (hno2 w)]; rfl)
  rw [sum_fin11,
    adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
    adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
    adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
    adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
    adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
    adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
    adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 1 from rfl),
    adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 1 from rfl),
    adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 3 from rfl),
    adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 3 from rfl),
    adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 3 from rfl)]
  omega

private lemma no_hit_edge_04 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x y1 y2 : V) (hy1 : y1 ∈ Uset G v 0) (hy2 : y2 ∈ Uset G v 4)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have ⟨h9_1', h9_4', h9_7'⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨h10_5', h10_0', h10_3'⟩ := (Finset.mem_filter.mp hy2).2
  have h9_1 : G.Adj y1 (v 1) := h9_1'
  have h9_4 : G.Adj y1 (v 4) := h9_4'
  have h9_7 : G.Adj y1 (v 7) := h9_7'
  have h10_5 : G.Adj y2 (v 5) := h10_5'
  have h10_0 : G.Adj y2 (v 0) := h10_0'
  have h10_3 : G.Adj y2 (v 3) := h10_3'
  by_cases hA : (∃ a : V, G.Adj a (v 1) ∧ G.Adj a (v 3) ∧ G.Adj a (v 6) ∧ G.Adj a x) ∨
                (∃ a : V, G.Adj a (v 2) ∧ G.Adj a y1 ∧ G.Adj a y2)
  · have hno1 : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 5) ∧ G.Adj b (v 7) ∧ G.Adj b x) := by
      rintro b ⟨hb2, hb5, hb7, hbx⟩
      rcases hA with ⟨a, ha1, ha3, ha6, hax⟩ | ⟨a, ha2, ha9, ha10⟩
      · exact mkGrotzsch G hnoG (v 1) (v 5) y2 x a (v 6) (v 0) b (v 3) y1 (v 7)
          e15 h10_5.symm hxy2.symm hax.symm ha1 e56.symm ha6.symm h10_0.symm e01 hbx hb5
          ha3.symm h10_3.symm h9_1 hxy1.symm e67.symm e70 hb7.symm e37.symm h9_7.symm
      · exact mkGrotzsch G hnoG (v 1) (v 2) b (v 7) y1 a (v 5) (v 3) x (v 0) y2
          e12 hb2.symm hb7 h9_7.symm h9_1 ha2 ha9 hb5.symm e15.symm e37 e23.symm hxy1 hbx.symm
          e01 e70.symm ha10.symm h10_5 h10_3 hxy2.symm h10_0
    have hno2 : ∀ b : V, ¬ (G.Adj b (v 6) ∧ G.Adj b y1 ∧ G.Adj b y2) := by
      rintro b ⟨hb6, hb9, hb10⟩
      rcases hA with ⟨a, ha1, ha3, ha6, hax⟩ | ⟨a, ha2, ha9, ha10⟩
      · exact mkGrotzsch G hnoG (v 1) y1 (v 7) (v 6) a x (v 0) b (v 3) (v 5) y2
          h9_1.symm h9_7 e67.symm ha6.symm ha1 hxy1 hax.symm e70.symm e01 hb6 hb9 ha3.symm e37
          e15.symm e56 hxy2.symm h10_0 hb10.symm h10_3 h10_5
      · exact mkGrotzsch G hnoG (v 1) (v 2) (v 6) (v 7) y1 a (v 5) (v 3) b (v 0) y2
          e12 e26 e67 h9_7.symm h9_1 ha2 ha9 e56 e15.symm e37 e23.symm hb9 hb6 e01 e70.symm
          ha10.symm h10_5 h10_3 hb10.symm h10_0
    have hy1' : y1 ∈ Uset G (fun k => v (-k)) 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h9_7, h9_4, h9_1⟩
    have hy2' : y2 ∈ Uset G (fun k => v (-k)) 4 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h10_3, h10_0, h10_5⟩
    exact no_hit_edge_04_caseA G hTF h14 (fun k => v (-k)) (isFullV8_neg hv) x y1 y2 hy1' hy2' hxy1 hxy2
      (fun w ⟨h7, h5, h2, hx⟩ => hno1 w ⟨h2, h5, h7, hx⟩)
      (fun w ⟨h6, h9, h10⟩ => hno2 w ⟨h6, h9, h10⟩)
  · push Not at hA
    exact no_hit_edge_04_caseA G hTF h14 v hv x y1 y2 hy1 hy2 hxy1 hxy2
      (fun w ⟨h1, h3, h6, hx⟩ => hA.1 w h1 h3 h6 hx)
      (fun w ⟨h2, h9, h10⟩ => hA.2 w h2 h9 h10)

private lemma no_hit_v8_edge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G) (hnoA : NoAnd4 G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x : V) (i j : Fin 8) (hij : j = i + 1 ∨ j = i + 4 ∨ j = i + 7)
    (y1 : V) (hy1 : y1 ∈ Uset G v i) (y2 : V) (hy2 : y2 ∈ Uset G v j)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) : False := by
  have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨b1, b4, b7⟩ := (Finset.mem_filter.mp hy2).2
  rcases hij with rfl | rfl | rfl
  · let v' : Fin 8 → V := fun k => v (i + k)
    have hy1' : y1 ∈ Uset G v' 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (0 + 1) = i + 1 := by fin_cases i <;> decide
      have h4 : i + (0 + 4) = i + 4 := by fin_cases i <;> decide
      have h7 : i + (0 + 7) = i + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨a1, a4, a7⟩
    have hy2' : y2 ∈ Uset G v' 1 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (1 + 1) = i + 1 + 1 := by fin_cases i <;> decide
      have h4 : i + (1 + 4) = i + 1 + 4 := by fin_cases i <;> decide
      have h7 : i + (1 + 7) = i + 1 + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨b1, b4, b7⟩
    exact no_hit_edge_01 G hTF h14 hnoA v' (isFullV8_rot hv i) x y1 y2 hy1' hy2' hxy1 hxy2
  · let v' : Fin 8 → V := fun k => v (i + k)
    have hy1' : y1 ∈ Uset G v' 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (0 + 1) = i + 1 := by fin_cases i <;> decide
      have h4 : i + (0 + 4) = i + 4 := by fin_cases i <;> decide
      have h7 : i + (0 + 7) = i + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨a1, a4, a7⟩
    have hy2' : y2 ∈ Uset G v' 4 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (4 + 1) = i + 4 + 1 := by fin_cases i <;> decide
      have h4 : i + (4 + 4) = i + 4 + 4 := by fin_cases i <;> decide
      have h7 : i + (4 + 7) = i + 4 + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨b1, b4, b7⟩
    exact no_hit_edge_04 G hTF h14 hnoG v' (isFullV8_rot hv i) x y1 y2 hy1' hy2' hxy1 hxy2
  · let v' : Fin 8 → V := fun k => v (i + (-k))
    have hv' : IsFullV8 G v' := isFullV8_neg (isFullV8_rot hv i)
    have hy1' : y1 ∈ Uset G v' 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + -(0 + 1) = i + 7 := by fin_cases i <;> decide
      have h4 : i + -(0 + 4) = i + 4 := by fin_cases i <;> decide
      have h7 : i + -(0 + 7) = i + 1 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨a7, a4, a1⟩
    have hy2' : y2 ∈ Uset G v' 1 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + -(1 + 1) = i + 7 + 7 := by fin_cases i <;> decide
      have h4 : i + -(1 + 4) = i + 7 + 4 := by fin_cases i <;> decide
      have h7 : i + -(1 + 7) = i + 7 + 1 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨b7, b4, b1⟩
    exact no_hit_edge_01 G hTF h14 hnoA v' hv' x y1 y2 hy1' hy2' hxy1 hxy2

private lemma uset_disjoint {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) (v : Fin 8 → V) (hv : IsFullV8 G v)
    {i j : Fin 8} (hij : i ≠ j) : Disjoint (Uset G v i) (Uset G v j) := by
  rw [Finset.disjoint_left]
  intro w hwi hwj
  have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hwi).2
  have ⟨b1, b4, b7⟩ := (Finset.mem_filter.mp hwj).2
  have hna : ∀ p q : Fin 8, (q = p + 1 ∨ q = p + 4 ∨ q = p + 7) → G.Adj w (v p) → G.Adj w (v q) → False :=
    fun p q hpq hp hq => not_adj_of_cliqueFree_three hTF hp (hv p q hpq) hq
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
    | exact hna _ _ (by decide) a1 b1 | exact hna _ _ (by decide) a1 b4 | exact hna _ _ (by decide) a1 b7
    | exact hna _ _ (by decide) a4 b1 | exact hna _ _ (by decide) a4 b4 | exact hna _ _ (by decide) a4 b7
    | exact hna _ _ (by decide) a7 b1

private lemma uset_complete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G) (hnoA : NoAnd4 G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (i j : Fin 8) (hij : j = i + 1 ∨ j = i + 4 ∨ j = i + 7)
    (y1 : V) (hy1 : y1 ∈ Uset G v i) (y2 : V) (hy2 : y2 ∈ Uset G v j) :
    G.Adj y1 y2 := by
  by_contra hnot
  have hne_ij : i ≠ j := by rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)
  have hne : y1 ≠ y2 := fun heq => by
    rw [heq] at hy1
    exact Finset.disjoint_left.mp (uset_disjoint G hTF v hv hne_ij) hy1 hy2
  obtain ⟨x, hx1, hx2⟩ := hmax y1 y2 hne hnot
  exact no_hit_v8_edge G hTF h14 hnoG hnoA v hv x i j hij y1 hy1 y2 hy2 hx1.symm hx2.symm

/- Step 4: No vertex hits `{v (c + 1), v (c + 7)}` while missing `v (c + 4)`. -/

private lemma no_101_caseA {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x w : V) (hx1 : G.Adj x (v 1)) (hx7 : G.Adj x (v 7)) (hw4 : G.Adj w (v 4)) (hxw : G.Adj x w)
    (hnoA : ∀ u : V, ¬ (G.Adj u (v 2) ∧ G.Adj u (v 4) ∧ G.Adj u x))
    (hnoC : ∀ u : V, ¬ (G.Adj u (v 1) ∧ G.Adj u (v 3) ∧ G.Adj u (v 6) ∧ G.Adj u w)) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  let pts : Fin 10 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, w]
  let wts : Fin 10 → ℕ := ![1, 2, 2, 2, 3, 1, 1, 1, 2, 2]
  refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun u => ?_) ⟨x⟩
  have key := bool_hno101_A (decide (G.Adj u (v 0))) (decide (G.Adj u (v 1))) (decide (G.Adj u (v 2)))
    (decide (G.Adj u (v 3))) (decide (G.Adj u (v 4))) (decide (G.Adj u (v 5))) (decide (G.Adj u (v 6)))
    (decide (G.Adj u (v 7))) (decide (G.Adj u x)) (decide (G.Adj u w))
    (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
            decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
            decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
            decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
            decide_not_both G hTF hx1, decide_not_both G hTF hx7, decide_not_both G hTF hw4,
            decide_not_both G hTF hxw,
            decide_not_triple G (hnoA u), decide_not_quad G (hnoC u)]; rfl)
  rw [sum_fin10,
    adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
    adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
    adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
    adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
    adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 3 from rfl),
    adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
    adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 1 from rfl),
    adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 1 from rfl),
    adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 2 from rfl),
    adj_term_eq G (show pts 9 = w from rfl) (show wts 9 = 2 from rfl)]
  omega

private lemma no_101_zero {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x : V) (hx1 : G.Adj x (v 1)) (hx7 : G.Adj x (v 7)) :
    G.Adj x (v 4) := by
  by_contra hx4
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have hne : x ≠ v 4 := by
    intro heq; rw [heq] at hx1
    exact not_adj_of_cliqueFree_three hTF e04.symm e01 hx1
  obtain ⟨w, hxw, hw4⟩ := hmax x (v 4) hne hx4
  have hw4' : G.Adj w (v 4) := hw4.symm
  by_cases hAC : (∃ a : V, G.Adj a (v 2) ∧ G.Adj a (v 4) ∧ G.Adj a x) ∨
                 (∃ a : V, G.Adj a (v 1) ∧ G.Adj a (v 3) ∧ G.Adj a (v 6) ∧ G.Adj a w)
  · have hnoB : ∀ b : V, ¬ (G.Adj b (v 4) ∧ G.Adj b (v 6) ∧ G.Adj b x) := by
      rintro b ⟨hb4, hb6, hbx⟩
      rcases hAC with ⟨a, ha2, ha4, hax⟩ | ⟨a, ha1, ha3, ha6, haw⟩
      · exact mkGrotzsch G hnoG (v 1) (v 2) (v 6) (v 7) x a (v 5) (v 3) b (v 0) (v 4)
          e12 e26 e67 hx7.symm hx1 ha2 hax e56 e15.symm e37 e23.symm hbx hb6 e01 e70.symm
          ha4.symm e45 e34.symm hb4.symm e04.symm
      · exact mkGrotzsch G hnoG (v 1) x (v 7) (v 6) a w (v 0) b (v 3) (v 5) (v 4)
          hx1.symm hx7 e67.symm ha6.symm ha1 hxw.symm haw.symm e70.symm e01 hb6 hbx ha3.symm e37
          e15.symm e56 hw4'.symm e04.symm hb4.symm e34.symm e45
    have hnoD : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 5) ∧ G.Adj b (v 7) ∧ G.Adj b w) := by
      rintro b ⟨hb2, hb5, hb7, hbw⟩
      rcases hAC with ⟨a, ha2, ha4, hax⟩ | ⟨a, ha1, ha3, ha6, haw⟩
      · exact mkGrotzsch G hnoG (v 1) (v 2) b (v 7) x a (v 5) (v 3) w (v 0) (v 4)
          e12 hb2.symm hb7 hx7.symm hx1 ha2 hax hb5.symm e15.symm e37 e23.symm hxw.symm hbw.symm
          e01 e70.symm ha4.symm e45 e34.symm hw4'.symm e04.symm
      · exact mkGrotzsch G hnoG (v 1) (v 5) (v 4) w a (v 6) (v 0) b (v 3) x (v 7)
          e15 e45.symm hw4'.symm haw.symm ha1 e56.symm ha6.symm e04 e01 hbw hb5
          ha3.symm e34 hx1 hxw e67.symm e70 hb7.symm e37.symm hx7.symm
    exact no_101_caseA G hTF h14 (fun k => v (-k)) (isFullV8_neg hv) x w hx7 hx1 hw4' hxw
      (fun u ⟨h6, h4, hx⟩ => hnoB u ⟨h4, h6, hx⟩)
      (fun u ⟨h7, h5, h2, hw⟩ => hnoD u ⟨h2, h5, h7, hw⟩)
  · push Not at hAC
    exact no_101_caseA G hTF h14 v hv x w hx1 hx7 hw4' hxw
      (fun u ⟨h2, h4, hx⟩ => hAC.1 u h2 h4 hx)
      (fun u ⟨h1, h3, h6, hw⟩ => hAC.2 u h1 h3 h6 hw)

private lemma no_101 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (c : Fin 8) (x : V) (hx1 : G.Adj x (v (c + 1))) (hx7 : G.Adj x (v (c + 7))) :
    G.Adj x (v (c + 4)) :=
  no_101_zero G hTF hmax h14 hnoG (fun k => v (c + k)) (isFullV8_rot hv c) x hx1 hx7

/- Elementary Mantel bound on any subset `B` of a triangle-free graph. -/

private lemma mantel_on_finset {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hTF : G.CliqueFree 3) (B : Finset V) :
    2 * ∑ x ∈ B, #(B.filter (G.Adj x)) ≤ (#B) ^ 2 := by
  by_cases hne : B.Nonempty
  · obtain ⟨u₀, hu₀B, hu₀max⟩ := Finset.exists_max_image B (fun u => #(B.filter (G.Adj u))) hne
    let I : Finset V := B.filter (G.Adj u₀)
    have hIB : I ⊆ B := Finset.filter_subset _ _
    have hI_le : #I ≤ #B := Finset.card_le_card hIB
    have hsum_split : ∑ x ∈ B, #(B.filter (G.Adj x)) =
        ∑ x ∈ I, #(B.filter (G.Adj x)) + ∑ x ∈ B \ I, #(B.filter (G.Adj x)) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hIB]
    have h1 : ∑ x ∈ I, #(B.filter (G.Adj x)) ≤ #I * (#B - #I) := by
      calc _ ≤ ∑ _x ∈ I, (#B - #I) := by
            apply Finset.sum_le_sum; intro x hx
            have hsub : B.filter (G.Adj x) ⊆ B \ I := by
              intro y hy
              rw [Finset.mem_sdiff]
              refine ⟨(Finset.mem_filter.mp hy).1, fun hyI => ?_⟩
              exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hx).2
                (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hyI).2
            have hle := Finset.card_le_card hsub
            rwa [Finset.card_sdiff_of_subset hIB] at hle
        _ = #I * (#B - #I) := by rw [Finset.sum_const, smul_eq_mul]
    have h2 : ∑ x ∈ B \ I, #(B.filter (G.Adj x)) ≤ #I * (#B - #I) := by
      calc _ ≤ ∑ _x ∈ B \ I, #I := by
            apply Finset.sum_le_sum; intro x hx
            exact hu₀max x (Finset.mem_sdiff.mp hx).1
        _ = #I * (#B - #I) := by rw [Finset.sum_const, Finset.card_sdiff_of_subset hIB, smul_eq_mul, mul_comm]
    have hsq : 4 * (#I * (#B - #I)) ≤ (#B) ^ 2 := by
      zify [hI_le]
      nlinarith [sq_nonneg ((#B : ℤ) - 2 * (#I : ℤ))]
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

/- Step 5: Pick a `∑ #(U v j)`-maximal full `V_8`, prove `B = ∅`, and apply `not_hom_andrasfai`. -/

private lemma main_proof : OMA.R_Erdos128_erdos_128_R2_H1_R1.H1 := by
  intro V _ G hTF hmax h50 h14 _hnot3 hnoG ⟨v₀, hv₀⟩ hnoA
  classical
  have hdeg : ∀ x : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj x)) := by
    intro x
    have h1 := h14 x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have h2 : (G.neighborSet x).toFinset = univ.filter (G.Adj x) := by ext y; simp
    rwa [h2] at h1
  have hv₀_full : IsFullV8 G v₀ := exists_full_v8 G hTF hmax hdeg hnoG v₀ hv₀
  let fullV8s : Finset (Fin 8 → V) := univ.filter (fun v => IsFullV8 G v)
  have hv₀_mem : v₀ ∈ fullV8s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀_full⟩
  obtain ⟨v, hv_mem, hv_max⟩ :=
    Finset.exists_max_image fullV8s (fun w => ∑ j : Fin 8, #(Uset G w j)) ⟨v₀, hv₀_mem⟩
  have hv : IsFullV8 G v := (Finset.mem_filter.mp hv_mem).2
  set n := Fintype.card V
  have hmem_v : ∀ j : Fin 8, v j ∈ Uset G v j := fun j =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hv j (j + 1) (Or.inl rfl), hv j (j + 4) (Or.inr (Or.inl rfl)), hv j (j + 7) (Or.inr (Or.inr rfl))⟩
  have hU_exact : ∀ j : Fin 8, ∀ w ∈ Uset G v j, ∀ i : Fin 8,
      G.Adj w (v i) ↔ (i = j + 1 ∨ i = j + 4 ∨ i = j + 7) := by
    intro j w hw i
    have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hw).2
    constructor
    · intro hwi
      by_contra hnot
      have hna : ∀ p q : Fin 8, (q = p + 1 ∨ q = p + 4 ∨ q = p + 7) →
          G.Adj w (v p) → G.Adj w (v q) → False :=
        fun p q hpq hp hq => not_adj_of_cliqueFree_three hTF hp (hv p q hpq) hq
      fin_cases j <;> fin_cases i <;> simp at hnot
      all_goals first
        | exact hna _ _ (by decide) hwi a1 | exact hna _ _ (by decide) hwi a4
        | exact hna _ _ (by decide) hwi a7
    · rintro (rfl | rfl | rfl) <;> assumption
  -- Classify every vertex `x` via `v8_indep_subset_nbhd`
  have hex_cls : ∀ x : V, ∃ c : Fin 8, ∀ j : Fin 8, (∃ y ∈ Uset G v j, G.Adj x y) →
      j = c + 1 ∨ j = c + 4 ∨ j = c + 7 := by
    intro x
    let J : Finset (Fin 8) := univ.filter (fun j => ∃ y ∈ Uset G v j, G.Adj x y)
    have hJ_indep : ∀ i ∈ J, ∀ j ∈ J, ¬ (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) := by
      intro i hi j hj hij
      obtain ⟨y1, hy1, hxy1⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨y2, hy2, hxy2⟩ := (Finset.mem_filter.mp hj).2
      exact no_hit_v8_edge G hTF hdeg hnoG hnoA v hv x i j hij y1 hy1 y2 hy2 hxy1 hxy2
    obtain ⟨c, hc⟩ := v8_indep_subset_nbhd J hJ_indep
    exact ⟨c, fun j hj => hc j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
  let cls : V → Fin 8 := fun x => (hex_cls x).choose
  have hcls_spec : ∀ x : V, ∀ j : Fin 8, ∀ y ∈ Uset G v j, G.Adj x y →
      j = cls x + 1 ∨ j = cls x + 4 ∨ j = cls x + 7 :=
    fun x j y hy hxy => (hex_cls x).choose_spec j ⟨y, hy, hxy⟩
  let B : Finset V := univ.filter (fun x => ∀ j : Fin 8, x ∉ Uset G v j)
  -- Every `x ∈ B` misses either all of `U v (cls x + 1)` or all of `U v (cls x + 7)`
  have hB_miss : ∀ x ∈ B,
      (∀ y ∈ Uset G v (cls x + 1), ¬ G.Adj x y) ∨
      (∀ y ∈ Uset G v (cls x + 7), ¬ G.Adj x y) := by
    intro x hxB
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨y1, hy1, hxy1⟩, ⟨y7, hy7, hxy7⟩⟩ := hboth
    have h17 : cls x + 1 ≠ cls x + 7 := by generalize cls x = c; fin_cases c <;> decide
    set c := cls x
    let v' : Fin 8 → V := fun k => if k = c + 1 then y1 else if k = c + 7 then y7 else v k
    have hv'_memU : ∀ k : Fin 8, v' k ∈ Uset G v k := by
      intro k; dsimp only [v']
      split_ifs with h1 h7
      · subst h1; exact hy1
      · subst h7; exact hy7
      · exact hmem_v k
    have hv'_full : IsFullV8 G v' := fun i j hij =>
      uset_complete G hTF hmax hdeg hnoG hnoA v hv i j hij (v' i) (hv'_memU i) (v' j) (hv'_memU j)
    have hU_sub : ∀ k : Fin 8, Uset G v k ⊆ Uset G v' k := by
      intro k u hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · exact uset_complete G hTF hmax hdeg hnoG hnoA v hv k (k + 1) (Or.inl rfl) u hu (v' (k + 1)) (hv'_memU (k + 1))
      · exact uset_complete G hTF hmax hdeg hnoG hnoA v hv k (k + 4) (Or.inr (Or.inl rfl)) u hu (v' (k + 4)) (hv'_memU (k + 4))
      · exact uset_complete G hTF hmax hdeg hnoG hnoA v hv k (k + 7) (Or.inr (Or.inr rfl)) u hu (v' (k + 7)) (hv'_memU (k + 7))
    have hx_v'1 : G.Adj x (v' (c + 1)) := by dsimp only [v']; rw [if_pos rfl]; exact hxy1
    have hx_v'7 : G.Adj x (v' (c + 7)) := by
      dsimp only [v']; rw [if_neg h17.symm, if_pos rfl]; exact hxy7
    have hx_v'4 : G.Adj x (v' (c + 4)) := no_101 G hTF hmax hdeg hnoG v' hv'_full c x hx_v'1 hx_v'7
    have hx_in' : x ∈ Uset G v' c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx_v'1, hx_v'4, hx_v'7⟩
    have hx_notin : x ∉ Uset G v c := (Finset.mem_filter.mp hxB).2 c
    have hlt_c : #(Uset G v c) < #(Uset G v' c) :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hU_sub c, fun heq => hx_notin (heq ▸ hx_in')⟩)
    have hsum_lt : ∑ k : Fin 8, #(Uset G v k) < ∑ k : Fin 8, #(Uset G v' k) :=
      Finset.sum_lt_sum (fun k _ => Finset.card_le_card (hU_sub k)) ⟨c, Finset.mem_univ c, hlt_c⟩
    have hv'_le := hv_max v' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'_full⟩)
    omega
  -- Every `w ∈ B` hits at most 2 vertices of `{v 0, ..., v 7}`
  have hB_cap2 : ∀ w ∈ B, #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) ≤ 2 := by
    intro w hwB
    have hsub : univ.filter (fun i : Fin 8 => G.Adj w (v i)) ⊆ ({cls w + 1, cls w + 4, cls w + 7} : Finset (Fin 8)) := by
      intro i hi
      have hwi := (Finset.mem_filter.mp hi).2
      have := hcls_spec w i (v i) (hmem_v i) hwi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have hne_all : univ.filter (fun i : Fin 8 => G.Adj w (v i)) ≠ ({cls w + 1, cls w + 4, cls w + 7} : Finset (Fin 8)) := by
      intro heq
      have h1 : cls w + 1 ∈ univ.filter (fun i : Fin 8 => G.Adj w (v i)) := by rw [heq]; simp
      have h4 : cls w + 4 ∈ univ.filter (fun i : Fin 8 => G.Adj w (v i)) := by rw [heq]; simp
      have h7 : cls w + 7 ∈ univ.filter (fun i : Fin 8 => G.Adj w (v i)) := by rw [heq]; simp
      exact (Finset.mem_filter.mp hwB).2 (cls w) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h4).2, (Finset.mem_filter.mp h7).2⟩)
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne_all⟩)
    have hcard3 : #({cls w + 1, cls w + 4, cls w + 7} : Finset (Fin 8)) ≤ 3 :=
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    omega
  -- Partition `B` into `E0 c` (misses `U (c + 1)`) and `E2 c` (misses `U (c + 7)`)
  let E0 : Fin 8 → Finset V := fun c =>
    B.filter (fun x => cls x = c ∧ ∀ y ∈ Uset G v (c + 1), ¬ G.Adj x y)
  let E2 : Fin 8 → Finset V := fun c =>
    B.filter (fun x => cls x = c ∧ ∀ y ∈ Uset G v (c + 7), ¬ G.Adj x y)
  -- Sharp 5-weight vertex count for `E2 c`
  have hbound_E2 : ∀ c : Fin 8,
      14 * (#(Uset G v (c + 1)) + #(Uset G v (c + 4))) + 7 * #B + 14 * #(E2 c) ≤ 5 * n := by
    intro c
    have hpt : ∀ w : V,
        (if w ∈ Uset G v (c + 1) then 2 else 0) + (if w ∈ Uset G v (c + 4) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 6)) then 2 else 0) + (if G.Adj w (v (c + 7)) then 2 else 0) +
        (if w ∈ E2 c then 2 else 0) ≤ 5 := by
      intro w
      by_cases hwB : w ∈ B
      · have hnot1 : w ∉ Uset G v (c + 1) := (Finset.mem_filter.mp hwB).2 (c + 1)
        have hnot4 : w ∉ Uset G v (c + 4) := (Finset.mem_filter.mp hwB).2 (c + 4)
        have hcap := hB_cap2 w hwB
        have h67 : G.Adj (v (c + 6)) (v (c + 7)) := hv (c + 6) (c + 7) (Or.inl (by fin_cases c <;> decide))
        by_cases hwE : w ∈ E2 c
        · have ⟨hclsw, hmiss7⟩ := (Finset.mem_filter.mp hwE).2
          have hno7 : ¬ G.Adj w (v (c + 7)) := hmiss7 (v (c + 7)) (hmem_v (c + 7))
          have hno6 : ¬ G.Adj w (v (c + 6)) := by
            intro h6
            have hmem := hcls_spec w (c + 6) (v (c + 6)) (hmem_v (c + 6)) h6
            rw [hclsw] at hmem
            fin_cases c <;> simp at hmem
          simp [hnot1, hnot4, hwB, hwE, hno6, hno7]; omega
        · by_cases h6 : G.Adj w (v (c + 6)) <;> by_cases h7 : G.Adj w (v (c + 7))
          · exact (not_adj_of_cliqueFree_three hTF h6 h67 h7).elim
          all_goals (simp [hnot1, hnot4, hwB, hwE, h6, h7]; omega)
      · have hexU : ∃ k : Fin 8, w ∈ Uset G v k := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
        obtain ⟨k, hwk⟩ := hexU
        have hnotE : w ∉ E2 c := fun h => hwB (Finset.mem_filter.mp h).1
        have hmem_iff : ∀ j : Fin 8, w ∈ Uset G v j ↔ k = j := by
          intro j; constructor
          · intro hwj; by_contra hne
            exact Finset.disjoint_left.mp (uset_disjoint G hTF v hv hne) hwk hwj
          · rintro rfl; exact hwk
        have hdeg3 : #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) = 3 := by
          have heq : univ.filter (fun i : Fin 8 => G.Adj w (v i)) = {k + 1, k + 4, k + 7} := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            exact hU_exact k w hwk i
          rw [heq]; fin_cases k <;> decide
        have h6iff : G.Adj w (v (c + 6)) ↔ (c + 6 = k + 1 ∨ c + 6 = k + 4 ∨ c + 6 = k + 7) :=
          hU_exact k w hwk (c + 6)
        have h7iff : G.Adj w (v (c + 7)) ↔ (c + 7 = k + 1 ∨ c + 7 = k + 4 ∨ c + 7 = k + 7) :=
          hU_exact k w hwk (c + 7)
        simp only [hwB, hnotE, if_false, add_zero, hdeg3, hmem_iff, h6iff, h7iff]
        fin_cases c <;> fin_cases k <;> decide
    have hsum_le : ∑ w : V, ((if w ∈ Uset G v (c + 1) then 2 else 0) + (if w ∈ Uset G v (c + 4) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 6)) then 2 else 0) + (if G.Adj w (v (c + 7)) then 2 else 0) +
        (if w ∈ E2 c then 2 else 0)) ≤ 5 * n := by
      calc _ ≤ ∑ _w : V, 5 := Finset.sum_le_sum (fun w _ => hpt w)
        _ = 5 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, ((if w ∈ Uset G v (c + 1) then 2 else 0) + (if w ∈ Uset G v (c + 4) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 6)) then 2 else 0) + (if G.Adj w (v (c + 7)) then 2 else 0) +
        (if w ∈ E2 c then 2 else 0)) =
        2 * #(Uset G v (c + 1)) + 2 * #(Uset G v (c + 4)) + #B +
        (∑ i : Fin 8, #(univ.filter (G.Adj (v i)))) +
        2 * #(univ.filter (G.Adj (v (c + 6)))) + 2 * #(univ.filter (G.Adj (v (c + 7)))) +
        2 * #(E2 c) := by
      simp_rw [Finset.sum_add_distrib]
      have hconst : ∀ (S : Finset V) (a : ℕ), ∑ w : V, (if w ∈ S then a else 0) = a * #S := by
        intro S a
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_comm]
      have hadj : ∀ (u : V) (a : ℕ), ∑ w : V, (if G.Adj w u then a else 0) = a * #(univ.filter (G.Adj u)) := by
        intro u a
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
      have hswap : ∑ w : V, #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) =
          ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
        simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      rw [hconst, hconst, hconst, one_mul, hswap, hadj, hadj, hconst]
    have h8deg : 40 * n ≤ 14 * ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
      rw [Finset.mul_sum]
      calc 40 * n = ∑ _i : Fin 8, 5 * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hdeg (v i))
    have hd6 := hdeg (v (c + 6))
    have hd7 := hdeg (v (c + 7))
    omega
  -- Symmetric 5-weight vertex count for `E0 c`
  have hbound_E0 : ∀ c : Fin 8,
      14 * (#(Uset G v (c + 4)) + #(Uset G v (c + 7))) + 7 * #B + 14 * #(E0 c) ≤ 5 * n := by
    intro c
    have hpt : ∀ w : V,
        (if w ∈ Uset G v (c + 4) then 2 else 0) + (if w ∈ Uset G v (c + 7) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 1)) then 2 else 0) + (if G.Adj w (v (c + 2)) then 2 else 0) +
        (if w ∈ E0 c then 2 else 0) ≤ 5 := by
      intro w
      by_cases hwB : w ∈ B
      · have hnot4 : w ∉ Uset G v (c + 4) := (Finset.mem_filter.mp hwB).2 (c + 4)
        have hnot7 : w ∉ Uset G v (c + 7) := (Finset.mem_filter.mp hwB).2 (c + 7)
        have hcap := hB_cap2 w hwB
        have h12 : G.Adj (v (c + 1)) (v (c + 2)) := hv (c + 1) (c + 2) (Or.inl (by fin_cases c <;> decide))
        by_cases hwE : w ∈ E0 c
        · have ⟨hclsw, hmiss1⟩ := (Finset.mem_filter.mp hwE).2
          have hno1 : ¬ G.Adj w (v (c + 1)) := hmiss1 (v (c + 1)) (hmem_v (c + 1))
          have hno2 : ¬ G.Adj w (v (c + 2)) := by
            intro h2
            have hmem := hcls_spec w (c + 2) (v (c + 2)) (hmem_v (c + 2)) h2
            rw [hclsw] at hmem
            fin_cases c <;> simp at hmem
          simp [hnot4, hnot7, hwB, hwE, hno1, hno2]; omega
        · by_cases h1 : G.Adj w (v (c + 1)) <;> by_cases h2 : G.Adj w (v (c + 2))
          · exact (not_adj_of_cliqueFree_three hTF h1 h12 h2).elim
          all_goals (simp [hnot4, hnot7, hwB, hwE, h1, h2]; omega)
      · have hexU : ∃ k : Fin 8, w ∈ Uset G v k := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
        obtain ⟨k, hwk⟩ := hexU
        have hnotE : w ∉ E0 c := fun h => hwB (Finset.mem_filter.mp h).1
        have hmem_iff : ∀ j : Fin 8, w ∈ Uset G v j ↔ k = j := by
          intro j; constructor
          · intro hwj; by_contra hne
            exact Finset.disjoint_left.mp (uset_disjoint G hTF v hv hne) hwk hwj
          · rintro rfl; exact hwk
        have hdeg3 : #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) = 3 := by
          have heq : univ.filter (fun i : Fin 8 => G.Adj w (v i)) = {k + 1, k + 4, k + 7} := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            exact hU_exact k w hwk i
          rw [heq]; fin_cases k <;> decide
        have h1iff : G.Adj w (v (c + 1)) ↔ (c + 1 = k + 1 ∨ c + 1 = k + 4 ∨ c + 1 = k + 7) :=
          hU_exact k w hwk (c + 1)
        have h2iff : G.Adj w (v (c + 2)) ↔ (c + 2 = k + 1 ∨ c + 2 = k + 4 ∨ c + 2 = k + 7) :=
          hU_exact k w hwk (c + 2)
        simp only [hwB, hnotE, if_false, add_zero, hdeg3, hmem_iff, h1iff, h2iff]
        fin_cases c <;> fin_cases k <;> decide
    have hsum_le : ∑ w : V, ((if w ∈ Uset G v (c + 4) then 2 else 0) + (if w ∈ Uset G v (c + 7) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 1)) then 2 else 0) + (if G.Adj w (v (c + 2)) then 2 else 0) +
        (if w ∈ E0 c then 2 else 0)) ≤ 5 * n := by
      calc _ ≤ ∑ _w : V, 5 := Finset.sum_le_sum (fun w _ => hpt w)
        _ = 5 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, ((if w ∈ Uset G v (c + 4) then 2 else 0) + (if w ∈ Uset G v (c + 7) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 1)) then 2 else 0) + (if G.Adj w (v (c + 2)) then 2 else 0) +
        (if w ∈ E0 c then 2 else 0)) =
        2 * #(Uset G v (c + 4)) + 2 * #(Uset G v (c + 7)) + #B +
        (∑ i : Fin 8, #(univ.filter (G.Adj (v i)))) +
        2 * #(univ.filter (G.Adj (v (c + 1)))) + 2 * #(univ.filter (G.Adj (v (c + 2)))) +
        2 * #(E0 c) := by
      simp_rw [Finset.sum_add_distrib]
      have hconst : ∀ (S : Finset V) (a : ℕ), ∑ w : V, (if w ∈ S then a else 0) = a * #S := by
        intro S a
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_comm]
      have hadj : ∀ (u : V) (a : ℕ), ∑ w : V, (if G.Adj w u then a else 0) = a * #(univ.filter (G.Adj u)) := by
        intro u a
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
      have hswap : ∑ w : V, #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) =
          ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
        simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      rw [hconst, hconst, hconst, one_mul, hswap, hadj, hadj, hconst]
    have h8deg : 40 * n ≤ 14 * ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
      rw [Finset.mul_sum]
      calc 40 * n = ∑ _i : Fin 8, 5 * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hdeg (v i))
    have hd1 := hdeg (v (c + 1))
    have hd2 := hdeg (v (c + 2))
    omega
  -- Prove `B = ∅` via Mantel on `G[B]`
  have hB_empty : B = ∅ := by
    by_contra hBne
    have hBpos : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBne
    let Uall : Finset V := univ \ B
    have hUall_bound : ∀ x ∈ B, 14 * #(Uall.filter (G.Adj x)) + 7 * #B < 5 * n := by
      intro x hxB
      set c := cls x
      rcases hB_miss x hxB with hmiss1 | hmiss7
      · have hxE0 : x ∈ E0 c := Finset.mem_filter.mpr ⟨hxB, rfl, hmiss1⟩
        have hpos : 1 ≤ #(E0 c) := Finset.card_pos.mpr ⟨x, hxE0⟩
        have hsub : Uall.filter (G.Adj x) ⊆ Uset G v (c + 4) ∪ Uset G v (c + 7) := by
          intro y hy
          have ⟨hyU, hxy⟩ := Finset.mem_filter.mp hy
          have hy_notB : y ∉ B := (Finset.mem_sdiff.mp hyU).2
          have hexU : ∃ j : Fin 8, y ∈ Uset G v j := by
            by_contra hnone; push Not at hnone
            exact hy_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
          obtain ⟨j, hyj⟩ := hexU
          rcases hcls_spec x j y hyj hxy with rfl | rfl | rfl
          · exact (hmiss1 y hyj hxy).elim
          · exact Finset.mem_union_left _ hyj
          · exact Finset.mem_union_right _ hyj
        have hle : #(Uall.filter (G.Adj x)) ≤ #(Uset G v (c + 4)) + #(Uset G v (c + 7)) :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hb := hbound_E0 c
        omega
      · have hxE2 : x ∈ E2 c := Finset.mem_filter.mpr ⟨hxB, rfl, hmiss7⟩
        have hpos : 1 ≤ #(E2 c) := Finset.card_pos.mpr ⟨x, hxE2⟩
        have hsub : Uall.filter (G.Adj x) ⊆ Uset G v (c + 1) ∪ Uset G v (c + 4) := by
          intro y hy
          have ⟨hyU, hxy⟩ := Finset.mem_filter.mp hy
          have hy_notB : y ∉ B := (Finset.mem_sdiff.mp hyU).2
          have hexU : ∃ j : Fin 8, y ∈ Uset G v j := by
            by_contra hnone; push Not at hnone
            exact hy_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
          obtain ⟨j, hyj⟩ := hexU
          rcases hcls_spec x j y hyj hxy with rfl | rfl | rfl
          · exact Finset.mem_union_left _ hyj
          · exact Finset.mem_union_right _ hyj
          · exact (hmiss7 y hyj hxy).elim
        have hle : #(Uall.filter (G.Adj x)) ≤ #(Uset G v (c + 1)) + #(Uset G v (c + 4)) :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hb := hbound_E2 c
        omega
    have hsum_lt : ∑ x ∈ B, (14 * #(Uall.filter (G.Adj x)) + 7 * #B) < ∑ _x ∈ B, (5 * n) :=
      Finset.sum_lt_sum_of_nonempty hBpos hUall_bound
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul] at hsum_lt
    have hdeg_split : ∀ x ∈ B, #(univ.filter (G.Adj x)) = #(Uall.filter (G.Adj x)) + #(B.filter (G.Adj x)) := by
      intro x _
      have hunion : Uall ∪ B = univ := Finset.sdiff_union_of_subset (Finset.subset_univ B)
      have hdisj : Disjoint Uall B := Finset.sdiff_disjoint
      rw [← hunion, Finset.filter_union,
        Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    have hdeg_sum : #B * (5 * n) ≤ 14 * ∑ x ∈ B, #(Uall.filter (G.Adj x)) + 14 * ∑ x ∈ B, #(B.filter (G.Adj x)) := by
      calc #B * (5 * n) = ∑ _x ∈ B, 5 * n := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ B, 14 * #(univ.filter (G.Adj x)) := Finset.sum_le_sum (fun x _ => hdeg x)
        _ = ∑ x ∈ B, (14 * #(Uall.filter (G.Adj x)) + 14 * #(B.filter (G.Adj x))) := by
            apply Finset.sum_congr rfl; intro x hx; rw [hdeg_split x hx, mul_add]
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hmantel := mantel_on_finset G hTF B
    have hsq : #B * (7 * #B) = 7 * (#B) ^ 2 := by ring
    omega
  -- Every vertex `x` lies in `Uset G v (cls x)`, so `cls` is a homomorphism `G → V_8`!
  have hall_U : ∀ x : V, x ∈ Uset G v (cls x) := by
    intro x
    have hx_notB : x ∉ B := by rw [hB_empty]; simp
    have hexU : ∃ j : Fin 8, x ∈ Uset G v j := by
      by_contra hnone; push Not at hnone
      exact hx_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
    obtain ⟨j, hxj⟩ := hexU
    have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hxj).2
    have h1 := hcls_spec x (j + 1) (v (j + 1)) (hmem_v (j + 1)) a1
    have h4 := hcls_spec x (j + 4) (v (j + 4)) (hmem_v (j + 4)) a4
    have h7 := hcls_spec x (j + 7) (v (j + 7)) (hmem_v (j + 7)) a7
    have heq : j = cls x := by
      generalize cls x = c at h1 h4 h7 ⊢
      fin_cases j <;> fin_cases c <;> simp at h1 h4 h7 ⊢
    rwa [← heq]
  have hcls_hom : ∀ x y : V, G.Adj x y → cls y = cls x + 1 ∨ cls y = cls x + 4 ∨ cls y = cls x + 7 :=
    fun x y hxy => hcls_spec x (cls y) y (hall_U y) hxy
  -- Convert Möbius labeling (`+1, +4, +7`) to consecutive `And(3)` (`+3, +4, +5`) via `3 * cls x`
  let φ : V → Fin 8 := fun x => 3 * cls x
  have hφ : ∀ x y : V, G.Adj x y →
      3 ≤ ((φ y).val + (3 * 3 - 1) - (φ x).val) % (3 * 3 - 1) ∧
      ((φ y).val + (3 * 3 - 1) - (φ x).val) % (3 * 3 - 1) < 2 * 3 := by
    intro x y hxy
    have h := hcls_hom x y hxy
    dsimp only [φ]
    rcases h with h | h | h <;> rw [h] <;> (generalize cls x = a; fin_cases a <;> decide)
  exact not_hom_andrasfai G h50 (fun H hHTF hHH => five_mul_edges_lt_sq H hHTF hHH) 3 (by decide) φ hφ

end Erdos128_R2_H1_R1_H1

theorem OMA.solution : OMA.R_Erdos128_erdos_128_R2_H1_R1.H1 :=
  Erdos128_R2_H1_R1_H1.main_proof
