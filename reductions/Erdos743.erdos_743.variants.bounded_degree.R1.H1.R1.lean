import OMAReductions.R_Erdos743_erdos_743_variants_bounded_degree_R1

/-! Allen, Böttcher, Clemens, Hladký, Piguet and Taraz, arXiv:2106.11720,
Section 2. For the trees of intermediate order, Theorem 5 handles a positive
density of trees with linearly many leaves. Otherwise the degree sum and a
greedy path argument supply linearly many disjoint bare paths in many trees,
which is the setting of Theorem 10. We use paths with twelve degree-two
vertices, hence eleven edges. -/

namespace OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1
open Filter Finset SimpleGraph
open scoped Classical

/-- Degree accounting for the vertices outside the paths of degree two. -/
def H1 : Prop :=
  ∀ (k : ℕ) (G : SimpleGraph (Fin k)), 2 ≤ k → G.IsTree →
    let L := (univ.filter (fun v => G.degree v = 1)).card
    let B := univ.filter (fun v => G.degree v ≠ 2)
    B.card ≤ 2*L ∧ (∑ v ∈ B, G.degree v) ≤ 4*L

/-- Extract disjoint bare paths when both the number and total degree of exceptions are small. -/
def H2 : Prop :=
  ∀ (k r : ℕ) (G : SimpleGraph (Fin k)), 0 < r → 4000000*r ≤ k → G.IsTree →
    let B := univ.filter (fun v => G.degree v ≠ 2)
    B.card ≤ 2*r → (∑ v ∈ B, G.degree v) ≤ 4*r →
    (∃ f : Fin r × Fin 12 → Fin k, Function.Injective f ∧
      (∀ i (j : Fin 11), G.Adj (f (i,j.castSucc)) (f (i,j.succ))) ∧
      ∀ i j, G.degree (f (i,j)) = 2)

/-- Leaf-rich packing, the complete-host tree case of Theorem 5. -/
def H3 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ T : (k : ℕ) → SimpleGraph (Fin k),
    (∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧ ((T k).maxDegree : ℝ) ≤ c*(n:ℝ)/Real.log n) →
    let r := n/100000000
    let S := Icc ((n+7)/8) (7*n/8)
    r ≤ (S.filter (fun k => r ≤ (univ.filter (fun v => (T k).degree v = 1)).card)).card →
      Erdos743.IsPacking n (Set.Icc 2 n) T

/-- Packing using bare paths and the remaining trees' odd-degree leaves, Theorem 10. -/
def H4 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ T : (k : ℕ) → SimpleGraph (Fin k),
    (∀ k ∈ Set.Icc 2 n, (T k).IsTree ∧ ((T k).maxDegree : ℝ) ≤ c*(n:ℝ)/Real.log n) →
    let r := n/100000000
    let S := Icc ((n+7)/8) (7*n/8)
    r ≤ (S.filter (fun k => (∃ f : Fin r × Fin 12 → Fin k, Function.Injective f ∧
      (∀ i (j : Fin 11), (T k).Adj (f (i,j.castSucc)) (f (i,j.succ))) ∧
      ∀ i j, (T k).degree (f (i,j)) = 2))).card →
      Erdos743.IsPacking n (Set.Icc 2 n) T

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1.H1 := by
  classical
  intro count extract manyLeaves manyPaths
  obtain ⟨a,ha,pa⟩ := manyLeaves
  obtain ⟨b,hb,pb⟩ := manyPaths
  refine ⟨min a b,lt_min ha hb,?_⟩
  filter_upwards [pa,pb,eventually_ge_atTop 100000000] with n packA packB hn
  intro T ht
  have lx : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have bounded (c : ℝ) (hc : min a b ≤ c) (k : ℕ) (hk : k ∈ Set.Icc 2 n) :
      (T k).IsTree ∧ ((T k).maxDegree : ℝ) ≤ c*(n:ℝ)/Real.log n :=
    ⟨(ht k hk).1,(ht k hk).2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)) lx)⟩
  let S := Icc ((n+7)/8) (7*n/8)
  let r := n/100000000
  let rich (k : ℕ) := r ≤ (univ.filter (fun v => (T k).degree v = 1)).card
  by_cases plentiful : r ≤ (S.filter rich).card
  · exact packA T (bounded a (min_le_left _ _)) plentiful
  · apply packB T (bounded b (min_le_right _ _))
    have size : 2*r ≤ S.card := by dsimp [S,r]; rw [Nat.card_Icc]; omega
    have partition := card_filter_add_card_filter_not (s := S) rich
    have enough : r ≤ (S.filter (fun k => ¬rich k)).card := by omega
    apply enough.trans (card_le_card ?_)
    intro k hk
    obtain ⟨hs,few⟩ := mem_filter.mp hk
    obtain ⟨ll,uu⟩ := mem_Icc.mp hs
    have inRange : k ∈ Set.Icc 2 n := ⟨by omega,by omega⟩
    have tree := (ht k inRange).1
    have nums := count k (T k) inRange.1 tree
    have nonrich : (univ.filter (fun v => (T k).degree v = 1)).card < r := Nat.lt_of_not_ge few
    refine mem_filter.mpr ⟨hs, extract k r (T k) (by dsimp [r]; omega)
      (by dsimp [r]; omega) tree ?_ ?_⟩
    · exact nums.1.trans (Nat.mul_le_mul_left _ nonrich.le)
    · exact nums.2.trans (Nat.mul_le_mul_left _ nonrich.le)

end OMA.R_Erdos743_erdos_743_variants_bounded_degree_R1_H1_R1
