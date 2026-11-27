import OMAReductions.R_GracefulLabeling_graceful_tree_conjecture_R1

/-!
# A reflection criterion for deleting the longest cycle edge

A candidate fold acts on a subset of the vertices by reflecting their labels in
the midpoint of the largest label and an unused position. The auxiliary graph
records two reasons why the decision to reflect must propagate. An edge away
from the midpoint propagates the decision to preserve its length. Vertices with
complementary labels propagate it to avoid collisions. The first step exactly
characterizes the folds shrinking the label range. The second concerns trees
whose every near labeling has a path obstructing every such fold.
-/

namespace OMA.R_GracefulLabeling_graceful_tree_conjecture_R1_H2_R1

open SimpleGraph

open scoped Classical

/-- The component of the largest label gives an exact test for a fold. -/
def H1 : Prop :=
  ∀ {V : Type} (T : SimpleGraph V) (f : V → ℕ) (q h : ℕ) (t : V),
    Function.Injective f → (∀ x, f x ≤ q) → f t = q → h < q →
    ((∃ s : Set V, let g (x : V) := if x ∈ s then q + h - f x else f x
      Function.Injective g ∧ (∀ x, g x < q) ∧
        ∀ a b, T.Adj a b → Nat.dist (g a) (g b) = Nat.dist (f a) (f b)) ↔
      ∀ x, Relation.ReflTransGen (fun a b =>
        (T.Adj a b ∧ 2 * f a ≠ q + h ∧ 2 * f b ≠ q + h) ∨ f a + f b = q + h) t x → h < f x)

/-- If every near labeling is obstructed at every axis, find a graceful relabeling. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj],
    T.IsTree →
    let q := T.edgeFinset.card + 1
    let near (f : V → ℕ) : Prop :=
      Function.Injective f ∧ (∀ x, f x ≤ q) ∧ (∃ u, f u = 0) ∧
      ∀ d ∈ Finset.Icc 1 (q - 1), ∃ a b, T.Adj a b ∧ Nat.dist (f a) (f b) = d
    (∃ f : V → ℕ, near f ∧ ∃ t, f t = q) →
    (∀ f : V → ℕ, near f → ∀ t, f t = q → ∀ h < q,
      ∃ x, Relation.ReflTransGen (fun a b =>
        (T.Adj a b ∧ 2 * f a ≠ q + h ∧ 2 * f b ≠ q + h) ∨ f a + f b = q + h) t x ∧ f x ≤ h) →
    ∃ g : V → ℕ, Function.Injective g ∧ (∀ x, g x ≤ q - 1) ∧
      ∀ d ∈ Finset.Icc 1 (q - 1), ∃ a b, T.Adj a b ∧ Nat.dist (g a) (g b) = d

theorem main : H1 → H2 → OMA.R_GracefulLabeling_graceful_tree_conjecture_R1.H2 := by
  classical
  intro hfold hblocked V _ _ T _ hT u v _ _ q hw
  obtain ⟨f, hfi, hbound, hu, hv, hwidth⟩ := hw
  let near (f : V → ℕ) : Prop := Function.Injective f ∧ (∀ x, f x ≤ q) ∧
    (∃ u, f u = 0) ∧ ∀ d ∈ Finset.Icc 1 (q - 1),
      ∃ a b, T.Adj a b ∧ Nat.dist (f a) (f b) = d
  have hnear : near f := by
    refine ⟨hfi, hbound, ⟨u, hu⟩, ?_⟩
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_Icc.mp hd
    obtain ⟨a,b,hadj,hlen⟩ := hwidth d (Finset.mem_Icc.mpr ⟨hd1, by omega⟩)
    rcases hadj with h | h
    · exact ⟨a,b,h,hlen⟩
    · have hpos : 0 < q := Nat.succ_pos _
      obtain ⟨hab, _⟩ := (edge_adj ..).mp h
      rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [hu,hv,Nat.dist] at hlen <;> omega
  by_contra hopen
  apply hopen
  apply hblocked T hT ⟨f, hnear, v, hv⟩
  intro F hF t ht h hh
  by_contra! hno
  obtain ⟨s, hi, hb, he⟩ := (hfold T F q h t hF.1 hF.2.1 ht hh).2 hno
  apply hopen
  refine ⟨_, hi, fun x => Nat.le_pred_of_lt (hb x), ?_⟩
  intro d hd
  obtain ⟨a, b, ha, hw⟩ := hF.2.2.2 d hd
  exact ⟨a, b, ha, (he a b ha).trans hw⟩

end OMA.R_GracefulLabeling_graceful_tree_conjecture_R1_H2_R1
