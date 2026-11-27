import OMAReductions.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1

-- Step DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1.H1.R1.H2: hypothesis H2 of reduction DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1.H1.R1

/-!
Let `L` be the length of the encoding of `F` and take `w = [a 0, …, a (L - 1)]`. A literal `t` of
a clause of `F` contributes `t.2 + 3` symbols to the encoding, so `t.2 < L` and the entry of `w`
at position `t.2` is `a t.2`.
-/

namespace OMA

theorem len_le {α β : Type} (f : α → List β) : ∀ (l : List α) (x : α), x ∈ l →
    (f x).length ≤ (l.flatMap f).length := by
  intro l
  induction l with
  | nil =>
    intro x hx
    simp at hx
  | cons y ys ih =>
    intro x hx
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp hx with h | h
    · rw [h]
      omega
    · have := ih x h
      omega

end OMA

theorem OMA.solution :
    OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1.H2 := by
  unfold OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1.H2
  intro F a
  refine ⟨(List.range (F.flatMap (fun c => c.flatMap
    (fun t => [true, t.1] ++ List.replicate t.2 true ++ [false]) ++ [false])).length).map a,
    by simp, ?_⟩
  intro c hc t ht
  have h1 := OMA.len_le
    (fun t : Bool × ℕ => [true, t.1] ++ List.replicate t.2 true ++ [false]) c t ht
  have h2 := OMA.len_le (fun c : List (Bool × ℕ) => c.flatMap
    (fun t => [true, t.1] ++ List.replicate t.2 true ++ [false]) ++ [false]) F c hc
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]
    at h1 h2
  have hlt : t.2 < (F.flatMap (fun c => c.flatMap
      (fun t => [true, t.1] ++ List.replicate t.2 true ++ [false]) ++ [false])).length := by
    omega
  generalize (F.flatMap (fun c => c.flatMap
      (fun t => [true, t.1] ++ List.replicate t.2 true ++ [false]) ++ [false])).length = L
    at hlt ⊢
  rw [List.getElem?_map, List.getElem?_range hlt]
  rfl
