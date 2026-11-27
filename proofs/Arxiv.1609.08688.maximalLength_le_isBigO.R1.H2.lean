import OMAReductions.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1

-- Step Arxiv.1609.08688.maximalLength_le_isBigO.R1.H2: hypothesis H2 of reduction Arxiv.1609.08688.maximalLength_le_isBigO.R1

/-!
A `2`-increasing list `s` of triples in `[1, n]^3` has no repetition, so the set `t` of triples
`x : Fin n × Fin n × Fin n` whose shift `(x.1 + 1, x.2.1 + 1, x.2.2 + 1)` lies in `s` has
`s.length` elements. Two different members of `s` are `2`-comparable in one of the two orders;
this rules out two triples of `t` agreeing in two coordinates (`ExplicitDisjoint`) and three
triples forming an accidental triangle (`NoAccidental`). In particular lengths are at most `n^3`,
so the supremum defining `maximalLength n` is attained.
-/

open Arxiv.«1609.08688» SimpleGraph.TripartiteFromTriangles

namespace OMA

def vec {n : ℕ} (x : Fin n × Fin n × Fin n) : Fin 3 → ℕ :=
  ![x.1.val + 1, x.2.1.val + 1, x.2.2.val + 1]

theorem vec_inj {n : ℕ} : Function.Injective (vec (n := n)) := by
  intro x y h
  have h0 : x.1.val + 1 = y.1.val + 1 := congrFun h 0
  have h1 : x.2.1.val + 1 = y.2.1.val + 1 := congrFun h 1
  have h2 : x.2.2.val + 1 = y.2.2.val + 1 := congrFun h 2
  exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))

theorem lt2_vec {n : ℕ} (x y : Fin n × Fin n × Fin n) (h : lt₂ (vec x) (vec y)) :
    (x.1.val < y.1.val ∧ x.2.1.val < y.2.1.val) ∨ (x.1.val < y.1.val ∧ x.2.2.val < y.2.2.val) ∨
      (x.2.1.val < y.2.1.val ∧ x.2.2.val < y.2.2.val) := by
  obtain ⟨i, j, hij, h1, h2⟩ := h
  have e0 : ∀ z : Fin n × Fin n × Fin n, vec z 0 = z.1.val + 1 := fun _ => rfl
  have e1 : ∀ z : Fin n × Fin n × Fin n, vec z 1 = z.2.1.val + 1 := fun _ => rfl
  have e2 : ∀ z : Fin n × Fin n × Fin n, vec z 2 = z.2.2.val + 1 := fun _ => rfl
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, e0, e1, e2,
    ne_eq, not_true_eq_false] at hij h1 h2 <;> omega

theorem key (n : ℕ) (s : List (Fin 3 → ℕ)) (hr : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n)
    (hinc : IsIncreasing₂ s) :
    ∃ t : Finset (Fin n × Fin n × Fin n), t.card = s.length ∧ ExplicitDisjoint t ∧
      NoAccidental t := by
  classical
  have hpw : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → lt₂ a b ∨ lt₂ b a := by
    intro a ha b hb hab
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact Or.inl (List.pairwise_iff_getElem.1 hinc i j hi hj h)
    · subst h
      exact absurd rfl hab
    · exact Or.inr (List.pairwise_iff_getElem.1 hinc j i hj hi h)
  have hnodup : s.Nodup := by
    have hne : ∀ {a b : Fin 3 → ℕ}, lt₂ a b → a ≠ b := by
      intro a b h hab
      subst hab
      exact not_lt₂_self a h
    exact List.Pairwise.imp hne hinc
  have hmem : ∀ x : Fin n × Fin n × Fin n,
      x ∈ Finset.univ.filter (fun x : Fin n × Fin n × Fin n => vec x ∈ s) ↔ vec x ∈ s := by
    intro x
    simp
  have hcmp : ∀ x y : Fin n × Fin n × Fin n, vec x ∈ s → vec y ∈ s → x ≠ y →
      ((x.1.val < y.1.val ∧ x.2.1.val < y.2.1.val) ∨
        (x.1.val < y.1.val ∧ x.2.2.val < y.2.2.val) ∨
        (x.2.1.val < y.2.1.val ∧ x.2.2.val < y.2.2.val)) ∨
      ((y.1.val < x.1.val ∧ y.2.1.val < x.2.1.val) ∨
        (y.1.val < x.1.val ∧ y.2.2.val < x.2.2.val) ∨
        (y.2.1.val < x.2.1.val ∧ y.2.2.val < x.2.2.val)) := by
    intro x y hx hy hxy
    exact (hpw _ hx _ hy (fun h => hxy (vec_inj h))).imp (lt2_vec x y) (lt2_vec y x)
  refine ⟨Finset.univ.filter (fun x : Fin n × Fin n × Fin n => vec x ∈ s), ?_, ?_, ?_⟩
  · have himg : (Finset.univ.filter (fun x : Fin n × Fin n × Fin n => vec x ∈ s)).image vec =
        s.toFinset := by
      ext a
      rw [Finset.mem_image, List.mem_toFinset]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hmem x).1 hx
      · intro ha
        have hra := hr a ha
        have h0 := Set.mem_Icc.1 (hra (Set.mem_range_self 0))
        have h1 := Set.mem_Icc.1 (hra (Set.mem_range_self 1))
        have h2 := Set.mem_Icc.1 (hra (Set.mem_range_self 2))
        have hv : vec ((⟨a 0 - 1, by omega⟩, ⟨a 1 - 1, by omega⟩, ⟨a 2 - 1, by omega⟩) :
            Fin n × Fin n × Fin n) = a := by
          funext i
          fin_cases i
          · show a 0 - 1 + 1 = a 0
            omega
          · show a 1 - 1 + 1 = a 1
            omega
          · show a 2 - 1 + 1 = a 2
            omega
        exact ⟨_, (hmem _).2 (by rw [hv]; exact ha), hv⟩
    rw [← Finset.card_image_of_injective _ vec_inj, himg, List.toFinset_card_of_nodup hnodup]
  · refine ⟨?_, ?_, ?_⟩
    · intro a b c a2 h1 h2
      by_contra hne
      have h := hcmp (a, b, c) (a2, b, c) ((hmem _).1 h1) ((hmem _).1 h2)
        (fun h => hne (Prod.mk.inj h).1)
      dsimp only at h
      omega
    · intro a b c b2 h1 h2
      by_contra hne
      have h := hcmp (a, b, c) (a, b2, c) ((hmem _).1 h1) ((hmem _).1 h2)
        (fun h => hne (Prod.mk.inj (Prod.mk.inj h).2).1)
      dsimp only at h
      omega
    · intro a b c c2 h1 h2
      by_contra hne
      have h := hcmp (a, b, c) (a, b, c2) ((hmem _).1 h1) ((hmem _).1 h2)
        (fun h => hne (Prod.mk.inj (Prod.mk.inj h).2).2)
      dsimp only at h
      omega
  · refine ⟨?_⟩
    intro a a2 b b2 c c2 h1 h2 h3
    by_contra hcon
    rw [not_or, not_or] at hcon
    obtain ⟨ha, hb, hc⟩ := hcon
    have m1 := (hmem _).1 h1
    have m2 := (hmem _).1 h2
    have m3 := (hmem _).1 h3
    have h12 := hcmp (a2, b, c) (a, b2, c) m1 m2 (fun h => ha (Prod.mk.inj h).1.symm)
    have h23 := hcmp (a, b2, c) (a, b, c2) m2 m3
      (fun h => hb (Prod.mk.inj (Prod.mk.inj h).2).1.symm)
    have h13 := hcmp (a2, b, c) (a, b, c2) m1 m3 (fun h => ha (Prod.mk.inj h).1.symm)
    dsimp only at h12 h23 h13
    omega

end OMA

theorem OMA.solution : OMA.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1.H2 := by
  unfold OMA.R_Arxiv_1609_08688_maximalLength_le_isBigO_R1.H2
  intro n
  have hmemS : maximalLength n ∈
      { List.length s | (s) (_ : ∀ a ∈ s, Set.range a ⊆ Set.Icc 1 n) (_ : IsIncreasing₂ s) } := by
    refine Nat.sSup_mem ?_ ?_
    · exact ⟨0, ⟨[], by simp, isIncreasing₂_nil, rfl⟩⟩
    · refine ⟨n ^ 3, ?_⟩
      rintro x ⟨s, hr, hinc, rfl⟩
      obtain ⟨t, ht, _, _⟩ := OMA.key n s hr hinc
      rw [← ht]
      calc t.card ≤ (Finset.univ : Finset (Fin n × Fin n × Fin n)).card := Finset.card_le_univ t
        _ = n ^ 3 := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin]
          ring
  obtain ⟨s, hr, hinc, hlen⟩ := hmemS
  obtain ⟨t, ht, h1, h2⟩ := OMA.key n s hr hinc
  exact ⟨t, ht.trans hlen, h1, h2⟩
