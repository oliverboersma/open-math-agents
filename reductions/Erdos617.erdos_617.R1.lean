import FormalConjectures.ErdosProblems.«617»

-- Reduction Erdos617.erdos_617.R1 of Erdos Problem 617
-- Proves r = 3 directly; reduces r = 4 and r = 5 to single-graph extremal theorems
-- on Fin 17 and Fin 26 (Xia-Szeider reduction); normalizes r >= 6 to Fin (r^2 + 1) with sparsest color 0.

namespace OMA.R_Erdos617_erdos_617_R1

def H1 : Prop :=
  ∀ adj : Sym2 (Fin 17) → Bool,
    ((Finset.univ : Finset (Fin 17 × Fin 17)).filter
      (fun p => p.1 ≠ p.2 ∧ adj s(p.1, p.2) = true)).card ≤ 68 →
    ∃ S : Finset (Fin 17), S.card = 5 ∧
      ((∀ u ∈ S, ∀ v ∈ S, u ≠ v → adj s(u, v) = false) ∨
       ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1, p.2) = false)).card < 6)

def H2 : Prop :=
  ∀ adj : Sym2 (Fin 26) → Bool,
    ((Finset.univ : Finset (Fin 26 × Fin 26)).filter
      (fun p => p.1 ≠ p.2 ∧ adj s(p.1, p.2) = true)).card ≤ 130 →
    ∃ S : Finset (Fin 26), S.card = 6 ∧
      ((∀ u ∈ S, ∀ v ∈ S, u ≠ v → adj s(u, v) = false) ∨
       ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1, p.2) = false)).card < 8)

def H3 : Prop :=
  ∀ (r : ℕ) (_ : r ≥ 6) (coloring : Sym2 (Fin (r ^ 2 + 1)) → Fin r),
    ((Finset.univ : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).filter
      (fun p => p.1 ≠ p.2 ∧ coloring s(p.1, p.2) = ⟨0, by omega⟩)).card ≤ r * (r ^ 2 + 1) →
    ∃ (S : Finset (Fin (r ^ 2 + 1))) (k : Fin r),
      S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k

section R3Proof

variable {V : Type} [DecidableEq V]

lemma exists_two_of_card_ge_two {S : Finset V} (h : 2 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b := by
  have h1 : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := h1
  have h2 : (S.erase a).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem ha]; omega)
  obtain ⟨b, hb⟩ := h2
  rw [Finset.mem_erase] at hb
  exact ⟨a, ha, b, hb.2, hb.1.symm⟩

lemma exists_three_of_card_ge_three {S : Finset V} (h : 3 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ d ∈ S, a ≠ b ∧ a ≠ d ∧ b ≠ d := by
  have h1 : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := h1
  have h2 : 2 ≤ (S.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb, d, hd, hbd⟩ := exists_two_of_card_ge_two h2
  rw [Finset.mem_erase] at hb hd
  exact ⟨a, ha, b, hb.2, d, hd.2, hb.1.symm, hd.1.symm, hbd⟩

lemma exists_four_of_card_ge_four {S : Finset V} (h : 4 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ d ∈ S, ∃ e ∈ S,
      a ≠ b ∧ a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e := by
  have h1 : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := h1
  have h2 : 3 ≤ (S.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb, d, hd, e, he, hbd, hbe, hde⟩ := exists_three_of_card_ge_three h2
  rw [Finset.mem_erase] at hb hd he
  exact ⟨a, ha, b, hb.2, d, hd.2, e, he.2, hb.1.symm, hd.1.symm, he.1.symm, hbd, hbe, hde⟩

lemma card_four_of_distinct {a b d e : V}
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) :
    ({a, b, d, e} : Finset V).card = 4 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [hde]
  · simp [hbd, hbe]
  · simp [hab, had, hae]

lemma no_diamond {c : Sym2 V → Fin 3}
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    (k : Fin 3) {a b d e : V}
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (h1 : c s(a, b) = k) (h2 : c s(a, d) = k) (h3 : c s(a, e) = k)
    (h4 : c s(b, d) = k) (h5 : c s(b, e) = k) : False := by
  have hcard := card_four_of_distinct hab had hae hbd hbe hde
  have hcol : ∀ j : Fin 3, j ≠ k → c s(d, e) = j := by
    intro j hjk
    obtain ⟨u, hu, v, hv, huv, hcuv⟩ := hbal {a, b, d, e} j hcard
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl
    · exact (huv rfl).elim
    · exact (hjk (hcuv.symm.trans h1)).elim
    · exact (hjk (hcuv.symm.trans h2)).elim
    · exact (hjk (hcuv.symm.trans h3)).elim
    · rw [Sym2.eq_swap] at hcuv; exact (hjk (hcuv.symm.trans h1)).elim
    · exact (huv rfl).elim
    · exact (hjk (hcuv.symm.trans h4)).elim
    · exact (hjk (hcuv.symm.trans h5)).elim
    · rw [Sym2.eq_swap] at hcuv; exact (hjk (hcuv.symm.trans h2)).elim
    · rw [Sym2.eq_swap] at hcuv; exact (hjk (hcuv.symm.trans h4)).elim
    · exact (huv rfl).elim
    · exact hcuv
    · rw [Sym2.eq_swap] at hcuv; exact (hjk (hcuv.symm.trans h3)).elim
    · rw [Sym2.eq_swap] at hcuv; exact (hjk (hcuv.symm.trans h5)).elim
    · rw [Sym2.eq_swap] at hcuv; exact hcuv
    · exact (huv rfl).elim
  fin_cases k
  · have c1 := hcol 1 (by decide)
    have c2 := hcol 2 (by decide)
    rw [c1] at c2; exact absurd c2 (by decide)
  · have c0 := hcol 0 (by decide)
    have c2 := hcol 2 (by decide)
    rw [c0] at c2; exact absurd c2 (by decide)
  · have c0 := hcol 0 (by decide)
    have c1 := hcol 1 (by decide)
    rw [c0] at c1; exact absurd c1 (by decide)

lemma noIndep3_nonNbr [Fintype V] {c : Sym2 V → Fin 3}
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    (v : V) (k : Fin 3) :
    ∀ a ∈ (Finset.univ.erase v).filter (fun u => c s(v, u) ≠ k),
    ∀ b ∈ (Finset.univ.erase v).filter (fun u => c s(v, u) ≠ k),
    ∀ d ∈ (Finset.univ.erase v).filter (fun u => c s(v, u) ≠ k),
    a ≠ b → a ≠ d → b ≠ d → c s(a, b) = k ∨ c s(a, d) = k ∨ c s(b, d) = k := by
  intro a ha b hb d hd hab had hbd
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at ha hb hd
  have hcard := card_four_of_distinct ha.1.symm hb.1.symm hd.1.symm hab had hbd
  obtain ⟨u, hu, w, hw, huw, hcuw⟩ := hbal {v, a, b, d} k hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hw
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl
  · exact (huw rfl).elim
  · exact (ha.2 hcuw).elim
  · exact (hb.2 hcuw).elim
  · exact (hd.2 hcuw).elim
  · rw [Sym2.eq_swap] at hcuw; exact (ha.2 hcuw).elim
  · exact (huw rfl).elim
  · exact Or.inl hcuw
  · exact Or.inr (Or.inl hcuw)
  · rw [Sym2.eq_swap] at hcuw; exact (hb.2 hcuw).elim
  · rw [Sym2.eq_swap] at hcuw; exact Or.inl hcuw
  · exact (huw rfl).elim
  · exact Or.inr (Or.inr hcuw)
  · rw [Sym2.eq_swap] at hcuw; exact (hd.2 hcuw).elim
  · rw [Sym2.eq_swap] at hcuw; exact Or.inr (Or.inl hcuw)
  · rw [Sym2.eq_swap] at hcuw; exact Or.inr (Or.inr hcuw)
  · exact (huw rfl).elim

lemma nbr_deg_le_one {c : Sym2 V → Fin 3}
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    (k : Fin 3) {x : V} {N : Finset V} (hN : ∀ y ∈ N, y ≠ x ∧ c s(x, y) = k)
    {a : V} (ha : a ∈ N) :
    ((N.erase a).filter (fun y => c s(a, y) = k)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro y₁ hy₁ y₂ hy₂
  by_contra hne
  simp only [Finset.mem_filter, Finset.mem_erase] at hy₁ hy₂
  exact no_diamond hbal k (hN a ha).1.symm (hN y₁ hy₁.1.2).1.symm (hN y₂ hy₂.1.2).1.symm
    hy₁.1.1.symm hy₂.1.1.symm hne
    (hN a ha).2 (hN y₁ hy₁.1.2).2 (hN y₂ hy₂.1.2).2 hy₁.2 hy₂.2

lemma M_clique {c : Sym2 V → Fin 3} {k : Fin 3} {U : Finset V}
    (hU : ∀ a ∈ U, ∀ b ∈ U, ∀ d ∈ U, a ≠ b → a ≠ d → b ≠ d →
      c s(a, b) = k ∨ c s(a, d) = k ∨ c s(b, d) = k)
    {x : V} (hx : x ∈ U)
    {u v : V} (hu : u ∈ (U.erase x).filter (fun y => c s(x, y) ≠ k))
    (hv : v ∈ (U.erase x).filter (fun y => c s(x, y) ≠ k)) (huv : u ≠ v) :
    c s(u, v) = k := by
  simp only [Finset.mem_filter, Finset.mem_erase] at hu hv
  rcases hU x hx u hu.1.2 v hv.1.2 hu.1.1.symm hv.1.1.symm huv with h | h | h
  · exact (hu.2 h).elim
  · exact (hv.2 h).elim
  · exact h

lemma M_card_le_three {c : Sym2 V → Fin 3}
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    {k : Fin 3} {U : Finset V}
    (hU : ∀ a ∈ U, ∀ b ∈ U, ∀ d ∈ U, a ≠ b → a ≠ d → b ≠ d →
      c s(a, b) = k ∨ c s(a, d) = k ∨ c s(b, d) = k)
    {x : V} (hx : x ∈ U) :
    ((U.erase x).filter (fun y => c s(x, y) ≠ k)).card ≤ 3 := by
  by_contra h
  have h4 : 4 ≤ ((U.erase x).filter (fun y => c s(x, y) ≠ k)).card := by omega
  obtain ⟨a, ha, b, hb, d, hd, e, he, hab, had, hae, hbd, hbe, hde⟩ :=
    exists_four_of_card_ge_four h4
  exact no_diamond hbal k hab had hae hbd hbe hde
    (M_clique hU hx ha hb hab) (M_clique hU hx ha hd had) (M_clique hU hx ha he hae)
    (M_clique hU hx hb hd hbd) (M_clique hU hx hb he hbe)

lemma N_card_le_four {c : Sym2 V → Fin 3}
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    {k : Fin 3} {U : Finset V}
    (hU : ∀ a ∈ U, ∀ b ∈ U, ∀ d ∈ U, a ≠ b → a ≠ d → b ≠ d →
      c s(a, b) = k ∨ c s(a, d) = k ∨ c s(b, d) = k)
    {x : V} :
    ((U.erase x).filter (fun y => c s(x, y) = k)).card ≤ 4 := by
  set N := (U.erase x).filter (fun y => c s(x, y) = k)
  have hN : ∀ y ∈ N, y ≠ x ∧ c s(x, y) = k := by
    intro y hy
    simp only [N, Finset.mem_filter, Finset.mem_erase] at hy
    exact ⟨hy.1.1, hy.2⟩
  have hNU : N ⊆ U := by
    intro y hy
    simp only [N, Finset.mem_filter, Finset.mem_erase] at hy
    exact hy.1.2
  by_contra h
  have h5 : 5 ≤ N.card := by omega
  obtain ⟨a₁, ha₁⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
  set N₁ := (N.erase a₁).filter (fun y => c s(a₁, y) ≠ k)
  have hN₁_split : ((N.erase a₁).filter (fun y => c s(a₁, y) = k)).card + N₁.card =
      (N.erase a₁).card := Finset.card_filter_add_card_filter_not _
  have hN₁_le : ((N.erase a₁).filter (fun y => c s(a₁, y) = k)).card ≤ 1 :=
    nbr_deg_le_one hbal k hN ha₁
  have hN₁_ge : 3 ≤ N₁.card := by
    rw [Finset.card_erase_of_mem ha₁] at hN₁_split; omega
  obtain ⟨a₂, ha₂⟩ := Finset.card_pos.mp (by omega : 0 < N₁.card)
  have ha₂N : a₂ ∈ N := (Finset.mem_erase.mp (Finset.mem_filter.mp ha₂).1).2
  set N₂ := (N₁.erase a₂).filter (fun y => c s(a₂, y) ≠ k)
  have hN₂_split : ((N₁.erase a₂).filter (fun y => c s(a₂, y) = k)).card + N₂.card =
      (N₁.erase a₂).card := Finset.card_filter_add_card_filter_not _
  have hN₂_sub : (N₁.erase a₂).filter (fun y => c s(a₂, y) = k) ⊆
      (N.erase a₂).filter (fun y => c s(a₂, y) = k) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_erase] at hy ⊢
    exact ⟨⟨hy.1.1, (Finset.mem_erase.mp (Finset.mem_filter.mp hy.1.2).1).2⟩, hy.2⟩
  have hN₂_le : ((N₁.erase a₂).filter (fun y => c s(a₂, y) = k)).card ≤ 1 :=
    (Finset.card_le_card hN₂_sub).trans (nbr_deg_le_one hbal k hN ha₂N)
  have hN₂_ge : 1 ≤ N₂.card := by
    rw [Finset.card_erase_of_mem ha₂] at hN₂_split; omega
  obtain ⟨a₃, ha₃⟩ := Finset.card_pos.mp (by omega : 0 < N₂.card)
  have ha₂_info := Finset.mem_filter.mp ha₂
  have ha₂_er := Finset.mem_erase.mp ha₂_info.1
  have ha₃_info := Finset.mem_filter.mp ha₃
  have ha₃_er := Finset.mem_erase.mp ha₃_info.1
  have ha₃_info1 := Finset.mem_filter.mp ha₃_er.2
  have ha₃_er1 := Finset.mem_erase.mp ha₃_info1.1
  rcases hU a₁ (hNU ha₁) a₂ (hNU ha₂N) a₃ (hNU ha₃_er1.2)
      ha₂_er.1.symm ha₃_er1.1.symm ha₃_er.1.symm with hc | hc | hc
  · exact ha₂_info.2 hc
  · exact ha₃_info1.2 hc
  · exact ha₃_info.2 hc

lemma N_clique_of_M_card_three {c : Sym2 V → Fin 3}
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    {k : Fin 3} {U : Finset V}
    (hU : ∀ a ∈ U, ∀ b ∈ U, ∀ d ∈ U, a ≠ b → a ≠ d → b ≠ d →
      c s(a, b) = k ∨ c s(a, d) = k ∨ c s(b, d) = k)
    {x : V} (hx : x ∈ U)
    (hM3 : ((U.erase x).filter (fun y => c s(x, y) ≠ k)).card = 3)
    {y₁ y₂ : V}
    (hy₁ : y₁ ∈ (U.erase x).filter (fun y => c s(x, y) = k))
    (hy₂ : y₂ ∈ (U.erase x).filter (fun y => c s(x, y) = k))
    (hne : y₁ ≠ y₂) : c s(y₁, y₂) = k := by
  set M := (U.erase x).filter (fun y => c s(x, y) ≠ k)
  have hle1 : ∀ y ∈ (U.erase x).filter (fun y => c s(x, y) = k),
      (M.filter (fun m => c s(y, m) = k)).card ≤ 1 := by
    intro y hy
    rw [Finset.card_le_one]
    intro m₁ hm₁ m₂ hm₂
    by_contra hmne
    simp only [Finset.mem_filter] at hm₁ hm₂
    have hrem : 0 < ((M.erase m₁).erase m₂).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hmne, hm₂.1⟩),
        Finset.card_erase_of_mem hm₁.1, hM3]
      norm_num
    obtain ⟨m₃, hm₃⟩ := Finset.card_pos.mp hrem
    rw [Finset.mem_erase, Finset.mem_erase] at hm₃
    have hyM : ∀ m ∈ M, m ≠ y := by
      intro m hm hmy
      subst hmy
      exact (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hy).2
    have hc1y : c s(m₁, y) = k := by rw [Sym2.eq_swap]; exact hm₁.2
    have hc2y : c s(m₂, y) = k := by rw [Sym2.eq_swap]; exact hm₂.2
    exact no_diamond hbal k hmne hm₃.2.1.symm (hyM m₁ hm₁.1) hm₃.1.symm (hyM m₂ hm₂.1)
      (hyM m₃ hm₃.2.2)
      (M_clique hU hx hm₁.1 hm₂.1 hmne)
      (M_clique hU hx hm₁.1 hm₃.2.2 hm₃.2.1.symm) hc1y
      (M_clique hU hx hm₂.1 hm₃.2.2 hm₃.1.symm) hc2y
  set B := M.filter (fun m => c s(y₁, m) = k) ∪ M.filter (fun m => c s(y₂, m) = k)
  have hBcard : B.card < M.card := by
    have h1 : B.card ≤ (M.filter (fun m => c s(y₁, m) = k)).card +
        (M.filter (fun m => c s(y₂, m) = k)).card :=
      Finset.card_union_le _ _
    have h2 := hle1 y₁ hy₁
    have h3 := hle1 y₂ hy₂
    omega
  obtain ⟨m, hmM, hmB⟩ := Finset.exists_mem_notMem_of_card_lt_card hBcard
  simp only [B, Finset.mem_union, Finset.mem_filter, not_or, not_and] at hmB
  have hmy₁ : m ≠ y₁ := by
    intro h; subst h; exact (Finset.mem_filter.mp hmM).2 (Finset.mem_filter.mp hy₁).2
  have hmy₂ : m ≠ y₂ := by
    intro h; subst h; exact (Finset.mem_filter.mp hmM).2 (Finset.mem_filter.mp hy₂).2
  have hmU : m ∈ U := (Finset.mem_erase.mp (Finset.mem_filter.mp hmM).1).2
  have hy₁U : y₁ ∈ U := (Finset.mem_erase.mp (Finset.mem_filter.mp hy₁).1).2
  have hy₂U : y₂ ∈ U := (Finset.mem_erase.mp (Finset.mem_filter.mp hy₂).1).2
  rcases hU m hmU y₁ hy₁U y₂ hy₂U hmy₁ hmy₂ hne with hc | hc | hc
  · rw [Sym2.eq_swap] at hc; exact (hmB.1 hmM hc).elim
  · rw [Sym2.eq_swap] at hc; exact (hmB.2 hmM hc).elim
  · exact hc

lemma N_card_le_two_of_M_three {c : Sym2 V → Fin 3}
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    {k : Fin 3} {U : Finset V}
    (hU : ∀ a ∈ U, ∀ b ∈ U, ∀ d ∈ U, a ≠ b → a ≠ d → b ≠ d →
      c s(a, b) = k ∨ c s(a, d) = k ∨ c s(b, d) = k)
    {x : V} (hx : x ∈ U)
    (hM3 : ((U.erase x).filter (fun y => c s(x, y) ≠ k)).card = 3) :
    ((U.erase x).filter (fun y => c s(x, y) = k)).card ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ ((U.erase x).filter (fun y => c s(x, y) = k)).card := by omega
  obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, h12, h13, h23⟩ := exists_three_of_card_ge_three h3
  have hc12 := N_clique_of_M_card_three hbal hU hx hM3 hy₁ hy₂ h12
  have hc23 := N_clique_of_M_card_three hbal hU hx hM3 hy₂ hy₃ h23
  simp only [Finset.mem_filter, Finset.mem_erase] at hy₁ hy₂ hy₃
  rw [Sym2.eq_swap] at hc12
  exact no_diamond hbal k hy₂.1.1.symm hy₁.1.1.symm hy₃.1.1.symm h12.symm h23 h13
    hy₂.2 hy₁.2 hy₃.2 hc12 hc23

lemma not_N_four_of_M_two {c : Sym2 V → Fin 3}
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    {k : Fin 3} {U : Finset V}
    (hU : ∀ a ∈ U, ∀ b ∈ U, ∀ d ∈ U, a ≠ b → a ≠ d → b ≠ d →
      c s(a, b) = k ∨ c s(a, d) = k ∨ c s(b, d) = k)
    {x : V}
    (hM2 : ((U.erase x).filter (fun y => c s(x, y) ≠ k)).card = 2)
    (hN4 : ((U.erase x).filter (fun y => c s(x, y) = k)).card = 4) : False := by
  set M := (U.erase x).filter (fun y => c s(x, y) ≠ k)
  set N := (U.erase x).filter (fun y => c s(x, y) = k)
  obtain ⟨u, huM⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
  have huU : u ∈ U := (Finset.mem_erase.mp (Finset.mem_filter.mp huM).1).2
  have hux : u ≠ x := (Finset.mem_erase.mp (Finset.mem_filter.mp huM).1).1
  have huN : ∀ y ∈ N, u ≠ y := by
    intro y hy huy; subst huy
    exact (Finset.mem_filter.mp huM).2 (Finset.mem_filter.mp hy).2
  have hNinfo : ∀ y ∈ N, y ∈ U ∧ y ≠ x ∧ c s(x, y) = k := by
    intro y hy
    simp only [N, Finset.mem_filter, Finset.mem_erase] at hy
    exact ⟨hy.1.2, hy.1.1, hy.2⟩
  have hdeg1 : ∀ a ∈ N, ∀ b ∈ N, ∀ d ∈ N, a ≠ b → a ≠ d → b ≠ d →
      c s(a, b) = k → c s(a, d) = k → False := by
    intro a ha b hb d hd hab had hbd h1 h2
    exact no_diamond hbal k (hNinfo a ha).2.1.symm (hNinfo b hb).2.1.symm (hNinfo d hd).2.1.symm
      hab had hbd (hNinfo a ha).2.2 (hNinfo b hb).2.2 (hNinfo d hd).2.2 h1 h2
  have hex : ∀ a ∈ N, ∃ b ∈ N, b ≠ a ∧ c s(a, b) = k := by
    intro a ha
    by_contra hno
    push Not at hno
    have h3 : 3 ≤ (N.erase a).card := by rw [Finset.card_erase_of_mem ha, hN4]
    obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ := exists_three_of_card_ge_three h3
    rw [Finset.mem_erase] at hp hq hr
    have hcpq : c s(p, q) = k := by
      rcases hU a (hNinfo a ha).1 p (hNinfo p hp.2).1 q (hNinfo q hq.2).1
          hp.1.symm hq.1.symm hpq with h | h | h
      · exact (hno p hp.2 hp.1 h).elim
      · exact (hno q hq.2 hq.1 h).elim
      · exact h
    have hcqr : c s(q, r) = k := by
      rcases hU a (hNinfo a ha).1 q (hNinfo q hq.2).1 r (hNinfo r hr.2).1
          hq.1.symm hr.1.symm hqr with h | h | h
      · exact (hno q hq.2 hq.1 h).elim
      · exact (hno r hr.2 hr.1 h).elim
      · exact h
    rw [Sym2.eq_swap] at hcpq
    exact hdeg1 q hq.2 p hp.2 r hr.2 hpq.symm hqr hpr hcpq hcqr
  obtain ⟨a₁, ha₁⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
  obtain ⟨b₁, hb₁, hb₁a₁, hc1⟩ := hex a₁ ha₁
  have hrem : 0 < ((N.erase a₁).erase b₁).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hb₁a₁, hb₁⟩),
      Finset.card_erase_of_mem ha₁, hN4]
    norm_num
  obtain ⟨a₂, ha₂'⟩ := Finset.card_pos.mp hrem
  rw [Finset.mem_erase, Finset.mem_erase] at ha₂'
  obtain ⟨ha₂b₁, ha₂a₁, ha₂⟩ := ha₂'
  obtain ⟨b₂, hb₂, hb₂a₂, hc2⟩ := hex a₂ ha₂
  have hb₂a₁ : b₂ ≠ a₁ := by
    intro h
    rw [h, Sym2.eq_swap] at hc2
    exact hdeg1 a₁ ha₁ b₁ hb₁ a₂ ha₂ hb₁a₁.symm ha₂a₁.symm ha₂b₁.symm hc1 hc2
  have hb₂b₁ : b₂ ≠ b₁ := by
    intro h
    rw [h, Sym2.eq_swap] at hc2
    have hc1' : c s(b₁, a₁) = k := by rw [Sym2.eq_swap]; exact hc1
    exact hdeg1 b₁ hb₁ a₁ ha₁ a₂ ha₂ hb₁a₁ ha₂b₁.symm ha₂a₁.symm hc1' hc2
  have hna₁a₂ : c s(a₁, a₂) ≠ k := fun h =>
    hdeg1 a₁ ha₁ b₁ hb₁ a₂ ha₂ hb₁a₁.symm ha₂a₁.symm ha₂b₁.symm hc1 h
  have hna₁b₂ : c s(a₁, b₂) ≠ k := fun h =>
    hdeg1 a₁ ha₁ b₁ hb₁ b₂ hb₂ hb₁a₁.symm hb₂a₁.symm hb₂b₁.symm hc1 h
  have hnb₁a₂ : c s(b₁, a₂) ≠ k := fun h => by
    have hc1' : c s(b₁, a₁) = k := by rw [Sym2.eq_swap]; exact hc1
    exact hdeg1 b₁ hb₁ a₁ ha₁ a₂ ha₂ hb₁a₁ ha₂b₁.symm ha₂a₁.symm hc1' h
  have hnb₁b₂ : c s(b₁, b₂) ≠ k := fun h => by
    have hc1' : c s(b₁, a₁) = k := by rw [Sym2.eq_swap]; exact hc1
    exact hdeg1 b₁ hb₁ a₁ ha₁ b₂ hb₂ hb₁a₁ hb₂b₁.symm hb₂a₁.symm hc1' h
  have hpair2 : c s(u, a₂) = k → c s(u, b₂) = k → False := by
    intro h1 h2
    have hxa₂ := (hNinfo a₂ ha₂).2.2; rw [Sym2.eq_swap] at hxa₂
    have hxb₂ := (hNinfo b₂ hb₂).2.2; rw [Sym2.eq_swap] at hxb₂
    rw [Sym2.eq_swap] at h1 h2
    exact no_diamond hbal k hb₂a₂.symm (hNinfo a₂ ha₂).2.1 (huN a₂ ha₂).symm
      (hNinfo b₂ hb₂).2.1 (huN b₂ hb₂).symm hux.symm hc2 hxa₂ h1 hxb₂ h2
  by_cases hua₁ : c s(u, a₁) = k
  · by_cases hub₁ : c s(u, b₁) = k
    · have hxa₁ := (hNinfo a₁ ha₁).2.2; rw [Sym2.eq_swap] at hxa₁
      have hxb₁ := (hNinfo b₁ hb₁).2.2; rw [Sym2.eq_swap] at hxb₁
      rw [Sym2.eq_swap] at hua₁ hub₁
      exact no_diamond hbal k hb₁a₁.symm (hNinfo a₁ ha₁).2.1 (huN a₁ ha₁).symm
        (hNinfo b₁ hb₁).2.1 (huN b₁ hb₁).symm hux.symm hc1 hxa₁ hua₁ hxb₁ hub₁
    · have hua₂ : c s(u, a₂) = k := by
        rcases hU u huU b₁ (hNinfo b₁ hb₁).1 a₂ (hNinfo a₂ ha₂).1
            (huN b₁ hb₁) (huN a₂ ha₂) ha₂b₁.symm with h | h | h
        · exact (hub₁ h).elim
        · exact h
        · exact (hnb₁a₂ h).elim
      have hub₂ : c s(u, b₂) = k := by
        rcases hU u huU b₁ (hNinfo b₁ hb₁).1 b₂ (hNinfo b₂ hb₂).1
            (huN b₁ hb₁) (huN b₂ hb₂) hb₂b₁.symm with h | h | h
        · exact (hub₁ h).elim
        · exact h
        · exact (hnb₁b₂ h).elim
      exact hpair2 hua₂ hub₂
  · have hua₂ : c s(u, a₂) = k := by
      rcases hU u huU a₁ (hNinfo a₁ ha₁).1 a₂ (hNinfo a₂ ha₂).1
          (huN a₁ ha₁) (huN a₂ ha₂) ha₂a₁.symm with h | h | h
      · exact (hua₁ h).elim
      · exact h
      · exact (hna₁a₂ h).elim
    have hub₂ : c s(u, b₂) = k := by
      rcases hU u huU a₁ (hNinfo a₁ ha₁).1 b₂ (hNinfo b₂ hb₂).1
          (huN a₁ ha₁) (huN b₂ hb₂) hb₂a₁.symm with h | h | h
      · exact (hua₁ h).elim
      · exact h
      · exact (hna₁b₂ h).elim
    exact hpair2 hua₂ hub₂

lemma card_le_six_of_noIndep3 {c : Sym2 V → Fin 3}
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    (k : Fin 3) {U : Finset V}
    (hU : ∀ a ∈ U, ∀ b ∈ U, ∀ d ∈ U, a ≠ b → a ≠ d → b ≠ d →
      c s(a, b) = k ∨ c s(a, d) = k ∨ c s(b, d) = k) : U.card ≤ 6 := by
  by_cases hne : U.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hsplit : ((U.erase x).filter (fun y => c s(x, y) = k)).card +
        ((U.erase x).filter (fun y => c s(x, y) ≠ k)).card = (U.erase x).card :=
      Finset.card_filter_add_card_filter_not _
    have her : (U.erase x).card + 1 = U.card := Finset.card_erase_add_one hx
    have hM : ((U.erase x).filter (fun y => c s(x, y) ≠ k)).card ≤ 3 :=
      M_card_le_three hbal hU hx
    have hN : ((U.erase x).filter (fun y => c s(x, y) = k)).card ≤ 4 :=
      N_card_le_four hbal hU
    by_cases hM3 : ((U.erase x).filter (fun y => c s(x, y) ≠ k)).card = 3
    · have hN2 := N_card_le_two_of_M_three hbal hU hx hM3
      omega
    · by_cases hM2 : ((U.erase x).filter (fun y => c s(x, y) ≠ k)).card = 2
      · by_cases hN4 : ((U.erase x).filter (fun y => c s(x, y) = k)).card = 4
        · exact (not_N_four_of_M_two hbal hU hM2 hN4).elim
        · omega
      · omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

lemma deg_eq_three [Fintype V] {c : Sym2 V → Fin 3} (hV : Fintype.card V = 10)
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    (v : V) (k : Fin 3) :
    ((Finset.univ.erase v).filter (fun u => c s(v, u) = k)).card = 3 := by
  have hge3 : ∀ j : Fin 3, 3 ≤ ((Finset.univ.erase v).filter (fun u => c s(v, u) = j)).card := by
    intro j
    have hsplit : ((Finset.univ.erase v).filter (fun u => c s(v, u) = j)).card +
        ((Finset.univ.erase v).filter (fun u => c s(v, u) ≠ j)).card =
        (Finset.univ.erase v).card := Finset.card_filter_add_card_filter_not _
    have hcard9 : (Finset.univ.erase v).card = 9 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV]
    have hle6 := card_le_six_of_noIndep3 hbal j (noIndep3_nonNbr hbal v j)
    omega
  have hsum : ∑ j : Fin 3, ((Finset.univ.erase v).filter (fun u => c s(v, u) = j)).card = 9 := by
    have hbi : (Finset.univ : Finset (Fin 3)).biUnion
        (fun j => (Finset.univ.erase v).filter (fun u => c s(v, u) = j)) =
        Finset.univ.erase v := by
      ext u
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
      exact ⟨fun ⟨_, hu, _⟩ => hu, fun hu => ⟨c s(v, u), hu, rfl⟩⟩
    have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin 3)) : Set (Fin 3))
        (fun j => (Finset.univ.erase v).filter (fun u => c s(v, u) = j)) := by
      intro i _ j _ hij
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro u hui huj
      exact hij ((Finset.mem_filter.mp hui).2.symm.trans (Finset.mem_filter.mp huj).2)
    rw [← Finset.card_biUnion hdisj, hbi,
      Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV]
  rw [Fin.sum_univ_three] at hsum
  have h0 := hge3 0
  have h1 := hge3 1
  have h2 := hge3 2
  fin_cases k
  · change ((Finset.univ.erase v).filter (fun u => c s(v, u) = 0)).card = 3; omega
  · change ((Finset.univ.erase v).filter (fun u => c s(v, u) = 1)).card = 3; omega
  · change ((Finset.univ.erase v).filter (fun u => c s(v, u) = 2)).card = 3; omega

lemma exists_triangle [Fintype V] {c : Sym2 V → Fin 3} (hV : Fintype.card V = 10)
    (hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k)
    (x : V) :
    ∃ a b : V, x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
      c s(x, a) = 0 ∧ c s(x, b) = 0 ∧ c s(a, b) = 0 := by
  have hnon : ((Finset.univ.erase x).filter (fun u => c s(x, u) ≠ 0)).card = 6 := by
    have hsplit : ((Finset.univ.erase x).filter (fun u => c s(x, u) = 0)).card +
        ((Finset.univ.erase x).filter (fun u => c s(x, u) ≠ 0)).card =
        (Finset.univ.erase x).card := Finset.card_filter_add_card_filter_not _
    have hdeg := deg_eq_three hV hbal x 0
    have hcard9 : (Finset.univ.erase x).card = 9 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hV]
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (by omega : 0 < ((Finset.univ.erase x).filter (fun u => c s(x, u) ≠ 0)).card)
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hv
  set U := (Finset.univ.erase v).filter (fun u => c s(v, u) ≠ 0)
  have hxU : x ∈ U := by
    simp only [U, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    refine ⟨hv.1.symm, ?_⟩
    rw [Sym2.eq_swap]; exact hv.2
  have hUcard : U.card = 6 := by
    have hsplit : ((Finset.univ.erase v).filter (fun u => c s(v, u) = 0)).card + U.card =
        (Finset.univ.erase v).card := Finset.card_filter_add_card_filter_not _
    have hdeg := deg_eq_three hV hbal v 0
    have hcard9 : (Finset.univ.erase v).card = 9 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hV]
    omega
  have hU := noIndep3_nonNbr hbal v 0
  set N := (U.erase x).filter (fun y => c s(x, y) = 0)
  set M := (U.erase x).filter (fun y => c s(x, y) ≠ 0)
  have hsplit : N.card + M.card = 5 := by
    have hs : N.card + M.card = (U.erase x).card := Finset.card_filter_add_card_filter_not _
    rw [Finset.card_erase_of_mem hxU, hUcard] at hs; exact hs
  have hNle3 : N.card ≤ 3 := by
    have hsub : N ⊆ (Finset.univ.erase x).filter (fun y => c s(x, y) = 0) := by
      intro y hy
      simp only [N, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true] at hy ⊢
      exact ⟨hy.1.1, hy.2⟩
    exact (Finset.card_le_card hsub).trans (deg_eq_three hV hbal x 0).le
  have hMle3 : M.card ≤ 3 := M_card_le_three hbal hU hxU
  by_cases hM3 : M.card = 3
  · have hN2 : 2 ≤ N.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := exists_two_of_card_ge_two hN2
    have hcab := N_clique_of_M_card_three hbal hU hxU hM3 ha hb hab
    simp only [N, Finset.mem_filter, Finset.mem_erase] at ha hb
    exact ⟨a, b, ha.1.1.symm, hb.1.1.symm, hab, ha.2, hb.2, hcab⟩
  · have hN3 : 3 ≤ N.card := by omega
    obtain ⟨a, ha, b, hb, d, hd, hab, had, hbd⟩ := exists_three_of_card_ge_three hN3
    simp only [N, Finset.mem_filter, Finset.mem_erase] at ha hb hd
    rcases hU a ha.1.2 b hb.1.2 d hd.1.2 hab had hbd with hc | hc | hc
    · exact ⟨a, b, ha.1.1.symm, hb.1.1.symm, hab, ha.2, hb.2, hc⟩
    · exact ⟨a, d, ha.1.1.symm, hd.1.1.symm, had, ha.2, hd.2, hc⟩
    · exact ⟨b, d, hb.1.1.symm, hd.1.1.symm, hbd, hb.2, hd.2, hc⟩

lemma solve_r3 [Fintype V] (hV : Fintype.card V = 10) (c : Sym2 V → Fin 3) :
    ∃ (S : Finset V) (k : Fin 3),
      S.card = 4 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k := by
  classical
  by_contra h
  push Not at h
  have hbal : ∀ (S : Finset V) (k : Fin 3), S.card = 4 →
      ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ c s(u, v) = k := fun S k hS => h S k hS
  let triSet : V → Finset V := fun x =>
    Finset.univ.filter (fun y =>
      y = x ∨ ∃ z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ c s(x, y) = 0 ∧ c s(x, z) = 0 ∧ c s(y, z) = 0)
  have htri_eq : ∀ x : V, ∃ a b : V, x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
      c s(x, a) = 0 ∧ c s(x, b) = 0 ∧ c s(a, b) = 0 ∧ triSet x = {x, a, b} := by
    intro x
    obtain ⟨a, b, hxa, hxb, hab, h1, h2, h3⟩ := exists_triangle hV hbal x
    refine ⟨a, b, hxa, hxb, hab, h1, h2, h3, ?_⟩
    ext y
    simp only [triSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨z, hxy, hxz, hyz, hcxy, hcxz, hcyz⟩)
      · exact Or.inl rfl
      · by_contra hyab
        push Not at hyab
        obtain ⟨_, hya, hyb⟩ := hyab
        by_cases hza : z = a
        · subst hza
          rw [Sym2.eq_swap] at hcyz
          exact no_diamond hbal 0 hxa hxb hxy hab hya.symm hyb.symm h1 h2 hcxy h3 hcyz
        · by_cases hzb : z = b
          · subst hzb
            rw [Sym2.eq_swap] at h3 hcyz
            exact no_diamond hbal 0 hxb hxa hxy hab.symm hyb.symm hya.symm h2 h1 hcxy h3 hcyz
          · have hsub : ({a, b, y, z} : Finset V) ⊆
                (Finset.univ.erase x).filter (fun u => c s(x, u) = 0) := by
              intro u hu
              simp only [Finset.mem_insert, Finset.mem_singleton] at hu
              simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
              rcases hu with rfl | rfl | rfl | rfl
              · exact ⟨hxa.symm, h1⟩
              · exact ⟨hxb.symm, h2⟩
              · exact ⟨hxy.symm, hcxy⟩
              · exact ⟨hxz.symm, hcxz⟩
            have h4 := card_four_of_distinct hab hya.symm (Ne.symm hza)
              hyb.symm (Ne.symm hzb) hyz
            have hle := Finset.card_le_card hsub
            rw [h4, deg_eq_three hV hbal x 0] at hle
            omega
    · rintro (rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hxa, hxb, hab, h1, h2, h3⟩
      · rw [Sym2.eq_swap] at h3
        exact Or.inr ⟨a, hxb, hxa, hab.symm, h2, h1, h3⟩
  have hcard3 : ∀ x : V, (triSet x).card = 3 := by
    intro x
    obtain ⟨a, b, hxa, hxb, hab, _, _, _, heq⟩ := htri_eq x
    rw [heq, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hab]
    · simp [hxa, hxb]
  have hmem_self : ∀ x : V, x ∈ triSet x := by
    intro x
    simp [triSet]
  have htri_symm : ∀ x y : V, y ∈ triSet x → triSet y = triSet x := by
    intro x y hy
    obtain ⟨a, b, hxa, hxb, hab, h1, h2, h3, heq⟩ := htri_eq x
    rw [heq] at hy ⊢
    symm
    apply Finset.eq_of_subset_of_card_le _ (by rw [hcard3 y, ← heq, hcard3 x])
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hw
    simp only [triSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨b, hxa, hxb, hab, h1, h2, h3⟩
    · exact Or.inr ⟨a, hxb, hxa, hab.symm, h2, h1, by rw [Sym2.eq_swap]; exact h3⟩
    · exact Or.inr ⟨b, hxa.symm, hab, hxb, by rw [Sym2.eq_swap]; exact h1, h3, h2⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨x, hab, hxa.symm, hxb.symm, h3,
        by rw [Sym2.eq_swap]; exact h1, by rw [Sym2.eq_swap]; exact h2⟩
    · exact Or.inr ⟨a, hxb.symm, hab.symm, hxa,
        by rw [Sym2.eq_swap]; exact h2, by rw [Sym2.eq_swap]; exact h3, h1⟩
    · exact Or.inr ⟨x, hab.symm, hxb.symm, hxa.symm,
        by rw [Sym2.eq_swap]; exact h3, by rw [Sym2.eq_swap]; exact h2,
        by rw [Sym2.eq_swap]; exact h1⟩
    · exact Or.inl rfl
  let F : Finset (Finset V) := Finset.univ.image triSet
  have hdisj : Set.PairwiseDisjoint (F : Set (Finset V)) id := by
    intro C₁ hC₁ C₂ hC₂ hne
    rw [Finset.mem_coe, Finset.mem_image] at hC₁ hC₂
    obtain ⟨x₁, _, rfl⟩ := hC₁
    obtain ⟨x₂, _, rfl⟩ := hC₂
    show Disjoint (triSet x₁) (triSet x₂)
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    exact hne ((htri_symm x₁ z hz₁).symm.trans (htri_symm x₂ z hz₂))
  have hunion : F.biUnion id = Finset.univ := by
    ext x
    simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
    exact ⟨triSet x, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, hmem_self x⟩
  have hsum : (Finset.univ : Finset V).card = ∑ C ∈ F, C.card := by
    rw [← hunion, Finset.card_biUnion hdisj]
    rfl
  have hsum3 : ∑ C ∈ F, C.card = F.card * 3 := by
    have hconst : ∀ C ∈ F, C.card = 3 := by
      intro C hC
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hC
      exact hcard3 x
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rw [Finset.card_univ, hV, hsum3] at hsum
  omega

end R3Proof

section GeneralReduction

lemma exists_sparse_color {r : ℕ} (hr : 1 ≤ r) (c : Sym2 (Fin (r ^ 2 + 1)) → Fin r) :
    ∃ k : Fin r,
      ((Finset.univ : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).filter
        (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = k)).card ≤ r * (r ^ 2 + 1) := by
  let offDiag : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1)) :=
    Finset.univ.filter (fun p => p.1 ≠ p.2)
  have hoff_card : offDiag.card = r * (r * (r ^ 2 + 1)) := by
    have h1 : offDiag = (Finset.univ : Finset (Fin (r ^ 2 + 1))).offDiag := by
      ext p; simp [offDiag, Finset.mem_offDiag]
    rw [h1, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hbi : (Finset.univ : Finset (Fin r)).biUnion
      (fun k => Finset.univ.filter (fun p : Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1) =>
        p.1 ≠ p.2 ∧ c s(p.1, p.2) = k)) = offDiag := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, offDiag]
    exact ⟨fun ⟨_, hp, _⟩ => hp, fun hp => ⟨c s(p.1, p.2), hp, rfl⟩⟩
  have hdisj : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin r)) : Set (Fin r))
      (fun k => Finset.univ.filter (fun p : Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1) =>
        p.1 ≠ p.2 ∧ c s(p.1, p.2) = k)) := by
    intro i _ j _ hij
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hpi hpj
    exact hij ((Finset.mem_filter.mp hpi).2.2.symm.trans (Finset.mem_filter.mp hpj).2.2)
  have hsum : ∑ k : Fin r,
      ((Finset.univ : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).filter
        (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = k)).card = r * (r * (r ^ 2 + 1)) := by
    rw [← Finset.card_biUnion hdisj, hbi, hoff_card]
  by_contra h
  push Not at h
  have hgt : r * (r * (r ^ 2 + 1)) < ∑ k : Fin r,
      ((Finset.univ : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).filter
        (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = k)).card := by
    have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have hstrict : ∑ _k : Fin r, (r * (r ^ 2 + 1)) < ∑ k : Fin r,
        ((Finset.univ : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).filter
          (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = k)).card :=
      Finset.sum_lt_sum_of_nonempty hne (fun k _ => h k)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using hstrict
  omega

lemma missing_color_of_few_nonedges {r : ℕ} (c : Sym2 (Fin (r ^ 2 + 1)) → Fin r)
    (k : Fin r) (S : Finset (Fin (r ^ 2 + 1)))
    (hfew : ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) ≠ k)).card < 2 * (r - 1)) :
    ∃ j : Fin r, ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ j := by
  by_contra hall
  push Not at hall
  have hge2 : ∀ j ∈ (Finset.univ : Finset (Fin r)).erase k,
      2 ≤ ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j)).card := by
    intro j _
    obtain ⟨u, hu, v, hv, huv, hcuv⟩ := hall j
    have hsub : ({(u, v), (v, u)} : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))) ⊆
        (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      simp only [Finset.mem_filter, Finset.mem_product]
      rcases hp with rfl | rfl
      · exact ⟨⟨hu, hv⟩, huv, hcuv⟩
      · exact ⟨⟨hv, hu⟩, huv.symm, by rw [Sym2.eq_swap]; exact hcuv⟩
    have h2 : ({(u, v), (v, u)} : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp [Prod.ext_iff, huv]
    calc
      2 = ({(u, v), (v, u)} : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).card := h2.symm
      _ ≤ ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j)).card :=
        Finset.card_le_card hsub
  have hbi : ((Finset.univ : Finset (Fin r)).erase k).biUnion
      (fun j => (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j)) =
      (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) ≠ k) := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter]
    exact ⟨fun ⟨j, hjk, hp, hne, hcj⟩ => ⟨hp, hne, hcj.symm ▸ hjk⟩,
      fun ⟨hp, hne, hck⟩ => ⟨c s(p.1, p.2), hck, hp, hne, rfl⟩⟩
  have hdisj : Set.PairwiseDisjoint (((Finset.univ : Finset (Fin r)).erase k) : Set (Fin r))
      (fun j => (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j)) := by
    intro i _ j _ hij
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hpi hpj
    exact hij ((Finset.mem_filter.mp hpi).2.2.symm.trans (Finset.mem_filter.mp hpj).2.2)
  have hcard_ge : 2 * (r - 1) ≤
      ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) ≠ k)).card := by
    rw [← hbi, Finset.card_biUnion hdisj]
    calc
      2 * (r - 1) = ∑ _j ∈ (Finset.univ : Finset (Fin r)).erase k, 2 := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
          Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
      _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin r)).erase k,
          ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = j)).card :=
        Finset.sum_le_sum hge2
  omega

lemma transport_from_fin {r : ℕ} {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = r ^ 2 + 1) (coloring : Sym2 V → Fin r)
    (hfin : ∀ c : Sym2 (Fin (r ^ 2 + 1)) → Fin r,
      ∃ (S : Finset (Fin (r ^ 2 + 1))) (k : Fin r),
        S.card = r + 1 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → c s(u, v) ≠ k) :
    ∃ (S : Finset V) (k : Fin r),
      S.card = r + 1 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  let e : V ≃ Fin (r ^ 2 + 1) := Fintype.equivFinOfCardEq hV
  let c : Sym2 (Fin (r ^ 2 + 1)) → Fin r := fun x => coloring (Sym2.map e.symm x)
  obtain ⟨S, k, hScard, hS⟩ := hfin c
  refine ⟨S.map e.symm.toEmbedding, k, by rw [Finset.card_map, hScard], ?_⟩
  intro u hu v hv huv
  rw [Finset.mem_map] at hu hv
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hv
  have hab : a ≠ b := fun h => huv (congrArg e.symm h)
  have := hS a ha b hb hab
  simpa [c, Sym2.map_mk] using this

lemma main_aux (h1 : H1) (h2 : H2) (h3 : H3)
    (r : ℕ) (hr : r ≥ 3) {V : Type} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = r ^ 2 + 1) (coloring : Sym2 V → Fin r) :
    ∃ (S : Finset V) (k : Fin r),
      S.card = r + 1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → coloring s(u, v) ≠ k := by
  by_cases hr3 : r = 3
  · subst hr3
    exact solve_r3 (by norm_num at hV; exact hV) coloring
  · by_cases hr4 : r = 4
    · subst hr4
      apply transport_from_fin hV coloring
      intro c
      obtain ⟨k, hk⟩ := exists_sparse_color (r := 4) (by omega) c
      let adj : Sym2 (Fin 17) → Bool := fun e => decide (c e = k)
      have hadj : ((Finset.univ : Finset (Fin 17 × Fin 17)).filter
          (fun p => p.1 ≠ p.2 ∧ adj s(p.1, p.2) = true)).card ≤ 68 := by
        simpa [adj] using hk
      obtain ⟨S, hScard, hS | hS⟩ := h1 adj hadj
      · refine ⟨S, k, hScard, ?_⟩
        intro u hu v hv huv
        have := hS u hu v hv huv
        simpa [adj] using this
      · have hfew : ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) ≠ k)).card < 2 * (4 - 1) := by
          simpa [adj] using hS
        obtain ⟨j, hj⟩ := missing_color_of_few_nonedges (r := 4) c k S hfew
        exact ⟨S, j, hScard, hj⟩
    · by_cases hr5 : r = 5
      · subst hr5
        apply transport_from_fin hV coloring
        intro c
        obtain ⟨k, hk⟩ := exists_sparse_color (r := 5) (by omega) c
        let adj : Sym2 (Fin 26) → Bool := fun e => decide (c e = k)
        have hadj : ((Finset.univ : Finset (Fin 26 × Fin 26)).filter
            (fun p => p.1 ≠ p.2 ∧ adj s(p.1, p.2) = true)).card ≤ 130 := by
          simpa [adj] using hk
        obtain ⟨S, hScard, hS | hS⟩ := h2 adj hadj
        · refine ⟨S, k, hScard, ?_⟩
          intro u hu v hv huv
          have := hS u hu v hv huv
          simpa [adj] using this
        · have hfew : ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) ≠ k)).card < 2 * (5 - 1) := by
            simpa [adj] using hS
          obtain ⟨j, hj⟩ := missing_color_of_few_nonedges (r := 5) c k S hfew
          exact ⟨S, j, hScard, hj⟩
      · have hr6 : r ≥ 6 := by omega
        apply transport_from_fin hV coloring
        intro c
        obtain ⟨k, hk⟩ := exists_sparse_color (r := r) (by omega) c
        let σ : Equiv.Perm (Fin r) := Equiv.swap k ⟨0, by omega⟩
        let c' : Sym2 (Fin (r ^ 2 + 1)) → Fin r := fun e => σ (c e)
        have hc' : ((Finset.univ : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).filter
            (fun p => p.1 ≠ p.2 ∧ c' s(p.1, p.2) = ⟨0, by omega⟩)).card ≤ r * (r ^ 2 + 1) := by
          have heq : (Finset.univ : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).filter
              (fun p => p.1 ≠ p.2 ∧ c' s(p.1, p.2) = ⟨0, by omega⟩) =
              (Finset.univ : Finset (Fin (r ^ 2 + 1) × Fin (r ^ 2 + 1))).filter
              (fun p => p.1 ≠ p.2 ∧ c s(p.1, p.2) = k) := by
            ext p
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, c', σ]
            constructor
            · rintro ⟨hne, hEq⟩
              refine ⟨hne, ?_⟩
              have hinv := congrArg (Equiv.swap k ⟨0, by omega⟩) hEq
              simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using hinv
            · rintro ⟨hne, hEq⟩
              exact ⟨hne, by rw [hEq, Equiv.swap_apply_left]⟩
          rw [heq]
          exact hk
        obtain ⟨S, j, hScard, hS⟩ := h3 r hr6 c' hc'
        refine ⟨S, σ.symm j, hScard, ?_⟩
        intro u hu v hv huv hcol
        have hbad := hS u hu v hv huv
        apply hbad
        simp only [c', hcol, Equiv.apply_symm_apply]

end GeneralReduction

theorem main : H1 → H2 → H3 → type_of% @Erdos617.erdos_617 := by
  intro h1 h2 h3 r hr V instF instD hV coloring
  exact @main_aux h1 h2 h3 r hr V instF instD hV coloring

end OMA.R_Erdos617_erdos_617_R1
