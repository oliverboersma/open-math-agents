import OMAStatements.S_mo_228227
import Mathlib

namespace MO228227Aux

/-- `A` sits just below `B`: all of `A` except its top element `x` lies below the bottom
element `y` of `B`, and `x` lies between `y` and the rest of `B`
(sorted pattern a ... a b a b ... b). -/
def lower {n : ℕ} (A B : Finset (Fin n)) : Prop :=
  ∃ x ∈ A, ∃ y ∈ B, y < x ∧ (∀ a ∈ A, a ≠ x → a < y) ∧ (∀ b ∈ B, b ≠ y → x < b)

/-- The colouring: an edge is red iff one side sits just below the other. -/
def red {n : ℕ} (A B : Finset (Fin n)) : Prop := lower A B ∨ lower B A

lemma red_symm {n : ℕ} (A B : Finset (Fin n)) : red A B ↔ red B A := or_comm

lemma chain {n : ℕ} {X Y Z : Finset (Fin n)} (hY : 3 ≤ Y.card)
    (h1 : lower X Y) (h2 : lower Y Z) : ∀ a ∈ X, ∀ c ∈ Z, a < c := by
  obtain ⟨x, hxX, y, hyY, hyx, hXy, hxY⟩ := h1
  obtain ⟨y', hy'Y, z, hzZ, hzy', hYz, hy'Z⟩ := h2
  obtain ⟨w, hwY, hwy, hwy'⟩ : ∃ w ∈ Y, w ≠ y ∧ w ≠ y' := by
    by_contra hcon
    have hsub : Y ⊆ {y, y'} := by
      intro w hw
      by_cases h : w = y
      · simp [h]
      · have h' : w = y' := by
          by_contra hne
          exact hcon ⟨w, hw, h, hne⟩
        simp [h']
    have hle := Finset.card_le_card hsub
    have h2 : ({y, y'} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    omega
  have hxw : x < w := hxY w hwY hwy
  have hwz : w < z := hYz w hwY hwy'
  have hxz : x < z := lt_trans hxw hwz
  intro a ha c hc
  have hax : a ≤ x := by
    by_cases h : a = x
    · exact le_of_eq h
    · exact le_of_lt (lt_trans (hXy a ha h) hyx)
  have hzc : z ≤ c := by
    by_cases h : c = z
    · exact le_of_eq h.symm
    · exact le_of_lt (lt_trans hzy' (hy'Z c hc h))
  exact lt_of_le_of_lt hax (lt_of_lt_of_le hxz hzc)

lemma not_red_of_below {n : ℕ} {X Z : Finset (Fin n)} (hX : 2 ≤ X.card)
    (h : ∀ a ∈ X, ∀ c ∈ Z, a < c) : ¬ red X Z := by
  rintro (⟨x, hxX, z, hzZ, hzx, -, -⟩ | ⟨z, hzZ, x, hxX, hxz, -, hzX⟩)
  · exact lt_asymm (h x hxX z hzZ) hzx
  · obtain ⟨a, haX, hax⟩ : ∃ a ∈ X, a ≠ x := by
      by_contra hcon
      have hsub : X ⊆ {x} := by
        intro a ha
        by_contra hne
        exact hcon ⟨a, ha, fun h => hne (by simp [h])⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_singleton] at hle
      omega
    exact lt_asymm (h a haX z hzZ) (hzX a haX hax)

lemma no_triangle {n : ℕ} {A B C : Finset (Fin n)}
    (hA : 3 ≤ A.card) (hB : 3 ≤ B.card) (hC : 3 ≤ C.card)
    (hAB : red A B) (hBC : red B C) (hAC : red A C) : False := by
  rcases hAB with hab | hba
  · rcases hBC with hbc | hcb
    · exact not_red_of_below (by omega) (chain hB hab hbc) hAC
    · rcases hAC with hac | hca
      · exact not_red_of_below (by omega) (chain hC hac hcb) (Or.inl hab)
      · exact not_red_of_below (by omega) (chain hA hca hab) (Or.inl hcb)
  · rcases hBC with hbc | hcb
    · rcases hAC with hac | hca
      · exact not_red_of_below (by omega) (chain hA hba hac) (Or.inl hbc)
      · exact not_red_of_below (by omega) (chain hC hbc hca) (Or.inl hba)
    · exact not_red_of_below (by omega) (chain hB hcb hba) ((red_symm A C).mp hAC)

/-- Positions `0, ..., k-2, k` of the sorted `3k`-set. -/
def gA (k : ℕ) (i : Fin k) : Fin (3 * k) :=
  if i.val + 1 < k then ⟨i.val, by have := i.isLt; omega⟩ else ⟨k, by have := i.isLt; omega⟩

/-- Positions `k-1, k+1, ..., 2k-1` of the sorted `3k`-set. -/
def gB (k : ℕ) (i : Fin k) : Fin (3 * k) :=
  if i.val = 0 then ⟨k - 1, by have := i.isLt; omega⟩ else ⟨k + i.val, by have := i.isLt; omega⟩

lemma gA_val (k : ℕ) (i : Fin k) : (gA k i).val = if i.val + 1 < k then i.val else k := by
  unfold gA
  split_ifs <;> rfl

lemma gB_val (k : ℕ) (i : Fin k) : (gB k i).val = if i.val = 0 then k - 1 else k + i.val := by
  unfold gB
  split_ifs <;> rfl

lemma gA_inj (k : ℕ) : Function.Injective (gA k) := by
  intro i j h
  have h' := congrArg Fin.val h
  rw [gA_val, gA_val] at h'
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at h' <;> omega

lemma gB_inj (k : ℕ) : Function.Injective (gB k) := by
  intro i j h
  have h' := congrArg Fin.val h
  rw [gB_val, gB_val] at h'
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at h' <;> omega

lemma gA_ne_gB (k : ℕ) (i j : Fin k) : gA k i ≠ gB k j := by
  intro h
  have h' := congrArg Fin.val h
  rw [gA_val, gB_val] at h'
  have hi := i.isLt
  have hj := j.isLt
  split_ifs at h' <;> omega

lemma gA_last (k : ℕ) (hk : 2 ≤ k) : (gA k ⟨k - 1, by omega⟩).val = k := by
  rw [gA_val]
  have h : ¬ ((⟨k - 1, by omega⟩ : Fin k).val + 1 < k) := by
    show ¬ (k - 1 + 1 < k)
    omega
  rw [if_neg h]

lemma gB_first (k : ℕ) (hk : 2 ≤ k) : (gB k ⟨0, by omega⟩).val = k - 1 := by
  rw [gB_val, if_pos rfl]

lemma exists_red {n k : ℕ} (hk : 2 ≤ k) (S : Finset (Fin n)) (hS : S.card = 3 * k) :
    ∃ A B : Finset (Fin n), A ⊆ S ∧ B ⊆ S ∧ A.card = k ∧ B.card = k ∧ Disjoint A B ∧
      red A B := by
  obtain ⟨f, hfS, hflt, hfinj⟩ : ∃ f : Fin (3 * k) → Fin n, (∀ j, f j ∈ S) ∧
      (∀ i j : Fin (3 * k), i.val < j.val → f i < f j) ∧ Function.Injective f := by
    refine ⟨S.orderEmbOfFin hS, fun j => S.orderEmbOfFin_mem hS j, ?_, (S.orderEmbOfFin hS).injective⟩
    intro i j hij
    exact (S.orderEmbOfFin hS).lt_iff_lt.mpr (Fin.lt_def.mpr hij)
  refine ⟨Finset.univ.image (fun i => f (gA k i)), Finset.univ.image (fun i => f (gB k i)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hfS _
  · intro a ha
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact hfS _
  · have hinj : Function.Injective (fun i => f (gA k i)) :=
      fun i j h => gA_inj k (hfinj h)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · have hinj : Function.Injective (fun i => f (gB k i)) :=
      fun i j h => gB_inj k (hfinj h)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hb
    exact gA_ne_gB k i j (hfinj hj).symm
  · left
    refine ⟨f (gA k ⟨k - 1, by omega⟩), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩,
      f (gB k ⟨0, by omega⟩), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_, ?_, ?_⟩
    · apply hflt
      rw [gA_last k hk, gB_first k hk]
      omega
    · intro a ha hne
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
      apply hflt
      rw [gB_first k hk, gA_val]
      have hi := i.isLt
      split_ifs with h
      · omega
      · exfalso
        have e : gA k i = gA k ⟨k - 1, by omega⟩ :=
          Fin.ext (by rw [gA_last k hk, gA_val, if_neg h])
        exact hne (by rw [e])
    · intro b hb hne
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
      apply hflt
      rw [gA_last k hk, gB_val]
      have hj := j.isLt
      split_ifs with h
      · exfalso
        have e : gB k j = gB k ⟨0, by omega⟩ :=
          Fin.ext (by rw [gB_first k hk, gB_val, if_pos h])
        exact hne (by rw [e])
      · omega

end MO228227Aux

theorem OMA.solution : type_of% @OMA.S_mo_228227.main := by
  intro k hk N
  refine ⟨N, le_refl N, MO228227Aux.red, ?_, ?_, ?_⟩
  · intro A B
    exact MO228227Aux.red_symm A B
  · intro S hS
    exact MO228227Aux.exists_red (by omega) S hS
  · intro A B C hA hB hC _ _ _ h
    exact MO228227Aux.no_triangle (by omega) (by omega) (by omega) h.1 h.2.1 h.2.2
