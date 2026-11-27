import OMAReductions.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1

-- Step Erdos757.erdos_757.variants.lowerBound.R1.H1.R1.H1: hypothesis H1 of reduction Erdos757.erdos_757.variants.lowerBound.R1.H1.R1
-- Credit: @ishaanzee
-- Proof: two 3-APs of A sharing two points, or sharing their middle point with different ends,
-- give four points of A with at most nine distinct differences, against the 11-difference
-- hypothesis. The six possible shapes of the fourth point are handled with explicit lists.

open scoped Pointwise

namespace E757H1Aux

/-- If all sixteen differences of `w, x, y, z` lie in a list of length at most `10`, the
difference set has at most `10` elements. -/
lemma diff_bound (w x y z : ℝ) (L : List ℝ) (hL : L.length ≤ 10)
    (hmem : ∀ u ∈ [w, x, y, z], ∀ v ∈ [w, x, y, z], u - v ∈ L) :
    (({w, x, y, z} : Set ℝ) - {w, x, y, z}).ncard ≤ 10 := by
  classical
  have hsub : (({w, x, y, z} : Set ℝ) - {w, x, y, z}) ⊆ (L.toFinset : Set ℝ) := by
    rintro _ ⟨u, hu, v, hv, rfl⟩
    simp only [Finset.mem_coe, List.mem_toFinset]
    apply hmem
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact hu
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact hv
  calc _ ≤ (L.toFinset : Set ℝ).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ ≤ L.length := List.toFinset_card_le L
    _ ≤ 10 := hL

lemma ncard_four {w x y z : ℝ} (h1 : w ≠ x) (h2 : w ≠ y) (h3 : w ≠ z) (h4 : x ≠ y) (h5 : x ≠ z)
    (h6 : y ≠ z) : ({w, x, y, z} : Set ℝ).ncard = 4 := by
  rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3]), Set.ncard_insert_of_notMem (by simp [h4, h5]),
    Set.ncard_pair h6]


lemma shape (A : Finset ℝ)
    (key : ∀ w x y z : ℝ, w ∈ A → x ∈ A → y ∈ A → z ∈ A →
      w ≠ x → w ≠ y → w ≠ z → x ≠ y → x ≠ z → y ≠ z →
      (({w, x, y, z} : Set ℝ) - {w, x, y, z}).ncard ≤ 10 → False)
    (a b z : ℝ) (hab : a < b) (ha : a ∈ A) (hb : b ∈ A) (hc : 2 * b - a ∈ A) (hz : z ∈ A)
    (hshape : z = 4 * b - 3 * a ∨ z = 3 * b - 2 * a ∨ z = 2 * a - b ∨ z = 3 * a - 2 * b ∨
      2 * z = a + b ∨ 2 * z = 3 * b - a) : False := by
  rcases hshape with rfl | rfl | rfl | rfl | h | h
  · refine key a b (2 * b - a) _ ha hb hc hz (by intro h; linarith) (by intro h; linarith)
      (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) ?_
    refine diff_bound _ _ _ _ [0, b - a, a - b, 2 * (b - a), 2 * (a - b), 3 * (b - a), 3 * (a - b),
      4 * (b - a), 4 * (a - b)] (by simp) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro u (rfl | rfl | rfl | rfl) v (rfl | rfl | rfl | rfl) <;> first
      | (left; ring1)
      | (right; left; ring1)
      | (right; right; left; ring1)
      | (right; right; right; left; ring1)
      | (right; right; right; right; left; ring1)
      | (right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; right; ring1)
  · refine key a b (2 * b - a) _ ha hb hc hz (by intro h; linarith) (by intro h; linarith)
      (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) ?_
    refine diff_bound _ _ _ _ [0, b - a, a - b, 2 * (b - a), 2 * (a - b), 3 * (b - a), 3 * (a - b),
      4 * (b - a), 4 * (a - b)] (by simp) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro u (rfl | rfl | rfl | rfl) v (rfl | rfl | rfl | rfl) <;> first
      | (left; ring1)
      | (right; left; ring1)
      | (right; right; left; ring1)
      | (right; right; right; left; ring1)
      | (right; right; right; right; left; ring1)
      | (right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; right; ring1)
  · refine key a b (2 * b - a) _ ha hb hc hz (by intro h; linarith) (by intro h; linarith)
      (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) ?_
    refine diff_bound _ _ _ _ [0, b - a, a - b, 2 * (b - a), 2 * (a - b), 3 * (b - a), 3 * (a - b),
      4 * (b - a), 4 * (a - b)] (by simp) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro u (rfl | rfl | rfl | rfl) v (rfl | rfl | rfl | rfl) <;> first
      | (left; ring1)
      | (right; left; ring1)
      | (right; right; left; ring1)
      | (right; right; right; left; ring1)
      | (right; right; right; right; left; ring1)
      | (right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; right; ring1)
  · refine key a b (2 * b - a) _ ha hb hc hz (by intro h; linarith) (by intro h; linarith)
      (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) ?_
    refine diff_bound _ _ _ _ [0, b - a, a - b, 2 * (b - a), 2 * (a - b), 3 * (b - a), 3 * (a - b),
      4 * (b - a), 4 * (a - b)] (by simp) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro u (rfl | rfl | rfl | rfl) v (rfl | rfl | rfl | rfl) <;> first
      | (left; ring1)
      | (right; left; ring1)
      | (right; right; left; ring1)
      | (right; right; right; left; ring1)
      | (right; right; right; right; left; ring1)
      | (right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; right; ring1)
  · obtain rfl : z = (a + b) / 2 := by linarith
    refine key a b (2 * b - a) _ ha hb hc hz (by intro h; linarith) (by intro h; linarith)
      (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) ?_
    refine diff_bound _ _ _ _ [0, (b - a) / 2, (a - b) / 2, b - a, a - b, 3 * (b - a) / 2,
      3 * (a - b) / 2, 2 * (b - a), 2 * (a - b)] (by simp) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro u (rfl | rfl | rfl | rfl) v (rfl | rfl | rfl | rfl) <;> first
      | (left; ring1)
      | (right; left; ring1)
      | (right; right; left; ring1)
      | (right; right; right; left; ring1)
      | (right; right; right; right; left; ring1)
      | (right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; right; ring1)
  · obtain rfl : z = (3 * b - a) / 2 := by linarith
    refine key a b (2 * b - a) _ ha hb hc hz (by intro h; linarith) (by intro h; linarith)
      (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) (by intro h; linarith) ?_
    refine diff_bound _ _ _ _ [0, (b - a) / 2, (a - b) / 2, b - a, a - b, 3 * (b - a) / 2,
      3 * (a - b) / 2, 2 * (b - a), 2 * (a - b)] (by simp) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro u (rfl | rfl | rfl | rfl) v (rfl | rfl | rfl | rfl) <;> first
      | (left; ring1)
      | (right; left; ring1)
      | (right; right; left; ring1)
      | (right; right; right; left; ring1)
      | (right; right; right; right; left; ring1)
      | (right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; right; ring1)

end E757H1Aux

open E757H1Aux

theorem OMA.solution : OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1.H1 := by
  unfold OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1.H1
  classical
  intro A hA E
  -- a four-point subset of A with at most ten differences is impossible
  have key : ∀ w x y z : ℝ, w ∈ A → x ∈ A → y ∈ A → z ∈ A →
      w ≠ x → w ≠ y → w ≠ z → x ≠ y → x ≠ z → y ≠ z →
      (({w, x, y, z} : Set ℝ) - {w, x, y, z}).ncard ≤ 10 → False := by
    intro w x y z hw hx hy hz h1 h2 h3 h4 h5 h6 hle
    have hsub : ({w, x, y, z} : Set ℝ) ⊆ (A : Set ℝ) := by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl <;> simpa
    have := hA _ hsub (ncard_four h1 h2 h3 h4 h5 h6)
    omega
  have memE : ∀ e, e ∈ E → e ⊆ A ∧ ∃ a b c : ℝ, a < b ∧ b < c ∧ a + c = 2 * b ∧ e = {a, b, c} := by
    intro e he
    have := Finset.mem_filter.1 he
    exact ⟨Finset.mem_powerset.1 this.1, this.2⟩
  refine ⟨?_, ?_⟩
  · intro e he f hf hne
    obtain ⟨heA, a, b, c, hab, hbc, habc, rfl⟩ := memE e he
    obtain ⟨hfA, d, g, h, hdg, hgh, hdgh, rfl⟩ := memE f hf
    have haA : a ∈ A := heA (by simp)
    have hbA : b ∈ A := heA (by simp)
    have hcA : c ∈ A := heA (by simp)
    have hdA : d ∈ A := hfA (by simp)
    have hgA : g ∈ A := hfA (by simp)
    have hhA : h ∈ A := hfA (by simp)
    by_contra hcard
    push_neg at hcard
    obtain rfl : c = 2 * b - a := by linarith
    obtain rfl : h = 2 * g - d := by linarith
    have haA : a ∈ A := heA (by simp)
    have hbA : b ∈ A := heA (by simp)
    have hcA : 2 * b - a ∈ A := heA (by simp)
    have hdA : d ∈ A := hfA (by simp)
    have hgA : g ∈ A := hfA (by simp)
    have hhA : 2 * g - d ∈ A := hfA (by simp)
    have small : ∀ y ∈ ({a, b, 2 * b - a} : Finset ℝ) ∩ {d, g, 2 * g - d},
        (y = a ∨ y = b ∨ y = 2 * b - a) ∧ (y = d ∨ y = g ∨ y = 2 * g - d) := by
      intro y hy
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hy
      exact hy
    by_cases hd : d = a ∨ d = b ∨ d = 2 * b - a <;> by_cases hg : g = a ∨ g = b ∨ g = 2 * b - a <;>
      by_cases hh : 2 * g - d = a ∨ 2 * g - d = b ∨ 2 * g - d = 2 * b - a
    · -- all three inside: f = e
      rcases hd with hd | hd | hd <;> rcases hg with hg | hg | hg <;>
        rcases hh with hh | hh | hh <;> subst d <;> subst g <;> first | linarith | exact hne rfl
    · -- d, g inside
      rcases hd with hd | hd | hd <;> rcases hg with hg | hg | hg <;> subst d <;> subst g <;>
        first
        | linarith
        | exact hh (Or.inr (Or.inr rfl))
        | (apply shape A key a b _ hab haA hbA hcA hhA; first
        | (left; linarith)
        | (right; left; linarith)
        | (right; right; left; linarith)
        | (right; right; right; left; linarith)
        | (right; right; right; right; left; linarith)
        | (right; right; right; right; right; linarith))
    · -- d, h inside
      rcases hd with hd | hd | hd <;> rcases hh with hh' | hh' | hh' <;> subst d <;>
        first
        | linarith
        | exact hg (Or.inl (by linarith))
        | exact hg (Or.inr (Or.inl (by linarith)))
        | exact hg (Or.inr (Or.inr (by linarith)))
        | (apply shape A key a b g hab haA hbA hcA hgA; first
        | (left; linarith)
        | (right; left; linarith)
        | (right; right; left; linarith)
        | (right; right; right; left; linarith)
        | (right; right; right; right; left; linarith)
        | (right; right; right; right; right; linarith))
    · -- only d inside
      apply absurd hcard
      rw [not_lt]
      apply Finset.card_le_one.2
      intro y hy y' hy'
      obtain ⟨h1, h2⟩ := small y hy
      obtain ⟨h1', h2'⟩ := small y' hy'
      rcases h2 with rfl | rfl | rfl <;> rcases h2' with rfl | rfl | rfl <;>
        first | rfl | exact absurd h1 hg | exact absurd h1 hh | exact absurd h1' hg | exact absurd h1' hh
    · -- g, h inside
      rcases hg with hg | hg | hg <;> rcases hh with hh' | hh' | hh' <;> subst g <;>
        first
        | linarith
        | exact hd (Or.inl (by linarith))
        | exact hd (Or.inr (Or.inl (by linarith)))
        | exact hd (Or.inr (Or.inr (by linarith)))
        | (apply shape A key a b d hab haA hbA hcA hdA; first
        | (left; linarith)
        | (right; left; linarith)
        | (right; right; left; linarith)
        | (right; right; right; left; linarith)
        | (right; right; right; right; left; linarith)
        | (right; right; right; right; right; linarith))
    · -- only g inside
      apply absurd hcard
      rw [not_lt]
      apply Finset.card_le_one.2
      intro y hy y' hy'
      obtain ⟨h1, h2⟩ := small y hy
      obtain ⟨h1', h2'⟩ := small y' hy'
      rcases h2 with rfl | rfl | rfl <;> rcases h2' with rfl | rfl | rfl <;>
        first | rfl | exact absurd h1 hd | exact absurd h1 hh | exact absurd h1' hd | exact absurd h1' hh
    · -- only h inside
      apply absurd hcard
      rw [not_lt]
      apply Finset.card_le_one.2
      intro y hy y' hy'
      obtain ⟨h1, h2⟩ := small y hy
      obtain ⟨h1', h2'⟩ := small y' hy'
      rcases h2 with rfl | rfl | rfl <;> rcases h2' with rfl | rfl | rfl <;>
        first | rfl | exact absurd h1 hd | exact absurd h1 hg | exact absurd h1' hd | exact absurd h1' hg
    · -- none inside
      apply absurd hcard
      rw [not_lt]
      apply Finset.card_le_one.2
      intro y hy y' hy'
      obtain ⟨h1, h2⟩ := small y hy
      rcases h2 with rfl | rfl | rfl
      · exact absurd h1 hd
      · exact absurd h1 hg
      · exact absurd h1 hh
  · intro a b c d t hab hbc hdb hbt habc hdbt hE1 hE2
    obtain ⟨hA1, -⟩ := memE _ hE1
    obtain ⟨hA2, -⟩ := memE _ hE2
    by_contra had
    have haA : a ∈ A := hA1 (by simp)
    have hcA : c ∈ A := hA1 (by simp)
    have hdA : d ∈ A := hA2 (by simp)
    have htA : t ∈ A := hA2 (by simp)
    obtain rfl : c = 2 * b - a := by linarith
    obtain rfl : t = 2 * b - d := by linarith
    apply key a (2 * b - a) d (2 * b - d) haA hcA hdA htA (by linarith) had (by linarith)
      (by linarith) (by intro h; apply had; linarith) (by linarith)
    apply diff_bound a (2 * b - a) d (2 * b - d)
      [0, b - a + (b - a), a - b + (a - b), d - a, a - d, b - d + (b - a), a - b + (d - b),
        b - d + (b - d), d - b + (d - b)] (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro u (rfl | rfl | rfl | rfl) v (rfl | rfl | rfl | rfl) <;>
      first
      | (left; ring1)
      | (right; left; ring1)
      | (right; right; left; ring1)
      | (right; right; right; left; ring1)
      | (right; right; right; right; left; ring1)
      | (right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; left; ring1)
      | (right; right; right; right; right; right; right; right; ring1)
