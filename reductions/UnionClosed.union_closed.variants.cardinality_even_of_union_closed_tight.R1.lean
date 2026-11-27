import FormalConjectures.Wikipedia.UnionClosed

-- Reduction UnionClosed.union_closed.variants.cardinality_even_of_union_closed_tight.R1 of Union-closed sets conjecture — cardinality even of union closed tight
-- Credit: @ivillar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Halving a tight union-closed family

Call a union-closed family `A` (with `A ≠ ∅` and `A ≠ {∅}`) *tight* when the largest number of
members containing a common element is exactly `|A| / 2`. The target says that then `|A| = 2 ^ k`.

Pick an element `i` lying in exactly half of the members and let `B` be the subfamily of members
avoiding `i`. Then `B` is union-closed and `|B| = |A| / 2`. The two hypotheses below say that `B`
is tight again (unless `B = {∅}`):

* the first is the bound of the union-closed sets conjecture for this particular family `B`:
  some element lies in at least half of the members of `B`;
* the second is a quarter bound: every element lies in at most half of the members of `B`, that
  is, in at most a quarter of the members of `A` once `i` is excluded.

Both hold for power sets and their blow-ups, with equality. An exhaustive enumeration of all
union-closed families on a ground set of at most `6` points (2 771 104 families on `5` points; on
`6` points a search with a sound pruning rule, cutting a branch only when some element lies in
more than half of the members of every completion) found exactly `202` and `876` tight families.
That is the number of blown-up power sets on `5` and on `6` points (one less than the Bell numbers
`203` and `877`), and those are all tight. So in this range the tight families are exactly the
blown-up power sets, and both hypotheses hold there.

Given both, a strong induction on `|A|` proved in this file gives `|A| = 2 * |B| = 2 ^ (k + 1)`;
the induction stops at `B = {∅}`, where `|A| = 2`. The hypotheses are stated for families of
finite sets of natural numbers; the file also proves that a tight family over an arbitrary type
can be relabelled into such a family without changing any of the numbers involved.
-/

namespace OMA.R_UnionClosed_union_closed_variants_cardinality_even_of_union_closed_tight_R1

/-- Frankl's bound for the half of a tight family that avoids a most frequent element. -/
def H1 : Prop :=
  ∀ (A : Finset (Finset ℕ)) (i : ℕ),
    A ≠ {∅} → A ≠ ∅ → (∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) →
    (∀ j : ℕ, 2 * (A.filter (fun X => j ∈ X)).card ≤ A.card) →
    2 * (A.filter (fun X => i ∈ X)).card = A.card →
    A.filter (fun X => i ∉ X) ≠ {∅} →
    ∃ j : ℕ, (A.filter (fun X => i ∉ X)).card ≤
      2 * ((A.filter (fun X => i ∉ X)).filter (fun X => j ∈ X)).card

/-- The quarter bound: in a tight family, among the members avoiding a most frequent element,
every element lies in at most half of them. -/
def H2 : Prop :=
  ∀ (A : Finset (Finset ℕ)) (i : ℕ),
    A ≠ {∅} → A ≠ ∅ → (∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) →
    (∀ j : ℕ, 2 * (A.filter (fun X => j ∈ X)).card ≤ A.card) →
    2 * (A.filter (fun X => i ∈ X)).card = A.card →
    ∀ j : ℕ, 2 * ((A.filter (fun X => i ∉ X)).filter (fun X => j ∈ X)).card ≤
      (A.filter (fun X => i ∉ X)).card

/-- The induction: a tight family of finite sets of naturals has `2 ^ k` members. -/
lemma core (h1 : H1) (h2 : H2) :
    ∀ N : ℕ, ∀ A : Finset (Finset ℕ), A.card = N → A ≠ {∅} → A ≠ ∅ →
      (∀ X ∈ A, ∀ Y ∈ A, X ∪ Y ∈ A) →
      (∀ j : ℕ, 2 * (A.filter (fun X => j ∈ X)).card ≤ A.card) →
      (∃ i : ℕ, 2 * (A.filter (fun X => i ∈ X)).card = A.card) →
      ∃ k : ℕ, A.card = 2 ^ k := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro A hN hne1 hne0 huc hle hex
    obtain ⟨i, hi⟩ := hex
    have hsplit : (A.filter (fun X => i ∈ X)).card + (A.filter (fun X => ¬ i ∈ X)).card = A.card :=
      Finset.card_filter_add_card_filter_not (fun X => i ∈ X)
    have hApos : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne0)
    have hBuc : ∀ X ∈ A.filter (fun X => i ∉ X), ∀ Y ∈ A.filter (fun X => i ∉ X),
        X ∪ Y ∈ A.filter (fun X => i ∉ X) := by
      intro X hX Y hY
      rw [Finset.mem_filter] at hX hY ⊢
      refine ⟨huc X hX.1 Y hY.1, ?_⟩
      rw [Finset.mem_union]
      exact fun h => h.elim hX.2 hY.2
    have hBle := h2 A i hne1 hne0 huc hle hi
    have hBfr := h1 A i hne1 hne0 huc hle hi
    generalize hB : A.filter (fun X => i ∉ X) = B at hsplit hBuc hBle hBfr
    have hBcard : 2 * B.card = A.card := by omega
    have hBne0 : B ≠ ∅ := by
      intro h
      rw [h, Finset.card_empty] at hBcard
      omega
    by_cases hB1 : B = {∅}
    · refine ⟨1, ?_⟩
      rw [hB1, Finset.card_singleton] at hBcard
      omega
    · obtain ⟨j, hj⟩ := hBfr hB1
      have hBlt : B.card < N := by omega
      obtain ⟨k, hk⟩ := ih B.card hBlt B rfl hB1 hBne0 hBuc hBle ⟨j, le_antisymm (hBle j) hj⟩
      refine ⟨k + 1, ?_⟩
      rw [← hBcard, hk, pow_succ]
      ring

theorem main : H1 → H2 → type_of% @UnionClosed.union_closed.variants.cardinality_even_of_union_closed_tight := by
  intro h1 h2 n _ A _ hne1 hne0 huc hgr
  classical
  -- the tightness hypothesis in natural-number form
  have hle : ∀ i : n, 2 * (A.filter (fun X => i ∈ X)).card ≤ A.card := by
    intro i
    have h := hgr.2 ⟨i, rfl⟩
    have h' : (2 * ((A.filter (fun X => i ∈ X)).card : ℚ)) ≤ (A.card : ℚ) := by linarith
    exact_mod_cast h'
  obtain ⟨i0, hi0⟩ := hgr.1
  have heq : 2 * (A.filter (fun X => i0 ∈ X)).card = A.card := by
    have h' : (2 * ((A.filter (fun X => i0 ∈ X)).card : ℚ)) = (A.card : ℚ) := by
      simp only at hi0
      linarith
    exact_mod_cast h'
  have hApos : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne0)
  -- relabel the ground set by natural numbers
  obtain ⟨U, hU⟩ : ∃ U : Finset n, U = A.biUnion id := ⟨_, rfl⟩
  have hsub : ∀ X ∈ A, X ⊆ U := by
    intro X hX
    rw [hU]
    exact Finset.subset_biUnion_of_mem id hX
  obtain ⟨g, hg⟩ : ∃ g : n → ℕ, g = fun x => U.toList.idxOf x := ⟨_, rfl⟩
  have ginj : ∀ x ∈ U, ∀ y ∈ U, g x = g y → x = y := by
    intro x hx y _ hxy
    rw [hg] at hxy
    exact (List.idxOf_inj (Finset.mem_toList.mpr hx)).mp hxy
  have memimg : ∀ X ∈ A, ∀ x ∈ U, (g x ∈ X.image g ↔ x ∈ X) := by
    intro X hX x hx
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h
      have : y = x := ginj y (hsub X hX hy) x hx hyx
      rw [← this]
      exact hy
    · exact Finset.mem_image_of_mem g
  have imginj : Set.InjOn (fun X : Finset n => X.image g) (A : Set (Finset n)) := by
    intro X hX Y hY hXY
    have hXY' : X.image g = Y.image g := hXY
    ext x
    constructor
    · intro hx
      have hxU := hsub X hX hx
      have : g x ∈ Y.image g := hXY' ▸ Finset.mem_image_of_mem g hx
      exact (memimg Y hY x hxU).mp this
    · intro hx
      have hxU := hsub Y hY hx
      have : g x ∈ X.image g := hXY' ▸ Finset.mem_image_of_mem g hx
      exact (memimg X hX x hxU).mp this
  obtain ⟨A', hA'⟩ : ∃ A' : Finset (Finset ℕ), A' = A.image (fun X => X.image g) := ⟨_, rfl⟩
  have cardA' : A'.card = A.card := by
    rw [hA']
    exact Finset.card_image_of_injOn imginj
  have freq : ∀ x ∈ U, (A'.filter (fun X' => g x ∈ X')).card = (A.filter (fun X => x ∈ X)).card := by
    intro x hx
    have h1' : A'.filter (fun X' => g x ∈ X') =
        (A.filter (fun X => x ∈ X)).image (fun X => X.image g) := by
      rw [hA']
      ext X'
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨X, hX, rfl⟩, hmem⟩
        exact ⟨X, ⟨hX, (memimg X hX x hx).mp hmem⟩, rfl⟩
      · rintro ⟨X, ⟨hX, hxX⟩, rfl⟩
        exact ⟨⟨X, hX, rfl⟩, Finset.mem_image_of_mem g hxX⟩
    rw [h1']
    apply Finset.card_image_of_injOn
    intro X hX Y hY hXY
    exact imginj (Finset.mem_filter.mp (Finset.mem_coe.mp hX)).1
      (Finset.mem_filter.mp (Finset.mem_coe.mp hY)).1 hXY
  have hle' : ∀ j : ℕ, 2 * (A'.filter (fun X' => j ∈ X')).card ≤ A'.card := by
    intro j
    by_cases hj : ∃ x ∈ U, g x = j
    · obtain ⟨x, hx, rfl⟩ := hj
      rw [freq x hx, cardA']
      exact hle x
    · have hempty : A'.filter (fun X' => j ∈ X') = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro X' hX' hjX'
        rw [hA'] at hX'
        obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hX'
        obtain ⟨y, hy, hyj⟩ := Finset.mem_image.mp hjX'
        exact hj ⟨y, hsub X hX hy, hyj⟩
      rw [hempty, Finset.card_empty]
      omega
  have hi0U : i0 ∈ U := by
    by_contra hnot
    have hempty : A.filter (fun X => i0 ∈ X) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro X hX hiX
      exact hnot (hsub X hX hiX)
    rw [hempty, Finset.card_empty] at heq
    omega
  have hex' : ∃ j : ℕ, 2 * (A'.filter (fun X' => j ∈ X')).card = A'.card :=
    ⟨g i0, by rw [freq i0 hi0U, cardA']; exact heq⟩
  have hne0' : A' ≠ ∅ := by
    intro h
    rw [h, Finset.card_empty] at cardA'
    omega
  have hne1' : A' ≠ {∅} := by
    intro h
    apply hne1
    obtain ⟨X0, hX0⟩ := Finset.nonempty_iff_ne_empty.mpr hne0
    have hall : ∀ X ∈ A, X = ∅ := by
      intro X hX
      have hXi : X.image g ∈ A' := by
        rw [hA']
        exact Finset.mem_image_of_mem _ hX
      rw [h, Finset.mem_singleton] at hXi
      exact Finset.image_eq_empty.mp hXi
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨hall X0 hX0 ▸ hX0, hall⟩
  have huc' : ∀ X ∈ A', ∀ Y ∈ A', X ∪ Y ∈ A' := by
    intro X' hX' Y' hY'
    rw [hA'] at hX' hY' ⊢
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hX'
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hY'
    rw [← Finset.image_union]
    exact Finset.mem_image_of_mem _ (huc X hX Y hY)
  obtain ⟨k, hk⟩ := core h1 h2 A'.card A' rfl hne1' hne0' huc' hle' hex'
  exact ⟨k, by rw [← cardA', hk]⟩

end OMA.R_UnionClosed_union_closed_variants_cardinality_even_of_union_closed_tight_R1
