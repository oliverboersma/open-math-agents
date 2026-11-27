import OMAReductions.R_Green3_green_3_R1_H2_R1

/-!
# Green's product problem on a geometric grid

For the cells [q^(j+1), q^j], products correspond to addition of
exponents.  The finite counterpart of the three-prefix inequality in
Franchi, Gowers and Yip, "Product-free subsets of (0,1)", Lemma 2.1
(arXiv:2607.06073), suffices. The proof only needs its strict version at
thresholds u+a at which both outer windows are about to gain one point.
The matching argument for the generating polynomial is discrete.
Original Lean formalization by @Deldor14.
-/

namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1

open MeasureTheory Finset

private lemma low_prefix (T : Finset ℕ) (a : ℕ) (ha : a ∈ T) (hmin : ∀ i ∈ T, a ≤ i)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (n : ℕ) (hn : n ≤ 2*a) :
    (T.filter (· < n-a)).card + (T.filter (· < n)).card + (T.filter (· < n+a)).card ≤ n := by
  classical
  have he : T.filter (· < n-a) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨hi,hil⟩ := mem_filter.mp hi
    have hai := hmin i hi
    omega
  rw [he,card_empty,zero_add]
  let L := (T.filter (· < n)).image (· + a)
  let R := T.filter (· < n+a)
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro i hi hr
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hi
    have h := hsep z (mem_filter.mp hz).1 a ha (z+a) (mem_filter.mp hr).1
    omega
  have hsub : L ∪ R ⊆ Ico a (n+a) := by
    intro i hi
    rcases mem_union.mp hi with hl | hr
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hl
      have hzn := (mem_filter.mp hz).2
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    · obtain ⟨hi,hin⟩ := mem_filter.mp hr
      exact mem_Ico.mpr ⟨hmin i hi,hin⟩
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis,Nat.card_Ico] at hc
  simpa [L,R,card_image_of_injective _ (add_left_injective a)] using hc

private lemma high_prefix (T : Finset ℕ) (a n : ℕ) (hn : 3*T.card ≤ n) :
    (T.filter (· < n-a)).card + (T.filter (· < n)).card + (T.filter (· < n+a)).card ≤ n := by
  have h (m : ℕ) := Finset.card_filter_le T (· < m)
  have h₁ := h (n-a)
  have h₂ := h n
  have h₃ := h (n+a)
  omega

private lemma count_next (T : Finset ℕ) (m : ℕ) :
    (T.filter (· < m+1)).card = (T.filter (· < m)).card + if m ∈ T then 1 else 0 := by
  by_cases h : m ∈ T
  · have he : T.filter (· < m+1) = insert m (T.filter (· < m)) := by
      ext i
      simp only [mem_filter,mem_insert]
      constructor
      · rintro ⟨hi,hlt⟩
        by_cases h' : i=m
        · exact Or.inl h'
        · exact Or.inr ⟨hi,by omega⟩
      · rintro (rfl | ⟨hi,hle⟩)
        · exact ⟨h,by omega⟩
        · exact ⟨hi,by omega⟩
    rw [he]
    simp [h]
  · have he : T.filter (· < m+1) = T.filter (· < m) := by
      ext i
      simp only [mem_filter]
      constructor
      · rintro ⟨hi,hle⟩
        have hne : i ≠ m := by rintro rfl; exact h hi
        exact ⟨hi,by omega⟩
      · rintro ⟨hi,hle⟩
        exact ⟨hi,by omega⟩
    rw [he]
    simp [h]

private lemma cumulative_of_double_hits (T : Finset ℕ) (a : ℕ) (ha : a ∈ T)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    (low : ∀ n ≤ 2*a, (T.filter (· < n-a)).card + (T.filter (· < n)).card +
      (T.filter (· < n+a)).card ≤ n)
    (high : ∀ n, 3*T.card ≤ n → (T.filter (· < n-a)).card + (T.filter (· < n)).card +
      (T.filter (· < n+a)).card ≤ n)
    (core : ∀ u ∈ T, u+2*a ∈ T → u+a+1 < 3*T.card →
      (T.filter (· < u)).card + (T.filter (· < u+a)).card + (T.filter (· < u+2*a)).card < u+a)
    (n : ℕ) :
    (T.filter (· < n-a)).card + (T.filter (· < n)).card + (T.filter (· < n+a)).card ≤ n := by
  induction n with
  | zero => exact low 0 (Nat.zero_le _)
  | succ n ih =>
    by_cases hlow : n+1 ≤ 2*a
    · exact low _ hlow
    by_cases hhigh : 3*T.card ≤ n+1
    · exact high _ hhigh
    have hma : a ≤ n := by omega
    obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hma
    have hf {z : ℕ} (hz : z ∈ T) : z+a ∉ T := by
      intro h
      have hh := hsep z hz a ha (z+a) h
      omega
    have e₁ : a+u+1-a = u+1 := by omega
    have e₂ : a+u+1 = (u+a)+1 := by omega
    have e₃ : a+u+1+a = (u+2*a)+1 := by omega
    have e₄ : a+u-a = u := by omega
    have e₅ : a+u = u+a := by omega
    have e₆ : a+u+a = u+2*a := by omega
    change (T.filter (· < a+u+1-a)).card + (T.filter (· < a+u+1)).card +
      (T.filter (· < a+u+1+a)).card ≤ a+u+1
    rw [e₁,e₃,e₂,count_next,count_next,count_next]
    rw [e₄,e₆,e₅] at ih
    by_cases hm : u+a ∈ T
    · have hl : u ∉ T := fun h => hf h hm
      have hr : u+2*a ∉ T := by simpa [two_mul,add_assoc] using hf hm
      simp only [hm,hl,hr,if_true,if_false] 
      omega
    · by_cases hl : u ∈ T
      · by_cases hr : u+2*a ∈ T
        · have hsave := core u hl hr (by omega)
          simp only [hm,hl,hr,if_true,if_false]
          omega
        · simp only [hm,hl,hr,if_true,if_false]
          omega
      · simp only [hm,hl,if_false]
        split <;> omega

/-- A geometric mesh extracts a finite set of sum-free closed exponent intervals. -/
def H1 : Prop := ∀ U : Set ℝ, IsOpen U → U ⊆ Set.Icc 0 1 → 1/3 < volume U →
    (∀ x ∈ U, ∀ y ∈ U, x*y ∉ U) →
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ T : Finset ℕ, T.Nonempty ∧
      (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) ∧
      1/3 < (1-q)*(∑ i ∈ T, q^i)

/-- At a simultaneous hit in the outer two windows there is one spare position.
This discrete statement follows mathematically from Lemma 2.1 of Franchi,
Gowers and Yip, applied to the union of the closed intervals [j,j+1]. -/
def H2 : Prop := ∀ (T : Finset ℕ) (a : ℕ), a ∈ T → (∀ i ∈ T, a ≤ i) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    ∀ u ∈ T, u+2*a ∈ T → u+a+1 < 3*T.card →
      (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

/-- A bound on three shifted prefix counts bounds the generating polynomial. -/
def H3 : Prop := ∀ (T : Finset ℕ) (a : ℕ), (∀ i ∈ T, a ≤ i) →
    (∀ n : ℕ, (T.filter (· < n-a)).card + (T.filter (· < n)).card +
      (T.filter (· < n+a)).card ≤ n) →
    ∀ q : ℝ, 0 < q → q < 1 → (1-q)*(∑ i ∈ T, q^i) ≤ 1/3

theorem main : H1 → H2 → H3 → OMA.R_Green3_green_3_R1_H2_R1.H2 := by
  classical
  intro geometric critical weights k m M S _hpos htop _hmin _hmax bounds _hcase hdense
  have hg : type_of% @Green3.green_3 := by
    intro U hU hu hvol
    by_contra h
    have habsent : ∀ x ∈ U, ∀ y ∈ U, x*y ∉ U :=
      fun x hx y hy hxy => h ⟨x,y,x*y,hx,hy,hxy,rfl⟩
    obtain ⟨q,hq,hq1,T,hT,hsep,hbig⟩ := geometric U hU hu hvol habsent
    let a := T.min' hT
    have ha : a ∈ T := T.min'_mem hT
    have hmin (i : ℕ) (hi : i ∈ T) : a ≤ i := T.min'_le i hi
    have hcum := cumulative_of_double_hits T a ha hsep (low_prefix T a ha hmin hsep)
      (high_prefix T a) (critical T a ha hmin hsep)
    exact (not_lt_of_ge (weights T a hmin hcum q hq hq1)) hbig
  exact OMA.R_Green3_green_3_R1.finite_of_green hg k S
    (fun i hi => mem_range.mpr ((bounds i hi).2.trans_le htop)) hdense

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1
