import OMAStatements.S_mo_506603
import Mathlib

/-!
# The complementary-minor criterion

Lchencz's problem and Will Sawin's sufficient rank condition appear in
MathOverflow 506603. We prove necessity as well by the two-set case of
Edmonds' matroid partition theorem (1965). The intermediate two-choice
independent representative theorem is a special case of Rado (1942).
The Lean proofs below use finite-dimensional linear algebra over a field.

Rado: https://doi.org/10.1093/qmath/os-13.1.83
Edmonds: https://doi.org/10.6028/jres.069b.004
Question and comment: https://mathoverflow.net/q/506603
-/

namespace TwoChoice

open Module Submodule
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable abbrev dim (X : Submodule K V) := finrank K X

def Hall (F : ι → Submodule K V) : Prop := ∀ J : Finset ι, J.card ≤ dim (J.sup F)

lemma tight_inter [DecidableEq ι] {F : ι → Submodule K V} (hF : Hall F) {T U : Finset ι}
    (ht : dim (T.sup F) = T.card) (hu : dim (U.sup F) = U.card) :
    dim ((T ∩ U).sup F) = (T ∩ U).card := by
  have hle : (T ∩ U).sup F ≤ T.sup F ⊓ U.sup F :=
    le_inf (Finset.sup_mono Finset.inter_subset_left) (Finset.sup_mono Finset.inter_subset_right)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (T.sup F) (U.sup F)
  simp only [dim] at ht hu
  rw [ht, hu, ← Finset.sup_union] at h
  have hle' := Submodule.finrank_mono hle
  have htu := hF (T ∪ U)
  have hi := hF (T ∩ U)
  have hcard := Finset.card_union_add_card_inter T U
  simp only [dim] at *
  omega

omit [FiniteDimensional K V] in
lemma sup_update_away [DecidableEq ι] (F : ι → Submodule K V) (i : ι) (a : Submodule K V)
    {J : Finset ι} (h : i ∉ J) : J.sup (Function.update F i a) = J.sup F := by
  apply Finset.sup_congr rfl
  intro j hj
  have hji : j ≠ i := fun hji => h (hji ▸ hj)
  simp [Function.update_of_ne hji]

omit [FiniteDimensional K V] in
lemma sup_update_at [DecidableEq ι] (F : ι → Submodule K V) (i : ι) (a : Submodule K V)
    {J : Finset ι} (h : i ∈ J) : J.sup (Function.update F i a) = a ⊔ (J.erase i).sup F := by
  conv_lhs => rw [← Finset.insert_erase h]
  rw [Finset.sup_insert, Function.update_self, sup_update_away F i a (Finset.notMem_erase _ _)]

omit [FiniteDimensional K V] in
lemma sup_at [DecidableEq ι] (F : ι → Submodule K V) (i : ι) {J : Finset ι} (h : i ∈ J) :
    J.sup F = F i ⊔ (J.erase i).sup F := by
  conv_lhs => rw [← Finset.insert_erase h]
  exact Finset.sup_insert

lemma bad_witness [DecidableEq ι] {F : ι → Submodule K V} (hF : Hall F) (i : ι)
    (a b : Submodule K V) (hs : F i = a ⊔ b) (hb : finrank K b ≤ 1)
    (hbad : ¬ Hall (Function.update F i a)) :
    ∃ T : Finset ι, i ∈ T ∧ dim (T.sup F) = T.card ∧
       ¬ b ≤ T.sup (Function.update F i a) := by
  unfold Hall at hbad
  push Not at hbad
  obtain ⟨T, hT⟩ := hbad
  have hfull := hF T
  have hi : i ∈ T := by
    by_contra h
    rw [sup_update_away F i a h] at hT
    omega
  let X := T.sup (Function.update F i a)
  have he : T.sup F = X ⊔ b := by
    rw [sup_at F i hi, hs]
    dsimp [X]
    rw [sup_update_at F i a hi]
    ac_rfl
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq X b
  change finrank K X < T.card at hT
  refine ⟨T, hi, ?_, ?_⟩
  · rw [he] at hfull ⊢
    simp only [dim] at *
    omega
  · intro hle
    have : X ⊔ b = X := sup_eq_left.mpr hle
    rw [he, this] at hfull
    exact (not_lt_of_ge hfull) hT

lemma choose_one [DecidableEq ι] {F : ι → Submodule K V} (hF : Hall F) (i : ι)
    (a b : Submodule K V) (hs : F i = a ⊔ b) (ha : finrank K a ≤ 1) (hb : finrank K b ≤ 1) :
    Hall (Function.update F i a) ∨ Hall (Function.update F i b) := by
  by_contra! h
  obtain ⟨T, hTi, ht, hbt⟩ := bad_witness hF i a b hs hb h.1
  obtain ⟨U, hUi, hu, hau⟩ := bad_witness hF i b a (hs.trans (sup_comm ..)) ha h.2
  let W := T ∩ U
  have hi : i ∈ W := Finset.mem_inter.mpr ⟨hTi, hUi⟩
  have hWt : W ⊆ T := Finset.inter_subset_left
  have hWu : W ⊆ U := Finset.inter_subset_right
  let Y := (W.erase i).sup F
  have hnotb : ¬ b ≤ a ⊔ Y := by
    have h := Finset.sup_mono (f := Function.update F i a) hWt
    rw [sup_update_at F i a hi] at h
    exact fun hle => hbt (hle.trans h)
  have hnota : ¬ a ≤ Y := by
    have h := Finset.sup_mono (f := Function.update F i b) hWu
    rw [sup_update_at F i b hi] at h
    exact fun hle => hau (hle.trans (le_sup_right.trans h))
  have hlt1 : Y < a ⊔ Y := lt_of_le_not_ge le_sup_right (fun hg => hnota (le_sup_left.trans hg))
  have hlt2 : a ⊔ Y < (a ⊔ Y) ⊔ b :=
    lt_of_le_not_ge le_sup_left (fun hg => hnotb (le_sup_right.trans hg))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt1
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt2
  have h3 := tight_inter hF ht hu
  change dim (W.sup F) = W.card at h3
  have he : W.sup F = (a ⊔ Y) ⊔ b := by rw [sup_at F i hi, hs]; dsimp [Y]; ac_rfl
  rw [he] at h3
  have h4 : (W.erase i).card ≤ finrank K Y := hF _
  have hcard := Finset.card_erase_add_one hi
  simp only [dim] at h3
  omega

omit [FiniteDimensional K V] in
lemma sup_lines (f : ι → V) (J : Finset ι) :
    J.sup (fun i => K ∙ f i) = span K (f '' (J : Set ι)) := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | insert a J ha ih => simp [Finset.sup_insert, ih, Set.image_insert_eq, span_insert]

omit [FiniteDimensional K V] in
lemma line_dim_le (v : V) : finrank K (K ∙ v) ≤ 1 := by
  classical
  exact finrank_span_le_card ({v} : Set V)

/-- The linear marriage theorem with two available vectors for each index. -/
theorem representatives [Fintype ι] (u v : ι → V)
    (h : Hall (fun i => (K ∙ u i) ⊔ (K ∙ v i))) :
    ∃ f : ι → V, (∀ i, f i = u i ∨ f i = v i) ∧ LinearIndependent K f := by
  classical
  let F (J : Finset ι) (w : ι → V) (i : ι) : Submodule K V :=
    if i ∈ J then K ∙ w i else (K ∙ u i) ⊔ (K ∙ v i)
  have aux (J : Finset ι) : ∃ w : ι → V,
      (∀ i ∈ J, w i = u i ∨ w i = v i) ∧ Hall (F J w) := by
    induction J using Finset.induction_on with
    | empty => exact ⟨u, by simp, by simpa [F] using h⟩
    | insert i J hi ih =>
      obtain ⟨w, hw, hF⟩ := ih
      have hs : F J w i = (K ∙ u i) ⊔ (K ∙ v i) := by simp [F, hi]
      have ho := choose_one hF i _ _ hs (line_dim_le (K := K) _) (line_dim_le (K := K) _)
      obtain ⟨z, hz, hsel⟩ : ∃ z : V, (z = u i ∨ z = v i) ∧ Hall (Function.update (F J w) i (K ∙ z)) := by
        rcases ho with h1 | h2
        · exact ⟨u i, Or.inl rfl, h1⟩
        · exact ⟨v i, Or.inr rfl, h2⟩
      refine ⟨Function.update w i z, ?_, ?_⟩
      · intro j hj
        by_cases he : j = i
        · subst j
          simpa using hz
        · simpa [Function.update_of_ne he] using hw j ((Finset.mem_insert.mp hj).resolve_left he)
      · convert hsel using 1
        funext j
        by_cases he : j = i
        · subst j
          simp [F]
        · simp [F, he]
  obtain ⟨w, hw, hF⟩ := aux Finset.univ
  refine ⟨w, fun i => hw i (Finset.mem_univ _), linearIndependent_iff_card_le_finrank_span.mpr ?_⟩
  have hc := hF Finset.univ
  have hfun : F Finset.univ w = fun i => K ∙ w i := by funext i; simp [F]
  rw [hfun, sup_lines] at hc
  rw [Finset.coe_univ, Set.image_univ] at hc
  exact hc

end TwoChoice

namespace TwoChoice

open Module Submodule

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
private def prodSelfEquiv (p : Submodule K V) : p.prod p ≃ₗ[K] (p × p) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun x := ⟨(x.1.1,x.2.1), x.1.2, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A family of vectors partitions into two independent families under the doubled dimension test. -/
theorem independent_partition [Fintype ι] [DecidableEq ι] (v : ι → V)
    (h : ∀ J : Finset ι, J.card ≤ 2 * finrank K (span K (v '' (J : Set ι)))) :
    ∃ T : Finset ι, LinearIndependent K (fun i : T => v i) ∧
      LinearIndependent K (fun i : ↥(Tᶜ) => v i) := by
  classical
  let l := LinearMap.inl K V V
  let r := LinearMap.inr K V V
  let u := l ∘ v
  let w := r ∘ v
  have hh : Hall (fun i => (K ∙ u i) ⊔ (K ∙ w i)) := by
    intro J
    let Y := span K (v '' (J : Set ι))
    have he : J.sup (fun i => (K ∙ u i) ⊔ (K ∙ w i)) = Y.prod Y := by
      change J.sup ((fun i => K ∙ u i) ⊔ (fun i => K ∙ w i)) = _
      rw [Finset.sup_sup, sup_lines, sup_lines, ← span_union]
      simpa only [u, w, l, r, Set.image_comp, Y] using
        (LinearMap.span_inl_union_inr (R := K) (s := v '' (J : Set ι)) (t := v '' (J : Set ι)))
    rw [he]
    have hf := (prodSelfEquiv Y).finrank_eq
    rw [Module.finrank_prod] at hf
    change J.card ≤ finrank K (Y.prod Y)
    rw [hf, ← two_mul]
    exact h J
  obtain ⟨f, hsel, hf⟩ := representatives u w hh
  let T := Finset.univ.filter (fun i => f i = u i)
  refine ⟨T, ?_, ?_⟩
  · apply LinearIndependent.of_comp l
    have he : l ∘ (fun i : T => v i) = fun i : T => f i := by
      funext i
      exact (Finset.mem_filter.mp i.2).2.symm
    rw [he]
    exact hf.comp _ Subtype.val_injective
  · apply LinearIndependent.of_comp r
    have he : r ∘ (fun i : ↥(Tᶜ) => v i) = fun i : ↥(Tᶜ) => f i := by
      funext i
      have ht : (i : ι) ∉ T := Finset.mem_compl.mp i.2
      have hne : f i ≠ u i := fun he => ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      exact ((hsel i).resolve_left hne).symm
    rw [he]
    exact hf.comp _ Subtype.val_injective

end TwoChoice

namespace TwoChoice

open Module Submodule

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A partition into two independent families gives the doubled dimension
bound on every subset of the column labels. -/
theorem counting_of_independent_partition [Fintype ι] [DecidableEq ι] (v : ι → V) (T : Finset ι)
    (hT : LinearIndependent K (fun i : T => v i))
    (hC : LinearIndependent K (fun i : ↥(Tᶜ) => v i)) (J : Finset ι) :
    J.card ≤ 2 * finrank K (span K (v '' (J : Set ι))) := by
  classical
  have bound {P D : Finset ι} (hP : LinearIndependent K (fun i : P => v i))
      (hDP : D ⊆ P) (hDJ : D ⊆ J) : D.card ≤ finrank K (span K (v '' (J : Set ι))) := by
    let f : ↥D → ↥P := fun i => ⟨i.val, hDP i.property⟩
    have inj : Function.Injective f := by
      intro i j h
      exact Subtype.ext (congrArg (fun x : P => (x : ι)) h)
    have hD : LinearIndependent K (fun i : D => v i) := hP.comp f inj
    have hdim : finrank K (span K (v '' (D : Set ι))) = D.card := by
      rw [Set.image_eq_range]
      exact (finrank_span_eq_card hD).trans (Fintype.card_coe D)
    rw [← hdim]
    exact Submodule.finrank_mono (span_mono (Set.image_mono hDJ))
  have hl := bound (D := J ∩ T) hT Finset.inter_subset_right Finset.inter_subset_left
  have hr := bound (D := J \ T) hC
    (fun i hi => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2) Finset.sdiff_subset
  have hc := Finset.card_inter_add_card_sdiff J T
  omega

end TwoChoice

namespace TwoChoice

open Module Submodule

theorem independent_partition_iff {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] (v : ι → V) :
    (∃ T : Finset ι, LinearIndependent K (fun i : T => v i) ∧
      LinearIndependent K (fun i : ↥(Tᶜ) => v i)) ↔
      ∀ J : Finset ι, J.card ≤ 2 * finrank K (span K (v '' (J : Set ι))) := by
  constructor
  · rintro ⟨T, hT, hC⟩
    exact counting_of_independent_partition v T hT hC
  · exact independent_partition v

end TwoChoice

namespace ComplementaryMinors

open OMA.S_mo_506603 Module Submodule

variable {K : Type*} [Field K] {n : ℕ}

/-- The columns of the augmented matrix [I | A], with the two sets of labels disjoint. -/
noncomputable def augCol (A : Matrix (Fin n) (Fin n) K) :
    Fin n ⊕ Fin n → Fin n → K := Sum.elim (fun i => Pi.single i 1) A.col

noncomputable def augRank (A : Matrix (Fin n) (Fin n) K) (S : Finset (Fin n ⊕ Fin n)) : ℕ :=
  finrank K (span K (augCol A '' (S : Set _)))

theorem independent_iff (A : Matrix (Fin n) (Fin n) K) (S : Finset (Fin n ⊕ Fin n)) :
    LinearIndependent K (fun i : S => augCol A i) ↔ S.card = augRank A S := by
  rw [linearIndependent_iff_card_eq_finrank_span, augRank, Set.image_eq_range, Fintype.card_coe]
  rfl

theorem augRank_eq (A : Matrix (Fin n) (Fin n) K) (S : Finset (Fin n ⊕ Fin n)) :
    augRank A S = S.toLeft.card + submatrixRank A S.toLeftᶜ S.toRight := by
  classical
  let V := span K (augCol A '' (S : Set _))
  let p := LinearMap.funLeft K K (Subtype.val : ↥(S.toLeftᶜ) → Fin n)
  have pk : p.ker ≤ V := by
    intro v hv
    have hv0 : p v = 0 := hv
    rw [pi_eq_sum_univ' v]
    apply V.sum_mem
    intro i _
    by_cases hi : i ∈ S.toLeft
    · apply V.smul_mem
      exact subset_span ⟨Sum.inl i, Finset.mem_toLeft.mp hi, rfl⟩
    · have vi : v i = 0 :=
        congrFun hv0 ⟨i, Finset.mem_compl.mpr hi⟩
      simp [vi]
  have ps : Function.Surjective p :=
    LinearMap.funLeft_surjective_of_injective K K _ Subtype.val_injective
  have pkdim : finrank K p.ker = S.toLeft.card := by
    have h := p.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr ps, finrank_top, finrank_pi, finrank_pi,
      Fintype.card_coe, Fintype.card_fin] at h
    have hc := Finset.card_compl_add_card S.toLeft
    simp only [Fintype.card_fin] at hc
    omega
  let B := A.submatrix (fun i : ↥(S.toLeftᶜ) => (i : Fin n))
      (fun j : S.toRight => (j : Fin n))
  have mapped : V.map p = span K (Set.range B.col) := by
    dsimp only [V]
    rw [Submodule.map_span, Set.image_image]
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨i | j, h, rfl⟩
      · have h0 : p (augCol A (.inl i)) = 0 := by
          ext k
          have hi := Finset.mem_toLeft.mpr h
          have hne : (k:Fin n) ≠ i := fun eq => Finset.mem_compl.mp k.property (eq ▸ hi)
          simp [p, augCol, hne]
        simp [h0]
      · exact subset_span ⟨⟨j, Finset.mem_toRight.mpr h⟩, rfl⟩
    · apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨Sum.inr j.val, Finset.mem_toRight.mp j.property, rfl⟩
  have nd := (p.domRestrict V).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, mapped,
    (Submodule.comapSubtypeEquivOfLe pk).finrank_eq, pkdim, ← Matrix.rank_eq_finrank_span_cols] at nd
  exact nd.symm.trans (Nat.add_comm _ _)

end ComplementaryMinors

namespace ComplementaryClassification
open Finset OMA.S_mo_506603

private lemma left_compl {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : Finset (α ⊕ β)) :
    Sᶜ.toLeft = S.toLeftᶜ := by ext i; simp

private lemma right_compl {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (S : Finset (α ⊕ β)) :
    Sᶜ.toRight = S.toRightᶜ := by ext i; simp

private lemma card_compl_plus {n : ℕ} (R : Finset (Fin n)) :
    Rᶜ.card + R.card = n := by
  simp

private lemma rank_le_rows {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (R C : Finset (Fin n)) :
    submatrixRank A R C ≤ R.card := by
  simpa [submatrixRank] using (A.submatrix (fun i : R => (i : Fin n))
    (fun j : C => (j : Fin n))).rank_le_card_height

/-- A partition of the 2n columns into two independent families is the
same as two complementary nonsingular minors. -/
private theorem bases_iff {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (ρ : Finset (Fin n ⊕ Fin n) → ℕ)
    (hr : ∀ S, ρ S = S.toLeft.card + submatrixRank A S.toLeftᶜ S.toRight) :
    (∃ S, S.card = ρ S ∧ Sᶜ.card = ρ Sᶜ) ↔
    ∃ R C, R.card = C.card ∧ submatrixRank A R C = R.card ∧
      submatrixRank A Rᶜ Cᶜ = Rᶜ.card := by
  constructor
  · rintro ⟨S, hS, hcom⟩
    rw [hr] at hS
    rw [hr, left_compl, right_compl, compl_compl] at hcom
    have hsize := S.card_toLeft_add_card_toRight
    have hcsize := Sᶜ.card_toLeft_add_card_toRight
    rw [left_compl,right_compl] at hcsize
    have h1 := rank_le_rows A S.toLeftᶜ S.toRight
    have h2 := rank_le_rows A S.toLeft S.toRightᶜ
    have hl := card_compl_plus S.toLeft
    have hc := card_compl_plus S.toRight
    refine ⟨S.toLeftᶜ, S.toRight, by omega, by omega, ?_⟩
    rw [compl_compl]
    omega
  · rintro ⟨R, C, hRC, ha, hb⟩
    use Rᶜ.disjSum C
    have hcard := (Rᶜ.disjSum C)ᶜ.card_toLeft_add_card_toRight
    simp only [left_compl,right_compl,toLeft_disjSum,toRight_disjSum,compl_compl] at hcard
    have hl := card_compl_plus R
    have hc := card_compl_plus C
    simp only [hr,left_compl,right_compl,toLeft_disjSum,toRight_disjSum,compl_compl,card_disjSum]
    omega

theorem of_partition_criterion {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (ρ : Finset (Fin n ⊕ Fin n) → ℕ)
    (hr : ∀ S, ρ S = S.toLeft.card + submatrixRank A S.toLeftᶜ S.toRight)
    (hall : (∃ S, S.card = ρ S ∧ Sᶜ.card = ρ Sᶜ) ↔ ∀ S, S.card ≤ 2 * ρ S) :
    (∀ R C : Finset (Fin n), R.card = C.card →
      submatrixRank A R C < R.card ∨ submatrixRank A Rᶜ Cᶜ < Rᶜ.card) ↔
    ∃ R C : Finset (Fin n), n + 2 * submatrixRank A R C < R.card + C.card := by
  classical
  have noPair : (∀ R C : Finset (Fin n), R.card = C.card →
      submatrixRank A R C < R.card ∨ submatrixRank A Rᶜ Cᶜ < Rᶜ.card) ↔
      ¬ (∃ R C, R.card = C.card ∧ submatrixRank A R C = R.card ∧
        submatrixRank A Rᶜ Cᶜ = Rᶜ.card) := by
    constructor
    · rintro h ⟨R, C, he, ha, hb⟩
      rcases h R C he with h | h <;> omega
    · intro h R C he
      have h1 := rank_le_rows A R C
      have h2 := rank_le_rows A Rᶜ Cᶜ
      by_contra! hn
      exact h ⟨R,C,he,by omega,by omega⟩
  rw [noPair, ← bases_iff A ρ hr, hall, not_forall]
  constructor
  · rintro ⟨S, hs⟩
    have h := S.card_toLeft_add_card_toRight
    rw [hr] at hs
    have hc := card_compl_plus S.toLeft
    exact ⟨S.toLeftᶜ,S.toRight,by omega⟩
  · rintro ⟨R,C,h⟩
    refine ⟨Rᶜ.disjSum C, ?_⟩
    simp only [hr, card_disjSum, toLeft_disjSum, toRight_disjSum, compl_compl]
    have hc := card_compl_plus R
    omega

end ComplementaryClassification

open ComplementaryMinors in
theorem OMA.solution : type_of% @OMA.S_mo_506603.main := by
  intro K _ n A
  apply ComplementaryClassification.of_partition_criterion A (augRank A) (augRank_eq A)
  have h := TwoChoice.independent_partition_iff (K := K) (augCol A)
  simpa only [independent_iff, augRank] using h
