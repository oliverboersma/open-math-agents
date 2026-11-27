import FormalConjectures.ErdosProblems.«732»

-- Credit: @connoranderson

/-!
A coefficient test for a prescribed block-size list. Attach a variable to each
vertex pair and a size variable to each block size. For each eligible vertex
subset multiply by one plus its monomial. The coefficient with every pair
variable to the first power and the requested size histogram counts the
designs on the labeled ground set. The test uses integer polynomial arithmetic.
-/

namespace BlockCriterion

abbrev Exp (n : ℕ) := (Finset (Fin n) → ℕ) × Multiset ℕ

def term {n : ℕ} (T : Finset (Fin n)) : Exp n :=
  (fun e => if e.card = 2 ∧ e ⊆ T then 1 else 0, {T.card})

def index (n : ℕ) (s : List ℕ) : Exp n :=
  (fun e => if e.card = 2 then 1 else 0, s)

def blocks (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun T => 2 ≤ T.card

noncomputable def polynomial (n : ℕ) : AddMonoidAlgebra ℕ (Exp n) :=
  ∏ T ∈ blocks n, (1 + AddMonoidAlgebra.single (term T) 1)

end BlockCriterion

noncomputable def OMA.answer (n : ℕ) (s : List ℕ) : Prop :=
  (s : Multiset ℕ).sort (· ≤ ·) = s ∧
    0 < (BlockCriterion.polynomial n).coeff (BlockCriterion.index n s)

namespace BlockCriterion

private theorem coeff_pos {n : ℕ} (i : Exp n) :
    0 < (polynomial n).coeff i ↔ ∃ H ⊆ blocks n, ∑ T ∈ H, term T = i := by
  classical
  unfold polynomial
  rw [Finset.prod_one_add]
  simp only [AddMonoidAlgebra.prod_single, Finset.prod_const_one, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  have pos_indicator (q : Prop) [Decidable q] : 0 < (if q then 1 else 0 : ℕ) ↔ q := by
    by_cases h : q <;> simp [h]
  simp only [Finset.mem_powerset, pos_indicator]

private lemma sizes {n : ℕ} (H : Finset (Finset (Fin n))) :
    (∑ T ∈ H, term T).2 = H.val.map Finset.card := by
  classical
  induction H using Finset.induction_on with
  | empty => simp
  | @insert a H ha ih =>
    rw [Finset.sum_insert ha, Prod.snd_add, ih, Finset.insert_val_of_notMem ha]
    simp [term]

private lemma counts {n : ℕ} (H : Finset (Finset (Fin n))) (e : Finset (Fin n)) :
    (∑ T ∈ H, term T).1 e =
       if e.card = 2 then (H.filter fun T => e ⊆ T).card else 0 := by
  classical
  induction H using Finset.induction_on with
  | empty => simp
  | @insert a H ha ih =>
    rw [Finset.sum_insert ha, Prod.fst_add, Pi.add_apply, ih]
    by_cases he : e.card = 2 <;> by_cases hsub : e ⊆ a <;>
      simp [term, he, hsub, Finset.filter_insert, ha, Nat.add_comm]

theorem iff_test (n : ℕ) (s : List ℕ) :
    s ∈ Hypergraph.blockSizeProfiles n ↔ OMA.answer n s := by
  classical
  unfold OMA.answer
  rw [coeff_pos]
  constructor
  · intro h
    obtain ⟨H,hH,rfl⟩ := Finset.mem_image.mp h
    have hd : H.IsPairwiseBalancedDesign := (Finset.mem_filter.mp hH).2
    constructor
    · unfold Finset.blockSizeProfile
      rw [Multiset.sort_eq]
    · refine ⟨H,fun T hT => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd.1 T hT⟩,?_⟩
      apply Prod.ext
      · funext e
        rw [counts]
        by_cases he : e.card = 2
        · have hc : (H.filter fun T => e ⊆ T).card = 1 :=
            Finset.card_eq_one_iff_existsUnique.mpr (by simpa using hd.2 e he)
          simp [index,he,hc]
        · simp [index,he]
      · rw [sizes]
        exact (Multiset.sort_eq _ _).symm
  · rintro ⟨hs,H,hH,hv⟩
    apply Finset.mem_image.mpr
    refine ⟨H,Finset.mem_filter.mpr ⟨by simp,?_⟩,?_⟩
    · constructor
      · intro T hT
        exact (Finset.mem_filter.mp (hH hT)).2
      · intro e he
        have h := congrArg (fun z : Exp n => z.1 e) hv
        change (∑ T ∈ H, term T).1 e = _ at h
        rw [counts] at h
        have hc : (H.filter fun T => e ⊆ T).card = 1 := by simpa [he,index] using h
        simpa using Finset.card_eq_one_iff_existsUnique.mp hc
    · have hsize := congrArg Prod.snd hv
      change (∑ T ∈ H, term T).2 = (s : Multiset ℕ) at hsize
      rw [sizes] at hsize
      simpa only [Finset.blockSizeProfile,hsize] using hs

end BlockCriterion

theorem OMA.solution : Erdos732.erdos_732.parts.i.answer = OMA.answer → type_of% @Erdos732.erdos_732.parts.i := by
  intro h
  rw [h]
  exact BlockCriterion.iff_test
