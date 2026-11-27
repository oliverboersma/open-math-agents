import OMAReductions.R_IrvingLeather_irving_leather_growth_rate_R1
import Mathlib.Tactic

-- Step IrvingLeather.irving_leather_growth_rate.R1.H1: hypothesis H1 of reduction IrvingLeather.irving_leather_growth_rate.R1
-- Credit: @tatashbar
-- Supermultiplicativity: put two profiles side by side; every agent ranks the first block ahead of
-- the second block, so pairs of stable matchings give distinct stable matchings of the union.

open StableMarriage IrvingLeather

namespace ILGH1

/-- Conjugate a pair of block permutations into a permutation of `Fin (m + n)`. -/
def blockPerm {m n : ℕ} (s : Equiv.Perm (Fin m)) (t : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m + n)) :=
  (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).permCongr (Equiv.sumCongr s t)

lemma blockPerm_castAdd {m n : ℕ} (s : Equiv.Perm (Fin m)) (t : Equiv.Perm (Fin n))
    (a : Fin m) : blockPerm s t (Fin.castAdd n a) = Fin.castAdd n (s a) := by
  simp [blockPerm, Equiv.permCongr_apply]

lemma blockPerm_natAdd {m n : ℕ} (s : Equiv.Perm (Fin m)) (t : Equiv.Perm (Fin n))
    (b : Fin n) : blockPerm s t (Fin.natAdd m b) = Fin.natAdd m (t b) := by
  simp [blockPerm, Equiv.permCongr_apply]

lemma blockPerm_symm {m n : ℕ} (s : Equiv.Perm (Fin m)) (t : Equiv.Perm (Fin n)) :
    (blockPerm s t).symm = blockPerm s.symm t.symm := by
  refine Equiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).surjective x
  rcases y with a | b
  · simp only [finSumFinEquiv_apply_left]
    rw [Equiv.symm_apply_eq, blockPerm_castAdd, blockPerm_castAdd, Equiv.apply_symm_apply]
  · simp only [finSumFinEquiv_apply_right]
    rw [Equiv.symm_apply_eq, blockPerm_natAdd, blockPerm_natAdd, Equiv.apply_symm_apply]

lemma castAdd_lt_natAdd {m n : ℕ} (a : Fin m) (b : Fin n) :
    Fin.castAdd n a < Fin.natAdd m b := by
  rw [Fin.lt_iff_val_lt_val]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  omega

lemma castAdd_lt_castAdd {m n : ℕ} (a a' : Fin m) :
    Fin.castAdd n a < Fin.castAdd n a' ↔ a < a' := by
  simp only [Fin.lt_iff_val_lt_val, Fin.val_castAdd]

lemma natAdd_lt_natAdd {m n : ℕ} (b b' : Fin n) :
    Fin.natAdd m b < Fin.natAdd m b' ↔ b < b' := by
  simp only [Fin.lt_iff_val_lt_val, Fin.val_natAdd, Nat.add_lt_add_iff_left]

/-- Two instances side by side: each agent ranks the other block by a fixed order, and
the members of the first block are ranked ahead of the second block by everyone. -/
def combine {m n : ℕ} (p : Profile m) (q : Profile n) : Profile (m + n) where
  manRank i := Sum.elim (fun a => blockPerm (p.manRank a) 1) (fun b => blockPerm 1 (q.manRank b))
    ((finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm i)
  womanRank i := Sum.elim (fun a => blockPerm (p.womanRank a) 1)
    (fun b => blockPerm 1 (q.womanRank b))
    ((finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm i)

lemma combine_manRank_castAdd {m n : ℕ} (p : Profile m) (q : Profile n) (a : Fin m) :
    (combine p q).manRank (Fin.castAdd n a) = blockPerm (p.manRank a) 1 := by
  simp [combine]

lemma combine_manRank_natAdd {m n : ℕ} (p : Profile m) (q : Profile n) (b : Fin n) :
    (combine p q).manRank (Fin.natAdd m b) = blockPerm 1 (q.manRank b) := by
  simp [combine]

lemma combine_womanRank_castAdd {m n : ℕ} (p : Profile m) (q : Profile n) (a : Fin m) :
    (combine p q).womanRank (Fin.castAdd n a) = blockPerm (p.womanRank a) 1 := by
  simp [combine]

lemma combine_womanRank_natAdd {m n : ℕ} (p : Profile m) (q : Profile n) (b : Fin n) :
    (combine p q).womanRank (Fin.natAdd m b) = blockPerm 1 (q.womanRank b) := by
  simp [combine]

lemma combine_stable {m n : ℕ} {p : Profile m} {q : Profile n} {μ : Matching m}
    {ν : Matching n} (hμ : IsStable p μ) (hν : IsStable q ν) :
    IsStable (combine p q) (blockPerm μ ν) := by
  intro i j hij
  obtain ⟨hne, hm, hw⟩ := hij
  rw [blockPerm_symm] at hw
  obtain ⟨x, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).surjective i
  obtain ⟨y, rfl⟩ := (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).surjective j
  rcases x with a | a <;> rcases y with b | b <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at hne hm hw
  · rw [blockPerm_castAdd] at hne hm hw
    rw [combine_manRank_castAdd, blockPerm_castAdd, blockPerm_castAdd,
      castAdd_lt_castAdd] at hm
    rw [combine_womanRank_castAdd, blockPerm_castAdd, blockPerm_castAdd,
      castAdd_lt_castAdd] at hw
    exact hμ a b ⟨fun h => hne (by rw [h]), hm, hw⟩
  · rw [blockPerm_castAdd] at hm
    rw [combine_manRank_castAdd, blockPerm_natAdd, blockPerm_castAdd] at hm
    exact absurd hm (not_lt.2 (castAdd_lt_natAdd _ _).le)
  · rw [blockPerm_castAdd] at hw
    rw [combine_womanRank_castAdd, blockPerm_natAdd, blockPerm_castAdd] at hw
    exact absurd hw (not_lt.2 (castAdd_lt_natAdd _ _).le)
  · rw [blockPerm_natAdd] at hne hm hw
    rw [combine_manRank_natAdd, blockPerm_natAdd, blockPerm_natAdd,
      natAdd_lt_natAdd] at hm
    rw [combine_womanRank_natAdd, blockPerm_natAdd, blockPerm_natAdd,
      natAdd_lt_natAdd] at hw
    exact hν a b ⟨fun h => hne (by rw [h]), hm, hw⟩

lemma blockPerm_inj {m n : ℕ} {s s' : Equiv.Perm (Fin m)} {t t' : Equiv.Perm (Fin n)}
    (h : blockPerm s t = blockPerm s' t') : s = s' ∧ t = t' := by
  constructor
  · ext a
    have := congrArg (fun f : Equiv.Perm (Fin (m + n)) => f (Fin.castAdd n a)) h
    simp only [blockPerm_castAdd] at this
    exact congrArg Fin.val (Fin.castAdd_injective m n this)
  · ext b
    have := congrArg (fun f : Equiv.Perm (Fin (m + n)) => f (Fin.natAdd m b)) h
    simp only [blockPerm_natAdd] at this
    exact congrArg Fin.val (Fin.natAdd_injective _ _ this)

lemma card_le_combine {m n : ℕ} (p : Profile m) (q : Profile n) :
    numStableMatchings p * numStableMatchings q ≤ numStableMatchings (combine p q) := by
  classical
  unfold numStableMatchings
  rw [← Fintype.card_prod]
  refine Fintype.card_le_of_injective
    (fun x => ⟨blockPerm x.1.1 x.2.1, combine_stable x.1.2 x.2.2⟩) ?_
  rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ h
  have h' : blockPerm s t = blockPerm s' t' := congrArg Subtype.val h
  obtain ⟨rfl, rfl⟩ := blockPerm_inj h'
  rfl

theorem supermul : ∀ m n : ℕ,
    maxStableMatchings m * maxStableMatchings n ≤ maxStableMatchings (m + n) := by
  intro m n
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Profile m))
    Finset.univ_nonempty (fun p => numStableMatchings p)
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Profile n))
    Finset.univ_nonempty (fun p => numStableMatchings p)
  unfold maxStableMatchings
  rw [hp, hq]
  exact (card_le_combine p q).trans
    (Finset.le_sup (f := fun p => numStableMatchings p) (Finset.mem_univ (combine p q)))

end ILGH1

theorem OMA.solution : OMA.R_IrvingLeather_irving_leather_growth_rate_R1.H1 :=
  ILGH1.supermul
