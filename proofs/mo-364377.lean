import OMAStatements.S_mo_364377
import Mathlib

/-!
# A counterexample to entrywise motion toward a nearest signed permutation

Use the normalized cyclic weighing matrix of order seven and weight four.
Up to transposition, its zero pattern and rigidity also appear in H. Tracy
Hall and Simone Severini, Locality for quantum systems on graphs depends on
the number field. Here a direct argument with three orthogonality equations
rules out the requested motion. In a column adjacent to a strictly improving
diagonal entry, one absolute value would have to be strictly smaller than the
next in a cycle of three, while the other two comparisons are non-strict.
-/

namespace MO364377Pattern
noncomputable def U (i j : Fin 7) : ℝ :=
  if i=j then -(1/2) else if j-i=1 ∨ j-i=2 ∨ j-i=4 then 1/2 else 0
end MO364377Pattern

namespace MO364377Pattern
theorem diagonal (i : Fin 7) : U i i = -(1/2) := by simp [U]

theorem bound (i j : Fin 7) : |U i j| ≤ 1/2 := by
  unfold U
  split
  · norm_num
  · split <;> norm_num

private def W (i j : Fin 7) : ℚ :=
  if i=j then -(1/2) else if j-i=1 ∨ j-i=2 ∨ j-i=4 then 1/2 else 0

private theorem cast_W (i j : Fin 7) : (W i j : ℝ) = U i j := by
  unfold W U
  split
  · norm_num
  · split <;> norm_num

private theorem gram_rat (i j : Fin 7) :
    ∑ k : Fin 7, W k i * W k j = (if i = j then 1 else 0) := by
  revert i j
  decide +kernel

theorem orthogonal : (Matrix.of U).transpose * Matrix.of U = 1 := by
  ext i j
  rw [Matrix.mul_apply,Matrix.one_apply]
  simp only [Matrix.transpose_apply,Matrix.of_apply,← cast_W]
  have h := congrArg (fun a : ℚ => (a : ℝ)) (gram_rat i j)
  push_cast at h
  split_ifs at h ⊢ <;> exact_mod_cast h
end MO364377Pattern

namespace MO364377Nearest

open OMA.S_mo_364377

theorem neg_one_signed (n : ℕ) : signedPermutation (-(1 : Mat n)) := by
  refine ⟨Equiv.refl _, fun _ => -1, fun _ => Or.inr rfl, ?_⟩
  intro i j
  by_cases h : j = i
  · subst j; simp
  · simp [h, Ne.symm h]

theorem neg_one_nearest {n : ℕ} (A : Mat n) (hb : ∀ i j, |A i j| ≤ 1/2)
    (hd : ∀ i, A i i = -1/2) (Q : Mat n) (hq : signedPermutation Q) :
    frobSq A (-1) ≤ frobSq A Q := by
  obtain ⟨σ, s, hs, he⟩ := hq
  unfold frobSq
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hleft : (A i j - (-(1 : Mat n)) i j)^2 = (A i j)^2 := by
    by_cases h : i = j
    · subst j; simp [hd]; norm_num
    · simp [h]
  rw [hleft, he]
  by_cases h : j = σ i
  · rw [if_pos h]
    obtain ⟨hl, hu⟩ := abs_le.mp (hb i j)
    rcases hs i with he | he <;> rw [he] <;> nlinarith
  · simp [h]
end MO364377Nearest

namespace MO364377Pairs
open OMA.S_mo_364377 MO364377Pattern

private abbrev hit (i j : Fin 7) : Prop := i = j ∨ j-i = 1 ∨ j-i = 2 ∨ j-i = 4

private theorem supported {i j : Fin 7} (h : ¬ hit i j) : U i j = 0 := by
  simp only [hit, not_or] at h
  simp [U, h.1, h.2.1, h.2.2.1, h.2.2.2]

private theorem reduce {B : Mat 7} (ho : orthogonal B) (hs : ∀ i j, U i j = 0 → B i j = 0)
    (p q j : Fin 7) (hpj : p ≠ j) (hpq : p ≠ q)
    (h : ∀ i, hit i p → hit i j → i = p ∨ i = q) :
    |B p p| * |B p j| = |B q p| * |B q j| := by
  have hj := congrArg (fun M : Mat 7 => M p j) ho
  change (∑ i, B i p * B i j) = (1 : Mat 7) p j at hj
  rw [Matrix.one_apply_ne hpj] at hj
  have hterms (i : Fin 7) : B i p * B i j =
      (if i = p then B p p * B p j else 0) + (if i = q then B q p * B q j else 0) := by
    by_cases hip : i=p
    · subst i; simp [hpq]
    by_cases hiq : i=q
    · subst i; simp [hip]
    simp only [if_neg hip, if_neg hiq, add_zero]
    by_cases hi : hit i p
    · have hn : ¬ hit i j := fun hj => (h i hi hj).elim hip hiq
      rw [hs i j (supported hn), mul_zero]
    · rw [hs i p (supported hi), zero_mul]
  rw [Finset.sum_congr rfl (fun i _ => hterms i)] at hj
  rw [Finset.sum_add_distrib] at hj
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hj
  have ha := congrArg abs (eq_neg_of_add_eq_zero_left hj)
  simpa [abs_mul] using ha

theorem pairs {B : Mat 7} (ho : orthogonal B) (hs : ∀ i j, U i j = 0 → B i j = 0) (j : Fin 7) :
    let a := j-1
    let b := j-2
    let c := j-4
    |B a a| * |B a j| = |B b a| * |B b j| ∧
    |B b b| * |B b j| = |B c b| * |B c j| ∧
    |B c c| * |B c j| = |B a c| * |B a j| := by
  dsimp only
  refine ⟨reduce ho hs _ _ _ ?_ ?_ ?_, reduce ho hs _ _ _ ?_ ?_ ?_, reduce ho hs _ _ _ ?_ ?_ ?_⟩
  all_goals revert j; decide

theorem incoming (j : Fin 7) :
    U (j-1) j = 1/2 ∧ U (j-2) j = 1/2 ∧ U (j-4) j = 1/2 := by
  have h (j : Fin 7) : j-1 ≠ j ∧ j-2 ≠ j ∧ j-4 ≠ j ∧
      j-(j-1) = 1 ∧ j-(j-2) = 2 ∧ j-(j-4) = 4 := by revert j; decide
  obtain ⟨h1,h2,h4,d1,d2,d4⟩ := h j
  simp [U,h1,h2,h4,d1,d2,d4]
end MO364377Pairs

namespace MO364377Cycle
open OMA.S_mo_364377 MO364377Pattern
private theorem cycle_bound {x y z a b c p q t : ℝ}
    (hx : 0 < x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 1/2 < a) (hb : 1/2 ≤ b) (hc : 1/2 ≤ c)
    (hp : p ≤ 1/2) (hq : q ≤ 1/2) (ht : t ≤ 1/2)
    (h1 : a*x=p*y) (h2 : b*y=q*z) (h3 : c*z=t*x) : False := by
  have hxy : (1/2)*x < (1/2)*y :=
    (mul_lt_mul_of_pos_right ha hx).trans_le (h1 ▸ mul_le_mul_of_nonneg_right hp hy)
  have hyz : (1/2)*y ≤ (1/2)*z :=
    (mul_le_mul_of_nonneg_right hb hy).trans (h2 ▸ mul_le_mul_of_nonneg_right hq hz)
  have hzx : (1/2)*z ≤ (1/2)*x :=
    (mul_le_mul_of_nonneg_right hc hz).trans (h3 ▸ mul_le_mul_of_nonneg_right ht hx.le)
  exact (hyz.trans hzx).not_gt hxy

private theorem square_entry_le (A B : Mat 7) (i j : Fin 7) :
    (A i j - B i j)^2 ≤ frobSq A B :=
  (Finset.single_le_sum (fun k _ => sq_nonneg (A i k-B i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (A k l-B k l))) (Finset.mem_univ i))

theorem rules_out_move
    (hA : orthogonal U) (hd : ∀ i, U i i = -(1/2:ℝ))
    (hb : ∀ i j, |U i j| ≤ 1/2)
    (hin : ∀ j : Fin 7, U (j-1) j = 1/2)
    (hpairs : ∀ B : Mat 7, orthogonal B → (∀ i j, U i j = 0 → B i j = 0) →
      ∀ j : Fin 7, let a:=j-1; let b:=j-2; let c:=j-4
      |B a a| * |B a j| = |B b a| * |B b j| ∧
      |B b b| * |B b j| = |B c b| * |B c j| ∧
      |B c c| * |B c j| = |B a c| * |B a j|) :
    ¬ (type_of% @OMA.S_mo_364377.main) := by
  have hns : ¬ signedPermutation U := by
    rintro ⟨σ,s,hs,he⟩
    have heq := he 0 0
    rw [hd] at heq
    split_ifs at heq
    · rcases hs 0 with h | h <;> rw [h] at heq <;> norm_num at heq
    · norm_num at heq
  have hmin := MO364377Nearest.neg_one_nearest U hb (by intro i; rw [hd]; norm_num)
  intro h
  obtain ⟨B,hB,hclose,hincr,⟨i,k,hik,hstrict⟩,hdecr⟩ :=
    h 7 U (-1) hA hns (MO364377Nearest.neg_one_signed 7) hmin (1/4) (by norm_num)
  have heq : k=i := by
    by_contra hne
    exact hik (by simp [Ne.symm hne])
  subst k
  rw [hd] at hstrict
  norm_num at hstrict
  have hdiag (u : Fin 7) : 1/2 ≤ |B u u| := by
    have h0 := hincr u u (by simp)
    rw [hd] at h0
    norm_num at h0
    exact h0
  have hoff (u v : Fin 7) (hne : u ≠ v) : |B u v| ≤ 1/2 :=
    (hdecr u v (by simp [hne])).trans (hb u v)
  have hs (u v : Fin 7) (hz : U u v=0) : B u v=0 := by
    have hne : u ≠ v := by rintro rfl; rw [hd] at hz; norm_num at hz
    have hh := hdecr u v (by simp [hne])
    simpa [hz] using hh
  let j := i+1
  have ha : j-1=i := by simp [j]
  have hpos : 0 < |B (j-1) j| := by
    apply abs_pos.mpr
    intro hzero
    have hh := (square_entry_le U B (j-1) j).trans_lt hclose
    rw [hin j,hzero] at hh
    norm_num at hh
  obtain ⟨h1,h2,h3⟩ := hpairs B hB hs j
  have hne : ∀ v : Fin 7, v-2 ≠ v-1 ∧ v-4 ≠ v-2 ∧ v-1 ≠ v-4 := by decide
  apply cycle_bound hpos (abs_nonneg _) (abs_nonneg _) (ha ▸ hstrict) (hdiag _) (hdiag _)
    (hoff _ _ (hne j).1) (hoff _ _ (hne j).2.1) (hoff _ _ (hne j).2.2) h1 h2 h3
end MO364377Cycle

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_364377.main) :=
  MO364377Cycle.rules_out_move MO364377Pattern.orthogonal
    MO364377Pattern.diagonal MO364377Pattern.bound (fun j => (MO364377Pairs.incoming j).1)
    (fun _ hB hs j => MO364377Pairs.pairs hB hs j)
