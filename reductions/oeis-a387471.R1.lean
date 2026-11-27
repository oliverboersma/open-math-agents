import OMAStatements.S_oeis_a387471
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

-- Reduction oeis-a387471.R1 of A387471: a(n) = number of interior triple intersections for the equal-angle model with parameter m = 2*n-1.
-- Credit: @begcdn
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_oeis_a387471_R1

open OMA.S_oeis_a387471

-- Every nonmedian solution has its three angles on the 3-degree grid.
def H1 : Prop := ∀ n : ℕ, 1 ≤ n → ∀ t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1),
  ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 →
  ¬ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n) → (n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1))

theorem ray_bounds {m : ℕ} (i : Fin m) :
    0 < (((i.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1))) ∧ (((i.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1))) < Real.pi/3 := by
  have hi : (i.val : ℝ) < m := by exact_mod_cast i.isLt
  have hm : (0 : ℝ) < 3*((m : ℝ)+1) := by positivity
  constructor
  · positivity
  · apply (div_lt_iff₀ hm).mpr
    nlinarith [mul_pos (sub_pos.mpr hi) Real.pi_pos]

theorem ratio_injective {m : ℕ} (i j : Fin m)
    (h : ratio m i = ratio m j) : i = j := by
  have hi := ray_bounds i
  have hj := ray_bounds j
  let a := (((i.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1)))
  let b := (((j.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1)))
  change 0 < a ∧ a < Real.pi/3 at hi
  change 0 < b ∧ b < Real.pi/3 at hj
  have hpos (t : ℝ) (ht : 0 < t ∧ t < Real.pi/3) :
      0 < Real.sin (Real.pi/3-t) := Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.2])
        (by linarith [ht.1, Real.pi_pos])
  change Real.sin a / Real.sin (Real.pi/3-a) = Real.sin b / Real.sin (Real.pi/3-b) at h
  have he := (div_eq_div_iff (hpos a hi).ne' (hpos b hj).ne').mp h
  have hs : Real.sin (Real.pi/3) * Real.sin (a-b) = 0 := by
    simp only [Real.sin_sub] at he ⊢
    linear_combination he
  have hzero := (mul_eq_zero.mp hs).resolve_left (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos] :
    0 < Real.pi/3) (by linarith [Real.pi_pos])).ne'
  have hab : a-b = 0 := Real.strictMonoOn_sin.injOn
    ⟨by linarith [hi.1,hj.2,Real.pi_pos], by linarith [hi.2,hj.1,Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ (by simpa using hzero)
  have ht : a=b := sub_eq_zero.mp hab
  change ((i.val : ℝ)+1)*Real.pi / _ = ((j.val : ℝ)+1)*Real.pi / _ at ht
  have hd : (3*((m : ℝ)+1)) ≠ 0 := by positivity
  have hnum := (div_left_inj' hd).mp ht
  apply Fin.ext
  have hval : (i.val : ℝ) = j.val := by linarith [(mul_left_inj' Real.pi_ne_zero).mp hnum]
  exact_mod_cast hval

theorem reflect_ray {m : ℕ} (i : Fin m) :
    (((i.rev.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1))) = Real.pi/3 - (((i.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1))) := by
  have hsum : i.rev.val + i.val + 1 = m := by rw [Fin.val_rev]; omega
  have hs : (i.rev.val : ℝ) + i.val + 1 = m := by exact_mod_cast hsum
  rw [eq_sub_iff_add_eq, ← add_div]
  apply (div_eq_iff (by positivity : (3*((m : ℝ)+1)) ≠ 0)).mpr
  linear_combination Real.pi * hs

theorem ratio_pos {m : ℕ} (i : Fin m) : 0 < ratio m i := by
  have h := ray_bounds i
  change 0 < Real.sin ((((i.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1)))) / Real.sin (Real.pi/3-(((i.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1))))
  apply div_pos <;> apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [h.1,h.2,Real.pi_pos]

theorem reflect_ratio {m : ℕ} (i : Fin m) :
    ratio m i.rev = (ratio m i)⁻¹ := by
  change Real.sin ((((i.rev.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1)))) / Real.sin (Real.pi/3-(((i.rev.val : ℝ)+1)*Real.pi/(3*((m : ℝ)+1)))) = _
  rw [reflect_ray, sub_sub_cancel]
  exact (inv_div _ _).symm

theorem pair_iff {m : ℕ} (i j : Fin m) :
    ratio m i * ratio m j = 1 ↔ j = i.rev := by
  constructor
  · intro h
    apply ratio_injective
    rw [reflect_ratio]
    exact eq_inv_of_mul_eq_one_right h
  · rintro rfl
    rw [reflect_ratio, mul_inv_cancel₀ (ratio_pos i).ne']

theorem median_count (n : ℕ) (hn : 1 ≤ n) :
    Set.ncard {t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1) |
      ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧
      (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)} = 6*n-5 := by
  let m := 2*n-1
  let c : Fin m := ⟨n-1, by dsimp [m]; omega⟩
  have hidx (i : Fin m) : i.val + 1 = n ↔ i = c := by
    change _ ↔ i = ⟨n-1, _⟩
    rw [Fin.ext_iff]
    dsimp
    omega
  have hrev : c.rev = c := by
    apply Fin.ext
    simp only [Fin.val_rev]
    dsimp [c,m]
    omega
  have hcenter : ratio m c = 1 := by
    have hp := (pair_iff c c).mpr hrev.symm
    nlinarith [ratio_pos c]
  let S : Set (Fin m) := Set.univ \ {c}
  let f (i : Fin m) := (c, i, i.rev)
  let g (i : Fin m) := (i, c, i.rev)
  let h (i : Fin m) := (i, i.rev, c)
  have hnot (i : Fin m) : i ∈ S ↔ i ≠ c := by simp [S]
  have hr (i : Fin m) : i.rev = c ↔ i = c := by
    constructor
    · intro hi
      simpa [hrev] using congrArg Fin.rev hi
    · rintro rfl
      exact hrev
  have heq : {t : Fin m × Fin m × Fin m |
      ratio m t.1 * ratio m t.2.1 * ratio m t.2.2 = 1 ∧
      (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)} =
      (f '' Set.univ ∪ g '' S) ∪ h '' S := by
    ext ⟨i,j,k⟩
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image, Set.mem_univ,
      true_and, hidx, hnot, f, g, h, Prod.mk.injEq]
    constructor
    · rintro ⟨ht, hm⟩
      by_cases hi : i=c
      · subst i
        left; left
        exact ⟨j,rfl,rfl,((pair_iff j k).mp (by simpa [hcenter] using ht)).symm⟩
      by_cases hj : j=c
      · subst j
        left; right
        exact ⟨i,hi,rfl,rfl,((pair_iff i k).mp (by simpa [hcenter] using ht)).symm⟩
      have hk : k=c := by tauto
      subst k
      exact Or.inr ⟨i,hi,rfl,((pair_iff i j).mp (by simpa [hcenter] using ht)).symm,rfl⟩
    · rintro ((⟨u,rfl,rfl,rfl⟩ | ⟨u,_,rfl,rfl,rfl⟩) | ⟨u,_,rfl,rfl,rfl⟩)
      all_goals constructor
      all_goals first | simpa only [hcenter, one_mul, mul_one] using (pair_iff u u.rev).mpr rfl | tauto
  have dfg : Disjoint (f '' Set.univ) (g '' S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i,_,rfl⟩ ⟨j,hj,e⟩
    exact (hnot j).mp hj (congrArg Prod.fst e)
  have dfh : Disjoint (f '' Set.univ) (h '' S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i,_,rfl⟩ ⟨j,hj,e⟩
    exact (hnot j).mp hj (congrArg Prod.fst e)
  have dgh : Disjoint (g '' S) (h '' S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i,_,rfl⟩ ⟨j,hj,e⟩
    exact (hnot j).mp hj ((hr j).mp (congrArg (fun t => t.2.1) e))
  have hf : Function.Injective f := fun _ _ e => congrArg (fun t => t.2.1) e
  have hg : Function.Injective g := fun _ _ e => congrArg Prod.fst e
  have hh : Function.Injective h := fun _ _ e => congrArg Prod.fst e
  have du : Disjoint (f '' Set.univ ∪ g '' S) (h '' S) := disjoint_sup_left.mpr ⟨dfh,dgh⟩
  rw [heq, Set.ncard_union_eq du, Set.ncard_union_eq dfg,
      Set.ncard_image_of_injective _ hf, Set.ncard_image_of_injective _ hg,
      Set.ncard_image_of_injective _ hh]
  simp [S,m]
  omega

-- Count the exceptional solutions on the fixed grid.
def H2 : Prop := ∀ n : ℕ, 1 ≤ n →
  Set.ncard {t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1) |
    ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧ ¬ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n) ∧
    (n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1))} = if 5 ∣ n then 12 else 0

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a387471.main := by
  intro hgrid hex n hn
  let A : Set (Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1)) :=
    {t | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)}
  let B : Set (Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1)) :=
    {t | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1 ∧ ¬ (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n) ∧ (n ∣ 10*(t.1.val+1) ∧ n ∣ 10*(t.2.1.val+1) ∧ n ∣ 10*(t.2.2.val+1))}
  have hab : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro t ht hs
    exact hs.2.1 ht.2
  have heq : {t : Fin (2*n-1) × Fin (2*n-1) × Fin (2*n-1) | ratio (2*n-1) t.1 * ratio (2*n-1) t.2.1 * ratio (2*n-1) t.2.2 = 1} = A ∪ B := by
    ext t
    constructor
    · intro ht
      by_cases hm : (t.1.val+1 = n ∨ t.2.1.val+1 = n ∨ t.2.2.val+1 = n)
      · exact Or.inl ⟨ht, hm⟩
      · exact Or.inr ⟨ht, hm, hgrid n hn t ht hm⟩
    · rintro (ht | ht)
      · exact ht.1
      · exact ht.1
  unfold d
  rw [heq, Set.ncard_union_eq hab]
  have ha : A.ncard = 6*n-5 := median_count n hn
  have hb : B.ncard = if 5 ∣ n then 12 else 0 := hex n hn
  rw [ha, hb]
  split <;> omega

end OMA.R_oeis_a387471_R1
