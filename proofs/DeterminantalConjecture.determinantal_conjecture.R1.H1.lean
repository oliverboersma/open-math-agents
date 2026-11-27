import OMAReductions.R_DeterminantalConjecture_determinantal_conjecture_R1

private theorem h1_fiber_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (v : ι → κ) (F : κ → ℝ) (w : ι → ℝ) :
    (∑ i, w i * F (v i)) = ∑ j, (∑ i, if v i = j then w i else 0) * F j := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Within each unordered image fiber, orient the pair to maximize the score on the second row. -/
private theorem h1_orientation {n : Type} [Fintype n] [DecidableEq n]
    (w : Equiv.Perm n → ℝ) (h1 : (∑ σ, w σ) = 1) (r s : n) (f : n → ℝ)
    (hm : ∀ J : Finset n,
      0 ≤ ∑ σ : Equiv.Perm n, if ({r,s} : Finset n).image σ = J then w σ else 0) :
    ∃ t : Equiv.Perm n → ℝ, (∀ σ, 0 ≤ t σ) ∧ (∑ σ, t σ) = 1 ∧
      (∀ J : Finset n, (∑ σ : Equiv.Perm n, if ({r,s} : Finset n).image σ = J then t σ else 0) =
          ∑ σ : Equiv.Perm n, if ({r,s} : Finset n).image σ = J then w σ else 0) ∧
      (∑ σ : Equiv.Perm n, t σ * f (σ s)) =
        ∑ σ : Equiv.Perm n, w σ * max (f (σ r)) (f (σ s)) := by
  classical
  let v (σ : Equiv.Perm n) := ({r,s} : Finset n).image σ
  let opt (σ : Equiv.Perm n) := if f (σ r) ≤ f (σ s) then σ else σ * Equiv.swap r s
  have hv_opt (σ : Equiv.Perm n) : v (opt σ) = v σ := by
    by_cases h : f (σ r) ≤ f (σ s)
    · simp [opt, h]
    · simp [opt, h, v, Equiv.Perm.mul_apply, Finset.pair_comm]
  have hf_opt (σ : Equiv.Perm n) : f (opt σ s) = max (f (σ r)) (f (σ s)) := by
    by_cases h : f (σ r) ≤ f (σ s)
    · simp [opt, h]
    · simp [opt, h, Equiv.Perm.mul_apply, max_eq_left (le_of_not_ge h)]
  have hle (σ : Equiv.Perm n) {i : n} (hi : i ∈ v σ) :
      f i ≤ max (f (σ r)) (f (σ s)) := by
    simp only [v, Finset.image_insert, Finset.image_singleton, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hmax {σ τ : Equiv.Perm n} (heq : v σ = v τ) :
      max (f (σ r)) (f (σ s)) = max (f (τ r)) (f (τ s)) := by
    apply le_antisymm
    · apply max_le
      · exact hle τ (heq ▸ (by simp [v] : σ r ∈ v σ))
      · exact hle τ (heq ▸ (by simp [v] : σ s ∈ v σ))
    · apply max_le
      · exact hle σ (heq.symm ▸ (by simp [v] : τ r ∈ v τ))
      · exact hle σ (heq.symm ▸ (by simp [v] : τ s ∈ v τ))
  let pick (J : Finset n) : Equiv.Perm n :=
    if h : ∃ σ, v σ = J then opt (Classical.choose h) else 1
  have hv_pick {J : Finset n} (h : ∃ σ, v σ = J) : v (pick J) = J := by
    rw [show pick J = opt (Classical.choose h) from dif_pos h, hv_opt]
    exact Classical.choose_spec h
  have hf_pick (σ : Equiv.Perm n) :
      f (pick (v σ) s) = max (f (σ r)) (f (σ s)) := by
    have h : ∃ τ, v τ = v σ := ⟨σ, rfl⟩
    rw [show pick (v σ) = opt (Classical.choose h) from dif_pos h, hf_opt]
    exact hmax (Classical.choose_spec h)
  let m (J : Finset n) := ∑ σ : Equiv.Perm n, if v σ = J then w σ else 0
  have hm_zero {J : Finset n} (h : ¬ ∃ σ, v σ = J) : m J = 0 := by
    simp [m, show ∀ σ, ¬ v σ = J from fun σ hv => h ⟨σ, hv⟩]
  let t (σ : Equiv.Perm n) := ∑ J : Finset n, if pick J = σ then m J else 0
  have hpush (g : Equiv.Perm n → ℝ) :
      (∑ σ, t σ * g σ) = ∑ J : Finset n, m J * g (pick J) := by
    exact (h1_fiber_sum pick g m).symm
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · intro σ
    exact Finset.sum_nonneg fun J _ => by
      split
      · exact hm J
      · exact le_rfl
  · have ht := hpush (fun _ => 1)
    have hw := h1_fiber_sum v (fun _ => 1) w
    simp only [mul_one] at ht hw
    exact ht.trans (hw.symm.trans h1)
  · intro J
    change (∑ σ, if v σ = J then t σ else 0) = m J
    have ht := hpush (fun σ => if v σ = J then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at ht
    rw [ht]
    calc
      (∑ K : Finset n, if v (pick K) = J then m K else 0) =
          ∑ K : Finset n, if K = J then m K else 0 := by
        apply Finset.sum_congr rfl
        intro K _
        by_cases h : ∃ σ, v σ = K
        · rw [hv_pick h]
        · simp [hm_zero h]
      _ = m J := by simp
  · rw [hpush]
    have hw := h1_fiber_sum v (fun J => f (pick J s)) w
    simpa only [hf_pick] using hw.symm

private theorem h1_image_mass_nonneg {n : Type} [Fintype n] [DecidableEq n]
    (w : Equiv.Perm n → ℝ)
    (hw : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    (I J : Finset n) :
    0 ≤ ∑ σ : Equiv.Perm n, if I.image σ = J then w σ else 0 := by
  classical
  by_cases hcard : I.card = J.card
  · refine (hw I J).trans_eq ?_
    refine Finset.sum_congr rfl ?_
    intro σ _
    have himage : (∀ i ∈ I, σ i ∈ J) ↔ I.image σ = J := by
      constructor
      · intro h
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
          exact h i hi
        · rw [Finset.card_image_of_injective I σ.injective, hcard]
      · intro h i hi
        rw [← h]
        exact Finset.mem_image_of_mem σ hi
    simp [himage, mul_ite]
  · have hne (σ : Equiv.Perm n) : I.image σ ≠ J := by
      intro h
      apply hcard
      rw [← h, Finset.card_image_of_injective I σ.injective]
    simp [hne]

private theorem h1_nonneg_by_fiber {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (w : α → ℝ) (p : α → β) (f : β → ℝ)
    (hw : ∀ j, 0 ≤ ∑ i, if p i = j then w i else 0) (hf : ∀ i, 0 ≤ f (p i)) :
    0 ≤ ∑ i, w i * f (p i) := by
  classical
  rw [h1_fiber_sum p f w]
  refine Finset.sum_nonneg ?_
  intro j _
  by_cases hex : ∃ i, p i = j
  · obtain ⟨i, rfl⟩ := hex
    exact mul_nonneg (hw (p i)) (hf i)
  · have hne (i : α) : p i ≠ j := fun he => hex ⟨i, he⟩
    simp [hne]

/-- Partition a directed cut by the preimage of its column set. -/
private theorem h1_cut_nonneg {n : Type} [Fintype n] [DecidableEq n]
    (w : Equiv.Perm n → ℝ)
    (hw : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    (r s : n) (J : Finset n) :
    0 ≤ ∑ σ : Equiv.Perm n, if σ r ∈ J ∧ σ s ∉ J then w σ else 0 := by
  classical
  have hmem (σ : Equiv.Perm n) (i : n) : i ∈ J.image σ.symm ↔ σ i ∈ J := by
    constructor
    · intro hi
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
      have heq : j = σ i := by simpa using congrArg σ hji
      simpa [← heq] using hj
    · intro hi
      exact Finset.mem_image.mpr ⟨σ i, hi, σ.symm_apply_apply i⟩
  have hinv (σ : Equiv.Perm n) (I : Finset n) : J.image σ.symm = I ↔ I.image σ = J := by
    constructor
    · intro h
      rw [← h, Finset.image_image]
      simp [Function.comp_def]
    · intro h
      rw [← h, Finset.image_image]
      simp [Function.comp_def]
  have hpreimage (I : Finset n) :
      0 ≤ ∑ σ : Equiv.Perm n, if J.image σ.symm = I then w σ else 0 := by
    simpa [hinv] using h1_image_mass_nonneg w hw I J
  have hpos := h1_nonneg_by_fiber w (fun σ => J.image σ.symm)
    (fun I => if r ∈ I ∧ s ∉ I then (1 : ℝ) else 0) hpreimage
    (fun σ => by split <;> norm_num)
  simpa [hmem, mul_ite] using hpos

open scoped BigOperators

private lemma h1_pospart_nonneg {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (x y : α → β)
    (hcut : ∀ K : Finset β, 0 ≤ ∑ i : α, if x i ∈ K ∧ y i ∉ K then w i else 0)
    (f : β → ℝ) :
    0 ≤ ∑ i : α, w i * max 0 (f (x i) - f (y i)) := by
  classical
  have aux (V : Finset ℝ) : ∀ g : β → ℝ, (∀ b, g b ∈ V) →
      0 ≤ ∑ i : α, w i * max 0 (g (x i) - g (y i)) := by
    refine Finset.eraseInduction (p := fun V => ∀ g : β → ℝ, (∀ b, g b ∈ V) →
      0 ≤ ∑ i : α, w i * max 0 (g (x i) - g (y i))) ?_ V
    intro V ih g hg
    by_cases hV : V.Nonempty
    · let m := V.max' hV
      have hm : m ∈ V := V.max'_mem hV
      by_cases hE : (V.erase m).Nonempty
      · let m' := (V.erase m).max' hE
        have hm' : m' ∈ V.erase m := (V.erase m).max'_mem hE
        have hm'm : m' ≤ m := V.le_max' _ (Finset.mem_of_mem_erase hm')
        have hle (b : β) (hb : g b ≠ m) : g b ≤ m' :=
          (V.erase m).le_max' _ (Finset.mem_erase.mpr ⟨hb, hg b⟩)
        let lower (b : β) : ℝ := if g b = m then m' else g b
        have hlower (b : β) : lower b ∈ V.erase m := by
          by_cases hb : g b = m
          · simpa [lower, hb] using hm'
          · simpa [lower, hb] using Finset.mem_erase.mpr ⟨hb, hg b⟩
        have hind := ih m hm lower hlower
        let K := Finset.univ.filter fun b : β => g b = m
        have term (i : α) :
            max 0 (g (x i) - g (y i)) =
              max 0 (lower (x i) - lower (y i)) +
              (if x i ∈ K ∧ y i ∉ K then m - m' else 0) := by
          by_cases hx : g (x i) = m <;> by_cases hy : g (y i) = m
          · simp [lower, K, hx, hy]
          · have h : g (y i) ≤ m' := hle _ hy
            rw [hx]
            simp [lower, K, hx, hy, max_eq_right (sub_nonneg.mpr h),
              max_eq_right (sub_nonneg.mpr (h.trans hm'm))]
          · have h : g (x i) ≤ m' := hle _ hx
            rw [hy]
            simp [lower, K, hx, hy, max_eq_left (sub_nonpos.mpr h),
              max_eq_left (sub_nonpos.mpr (h.trans hm'm))]
          · simp [lower, K, hx, hy]
        have hsum :
            (∑ i : α, w i * max 0 (g (x i) - g (y i))) =
              (∑ i : α, w i * max 0 (lower (x i) - lower (y i))) +
                (m - m') * ∑ i : α, if x i ∈ K ∧ y i ∉ K then w i else 0 := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [term i]
          split_ifs <;> ring
        rw [hsum]
        exact add_nonneg hind (mul_nonneg (sub_nonneg.mpr hm'm) (hcut K))
      · have hconst (b : β) : g b = m := by
          by_contra hne
          exact hE ⟨g b, Finset.mem_erase.mpr ⟨hne, hg b⟩⟩
        simp [hconst]
    · have hzero : (∑ i : α, w i * max 0 (g (x i) - g (y i))) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact (hV ⟨g (x i), hg (x i)⟩).elim
      simp [hzero]
  let V := Finset.univ.image f
  exact aux V f fun b => Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩

private lemma h1_signed_max {n : Type*} [Fintype n] [DecidableEq n]
    (w : Equiv.Perm n → ℝ) (r s : n)
    (hw : ∀ J : Finset n,
      0 ≤ ∑ σ : Equiv.Perm n, if σ r ∈ J ∧ σ s ∉ J then w σ else 0)
    (f : n → ℝ) :
    (∑ σ : Equiv.Perm n, w σ * f (σ s)) ≤
      ∑ σ : Equiv.Perm n, w σ * max (f (σ r)) (f (σ s)) := by
  apply sub_nonneg.mp
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  have hmax (σ : Equiv.Perm n) :
      max (f (σ r)) (f (σ s)) - f (σ s) = max 0 (f (σ r) - f (σ s)) := by
    by_cases h : f (σ r) ≤ f (σ s)
    · rw [max_eq_right h, max_eq_left (sub_nonpos.mpr h), sub_self]
    · have h' : f (σ s) ≤ f (σ r) := le_of_not_ge h
      rw [max_eq_left h', max_eq_right (sub_nonneg.mpr h')]
  simp_rw [hmax]
  exact h1_pospart_nonneg w (fun σ : Equiv.Perm n => σ r)
    (fun σ : Equiv.Perm n => σ s) hw f

private noncomputable def h1_fiber_map {α β : Type*} [Fintype α] [DecidableEq β]
    (p : α → β) : (α → ℝ) →ₗ[ℝ] (β → ℝ) := by
  classical
  exact LinearMap.pi (fun b => ∑ a ∈ Finset.univ.filter (fun a => p a = b), LinearMap.proj a)

private theorem h1_fiber_map_apply {α β : Type*} [Fintype α] [DecidableEq β]
    (p : α → β) (w : α → ℝ) (b : β) :
    h1_fiber_map p w b = ∑ a : α, if p a = b then w a else 0 := by
  classical
  simp [h1_fiber_map, LinearMap.sum_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split <;> simp

/-- Separate the desired row marginal from the compact convex set of marginals of
probability distributions with the prescribed unordered pair masses. The maximizing
orientation and directed cut inequalities rule out any strict separator. -/
private theorem h1_two_rows {n : Type} [Fintype n] [DecidableEq n]
    (w : Equiv.Perm n → ℝ)
    (hw₁ : (∑ σ, w σ) = 1)
    (hw : ∀ I J : Finset n, 0 ≤ ∑ σ : Equiv.Perm n,
      w σ * (if ∀ i ∈ I, σ i ∈ J then (1 : ℝ) else 0))
    (r s : n) :
    ∃ t : Equiv.Perm n → ℝ,
      (∀ σ, 0 ≤ t σ) ∧ (∑ σ, t σ) = 1 ∧
      (∀ J : Finset n, (∑ σ : Equiv.Perm n, if ({r,s} : Finset n).image σ = J then w σ else 0) =
        ∑ σ : Equiv.Perm n, if ({r,s} : Finset n).image σ = J then t σ else 0) ∧
      (∀ j : n, (∑ σ : Equiv.Perm n, if σ r = j then w σ else 0) =
        ∑ σ : Equiv.Perm n, if σ r = j then t σ else 0) ∧
      (∀ j : n, (∑ σ : Equiv.Perm n, if σ s = j then w σ else 0) =
        ∑ σ : Equiv.Perm n, if σ s = j then t σ else 0) := by
  classical
  let p (σ : Equiv.Perm n) := ({r,s} : Finset n).image σ
  let row := h1_fiber_map (fun σ : Equiv.Perm n => σ s)
  let pair := h1_fiber_map p
  let P : Set (Equiv.Perm n → ℝ) := {t | 0 ≤ t ∧ (∑ σ, t σ) = 1 ∧ pair t = pair w}
  have hconv : Convex ℝ P := by
    rintro x ⟨hx₀, hx₁, hx₂⟩ y ⟨hy₀, hy₁, hy₂⟩ a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · intro σ
      exact add_nonneg (mul_nonneg ha (hx₀ σ)) (mul_nonneg hb (hy₀ σ))
    · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hx₁, hy₁, mul_one] using hab
    · rw [map_add, map_smul, map_smul, hx₂, hy₂, ← add_smul, hab, one_smul]
  have hclosed : IsClosed P := by
    have hP : P = Set.Ici 0 ∩ {t | (∑ σ : Equiv.Perm n, t σ) = 1} ∩ {t | pair t = pair w} := by
      ext t
      simp [P, and_assoc]
    rw [hP]
    exact (isClosed_Ici.inter (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_eq pair.continuous_of_finiteDimensional continuous_const)
  have hcompact : IsCompact P := by
    apply isCompact_Icc.of_isClosed_subset hclosed
    rintro t ⟨ht₀, ht₁, _⟩
    refine ⟨ht₀, fun σ => ?_⟩
    change t σ ≤ 1
    rw [← ht₁]
    exact Finset.single_le_sum (fun τ _ => ht₀ τ) (Finset.mem_univ σ)
  have hmem : row w ∈ row '' P := by
    by_contra hbad
    obtain ⟨F, u, hu, hwu⟩ := geometric_hahn_banach_closed_point (hconv.linear_image row)
      (hcompact.image row.continuous_of_finiteDimensional).isClosed hbad
    let f (j : n) : ℝ := F (fun k => if j = k then 1 else 0)
    have eval (x : Equiv.Perm n → ℝ) : F (row x) = ∑ σ : Equiv.Perm n, x σ * f (σ s) := by
      change F.toLinearMap (row x) = _
      rw [LinearMap.pi_apply_eq_sum_univ]
      simp only [smul_eq_mul, row, h1_fiber_map_apply]
      exact (h1_fiber_sum (fun σ : Equiv.Perm n => σ s) f x).symm
    have hm (J : Finset n) : 0 ≤ ∑ σ : Equiv.Perm n, if p σ = J then w σ else 0 :=
      h1_image_mass_nonneg w hw {r,s} J
    obtain ⟨t, ht₀, ht₁, ht₂, ht₃⟩ := h1_orientation w hw₁ r s f hm
    have htmem : t ∈ P := ⟨ht₀, ht₁, by
      funext J
      simpa only [pair, h1_fiber_map_apply] using ht₂ J⟩
    have hlt := (hu (row t) ⟨t, htmem, rfl⟩).trans hwu
    rw [eval, eval, ht₃] at hlt
    exact (not_lt_of_ge (h1_signed_max w r s (h1_cut_nonneg w hw r s) f)) hlt
  obtain ⟨t, ⟨ht₀, ht₁, ht₂⟩, htrow⟩ := hmem
  have hpair (J : Finset n) : (∑ σ : Equiv.Perm n, if p σ = J then w σ else 0) =
      ∑ σ : Equiv.Perm n, if p σ = J then t σ else 0 := by
    simpa only [pair, h1_fiber_map_apply] using congrFun ht₂.symm J
  have hs (j : n) : (∑ σ : Equiv.Perm n, if σ s = j then w σ else 0) =
      ∑ σ : Equiv.Perm n, if σ s = j then t σ else 0 := by
    simpa only [row, h1_fiber_map_apply] using congrFun htrow.symm j
  refine ⟨t, ht₀, ht₁, hpair, fun j => ?_, hs⟩
  by_cases hrs : r = s
  · simpa only [hrs] using hs j
  have hcount (x : Equiv.Perm n → ℝ) :
      (∑ σ : Equiv.Perm n, if σ r = j then x σ else 0) +
      (∑ σ : Equiv.Perm n, if σ s = j then x σ else 0) =
      ∑ J : Finset n, (∑ σ : Equiv.Perm n, if p σ = J then x σ else 0) *
        (if j ∈ J then (1 : ℝ) else 0) := by
    rw [← h1_fiber_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    have hne : σ r ≠ σ s := fun h => hrs (σ.injective h)
    by_cases hr : σ r = j
    · have hs' : σ s ≠ j := fun he => hne (hr.trans he.symm)
      simp [p, hr, hs']
    · by_cases hs' : σ s = j
      · simp [p, hr, hs']
      · simp [p, hr, hs', Ne.symm hr, Ne.symm hs']
  have hc := hcount w
  have hct := hcount t
  rw [← hs j] at hct
  have hgap :
    (∑ J : Finset n, (∑ σ : Equiv.Perm n, if p σ = J then w σ else 0) *
        (if j ∈ J then (1 : ℝ) else 0)) =
      ∑ J : Finset n, (∑ σ : Equiv.Perm n, if p σ = J then t σ else 0) *
        (if j ∈ J then (1 : ℝ) else 0) := by simp_rw [hpair]
  linarith only [hc, hct, hgap]

private theorem h1_singleton_image {n : Type} [Fintype n] [DecidableEq n]
    (x : n) (w t : Equiv.Perm n → ℝ)
    (hx : ∀ j : n, (∑ σ : Equiv.Perm n, if σ x = j then w σ else 0) =
      ∑ σ : Equiv.Perm n, if σ x = j then t σ else 0) (J : Finset n) :
    (∑ σ : Equiv.Perm n, if ({x} : Finset n).image σ = J then w σ else 0) =
      ∑ σ : Equiv.Perm n, if ({x} : Finset n).image σ = J then t σ else 0 := by
  classical
  by_cases hJ : J.card = 1
  · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ
    simpa only [Finset.image_singleton, Finset.singleton_inj] using hx j
  have hn (σ : Equiv.Perm n) : ({x} : Finset n).image σ ≠ J := by
    intro h
    apply hJ
    rw [← h]
    simp
  simp only [hn, if_false, Finset.sum_const_zero]

theorem OMA.solution : OMA.R_DeterminantalConjecture_determinantal_conjecture_R1.H1 := by
  classical
  intro n _ _ w hw₁ hw T hT
  have empty (t : Equiv.Perm n → ℝ) (ht₁ : (∑ σ, t σ) = 1) (J : Finset n) :
      (∑ σ : Equiv.Perm n, if (∅ : Finset n).image σ = J then w σ else 0) =
        ∑ σ : Equiv.Perm n, if (∅ : Finset n).image σ = J then t σ else 0 := by
    by_cases hJ : J = ∅ <;> simp [hJ, eq_comm, hw₁, ht₁]
  have cases_card : T.card = 0 ∨ T.card = 1 ∨ T.card = 2 := by omega
  rcases cases_card with hT₀ | hT₁ | hT₂
  · obtain rfl := Finset.card_eq_zero.mp hT₀
    let t (σ : Equiv.Perm n) : ℝ := if σ = 1 then 1 else 0
    have ht₁ : (∑ σ, t σ) = 1 := by simp [t]
    refine ⟨t, fun σ => by dsimp [t]; split <;> norm_num, ht₁, ?_⟩
    intro S hS J
    obtain rfl := Finset.subset_empty.mp hS
    exact empty t ht₁ J
  · obtain ⟨r, rfl⟩ := Finset.card_eq_one.mp hT₁
    obtain ⟨t, ht₀, ht₁, _, hr, _⟩ := h1_two_rows w hw₁ hw r r
    refine ⟨t, ht₀, ht₁, fun S hS J => ?_⟩
    rcases Finset.subset_singleton_iff.mp hS with rfl | rfl
    · exact empty t ht₁ J
    · exact h1_singleton_image r w t hr J
  · obtain ⟨r, s, hrs, rfl⟩ := Finset.card_eq_two.mp hT₂
    obtain ⟨t, ht₀, ht₁, hpair, hr, hs⟩ := h1_two_rows w hw₁ hw r s
    refine ⟨t, ht₀, ht₁, fun S hS J => ?_⟩
    have hScard := Finset.card_le_card hS
    have hcard : ({r,s} : Finset n).card = 2 := by simp [hrs]
    rw [hcard] at hScard
    have Scases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
    rcases Scases with hS₀ | hS₁ | hS₂
    · obtain rfl := Finset.card_eq_zero.mp hS₀
      exact empty t ht₁ J
    · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hS₁
      have hj := hS (Finset.mem_singleton_self j)
      have hjs : j = r ∨ j = s := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hj
      rcases hjs with rfl | rfl
      · exact h1_singleton_image j w t hr J
      · exact h1_singleton_image j w t hs J
    · have hSame : S = {r,s} := (Finset.subset_iff_eq_of_card_le (by omega)).mp hS
      rw [hSame]
      exact hpair J
