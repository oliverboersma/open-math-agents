import OMAReductions.R_Erdos1070_erdos_1070_parts_ii_R1
import Mathlib

/-! Finite sums with slowly growing support and with room for prescribed shifts. -/

namespace OMA.Erdos1070

open Filter BigOperators Topology

section FiniteSums

variable {ι G : Type*} [Fintype ι] [AddCommGroup G]

private def evalBox (g : ι → G) (n : ℕ) (a : ι → Fin (2 * n + 1)) : G :=
  ∑ i, (((a i : ℕ) : ℤ) - (n : ℤ)) • g i

private noncomputable def sumBox (g : ι → G) (n : ℕ) : Finset G :=
  by
    classical
    exact Finset.univ.image (evalBox g n)

private theorem zero_mem_sumBox (g : ι → G) (n : ℕ) : 0 ∈ sumBox g n := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨fun _ ↦ ⟨n, by omega⟩, Finset.mem_univ _, ?_⟩
  simp [evalBox]

private theorem sumBox_card (g : ι → G) (n : ℕ) :
    (sumBox g n).card ≤ (2 * n + 1) ^ Fintype.card ι := by
  classical
  exact Finset.card_image_le.trans_eq (by simp)

private theorem sumBox_translate (g : ι → G) (n : ℕ) (d : ι → ℤ)
    (hd : ∀ i, -1 ≤ d i ∧ d i ≤ 1) {x : G} (hx : x ∈ sumBox g n) :
    (∑ i, d i • g i) + x ∈ sumBox g (n + 1) := by
  classical
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
  let b (i : ι) : Fin (2 * (n + 1) + 1) :=
    ⟨(((a i : ℕ) : ℤ) + 1 + d i).toNat, by
      have ha := (a i).isLt
      have hdi := hd i
      omega⟩
  apply Finset.mem_image.mpr
  refine ⟨b, Finset.mem_univ _, ?_⟩
  unfold evalBox
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_zsmul]
  congr 1
  have hdi := hd i
  change (((((a i : ℕ) : ℤ) + 1 + d i).toNat : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)
    = d i + (((a i : ℕ) : ℤ) - (n : ℤ))
  omega

theorem exists_finite_sum_boxes (g : ι → G) (ε : ℝ) (hε : 0 < ε) :
    ∃ A B : Finset G, A.Nonempty ∧ ((B.card : ℝ) < (1 + ε) * (A.card : ℝ)) ∧
      ∀ (d : ι → ℤ), (∀ i, -1 ≤ d i ∧ d i ≤ 1) →
        ∀ x ∈ A, (∑ i, d i • g i) + x ∈ B := by
  classical
  suffices h : ∃ n, ((sumBox g (n + 1)).card : ℝ) < (1 + ε) * (sumBox g n).card by
    obtain ⟨n, hn⟩ := h
    exact ⟨sumBox g n, sumBox g (n + 1), ⟨0, zero_mem_sumBox g n⟩, hn,
      fun d hd _ hx ↦ sumBox_translate g n d hd hx⟩
  by_contra! h
  have hLower (n : ℕ) : (1 + ε) ^ n ≤ ((sumBox g n).card : ℝ) := by
    induction n with
    | zero =>
      simp only [pow_zero]
      exact_mod_cast Finset.card_pos.mpr (show (sumBox g 0).Nonempty from
        ⟨0, zero_mem_sumBox g 0⟩)
    | succ n ih =>
      rw [pow_succ']
      exact (mul_le_mul_of_nonneg_left ih (by positivity)).trans (h n)
  let k := Fintype.card ι
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt k (by linarith : 1 < 1 + ε)
  have hlt : ∀ᶠ n : ℕ in atTop,
      (3 : ℝ)^k * ((n : ℝ)^k / (1 + ε)^n) < 1 := by
    apply (tendsto_const_nhds.mul hlim).eventually_lt tendsto_const_nhds
    simp
  obtain ⟨n, hn, hne⟩ := ((eventually_ge_atTop (1 : ℕ)).and hlt).exists
  have hpoly : ((sumBox g n).card : ℝ) ≤ (3 : ℝ)^k * (n : ℝ)^k := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      ((sumBox g n).card : ℝ) ≤ ((2 * (n : ℝ) + 1) ^ k) := by
        exact_mod_cast sumBox_card g n
      _ ≤ (3 * (n : ℝ)) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = _ := mul_pow _ _ _
  rw [← mul_div_assoc, div_lt_iff₀ (pow_pos (by positivity) _), one_mul] at hne
  exact (not_lt_of_ge ((hLower n).trans hpoly)) hne

end FiniteSums

end OMA.Erdos1070

namespace OMA.Erdos1070

open BigOperators ComplexConjugate

private def oriented (r : Additive Circle × Bool) (z : ℂ) : ℂ :=
  (r.1.toMul : ℂ) * (if r.2 then conj z else z)

private noncomputable def composeOrientation (s r : Additive Circle × Bool) : Additive Circle × Bool :=
  (r.1 + (if r.2 then -s.1 else s.1), r.2 ^^ s.2)

private theorem oriented_add (r : Additive Circle × Bool) (b z : ℂ) :
    oriented r (z + b) = oriented r z + oriented r b := by
  cases r with
  | mk r f =>
    cases f <;> simp [oriented, mul_add]

private theorem oriented_dist (r : Additive Circle × Bool) (x y : ℂ) :
    dist (oriented r x) (oriented r y) = dist x y := by
  cases r with
  | mk r f =>
    cases f <;> simp [oriented, dist_eq_norm, ← mul_sub, ← map_sub, Circle.norm_coe]

private theorem oriented_compose (s r : Additive Circle × Bool) (z : ℂ) :
    oriented (composeOrientation s r) z = oriented r (oriented s z) := by
  rcases r with ⟨r, fr⟩
  rcases s with ⟨s, fs⟩
  have hc : ((s.toMul : ℂ)⁻¹) = conj (s.toMul : ℂ) := by
    rw [← Circle.coe_inv]
    exact Circle.coe_inv_eq_conj _
  cases fr <;> cases fs <;>
    simp [oriented, composeOrientation, mul_assoc, hc]

private theorem composeOrientation_inj (s : Additive Circle × Bool) :
    Function.Injective (composeOrientation s) := by
  rintro ⟨a, fa⟩ ⟨b, fb⟩ h
  have h₂ := congrArg Prod.snd h
  have hbool : fa = fb := by
    change (fa ^^ s.2) = (fb ^^ s.2) at h₂
    cases fs : s.2 <;> simpa [fs] using h₂
  subst fb
  have h₁ := congrArg Prod.fst h
  change a + (if fa then -s.1 else s.1) = b + (if fa then -s.1 else s.1) at h₁
  exact congrArg (fun v ↦ (v, fa)) (add_right_cancel h₁)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private noncomputable def shifts (B : Finset ℂ) (v : ι → ℂ) (S : Finset ι) : Finset ℂ := by
  classical
  exact if h : S.Nonempty then
    (B.image fun z ↦ z - v h.choose).filter fun t ↦ ∀ i ∈ S, v i + t ∈ B
    else ∅

private theorem mem_shifts {B : Finset ℂ} {v : ι → ℂ} {S : Finset ι} (hS : S.Nonempty) (t : ℂ) :
    t ∈ shifts B v S ↔ ∀ i ∈ S, v i + t ∈ B := by
  classical
  rw [shifts, dif_pos hS, Finset.mem_filter]
  refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
  exact Finset.mem_image.mpr ⟨v hS.choose + t, h _ hS.choose_spec, by abel⟩

private theorem card_shifts_le {B : Finset ℂ} {v : ι → ℂ} {S : Finset ι} :
    (shifts B v S).card ≤ B.card := by
  classical
  by_cases hS : S.Nonempty
  · rw [shifts, dif_pos hS]
    exact (Finset.card_filter_le _ _).trans Finset.card_image_le
  · simp [shifts, hS]

private theorem card_shifts_singleton (B : Finset ℂ) (v : ι → ℂ) (i : ι) :
    (shifts B v {i}).card = B.card := by
  classical
  have h : shifts B v {i} = B.image (fun b ↦ b - v i) := by
    ext t
    rw [mem_shifts (Finset.singleton_nonempty i), Finset.mem_image]
    simp only [Finset.mem_singleton, forall_eq]
    exact ⟨fun h ↦ ⟨v i + t, h, by abel⟩, by
      rintro ⟨b, hb, rfl⟩
      rwa [add_comm, sub_add_cancel]⟩
  rw [h, Finset.card_image_of_injective]
  exact sub_left_injective

private theorem card_shifts_congr {B : Finset ℂ} {u v : ι → ℂ}
    {S R : Finset ι} (hS : S.Nonempty) (hR : R.Nonempty) (c : ℂ)
    (h : S.image (fun i ↦ u i + c) = R.image v) :
    (shifts B u S).card = (shifts B v R).card := by
  classical
  have hs : (shifts B u S).image (fun t ↦ t - c) = shifts B v R := by
    ext t
    rw [mem_shifts hR, Finset.mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, hx, rfl⟩ j hj
      have hmem : v j ∈ S.image (fun i ↦ u i + c) :=
        h.symm ▸ Finset.mem_image_of_mem v hj
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
      rw [← he, show u i + c + (x - c) = u i + x by abel]
      exact (mem_shifts hS x).mp hx i hi
    · intro ht
      refine ⟨t + c, (mem_shifts hS _).mpr ?_, add_sub_cancel_right _ _⟩
      intro i hi
      have hmem : u i + c ∈ R.image v :=
        h ▸ Finset.mem_image_of_mem (fun i ↦ u i + c) hi
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hmem
      rw [show u i + (t + c) = u i + c + t by abel, ← he]
      exact ht j hj
  rw [← hs, Finset.card_image_of_injective]
  exact sub_left_injective


private theorem exists_orientation_boxes (o : ι → Additive Circle × Bool) (ε : ℝ) (hε : 0 < ε) :
    ∃ F L : Finset (Additive Circle × Bool), F.Nonempty ∧ F ⊆ L ∧
      (L.card : ℝ) < (1 + ε) * (F.card : ℝ) ∧
      ∀ i r, r ∈ F → composeOrientation (o i) r ∈ L := by
  classical
  obtain ⟨A, B, hA, hcard, hMove⟩ := exists_finite_sum_boxes (fun i ↦ (o i).1) ε hε
  have hSub : A ⊆ B := by
    intro a ha
    simpa using hMove (fun _ ↦ 0) (fun _ ↦ by norm_num) a ha
  let F := A ×ˢ (Finset.univ : Finset Bool)
  let L := B ×ˢ (Finset.univ : Finset Bool)
  refine ⟨F, L, hA.product Finset.univ_nonempty, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨h, hf⟩ := Finset.mem_product.mp hx
    exact Finset.mem_product.mpr ⟨hSub h, hf⟩
  · dsimp [F, L]
    simp only [Finset.card_product, Nat.cast_mul, ← mul_assoc]
    exact mul_lt_mul_of_pos_right hcard (by norm_num)
  · intro i r hr
    let d j : ℤ := if j = i then (if r.2 then -1 else 1) else 0
    have hd : ∀ j, -1 ≤ d j ∧ d j ≤ 1 := by
      intro j
      by_cases hij : j = i <;> cases hbool : r.2 <;> simp [d, hij, hbool]
    have hsum : ∑ j, d j • (o j).1 = if r.2 then -(o i).1 else (o i).1 := by
      cases hbool : r.2 <;> simp [d, hbool, ite_smul]
    have h := hMove d hd r.1 (Finset.mem_product.mp hr).1
    rw [hsum, add_comm] at h
    exact Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩

private theorem exists_translation_boxes (g : ι → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X T : Finset ℂ, X.Nonempty ∧ X ⊆ T ∧ (T.card : ℝ) < (1 + ε) * (X.card : ℝ)
      ∧ ∀ i x, x ∈ X → x - g i ∈ T := by
  classical
  obtain ⟨X, T, hX, hcard, hMove⟩ := exists_finite_sum_boxes g ε hε
  have hSub : X ⊆ T := by
    intro x hx
    simpa using hMove (fun _ ↦ 0) (fun _ ↦ by norm_num) x hx
  refine ⟨X, T, hX, hSub, hcard, ?_⟩
  intro i x hx
  let d j : ℤ := if j = i then -1 else 0
  have hd : ∀ j, -1 ≤ d j ∧ d j ≤ 1 := by
    intro j
    by_cases hji : j = i <;> simp [d, hji]
  have hsum : ∑ j, d j • g j = -g i := by simp [d, ite_smul]
  have h := hMove d hd x hx
  rwa [hsum, add_comm, ← sub_eq_add_neg] at h

private theorem sum_shift_error {α : Type*} [DecidableEq α]
    {F L : Finset α} (hF : F ⊆ L) {f : α → ℝ} {M : ℝ}
    (hValues : ∀ x ∈ L, 0 ≤ f x ∧ f x ≤ M) (e : α ↪ α) (he : F.map e ⊆ L) :
    |(∑ x ∈ F, f (e x)) - ∑ x ∈ F, f x| ≤ ((L.card : ℝ) - F.card) * M := by
  have rest (A : Finset α) (hA : A ⊆ L) :
      0 ≤ ∑ x ∈ L \ A, f x ∧
        (∑ x ∈ L \ A, f x) ≤ ((L.card : ℝ) - A.card) * M := by
    have hsubset : L \ A ⊆ L := Finset.sdiff_subset
    have hCount : ((L \ A).card : ℝ) = (L.card : ℝ) - A.card := by
      rw [Finset.card_sdiff_of_subset hA, Nat.cast_sub (Finset.card_le_card hA)]
    refine ⟨Finset.sum_nonneg (fun x hx ↦ (hValues x (hsubset hx)).1), ?_⟩
    calc
      (∑ x ∈ L \ A, f x) ≤ ∑ x ∈ L \ A, M :=
        Finset.sum_le_sum fun x hx ↦ (hValues x (hsubset hx)).2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hCount]
  have h₁ := Finset.sum_sdiff hF (f := f)
  have h₂ := Finset.sum_sdiff he (f := f)
  have hb₁ := rest F hF
  have hb₂ := rest (F.map e) he
  rw [Finset.sum_map] at h₂
  rw [Finset.card_map] at hb₂
  exact abs_le.mpr ⟨by linarith [hb₁.1, hb₂.2], by linarith [hb₂.1, hb₁.2]⟩


theorem exists_complex_moments (p : ι → ℂ)
    (C : List (ℤ × Finset ι × Finset ι)) (i₀ : ι)
    (hCongruent : ∀ r ∈ C, ∃ a b : ℂ, ‖a‖ = 1 ∧
      (r.2.1.image (fun i ↦ a * p i + b) = r.2.2.image p ∨
        r.2.1.image (fun i ↦ a * conj (p i) + b) = r.2.2.image p))
    (hLarge : ∀ X : Finset ℂ, ∃ B ⊆ X, (X.card : ℝ) / 4 ≤ B.card ∧
      ∀ x ∈ B, ∀ y ∈ B, dist x y ≠ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : Finset ι → ℝ,
      (∀ I, 0 ≤ μ I) ∧ (∑ I, μ I) = 1 ∧
      (∀ I, ¬ (∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1) → μ I = 0) ∧
      let moment := fun S : Finset ι ↦ ∑ I, if S ⊆ I then μ I else 0
      1 / 4 - ε ≤ moment {i₀} ∧ ∀ r ∈ C, |moment r.2.1 - moment r.2.2| ≤ ε := by
  classical
  let CSet := C.toFinset
  have hMaps (r : CSet) : ∃ (o : Additive Circle × Bool) (b : ℂ),
      r.val.2.1.image (fun i ↦ oriented o (p i) + b) = r.val.2.2.image p := by
    obtain ⟨a, b, ha, hb⟩ := hCongruent r.val (List.mem_toFinset.mp r.property)
    let v : Circle := ⟨a, mem_sphere_zero_iff_norm.mpr ha⟩
    rcases hb with h | h
    · exact ⟨(Additive.ofMul v, false), b, h⟩
    · exact ⟨(Additive.ofMul v, true), b, h⟩
  choose o b hb using hMaps
  obtain ⟨F, L, hF, hFL, hFLCard, hFMove⟩ := exists_orientation_boxes o ε hε
  let g (i : F × ι) := oriented (i.1 : Additive Circle × Bool) (p i.2)
  obtain ⟨X, T, hX, hXT, hXTCard, hTMove⟩ := exists_translation_boxes g ε hε
  obtain ⟨B, hBX, hBCard, hB⟩ := hLarge X
  let P := F ×ˢ T
  let atom (z : (Additive Circle × Bool) × ℂ) : Finset ι :=
    Finset.univ.filter fun i ↦ oriented z.1 (p i) + z.2 ∈ B
  let μ (I : Finset ι) : ℝ := ((P.filter fun z ↦ atom z = I).card : ℝ) / P.card
  let moment (S : Finset ι) : ℝ := ∑ I, if S ⊆ I then μ I else 0
  have hFPos : 0 < (F.card : ℝ) := by exact_mod_cast hF.card_pos
  have hTPos : 0 < (T.card : ℝ) := by exact_mod_cast (hX.mono hXT).card_pos
  have hPPos : 0 < (P.card : ℝ) := by
    dsimp [P]
    rw [Finset.card_product, Nat.cast_mul]
    exact mul_pos hFPos hTPos
  have hMoment (S : Finset ι) :
      moment S = ((P.filter fun z ↦ S ⊆ atom z).card : ℝ) / P.card := by
    have hc := Finset.sum_card_fiberwise_eq_card_filter P
      (Finset.univ.filter fun I : Finset ι ↦ S ⊆ I) atom
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_filter] at hc
    have hI (I : Finset ι) :
        (if S ⊆ I then ((P.filter fun z ↦ atom z = I).card : ℝ) / P.card else 0) =
          (if S ⊆ I then ((P.filter fun z ↦ atom z = I).card : ℝ) else 0) / P.card := by
      split_ifs <;> simp
    unfold moment μ
    simp_rw [hI]
    rw [← Finset.sum_div]
    congr 1
    exact_mod_cast hc
  have hMomentShifts (S : Finset ι) (hS : S.Nonempty) :
      moment S = (∑ r ∈ F, ((shifts B (fun i ↦ oriented r (p i)) S).card : ℝ)) / P.card := by
    rw [hMoment, Finset.card_filter, Nat.cast_sum]
    dsimp only [P]
    rw [Finset.sum_product]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    have hEq : (T.filter fun t ↦ S ⊆ atom (r,t)) =
        shifts B (fun i ↦ oriented r (p i)) S := by
      ext t
      rw [Finset.mem_filter, mem_shifts hS]
      constructor
      · intro ht i hi
        exact (Finset.mem_filter.mp (ht.2 hi)).2
      · intro ht
        have hXt := hBX (ht hS.choose hS.choose_spec)
        have hMove := hTMove (⟨r, hr⟩, hS.choose) (oriented r (p hS.choose) + t) hXt
        have htT : t ∈ T := by
          convert hMove using 1
          dsimp [g]
          abel
        exact ⟨htT, fun i hi ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht i hi⟩⟩
    rw [← hEq, Finset.card_filter, Nat.cast_sum]
  refine ⟨μ, fun I ↦ div_nonneg (Nat.cast_nonneg _) hPPos.le, ?_, ?_, ?_, ?_⟩
  · rw [show (∑ I, μ I) = moment ∅ by simp [moment], hMoment]
    simp [hPPos.ne']
  · intro I hI
    have he : (P.filter fun z ↦ atom z = I) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨_, hEq⟩ := Finset.mem_filter.mp hz
      apply hI
      subst I
      intro i hi j hj hij
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      apply hB _ hi' _ hj'
      rwa [dist_add_right, oriented_dist]
    simp [μ, he]
  · change 1 / 4 - ε ≤ moment {i₀}
    rw [hMomentShifts _ (Finset.singleton_nonempty _)]
    simp only [card_shifts_singleton, Finset.sum_const, nsmul_eq_mul]
    dsimp only [P]
    rw [Finset.card_product, Nat.cast_mul, mul_div_mul_left _ _ hFPos.ne']
    have hXLe : (X.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hXT
    have hXError : (T.card : ℝ) - X.card ≤ ε * T.card := by
      exact (show (T.card : ℝ) - X.card ≤ ε * X.card by linarith [hXTCard]).trans
        (mul_le_mul_of_nonneg_left hXLe hε.le)
    apply (le_div_iff₀ hTPos).mpr
    linarith [hXError, mul_nonneg hε.le hTPos.le]
  · intro r hr
    change |moment r.2.1 - moment r.2.2| ≤ ε
    let c : CSet := ⟨r, List.mem_toFinset.mpr hr⟩
    have hEq := hb c
    change r.2.1.image (fun i ↦ oriented (o c) (p i) + b c) = r.2.2.image p at hEq
    by_cases hLeft : r.2.1.Nonempty
    · have hRight : r.2.2.Nonempty := Finset.image_nonempty.mp
        (hEq ▸ hLeft.image _)
      let e : (Additive Circle × Bool) ↪ (Additive Circle × Bool) :=
        ⟨composeOrientation (o c), composeOrientation_inj _⟩
      have hMap : F.map e ⊆ L := by
        intro a h
        obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp h
        exact hFMove c z hz
      let f (z : Additive Circle × Bool) :=
        ((shifts B (fun i ↦ oriented z (p i)) r.2.1).card : ℝ)
      have hReindex (z : Additive Circle × Bool) :
          f (e z) = ((shifts B (fun i ↦ oriented z (p i)) r.2.2).card : ℝ) := by
        dsimp [f, e]
        exact_mod_cast card_shifts_congr hLeft hRight (oriented z (b c)) (by
          have he := congrArg (Finset.image (oriented z)) hEq
          simpa only [Finset.image_image, Function.comp_def, oriented_add, oriented_compose] using he)
      have hValues (z) (_ : z ∈ L) : 0 ≤ f z ∧ f z ≤ (B.card : ℝ) := by
        refine ⟨Nat.cast_nonneg _, ?_⟩
        dsimp [f]
        exact_mod_cast card_shifts_le
      have herror := sum_shift_error hFL hValues e hMap
      rw [hMomentShifts _ hLeft, hMomentShifts _ hRight, abs_sub_comm,
        ← sub_div, abs_div, abs_of_pos hPPos]
      simp only [hReindex] at herror
      apply (div_le_iff₀ hPPos).mpr
      refine herror.trans ?_
      have hBT : (B.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card (hBX.trans hXT)
      calc
        ((L.card : ℝ) - F.card) * (B.card : ℝ) ≤ (ε * F.card) * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [hFLCard]) (Nat.cast_nonneg _)
        _ ≤ (ε * F.card) * (T.card : ℝ) :=
          mul_le_mul_of_nonneg_left hBT (mul_nonneg hε.le hFPos.le)
        _ = ε * (P.card : ℝ) := by
          rw [show P.card = F.card * T.card by exact Finset.card_product _ _, Nat.cast_mul]
          ring
    · have hn : r.2.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLeft
      rw [hn, Finset.image_empty, eq_comm, Finset.image_eq_empty] at hEq
      rw [hn, hEq, sub_self, abs_zero]
      exact hε.le

end OMA.Erdos1070

theorem OMA.solution : OMA.R_Erdos1070_erdos_1070_parts_ii_R1.H2 := by
  intro p C hCongruent hLarge ε hε
  exact OMA.Erdos1070.exists_complex_moments p C 0 hCongruent hLarge ε hε
