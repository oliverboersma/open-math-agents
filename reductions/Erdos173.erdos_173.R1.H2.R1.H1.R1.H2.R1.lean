import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H1_R1

/-! Countable carrier fields for both prescribed scales.
Port of Jacob Parish (Plasma AI), plasma-ai/erdos-173@4a368a652753, Apache-2.0.
Includes modified portions of OpenAI, openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Apache-2.0, on number fields and finite direction selections. -/
-- Credit: @marcusbuffett


-- Erdos173.Template.Density
section
noncomputable section

namespace Parish173.Template

open Polynomial

variable (K : Type*) [Field K] (ι : Type*)

private def polyFuns : Subalgebra K ((ι → K) → K) :=
  (MvPolynomial.aeval (fun i (z : ι → K) => z i)).range

variable {K ι}

lemma aeval_coords_apply (P : MvPolynomial ι K) (z : ι → K) :
    MvPolynomial.aeval (fun i (z : ι → K) => z i) P z = MvPolynomial.eval z P := by
  have h := MvPolynomial.comp_aeval_apply (R := K) (fun i (z : ι → K) => z i)
    (Pi.evalAlgHom K (fun _ : ι → K => K) z) P
  simp only [Pi.evalAlgHom_apply] at h
  rw [h]
  rfl

lemma coord_mem_polyFuns (i : ι) : (fun z : ι → K => z i) ∈ polyFuns K ι :=
  ⟨MvPolynomial.X i, by simp⟩

lemma const_mem_polyFuns (c : K) : (fun _ : ι → K => c) ∈ polyFuns K ι :=
  (polyFuns K ι).algebraMap_mem c

lemma polyFuns_eq_adjoin :
    polyFuns K ι = Algebra.adjoin K (Set.range (fun i (z : ι → K) => z i)) :=
  (Algebra.adjoin_range_eq_range_aeval K _).symm

lemma add_mem_polyFuns {f g : (ι → K) → K} (hf : f ∈ polyFuns K ι) (hg : g ∈ polyFuns K ι) :
    (fun z => f z + g z) ∈ polyFuns K ι := (polyFuns K ι).add_mem hf hg

lemma sub_mem_polyFuns {f g : (ι → K) → K} (hf : f ∈ polyFuns K ι) (hg : g ∈ polyFuns K ι) :
    (fun z => f z - g z) ∈ polyFuns K ι := (polyFuns K ι).sub_mem hf hg

lemma mul_mem_polyFuns {f g : (ι → K) → K} (hf : f ∈ polyFuns K ι) (hg : g ∈ polyFuns K ι) :
    (fun z => f z * g z) ∈ polyFuns K ι := (polyFuns K ι).mul_mem hf hg

lemma comp_mem_polyFuns {κ : Type*} {φ : (ι → K) → (κ → K)}
    (hφ : ∀ j, (fun z => φ z j) ∈ polyFuns K ι) {f : (κ → K) → K}
    (hf : f ∈ polyFuns K κ) : (fun z => f (φ z)) ∈ polyFuns K ι := by
  rw [polyFuns_eq_adjoin] at hf
  induction hf using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨j, rfl⟩ := hg
    exact hφ j
  | algebraMap c => exact const_mem_polyFuns c
  | add f g _ _ hf hg => exact (polyFuns K ι).add_mem hf hg
  | mul f g _ _ hf hg => exact (polyFuns K ι).mul_mem hf hg

lemma eval_mem_polyFuns (p : K[X]) {f : (ι → K) → K} (hf : f ∈ polyFuns K ι) :
    (fun z => p.eval (f z)) ∈ polyFuns K ι := by
  induction p using Polynomial.induction_on with
  | C c => simpa using const_mem_polyFuns c
  | add p q hp hq =>
    convert (polyFuns K ι).add_mem hp hq using 1
    ext z
    simp
  | monomial n c _ =>
    convert (polyFuns K ι).mul_mem (const_mem_polyFuns c) ((polyFuns K ι).pow_mem hf (n + 1))
      using 1
    ext z
    simp

lemma exists_poly_comp {φ : K → ι → K} (hφ : ∀ i, ∃ p : K[X], ∀ t, φ t i = p.eval t)
    {f : (ι → K) → K} (hf : f ∈ polyFuns K ι) : ∃ p : K[X], ∀ t, f (φ t) = p.eval t := by
  rw [polyFuns_eq_adjoin] at hf
  induction hf using Algebra.adjoin_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact hφ i
  | algebraMap c => exact ⟨C c, fun t => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨p, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    exact ⟨p + q, fun t => by simp [hp, hq]⟩
  | mul f g _ _ hf hg =>
    obtain ⟨p, hp⟩ := hf
    obtain ⟨q, hq⟩ := hg
    exact ⟨p * q, fun t => by simp [hp, hq]⟩

lemma eval_coord_mem_polyFuns (p : K[X]) (i : ι) : (fun z : ι → K => p.eval (z i)) ∈ polyFuns K ι :=
  eval_mem_polyFuns p (coord_mem_polyFuns i)

variable [Infinite K]

lemma eq_zero_or_eq_zero_of_mul_eq_zero {f g : (ι → K) → K} (hf : f ∈ polyFuns K ι)
    (hg : g ∈ polyFuns K ι) (hfg : f * g = 0) : f = 0 ∨ g = 0 := by
  obtain ⟨P, rfl⟩ := hf
  obtain ⟨Q, rfl⟩ := hg
  rw [← map_mul] at hfg
  have hPQ : P * Q = 0 := MvPolynomial.funext fun z => by
    simpa [aeval_coords_apply] using congrFun hfg z
  rcases mul_eq_zero.mp hPQ with h | h
  · exact Or.inl (by rw [h, map_zero])
  · exact Or.inr (by rw [h, map_zero])

lemma prod_mem_ne_zero {α : Type*} (s : Finset α) {f : α → (ι → K) → K}
    (hf : ∀ a ∈ s, f a ∈ polyFuns K ι) (hf0 : ∀ a ∈ s, f a ≠ 0) :
    (fun z => ∏ a ∈ s, f a z) ∈ polyFuns K ι ∧ (fun z => ∏ a ∈ s, f a z) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using const_mem_polyFuns (1 : K), fun h => ?_⟩
    simpa using congrFun h (fun _ => 0)
  | @insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
      (fun b hb => hf0 b (Finset.mem_insert_of_mem hb))
    simp only [Finset.prod_insert ha]
    refine ⟨mul_mem_polyFuns (hf a (Finset.mem_insert_self _ _)) h1, fun h => ?_⟩
    rcases eq_zero_or_eq_zero_of_mul_eq_zero (hf a (Finset.mem_insert_self _ _)) h1 h with h | h
    · exact hf0 a (Finset.mem_insert_self _ _) h
    · exact h2 h

omit [Infinite K] in

lemma poly_eq_zero_of_infinite {p : K[X]} {s : Set K} (hs : s.Infinite)
    (hp : ∀ t ∈ s, p.eval t = 0) : p = 0 :=
  p.eq_zero_of_infinite_isRoot (hs.mono fun t ht => hp t ht)

lemma poly_eq_zero_of_forall {p : K[X]} (hp : ∀ t, p.eval t = 0) : p = 0 :=
  poly_eq_zero_of_infinite Set.infinite_univ fun t _ => hp t

lemma exists_eval_ne_zero {p : K[X]} (hp : p ≠ 0) (s : Finset K) :
    ∃ t, t ∉ s ∧ p.eval t ≠ 0 := by
  by_contra! h
  apply hp
  apply poly_eq_zero_of_infinite (Set.Finite.infinite_compl s.finite_toSet)
  intro t ht
  exact h t ht

private def ZariskiDense (Z : Set (ι → K)) : Prop :=
  ∀ f ∈ polyFuns K ι, (∀ z ∈ Z, f z = 0) → f = 0

omit [Infinite K] in

lemma ZariskiDense.mono {Z Z' : Set (ι → K)} (hZ : ZariskiDense Z) (h : Z ⊆ Z') : ZariskiDense Z' :=
  fun f hf hZ' => hZ f hf fun z hz => hZ' z (h hz)

lemma ZariskiDense.inter {Z : Set (ι → K)} (hZ : ZariskiDense Z) {f : (ι → K) → K}
    (hf : f ∈ polyFuns K ι) (hf0 : f ≠ 0) : ZariskiDense {z | z ∈ Z ∧ f z ≠ 0} := by
  intro g hg hzero
  have hfg : f * g = 0 := hZ _ ((polyFuns K ι).mul_mem hf hg) fun z hz => by
    by_cases h : f z = 0
    · simp [h]
    · simp [hzero z ⟨hz, h⟩]
  exact (eq_zero_or_eq_zero_of_mul_eq_zero hf hg hfg).resolve_left hf0

lemma ZariskiDense.exists_of_cover {α : Type*} {Z : Set (ι → K)} (hZ : ZariskiDense Z)
    (s : Finset α)
    (Y : α → Set (ι → K)) (hcov : ∀ z ∈ Z, ∃ a ∈ s, z ∈ Y a) : ∃ a ∈ s, ZariskiDense (Y a) := by
  classical
  induction s using Finset.induction_on generalizing Z with
  | empty =>
    have h := hZ 1 (polyFuns K ι).one_mem fun z hz => by simpa using hcov z hz
    exact absurd (congrFun h (fun _ => 0)) one_ne_zero
  | @insert a s ha ih =>
    by_cases hY : ZariskiDense (Y a)
    · exact ⟨a, Finset.mem_insert_self _ _, hY⟩
    · simp only [ZariskiDense, not_forall] at hY
      obtain ⟨f, hf, hfY, hf0⟩ := hY
      obtain ⟨b, hb, hbY⟩ := ih (hZ.inter hf hf0) fun z hz => by
        obtain ⟨b, hb, hzb⟩ := hcov z hz.1
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact absurd (hfY z hzb) hz.2
        · exact ⟨b, hb, hzb⟩
      exact ⟨b, Finset.mem_insert_of_mem hb, hbY⟩

omit [Infinite K] in

lemma ZariskiDense.prod {κ : Type*} {Z : Set (ι → K)} {Z' : Set (κ → K)} (hZ : ZariskiDense Z)
    (hZ' : ZariskiDense Z') :
    ZariskiDense {w : ι ⊕ κ → K | w ∘ Sum.inl ∈ Z ∧ w ∘ Sum.inr ∈ Z'} := by
  intro f hf hzero
  have h1 (w' : κ → K) (hw' : w' ∈ Z') (z : ι → K) : f (Sum.elim z w') = 0 := by
    have hmem : (fun z => f (Sum.elim z w')) ∈ polyFuns K ι :=
      comp_mem_polyFuns (fun j => by
        rcases j with j | j
        · exact coord_mem_polyFuns j
        · exact const_mem_polyFuns _) hf
    exact congrFun (hZ _ hmem fun z hz => hzero _ ⟨hz, hw'⟩) z
  ext w
  have hmem : (fun w' => f (Sum.elim (w ∘ Sum.inl) w')) ∈ polyFuns K κ :=
    comp_mem_polyFuns (fun j => by
      rcases j with j | j
      · exact const_mem_polyFuns _
      · exact coord_mem_polyFuns j) hf
  have h := congrFun (hZ' _ hmem fun w' hw' => h1 w' hw' _) (w ∘ Sum.inr)
  simpa only [Sum.elim_comp_inl_inr, Pi.zero_apply] using h

end Parish173.Template

end
end

-- Erdos173.Template.Algebraic
section
noncomputable section

namespace Parish173.Template

open Polynomial ComplexConjugate

private abbrev 𝔸 : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

private instance algClosureA : IsAlgClosure ℚ 𝔸 := algebraicClosure.isAlgClosure ℚ ℂ
private instance algebraicA : Algebra.IsAlgebraic ℚ 𝔸 := algebraicClosure.isAlgebraic ℚ ℂ
private instance : IsAlgClosed 𝔸 := IsAlgClosure.isAlgClosed ℚ

private instance : Infinite 𝔸 := Infinite.of_injective (algebraMap ℚ 𝔸) (algebraMap ℚ 𝔸).injective

lemma I_mem_𝔸 : Complex.I ∈ 𝔸 :=
  mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow (n := 2) (by norm_num) (by
    rw [Complex.I_sq]; exact isAlgebraic_one.neg))

lemma conj_mem_𝔸 {z : ℂ} (hz : z ∈ 𝔸) : conj z ∈ 𝔸 :=
  mem_algebraicClosure_iff.mpr ((mem_algebraicClosure_iff.mp hz).algHom
    (Complex.conjAe.restrictScalars ℚ).toAlgHom)

private def iA : 𝔸 := ⟨Complex.I, I_mem_𝔸⟩

@[simp] lemma coe_iA : ((iA : 𝔸) : ℂ) = Complex.I := rfl

private def conjA (a : 𝔸) : 𝔸 := ⟨conj (a : ℂ), conj_mem_𝔸 a.property⟩

@[simp] lemma coe_conjA (a : 𝔸) : ((conjA a : 𝔸) : ℂ) = conj (a : ℂ) := rfl

lemma smul_eq (a : 𝔸) (z : ℂ) : a • z = (a : ℂ) * z := rfl

private def Ω : Set (Fin 2 → 𝔸) :=
  {z | z 0 ≠ 0 ∧ ‖((z 0 : 𝔸) : ℂ)‖ ≠ 1 ∧ z 1 = z 0 - (conjA (z 0))⁻¹}

lemma Ω_h_ne_zero {z : Fin 2 → 𝔸} (hz : z ∈ Ω) : z 1 ≠ 0 := by
  obtain ⟨h0, h1, hh⟩ := hz
  intro he
  rw [he, eq_comm, sub_eq_zero] at hh
  apply h1
  have hc := congrArg (fun w : 𝔸 => (w : ℂ)) hh
  simp only [IntermediateField.coe_inv, coe_conjA] at hc
  have hn : (z 0 : ℂ) * conj (z 0 : ℂ) = 1 := by
    nth_rewrite 1 [hc]
    exact inv_mul_cancel₀ (by simpa using h0)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hn
  have : ‖(z 0 : ℂ)‖ ^ 2 = 1 := by exact_mod_cast hn
  nlinarith [norm_nonneg (z 0 : ℂ)]

lemma Ω_unit {z : Fin 2 → 𝔸} (hz : z ∈ Ω) {T : ℂ} (hT : ‖T‖ = 1) :
    T - (z 0 : ℂ) ≠ 0 ∧ ‖(z 0 : ℂ) * (1 + (z 1 : ℂ) / (T - z 0))‖ = 1 := by
  obtain ⟨h0, h1, hh⟩ := hz
  set a : ℂ := (z 0 : ℂ)
  have ha : a ≠ 0 := by simpa [a] using h0
  have hTa : T - a ≠ 0 := by
    intro he
    apply h1
    rw [← sub_eq_zero.mp he, hT]
  refine ⟨hTa, ?_⟩
  have hh' : (z 1 : ℂ) = a - (conj a)⁻¹ := by
    have hc := congrArg (fun w : 𝔸 => (w : ℂ)) hh
    simpa [a] using hc
  have hca : conj a ≠ 0 := by simpa using ha
  have he : a * (1 + (z 1 : ℂ) / (T - a)) = (conj a * T - 1) * (a / conj a) / (T - a) := by
    rw [hh']
    field_simp
    ring
  rw [he, norm_div, norm_mul, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr ha),
    mul_one, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hTa)]
  have hTT : T * conj T = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hT]
    simp
  have h2 : conj (conj a * T - 1) = conj T * (a - T) := by
    simp only [map_sub, map_mul, Complex.conj_conj, map_one]
    linear_combination hTT
  rw [← Complex.norm_conj, h2, norm_mul, Complex.norm_conj, hT, one_mul, norm_sub_rev]

private def cayA (s : ℚ) : 𝔸 := (1 + (s : 𝔸) * iA) / (1 - (s : 𝔸) * iA)

lemma coe_cayA (s : ℚ) : ((cayA s : 𝔸) : ℂ) = (1 + s * Complex.I) / (1 - s * Complex.I) := by
  simp [cayA]

lemma one_sub_mul_I_ne (s : ℚ) : (1 : ℂ) - s * Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

lemma conj_cayA (s : ℚ) : conj ((cayA s : 𝔸) : ℂ) = ((cayA s : 𝔸) : ℂ)⁻¹ := by
  rw [coe_cayA, map_div₀, inv_div]
  simp [sub_eq_add_neg]

lemma norm_cayA (s : ℚ) : ‖((cayA s : 𝔸) : ℂ)‖ = 1 := by
  rw [coe_cayA, norm_div]
  have he : conj (1 + (s : ℂ) * Complex.I) = 1 - s * Complex.I := by simp [sub_eq_add_neg]
  rw [← he, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr ?_)]
  intro h
  have := congrArg Complex.re h
  simp at this

lemma cayA_injective : Function.Injective cayA := by
  intro s t hst
  have hc := congrArg (fun w : 𝔸 => (w : ℂ)) hst
  simp only [coe_cayA] at hc
  rw [div_eq_div_iff (one_sub_mul_I_ne s) (one_sub_mul_I_ne t)] at hc
  have h2 := congrArg Complex.im hc
  simp at h2
  exact_mod_cast (by linarith : (s : ℝ) = t)

lemma zariskiDense_Ω : ZariskiDense Ω := by
  intro f hf hzero
  
  let κ : ℚ → 𝔸 := fun r => 1 - ((r : 𝔸) ^ 2)⁻¹
  have hκ : ∀ r s : ℚ, 1 < r → 1 < s → κ r = κ s → r = s := by
    intro r s hr hs he
    have he' : ((r : 𝔸) ^ 2)⁻¹ = ((s : 𝔸) ^ 2)⁻¹ := by simpa [κ] using he
    rw [inv_inj] at he'
    have : ((r ^ 2 : ℚ) : 𝔸) = ((s ^ 2 : ℚ) : 𝔸) := by push_cast; exact he'
    have h2 : r ^ 2 = s ^ 2 := Rat.cast_injective this
    nlinarith
  
  have hline (r : ℚ) (hr : 1 < r) (t : ℚ) : ![(r : 𝔸) * cayA t, κ r * ((r : 𝔸) * cayA t)] ∈ Ω := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (by linarith : r ≠ 0)
    have hc0 : ((cayA t : 𝔸) : ℂ) ≠ 0 := by
      intro h
      have := norm_cayA t
      rw [h, norm_zero] at this
      exact zero_ne_one this
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hc := congrArg (fun w : 𝔸 => (w : ℂ)) h
      simp only [Matrix.cons_val_zero] at hc
      push_cast at hc
      exact mul_ne_zero hr0 hc0 hc
    · simp only [Matrix.cons_val_zero]
      push_cast
      rw [norm_mul, norm_cayA, mul_one, Complex.norm_ratCast]
      have : (1 : ℝ) < |(r : ℝ)| := by
        rw [abs_of_pos (by exact_mod_cast (by linarith : (0 : ℚ) < r))]
        exact_mod_cast hr
      exact ne_of_gt this
    · apply Subtype.ext
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, κ]
      push_cast
      rw [coe_conjA]
      push_cast
      rw [map_mul, conj_cayA]
      simp only [map_ratCast]
      field_simp
  
  have h1 (r : ℚ) (hr : 1 < r) (a : 𝔸) : f ![a, κ r * a] = 0 := by
    obtain ⟨p, hp⟩ := exists_poly_comp (φ := fun t => ![t, κ r * t]) (fun i => by
      fin_cases i
      · exact ⟨X, fun t => by simp⟩
      · exact ⟨C (κ r) * X, fun t => by simp⟩) hf
    have hp0 : p = 0 := by
      apply poly_eq_zero_of_infinite (s := Set.range (fun t : ℚ => (r : 𝔸) * cayA t))
      · apply Set.infinite_range_of_injective
        intro s t hst
        apply cayA_injective
        have hr0 : (r : 𝔸) ≠ 0 := by exact_mod_cast (by linarith : r ≠ 0)
        exact mul_left_cancel₀ hr0 hst
      · rintro _ ⟨t, rfl⟩
        rw [← hp]
        exact hzero _ (hline r hr t)
    rw [hp, hp0, eval_zero]
  
  have h2 (a : 𝔸) (ha : a ≠ 0) (h : 𝔸) : f ![a, h] = 0 := by
    obtain ⟨p, hp⟩ := exists_poly_comp (φ := fun t => ![a, t]) (fun i => by
      fin_cases i
      · exact ⟨C a, fun t => by simp⟩
      · exact ⟨X, fun t => by simp⟩) hf
    have hp0 : p = 0 := by
      apply poly_eq_zero_of_infinite (s := (fun r : {r : ℚ // 1 < r} => κ r * a) '' Set.univ)
      · refine Set.Infinite.image (fun r _ s _ hrs => Subtype.ext (hκ r s r.property s.property
          (mul_right_cancel₀ ha hrs))) ?_
        have : Infinite {r : ℚ // 1 < r} :=
          Infinite.of_injective (fun n : ℕ => (⟨n + 2, by linarith [n.cast_nonneg (α := ℚ)]⟩ :
            {r : ℚ // 1 < r})) (fun m n h => by
              have := congrArg Subtype.val h
              simpa using this)
        exact Set.infinite_univ
      · rintro _ ⟨r, -, rfl⟩
        rw [← hp]
        exact h1 r r.property a
    rw [hp, hp0, eval_zero]
  
  have h3 (a h : 𝔸) : f ![a, h] = 0 := by
    by_cases ha : a = 0
    · obtain ⟨p, hp⟩ := exists_poly_comp (φ := fun t => ![t, h]) (fun i => by
        fin_cases i
        · exact ⟨X, fun t => by simp⟩
        · exact ⟨C h, fun t => by simp⟩) hf
      have hp0 : p = 0 := by
        apply poly_eq_zero_of_infinite (s := {t : 𝔸 | t ≠ 0})
        · exact (Set.infinite_univ.sdiff (Set.finite_singleton (0 : 𝔸))).mono fun t ht => ht.2
        · intro t ht
          rw [← hp]
          exact h2 t ht h
      rw [hp, hp0, eval_zero]
    · exact h2 a ha h
  funext z
  have hz : z = ![z 0, z 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hz]
  exact h3 (z 0) (z 1)

end Parish173.Template

end
end

-- Erdos173.Template.Branches
section
noncomputable section

namespace Parish173.Template

open Polynomial

private def Gen (P : (Fin 2 → 𝔸) → Prop) : Prop :=
  ∃ g ∈ polyFuns 𝔸 (Fin 2), g ≠ 0 ∧ ∀ z ∈ Ω, g z ≠ 0 → P z

lemma Gen.mono {P P' : (Fin 2 → 𝔸) → Prop} (h : Gen P) (hP : ∀ z ∈ Ω, P z → P' z) : Gen P' := by
  obtain ⟨g, hg, hg0, hP0⟩ := h
  exact ⟨g, hg, hg0, fun z hz hgz => hP z hz (hP0 z hz hgz)⟩

lemma Gen.and {P P' : (Fin 2 → 𝔸) → Prop} (h : Gen P) (h' : Gen P') : Gen fun z => P z ∧ P' z := by
  obtain ⟨g, hg, hg0, hP⟩ := h
  obtain ⟨g', hg', hg0', hP'⟩ := h'
  refine ⟨fun z => g z * g' z, mul_mem_polyFuns hg hg', fun he => ?_, fun z hz hgz => ?_⟩
  · rcases eq_zero_or_eq_zero_of_mul_eq_zero hg hg' he with h | h
    · exact hg0 h
    · exact hg0' h
  · exact ⟨hP z hz (left_ne_zero_of_mul hgz), hP' z hz (right_ne_zero_of_mul hgz)⟩

lemma Gen.zariskiDense {P : (Fin 2 → 𝔸) → Prop} (h : Gen P) : ZariskiDense {z | P z} := by
  obtain ⟨g, hg, hg0, hP⟩ := h
  exact (zariskiDense_Ω.inter hg hg0).mono fun z hz => hP z hz.1 hz.2

lemma Gen.poly_eq_zero {p : 𝔸[X]} (h : Gen fun z => p.eval (z 0) = 0) : p = 0 := by
  have hz := h.zariskiDense _ (eval_coord_mem_polyFuns p 0) fun z hz => hz
  exact poly_eq_zero_of_forall fun a => by simpa using congrFun hz (fun _ => a)

private structure CauchyFrame where
  
  T : ℂ
  
  d : ℕ
  
  n : ℕ
  
  Q : Finset ℂ
  
  b : Fin d → ℂ
  
  s : Fin n → ℂ
  
  κ : 𝔸[X]
  
  p : Q → Fin n → Fin d → 𝔸[X]
  
  U : Set ℂ
  
  norm_T : ‖T‖ = 1
  
  κ_ne : κ ≠ 0
  
  coord : ∀ (j : Q) k, aeval T κ * ((j : ℂ) * s k) = ∑ l, aeval T (p j k l) * b l
  
  det_ne : ∀ (j : Q) (e : Fin d ↪ Fin n), (Matrix.of fun i l => p j (e i) l).det ≠ 0
  
  card_lt : Fintype.card Q * (d - 1) < n
  
  s_mem : ∀ k, s k ∈ U
  
  mul_mem : ∀ z ∈ Ω, ∀ u ∈ U, u * ((z 0 : ℂ) * (1 + (z 1 : ℂ) / (T - z 0))) ∈ U

namespace CauchyFrame

variable (𝔣 : CauchyFrame) (μ : ℂ →ₗ[𝔸] 𝔸)

private def Covered : Prop := ∀ u ∈ 𝔣.U, ∃ q ∈ 𝔣.Q, μ (q * u) = 0

private def cauchy (a : 𝔸) (l : Fin 𝔣.d) : 𝔸 := μ (𝔣.b l / (𝔣.T - a))

private def H (j : 𝔣.Q) (k : Fin 𝔣.n) (a : 𝔸) : 𝔸 := μ ((j : ℂ) * 𝔣.s k / (𝔣.T - a))

private def L (j : 𝔣.Q) (k : Fin 𝔣.n) : 𝔸 := μ ((j : ℂ) * 𝔣.s k)

private def divDiff (p : 𝔸[X]) (z : ℂ) : 𝔸[X] :=
  ∑ m ∈ Finset.range (p.natDegree + 1), ∑ i ∈ Finset.range m,
    C (p.coeff m * μ (z * 𝔣.T ^ i)) * X ^ (m - 1 - i)

lemma eval_divDiff (p : 𝔸[X]) (z : ℂ) (a : 𝔸) (hTa : 𝔣.T - a ≠ 0) :
    (𝔣.divDiff μ p z).eval a = μ (z * (aeval 𝔣.T p - ((p.eval a : 𝔸) : ℂ)) / (𝔣.T - a)) := by
  have key : z * (aeval 𝔣.T p - ((p.eval a : 𝔸) : ℂ)) / (𝔣.T - a) =
      ∑ m ∈ Finset.range (p.natDegree + 1), ∑ i ∈ Finset.range m,
        (p.coeff m * a ^ (m - 1 - i)) • (z * 𝔣.T ^ i) := by
    rw [aeval_eq_sum_range, eval_eq_sum_range]
    push_cast
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [div_eq_iff hTa, Finset.sum_mul]
    have hg := geom_sum₂_mul 𝔣.T (a : ℂ) m
    simp only [Algebra.smul_def, IntermediateField.algebraMap_apply] at *
    push_cast
    rw [show z * ((p.coeff m : ℂ) * 𝔣.T ^ m - (p.coeff m : ℂ) * (a : ℂ) ^ m) =
      z * (p.coeff m : ℂ) * (𝔣.T ^ m - (a : ℂ) ^ m) by ring, ← hg, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [key, map_sum]
  simp only [divDiff, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_smul,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  ring

lemma natDegree_divDiff_le (p : 𝔸[X]) (z : ℂ) : (𝔣.divDiff μ p z).natDegree ≤ p.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro m hm
  apply natDegree_sum_le_of_forall_le
  intro i _
  have hm : m ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

private def D (j : 𝔣.Q) (k : Fin 𝔣.n) : 𝔸[X] :=
  ∑ l, 𝔣.divDiff μ (𝔣.p j k l) (𝔣.b l) - 𝔣.divDiff μ 𝔣.κ ((j : ℂ) * 𝔣.s k)

lemma κ_mul_H (j : 𝔣.Q) (k : Fin 𝔣.n) (a : 𝔸) (hTa : 𝔣.T - a ≠ 0) :
    𝔣.κ.eval a * 𝔣.H μ j k a =
      ∑ l, (𝔣.p j k l).eval a * 𝔣.cauchy μ a l + (𝔣.D μ j k).eval a := by
  have hc := congrArg (fun w : ℂ => w / (𝔣.T - a)) (𝔣.coord j k)
  have h1 : aeval 𝔣.T 𝔣.κ * ((j : ℂ) * 𝔣.s k) / (𝔣.T - a) =
      𝔣.κ.eval a • ((j : ℂ) * 𝔣.s k / (𝔣.T - a)) +
        (j : ℂ) * 𝔣.s k * (aeval 𝔣.T 𝔣.κ - ((𝔣.κ.eval a : 𝔸) : ℂ)) / (𝔣.T - a) := by
    rw [smul_eq]
    ring
  have h2 : (∑ l, aeval 𝔣.T (𝔣.p j k l) * 𝔣.b l) / (𝔣.T - a) =
      ∑ l, ((𝔣.p j k l).eval a • (𝔣.b l / (𝔣.T - a)) +
        𝔣.b l * (aeval 𝔣.T (𝔣.p j k l) - (((𝔣.p j k l).eval a : 𝔸) : ℂ)) / (𝔣.T - a)) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_eq]
    ring
  rw [h1, h2] at hc
  have hμ := congrArg μ hc
  simp only [map_add, map_sum, map_smul, smul_eq_mul, Finset.sum_add_distrib] at hμ
  rw [D, eval_sub, eval_finsetSum, 𝔣.eval_divDiff μ _ _ a hTa]
  simp only [𝔣.eval_divDiff μ _ _ a hTa, H, cauchy]
  linear_combination hμ

lemma cover_single {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) {z : Fin 2 → 𝔸} (hz : z ∈ Ω)
    (k : Fin 𝔣.n) : ∃ j : 𝔣.Q, 𝔣.L μ j k + z 1 * 𝔣.H μ j k (z 0) = 0 := by
  obtain ⟨q, hq, hμ⟩ := hcov _ (𝔣.mul_mem z hz _ (𝔣.s_mem k))
  refine ⟨⟨q, hq⟩, ?_⟩
  have hTa := (Ω_unit hz 𝔣.norm_T).1
  have he : q * (𝔣.s k * ((z 0 : ℂ) * (1 + (z 1 : ℂ) / (𝔣.T - z 0)))) =
      z 0 • (q * 𝔣.s k) + (z 0 * z 1) • (q * 𝔣.s k / (𝔣.T - z 0)) := by
    simp only [smul_eq]
    push_cast
    ring
  rw [he, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hμ
  have h0 : z 0 ≠ 0 := hz.1
  have : z 0 * (𝔣.L μ ⟨q, hq⟩ k + z 1 * 𝔣.H μ ⟨q, hq⟩ k (z 0)) = 0 := by
    rw [← hμ, L, H]
    ring
  exact (mul_eq_zero.mp this).resolve_left h0

private abbrev Branch := 𝔣.Q × (Fin 𝔣.d ↪ Fin 𝔣.n)

private def M (β : 𝔣.Branch) : Matrix (Fin 𝔣.d) (Fin 𝔣.d) 𝔸[X] := Matrix.of fun i l => 𝔣.p β.1 (β.2 i) l

private def δ (β : 𝔣.Branch) : 𝔸[X] := (𝔣.M β).det

lemma δ_ne (β : 𝔣.Branch) : 𝔣.δ β ≠ 0 := 𝔣.det_ne β.1 β.2

private def R (β : 𝔣.Branch) (l : Fin 𝔣.d) : 𝔸[X] :=
  -∑ i, (𝔣.M β).adjugate l i * 𝔣.D μ β.1 (β.2 i)

private def S (β : 𝔣.Branch) (l : Fin 𝔣.d) : 𝔸[X] :=
  -∑ i, (𝔣.M β).adjugate l i * C (𝔣.L μ β.1 (β.2 i)) * 𝔣.κ

private def Z (β : 𝔣.Branch) : Set (Fin 2 → 𝔸) :=
  {z | z ∈ Ω ∧ ∀ i, 𝔣.L μ β.1 (β.2 i) + z 1 * 𝔣.H μ β.1 (β.2 i) (z 0) = 0}

lemma exists_branch (f : Fin 𝔣.n → 𝔣.Q) : ∃ β : 𝔣.Branch, ∀ i, f (β.2 i) = β.1 := by
  classical
  obtain ⟨j, hj⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card f (by simpa using 𝔣.card_lt)
  have hd : 𝔣.d ≤ (Finset.univ.filter fun x => f x = j).card := by omega
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hd
  let e : Fin 𝔣.d ↪ Fin 𝔣.n := (t.orderEmbOfFin htc).toEmbedding
  refine ⟨(j, e), fun i => ?_⟩
  have hm : e i ∈ t := Finset.orderEmbOfFin_mem t htc i
  exact (Finset.mem_filter.mp (ht hm)).2

lemma cover_branches {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) {z : Fin 2 → 𝔸} (hz : z ∈ Ω) :
    ∃ β, z ∈ 𝔣.Z μ β := by
  choose f hf using 𝔣.cover_single hcov hz
  obtain ⟨β, hβ⟩ := 𝔣.exists_branch f
  refine ⟨β, hz, fun i => ?_⟩
  have h := hf (β.2 i)
  rwa [hβ i] at h

lemma branch_formula (β : 𝔣.Branch) {z : Fin 2 → 𝔸} (hz : z ∈ 𝔣.Z μ β) (l : Fin 𝔣.d) :
    (𝔣.δ β).eval (z 0) * z 1 * 𝔣.cauchy μ (z 0) l =
      z 1 * (𝔣.R μ β l).eval (z 0) + (𝔣.S μ β l).eval (z 0) := by
  classical
  set a := z 0
  set h := z 1
  have hTa := (Ω_unit hz.1 𝔣.norm_T).1
  let Ma : Matrix (Fin 𝔣.d) (Fin 𝔣.d) 𝔸 := (evalRingHom a).mapMatrix (𝔣.M β)
  let x : Fin 𝔣.d → 𝔸 := fun l => h * 𝔣.cauchy μ a l
  have hMx : Ma.mulVec x = fun i =>
      -(𝔣.κ.eval a * 𝔣.L μ β.1 (β.2 i) + h * (𝔣.D μ β.1 (β.2 i)).eval a) := by
    funext i
    have h1 := 𝔣.κ_mul_H μ β.1 (β.2 i) a hTa
    have h2 := hz.2 i
    simp only [Ma, x, Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, M,
      Matrix.of_apply, coe_evalRingHom]
    have : ∑ l, eval a (𝔣.p β.1 (β.2 i) l) * (h * 𝔣.cauchy μ a l) =
        h * ∑ l, eval a (𝔣.p β.1 (β.2 i) l) * 𝔣.cauchy μ a l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]
    linear_combination (-h) * h1 + 𝔣.κ.eval a * h2
  have hadj := congrArg (fun v => Ma.adjugate.mulVec v) hMx
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec] at hadj
  have hl := congrFun hadj l
  have hdet : Ma.det = (𝔣.δ β).eval a := by
    rw [δ, ← coe_evalRingHom, RingHom.map_det]
  have hadjM : Ma.adjugate = (evalRingHom a).mapMatrix (𝔣.M β).adjugate := by
    rw [RingHom.map_adjugate]
  simp only [Pi.smul_apply, smul_eq_mul, hdet, x] at hl
  rw [← mul_assoc] at hl
  rw [hl, hadjM]
  simp only [R, S, eval_neg, eval_finsetSum, eval_mul, eval_C, Matrix.mulVec, dotProduct,
    RingHom.mapMatrix_apply, Matrix.map_apply, coe_evalRingHom]
  rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private def ε (β : 𝔣.Branch) : 𝔸[X] := 𝔣.δ β * 𝔣.κ

lemma ε_ne (β : 𝔣.Branch) : 𝔣.ε β ≠ 0 := mul_ne_zero (𝔣.δ_ne β) 𝔣.κ_ne

private def V (β : 𝔣.Branch) (j : 𝔣.Q) (k : Fin 𝔣.n) : 𝔸[X] :=
  ∑ l, 𝔣.p j k l * 𝔣.R μ β l + 𝔣.δ β * 𝔣.D μ j k

private def W (β : 𝔣.Branch) (j : 𝔣.Q) (k : Fin 𝔣.n) : 𝔸[X] := ∑ l, 𝔣.p j k l * 𝔣.S μ β l

lemma branch_H (β : 𝔣.Branch) {z : Fin 2 → 𝔸} (hz : z ∈ 𝔣.Z μ β) (j : 𝔣.Q) (k : Fin 𝔣.n) :
    (𝔣.ε β).eval (z 0) * z 1 * 𝔣.H μ j k (z 0) =
      z 1 * (𝔣.V μ β j k).eval (z 0) + (𝔣.W μ β j k).eval (z 0) := by
  have hTa := (Ω_unit hz.1 𝔣.norm_T).1
  have h1 := 𝔣.κ_mul_H μ j k (z 0) hTa
  have h2 (l : Fin 𝔣.d) := 𝔣.branch_formula μ β hz l
  simp only [ε, V, W, eval_mul, eval_add, eval_finsetSum]
  calc (𝔣.δ β).eval (z 0) * 𝔣.κ.eval (z 0) * z 1 * 𝔣.H μ j k (z 0)
      = (𝔣.δ β).eval (z 0) * z 1 * (𝔣.κ.eval (z 0) * 𝔣.H μ j k (z 0)) := by ring
    _ = ∑ l, (𝔣.p j k l).eval (z 0) * ((𝔣.δ β).eval (z 0) * z 1 * 𝔣.cauchy μ (z 0) l) +
          z 1 * ((𝔣.δ β).eval (z 0) * (𝔣.D μ j k).eval (z 0)) := by
        rw [h1, mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun l _ => by ring
        · ring
    _ = _ := by
        simp only [h2]
        have : ∑ l, (𝔣.p j k l).eval (z 0) * (z 1 * (𝔣.R μ β l).eval (z 0) +
            (𝔣.S μ β l).eval (z 0)) = z 1 * ∑ l, (𝔣.p j k l).eval (z 0) * (𝔣.R μ β l).eval (z 0) +
            ∑ l, (𝔣.p j k l).eval (z 0) * (𝔣.S μ β l).eval (z 0) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [this]
        ring

omit 𝔣 μ in

lemma double_coefficients {εβ εγ Vβ Wβ Vγ Wγ : 𝔸[X]} {L₀ : 𝔸} (hεβ : εβ ≠ 0) (hεγ : εγ ≠ 0)
    (hE : ∀ a h c k : 𝔸, (a - c) * εβ.eval a * εγ.eval c * L₀
      + (a - c) * εγ.eval c * (h * Vβ.eval a + Wβ.eval a)
      + (a - c) * εβ.eval a * (k * Vγ.eval c + Wγ.eval c)
      + k * εγ.eval c * (h * Vβ.eval a + Wβ.eval a)
      - h * εβ.eval a * (k * Vγ.eval c + Wγ.eval c) = 0) :
    Wβ = 0 ∧ Vβ = 0 ∧ Wγ = 0 ∧ Vγ = 0 ∧ L₀ = 0 := by
  have hWγ : Wγ = 0 := by
    have h0 : εβ * Wγ = 0 := poly_eq_zero_of_forall fun a => by
      have := hE a 1 a 0
      rw [eval_mul]
      linear_combination -this
    exact (mul_eq_zero.mp h0).resolve_left hεβ
  have hWβ : Wβ = 0 := by
    have h0 : εγ * Wβ = 0 := poly_eq_zero_of_forall fun a => by
      have := hE a 0 a 1
      rw [eval_mul]
      linear_combination this
    exact (mul_eq_zero.mp h0).resolve_left hεγ
  subst hWβ hWγ
  obtain ⟨c₀, -, hc₀⟩ := exists_eval_ne_zero hεγ ∅
  obtain ⟨a₀, -, ha₀⟩ := exists_eval_ne_zero hεβ ∅
  have hVβ : Vβ = 0 := by
    have h0 : (X - C c₀) * C (εγ.eval c₀) * Vβ = 0 := poly_eq_zero_of_forall fun a => by
      have h1 := hE a 1 c₀ 0
      have h2 := hE a 0 c₀ 0
      simp only [eval_mul, eval_sub, eval_X, eval_C, eval_zero] at h1 h2 ⊢
      linear_combination h1 - h2
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (mul_ne_zero (X_sub_C_ne_zero c₀) (C_ne_zero.mpr hc₀))
    · exact h
  have hVγ : Vγ = 0 := by
    have h0 : (C a₀ - X) * C (εβ.eval a₀) * Vγ = 0 := poly_eq_zero_of_forall fun c => by
      have h1 := hE a₀ 0 c 1
      have h2 := hE a₀ 0 c 0
      simp only [eval_mul, eval_sub, eval_X, eval_C, eval_zero] at h1 h2 ⊢
      linear_combination h1 - h2
    rcases mul_eq_zero.mp h0 with h | h
    · refine absurd h (mul_ne_zero ?_ (C_ne_zero.mpr ha₀))
      rw [← neg_sub]
      exact neg_ne_zero.mpr (X_sub_C_ne_zero a₀)
    · exact h
  refine ⟨rfl, hVβ, rfl, hVγ, ?_⟩
  have h0 : (X - C c₀) * εβ * C (εγ.eval c₀ * L₀) = 0 := poly_eq_zero_of_forall fun a => by
    have h1 := hE a 0 c₀ 0
    simp only [eval_mul, eval_sub, eval_X, eval_C, eval_zero] at h1 ⊢
    linear_combination h1
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h (mul_ne_zero (X_sub_C_ne_zero c₀) hεβ)
  · exact (mul_eq_zero.mp (C_eq_zero.mp h)).resolve_left hc₀

private def doubleForm (β γ : 𝔣.Branch) (j : 𝔣.Q) (k : Fin 𝔣.n) (w : Fin 2 ⊕ Fin 2 → 𝔸) : 𝔸 :=
  (w (.inl 0) - w (.inr 0)) * (𝔣.ε β).eval (w (.inl 0)) * (𝔣.ε γ).eval (w (.inr 0)) * 𝔣.L μ j k
  + (w (.inl 0) - w (.inr 0)) * (𝔣.ε γ).eval (w (.inr 0)) *
      (w (.inl 1) * (𝔣.V μ β j k).eval (w (.inl 0)) + (𝔣.W μ β j k).eval (w (.inl 0)))
  + (w (.inl 0) - w (.inr 0)) * (𝔣.ε β).eval (w (.inl 0)) *
      (w (.inr 1) * (𝔣.V μ γ j k).eval (w (.inr 0)) + (𝔣.W μ γ j k).eval (w (.inr 0)))
  + w (.inr 1) * (𝔣.ε γ).eval (w (.inr 0)) *
      (w (.inl 1) * (𝔣.V μ β j k).eval (w (.inl 0)) + (𝔣.W μ β j k).eval (w (.inl 0)))
  - w (.inl 1) * (𝔣.ε β).eval (w (.inl 0)) *
      (w (.inr 1) * (𝔣.V μ γ j k).eval (w (.inr 0)) + (𝔣.W μ γ j k).eval (w (.inr 0)))

lemma double_branch {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) {β γ : 𝔣.Branch}
    (hβ : ZariskiDense (𝔣.Z μ β)) (hγ : ZariskiDense (𝔣.Z μ γ)) (k : Fin 𝔣.n) :
    ∃ j, 𝔣.W μ β j k = 0 ∧ 𝔣.V μ β j k = 0 ∧ 𝔣.W μ γ j k = 0 ∧ 𝔣.V μ γ j k = 0 ∧
      𝔣.L μ j k = 0 := by
  classical
  have hg : (fun w : Fin 2 ⊕ Fin 2 → 𝔸 => w (.inl 0) - w (.inr 0)) ∈
      polyFuns 𝔸 (Fin 2 ⊕ Fin 2) := by
    repeat' (first
      | exact coord_mem_polyFuns _ | exact const_mem_polyFuns _ | exact eval_coord_mem_polyFuns _ _
      | apply add_mem_polyFuns | apply sub_mem_polyFuns | apply mul_mem_polyFuns)
  have hg0 : (fun w : Fin 2 ⊕ Fin 2 → 𝔸 => w (.inl 0) - w (.inr 0)) ≠ 0 := by
    intro h
    have := congrFun h (Sum.elim (fun _ => 1) (fun _ => 0))
    simp at this
  have hD := (hβ.prod hγ).inter hg hg0
  
  let Ex : 𝔣.Q → (Fin 2 ⊕ Fin 2 → 𝔸) → 𝔸 := fun j w =>
    𝔣.L μ j k + w (.inl 1) * 𝔣.H μ j k (w (.inl 0)) + w (.inr 1) * 𝔣.H μ j k (w (.inr 0)) +
      w (.inl 1) * w (.inr 1) * (w (.inl 0) - w (.inr 0))⁻¹ *
        (𝔣.H μ j k (w (.inl 0)) - 𝔣.H μ j k (w (.inr 0)))
  obtain ⟨j, -, hj⟩ := hD.exists_of_cover Finset.univ
      (fun j => {w | (w ∘ Sum.inl ∈ 𝔣.Z μ β ∧ w ∘ Sum.inr ∈ 𝔣.Z μ γ) ∧
        w (.inl 0) - w (.inr 0) ≠ 0 ∧ Ex j w = 0}) (by
    rintro w ⟨⟨hw1, hw2⟩, hac⟩
    have hu := 𝔣.mul_mem _ hw2.1 _ (𝔣.mul_mem _ hw1.1 _ (𝔣.s_mem k))
    obtain ⟨q, hq, hμ⟩ := hcov _ hu
    refine ⟨⟨q, hq⟩, Finset.mem_univ _, ⟨hw1, hw2⟩, hac, ?_⟩
    have hTa : 𝔣.T - (w (.inl 0) : ℂ) ≠ 0 := (Ω_unit hw1.1 𝔣.norm_T).1
    have hTc : 𝔣.T - (w (.inr 0) : ℂ) ≠ 0 := (Ω_unit hw2.1 𝔣.norm_T).1
    have hac' : (w (.inl 0) : ℂ) - w (.inr 0) ≠ 0 := by
      intro h
      apply hac
      have : w (.inl 0) = w (.inr 0) := Subtype.ext (sub_eq_zero.mp h)
      simp [this]
    have he : q * (𝔣.s k * ((w (.inl 0) : ℂ) * (1 + (w (.inl 1) : ℂ) / (𝔣.T - w (.inl 0)))) *
        ((w (.inr 0) : ℂ) * (1 + (w (.inr 1) : ℂ) / (𝔣.T - w (.inr 0))))) =
        (w (.inl 0) * w (.inr 0)) • (q * 𝔣.s k) +
        (w (.inl 0) * w (.inr 0) * w (.inl 1)) • (q * 𝔣.s k / (𝔣.T - w (.inl 0))) +
        (w (.inl 0) * w (.inr 0) * w (.inr 1)) • (q * 𝔣.s k / (𝔣.T - w (.inr 0))) +
        (w (.inl 0) * w (.inr 0) * w (.inl 1) * w (.inr 1) * (w (.inl 0) - w (.inr 0))⁻¹) •
          (q * 𝔣.s k / (𝔣.T - w (.inl 0)) - q * 𝔣.s k / (𝔣.T - w (.inr 0))) := by
      simp only [smul_eq]
      push_cast
      field_simp
      ring
    simp only [Function.comp] at hμ
    rw [he] at hμ
    simp only [map_add, map_sub, map_smul, smul_eq_mul] at hμ
    have h0 : w (.inl 0) * w (.inr 0) ≠ 0 := mul_ne_zero hw1.1.1 hw2.1.1
    change Ex ⟨q, hq⟩ w = 0
    apply (mul_eq_zero.mp _).resolve_left h0
    rw [← hμ]
    simp only [Ex, L, H]
    ring)
  have hΦ : (fun w => 𝔣.doubleForm μ β γ j k w) ∈ polyFuns 𝔸 (Fin 2 ⊕ Fin 2) := by
    unfold doubleForm
    repeat' (first
      | exact coord_mem_polyFuns _ | exact const_mem_polyFuns _ | exact eval_coord_mem_polyFuns _ _
      | apply add_mem_polyFuns | apply sub_mem_polyFuns | apply mul_mem_polyFuns)
  have hzero := hj _ hΦ (by
    rintro w ⟨⟨hw1, hw2⟩, hac, hEx⟩
    have hb := 𝔣.branch_H μ β hw1 j k
    have hc := 𝔣.branch_H μ γ hw2 j k
    simp only [Function.comp] at hb hc
    have hac' : w (.inl 0) - w (.inr 0) ≠ 0 := hac
    simp only [doubleForm]
    have hE : (w (.inl 0) - w (.inr 0)) * (𝔣.ε β).eval (w (.inl 0)) *
        (𝔣.ε γ).eval (w (.inr 0)) * Ex j w = 0 := by rw [hEx, mul_zero]
    simp only [Ex] at hE
    rw [← hb, ← hc]
    rw [← hE]
    field_simp
    ring)
  have hc := double_coefficients (𝔣.ε_ne β) (𝔣.ε_ne γ) (L₀ := 𝔣.L μ j k)
    (Vβ := 𝔣.V μ β j k) (Wβ := 𝔣.W μ β j k) (Vγ := 𝔣.V μ γ j k) (Wγ := 𝔣.W μ γ j k)
    fun a h c k' => by
      have := congrFun hzero (Sum.elim ![a, h] ![c, k'])
      simpa [doubleForm] using this
  exact ⟨j, hc⟩

lemma eq_zero_of_rows (β : 𝔣.Branch) (v : Fin 𝔣.d → 𝔸[X])
    (hv : ∀ i, ∑ l, 𝔣.p β.1 (β.2 i) l * v l = 0) : v = 0 := by
  classical
  have hM : (𝔣.M β).mulVec v = 0 := by
    funext i
    simpa [Matrix.mulVec, dotProduct, M] using hv i
  have h := congrArg (fun w => (𝔣.M β).adjugate.mulVec w) hM
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  funext l
  have hl := congrFun h l
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hl
  exact (mul_eq_zero.mp hl).resolve_left (𝔣.δ_ne β)

lemma dense_branches {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) {β γ : 𝔣.Branch}
    (hβ : ZariskiDense (𝔣.Z μ β)) (hγ : ZariskiDense (𝔣.Z μ γ)) :
    𝔣.S μ β = 0 ∧ 𝔣.δ γ • 𝔣.R μ β = 𝔣.δ β • 𝔣.R μ γ := by
  choose j hj using 𝔣.double_branch hcov hβ hγ
  obtain ⟨β', hβ'⟩ := 𝔣.exists_branch j
  have hk (i : Fin 𝔣.d) := hj (β'.2 i)
  simp only [hβ'] at hk
  refine ⟨𝔣.eq_zero_of_rows β' _ fun i => (hk i).1, ?_⟩
  rw [← sub_eq_zero]
  refine 𝔣.eq_zero_of_rows β' _ fun i => ?_
  have h1 := (hk i).2.1
  have h2 := (hk i).2.2.2.1
  simp only [V] at h1 h2
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  have e1 : ∑ l, 𝔣.p β'.1 (β'.2 i) l * (𝔣.δ γ * 𝔣.R μ β l) =
      𝔣.δ γ * ∑ l, 𝔣.p β'.1 (β'.2 i) l * 𝔣.R μ β l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e2 : ∑ l, 𝔣.p β'.1 (β'.2 i) l * (𝔣.δ β * 𝔣.R μ γ l) =
      𝔣.δ β * ∑ l, 𝔣.p β'.1 (β'.2 i) l * 𝔣.R μ γ l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e1, e2]
  linear_combination 𝔣.δ γ * h1 - 𝔣.δ β * h2

private def Δ : 𝔸[X] := ∏ β, 𝔣.δ β

lemma Δ_ne : 𝔣.Δ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun β _ => 𝔣.δ_ne β

private def adjBound : ℕ := Finset.univ.sup fun x : 𝔣.Branch × Fin 𝔣.d × Fin 𝔣.d =>
  ((𝔣.M x.1).adjugate x.2.1 x.2.2).natDegree

private def coordBound : ℕ :=
  (Finset.univ.sup fun x : 𝔣.Q × Fin 𝔣.n × Fin 𝔣.d => (𝔣.p x.1 x.2.1 x.2.2).natDegree) ⊔
    𝔣.κ.natDegree

private def degBound : ℕ := ∑ β, (𝔣.δ β).natDegree + (𝔣.adjBound + 𝔣.coordBound)

private def Tame (P : Fin 𝔣.d → 𝔸[X]) : Prop :=
  Gen fun z => ∀ l, 𝔣.Δ.eval (z 0) * 𝔣.cauchy μ (z 0) l = (P l).eval (z 0)

lemma natDegree_D_le (j : 𝔣.Q) (k : Fin 𝔣.n) : (𝔣.D μ j k).natDegree ≤ 𝔣.coordBound := by
  refine (natDegree_sub_le _ _).trans (max_le_max ?_ (𝔣.natDegree_divDiff_le μ _ _))
  refine natDegree_sum_le_of_forall_le _ _ fun l _ => (𝔣.natDegree_divDiff_le μ _ _).trans ?_
  exact Finset.le_sup (f := fun x : 𝔣.Q × Fin 𝔣.n × Fin 𝔣.d => (𝔣.p x.1 x.2.1 x.2.2).natDegree)
    (Finset.mem_univ (j, k, l))

lemma natDegree_adj_le (β : 𝔣.Branch) (l i : Fin 𝔣.d) :
    ((𝔣.M β).adjugate l i).natDegree ≤ 𝔣.adjBound := by
  unfold adjBound
  have h := Finset.le_sup (f := fun x : 𝔣.Branch × Fin 𝔣.d × Fin 𝔣.d =>
    ((𝔣.M x.1).adjugate x.2.1 x.2.2).natDegree) (Finset.mem_univ (β, l, i))
  exact h

lemma natDegree_R_le (β : 𝔣.Branch) (l : Fin 𝔣.d) :
    (𝔣.R μ β l).natDegree ≤ 𝔣.adjBound + 𝔣.coordBound := by
  rw [R, natDegree_neg]
  exact natDegree_sum_le_of_forall_le _ _ fun i _ => natDegree_mul_le.trans
    (add_le_add (𝔣.natDegree_adj_le β l i) (𝔣.natDegree_D_le μ _ _))

theorem tame_of_covered {μ : ℂ →ₗ[𝔸] 𝔸} (hcov : 𝔣.Covered μ) :
    ∃ P : Fin 𝔣.d → 𝔸[X], (∀ l, (P l).natDegree ≤ 𝔣.degBound) ∧ 𝔣.Tame μ P := by
  classical
  obtain ⟨β₀, -, hβ₀⟩ := zariskiDense_Ω.exists_of_cover Finset.univ (𝔣.Z μ)
    fun z hz => (𝔣.cover_branches hcov hz).imp fun β h => ⟨Finset.mem_univ _, h⟩
  have hg (β : 𝔣.Branch) : ∃ g ∈ polyFuns 𝔸 (Fin 2), g ≠ 0 ∧
      (¬ ZariskiDense (𝔣.Z μ β) → ∀ z ∈ 𝔣.Z μ β, g z = 0) ∧
      (ZariskiDense (𝔣.Z μ β) → ∀ z, g z ≠ 0 → (𝔣.δ β).eval (z 0) ≠ 0) := by
    by_cases hd : ZariskiDense (𝔣.Z μ β)
    · refine ⟨fun z => (𝔣.δ β).eval (z 0), eval_coord_mem_polyFuns _ 0, fun h => 𝔣.δ_ne β ?_,
        fun h => absurd hd h, fun _ z hz => hz⟩
      exact poly_eq_zero_of_forall fun a => by simpa using congrFun h (fun _ => a)
    · simp only [ZariskiDense, not_forall] at hd
      obtain ⟨g, hg, hgZ, hg0⟩ := hd
      exact ⟨g, hg, hg0, fun _ => hgZ,
        fun h => absurd h (by simpa [ZariskiDense] using ⟨g, hg, hgZ, hg0⟩)⟩
  choose g hgm hg0 hgnd hgd using hg
  obtain ⟨hG, hG0⟩ := prod_mem_ne_zero Finset.univ (fun β _ => hgm β) (fun β _ => hg0 β)
  refine ⟨fun l => (∏ β ∈ Finset.univ.erase β₀, 𝔣.δ β) * 𝔣.R μ β₀ l, fun l => ?_,
    _, hG, hG0, fun z hz hGz l => ?_⟩
  · have h1 : (∏ β ∈ Finset.univ.erase β₀, 𝔣.δ β).natDegree ≤ ∑ β, (𝔣.δ β).natDegree :=
      (natDegree_prod_le _ _).trans (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
    have h2 := 𝔣.natDegree_R_le μ β₀ l
    calc _ ≤ _ := natDegree_mul_le
      _ ≤ _ := add_le_add h1 h2
      _ = 𝔣.degBound := rfl
  have hgz (β : 𝔣.Branch) : g β z ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hGz β (Finset.mem_univ _)
  obtain ⟨β, hzβ⟩ := 𝔣.cover_branches hcov hz
  have hβ : ZariskiDense (𝔣.Z μ β) := by
    by_contra hnd
    exact hgz β (hgnd β hnd z hzβ)
  have hδ : (𝔣.δ β).eval (z 0) ≠ 0 := hgd β hβ z (hgz β)
  have hS := (𝔣.dense_branches hcov hβ hβ).1
  have hRR := congrFun (𝔣.dense_branches hcov hβ hβ₀).2 l
  have hF := 𝔣.branch_formula μ β hzβ l
  rw [hS, Pi.zero_apply, eval_zero, add_zero, mul_comm _ (z 1), mul_assoc] at hF
  have hF' := mul_left_cancel₀ (Ω_h_ne_zero hz) hF
  have hRR' := congrArg (eval (z 0)) hRR
  simp only [Pi.smul_apply, smul_eq_mul, eval_mul] at hRR'
  have hkey : (𝔣.δ β₀).eval (z 0) * 𝔣.cauchy μ (z 0) l = (𝔣.R μ β₀ l).eval (z 0) := by
    apply mul_left_cancel₀ hδ
    rw [← hRR', ← hF']
    ring
  rw [Δ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ β₀), eval_mul, eval_mul, mul_comm
    ((𝔣.δ β₀).eval _), mul_assoc, hkey]

end CauchyFrame

end Parish173.Template

end
end

-- Erdos173.Template.Annihilator
section
noncomputable section

namespace Parish173.Template

open Polynomial

namespace CauchyFrame

variable (𝔣 : CauchyFrame) (ℓ : ℂ →ₗ[𝔸] 𝔸)

private def twist (v : ℂ) : ℂ →ₗ[𝔸] 𝔸 := ℓ.comp (LinearMap.mulLeft 𝔸 v)

@[simp] lemma twist_apply (v z : ℂ) : twist ℓ v z = ℓ (v * z) := rfl

lemma covered_twist (hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U) (hcov : 𝔣.Covered ℓ)
    {v : ℂ} (hv : v ∈ 𝔣.U) : 𝔣.Covered (twist ℓ v) := by
  intro u hu
  obtain ⟨q, hq, h⟩ := hcov _ (hmul v hv u hu)
  refine ⟨q, hq, ?_⟩
  rw [twist_apply, ← h]
  ring_nf

lemma Tame.unique {μ : ℂ →ₗ[𝔸] 𝔸} {P P' : Fin 𝔣.d → 𝔸[X]} (h : 𝔣.Tame μ P)
    (h' : 𝔣.Tame μ P') : P = P' := by
  funext l
  rw [← sub_eq_zero]
  refine Gen.poly_eq_zero ((h.and h').mono fun z _ hz => ?_)
  rw [eval_sub, ← hz.1 l, ← hz.2 l, sub_self]

lemma Tame.linear {v w : ℂ} {P P' : Fin 𝔣.d → 𝔸[X]} (c : 𝔸) (h : 𝔣.Tame (twist ℓ v) P)
    (h' : 𝔣.Tame (twist ℓ w) P') : 𝔣.Tame (twist ℓ (c • v + w)) (c • P + P') := by
  refine (h.and h').mono fun z _ hz l => ?_
  simp only [cauchy, twist_apply, Pi.add_apply, Pi.smul_apply, eval_add, eval_smul,
    smul_eq_mul] at hz ⊢
  rw [add_mul, smul_mul_assoc, map_add, map_smul, smul_eq_mul, mul_add, ← hz.1 l, ← hz.2 l]
  ring

lemma Tame.zero : 𝔣.Tame (twist ℓ 0) 0 := by
  refine ⟨1, const_mem_polyFuns 1, fun h => one_ne_zero (congrFun h 0), fun z _ _ l => ?_⟩
  simp [cauchy]

lemma Tame.shift {v : ℂ} {P : Fin 𝔣.d → 𝔸[X]} (h : 𝔣.Tame (twist ℓ v) P) :
    𝔣.Tame (twist ℓ (𝔣.T * v)) (fun l => X * P l + C (ℓ (v * 𝔣.b l)) * 𝔣.Δ) := by
  refine h.mono fun z hz hP l => ?_
  have hTa := (Ω_unit hz 𝔣.norm_T).1
  have he : 𝔣.T * v * (𝔣.b l / (𝔣.T - z 0)) = v * 𝔣.b l + z 0 • (v * (𝔣.b l / (𝔣.T - z 0))) := by
    rw [smul_eq]
    field_simp
    ring
  simp only [cauchy, twist_apply] at hP ⊢
  rw [he, map_add, map_smul, smul_eq_mul, eval_add, eval_mul, eval_X, eval_mul, eval_C, ← hP l]
  ring

private def A : Submodule 𝔸 ℂ := Submodule.span 𝔸 𝔣.U

variable {𝔣 ℓ}

lemma exists_tame (hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U) (hcov : 𝔣.Covered ℓ)
    {v : ℂ} (hv : v ∈ 𝔣.A) :
    ∃ P : Fin 𝔣.d → 𝔸[X], (∀ l, (P l).natDegree ≤ 𝔣.degBound) ∧ 𝔣.Tame (twist ℓ v) P := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact 𝔣.tame_of_covered (𝔣.covered_twist ℓ hmul hcov hv)
  | zero => exact ⟨0, fun l => by simp, Tame.zero 𝔣 ℓ⟩
  | add v w _ _ hv hw =>
    obtain ⟨P, hPd, hP⟩ := hv
    obtain ⟨P', hPd', hP'⟩ := hw
    refine ⟨1 • P + P', fun l => ?_, by simpa using Tame.linear 𝔣 ℓ 1 hP hP'⟩
    simp only [one_smul, Pi.add_apply]
    exact (natDegree_add_le _ _).trans (max_le (hPd l) (hPd' l))
  | smul c v _ hv =>
    obtain ⟨P, hPd, hP⟩ := hv
    refine ⟨c • P + 0, fun l => ?_, by simpa using Tame.linear 𝔣 ℓ c hP (Tame.zero 𝔣 ℓ)⟩
    simp only [add_zero, Pi.smul_apply]
    exact (natDegree_smul_le _ _).trans (hPd l)

variable (hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U) (hcov : 𝔣.Covered ℓ)
include hmul hcov

private def tameVec (v : 𝔣.A) : Fin 𝔣.d → 𝔸[X] := Classical.choose (exists_tame hmul hcov v.property)

lemma tameVec_spec (v : 𝔣.A) :
    (∀ l, (tameVec hmul hcov v l).natDegree ≤ 𝔣.degBound) ∧
      𝔣.Tame (twist ℓ v) (tameVec hmul hcov v) :=
  Classical.choose_spec (exists_tame hmul hcov v.property)

lemma tameVec_eq {v : 𝔣.A} {P : Fin 𝔣.d → 𝔸[X]} (h : 𝔣.Tame (twist ℓ v) P) :
    tameVec hmul hcov v = P :=
  Tame.unique 𝔣 (tameVec_spec hmul hcov v).2 h

private def Φ : 𝔣.A →ₗ[𝔸] (Fin 𝔣.d → Fin (𝔣.degBound + 1) → 𝔸) where
  toFun v l m := (tameVec hmul hcov v l).coeff m
  map_add' v w := by
    have hl := Tame.linear 𝔣 ℓ 1 (tameVec_spec hmul hcov v).2 (tameVec_spec hmul hcov w).2
    rw [one_smul, one_smul] at hl
    have h' := tameVec_eq hmul hcov (v := v + w) hl
    funext l m
    change (tameVec hmul hcov (v + w) l).coeff m =
      (tameVec hmul hcov v l).coeff m + (tameVec hmul hcov w l).coeff m
    rw [h', Pi.add_apply, coeff_add]
  map_smul' c v := by
    have hl := Tame.linear 𝔣 ℓ c (tameVec_spec hmul hcov v).2 (Tame.zero 𝔣 ℓ)
    rw [add_zero, add_zero] at hl
    have h' := tameVec_eq hmul hcov (v := c • v) hl
    funext l m
    change (tameVec hmul hcov (c • v) l).coeff m = c • (tameVec hmul hcov v l).coeff m
    rw [h', Pi.smul_apply, coeff_smul]

lemma Φ_apply (v : 𝔣.A) (l : Fin 𝔣.d) (m : Fin (𝔣.degBound + 1)) :
    Φ hmul hcov v l m = (tameVec hmul hcov v l).coeff m := rfl

lemma tameVec_eq_zero {v : 𝔣.A} (hv : v ∈ LinearMap.ker (Φ hmul hcov)) :
    tameVec hmul hcov v = 0 := by
  funext l
  refine Polynomial.ext fun m => ?_
  rw [Pi.zero_apply, coeff_zero]
  by_cases hm : m ≤ 𝔣.degBound
  · have h := congrFun (congrFun (LinearMap.mem_ker.mp hv) l) ⟨m, Nat.lt_succ_of_le hm⟩
    rwa [Φ_apply] at h
  · exact coeff_eq_zero_of_natDegree_lt ((tameVec_spec hmul hcov v).1 l |>.trans_lt
      (not_le.mp hm))

variable (hTU : 𝔣.T ∈ 𝔣.U)
include hTU

omit hmul hcov hTU in

lemma T_mul_mem (hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U) (hTU : 𝔣.T ∈ 𝔣.U) {v : ℂ}
    (hv : v ∈ 𝔣.A) : 𝔣.T * v ∈ 𝔣.A := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span (hmul _ hTU _ hv)
  | zero => simp
  | add v w _ _ hv hw => rw [mul_add]; exact Submodule.add_mem _ hv hw
  | smul c v _ hv => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hv

private def τ : 𝔣.A →ₗ[𝔸] 𝔣.A := (LinearMap.mulLeft 𝔸 𝔣.T).restrict fun _ hv => T_mul_mem hmul hTU hv

omit hcov in

@[simp] lemma coe_τ (v : 𝔣.A) : ((τ hmul hTU v : 𝔣.A) : ℂ) = 𝔣.T * v := rfl

lemma tameVec_τ (v : 𝔣.A) : tameVec hmul hcov (τ hmul hTU v) =
    fun l => X * tameVec hmul hcov v l + C (ℓ (v * 𝔣.b l)) * 𝔣.Δ :=
  tameVec_eq hmul hcov (Tame.shift 𝔣 ℓ (tameVec_spec hmul hcov v).2)

lemma Λ_eq_zero {v : 𝔣.A} (hv : v ∈ LinearMap.ker (Φ hmul hcov)) (l : Fin 𝔣.d) :
    ℓ (v * 𝔣.b l) = 0 := by
  by_contra hne
  have hv0 := tameVec_eq_zero hmul hcov hv
  have key : ∀ m : ℕ, ∃ Q : 𝔸[X], Q ≠ 0 ∧ Q.natDegree = m ∧
      tameVec hmul hcov (((τ hmul hTU) ^ (m + 1)) v) l = 𝔣.Δ * Q := by
    intro m
    induction m with
    | zero =>
      refine ⟨C (ℓ (v * 𝔣.b l)), C_ne_zero.mpr hne, natDegree_C _, ?_⟩
      rw [zero_add, pow_one, tameVec_τ, hv0]
      simp only [Pi.zero_apply, mul_zero, zero_add]
      ring
    | succ m ih =>
      obtain ⟨Q, hQ, hQd, hQe⟩ := ih
      set c := ℓ ((((τ hmul hTU) ^ (m + 1)) v : 𝔣.A) * 𝔣.b l)
      refine ⟨X * Q + C c, ?_, ?_, ?_⟩
      · intro h
        have := congrArg natDegree h
        rw [natDegree_add_C, natDegree_X_mul hQ, natDegree_zero] at this
        omega
      · rw [natDegree_add_C, natDegree_X_mul hQ, hQd]
      · rw [pow_succ', Module.End.mul_apply, tameVec_τ]
        dsimp only
        rw [hQe]
        ring
  obtain ⟨Q, hQ, hQd, hQe⟩ := key (𝔣.degBound + 1)
  have hb := (tameVec_spec hmul hcov (((τ hmul hTU) ^ (𝔣.degBound + 2)) v)).1 l
  rw [hQe, natDegree_mul 𝔣.Δ_ne hQ, hQd] at hb
  omega

lemma ker_Φ_stable :
    LinearMap.ker (Φ hmul hcov) ≤ (LinearMap.ker (Φ hmul hcov)).comap (τ hmul hTU) := by
  intro v hv
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  have h : tameVec hmul hcov (τ hmul hTU v) = 0 := by
    rw [tameVec_τ, tameVec_eq_zero hmul hcov hv]
    funext l
    simp [Λ_eq_zero hmul hcov hTU hv l]
  funext l m
  rw [Φ_apply, h]
  rfl

omit hcov in

lemma pow_τ (n : ℕ) (v : 𝔣.A) : ((((τ hmul hTU) ^ n) v : 𝔣.A) : ℂ) = 𝔣.T ^ n * v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, coe_τ, ih]
    ring

omit hcov in

lemma aeval_τ (p : 𝔸[X]) (v : 𝔣.A) : ((aeval (τ hmul hTU) p v : 𝔣.A) : ℂ) = aeval 𝔣.T p * v := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply,
    Submodule.coe_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Submodule.coe_smul, pow_τ, smul_eq, smul_eq]
  ring

theorem exists_annihilator :
    ∃ p : 𝔸[X], p ≠ 0 ∧ ∀ v ∈ 𝔣.A, ∀ l, ℓ (aeval 𝔣.T p * v * 𝔣.b l) = 0 := by
  classical
  set K := LinearMap.ker (Φ hmul hcov)
  have hstab := ker_Φ_stable hmul hcov hTU
  let τq := K.mapQ K (τ hmul hTU) hstab
  have : FiniteDimensional 𝔸 (𝔣.A ⧸ K) :=
    LinearEquiv.finiteDimensional (LinearMap.quotKerEquivRange (Φ hmul hcov)).symm
  have hpow (n : ℕ) (v : 𝔣.A) : (τq ^ n) (K.mkQ v) = K.mkQ (((τ hmul hTU) ^ n) v) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      rfl
  have hcomm (p : 𝔸[X]) (v : 𝔣.A) :
      aeval τq p (K.mkQ v) = K.mkQ (aeval (τ hmul hTU) p v) := by
    rw [aeval_eq_sum_range, aeval_eq_sum_range, LinearMap.sum_apply,
      LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hpow, map_smul]
  refine ⟨τq.charpoly, τq.charpoly_monic.ne_zero, fun v hv l => ?_⟩
  have hmem : aeval (τ hmul hTU) τq.charpoly ⟨v, hv⟩ ∈ K := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, ← hcomm,
      LinearMap.aeval_self_charpoly]
    rfl
  have h := Λ_eq_zero hmul hcov hTU hmem l
  rwa [aeval_τ] at h

end CauchyFrame

end Parish173.Template

end
end

-- Erdos173.Template.CayleyEscape
section
noncomputable section

namespace Parish173.Template

open Polynomial

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

lemma reciprocal_denominator (b : R) (hb : IsIntegral K b) :
    ∃ (P : K[X]) (Rp : R[X]), P.coeff 0 = 1 ∧
      (1 - C b * X) * Rp = P.map (algebraMap K R) ∧
      ∀ t : K, IsUnit (1 - b * algebraMap K R t) → P.eval t ≠ 0 := by
  set m := minpoly K b with hm_def
  have hm : m.Monic := minpoly.monic hb
  set n := m.natDegree
  let P : K[X] := ∑ k ∈ Finset.range (n + 1), C (m.coeff k) * X ^ (n - k)
  let Rp : R[X] := ∑ k ∈ Finset.range (n + 1),
    C (algebraMap K R (m.coeff k)) * X ^ (n - k) * ∑ i ∈ Finset.range k, (C b * X) ^ i
  have hP0 : P.coeff 0 = 1 := by
    simp only [P, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single n]
    · rw [if_pos (by omega)]
      exact hm.coeff_natDegree
    · intro k hk hkn
      have : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [if_neg (by omega)]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  refine ⟨P, Rp, hP0, ?_, ?_⟩
  · have hz : ∑ k ∈ Finset.range (n + 1), algebraMap K R (m.coeff k) * b ^ k = 0 := by
      have h := minpoly.aeval K b
      rw [← hm_def, aeval_eq_sum_range] at h
      simpa only [Algebra.smul_def] using h
    calc (1 - C b * X) * Rp
        = ∑ k ∈ Finset.range (n + 1), (C (algebraMap K R (m.coeff k)) * X ^ (n - k) -
            C (algebraMap K R (m.coeff k) * b ^ k) * X ^ n) := by
          simp only [Rp]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k hk => ?_
          have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have he : (1 - C b * X) * (C (algebraMap K R (m.coeff k)) * X ^ (n - k) *
              ∑ i ∈ Finset.range k, (C b * X) ^ i) =
              C (algebraMap K R (m.coeff k)) * X ^ (n - k) *
                ((1 - C b * X) * ∑ i ∈ Finset.range k, (C b * X) ^ i) := by ring
          rw [he, mul_neg_geom_sum, map_mul, map_pow]
          have hX : (X : R[X]) ^ n = X ^ (n - k) * X ^ k := by
            rw [← pow_add, Nat.sub_add_cancel hk]
          rw [hX]
          ring
      _ = P.map (algebraMap K R) - C (∑ k ∈ Finset.range (n + 1),
            algebraMap K R (m.coeff k) * b ^ k) * X ^ n := by
          rw [Finset.sum_sub_distrib, map_sum, Finset.sum_mul]
          simp [P, Polynomial.map_sum]
      _ = P.map (algebraMap K R) := by rw [hz, map_zero, zero_mul, sub_zero]
  · intro t ht hP
    by_cases ht0 : t = 0
    · subst t
      rw [← coeff_zero_eq_eval_zero, hP0] at hP
      exact one_ne_zero hP
    have hroot : m.IsRoot t⁻¹ := by
      have he : P.eval t = t ^ n * m.eval t⁻¹ := by
        simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
        rw [eval_eq_sum_range, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [inv_pow, pow_sub₀ _ ht0 hk]
        ring
      rw [he] at hP
      exact (mul_eq_zero.mp hP).resolve_left (pow_ne_zero _ ht0)
    have hdiv := mul_divByMonic_eq_iff_isRoot.mpr hroot
    set g := m /ₘ (X - C t⁻¹)
    have hg : aeval b g = 0 := by
      have h := minpoly.aeval K b
      rw [← hm_def, ← hdiv, map_mul] at h
      have hu : IsUnit (aeval b (X - C t⁻¹)) := by
        have hti : algebraMap K R t⁻¹ * algebraMap K R t = 1 := by
          rw [← map_mul, inv_mul_cancel₀ ht0, map_one]
        have he : aeval b (X - C t⁻¹) = algebraMap K R (-t⁻¹) * (1 - b * algebraMap K R t) := by
          simp only [map_sub, aeval_X, aeval_C, map_neg]
          linear_combination (-b) * hti
        rw [he]
        exact ((isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr (inv_ne_zero ht0))).map
          (algebraMap K R)).mul ht
      exact (hu.mul_right_eq_zero).mp h
    have hm0 : m ≠ 0 := hm.ne_zero
    have hg0 : g ≠ 0 := by
      intro h
      rw [h, mul_zero] at hdiv
      exact hm0 hdiv.symm
    have hle := minpoly.degree_le_of_ne_zero K b hg0 hg
    have hlt := degree_divByMonic_lt m (X - C t⁻¹) hm0 (by rw [degree_X_sub_C]; exact one_pos)
    exact absurd (hle.trans_lt hlt) (lt_irrefl _)

private def polyLinear (ℓ : R →ₗ[K] K) (p : R[X]) : K[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange ℓ (map_zero ℓ)))

@[simp] lemma coeff_polyLinear (ℓ : R →ₗ[K] K) (p : R[X]) (n : ℕ) :
    (polyLinear ℓ p).coeff n = ℓ (p.coeff n) := rfl

lemma polyLinear_add (ℓ : R →ₗ[K] K) (p q : R[X]) :
    polyLinear ℓ (p + q) = polyLinear ℓ p + polyLinear ℓ q := by
  ext n
  simp only [coeff_polyLinear, coeff_add, map_add]

lemma polyLinear_monomial (ℓ : R →ₗ[K] K) (n : ℕ) (a : R) :
    polyLinear ℓ (monomial n a) = monomial n (ℓ a) := by
  ext k
  simp only [coeff_polyLinear, coeff_monomial]
  split_ifs <;> simp

lemma eval_polyLinear (ℓ : R →ₗ[K] K) (p : R[X]) (t : K) :
    (polyLinear ℓ p).eval t = ℓ (p.eval (algebraMap K R t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [polyLinear_add, eval_add, hp, hq, map_add]
  | monomial n a =>
    rw [polyLinear_monomial, eval_monomial, eval_monomial]
    have he : a * (algebraMap K R t) ^ n = (t ^ n) • a := by
      rw [Algebra.smul_def, map_pow, mul_comm]
    rw [he, map_smul]
    exact mul_comm _ _

variable [CharZero K]

lemma eq_zero_of_forall_rat {p : K[X]} (hp : ∀ t : ℚ, p.eval (t : K) = 0) : p = 0 :=
  p.eq_zero_of_infinite_isRoot ((Set.infinite_range_of_injective
    (Rat.cast_injective (α := K))).mono fun x hx => by
      obtain ⟨t, rfl⟩ := hx
      exact hp t)

lemma cayley_annihilation (b : R) (hb : IsIntegral K b) (ℓ : R →ₗ[K] K)
    (hd : ∀ t : ℚ, IsUnit (1 - b * algebraMap K R t))
    (h : ∀ t : ℚ, ∀ u, (1 - b * algebraMap K R t) * u = 1 + b * algebraMap K R t → ℓ u = 0) :
    ℓ 1 = 0 ∧ ℓ b = 0 ∧ ℓ (b ^ 2) = 0 := by
  obtain ⟨P, Rp, hP, hR, hPreg⟩ := reciprocal_denominator (K := K) b hb
  have hR' : Rp - (C b * Rp) * X = P.map (algebraMap K R) := by
    rw [← hR]
    ring
  let T := Rp + (C b * Rp) * X
  have hT : polyLinear ℓ T = 0 := by
    apply eq_zero_of_forall_rat
    intro t
    rw [eval_polyLinear]
    have hRt := congrArg (Polynomial.eval (algebraMap K R t)) hR
    simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
    have hPt := hPreg t (hd t)
    have hu : (1 - b * algebraMap K R t) * ((P.eval (t : K))⁻¹ • T.eval (algebraMap K R t)) =
        1 + b * algebraMap K R t := by
      rw [mul_smul_comm]
      have he : (1 - b * algebraMap K R t) * T.eval (algebraMap K R t) =
          (1 + b * algebraMap K R t) * algebraMap K R (P.eval (t : K)) := by
        simp only [T, eval_add, eval_mul, eval_C, eval_X]
        rw [← hRt]
        ring
      rw [he, Algebra.smul_def, ← mul_assoc, mul_comm (algebraMap K R _), mul_assoc, ← map_mul,
        inv_mul_cancel₀ hPt, map_one, mul_one]
    have h0 := h t _ hu
    rw [map_smul, smul_eq_mul] at h0
    exact (mul_eq_zero.mp h0).resolve_left (inv_ne_zero hPt)
  have h0 : Rp.coeff 0 = 1 := by
    have he := congrArg (fun p : R[X] => p.coeff 0) hR'
    simpa only [coeff_sub, coeff_mul_X_zero, sub_zero, coeff_map, hP, map_one] using he
  have h1 : Rp.coeff 1 - b = algebraMap K R (P.coeff 1) := by
    have he := congrArg (fun p : R[X] => p.coeff 1) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, h0, mul_one, coeff_map] using he
  have h2 : Rp.coeff 2 - b * Rp.coeff 1 = algebraMap K R (P.coeff 2) := by
    have he := congrArg (fun p : R[X] => p.coeff 2) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, coeff_map] using he
  have ht0 : ℓ 1 = 0 := by
    have he := congrArg (fun p : K[X] => p.coeff 0) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X_zero, add_zero, h0, coeff_zero] using he
  have ht1 : ℓ (Rp.coeff 1) + ℓ b = 0 := by
    have he := congrArg (fun p : K[X] => p.coeff 1) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul, h0, mul_one,
      map_add, coeff_zero] using he
  have ht2 : ℓ (Rp.coeff 2) + ℓ (b * Rp.coeff 1) = 0 := by
    have he := congrArg (fun p : K[X] => p.coeff 2) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul,
      map_add, coeff_zero] using he
  have hlK (c : K) : ℓ (algebraMap K R c) = 0 := by
    have he : algebraMap K R c = c • (1 : R) := by rw [Algebra.smul_def, mul_one]
    rw [he, map_smul, ht0, smul_zero]
  have hh1 := congrArg ℓ h1
  rw [map_sub, hlK] at hh1
  have hb0 : ℓ b = 0 := by
    have h2b : (2 : K) * ℓ b = 0 := by linear_combination ht1 - hh1
    exact (mul_eq_zero.mp h2b).resolve_left two_ne_zero
  have hh2 := congrArg ℓ h2
  rw [map_sub, hlK] at hh2
  have hbR : ℓ (b * Rp.coeff 1) = 0 := by
    have h2b : (2 : K) * ℓ (b * Rp.coeff 1) = 0 := by linear_combination ht2 - hh2
    exact (mul_eq_zero.mp h2b).resolve_left two_ne_zero
  have hR1 : Rp.coeff 1 = algebraMap K R (P.coeff 1) + b := sub_eq_iff_eq_add.mp h1
  rw [hR1, mul_add, map_add] at hbR
  have he : b * algebraMap K R (P.coeff 1) = (P.coeff 1) • b := by
    rw [Algebra.smul_def, mul_comm]
  rw [he, map_smul, hb0, smul_zero, zero_add, ← sq] at hbR
  exact ⟨ht0, hb0, hbR⟩

omit [CharZero K] in

lemma linearFraction_polynomials [Algebra.IsIntegral K R] (A B C' D : R) (ℓ : R →ₗ[K] K)
    (hd : ∀ t : ℚ, IsUnit (C' + D * algebraMap K R t)) :
    ∃ P Q : K[X], ∀ t : ℚ, Q.eval (t : K) ≠ 0 ∧ ∀ u : R,
      (C' + D * algebraMap K R t) * u = A + B * algebraMap K R t →
        P.eval (t : K) = Q.eval (t : K) * ℓ u := by
  have hC : IsUnit C' := by simpa using hd 0
  obtain ⟨c, hc⟩ := hC
  let ci : R := ↑c⁻¹
  have hcc : C' * ci = 1 := by rw [← hc]; exact c.mul_inv
  let b := -(D * ci)
  have hfac (t : ℚ) : C' + D * algebraMap K R t = C' * (1 - b * algebraMap K R t) := by
    have : C' + D * algebraMap K R t = C' + (C' * ci) * D * algebraMap K R t := by
      rw [hcc, one_mul]
    rw [this]
    ring
  obtain ⟨Q, Rp, -, hR, hQreg⟩ := reciprocal_denominator (K := K) b
    (Algebra.IsIntegral.isIntegral b)
  have hdn (t : ℚ) : IsUnit (1 - b * algebraMap K R t) := by
    have h := hd t
    rw [hfac] at h
    exact isUnit_of_mul_isUnit_right h
  let U : R[X] := (Polynomial.C (ci * A) + Polynomial.C (ci * B) * X) * Rp
  refine ⟨polyLinear ℓ U, Q, fun t => ⟨hQreg t (hdn t), fun u hu => ?_⟩⟩
  rw [eval_polyLinear]
  have hRt := congrArg (Polynomial.eval (algebraMap K R t)) hR
  simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
  have he : U.eval (algebraMap K R t) = (Q.eval (t : K)) • u := by
    simp only [U, eval_mul, eval_add, eval_C, eval_X, Algebra.smul_def]
    rw [← hRt]
    have hu' : ci * (A + B * algebraMap K R t) = (1 - b * algebraMap K R t) * u := by
      rw [← hu, hfac, ← mul_assoc, ← mul_assoc, mul_comm ci C', hcc, one_mul]
    calc (ci * A + ci * B * algebraMap K R t) * Rp.eval (algebraMap K R t)
        = (ci * (A + B * algebraMap K R t)) * Rp.eval (algebraMap K R t) := by ring
      _ = _ := by rw [hu']; ring
  rw [he, map_smul, smul_eq_mul]

lemma rational_functions_avoid {α : Type*} (s : Finset α) (f : α → ℚ → K)
    (hpoly : ∀ i ∈ s, ∃ P Q : K[X], ∀ t : ℚ, Q.eval (t : K) ≠ 0 ∧
      P.eval (t : K) = Q.eval (t : K) * f i t)
    (hn : ∀ i ∈ s, ∃ t, f i t ≠ 0) :
    ∃ t, ∀ i ∈ s, f i t ≠ 0 := by
  classical
  choose P Q hQ using fun i : s => hpoly i i.property
  have hP (i : s) : P i ≠ 0 := by
    obtain ⟨t, ht⟩ := hn i i.property
    intro he
    have hh := (hQ i t).2
    rw [he, eval_zero] at hh
    exact mul_ne_zero (hQ i t).1 ht hh.symm
  have hz : (∏ i : s, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => hP _)
  obtain ⟨t, ht⟩ : ∃ t : ℚ, (∏ i : s, P i).eval (t : K) ≠ 0 := by
    by_contra! hn
    exact hz (eq_zero_of_forall_rat hn)
  refine ⟨t, fun i hi hh => ?_⟩
  have hpt : (P ⟨i, hi⟩).eval (t : K) ≠ 0 := by
    rw [eval_prod] at ht
    exact Finset.prod_ne_zero_iff.mp ht _ (Finset.mem_univ _)
  apply hpt
  rw [(hQ ⟨i, hi⟩ t).2, hh, mul_zero]

lemma finite_hyperplanes_avoid {T : Type*} [Nonempty T]
    (f : T → R) (line : T → T → ℚ → T)
    (hzero : ∀ a b, line a b 0 = a) (hone : ∀ a b, line a b 1 = b)
    (hline : ∀ a b (ℓ : R →ₗ[K] K), ∃ P Q : K[X], ∀ t : ℚ,
      Q.eval (t : K) ≠ 0 ∧ P.eval (t : K) = Q.eval (t : K) * ℓ (f (line a b t)))
    (s : Finset (R →ₗ[K] K)) (hs : ∀ ℓ ∈ s, ∃ t, ℓ (f t) ≠ 0) :
    ∃ t, ∀ ℓ ∈ s, ℓ (f t) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary T, by simp⟩
  | @insert ℓ s hℓ ih =>
    obtain ⟨a, ha⟩ := ih (fun ψ hψ => hs ψ (Finset.mem_insert_of_mem hψ))
    obtain ⟨b, hb⟩ := hs ℓ (Finset.mem_insert_self _ _)
    obtain ⟨t, ht⟩ := rational_functions_avoid (insert ℓ s)
      (fun ψ t => ψ (f (line a b t))) (fun ψ _ => hline a b ψ) (by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · exact ⟨1, by simpa only [hone] using hb⟩
        · exact ⟨0, by simpa only [hzero] using ha ψ hψ⟩)
    exact ⟨line a b t, ht⟩

private structure RealStructure (K R : Type*) [Field K] [CommRing R] [Algebra K R] where
  
  ι : R
  
  Re : Set R
  
  ι_sq : ι * ι = -1
  
  one_mem : (1 : R) ∈ Re
  
  add_mem : ∀ r ∈ Re, ∀ s ∈ Re, r + s ∈ Re
  
  smul_mem : ∀ t : ℚ, ∀ r ∈ Re, algebraMap K R t * r ∈ Re
  
  isUnit : ∀ r ∈ Re, IsUnit (1 - ι * r)

namespace RealStructure

variable (S : RealStructure K R)

private def cay (r : S.Re) : R := (1 + S.ι * r) * ↑(S.isUnit r r.property).unit⁻¹

omit [CharZero K] in

lemma cay_spec (r : S.Re) : (1 - S.ι * r) * S.cay r = 1 + S.ι * r := by
  rw [cay, mul_left_comm, IsUnit.mul_val_inv, mul_one]

omit [CharZero K] in

lemma cay_unique (r : S.Re) {u : R} (hu : (1 - S.ι * r) * u = 1 + S.ι * r) : u = S.cay r := by
  have h := (S.isUnit r r.property)
  calc u = ↑h.unit⁻¹ * ((1 - S.ι * r) * u) := by
        rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
    _ = S.cay r := by rw [hu, cay, mul_comm]

private def line (a b : S.Re) (t : ℚ) : S.Re :=
  ⟨(a : R) + algebraMap K R t * ((b : R) + algebraMap K R (-1 : ℚ) * a),
    S.add_mem _ a.property _
      (S.smul_mem t _ (S.add_mem _ b.property _ (S.smul_mem _ _ a.property)))⟩

omit [CharZero K] in

lemma line_zero (a b : S.Re) : S.line a b 0 = a := by
  ext
  simp [line]

omit [CharZero K] in

lemma line_one (a b : S.Re) : S.line a b 1 = b := by
  ext
  simp [line]

variable [Algebra.IsIntegral K R]

omit [CharZero K] in

lemma cay_line_polynomials (a b : S.Re) (ℓ : R →ₗ[K] K) :
    ∃ P Q : K[X], ∀ t : ℚ, Q.eval (t : K) ≠ 0 ∧
      P.eval (t : K) = Q.eval (t : K) * ℓ (S.cay (S.line a b t)) := by
  set w : R := (b : R) + algebraMap K R (-1 : ℚ) * a
  have hl (t : ℚ) : (S.line a b t : R) = a + algebraMap K R t * w := rfl
  obtain ⟨P, Q, hPQ⟩ := linearFraction_polynomials (1 + S.ι * a) (S.ι * w) (1 - S.ι * a)
    (-(S.ι * w)) ℓ (fun t => by
      have h := S.isUnit _ (S.line a b t).property
      rw [hl] at h
      convert h using 1
      ring)
  refine ⟨P, Q, fun t => ⟨(hPQ t).1, (hPQ t).2 _ ?_⟩⟩
  have h := S.cay_spec (S.line a b t)
  rw [hl] at h
  rw [← sub_eq_zero] at h ⊢
  rw [← h]
  ring

lemma cay_functional_escape (hspan : ∀ ℓ : R →ₗ[K] K,
      (∀ r ∈ S.Re, ℓ r = 0 ∧ ℓ (S.ι * r) = 0) → ℓ = 0)
    (ℓ : R →ₗ[K] K) (hℓ : ℓ ≠ 0) : ∃ r : S.Re, ℓ (S.cay r) ≠ 0 := by
  by_contra! hh
  have hx (r : R) (hr : r ∈ S.Re) : ℓ 1 = 0 ∧ ℓ (S.ι * r) = 0 ∧ ℓ (r ^ 2) = 0 := by
    have hrt (t : ℚ) : algebraMap K R t * r ∈ S.Re := S.smul_mem t r hr
    have he (t : ℚ) : S.ι * (algebraMap K R t * r) = (S.ι * r) * algebraMap K R t := by ring
    obtain ⟨h1, hb, hb2⟩ := cayley_annihilation (K := K) (S.ι * r)
      (Algebra.IsIntegral.isIntegral _) ℓ
      (fun t => by rw [← he]; exact S.isUnit _ (hrt t))
      (fun t u hu => by
        have hu' : (1 - S.ι * ((⟨_, hrt t⟩ : S.Re) : R)) * u =
            1 + S.ι * ((⟨_, hrt t⟩ : S.Re) : R) := by simpa only [he] using hu
        rw [S.cay_unique ⟨_, hrt t⟩ hu']
        exact hh _)
    refine ⟨h1, hb, ?_⟩
    have hsq : (S.ι * r) ^ 2 = -(r ^ 2) := by
      rw [mul_pow, sq S.ι, S.ι_sq]
      ring
    rw [hsq, map_neg, neg_eq_zero] at hb2
    exact hb2
  have hreal (r : R) (hr : r ∈ S.Re) : ℓ r = 0 := by
    have hm : algebraMap K R (-1 : ℚ) * 1 ∈ S.Re := S.smul_mem _ _ S.one_mem
    have h1 := (hx _ (S.add_mem r hr 1 S.one_mem)).2.2
    have h2 := (hx _ (S.add_mem r hr _ hm)).2.2
    have he : (r + 1) ^ 2 - (r + algebraMap K R (-1 : ℚ) * 1) ^ 2 = (4 : K) • r := by
      simp only [Algebra.smul_def, Rat.cast_neg, Rat.cast_one, map_neg, map_one, map_ofNat]
      ring
    have hh := congrArg ℓ he
    rw [map_sub, h1, h2, sub_self, map_smul, smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left (by norm_num)
  exact hℓ (hspan ℓ fun r hr => ⟨hreal r hr, (hx r hr).2.1⟩)

lemma cay_finite_avoid (hspan : ∀ ℓ : R →ₗ[K] K,
      (∀ r ∈ S.Re, ℓ r = 0 ∧ ℓ (S.ι * r) = 0) → ℓ = 0)
    (s : Finset (R →ₗ[K] K)) (hs : ∀ ℓ ∈ s, ℓ ≠ 0) :
    ∃ r : S.Re, ∀ ℓ ∈ s, ℓ (S.cay r) ≠ 0 := by
  have : Nonempty S.Re := ⟨⟨1, S.one_mem⟩⟩
  exact finite_hyperplanes_avoid S.cay S.line S.line_zero S.line_one S.cay_line_polynomials s
    (fun ℓ hℓ => S.cay_functional_escape hspan ℓ (hs ℓ hℓ))

lemma cay_subspaces_avoid (hspan : ∀ ℓ : R →ₗ[K] K,
      (∀ r ∈ S.Re, ℓ r = 0 ∧ ℓ (S.ι * r) = 0) → ℓ = 0)
    (P : Finset (Submodule K R)) (hP : ∀ p ∈ P, p < ⊤) :
    ∃ r : S.Re, ∀ p ∈ P, S.cay r ∉ p := by
  classical
  choose ℓ hn hker using fun p : P => Submodule.exists_le_ker_of_lt_top p.val (hP p p.property)
  obtain ⟨r, hr⟩ := S.cay_finite_avoid hspan (Finset.univ.image ℓ) (by
    intro ψ hψ
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hψ
    exact hn p)
  exact ⟨r, fun p hp hx => hr (ℓ ⟨p, hp⟩)
    (Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩) (hker ⟨p, hp⟩ hx)⟩

end RealStructure

end Parish173.Template

end
end

-- Erdos173.Template.GeneralPosition
section
noncomputable section

namespace Parish173.Template

open Module

variable (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [Module K V]

private def GeneralFamily {n : ℕ} (s : Fin n → V) : Prop :=
  ∀ t : Finset (Fin n), t.card ≤ finrank K V → LinearIndepOn K s (t : Set (Fin n))

variable {K}

lemma exists_generalFamily [FiniteDimensional K V] (A : Set V)
    (ha : ∀ P : Finset (Submodule K V), (∀ p ∈ P, p < ⊤) → ∃ x ∈ A, ∀ p ∈ P, x ∉ p) (n : ℕ) :
    ∃ s : Fin n → V, (∀ i, s i ∈ A) ∧ GeneralFamily K s := by
  classical
  induction n with
  | zero =>
    refine ⟨Fin.elim0, fun i => i.elim0, fun t _ => ?_⟩
    have : t = ∅ := Finset.eq_empty_of_forall_notMem fun i => i.elim0
    simp [this, linearIndepOn_empty]
  | succ n ih =>
    obtain ⟨s, hA, hg⟩ := ih
    let B := (Finset.univ : Finset (Finset (Fin n))).filter (fun t => t.card < finrank K V)
    let P := B.image (fun t : Finset (Fin n) => Submodule.span K (s '' (t : Set (Fin n))))
    have hP : ∀ p ∈ P, p < ⊤ := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      have hc : t.card < finrank K V := (Finset.mem_filter.mp ht).2
      apply Submodule.lt_top_of_finrank_lt_finrank
      have h1 := finrank_span_finset_le_card (R := K) (t.image s)
      have h2 : (t.image s).card ≤ t.card := Finset.card_image_le
      rw [Finset.coe_image] at h1
      exact (h1.trans h2).trans_lt hc
    obtain ⟨x, hx, havoid⟩ := ha P hP
    have havo (t : Finset (Fin n)) (hc : t.card < finrank K V) :
        x ∉ Submodule.span K (s '' (t : Set (Fin n))) :=
      havoid _ (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩)
    refine ⟨Fin.snoc s x, fun i => ?_, fun t ht => ?_⟩
    · induction i using Fin.lastCases with
      | last => simpa using hx
      | cast i => simpa using hA i
    let t' := (Finset.univ : Finset (Fin n)).filter (fun i => Fin.castSucc i ∈ t)
    have hcomp : (Fin.snoc s x : Fin (n + 1) → V) ∘ Fin.castSucc = s := by
      funext i
      simp
    have himage : Fin.castSucc '' (t' : Set (Fin n)) = (t : Set (Fin (n + 1))) \ {Fin.last n} := by
      ext i
      induction i using Fin.lastCases with
      | last => simp [t', Fin.castSucc_ne_last]
      | cast i => simp [t', Fin.castSucc_ne_last]
    have hcard : t'.card + (if Fin.last n ∈ t then 1 else 0) ≤ t.card := by
      have hsub : t'.map Fin.castSuccEmb ⊆ t.erase (Fin.last n) := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last j, (Finset.mem_filter.mp hj).2⟩
      have h := Finset.card_le_card hsub
      rw [Finset.card_map] at h
      split_ifs with hl
      · rw [Finset.card_erase_of_mem hl] at h
        have := Finset.card_pos.mpr ⟨_, hl⟩
        omega
      · exact h.trans (Finset.card_erase_le)
    have hold : LinearIndepOn K (Fin.snoc s x : Fin (n + 1) → V)
        (Fin.castSucc '' (t' : Set (Fin n))) :=
      LinearIndepOn.image_of_comp _ _ (by rw [hcomp]; exact hg t' (by split_ifs at hcard <;> omega))
    by_cases hl : Fin.last n ∈ t
    · have he : (t : Set (Fin (n + 1))) =
          insert (Fin.last n) (Fin.castSucc '' (t' : Set (Fin n))) := by
        rw [himage]
        ext i
        by_cases hi : i = Fin.last n
        · subst hi
          simpa using hl
        · simp [hi]
      rw [he, linearIndepOn_insert (by rw [himage]; simp)]
      refine ⟨hold, ?_⟩
      rw [Fin.snoc_last, ← Set.image_comp, hcomp]
      exact havo t' (by rw [if_pos hl] at hcard; omega)
    · have he : (t : Set (Fin (n + 1))) = Fin.castSucc '' (t' : Set (Fin n)) := by
        rw [himage]
        ext i
        by_cases hi : i = Fin.last n
        · subst hi
          simpa using hl
        · simp [hi]
      rw [he]
      exact hold

lemma GeneralFamily.linearIndependent {n : ℕ} {s : Fin n → V} (hs : GeneralFamily K s)
    (e : Fin (finrank K V) ↪ Fin n) : LinearIndependent K (s ∘ e) := by
  classical
  have h := hs (Finset.univ.map e) (by simp)
  have hc : LinearIndependent K (fun i : ((Finset.univ.map e : Finset (Fin n)) : Set (Fin n)) =>
      s i) := h
  exact hc.comp (fun i => ⟨e i, by simp⟩) (fun i j hij => e.injective (congrArg Subtype.val hij))

end Parish173.Template

end
end

-- Erdos173.Template.FunctionField
section
noncomputable section

namespace Parish173.Template

open Polynomial IntermediateField ComplexConjugate Module

variable {T : ℂ}

lemma aeval_ne_zero (hT : Transcendental 𝔸 T) {p : 𝔸[X]} (hp : p ≠ 0) : aeval T p ≠ 0 :=
  fun h => hp (transcendental_iff.mp hT p h)

lemma exists_common_denom (hT : Transcendental 𝔸 T) {ι : Type*} [Finite ι] (g : ι → 𝔸⟮T⟯) :
    ∃ κ : 𝔸[X], κ ≠ 0 ∧ ∃ P : ι → 𝔸[X], ∀ i, aeval T κ * (g i : ℂ) = aeval T (P i) := by
  classical
  have := Fintype.ofFinite ι
  have hrep (i : ι) : ∃ r s : 𝔸[X], s ≠ 0 ∧ (g i : ℂ) = aeval T r / aeval T s := by
    obtain ⟨r, s, h⟩ := (mem_adjoin_simple_iff 𝔸 (g i : ℂ)).mp (g i).property
    by_cases hs : s = 0
    · refine ⟨0, 1, one_ne_zero, ?_⟩
      rw [h, hs]
      simp
    · exact ⟨r, s, hs, h⟩
  choose r s hs hrs using hrep
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.mpr fun i _ => hs i,
    fun i => r i * ∏ j ∈ Finset.univ.erase i, s j, fun i => ?_⟩
  rw [hrs i, map_mul, map_prod, map_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  field_simp [aeval_ne_zero hT (hs i)]

variable (N : IntermediateField 𝔸⟮T⟯ ℂ)

lemma T_mem : T ∈ N := N.algebraMap_mem (AdjoinSimple.gen 𝔸 T)

lemma coe_𝔸_mem (a : 𝔸) : (a : ℂ) ∈ N := N.algebraMap_mem (algebraMap 𝔸 𝔸⟮T⟯ a)

lemma I_mem : Complex.I ∈ N := coe_𝔸_mem N iA

private def units : Set ℂ := {u | u ∈ N ∧ ‖u‖ = 1}

variable {N}

lemma mul_mem_units {u v : ℂ} (hu : u ∈ units N) (hv : v ∈ units N) : u * v ∈ units N :=
  ⟨N.mul_mem hu.1 hv.1, by rw [norm_mul, hu.2, hv.2, one_mul]⟩

lemma conj_eq_inv {u : ℂ} (hu : ‖u‖ = 1) : conj u = u⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hu]
  simp

lemma inv_mem_units {u : ℂ} (hu : u ∈ units N) : u⁻¹ ∈ units N :=
  ⟨N.inv_mem hu.1, by rw [norm_inv, hu.2, inv_one]⟩

lemma conj_mem_units {u : ℂ} (hu : u ∈ units N) : conj u ∈ units N := by
  rw [conj_eq_inv hu.2]
  exact inv_mem_units hu

lemma one_sub_I_mul_ne {r : ℂ} (hr : r.im = 0) : 1 - Complex.I * r ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [hr] at this

lemma norm_cayley {r : ℂ} (hr : r.im = 0) :
    ‖(1 + Complex.I * r) / (1 - Complex.I * r)‖ = 1 := by
  have he : conj (1 + Complex.I * r) = 1 - Complex.I * r := by
    rw [← Complex.re_add_im r, hr]
    simp [sub_eq_add_neg]
  rw [norm_div, ← he, Complex.norm_conj, div_self]
  rw [norm_ne_zero_iff, ← (RingHom.injective (starRingEnd ℂ)).ne_iff, he, map_zero]
  exact one_sub_I_mul_ne hr

variable (N)

private def realStructure : RealStructure 𝔸⟮T⟯ N where
  ι := ⟨Complex.I, I_mem N⟩
  Re := {z | (z : ℂ).im = 0}
  ι_sq := Subtype.ext (by simp)
  one_mem := by simp
  add_mem r hr s hs := by simp_all
  smul_mem t r hr := by
    change ((algebraMap 𝔸⟮T⟯ ℂ (t : 𝔸⟮T⟯)) * (r : ℂ)).im = 0
    have : algebraMap 𝔸⟮T⟯ ℂ (t : 𝔸⟮T⟯) = (t : ℂ) := by simp
    rw [this, Complex.mul_im]
    simp [show (r : ℂ).im = 0 from hr]
  isUnit r hr := by
    refine isUnit_iff_ne_zero.mpr fun h => one_sub_I_mul_ne (r := (r : ℂ)) hr ?_
    simpa using congrArg (fun z : N => (z : ℂ)) h

lemma coe_realStructure_cay (r : (realStructure N).Re) :
    (((realStructure N).cay r : N) : ℂ) =
      (1 + Complex.I * (r : ℂ)) / (1 - Complex.I * (r : ℂ)) := by
  have h := (realStructure N).cay_spec r
  have hc := congrArg (fun z : N => (z : ℂ)) h
  simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one,
    AddMemClass.coe_add] at hc
  rw [eq_div_iff (one_sub_I_mul_ne r.property), mul_comm]
  exact hc

lemma realStructure_span
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1})
    (ℓ : N →ₗ[𝔸⟮T⟯] 𝔸⟮T⟯)
    (h : ∀ r ∈ (realStructure N).Re, ℓ r = 0 ∧ ℓ ((realStructure N).ι * r) = 0) : ℓ = 0 := by
  have hu (y : N) (hy : ‖(y : ℂ)‖ = 1) : ℓ y = 0 := by
    have hy0 : (y : ℂ) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hy
      exact zero_ne_one hy
    have hc : conj (y : ℂ) = (y : ℂ)⁻¹ := conj_eq_inv hy
    let ι : N := (realStructure N).ι
    have hι : (ι : ℂ) = Complex.I := rfl
    have h2 : ((2 : N) : ℂ) = 2 := rfl
    let r₁ : N := (y + y⁻¹) / 2
    let r₂ : N := (y - y⁻¹) / (2 * ι)
    have hr₁ : r₁ ∈ (realStructure N).Re := by
      change ((((y + y⁻¹) / 2 : N)) : ℂ).im = 0
      push_cast
      rw [h2, ← hc, Complex.add_conj]
      simp
    have hr₂ : r₂ ∈ (realStructure N).Re := by
      change ((((y - y⁻¹) / (2 * ι) : N)) : ℂ).im = 0
      push_cast
      rw [h2, hι, ← hc, Complex.sub_conj]
      field_simp
      simp
    have he : y = r₁ + ι * r₂ := by
      apply Subtype.ext
      simp only [r₁, r₂]
      push_cast
      rw [h2, hι]
      field_simp
      ring
    rw [he, map_add, (h r₁ hr₁).1, (h r₂ hr₂).2, add_zero]
  ext x
  induction hspan x using Submodule.span_induction with
  | mem y hy => simp [hu y hy]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

variable [FiniteDimensional 𝔸⟮T⟯ N]

lemma exists_general_units
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1}) (n : ℕ) :
    ∃ s : Fin n → N, (∀ i, ‖(s i : ℂ)‖ = 1) ∧ GeneralFamily 𝔸⟮T⟯ s := by
  have : Algebra.IsIntegral 𝔸⟮T⟯ N := Algebra.IsIntegral.of_finite _ _
  refine exists_generalFamily {y : N | ‖(y : ℂ)‖ = 1} (fun P hP => ?_) n
  obtain ⟨r, hr⟩ := (realStructure N).cay_subspaces_avoid (realStructure_span N hspan) P hP
  refine ⟨_, ?_, hr⟩
  change ‖(((realStructure N).cay r : N) : ℂ)‖ = 1
  rw [coe_realStructure_cay]
  exact norm_cayley r.property

omit [FiniteDimensional 𝔸⟮T⟯ N] in

lemma mul_multiplier_mem_units (hT1 : ‖T‖ = 1) {z : Fin 2 → 𝔸} (hz : z ∈ Ω) {u : ℂ}
    (hu : u ∈ units N) :
    u * ((z 0 : ℂ) * (1 + (z 1 : ℂ) / (T - z 0))) ∈ units N := by
  refine mul_mem_units hu ⟨?_, (Ω_unit hz hT1).2⟩
  exact N.mul_mem (coe_𝔸_mem N _) (N.add_mem N.one_mem (N.div_mem (coe_𝔸_mem N _)
    (N.sub_mem (T_mem N) (coe_𝔸_mem N _))))

lemma coe_aeval_gen (p : 𝔸[X]) : ((aeval (AdjoinSimple.gen 𝔸 T) p : 𝔸⟮T⟯) : ℂ) = aeval T p := by
  rw [← AdjoinSimple.coe_gen 𝔸 T]
  exact (aeval_algHom_apply (𝔸⟮T⟯).val (AdjoinSimple.gen 𝔸 T) p).symm

theorem exists_frame (hT1 : ‖T‖ = 1) (hT : Transcendental 𝔸 T)
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1})
    (Q : Finset ℂ) (hQ : ∀ q ∈ Q, q ∈ units N) :
    ∃ 𝔣 : CauchyFrame, 𝔣.T = T ∧ 𝔣.Q = Q ∧ 𝔣.U = units N ∧ 0 < 𝔣.d ∧
      ∀ l, 𝔣.b l ∈ units N := by
  classical
  set d := finrank 𝔸⟮T⟯ N with hd_def
  have hd : 0 < d := finrank_pos
  set n := Fintype.card Q * (d - 1) + d with hn
  obtain ⟨s, hsn, hsg⟩ := exists_general_units N hspan n
  let e₀ : Fin d ↪ Fin n := Fin.castLEEmb (by omega)
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hli : LinearIndependent 𝔸⟮T⟯ (s ∘ e₀) := hsg.linearIndependent e₀
  let bas : Basis (Fin d) 𝔸⟮T⟯ N := basisOfLinearIndependentOfCardEqFinrank hli (by simp [d])
  have hbas (l : Fin d) : bas l = s (e₀ l) := by
    simp [bas, coe_basisOfLinearIndependentOfCardEqFinrank]
  let qN : Q → N := fun j => ⟨j, (hQ j j.2).1⟩
  let g : Q × Fin n × Fin d → 𝔸⟮T⟯ := fun x => bas.repr (qN x.1 * s x.2.1) x.2.2
  obtain ⟨κ, hκ, P, hP⟩ := exists_common_denom hT g
  let TB := AdjoinSimple.gen 𝔸 T
  have hPB (x : Q × Fin n × Fin d) : aeval TB κ * g x = aeval TB (P x) := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, coe_aeval_gen, coe_aeval_gen, hP]
  have hsmul (c : 𝔸⟮T⟯) (x : N) : ((c • x : N) : ℂ) = (c : ℂ) * x := rfl
  refine ⟨{
    T := T
    d := d
    n := n
    Q := Q
    b := fun l => (s (e₀ l) : ℂ)
    s := fun k => (s k : ℂ)
    κ := κ
    p := fun j k l => P (j, k, l)
    U := units N
    norm_T := hT1
    κ_ne := hκ
    coord := fun j k => ?_
    det_ne := fun j e => ?_
    card_lt := by omega
    s_mem := fun k => ⟨(s k).property, hsn k⟩
    mul_mem := fun z hz u hu => mul_multiplier_mem_units N hT1 hz hu }, rfl, rfl, rfl, hd,
    fun l => ⟨(s (e₀ l)).property, hsn (e₀ l)⟩⟩
  · have h := congrArg (fun x : N => (x : ℂ)) (bas.sum_repr (qN j * s k))
    simp only [AddSubmonoidClass.coe_finsetSum, hsmul, hbas, MulMemClass.coe_mul] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc]
    congr 1
    exact hP (j, k, l)
  · intro hdet
    have hq0 : (j : ℂ) ≠ 0 := by
      intro h0
      have := (hQ j j.2).2
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    let c : N := algebraMap 𝔸⟮T⟯ N (aeval TB κ) * qN j
    have hc : c ≠ 0 := by
      intro h0
      have := congrArg (fun x : N => (x : ℂ)) h0
      simp only [c, MulMemClass.coe_mul, ZeroMemClass.coe_zero] at this
      rcases mul_eq_zero.mp this with h | h
      · exact aeval_ne_zero hT hκ (by rw [← coe_aeval_gen]; exact h)
      · exact hq0 h
    let v : Fin d → N := fun i => c * s (e i)
    have hv : LinearIndependent 𝔸⟮T⟯ v :=
      (hsg.linearIndependent e).map' (LinearMap.mulLeft 𝔸⟮T⟯ c)
        (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hc))
    have hspanv : Submodule.span 𝔸⟮T⟯ (Set.range v) = ⊤ := by
      have := (basisOfLinearIndependentOfCardEqFinrank hv (by simp [d])).span_eq
      rwa [coe_basisOfLinearIndependentOfCardEqFinrank] at this
    have hunit := (Module.Basis.is_basis_iff_det bas).mp ⟨hv, hspanv⟩
    have hmat : bas.toMatrix v = ((aeval TB).toRingHom.mapMatrix
        (Matrix.of fun i l => P (j, e i, l))).transpose := by
      ext l i
      rw [Basis.toMatrix_apply]
      simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.of_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← hPB (j, e i, l)]
      have he : v i = aeval TB κ • (qN j * s (e i)) := by
        simp only [v, c, Algebra.smul_def, mul_assoc]
      rw [he, map_smul]
      rfl
    rw [Basis.det_apply, hmat, Matrix.det_transpose, ← RingHom.map_det] at hunit
    erw [hdet, map_zero] at hunit
    exact not_isUnit_zero hunit

end Parish173.Template

end
end

-- Erdos173.Template.Cover
section
noncomputable section

namespace Parish173.Template

open Polynomial IntermediateField ComplexConjugate Module

variable {T : ℂ} (N : IntermediateField 𝔸⟮T⟯ ℂ)

private def spanA : Submodule 𝔸 ℂ := Submodule.span 𝔸 (units N)

variable {N}

lemma mem_of_mem_spanA {v : ℂ} (hv : v ∈ spanA N) : v ∈ N := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact hv.1
  | zero => exact N.zero_mem
  | add v w _ _ hv hw => exact N.add_mem hv hw
  | smul c v _ hv => rw [smul_eq]; exact N.mul_mem (coe_𝔸_mem N c) hv

lemma mem_spanA_of_mem_units {u : ℂ} (hu : u ∈ units N) : u ∈ spanA N := Submodule.subset_span hu

lemma mul_mem_spanA {v w : ℂ} (hv : v ∈ spanA N) (hw : w ∈ spanA N) : v * w ∈ spanA N := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    induction hw using Submodule.span_induction with
    | mem w hw => exact mem_spanA_of_mem_units (mul_mem_units hv hw)
    | zero => simp
    | add w w' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul c w _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
  | zero => simp
  | add v v' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
  | smul c v _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

lemma one_mem_spanA : (1 : ℂ) ∈ spanA N :=
  mem_spanA_of_mem_units ⟨N.one_mem, norm_one⟩

lemma coe_mem_spanA (a : 𝔸) : (a : ℂ) ∈ spanA N := by
  have h := Submodule.smul_mem (spanA N) a (one_mem_spanA (N := N))
  rwa [smul_eq, mul_one] at h

lemma aeval_mem_spanA (hT1 : ‖T‖ = 1) (p : 𝔸[X]) : aeval T p ∈ spanA N := by
  have hT : T ∈ units N := ⟨T_mem N, hT1⟩
  have hpow (n : ℕ) : T ^ n ∈ spanA N := by
    induction n with
    | zero => simpa using one_mem_spanA (N := N)
    | succ n ih => rw [pow_succ]; exact mul_mem_spanA ih (mem_spanA_of_mem_units hT)
  rw [aeval_eq_sum_range]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hpow i)

lemma conj_mem_spanA {v : ℂ} (hv : v ∈ spanA N) : conj v ∈ spanA N := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact mem_spanA_of_mem_units (conj_mem_units hv)
  | zero => simp
  | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
  | smul c v _ hv =>
    rw [smul_eq, map_mul]
    have h := Submodule.smul_mem _ (conjA c) hv
    rwa [smul_eq, coe_conjA] at h

lemma spanA_re_im {v : ℂ} (hv : v ∈ spanA N) :
    ∃ r₁ r₂ : ℂ, r₁ ∈ spanA N ∧ r₂ ∈ spanA N ∧ r₁.im = 0 ∧ r₂.im = 0 ∧
      v = r₁ + Complex.I * r₂ := by
  have h2 : ((2 : 𝔸) : ℂ) = 2 := rfl
  refine ⟨((2 : 𝔸)⁻¹ : 𝔸) • (v + conj v), ((2 * iA : 𝔸)⁻¹ : 𝔸) • (v - conj v),
    Submodule.smul_mem _ _ (Submodule.add_mem _ hv (conj_mem_spanA hv)),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ hv (conj_mem_spanA hv)), ?_, ?_, ?_⟩
  · rw [smul_eq, Complex.add_conj]
    push_cast
    rw [h2]
    simp
  · rw [smul_eq, Complex.sub_conj]
    push_cast
    rw [h2, coe_iA]
    field_simp
    simp
  · simp only [smul_eq]
    push_cast
    rw [h2, coe_iA]
    field_simp
    ring

lemma cayley_mem {z : ℂ} (hz : z ∈ spanA N) (hre : z.im = 0) :
    (1 + Complex.I * z) / (1 - Complex.I * z) ∈ units N ∧
      (1 - Complex.I * z)⁻¹ ∈ spanA N := by
  have hd := one_sub_I_mul_ne hre
  have hzN := mem_of_mem_spanA hz
  have hu : (1 + Complex.I * z) / (1 - Complex.I * z) ∈ units N :=
    ⟨N.div_mem (N.add_mem N.one_mem (N.mul_mem (I_mem N) hzN))
      (N.sub_mem N.one_mem (N.mul_mem (I_mem N) hzN)), norm_cayley hre⟩
  refine ⟨hu, ?_⟩
  have he : (1 - Complex.I * z)⁻¹ = ((2 : 𝔸)⁻¹ : 𝔸) •
      (1 + (1 + Complex.I * z) / (1 - Complex.I * z)) := by
    rw [smul_eq]
    push_cast
    rw [show ((2 : 𝔸) : ℂ) = 2 from rfl]
    field_simp
    ring
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ one_mem_spanA (mem_spanA_of_mem_units hu))

private def Good (p : 𝔸[X]) : Prop :=
  ∃ F : Finset ℂ, (↑F ⊆ (spanA N : Set ℂ)) ∧
    ∀ v ∈ spanA N, ∃ w ∈ spanA N, v - aeval T p * w ∈ Submodule.span 𝔸 (F : Set ℂ)

section Reduction

variable (hT1 : ‖T‖ = 1) (hT : Transcendental 𝔸 T)
include hT1 hT

lemma reduce_relation {ι : Type*} [Fintype ι] (a : 𝔸) (P : ι → 𝔸[X]) (hP : ∃ i, P i ≠ 0)
    (vs : ι → ℂ) (hvs : ∀ i, vs i ∈ spanA N) (hrel : ∑ i, aeval T (P i) * vs i = 0) :
    ∃ c : ι → 𝔸, (∃ i, c i ≠ 0) ∧ ∃ w ∈ spanA N, ∑ i, c i • vs i = (T - a) * w := by
  classical
  obtain ⟨i₀, hi₀, hmin⟩ := (Finset.univ.filter fun i => P i ≠ 0).exists_min_image
    (fun i => rootMultiplicity a (P i)) (by
      obtain ⟨i, hi⟩ := hP
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)
  have hP₀ : P i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  set m := rootMultiplicity a (P i₀)
  have hdvd (i : ι) : (X - C a) ^ m ∣ P i := by
    by_cases hi : P i = 0
    · rw [hi]
      exact dvd_zero _
    · exact (pow_dvd_pow _ (hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))).trans
        (pow_rootMultiplicity_dvd _ _)
  choose P' hP' using hdvd
  have hXa : (X - C a) ^ m ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero a)
  have hev : (P' i₀).eval a ≠ 0 := by
    obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd (P i₀) hP₀ a
    have : P' i₀ = q := mul_left_cancel₀ hXa ((hP' i₀).symm.trans hq)
    rw [this]
    intro h
    exact hnd (dvd_iff_isRoot.mpr h)
  have hTa : T - (a : ℂ) ≠ 0 := by
    intro h
    have := transcendental_iff.mp hT (X - C a) (by simpa [sub_eq_zero] using h)
    exact X_sub_C_ne_zero a this
  have hrel' : ∑ i, aeval T (P' i) * vs i = 0 := by
    have h : (T - a) ^ m * ∑ i, aeval T (P' i) * vs i = 0 := by
      rw [Finset.mul_sum, ← hrel]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hP' i, map_mul, map_pow, map_sub, aeval_X, aeval_C]
      simp only [IntermediateField.algebraMap_apply]
      ring
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hTa)
  have hR (i : ι) : X - C a ∣ P' i - C ((P' i).eval a) := X_sub_C_dvd_sub_C_eval
  choose R hR using hR
  refine ⟨fun i => (P' i).eval a, ⟨i₀, hev⟩, -∑ i, aeval T (R i) * vs i,
    Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ =>
      mul_mem_spanA (aeval_mem_spanA hT1 _) (hvs i)), ?_⟩
  have hpt (i : ι) : (((P' i).eval a : 𝔸) : ℂ) = aeval T (P' i) - (T - a) * aeval T (R i) := by
    have h := congrArg (aeval T) (hR i)
    rw [map_sub, aeval_C, map_mul, map_sub, aeval_X, aeval_C] at h
    simp only [IntermediateField.algebraMap_apply] at h
    rw [← h]
    ring
  simp only [smul_eq, hpt, sub_mul, Finset.sum_sub_distrib, hrel', mul_assoc, ← Finset.mul_sum]
  ring

omit hT1 hT in

lemma good_C {c : 𝔸} (hc : c ≠ 0) : Good (N := N) (C c) := by
  refine ⟨∅, by simp, fun v hv => ⟨((c⁻¹ : 𝔸) : ℂ) * v, ?_, ?_⟩⟩
  · rw [← smul_eq]
    exact Submodule.smul_mem _ _ hv
  · rw [aeval_C, IntermediateField.algebraMap_apply, ← mul_assoc, ← IntermediateField.coe_mul,
      mul_inv_cancel₀ hc]
    simp

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1500000 in
lemma good_linear [FiniteDimensional 𝔸⟮T⟯ N] (a : 𝔸) : Good (N := N) (X - C a) := by
  classical
  let A' : Subalgebra 𝔸 ℂ := (spanA N).toSubalgebra one_mem_spanA fun _ _ => mul_mem_spanA
  have hTa : (T - a : ℂ) ∈ A' := Submodule.sub_mem _ (by
    simpa using aeval_mem_spanA (N := N) hT1 X) (coe_mem_spanA a)
  let S : Submodule 𝔸 A' := LinearMap.range (LinearMap.mulLeft 𝔸 (⟨T - a, hTa⟩ : A'))
  have hrank : Module.rank 𝔸 (A' ⧸ S) ≤ finrank 𝔸⟮T⟯ N := by
    apply rank_le
    intro s hs
    by_contra! hlt
    let f : Fin (finrank 𝔸⟮T⟯ N + 1) → s := fun i => s.equivFin.symm ⟨i, by omega⟩
    have hf : Function.Injective f := fun i j h => by
      have := Fin.ext_iff.mp (s.equivFin.symm.injective h)
      exact Fin.ext this
    have hli := hs.comp f hf
    choose vs hvs using fun i => Submodule.Quotient.mk_surjective S (f i : A' ⧸ S)
    let wN : Fin (finrank 𝔸⟮T⟯ N + 1) → N := fun i => ⟨(vs i : ℂ), mem_of_mem_spanA (vs i).property⟩
    have hnli : ¬ LinearIndependent 𝔸⟮T⟯ wN := fun h => by
      have := h.fintype_card_le_finrank
      simp at this
    obtain ⟨g, hg, i, hgi⟩ := Fintype.not_linearIndependent_iff.mp hnli
    obtain ⟨κ, hκ, P, hP⟩ := exists_common_denom hT g
    have hrel : ∑ i, aeval T (P i) * (vs i : ℂ) = 0 := by
      have h := congrArg (fun x : N => aeval T κ * (x : ℂ)) hg
      simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, mul_zero,
        Finset.mul_sum] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hP j]
      change _ = aeval T κ * ((g j : ℂ) * (vs j : ℂ))
      ring
    have hPi : P i ≠ 0 := by
      intro h0
      have := hP i
      rw [h0, map_zero] at this
      exact hgi (Subtype.ext ((mul_eq_zero.mp this).resolve_left (aeval_ne_zero hT hκ)))
    obtain ⟨c, ⟨j, hcj⟩, w, hw, hcw⟩ := reduce_relation hT1 hT a P ⟨i, hPi⟩
      (fun i => (vs i : ℂ)) (fun i => (vs i).property) hrel
    have hS : ∑ i, c i • vs i ∈ S := ⟨⟨w, hw⟩, by
      apply Subtype.ext
      simp only [LinearMap.mulLeft_apply, MulMemClass.coe_mul, AddSubmonoidClass.coe_finsetSum,
        SetLike.val_smul]
      rw [hcw]⟩
    have hzero : ∑ i, c i • (f i : A' ⧸ S) = 0 := by
      have h : S.mkQ (∑ i, c i • vs i) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hS
      simpa only [map_sum, map_smul, Submodule.mkQ_apply, hvs] using h
    exact hcj (Fintype.linearIndependent_iff.mp hli c hzero j)
  have : Module.Finite 𝔸 (A' ⧸ S) :=
    Module.rank_lt_aleph0_iff.mp (hrank.trans_lt (Cardinal.natCast_lt_aleph0))
  obtain ⟨k, fs, hfs⟩ := Module.Finite.exists_fin (R := 𝔸) (M := A' ⧸ S)
  choose ls hls using fun i => Submodule.Quotient.mk_surjective S (fs i)
  refine ⟨Finset.univ.image fun i => (ls i : ℂ), ?_, fun v hv => ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact (ls i).property
  have hmem : Submodule.Quotient.mk (⟨v, hv⟩ : A') ∈ Submodule.span 𝔸 (Set.range fs) := by
    rw [hfs]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝔸).mp hmem
  have hd : (⟨v, hv⟩ : A') - ∑ i, c i • ls i ∈ S := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← hc, sub_eq_zero]
    have h := map_sum S.mkQ (fun i => c i • ls i) Finset.univ
    simp only [map_smul, Submodule.mkQ_apply, hls] at h
    exact h.symm
  obtain ⟨w, hw⟩ := hd
  refine ⟨w, w.property, ?_⟩
  have hw' := congrArg (fun x : A' => (x : ℂ)) hw
  simp only [LinearMap.mulLeft_apply, MulMemClass.coe_mul, AddSubgroupClass.coe_sub,
    AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at hw'
  have he : v - aeval T (X - C a) * (w : ℂ) = ∑ i, c i • (ls i : ℂ) := by
    rw [map_sub, aeval_X, aeval_C, IntermediateField.algebraMap_apply, hw']
    ring
  rw [he]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp

omit hT in

lemma good_mul {p : 𝔸[X]} (a : 𝔸) (hp : Good (N := N) p) (ha : Good (N := N) (X - C a)) :
    Good (N := N) (p * (X - C a)) := by
  classical
  obtain ⟨F, hF, hFp⟩ := hp
  obtain ⟨G, hG, hGa⟩ := ha
  refine ⟨F ∪ G.image (fun g => aeval T p * g), ?_, fun v hv => ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hF hx
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
      exact mul_mem_spanA (aeval_mem_spanA hT1 p) (hG hg)
  obtain ⟨w₁, hw₁, h₁⟩ := hFp v hv
  obtain ⟨w₂, hw₂, h₂⟩ := hGa w₁ hw₁
  refine ⟨w₂, hw₂, ?_⟩
  have he : v - aeval T (p * (X - C a)) * w₂ =
      (v - aeval T p * w₁) + aeval T p * (w₁ - aeval T (X - C a) * w₂) := by
    rw [map_mul]
    ring
  rw [he]
  refine Submodule.add_mem _ (Submodule.span_mono Finset.subset_union_left h₁) ?_
  have hmap : aeval T p * (w₁ - aeval T (X - C a) * w₂) ∈
      (Submodule.span 𝔸 (G : Set ℂ)).map (LinearMap.mulLeft 𝔸 (aeval T p)) :=
    ⟨_, h₂, rfl⟩
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨g, hg, rfl⟩
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg)

lemma good_of_ne_zero [FiniteDimensional 𝔸⟮T⟯ N] {p : 𝔸[X]} (hp : p ≠ 0) : Good (N := N) p := by
  induction h : p.natDegree generalizing p with
  | zero =>
    rw [eq_C_of_natDegree_eq_zero h]
    exact good_C (fun hc => hp (by rw [eq_C_of_natDegree_eq_zero h, hc, map_zero]))
  | succ n ih =>
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
      rw [degree_eq_natDegree hp, h]
      exact_mod_cast Nat.succ_ne_zero n)
    have hdiv := mul_divByMonic_eq_iff_isRoot.mpr ha
    set q := p /ₘ (X - C a)
    have hq : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdiv
      exact hp hdiv.symm
    have hqd : q.natDegree = n := by
      have := congrArg natDegree hdiv
      rw [natDegree_mul (X_sub_C_ne_zero a) hq, natDegree_X_sub_C, h] at this
      omega
    rw [← hdiv, mul_comm]
    exact good_mul hT1 a (ih hq hqd) (good_linear hT1 hT a)

end Reduction

variable (N)

private def algA : Subalgebra 𝔸 ℂ := (spanA N).toSubalgebra one_mem_spanA fun _ _ => mul_mem_spanA

variable {N}

lemma mem_algA {x : ℂ} : x ∈ algA N ↔ x ∈ spanA N := Submodule.mem_toSubalgebra

variable (N) (ℓ : ℂ →ₗ[𝔸] 𝔸)

private def annIdeal : Ideal (algA N) where
  carrier := {v | ∀ w : algA N, ℓ ((v : ℂ) * w) = 0}
  add_mem' {v v'} hv hv' w := by
    simp only [Set.mem_ofPred_eq, Subalgebra.coe_add, add_mul, map_add] at hv hv' ⊢
    rw [hv w, hv' w, add_zero]
  zero_mem' w := by simp
  smul_mem' c v hv w := by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, Subalgebra.coe_mul] at hv ⊢
    have := hv (c * w)
    rw [Subalgebra.coe_mul] at this
    rw [← this]
    ring_nf

private abbrev quotA := algA N ⧸ annIdeal N ℓ

private abbrev πA : algA N →ₐ[𝔸] quotA N ℓ := Ideal.Quotient.mkₐ 𝔸 (annIdeal N ℓ)

lemma annIdeal_le_ker :
    (annIdeal N ℓ).restrictScalars 𝔸 ≤ LinearMap.ker (ℓ ∘ₗ (algA N).val.toLinearMap) :=
  fun v hv => by simpa using hv 1

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1500000 in
private def ℓbar : quotA N ℓ →ₗ[𝔸] 𝔸 :=
  ((annIdeal N ℓ).restrictScalars 𝔸).liftQ _ (annIdeal_le_ker N ℓ) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv 𝔸 (annIdeal N ℓ)).symm.toLinearMap

lemma ℓbar_π (v : algA N) : ℓbar N ℓ (πA N ℓ v) = ℓ v := by
  have h : (Submodule.Quotient.restrictScalarsEquiv 𝔸 (annIdeal N ℓ)).symm (πA N ℓ v) =
      Submodule.Quotient.mk v :=
    (Submodule.Quotient.restrictScalarsEquiv 𝔸 (annIdeal N ℓ)).symm_apply_eq.mpr
      (Submodule.Quotient.restrictScalarsEquiv_mk 𝔸 (annIdeal N ℓ) v).symm
  simp only [ℓbar, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h]
  rfl

variable {N ℓ}

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1500000 in
lemma finiteDimensional_quotA [FiniteDimensional 𝔸⟮T⟯ N] (hT1 : ‖T‖ = 1)
    (hT : Transcendental 𝔸 T) {p : 𝔸[X]} (hp : p ≠ 0)
    (hann : ∀ w ∈ spanA N, ℓ (aeval T p * w) = 0) : FiniteDimensional 𝔸 (quotA N ℓ) := by
  classical
  obtain ⟨F, hF, hFp⟩ := good_of_ne_zero hT1 hT (N := N) hp
  let F' : Finset (algA N) := F.attach.image fun x : F => (⟨x.1, mem_algA.mpr (hF x.2)⟩ : algA N)
  refine ⟨⟨F'.image (πA N ℓ), eq_top_iff.mpr fun x _ => ?_⟩⟩
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mkₐ_surjective 𝔸 (annIdeal N ℓ) x
  obtain ⟨w, hw, hvw⟩ := hFp v (mem_algA.mp v.property)
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hvw
  let pw : algA N := ⟨aeval T p * w, mem_algA.mpr (mul_mem_spanA (aeval_mem_spanA hT1 p) hw)⟩
  have hpw : pw ∈ annIdeal N ℓ := fun w' => by
    change ℓ (aeval T p * w * w') = 0
    rw [mul_assoc]
    exact hann _ (mul_mem_spanA hw (mem_algA.mp w'.property))
  have hv : v = pw + ∑ x ∈ F.attach, c x • (⟨x.1, mem_algA.mpr (hF x.2)⟩ : algA N) := by
    apply Subtype.ext
    simp only [pw, Subalgebra.coe_add, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    rw [Finset.sum_attach F (fun x => c x • x), hc]
    ring
  have hπ0 : πA N ℓ pw = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpw
  rw [hv, map_add, hπ0, zero_add, map_sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr
    (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_attach _ x)))))

variable (N ℓ)

private def iAlg : algA N := ⟨Complex.I, mem_algA.mpr (coe_mem_spanA iA)⟩

lemma isUnit_one_sub (z : algA N) (hz : (z : ℂ).im = 0) : IsUnit (1 - iAlg N * z) := by
  refine isUnit_iff_exists_inv.mpr
    ⟨⟨(1 - Complex.I * z)⁻¹, mem_algA.mpr (cayley_mem (mem_algA.mp z.property) hz).2⟩, ?_⟩
  apply Subtype.ext
  change (1 - Complex.I * z) * (1 - Complex.I * z)⁻¹ = 1
  exact mul_inv_cancel₀ (one_sub_I_mul_ne hz)

private def quotReal : RealStructure 𝔸 (quotA N ℓ) where
  ι := πA N ℓ (iAlg N)
  Re := {x | ∃ z : algA N, (z : ℂ).im = 0 ∧ πA N ℓ z = x}
  ι_sq := by
    have h : iAlg N * iAlg N = -1 := Subtype.ext Complex.I_mul_I
    rw [← map_mul, h, map_neg, map_one]
  one_mem := ⟨1, by simp, map_one _⟩
  add_mem r := fun ⟨z, hz, hzr⟩ r' ⟨z', hz', hzr'⟩ =>
    ⟨z + z', by simp [hz, hz'], by rw [← hzr, ← hzr']; exact (πA N ℓ).toRingHom.map_add z z'⟩
  smul_mem t r := fun ⟨z, hz, hzr⟩ => ⟨algebraMap 𝔸 (algA N) t * z, by
      change ((t : ℂ) * (z : ℂ)).im = 0
      rw [Complex.mul_im, hz]
      simp, by rw [map_mul, AlgHom.commutes, hzr]⟩
  isUnit r := fun ⟨z, hz, hzr⟩ => by
    rw [← hzr, ← map_mul, ← map_one (πA N ℓ), ← map_sub]
    exact (isUnit_one_sub N z hz).map _

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1500000 in
lemma quotReal_span (ℓ' : quotA N ℓ →ₗ[𝔸] 𝔸)
    (h : ∀ r ∈ (quotReal N ℓ).Re, ℓ' r = 0 ∧ ℓ' ((quotReal N ℓ).ι * r) = 0) : ℓ' = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mkₐ_surjective 𝔸 (annIdeal N ℓ) x
  obtain ⟨r₁, r₂, h₁, h₂, hr₁, hr₂, hv⟩ := spanA_re_im (mem_algA.mp v.property)
  have hv' : v = ⟨r₁, mem_algA.mpr h₁⟩ + iAlg N * ⟨r₂, mem_algA.mpr h₂⟩ := Subtype.ext hv
  rw [LinearMap.zero_apply, hv', map_add, map_mul, map_add,
    (h _ ⟨⟨r₁, mem_algA.mpr h₁⟩, hr₁, rfl⟩).1, zero_add]
  exact (h _ ⟨⟨r₂, mem_algA.mpr h₂⟩, hr₂, rfl⟩).2

variable {N ℓ}

set_option synthInstance.maxHeartbeats 200000 in

set_option synthInstance.maxHeartbeats 300000 in
set_option maxHeartbeats 1500000 in
lemma escape_of_finiteDimensional [FiniteDimensional 𝔸 (quotA N ℓ)] (hℓ : ℓ 1 = 1)
    (Q : Finset ℂ) (hQ : ∀ q ∈ Q, q ∈ units N) : ∃ u ∈ units N, ∀ q ∈ Q, ℓ (q * u) ≠ 0 := by
  classical
  have : Algebra.IsIntegral 𝔸 (quotA N ℓ) := Algebra.IsIntegral.of_finite _ _
  let S := quotReal N ℓ
  let qA : Q → algA N := fun q => ⟨q, mem_algA.mpr (mem_spanA_of_mem_units (hQ q q.2))⟩
  let μ : Q → quotA N ℓ →ₗ[𝔸] 𝔸 := fun q => ℓbar N ℓ ∘ₗ LinearMap.mulLeft 𝔸 (πA N ℓ (qA q))
  have hμ (q : Q) (v : algA N) : μ q (πA N ℓ v) = ℓ (q * v) := by
    simp only [μ, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply, ← map_mul,
      ℓbar_π]
    rfl
  have hμ0 (q : Q) : μ q ≠ 0 := by
    intro h0
    have hq := hQ q q.2
    have h := LinearMap.congr_fun h0
      (πA N ℓ ⟨conj (q : ℂ), mem_algA.mpr (mem_spanA_of_mem_units (conj_mem_units hq))⟩)
    rw [hμ, LinearMap.zero_apply] at h
    have hqq : (q : ℂ) * conj (q : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hq.2]
      simp
    rw [show (q : ℂ) * ((⟨conj (q : ℂ), _⟩ : algA N) : ℂ) = 1 from hqq, hℓ] at h
    exact one_ne_zero h
  obtain ⟨r, hr⟩ := S.cay_finite_avoid (quotReal_span N ℓ) (Finset.univ.image μ) (by
    intro ψ hψ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hψ
    exact hμ0 q)
  obtain ⟨z, hz, hzr⟩ := r.property
  obtain ⟨hu, -⟩ := cayley_mem (mem_algA.mp z.property) hz
  let uA : algA N :=
    ⟨(1 + Complex.I * z) / (1 - Complex.I * z), mem_algA.mpr (mem_spanA_of_mem_units hu)⟩
  have hcay : S.cay r = πA N ℓ uA := by
    symm
    apply S.cay_unique
    change (1 - πA N ℓ (iAlg N) * (r : quotA N ℓ)) * πA N ℓ uA =
      1 + πA N ℓ (iAlg N) * (r : quotA N ℓ)
    rw [← hzr, ← map_mul, ← map_one (πA N ℓ), ← map_sub, ← map_mul, ← map_add]
    congr 1
    apply Subtype.ext
    change (1 - Complex.I * z) * ((1 + Complex.I * z) / (1 - Complex.I * z)) = 1 + Complex.I * z
    field_simp [one_sub_I_mul_ne hz]
  refine ⟨_, hu, fun q hq hqu => hr (μ ⟨q, hq⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _)) ?_⟩
  rw [hcay, hμ]
  exact hqu

lemma annihilator_of_cover [FiniteDimensional 𝔸⟮T⟯ N] (hT1 : ‖T‖ = 1) (hT : Transcendental 𝔸 T)
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1})
    (Q : Finset ℂ) (hQ : ∀ q ∈ Q, q ∈ units N)
    (hcov0 : ∀ u ∈ units N, ∃ q ∈ Q, ℓ (q * u) = 0) :
    ∃ p : 𝔸[X], p ≠ 0 ∧ ∀ w ∈ spanA N, ℓ (aeval T p * w) = 0 := by
  obtain ⟨𝔣, hfT, hfQ, hfU, hd, hb⟩ := exists_frame N hT1 hT hspan Q hQ
  have hcov : 𝔣.Covered ℓ := by
    intro u hu
    rw [hfU] at hu
    rw [hfQ]
    exact hcov0 u hu
  have hmul : ∀ u ∈ 𝔣.U, ∀ v ∈ 𝔣.U, u * v ∈ 𝔣.U := by
    rw [hfU]
    exact fun u hu v hv => mul_mem_units hu hv
  have hTU : 𝔣.T ∈ 𝔣.U := by
    rw [hfU, hfT]
    exact ⟨T_mem N, hT1⟩
  obtain ⟨p, hp, hann⟩ := CauchyFrame.exists_annihilator hmul hcov hTU
  have hA : 𝔣.A = spanA N := by rw [CauchyFrame.A, hfU]; rfl
  refine ⟨p, hp, fun w hw => ?_⟩
  let l : Fin 𝔣.d := ⟨0, hd⟩
  have hb0 : 𝔣.b l ≠ 0 := by
    intro h0
    have := (hb l).2
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h := hann (w * (𝔣.b l)⁻¹) (by
    rw [hA]
    exact mul_mem_spanA hw (mem_spanA_of_mem_units (inv_mem_units (hb l)))) l
  rwa [hfT, mul_assoc, inv_mul_cancel_right₀ hb0] at h

theorem cover_impossible [FiniteDimensional 𝔸⟮T⟯ N] (hT1 : ‖T‖ = 1) (hT : Transcendental 𝔸 T)
    (hspan : ∀ x : N, x ∈ Submodule.span 𝔸⟮T⟯ {y : N | ‖(y : ℂ)‖ = 1})
    (Q : Finset ℂ) (hQ : ∀ q ∈ Q, q ∈ units N) (hℓ : ℓ 1 = 1) :
    ∃ u ∈ units N, ∀ q ∈ Q, ℓ (q * u) ≠ 0 := by
  by_contra! hcov0
  obtain ⟨p, hp, hann⟩ := annihilator_of_cover hT1 hT hspan Q hQ hcov0
  have := finiteDimensional_quotA hT1 hT hp hann
  obtain ⟨u, hu, hq⟩ := escape_of_finiteDimensional hℓ Q hQ
  obtain ⟨q, hqQ, hqu⟩ := hcov0 u hu
  exact hq q hqQ hqu

end Parish173.Template

end
end

-- OAI.Analysis.PlaneSpectrum.Carrier
section
noncomputable section

namespace ParishSpectral.PlaneFiveColor.Spectral

private def TemplateProperty (E : Set ℂ) : Prop :=
  ∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
    ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s * s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s * s) '' (S : Set ℂ))

private class Carrier where
  
  E : IntermediateField ℚ ℂ
  
  F : IntermediateField ℚ ℝ
  
  countable : Countable E
  
  mem_iff : ∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F
  
  algClosed : ∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) →
    ∀ z : ℂ, p.eval z = 0 → z ∈ E
  
  template : TemplateProperty (E : Set ℂ)

namespace Carrier

variable [Carrier]

theorem re_mem {z : ℂ} (hz : z ∈ E) : z.re ∈ F := ((mem_iff z).mp hz).1

theorem im_mem {z : ℂ} (hz : z ∈ E) : z.im ∈ F := ((mem_iff z).mp hz).2

theorem ofReal_mem {t : ℝ} (ht : t ∈ F) : (t : ℂ) ∈ E :=
  (mem_iff _).mpr ⟨by simpa using ht, by simp⟩

theorem I_mem : Complex.I ∈ E :=
  (mem_iff _).mpr ⟨by simp, by simp⟩

theorem ratCast_mem (q : ℚ) : (q : ℝ) ∈ F := SubfieldClass.ratCast_mem F q

theorem mem_of_pow_mem {w : ℂ} {n : ℕ} (hn : n ≠ 0) (hw : w ^ n ∈ E) : w ∈ E := by
  classical
  have hdeg : (Polynomial.X ^ n - Polynomial.C (w ^ n)).natDegree = n :=
    Polynomial.natDegree_X_pow_sub_C
  apply algClosed (Polynomial.X ^ n - Polynomial.C (w ^ n))
  · intro h
    rw [h, Polynomial.natDegree_zero] at hdeg
    exact hn hdeg.symm
  · intro k
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    split_ifs
    · exact E.sub_mem E.one_mem hw
    · simp
    · simpa using E.neg_mem hw
    · simp
  · simp

theorem sqrt_mem {t : ℝ} (ht : t ∈ F) : Real.sqrt t ∈ F := by
  by_cases h : 0 ≤ t
  · have hc : ((Real.sqrt t : ℝ) : ℂ) ∈ E := by
      apply mem_of_pow_mem (n := 2) (by norm_num)
      rw [← Complex.ofReal_pow, Real.sq_sqrt h]
      exact ofReal_mem ht
    simpa using re_mem hc
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge h)]
    exact F.zero_mem

theorem norm_mem {z : ℂ} (hz : z ∈ E) : ‖z‖ ∈ F := by
  have h : ‖z‖ = Real.sqrt (z.re * z.re + z.im * z.im) := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg z)]
  rw [h]
  exact sqrt_mem (F.add_mem (F.mul_mem (re_mem hz) (re_mem hz))
    (F.mul_mem (im_mem hz) (im_mem hz)))

theorem countable_F : Countable F := by
  have := countable
  let f : F → E := fun t => ⟨((t : ℝ) : ℂ), ofReal_mem t.property⟩
  apply Function.Injective.countable (f := f)
  intro s t h
  exact Subtype.ext (Complex.ofReal_injective (congrArg Subtype.val h))

end Carrier

private def fieldOf (x : ℝ) : IntermediateField ℚ ℂ :=
  (algebraicClosure (IntermediateField.adjoin ℚ {(x : ℂ)}) ℂ).restrictScalars ℚ

private def realFieldOf (x : ℝ) : IntermediateField ℚ ℝ :=
  (algebraicClosure (IntermediateField.adjoin ℚ {x}) ℝ).restrictScalars ℚ

end ParishSpectral.PlaneFiveColor.Spectral
end
end

-- Erdos173.Template.Scale
section
noncomputable section

namespace Parish173.Template

open Polynomial IntermediateField ComplexConjugate ParishSpectral.PlaneFiveColor.Spectral

private def cayX (x : ℝ) : ℂ := ((x : ℂ) + Complex.I) / ((x : ℂ) - Complex.I)

lemma sub_I_ne (x : ℝ) : (x : ℂ) - Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

lemma norm_cayX (x : ℝ) : ‖cayX x‖ = 1 := by
  have he : conj ((x : ℂ) + Complex.I) = (x : ℂ) - Complex.I := by
    simp [sub_eq_add_neg]
  rw [cayX, norm_div, ← he, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr ?_)]
  rw [← (RingHom.injective (starRingEnd ℂ)).ne_iff, he, map_zero]
  exact sub_I_ne x

lemma x_eq_cayX (x : ℝ) : (x : ℂ) = Complex.I * (cayX x + 1) / (cayX x - 1) := by
  have h1 : cayX x - 1 = 2 * Complex.I / ((x : ℂ) - Complex.I) := by
    rw [cayX]
    field_simp [sub_I_ne x]
    ring
  have h2 : (2 : ℂ) * Complex.I ≠ 0 := by simp
  rw [h1, cayX]
  field_simp [sub_I_ne x]
  ring_nf

lemma transcendental_cayX {x : ℝ} (hx : Transcendental ℚ x) : Transcendental 𝔸 (cayX x) := by
  intro hT
  have hxC : Transcendental ℚ (x : ℂ) :=
    (transcendental_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ) Complex.ofReal_injective).mpr hx
  have hI : IsAlgebraic 𝔸 Complex.I := by
    simpa using isAlgebraic_algebraMap (R := 𝔸) (A := ℂ) iA
  have hA : IsAlgebraic 𝔸 (x : ℂ) := by
    rw [x_eq_cayX]
    rw [div_eq_mul_inv]
    exact (hI.mul (hT.add isAlgebraic_one)).mul (hT.sub isAlgebraic_one).inv
  exact hxC (hA.restrictScalars ℚ)

lemma mem_fieldOf_iff {x : ℝ} {z : ℂ} : z ∈ fieldOf x ↔ IsAlgebraic ℚ⟮(x : ℂ)⟯ z := by
  rw [fieldOf, IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]

lemma mem_fieldOf_of_𝔸 {x : ℝ} {z : ℂ} (hz : z ∈ 𝔸) : z ∈ fieldOf x :=
  mem_fieldOf_iff.mpr ((mem_algebraicClosure_iff.mp hz).tower_top _)

lemma x_mem_fieldOf (x : ℝ) : (x : ℂ) ∈ fieldOf x :=
  mem_fieldOf_iff.mpr (by
    simpa using isAlgebraic_algebraMap (R := ℚ⟮(x : ℂ)⟯) (A := ℂ) (AdjoinSimple.gen ℚ (x : ℂ)))

lemma cayX_mem_fieldOf (x : ℝ) : cayX x ∈ fieldOf x := by
  have hI : Complex.I ∈ fieldOf x := mem_fieldOf_of_𝔸 I_mem_𝔸
  exact (fieldOf x).div_mem ((fieldOf x).add_mem (x_mem_fieldOf x) hI)
    ((fieldOf x).sub_mem (x_mem_fieldOf x) hI)

lemma mem_fieldOf_of_mem_base {x : ℝ} {z : ℂ} (hz : z ∈ 𝔸⟮cayX x⟯) : z ∈ fieldOf x := by
  induction hz using IntermediateField.adjoin_induction with
  | mem z hz =>
    rw [Set.mem_singleton_iff.mp hz]
    exact cayX_mem_fieldOf x
  | algebraMap a => exact mem_fieldOf_of_𝔸 a.property
  | add z w _ _ hz hw => exact (fieldOf x).add_mem hz hw
  | inv z _ hz => exact (fieldOf x).inv_mem hz
  | mul z w _ _ hz hw => exact (fieldOf x).mul_mem hz hw

lemma x_mem_base (x : ℝ) : (x : ℂ) ∈ 𝔸⟮cayX x⟯ := by
  rw [x_eq_cayX]
  have hT := mem_adjoin_simple_self 𝔸 (cayX x)
  have hI : Complex.I ∈ 𝔸⟮cayX x⟯ := (𝔸⟮cayX x⟯).algebraMap_mem iA
  exact (𝔸⟮cayX x⟯).div_mem ((𝔸⟮cayX x⟯).mul_mem hI ((𝔸⟮cayX x⟯).add_mem hT
    (𝔸⟮cayX x⟯).one_mem)) ((𝔸⟮cayX x⟯).sub_mem hT (𝔸⟮cayX x⟯).one_mem)

lemma isIntegral_base {x : ℝ} {z : ℂ} (hz : z ∈ fieldOf x) : IsIntegral 𝔸⟮cayX x⟯ z := by
  obtain ⟨p, hp, hpz⟩ := mem_fieldOf_iff.mp hz
  have hle : ∀ c ∈ ℚ⟮(x : ℂ)⟯, c ∈ 𝔸⟮cayX x⟯ := fun c hc =>
    (adjoin_simple_le_iff (K := (𝔸⟮cayX x⟯).restrictScalars ℚ)).mpr (x_mem_base x) hc
  let φ : ℚ⟮(x : ℂ)⟯ →+* 𝔸⟮cayX x⟯ :=
    { toFun := fun c => ⟨c, hle c c.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Function.Injective φ := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  refine IsAlgebraic.isIntegral ⟨p.map φ, (Polynomial.map_ne_zero_iff hφ).mpr hp, ?_⟩
  rw [aeval_def, eval₂_map]
  exact hpz

private def fieldN (x : ℝ) (Q : Finset ℂ) : IntermediateField 𝔸⟮cayX x⟯ ℂ :=
  IntermediateField.adjoin 𝔸⟮cayX x⟯ (Q : Set ℂ)

variable {x : ℝ} {Q : Finset ℂ}

lemma mem_fieldOf_of_mem_fieldN (hQ : ∀ q ∈ Q, q ∈ fieldOf x) {z : ℂ} (hz : z ∈ fieldN x Q) :
    z ∈ fieldOf x := by
  induction hz using IntermediateField.adjoin_induction with
  | mem z hz => exact hQ z hz
  | algebraMap a => exact mem_fieldOf_of_mem_base a.property
  | add z w _ _ hz hw => exact (fieldOf x).add_mem hz hw
  | inv z _ hz => exact (fieldOf x).inv_mem hz
  | mul z w _ _ hz hw => exact (fieldOf x).mul_mem hz hw

lemma finiteDimensional_fieldN (hQ : ∀ q ∈ Q, q ∈ fieldOf x) :
    FiniteDimensional 𝔸⟮cayX x⟯ (fieldN x Q) :=
  IntermediateField.finiteDimensional_adjoin fun q hq => isIntegral_base (hQ q hq)

lemma span_units_fieldN (hQ : ∀ q ∈ Q, q ∈ fieldOf x ∧ ‖q‖ = 1) (y : fieldN x Q) :
    y ∈ Submodule.span 𝔸⟮cayX x⟯ {u : fieldN x Q | ‖(u : ℂ)‖ = 1} := by
  have hy : (y : ℂ) ∈ Subalgebra.toSubmodule (Algebra.adjoin 𝔸⟮cayX x⟯ (Q : Set ℂ)) := by
    rw [← adjoin_toSubalgebra_of_isAlgebraic fun q hq =>
      (isIntegral_base (hQ q hq).1).isAlgebraic]
    exact y.property
  rw [Algebra.adjoin_eq_span] at hy
  have hcl (z : ℂ) (hz : z ∈ Submonoid.closure (Q : Set ℂ)) : z ∈ fieldN x Q ∧ ‖z‖ = 1 := by
    induction hz using Submonoid.closure_induction with
    | mem z hz => exact ⟨subset_adjoin _ _ hz, (hQ z hz).2⟩
    | one => exact ⟨(fieldN x Q).one_mem, norm_one⟩
    | mul z w _ _ hz hw =>
      exact ⟨(fieldN x Q).mul_mem hz.1 hw.1, by rw [norm_mul, hz.2, hw.2, one_mul]⟩
  have key : ∀ z ∈ Submodule.span 𝔸⟮cayX x⟯ (Submonoid.closure (Q : Set ℂ) : Set ℂ),
      ∃ hz : z ∈ fieldN x Q, (⟨z, hz⟩ : fieldN x Q) ∈
        Submodule.span 𝔸⟮cayX x⟯ {u : fieldN x Q | ‖(u : ℂ)‖ = 1} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact ⟨(hcl z hz).1, Submodule.subset_span (hcl z hz).2⟩
    | zero => exact ⟨(fieldN x Q).zero_mem, Submodule.zero_mem _⟩
    | add z w _ _ hz hw =>
      obtain ⟨hz, hz'⟩ := hz
      obtain ⟨hw, hw'⟩ := hw
      exact ⟨(fieldN x Q).add_mem hz hw, Submodule.add_mem _ hz' hw'⟩
    | smul c z _ hz =>
      obtain ⟨hz, hz'⟩ := hz
      exact ⟨SMulMemClass.smul_mem c hz, Submodule.smul_mem _ c hz'⟩
  obtain ⟨_, h⟩ := key _ hy
  exact h

theorem cover_impossible_fieldOf (hx : Transcendental ℚ x)
    (hQ : ∀ q ∈ Q, q ∈ fieldOf x ∧ ‖q‖ = 1) (ℓ : ℂ →ₗ[𝔸] 𝔸) (hℓ : ℓ 1 = 1) :
    ∃ u ∈ fieldOf x, ‖u‖ = 1 ∧ ∀ q ∈ Q, ℓ (q * u) ≠ 0 := by
  have := finiteDimensional_fieldN fun q hq => (hQ q hq).1
  obtain ⟨u, hu, h⟩ := cover_impossible (N := fieldN x Q) (norm_cayX x) (transcendental_cayX hx)
    (span_units_fieldN hQ) Q (fun q hq => ⟨subset_adjoin _ _ hq, (hQ q hq).2⟩) hℓ
  exact ⟨u, mem_fieldOf_of_mem_fieldN (fun q hq => (hQ q hq).1) hu.1, hu.2, h⟩

end Parish173.Template

end
end

-- OAI.Analysis.PlaneSpectrum.NumberFields
section
namespace ParishSpectral

noncomputable section
open Polynomial
namespace EuclideanFiveColor.AlgebraicCayley
variable {L : Type*} [Field L] [Algebra ℚ L]

lemma minpoly_reverse_eval_ne_zero (b : L) (hb : IsAlgebraic ℚ b) (t : ℚ)
    (ht : 1-b*algebraMap ℚ L t ≠ 0) : (minpoly ℚ b).reverse.eval t ≠ 0 := by
  intro hz
  by_cases ht0 : t = 0
  · subst t
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse, (minpoly.monic hb.isIntegral).leadingCoeff] at hz
    exact one_ne_zero hz
  let : Invertible (t⁻¹) := invertibleOfNonzero (inv_ne_zero ht0)
  have hp : (minpoly ℚ b).IsRoot t⁻¹ := by
    have he := (eval₂_reverse_eq_zero_iff (RingHom.id ℚ) t⁻¹ (minpoly ℚ b))
    simp only [invOf_eq_inv, inv_inv, eval₂_id] at he
    exact he.mp hz
  have he := minpoly.root hb.isIntegral hp
  apply ht
  rw [← he, ← map_mul, inv_mul_cancel₀ ht0, map_one, sub_self]

lemma reciprocal_denominator (b : L) (hb : IsAlgebraic ℚ b) :
    ∃ (P : ℚ[X]) (R : L[X]), P.coeff 0 = 1 ∧
      (1-C b*X)*R = P.map (algebraMap ℚ L) ∧
      ∀ t : ℚ, 1-b*algebraMap ℚ L t ≠ 0 → P.eval t ≠ 0 := by
  by_cases hb0 : b = 0
  · subst b
    exact ⟨1,1,by simp,by simp,by simp⟩
  let p := minpoly ℚ b
  have hm : p.Monic := minpoly.monic hb.isIntegral
  let : Invertible b := invertibleOfNonzero hb0
  have hz : (p.reverse.map (algebraMap ℚ L)).IsRoot b⁻¹ := by
    rw [IsRoot, eval_map]
    have h := (eval₂_reverse_eq_zero_iff (algebraMap ℚ L) b p).mpr (minpoly.aeval ℚ b)
    simpa only [invOf_eq_inv] using h
  obtain ⟨R,hR⟩ := (dvd_iff_isRoot.mpr hz)
  refine ⟨p.reverse,C (-b⁻¹)*R,?_,?_,minpoly_reverse_eval_ne_zero b hb⟩
  · rw [coeff_zero_reverse, hm.leadingCoeff]
  · calc
      _ = (X-C b⁻¹)*R := by
        have he : (1-C b*X)*C (-b⁻¹) = X-C b⁻¹ := by
          have hc : C b*C b⁻¹ = (1 : L[X]) := by rw [← map_mul, mul_inv_cancel₀ hb0, map_one]
          rw [map_neg]
          calc
            _ = (C b*C b⁻¹)*X-C b⁻¹ := by ring
            _ = _ := by rw [hc, one_mul]
        rw [← mul_assoc, he]
      _ = _ := hR.symm

private def polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) : ℚ[X] :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange ℓ (map_zero ℓ)))
@[simp] lemma coeff_polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) (n : ℕ) :
    (polyLinear ℓ p).coeff n = ℓ (p.coeff n) := rfl
lemma polyLinear_add (ℓ : L →ₗ[ℚ] ℚ) (p q : L[X]) :
    polyLinear ℓ (p+q) = polyLinear ℓ p + polyLinear ℓ q := by
  ext n
  simp only [coeff_polyLinear, coeff_add, map_add]
lemma polyLinear_monomial (ℓ : L →ₗ[ℚ] ℚ) (n : ℕ) (a : L) :
    polyLinear ℓ (monomial n a) = monomial n (ℓ a) := by
  ext k
  simp only [coeff_polyLinear, coeff_monomial]
  split_ifs <;> simp
lemma eval_polyLinear (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) (t : ℚ) :
    (polyLinear ℓ p).eval t = ℓ (p.eval (algebraMap ℚ L t)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [polyLinear_add, eval_add, hp, hq, map_add]
  | monomial n a =>
    rw [polyLinear_monomial, eval_monomial, eval_monomial]
    have he : a*(algebraMap ℚ L t)^n = (t^n) • a := by
      rw [Algebra.smul_def, map_pow, mul_comm]
    rw [he, map_smul]
    exact mul_comm _ _

lemma polyLinear_eq_zero_iff (ℓ : L →ₗ[ℚ] ℚ) (p : L[X]) :
    polyLinear ℓ p = 0 ↔ ∀ t : ℚ, ℓ (p.eval (algebraMap ℚ L t)) = 0 := by
  simp_rw [← eval_polyLinear]
  exact ⟨fun he _ => by rw [he, eval_zero], fun h => Polynomial.funext fun t => by simpa using h t⟩

lemma cayley_annihilation (b : L) (hb : IsAlgebraic ℚ b) (ℓ : L →ₗ[ℚ] ℚ)
    (hd : ∀ t : ℚ, 1-b*(algebraMap ℚ L t) ≠ 0)
    (h : ∀ t : ℚ, ℓ ((1+b*(algebraMap ℚ L t))/(1-b*(algebraMap ℚ L t))) = 0) :
    ℓ 1 = 0 ∧ ℓ b = 0 ∧ ℓ (b^2) = 0 := by
  obtain ⟨P,R,hP,hR,_hPreg⟩ := reciprocal_denominator b hb
  have hR' : R-(C b*R)*X = P.map (algebraMap ℚ L) := by
    convert hR using 1
    ring
  let T := R+(C b*R)*X
  have hT : polyLinear ℓ T = 0 := by
    apply (polyLinear_eq_zero_iff ℓ T).mpr
    intro t
    have hRt := congrArg (Polynomial.eval (algebraMap ℚ L t)) hR
    simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
    have he : T.eval (algebraMap ℚ L t) =
        (P.eval t) • ((1+b*(algebraMap ℚ L t))/(1-b*(algebraMap ℚ L t))) := by
      dsimp only [T]
      simp only [eval_add, eval_mul, eval_C, eval_X, Algebra.smul_def]
      rw [← hRt]
      rw [← mul_div_assoc, eq_div_iff (hd t)]
      ring
    rw [he, map_smul, h t, smul_zero]
  have h0 : R.coeff 0 = 1 := by
    have he := congrArg (fun p : L[X] => p.coeff 0) hR'
    simpa only [coeff_sub, coeff_mul_X_zero, sub_zero, coeff_map, hP, map_one] using he
  have h1 : R.coeff 1-b = algebraMap ℚ L (P.coeff 1) := by
    have he := congrArg (fun p : L[X] => p.coeff 1) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, h0, mul_one, coeff_map] using he
  have h2 : R.coeff 2-b*R.coeff 1 = algebraMap ℚ L (P.coeff 2) := by
    have he := congrArg (fun p : L[X] => p.coeff 2) hR'
    simpa only [coeff_sub, coeff_mul_X, coeff_C_mul, coeff_map] using he
  have ht0 : ℓ 1 = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 0) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X_zero, add_zero, h0, coeff_zero] using he
  have ht1 : ℓ (R.coeff 1) + ℓ b = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 1) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul, h0, mul_one,
      map_add, coeff_zero] using he
  have ht2 : ℓ (R.coeff 2) + ℓ (b*R.coeff 1) = 0 := by
    have he := congrArg (fun p : ℚ[X] => p.coeff 2) hT
    simpa only [coeff_polyLinear, T, coeff_add, coeff_mul_X, coeff_C_mul,
      map_add, coeff_zero] using he
  have hlQ (c : ℚ) : ℓ (algebraMap ℚ L c) = 0 := by
    have he : algebraMap ℚ L c = c • (1:L) := by rw [Algebra.smul_def, mul_one]
    rw [he, map_smul, ht0, smul_zero]
  have hh1 := congrArg ℓ h1
  rw [map_sub, hlQ] at hh1
  have hb0 : ℓ b = 0 := by linarith
  have hh2 := congrArg ℓ h2
  rw [map_sub, hlQ] at hh2
  have hbR : ℓ (b*R.coeff 1) = 0 := by linarith
  have hR1 : R.coeff 1 = algebraMap ℚ L (P.coeff 1)+b := sub_eq_iff_eq_add.mp h1
  rw [hR1, mul_add, map_add] at hbR
  have he : b*algebraMap ℚ L (P.coeff 1) = (P.coeff 1) • b := by
    rw [Algebra.smul_def, mul_comm]
  rw [he, map_smul, hb0, smul_zero, zero_add, ← sq] at hbR
  exact ⟨ht0,hb0,hbR⟩

end EuclideanFiveColor.AlgebraicCayley

end

noncomputable section
open Polynomial
namespace EuclideanFiveColor.AlgebraicCayley
variable {L : Type*} [Field L] [Algebra ℚ L]

lemma linearFraction_polynomials (a b c d : L) (hc : c ≠ 0)
    (hb : IsAlgebraic ℚ (-d/c)) (ℓ : L →ₗ[ℚ] ℚ)
    (hd : ∀ t : ℚ, c+d*algebraMap ℚ L t ≠ 0) :
    ∃ P Q : ℚ[X], ∀ t : ℚ, Q.eval t ≠ 0 ∧
      P.eval t = Q.eval t * ℓ ((a+b*algebraMap ℚ L t)/(c+d*algebraMap ℚ L t)) := by
  obtain ⟨Q,R,hQ,hR,hQreg⟩ := reciprocal_denominator (-d/c) hb
  clear hQ
  have hdn (t : ℚ) : 1-(-d/c)*algebraMap ℚ L t ≠ 0 := by
    intro hh
    apply hd t
    have he : c+d*algebraMap ℚ L t = c*(1-(-d/c)*algebraMap ℚ L t) := by
      field_simp
      ring
    rw [he, hh, mul_zero]
  let U : L[X] := (C (a/c)+C (b/c)*X)*R
  refine ⟨polyLinear ℓ U,Q,fun t => ⟨hQreg t (hdn t),?_⟩⟩
  rw [eval_polyLinear]
  have hRt := congrArg (Polynomial.eval (algebraMap ℚ L t)) hR
  simp only [eval_mul, eval_sub, eval_one, eval_C, eval_X, eval_map, eval₂_at_apply] at hRt
  have he : U.eval (algebraMap ℚ L t) =
      (Q.eval t) • ((a+b*algebraMap ℚ L t)/(c+d*algebraMap ℚ L t)) := by
    dsimp only [U]
    simp only [eval_mul, eval_add, eval_C, eval_X, Algebra.smul_def]
    rw [← hRt, ← mul_div_assoc, eq_div_iff (hd t)]
    field_simp
    ring
  rw [he, map_smul, smul_eq_mul]

lemma rational_functions_avoid {ι : Type*} (s : Finset ι) (f : ι → ℚ → ℚ)
    (hpoly : ∀ i ∈ s, ∃ P Q : ℚ[X], ∀ t, Q.eval t ≠ 0 ∧ P.eval t = Q.eval t*f i t)
    (hn : ∀ i ∈ s, ∃ t, f i t ≠ 0) :
    ∃ t, ∀ i ∈ s, f i t ≠ 0 := by
  classical
  choose P Q hQ using fun i : s => hpoly i i.property
  have hP (i : s) : P i ≠ 0 := by
    obtain ⟨t,ht⟩ := hn i i.property
    intro he
    have hh := (hQ i t).2
    rw [he, eval_zero] at hh
    exact mul_ne_zero (hQ i t).1 ht hh.symm
  have hz : (∏ i : s, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ _ => hP _)
  obtain ⟨t,ht⟩ : ∃ t : ℚ, (∏ i : s, P i).eval t ≠ 0 := by
    by_contra! hn
    exact hz (Polynomial.funext fun t => by simpa using hn t)
  refine ⟨t,fun i hi hh => ?_⟩
  have hpt : (P ⟨i,hi⟩).eval t ≠ 0 := by
    rw [eval_prod] at ht
    exact Finset.prod_ne_zero_iff.mp ht _ (Finset.mem_univ _)
  apply hpt
  rw [(hQ ⟨i,hi⟩ t).2, hh, mul_zero]

lemma finite_hyperplanes_avoid {T : Type*} [Nonempty T]
    (f : T → L) (line : T → T → ℚ → T)
    (hzero : ∀ a b, line a b 0 = a) (hone : ∀ a b, line a b 1 = b)
    (hline : ∀ a b (ℓ : L →ₗ[ℚ] ℚ), ∃ P Q : ℚ[X], ∀ t,
      Q.eval t ≠ 0 ∧ P.eval t = Q.eval t * ℓ (f (line a b t)))
    (s : Finset (L →ₗ[ℚ] ℚ)) (hs : ∀ ℓ ∈ s, ∃ t, ℓ (f t) ≠ 0) :
    ∃ t, ∀ ℓ ∈ s, ℓ (f t) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary T, by simp⟩
  | @insert ℓ s hℓ ih =>
    obtain ⟨a,ha⟩ := ih (fun ψ hψ => hs ψ (Finset.mem_insert_of_mem hψ))
    obtain ⟨b,hb⟩ := hs ℓ (Finset.mem_insert_self _ _)
    obtain ⟨t,ht⟩ := rational_functions_avoid (insert ℓ s)
      (fun ψ t => ψ (f (line a b t))) (fun ψ _ => hline a b ψ) (by
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · exact ⟨1,by simpa only [hone] using hb⟩
        · exact ⟨0,by simpa only [hzero] using ha ψ hψ⟩)
    exact ⟨line a b t,ht⟩
end EuclideanFiveColor.AlgebraicCayley
end

noncomputable section
open Polynomial
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley
variable (N : IntermediateField ℚ ℂ)
private def realSlice : Subfield ℝ := N.toSubfield.comap Complex.ofRealHom
private def asN : realSlice N →+* N where
  toFun a := ⟨(a : ℝ),a.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp
@[simp] lemma coe_asN (a : realSlice N) : ((asN N a : N) : ℂ) = (a : ℝ) := rfl
variable (hi : Complex.I ∈ N)
private def iN : N := ⟨Complex.I, hi⟩
@[simp] lemma coe_iN : ((iN N hi : N) : ℂ) = Complex.I := rfl
lemma iN_sq : iN N hi ^2 = -1 := by ext; exact Complex.I_sq
lemma cayley_den_ne (a : realSlice N) : 1-iN N hi*asN N a ≠ 0 := by
  intro h
  have hh := congrArg (fun z : N => (z : ℂ).re) h
  simp [iN, asN] at hh

private def realCayley (a : realSlice N) : N :=
  (1+iN N hi*asN N a)/(1-iN N hi*asN N a)
lemma cayley_real_norm (a : realSlice N) : ‖((realCayley N hi a : N) : ℂ)‖ = 1 := by
  change ‖(1+Complex.I*(a:ℝ))/(1-Complex.I*(a:ℝ))‖ = 1
  have hn : ‖(1+Complex.I*(a:ℝ))‖ = ‖(1-Complex.I*(a:ℝ))‖ := by
    have he : conj (1+Complex.I*(a:ℝ)) = 1-Complex.I*(a:ℝ) := by simp; ring
    rw [← he, Complex.norm_conj]
  rw [norm_div, hn, div_self]
  apply norm_ne_zero_iff.mpr
  intro hz
  have he := congrArg Complex.re hz
  simp at he

variable [FiniteDimensional ℚ N]
lemma cayley_functional_escape
    (hre : ∀ z : N, ((z : ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z : ℂ).im : ℂ) ∈ N)
    (ℓ : N →ₗ[ℚ] ℚ) (hℓ : ℓ ≠ 0) :
    ∃ a : realSlice N, ℓ (realCayley N hi a) ≠ 0 := by
  by_contra! hh
  have hx (a : realSlice N) : ℓ 1 = 0 ∧ ℓ (iN N hi*asN N a) = 0 ∧
      ℓ ((asN N a)^2) = 0 := by
    have he (t : ℚ) : asN N (a*algebraMap ℚ (realSlice N) t) =
        asN N a*algebraMap ℚ N t := by simp
    have hd (t : ℚ) : 1-(iN N hi*asN N a)*algebraMap ℚ N t ≠ 0 := by
      simpa only [he, mul_assoc] using cayley_den_ne N hi (a*algebraMap ℚ (realSlice N) t)
    have ha (t : ℚ) : ℓ ((1+(iN N hi*asN N a)*algebraMap ℚ N t)/
        (1-(iN N hi*asN N a)*algebraMap ℚ N t)) = 0 := by
      simpa only [realCayley, he, mul_assoc] using hh (a*algebraMap ℚ (realSlice N) t)
    obtain ⟨h1,hia,hsa⟩ := cayley_annihilation (iN N hi*asN N a)
      (Algebra.IsAlgebraic.isAlgebraic _) ℓ hd ha
    rw [mul_pow, iN_sq, neg_one_mul, map_neg, neg_eq_zero] at hsa
    exact ⟨h1,hia,hsa⟩
  have hreal (a : realSlice N) : ℓ (asN N a) = 0 := by
    have h1 := (hx (a+1)).2.2
    have h2 := (hx (a-1)).2.2
    have he : (asN N (a+1))^2-(asN N (a-1))^2 = (4:ℚ) • asN N a := by
      simp only [map_add, map_one, map_sub, Algebra.smul_def, map_ofNat]
      ring
    have hh := congrArg ℓ he
    rw [map_sub, h1,h2,sub_self,map_smul,smul_eq_mul] at hh
    linarith
  apply hℓ
  ext z
  let a : realSlice N := ⟨(z:ℂ).re,hre z⟩
  let b : realSlice N := ⟨(z:ℂ).im,him z⟩
  have he : z = asN N a+iN N hi*asN N b := by
    apply Subtype.ext
    change (z:ℂ) = (z:ℂ).re+Complex.I*(z:ℂ).im
    rw [mul_comm]
    exact (Complex.re_add_im _).symm
  rw [he,map_add,hreal,(hx b).2.1,add_zero]
  rfl

private def realLine (a b : realSlice N) (t : ℚ) : realSlice N :=
  a+algebraMap ℚ (realSlice N) t*(b-a)
omit [FiniteDimensional ℚ N] in
@[simp] lemma realLine_zero (a b : realSlice N) : realLine N a b 0 = a := by simp [realLine]
omit [FiniteDimensional ℚ N] in
@[simp] lemma realLine_one (a b : realSlice N) : realLine N a b 1 = b := by simp [realLine]
lemma cayley_line_polynomials (a b : realSlice N) (ℓ : N →ₗ[ℚ] ℚ) :
    ∃ P Q : ℚ[X], ∀ t, Q.eval t ≠ 0 ∧
      P.eval t = Q.eval t*ℓ (realCayley N hi (realLine N a b t)) := by
  let A := 1+iN N hi*asN N a
  let B := iN N hi*(asN N b-asN N a)
  let C := 1-iN N hi*asN N a
  let D := -iN N hi*(asN N b-asN N a)
  have he (t : ℚ) : asN N (realLine N a b t) =
      asN N a+algebraMap ℚ N t*(asN N b-asN N a) := by simp [realLine]
  have hd (t : ℚ) : C+D*algebraMap ℚ N t = 1-iN N hi*asN N (realLine N a b t) := by
    rw [he]; dsimp [C,D]; ring
  have hn (t : ℚ) : A+B*algebraMap ℚ N t = 1+iN N hi*asN N (realLine N a b t) := by
    rw [he]; dsimp [A,B]; ring
  obtain ⟨P,Q,hPQ⟩ := linearFraction_polynomials A B C D (cayley_den_ne N hi a)
    (Algebra.IsAlgebraic.isAlgebraic _) ℓ (fun t => by rw [hd]; exact cayley_den_ne N hi _)
  refine ⟨P,Q,fun t => ?_⟩
  simpa only [hn,hd,realCayley] using hPQ t

lemma cayley_finite_avoid
    (hre : ∀ z : N, ((z : ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z : ℂ).im : ℂ) ∈ N)
    (s : Finset (N →ₗ[ℚ] ℚ)) (hs : ∀ ℓ ∈ s, ℓ ≠ 0) :
    ∃ a : realSlice N, ∀ ℓ ∈ s, ℓ (realCayley N hi a) ≠ 0 :=
  finite_hyperplanes_avoid (realCayley N hi) (realLine N)
    (realLine_zero N) (realLine_one N) (cayley_line_polynomials N hi) s
    (fun ℓ hℓ => cayley_functional_escape N hi hre him ℓ (hs ℓ hℓ))
end EuclideanFiveColor.AlgebraicCayley
end

noncomputable section
open Module
namespace EuclideanFiveColor.GeneralPosition
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

private def General (s : Finset V) : Prop :=
  ∀ t ⊆ s, t.card ≤ finrank ℚ V → LinearIndepOn ℚ id (t : Set V)

omit [FiniteDimensional ℚ V] in

lemma exists_general (A : Set V) (hd : 2 ≤ finrank ℚ V)
    (ha : ∀ P : Finset (Submodule ℚ V), (∀ p ∈ P, p < ⊤) →
      ∃ x ∈ A, ∀ p ∈ P, x ∉ p) (n : ℕ) :
    ∃ s : Finset V, s.card = n ∧ (s : Set V) ⊆ A ∧ General s := by
  classical
  induction n with
  | zero =>
    refine ⟨∅,rfl,by simp,?_⟩
    intro t ht _
    have : t = ∅ := Finset.subset_empty.mp ht
    simp [this, linearIndepOn_empty]
  | succ n ih =>
    obtain ⟨s,hs,hA,hg⟩ := ih
    let B := s.powerset.filter (fun t => t.card < finrank ℚ V)
    let P := B.image (fun t : Finset V => Submodule.span ℚ (t : Set V))
    have hP : ∀ p ∈ P, p < ⊤ := by
      intro p hp
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hp
      have hc : t.card < finrank ℚ V := (Finset.mem_filter.mp ht).2
      apply Submodule.lt_top_of_finrank_lt_finrank
      exact (finrank_span_finset_le_card t).trans_lt hc
    obtain ⟨x,hx,havoid⟩ := ha P hP
    have havo (t : Finset V) (ht : t ⊆ s) (hc : t.card < finrank ℚ V) :
        x ∉ Submodule.span ℚ (t : Set V) := by
      apply havoid _
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ht,hc⟩,rfl⟩
    have hxs : x ∉ s := by
      intro hh
      exact havo {x} (Finset.singleton_subset_iff.mpr hh) (by simpa only [Finset.card_singleton] using (show 1 < finrank ℚ V by omega))
        (Submodule.subset_span (by simp))
    refine ⟨insert x s,by simp [hxs,hs],?_,?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hA hy
    · intro t ht hc
      by_cases hxt : x ∈ t
      · have hts : t.erase x ⊆ s := by
          intro y hy
          obtain ⟨hyx,hyt⟩ := Finset.mem_erase.mp hy
          exact (Finset.mem_insert.mp (ht hyt)).resolve_left hyx
        have hct : (t.erase x).card < finrank ℚ V := by
          rw [Finset.card_erase_of_mem hxt]
          have hp := Finset.card_pos.mpr ⟨x,hxt⟩
          omega
        have hli := hg (t.erase x) hts hct.le
        have hn := havo (t.erase x) hts hct
        have hh := (linearIndepOn_id_insert (K := ℚ) (by simp : x ∉ (t.erase x : Set V))).mpr ⟨hli,hn⟩
        simpa only [← Finset.coe_insert, Finset.insert_erase hxt] using hh
      · exact hg t (by
          intro y hy
          exact (Finset.mem_insert.mp (ht hy)).resolve_left (fun he => hxt (he ▸ hy))) hc

lemma General.spans {s t : Finset V} (hs : General s) (ht : t ⊆ s)
    (hc : t.card = finrank ℚ V) : Submodule.span ℚ (t : Set V) = ⊤ := by
  have hli := hs t ht hc.le
  have hr : finrank ℚ (Submodule.span ℚ (t : Set V)) = finrank ℚ V :=
    (finrank_span_finset_eq_card hli).trans hc
  exact Submodule.eq_top_of_finrank_eq hr

end EuclideanFiveColor.GeneralPosition
end

noncomputable section
open Module
open scoped ComplexConjugate
namespace EuclideanFiveColor.AlgebraicCayley

private def generatingSet (s : Finset ℂ) : Finset ℂ :=
  {Complex.I} ∪ s.image (fun z => (z.re : ℂ)) ∪ s.image (fun z => (z.im : ℂ))
private def generatedField (s : Finset ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (generatingSet s : Set ℂ)
lemma generatedField_I (s : Finset ℂ) : Complex.I ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp [generatingSet]
lemma generatedField_real (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) :
    (z.re : ℂ) ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp only [generatingSet, Finset.mem_coe, Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨z,hz,rfl⟩))
lemma generatedField_imag (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) :
    (z.im : ℂ) ∈ generatedField s := by
  apply IntermediateField.subset_adjoin
  simp only [generatingSet, Finset.mem_coe, Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
lemma generatedField_contains (s : Finset ℂ) (z : ℂ) (hz : z ∈ s) : z ∈ generatedField s := by
  rw [← Complex.re_add_im z]
  exact (generatedField s).add_mem (generatedField_real s z hz)
    ((generatedField s).mul_mem (generatedField_imag s z hz) (generatedField_I s))
lemma generatedField_conj (s : Finset ℂ) {z : ℂ} (hz : z ∈ generatedField s) :
    conj z ∈ generatedField s := by
  induction hz using IntermediateField.adjoin_induction ℚ with
  | mem z hz =>
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · have : z = Complex.I := Finset.mem_singleton.mp hz
        rw [this,Complex.conj_I]
        exact (generatedField s).neg_mem (generatedField_I s)
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        simpa using generatedField_real s w hw
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      simpa using generatedField_imag s w hw
  | algebraMap r => simp
  | add x y hx hy ihx ihy => simpa using (generatedField s).add_mem ihx ihy
  | inv x hx ihx => simpa using (generatedField s).inv_mem ihx
  | mul x y hx hy ihx ihy => simpa using (generatedField s).mul_mem ihx ihy
lemma generatedField_re_closed (s : Finset ℂ) (z : generatedField s) :
    ((z:ℂ).re : ℂ) ∈ generatedField s := by
  rw [Complex.re_eq_add_conj]
  exact (generatedField s).div_mem ((generatedField s).add_mem z.property
    (generatedField_conj s z.property)) (by norm_cast; exact (generatedField s).natCast_mem 2)
lemma generatedField_im_closed (s : Finset ℂ) (z : generatedField s) :
    ((z:ℂ).im : ℂ) ∈ generatedField s := by
  rw [Complex.im_eq_sub_conj]
  exact (generatedField s).div_mem ((generatedField s).sub_mem z.property
    (generatedField_conj s z.property)) ((generatedField s).mul_mem
      (by norm_cast; exact (generatedField s).natCast_mem 2) (generatedField_I s))

lemma generatedField_finite (s : Finset ℂ) (hs : ∀ z ∈ s, IsAlgebraic ℚ z) :
    FiniteDimensional ℚ (generatedField s) := by
  have hiAlg : IsAlgebraic ℚ Complex.I := IsAlgebraic.of_pow (n := 2) (by norm_num) (by
    rw [Complex.I_sq]; exact isAlgebraic_one.neg)
  apply IntermediateField.finiteDimensional_adjoin
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · rcases Finset.mem_union.mp hz with hz | hz
    · have : z = Complex.I := Finset.mem_singleton.mp hz
      rw [this]
      exact hiAlg.isIntegral
    · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      rw [Complex.re_eq_add_conj, div_eq_mul_inv]
      exact ((hs w hw).add (IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
        (hs w hw))).mul (isAlgebraic_natCast 2).inv |>.isIntegral
  · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    rw [Complex.im_eq_sub_conj, div_eq_mul_inv]
    exact ((hs w hw).sub (IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom
      (hs w hw))).mul ((isAlgebraic_natCast 2).mul hiAlg).inv |>.isIntegral

lemma finrank_ge_two (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) : 2 ≤ finrank ℚ N := by
  have hp : 0 < finrank ℚ N := finrank_pos
  by_contra! hh
  have he : finrank ℚ N = 1 := by omega
  obtain ⟨q,hq⟩ := (finrank_eq_one_iff_of_nonzero' (1:N) one_ne_zero).mp he (iN N hi)
  have hqc := congrArg (fun z : N => (z:ℂ).im) hq
  simp [iN,Algebra.smul_def] at hqc

lemma cayley_subspaces_avoid (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) (hre : ∀ z : N, ((z:ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z:ℂ).im : ℂ) ∈ N)
    (P : Finset (Submodule ℚ N)) (hP : ∀ p ∈ P, p < ⊤) :
    ∃ x : N, ‖(x:ℂ)‖ = 1 ∧ ∀ p ∈ P, x ∉ p := by
  classical
  choose ℓ hn hker using fun p : P => Submodule.exists_le_ker_of_lt_top p.val (hP p p.property)
  let s : Finset (N →ₗ[ℚ] ℚ) := Finset.univ.image ℓ
  have hs : ∀ ψ ∈ s, ψ ≠ 0 := by
    intro ψ hψ
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hψ
    exact hn p
  obtain ⟨a,ha⟩ := cayley_finite_avoid N hi hre him s hs
  refine ⟨realCayley N hi a,cayley_real_norm N hi a,fun p hp hx => ?_⟩
  exact ha (ℓ ⟨p,hp⟩) (Finset.mem_image.mpr ⟨⟨p,hp⟩,Finset.mem_univ _,rfl⟩) (hker ⟨p,hp⟩ hx)

lemma numberField_general_position (N : IntermediateField ℚ ℂ) [FiniteDimensional ℚ N]
    (hi : Complex.I ∈ N) (hre : ∀ z : N, ((z:ℂ).re : ℂ) ∈ N)
    (him : ∀ z : N, ((z:ℂ).im : ℂ) ∈ N) (n : ℕ) :
    ∃ s : Finset N, s.card = n ∧ (∀ z ∈ s, ‖(z:ℂ)‖ = 1) ∧ GeneralPosition.General s := by
  obtain ⟨s,hs,hA,hg⟩ := GeneralPosition.exists_general {z : N | ‖(z:ℂ)‖ = 1}
    (finrank_ge_two N hi) (cayley_subspaces_avoid N hi hre him) n
  exact ⟨s,hs,hA,hg⟩
end EuclideanFiveColor.AlgebraicCayley
end

end ParishSpectral
end

-- OAI.Analysis.PlaneSpectrum.Selections
section
namespace ParishSpectral

noncomputable section
open Module
namespace EuclideanFiveColor.GeneralPosition
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

lemma spanning_selection {ι : Type*} (Q : Finset ι) (S : Finset V) (hS : General S)
    (hcard : Q.card*(finrank ℚ V-1) < S.card)
    (A : ι → V → Prop) (hA : ∀ x ∈ S, ∃ i ∈ Q, A i x) :
    ∃ i ∈ Q, ∃ T ⊆ S, T.card = finrank ℚ V ∧
      Submodule.span ℚ (T : Set V) = ⊤ ∧ ∀ x ∈ T, A i x := by
  classical
  choose f hfQ hfA using fun x : S => hA x x.property
  have hs : Fintype.card Q * (finrank ℚ V-1) < Fintype.card S := by simpa using hcard
  let g : S → Q := fun x => ⟨f x,hfQ x⟩
  obtain ⟨i,hi⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card g hs
  have hi' : finrank ℚ V ≤ (S.filter (fun x => A i x)).card := by
    have hx : (Finset.univ.filter (fun x : S => g x = i)).card ≤
        (S.filter (fun x => A i x)).card := by
      apply Finset.card_le_card_of_injOn (fun x : S => x.val)
      · intro x hx
        have hg : g x = i := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨x.property,by
          have hh := hfA x
          change A (g x).val x.val at hh
          rwa [hg] at hh⟩
      · intro x hx y hy hxy
        exact Subtype.ext hxy
    omega
  obtain ⟨T,hT,hTc⟩ := Finset.exists_subset_card_eq hi'
  have hTS : T ⊆ S := fun x hx => (Finset.mem_filter.mp (hT hx)).1
  exact ⟨i,i.property,T,hTS,hTc,hS.spans hTS hTc, fun x hx => (Finset.mem_filter.mp (hT hx)).2⟩
end EuclideanFiveColor.GeneralPosition
end

noncomputable section
namespace EuclideanFiveColor.Arithmetic

lemma common_denominator {ι : Type*} [Fintype ι] (c : ι → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ a : ι → ℤ, ∀ i, (D:ℚ)*c i = a i := by
  classical
  let D := ∏ i, (c i).den
  let a := fun i => ((∏ j ∈ Finset.univ.erase i, (c j).den : ℕ) : ℤ)*(c i).num
  refine ⟨D,Finset.prod_pos (fun _ _ => Rat.den_pos _),a,fun i => ?_⟩
  have hD : D = (∏ j ∈ Finset.univ.erase i, (c j).den)*(c i).den :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  rw [hD, Nat.cast_mul, mul_assoc, Rat.den_mul_eq_num]
  simp only [a, Int.cast_mul, Int.cast_natCast]

lemma uniform_integral_representations {ι : Type*} [Fintype ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (v : ∀ i, κ i → V) (x y : V)
    (hx : ∀ i, ∃ c : κ i → ℚ, ∑ j, c j • v i j = x)
    (hy : ∀ i, ∃ c : κ i → ℚ, ∑ j, c j • v i j = y) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∃ a b : ∀ i, κ i → ℤ, ∀ i : ι,
      (∑ j, a i j • v i j) = D • x ∧
      (∑ j, b i j • v i j) = D • y ∧
      (∑ j : κ i, ((a i j).natAbs+(b i j).natAbs)) ≤ M := by
  classical
  choose c hc using hx
  choose d hd using hy
  let f : (Σ i, κ i) × Bool → ℚ := fun p => if p.2 then c p.1.1 p.1.2 else d p.1.1 p.1.2
  obtain ⟨D,hD,A,hA⟩ := common_denominator f
  let a := fun (i : ι) (j : κ i) => A (⟨i,j⟩,true)
  let b := fun (i : ι) (j : κ i) => A (⟨i,j⟩,false)
  let m := fun i => ∑ j : κ i, ((a i j).natAbs+(b i j).natAbs)
  let M := (∑ i, m i)+1
  refine ⟨D,M,hD,Nat.zero_lt_succ _,a,b,fun i => ⟨?_,?_,?_⟩⟩
  · calc
      (∑ j, a i j • v i j) = ∑ j, ((D:ℚ)*c i j) • v i j := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := hA (⟨i,j⟩,true)
        simp only [f,ite_true] at hh
        rw [hh,Int.cast_smul_eq_zsmul]
      _ = (D:ℚ) • ∑ j, c i j • v i j := by simp only [Finset.smul_sum,smul_smul]
      _ = D • x := by rw [hc,Nat.cast_smul_eq_nsmul]
  · calc
      (∑ j, b i j • v i j) = ∑ j, ((D:ℚ)*d i j) • v i j := by
        apply Finset.sum_congr rfl
        intro j _
        have hh := hA (⟨i,j⟩,false)
        simp only [f,Bool.false_eq_true,ite_false] at hh
        rw [hh,Int.cast_smul_eq_zsmul]
      _ = (D:ℚ) • ∑ j, d i j • v i j := by simp only [Finset.smul_sum,smul_smul]
      _ = D • y := by rw [hd,Nat.cast_smul_eq_nsmul]
  · exact (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)).trans (Nat.le_succ _)
end EuclideanFiveColor.Arithmetic
end

noncomputable section
open Module
namespace EuclideanFiveColor.Arithmetic
open AlgebraicCayley GeneralPosition

lemma span_mult_rep (N : IntermediateField ℚ ℂ) (T : Finset N)
    (hT : Submodule.span ℚ (T : Set N) = ⊤) (q : N) (hq : q ≠ 0) (x : N) :
    ∃ c : T → ℚ, ∑ j, c j • (q*j.val) = x := by
  have hs : Set.range (fun j : T => j.val) = (T : Set N) := Subtype.range_coe
  have hx : q⁻¹*x ∈ Submodule.span ℚ (Set.range (fun j : T => j.val)) := by rw [hs,hT]; trivial
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  refine ⟨c,?_⟩
  calc
    (∑ j, c j • (q*j.val)) = q * ∑ j, c j • j.val := by
      simp only [Finset.mul_sum, mul_smul_comm]
    _ = x := by rw [hc,← mul_assoc,mul_inv_cancel₀ hq,one_mul]

lemma uniform_selection (Q : Finset ℂ)
    (hQn : ∀ q ∈ Q, ‖q‖ = 1) (hQa : ∀ q ∈ Q, IsAlgebraic ℚ q)
    (A : ℂ → Prop)
    (hA : ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v → ∃ q ∈ Q, A (q*v)) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∀ v : ℂ, ‖v‖ = 1 → IsAlgebraic ℚ v →
      ∃ n : ℕ, ∃ k : Fin n → ℂ, ∃ a b : Fin n → ℤ,
        (∀ j, ‖k j‖ = 1 ∧ IsAlgebraic ℚ (k j) ∧ A (k j*v)) ∧
        (∑ j, a j • k j) = D • (1:ℂ) ∧
        (∑ j, b j • k j) = D • Complex.I ∧
        (∑ j, ((a j).natAbs+(b j).natAbs)) ≤ M := by
  classical
  let N := generatedField Q
  have : FiniteDimensional ℚ N := generatedField_finite Q hQa
  obtain ⟨S,hSc,hSn,hSg⟩ := numberField_general_position N (generatedField_I Q)
    (generatedField_re_closed Q) (generatedField_im_closed Q)
    (Q.card*(finrank ℚ N-1)+1)
  let TS : Finset (Finset N) := S.powerset.filter (fun T => Submodule.span ℚ (T:Set N) = ⊤)
  let I := Q × TS
  let κ : I → Type := fun i => i.2.val
  let qs : Q → N := fun q => ⟨q.val,generatedField_contains Q q.val q.property⟩
  have hqs (q : Q) : qs q ≠ 0 := by
    intro he
    have hec := congrArg (fun z : N => (z:ℂ)) he
    have hn := hQn q q.property
    change q.val = 0 at hec
    simp [hec] at hn
  let k : ∀ i : I, κ i → N := fun i j => qs i.1*j.val
  have hs (i : I) : Submodule.span ℚ (i.2.val:Set N) = ⊤ := (Finset.mem_filter.mp i.2.property).2
  obtain ⟨D,M,hD,hM,a,b,hab⟩ := uniform_integral_representations k (1:N) (iN N (generatedField_I Q))
    (fun i => span_mult_rep N i.2.val (hs i) _ (hqs _) _)
    (fun i => span_mult_rep N i.2.val (hs i) _ (hqs _) _)
  refine ⟨D,M,hD,hM,fun v hv hva => ?_⟩
  have hAlg (z : N) : IsAlgebraic ℚ (z:ℂ) :=
    IsAlgebraic.algHom N.val (IsAlgebraic.of_finite ℚ z)
  obtain ⟨q,hq,T,hTS,hTc,hTspan,hTA⟩ := spanning_selection Q S hSg (by omega)
    (fun q s => A (q*(s:ℂ)*v)) (by
      intro s hs
      have hn : ‖(s:ℂ)*v‖ = 1 := by rw [norm_mul,hSn s hs,hv,one_mul]
      obtain ⟨q,hq,hqA⟩ := hA ((s:ℂ)*v) hn ((hAlg s).mul hva)
      exact ⟨q,hq,by simpa only [mul_assoc] using hqA⟩)
  have hTmem : T ∈ TS := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hTS,hTspan⟩
  let i : I := (⟨q,hq⟩,⟨T,hTmem⟩)
  let e := (Fintype.equivFin (κ i)).symm
  refine ⟨Fintype.card (κ i),fun j => (k i (e j):ℂ),fun j => a i (e j),fun j => b i (e j),?_,?_,?_,?_⟩
  · intro j
    have hj : (e j).val ∈ T := (e j).property
    refine ⟨?_,hAlg (k i (e j)),?_⟩
    · change ‖q*((e j).val:ℂ)‖ = 1
      rw [norm_mul,hQn q hq,hSn _ (hTS hj),one_mul]
    · exact hTA _ hj
  · have he := congrArg (fun z : N => (z:ℂ)) (hab i).1
    push_cast at he
    rw [← he]
    exact Fintype.sum_equiv e _ _ (fun _ => by simp)
  · have he := congrArg (fun z : N => (z:ℂ)) (hab i).2.1
    push_cast at he
    change (∑ j, b i j • (k i j:ℂ)) = D • Complex.I at he
    rw [← he]
    exact Fintype.sum_equiv e _ _ (fun _ => by simp)
  · rw [Fintype.sum_equiv e _ (fun j => (a i j).natAbs+(b i j).natAbs) (fun _ => rfl)]
    exact (hab i).2.2

lemma uniform_selection_of_template (E : Set ℂ) (hE : PlaneFiveColor.Spectral.TemplateProperty E)
    (hEmul : ∀ a ∈ E, ∀ b ∈ E, a*b ∈ E) (Q : Finset ℂ)
    (hQn : ∀ q ∈ Q, ‖q‖ = 1) (hQa : ∀ q ∈ Q, q ∈ E)
    (A : ℂ → Prop)
    (hA : ∀ v : ℂ, ‖v‖ = 1 → v ∈ E → ∃ q ∈ Q, A (q*v)) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ ∀ v : ℂ, ‖v‖ = 1 → v ∈ E →
      ∃ n : ℕ, ∃ k : Fin n → ℂ, ∃ a b : Fin n → ℤ,
        (∀ j, ‖k j‖ = 1 ∧ k j ∈ E ∧ A (k j*v)) ∧
        (∑ j, a j • k j) = D • (1:ℂ) ∧
        (∑ j, b j • k j) = D • Complex.I ∧
        (∑ j, ((a j).natAbs+(b j).natAbs)) ≤ M := by
  classical
  obtain ⟨S,hSa,hS⟩ := hE Q (fun q hq => ⟨hQa q hq,hQn q hq⟩)
  let k : ∀ i : S → Q, S → ℂ := fun i s => (i s:ℂ)*s
  let jf : (S → Q) → ℂ → ℂ := fun i z => if h : z ∈ S then (i ⟨z,h⟩:ℂ) else 0
  have hspan (i : S → Q) (x : ℂ)
      (hx : x ∈ Submodule.span ℚ ((fun s => jf i s*s) '' (S:Set ℂ))) :
      ∃ c : S → ℚ, ∑ s, c s • k i s = x := by
    have he : (fun s => jf i s*s) '' (S:Set ℂ) = Set.range (k i) := by
      ext z
      constructor
      · rintro ⟨s,hs,rfl⟩
        exact ⟨⟨s,hs⟩,by simp [k,jf,Finset.mem_coe.mp hs]⟩
      · rintro ⟨s,rfl⟩
        exact ⟨s,s.property,by simp [k,jf]⟩
    rw [he] at hx
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp hx
  have hj (i : S → Q) : ∀ s ∈ S, jf i s ∈ Q := fun s hs => by simp [jf,hs]
  obtain ⟨D,M,hD,hM,a,b,hab⟩ := uniform_integral_representations (κ := fun _ : S → Q => S)
    k (1:ℂ) Complex.I
    (fun i => hspan i 1 (hS (jf i) (hj i)).1)
    (fun i => hspan i Complex.I (hS (jf i) (hj i)).2)
  refine ⟨D,M,hD,hM,fun v hv hva => ?_⟩
  have hc (s : S) : ∃ q ∈ Q, A (q*((s:ℂ)*v)) :=
    hA _ (by rw [norm_mul,(hSa s s.property).2,hv,one_mul]) (hEmul _ (hSa s s.property).1 _ hva)
  choose f hfQ hfA using hc
  let i : S → Q := fun s => ⟨f s,hfQ s⟩
  let e := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S,fun j => k i (e j),fun j => a i (e j),fun j => b i (e j),?_,?_,?_,?_⟩
  · intro j
    refine ⟨?_,hEmul _ (hQa _ (hfQ _)) _ (hSa _ (e j).property).1,?_⟩
    · change ‖f (e j)*((e j:S):ℂ)‖ = 1
      rw [norm_mul,hQn _ (hfQ _),hSa _ (e j).property |>.2,one_mul]
    · change A (f (e j)*((e j:S):ℂ)*v)
      rw [mul_assoc]
      exact hfA _
  · rw [← (hab i).1]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · rw [← (hab i).2.1]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  · rw [Fintype.sum_equiv e _ (fun j => (a i j).natAbs+(b i j).natAbs) (fun _ => rfl)]
    exact (hab i).2.2
end EuclideanFiveColor.Arithmetic
end

noncomputable section
namespace EuclideanFiveColor.Arithmetic

lemma real_sum_bound {ι : Type*} [Fintype ι] (a : ι → ℤ) (x : ι → ℝ) (B : ℝ)
    (hx : ∀ i, |x i| ≤ B) :
    |∑ i, (a i : ℝ)*x i| ≤ (∑ i, ((a i).natAbs : ℝ))*B := by
  calc
    _ ≤ ∑ i, |(a i:ℝ)*x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((a i).natAbs : ℝ)*B := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have he : |(a i:ℝ)| = ((a i).natAbs : ℝ) := by simp
      rw [he]
      exact mul_le_mul_of_nonneg_left (hx i) (Nat.cast_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma selection_transverse {ι : Type*} [Fintype ι] (k : ι → ℂ) (a b : ι → ℤ)
    (D M : ℕ) (hD : 0 < D)
    (ha : (∑ i, a i • k i) = D • (1:ℂ))
    (hb : (∑ i, b i • k i) = D • Complex.I)
    (hM : (∑ i, ((a i).natAbs+(b i).natAbs)) ≤ M)
    (v : ℂ) (hv : ‖v‖ = 1) :
    ∃ i, ∀ j, |(k j*v).re| ≤ |(k i*v).re| ∧
      (D:ℝ) ≤ (M:ℝ)*|(k i*v).re| := by
  classical
  have hn : Nonempty ι := by
    by_contra hh
    have : IsEmpty ι := not_nonempty_iff.mp hh
    have he : (D:ℂ) = 0 := by simpa using ha.symm
    have : D = 0 := by exact_mod_cast he
    omega
  have := hn
  obtain ⟨i,_,him⟩ := Finset.exists_max_image Finset.univ (fun j => |(k j*v).re|) Finset.univ_nonempty
  have hm (j : ι) : |(k j*v).re| ≤ |(k i*v).re| := him j (Finset.mem_univ j)
  have h1 : (∑ j, (a j:ℝ)*(k j*v).re) = (D:ℝ)*v.re := by
    have he := congrArg (fun z : ℂ => (z*v).re) ha
    simpa only [Finset.sum_mul, Complex.re_sum, zsmul_eq_mul, nsmul_eq_mul,
      mul_assoc, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.natCast_re, Complex.natCast_im, Complex.one_re, Complex.one_im,
      mul_one] using he
  have h2 : (∑ j, (b j:ℝ)*(k j*v).re) = -(D:ℝ)*v.im := by
    have he := congrArg (fun z : ℂ => (z*v).re) hb
    simpa only [Finset.sum_mul, Complex.re_sum, zsmul_eq_mul, nsmul_eq_mul,
      mul_assoc, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul,
      sub_zero, Complex.natCast_re, Complex.natCast_im, Complex.I_re, Complex.I_im,
      one_mul, zero_sub, mul_neg, neg_mul] using he
  have h1b := real_sum_bound a (fun j => (k j*v).re) _ hm
  have h2b := real_sum_bound b (fun j => (k j*v).re) _ hm
  rw [h1,abs_mul,abs_of_nonneg (Nat.cast_nonneg D)] at h1b
  rw [h2,abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg D)] at h2b
  have hcomp : 1 ≤ |v.re|+|v.im| := hv ▸ Complex.norm_le_abs_re_add_abs_im v
  have hMc : (∑ j, ((a j).natAbs:ℝ))+(∑ j, ((b j).natAbs:ℝ)) ≤ (M:ℝ) := by
    have he : ((∑ j, ((a j).natAbs+(b j).natAbs) : ℕ):ℝ) =
        (∑ j, ((a j).natAbs:ℝ))+(∑ j, ((b j).natAbs:ℝ)) := by
      simp [Finset.sum_add_distrib]
    rw [← he]
    exact_mod_cast hM
  have hexp := mul_le_mul_of_nonneg_right hMc (abs_nonneg (k i*v).re)
  have hfinal : (D:ℝ) ≤ (M:ℝ)*|(k i*v).re| := by
    nlinarith [mul_le_mul_of_nonneg_left hcomp (Nat.cast_nonneg D)]
  exact ⟨i,fun j => ⟨hm j,hfinal⟩⟩
end EuclideanFiveColor.Arithmetic
end

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable (m : α → ℝ) (hm0 : m 0 = 1)
  (hd : ∀ a b : α, 0 ≤ a → 0 ≤ b → m a * m b ≤ m |a-b|)
  (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)

private def Good (n : ℕ) (x : α) : Prop := c^n ≤ m x
include hc0 hc1 in
omit [Field α] [LinearOrder α] [IsStrictOrderedRing α] in
lemma good_mono {n k : ℕ} {x : α} (h : Good m c n x) (hnk : n ≤ k) : Good m c k x :=
  (pow_le_pow_of_le_one hc0 hc1 hnk).trans h
include hm0 hc0 hc1 in
omit [LinearOrder α] [IsStrictOrderedRing α] in
lemma good_zero (n : ℕ) : Good m c n 0 := by
  unfold Good
  rw [hm0]
  exact pow_le_one₀ hc0 hc1
include hd hc0 in
omit [IsStrictOrderedRing α] in
lemma good_diff {n k : ℕ} {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : Good m c n a) (hB : Good m c k b) : Good m c (n+k) |a-b| := by
  unfold Good at *
  rw [pow_add]
  exact (mul_le_mul hA hB (pow_nonneg hc0 k) ((pow_nonneg hc0 n).trans hA)).trans (hd a b ha hb)

variable {p : α} (hp : 0 < p) (hpG : Good m c 1 p)
include hd hc0 hc1 hp hpG in
lemma add_residues {a b : α} {n k : ℕ} (ha : a ∈ Set.Ico 0 p) (hb : b ∈ Set.Ico 0 p)
    (hA : Good m c n a) (hB : Good m c k b) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c (n+k+2) r ∧ ∃ j : ℤ, a+b = r+j•p := by
  obtain ⟨ha0, hap⟩ := ha
  obtain ⟨hb0, hbp⟩ := hb
  have ha : a ∈ Set.Ico 0 p := ⟨ha0,hap⟩
  have hb : b ∈ Set.Ico 0 p := ⟨hb0,hbp⟩
  by_cases hs : a+b < p
  · refine ⟨a+b, ⟨add_nonneg ha.1 hb.1, hs⟩, ?_, 0, by simp⟩
    have hpa : Good m c (1+n) (p-a) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr ha.2.le)] using
        good_diff m hd c hc0 hp.le ha.1 hpG hA
    have hsub : Good m c (1+n+k) ((p-a)-b) := by
      simpa only [abs_of_nonneg (show 0 ≤ (p-a)-b by linarith)] using
        good_diff m hd c hc0 (sub_nonneg.mpr ha.2.le) hb.1 hpa hB
    have hfinal := good_diff m hd c hc0 hp.le (show 0 ≤ (p-a)-b by linarith) hpG hsub
    have he : |p-((p-a)-b)| = a+b := by rw [abs_of_nonneg (by linarith)]; abel
    simpa only [he, show 1+(1+n+k) = n+k+2 by omega] using hfinal
  · refine ⟨a+b-p, ⟨by linarith, by linarith⟩, ?_, 1, by simp⟩
    have hpb : Good m c (1+k) (p-b) := by
      simpa only [abs_of_nonneg (sub_nonneg.mpr hb.2.le)] using
        good_diff m hd c hc0 hp.le hb.1 hpG hB
    have hfinal := good_diff m hd c hc0 ha.1 (sub_nonneg.mpr hb.2.le) hA hpb
    have he : |a-(p-b)| = a+b-p := by rw [abs_of_nonneg (by linarith)]; abel
    apply good_mono m c hc0 hc1 (n := n+(1+k)) (hnk := by omega)
    simpa only [he] using hfinal

include hm0 hd hc0 hc1 hp hpG in
lemma input_residue {x : α} (hx : |x| ≤ p) (hG : Good m c 1 |x|) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c 2 r ∧ ∃ j : ℤ, x = r+j•p := by
  by_cases hx0 : 0 ≤ x
  · have hxp : x ≤ p := by simpa [abs_of_nonneg hx0] using hx
    rcases lt_or_eq_of_le hxp with hlt | rfl
    · exact ⟨x, ⟨hx0,hlt⟩, good_mono m c hc0 hc1 (by simpa [abs_of_nonneg hx0] using hG) (by omega), 0, by simp⟩
    · exact ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 2, 1, by simp⟩
  · have hn : 0 < -x := neg_pos.mpr (lt_of_not_ge hx0)
    have hnx : -x ≤ p := by simpa [abs_of_neg (lt_of_not_ge hx0)] using hx
    rcases lt_or_eq_of_le hnx with hlt | heq
    · refine ⟨p+x, ⟨by linarith, by linarith⟩, ?_, -1, by simp⟩
      have hneg : Good m c 1 (-x) := by simpa [abs_of_neg (lt_of_not_ge hx0)] using hG
      have hfinal := good_diff m hd c hc0 hp.le hn.le hpG hneg
      simpa only [show |p- -x| = p+x by rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]] using hfinal
    · refine ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 2, -1, ?_⟩
      simp only [neg_smul, one_smul, zero_add]
      linarith

include hm0 hd hc0 hc1 hp hpG in
lemma list_residue (l : List α) (hl : ∀ x∈l, |x| ≤ p ∧ Good m c 1 |x|) :
    ∃ r : α, r ∈ Set.Ico 0 p ∧ Good m c (4*l.length) r ∧ ∃ j : ℤ, l.sum = r+j•p := by
  induction l with
  | nil => exact ⟨0, ⟨le_rfl,hp⟩, good_zero m hm0 c hc0 hc1 _, 0, by simp⟩
  | cons x l ih =>
    obtain ⟨a,ha,hA,i,hi⟩ := input_residue m hm0 hd c hc0 hc1 hp hpG (hl x (List.mem_cons_self)).1 (hl x (List.mem_cons_self)).2
    obtain ⟨b,hb,hB,j,hj⟩ := ih (fun y hy => hl y (List.mem_cons_of_mem x hy))
    obtain ⟨r,hr,hR,k,hk⟩ := add_residues m hd c hc0 hc1 hp hpG ha hb hA hB
    refine ⟨r,hr,?_,i+j+k,?_⟩
    · simpa only [List.length_cons, show 2+4*l.length+2 = 4*(l.length+1) by omega] using hR
    · simp only [List.sum_cons, hi, hj, add_zsmul]
      calc
        _ = (a+b)+(i•p+j•p) := by abel
        _ = _ := by rw [hk]; abel

include hm0 hd hc0 hc1 hp hpG in
lemma list_cap (l : List α) (hl : ∀ x∈l, |x| ≤ p ∧ Good m c 1 |x|)
    (hz : l.sum ∈ Set.Ico 0 p) : Good m c (4*l.length) l.sum := by
  obtain ⟨r,hr,hR,j,hj⟩ := list_residue m hm0 hd c hc0 hc1 hp hpG l hl
  have hzero : j = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hle : j ≤ -1 := by omega
      have hh : j•p ≤ (-1:ℤ)•p := by
        simp only [zsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) hp.le
      simp only [neg_smul, one_smul] at hh
      linarith [hz.1, hr.2]
    · have hge : 1 ≤ j := by omega
      have hh : (1:ℤ)•p ≤ j•p := by
        simp only [zsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hge) hp.le
      simp only [one_smul] at hh
      linarith [hz.2, hr.1]
  have he : l.sum = r := by simpa only [hzero, zero_smul, add_zero] using hj
  rw [he]
  exact hR
end EuclideanFiveColor.CappedResidues
end

noncomputable section
namespace EuclideanFiveColor.CappedResidues
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

private def signedList (a : ℤ) (x : α) : List α :=
  match a with
  | .ofNat n => List.replicate n x
  | .negSucc n => List.replicate (n+1) (-x)
omit [LinearOrder α] [IsStrictOrderedRing α] in
@[simp] lemma signedList_length (a : ℤ) (x : α) : (signedList a x).length = a.natAbs := by
  cases a <;> simp [signedList]
omit [LinearOrder α] [IsStrictOrderedRing α] in
@[simp] lemma signedList_sum (a : ℤ) (x : α) : (signedList a x).sum = a • x := by
  cases a <;> simp [signedList]
  ring
omit [IsStrictOrderedRing α] in
lemma signedList_mem (a : ℤ) (x v : α) (hv : v ∈ signedList a x) : |v| = |x| := by
  cases a <;> simp only [signedList,List.mem_replicate] at hv
  · rw [hv.2]
  · rw [hv.2,abs_neg]

omit [IsStrictOrderedRing α] in
lemma integer_list {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α) :
    ∃ l : List α, l.length = ∑ i ∈ s, (a i).natAbs ∧ l.sum = ∑ i ∈ s, a i • x i ∧
      ∀ v ∈ l, ∃ i ∈ s, |v| = |x i| := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[],by simp,by simp,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨l,hl,hs,hv⟩ := ih
    refine ⟨signedList (a i) (x i) ++ l,?_,?_,?_⟩
    · simp [hl,hi]
    · simp [hs,hi]
    · intro v hv'
      rcases List.mem_append.mp hv' with hv' | hv'
      · exact ⟨i,Finset.mem_insert_self _ _,signedList_mem _ _ _ hv'⟩
      · obtain ⟨j,hj,he⟩ := hv v hv'
        exact ⟨j,Finset.mem_insert_of_mem hj,he⟩

variable (m : α → ℝ) (hm0 : m 0 = 1)
  (hd : ∀ a b : α, 0 ≤ a → 0 ≤ b → m a*m b ≤ m |a-b|)
  (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
  {p : α} (hp : 0 < p) (hpG : Good m c 1 p)
include hm0 hd hc0 hc1 hp hpG in
lemma integer_cap {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α)
    (hx : ∀ i ∈ s, |x i| ≤ p ∧ Good m c 1 |x i|)
    (hz : (∑ i ∈ s, a i • x i) ∈ Set.Ico 0 p) :
    Good m c (4*∑ i ∈ s, (a i).natAbs) (∑ i ∈ s, a i • x i) := by
  obtain ⟨l,hl,hs,hv⟩ := integer_list s a x
  have he := list_cap m hm0 hd c hc0 hc1 hp hpG l (by
    intro v hvl
    obtain ⟨i,hi,he⟩ := hv v hvl
    rw [he]
    exact hx i hi) (hs.symm ▸ hz)
  rwa [hl,hs] at he
include hm0 hd hc0 hc1 hp hpG in
lemma integer_abs_cap {ι : Type*} (s : Finset ι) (a : ι → ℤ) (x : ι → α)
    (hx : ∀ i ∈ s, |x i| ≤ p ∧ Good m c 1 |x i|)
    (hz : |∑ i ∈ s, a i • x i| < p) :
    Good m c (4*∑ i ∈ s, (a i).natAbs) |∑ i ∈ s, a i • x i| := by
  by_cases hn : 0 ≤ ∑ i ∈ s, a i • x i
  · rw [abs_of_nonneg hn] at hz ⊢
    exact integer_cap m hm0 hd c hc0 hc1 hp hpG s a x hx ⟨hn,hz⟩
  · have hs : (∑ i ∈ s, a i • (-x i)) = -∑ i ∈ s, a i • x i := by simp
    have hz' : (∑ i ∈ s, a i • (-x i)) ∈ Set.Ico 0 p := by
      rw [hs]
      have he : |∑ i ∈ s, a i • x i| = -∑ i ∈ s, a i • x i := abs_of_neg (lt_of_not_ge hn)
      exact ⟨by linarith,he ▸ hz⟩
    have he := integer_cap m hm0 hd c hc0 hc1 hp hpG s a (fun i => -x i)
      (fun i hi => by simpa only [abs_neg] using hx i hi) hz'
    simpa only [hs,abs_of_neg (lt_of_not_ge hn)] using he
end EuclideanFiveColor.CappedResidues
end

end ParishSpectral
end

-- Erdos173.Template.Transcendental
section
noncomputable section

namespace Parish173

open ParishSpectral.PlaneFiveColor.Spectral Parish173.Template Module

lemma algebraic_template {x : ℝ} (hx : Transcendental ℚ x) (Q : Finset ℂ)
    (hQ : ∀ q ∈ Q, q ∈ fieldOf x ∧ ‖q‖ = 1) :
    ∃ P : Finset ℂ, (∀ p ∈ P, p ∈ fieldOf x ∧ ‖p‖ = 1) ∧ ∀ j : ℂ → ℂ, (∀ p ∈ P, j p ∈ Q) →
      (1 : ℂ) ∈ Submodule.span 𝔸 ((fun p => j p * p) '' (P : Set ℂ)) := by
  classical
  by_contra! h
  let K := {z : ℂ // z ∈ fieldOf x ∧ ‖z‖ = 1}
  obtain ⟨j₁, hj₁, -⟩ := h {1} (by simp [(fieldOf x).one_mem])
  let q₀ : Q := ⟨j₁ 1, hj₁ 1 (Finset.mem_singleton_self 1)⟩
  let _ : TopologicalSpace Q := ⊥
  have : DiscreteTopology Q := ⟨rfl⟩
  
  let C : Finset K → Set (K → Q) := fun P =>
    {f | (1 : ℂ) ∉ Submodule.span 𝔸 ((fun p : K => ((f p : ℂ)) * p) '' (P : Set K))}
  have hC : ∀ P, (C P).Nonempty := by
    intro P
    obtain ⟨j, hjQ, hj⟩ := h (P.image Subtype.val) (by
      intro p hp
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hp
      exact p.property)
    refine ⟨fun p => if hp : (p : ℂ) ∈ P.image Subtype.val then ⟨j p, hjQ p hp⟩ else q₀, ?_⟩
    have he : (fun p : K => (((fun p : K => if hp : (p : ℂ) ∈ P.image Subtype.val then
        (⟨j p, hjQ p hp⟩ : Q) else q₀) p : Q) : ℂ) * p) '' (P : Set K) =
        (fun p => j p * p) '' ((P.image Subtype.val : Finset ℂ) : Set ℂ) := by
      ext y
      simp only [Set.mem_image, Finset.mem_coe, Finset.coe_image]
      constructor
      · rintro ⟨p, hp, rfl⟩
        refine ⟨p, ⟨p, hp, rfl⟩, ?_⟩
        rw [dif_pos (Finset.mem_image_of_mem _ hp)]
      · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        refine ⟨p, hp, ?_⟩
        rw [dif_pos (Finset.mem_image_of_mem _ hp)]
    change (1 : ℂ) ∉ _
    rw [he]
    exact hj
  have hCc : ∀ P, IsClosed (C P) := by
    intro P
    let r : (K → Q) → (P → Q) := fun f p => f p
    have hr : Continuous r := continuous_pi fun p => continuous_apply _
    have he : C P = r ⁻¹' {g | (1 : ℂ) ∉ Submodule.span 𝔸
        (Set.range fun p : P => ((g p : ℂ)) * (p : ℂ))} := by
      ext f
      simp only [C, r, Set.mem_ofPred_eq, Set.mem_preimage]
      have : (fun p : K => ((f p : ℂ)) * p) '' (P : Set K) =
          Set.range (fun p : P => ((f p : ℂ)) * (p : ℂ)) := by
        ext y
        simp
      rw [this]
    rw [he]
    exact (isClosed_discrete _).preimage hr
  have hdir : Directed (· ⊇ ·) C := by
    intro P₁ P₂
    refine ⟨P₁ ∪ P₂, fun f hf h1 => hf (Submodule.span_mono (Set.image_mono ?_) h1),
      fun f hf h1 => hf (Submodule.span_mono (Set.image_mono ?_) h1)⟩
    · simp
    · simp
  obtain ⟨f, hf⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hC
    (fun P => (hCc P).isCompact) hCc
  rw [Set.mem_iInter] at hf
  
  let W := Submodule.span 𝔸 (Set.range fun p : K => ((f p : ℂ)) * p)
  have h1 : (1 : ℂ) ∉ W := by
    intro hW
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hW
    apply hf c.support
    rw [← hc]
    exact Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨p, hp, rfl⟩)
  obtain ⟨g, hg1, hgW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h1 inferInstance
  let ℓ : ℂ →ₗ[𝔸] 𝔸 := (g 1)⁻¹ • g
  have hℓ : ℓ 1 = 1 := by simp [ℓ, inv_mul_cancel₀ hg1]
  obtain ⟨u, hu, hu1, hℓu⟩ := cover_impossible_fieldOf hx hQ ℓ hℓ
  apply hℓu (f ⟨u, hu, hu1⟩) (f ⟨u, hu, hu1⟩).property
  have hgu : g ((f ⟨u, hu, hu1⟩ : ℂ) * u) = 0 := by
    have : g ((f ⟨u, hu, hu1⟩ : ℂ) * u) ∈ W.map g :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨u, hu, hu1⟩, rfl⟩)
    rwa [hgW, Submodule.mem_bot] at this
  simp [ℓ, hgu]

open ParishSpectral.EuclideanFiveColor.AlgebraicCayley ParishSpectral.EuclideanFiveColor.GeneralPosition in

theorem templateProperty_fieldOf {x : ℝ} (hx : Transcendental ℚ x) :
    TemplateProperty (fieldOf x : Set ℂ) := by
  classical
  intro Q hQ
  obtain ⟨P, hP, hPspan⟩ := algebraic_template hx Q hQ
  
  let ext : (P → Q) → ℂ → ℂ := fun L p => if h : p ∈ P then (L ⟨p, h⟩ : ℂ) else 0
  let img : (P → Q) → Finset ℂ := fun L => P.image fun p => ext L p * p
  have hcoef (L : P → Q) : ∃ c : ℂ → 𝔸, ∑ y ∈ img L, (c y : ℂ) * y = 1 := by
    have h := hPspan (ext L) fun p hp => by simp [ext, hp]
    rw [← Finset.coe_image] at h
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp h
    exact ⟨c, hc⟩
  choose c hc using hcoef
  
  let Cset : Finset ℂ := Finset.univ.biUnion fun L => (img L).image fun y => (c L y : ℂ)
  have hCalg : ∀ z ∈ Cset, IsAlgebraic ℚ z := by
    intro z hz
    obtain ⟨L, -, hL⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hL
    exact mem_algebraicClosure_iff.mp (c L y).property
  let Ng := generatedField Cset
  have : FiniteDimensional ℚ Ng := generatedField_finite Cset hCalg
  have hcN (L : P → Q) (y : ℂ) (hy : y ∈ img L) : (c L y : ℂ) ∈ Ng :=
    generatedField_contains Cset _
      (Finset.mem_biUnion.mpr ⟨L, Finset.mem_univ _, Finset.mem_image_of_mem _ hy⟩)
  have hIN : Complex.I ∈ Ng := generatedField_I Cset
  obtain ⟨S₀, hS₀c, hS₀n, hS₀g⟩ := numberField_general_position Ng hIN
    (generatedField_re_closed Cset) (generatedField_im_closed Cset)
    (Q.card * (finrank ℚ Ng - 1) + 1)
  have hNalg (s : Ng) : (s : ℂ) ∈ fieldOf x :=
    mem_fieldOf_of_𝔸 (mem_algebraicClosure_iff.mpr
      (IsAlgebraic.algHom Ng.val (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s)))
  
  refine ⟨(P ×ˢ S₀).image fun ps => ps.1 * (ps.2 : ℂ), ?_, fun j hj => ?_⟩
  · intro σ hσ
    obtain ⟨⟨p, s⟩, hps, rfl⟩ := Finset.mem_image.mp hσ
    obtain ⟨hp, hs⟩ := Finset.mem_product.mp hps
    exact ⟨(fieldOf x).mul_mem (hP p hp).1 (hNalg s),
      by rw [norm_mul, (hP p hp).2, hS₀n s hs, one_mul]⟩
  set W := Submodule.span ℚ ((fun s => j s * s) '' ↑((P ×ˢ S₀).image fun ps => ps.1 * (ps.2 : ℂ)))
  have hmemS (p : ℂ) (hp : p ∈ P) (s : Ng) (hs : s ∈ S₀) :
      p * (s : ℂ) ∈ (P ×ˢ S₀).image fun ps => ps.1 * (ps.2 : ℂ) :=
    Finset.mem_image.mpr ⟨(p, s), Finset.mem_product.mpr ⟨hp, hs⟩, rfl⟩
  
  have hsel (p : P) : ∃ q ∈ Q, ∃ T ⊆ S₀, T.card = finrank ℚ Ng ∧
      Submodule.span ℚ (T : Set Ng) = ⊤ ∧ ∀ s ∈ T, j (p * (s : ℂ)) = q :=
    spanning_selection Q S₀ hS₀g (by omega)
      (fun q s => j (p * (s : ℂ)) = q) fun s hs => ⟨_, hj _ (hmemS p p.2 s hs), rfl⟩
  choose q hq T hTS _hTc hTspan hTj using hsel
  have key (p : P) (a : Ng) : (a : ℂ) * (q p * p) ∈ W := by
    have ha : a ∈ Submodule.span ℚ (T p : Set Ng) := by rw [hTspan p]; trivial
    induction ha using Submodule.span_induction with
    | mem s hs =>
      have he : (s : ℂ) * (q p * p) = j (p * s) * (p * s) := by
        rw [hTj p s hs]
        ring
      rw [he]
      exact Submodule.subset_span ⟨_, Finset.mem_coe.mpr (hmemS p p.2 s (hTS p hs)), rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [show ((a + b : Ng) : ℂ) = a + b from rfl, add_mul]
      exact W.add_mem ha hb
    | smul r a _ ha =>
      rw [show ((r • a : Ng) : ℂ) = r • (a : ℂ) from rfl, smul_mul_assoc]
      exact W.smul_mem r ha
  let L : P → Q := fun p => ⟨q p, hq p⟩
  have hterm (z : ℂ) (hz : z ∈ Ng) (y : ℂ) (hy : y ∈ img L) : z * y ∈ W := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have he : ext L p = q ⟨p, hp⟩ := by simp [ext, hp, L]
    rw [he]
    exact key ⟨p, hp⟩ ⟨z, hz⟩
  have hsum (z : ℂ → ℂ) (hz : ∀ y ∈ img L, z y ∈ Ng) : ∑ y ∈ img L, z y * y ∈ W :=
    W.sum_mem fun y hy => hterm _ (hz y hy) y hy
  refine ⟨?_, ?_⟩
  · rw [← hc L]
    exact hsum _ fun y hy => hcN L y hy
  · have he : ∑ y ∈ img L, (Complex.I * (c L y : ℂ)) * y = Complex.I := by
      conv_rhs => rw [← mul_one Complex.I, ← hc L, Finset.mul_sum]
      simp only [mul_assoc]
    rw [← he]
    exact hsum _ fun y hy => Ng.mul_mem hIN (hcN L y hy)

end Parish173

end
end

-- OAI.Analysis.PlaneSpectrum.Carriers
section
noncomputable section

namespace ParishSpectral.PlaneFiveColor.Spectral

open scoped ComplexConjugate
open Module EuclideanFiveColor.AlgebraicCayley EuclideanFiveColor.GeneralPosition
  EuclideanFiveColor.Arithmetic

theorem mem_algebraicClosure_of_root {k : Type*} [Field k] [Algebra k ℂ] (p : Polynomial ℂ)
    (hp : p ≠ 0) (hc : ∀ n, p.coeff n ∈ algebraicClosure k ℂ) (z : ℂ) (hz : p.eval z = 0) :
    z ∈ algebraicClosure k ℂ := by
  let A := algebraicClosure k ℂ
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts p).mp
    ((Polynomial.lifts_iff_coeff_lifts (f := algebraMap A ℂ) p).mpr fun n => ⟨⟨_, hc n⟩, rfl⟩)
  have hza : IsAlgebraic A z := by
    refine ⟨q, fun h => hp (by rw [← hq, h, Polynomial.map_zero]), ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hq]
    exact hz
  exact mem_algebraicClosure_iff.mpr (hza.restrictScalars k)

theorem algebraic_complex_iff_coordinates (z : ℂ) :
    IsAlgebraic ℚ z ↔ IsAlgebraic ℚ z.re ∧ IsAlgebraic ℚ z.im := by
  have hi : IsAlgebraic ℚ Complex.I := IsAlgebraic.of_pow (n:=2) (by norm_num) (by rw [Complex.I_sq]; exact isAlgebraic_one.neg)
  have hhalf : IsAlgebraic ℚ ((2 : ℂ)⁻¹) := (isAlgebraic_natCast 2).inv
  constructor
  · intro hz
    have hc : IsAlgebraic ℚ (conj z) :=
      IsAlgebraic.algHom (Complex.conjAe.restrictScalars ℚ).toAlgHom hz
    constructor
    · apply (isAlgebraic_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
        Complex.ofReal_injective).mp
      have h := (hz.add hc).mul hhalf
      convert! h using 1 <;> first | rfl | (apply Complex.ext <;> simp; ring)
    · apply (isAlgebraic_algebraMap_iff (R := ℚ) (S := ℝ) (A := ℂ)
        Complex.ofReal_injective).mp
      have h := ((hz.sub hc).mul hhalf).mul hi.inv
      convert! h using 1 <;> first | rfl | (apply Complex.ext <;> simp; ring)
  · rintro ⟨hr, hi'⟩
    have hr' : IsAlgebraic ℚ (z.re : ℂ) := hr.algebraMap
    have hi'' : IsAlgebraic ℚ (z.im : ℂ) := hi'.algebraMap
    simpa only [Complex.re_add_im] using hr'.add (hi''.mul hi)

theorem templateProperty_algebraic : TemplateProperty (algebraicClosure ℚ ℂ : Set ℂ) := by
  classical
  intro Q hQ
  let N := generatedField Q
  have : FiniteDimensional ℚ N :=
    generatedField_finite Q (fun q hq => mem_algebraicClosure_iff.mp (hQ q hq).1)
  obtain ⟨S,hSc,hSn,hSg⟩ := numberField_general_position N (generatedField_I Q)
    (generatedField_re_closed Q) (generatedField_im_closed Q)
    (Q.card*(finrank ℚ N-1)+1)
  refine ⟨S.image (fun s : N => (s:ℂ)), ?_, ?_⟩
  · intro s hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨mem_algebraicClosure_iff.mpr (IsAlgebraic.algHom N.val (IsAlgebraic.of_finite ℚ t)),
      hSn t ht⟩
  · intro j hj
    obtain ⟨q,hq,T,hTS,_,hTspan,hTA⟩ := spanning_selection Q S hSg (by omega)
      (fun q (s : N) => j s = q) (fun s hs => ⟨j s,hj _ (Finset.mem_image_of_mem _ hs),rfl⟩)
    let qN : N := ⟨q,generatedField_contains Q q hq⟩
    have hq0 : qN ≠ 0 := by
      intro he
      have hec := congrArg (fun z : N => (z:ℂ)) he
      have hn := (hQ q hq).2
      change q = 0 at hec
      simp [hec] at hn
    have hmem (x : N) : (x:ℂ) ∈
        Submodule.span ℚ
          ((fun s => j s*s) '' ((S.image (fun s : N => (s:ℂ)) : Finset ℂ) : Set ℂ)) := by
      obtain ⟨c,hc⟩ := span_mult_rep N T hTspan qN hq0 x
      rw [← hc, IntermediateField.coe_sum]
      refine Submodule.sum_mem _ fun t _ => ?_
      rw [IntermediateField.coe_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(t.val:ℂ),?_,?_⟩)
      · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (hTS t.property))
      · change j (t.val:ℂ)*(t.val:ℂ) = q*(t.val:ℂ)
        rw [hTA t t.property]
    exact ⟨by simpa using hmem 1, by simpa using hmem (iN N (generatedField_I Q))⟩

private abbrev algebraicCarrier : Carrier where
  E := algebraicClosure ℚ ℂ
  F := algebraicClosure ℚ ℝ
  countable := by
    apply Set.Countable.to_subtype
    have heq : (algebraicClosure ℚ ℂ : Set ℂ) = {x | IsAlgebraic ℚ x} := by
      ext z; exact mem_algebraicClosure_iff
    rw [heq]
    exact Algebraic.countable ℚ ℂ
  mem_iff z := by
    simp only [mem_algebraicClosure_iff]
    exact algebraic_complex_iff_coordinates z
  algClosed := mem_algebraicClosure_of_root
  template := templateProperty_algebraic

theorem ofReal_mem_algebraicCarrier {x : ℝ} (hx : IsAlgebraic ℚ x) :
    (x : ℂ) ∈ algebraicCarrier.E :=
  mem_algebraicClosure_iff.mpr hx.algebraMap

section fieldOf

variable (x : ℝ)

theorem adjoin_map_ofReal :
    (IntermediateField.adjoin ℚ {x}).map (Complex.ofRealAm.restrictScalars ℚ) =
      IntermediateField.adjoin ℚ {(x : ℂ)} := by
  rw [IntermediateField.adjoin_map, Set.image_singleton]
  rfl

private def adjoinEquiv :
    IntermediateField.adjoin ℚ {x} ≃ₐ[ℚ] IntermediateField.adjoin ℚ {(x : ℂ)} :=
  (IntermediateField.equivMap _ (Complex.ofRealAm.restrictScalars ℚ)).trans
    (IntermediateField.equivOfEq (adjoin_map_ofReal x))

theorem ofReal_mem_fieldOf_iff (t : ℝ) : (t : ℂ) ∈ fieldOf x ↔ t ∈ realFieldOf x := by
  simp only [fieldOf, realFieldOf, IntermediateField.mem_restrictScalars,
    mem_algebraicClosure_iff]
  exact isAlgebraic_ringHom_iff_of_comp_eq (adjoinEquiv x) Complex.ofRealHom
    Complex.ofReal_injective (RingHom.ext fun _ => rfl)

theorem I_mem_fieldOf : Complex.I ∈ fieldOf x := by
  simp only [fieldOf, IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]
  exact (IsAlgebraic.of_pow (R := ℚ) (r := Complex.I) (n:=2) (by norm_num) (by rw [Complex.I_sq]; exact isAlgebraic_one.neg)).extendScalars
    (algebraMap ℚ (IntermediateField.adjoin ℚ {(x : ℂ)})).injective

theorem conj_mem_fieldOf {z : ℂ} (hz : z ∈ fieldOf x) : conj z ∈ fieldOf x := by
  let k := IntermediateField.adjoin ℚ {(x : ℂ)}
  let c : ℂ →ₐ[k] ℂ :=
    { (Complex.conjAe : ℂ →ₐ[ℝ] ℂ).toRingHom with
      commutes' := fun a => by
        obtain ⟨b, hb⟩ := (adjoinEquiv x).surjective a
        rw [← hb]
        exact Complex.conj_ofReal _ }
  simp only [fieldOf, IntermediateField.mem_restrictScalars] at hz ⊢
  exact (map_mem_algebraicClosure_iff c).mpr hz

private abbrev carrierOf (h : TemplateProperty (fieldOf x : Set ℂ)) : Carrier where
  E := fieldOf x
  F := realFieldOf x
  countable := by
    let k := IntermediateField.adjoin ℚ {(x : ℂ)}
    have : Countable k := by
      rw [← Cardinal.mk_le_aleph0_iff]
      refine (IntermediateField.cardinalMk_adjoin_le ℚ _).trans ?_
      simp
    apply Set.Countable.to_subtype
    have heq : (fieldOf x : Set ℂ) = {z | IsAlgebraic k z} := by
      ext z
      exact mem_algebraicClosure_iff
    rw [heq]
    exact Algebraic.countable k ℂ
  mem_iff z := by
    rw [← ofReal_mem_fieldOf_iff, ← ofReal_mem_fieldOf_iff]
    constructor
    · intro hz
      have hc := conj_mem_fieldOf x hz
      constructor
      · rw [Complex.re_eq_add_conj]
        exact div_mem (add_mem hz hc) (by simp)
      · rw [Complex.im_eq_sub_conj]
        exact div_mem (sub_mem hz hc)
          (mul_mem (by simp) (I_mem_fieldOf x))
    · rintro ⟨hr, hi⟩
      rw [← Complex.re_add_im z]
      exact add_mem hr (mul_mem hi (I_mem_fieldOf x))
  algClosed p hp hc z hz := by
    simp only [fieldOf, IntermediateField.mem_restrictScalars] at hc ⊢
    exact mem_algebraicClosure_of_root p hp hc z hz
  template := h

theorem ofReal_mem_carrierOf (h : TemplateProperty (fieldOf x : Set ℂ)) :
    (x : ℂ) ∈ (carrierOf x h).E := by
  change (x : ℂ) ∈ fieldOf x
  simp only [fieldOf, IntermediateField.mem_restrictScalars, mem_algebraicClosure_iff]
  exact isAlgebraic_algebraMap (⟨(x : ℂ), IntermediateField.mem_adjoin_simple_self ℚ _⟩ :
    IntermediateField.adjoin ℚ {(x : ℂ)})

end fieldOf

end ParishSpectral.PlaneFiveColor.Spectral
end
end

namespace OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1
open MeasureTheory Real
open ParishSpectral.PlaneFiveColor.Spectral

/-- The spectral law for a coloring on a fixed countable carrier with the finite
direction selection property. Only values of the coloring on the carrier triangles are used. -/
def H1 : Prop :=
  let ζ : ℂ := ⟨1 / 2, √3 / 2⟩
  ∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), Countable E →
    (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F) →
    (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E) →
    (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ))) →
    ∀ x : ℝ, 0 < x → (x : ℂ) ∈ E → ∀ c : ℂ → Fin 2,
    (∀ r : ℝ, r=1 ∨ r=x → ∀ p ∈ E, ∀ u ∈ E, ‖u‖=1 →
      ¬ (c (p+u*r)=c p ∧ c (p+u*(r*ζ))=c p)) →
    ∃ ν : Measure ℂ, IsFiniteMeasure ν ∧ ν.real Set.univ ≤ 1 ∧
    ∀ r : ℝ, r=1 ∨ r=x → ∀ u : Circle,
      (∫ ξ, (Circle.exp (inner ℝ ξ ((u : ℂ)*(r:ℂ))) : ℂ) ∂ν) = -1/3

/-- Averaging a constant planar Fourier transform on a circle gives its
real Bessel transform at that radius. -/
def H2 : Prop := ∀ (ν : Measure ℂ) [IsFiniteMeasure ν] (r : ℝ), 0 < r →
  (∀ u : Circle, (∫ ξ, (Circle.exp (inner ℝ ξ ((u : ℂ)*(r:ℂ))) : ℂ) ∂ν) = -1/3) →
  (∫ ξ : ℂ, (2 * π)⁻¹ * (∫ θ in (0:ℝ)..2*π, cos ((r * ‖ξ‖) * cos θ)) ∂ν) = -1/3

theorem main : H1 → H2 → OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1.H2 := by
  intro law average x hx c h₁ h₂
  have ex : ∃ (C : Carrier), (x:ℂ) ∈ C.E := by
    by_cases ha : IsAlgebraic ℚ x
    · exact ⟨algebraicCarrier, ofReal_mem_algebraicCarrier ha⟩
    · have h := Parish173.templateProperty_fieldOf (x:=x) ha
      exact ⟨carrierOf x h,ofReal_mem_carrierOf x h⟩
  obtain ⟨C,hxE⟩ := ex
  obtain ⟨ν,hfin,hmass,hcorr⟩ := law C.E C.F C.countable C.mem_iff C.algClosed C.template x hx hxE c (by
    intro r hr p hp u hu hunit
    rcases hr with rfl | rfl
    · exact h₁ p u hunit
    · exact h₂ p u hunit)
  letI : IsFiniteMeasure ν := hfin
  refine ⟨ν,hfin,hmass,?_,?_⟩
  · simpa only [one_mul] using average ν 1 (by norm_num) (hcorr 1 (Or.inl rfl))
  · exact average ν x hx (hcorr x (Or.inr rfl))
end OMA.R_Erdos173_erdos_173_R1_H2_R1_H1_R1_H2_R1
