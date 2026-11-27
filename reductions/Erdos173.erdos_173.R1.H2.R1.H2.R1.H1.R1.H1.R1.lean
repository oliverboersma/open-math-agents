import OMAReductions.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1
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


/-! Construction of the bounded projected sign field. The argument adapts the
continuous-vector, Koopman, and triangle-sampling proofs of Jacob Parish
(plasma-ai/erdos-173@4a368a652753) and OpenAI
(openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a), both Apache-2.0.
The two outstanding statements concern the Fourier coefficients of a wild law
and the ordinary spectral mass of vectors orthogonal to continuous vectors. -/
-- OAI.Analysis.PlaneSpectrum.Carrier
section
noncomputable section

namespace ParishLaw.PlaneFiveColor.Spectral

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
end ParishLaw.PlaneFiveColor.Spectral
end
end

-- OAI.Analysis.PlaneSpectrum.Basic
section
namespace ParishLaw

noncomputable section
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral

variable [Carrier]

private abbrev E : IntermediateField ℚ ℂ := Carrier.E

private def K : Subgroup Circle where
  carrier := {u | (u : ℂ) ∈ E}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simpa using E.mul_mem ha hb
  inv_mem' := by intro a ha; simpa using E.inv_mem ha

theorem K_pow_surjective (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective (fun u : K => u ^ n) := by
  intro u
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u.val : ℂ) (Nat.pos_of_ne_zero hn)
  have ha : z ∈ E := Carrier.mem_of_pow_mem hn (by
    rw [hz]; exact u.property)
  have hnrm : ‖z‖ = 1 := by
    have hpow : ‖z‖ ^ n = (1 : ℝ) ^ n := by
      simp only [← norm_pow, hz, Circle.norm_coe, one_pow]
    exact (pow_left_inj₀ (norm_nonneg z) zero_le_one hn).mp hpow
  refine ⟨⟨⟨z, mem_sphere_zero_iff_norm.mpr hnrm⟩, ha⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hz

private instance K_rootable : RootableBy K ℕ := rootableByOfPowLeftSurj K ℕ (fun {n} hn => K_pow_surjective n hn)

omit [Carrier] in

theorem finite_image_trivial {G H : Type*} [Group G] [Group H] [Finite H]
    [RootableBy G ℕ] (f : G →* H) (g : G) : f g = 1 := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨x, hx⟩ := RootableBy.surjective_pow G ℕ (Fintype.card_ne_zero : Fintype.card H ≠ 0) g
  rw [← hx, map_pow, pow_card_eq_one]

private def DiscreteE := Multiplicative E deriving CommGroup
private instance : TopologicalSpace DiscreteE := ⊥
private instance : DiscreteTopology DiscreteE := ⟨rfl⟩
private instance : IsTopologicalGroup DiscreteE := inferInstance
private abbrev D := PontryaginDual DiscreteE


private instance E_countable : Countable E := Carrier.countable

private instance : Countable DiscreteE := inferInstanceAs (Countable E)

private instance : SecondCountableTopology D :=
  ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.secondCountableTopology

private def embed (z : DiscreteE) : ℂ := ((Multiplicative.toAdd z : E) : ℂ)

@[simp] theorem embed_one : embed 1 = 0 := rfl
@[simp] theorem embed_mul (z w : DiscreteE) : embed (z * w) = embed z + embed w := rfl

private def j (ξ : ℂ) : D where
  toFun z := Circle.exp (inner ℝ ξ (embed z))
  map_one' := by simp
  map_mul' z w := by simp only [embed_mul, inner_add_right, Circle.exp_add]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem j_apply (ξ : ℂ) (z : DiscreteE) :
    j ξ z = Circle.exp (inner ℝ ξ (embed z)) := rfl

@[simp] theorem j_zero : j 0 = 1 := by
  apply PontryaginDual.ext
  intro z
  simp

@[simp] theorem j_add (ξ η : ℂ) : j (ξ + η) = j ξ * j η := by
  apply PontryaginDual.ext
  intro z
  change Circle.exp (inner ℝ (ξ + η) (embed z)) =
    Circle.exp (inner ℝ ξ (embed z)) * Circle.exp (inner ℝ η (embed z))
  rw [inner_add_left, Circle.exp_add]

private def jHom : Multiplicative ℂ →* D where
  toFun ξ := j (Multiplicative.toAdd ξ)
  map_one' := j_zero
  map_mul' ξ η := j_add (Multiplicative.toAdd ξ) (Multiplicative.toAdd η)

private def C : Subgroup D := jHom.range

theorem continuous_j : Continuous j := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi
  intro z
  exact Circle.exp.continuous.comp (continuous_id.inner continuous_const)

private instance : MeasurableSpace D := borel D
private instance : BorelSpace D := ⟨rfl⟩

theorem measurableSet_C : MeasurableSet (C : Set D) := by
  change MeasurableSet (Set.range j)
  rw [← Set.image_univ, ← Metric.iUnion_closedBall_nat (0 : ℂ), Set.image_iUnion]
  exact MeasurableSet.iUnion fun n =>
    ((isCompact_closedBall (0 : ℂ) (n : ℝ)).image continuous_j).measurableSet

private def scaleE (a : E) : DiscreteE →ₜ* DiscreteE where
  toFun z := Multiplicative.ofAdd (a * Multiplicative.toAdd z)
  map_one' := by change Multiplicative.ofAdd (a * 0) = 1; simp
  map_mul' z w := by
    change Multiplicative.ofAdd (a * (_ + _)) = _
    rw [mul_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

private def scalar (a : E) (d : D) : D := d.comp (scaleE a)

@[simp] theorem scalar_apply (a : E) (d : D) (z : DiscreteE) :
    scalar a d z = d (Multiplicative.ofAdd (a * Multiplicative.toAdd z)) := rfl

@[simp] theorem scalar_one (d : D) : scalar 1 d = d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd (1 * Multiplicative.toAdd z)) = d z
  rw [one_mul]
  rfl

@[simp] theorem scalar_mul (a b : E) (d : D) :
    scalar a (scalar b d) = scalar (a * b) d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd (b * (a * Multiplicative.toAdd z))) =
    d (Multiplicative.ofAdd ((a * b) * Multiplicative.toAdd z))
  rw [mul_left_comm, ← mul_assoc]

@[simp] theorem scalar_add (a b : E) (d : D) :
    scalar (a + b) d = scalar a d * scalar b d := by
  apply PontryaginDual.ext
  intro z
  change d (Multiplicative.ofAdd ((a + b) * Multiplicative.toAdd z)) = _
  rw [add_mul]
  exact map_mul d _ _

@[simp] theorem scalar_j (a : E) (ξ : ℂ) :
    scalar a (j ξ) = j (conj (a : ℂ) * ξ) := by
  apply PontryaginDual.ext
  intro z
  change Circle.exp (inner ℝ ξ ((a : ℂ) * embed z)) = _
  rw [j_apply]
  congr 1
  simp only [Complex.inner, map_mul, starRingEnd_self_apply]
  congr 1
  ring

theorem scalar_mem_C (a : E) {d : D} (hd : d ∈ C) : scalar a d ∈ C := by
  obtain ⟨ξ, rfl⟩ := hd
  exact ⟨Multiplicative.ofAdd (conj (a : ℂ) * Multiplicative.toAdd ξ), scalar_j a _ |>.symm⟩

theorem scalar_mem_C_iff {a : E} (ha : a ≠ 0) (d : D) : scalar a d ∈ C ↔ d ∈ C := by
  constructor
  · intro h
    have h' := scalar_mem_C a⁻¹ h
    simpa [ha] using h'
  · exact scalar_mem_C a
private def kCoeff (u : K) : E := ⟨(u.val : ℂ), u.property⟩

@[simp] theorem kCoeff_one : kCoeff 1 = 1 := rfl
@[simp] theorem kCoeff_mul (u v : K) : kCoeff (u * v) = kCoeff u * kCoeff v := rfl

private def scalarHom (a : E) : D →* D where
  toFun := scalar a
  map_one' := by apply PontryaginDual.ext; intro z; rfl
  map_mul' d e := by apply PontryaginDual.ext; intro z; rfl

private instance : MulAction K D where
  smul u d := scalar (kCoeff u) d
  one_smul d := scalar_one d
  mul_smul u v d := (scalar_mul (kCoeff u) (kCoeff v) d).symm

private def IsWild (ν : MeasureTheory.Measure D) : Prop :=
  (∀ u : K, MeasureTheory.MeasurePreserving (fun d : D => u • d) ν ν) ∧
    ν (C : Set D) = 0

theorem continuous_scalar (a : E) : Continuous (scalar a) :=
  (scaleE a).continuous_comp_left

omit [Carrier] in

theorem frequency_zero_of_rational_tests (a : ℝ)
    (h : ∀ q : ℚ, Circle.exp (a * (q : ℝ)) = 1) : a = 0 := by
  have heq : (fun t : ℝ => Circle.exp (a * t)) = fun _ => 1 :=
    Rat.denseRange_cast.equalizer
      (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
      continuous_const (funext h)
  have hpi : Circle.exp Real.pi ≠ 1 := by
    intro hone
    have ha := congrArg (fun u : Circle => (u : ℂ).arg) hone
    rw [Circle.arg_exp (by linarith [Real.pi_pos]) le_rfl] at ha
    simp at ha
  by_contra ha
  have ht := congrFun heq (Real.pi / a)
  have hmul : a * (Real.pi / a) = Real.pi := by field_simp
  rw [hmul] at ht
  exact hpi ht

private def imagUnit : E := ⟨Complex.I, Carrier.I_mem⟩

@[simp] theorem coe_imagUnit : (imagUnit : ℂ) = Complex.I := rfl

theorem j_eq_one_iff (ξ : ℂ) : j ξ = 1 ↔ ξ = 0 := by
  constructor
  · intro h
    have hre : ξ.re = 0 := frequency_zero_of_rational_tests ξ.re (by
      intro q
      have ht := congrArg (fun d : D => d (Multiplicative.ofAdd (q : E))) h
      change Circle.exp (inner ℝ ξ ((q : E) : ℂ)) = 1 at ht
      simpa [Complex.inner, Complex.mul_re, mul_comm] using ht)
    have him : ξ.im = 0 := frequency_zero_of_rational_tests ξ.im (by
      intro q
      have ht := congrArg (fun d : D => d (Multiplicative.ofAdd ((q : E) * imagUnit))) h
      change Circle.exp (inner ℝ ξ (((q : E) * imagUnit : E) : ℂ)) = 1 at ht
      simpa [Complex.inner, Complex.mul_re, mul_comm] using ht)
    exact Complex.ext hre him
  · rintro rfl
    exact j_zero

@[simp] theorem j_neg (ξ : ℂ) : j (-ξ) = (j ξ)⁻¹ :=
  map_inv jHom (Multiplicative.ofAdd ξ)

@[simp] theorem j_sub (ξ η : ℂ) : j (ξ - η) = j ξ / j η := by
  rw [sub_eq_add_neg, j_add, j_neg, div_eq_mul_inv]

theorem j_injective : Function.Injective j := by
  intro ξ η h
  apply sub_eq_zero.mp
  apply (j_eq_one_iff _).mp
  rw [j_sub, h, div_self']

theorem j_measurableEmbedding : MeasurableEmbedding j :=
  continuous_j.measurableEmbedding j_injective

@[simp] theorem kCoeff_inv (u : K) : kCoeff u⁻¹ = (kCoeff u)⁻¹ := by
  apply Subtype.ext
  change ((u.val)⁻¹ : Circle).val = (u.val : ℂ)⁻¹
  exact Circle.coe_inv u.val

@[simp] theorem kCoeff_ne_zero (u : K) : kCoeff u ≠ 0 := by
  intro h
  have hz : (u.val : ℂ) = 0 := congrArg (fun x : E => (x : ℂ)) h
  exact u.val.coe_ne_zero hz
end PlaneFiveColor.Spectral
end
end ParishLaw
end

-- OAI.Analysis.PlaneSpectrum.InvariantMean
section
namespace ParishLaw

noncomputable section
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators

noncomputable section
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
namespace PlaneFiveColor.InvariantMean

local instance (α : Type*) : DecidableEq α := Classical.decEq α

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

private def shift (g : G) (f : G →ᵇ ℝ) : G →ᵇ ℝ :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma shift_apply (g x : G) (f : G →ᵇ ℝ) : shift g f x = f (x+g) := rfl

lemma shift_comm (g h : G) (f : G →ᵇ ℝ) : shift g (shift h f) = shift h (shift g f) := by
  ext x
  simp only [shift_apply, add_assoc, add_comm g h]

@[simp] lemma shift_add (g : G) (f h : G →ᵇ ℝ) : shift g (f+h) = shift g f + shift g h := by
  ext x
  rfl

@[simp] lemma shift_sub (g : G) (f h : G →ᵇ ℝ) : shift g (f-h) = shift g f - shift g h := by
  ext x
  rfl

@[simp] lemma shift_smul (g : G) (c : ℝ) (f : G →ᵇ ℝ) : shift g (c • f) = c • shift g f := by
  ext x
  rfl

lemma shift_norm_le (g : G) (f : G →ᵇ ℝ) : ‖shift g f‖ ≤ ‖f‖ := by
  exact BoundedContinuousFunction.norm_compContinuous_le _ _

private def single (g : G) (n : ℕ) (f : G →ᵇ ℝ) : G →ᵇ ℝ :=
  ((n+1 : ℕ) : ℝ)⁻¹ • ∑ k ∈ Finset.range (n+1), shift (k • g) f

@[simp] lemma single_apply (g x : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n f x = ((n+1 : ℕ) : ℝ)⁻¹ * ∑ k ∈ Finset.range (n+1), f (x+k • g) := by
  simp [single]

lemma single_norm_le (g : G) (n : ℕ) (f : G →ᵇ ℝ) : ‖single g n f‖ ≤ ‖f‖ := by
  have hn : (0 : ℝ) < (n+1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos _)
  calc
    ‖single g n f‖ = ((n+1 : ℕ) : ℝ)⁻¹ * ‖∑ k ∈ Finset.range (n+1), shift (k • g) f‖ := by
      rw [single, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (∑ _k ∈ Finset.range (n+1), ‖f‖) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => shift_norm_le _ _)
    _ = ‖f‖ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

@[simp] lemma single_add (g : G) (n : ℕ) (f h : G →ᵇ ℝ) :
    single g n (f+h) = single g n f + single g n h := by
  simp only [single, shift_add, Finset.sum_add_distrib, smul_add]

@[simp] lemma single_sub (g : G) (n : ℕ) (f h : G →ᵇ ℝ) :
    single g n (f-h) = single g n f - single g n h := by
  simp only [single, shift_sub, Finset.sum_sub_distrib, smul_sub]

@[simp] lemma single_smul (g : G) (n : ℕ) (c : ℝ) (f : G →ᵇ ℝ) :
    single g n (c • f) = c • single g n f := by
  simp only [single, shift_smul, ← Finset.smul_sum]
  exact smul_comm _ _ _

lemma single_shift (g h : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n (shift h f) = shift h (single g n f) := by
  ext x
  simp only [single_apply, shift_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  abel

lemma single_const (g : G) (n : ℕ) (c : ℝ) :
    single g n (BoundedContinuousFunction.const G c) = BoundedContinuousFunction.const G c := by
  ext x
  simp only [single_apply, BoundedContinuousFunction.const_apply, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_mul]

lemma single_nonneg (g : G) (n : ℕ) (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ single g n f x := by
  intro x
  rw [single_apply]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun k hk => hf _

lemma single_telescope (g x : G) (n : ℕ) (f : G →ᵇ ℝ) :
    single g n (shift g f - f) x =
      ((n+1 : ℕ) : ℝ)⁻¹ * (f (x+(n+1) • g) - f x) := by
  rw [single_apply]
  congr 1
  have he (k : ℕ) : (shift g f - f) (x+k • g) =
      f (x+(k+1) • g) - f (x+k • g) := by
    simp only [BoundedContinuousFunction.sub_apply, shift_apply, add_nsmul, one_nsmul, add_assoc]
  simp_rw [he]
  simpa only [zero_nsmul, add_zero] using Finset.sum_range_sub (fun k => f (x+k • g)) (n+1)

lemma single_coboundary_norm (g : G) (n : ℕ) (f : G →ᵇ ℝ) :
    ‖single g n (shift g f - f)‖ ≤ 2 * ‖f‖ / (n+1 : ℕ) := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  rw [single_telescope, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ)⁻¹)]
  have hb : |f (x+(n+1) • g) - f x| ≤ 2 * ‖f‖ := by
    calc
      _ ≤ |f (x+(n+1) • g)| + |f x| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
      _ = _ := by ring
  calc
    _ ≤ ((n+1 : ℕ) : ℝ)⁻¹ * (2 * ‖f‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

private def cube : List G → ℕ → (G →ᵇ ℝ) → (G →ᵇ ℝ)
  | [], _, f => f
  | g::L, n, f => single g n (cube L n f)

lemma cube_norm_le (L : List G) (n : ℕ) (f : G →ᵇ ℝ) : ‖cube L n f‖ ≤ ‖f‖ := by
  induction L with
  | nil => exact le_rfl
  | cons g L ih => exact (single_norm_le g n _).trans ih

lemma cube_shift (L : List G) (g : G) (n : ℕ) (f : G →ᵇ ℝ) :
    cube L n (shift g f) = shift g (cube L n f) := by
  induction L with
  | nil => rfl
  | cons h L ih => simp only [cube, ih, single_shift]

@[simp] lemma cube_add (L : List G) (n : ℕ) (f h : G →ᵇ ℝ) :
    cube L n (f+h) = cube L n f + cube L n h := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_add]

@[simp] lemma cube_sub (L : List G) (n : ℕ) (f h : G →ᵇ ℝ) :
    cube L n (f-h) = cube L n f - cube L n h := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_sub]

@[simp] lemma cube_smul (L : List G) (n : ℕ) (c : ℝ) (f : G →ᵇ ℝ) :
    cube L n (c • f) = c • cube L n f := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_smul]

lemma cube_const (L : List G) (n : ℕ) (c : ℝ) :
    cube L n (BoundedContinuousFunction.const G c) = BoundedContinuousFunction.const G c := by
  induction L with
  | nil => rfl
  | cons g L ih => simp only [cube, ih, single_const]

lemma cube_nonneg (L : List G) (n : ℕ) (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ cube L n f x := by
  induction L with
  | nil => exact hf
  | cons g L ih => exact single_nonneg g n _ ih

lemma cube_coboundary_norm (L : List G) (g : G) (hg : g ∈ L) (n : ℕ) (f : G →ᵇ ℝ) :
    ‖cube L n (shift g f-f)‖ ≤ 2 * ‖f‖ / (n+1 : ℕ) := by
  induction L with
  | nil => simp at hg
  | cons h L ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · rw [cube, cube_sub, cube_shift]
      apply (single_coboundary_norm g n _).trans
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cube_norm_le L n f) (by norm_num)) (by positivity)
    · exact (single_norm_le h n _).trans (ih hg)

private def approx (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ℝ :=
  cube i.1.toList i.2 f 0

lemma approx_norm_le (i : Finset G × ℕ) (f : G →ᵇ ℝ) : ‖approx i f‖ ≤ ‖f‖ :=
  ((cube i.1.toList i.2 f).norm_coe_le_norm 0).trans (cube_norm_le _ _ _)

private def averagingUF (G : Type*) [AddCommGroup G] : Ultrafilter (Finset G × ℕ) :=
  Ultrafilter.of atTop

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma averagingUF_le : (averagingUF G : Filter (Finset G × ℕ)) ≤ atTop :=
  Ultrafilter.of_le _

lemma approx_has_limit (f : G →ᵇ ℝ) :
    ∃ r : ℝ, Tendsto (fun i => approx i f) (averagingUF G : Filter _) (𝓝 r) := by
  have hb : (Ultrafilter.map (fun i => approx i f) (averagingUF G) : Filter ℝ) ≤
      𝓟 (Set.Icc (-‖f‖) ‖f‖) := by
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    apply Filter.Eventually.of_forall
    intro i
    exact abs_le.mp (approx_norm_le i f)
  obtain ⟨r, _, hr⟩ := isCompact_Icc.ultrafilter_le_nhds
    (Ultrafilter.map (fun i => approx i f) (averagingUF G)) hb
  exact ⟨r, hr⟩

private def mean (f : G →ᵇ ℝ) : ℝ :=
  (averagingUF G : Filter _).limUnder (fun i => approx i f)

lemma tendsto_approx (f : G →ᵇ ℝ) :
    Tendsto (fun i => approx i f) (averagingUF G : Filter _) (𝓝 (mean f)) :=
  tendsto_nhds_limUnder (approx_has_limit f)

lemma mean_add (f h : G →ᵇ ℝ) : mean (f+h) = mean f + mean h := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx f).add (tendsto_approx h) using 1
  simp only [approx, cube_add, BoundedContinuousFunction.add_apply]

lemma mean_smul (c : ℝ) (f : G →ᵇ ℝ) : mean (c • f) = c * mean f := by
  apply Tendsto.limUnder_eq
  convert (tendsto_approx f).const_mul c using 1
  simp only [approx, cube_smul, BoundedContinuousFunction.smul_apply, smul_eq_mul]

lemma mean_const (c : ℝ) : mean (BoundedContinuousFunction.const G c) = c := by
  apply Tendsto.limUnder_eq
  convert (tendsto_const_nhds : Tendsto (fun _ : Finset G × ℕ => c)
    (averagingUF G : Filter _) (𝓝 c)) using 1
  simp only [approx, cube_const, BoundedContinuousFunction.const_apply]

lemma mean_nonneg (f : G →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  exact ge_of_tendsto (tendsto_approx f) (Filter.Eventually.of_forall fun i =>
    cube_nonneg i.1.toList i.2 f hf 0)

lemma mean_norm_le (f : G →ᵇ ℝ) : ‖mean f‖ ≤ ‖f‖ := by
  exact le_of_tendsto (tendsto_approx f).norm
    (Filter.Eventually.of_forall fun i => approx_norm_le i f)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma eventually_mem (g : G) : ∀ᶠ i : Finset G × ℕ in (averagingUF G : Filter _), g ∈ i.1 := by
  classical
  apply Filter.Eventually.filter_mono averagingUF_le
  apply Filter.eventually_atTop.mpr
  refine ⟨({g}, 0), fun i hi => ?_⟩
  exact hi.1 (Finset.mem_singleton_self g)

omit [TopologicalSpace G] [DiscreteTopology G] in
lemma tendsto_index : Tendsto (fun i : Finset G × ℕ => i.2)
    (averagingUF G : Filter _) atTop := by
  apply Tendsto.mono_left _ averagingUF_le
  apply tendsto_atTop.mpr
  intro n
  apply Filter.eventually_atTop.mpr
  exact ⟨(∅, n), fun i hi => hi.2⟩

omit [DiscreteTopology G] in
lemma tendsto_boundary (f : G →ᵇ ℝ) :
    Tendsto (fun i : Finset G × ℕ => 2 * ‖f‖ / (i.2+1 : ℕ))
      (averagingUF G : Filter _) (𝓝 0) := by
  have hn : Tendsto (fun i : Finset G × ℕ => ((i.2+1 : ℕ) : ℝ))
      (averagingUF G : Filter _) atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp tendsto_index)
  simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
    (tendsto_inv_atTop_zero.comp hn).const_mul (2 * ‖f‖)

lemma mean_shift (g : G) (f : G →ᵇ ℝ) : mean (shift g f) = mean f := by
  have hz : Tendsto (fun i : Finset G × ℕ => approx i (shift g f) - approx i f)
      (averagingUF G : Filter _) (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_boundary f)
    filter_upwards [eventually_mem g] with i hi
    have h := ((cube i.1.toList i.2 (shift g f-f)).norm_coe_le_norm 0).trans
      (cube_coboundary_norm i.1.toList g (Finset.mem_toList.mpr hi) i.2 f)
    simpa only [cube_sub, BoundedContinuousFunction.sub_apply, approx] using h
  exact sub_eq_zero.mp (tendsto_nhds_unique ((tendsto_approx _).sub (tendsto_approx _)) hz)
end PlaneFiveColor.InvariantMean
end
end
end
end ParishLaw
end

-- OAI.MeasureTheory.CompactFactors.Stationary
section
namespace ParishLaw

noncomputable section

section
open MeasureTheory
open scoped BoundedContinuousFunction
open PlaneFiveColor.InvariantMean
namespace EuclideanFiveColor.StationaryMean
variable {A B X : Type*} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
  [TopologicalSpace X] [CompactSpace X]
  (t : A → X → X) (r : B → X → X) (x₀ : X)
private def inner (f : C(X,ℝ)) (b : B) : A →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun a => f (r b (t a x₀)))
    continuous_of_discreteTopology ‖f‖ (fun _ => f.norm_coe_le_norm _)
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_norm (f : C(X,ℝ)) (b : B) : ‖inner t r x₀ f b‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr fun _ => f.norm_coe_le_norm _
private def outer (f : C(X,ℝ)) : B →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun b => mean (inner t r x₀ f b))
    continuous_of_discreteTopology ‖f‖ (fun b => (mean_norm_le _).trans (inner_norm t r x₀ f b))
private def average (f : C(X,ℝ)) : ℝ := mean (outer t r x₀ f)
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_add (f g : C(X,ℝ)) (b : B) : inner t r x₀ (f+g) b = inner t r x₀ f b + inner t r x₀ g b := by ext; rfl
omit [AddCommGroup A] [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] in
lemma inner_smul (c : ℝ) (f : C(X,ℝ)) (b : B) : inner t r x₀ (c • f) b = c • inner t r x₀ f b := by ext; rfl
omit [AddCommGroup B] in
lemma outer_add (f g : C(X,ℝ)) : outer t r x₀ (f+g) = outer t r x₀ f + outer t r x₀ g := by
  ext b
  exact (congrArg mean (inner_add t r x₀ f g b)).trans (mean_add _ _)
omit [AddCommGroup B] in
lemma outer_smul (c : ℝ) (f : C(X,ℝ)) : outer t r x₀ (c • f) = c • outer t r x₀ f := by
  ext b
  exact (congrArg mean (inner_smul t r x₀ c f b)).trans (mean_smul _ _)
lemma average_add (f g : C(X,ℝ)) : average t r x₀ (f+g) = average t r x₀ f + average t r x₀ g := by
  simp only [average,outer_add,mean_add]
lemma average_smul (c : ℝ) (f : C(X,ℝ)) : average t r x₀ (c • f) = c * average t r x₀ f := by
  simp only [average,outer_smul,mean_smul]
lemma average_mono {f g : C(X,ℝ)} (h : f ≤ g) : average t r x₀ f ≤ average t r x₀ g := by
  have hp : 0 ≤ average t r x₀ (g-f) := mean_nonneg _ fun b => mean_nonneg _ fun a => sub_nonneg.mpr (h _)
  have he : average t r x₀ (g-f) = average t r x₀ g - average t r x₀ f := by
    rw [sub_eq_add_neg,average_add,← neg_one_smul ℝ f,average_smul]; ring
  linarith
lemma average_const (c : ℝ) : average t r x₀ (ContinuousMap.const X c) = c := by
  have hi (b : B) : inner t r x₀ (ContinuousMap.const X c) b = BoundedContinuousFunction.const A c := by ext; rfl
  have ho : outer t r x₀ (ContinuousMap.const X c) = BoundedContinuousFunction.const B c := by
    ext b
    change mean (inner t r x₀ _ b) = c
    rw [hi,mean_const]
  rw [average,ho,mean_const]
lemma average_translation (ht : ∀ a b x, t a (t b x) = t (a+b) x)
    (φ : B → A → A) (hc : ∀ a b x, t a (r b x) = r b (t (φ b a) x))
    (a : A) (f : C(X,ℝ)) (ha : Continuous (t a)) :
    average t r x₀ (f.comp ⟨t a,ha⟩) = average t r x₀ f := by
  unfold average
  congr 1
  ext b
  change mean (inner t r x₀ (f.comp _) b) = mean (inner t r x₀ f b)
  have he : inner t r x₀ (f.comp ⟨t a,ha⟩) b = shift (φ b a) (inner t r x₀ f b) := by
    ext z
    change f (t a (r b (t z x₀))) = f (r b (t (z+φ b a) x₀))
    rw [hc,ht,add_comm]
  rw [he,mean_shift]
lemma average_rotation (hr : ∀ a b x, r a (r b x) = r (a+b) x)
    (b : B) (f : C(X,ℝ)) (hb : Continuous (r b)) :
    average t r x₀ (f.comp ⟨r b,hb⟩) = average t r x₀ f := by
  unfold average
  have he : outer t r x₀ (f.comp ⟨r b,hb⟩) = shift b (outer t r x₀ f) := by
    ext c
    change mean (inner t r x₀ (f.comp _) c) = mean (inner t r x₀ f (c+b))
    congr 1
    ext z
    change f (r b (r c (t z x₀))) = f (r (c+b) (t z x₀))
    rw [hr,add_comm]
  rw [he,mean_shift]
variable [T2Space X] [MeasurableSpace X] [BorelSpace X]
private def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := average t r x₀ f.toContinuousMap
  map_add' := fun f g => average_add t r x₀ f.toContinuousMap g.toContinuousMap
  map_smul' := fun c f => average_smul t r x₀ c f.toContinuousMap
  monotone' := fun _ _ h => average_mono t r x₀ h
private def measure : Measure X := RealRMK.rieszMeasure (functional t r x₀)
private instance : IsFiniteMeasure (measure t r x₀) := by dsimp [measure]; infer_instance
private instance : (measure t r x₀).Regular := by dsimp [measure]; infer_instance
lemma integral (f : C(X,ℝ)) : ∫ x, f x ∂measure t r x₀ = average t r x₀ f :=
  RealRMK.integral_rieszMeasure (functional t r x₀) (CompactlySupportedContinuousMap.continuousMapEquiv f)
private instance : IsProbabilityMeasure (measure t r x₀) := by
  have he := integral t r x₀ (ContinuousMap.const X 1)
  rw [average_const] at he
  change (∫ _ : X, (1:ℝ) ∂measure t r x₀) = 1 at he
  simp only [integral_const,smul_eq_mul,mul_one] at he
  constructor
  exact (ENNReal.toReal_eq_one_iff _).mp he
lemma preserving_of_average (s : X ≃ₜ X)
    (hav : ∀ f : C(X,ℝ), average t r x₀ (f.comp ⟨s,s.continuous⟩) = average t r x₀ f) :
    MeasurePreserving s (measure t r x₀) (measure t r x₀) := by
  refine ⟨s.continuous.measurable,?_⟩
  have : (Measure.map s (measure t r x₀)).Regular := Measure.Regular.map s
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂(measure t r x₀).map s) = ∫ x, f.toContinuousMap x ∂measure t r x₀
  rw [integral_map s.continuous.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact (integral t r x₀ (f.toContinuousMap.comp ⟨s,s.continuous⟩)).trans ((hav f.toContinuousMap).trans (integral t r x₀ f.toContinuousMap).symm)
end EuclideanFiveColor.StationaryMean
end
end
end ParishLaw
end

-- OAI.Analysis.PlaneSpectrum.Representations
section
namespace ParishLaw

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction
namespace PlaneFiveColor.Spectral
variable [Carrier]

private def Rot := Additive K deriving AddCommGroup
private instance : TopologicalSpace Rot := ⊥
private instance : DiscreteTopology Rot := ⟨rfl⟩
private def rotMul (g : Rot) : K := Additive.toMul g
private def mulRot (k : K) : Rot := Additive.ofMul k
@[simp] lemma rotMul_mulRot (k : K) : rotMul (mulRot k) = k := rfl
@[simp] lemma mulRot_rotMul (g : Rot) : mulRot (rotMul g) = g := rfl
end PlaneFiveColor.Spectral
end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace EuclideanFiveColor.Koopman
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
private def isometry (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  __ := Lp.compMeasurePreservingₗᵢ ℂ s hs
  invFun := Lp.compMeasurePreserving s.symm (hs.symm s)
  left_inv v := by
    change Lp.compMeasurePreserving s.symm (hs.symm s) (Lp.compMeasurePreserving s hs v) = v
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : (s : X → X) ∘ s.symm = id := funext s.apply_symm_apply
    simp only [he,Lp.compMeasurePreserving_id_apply]
  right_inv v := by
    change Lp.compMeasurePreserving s hs (Lp.compMeasurePreserving s.symm (hs.symm s) v) = v
    rw [← Lp.compMeasurePreserving_comp_apply]
    have he : (s.symm : X → X) ∘ s = id := funext s.symm_apply_apply
    simp only [he,Lp.compMeasurePreserving_id_apply]
private def unitary (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) : unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  Unitary.linearIsometryEquiv.symm (isometry μ s hs)
lemma unitary_apply (s : X ≃ᵐ X) (hs : MeasurePreserving s μ μ) (v : Lp ℂ 2 μ) :
    (unitary μ s hs : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) v = Lp.compMeasurePreserving s hs v := rfl
lemma nonlinear_commute (s : X → X) (hs : MeasurePreserving s μ μ)
    {F : ℂ → ℂ} {c : ℝ≥0} (hF : LipschitzWith c F) (h0 : F 0 = 0) (v : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving s hs (hF.compLp h0 v) = hF.compLp h0 (Lp.compMeasurePreserving s hs v) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (hF.compLp h0 v) hs,
    hs.quasiMeasurePreserving.ae (hF.coeFn_compLp h0 v),
    hF.coeFn_compLp h0 (Lp.compMeasurePreserving s hs v),Lp.coeFn_compMeasurePreserving v hs] with x h1 h2 h3 h4
  simp only [Function.comp_apply,h1,h2,h3,h4]
end EuclideanFiveColor.Koopman
end
noncomputable section
open Filter Topology
namespace EuclideanFiveColor.ContinuousVectors
variable {A H : Type*} [AddCommGroup A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))
private def op (a : A) : H →L[ℂ] H := U (Multiplicative.ofAdd a)
@[simp] lemma op_zero (v : H) : op U 0 v = v := by simp [op]
lemma op_add (a b : A) (v : H) : op U (a+b) v = op U a (op U b v) := by
  change ((U (Multiplicative.ofAdd a * Multiplicative.ofAdd b) : unitary _) : H →L[ℂ] H) v = _
  rw [map_mul]; rfl
lemma op_comm (a b : A) (v : H) : op U a (op U b v) = op U b (op U a v) := by
  rw [← op_add,← op_add,add_comm]
lemma norm_op (a : A) (v : H) : ‖op U a v‖ = ‖v‖ := Unitary.norm_map _ _
lemma dist_op (a : A) (v w : H) : dist (op U a v) (op U a w) = dist v w := by
  simp only [dist_eq_norm,← map_sub,norm_op]
variable [TopologicalSpace A]
private def space : Submodule ℂ H where
  carrier := {v | Tendsto (fun a => op U a v) (𝓝 0) (𝓝 v)}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change Tendsto (fun a => op U a (v+w)) (𝓝 0) (𝓝 (v+w))
    simpa only [map_add] using hv.add hw
  smul_mem' := by
    intro c v hv
    change Tendsto (fun a => op U a (c • v)) (𝓝 0) (𝓝 (c • v))
    simpa only [map_smul] using hv.const_smul c
lemma mem_space (v : H) : v ∈ space U ↔ Tendsto (fun a => op U a v) (𝓝 0) (𝓝 v) := Iff.rfl
lemma isClosed_space : IsClosed (space U : Set H) := by
  apply isClosed_of_closure_subset
  intro v hv
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨w,hw,hd⟩ := Metric.mem_closure_iff.mp hv (ε/4) (by positivity)
  have ht := Metric.tendsto_nhds.mp hw (ε/2) (by positivity)
  filter_upwards [ht] with a ha
  have he : dist (op U a v) v ≤ 2 * dist v w + dist (op U a w) w := by
    calc
      _ ≤ dist (op U a v) (op U a w) + dist (op U a w) v := dist_triangle _ _ _
      _ ≤ dist (op U a v) (op U a w) + (dist (op U a w) w + dist w v) :=
        by linarith [dist_triangle (op U a w) w v]
      _ = _ := by rw [dist_op,dist_comm w v]; ring
  linarith
private instance : CompleteSpace (space U) := (isClosed_space U).completeSpace_coe
lemma op_mem (a : A) {v : H} (hv : v ∈ space U) : op U a v ∈ space U := by
  have ht := ((op U a).continuous.tendsto v).comp hv
  change Tendsto (fun z => op U z (op U a v)) (𝓝 0) (𝓝 (op U a v))
  simpa only [Function.comp_def,op_comm U a] using ht
variable [IsTopologicalAddGroup A]
lemma orbit_continuous {v : H} (hv : v ∈ space U) : Continuous (fun a => op U a v) := by
  rw [continuous_iff_continuousAt]
  intro a
  have ht0 : Tendsto (fun b : A => b-a) (𝓝 a) (𝓝 0) := by
    have hh := ((tendsto_id : Tendsto (fun b : A => b) (𝓝 a) (𝓝 a)).sub_const a)
    rw [sub_self] at hh
    exact hh
  have ht := (((op U a).continuous.tendsto v).comp hv).comp ht0
  change Tendsto (fun b => op U b v) (𝓝 a) (𝓝 (op U a v))
  convert ht using 1
  ext b
  change op U b v = op U a (op U (b-a) v)
  rw [← op_add]
  congr 1
  abel_nf
end EuclideanFiveColor.ContinuousVectors
end

noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace EuclideanFiveColor.VectorMeasure
variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (Φ : C(X,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H)
private def realCM (f : C(X,ℝ)) : C(X,ℂ) := ⟨fun x => (f x : ℂ),by fun_prop⟩
@[simp] lemma realCM_apply (f : C(X,ℝ)) (x : X) : realCM f x = (f x : ℂ) := rfl
@[simp] lemma realCM_add (f g : C(X,ℝ)) : realCM (f+g) = realCM f+realCM g := by ext; simp
@[simp] lemma realCM_sub (f g : C(X,ℝ)) : realCM (f-g) = realCM f-realCM g := by ext; simp
@[simp] lemma realCM_smul (c : ℝ) (f : C(X,ℝ)) : realCM (c • f) = (c:ℂ) • realCM f := by ext; simp
@[simp] lemma realCM_one : realCM (1:C(X,ℝ)) = 1 := by ext; simp
variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma real_nonneg (f : C(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ (⟪v, Φ (realCM f) v⟫_ℂ).re := by
  let g : C(X,ℂ) := realCM ⟨fun x => Real.sqrt (f x),by fun_prop⟩
  have he : star g * g = realCM f := by
    ext x
    simp only [ContinuousMap.mul_apply,ContinuousMap.star_apply,realCM_apply,g,ContinuousMap.coe_mk,Complex.star_def,Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    exact congrArg Complex.ofReal (Real.mul_self_sqrt (show 0 ≤ f x from hf x))
  rw [← he,map_mul,map_star]
  change 0 ≤ (⟪v, (star (Φ g)) ((Φ g) v)⟫_ℂ).re
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := (Φ g) v)

private def functional : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ where
  toFun f := (⟪v,Φ (realCM f.toContinuousMap) v⟫_ℂ).re
  map_add' f g := by
    change (⟪v,Φ (realCM (f.toContinuousMap+g.toContinuousMap)) v⟫_ℂ).re = _
    simp
  map_smul' c f := by
    change (⟪v,Φ (realCM (c • f.toContinuousMap)) v⟫_ℂ).re = c * _
    rw [realCM_smul,map_smul]
    simp only [FunLike.coe_smul,Pi.smul_apply,inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  monotone' f g hfg := by
    have he := real_nonneg Φ v (g.toContinuousMap-f.toContinuousMap) (sub_nonneg.mpr hfg)
    simpa [inner_sub_right] using he

private def measure : Measure X := RealRMK.rieszMeasure (functional Φ v)
private instance : IsFiniteMeasure (measure Φ v) := by dsimp [measure]; infer_instance
private instance : (measure Φ v).Regular := by dsimp [measure]; infer_instance
lemma integral_real (f : C(X,ℝ)) : ∫ x, f x ∂measure Φ v = (⟪v,Φ (realCM f) v⟫_ℂ).re := by
  exact RealRMK.integral_rieszMeasure (functional Φ v) (CompactlySupportedContinuousMap.continuousMapEquiv f)
lemma integral_complex (f : C(X,ℂ)) : ∫ x, f x ∂measure Φ v = ⟪v,Φ f v⟫_ℂ := by
  let fr : C(X,ℝ) := ⟨fun x => (f x).re,by fun_prop⟩
  let fi : C(X,ℝ) := ⟨fun x => (f x).im,by fun_prop⟩
  have he : f = realCM fr + Complex.I • realCM fi := by
    ext x
    simpa [fr,fi,smul_eq_mul,mul_comm] using (Complex.re_add_im (f x)).symm
  have hi_real (g : C(X,ℝ)) : (⟪v,Φ (realCM g) v⟫_ℂ).im = 0 := by
    have hs : star (Φ (realCM g)) = Φ (realCM g) := by
      rw [← map_star]; congr 1; ext x; simp
    have ht := inner_conj_symm (𝕜 := ℂ) v (Φ (realCM g) v)
    rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,hs] at ht
    have hh := congrArg Complex.im ht
    simp only [Complex.conj_im] at hh
    linarith
  have hb (g : C(X,ℝ)) : ∫ x, (g x : ℂ) ∂measure Φ v = ⟪v,Φ (realCM g) v⟫_ℂ := by
    rw [integral_complex_ofReal,integral_real]
    exact Complex.ext (by simp) (by simp [hi_real])
  rw [he,map_add,map_smul]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,realCM_apply,add_apply,
    smul_apply,inner_add_right,inner_smul_right]
  have hir : Integrable (fun x => (fr x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fr.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hii : Integrable (fun x => (fi x : ℂ)) (measure Φ v) :=
    (Complex.continuous_ofReal.comp fi.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = (∫ x, (fr x : ℂ) ∂measure Φ v) +
        (∫ x, Complex.I • (fi x : ℂ) ∂measure Φ v) := integral_add hir (hii.smul Complex.I)
    _ = _ := by rw [integral_smul,hb,hb]; rfl
lemma measure_univ : (measure Φ v).real Set.univ = ‖v‖^2 := by
  have he := integral_real Φ v (1:C(X,ℝ))
  simp only [ContinuousMap.one_apply,integral_const,smul_eq_mul,mul_one,realCM_one,map_one,one_apply_eq_self] at he
  exact he.trans (inner_self_eq_norm_sq (𝕜 := ℂ) v)
end EuclideanFiveColor.VectorMeasure
end

end ParishLaw
end

-- OAI.Analysis.PlaneSpectrum.SpectralMeasure
section
namespace ParishLaw

noncomputable section
open scoped ComplexConjugate IsMulCommutative
namespace EuclideanFiveColor.CommutingSpectral
variable {G H : Type*} [CommGroup G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : G →* unitary (H →L[ℂ] H))
private abbrev algebra : StarSubalgebra ℂ (H →L[ℂ] H) :=
  (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g : H →L[ℂ] H)))).topologicalClosure
private instance algebra_closed : IsClosed (algebra U : Set (H →L[ℂ] H)) :=
  StarSubalgebra.isClosed_topologicalClosure _
set_option synthInstance.maxHeartbeats 80000 in
lemma adjoin_comm : IsMulCommutative (StarAlgebra.adjoin ℂ (Set.range (fun g => (U g : H →L[ℂ] H)))) := by
  apply StarAlgebra.isMulCommutative_adjoin
  · rintro _ ⟨left,rfl⟩ _ ⟨right,rfl⟩
    change ((U left * U right : unitary _) : H →L[ℂ] H) = ((U right * U left : unitary _) : H →L[ℂ] H)
    rw [← map_mul,← map_mul,mul_comm]
  · rintro _ ⟨left,rfl⟩ _ ⟨right,rfl⟩
    change ((U left * (U right)⁻¹ : unitary _) : H →L[ℂ] H) = (((U right)⁻¹ * U left : unitary _) : H →L[ℂ] H)
    rw [← map_inv,← map_mul,← map_mul,mul_comm]
open scoped IsMulCommutative in
private instance algebra_commRing : CommRing (algebra U) :=
  let := adjoin_comm U
  StarSubalgebra.commRingTopologicalClosure _ mul_comm
private instance algebra_commCStar : CommCStarAlgebra (algebra U) where

private def generator (g : G) : algebra U :=
  ⟨U g,StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g))⟩
@[simp] lemma generator_one : generator U 1 = 1 := by ext; simp [generator]
@[simp] lemma generator_mul (g h : G) : generator U (g*h) = generator U g * generator U h := by
  apply Subtype.ext; change (U (g*h) : H →L[ℂ] H) = (U g : H →L[ℂ] H) * U h
  rw [map_mul]; rfl
lemma generator_unitary (g : G) : generator U g ∈ unitary (algebra U) := by
  constructor <;> apply Subtype.ext
  · exact (U g).property.1
  · exact (U g).property.2
variable [TopologicalSpace G] [DiscreteTopology G]
private abbrev Spectrum := WeakDual.characterSpace ℂ (algebra U)
private def character (φ : Spectrum U) : PontryaginDual G where
  toFun g := ⟨gelfandStarTransform (algebra U) (generator U g) φ, by
    change gelfandStarTransform (algebra U) (generator U g) φ ∈ Metric.sphere (0:ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
    apply CStarRing.norm_of_mem_unitary
    exact Unitary.map_mem ((ContinuousMap.evalStarAlgHom ℂ ℂ φ).comp
      (gelfandStarTransform (algebra U)).toStarAlgHom) (generator_unitary U g)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change _ = (gelfandStarTransform (algebra U) (generator U g) φ) *
      (gelfandStarTransform (algebra U) (generator U h) φ)
    simp
  continuous_toFun := continuous_of_discreteTopology
lemma character_apply (φ : Spectrum U) (g : G) :
    (character U φ g : ℂ) = gelfandStarTransform (algebra U) (generator U g) φ := rfl
lemma character_continuous : Continuous (character U) := by
  apply ContinuousMonoidHom.isClosedEmbedding_coe.isEmbedding.isInducing.continuous_iff.mpr
  apply continuous_pi; intro g
  exact Continuous.subtype_mk (map_continuous (gelfandStarTransform (algebra U) (generator U g))) _
private def calculus : C(PontryaginDual G,ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (algebra U).subtype.comp <| (gelfandStarTransform (algebra U)).symm.toStarAlgHom.comp
    (ContinuousMap.compStarAlgHom' ℂ ℂ ⟨character U,character_continuous U⟩)
private def evaluation (g : G) : C(PontryaginDual G,ℂ) :=
  ⟨fun d => (d g : ℂ),continuous_subtype_val.comp ((continuous_apply g).comp ContinuousMonoidHom.isClosedEmbedding_coe.continuous)⟩
lemma calculus_evaluation (g : G) : calculus U (evaluation g) = U g := by
  change ((gelfandStarTransform (algebra U)).symm ((evaluation g).comp ⟨character U,character_continuous U⟩) : H →L[ℂ] H) = U g
  have he : (evaluation g).comp ⟨character U,character_continuous U⟩ =
      gelfandStarTransform (algebra U) (generator U g) := by ext φ; rfl
  rw [he,StarAlgEquiv.symm_apply_apply]; rfl
end EuclideanFiveColor.CommutingSpectral
end

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace EuclideanFiveColor.CommutingSpectral
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
lemma evaluation_one : evaluation (1:G) = 1 := by
  ext d
  change (d 1 : ℂ) = 1
  rw [map_one]; rfl
lemma evaluation_mul (g h : G) : evaluation (g*h) = evaluation g * evaluation h := by
  ext d
  change (d (g*h) : ℂ) = (d g : ℂ)*(d h : ℂ)
  rw [map_mul]; rfl
lemma star_evaluation (g : G) : star (evaluation g) = evaluation g⁻¹ := by
  ext d
  change star (d g : ℂ) = (d g⁻¹ : ℂ)
  rw [map_inv]
  exact (Circle.coe_inv_eq_conj (d g)).symm
private def evaluationHom : G →* C(PontryaginDual G,ℂ) where
  toFun := evaluation
  map_one' := evaluation_one
  map_mul' := evaluation_mul
lemma evaluation_span_dense : Dense (Submodule.span ℂ (Set.range (evaluation (G := G))) : Set C(PontryaginDual G,ℂ)) := by
  let A := StarAlgebra.adjoin ℂ (Set.range (evaluation (G := G)))
  have hs : star (Set.range (evaluation (G := G))) = Set.range (evaluation (G := G)) := by
    ext f
    rw [Set.mem_star]
    constructor
    · rintro ⟨g,hg⟩
      refine ⟨g⁻¹,?_⟩
      rw [← star_evaluation,hg,star_star]
    · rintro ⟨g,rfl⟩
      exact ⟨g⁻¹,(star_evaluation g).symm⟩
  have he : A.toSubalgebra.toSubmodule = Submodule.span ℂ (Set.range (evaluation (G := G))) := by
    rw [StarAlgebra.adjoin_eq_span,hs,Set.union_self]
    have hc : Submonoid.closure (Set.range (evaluation (G := G))) = MonoidHom.mrange (evaluationHom (G := G)) :=
      Submonoid.closure_eq (MonoidHom.mrange (evaluationHom (G := G)))
    rw [hc]
    rfl
  have hsep : A.SeparatesPoints := by
    intro d e hde
    have hn : ∃ g, d g ≠ e g := by
      by_contra! h
      exact hde (DFunLike.ext _ _ h)
    obtain ⟨g,hg⟩ := hn
    refine ⟨evaluation g,⟨evaluation g,StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self g),rfl⟩,?_⟩
    change (d g : ℂ) ≠ (e g : ℂ)
    exact fun h => hg (Subtype.ext h)
  have ht := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  rw [dense_iff_closure_eq,← he]
  change closure (A:Set C(PontryaginDual G,ℂ)) = _
  rw [← StarSubalgebra.topologicalClosure_coe,ht]
  rfl
end EuclideanFiveColor.CommutingSpectral
namespace EuclideanFiveColor.CompactIntegral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]
lemma integrableCM (f : C(X,ℂ)) : Integrable (f : X → ℂ) μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
private def linear : C(X,ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (integrableCM μ f) (integrableCM μ g)
  map_smul' c f := integral_smul c f
lemma norm_le (f : C(X,ℂ)) : ‖linear μ f‖ ≤ μ.real Set.univ * ‖f‖ := by
  simpa only [linear,LinearMap.coe_mk,AddHom.coe_mk,mul_comm] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall (ContinuousMap.norm_coe_le_norm f))
private def clm : C(X,ℂ) →L[ℂ] ℂ := (linear μ).mkContinuous (μ.real Set.univ) (norm_le μ)
lemma apply_clm (f : C(X,ℂ)) : clm μ f = ∫ x, f x ∂μ := rfl
end EuclideanFiveColor.CompactIntegral
namespace EuclideanFiveColor.CommutingSpectral
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
lemma measure_eq_of_fourier (μ ν : Measure (PontryaginDual G)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular]
    (h : ∀ g, ∫ d, (d g : ℂ) ∂μ = ∫ d, (d g : ℂ) ∂ν) : μ = ν := by
  have he : CompactIntegral.clm μ = CompactIntegral.clm ν := by
    apply ContinuousLinearMap.ext_on evaluation_span_dense
    rintro _ ⟨g,rfl⟩
    exact h g
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let fc : C(PontryaginDual G,ℂ) := ⟨fun d => (f d : ℂ),by fun_prop⟩
  have hh := congrArg (fun L : C(PontryaginDual G,ℂ) →L[ℂ] ℂ => (L fc).re) he
  simpa only [CompactIntegral.apply_clm,fc,ContinuousMap.coe_mk,integral_complex_ofReal,Complex.ofReal_re] using hh
end EuclideanFiveColor.CommutingSpectral
end

end ParishLaw
end

-- Erdos173.Basic
section
noncomputable section

namespace ParishPlane

open MeasureTheory

private def ζ : ℂ := ⟨1 / 2, √3 / 2⟩

lemma norm_ζ : ‖ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

lemma norm_one_sub_ζ : ‖1 - ζ‖ = 1 := by
  rw [Complex.norm_def, Real.sqrt_eq_one]
  simp [ζ, Complex.normSq]
  ring_nf
  norm_num

lemma norm_ζ_sub_one : ‖ζ - 1‖ = 1 := by
  rw [norm_sub_rev, norm_one_sub_ζ]
end ParishPlane
end
end

-- Erdos173.Transfer.LabelModel
section
noncomputable section

namespace ParishPlane.Transfer

open MeasureTheory
open ParishLaw ParishLaw.PlaneFiveColor.Spectral ParishLaw.EuclideanFiveColor ParishLaw.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace

variable [Carrier]

lemma sqrt_three_mem : ((√3 : ℝ) : ℂ) ∈ E :=
  Carrier.ofReal_mem (Carrier.sqrt_mem (by simp))

lemma exists_kCoeff_eq (z : E) (hz : ‖(z : ℂ)‖ = 1) : ∃ b : K, kCoeff b = z :=
  ⟨⟨⟨z, mem_sphere_zero_iff_norm.mpr hz⟩, z.property⟩, rfl⟩

@[simp] lemma coe_kCoeff (u : K) : ((kCoeff u : E) : ℂ) = (u.val : ℂ) := rfl

omit [Carrier] in

lemma ζ_eq : ζ = (1 + ((√3 : ℝ) : ℂ) * Complex.I) / 2 := by
  apply Complex.ext <;> simp [ζ]

lemma ζ_mem : ζ ∈ E := by
  rw [ζ_eq]
  have h₂ : (2 : ℂ) ∈ E := by simp
  exact E.div_mem (E.add_mem E.one_mem (E.mul_mem sqrt_three_mem imagUnit.property)) h₂

private def ζE : E := ⟨ζ, ζ_mem⟩

@[simp] lemma coe_ζE : (ζE : ℂ) = ζ := rfl

private def AvoidsSide (r : E) (η : E → Fin 2) : Prop :=
  ∀ p : E, ∀ u : K, ¬ (η (p + kCoeff u * r) = η p ∧ η (p + kCoeff u * (r * ζE)) = η p)

variable (R : Set E)

private def Admissible (η : E → Fin 2) : Prop := ∀ r ∈ R, AvoidsSide r η

private abbrev Space := {η : E → Fin 2 // Admissible R η}

theorem isClosed_admissible : IsClosed {η : E → Fin 2 | Admissible R η} := by
  unfold Admissible AvoidsSide
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun p =>
    isClosed_iInter fun u => ?_
  have hc : Continuous (fun η : E → Fin 2 =>
      (η p, η (p + kCoeff u * r), η (p + kCoeff u * (r * ζE)))) :=
    (continuous_apply p).prodMk ((continuous_apply _).prodMk (continuous_apply _))
  exact (isClosed_discrete {q : Fin 2 × Fin 2 × Fin 2 | ¬ (q.2.1 = q.1 ∧ q.2.2 = q.1)}).preimage hc

private instance : CompactSpace (Space R) := isCompact_iff_compactSpace.mp (isClosed_admissible R).isCompact

private def trans (a : E) (ω : Space R) : Space R := ⟨fun x => ω.val (x + a), by
  intro r hr p u h
  refine ω.property r hr (p + a) u ?_
  rwa [add_right_comm p a, add_right_comm p a]⟩

private def rotate (b : K) (ω : Space R) : Space R := ⟨fun x => ω.val (kCoeff b * x), by
  intro r hr p u h
  refine ω.property r hr (kCoeff b * p) (b * u) ?_
  simpa only [kCoeff_mul, mul_add, mul_assoc] using h⟩

@[simp] lemma trans_apply (a : E) (ω : Space R) (x : E) : (trans R a ω).val x = ω.val (x + a) :=
  rfl

@[simp] lemma rotate_apply (b : K) (ω : Space R) (x : E) :
    (rotate R b ω).val x = ω.val (kCoeff b * x) := rfl

lemma continuous_trans (a : E) : Continuous (trans R a) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (x + a)).comp continuous_subtype_val

lemma continuous_rotate (b : K) : Continuous (rotate R b) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun x => (continuous_apply (kCoeff b * x)).comp continuous_subtype_val

@[simp] lemma trans_zero (ω : Space R) : trans R 0 ω = ω := by
  apply Subtype.ext
  funext x
  simp

lemma trans_add (a b : E) (ω : Space R) : trans R a (trans R b ω) = trans R (a + b) ω := by
  apply Subtype.ext
  funext x
  simp [add_assoc]

@[simp] lemma rotate_one (ω : Space R) : rotate R 1 ω = ω := by
  apply Subtype.ext
  funext x
  simp

lemma rotate_mul (a b : K) (ω : Space R) : rotate R a (rotate R b ω) = rotate R (a * b) ω := by
  apply Subtype.ext
  funext x
  change ω.val (kCoeff b * (kCoeff a * x)) = ω.val (kCoeff (a * b) * x)
  rw [kCoeff_mul]
  ring_nf

lemma covariance (a : E) (b : K) (ω : Space R) :
    trans R a (rotate R b ω) = rotate R b (trans R (kCoeff b * a) ω) := by
  apply Subtype.ext
  funext x
  simp only [trans_apply, rotate_apply, mul_add]

private def transHomeo (a : E) : Space R ≃ₜ Space R where
  toFun := trans R a
  invFun := trans R (-a)
  left_inv ω := by rw [trans_add, neg_add_cancel, trans_zero]
  right_inv ω := by rw [trans_add, add_neg_cancel, trans_zero]
  continuous_toFun := continuous_trans R a
  continuous_invFun := continuous_trans R (-a)

private def rotateHomeo (b : K) : Space R ≃ₜ Space R where
  toFun := rotate R b
  invFun := rotate R b⁻¹
  left_inv ω := by rw [rotate_mul, inv_mul_cancel, rotate_one]
  right_inv ω := by rw [rotate_mul, mul_inv_cancel, rotate_one]
  continuous_toFun := continuous_rotate R b
  continuous_invFun := continuous_rotate R b⁻¹

private abbrev Trans := Additive DiscreteE

private def tr (a : Trans) : Space R → Space R := trans R (Multiplicative.toAdd (Additive.toMul a))

private def ro (b : Rot) : Space R → Space R := rotate R (rotMul b)

private def measure (ω₀ : Space R) : Measure (Space R) := StationaryMean.measure (tr R) (ro R) ω₀

private instance (ω₀ : Space R) : IsProbabilityMeasure (measure R ω₀) :=
  inferInstanceAs (IsProbabilityMeasure (StationaryMean.measure (tr R) (ro R) ω₀))

lemma trans_preserving (ω₀ : Space R) (a : E) :
    MeasurePreserving (trans R a) (measure R ω₀) (measure R ω₀) := by
  apply StationaryMean.preserving_of_average (tr R) (ro R) ω₀ (transHomeo R a)
  intro f
  apply StationaryMean.average_translation (tr R) (ro R) ω₀
    (fun a b x => trans_add R _ _ x)
    (fun b a => Additive.ofMul (Multiplicative.ofAdd
      (kCoeff (rotMul b) * Multiplicative.toAdd (Additive.toMul a))))
    (fun a b x => covariance R _ _ x) (Additive.ofMul (Multiplicative.ofAdd a)) f
    (continuous_trans R a)

lemma rotate_preserving (ω₀ : Space R) (b : K) :
    MeasurePreserving (rotate R b) (measure R ω₀) (measure R ω₀) := by
  apply StationaryMean.preserving_of_average (tr R) (ro R) ω₀ (rotateHomeo R b)
  intro f
  exact StationaryMean.average_rotation (tr R) (ro R) ω₀
    (fun a b x => rotate_mul R _ _ x) (mulRot b) f (continuous_rotate R b)

variable (ω₀ : Space R)

private abbrev Hilbert := Lp ℂ 2 (measure R ω₀)

private def translation (a : E) : unitary (Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) :=
  Koopman.unitary (measure R ω₀) (transHomeo R a).toMeasurableEquiv (trans_preserving R ω₀ a)

private def rotation (b : K) : unitary (Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) :=
  Koopman.unitary (measure R ω₀) (rotateHomeo R b).toMeasurableEquiv (rotate_preserving R ω₀ b)

private def representation : DiscreteE →* unitary (Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) where
  toFun a := translation R ω₀ (Multiplicative.toAdd a)
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving (trans R 0) (trans_preserving R ω₀ 0) v = v
    have he : trans R 0 = id := funext (trans_zero R)
    simp only [he, Lp.compMeasurePreserving_id_apply]
  map_mul' a b := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro v
    change Lp.compMeasurePreserving
        (trans R (Multiplicative.toAdd a + Multiplicative.toAdd b)) _ v =
      Lp.compMeasurePreserving (trans R (Multiplicative.toAdd a)) _
        (Lp.compMeasurePreserving (trans R (Multiplicative.toAdd b)) _ v)
    rw [← Lp.compMeasurePreserving_comp_apply]
    congr 2
    funext x
    exact (congrArg (fun c => trans R c x) (add_comm _ _)).trans (trans_add R _ _ x).symm

lemma op_apply (a : E) (v : Hilbert R ω₀) : op (representation R ω₀) a v =
    Lp.compMeasurePreserving (trans R a) (trans_preserving R ω₀ a) v := rfl

lemma rotation_apply (b : K) (v : Hilbert R ω₀) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) v =
      Lp.compMeasurePreserving (rotate R b) (rotate_preserving R ω₀ b) v := rfl

lemma rotation_covariance (b : K) (a : E) (v : Hilbert R ω₀) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) (op (representation R ω₀) a v) =
      op (representation R ω₀) (kCoeff b * a)
        ((rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) v) := by
  simp only [rotation_apply, op_apply, ← Lp.compMeasurePreserving_comp_apply]
  congr 2
  funext x
  exact covariance R a b x

private def sgnAt (z : E) (ω : Space R) : ℝ := if ω.val z = 0 then 1 else -1

lemma continuous_sgnAt (z : E) : Continuous (sgnAt R z) :=
  (continuous_of_discreteTopology (f := fun c : Fin 2 => if c = 0 then (1 : ℝ) else -1)).comp
    ((continuous_apply z).comp continuous_subtype_val)

private def corr (z : E) : ℝ := ∫ ω, sgnAt R 0 ω * sgnAt R z ω ∂measure R ω₀

lemma memLp_sign : MemLp (fun ω => (sgnAt R 0 ω : ℂ)) 2 (measure R ω₀) := by
  refine MemLp.of_bound ?_ 1 ?_
  · exact (Complex.continuous_ofReal.comp (continuous_sgnAt R 0)).aestronglyMeasurable
  · exact .of_forall fun ω => by dsimp [sgnAt]; split_ifs <;> simp

private def signVector : Hilbert R ω₀ := (memLp_sign R ω₀).toLp fun ω => (sgnAt R 0 ω : ℂ)

lemma sign_ae : signVector R ω₀ =ᵐ[measure R ω₀] fun ω => (sgnAt R 0 ω : ℂ) :=
  (memLp_sign R ω₀).coeFn_toLp

lemma inner_signVector (z : E) :
    ⟪signVector R ω₀, op (representation R ω₀) z (signVector R ω₀)⟫_ℂ = (corr R ω₀ z : ℂ) := by
  rw [op_apply, L2.inner_def, corr, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [sign_ae R ω₀,
    Lp.coeFn_compMeasurePreserving (signVector R ω₀) (trans_preserving R ω₀ z),
    (trans_preserving R ω₀ z).quasiMeasurePreserving.ae (sign_ae R ω₀)] with ω h1 h2 h3
  simp only [h1, h2, Function.comp_apply, h3, sgnAt, trans_apply, zero_add]
  split_ifs <;> simp

lemma norm_signVector_sq : ‖signVector R ω₀‖ ^ 2 = 1 := by
  have h : ⟪signVector R ω₀, signVector R ω₀⟫_ℂ = 1 := by
    rw [L2.inner_def]
    have he : (fun ω => ⟪signVector R ω₀ ω, signVector R ω₀ ω⟫_ℂ) =ᵐ[measure R ω₀]
        fun _ => (1 : ℂ) := by
      filter_upwards [sign_ae R ω₀] with ω h1
      simp only [h1, sgnAt]
      split_ifs <;> simp
    rw [integral_congr_ae he]
    simp
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : ((‖signVector R ω₀‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h
  exact Complex.ofReal_injective h'

lemma rotation_signVector (b : K) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) (signVector R ω₀) = signVector R ω₀ := by
  rw [rotation_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (signVector R ω₀) (rotate_preserving R ω₀ b),
    (rotate_preserving R ω₀ b).quasiMeasurePreserving.ae (sign_ae R ω₀), sign_ae R ω₀]
    with ω h1 h2 h3
  simp only [Function.comp_apply, h1, h2, h3, sgnAt, rotate_apply, mul_zero]

lemma integrable_of_continuous {g : Space R → ℝ} (hg : Continuous g) :
    Integrable g (measure R ω₀) :=
  hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

lemma integral_trans (a : E) (g : Space R → ℝ) :
    ∫ ω, g (trans R a ω) ∂measure R ω₀ = ∫ ω, g ω ∂measure R ω₀ :=
  (trans_preserving R ω₀ a).integral_comp (transHomeo R a).measurableEmbedding g

lemma integral_rotate (b : K) (g : Space R → ℝ) :
    ∫ ω, g (rotate R b ω) ∂measure R ω₀ = ∫ ω, g ω ∂measure R ω₀ :=
  (rotate_preserving R ω₀ b).integral_comp (rotateHomeo R b).measurableEmbedding g

lemma integral_sgnAt_mul (a b : E) :
    ∫ ω, sgnAt R a ω * sgnAt R b ω ∂measure R ω₀ = corr R ω₀ (b - a) := by
  rw [corr, ← integral_trans R ω₀ a (fun ω => sgnAt R 0 ω * sgnAt R (b - a) ω)]
  simp [sgnAt]

theorem corr_radial {z w : E} (h : ‖(z : ℂ)‖ = ‖(w : ℂ)‖) : corr R ω₀ z = corr R ω₀ w := by
  rcases eq_or_ne z 0 with rfl | hz
  · have hw : w = 0 := by
      apply Subtype.ext
      simpa [eq_comm] using h
    rw [hw]
  have hz' : (z : ℂ) ≠ 0 := by simpa using hz
  obtain ⟨b, hb⟩ := exists_kCoeff_eq (w / z) (by
    rw [IntermediateField.coe_div, norm_div, ← h, div_self (norm_ne_zero_iff.mpr hz')])
  have hb' : kCoeff b * z = w := by rw [hb, div_mul_cancel₀ w hz]
  rw [← hb', corr, corr, ← integral_rotate R ω₀ b (fun ω => sgnAt R 0 ω * sgnAt R z ω)]
  simp only [sgnAt, rotate_apply, mul_zero]
  rfl

lemma sgn_triangle {r : E} (hr : r ∈ R) (ω : Space R) (p : E) (u : K) :
    sgnAt R p ω * sgnAt R (p + kCoeff u * r) ω +
      sgnAt R p ω * sgnAt R (p + kCoeff u * (r * ζE)) ω +
      sgnAt R (p + kCoeff u * r) ω * sgnAt R (p + kCoeff u * (r * ζE)) ω = -1 := by
  have h := ω.property r hr p u
  unfold sgnAt
  generalize ω.val p = A at *
  generalize ω.val (p + kCoeff u * r) = B at *
  generalize ω.val (p + kCoeff u * (r * ζE)) = C at *
  fin_cases A <;> fin_cases B <;> fin_cases C <;> simp_all

theorem corr_triangle {r : E} (hr : r ∈ R) (u : K) :
    corr R ω₀ (kCoeff u * r) + corr R ω₀ (kCoeff u * (r * ζE)) +
      corr R ω₀ (kCoeff u * (r * ζE) - kCoeff u * r) = -1 := by
  have hi {g : Space R → ℝ} (hg : Continuous g) := integrable_of_continuous R ω₀ hg
  have hc := continuous_sgnAt R
  have h := integral_congr_ae (μ := measure R ω₀)
    (Filter.Eventually.of_forall (sgn_triangle R hr · 0 u))
  rw [integral_add (hi (by fun_prop)) (hi (by fun_prop)),
    integral_add (hi (by fun_prop)) (hi (by fun_prop)), integral_sgnAt_mul, integral_sgnAt_mul,
    integral_sgnAt_mul] at h
  simpa using h

theorem corr_side {r : E} (hr : r ∈ R) : corr R ω₀ r = -1 / 3 := by
  have h := corr_triangle R ω₀ hr 1
  have h₁ : corr R ω₀ (kCoeff 1 * (r * ζE)) = corr R ω₀ r := by
    apply corr_radial
    simp [norm_ζ]
  have h₂ : corr R ω₀ (kCoeff 1 * (r * ζE) - kCoeff 1 * r) = corr R ω₀ r := by
    apply corr_radial
    have he : ((kCoeff 1 * (r * ζE) - kCoeff 1 * r : E) : ℂ) = (r : ℂ) * (ζ - 1) := by
      simp only [kCoeff_one, one_mul]
      push_cast
      rw [coe_ζE]
      ring
    rw [he, norm_mul, norm_ζ_sub_one, mul_one]
  rw [h₁, h₂, kCoeff_one, one_mul] at h
  linarith

end ParishPlane.Transfer

end
end

-- OAI.Analysis.PlaneSpectrum.ConditionalSpectrum
section
namespace ParishLaw

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace PlaneFiveColor.Spectral
variable [Carrier]

private instance dualPolishSpace : PolishSpace D := by
  have : TopologicalSpace.SeparableSpace (DiscreteE → Circle) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (DiscreteE → Circle) := inferInstance
  exact ContinuousMonoidHom.isClosedEmbedding_coe.polishSpace

local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

private def eval (a : E) : D →* Circle where
  toFun d := d (Multiplicative.ofAdd a)
  map_one' := rfl
  map_mul' _ _ := rfl

lemma continuous_eval (a : E) : Continuous (eval a) :=
  (continuous_apply (Multiplicative.ofAdd a)).comp
    ContinuousMonoidHom.isClosedEmbedding_coe.continuous

lemma measurable_eval (a : E) : Measurable (eval a) := (continuous_eval a).measurable
lemma measurable_eval_coe (a : E) : Measurable (fun d => (eval a d : ℂ)) :=
  ((show Continuous (fun z : Circle => (z : ℂ)) from continuous_subtype_val).comp
    (continuous_eval a)).measurable
end PlaneFiveColor.Spectral
end
end ParishLaw
end

-- OAI.Geometry.PlaneColoring.BorelTransfer
section
namespace ParishLaw

noncomputable section
open Filter Topology
open scoped ComplexConjugate
namespace PlaneFiveColor.Spectral
variable [Carrier]
lemma dense_E : Dense (E : Set ℂ) := by
  intro z
  have hh : ∀ x y : ℝ, (x : ℂ)+(y : ℂ)*Complex.I ∈ closure (E : Set ℂ) := by
    intro x y
    refine (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).induction_on₂
      (p := fun x y : ℝ => (x : ℂ)+(y : ℂ)*Complex.I ∈ closure (E : Set ℂ)) ?_ ?_ x y
    · exact isClosed_closure.preimage ((Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul_const Complex.I))
    · intro q r
      apply subset_closure
      have hq : ((q : ℝ) : ℂ) ∈ E := Carrier.ofReal_mem (Carrier.ratCast_mem q)
      have hr : ((r : ℝ) : ℂ) ∈ E := Carrier.ofReal_mem (Carrier.ratCast_mem r)
      exact E.add_mem hq (E.mul_mem hr imagUnit.property)
  simpa only [Complex.re_add_im] using hh z.re z.im
lemma algebraic_norm (z : E) : (‖(z:ℂ)‖ : ℂ) ∈ E :=
  Carrier.ofReal_mem (Carrier.norm_mem z.property)
end PlaneFiveColor.Spectral
end
noncomputable section
open Filter Topology
namespace PlaneFiveColor.Spectral
variable [Carrier]
lemma normalized_algebraic (z : E) (hz : z ≠ 0) :
    ∃ b : K, (b.val : ℂ) = (z : ℂ) / (‖(z:ℂ)‖ : ℂ) := by
  have hn : ‖(z:ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr (Subtype.coe_ne_coe.mpr hz)
  have hb : ‖(z:ℂ) / (‖(z:ℂ)‖ : ℂ)‖ = 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self hn]
  exact ⟨⟨⟨_,mem_sphere_zero_iff_norm.mpr hb⟩,
    by
      change (z : ℂ)/(‖(z:ℂ)‖ : ℂ) ∈ E
      exact div_mem z.property (algebraic_norm z)⟩,rfl⟩
lemma circle_closed_induction {p : ℂ → Prop} (hp : IsClosed {z | p z})
    (halg : ∀ b : K, p (b.val : ℂ)) (u : Circle) : p (u : ℂ) := by
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (dense_E (u : ℂ))
  have hne : ∀ᶠ n in atTop, s n ≠ 0 := ht.eventually (isOpen_compl_singleton.mem_nhds (Circle.coe_ne_zero u))
  have hnorm : Tendsto (fun n => s n / (‖s n‖ : ℂ)) atTop (𝓝 (u : ℂ)) := by
    have h := ht.div (Complex.continuous_ofReal.continuousAt.tendsto.comp ht.norm)
      (show (‖(u:ℂ)‖ : ℂ) ≠ 0 by simp [Circle.norm_coe])
    have he : (u : ℂ) / (‖(u:ℂ)‖ : ℂ) = (u : ℂ) := by simp only [Circle.norm_coe,Complex.ofReal_one,div_one]
    rw [he] at h
    convert h using 1
    rfl
  apply hp.mem_of_tendsto hnorm
  filter_upwards [hne] with n hn
  obtain ⟨b,hb⟩ := normalized_algebraic ⟨s n,hs n⟩ (fun h => hn (congrArg Subtype.val h))
  rw [← hb]
  exact halg b
end PlaneFiveColor.Spectral
end
end ParishLaw
end

-- OAI.Analysis.PlaneSpectrum.Ergodicity
section
namespace ParishLaw

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.VectorMeasure EuclideanFiveColor.CommutingSpectral
variable [Carrier]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (W : K → unitary (H →L[ℂ] H))
  (hcov : ∀ k z w, (W k : H →L[ℂ] H) (ContinuousVectors.op U z w) =
    ContinuousVectors.op U ((kCoeff k)*z) ((W k : H →L[ℂ] H) w))
include hcov
lemma vectorMeasure_invariant (v : H) (hfix : ∀ k, (W k : H →L[ℂ] H) v = v) :
    ∀ k : K, MeasurePreserving (fun d : D => k • d) (measure (calculus U) v) (measure (calculus U) v) := by
  intro k
  have hm : Measurable (fun d : D => k • d) := (continuous_scalar (kCoeff k)).measurable
  refine ⟨hm,measure_eq_of_fourier _ _ (fun z => ?_)⟩
  change (∫ d, evaluation z d ∂(measure (calculus U) v).map (fun d : D => k • d)) = _
  rw [integral_map hm.aemeasurable ((evaluation z).continuous.measurable.aestronglyMeasurable)]
  change (∫ d, (eval (kCoeff k * Multiplicative.toAdd z) d : ℂ) ∂measure (calculus U) v) = _
  have hc (a : E) : (∫ d, (eval a d:ℂ) ∂measure (calculus U) v) =
      ⟪v,ContinuousVectors.op U a v⟫_ℂ := by
    have hh := integral_complex (calculus U) v (evaluation (G := DiscreteE) (Multiplicative.ofAdd a))
    rw [calculus_evaluation U (Multiplicative.ofAdd a : DiscreteE)] at hh
    exact hh
  change (∫ d, (eval (kCoeff k * Multiplicative.toAdd z) d : ℂ) ∂measure (calculus U) v) =
    ∫ d, (eval (Multiplicative.toAdd z) d:ℂ) ∂measure (calculus U) v
  rw [hc,hc]
  calc
    _ = ⟪(W k : H →L[ℂ] H) v,ContinuousVectors.op U (kCoeff k * Multiplicative.toAdd z) ((W k : H →L[ℂ] H) v)⟫_ℂ := by rw [hfix k]
    _ = ⟪(W k : H →L[ℂ] H) v,(W k : H →L[ℂ] H) (ContinuousVectors.op U (Multiplicative.toAdd z) v)⟫_ℂ := by rw [hcov]
    _ = _ := Unitary.inner_map_map (W k) v (ContinuousVectors.op U (Multiplicative.toAdd z) v)
end PlaneFiveColor.Spectral
end
end ParishLaw
end

section
namespace ParishLaw

noncomputable section
open scoped InnerProductSpace
namespace EuclideanFiveColor
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
lemma projection_fixed_of_contraction (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (F : H → H) (hF : LipschitzWith 1 F) (hS : ∀ v ∈ S, F v ∈ S)
    (v : H) (hv : F v = v) : F (S.starProjection v) = S.starProjection v := by
  let p := S.starProjection v
  have hp : p ∈ S := S.starProjection_apply_mem v
  have hh : ‖v-F p‖ ≤ ‖v-p‖ := by
    simpa only [hv,NNReal.coe_one,one_mul,dist_eq_norm] using hF.dist_le_mul v p
  have ho : ⟪v-p,p-F p⟫_ℂ = 0 := S.starProjection_inner_eq_zero v _ (S.sub_mem hp (hS p hp))
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v-p) (p-F p) ho
  rw [sub_add_sub_cancel] at he
  have hz : ‖p-F p‖ = 0 := by nlinarith [norm_nonneg (v-p),norm_nonneg (p-F p),norm_nonneg (v-F p)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace EuclideanFiveColor.ContinuousVectors
variable {A X : Type*} [AddCommGroup A] [TopologicalSpace A] [MeasurableSpace X]
  (μ : Measure X) (U : Multiplicative A →* unitary (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ))
  (s : A → X → X) (hs : ∀ a, MeasurePreserving (s a) μ μ)
  (hU : ∀ a v, op U a v = Lp.compMeasurePreserving (s a) (hs a) v)
include hU
lemma nonlinear_mem {F : ℂ → ℂ} {c : ℝ≥0} (hF : LipschitzWith c F) (h0 : F 0 = 0)
    {v : Lp ℂ 2 μ} (hv : v ∈ space U) : hF.compLp h0 v ∈ space U := by
  have ht := (hF.continuous_compLp h0).continuousAt.tendsto.comp hv
  change Tendsto (fun a => op U a (hF.compLp h0 v)) (𝓝 0) (𝓝 (hF.compLp h0 v))
  convert ht using 1
  funext a
  simp only [Function.comp_apply,hU,Koopman.nonlinear_commute]
omit hU
end EuclideanFiveColor.ContinuousVectors
end

noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace EuclideanFiveColor.ContinuousVectors
variable {A H : Type*} [AddCommGroup A] [TopologicalSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative A →* unitary (H →L[ℂ] H))
lemma covariance_mem (W : unitary (H →L[ℂ] H)) (φ : A ≃ₜ A) (hφ : φ 0 = 0)
    (hc : ∀ a v, (W : H →L[ℂ] H) (op U a v) = op U (φ a) ((W : H →L[ℂ] H) v))
    {v : H} (hv : v ∈ space U) : (W : H →L[ℂ] H) v ∈ space U := by
  have h0 : φ.symm 0 = 0 := by simpa only [hφ] using φ.symm_apply_apply 0
  have ht0 := φ.symm.continuous.tendsto 0
  rw [h0] at ht0
  have ht := ((W.val.continuous.tendsto v).comp hv).comp ht0
  change Tendsto (fun a => op U a ((W : H →L[ℂ] H) v)) (𝓝 0) (𝓝 ((W : H →L[ℂ] H) v))
  simpa only [Function.comp_def,hc,φ.apply_symm_apply] using ht
lemma projection_covariance_fixed (W : unitary (H →L[ℂ] H)) (φ : A ≃ₜ A) (hφ : φ 0 = 0)
    (hc : ∀ a v, (W : H →L[ℂ] H) (op U a v) = op U (φ a) ((W : H →L[ℂ] H) v))
    (v : H) (hv : (W : H →L[ℂ] H) v = v) :
    (W : H →L[ℂ] H) ((space U).starProjection v) = (space U).starProjection v := by
  exact projection_fixed_of_contraction (space U) (W : H →L[ℂ] H)
    (Unitary.linearIsometryEquiv W).isometry.lipschitz (fun w hw => covariance_mem U W φ hφ hc hw) v hv
lemma op_orthogonal (a : A) {v : H} (hv : v ∈ (space U)ᗮ) : op U a v ∈ (space U)ᗮ := by
  rw [Submodule.mem_orthogonal'] at hv ⊢
  intro w hw
  have hh := hv (op U (-a) w) (op_mem U (-a) hw)
  have he := Unitary.inner_map_map (U (Multiplicative.ofAdd a)) v (op U (-a) w)
  change ⟪op U a v,op U a (op U (-a) w)⟫_ℂ = _ at he
  rw [← op_add,add_neg_cancel,op_zero] at he
  exact he.trans hh
lemma projection_coefficient (v : H) (a : A)
    (hb : ⟪v-(space U).starProjection v, op U a (v-(space U).starProjection v)⟫_ℂ = 0) :
    ⟪(space U).starProjection v,op U a ((space U).starProjection v)⟫_ℂ = ⟪v,op U a v⟫_ℂ := by
  let p := (space U).starProjection v
  let b := v-p
  have hp : p ∈ space U := (space U).starProjection_apply_mem v
  have hbmem : b ∈ (space U)ᗮ := (space U).sub_starProjection_mem_orthogonal v
  have h1 : ⟪b,op U a p⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).mp hbmem _ (op_mem U a hp)
  have h2 : ⟪p,op U a b⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp (op_orthogonal U a hbmem) _ hp
  have he : v = p+b := by dsimp [b]; abel
  change ⟪p,op U a p⟫_ℂ = ⟪v,op U a v⟫_ℂ
  rw [he,map_add,inner_add_left,inner_add_right,inner_add_right,h1,h2]
  change _ = _ + 0 + (0 + ⟪b,op U a b⟫_ℂ)
  rw [hb]; simp
end EuclideanFiveColor.ContinuousVectors
end
noncomputable section
open Filter Topology
open scoped InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor.ContinuousVectors
variable [Carrier]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H))
lemma orbit_uniformContinuous {v : H} (hv : v ∈ space (A := E) U) : UniformContinuous (fun a : E => op U a v) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,h⟩ := Metric.continuousAt_iff.mp (orbit_continuous U hv).continuousAt ε hε
  refine ⟨δ,hδ,fun a b hab => ?_⟩
  have ht : dist (op U (a-b) v) v < ε := by
    have hh := h (show dist (a-b) 0 < δ by simpa only [dist_zero_right,dist_eq_norm,sub_zero] using hab)
    simpa only [op_zero (A := E) U] using hh
  calc
    _ = dist (op U b (op U (a-b) v)) (op U b v) := by
      rw [← op_add (A := E) U]
      congr 2
      abel_nf
    _ = dist (op U (a-b) v) v := dist_op U b _ _
    _ < ε := ht
private def orbitExtension (v : H) : ℂ → H := dense_E.extend (fun a : E => op U a v)
lemma orbitExtension_continuous {v : H} (hv : v ∈ space (A := E) U) : Continuous (orbitExtension U v) :=
  (dense_E.uniformContinuous_extend (orbit_uniformContinuous U hv)).continuous
lemma orbitExtension_eq {v : H} (hv : v ∈ space (A := E) U) (a : E) : orbitExtension U v (a : ℂ) = op U a v :=
  dense_E.extend_eq (orbit_continuous U hv) a
lemma orbitExtension_inner {v w : H} (hv : v ∈ space (A := E) U) (hw : w ∈ space (A := E) U) (x y : ℂ) :
    ⟪orbitExtension U v x,orbitExtension U w (x+y)⟫_ℂ = ⟪v,orbitExtension U w y⟫_ℂ := by
  have hc := orbitExtension_continuous U hv
  have hd := orbitExtension_continuous U hw
  refine dense_E.denseRange_val.induction_on₂
    (p := fun x y : ℂ => ⟪orbitExtension U v x,orbitExtension U w (x+y)⟫_ℂ = ⟪v,orbitExtension U w y⟫_ℂ) ?_ ?_ x y
  · exact isClosed_eq ((hc.comp continuous_fst).inner (hd.comp (continuous_fst.add continuous_snd)))
      (continuous_const.inner (hd.comp continuous_snd))
  · intro a b
    change ⟪orbitExtension U v (a : ℂ),orbitExtension U w ((a+b : E) : ℂ)⟫_ℂ = _
    rw [orbitExtension_eq U hv,orbitExtension_eq U hw,orbitExtension_eq U hw,op_add (A := E) U]
    exact Unitary.inner_map_map (U (Multiplicative.ofAdd a)) v (op U b w)
end PlaneFiveColor.Spectral
end
end ParishLaw
end

noncomputable section
namespace OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1
open MeasureTheory
open scoped InnerProductSpace
open ParishLaw ParishLaw.PlaneFiveColor.Spectral ParishLaw.EuclideanFiveColor

/-- Wild finite rotationally invariant measures have vanishing nontrivial Fourier coefficients. -/
def H1 : Prop := ∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,
    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),
    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),
    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ))),
    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩

    ∀ (μ : Measure D) [IsFiniteMeasure μ], IsWild μ → ∀ a : E, a ≠ 0 → ∫ d, (eval a d : ℂ) ∂μ = 0

/-- The spectral measure of a vector orthogonal to the continuous vectors gives the ordinary characters zero mass. -/
def H2 : Prop := ∀ (E : IntermediateField ℚ ℂ) (F : IntermediateField ℚ ℝ), ∀ hc : Countable E,
    ∀ hF : (∀ z : ℂ, z ∈ E ↔ z.re ∈ F ∧ z.im ∈ F),
    ∀ ha : (∀ p : Polynomial ℂ, p ≠ 0 → (∀ n, p.coeff n ∈ E) → ∀ z, p.eval z = 0 → z ∈ E),
    ∀ ht : (∀ Q : Finset ℂ, (∀ q ∈ Q, q ∈ E ∧ ‖q‖ = 1) →
      ∃ S : Finset ℂ, (∀ s ∈ S, s ∈ E ∧ ‖s‖ = 1) ∧
      ∀ j : ℂ → ℂ, (∀ s ∈ S, j s ∈ Q) →
        (1 : ℂ) ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ)) ∧
        Complex.I ∈ Submodule.span ℚ ((fun s => j s*s) '' (S : Set ℂ))),
    letI : Carrier := ⟨E,F,hc,hF,ha,ht⟩

    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (U : DiscreteE →* unitary (H →L[ℂ] H)) (v : H), v ∈ (ContinuousVectors.space U)ᗮ →
      VectorMeasure.measure (CommutingSpectral.calculus U) v (C : Set D) = 0
end OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1
end
-- OAI.Analysis.PlaneSpectrum.Ergodicity
section
namespace ParishLaw

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
namespace PlaneFiveColor.Spectral
open EuclideanFiveColor EuclideanFiveColor.VectorMeasure EuclideanFiveColor.CommutingSpectral
variable [car : Carrier]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : DiscreteE →* unitary (H →L[ℂ] H)) (W : K → unitary (H →L[ℂ] H))
  (hcov : ∀ k z w, (W k : H →L[ℂ] H) (ContinuousVectors.op U z w) =
    ContinuousVectors.op U ((kCoeff k)*z) ((W k : H →L[ℂ] H) w))
include hcov
private lemma residual_fourier (wild : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1.H1) (orth : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1.H2) (v : H) (hv : v ∈ (ContinuousVectors.space U)ᗮ)
    (hfix : ∀ k, (W k : H →L[ℂ] H) v = v) (z : E) (hz : z ≠ 0) :
    ⟪v,ContinuousVectors.op U z v⟫_ℂ = 0 := by
  have hw : IsWild (measure (calculus U) v) :=
    ⟨vectorMeasure_invariant U W hcov v hfix,orth car.E car.F car.countable car.mem_iff car.algClosed car.template H U v hv⟩
  have hh := wild car.E car.F car.countable car.mem_iff car.algClosed car.template (measure (calculus U) v) hw z hz
  have hc := integral_complex (calculus U) v (evaluation (G := DiscreteE) (Multiplicative.ofAdd z))
  rw [calculus_evaluation U (Multiplicative.ofAdd z : DiscreteE)] at hc
  exact hc.symm.trans hh
end PlaneFiveColor.Spectral
end

end ParishLaw
end
section
noncomputable section

namespace ParishPlane.Transfer

open MeasureTheory Filter
open ParishLaw ParishLaw.PlaneFiveColor.Spectral ParishLaw.EuclideanFiveColor ParishLaw.EuclideanFiveColor.ContinuousVectors
open scoped InnerProductSpace NNReal

variable [Carrier]
/-- The contraction of `ℂ` onto the real interval `[-1, 1]`. -/
private def clampSign (z : ℂ) : ℂ := (max (-1) (min 1 z.re) : ℝ)

omit [Carrier] in
/-- The clamp is `1`-Lipschitz. -/
lemma lipschitzWith_clampSign : LipschitzWith 1 clampSign := by
  have hr : LipschitzWith 1 (fun z : ℂ => z.re) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs,
      ← Complex.sub_re] using Complex.abs_re_le_norm (a - b)
  change LipschitzWith 1 (fun z : ℂ => ((max (-1) (min 1 z.re) : ℝ) : ℂ))
  simpa only [one_mul, Function.comp_def] using
    Complex.isometry_ofReal.lipschitz.comp ((hr.const_min 1).const_max (-1))

omit [Carrier] in
/-- The clamp fixes `0`. -/
@[simp] lemma clampSign_zero : clampSign 0 = 0 := by simp [clampSign]

omit [Carrier] in
/-- The clamp is real with values in `[-1, 1]`. -/
lemma clampSign_range (z : ℂ) :
    (clampSign z).im = 0 ∧ -1 ≤ (clampSign z).re ∧ (clampSign z).re ≤ 1 := by
  change (0 : ℝ) = 0 ∧ -1 ≤ max (-1) (min 1 z.re) ∧ max (-1) (min 1 z.re) ≤ 1
  exact ⟨rfl, le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

omit [Carrier] in
/-- The clamp fixes real numbers in `[-1, 1]`. -/
lemma clampSign_eq {z : ℂ} (hz : z.im = 0 ∧ -1 ≤ z.re ∧ z.re ≤ 1) : clampSign z = z := by
  rw [clampSign, min_eq_right hz.2.2, max_eq_right hz.2.1]
  exact Complex.ext (by simp) (by simpa using hz.1.symm)

/-! ### The projected sign and its field -/

variable (R : Set E) (ω₀ : Space R)

/-- The continuous vectors form a complete subspace. -/
private instance continuous_complete : CompleteSpace (space (A := E) (representation R ω₀)) :=
  (isClosed_space (A := E) (representation R ω₀)).completeSpace_coe

/-- The projection of the sign onto the continuous vectors. -/
private def projected : Hilbert R ω₀ :=
  (space (A := E) (representation R ω₀)).starProjection (signVector R ω₀)

/-- The projected sign is continuous under translation. -/
lemma projected_mem : projected R ω₀ ∈ space (A := E) (representation R ω₀) :=
  (space (A := E) (representation R ω₀)).starProjection_apply_mem _

/-- The sign vector is real with values in `[-1, 1]`. -/
lemma sign_range : ∀ᵐ η ∂measure R ω₀,
    (signVector R ω₀ η).im = 0 ∧ -1 ≤ (signVector R ω₀ η).re ∧ (signVector R ω₀ η).re ≤ 1 := by
  filter_upwards [sign_ae R ω₀] with η h
  rw [h]
  simp only [Complex.ofReal_im, Complex.ofReal_re, sgnAt]
  split_ifs <;> norm_num

/-- `clampSign` acting on `L²` maps the continuous vectors to themselves. -/
lemma clampSign_mem {v : Hilbert R ω₀} (hv : v ∈ space (A := E) (representation R ω₀)) :
    lipschitzWith_clampSign.compLp clampSign_zero v ∈ space (A := E) (representation R ω₀) :=
  nonlinear_mem (measure R ω₀) (representation R ω₀) (trans R) (trans_preserving R ω₀)
    (op_apply R ω₀) lipschitzWith_clampSign clampSign_zero hv

/-- The projected sign is real with values in `[-1, 1]`, since the projection
commutes with the clamp. -/
lemma projected_range : ∀ᵐ η ∂measure R ω₀,
    (projected R ω₀ η).im = 0 ∧ -1 ≤ (projected R ω₀ η).re ∧ (projected R ω₀ η).re ≤ 1 := by
  have he : lipschitzWith_clampSign.compLp clampSign_zero (signVector R ω₀) = signVector R ω₀ := by
    apply Lp.ext
    filter_upwards [lipschitzWith_clampSign.coeFn_compLp clampSign_zero (signVector R ω₀),
      sign_range R ω₀] with η hη h
    exact hη.trans (clampSign_eq h)
  have hp := projection_fixed_of_contraction (space (A := E) (representation R ω₀))
    (lipschitzWith_clampSign.compLp clampSign_zero)
    (lipschitzWith_clampSign.lipschitzWith_compLp clampSign_zero)
    (fun v hv => clampSign_mem R ω₀ hv) _ he
  have hae := lipschitzWith_clampSign.coeFn_compLp clampSign_zero (projected R ω₀)
  rw [projected, hp] at hae
  filter_upwards [hae] with η hη
  exact hη.symm ▸ clampSign_range _

/-- The projected sign is fixed by the rotations. -/
lemma projected_rotation_fixed (b : K) :
    (rotation R ω₀ b : Hilbert R ω₀ →L[ℂ] Hilbert R ω₀) (projected R ω₀) = projected R ω₀ :=
  projection_covariance_fixed (representation R ω₀) (rotation R ω₀ b)
    (Homeomorph.mulLeft₀ (kCoeff b) (kCoeff_ne_zero b)) (mul_zero _)
    (rotation_covariance R ω₀ b) _ (rotation_signVector R ω₀ b)

/-- Rigidity: away from zero, the projected sign has the sign's correlations. -/
lemma projected_corr (wild : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1.H1) (orth : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1.H2) (z : E) (hz : z ≠ 0) :
    ⟪projected R ω₀, op (representation R ω₀) z (projected R ω₀)⟫_ℂ = (corr R ω₀ z : ℂ) := by
  have hb := residual_fourier (representation R ω₀) (rotation R ω₀) (rotation_covariance R ω₀) wild orth
    (signVector R ω₀ - projected R ω₀)
    ((space (A := E) (representation R ω₀)).sub_starProjection_mem_orthogonal (signVector R ω₀))
    (fun b => by rw [map_sub, rotation_signVector, projected_rotation_fixed]) z hz
  exact (projection_coefficient (representation R ω₀) (signVector R ω₀) z hb).trans
    (inner_signVector R ω₀ z)

/-- The continuous extension `G(y)` of the orbit of the projected sign. -/
private def field (y : ℂ) : Hilbert R ω₀ := orbitExtension (representation R ω₀) (projected R ω₀) y

/-- The field is continuous. -/
lemma continuous_field : Continuous (field R ω₀) :=
  orbitExtension_continuous _ (projected_mem R ω₀)

/-- On `E` the field is the orbit of the projected sign. -/
lemma field_eq (a : E) : field R ω₀ (a : ℂ) = op (representation R ω₀) a (projected R ω₀) :=
  orbitExtension_eq _ (projected_mem R ω₀) a

/-- The correlations of the field are translation invariant. -/
lemma field_inner (y w : ℂ) :
    ⟪field R ω₀ y, field R ω₀ (y + w)⟫_ℂ = ⟪projected R ω₀, field R ω₀ w⟫_ℂ :=
  orbitExtension_inner _ (projected_mem R ω₀) (projected_mem R ω₀) y w

/-- The field is real with values in `[-1, 1]`. -/
lemma field_range (y : ℂ) : ∀ᵐ η ∂measure R ω₀,
    (field R ω₀ y η).im = 0 ∧ -1 ≤ (field R ω₀ y η).re ∧ (field R ω₀ y η).re ≤ 1 := by
  have he : lipschitzWith_clampSign.compLp clampSign_zero (field R ω₀ y) = field R ω₀ y := by
    refine dense_E.denseRange_val.induction_on y (isClosed_eq
      ((lipschitzWith_clampSign.continuous_compLp clampSign_zero).comp (continuous_field R ω₀))
      (continuous_field R ω₀)) ?_
    intro a
    rw [field_eq, op_apply]
    apply Lp.ext
    filter_upwards [lipschitzWith_clampSign.coeFn_compLp clampSign_zero
        (Lp.compMeasurePreserving (trans R a) (trans_preserving R ω₀ a) (projected R ω₀)),
      Lp.coeFn_compMeasurePreserving (projected R ω₀) (trans_preserving R ω₀ a),
      (trans_preserving R ω₀ a).quasiMeasurePreserving.ae (projected_range R ω₀)]
      with η h1 h2 h3
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2]
    exact clampSign_eq h3
  have ha := lipschitzWith_clampSign.coeFn_compLp clampSign_zero (field R ω₀ y)
  rw [he] at ha
  filter_upwards [ha] with η hη
  exact hη.symm ▸ clampSign_range _

/-! ### Vanishing of `Q` on every triangle -/

/-- The sides avoided by a labeling are nonzero. -/
lemma ne_zero_of_mem (ω : Space R) {r : E} (hr : r ∈ R) : r ≠ 0 := by
  rintro rfl
  exact ω.property 0 hr 0 1 (by simp)

/-- `ζ ≠ 1`. -/
lemma ζE_sub_one_ne_zero : ζE - 1 ≠ 0 := by
  intro h
  have h' := congrArg (fun z : E => (z : ℂ)) h
  push_cast at h'
  have hn := norm_ζ_sub_one
  rw [← coe_ζE, h', norm_zero] at hn
  exact zero_ne_one hn

/-- On every triangle of side `r ∈ R`, `1` plus the three field correlations vanishes. -/
lemma triangle_sum (wild : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1.H1) (orth : OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1.H2) {r : E} (hr : r ∈ R) (u : Circle) :
    1 + ⟪projected R ω₀, field R ω₀ (u * r)⟫_ℂ + ⟪projected R ω₀, field R ω₀ (u * (r * ζ))⟫_ℂ +
      ⟪projected R ω₀, field R ω₀ (u * (r * ζ) - u * r)⟫_ℂ = 0 := by
  have hφ : Continuous fun w => ⟪projected R ω₀, field R ω₀ w⟫_ℂ :=
    continuous_const.inner (continuous_field R ω₀)
  refine circle_closed_induction
    (p := fun v => 1 + ⟪projected R ω₀, field R ω₀ (v * r)⟫_ℂ +
      ⟪projected R ω₀, field R ω₀ (v * (r * ζ))⟫_ℂ +
      ⟪projected R ω₀, field R ω₀ (v * (r * ζ) - v * r)⟫_ℂ = 0)
    (isClosed_eq (((continuous_const.add (hφ.comp (continuous_id.mul continuous_const))).add
      (hφ.comp (continuous_id.mul continuous_const))).add
      (hφ.comp ((continuous_id.mul continuous_const).sub (continuous_id.mul continuous_const))))
      continuous_const) (fun b => ?_) u
  have hr0 := ne_zero_of_mem R ω₀ hr
  have e₁ : (b.val : ℂ) * r = ((kCoeff b * r : E) : ℂ) := rfl
  have e₂ : (b.val : ℂ) * (r * ζ) = ((kCoeff b * (r * ζE) : E) : ℂ) := rfl
  have e₃ : (b.val : ℂ) * (r * ζ) - b.val * r =
      ((kCoeff b * (r * ζE) - kCoeff b * r : E) : ℂ) := rfl
  have n₁ : kCoeff b * r ≠ 0 := mul_ne_zero (kCoeff_ne_zero b) hr0
  have n₂ : kCoeff b * (r * ζE) ≠ 0 :=
    mul_ne_zero (kCoeff_ne_zero b) (mul_ne_zero hr0 (by
      intro h
      have h' := congrArg (fun z : E => ‖(z : ℂ)‖) h
      simp [norm_ζ] at h'))
  have n₃ : kCoeff b * (r * ζE) - kCoeff b * r ≠ 0 := by
    rw [show kCoeff b * (r * ζE) - kCoeff b * r = kCoeff b * r * (ζE - 1) by ring]
    exact mul_ne_zero n₁ ζE_sub_one_ne_zero
  rw [e₃, e₁, e₂, field_eq, field_eq, field_eq, projected_corr R ω₀ wild orth _ n₁,
    projected_corr R ω₀ wild orth _ n₂, projected_corr R ω₀ wild orth _ n₃]
  have h := corr_triangle R ω₀ hr b
  have h' : ((1 + corr R ω₀ (kCoeff b * r) + corr R ω₀ (kCoeff b * (r * ζE)) +
      corr R ω₀ (kCoeff b * (r * ζE) - kCoeff b * r) : ℝ) : ℂ) = 0 := by
    rw [add_assoc, add_assoc, ← add_assoc (corr R ω₀ _), h]
    norm_num
  push_cast at h'
  exact h'
end ParishPlane.Transfer
end
end
noncomputable section
namespace OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1
open MeasureTheory
open scoped InnerProductSpace
open ParishLaw.PlaneFiveColor.Spectral ParishPlane.Transfer
theorem main : H1 → H2 → OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro wild orth x hlow hhigh hne c h₁ h₂
  have ex : ∃ (C : ParishSpectral.PlaneFiveColor.Spectral.Carrier), (x:ℂ) ∈ C.E := by
    by_cases ha : IsAlgebraic ℚ x
    · exact ⟨ParishSpectral.PlaneFiveColor.Spectral.algebraicCarrier, ParishSpectral.PlaneFiveColor.Spectral.ofReal_mem_algebraicCarrier ha⟩
    · have h := Parish173.templateProperty_fieldOf (x:=x) ha
      exact ⟨ParishSpectral.PlaneFiveColor.Spectral.carrierOf x h,ParishSpectral.PlaneFiveColor.Spectral.ofReal_mem_carrierOf x h⟩
  obtain ⟨C,hxE⟩ := ex
  letI : Carrier := ⟨C.E,C.F,C.countable,C.mem_iff,C.algClosed,C.template⟩
  let xE : E := ⟨(x : ℂ),hxE⟩
  let R : Set E := {1,xE}
  let ω : Space R := ⟨fun z => c z, by
    intro r hr p u
    rcases hr with he | he
    · subst r
      exact h₁ p u.val (Circle.norm_coe _)
    · change r = xE at he
      subst r
      exact h₂ p u.val (Circle.norm_coe _)⟩
  refine ⟨Space R, inferInstance, measure R ω, inferInstance, field R ω, continuous_field R ω, field_range R ω, ?_⟩
  intro r hr p u
  have aux (a : E) (ha : a ∈ R) :
      (1 + inner ℂ (field R ω p) (field R ω (p + u * a)) +
        inner ℂ (field R ω p) (field R ω (p + u * (a * ParishPlane.ζ))) +
        inner ℂ (field R ω (p + u * a)) (field R ω (p + u * (a * ParishPlane.ζ)))).re = 0 := by
    have he : p + (u : ℂ) * (a * ParishPlane.ζ) = (p + u * a) + (u * (a * ParishPlane.ζ) - u * a) := by ring
    rw [field_inner, field_inner, he, field_inner, triangle_sum R ω wild orth ha u, Complex.zero_re]
  rcases hr with rfl | rfl
  · exact aux 1 (Set.mem_insert 1 _)
  · exact aux xE (Set.mem_insert_of_mem _ rfl)
end OMA.R_Erdos173_erdos_173_R1_H2_R1_H2_R1_H1_R1_H1_R1
end
