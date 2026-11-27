import OMAStatements.S_mo_448788

-- ===== Cuntz/CoreAlg =====
/-!
# Algebra of a Cuntz family (blueprint section 1, items A1 to A9)
-/

namespace OMA.S_mo_480222

section CuntzFamily

variable {B : Type*} [CStarAlgebra B] {n : ℕ}

/-- A1: the isometries of a Cuntz family have orthogonal ranges. -/
theorem cuntz_orth (t : Fin n → B) (h1 : ∀ i, star (t i) * t i = 1)
    (h2 : ∑ i, t i * star (t i) = 1) (i j : Fin n) :
    star (t i) * t j = if i = j then 1 else 0 := by
  let _ := CStarAlgebra.spectralOrder B
  have := CStarAlgebra.spectralOrderedRing B
  by_cases hij : i = j
  · subst hij; simp [h1]
  · rw [if_neg hij]
    have key : ∑ j, (star (t i) * t j) * star (star (t i) * t j) = 1 := by
      have : ∑ j, (star (t i) * t j) * star (star (t i) * t j)
          = star (t i) * (∑ j, t j * star (t j)) * t i := by
        simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      rw [this, h2, mul_one, h1]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)] at key
    have hii : (star (t i) * t i) * star (star (t i) * t i) = 1 := by simp [h1]
    rw [hii] at key
    have hz : ∑ x ∈ Finset.univ.erase i, (star (t i) * t x) * star (star (t i) * t x) = 0 := by
      have := congrArg (fun y => y - 1) key
      simpa using this
    have hnn : ∀ x ∈ Finset.univ.erase i, 0 ≤ (star (t i) * t x) * star (star (t i) * t x) :=
      fun x _ => mul_star_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz j
      (Finset.mem_erase.2 ⟨fun h => hij h.symm, Finset.mem_univ j⟩)
    exact (CStarRing.mul_star_self_eq_zero_iff _).1 this

/-- A2: the canonical endomorphism of a Cuntz family. -/
noncomputable def cPhi (t : Fin n → B) (x : B) : B := ∑ i, t i * x * star (t i)

theorem cPhi_zero (t : Fin n → B) : cPhi t 0 = 0 := by simp [cPhi]

theorem cPhi_one (t : Fin n → B) (h2 : ∑ i, t i * star (t i) = 1) : cPhi t 1 = 1 := by
  simp [cPhi, h2]

theorem cPhi_star (t : Fin n → B) (x : B) : star (cPhi t x) = cPhi t (star x) := by
  simp [cPhi, star_sum, mul_assoc]

theorem star_mul_cPhi (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (i : Fin n) (x : B) : star (t i) * cPhi t x = x * star (t i) := by
  unfold cPhi
  rw [Finset.mul_sum]
  have : ∀ j, star (t i) * (t j * x * star (t j)) = if i = j then x * star (t j) else 0 := by
    intro j
    rw [← mul_assoc, ← mul_assoc, ho]
    split_ifs <;> simp
  simp [this]

theorem cPhi_mul_gen (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (i : Fin n) (x : B) : cPhi t x * t i = t i * x := by
  have := congrArg star (star_mul_cPhi t ho i (star x))
  simpa [cPhi_star] using this

theorem cPhi_mul (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (x y : B) : cPhi t x * cPhi t y = cPhi t (x * y) := by
  conv_lhs => rw [cPhi, Finset.sum_mul]
  unfold cPhi
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := star_mul_cPhi t ho i y
  unfold cPhi at h
  rw [mul_assoc (t i * x), h]
  simp [mul_assoc]

theorem cPhi_iter_zero (t : Fin n → B) (k : ℕ) : (cPhi t)^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, cPhi_zero]

theorem cPhi_iter_one (t : Fin n → B) (h2 : ∑ i, t i * star (t i) = 1) (k : ℕ) :
    (cPhi t)^[k] 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, cPhi_one t h2]

theorem cPhi_iter_star (t : Fin n → B) (k : ℕ) (x : B) :
    star ((cPhi t)^[k] x) = (cPhi t)^[k] (star x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', cPhi_star, ih]

theorem cPhi_iter_mul (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (k : ℕ) (x y : B) : (cPhi t)^[k] x * (cPhi t)^[k] y = (cPhi t)^[k] (x * y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      cPhi_mul t ho, ih]

/-- A3: words in the generators. -/
def cW (t : Fin n → B) (μ : List (Fin n)) : B := (μ.map t).prod

@[simp] theorem cW_nil (t : Fin n → B) : cW t [] = 1 := by simp [cW]

@[simp] theorem cW_cons (t : Fin n → B) (i : Fin n) (μ : List (Fin n)) :
    cW t (i :: μ) = t i * cW t μ := by simp [cW]

theorem cW_append (t : Fin n → B) (μ ν : List (Fin n)) :
    cW t (μ ++ ν) = cW t μ * cW t ν := by simp [cW]

theorem cW_star_mul_self (t : Fin n → B) (h1 : ∀ i, star (t i) * t i = 1) (μ : List (Fin n)) :
    star (cW t μ) * cW t μ = 1 := by
  induction μ with
  | nil => simp
  | cons i μ ih =>
    rw [cW_cons, star_mul, mul_assoc, ← mul_assoc (star (t i)), h1, one_mul, ih]

theorem star_cW_mul_iter (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (μ : List (Fin n)) : ∀ (k : ℕ) (x : B), μ.length ≤ k →
      star (cW t μ) * (cPhi t)^[k] x = (cPhi t)^[k - μ.length] x * star (cW t μ) := by
  induction μ with
  | nil => intro k x _; simp
  | cons i μ ih =>
    intro k x hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hk' : μ.length ≤ k' := by simpa using hk
    rw [cW_cons, star_mul, Function.iterate_succ_apply', mul_assoc, star_mul_cPhi t ho,
      ← mul_assoc, ih k' x hk', mul_assoc]
    simp

theorem iter_mul_cW (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (μ : List (Fin n)) (k : ℕ) (x : B) (hk : μ.length ≤ k) :
    (cPhi t)^[k] x * cW t μ = cW t μ * (cPhi t)^[k - μ.length] x := by
  have := congrArg star (star_cW_mul_iter t ho μ k (star x) hk)
  simpa [cPhi_iter_star] using this

theorem star_pow_mul_pow (x : B) (hx : star x * x = 1) (k : ℕ) : star (x ^ k) * x ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, star_mul, mul_assoc, ← mul_assoc (star (x ^ k)), ih, one_mul, hx]

theorem star_pow_mul_iter (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (i : Fin n) (m : ℕ) (x : B) :
    star (t i ^ m) * (cPhi t)^[m] x = x * star (t i ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', star_mul, Function.iterate_succ_apply', mul_assoc, star_mul_cPhi t ho,
      ← mul_assoc, ih, mul_assoc]

/-- A4: the word used to build the compressing isometry. -/
def cG (t : Fin n → B) (i0 i1 : Fin n) (k : ℕ) : B := t i0 ^ k * t i1

theorem cG_star_mul_self (t : Fin n → B) (h1 : ∀ i, star (t i) * t i = 1) (i0 i1 : Fin n) (k : ℕ) :
    star (cG t i0 i1 k) * cG t i0 i1 k = 1 := by
  unfold cG
  rw [star_mul, mul_assoc, ← mul_assoc (star (t i0 ^ k)), star_pow_mul_pow _ (h1 i0), one_mul, h1]

theorem cG_star_mul_iter (t : Fin n → B) (h1 : ∀ i, star (t i) * t i = 1)
    (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (i0 i1 : Fin n) (hne : i0 ≠ i1) (k m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) :
    star (cG t i0 i1 k) * (cPhi t)^[m] (cG t i0 i1 k) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have e1 : star (cG t i0 i1 (m' + 1 + j)) = star (t i1) * star (t i0 ^ j) * star (t i0 ^ (m' + 1)) := by
    unfold cG
    rw [pow_add, star_mul, star_mul, mul_assoc]
  rw [e1, mul_assoc, star_pow_mul_iter t ho]
  have e2 : cG t i0 i1 (m' + 1 + j) = t i0 ^ j * (t i0 * (t i0 ^ m' * t i1)) := by
    unfold cG
    rw [add_comm (m' + 1) j, pow_add, pow_succ']
    simp [mul_assoc]
  rw [e2]
  have e3 : star (t i1) * star (t i0 ^ j) * (t i0 ^ j * (t i0 * (t i0 ^ m' * t i1)) * star (t i0 ^ (m' + 1)))
      = star (t i1) * (star (t i0 ^ j) * t i0 ^ j) * t i0 * (t i0 ^ m' * t i1) * star (t i0 ^ (m' + 1)) := by
    simp [mul_assoc]
  rw [e3, star_pow_mul_pow _ (h1 i0), mul_one, ho, if_neg (Ne.symm hne)]
  simp

theorem iter_cG_orth (t : Fin n → B) (h1 : ∀ i, star (t i) * t i = 1)
    (h2 : ∑ i, t i * star (t i) = 1)
    (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (i0 i1 : Fin n) (hne : i0 ≠ i1) (k a b : ℕ) (ha : a ≤ k) (hb : b ≤ k) :
    star ((cPhi t)^[a] (cG t i0 i1 k)) * (cPhi t)^[b] (cG t i0 i1 k) = if a = b then 1 else 0 := by
  have lt_case : ∀ a b : ℕ, a < b → b ≤ k →
      star ((cPhi t)^[a] (cG t i0 i1 k)) * (cPhi t)^[b] (cG t i0 i1 k) = 0 := by
    intro a b hab hb
    obtain ⟨m, rfl⟩ : ∃ m, b = a + m := ⟨b - a, by omega⟩
    rw [Function.iterate_add_apply, cPhi_iter_star, cPhi_iter_mul t ho,
      cG_star_mul_iter t h1 ho i0 i1 hne k m (by omega) (by omega), cPhi_iter_zero]
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [lt_case a b hab hb, if_neg (by omega)]
  · subst hab
    rw [if_pos rfl, cPhi_iter_star, cPhi_iter_mul t ho, cG_star_mul_self t h1, cPhi_iter_one t h2]
  · have := congrArg star (lt_case b a hab ha)
    rw [star_mul, star_star, star_zero] at this
    rw [this, if_neg (by omega)]

/-- A5: the compression formula. -/
theorem compress_word (t : Fin n → B) (h1 : ∀ i, star (t i) * t i = 1)
    (h2 : ∑ i, t i * star (t i) = 1)
    (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (i0 i1 : Fin n) (hne : i0 ≠ i1) (k : ℕ) (μ ν : List (Fin n))
    (hμ : μ.length ≤ k) (hν : ν.length ≤ k) :
    star ((cPhi t)^[k] (cG t i0 i1 k)) * (cW t μ * star (cW t ν)) * (cPhi t)^[k] (cG t i0 i1 k)
      = if μ.length = ν.length then cW t μ * star (cW t ν) else 0 := by
  have e1 : star ((cPhi t)^[k] (cG t i0 i1 k)) * cW t μ
      = cW t μ * star ((cPhi t)^[k - μ.length] (cG t i0 i1 k)) := by
    have := congrArg star (star_cW_mul_iter t ho μ k (cG t i0 i1 k) hμ)
    simpa using this
  have e2 := star_cW_mul_iter t ho ν k (cG t i0 i1 k) hν
  calc star ((cPhi t)^[k] (cG t i0 i1 k)) * (cW t μ * star (cW t ν)) * (cPhi t)^[k] (cG t i0 i1 k)
      = (star ((cPhi t)^[k] (cG t i0 i1 k)) * cW t μ) *
          (star (cW t ν) * (cPhi t)^[k] (cG t i0 i1 k)) := by simp [mul_assoc]
    _ = cW t μ * (star ((cPhi t)^[k - μ.length] (cG t i0 i1 k)) *
          (cPhi t)^[k - ν.length] (cG t i0 i1 k)) * star (cW t ν) := by
        rw [e1, e2]; simp [mul_assoc]
    _ = if μ.length = ν.length then cW t μ * star (cW t ν) else 0 := by
        rw [iter_cG_orth t h1 h2 ho i0 i1 hne k _ _ (by omega) (by omega)]
        by_cases h : μ.length = ν.length
        · rw [if_pos (by omega), if_pos h, mul_one]
        · rw [if_neg (by omega), if_neg h, mul_zero, zero_mul]

/-- The compressing element is an isometry. -/
theorem compress_isometry (t : Fin n → B) (h1 : ∀ i, star (t i) * t i = 1)
    (h2 : ∑ i, t i * star (t i) = 1)
    (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (i0 i1 : Fin n) (k : ℕ) :
    star ((cPhi t)^[k] (cG t i0 i1 k)) * (cPhi t)^[k] (cG t i0 i1 k) = 1 := by
  rw [cPhi_iter_star, cPhi_iter_mul t ho, cG_star_mul_self t h1, cPhi_iter_one t h2]

/-- A6: products of words, general trichotomy. -/
theorem star_cW_mul_cW (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (μ : List (Fin n)) : ∀ ν : List (Fin n),
      star (cW t μ) * cW t ν = 0 ∨
      (∃ γ : List (Fin n), γ.length + μ.length = ν.length ∧ star (cW t μ) * cW t ν = cW t γ) ∨
      (∃ γ : List (Fin n), γ.length + ν.length = μ.length ∧
        star (cW t μ) * cW t ν = star (cW t γ)) := by
  induction μ with
  | nil => intro ν; exact Or.inr (Or.inl ⟨ν, by simp, by simp⟩)
  | cons i μ ih =>
    intro ν
    cases ν with
    | nil => exact Or.inr (Or.inr ⟨i :: μ, by simp, by simp⟩)
    | cons j ν =>
      have e : star (cW t (i :: μ)) * cW t (j :: ν)
          = if i = j then star (cW t μ) * cW t ν else 0 := by
        rw [cW_cons, cW_cons, star_mul, mul_assoc, ← mul_assoc (star (t i)), ho]
        split_ifs <;> simp
      by_cases hij : i = j
      · rw [e, if_pos hij]
        rcases ih ν with h | ⟨γ, hl, h⟩ | ⟨γ, hl, h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨γ, by simp; omega, h⟩)
        · exact Or.inr (Or.inr ⟨γ, by simp; omega, h⟩)
      · rw [e, if_neg hij]; exact Or.inl rfl

theorem star_cW_mul_cW_of_le (t : Fin n → B)
    (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (μ δ : List (Fin n)) (h : μ.length ≤ δ.length) :
    star (cW t μ) * cW t δ = 0 ∨
      ∃ γ : List (Fin n), γ.length + μ.length = δ.length ∧ star (cW t μ) * cW t δ = cW t γ := by
  rcases star_cW_mul_cW t ho μ δ with h0 | h1 | ⟨γ, hl, hγ⟩
  · exact Or.inl h0
  · exact Or.inr h1
  · have : γ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact Or.inr ⟨[], by simp at hl ⊢; omega, by simpa using hγ⟩

theorem star_cW_mul_cW_of_eq (t : Fin n → B)
    (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (μ δ : List (Fin n)) (h : μ.length = δ.length) :
    star (cW t μ) * cW t δ = 0 ∨ star (cW t μ) * cW t δ = 1 := by
  rcases star_cW_mul_cW_of_le t ho μ δ h.le with h0 | ⟨γ, hl, hγ⟩
  · exact Or.inl h0
  · have : γ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact Or.inr (by simpa using hγ)

end CuntzFamily

end OMA.S_mo_480222

-- ===== Cuntz/CoreSpan =====
/-!
# Span of words, matrix unit systems, scalar entries (blueprint items A7, A8, A9)
-/

namespace OMA.S_mo_480222

section CuntzSpan

variable {B : Type*} [CStarAlgebra B] {n : ℕ}

/-- The words `T(μ) T(ν)*` with both lengths at most `k`. -/
def cS (t : Fin n → B) (k : ℕ) : Set B :=
  {x | ∃ μ ν : List (Fin n), μ.length ≤ k ∧ ν.length ≤ k ∧ x = cW t μ * star (cW t ν)}

/-- The linear span of the words of length at most `k`. -/
noncomputable def cP (t : Fin n → B) (k : ℕ) : Submodule ℂ B := Submodule.span ℂ (cS t k)

theorem cP_mono (t : Fin n → B) {k l : ℕ} (h : k ≤ l) : cP t k ≤ cP t l := by
  apply Submodule.span_mono
  rintro x ⟨μ, ν, hμ, hν, rfl⟩
  exact ⟨μ, ν, hμ.trans h, hν.trans h, rfl⟩

theorem cP_one (t : Fin n → B) : (1 : B) ∈ cP t 0 :=
  Submodule.subset_span ⟨[], [], by simp, by simp, by simp⟩

theorem cP_gen (t : Fin n → B) (i : Fin n) : t i ∈ cP t 1 :=
  Submodule.subset_span ⟨[i], [], by simp, by simp, by simp⟩

theorem cP_star (t : Fin n → B) {k : ℕ} {x : B} (hx : x ∈ cP t k) : star x ∈ cP t k := by
  unfold cP at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨μ, ν, hμ, hν, rfl⟩ := h
    exact Submodule.subset_span ⟨ν, μ, hν, hμ, by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
  | smul a x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

theorem cP_mul_gen (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    {k l : ℕ} (μ ν α β : List (Fin n)) (hμ : μ.length ≤ k) (hν : ν.length ≤ k)
    (hα : α.length ≤ l) (hβ : β.length ≤ l) :
    cW t μ * star (cW t ν) * (cW t α * star (cW t β)) ∈ cP t (k + l) := by
  have e : cW t μ * star (cW t ν) * (cW t α * star (cW t β))
      = cW t μ * (star (cW t ν) * cW t α) * star (cW t β) := by simp [mul_assoc]
  rw [e]
  rcases star_cW_mul_cW t ho ν α with h | ⟨γ, hl, h⟩ | ⟨γ, hl, h⟩
  · rw [h]; simp
  · rw [h, ← cW_append]
    exact Submodule.subset_span ⟨μ ++ γ, β, by simp; omega, by omega, rfl⟩
  · rw [h, mul_assoc, ← star_mul, ← cW_append]
    exact Submodule.subset_span ⟨μ, β ++ γ, by omega, by simp; omega, rfl⟩

theorem cP_mul (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    {k l : ℕ} {x y : B} (hx : x ∈ cP t k) (hy : y ∈ cP t l) : x * y ∈ cP t (k + l) := by
  unfold cP at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨μ, ν, hμ, hν, rfl⟩ := h
    unfold cP at hy
    induction hy using Submodule.span_induction with
    | mem y h =>
      obtain ⟨α, β, hα, hβ, rfl⟩ := h
      exact cP_mul_gen t ho μ ν α β hμ hν hα hβ
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx

/-- A7: the star algebra generated by a Cuntz family is the union of the spans of words. -/
theorem adjoin_subset_cP (t : Fin n → B) (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    {x : B} (hx : x ∈ StarAlgebra.adjoin ℂ (Set.range t)) : ∃ k, x ∈ cP t k := by
  induction hx using StarAlgebra.adjoin_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    exact ⟨1, cP_gen t i⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (cP_one t)
  | add x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    exact ⟨k + l, add_mem (cP_mono t (by omega) hk) (cP_mono t (by omega) hl)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    exact ⟨k + l, cP_mul t ho hk hl⟩
  | star x _ hx =>
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, cP_star t hk⟩

/-- A8: the words of length `k` form a system of matrix units generators. -/
theorem exists_system (t : Fin n → B) (h2 : ∑ i, t i * star (t i) = 1)
    (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0) (k : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (u : ι → B),
      (∀ i j, star (u i) * u j = if i = j then 1 else 0) ∧
      ∑ i, u i * star (u i) = 1 ∧
      ∀ i, ∃ δ : List (Fin n), δ.length = k ∧ u i = cW t δ := by
  induction k with
  | zero =>
    refine ⟨Unit, inferInstance, inferInstance, fun _ => 1, ?_, ?_, ?_⟩
    · intro i j; simp
    · simp
    · intro i; exact ⟨[], rfl, by simp⟩
  | succ k ih =>
    obtain ⟨ι, _, _, u, hu, hs, hw⟩ := ih
    refine ⟨Fin n × ι, inferInstance, inferInstance, fun p => t p.1 * u p.2, ?_, ?_, ?_⟩
    · rintro ⟨i, j⟩ ⟨i', j'⟩
      have e : star (t i * u j) * (t i' * u j') = star (u j) * (star (t i) * t i') * u j' := by
        simp [mul_assoc]
      simp only [e, ho, Prod.mk.injEq]
      by_cases hi : i = i'
      · by_cases hj : j = j'
        · simp [hi, hj, hu]
        · simp [hi, hj, hu]
      · simp [hi]
    · rw [Fintype.sum_prod_type]
      have e : ∀ i : Fin n, ∑ j : ι, t i * u j * star (t i * u j)
          = t i * (∑ j : ι, u j * star (u j)) * star (t i) := by
        intro i
        simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      simp only [e, hs, mul_one, h2]
    · rintro ⟨i, j⟩
      obtain ⟨δ, hδ, hj⟩ := hw j
      exact ⟨i :: δ, by simp [hδ], by simp [hj]⟩

/-- A9: the compression of an element of the span of words of length at most `k` has scalar
entries with respect to the words of length exactly `k`. -/
theorem compress_entry (t : Fin n → B) (h1 : ∀ i, star (t i) * t i = 1)
    (h2 : ∑ i, t i * star (t i) = 1)
    (ho : ∀ i j, star (t i) * t j = if i = j then 1 else 0)
    (i0 i1 : Fin n) (hne : i0 ≠ i1) (k : ℕ) {x : B} (hx : x ∈ cP t k)
    (δ δ' : List (Fin n)) (hδ : δ.length = k) (hδ' : δ'.length = k) :
    ∃ c : ℂ, star (cW t δ) *
      (star ((cPhi t)^[k] (cG t i0 i1 k)) * x * (cPhi t)^[k] (cG t i0 i1 k)) * cW t δ'
        = c • (1 : B) := by
  unfold cP at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨μ, ν, hμ, hν, rfl⟩ := h
    rw [compress_word t h1 h2 ho i0 i1 hne k μ ν hμ hν]
    by_cases hl : μ.length = ν.length
    · rw [if_pos hl]
      have e : star (cW t δ) * (cW t μ * star (cW t ν)) * cW t δ'
          = star (star (cW t μ) * cW t δ) * (star (cW t ν) * cW t δ') := by
        simp [mul_assoc]
      rw [e]
      rcases star_cW_mul_cW_of_le t ho μ δ (by omega) with h | ⟨γ, hγl, h⟩
      · exact ⟨0, by rw [h]; simp⟩
      · rcases star_cW_mul_cW_of_le t ho ν δ' (by omega) with h' | ⟨γ', hγl', h'⟩
        · exact ⟨0, by rw [h']; simp⟩
        · rw [h, h']
          rcases star_cW_mul_cW_of_eq t ho γ γ' (by omega) with h'' | h''
          · exact ⟨0, by rw [h'']; simp⟩
          · exact ⟨1, by rw [h'']; simp⟩
    · rw [if_neg hl]
      exact ⟨0, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hy
    refine ⟨c + c', ?_⟩
    rw [mul_add, add_mul, mul_add, add_mul, hc, hc', add_smul]
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    refine ⟨a * c, ?_⟩
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, hc, smul_smul]

end CuntzSpan

end OMA.S_mo_480222

-- ===== Cuntz/CoreSpec =====
/-!
# A finite-dimensional spectral lemma inside a C⋆-algebra

Given a finite family of isometries with orthogonal ranges summing to one, and a positive element
whose compressions by the family are all scalars, some unit linear combination of the family
compresses the positive element to a scalar which dominates its norm.
-/

namespace OMA.S_mo_480222

open scoped ComplexConjugate

section core

variable {B : Type*} [CStarAlgebra B] {ι : Type*} [Fintype ι]

/-- Inserting the resolution of the identity on the left. -/
theorem mul_u_eq_sum (u : ι → B) (hsum : ∑ i, u i * star (u i) = 1) (Q : B) (c : ι → ι → ℂ)
    (hc : ∀ i j, star (u i) * Q * u j = c i j • (1 : B)) (i : ι) :
    Q * u i = ∑ k, c k i • u k := by
  calc Q * u i = (∑ k, u k * star (u k)) * (Q * u i) := by rw [hsum, one_mul]
    _ = ∑ k, c k i • u k := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, ← mul_assoc (star (u k)), hc, mul_smul_comm, mul_one]

/-- A nonnegative real multiple of one has a nonnegative coefficient. -/
theorem nonneg_of_smul_one_nonneg [Nontrivial B] [PartialOrder B] [StarOrderedRing B] (r : ℝ)
    (h : 0 ≤ (r : ℂ) • (1 : B)) : 0 ≤ r := by
  by_contra hr
  rw [not_le] at hr
  rw [Complex.coe_smul] at h
  have h1 : (0 : B) ≤ (-r) • (1 : B) :=
    smul_nonneg (by linarith) (by simp)
  rw [neg_smul] at h1
  have h2 : r • (1 : B) = 0 := le_antisymm (neg_nonneg.1 h1) h
  rcases smul_eq_zero.1 h2 with h3 | h3
  · linarith
  · exact one_ne_zero h3

/-- The algebraic core: the statement with an abstract unitary diagonalisation as input. -/
theorem core_compress [DecidableEq ι] [Nontrivial B] (u : ι → B)
    (hu : ∀ i j, star (u i) * u j = if i = j then 1 else 0)
    (hsum : ∑ i, u i * star (u i) = 1) (a : B) (c : ι → ι → ℂ)
    (hc : ∀ i j, star (u i) * (star a * a) * u j = c i j • (1 : B))
    (U : ι → ι → ℂ) (d : ι → ℝ)
    (hU1 : ∀ j k, ∑ i, conj (U i j) * U i k = if j = k then 1 else 0)
    (hU2 : ∀ i k, ∑ j, U i j * conj (U k j) = if i = k then 1 else 0)
    (hCU : ∀ i j, ∑ k, c i k * U k j = (d j : ℂ) * U i j) :
    ∃ (ξ : ι → ℂ) (d : ℝ), star (∑ i, ξ i • u i) * (∑ i, ξ i • u i) = 1 ∧
      star (∑ i, ξ i • u i) * (star a * a) * (∑ i, ξ i • u i) = (d : ℂ) • (1 : B) ∧
      ‖star a * a‖ ≤ d := by
  obtain ⟨v, hv⟩ : ∃ v : ι → B, ∀ j, v j = ∑ i, U i j • u i := ⟨_, fun _ => rfl⟩
  have hsv : ∀ i k, star (u i) * v k = U i k • (1 : B) := by
    intro i k
    simp [hv, Finset.mul_sum, hu]
  have hstar : ∀ j, star (v j) = ∑ i, conj (U i j) • star (u i) := by
    intro j
    simp [hv, star_sum, star_smul]
  have h1 : ∀ j k, star (v j) * v k = if j = k then 1 else 0 := by
    intro j k
    rw [hstar, Finset.sum_mul]
    simp_rw [smul_mul_assoc, hsv, smul_smul]
    rw [← Finset.sum_smul, hU1]
    split_ifs <;> simp
  have h2 : ∑ j, v j * star (v j) = 1 := by
    have key : ∀ j, v j * star (v j) = ∑ i, ∑ k, (U i j * conj (U k j)) • (u i * star (u k)) := by
      intro j
      rw [hstar, hv]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
      exact Finset.sum_comm
    simp_rw [key]
    rw [Finset.sum_comm]
    have key2 : ∀ i, ∑ j, ∑ k, (U i j * conj (U k j)) • (u i * star (u k)) =
        u i * star (u i) := by
      intro i
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hU2]
      simp
    simp_rw [key2]
    exact hsum
  have h3 : ∀ j, (star a * a) * v j = (d j : ℂ) • v j := by
    intro j
    rw [hv, Finset.mul_sum, Finset.smul_sum]
    simp_rw [mul_smul_comm, mul_u_eq_sum u hsum (star a * a) c hc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, ← hCU]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h4 : ∀ j, star (v j) * (star a * a) * v j = (d j : ℂ) • (1 : B) := by
    intro j
    rw [mul_assoc, h3, mul_smul_comm, h1, if_pos rfl]
  have h5 : ∑ j, (d j : ℂ) • (v j * star (v j)) = star a * a := by
    calc ∑ j, (d j : ℂ) • (v j * star (v j))
        = ∑ j, (star a * a) * (v j * star (v j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_assoc, h3, smul_mul_assoc]
      _ = star a * a := by rw [← Finset.mul_sum, h2, mul_one]
  have hne : Nonempty ι := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    rw [Finset.sum_of_isEmpty] at hsum
    exact zero_ne_one hsum
  obtain ⟨j0, hj0⟩ := Finite.exists_max d
  let _ : PartialOrder B := CStarAlgebra.spectralOrder B
  have _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hd0 : 0 ≤ d j0 := by
    refine nonneg_of_smul_one_nonneg (B := B) (d j0) ?_
    rw [← h4 j0]
    have hp := star_mul_self_nonneg (a * v j0)
    rwa [star_mul, mul_assoc, ← mul_assoc (star a), ← mul_assoc] at hp
  have hle : star a * a ≤ algebraMap ℝ B (d j0) := by
    rw [← sub_nonneg]
    have hdiff : algebraMap ℝ B (d j0) - star a * a =
        ∑ j, (d j0 - d j) • (v j * star (v j)) := by
      rw [Algebra.algebraMap_eq_smul_one, ← h5, ← h2, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sub_smul, Complex.coe_smul]
    rw [hdiff]
    exact Finset.sum_nonneg fun j _ => smul_nonneg (sub_nonneg.2 (hj0 j)) (mul_star_self_nonneg _)
  refine ⟨fun i => U i j0, d j0, ?_, ?_, ?_⟩
  · rw [← hv j0, h1, if_pos rfl]
  · rw [← hv j0, h4]
  · exact (CStarAlgebra.norm_le_iff_le_algebraMap _ hd0 (star_mul_self_nonneg a)).2 hle

end core

theorem exists_isometry_compress {B : Type*} [CStarAlgebra B] [Nontrivial B] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → B) (hu : ∀ i j, star (u i) * u j = if i = j then 1 else 0)
    (hsum : ∑ i, u i * star (u i) = 1) (a : B) (c : ι → ι → ℂ)
    (hc : ∀ i j, star (u i) * (star a * a) * u j = c i j • (1 : B)) :
    ∃ (ξ : ι → ℂ) (d : ℝ), star (∑ i, ξ i • u i) * (∑ i, ξ i • u i) = 1 ∧
      star (∑ i, ξ i • u i) * (star a * a) * (∑ i, ξ i • u i) = (d : ℂ) • (1 : B) ∧
      ‖star a * a‖ ≤ d := by
  have hherm : ∀ i j, star (c j i) = c i j := by
    intro i j
    have h := congrArg star (hc j i)
    rw [star_mul, star_mul, star_star, star_mul, star_star, star_smul, star_one, ← mul_assoc,
      hc i j] at h
    exact (smul_left_injective ℂ (one_ne_zero (α := B)) h).symm
  have hC : (Matrix.of c).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, hherm]
  refine core_compress u hu hsum a c hc (fun i j => hC.eigenvectorUnitary i j) hC.eigenvalues
    ?_ ?_ ?_
  · intro j k
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hC.eigenvectorUnitary.2) j) k
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
  · intro i k
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hC.eigenvectorUnitary.2) i) k
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
  · intro i j
    have h := congrFun (hC.mulVec_eigenvectorBasis j) i
    simpa [Matrix.mulVec, dotProduct] using h

end OMA.S_mo_480222

-- ===== Cuntz/CoreInt =====
/-!
# mo-480222: faithfulness of the integral on positive C*-algebra valued functions

If a continuous function from the reals to a C*-algebra is pointwise positive and its integral
over the unit interval vanishes, then the function vanishes on the unit interval.
Also: the integral of a nonzero integer power of the circle character vanishes.
-/

namespace OMA.S_mo_480222

open MeasureTheory Set Filter Topology

/-- Step 1: the integral of a pointwise positive continuous function over an ordered interval is
positive. -/
theorem integral_pos_nonneg {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (c : ℝ → A) (hpos : ∀ θ, 0 ≤ c θ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ ∫ θ in a..b, c θ := by
  rw [intervalIntegral.integral_of_le hab]
  exact MeasureTheory.integral_nonneg (fun θ => hpos θ)

/-- Step 2: the integral up to any point of the unit interval vanishes. -/
theorem integral_pos_upto_eq_zero {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (c : ℝ → A) (hc : Continuous c)
    (hpos : ∀ θ, 0 ≤ c θ) (h0 : ∫ θ in (0:ℝ)..1, c θ = 0) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 1) :
    ∫ θ in (0:ℝ)..u, c θ = 0 := by
  have h1 : 0 ≤ ∫ θ in (0:ℝ)..u, c θ := integral_pos_nonneg c hpos hu.1
  have h2 : 0 ≤ ∫ θ in u..(1:ℝ), c θ := integral_pos_nonneg c hpos hu.2
  have h3 : (∫ θ in (0:ℝ)..u, c θ) + ∫ θ in u..(1:ℝ), c θ = ∫ θ in (0:ℝ)..1, c θ :=
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
  rw [h0] at h3
  have h4 : ∫ θ in (0:ℝ)..u, c θ = -∫ θ in u..(1:ℝ), c θ := eq_neg_of_add_eq_zero_left h3
  refine le_antisymm ?_ h1
  rw [h4]
  exact neg_nonpos.2 h2

/-- Faithfulness of the integral on pointwise positive continuous functions with values in a
C*-algebra (with its C*-order). -/
theorem integral_pos_faithful {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (c : ℝ → A) (hc : Continuous c)
    (hpos : ∀ θ, 0 ≤ c θ) (h0 : ∫ θ in (0:ℝ)..1, c θ = 0) :
    ∀ θ ∈ Set.Icc (0:ℝ) 1, c θ = 0 := by
  have hIoo : ∀ u ∈ Set.Ioo (0:ℝ) 1, c u = 0 := by
    intro u hu
    have hd : HasDerivAt (fun v => ∫ θ in (0:ℝ)..v, c θ) (c u) u :=
      (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
    have hev : (fun _ : ℝ => (0 : A)) =ᶠ[𝓝 u] (fun v => ∫ θ in (0:ℝ)..v, c θ) := by
      filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
      exact (integral_pos_upto_eq_zero c hc hpos h0 (Set.Ioo_subset_Icc_self hv)).symm
    have hd0 : HasDerivAt (fun _ : ℝ => (0 : A)) (c u) u := hd.congr_of_eventuallyEq hev
    exact hd0.unique (hasDerivAt_const u (0 : A))
  intro θ hθ
  have hcl : IsClosed {x : ℝ | c x = 0} := isClosed_eq hc continuous_const
  have hsub : Set.Icc (0:ℝ) 1 ⊆ {x : ℝ | c x = 0} := by
    rw [← closure_Ioo (zero_ne_one' ℝ)]
    exact hcl.closure_subset_iff.2 hIoo
  exact hsub hθ

/-- Order-free version: positivity is expressed by star-squares, as elsewhere in this project. -/
theorem integral_star_mul_self_faithful {A : Type*} [CStarAlgebra A] (c : ℝ → A)
    (hc : Continuous c) (hpos : ∀ θ, ∃ y : A, c θ = star y * y)
    (h0 : ∫ θ in (0:ℝ)..1, c θ = 0) :
    ∀ θ ∈ Set.Icc (0:ℝ) 1, c θ = 0 := by
  let _ := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  refine integral_pos_faithful c hc (fun θ => ?_) h0
  obtain ⟨y, hy⟩ := hpos θ
  rw [hy]
  exact star_mul_self_nonneg y

/-- The integral over a period of a nonzero integer power of the circle character vanishes. -/
theorem integral_exp_int_eq_zero (d : ℤ) (hd : d ≠ 0) :
    ∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * θ) ^ d = 0 := by
  have hne : (d : ℂ) * (2 * Real.pi * Complex.I) ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.2 hd) Complex.two_pi_I_ne_zero
  have hrw : ∀ θ : ℝ, Complex.exp (2 * Real.pi * Complex.I * θ) ^ d
      = Complex.exp ((d : ℂ) * (2 * Real.pi * Complex.I) * θ) := by
    intro θ
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  simp_rw [hrw]
  rw [integral_exp_mul_complex hne]
  simp [Complex.exp_int_mul_two_pi_mul_I]

end OMA.S_mo_480222

-- ===== Cuntz/CoreCfc =====
/-!
Core functional-calculus step: if a conjugate of a positive element is within distance one of
the identity, then some conjugate of it is exactly the identity.

The order on a bare C⋆-algebra is not a global instance in Mathlib, so the main theorem takes
the order as instance arguments, and the corollary for elements of the form star w * w needs no
order at all.
-/

namespace OMA.S_mo_480222

/-- If `c` is positive and `z * c * star z` is within distance one of `1`, then some conjugate
`z' * c * star z'` equals `1`. -/
theorem exists_conj_eq_one {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (c z : A) (hc : 0 ≤ c)
    (h : ‖z * c * star z - 1‖ < 1) : ∃ z' : A, z' * c * star z' = 1 := by
  have ha : 0 ≤ z * c * star z := star_right_conjugate_nonneg hc z
  have hunit : IsUnit (z * c * star z) := by
    have h' : ‖1 - z * c * star z‖ < 1 := by rwa [norm_sub_rev]
    have h2 := isUnit_one_sub_of_norm_lt_one h'
    rwa [sub_sub_cancel] at h2
  have hrr : CFC.sqrt (z * c * star z) * CFC.sqrt (z * c * star z) = z * c * star z :=
    CFC.sqrt_mul_sqrt_self (z * c * star z) ha
  have hrstar : star (CFC.sqrt (z * c * star z)) = CFC.sqrt (z * c * star z) :=
    (CFC.sqrt_nonneg (z * c * star z)).isSelfAdjoint.star_eq
  have hrunit : IsUnit (CFC.sqrt (z * c * star z)) :=
    (CFC.isUnit_sqrt_iff (z * c * star z) ha).mpr hunit
  obtain ⟨u, hu⟩ := hrunit
  generalize CFC.sqrt (z * c * star z) = r at hrr hrstar hu
  have hqr : (↑u⁻¹ : A) * r = 1 := by
    rw [← hu]; exact Units.inv_mul u
  have hrq : r * (↑u⁻¹ : A) = 1 := by
    rw [← hu]; exact Units.mul_inv u
  have hqstar : star (↑u⁻¹ : A) = (↑u⁻¹ : A) := by
    have h1 : star (↑u⁻¹ : A) * r = 1 := by
      have := congrArg star hrq
      rwa [star_mul, hrstar, star_one] at this
    calc star (↑u⁻¹ : A)
        = star (↑u⁻¹ : A) * (r * (↑u⁻¹ : A)) := by rw [hrq, mul_one]
      _ = star (↑u⁻¹ : A) * r * (↑u⁻¹ : A) := (mul_assoc _ _ _).symm
      _ = (↑u⁻¹ : A) := by rw [h1, one_mul]
  refine ⟨(↑u⁻¹ : A) * z, ?_⟩
  calc (↑u⁻¹ : A) * z * c * star ((↑u⁻¹ : A) * z)
      = (↑u⁻¹ : A) * (z * c * star z) * (↑u⁻¹ : A) := by
        rw [star_mul, hqstar]; simp only [mul_assoc]
    _ = (↑u⁻¹ : A) * (r * r) * (↑u⁻¹ : A) := by rw [hrr]
    _ = ((↑u⁻¹ : A) * r) * (r * (↑u⁻¹ : A)) := by simp only [mul_assoc]
    _ = 1 := by rw [hqr, hrq, mul_one]

/-- Order-free form for elements `star w * w`: usable with only `[CStarAlgebra A]` in scope. -/
theorem exists_conj_star_mul_self_eq_one {A : Type*} [CStarAlgebra A] (w z : A)
    (h : ‖z * (star w * w) * star z - 1‖ < 1) : ∃ z' : A, z' * (star w * w) * star z' = 1 := by
  let _ := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  exact exists_conj_eq_one (star w * w) z (star_mul_self_nonneg w) h

end OMA.S_mo_480222

-- ===== Cuntz/CoreCircle =====
/-!
# The circle trick (blueprint section 4) and the key fact (section 5)
-/

namespace OMA.S_mo_480222

section Circle

variable {A : Type*} [CStarAlgebra A] {n : ℕ}

/-- The character `θ ↦ exp(2πiθ)` on the unit interval. -/
noncomputable def cE : C(unitInterval, ℂ) :=
  ⟨fun θ => Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ)), by fun_prop⟩

theorem cE_apply (θ : unitInterval) :
    cE θ = Complex.exp (2 * Real.pi * Complex.I * ((θ : ℝ) : ℂ)) := rfl

theorem exp_star_mul_self (r : ℝ) :
    star (Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))) *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) = 1 := by
  have he : 2 * Real.pi * Complex.I * (r : ℂ) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [he, Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
  simp

theorem cE_star_mul_self (θ : unitInterval) : star (cE θ) * cE θ = 1 :=
  exp_star_mul_self θ

theorem cE_zero : cE (0 : unitInterval) = 1 := by
  simp [cE_apply]

/-- The lifted family `θ ↦ e(θ) s i` in `C(unitInterval, A)`. -/
noncomputable def tB (s : Fin n → A) (i : Fin n) : C(unitInterval, A) :=
  ⟨fun θ => cE θ • s i, by fun_prop⟩

theorem tB_apply (s : Fin n → A) (i : Fin n) (θ : unitInterval) : tB s i θ = cE θ • s i := rfl

theorem tB_iso (s : Fin n → A) (h1 : ∀ i, star (s i) * s i = 1) (i : Fin n) :
    star (tB s i) * tB s i = 1 := by
  ext θ
  simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, tB_apply, ContinuousMap.one_apply,
    star_smul, smul_mul_smul_comm, h1, cE_star_mul_self, one_smul]

theorem tB_sum (s : Fin n → A) (h2 : ∑ i, s i * star (s i) = 1) :
    ∑ i, tB s i * star (tB s i) = 1 := by
  ext θ
  have e : ∀ i, (tB s i * star (tB s i)) θ = s i * star (s i) := by
    intro i
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, tB_apply,
      star_smul, smul_mul_smul_comm]
    rw [mul_comm, cE_star_mul_self, one_smul]
  rw [ContinuousMap.sum_apply]
  simp only [e, h2, ContinuousMap.one_apply]

theorem cW_tB_apply (s : Fin n → A) (μ : List (Fin n)) (θ : unitInterval) :
    cW (tB s) μ θ = cE θ ^ μ.length • cW s μ := by
  induction μ with
  | nil => simp
  | cons i μ ih =>
    rw [cW_cons, cW_cons, ContinuousMap.mul_apply, ih, tB_apply, smul_mul_smul_comm,
      List.length_cons, pow_succ']

/-- The value of a word monomial of the lifted family. -/
theorem word_tB_apply (s : Fin n → A) (μ ν : List (Fin n)) (θ : unitInterval) :
    (cW (tB s) μ * star (cW (tB s) ν)) θ
      = (cE θ ^ μ.length * star (cE θ) ^ ν.length) • (cW s μ * star (cW s ν)) := by
  rw [ContinuousMap.mul_apply, ContinuousMap.star_apply, cW_tB_apply, cW_tB_apply, star_smul,
    smul_mul_smul_comm, star_pow]

/-- Pointwise evaluation maps the span of lifted words into the span of words. -/
theorem eval_mem_cP (s : Fin n → A) {k : ℕ} {g : C(unitInterval, A)} (hg : g ∈ cP (tB s) k)
    (θ : unitInterval) : g θ ∈ cP s k := by
  unfold cP at hg
  induction hg using Submodule.span_induction with
  | mem x h =>
    obtain ⟨μ, ν, hμ, hν, rfl⟩ := h
    rw [word_tB_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, ν, hμ, hν, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [ContinuousMap.add_apply]; exact add_mem hx hy
  | smul a x _ hx => rw [ContinuousMap.smul_apply]; exact Submodule.smul_mem _ _ hx

/-- The integral over the unit interval of a continuous `A`-valued function. -/
noncomputable def cI (g : C(unitInterval, A)) : A :=
  ∫ r in (0:ℝ)..1, g (Set.projIcc (0:ℝ) 1 zero_le_one r)

theorem cI_continuous (g : C(unitInterval, A)) :
    Continuous fun r : ℝ => g (Set.projIcc (0:ℝ) 1 zero_le_one r) :=
  g.continuous.comp continuous_projIcc

theorem cI_add (g h : C(unitInterval, A)) : cI (g + h) = cI g + cI h := by
  unfold cI
  simp only [ContinuousMap.add_apply]
  exact intervalIntegral.integral_add ((cI_continuous g).intervalIntegrable _ _)
    ((cI_continuous h).intervalIntegrable _ _)

theorem cI_sub (g h : C(unitInterval, A)) : cI (g - h) = cI g - cI h := by
  unfold cI
  simp only [ContinuousMap.sub_apply]
  exact intervalIntegral.integral_sub ((cI_continuous g).intervalIntegrable _ _)
    ((cI_continuous h).intervalIntegrable _ _)

theorem cI_smul (a : ℂ) (g : C(unitInterval, A)) : cI (a • g) = a • cI g := by
  unfold cI
  simp only [ContinuousMap.smul_apply]
  exact intervalIntegral.integral_smul a _

theorem norm_cI_le (g : C(unitInterval, A)) : ‖cI g‖ ≤ ‖g‖ := by
  unfold cI
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1) (C := ‖g‖)
    (f := fun r : ℝ => g (Set.projIcc (0:ℝ) 1 zero_le_one r))
    (fun r _ => ContinuousMap.norm_coe_le_norm g _)
  simpa using this

/-- The integral of a word monomial: only degree zero survives. -/
theorem cI_word (s : Fin n → A) (μ ν : List (Fin n)) :
    cI (cW (tB s) μ * star (cW (tB s) ν))
      = if μ.length = ν.length then cW s μ * star (cW s ν) else 0 := by
  unfold cI
  have hcongr : ∫ r in (0:ℝ)..1,
        (cW (tB s) μ * star (cW (tB s) ν)) (Set.projIcc (0:ℝ) 1 zero_le_one r)
      = ∫ r in (0:ℝ)..1, (Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) ^
          ((μ.length : ℤ) - (ν.length : ℤ))) • (cW s μ * star (cW s ν)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [Set.uIcc_of_le zero_le_one] at hr
    have hp : ((Set.projIcc (0:ℝ) 1 zero_le_one r : unitInterval) : ℝ) = r := by
      rw [Set.projIcc_of_mem zero_le_one hr]
    simp only [word_tB_apply, cE_apply, hp]
    congr 1
    have hne : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    have hinv : star (Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)))
        = (Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)))⁻¹ :=
      eq_inv_of_mul_eq_one_left (exp_star_mul_self r)
    rw [hinv, zpow_sub₀ hne, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]
  rw [hcongr, intervalIntegral.integral_smul_const]
  by_cases h : μ.length = ν.length
  · rw [if_pos h, h]
    simp
  · rw [if_neg h, integral_exp_int_eq_zero _ (by omega), zero_smul]

/-- C2: the compression of an element of the span of lifted words is its integral. -/
theorem compress_eq_cI (s : Fin n → A) (h1 : ∀ i, star (s i) * s i = 1)
    (h2 : ∑ i, s i * star (s i) = 1)
    (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (i0 i1 : Fin n) (hne : i0 ≠ i1) (k : ℕ) {g : C(unitInterval, A)} (hg : g ∈ cP (tB s) k)
    (θ : unitInterval) :
    star ((cPhi s)^[k] (cG s i0 i1 k)) * g θ * (cPhi s)^[k] (cG s i0 i1 k) = cI g := by
  unfold cP at hg
  induction hg using Submodule.span_induction with
  | mem x h =>
    obtain ⟨μ, ν, hμ, hν, rfl⟩ := h
    rw [cI_word, word_tB_apply, mul_smul_comm, smul_mul_assoc,
      compress_word s h1 h2 ho i0 i1 hne k μ ν hμ hν]
    by_cases h : μ.length = ν.length
    · rw [if_pos h, h, ← mul_pow, mul_comm, cE_star_mul_self, one_pow, one_smul]
    · rw [if_neg h, smul_zero]
  | zero => simp [cI]
  | add x y _ _ hx hy =>
    rw [ContinuousMap.add_apply, mul_add, add_mul, hx, hy, cI_add]
  | smul a x _ hx =>
    rw [ContinuousMap.smul_apply, mul_smul_comm, smul_mul_assoc, hx, cI_smul]

theorem norm_eq_one_of_star_mul_self [Nontrivial A] (v : A) (hv : star v * v = 1) : ‖v‖ = 1 := by
  have h := CStarRing.norm_star_mul_self (x := v)
  rw [hv, norm_one] at h
  nlinarith [norm_nonneg v]

/-- C3: the main estimate. A nonzero element of the closed star algebra generated by the lifted
family can be compressed, uniformly in the parameter, to something close to `1`. -/
theorem main_estimate [Nontrivial A] (s : Fin n → A) (h1 : ∀ i, star (s i) * s i = 1)
    (h2 : ∑ i, s i * star (s i) = 1) (i0 i1 : Fin n) (hne : i0 ≠ i1)
    (x : C(unitInterval, A))
    (hx : x ∈ (StarAlgebra.adjoin ℂ (Set.range (tB s))).topologicalClosure) (hx0 : x ≠ 0) :
    ∃ z0 : A, ∀ θ : unitInterval, ‖z0 * (star (x θ) * x θ) * star z0 - 1‖ < 1 := by
  have ho := cuntz_orth s h1 h2
  have hoB := cuntz_orth (tB s) (tB_iso s h1) (tB_sum s h2)
  -- the integral of star x * x is nonzero
  have hI : cI (star x * x) ≠ 0 := by
    intro h
    have hz := integral_star_mul_self_faithful
      (fun r : ℝ => (star x * x) (Set.projIcc (0:ℝ) 1 zero_le_one r)) (cI_continuous _)
      (fun r => ⟨x (Set.projIcc (0:ℝ) 1 zero_le_one r), rfl⟩) h
    apply hx0
    ext θ
    have hθ := hz θ θ.2
    rw [Set.projIcc_of_mem zero_le_one θ.2] at hθ
    have hθ' : star (x θ) * x θ = 0 := hθ
    simpa using (CStarRing.star_mul_self_eq_zero_iff (x θ)).1 hθ'
  have hδ0pos : 0 < ‖cI (star x * x)‖ := norm_pos_iff.2 hI
  obtain ⟨δ0, hδ0⟩ : ∃ δ0 : ℝ, δ0 = ‖cI (star x * x)‖ := ⟨_, rfl⟩
  rw [← hδ0] at hδ0pos
  -- approximate x by an element of the algebraic span
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ StarAlgebra.adjoin ℂ (Set.range (tB s)),
      ‖star y * y - star x * x‖ < δ0 / 4 := by
    have hx' : x ∈ closure ((StarAlgebra.adjoin ℂ (Set.range (tB s)) :
        StarSubalgebra ℂ C(unitInterval, A)) : Set C(unitInterval, A)) := by
      rw [← StarSubalgebra.topologicalClosure_coe]; exact hx
    have hcont : Continuous fun y : C(unitInterval, A) => star y * y :=
      continuous_star.mul continuous_id
    have hU : (fun y : C(unitInterval, A) => star y * y) ⁻¹' Metric.ball (star x * x) (δ0 / 4)
        ∈ nhds x :=
      hcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity))
    obtain ⟨y, hyU, hyS⟩ := mem_closure_iff_nhds.1 hx' _ hU
    refine ⟨y, hyS, ?_⟩
    have : dist (star y * y) (star x * x) < δ0 / 4 := hyU
    rwa [dist_eq_norm] at this
  obtain ⟨k, hk⟩ := adjoin_subset_cP (tB s) hoB hy
  have hg : star y * y ∈ cP (tB s) (k + k) := cP_mul (tB s) hoB (cP_star (tB s) hk) hk
  have hWiso := compress_isometry s h1 h2 ho i0 i1 (k + k)
  have hcomp : ∀ θ : unitInterval, star ((cPhi s)^[k + k] (cG s i0 i1 (k + k))) *
      (star y * y) θ * (cPhi s)^[k + k] (cG s i0 i1 (k + k)) = cI (star y * y) :=
    fun θ => compress_eq_cI s h1 h2 ho i0 i1 hne (k + k) hg θ
  have hent : ∀ δ δ' : List (Fin n), δ.length = k + k → δ'.length = k + k →
      ∃ c : ℂ, star (cW s δ) * (star ((cPhi s)^[k + k] (cG s i0 i1 (k + k))) *
        (star y * y) 0 * (cPhi s)^[k + k] (cG s i0 i1 (k + k))) * cW s δ' = c • (1 : A) :=
    fun δ δ' hδ hδ' =>
      compress_entry s h1 h2 ho i0 i1 hne (k + k) (eval_mem_cP s hg 0) δ δ' hδ hδ'
  generalize (cPhi s)^[k + k] (cG s i0 i1 (k + k)) = W at hWiso hcomp hent
  -- lower bound for the norm of the compression
  have hQ : δ0 - δ0 / 4 < ‖cI (star y * y)‖ := by
    have h1' : ‖cI (star y * y) - cI (star x * x)‖ < δ0 / 4 := by
      rw [← cI_sub]; exact (norm_cI_le _).trans_lt hyx
    have h2' : ‖cI (star x * x)‖ ≤ ‖cI (star y * y)‖ + ‖cI (star y * y) - cI (star x * x)‖ := by
      have := norm_sub_le (cI (star y * y)) (cI (star y * y) - cI (star x * x))
      simpa using this
    rw [← hδ0] at h2'
    linarith
  -- the matrix unit system of level k + k
  obtain ⟨ι, _, _, u, hu, hus, huw⟩ := exists_system s h2 ho (k + k)
  have ha : star (y 0 * W) * (y 0 * W) = cI (star y * y) := by
    rw [← hcomp 0]
    simp [mul_assoc]
  have hentry : ∀ i j, ∃ c : ℂ, star (u i) * (star (y 0 * W) * (y 0 * W)) * u j = c • (1 : A) := by
    intro i j
    obtain ⟨δ, hδ, hi⟩ := huw i
    obtain ⟨δ', hδ', hj⟩ := huw j
    rw [ha, ← hcomp 0, hi, hj]
    exact hent δ δ' hδ hδ'
  choose c hc using hentry
  obtain ⟨ξ, d, hV, hVQ, hd⟩ := exists_isometry_compress u hu hus (y 0 * W) c hc
  generalize (∑ i, ξ i • u i) = V at hV hVQ
  rw [ha] at hd hVQ
  have hd0 : 0 < d := by linarith
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Real.sqrt d)⁻¹ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; exact inv_pos.2 hsq
  have hrr : r * r * d = 1 := by
    have := Real.mul_self_sqrt hd0.le
    rw [hr]
    field_simp
    nlinarith
  have hnV : ‖V‖ = 1 := norm_eq_one_of_star_mul_self V hV
  have hnW : ‖W‖ = 1 := norm_eq_one_of_star_mul_self W hWiso
  have hz1 : ∀ m : A, ((r : ℂ) • (star V * star W)) * m * star ((r : ℂ) • (star V * star W))
      = ((r * r : ℝ) : ℂ) • (star V * (star W * m * W) * V) := by
    intro m
    simp only [star_smul, star_mul, star_star, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_assoc, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  have hg1 : ∀ θ : unitInterval, ((r : ℂ) • (star V * star W)) * (star y * y) θ *
      star ((r : ℂ) • (star V * star W)) = 1 := by
    intro θ
    rw [hz1, hcomp θ, hVQ, smul_smul, ← Complex.ofReal_mul, hrr]
    simp
  have hnz : ‖(r : ℂ) • (star V * star W)‖ ≤ r := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    have : ‖star V * star W‖ ≤ 1 := by
      calc ‖star V * star W‖ ≤ ‖star V‖ * ‖star W‖ := norm_mul_le _ _
        _ = 1 := by rw [norm_star, norm_star, hnV, hnW, one_mul]
    nlinarith
  refine ⟨(r : ℂ) • (star V * star W), fun θ => ?_⟩
  have hdiff : ‖(star x * x) θ - (star y * y) θ‖ < δ0 / 4 := by
    have := ContinuousMap.norm_coe_le_norm (star x * x - star y * y) θ
    rw [norm_sub_rev] at hyx
    exact lt_of_le_of_lt this hyx
  have e : (r : ℂ) • (star V * star W) * (star (x θ) * x θ) * star ((r : ℂ) • (star V * star W)) - 1
      = (r : ℂ) • (star V * star W) * ((star x * x) θ - (star y * y) θ) *
        star ((r : ℂ) • (star V * star W)) := by
    rw [mul_sub, sub_mul, hg1 θ]
    rfl
  rw [e]
  calc ‖(r : ℂ) • (star V * star W) * ((star x * x) θ - (star y * y) θ) *
        star ((r : ℂ) • (star V * star W))‖
      ≤ ‖(r : ℂ) • (star V * star W)‖ * ‖(star x * x) θ - (star y * y) θ‖ *
        ‖star ((r : ℂ) • (star V * star W))‖ := norm_mul₃_le
    _ ≤ r * (δ0 / 4) * r := by
        rw [norm_star]
        have hn0 := norm_nonneg ((r : ℂ) • (star V * star W))
        have hm0 := norm_nonneg ((star x * x) θ - (star y * y) θ)
        gcongr
    _ < 1 := by
        have : r * (δ0 / 4) * r = r * r * (δ0 / 4) := by ring
        rw [this, ← hrr]
        have hrr0 : 0 < r * r := mul_pos hr0 hr0
        nlinarith

/-- **Key fact** (Cuntz 1977): a nonzero C⋆-algebra generated by `n > 1` Cuntz isometries is
simple and purely infinite, in the form: every nonzero `w` has `z` with `z (w⋆ w) z⋆ = 1`. -/
theorem key_fact : ∀ (n : ℕ), 1 < n →
    ∀ (A : Type) [CStarAlgebra A] [Nontrivial A] (s : Fin n → A),
      (∀ i, star (s i) * s i = 1) →
      ∑ i, s i * star (s i) = 1 →
      (StarAlgebra.adjoin ℂ (Set.range s)).topologicalClosure = ⊤ →
      ∀ w : A, w ≠ 0 → ∃ z : A, z * (star w * w) * star z = 1 := by
  intro n hn A _ _ s h1 h2 hgen w hw
  obtain ⟨i0, i1, hne⟩ : ∃ i0 i1 : Fin n, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, hn⟩, by simp [Fin.ext_iff]⟩
  obtain ⟨S, hS⟩ : ∃ S : StarSubalgebra ℂ C(unitInterval, A),
      S = (StarAlgebra.adjoin ℂ (Set.range (tB s))).topologicalClosure := ⟨_, rfl⟩
  have hSclosed : IsClosed (S : Set C(unitInterval, A)) := by
    rw [hS]; exact StarSubalgebra.isClosed_topologicalClosure _
  let φ : S →⋆ₐ[ℂ] A :=
    { toFun := fun x => (x : C(unitInterval, A)) 0
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl
      map_star' := fun _ => rfl }
  have hφ : ∀ x : S, φ x = (x : C(unitInterval, A)) 0 := fun x => rfl
  have hmain : ∀ x : S, (x : C(unitInterval, A)) ≠ 0 →
      ∃ z0 : A, ‖z0 * (star (φ x) * φ x) * star z0 - 1‖ < 1 := by
    intro x hx0
    obtain ⟨z0, hz0⟩ := main_estimate s h1 h2 i0 i1 hne (x : C(unitInterval, A))
      (by rw [← hS]; exact x.2) hx0
    exact ⟨z0, hz0 0⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨z0, hz0⟩ := hmain x (fun h => hx0 (Subtype.ext h))
    rw [hx] at hz0
    simp at hz0
  have hiso : Isometry φ := NonUnitalStarAlgHom.isometry φ hinj
  have hcomplete : CompleteSpace S := hSclosed.completeSpace_coe
  have hclosed : IsClosed (Set.range φ) := hiso.isClosedEmbedding.isClosed_range
  have hrange : (StarAlgebra.adjoin ℂ (Set.range s)).topologicalClosure ≤ φ.range := by
    apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      refine ⟨⟨tB s i, ?_⟩, ?_⟩
      · rw [hS]
        exact StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)
      · simp [hφ, tB_apply, cE_zero]
    · exact hclosed
  obtain ⟨x, hxw⟩ : w ∈ φ.range := hrange (by rw [hgen]; trivial)
  have hxw' : φ x = w := hxw
  subst hxw'
  have hx0 : (x : C(unitInterval, A)) ≠ 0 := by
    intro h
    apply hw
    rw [hφ, h]
    rfl
  obtain ⟨z0, hz0⟩ := hmain x hx0
  exact exists_conj_star_mul_self_eq_one (φ x) z0 hz0

end Circle

end OMA.S_mo_480222

-- ===== MO448788/Common =====
/-!
# MO 448788 proof: shared interface between the pieces

`IsStandardGenerators S`: each `S i` acts as the convolution operator of the indicator of the compact open
bisection `Z_i = {(i x, 1, x)}`, that is `S_i δ_β = δ_{(i·β.x, β.k + 1, β.y)}`.
-/

namespace OMA.S_mo_448788

open scoped ENNReal
open Classical

/-- Prepend the letter `i` to a word. -/
def consFn {ι : Type} (i : ι) (w : ℕ → Option ι) : ℕ → Option ι
  | 0 => some i
  | k + 1 => w k

/-- The operators `S i` are the standard Cuntz generators on `ℓ²(G_ι)`. -/
def IsStandardGenerators {ι : Type} (S : ι → (L2 ι →L[ℂ] L2 ι)) : Prop :=
  ∀ (i : ι) (β γ : CuntzGroupoid ι), S i (lp.single 2 β (1 : ℂ)) γ =
    if γ.1.1.1 = consFn i β.1.1.1 ∧ γ.1.2.1 = β.1.2.1 + 1 ∧ γ.1.2.2 = β.1.2.2 then 1 else 0

/-- Simplicity in Cuntz's strong form, for every C⋆-algebra generated by a Cuntz family indexed by `ι`. -/
def CuntzKeyFact (ι : Type) : Prop :=
  ∀ (D : Type) [CStarAlgebra D] [Nontrivial D] (s : ι → D), IsCuntzFamily s →
    (StarAlgebra.adjoin ℂ (Set.range s)).topologicalClosure = ⊤ →
    ∀ w : D, w ≠ 0 → ∃ z : D, z * (star w * w) * star z = 1

end OMA.S_mo_448788

-- ===== MO448788/Bridge =====
namespace OMA.S_mo_448788

open Classical

theorem cuntzKeyFact_fin (n : ℕ) (hn : 1 < n) : CuntzKeyFact (Fin n) := by
  intro D _ _ s hs hgen w hw
  refine OMA.S_mo_480222.key_fact n hn D s (fun i => by simpa using hs.1 i i) ?_ hgen w hw
  have := hs.2 inferInstance
  rwa [finsum_eq_sum_of_fintype] at this

end OMA.S_mo_448788

-- ===== MO448788/Assembly =====
/-!
# MO 448788, piece C: abstract assembly

From the key fact (every nonzero element of a C*-algebra generated by a Cuntz family can be
compressed to the unit) we get the universal property of the reduced algebra, once it holds a
Cuntz family that generates it.
-/

namespace OMA.S_mo_448788

open Classical

namespace AssemblyC

/-- A family that becomes a Cuntz family under an injective star algebra map is a Cuntz family. -/
theorem isCuntzFamily_of_injective {ι : Type} {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [Ring B] [StarRing B] [Algebra ℂ B] (f : A →⋆ₐ[ℂ] B) (hf : Function.Injective f)
    (s : ι → A) (h : IsCuntzFamily (fun i => f (s i))) : IsCuntzFamily s := by
  refine ⟨fun i j => hf ?_, fun hfin => hf ?_⟩
  · have := h.1 i j
    rw [map_mul, map_star, this]
    split_ifs <;> simp
  · have : Fintype ι := Fintype.ofFinite ι
    have := h.2 hfin
    rw [finsum_eq_sum_of_fintype] at this ⊢
    rw [map_sum, map_one]
    simpa [map_mul, map_star] using this

/-- Pairing two Cuntz families gives a Cuntz family in the product. -/
theorem isCuntzFamily_prod {ι : Type} {A B : Type*} [Ring A] [StarRing A] [Ring B] [StarRing B]
    (t : ι → A) (S : ι → B) (ht : IsCuntzFamily t) (hS : IsCuntzFamily S) :
    IsCuntzFamily (fun i => (t i, S i)) := by
  refine ⟨fun i j => ?_, fun hfin => ?_⟩
  · ext
    · simp only [Prod.fst_mul, Prod.fst_star]
      rw [ht.1 i j]
      split_ifs <;> rfl
    · simp only [Prod.snd_mul, Prod.snd_star]
      rw [hS.1 i j]
      split_ifs <;> rfl
  · have : Fintype ι := Fintype.ofFinite ι
    have h1 := ht.2 hfin
    have h2 := hS.2 hfin
    rw [finsum_eq_sum_of_fintype] at h1 h2 ⊢
    ext
    · rw [Prod.fst_sum]; simpa using h1
    · rw [Prod.snd_sum]; simpa using h2

/-- The image of a Cuntz family under a unital star algebra map is a Cuntz family. -/
theorem isCuntzFamily_map {ι : Type} {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [Ring B] [StarRing B] [Algebra ℂ B] (f : A →⋆ₐ[ℂ] B) (s : ι → A) (h : IsCuntzFamily s) :
    IsCuntzFamily (fun i => f (s i)) := by
  refine ⟨fun i j => ?_, fun hfin => ?_⟩
  · rw [← map_star, ← map_mul, h.1 i j]
    split_ifs <;> simp
  · have : Fintype ι := Fintype.ofFinite ι
    have h2 := h.2 hfin
    rw [finsum_eq_sum_of_fintype] at h2 ⊢
    simp_rw [← map_star, ← map_mul]
    rw [← map_sum, h2, map_one]

/-- The heart of the assembly, in an abstract C*-algebra P: a star algebra map into a nontrivial
algebra is injective and has closed image on the closed algebra generated by a Cuntz family. -/
theorem abstract_embed {ι P Q : Type} [CStarAlgebra P] [CStarAlgebra Q] [Nontrivial Q]
    (hK : CuntzKeyFact ι) (u : ι → P) (hu : IsCuntzFamily u) (ψ : P →⋆ₐ[ℂ] Q) :
    (∀ x ∈ (StarAlgebra.adjoin ℂ (Set.range u)).topologicalClosure, ψ x = 0 → x = 0) ∧
    IsClosed (ψ '' ((StarAlgebra.adjoin ℂ (Set.range u)).topologicalClosure : Set P)) := by
  set D : StarSubalgebra ℂ P := (StarAlgebra.adjoin ℂ (Set.range u)).topologicalClosure with hD
  have hDc : IsClosed (D : Set P) := StarSubalgebra.isClosed_topologicalClosure _
  let _ : CStarAlgebra D := StarSubalgebra.cstarAlgebra D (h_closed := hDc)
  have hmem : ∀ i, u i ∈ D := fun i =>
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)
  let s : ι → D := fun i => ⟨u i, hmem i⟩
  have hs : IsCuntzFamily s := isCuntzFamily_of_injective D.subtype Subtype.val_injective s hu
  let π : D →⋆ₐ[ℂ] Q := ψ.comp D.subtype
  have : Nontrivial D := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have := congrArg π h
    rw [map_zero, map_one] at this
    exact zero_ne_one this
  have hgenD : (StarAlgebra.adjoin ℂ (Set.range s)).topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe,
      Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have h1 : StarAlgebra.adjoin ℂ (Set.range u) ≤
        (StarAlgebra.adjoin ℂ (Set.range s)).map D.subtype := by
      rw [StarAlgebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact ⟨s i, StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩, rfl⟩
    have h2 : (x : P) ∈ closure (StarAlgebra.adjoin ℂ (Set.range u) : Set P) := by
      rw [← StarSubalgebra.topologicalClosure_coe]
      exact x.2
    refine closure_mono (fun y hy => ?_) h2
    obtain ⟨z, hz, rfl⟩ := h1 hy
    exact ⟨z, hz, rfl⟩
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    by_contra hw0
    obtain ⟨z, hz⟩ := hK D s hs hgenD w hw0
    have := congrArg π hz
    rw [map_mul, map_mul, map_star, map_mul, map_star, hw, map_one] at this
    simp at this
  refine ⟨fun x hx h0 => ?_, ?_⟩
  · have := hπinj (a₁ := ⟨x, hx⟩) (a₂ := 0) (by rw [map_zero]; exact h0)
    exact congrArg Subtype.val this
  · have hiso : Isometry π := NonUnitalStarAlgHom.isometry π hπinj
    have hcl : IsClosed (Set.range π) := hiso.isClosedEmbedding.isClosed_range
    have he : Set.range π = ψ '' (D : Set P) := by
      ext y
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨d, d.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [← he]
    exact hcl

end AssemblyC

open AssemblyC in
/-- Piece C: the key fact plus a generating Cuntz family in the reduced algebra give the model. -/
theorem model_of_keyFact (ι : Type) (hK : CuntzKeyFact ι) [Nontrivial (reducedAlgebra ι)]
    (S : ι → reducedAlgebra ι) (hS : IsCuntzFamily S)
    (hgen : (StarAlgebra.adjoin ℂ (Set.range fun i => (S i : L2 ι →L[ℂ] L2 ι))).topologicalClosure =
      reducedAlgebra ι) :
    IsGroupoidModel ι := by
  refine ⟨S, hS, hgen, ?_⟩
  intro A _ t ht
  have hS' : IsCuntzFamily (fun i => (S i : L2 ι →L[ℂ] L2 ι)) :=
    isCuntzFamily_map (reducedAlgebra ι).subtype S hS
  have : Nontrivial (L2 ι →L[ℂ] L2 ι) := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne (reducedAlgebra ι)
    exact ⟨⟨x, y, fun h => hxy (Subtype.ext h)⟩⟩
  let u : ι → A × (L2 ι →L[ℂ] L2 ι) := fun i => (t i, (S i : L2 ι →L[ℂ] L2 ι))
  have hu : IsCuntzFamily u := isCuntzFamily_prod t _ ht hS'
  let ψ : A × (L2 ι →L[ℂ] L2 ι) →⋆ₐ[ℂ] (L2 ι →L[ℂ] L2 ι) :=
    StarAlgHom.snd ℂ A (L2 ι →L[ℂ] L2 ι)
  obtain ⟨hinj, hcl⟩ := abstract_embed hK u hu ψ
  set D : StarSubalgebra ℂ (A × (L2 ι →L[ℂ] L2 ι)) :=
    (StarAlgebra.adjoin ℂ (Set.range u)).topologicalClosure with hD
  have hmem : ∀ i, u i ∈ D := fun i =>
    StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)
  -- the image of D lies in the reduced algebra
  have hsub : ∀ x ∈ D, ψ x ∈ reducedAlgebra ι := by
    intro x hx
    have hadj : StarAlgebra.adjoin ℂ (Set.range u) ≤ (reducedAlgebra ι).comap ψ := by
      rw [StarAlgebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact (S i).2
    have hcl2 : IsClosed (((reducedAlgebra ι).comap ψ : StarSubalgebra ℂ _) :
        Set (A × (L2 ι →L[ℂ] L2 ι))) :=
      (StarSubalgebra.isClosed_topologicalClosure _).preimage continuous_snd
    exact StarSubalgebra.topologicalClosure_minimal hadj hcl2 hx
  -- and covers it
  have hsup : reducedAlgebra ι ≤ D.map ψ := by
    rw [← hgen]
    apply StarSubalgebra.topologicalClosure_minimal
    · rw [StarAlgebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact ⟨u i, hmem i, rfl⟩
    · rw [StarSubalgebra.coe_map]
      exact hcl
  let π : D →⋆ₐ[ℂ] reducedAlgebra ι :=
    (ψ.comp D.subtype).codRestrict (reducedAlgebra ι) (fun x => hsub x.1 x.2)
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : ψ x.1 = 0 := congrArg Subtype.val hx
    exact Subtype.ext (hinj x.1 x.2 h0)
  have hπsurj : Function.Surjective π := by
    intro b
    obtain ⟨x, hx, hxb⟩ := hsup b.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxb⟩
  let e : D ≃⋆ₐ[ℂ] reducedAlgebra ι := StarAlgEquiv.ofBijective π ⟨hπinj, hπsurj⟩
  have he : ∀ i, e.symm (S i) = ⟨u i, hmem i⟩ := by
    intro i
    rw [StarAlgEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  refine ⟨((StarAlgHom.fst ℂ A (L2 ι →L[ℂ] L2 ι)).comp D.subtype).comp
    (e.symm : reducedAlgebra ι →⋆ₐ[ℂ] D), fun i => ?_⟩
  show ((e.symm (S i) : D) : A × (L2 ι →L[ℂ] L2 ι)).1 = t i
  rw [he]

/-- The finite case: for n at least 2 the key fact is proved, so a generating Cuntz family in the
reduced algebra is all that is still needed. -/
theorem model_fin (n : ℕ) (hn : 1 < n) [Nontrivial (reducedAlgebra (Fin n))]
    (S : Fin n → reducedAlgebra (Fin n)) (hS : IsCuntzFamily S)
    (hgen : (StarAlgebra.adjoin ℂ
      (Set.range fun i => (S i : L2 (Fin n) →L[ℂ] L2 (Fin n)))).topologicalClosure =
      reducedAlgebra (Fin n)) :
    IsGroupoidModel (Fin n) :=
  model_of_keyFact (Fin n) (cuntzKeyFact_fin n hn) S hS hgen

end OMA.S_mo_448788

-- ===== MO448788/CaseOne =====
/-!
# MO 448788, piece E: the case of one letter

For one letter the groupoid is the integers, the first generator is the bilateral shift, and
the reduced algebra is the algebra of continuous functions on the circle. We show its spectrum is
the whole circle (rotation invariance through a diagonal unitary), and then map out of the
algebra with the continuous functional calculus.
-/

namespace OMA.S_mo_448788

open scoped ENNReal
open Classical

namespace CaseOne

/-- Two operators on the square-summable sequences agreeing on point masses are equal. -/
theorem clm_ext_single {α : Type} (T T' : lp (fun _ : α => ℂ) 2 →L[ℂ] lp (fun _ : α => ℂ) 2)
    (h : ∀ β, T (lp.single 2 β (1 : ℂ)) = T' (lp.single 2 β (1 : ℂ))) : T = T' := by
  ext1 f
  have hs := lp.hasSum_single (E := fun _ : α => ℂ) (p := 2) (by norm_num) f
  have e : ∀ i, lp.single (E := fun _ : α => ℂ) 2 i (f i) =
      f i • lp.single (E := fun _ : α => ℂ) 2 i (1 : ℂ) := by
    intro i
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  have h1 := hs.mapL T
  have h2 := hs.mapL T'
  have hfun : (fun i => T (lp.single 2 i (f i))) = fun i => T' (lp.single 2 i (f i)) := by
    funext i
    rw [e, map_smul, map_smul, h]
  rw [hfun] at h1
  exact h1.unique h2

theorem diag_memℓp {α : Type} (c : α → ℂ) (hc : ∀ i, ‖c i‖ = 1) (f : lp (fun _ : α => ℂ) 2) :
    Memℓp (fun i => c i * f i) 2 := by
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num)] at hf ⊢
  simpa [norm_mul, hc] using hf

/-- Pointwise multiplication by a function of modulus one. -/
noncomputable def diagFun {α : Type} (c : α → ℂ) (hc : ∀ i, ‖c i‖ = 1)
    (f : lp (fun _ : α => ℂ) 2) : lp (fun _ : α => ℂ) 2 :=
  ⟨fun i => c i * f i, diag_memℓp c hc f⟩

theorem diagFun_apply {α : Type} (c : α → ℂ) (hc : ∀ i, ‖c i‖ = 1)
    (f : lp (fun _ : α => ℂ) 2) (i : α) : diagFun c hc f i = c i * f i := rfl

/-- Multiplication by a function of modulus one, as an operator. -/
noncomputable def diagL {α : Type} (c : α → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    lp (fun _ : α => ℂ) 2 →L[ℂ] lp (fun _ : α => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := diagFun c hc
      map_add' := fun f g => by
        ext i
        rw [lp.coeFn_add, Pi.add_apply, diagFun_apply, diagFun_apply, diagFun_apply,
          lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun r f => by
        ext i
        rw [lp.coeFn_smul, Pi.smul_apply, diagFun_apply, diagFun_apply, lp.coeFn_smul,
          Pi.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.id_apply]
        ring }
    1 (fun f => by
      rw [one_mul, lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
      simp [diagFun_apply, hc])

theorem diagL_apply {α : Type} (c : α → ℂ) (hc : ∀ i, ‖c i‖ = 1)
    (f : lp (fun _ : α => ℂ) 2) (i : α) : diagL c hc f i = c i * f i := rfl

theorem diagL_mul {α : Type} (c d : α → ℂ) (hc : ∀ i, ‖c i‖ = 1) (hd : ∀ i, ‖d i‖ = 1)
    (hcd : ∀ i, c i * d i = 1) : diagL c hc * diagL d hd = 1 := by
  ext f i
  show c i * (d i * f i) = f i
  rw [← mul_assoc, hcd, one_mul]

/-- The unit of modulus one, conjugated. -/
theorem mul_star_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : z * star z = 1 := by
  rw [Complex.star_def, Complex.mul_conj', hz]
  simp

theorem star_mul_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : star z * z = 1 := by
  rw [mul_comm]; exact mul_star_of_norm_one hz

/-- The diagonal gauge unitary as a unit of the operator algebra. -/
noncomputable def gaugeUnit {α : Type} (c : α → ℂ) (hc : ∀ i, ‖c i‖ = 1) :
    (lp (fun _ : α => ℂ) 2 →L[ℂ] lp (fun _ : α => ℂ) 2)ˣ where
  val := diagL c hc
  inv := diagL (fun i => star (c i)) (fun i => by rw [norm_star]; exact hc i)
  val_inv := diagL_mul _ _ _ _ (fun i => mul_star_of_norm_one (hc i))
  inv_val := diagL_mul _ _ _ _ (fun i => star_mul_of_norm_one (hc i))

/-- The constant word. -/
def word0 : BoundaryWord (Fin 1) :=
  ⟨fun _ => some 0, ⟨fun _ h => (Option.some_ne_none _ h).elim, fun _ _ => Option.some_ne_none _⟩⟩

/-- The unit arrow at the constant word. -/
def arrow0 : CuntzGroupoid (Fin 1) :=
  ⟨(word0, 0, word0), 0, 0, by simp, fun k hk => absurd hk (Nat.not_lt_zero k),
    fun k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩

theorem nontrivial_L2 : Nontrivial (L2 (Fin 1)) :=
  ⟨⟨lp.single 2 arrow0 (1 : ℂ), 0, fun h => by
    have := congrArg (fun f : L2 (Fin 1) => f arrow0) h
    simp at this⟩⟩

/-- Rotation invariance of the spectrum of the shift. -/
theorem smul_mem_spectrum (a : L2 (Fin 1) →L[ℂ] L2 (Fin 1))
    (ha : ∀ β γ : CuntzGroupoid (Fin 1), a (lp.single 2 β (1 : ℂ)) γ =
      if γ.1.1.1 = consFn 0 β.1.1.1 ∧ γ.1.2.1 = β.1.2.1 + 1 ∧ γ.1.2.2 = β.1.2.2 then 1 else 0)
    {z : ℂ} (hz : ‖z‖ = 1) {μ : ℂ} (hμ : μ ∈ spectrum ℂ a) : z * μ ∈ spectrum ℂ a := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  let c : CuntzGroupoid (Fin 1) → ℂ := fun γ => z ^ γ.1.2.1
  have hc : ∀ γ, ‖c γ‖ = 1 := fun γ => by simp [c, norm_zpow, hz]
  let U := gaugeUnit c hc
  have key : (U : L2 (Fin 1) →L[ℂ] L2 (Fin 1)) * a = (z • a) * (U : L2 (Fin 1) →L[ℂ] L2 (Fin 1)) := by
    apply clm_ext_single
    intro β
    have hU : (U : L2 (Fin 1) →L[ℂ] L2 (Fin 1)) (lp.single 2 β (1 : ℂ)) =
        c β • lp.single 2 β (1 : ℂ) := by
      ext γ
      show c γ * lp.single (E := fun _ : CuntzGroupoid (Fin 1) => ℂ) 2 β (1 : ℂ) γ =
        c β * lp.single (E := fun _ : CuntzGroupoid (Fin 1) => ℂ) 2 β (1 : ℂ) γ
      by_cases h : γ = β
      · rw [h]
      · rw [lp.single_apply_ne _ _ _ h]; simp
    ext γ
    show c γ * a (lp.single 2 β (1 : ℂ)) γ =
      (z • a) ((U : L2 (Fin 1) →L[ℂ] L2 (Fin 1)) (lp.single 2 β (1 : ℂ))) γ
    rw [hU, smul_apply, map_smul, lp.coeFn_smul, lp.coeFn_smul,
      Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ha]
    split_ifs with h
    · simp only [c, h.2.1, mul_one]
      rw [zpow_add_one₀ hz0, mul_comm]
    · simp
  have hconj : (U : L2 (Fin 1) →L[ℂ] L2 (Fin 1)) * a * ((U⁻¹ : _ˣ) : L2 (Fin 1) →L[ℂ] L2 (Fin 1)) =
      z • a := by
    rw [key, mul_assoc, Units.mul_inv, mul_one]
  have hspec : spectrum ℂ (z • a) = spectrum ℂ a := by
    rw [← hconj, spectrum.units_conjugate]
  rw [← hspec]
  have := spectrum.unit_smul_eq_smul (R := ℂ) a (Units.mk0 z hz0)
  rw [Units.smul_def, Units.val_mk0] at this
  rw [this]
  exact Set.smul_mem_smul_set (a := Units.mk0 z hz0) hμ

/-- The spectrum of the shift is the whole circle. -/
theorem sphere_subset_spectrum (a : L2 (Fin 1) →L[ℂ] L2 (Fin 1))
    (ha : ∀ β γ : CuntzGroupoid (Fin 1), a (lp.single 2 β (1 : ℂ)) γ =
      if γ.1.1.1 = consFn 0 β.1.1.1 ∧ γ.1.2.1 = β.1.2.1 + 1 ∧ γ.1.2.2 = β.1.2.2 then 1 else 0)
    (hu : a ∈ unitary (L2 (Fin 1) →L[ℂ] L2 (Fin 1))) :
    Metric.sphere (0 : ℂ) 1 ⊆ spectrum ℂ a := by
  have := nontrivial_L2
  obtain ⟨μ, hμ⟩ := spectrum.nonempty a
  have hμ1 : ‖μ‖ = 1 := by
    simpa using spectrum.subset_circle_of_unitary (𝕜 := ℂ) hu hμ
  have hμ0 : μ ≠ 0 := by
    intro h; rw [h, norm_zero] at hμ1; exact zero_ne_one hμ1
  intro ν hν
  have hν1 : ‖ν‖ = 1 := by simpa using hν
  have hz : ‖ν / μ‖ = 1 := by rw [norm_div, hν1, hμ1, div_one]
  have := smul_mem_spectrum a ha hz hμ
  rwa [div_mul_cancel₀ _ hμ0] at this

end CaseOne

open CaseOne in
theorem model_fin_one (S : Fin 1 → reducedAlgebra (Fin 1))
    (hS : IsStandardGenerators (fun i => (S i : L2 (Fin 1) →L[ℂ] L2 (Fin 1))))
    (hgen : (StarAlgebra.adjoin ℂ (Set.range fun i => (S i : L2 (Fin 1) →L[ℂ] L2 (Fin 1)))).topologicalClosure =
      reducedAlgebra (Fin 1))
    (hcuntz : IsCuntzFamily S) : IsGroupoidModel (Fin 1) := by
  refine ⟨S, hcuntz, hgen, ?_⟩
  intro A _ t ht
  let a : L2 (Fin 1) →L[ℂ] L2 (Fin 1) := (S 0 : L2 (Fin 1) →L[ℂ] L2 (Fin 1))
  have hsa : star a * a = 1 := by
    have := congrArg Subtype.val (hcuntz.1 0 0)
    simpa using this
  have has : a * star a = 1 := by
    have := hcuntz.2 inferInstance
    rw [finsum_unique] at this
    have := congrArg Subtype.val this
    simpa using this
  have hau : a ∈ unitary (L2 (Fin 1) →L[ℂ] L2 (Fin 1)) := Unitary.mem_iff.mpr ⟨hsa, has⟩
  have : IsStarNormal a := ⟨by rw [Commute, SemiconjBy, hsa, has]⟩
  let u : A := t 0
  have hsu : star u * u = 1 := by
    have := ht.1 0 0
    simpa using this
  have hus : u * star u = 1 := by
    have := ht.2 inferInstance
    rwa [finsum_unique] at this
  have huu : u ∈ unitary A := Unitary.mem_iff.mpr ⟨hsu, hus⟩
  have hun : IsStarNormal u := ⟨by rw [Commute, SemiconjBy, hsu, hus]⟩
  have hle : reducedAlgebra (Fin 1) ≤ StarAlgebra.elemental ℂ a := by
    rw [← hgen, Set.range_unique]
    exact le_rfl
  have hsub : spectrum ℂ u ⊆ spectrum ℂ a :=
    (spectrum.subset_circle_of_unitary (𝕜 := ℂ) huu).trans
      (sphere_subset_spectrum a (hS 0) hau)
  let φ : reducedAlgebra (Fin 1) →⋆ₐ[ℂ] A :=
    (cfcHomSuperset hun hsub).comp
      ((continuousFunctionalCalculus a).symm.toStarAlgHom.comp (StarSubalgebra.inclusion hle))
  refine ⟨φ, fun i => ?_⟩
  rw [Subsingleton.elim i 0]
  have h1 : StarSubalgebra.inclusion hle (S 0) =
      continuousFunctionalCalculus a ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) := by
    rw [continuousFunctionalCalculus_map_id]
    rfl
  show cfcHomSuperset hun hsub ((continuousFunctionalCalculus a).symm
    (StarSubalgebra.inclusion hle (S 0))) = u
  rw [h1, StarAlgEquiv.symm_apply_apply]
  exact cfcHomSuperset_id hun hsub

end OMA.S_mo_448788

-- ===== MO448788/KeyFactInf =====
/-!
MO 448788, piece D: Cuntz's theorem for infinitely many letters

Every nontrivial C⋆-algebra generated by isometries `s i` (`i : ℕ`) with `s i⋆ s j = δ i j` satisfies:
every nonzero `w` has `z` with `z (w⋆ w) z⋆ = 1`. Blueprint: BLUEPRINT_INF.md.
-/

namespace OMA.S_mo_448788

namespace KeyInf

open OMA.S_mo_480222

section Alg

variable {A : Type*} [CStarAlgebra A]

/-- The restriction of an infinite family to its first `N` members. -/
def rs (s : ℕ → A) (N : ℕ) : Fin N → A := fun i => s i

theorem rs_orth (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (i j : Fin N) : star (rs s N i) * rs s N j = if i = j then 1 else 0 := by
  show star (s i) * s j = _
  rw [ho]
  by_cases h : i = j
  · rw [if_pos h, if_pos (congrArg Fin.val h)]
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext h'))]

/-- The projection onto the complement of the ranges of the first `N` isometries. -/
noncomputable def cQ (s : ℕ → A) (N : ℕ) : A := 1 - cPhi (rs s N) 1

theorem cQ_star (s : ℕ → A) (N : ℕ) : star (cQ s N) = cQ s N := by
  unfold cQ
  rw [star_sub, star_one, cPhi_star, star_one]

theorem star_gen_mul_cQ (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (i : Fin N) : star (rs s N i) * cQ s N = 0 := by
  unfold cQ
  rw [mul_sub, mul_one, star_mul_cPhi _ (rs_orth s ho N), one_mul, sub_self]

theorem cQ_mul_gen (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (i : Fin N) : cQ s N * rs s N i = 0 := by
  have h := congrArg star (star_gen_mul_cQ s ho N i)
  rw [star_mul, star_star, cQ_star, star_zero] at h
  exact h

theorem cQ_mul_cPhi (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (x : A) : cQ s N * cPhi (rs s N) x = 0 := by
  unfold cPhi
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← mul_assoc, ← mul_assoc, cQ_mul_gen s ho N i, zero_mul, zero_mul]

theorem cQ_mul_cQ (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ) :
    cQ s N * cQ s N = cQ s N := by
  have h := cQ_mul_cPhi s ho N 1
  calc cQ s N * cQ s N = cQ s N * (1 - cPhi (rs s N) 1) := rfl
    _ = cQ s N := by rw [mul_sub, mul_one, h, sub_zero]

theorem cQ_add_sum (s : ℕ → A) (N : ℕ) : cQ s N + ∑ i, rs s N i * star (rs s N i) = 1 := by
  unfold cQ cPhi
  simp

theorem star_gen_mul_out (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (i : Fin N) (m : ℕ) (hm : N ≤ m) : star (rs s N i) * s m = 0 := by
  have hi := i.2
  show star (s i) * s m = 0
  rw [ho, if_neg (by omega)]

theorem star_out_mul_gen (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (i : Fin N) (m : ℕ) (hm : N ≤ m) : star (s m) * rs s N i = 0 := by
  have hi := i.2
  show star (s m) * s i = 0
  rw [ho, if_neg (by omega)]

theorem star_out_mul_cPhi (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (m : ℕ) (hm : N ≤ m) (x : A) : star (s m) * cPhi (rs s N) x = 0 := by
  unfold cPhi
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← mul_assoc, ← mul_assoc, star_out_mul_gen s ho N i m hm, zero_mul, zero_mul]

theorem cPhi_mul_out (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (m : ℕ) (hm : N ≤ m) (x : A) : cPhi (rs s N) x * s m = 0 := by
  unfold cPhi
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [mul_assoc, star_gen_mul_out s ho N i m hm, mul_zero]

theorem cQ_mul_out (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (m : ℕ) (hm : N ≤ m) : cQ s N * s m = s m := by
  unfold cQ
  rw [sub_mul, one_mul, cPhi_mul_out s ho N m hm, sub_zero]

theorem star_out_mul_cQ (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (N : ℕ)
    (m : ℕ) (hm : N ≤ m) : star (s m) * cQ s N = star (s m) := by
  unfold cQ
  rw [mul_sub, mul_one, star_out_mul_cPhi s ho N m hm, sub_zero]

/-- The compressing isometry of level `k` and offset `j`. -/
noncomputable def cV (s : ℕ → A) (N : ℕ) : ℕ → ℕ → A
  | 0, j => s (N + j)
  | k + 1, j => s (N + j) * cQ s N + cPhi (rs s N) (cV s N k (j + 1))

theorem cV_zero (s : ℕ → A) (N j : ℕ) : cV s N 0 j = s (N + j) := rfl

theorem cV_succ (s : ℕ → A) (N k j : ℕ) :
    cV s N (k + 1) j = s (N + j) * cQ s N + cPhi (rs s N) (cV s N k (j + 1)) := rfl

theorem star_gen_mul_cV_succ (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (N : ℕ) (i : Fin N) (k j : ℕ) :
    star (rs s N i) * cV s N (k + 1) j = cV s N k (j + 1) * star (rs s N i) := by
  rw [cV_succ, mul_add, ← mul_assoc, star_gen_mul_out s ho N i (N + j) (by omega), zero_mul, zero_add,
    star_mul_cPhi _ (rs_orth s ho N)]

/-- W2: the compressing element is an isometry. -/
theorem cV_star_mul_self (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (N k : ℕ) : ∀ j, star (cV s N k j) * cV s N k j = 1 := by
  induction k with
  | zero => intro j; rw [cV_zero, ho, if_pos rfl]
  | succ k ih =>
    intro j
    have e1 : cQ s N * star (s (N + j)) * (s (N + j) * cQ s N) = cQ s N := by
      rw [mul_assoc, ← mul_assoc (star (s (N + j))), ho, if_pos rfl, one_mul, cQ_mul_cQ s ho N]
    have e2 : cQ s N * star (s (N + j)) * cPhi (rs s N) (cV s N k (j + 1)) = 0 := by
      rw [mul_assoc, star_out_mul_cPhi s ho N (N + j) (by omega), mul_zero]
    have e3 : star (cPhi (rs s N) (cV s N k (j + 1))) * (s (N + j) * cQ s N) = 0 := by
      rw [← mul_assoc, cPhi_star, cPhi_mul_out s ho N (N + j) (by omega), zero_mul]
    have e4 : star (cPhi (rs s N) (cV s N k (j + 1))) * cPhi (rs s N) (cV s N k (j + 1))
        = 1 - cQ s N := by
      rw [cPhi_star, cPhi_mul _ (rs_orth s ho N), ih (j + 1)]
      unfold cQ
      rw [sub_sub_cancel]
    rw [cV_succ, star_add, star_mul, cQ_star, add_mul, mul_add, mul_add, e1, e2, e3, e4]
    abel

/-- W3: moving a word past the compressing element. -/
theorem star_cW_mul_cV (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (N : ℕ) (β : List (Fin N)) : ∀ k j, β.length ≤ k →
      star (cW (rs s N) β) * cV s N k j
        = cV s N (k - β.length) (j + β.length) * star (cW (rs s N) β) := by
  induction β with
  | nil => intro k j _; simp
  | cons i β ih =>
    intro k j hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hk' : β.length ≤ k' := by simpa using hk
    have h1 : k' + 1 - (i :: β).length = k' - β.length := by simp
    have h2 : j + (i :: β).length = j + 1 + β.length := by simp; omega
    rw [cW_cons, star_mul, mul_assoc, star_gen_mul_cV_succ s ho N, ← mul_assoc, ih k' (j + 1) hk',
      mul_assoc, h1, h2]

/-- W4: compressing elements of different offsets are orthogonal. -/
theorem cV_orth_lt (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (N a : ℕ) : ∀ b d, 0 < d → star (cV s N (a + d) b) * cV s N a (b + d) = 0 := by
  induction a with
  | zero =>
    intro b d hd
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rw [Nat.zero_add, cV_succ, cV_zero, star_add, add_mul, star_mul, cQ_star, mul_assoc, ho,
      if_neg (by omega), mul_zero, zero_add, cPhi_star,
      cPhi_mul_out s ho N (N + (b + (d' + 1))) (by omega)]
  | succ a ih =>
    intro b d hd
    have h1 : a + 1 + d = (a + d) + 1 := by omega
    have h2 : b + d + 1 = b + 1 + d := by omega
    have e1 : cQ s N * star (s (N + b)) * (s (N + (b + d)) * cQ s N) = 0 := by
      rw [mul_assoc, ← mul_assoc (star (s (N + b))), ho, if_neg (by omega), zero_mul, mul_zero]
    have e2 : cQ s N * star (s (N + b)) * cPhi (rs s N) (cV s N a (b + d + 1)) = 0 := by
      rw [mul_assoc, star_out_mul_cPhi s ho N (N + b) (by omega), mul_zero]
    have e3 : star (cPhi (rs s N) (cV s N (a + d) (b + 1))) * (s (N + (b + d)) * cQ s N) = 0 := by
      rw [← mul_assoc, cPhi_star, cPhi_mul_out s ho N (N + (b + d)) (by omega), zero_mul]
    have e4 : star (cPhi (rs s N) (cV s N (a + d) (b + 1))) * cPhi (rs s N) (cV s N a (b + d + 1))
        = 0 := by
      rw [cPhi_star, cPhi_mul _ (rs_orth s ho N), h2, ih (b + 1) d hd, cPhi_zero]
    rw [h1, cV_succ, cV_succ, star_add, star_mul, cQ_star, add_mul, mul_add, mul_add, e1, e2, e3, e4]
    abel

/-- W5: the compression formula. -/
theorem compress_word_inf (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (N k : ℕ) (μ ν : List (Fin N)) (hμ : μ.length ≤ k) (hν : ν.length ≤ k) :
    star (cV s N k 0) * (cW (rs s N) μ * star (cW (rs s N) ν)) * cV s N k 0
      = if μ.length = ν.length then cW (rs s N) μ * star (cW (rs s N) ν) else 0 := by
  have e1 : star (cV s N k 0) * cW (rs s N) μ
      = cW (rs s N) μ * star (cV s N (k - μ.length) μ.length) := by
    have h := congrArg star (star_cW_mul_cV s ho N μ k 0 hμ)
    rw [star_mul, star_star, star_mul, star_star, Nat.zero_add] at h
    exact h
  have e2 := star_cW_mul_cV s ho N ν k 0 hν
  rw [Nat.zero_add] at e2
  have key : star (cV s N (k - μ.length) μ.length) * cV s N (k - ν.length) ν.length
      = if μ.length = ν.length then 1 else 0 := by
    rcases lt_trichotomy μ.length ν.length with h | h | h
    · have h0 := cV_orth_lt s ho N (k - ν.length) μ.length (ν.length - μ.length) (by omega)
      have h1 : k - ν.length + (ν.length - μ.length) = k - μ.length := by omega
      have h2 : μ.length + (ν.length - μ.length) = ν.length := by omega
      rw [h1, h2] at h0
      rw [h0, if_neg (by omega)]
    · rw [h, if_pos rfl, cV_star_mul_self s ho N]
    · have h0 := cV_orth_lt s ho N (k - μ.length) ν.length (μ.length - ν.length) (by omega)
      have h1 : k - μ.length + (μ.length - ν.length) = k - ν.length := by omega
      have h2 : ν.length + (μ.length - ν.length) = μ.length := by omega
      rw [h1, h2] at h0
      have h3 := congrArg star h0
      rw [star_mul, star_star, star_zero] at h3
      rw [h3, if_neg (by omega)]
  calc star (cV s N k 0) * (cW (rs s N) μ * star (cW (rs s N) ν)) * cV s N k 0
      = (star (cV s N k 0) * cW (rs s N) μ) * (star (cW (rs s N) ν) * cV s N k 0) := by
        simp only [mul_assoc]
    _ = cW (rs s N) μ * (star (cV s N (k - μ.length) μ.length) *
          cV s N (k - ν.length) ν.length) * star (cW (rs s N) ν) := by
        rw [e1, e2]; simp only [mul_assoc]
    _ = if μ.length = ν.length then cW (rs s N) μ * star (cW (rs s N) ν) else 0 := by
        rw [key]
        by_cases h : μ.length = ν.length
        · rw [if_pos h, if_pos h, mul_one]
        · rw [if_neg h, if_neg h, mul_zero, zero_mul]

/-- S: the graded matrix-unit system of level `k`, with the scalar-entry property of the
equal-length words of length at most `k`. -/
theorem exists_system_inf (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (N k : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (u e r : ι → A),
      (∀ a b, star (u a) * u b = if a = b then e a else 0) ∧
      ∑ a, u a * star (u a) = 1 ∧
      (∀ a, u a * e a = u a) ∧
      (∀ a, star (r a) * e a * r a = 1) ∧
      ∀ μ ν : List (Fin N), μ.length = ν.length → μ.length ≤ k → ∀ a b, ∃ c : ℂ,
        star (u a) * (cW (rs s N) μ * star (cW (rs s N) ν)) * u b = c • e a ∧
          (c ≠ 0 → e a = e b) := by
  induction k with
  | zero =>
    refine ⟨Unit, inferInstance, inferInstance, fun _ => 1, fun _ => 1, fun _ => 1,
      ?_, ?_, ?_, ?_, ?_⟩
    · intro a b; simp
    · simp
    · intro a; simp
    · intro a; simp
    · intro μ ν hl hk a b
      have hμ : μ = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hν : ν = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hμ; subst hν
      exact ⟨1, by simp, fun _ => rfl⟩
  | succ k ih =>
    obtain ⟨ι, _, _, u, e, r, hu, hs, hue, hr, hent⟩ := ih
    have hoN := rs_orth s ho N
    refine ⟨Option (Fin N × ι), inferInstance, inferInstance,
      fun o => o.elim (cQ s N) (fun p => rs s N p.1 * u p.2),
      fun o => o.elim (cQ s N) (fun p => e p.2),
      fun o => o.elim (s N) (fun p => r p.2), ?_, ?_, ?_, ?_, ?_⟩
    · rintro (_ | ⟨i, a⟩) (_ | ⟨i', a'⟩)
      · show star (cQ s N) * cQ s N = if (none : Option (Fin N × ι)) = none then cQ s N else 0
        rw [if_pos rfl, cQ_star, cQ_mul_cQ s ho N]
      · show star (cQ s N) * (rs s N i' * u a')
          = if (none : Option (Fin N × ι)) = some (i', a') then cQ s N else 0
        rw [if_neg (by simp), cQ_star, ← mul_assoc, cQ_mul_gen s ho N, zero_mul]
      · show star (rs s N i * u a) * cQ s N
          = if some (i, a) = (none : Option (Fin N × ι)) then e a else 0
        rw [if_neg (by simp), star_mul, mul_assoc, star_gen_mul_cQ s ho N, mul_zero]
      · show star (rs s N i * u a) * (rs s N i' * u a')
          = if (some (i, a) : Option (Fin N × ι)) = some (i', a') then e a else 0
        have e0 : star (rs s N i * u a) * (rs s N i' * u a')
            = star (u a) * (star (rs s N i) * rs s N i') * u a' := by
          simp only [star_mul, mul_assoc]
        rw [e0, hoN]
        by_cases hi : i = i'
        · by_cases ha : a = a'
          · subst hi; subst ha
            rw [if_pos rfl, if_pos rfl, mul_one, hu, if_pos rfl]
          · rw [if_pos hi, mul_one, hu, if_neg ha, if_neg (by simp [ha])]
        · rw [if_neg hi, mul_zero, zero_mul, if_neg (by simp [hi])]
    · rw [Fintype.sum_option, Fintype.sum_prod_type]
      show cQ s N * star (cQ s N) + ∑ i, ∑ a, rs s N i * u a * star (rs s N i * u a) = 1
      have e0 : ∀ i : Fin N, ∑ a : ι, rs s N i * u a * star (rs s N i * u a)
          = rs s N i * star (rs s N i) := by
        intro i
        have h : ∑ a : ι, rs s N i * u a * star (rs s N i * u a)
            = rs s N i * (∑ a : ι, u a * star (u a)) * star (rs s N i) := by
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        rw [h, hs, mul_one]
      simp only [e0]
      rw [cQ_star, cQ_mul_cQ s ho N, cQ_add_sum]
    · rintro (_ | ⟨i, a⟩)
      · exact cQ_mul_cQ s ho N
      · show rs s N i * u a * e a = rs s N i * u a
        rw [mul_assoc, hue]
    · rintro (_ | ⟨i, a⟩)
      · show star (s N) * cQ s N * s N = 1
        rw [mul_assoc, cQ_mul_out s ho N N le_rfl, ho, if_pos rfl]
      · exact hr a
    · intro μ ν hl hk a b
      cases μ with
      | nil =>
        cases ν with
        | nil =>
          rcases a with _ | ⟨i, a⟩
          · rcases b with _ | ⟨i', a'⟩
            · refine ⟨1, ?_, fun _ => rfl⟩
              show star (cQ s N) * (cW (rs s N) [] * star (cW (rs s N) [])) * cQ s N = (1 : ℂ) • cQ s N
              rw [cW_nil, star_one, mul_one, mul_one, cQ_star, cQ_mul_cQ s ho N, one_smul]
            · refine ⟨0, ?_, fun h => absurd rfl h⟩
              show star (cQ s N) * (cW (rs s N) [] * star (cW (rs s N) [])) * (rs s N i' * u a') = (0 : ℂ) • cQ s N
              rw [cW_nil, star_one, mul_one, mul_one, cQ_star, ← mul_assoc, cQ_mul_gen s ho N,
                zero_mul, zero_smul]
          · rcases b with _ | ⟨i', a'⟩
            · refine ⟨0, ?_, fun h => absurd rfl h⟩
              show star (rs s N i * u a) * (cW (rs s N) [] * star (cW (rs s N) [])) * cQ s N = (0 : ℂ) • e a
              rw [cW_nil, star_one, mul_one, mul_one, star_mul, mul_assoc, star_gen_mul_cQ s ho N,
                mul_zero, zero_smul]
            · have e0 : star (rs s N i * u a) * (cW (rs s N) [] * star (cW (rs s N) [])) * (rs s N i' * u a')
                  = star (u a) * (star (rs s N i) * rs s N i') * u a' := by
                rw [cW_nil, star_one, mul_one, mul_one]
                simp only [star_mul, mul_assoc]
              by_cases hi : i = i'
              · by_cases ha : a = a'
                · refine ⟨1, ?_, fun _ => congrArg e ha⟩
                  show star (rs s N i * u a) * (cW (rs s N) [] * star (cW (rs s N) [])) * (rs s N i' * u a') = (1 : ℂ) • e a
                  rw [e0, hoN, if_pos hi, mul_one, hu, if_pos ha, one_smul]
                · refine ⟨0, ?_, fun h => absurd rfl h⟩
                  show star (rs s N i * u a) * (cW (rs s N) [] * star (cW (rs s N) [])) * (rs s N i' * u a') = (0 : ℂ) • e a
                  rw [e0, hoN, if_pos hi, mul_one, hu, if_neg ha, zero_smul]
              · refine ⟨0, ?_, fun h => absurd rfl h⟩
                show star (rs s N i * u a) * (cW (rs s N) [] * star (cW (rs s N) [])) * (rs s N i' * u a') = (0 : ℂ) • e a
                rw [e0, hoN, if_neg hi, mul_zero, zero_mul, zero_smul]
        | cons l ν => simp at hl
      | cons i0 μ =>
        cases ν with
        | nil => simp at hl
        | cons l0 ν =>
          have hl' : μ.length = ν.length := by simpa using hl
          have hk' : μ.length ≤ k := by simpa using hk
          have ex : cW (rs s N) (i0 :: μ) * star (cW (rs s N) (l0 :: ν)) = (rs s N i0 * (cW (rs s N) μ * star (cW (rs s N) ν)) * star (rs s N l0)) := by
            rw [cW_cons, cW_cons, star_mul]
            simp only [mul_assoc]
          rw [ex]
          rcases a with _ | ⟨i, a⟩
          · refine ⟨0, ?_, fun h => absurd rfl h⟩
            rcases b with _ | ⟨i', a'⟩
            · show star (cQ s N) * (rs s N i0 * (cW (rs s N) μ * star (cW (rs s N) ν)) * star (rs s N l0)) * cQ s N = (0 : ℂ) • cQ s N
              rw [cQ_star, mul_assoc (rs s N i0), ← mul_assoc (cQ s N), cQ_mul_gen s ho N, zero_mul,
                zero_mul, zero_smul]
            · show star (cQ s N) * (rs s N i0 * (cW (rs s N) μ * star (cW (rs s N) ν)) * star (rs s N l0)) * (rs s N i' * u a') = (0 : ℂ) • cQ s N
              rw [cQ_star, mul_assoc (rs s N i0), ← mul_assoc (cQ s N), cQ_mul_gen s ho N, zero_mul,
                zero_mul, zero_smul]
          · rcases b with _ | ⟨i', a'⟩
            · refine ⟨0, ?_, fun h => absurd rfl h⟩
              show star (rs s N i * u a) * (rs s N i0 * (cW (rs s N) μ * star (cW (rs s N) ν)) * star (rs s N l0)) * cQ s N = (0 : ℂ) • e a
              rw [mul_assoc, mul_assoc _ (star (rs s N l0)), star_gen_mul_cQ s ho N, mul_zero,
                mul_zero, zero_smul]
            · have e0 : star (rs s N i * u a) * (rs s N i0 * (cW (rs s N) μ * star (cW (rs s N) ν)) * star (rs s N l0)) * (rs s N i' * u a')
                  = star (u a) * ((star (rs s N i) * rs s N i0) * (cW (rs s N) μ * star (cW (rs s N) ν)) *
                      (star (rs s N l0) * rs s N i')) * u a' := by
                simp only [star_mul, mul_assoc]
              by_cases h1 : i = i0
              · by_cases h2 : l0 = i'
                · obtain ⟨c, hc, hc'⟩ := hent μ ν hl' hk' a a'
                  refine ⟨c, ?_, hc'⟩
                  show star (rs s N i * u a) * (rs s N i0 * (cW (rs s N) μ * star (cW (rs s N) ν)) * star (rs s N l0)) * (rs s N i' * u a') = c • e a
                  rw [e0, hoN, hoN, if_pos h1, if_pos h2, one_mul, mul_one]
                  exact hc
                · refine ⟨0, ?_, fun h => absurd rfl h⟩
                  show star (rs s N i * u a) * (rs s N i0 * (cW (rs s N) μ * star (cW (rs s N) ν)) * star (rs s N l0)) * (rs s N i' * u a') = (0 : ℂ) • e a
                  rw [e0, hoN, hoN, if_neg h2, mul_zero, mul_zero, zero_mul, zero_smul]
              · refine ⟨0, ?_, fun h => absurd rfl h⟩
                show star (rs s N i * u a) * (rs s N i0 * (cW (rs s N) μ * star (cW (rs s N) ν)) * star (rs s N l0)) * (rs s N i' * u a') = (0 : ℂ) • e a
                rw [e0, hoN, if_neg h1, zero_mul, zero_mul, mul_zero, zero_mul, zero_smul]

/-- S2: the compression of an element of the span of words has graded scalar entries. -/
theorem compress_entry_inf (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (N k : ℕ) {ι : Type} (u e : ι → A)
    (hent : ∀ μ ν : List (Fin N), μ.length = ν.length → μ.length ≤ k → ∀ a b, ∃ c : ℂ,
      star (u a) * (cW (rs s N) μ * star (cW (rs s N) ν)) * u b = c • e a ∧ (c ≠ 0 → e a = e b))
    {x : A} (hx : x ∈ cP (rs s N) k) (a b : ι) :
    ∃ c : ℂ, star (u a) * (star (cV s N k 0) * x * cV s N k 0) * u b = c • e a ∧
      (c ≠ 0 → e a = e b) := by
  unfold cP at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨μ, ν, hμ, hν, rfl⟩ := h
    rw [compress_word_inf s ho N k μ ν hμ hν]
    by_cases hl : μ.length = ν.length
    · rw [if_pos hl]
      exact hent μ ν hl hμ a b
    · rw [if_neg hl]
      exact ⟨0, by simp, fun h => absurd rfl h⟩
  | zero => exact ⟨0, by simp, fun h => absurd rfl h⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hc0⟩ := hx
    obtain ⟨c', hc', hc0'⟩ := hy
    refine ⟨c + c', ?_, fun h => ?_⟩
    · rw [mul_add, add_mul, mul_add, add_mul, hc, hc', add_smul]
    · by_cases h0 : c = 0
      · exact hc0' (by rwa [h0, zero_add] at h)
      · exact hc0 h0
  | smul t x _ hx =>
    obtain ⟨c, hc, hc0⟩ := hx
    refine ⟨t * c, ?_, fun h => hc0 (right_ne_zero_of_mul h)⟩
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, hc, smul_smul]

/-- W6: the compression of an element of the span of lifted words is its integral. -/
theorem compress_eq_cI_inf (s : ℕ → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (N k : ℕ) {g : C(unitInterval, A)} (hg : g ∈ cP (tB (rs s N)) k) (θ : unitInterval) :
    star (cV s N k 0) * g θ * cV s N k 0 = cI g := by
  unfold cP at hg
  induction hg using Submodule.span_induction with
  | mem x h =>
    obtain ⟨μ, ν, hμ, hν, rfl⟩ := h
    rw [cI_word, word_tB_apply, mul_smul_comm, smul_mul_assoc,
      compress_word_inf s ho N k μ ν hμ hν]
    by_cases h : μ.length = ν.length
    · rw [if_pos h, h, ← mul_pow, mul_comm, cE_star_mul_self, one_pow, one_smul]
    · rw [if_neg h, smul_zero]
  | zero => simp [cI]
  | add x y _ _ hx hy =>
    rw [ContinuousMap.add_apply, mul_add, add_mul, hx, hy, cI_add]
  | smul a x _ hx =>
    rw [ContinuousMap.smul_apply, mul_smul_comm, smul_mul_assoc, hx, cI_smul]

end Alg

section Spec

open scoped ComplexConjugate

/-- G: the spectral lemma for a graded matrix-unit system. -/
theorem exists_isometry_compress_inf {B : Type*} [CStarAlgebra B] [Nontrivial B] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (u e r : ι → B)
    (hu : ∀ i j, star (u i) * u j = if i = j then e i else 0)
    (hsum : ∑ i, u i * star (u i) = 1) (hue : ∀ i, u i * e i = u i)
    (hr : ∀ i, star (r i) * e i * r i = 1) (a : B) (c : ι → ι → ℂ)
    (hc : ∀ i j, star (u i) * (star a * a) * u j = c i j • e i)
    (hlvl : ∀ i j, c i j ≠ 0 → e i = e j) :
    ∃ (V : B) (d : ℝ), star V * V = 1 ∧ star V * (star a * a) * V = (d : ℂ) • (1 : B) ∧
      ‖star a * a‖ ≤ d := by
  have he0 : ∀ i, e i ≠ 0 := by
    intro i h
    have h1 := hr i
    rw [h, mul_zero, zero_mul] at h1
    exact zero_ne_one h1
  have hes : ∀ i, star (e i) = e i := by
    intro i
    have h1 := hu i i
    rw [if_pos rfl] at h1
    rw [← h1, star_mul, star_star]
  have hherm : ∀ i j, star (c j i) = c i j := by
    intro i j
    have h := congrArg star (hc j i)
    rw [star_mul, star_mul, star_star, star_mul, star_star, star_smul, hes, ← mul_assoc,
      hc i j] at h
    by_cases hij : c i j = 0
    · rw [hij, zero_smul] at h
      have h1 := (smul_eq_zero.1 h.symm).resolve_right (he0 j)
      rw [h1, hij]
    · rw [← hlvl i j hij] at h
      exact (smul_left_injective ℂ (he0 i) h).symm
  have hC : (Matrix.of c).IsHermitian := by
    ext i j
    simp [Matrix.conjTranspose_apply, hherm]
  obtain ⟨U, d, hU1, hU2, hCU⟩ : ∃ (U : ι → ι → ℂ) (d : ι → ℝ),
      (∀ j k, ∑ i, conj (U i j) * U i k = if j = k then 1 else 0) ∧
      (∀ i k, ∑ j, U i j * conj (U k j) = if i = k then 1 else 0) ∧
      (∀ i j, ∑ k, c i k * U k j = (d j : ℂ) * U i j) := by
    refine ⟨fun i j => hC.eigenvectorUnitary i j, hC.eigenvalues, ?_, ?_, ?_⟩
    · intro j k
      have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 hC.eigenvectorUnitary.2) j) k
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
    · intro i k
      have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hC.eigenvectorUnitary.2) i) k
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h
    · intro i j
      have h := congrFun (hC.mulVec_eigenvectorBasis j) i
      simpa [Matrix.mulVec, dotProduct] using h
  obtain ⟨v, hv⟩ : ∃ v : ι → B, ∀ j, v j = ∑ i, U i j • u i := ⟨_, fun _ => rfl⟩
  have hstar : ∀ j, star (v j) = ∑ i, conj (U i j) • star (u i) := by
    intro j
    simp [hv, star_sum, star_smul]
  have hQu : ∀ i, (star a * a) * u i = ∑ k, c k i • u k := by
    intro i
    calc (star a * a) * u i = (∑ k, u k * star (u k)) * ((star a * a) * u i) := by
          rw [hsum, one_mul]
      _ = ∑ k, c k i • u k := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← mul_assoc (star (u k)), hc, mul_smul_comm, hue]
  have h2 : ∑ j, v j * star (v j) = 1 := by
    have key : ∀ j, v j * star (v j) = ∑ i, ∑ k, (U i j * conj (U k j)) • (u i * star (u k)) := by
      intro j
      rw [hstar, hv]
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
      exact Finset.sum_comm
    simp_rw [key]
    rw [Finset.sum_comm]
    have key2 : ∀ i, ∑ j, ∑ k, (U i j * conj (U k j)) • (u i * star (u k)) =
        u i * star (u i) := by
      intro i
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, hU2]
      simp
    simp_rw [key2]
    exact hsum
  have h3 : ∀ j, (star a * a) * v j = (d j : ℂ) • v j := by
    intro j
    rw [hv, Finset.mul_sum, Finset.smul_sum]
    simp_rw [mul_smul_comm, hQu, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, ← hCU]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have h5 : ∑ j, (d j : ℂ) • (v j * star (v j)) = star a * a := by
    calc ∑ j, (d j : ℂ) • (v j * star (v j))
        = ∑ j, (star a * a) * (v j * star (v j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← mul_assoc, h3, smul_mul_assoc]
      _ = star a * a := by rw [← Finset.mul_sum, h2, mul_one]
  have hne : Nonempty ι := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    rw [Finset.sum_of_isEmpty] at hsum
    exact zero_ne_one hsum
  obtain ⟨j0, hj0⟩ := Finite.exists_max d
  let _ : PartialOrder B := CStarAlgebra.spectralOrder B
  have _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hle : star a * a ≤ algebraMap ℝ B (d j0) := by
    rw [← sub_nonneg]
    have hdiff : algebraMap ℝ B (d j0) - star a * a =
        ∑ j, (d j0 - d j) • (v j * star (v j)) := by
      rw [Algebra.algebraMap_eq_smul_one, ← h5, ← h2, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [sub_smul, Complex.coe_smul]
    rw [hdiff]
    exact Finset.sum_nonneg fun j _ => smul_nonneg (sub_nonneg.2 (hj0 j)) (mul_star_self_nonneg _)
  -- the top eigenvector, cut down to one block
  have hnorm : ∑ i, conj (U i j0) * U i j0 = 1 := by
    have h := hU1 j0 j0
    rwa [if_pos rfl] at h
  obtain ⟨i0, hi0⟩ : ∃ i0, U i0 j0 ≠ 0 := by
    by_contra hcon
    have hall : ∀ i, U i j0 = 0 := fun i => by
      by_contra h
      exact hcon ⟨i, h⟩
    simp [hall] at hnorm
  classical
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ι → ℂ, ∀ i, ξ i = if e i = e i0 then U i j0 else 0 := ⟨_, fun _ => rfl⟩
  have hξe : ∀ i, ξ i • e i = ξ i • e i0 := by
    intro i
    rw [hξ]
    split_ifs with h
    · rw [h]
    · rw [zero_smul, zero_smul]
  have heig : ∀ i, ∑ k, c i k * ξ k = (d j0 : ℂ) * ξ i := by
    intro i
    by_cases hi : e i = e i0
    · rw [hξ i, if_pos hi, ← hCU i j0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hξ k]
      split_ifs with hk
      · rfl
      · have h0 : c i k = 0 := by
          by_contra hne'
          exact hk ((hlvl i k hne').symm.trans hi)
        rw [h0, zero_mul, zero_mul]
    · rw [hξ i, if_neg hi, mul_zero]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hξ k]
      split_ifs with hk
      · have h0 : c i k = 0 := by
          by_contra hne'
          exact hi ((hlvl i k hne').trans hk)
        rw [h0, zero_mul]
      · rw [mul_zero]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ∑ i, ‖ξ i‖ ^ 2 := ⟨_, rfl⟩
  have hρpos : 0 < ρ := by
    rw [hρ]
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i0, Finset.mem_univ _, ?_⟩
    rw [hξ, if_pos rfl]
    exact pow_pos (norm_pos_iff.2 hi0) 2
  obtain ⟨w, hw⟩ : ∃ w : B, w = ∑ i, ξ i • u i := ⟨_, rfl⟩
  have hwstar : star w = ∑ i, conj (ξ i) • star (u i) := by
    rw [hw]
    simp [star_sum, star_smul]
  have hsw : ∀ i, star (u i) * w = ξ i • e i0 := by
    intro i
    rw [hw, Finset.mul_sum, ← hξe i]
    simp_rw [mul_smul_comm, hu]
    simp
  have hww : star w * w = (ρ : ℂ) • e i0 := by
    rw [hwstar, Finset.sum_mul]
    simp_rw [smul_mul_assoc, hsw, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    rw [hρ]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.conj_mul']
  have hQw : (star a * a) * w = (d j0 : ℂ) • w := by
    rw [hw, Finset.mul_sum, Finset.smul_sum]
    simp_rw [mul_smul_comm, hQu, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, ← heig]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = (Real.sqrt ρ)⁻¹ := ⟨_, rfl⟩
  have hττ : τ * τ * ρ = 1 := by
    have hsq : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρpos
    have h1 := Real.mul_self_sqrt hρpos.le
    rw [hτ]
    field_simp
    nlinarith
  have hττc : ((τ * τ : ℝ) : ℂ) * (ρ : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hττ, Complex.ofReal_one]
  have hz1 : ∀ m : B, star ((τ : ℂ) • (w * r i0)) * m * ((τ : ℂ) • (w * r i0))
      = ((τ * τ : ℝ) : ℂ) • (star (r i0) * (star w * m * w) * r i0) := by
    intro m
    simp only [star_smul, star_mul, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_assoc, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  have hVV : star ((τ : ℂ) • (w * r i0)) * ((τ : ℂ) • (w * r i0)) = 1 := by
    have e1 : star (r i0) * (star w * 1 * w) * r i0 = (ρ : ℂ) • (1 : B) := by
      rw [mul_one, hww, mul_smul_comm, smul_mul_assoc, hr]
    have h := hz1 1
    rw [e1, smul_smul, hττc, one_smul, mul_one] at h
    exact h
  have hVQ : star ((τ : ℂ) • (w * r i0)) * (star a * a) * ((τ : ℂ) • (w * r i0))
      = (d j0 : ℂ) • (1 : B) := by
    have e2 : star (r i0) * (star w * (star a * a) * w) * r i0
        = ((d j0 : ℂ) * (ρ : ℂ)) • (1 : B) := by
      rw [mul_assoc (star w), hQw, mul_smul_comm, hww, smul_smul, mul_smul_comm, smul_mul_assoc, hr]
    have h := hz1 (star a * a)
    rw [e2, smul_smul] at h
    rw [h]
    congr 1
    calc ((τ * τ : ℝ) : ℂ) * ((d j0 : ℂ) * (ρ : ℂ)) = (d j0 : ℂ) * (((τ * τ : ℝ) : ℂ) * (ρ : ℂ)) := by
          ring
      _ = (d j0 : ℂ) := by rw [hττc, mul_one]
  have hd0 : 0 ≤ d j0 := by
    refine nonneg_of_smul_one_nonneg (B := B) (d j0) ?_
    rw [← hVQ]
    have hp := star_mul_self_nonneg (a * ((τ : ℂ) • (w * r i0)))
    rwa [star_mul, mul_assoc, ← mul_assoc (star a), ← mul_assoc] at hp
  exact ⟨(τ : ℂ) • (w * r i0), d j0, hVV, hVQ,
    (CStarAlgebra.norm_le_iff_le_algebraMap _ hd0 (star_mul_self_nonneg a)).2 hle⟩

end Spec

section Circle

variable {A : Type*} [CStarAlgebra A]

/-- D1: an element of the star algebra generated by a sequence only uses finitely many members. -/
theorem adjoin_nat_directed {B : Type*} [CStarAlgebra B] (t : ℕ → B) {x : B}
    (hx : x ∈ StarAlgebra.adjoin ℂ (Set.range t)) :
    ∃ N, x ∈ StarAlgebra.adjoin ℂ (Set.range (fun i : Fin N => t i)) := by
  have mono : ∀ {N M : ℕ}, N ≤ M → StarAlgebra.adjoin ℂ (Set.range (fun i : Fin N => t i))
      ≤ StarAlgebra.adjoin ℂ (Set.range (fun i : Fin M => t i)) := by
    intro N M h
    apply StarAlgebra.adjoin_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, lt_of_lt_of_le i.2 h⟩, rfl⟩
  induction hx using StarAlgebra.adjoin_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    exact ⟨i + 1, StarAlgebra.subset_adjoin ℂ _ ⟨⟨i, Nat.lt_succ_self i⟩, rfl⟩⟩
  | algebraMap r => exact ⟨0, algebraMap_mem _ r⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hy
    exact ⟨max N M, add_mem (mono (le_max_left N M) hN) (mono (le_max_right N M) hM)⟩
  | mul x y _ _ hx hy =>
    obtain ⟨N, hN⟩ := hx
    obtain ⟨M, hM⟩ := hy
    exact ⟨max N M, mul_mem (mono (le_max_left N M) hN) (mono (le_max_right N M) hM)⟩
  | star x _ hx =>
    obtain ⟨N, hN⟩ := hx
    exact ⟨N, star_mem hN⟩

/-- The lifted family `θ ↦ e(θ) s i` in `C(unitInterval, A)`, for a sequence `s`. -/
noncomputable def tI (s : ℕ → A) (i : ℕ) : C(unitInterval, A) :=
  ⟨fun θ => cE θ • s i, by fun_prop⟩

theorem tI_apply (s : ℕ → A) (i : ℕ) (θ : unitInterval) : tI s i θ = cE θ • s i := rfl

theorem tI_restrict (s : ℕ → A) (N : ℕ) : (fun i : Fin N => tI s i) = tB (rs s N) := rfl

theorem tB_orth {n : ℕ} (s : Fin n → A) (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (i j : Fin n) : star (tB s i) * tB s j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    refine tB_iso s (fun i => ?_) i
    rw [ho, if_pos rfl]
  · rw [if_neg h]
    ext θ
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply, tB_apply, star_smul,
      smul_mul_smul_comm, ho, if_neg h, smul_zero, ContinuousMap.zero_apply]

/-- C3: the main estimate for a sequence of isometries with orthogonal ranges. -/
theorem main_estimate_inf [Nontrivial A] (s : ℕ → A)
    (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (x : C(unitInterval, A))
    (hx : x ∈ (StarAlgebra.adjoin ℂ (Set.range (tI s))).topologicalClosure) (hx0 : x ≠ 0) :
    ∃ z0 : A, ∀ θ : unitInterval, ‖z0 * (star (x θ) * x θ) * star z0 - 1‖ < 1 := by
  -- the integral of star x * x is nonzero
  have hI : cI (star x * x) ≠ 0 := by
    intro h
    have hz := integral_star_mul_self_faithful
      (fun r : ℝ => (star x * x) (Set.projIcc (0:ℝ) 1 zero_le_one r)) (cI_continuous _)
      (fun r => ⟨x (Set.projIcc (0:ℝ) 1 zero_le_one r), rfl⟩) h
    apply hx0
    ext θ
    have hθ := hz θ θ.2
    rw [Set.projIcc_of_mem zero_le_one θ.2] at hθ
    have hθ' : star (x θ) * x θ = 0 := hθ
    simpa using (CStarRing.star_mul_self_eq_zero_iff (x θ)).1 hθ'
  have hδ0pos : 0 < ‖cI (star x * x)‖ := norm_pos_iff.2 hI
  obtain ⟨δ0, hδ0⟩ : ∃ δ0 : ℝ, δ0 = ‖cI (star x * x)‖ := ⟨_, rfl⟩
  rw [← hδ0] at hδ0pos
  -- approximate x by an element of the algebraic span
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ StarAlgebra.adjoin ℂ (Set.range (tI s)),
      ‖star y * y - star x * x‖ < δ0 / 4 := by
    have hx' : x ∈ closure ((StarAlgebra.adjoin ℂ (Set.range (tI s)) :
        StarSubalgebra ℂ C(unitInterval, A)) : Set C(unitInterval, A)) := by
      rw [← StarSubalgebra.topologicalClosure_coe]; exact hx
    have hcont : Continuous fun y : C(unitInterval, A) => star y * y :=
      continuous_star.mul continuous_id
    have hU : (fun y : C(unitInterval, A) => star y * y) ⁻¹' Metric.ball (star x * x) (δ0 / 4)
        ∈ nhds x :=
      hcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity))
    obtain ⟨y, hyU, hyS⟩ := mem_closure_iff_nhds.1 hx' _ hU
    refine ⟨y, hyS, ?_⟩
    have : dist (star y * y) (star x * x) < δ0 / 4 := hyU
    rwa [dist_eq_norm] at this
  -- only finitely many letters occur
  obtain ⟨N, hyN⟩ := adjoin_nat_directed (tI s) hy
  have hyN' : y ∈ StarAlgebra.adjoin ℂ (Set.range (tB (rs s N))) := hyN
  have hoB := tB_orth (rs s N) (rs_orth s ho N)
  obtain ⟨k, hk⟩ := adjoin_subset_cP (tB (rs s N)) hoB hyN'
  have hg : star y * y ∈ cP (tB (rs s N)) (k + k) :=
    cP_mul (tB (rs s N)) hoB (cP_star (tB (rs s N)) hk) hk
  have hWiso := cV_star_mul_self s ho N (k + k) 0
  have hcomp : ∀ θ : unitInterval, star (cV s N (k + k) 0) *
      (star y * y) θ * cV s N (k + k) 0 = cI (star y * y) :=
    fun θ => compress_eq_cI_inf s ho N (k + k) hg θ
  -- the graded matrix unit system of level k + k
  obtain ⟨ι, _, _, u, e, r, hu, hus, hue, hr, hent⟩ := exists_system_inf s ho N (k + k)
  have hentry : ∀ a b : ι, ∃ c : ℂ, star (u a) * (star (cV s N (k + k) 0) *
      (star y * y) 0 * cV s N (k + k) 0) * u b = c • e a ∧ (c ≠ 0 → e a = e b) :=
    fun a b => compress_entry_inf s ho N (k + k) u e hent (eval_mem_cP (rs s N) hg 0) a b
  generalize cV s N (k + k) 0 = W at hWiso hcomp hentry
  -- lower bound for the norm of the compression
  have hQ : δ0 - δ0 / 4 < ‖cI (star y * y)‖ := by
    have h1' : ‖cI (star y * y) - cI (star x * x)‖ < δ0 / 4 := by
      rw [← cI_sub]; exact (norm_cI_le _).trans_lt hyx
    have h2' : ‖cI (star x * x)‖ ≤ ‖cI (star y * y)‖ + ‖cI (star y * y) - cI (star x * x)‖ := by
      have := norm_sub_le (cI (star y * y)) (cI (star y * y) - cI (star x * x))
      simpa using this
    rw [← hδ0] at h2'
    linarith
  have ha : star (y 0 * W) * (y 0 * W) = cI (star y * y) := by
    rw [← hcomp 0]
    simp [mul_assoc]
  have hentry' : ∀ a b : ι, ∃ c : ℂ, star (u a) * (star (y 0 * W) * (y 0 * W)) * u b = c • e a ∧
      (c ≠ 0 → e a = e b) := by
    intro a b
    rw [ha, ← hcomp 0]
    exact hentry a b
  choose c hc hclvl using hentry'
  obtain ⟨V, d, hV, hVQ, hd⟩ :=
    exists_isometry_compress_inf u e r hu hus hue hr (y 0 * W) c hc hclvl
  rw [ha] at hd hVQ
  have hd0 : 0 < d := by linarith
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.2 hd0
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (Real.sqrt d)⁻¹ := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; exact inv_pos.2 hsq
  have hρρ : ρ * ρ * d = 1 := by
    have := Real.mul_self_sqrt hd0.le
    rw [hρ]
    field_simp
    nlinarith
  have hnV : ‖V‖ = 1 := norm_eq_one_of_star_mul_self V hV
  have hnW : ‖W‖ = 1 := norm_eq_one_of_star_mul_self W hWiso
  have hz1 : ∀ m : A, ((ρ : ℂ) • (star V * star W)) * m * star ((ρ : ℂ) • (star V * star W))
      = ((ρ * ρ : ℝ) : ℂ) • (star V * (star W * m * W) * V) := by
    intro m
    simp only [star_smul, star_mul, star_star, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_assoc, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
  have hg1 : ∀ θ : unitInterval, ((ρ : ℂ) • (star V * star W)) * (star y * y) θ *
      star ((ρ : ℂ) • (star V * star W)) = 1 := by
    intro θ
    rw [hz1, hcomp θ, hVQ, smul_smul, ← Complex.ofReal_mul, hρρ]
    simp
  have hnz : ‖(ρ : ℂ) • (star V * star W)‖ ≤ ρ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    have : ‖star V * star W‖ ≤ 1 := by
      calc ‖star V * star W‖ ≤ ‖star V‖ * ‖star W‖ := norm_mul_le _ _
        _ = 1 := by rw [norm_star, norm_star, hnV, hnW, one_mul]
    nlinarith
  refine ⟨(ρ : ℂ) • (star V * star W), fun θ => ?_⟩
  have hdiff : ‖(star x * x) θ - (star y * y) θ‖ < δ0 / 4 := by
    have := ContinuousMap.norm_coe_le_norm (star x * x - star y * y) θ
    rw [norm_sub_rev] at hyx
    exact lt_of_le_of_lt this hyx
  have e0 : (ρ : ℂ) • (star V * star W) * (star (x θ) * x θ) * star ((ρ : ℂ) • (star V * star W)) - 1
      = (ρ : ℂ) • (star V * star W) * ((star x * x) θ - (star y * y) θ) *
        star ((ρ : ℂ) • (star V * star W)) := by
    rw [mul_sub, sub_mul, hg1 θ]
    rfl
  rw [e0]
  calc ‖(ρ : ℂ) • (star V * star W) * ((star x * x) θ - (star y * y) θ) *
        star ((ρ : ℂ) • (star V * star W))‖
      ≤ ‖(ρ : ℂ) • (star V * star W)‖ * ‖(star x * x) θ - (star y * y) θ‖ *
        ‖star ((ρ : ℂ) • (star V * star W))‖ := norm_mul₃_le
    _ ≤ ρ * (δ0 / 4) * ρ := by
        rw [norm_star]
        have hn0 := norm_nonneg ((ρ : ℂ) • (star V * star W))
        have hm0 := norm_nonneg ((star x * x) θ - (star y * y) θ)
        gcongr
    _ < 1 := by
        have : ρ * (δ0 / 4) * ρ = ρ * ρ * (δ0 / 4) := by ring
        rw [this, ← hρρ]
        have hρρ0 : 0 < ρ * ρ := mul_pos hρ0 hρ0
        nlinarith

/-- Cuntz's theorem for infinitely many letters: a nonzero C⋆-algebra generated by a sequence of
isometries with orthogonal ranges is simple and purely infinite, in the form: every nonzero `w`
has `z` with `z (w⋆ w) z⋆ = 1`. -/
theorem key_fact_inf (A : Type) [CStarAlgebra A] [Nontrivial A] (s : ℕ → A)
    (ho : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hgen : (StarAlgebra.adjoin ℂ (Set.range s)).topologicalClosure = ⊤)
    (w : A) (hw : w ≠ 0) : ∃ z : A, z * (star w * w) * star z = 1 := by
  obtain ⟨S, hS⟩ : ∃ S : StarSubalgebra ℂ C(unitInterval, A),
      S = (StarAlgebra.adjoin ℂ (Set.range (tI s))).topologicalClosure := ⟨_, rfl⟩
  have hSclosed : IsClosed (S : Set C(unitInterval, A)) := by
    rw [hS]; exact StarSubalgebra.isClosed_topologicalClosure _
  let φ : S →⋆ₐ[ℂ] A :=
    { toFun := fun x => (x : C(unitInterval, A)) 0
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl
      map_star' := fun _ => rfl }
  have hφ : ∀ x : S, φ x = (x : C(unitInterval, A)) 0 := fun x => rfl
  have hmain : ∀ x : S, (x : C(unitInterval, A)) ≠ 0 →
      ∃ z0 : A, ‖z0 * (star (φ x) * φ x) * star z0 - 1‖ < 1 := by
    intro x hx0
    obtain ⟨z0, hz0⟩ := main_estimate_inf s ho (x : C(unitInterval, A))
      (by rw [← hS]; exact x.2) hx0
    exact ⟨z0, hz0 0⟩
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨z0, hz0⟩ := hmain x (fun h => hx0 (Subtype.ext h))
    rw [hx] at hz0
    simp at hz0
  have hiso : Isometry φ := NonUnitalStarAlgHom.isometry φ hinj
  have hcomplete : CompleteSpace S := hSclosed.completeSpace_coe
  have hclosed : IsClosed (Set.range φ) := hiso.isClosedEmbedding.isClosed_range
  have hrange : (StarAlgebra.adjoin ℂ (Set.range s)).topologicalClosure ≤ φ.range := by
    apply StarSubalgebra.topologicalClosure_minimal
    · apply StarAlgebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      refine ⟨⟨tI s i, ?_⟩, ?_⟩
      · rw [hS]
        exact StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩)
      · simp [hφ, tI_apply, cE_zero]
    · exact hclosed
  obtain ⟨x, hxw⟩ : w ∈ φ.range := hrange (by rw [hgen]; trivial)
  have hxw' : φ x = w := hxw
  subst hxw'
  have hx0 : (x : C(unitInterval, A)) ≠ 0 := by
    intro h
    apply hw
    rw [hφ, h]
    rfl
  obtain ⟨z0, hz0⟩ := hmain x hx0
  exact exists_conj_star_mul_self_eq_one (φ x) z0 hz0

end Circle

end KeyInf

/-- Piece D: Cuntz's simplicity theorem for the Cuntz family indexed by the natural numbers. -/
theorem cuntzKeyFact_nat : CuntzKeyFact ℕ := by
  intro D _ _ s hs hgen w hw
  refine KeyInf.key_fact_inf D s ?_ hgen w hw
  intro i j
  have h := hs.1 i j
  by_cases hij : i = j
  · rw [if_pos hij] at h ⊢
    exact h
  · rw [if_neg hij] at h ⊢
    exact h

end OMA.S_mo_448788

-- ===== MO448788/Generators =====
/-!
MO 448788, piece A: groupoid toolkit and the standard Cuntz generators

* Toolkit.op_ext_single, Toolkit.op_ext_coord: bounded operators on l2 agreeing on point masses are equal.
* Toolkit.star_single_apply: matrix coefficients of the adjoint.
* Toolkit.injOp: the isometry delta_b to delta_(phi b) of an injection phi.
* BoundaryWord is compact Hausdorff; CuntzGroupoid is Hausdorff.
* Toolkit.bisec i = {(i y, 1, y)} is compact open; its indicator Toolkit.bisecFn i is in C_c.
* standard_generators, reducedAlgebra_nontrivial.
-/

namespace OMA.S_mo_448788

open scoped ENNReal
open Classical

namespace Toolkit

section Ops

variable {G : Type}

theorem single_eq_smul (β : G) (c : ℂ) :
    lp.single (E := fun _ : G => ℂ) 2 β c = c • lp.single (E := fun _ : G => ℂ) 2 β (1 : ℂ) := by
  rw [← lp.single_smul, smul_eq_mul, mul_one]

theorem single_apply' (β γ : G) (c : ℂ) :
    lp.single (E := fun _ : G => ℂ) 2 β c γ = if γ = β then c else 0 := by
  rw [lp.single_apply, Pi.single_apply]

theorem coord_eq_inner (x : lp (fun _ : G => ℂ) 2) (γ : G) :
    x γ = inner ℂ (lp.single 2 γ (1 : ℂ)) x := by
  rw [lp.inner_single_left]; simp

/-- Two bounded operators agreeing on every point mass are equal. -/
theorem op_ext_single {T T' : lp (fun _ : G => ℂ) 2 →L[ℂ] lp (fun _ : G => ℂ) 2}
    (h : ∀ β, T (lp.single 2 β (1 : ℂ)) = T' (lp.single 2 β (1 : ℂ))) : T = T' := by
  ext1 f
  have hs := lp.hasSum_single (E := fun _ : G => ℂ) (p := 2) ENNReal.ofNat_ne_top f
  have h1 := hs.mapL T
  have h2 := hs.mapL T'
  have e : (fun i => T (lp.single 2 i (f i))) = fun i => T' (lp.single 2 i (f i)) := by
    funext i; rw [single_eq_smul, map_smul, map_smul, h]
  rw [e] at h1
  exact h1.unique h2

/-- Two bounded operators with the same matrix coefficients are equal. -/
theorem op_ext_coord {T T' : lp (fun _ : G => ℂ) 2 →L[ℂ] lp (fun _ : G => ℂ) 2}
    (h : ∀ β γ, T (lp.single 2 β (1 : ℂ)) γ = T' (lp.single 2 β (1 : ℂ)) γ) : T = T' :=
  op_ext_single fun β => lp.ext (funext fun γ => h β γ)

/-- Matrix coefficients of the adjoint. -/
theorem star_single_apply (T : lp (fun _ : G => ℂ) 2 →L[ℂ] lp (fun _ : G => ℂ) 2) (β γ : G) :
    (star T) (lp.single 2 β (1 : ℂ)) γ = starRingEnd ℂ (T (lp.single 2 γ (1 : ℂ)) β) := by
  rw [coord_eq_inner, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    lp.inner_single_right]
  simp

theorem norm_extend_rpow {φ : G → G} (hφ : Function.Injective φ) (ξ : G → ℂ) (r : ℝ) (hr : 0 < r) :
    (fun γ => ‖Function.extend φ ξ 0 γ‖ ^ r) = Function.extend φ (fun β => ‖ξ β‖ ^ r) 0 := by
  funext γ
  by_cases h : ∃ β, φ β = γ
  · obtain ⟨β, rfl⟩ := h
    rw [hφ.extend_apply, hφ.extend_apply]
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
    simp [Real.zero_rpow hr.ne']

theorem memℓp_extend {φ : G → G} (hφ : Function.Injective φ) (ξ : lp (fun _ : G => ℂ) 2) :
    Memℓp (Function.extend φ (ξ : G → ℂ) 0) 2 := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hξ := lp.memℓp ξ
  rw [memℓp_gen_iff h2] at hξ ⊢
  rw [norm_extend_rpow hφ _ _ h2]
  exact (summable_extend_zero hφ).mpr hξ

/-- The linear map delta_b to delta_(phi b). -/
noncomputable def injLin {φ : G → G} (hφ : Function.Injective φ) :
    lp (fun _ : G => ℂ) 2 →ₗ[ℂ] lp (fun _ : G => ℂ) 2 where
  toFun ξ := ⟨Function.extend φ (ξ : G → ℂ) 0, memℓp_extend hφ ξ⟩
  map_add' ξ η := by
    apply lp.ext
    funext γ
    show Function.extend φ (fun β => ξ β + η β) 0 γ =
      Function.extend φ (ξ : G → ℂ) 0 γ + Function.extend φ (η : G → ℂ) 0 γ
    by_cases h : ∃ β, φ β = γ
    · obtain ⟨β, rfl⟩ := h
      rw [hφ.extend_apply, hφ.extend_apply, hφ.extend_apply]
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h,
        Function.extend_apply' _ _ _ h]
      simp
  map_smul' c ξ := by
    apply lp.ext
    funext γ
    show Function.extend φ (fun β => c * ξ β) 0 γ = c * Function.extend φ (ξ : G → ℂ) 0 γ
    by_cases h : ∃ β, φ β = γ
    · obtain ⟨β, rfl⟩ := h
      rw [hφ.extend_apply, hφ.extend_apply]
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp

theorem norm_injLin_le {φ : G → G} (hφ : Function.Injective φ) (ξ : lp (fun _ : G => ℂ) 2) :
    ‖injLin hφ ξ‖ ≤ 1 * ‖ξ‖ := by
  rw [one_mul]
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  apply lp.norm_le_of_tsum_le h2 (norm_nonneg ξ)
  rw [lp.norm_rpow_eq_tsum h2 ξ]
  show ∑' γ, ‖Function.extend φ (ξ : G → ℂ) 0 γ‖ ^ (2 : ℝ≥0∞).toReal ≤ _
  rw [norm_extend_rpow hφ _ _ h2, tsum_extend_zero hφ]

/-- The isometry delta_b to delta_(phi b) of an injection phi. -/
noncomputable def injOp (φ : G → G) (hφ : Function.Injective φ) :
    lp (fun _ : G => ℂ) 2 →L[ℂ] lp (fun _ : G => ℂ) 2 :=
  (injLin hφ).mkContinuous 1 (norm_injLin_le hφ)

theorem injOp_apply (φ : G → G) (hφ : Function.Injective φ) (ξ : lp (fun _ : G => ℂ) 2) (γ : G) :
    injOp φ hφ ξ γ = Function.extend φ (ξ : G → ℂ) 0 γ := rfl

theorem injOp_single (φ : G → G) (hφ : Function.Injective φ) (β : G) (c : ℂ) :
    injOp φ hφ (lp.single 2 β c) = lp.single 2 (φ β) c := by
  apply lp.ext
  funext γ
  rw [injOp_apply]
  by_cases h : ∃ β', φ β' = γ
  · obtain ⟨β', rfl⟩ := h
    rw [hφ.extend_apply, single_apply', single_apply']
    simp [hφ.eq_iff]
  · rw [Function.extend_apply' _ _ _ h, single_apply', if_neg (fun e => h ⟨β, e.symm⟩)]
    rfl

theorem star_injOp_single_apply (φ : G → G) (hφ : Function.Injective φ) (β γ : G) :
    (star (injOp φ hφ)) (lp.single 2 β (1 : ℂ)) γ = if β = φ γ then 1 else 0 := by
  rw [star_single_apply, injOp_single, single_apply']
  split_ifs <;> simp

theorem star_injOp_single_image (φ : G → G) (hφ : Function.Injective φ) (β : G) :
    (star (injOp φ hφ)) (lp.single 2 (φ β) (1 : ℂ)) = lp.single 2 β (1 : ℂ) := by
  apply lp.ext
  funext γ
  rw [star_injOp_single_apply, single_apply']
  by_cases h : γ = β
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun e => h (hφ e).symm)]

theorem star_injOp_single_of_not_mem (φ : G → G) (hφ : Function.Injective φ) (β : G)
    (h : ∀ γ, φ γ ≠ β) : (star (injOp φ hφ)) (lp.single 2 β (1 : ℂ)) = 0 := by
  apply lp.ext
  funext γ
  rw [star_injOp_single_apply, if_neg (fun e => h γ e.symm)]
  rfl

end Ops

section Words

variable {ι : Type}

theorem prefixes_eq_true (w : BoundaryWord ι) (μ : List ι) :
    prefixes w μ = true ↔ ∀ (i : ℕ) (h : i < μ.length), w.1 i = some μ[i] := by
  simp [prefixes]

theorem prefixes_nil (w : BoundaryWord ι) : prefixes w [] = true := by
  simp [prefixes]

theorem continuous_prefixes : Continuous (prefixes : BoundaryWord ι → List ι → Bool) :=
  continuous_induced_dom

theorem continuous_prefixes_apply (μ : List ι) : Continuous fun w : BoundaryWord ι => prefixes w μ :=
  (continuous_apply μ).comp continuous_prefixes

/-- The cylinder of words starting with mu. -/
def cyl (μ : List ι) : Set (BoundaryWord ι) := {w | prefixes w μ = true}

theorem isOpen_cyl (μ : List ι) : IsOpen (cyl μ) :=
  (isOpen_discrete {true}).preimage (continuous_prefixes_apply μ)

theorem isClosed_cyl (μ : List ι) : IsClosed (cyl μ) :=
  (isClosed_discrete {true}).preimage (continuous_prefixes_apply μ)

theorem isClopen_cyl (μ : List ι) : IsClopen (cyl μ) := ⟨isClosed_cyl μ, isOpen_cyl μ⟩

theorem none_mono (w : BoundaryWord ι) {j k : ℕ} (hjk : j ≤ k) (h : w.1 j = none) : w.1 k = none := by
  induction hjk with
  | refl => exact h
  | step _ ih => exact w.2.1 _ ih

theorem lengthAtLeast_of_ne_none (w : BoundaryWord ι) {k : ℕ} (hk : w.1 k ≠ none) :
    LengthAtLeast w (k + 1) :=
  fun j hj hn => hk (none_mono w (by omega) hn)

/-- The first m letters of a word of length at least m. -/
noncomputable def pre (w : BoundaryWord ι) (m : ℕ) (hw : LengthAtLeast w m) : List ι :=
  List.ofFn fun j : Fin m => (w.1 j).get (Option.isSome_iff_ne_none.mpr (hw j j.2))

theorem mem_cyl_pre (w : BoundaryWord ι) (m : ℕ) (hw : LengthAtLeast w m) (w' : BoundaryWord ι) :
    w' ∈ cyl (pre w m hw) ↔ ∀ k < m, w'.1 k = w.1 k := by
  simp only [cyl, Set.mem_ofPred_eq, prefixes_eq_true, pre, List.length_ofFn, List.getElem_ofFn,
    Option.some_get]

theorem lengthAtLeast_of_mem_cyl_pre (w : BoundaryWord ι) (m : ℕ) (hw : LengthAtLeast w m)
    (w' : BoundaryWord ι) (h : w' ∈ cyl (pre w m hw)) : LengthAtLeast w' m := by
  intro k hk
  rw [(mem_cyl_pre w m hw w').1 h k hk]
  exact hw k hk

theorem prefixes_injective : Function.Injective (prefixes : BoundaryWord ι → List ι → Bool) := by
  have key : ∀ w w' : BoundaryWord ι, prefixes w = prefixes w' → ∀ k, w.1 k ≠ none →
      w'.1 k = w.1 k := by
    intro w w' h k hk
    have hl := lengthAtLeast_of_ne_none w hk
    have hm : w ∈ cyl (pre w (k + 1) hl) := (mem_cyl_pre _ _ _ _).2 fun _ _ => rfl
    have hm' : w' ∈ cyl (pre w (k + 1) hl) := by
      show prefixes w' _ = true
      rw [← h]; exact hm
    exact (mem_cyl_pre _ _ _ _).1 hm' k (Nat.lt_succ_self k)
  intro w w' h
  apply Subtype.ext
  funext k
  by_cases hk : w.1 k = none
  · by_cases hk' : w'.1 k = none
    · rw [hk, hk']
    · exact key w' w h.symm k hk'
  · exact (key w w' h k hk).symm

instance t2Space_boundaryWord : T2Space (BoundaryWord ι) :=
  T2Space.of_injective_continuous prefixes_injective continuous_prefixes

/-- The closed set of prefix indicators that come from words. -/
def GoodSet (ι : Type) : Set (List ι → Bool) :=
  {P | P [] = true ∧ (∀ (μ : List ι) (k : ℕ), P μ = true → P (μ.take k) = true) ∧
    (∀ μ ν : List ι, μ.length = ν.length → P μ = true → P ν = true → μ = ν) ∧
    (Finite ι → ∀ μ : List ι, P μ = true → ∃ a, P (μ ++ [a]) = true)}

theorem isClosed_goodSet (ι : Type) : IsClosed (GoodSet ι) := by
  have e : GoodSet ι = {P | P [] = true} ∩
      ((⋂ μ : List ι, ⋂ k : ℕ, {P : List ι → Bool | P μ = true → P (μ.take k) = true}) ∩
      ((⋂ μ : List ι, ⋂ ν : List ι,
          {P : List ι → Bool | μ.length = ν.length → P μ = true → P ν = true → μ = ν}) ∩
        {P : List ι → Bool | Finite ι → ∀ μ : List ι, P μ = true → ∃ a, P (μ ++ [a]) = true})) := by
    ext P
    simp only [GoodSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine (isClosed_eq (continuous_apply _) continuous_const).inter
    ((isClosed_iInter fun μ => isClosed_iInter fun k => ?_).inter
      ((isClosed_iInter fun μ => isClosed_iInter fun ν => ?_).inter ?_))
  · have hc : Continuous fun P : List ι → Bool => (P μ, P (μ.take k)) := by fun_prop
    exact (isClosed_discrete {q : Bool × Bool | q.1 = true → q.2 = true}).preimage hc
  · have hc : Continuous fun P : List ι → Bool => (P μ, P ν) := by fun_prop
    exact (isClosed_discrete
      {q : Bool × Bool | μ.length = ν.length → q.1 = true → q.2 = true → μ = ν}).preimage hc
  · by_cases hf : Finite ι
    · have e2 : {P : List ι → Bool | Finite ι → ∀ μ : List ι, P μ = true → ∃ a, P (μ ++ [a]) = true} =
          ⋂ μ : List ι, {P : List ι → Bool | P μ = true → ∃ a, P (μ ++ [a]) = true} := by
        ext P
        simp only [Set.mem_ofPred_eq, Set.mem_iInter]
        exact ⟨fun h => h hf, fun h _ => h⟩
      rw [e2]
      refine isClosed_iInter fun μ => ?_
      have := hf
      have hc : Continuous fun P : List ι → Bool => (P μ, fun a : ι => P (μ ++ [a])) := by fun_prop
      exact (isClosed_discrete {q : Bool × (ι → Bool) | q.1 = true → ∃ a, q.2 a = true}).preimage hc
    · have e2 : {P : List ι → Bool | Finite ι → ∀ μ : List ι, P μ = true → ∃ a, P (μ ++ [a]) = true} =
          Set.univ := by
        ext P
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact fun h => absurd h hf
      rw [e2]
      exact isClosed_univ

theorem range_prefixes_subset :
    Set.range (prefixes : BoundaryWord ι → List ι → Bool) ⊆ GoodSet ι := by
  rintro _ ⟨w, rfl⟩
  refine ⟨prefixes_nil w, fun μ k h => ?_, fun μ ν hl hμ hν => ?_, fun hf μ hμ => ?_⟩
  · rw [prefixes_eq_true] at h ⊢
    intro j hj
    rw [List.getElem_take]
    exact h j (by simp at hj; omega)
  · rw [prefixes_eq_true] at hμ hν
    apply List.ext_getElem hl
    intro j h1 h2
    exact Option.some.inj ((hμ j h1).symm.trans (hν j h2))
  · rw [prefixes_eq_true] at hμ
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (w.2.2 hf μ.length)
    refine ⟨a, ?_⟩
    rw [prefixes_eq_true]
    intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_or_ge j μ.length with h | h
    · rw [List.getElem_append_left h]; exact hμ j h
    · have : j = μ.length := by omega
      subst this
      simp [ha]

theorem good_chain (P : List ι → Bool) (hP : P ∈ GoodSet ι) {μ ν : List ι} (hμ : P μ = true)
    (hν : P ν = true) (hl : μ.length ≤ ν.length) : μ = ν.take μ.length :=
  hP.2.2.1 μ (ν.take μ.length) (by simp [hl]) hμ (hP.2.1 ν μ.length hν)

theorem good_agree (P : List ι → Bool) (hP : P ∈ GoodSet ι) {μ ν : List ι} (hμ : P μ = true)
    (hν : P ν = true) (k : ℕ) (h1 : k < μ.length) (h2 : k < ν.length) : μ[k] = ν[k] := by
  rcases le_total μ.length ν.length with hl | hl
  · rw [List.getElem_of_eq (good_chain P hP hμ hν hl) h1]
    simp
  · rw [List.getElem_of_eq (good_chain P hP hν hμ hl) h2]
    simp

theorem good_long (P : List ι → Bool) (hP : P ∈ GoodSet ι) (hf : Finite ι) :
    ∀ k, ∃ μ : List ι, P μ = true ∧ μ.length = k := by
  intro k
  induction k with
  | zero => exact ⟨[], hP.1, rfl⟩
  | succ k ih =>
    obtain ⟨μ, hμ, hl⟩ := ih
    obtain ⟨a, ha⟩ := hP.2.2.2 hf μ hμ
    exact ⟨μ ++ [a], ha, by simp [hl]⟩

noncomputable def buildFun (P : List ι → Bool) (k : ℕ) : Option ι :=
  if h : ∃ μ : List ι, P μ = true ∧ k < μ.length then
    some ((Classical.choose h)[k]'(Classical.choose_spec h).2) else none

theorem buildFun_eq (P : List ι → Bool) (hP : P ∈ GoodSet ι) {μ : List ι} (hμ : P μ = true)
    {k : ℕ} (hk : k < μ.length) : buildFun P k = some μ[k] := by
  have h : ∃ μ : List ι, P μ = true ∧ k < μ.length := ⟨μ, hμ, hk⟩
  rw [buildFun, dif_pos h]
  congr 1
  exact good_agree P hP (Classical.choose_spec h).1 hμ k _ hk

theorem buildFun_ne_none (P : List ι → Bool) {k : ℕ} (h : buildFun P k ≠ none) :
    ∃ μ : List ι, P μ = true ∧ k < μ.length := by
  by_contra hc
  exact h (dif_neg hc)

noncomputable def buildWord (P : List ι → Bool) (hP : P ∈ GoodSet ι) : BoundaryWord ι :=
  ⟨buildFun P, fun k hk => by
      by_contra hne
      obtain ⟨μ, hμ, hl⟩ := buildFun_ne_none P hne
      rw [buildFun_eq P hP hμ (by omega : k < μ.length)] at hk
      exact Option.some_ne_none _ hk,
    fun hf k => by
      obtain ⟨μ, hμ, hl⟩ := good_long P hP hf (k + 1)
      rw [buildFun_eq P hP hμ (by omega)]
      exact Option.some_ne_none _⟩

theorem prefixes_buildWord (P : List ι → Bool) (hP : P ∈ GoodSet ι) :
    prefixes (buildWord P hP) = P := by
  funext μ
  apply Bool.eq_iff_iff.mpr
  rw [prefixes_eq_true]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos μ.length with h0 | h0
    · rw [List.eq_nil_of_length_eq_zero h0]; exact hP.1
    · have hne : buildFun P (μ.length - 1) ≠ none := by
        rw [show buildFun P (μ.length - 1) = _ from h (μ.length - 1) (by omega)]
        exact Option.some_ne_none _
      obtain ⟨ν, hν, hl⟩ := buildFun_ne_none P hne
      have e : μ = ν.take μ.length := by
        apply List.ext_getElem (by simp; omega)
        intro j h1 h2
        have a1 : buildFun P j = some μ[j] := h j h1
        have a2 := buildFun_eq P hP hν (k := j) (by omega)
        rw [List.getElem_take]
        exact Option.some.inj (a1.symm.trans a2)
      rw [e]; exact hP.2.1 ν _ hν
  · intro h j hj
    exact buildFun_eq P hP h hj

theorem range_prefixes : Set.range (prefixes : BoundaryWord ι → List ι → Bool) = GoodSet ι :=
  Set.Subset.antisymm range_prefixes_subset fun P hP => ⟨buildWord P hP, prefixes_buildWord P hP⟩

instance compactSpace_boundaryWord : CompactSpace (BoundaryWord ι) := by
  have hind : Topology.IsInducing (prefixes : BoundaryWord ι → List ι → Bool) := ⟨rfl⟩
  constructor
  rw [hind.isCompact_iff, Set.image_univ, range_prefixes]
  exact (isClosed_goodSet ι).isCompact

theorem isCompact_cyl (μ : List ι) : IsCompact (cyl μ) := (isClosed_cyl μ).isCompact

/-- Prepend a letter. -/
def consWord (i : ι) (w : BoundaryWord ι) : BoundaryWord ι :=
  ⟨consFn i w.1, fun k hk => by
      cases k with
      | zero => exact absurd hk (Option.some_ne_none _)
      | succ k => exact w.2.1 k hk,
    fun hf k => by
      cases k with
      | zero => exact Option.some_ne_none _
      | succ k => exact w.2.2 hf k⟩

theorem consWord_zero (i : ι) (w : BoundaryWord ι) : (consWord i w).1 0 = some i := rfl

theorem consWord_succ (i : ι) (w : BoundaryWord ι) (k : ℕ) : (consWord i w).1 (k + 1) = w.1 k := rfl

theorem prefixes_consWord_cons (i a : ι) (w : BoundaryWord ι) (ν : List ι) :
    prefixes (consWord i w) (a :: ν) = (decide (a = i) && prefixes w ν) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, decide_eq_true_iff, prefixes_eq_true, prefixes_eq_true]
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have := h 0 (by simp)
      rw [consWord_zero] at this
      simpa using this.symm
    · have := h (j + 1) (by simp; omega)
      rw [consWord_succ] at this
      simpa using this
  · rintro ⟨rfl, h⟩ j hj
    cases j with
    | zero => simp [consWord_zero]
    | succ j =>
      rw [consWord_succ]
      simpa using h j (by simp at hj; omega)

theorem continuous_consWord (i : ι) : Continuous (consWord i) := by
  apply continuous_induced_rng.2
  refine continuous_pi fun μ => ?_
  cases μ with
  | nil =>
    simp only [Function.comp_apply, prefixes_nil]
    exact continuous_const
  | cons a ν =>
    simp only [Function.comp_apply, prefixes_consWord_cons]
    exact (continuous_of_discreteTopology (f := fun b : Bool => decide (a = i) && b)).comp
      (continuous_prefixes_apply ν)

end Words

section Groupoid

variable {ι : Type}

theorem arrow_ext {g h : CuntzGroupoid ι} (hx : g.1.1.1 = h.1.1.1) (hk : g.1.2.1 = h.1.2.1)
    (hy : g.1.2.2.1 = h.1.2.2.1) : g = h :=
  Subtype.ext (Prod.ext (Subtype.ext hx) (Prod.ext hk (Subtype.ext hy)))

/-- The unit arrow (w, 0, w). -/
def unitArrow (w : BoundaryWord ι) : CuntzGroupoid ι :=
  ⟨(w, 0, w), 0, 0, by simp, fun _ hk => absurd hk (Nat.not_lt_zero _),
    fun _ hk => absurd hk (Nat.not_lt_zero _), fun _ => rfl⟩

/-- The arrow map (x, k, y) to (i x, k + 1, y). -/
def consArrow (i : ι) (β : CuntzGroupoid ι) : CuntzGroupoid ι :=
  ⟨(consWord i β.1.1, β.1.2.1 + 1, β.1.2.2), by
    obtain ⟨m, n, hk, hx, hy, hs⟩ := β.2
    refine ⟨m + 1, n, by rw [hk]; push_cast; ring, ?_, hy, fun k => hs k⟩
    intro k hk'
    cases k with
    | zero => exact Option.some_ne_none _
    | succ k => exact hx k (by omega)⟩

theorem consArrow_eq_iff (i j : ι) (β γ : CuntzGroupoid ι) :
    consArrow i β = consArrow j γ ↔ i = j ∧ β = γ := by
  constructor
  · intro h
    have h0 := congrArg (fun g : CuntzGroupoid ι => g.1.1.1 0) h
    have hk := congrArg (fun g : CuntzGroupoid ι => g.1.2.1) h
    have hy := congrArg (fun g : CuntzGroupoid ι => g.1.2.2.1) h
    refine ⟨Option.some.inj h0, arrow_ext ?_ ?_ hy⟩
    · funext k
      exact congrArg (fun g : CuntzGroupoid ι => g.1.1.1 (k + 1)) h
    · have hk' : β.1.2.1 + 1 = γ.1.2.1 + 1 := hk
      omega
  · rintro ⟨rfl, rfl⟩; rfl

theorem consArrow_injective (i : ι) : Function.Injective (consArrow i) :=
  fun _ _ h => ((consArrow_eq_iff i i _ _).1 h).2

/-- Drop the first letter. -/
def tailWord (w : BoundaryWord ι) : BoundaryWord ι :=
  ⟨fun k => w.1 (k + 1), fun k hk => w.2.1 _ hk, fun hf k => w.2.2 hf _⟩

/-- Every arrow whose range word starts with a is consArrow a of an arrow. -/
theorem exists_consArrow (β : CuntzGroupoid ι) (a : ι) (ha : β.1.1.1 0 = some a) :
    ∃ β', consArrow a β' = β := by
  obtain ⟨m, n, hk, hx, hy, hs⟩ := β.2
  have hex : ∃ m' n' : ℕ, β.1.2.1 - 1 = (m' : ℤ) - n' ∧ LengthAtLeast (tailWord β.1.1) m' ∧
      LengthAtLeast β.1.2.2 n' ∧ ∀ k, (tailWord β.1.1).1 (k + m') = β.1.2.2.1 (k + n') := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      refine ⟨0, n + 1, by rw [hk]; push_cast; ring, fun k hk' => absurd hk' (Nat.not_lt_zero k),
        ?_, ?_⟩
      · intro k hk'
        rcases Nat.lt_or_ge k n with h1 | h1
        · exact hy k h1
        · have hkn : k = n := by omega
          subst hkn
          have := hs 0
          simp only [Nat.zero_add] at this
          rw [← this, ha]
          exact Option.some_ne_none _
      · intro k
        have := hs (k + 1)
        show β.1.1.1 (k + 0 + 1) = β.1.2.2.1 (k + (n + 1))
        rw [show k + 0 + 1 = k + 1 + 0 by omega, show k + (n + 1) = k + 1 + n by omega]
        exact this
    · refine ⟨m - 1, n, by rw [hk]; push_cast [Nat.cast_sub hm]; ring, ?_, hy, ?_⟩
      · intro k hk'
        exact hx (k + 1) (by omega)
      · intro k
        show β.1.1.1 (k + (m - 1) + 1) = β.1.2.2.1 (k + n)
        rw [show k + (m - 1) + 1 = k + m by omega]
        exact hs k
  refine ⟨⟨(tailWord β.1.1, β.1.2.1 - 1, β.1.2.2), hex⟩, arrow_ext ?_ ?_ rfl⟩
  · funext k
    cases k with
    | zero => exact ha.symm
    | succ k => rfl
  · show β.1.2.1 - 1 + 1 = β.1.2.1
    ring

theorem isOpen_generator {U V : Set (BoundaryWord ι)} {m n : ℕ} (hU : IsOpen U) (hV : IsOpen V)
    (hU' : ∀ x ∈ U, LengthAtLeast x m) (hV' : ∀ y ∈ V, LengthAtLeast y n) :
    IsOpen (cylinderPair U V m n : Set (CuntzGroupoid ι)) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, V, m, n, hU, hV, hU', hV', rfl⟩

/-- Every arrow has basic open neighbourhoods inside given range and source sets, on which the
degree is constant. -/
theorem exists_open_nbhd (g : CuntzGroupoid ι) {U V : Set (BoundaryWord ι)} (hU : IsOpen U)
    (hV : IsOpen V) (hgU : g.1.1 ∈ U) (hgV : g.1.2.2 ∈ V) :
    ∃ N : Set (CuntzGroupoid ι), IsOpen N ∧ g ∈ N ∧
      ∀ g' ∈ N, g'.1.1 ∈ U ∧ g'.1.2.2 ∈ V ∧ g'.1.2.1 = g.1.2.1 := by
  obtain ⟨m, n, hk, hx, hy, hs⟩ := g.2
  refine ⟨cylinderPair (U ∩ cyl (pre g.1.1 m hx)) (V ∩ cyl (pre g.1.2.2 n hy)) m n, ?_, ?_, ?_⟩
  · exact isOpen_generator (hU.inter (isOpen_cyl _)) (hV.inter (isOpen_cyl _))
      (fun x hx' => lengthAtLeast_of_mem_cyl_pre _ _ hx _ hx'.2)
      (fun y hy' => lengthAtLeast_of_mem_cyl_pre _ _ hy _ hy'.2)
  · exact ⟨⟨hgU, (mem_cyl_pre _ _ _ _).2 fun _ _ => rfl⟩, ⟨hgV, (mem_cyl_pre _ _ _ _).2 fun _ _ => rfl⟩,
      hk, hs⟩
  · rintro g' ⟨h1, h2, h3, -⟩
    exact ⟨h1.1, h2.1, h3.trans hk.symm⟩

theorem continuous_arrowVal :
    Continuous fun g : CuntzGroupoid ι => (g.1 : BoundaryWord ι × ℤ × BoundaryWord ι) := by
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · refine continuous_def.2 fun s hs => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    obtain ⟨N, hN, hgN, hN'⟩ := exists_open_nbhd g hs isOpen_univ hg trivial
    exact ⟨N, fun g' hg' => (hN' g' hg').1, hN, hgN⟩
  · refine continuous_def.2 fun s _ => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    obtain ⟨N, hN, hgN, hN'⟩ := exists_open_nbhd g isOpen_univ isOpen_univ trivial trivial
    refine ⟨N, fun g' hg' => ?_, hN, hgN⟩
    show g'.1.2.1 ∈ s
    rw [(hN' g' hg').2.2]
    exact hg
  · refine continuous_def.2 fun s hs => isOpen_iff_forall_mem_open.2 fun g hg => ?_
    obtain ⟨N, hN, hgN, hN'⟩ := exists_open_nbhd g isOpen_univ hs trivial hg
    exact ⟨N, fun g' hg' => (hN' g' hg').2.1, hN, hgN⟩

instance t2Space_cuntzGroupoid : T2Space (CuntzGroupoid ι) :=
  T2Space.of_injective_continuous (fun a b h => Subtype.ext h) continuous_arrowVal

/-- The compact open bisection Z_i = {(i y, 1, y)}. -/
def bisec (i : ι) : Set (CuntzGroupoid ι) := Set.range fun y => consArrow i (unitArrow y)

theorem continuous_bisecMap (i : ι) :
    Continuous fun y : BoundaryWord ι => (consArrow i (unitArrow y) : CuntzGroupoid ι) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro s ⟨U, V, m, n, hU, hV, hU', hV', rfl⟩
  by_cases h : m = n + 1
  · subst h
    have e : (fun y : BoundaryWord ι => (consArrow i (unitArrow y) : CuntzGroupoid ι)) ⁻¹'
        cylinderPair U V (n + 1) n = consWord i ⁻¹' U ∩ V := by
      ext y
      simp only [Set.mem_preimage, cylinderPair, Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨h1, h2, -, -⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, h2, ?_, fun k => rfl⟩
        show (0 : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) - (n : ℤ)
        push_cast; ring
    rw [e]
    exact ((continuous_consWord i).isOpen_preimage U hU).inter hV
  · have e : (fun y : BoundaryWord ι => (consArrow i (unitArrow y) : CuntzGroupoid ι)) ⁻¹'
        cylinderPair U V m n = ∅ := by
      ext y
      simp only [Set.mem_preimage, cylinderPair, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨-, -, hk, -⟩
      have hk' : (0 : ℤ) + 1 = (m : ℤ) - n := hk
      omega
    rw [e]
    exact isOpen_empty

theorem isCompact_bisec (i : ι) : IsCompact (bisec i) :=
  isCompact_range (continuous_bisecMap i)

theorem bisec_eq (i : ι) : bisec i = cylinderPair (cyl [i]) Set.univ 1 0 := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨?_, trivial, ?_, fun k => rfl⟩
    · show prefixes (consWord i y) [i] = true
      rw [prefixes_consWord_cons]
      simp [prefixes_nil]
    · show (0 : ℤ) + 1 = ((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)
      norm_num
  · rintro ⟨h1, -, h3, h4⟩
    refine ⟨g.1.2.2, arrow_ext ?_ ?_ rfl⟩
    · funext k
      cases k with
      | zero =>
        have := (prefixes_eq_true _ _).1 h1 0 (by simp)
        show some i = g.1.1.1 0
        simpa using this.symm
      | succ k =>
        show g.1.2.2.1 k = g.1.1.1 (k + 1)
        exact (h4 k).symm
    · show (0 : ℤ) + 1 = g.1.2.1
      rw [h3]; norm_num

theorem isOpen_bisec (i : ι) : IsOpen (bisec i) := by
  rw [bisec_eq]
  refine isOpen_generator (isOpen_cyl _) isOpen_univ ?_ ?_
  · intro x hx k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rw [(prefixes_eq_true _ _).1 hx 0 (by simp)]
    exact Option.some_ne_none _
  · intro y _ k hk
    exact absurd hk (Nat.not_lt_zero k)

theorem isClopen_bisec (i : ι) : IsClopen (bisec i) :=
  ⟨(isCompact_bisec i).isClosed, isOpen_bisec i⟩

/-- The indicator of Z_i, a continuous compactly supported function. -/
noncomputable def bisecFn (i : ι) : CompactlySupportedContinuousMap (CuntzGroupoid ι) ℂ :=
  ⟨⟨(bisec i).indicator 1, (isClopen_bisec i).continuous_indicator continuous_one⟩,
    HasCompactSupport.intro (isCompact_bisec i) fun _ hg => Set.indicator_of_notMem hg _⟩

theorem bisecFn_apply (i : ι) (g : CuntzGroupoid ι) : bisecFn i g = (bisec i).indicator 1 g := rfl

end Groupoid

section Generators

variable {ι : Type}

/-- The standard generator S_i delta_b = delta_(i b). -/
noncomputable def Sop (i : ι) : L2 ι →L[ℂ] L2 ι := injOp (consArrow i) (consArrow_injective i)

theorem Sop_single (i : ι) (β : CuntzGroupoid ι) (c : ℂ) :
    Sop i (lp.single 2 β c) = lp.single 2 (consArrow i β) c :=
  injOp_single _ _ β c

theorem Sop_isStandard : IsStandardGenerators (Sop (ι := ι)) := by
  intro i β γ
  rw [Sop_single, single_apply']
  have hiff : γ = consArrow i β ↔ (γ.1.1.1 = consFn i β.1.1.1 ∧ γ.1.2.1 = β.1.2.1 + 1 ∧
      γ.1.2.2 = β.1.2.2) := by
    constructor
    · rintro rfl; exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨h1, h2, h3⟩
      exact arrow_ext h1 h2 (congrArg Subtype.val h3)
  by_cases h : γ = consArrow i β
  · rw [if_pos h, if_pos (hiff.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h'))]

/-- Any family satisfying IsStandardGenerators is the family Sop. -/
theorem eq_Sop_of_isStandard {S : ι → (L2 ι →L[ℂ] L2 ι)} (hS : IsStandardGenerators S) (i : ι) :
    S i = Sop i :=
  op_ext_coord fun β γ => by rw [hS i β γ, Sop_isStandard i β γ]

theorem Sop_isConvolution (i : ι) : IsConvolutionOperator (bisecFn i) (Sop i) := by
  intro β γ
  rw [Sop_single, single_apply']
  by_cases h : γ = consArrow i β
  · have hmem : (consArrow i (unitArrow β.1.1)).1.2.2 = β.1.1 ∧
        ((consArrow i (unitArrow β.1.1)).1.1, (consArrow i (unitArrow β.1.1)).1.2.1 + β.1.2.1,
          β.1.2.2) = γ.1 := by
      refine ⟨rfl, ?_⟩
      subst h
      exact Prod.ext rfl (Prod.ext (show (0 : ℤ) + 1 + β.1.2.1 = β.1.2.1 + 1 by ring) rfl)
    rw [if_pos h, tsum_eq_single ⟨consArrow i (unitArrow β.1.1), hmem⟩]
    · rw [bisecFn_apply, Set.indicator_of_mem
        (show consArrow i (unitArrow β.1.1) ∈ bisec i from ⟨_, rfl⟩)]
      rfl
    · rintro ⟨α, hα1, hα2⟩ hne
      rw [bisecFn_apply]
      apply Set.indicator_of_notMem
      rintro ⟨y, rfl⟩
      apply hne
      have hy : y = β.1.1 := hα1
      subst hy
      rfl
  · rw [if_neg h]
    symm
    refine (tsum_congr fun α => ?_).trans tsum_zero
    obtain ⟨α, hα1, hα2⟩ := α
    rw [bisecFn_apply]
    apply Set.indicator_of_notMem
    rintro ⟨y, rfl⟩
    apply h
    have hy : y = β.1.1 := hα1
    subst hy
    apply arrow_ext
    · exact (congrArg (fun p => p.1.1) hα2).symm
    · have hk : (0 : ℤ) + 1 + β.1.2.1 = γ.1.2.1 := congrArg (fun p => p.2.1) hα2
      show γ.1.2.1 = β.1.2.1 + 1
      omega
    · exact (congrArg (fun p => p.2.2.1) hα2).symm

theorem Sop_mem (i : ι) : Sop i ∈ reducedAlgebra ι :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _
    (show Sop i ∈ {T | ∃ f : CompactlySupportedContinuousMap (CuntzGroupoid ι) ℂ,
      IsConvolutionOperator f T} from ⟨bisecFn i, Sop_isConvolution i⟩))

theorem star_Sop_mul_Sop (i j : ι) :
    star (Sop i) * Sop j = if i = j then (1 : L2 ι →L[ℂ] L2 ι) else 0 := by
  apply op_ext_single
  intro β
  rw [ContinuousLinearMap.mul_apply, Sop_single]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Sop, star_injOp_single_image]
    rfl
  · rw [if_neg h, Sop, star_injOp_single_of_not_mem]
    · rfl
    · intro γ e
      exact h ((consArrow_eq_iff i j γ β).1 e).1

theorem sum_Sop_mul_star [Fintype ι] :
    ∑ i, Sop i * star (Sop i) = (1 : L2 ι →L[ℂ] L2 ι) := by
  apply op_ext_single
  intro β
  rw [ContinuousLinearMap.sum_apply]
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (β.1.1.2.2 (Finite.of_fintype ι) 0)
  obtain ⟨β', rfl⟩ := exists_consArrow β a ha
  rw [Finset.sum_eq_single a]
  · rw [ContinuousLinearMap.mul_apply, Sop, star_injOp_single_image, ← Sop, Sop_single]
    rfl
  · intro b _ hb
    rw [ContinuousLinearMap.mul_apply, Sop, star_injOp_single_of_not_mem, map_zero]
    intro γ e
    exact hb ((consArrow_eq_iff b a γ β').1 e).1
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The constant word i i i ... -/
def constWord (i : ι) : BoundaryWord ι :=
  ⟨fun _ => some i, fun _ h => absurd h (Option.some_ne_none _), fun _ _ => Option.some_ne_none _⟩

end Generators

end Toolkit

open Toolkit

/-- The standard generators S_i, lying in the reduced algebra and satisfying the Cuntz relations. -/
theorem standard_generators (ι : Type) [Nonempty ι] :
    ∃ S : ι → reducedAlgebra ι, IsStandardGenerators (fun i => (S i : L2 ι →L[ℂ] L2 ι)) ∧
      IsCuntzFamily S := by
  refine ⟨fun i => ⟨Sop i, Sop_mem i⟩, Sop_isStandard, fun i j => ?_, fun hf => ?_⟩
  · apply Subtype.ext
    show star (Sop i) * Sop j = _
    rw [star_Sop_mul_Sop]
    split_ifs <;> rfl
  · have := Fintype.ofFinite ι
    rw [finsum_eq_sum_of_fintype]
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    exact sum_Sop_mul_star

theorem reducedAlgebra_nontrivial (ι : Type) [Nonempty ι] : Nontrivial (reducedAlgebra ι) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : (0 : L2 ι →L[ℂ] L2 ι) = 1 := congrArg Subtype.val h
  let g : CuntzGroupoid ι := unitArrow (constWord (Classical.arbitrary ι))
  have := congrArg (fun T : L2 ι →L[ℂ] L2 ι => T (lp.single 2 g (1 : ℂ)) g) h'
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply] at this
  rw [single_apply', if_pos rfl] at this
  exact zero_ne_one this

end OMA.S_mo_448788

-- ===== MO448788/Generation =====
/-!
# MO 448788, piece B: the standard generators generate the reduced algebra

Every convolution operator of a continuous compactly supported function lies in the closed star
algebra generated by the standard generators. Route: diagonal operators of continuous functions on
the unit space are in that algebra (Stone-Weierstrass on the compact unit space), and a convolution
operator is peeled off one basic bisection at a time.
-/

namespace OMA.S_mo_448788

open scoped ENNReal
open Classical

namespace Gen

variable {ι : Type}

/-! ## Words -/

theorem prefixes_iff (w : BoundaryWord ι) (μ : List ι) :
    prefixes w μ = true ↔ ∀ (i : ℕ) (h : i < μ.length), w.1 i = some μ[i] := by
  unfold prefixes
  rw [decide_eq_true_iff]
  rfl

theorem prefixes_nil (w : BoundaryWord ι) : prefixes w [] = true := by
  rw [prefixes_iff]
  intro i h
  exact absurd h (Nat.not_lt_zero i)

theorem prefixes_concat_iff (w : BoundaryWord ι) (μ : List ι) (a : ι) :
    prefixes w (μ ++ [a]) = true ↔ prefixes w μ = true ∧ w.1 μ.length = some a := by
  rw [prefixes_iff, prefixes_iff]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have := h i (by rw [List.length_append]; exact Nat.lt_add_right _ hi)
      rw [this, List.getElem_append_left hi]
    · have := h μ.length (by rw [List.length_append]; exact Nat.lt_succ_self _)
      rw [this, List.getElem_concat_length rfl]
  · rintro ⟨h1, h2⟩ i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < μ.length
    · rw [h1 i hlt, List.getElem_append_left hlt]
    · have hi' : i = μ.length := by omega
      subst hi'
      rw [h2, List.getElem_concat_length rfl]

/-- The cylinder of words starting with the finite word. -/
def Zc (μ : List ι) : Set (BoundaryWord ι) := {x | prefixes x μ = true}

theorem continuous_prefixes_apply (μ : List ι) :
    Continuous (fun x : BoundaryWord ι => prefixes x μ) :=
  (continuous_apply μ).comp
    (continuous_induced_dom : Continuous (prefixes : BoundaryWord ι → List ι → Bool))

theorem isClopen_Zc (μ : List ι) : IsClopen (Zc (ι := ι) μ) :=
  (isClopen_discrete ({true} : Set Bool)).preimage (continuous_prefixes_apply μ)

theorem none_propagates (w : BoundaryWord ι) (k : ℕ) (h : w.1 k = none) (d : ℕ) :
    w.1 (k + d) = none := by
  induction d with
  | zero => exact h
  | succ d ih => exact w.2.1 _ ih

theorem lengthAtLeast_of_ne_none (w : BoundaryWord ι) (k : ℕ) (h : w.1 k ≠ none) :
    LengthAtLeast w (k + 1) := by
  intro j hj hn
  apply h
  have := none_propagates w j hn (k - j)
  rwa [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp hj)] at this

theorem exists_prefix (w : BoundaryWord ι) (m : ℕ) (h : LengthAtLeast w m) :
    ∃ μ : List ι, μ.length = m ∧ prefixes w μ = true := by
  induction m with
  | zero => exact ⟨[], rfl, prefixes_nil w⟩
  | succ m ih =>
    obtain ⟨μ, hμ, hp⟩ := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (h m (Nat.lt_succ_self m))
    refine ⟨μ ++ [a], by rw [List.length_append, hμ, List.length_singleton], ?_⟩
    rw [prefixes_concat_iff, hμ]
    exact ⟨hp, ha⟩

theorem prefixes_inj (x y : BoundaryWord ι) (h : ∀ μ, prefixes x μ = prefixes y μ) : x = y := by
  have key : ∀ (u v : BoundaryWord ι), (∀ μ, prefixes u μ = prefixes v μ) → ∀ k a,
      u.1 k = some a → v.1 k = some a := by
    intro u v huv k a hk
    have hne : u.1 k ≠ none := by rw [hk]; exact Option.some_ne_none a
    obtain ⟨μ, hμ, hp⟩ := exists_prefix u (k + 1) (lengthAtLeast_of_ne_none u k hne)
    have hq : prefixes v μ = true := by rw [← huv μ]; exact hp
    rw [prefixes_iff] at hp hq
    have hk' : k < μ.length := by rw [hμ]; exact Nat.lt_succ_self k
    have e1 := hp k hk'
    have e2 := hq k hk'
    rw [e2, ← e1, hk]
  apply Subtype.ext
  funext k
  cases hx : x.1 k with
  | some a => exact (key x y h k a hx).symm
  | none =>
    cases hy : y.1 k with
    | none => rfl
    | some b =>
      have := key y x (fun μ => (h μ).symm) k b hy
      rw [hx] at this
      exact this

/-! ## Prepending a finite word -/

/-- Prepend a finite word to a sequence. -/
def catFn (μ : List ι) (w : ℕ → Option ι) : ℕ → Option ι :=
  fun k => if h : k < μ.length then some μ[k] else w (k - μ.length)

theorem catFn_lt (μ : List ι) (w : ℕ → Option ι) (k : ℕ) (h : k < μ.length) :
    catFn μ w k = some μ[k] := dif_pos h

theorem catFn_ge (μ : List ι) (w : ℕ → Option ι) (k : ℕ) (h : ¬ k < μ.length) :
    catFn μ w k = w (k - μ.length) := dif_neg h

theorem catFn_add (μ : List ι) (w : ℕ → Option ι) (j : ℕ) :
    catFn μ w (j + μ.length) = w j := by
  rw [catFn_ge μ w _ (by omega), Nat.add_sub_cancel]

theorem catFn_nil (w : ℕ → Option ι) : catFn [] w = w := by
  funext k
  rw [catFn_ge [] w k (Nat.not_lt_zero k)]
  rfl

theorem catFn_cons (i : ι) (μ : List ι) (w : ℕ → Option ι) :
    catFn (i :: μ) w = consFn i (catFn μ w) := by
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    show catFn (i :: μ) w (k + 1) = catFn μ w k
    by_cases h : k < μ.length
    · rw [catFn_lt μ w k h, catFn_lt (i :: μ) w (k + 1) (by rw [List.length_cons]; omega)]
      rfl
    · rw [catFn_ge μ w k h, catFn_ge (i :: μ) w (k + 1) (by rw [List.length_cons]; omega),
        List.length_cons, Nat.add_sub_add_right]

/-- Prepend a finite word to a boundary word. -/
def cat (μ : List ι) (w : BoundaryWord ι) : BoundaryWord ι :=
  ⟨catFn μ w.1, by
    refine ⟨fun k hk => ?_, fun hf k => ?_⟩
    · by_cases h1 : k < μ.length
      · rw [catFn_lt μ w.1 k h1] at hk
        exact absurd hk (Option.some_ne_none _)
      · rw [catFn_ge μ w.1 k h1] at hk
        rw [catFn_ge μ w.1 (k + 1) (by omega)]
        have e : k + 1 - μ.length = (k - μ.length) + 1 := by omega
        rw [e]
        exact w.2.1 _ hk
    · by_cases h1 : k < μ.length
      · rw [catFn_lt μ w.1 k h1]
        exact Option.some_ne_none _
      · rw [catFn_ge μ w.1 k h1]
        exact w.2.2 hf _⟩

theorem cat_val (μ : List ι) (w : BoundaryWord ι) : (cat μ w).1 = catFn μ w.1 := rfl

theorem cat_nil (w : BoundaryWord ι) : cat [] w = w :=
  Subtype.ext (catFn_nil w.1)

theorem cat_cons (i : ι) (μ : List ι) (w : BoundaryWord ι) :
    cat (i :: μ) w = cat [i] (cat μ w) := by
  apply Subtype.ext
  show catFn (i :: μ) w.1 = catFn [i] (catFn μ w.1)
  rw [catFn_cons, catFn_cons, catFn_nil]

theorem prefixes_cat (μ : List ι) (w : BoundaryWord ι) : prefixes (cat μ w) μ = true := by
  rw [prefixes_iff]
  intro i h
  exact catFn_lt μ w.1 i h

theorem cat_injective (μ : List ι) (w w' : BoundaryWord ι) (h : cat μ w = cat μ w') : w = w' := by
  apply Subtype.ext
  funext j
  have := congrArg (fun x : BoundaryWord ι => x.1 (j + μ.length)) h
  simp only [cat_val, catFn_add] at this
  exact this

theorem eq_cat_of (x z : BoundaryWord ι) (μ : List ι) (hp : prefixes x μ = true)
    (hs : ∀ j, x.1 (j + μ.length) = z.1 j) : x = cat μ z := by
  apply Subtype.ext
  funext k
  rw [cat_val]
  by_cases h : k < μ.length
  · rw [catFn_lt μ z.1 k h]
    exact (prefixes_iff x μ).mp hp k h
  · rw [catFn_ge μ z.1 k h, ← hs, Nat.sub_add_cancel (Nat.le_of_not_lt h)]

/-- Drop the first letters of a boundary word. -/
def dropW (n : ℕ) (w : BoundaryWord ι) : BoundaryWord ι :=
  ⟨fun k => w.1 (k + n), by
    refine ⟨fun k hk => ?_, fun hf k => w.2.2 hf _⟩
    have e : k + 1 + n = (k + n) + 1 := by omega
    show w.1 (k + 1 + n) = none
    rw [e]
    exact w.2.1 _ hk⟩

theorem cat_dropW (x : BoundaryWord ι) (μ : List ι) (hp : prefixes x μ = true) :
    x = cat μ (dropW μ.length x) :=
  eq_cat_of x _ μ hp (fun _ => rfl)

theorem prefixes_cat_single_cons (i j : ι) (τ : List ι) (z : BoundaryWord ι) :
    prefixes (cat [i] z) (j :: τ) = if i = j then prefixes z τ else false := by
  rw [Bool.eq_iff_iff, prefixes_iff]
  constructor
  · intro h
    have h0 := h 0 (by rw [List.length_cons]; omega)
    have hij : i = j := by
      rw [cat_val, catFn_lt [i] z.1 0 (by rw [List.length_singleton]; omega)] at h0
      exact Option.some.inj h0
    rw [if_pos hij, prefixes_iff]
    intro k hk
    have h1 := h (k + 1) (by rw [List.length_cons]; omega)
    rw [cat_val] at h1
    have e : catFn [i] z.1 (k + 1) = z.1 k := catFn_add [i] z.1 k
    rw [e] at h1
    rw [h1]
    rfl
  · intro h k hk
    by_cases hij : i = j
    · rw [if_pos hij, prefixes_iff] at h
      cases k with
      | zero =>
        rw [cat_val, catFn_lt [i] z.1 0 (by rw [List.length_singleton]; omega)]
        show some i = some j
        rw [hij]
      | succ k =>
        rw [List.length_cons] at hk
        have e : catFn [i] z.1 (k + 1) = z.1 k := catFn_add [i] z.1 k
        rw [cat_val, e, h k (by omega)]
        rfl
    · rw [if_neg hij] at h
      exact absurd h Bool.false_ne_true

theorem continuous_cat (μ : List ι) : Continuous (cat (ι := ι) μ) := by
  induction μ with
  | nil =>
    have : cat (ι := ι) [] = id := funext cat_nil
    rw [this]
    exact continuous_id
  | cons i μ ih =>
    have hc : cat (ι := ι) (i :: μ) = cat [i] ∘ cat μ := funext (cat_cons i μ)
    rw [hc]
    refine Continuous.comp ?_ ih
    rw [continuous_induced_rng]
    refine continuous_pi (fun τ => ?_)
    cases τ with
    | nil =>
      have : ((fun p : List ι → Bool => p []) ∘ (prefixes ∘ cat (ι := ι) [i])) = fun _ => true :=
        funext (fun z => prefixes_nil (cat [i] z))
      show Continuous ((fun p : List ι → Bool => p []) ∘ (prefixes ∘ cat (ι := ι) [i]))
      rw [this]
      exact continuous_const
    | cons j τ =>
      have : ((fun p : List ι → Bool => p (j :: τ)) ∘ (prefixes ∘ cat (ι := ι) [i])) =
          fun z => if i = j then prefixes z τ else false :=
        funext (fun z => prefixes_cat_single_cons i j τ z)
      show Continuous ((fun p : List ι → Bool => p (j :: τ)) ∘ (prefixes ∘ cat (ι := ι) [i]))
      rw [this]
      by_cases hij : i = j
      · simp only [if_pos hij]
        exact continuous_prefixes_apply τ
      · simp only [if_neg hij]
        exact continuous_const

/-! ## The unit space is compact -/

theorem unique_of_chain (p : List ι → Bool)
    (h2 : ∀ (μ : List ι) (i : ι), p (μ ++ [i]) = true → p μ = true)
    (h3 : ∀ (μ : List ι) (i j : ι), p (μ ++ [i]) = true → p (μ ++ [j]) = true → i = j) :
    ∀ (n : ℕ) (μ ν : List ι), μ.length = n → ν.length = n → p μ = true → p ν = true → μ = ν := by
  intro n
  induction n with
  | zero =>
    intro μ ν hμ hν _ _
    rw [List.length_eq_zero_iff.mp hμ, List.length_eq_zero_iff.mp hν]
  | succ n ih =>
    intro μ ν hμ hν pμ pν
    rcases List.eq_nil_or_concat' μ with rfl | ⟨μ', a, rfl⟩
    · exact (Nat.succ_ne_zero n hμ.symm).elim
    rcases List.eq_nil_or_concat' ν with rfl | ⟨ν', b, rfl⟩
    · exact (Nat.succ_ne_zero n hν.symm).elim
    rw [List.length_append, List.length_singleton] at hμ hν
    have e := ih μ' ν' (by omega) (by omega) (h2 _ _ pμ) (h2 _ _ pν)
    subst e
    rw [h3 μ' a b pμ pν]

/-- The word whose set of prefixes is a given chain of finite words. -/
noncomputable def wordOf (p : List ι → Bool) : ℕ → Option ι :=
  fun k => if h : ∃ i : ι, ∃ μ : List ι, μ.length = k ∧ p (μ ++ [i]) = true then some h.choose
    else none

theorem wordOf_eq_some_iff (p : List ι → Bool)
    (h2 : ∀ (μ : List ι) (i : ι), p (μ ++ [i]) = true → p μ = true)
    (h3 : ∀ (μ : List ι) (i j : ι), p (μ ++ [i]) = true → p (μ ++ [j]) = true → i = j)
    (k : ℕ) (a : ι) :
    wordOf p k = some a ↔ ∃ μ : List ι, μ.length = k ∧ p (μ ++ [a]) = true := by
  constructor
  · intro h
    unfold wordOf at h
    by_cases hex : ∃ i : ι, ∃ μ : List ι, μ.length = k ∧ p (μ ++ [i]) = true
    · rw [dif_pos hex] at h
      have hs := hex.choose_spec
      rw [Option.some.inj h] at hs
      exact hs
    · rw [dif_neg hex] at h
      exact absurd h.symm (Option.some_ne_none a)
  · rintro ⟨μ, hμ, hp⟩
    have hex : ∃ i : ι, ∃ μ : List ι, μ.length = k ∧ p (μ ++ [i]) = true := ⟨a, μ, hμ, hp⟩
    unfold wordOf
    rw [dif_pos hex]
    obtain ⟨μ', hμ', hp'⟩ := hex.choose_spec
    have e := unique_of_chain p h2 h3 (k + 1) (μ' ++ [hex.choose]) (μ ++ [a])
      (by rw [List.length_append, hμ', List.length_singleton])
      (by rw [List.length_append, hμ, List.length_singleton]) hp' hp
    have e2 := (List.append_inj' e rfl).2
    rw [(List.cons.inj e2).1]

theorem range_prefixes_eq :
    Set.range (prefixes : BoundaryWord ι → List ι → Bool) =
      {p | p [] = true ∧ (∀ (μ : List ι) (i : ι), p (μ ++ [i]) = true → p μ = true) ∧
        (∀ (μ : List ι) (i j : ι), p (μ ++ [i]) = true → p (μ ++ [j]) = true → i = j) ∧
        (Finite ι → ∀ μ : List ι, p μ = true → ∃ i : ι, p (μ ++ [i]) = true)} := by
  ext p
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨prefixes_nil w, fun μ i h => ((prefixes_concat_iff w μ i).mp h).1,
      fun μ i j hi hj => ?_, fun hf μ h => ?_⟩
    · have e1 := ((prefixes_concat_iff w μ i).mp hi).2
      have e2 := ((prefixes_concat_iff w μ j).mp hj).2
      rw [e1] at e2
      exact Option.some.inj e2
    · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (w.2.2 hf μ.length)
      exact ⟨a, (prefixes_concat_iff w μ a).mpr ⟨h, ha⟩⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hw : (∀ k, wordOf p k = none → wordOf p (k + 1) = none) ∧
        (Finite ι → ∀ k, wordOf p k ≠ none) := by
      refine ⟨fun k hk => ?_, fun hf => ?_⟩
      · by_contra hne
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
        obtain ⟨μ, hμ, hp⟩ := (wordOf_eq_some_iff p h2 h3 (k + 1) a).mp ha
        have hpμ := h2 μ a hp
        rcases List.eq_nil_or_concat' μ with rfl | ⟨μ', b, rfl⟩
        · exact Nat.succ_ne_zero k hμ.symm
        · rw [List.length_append, List.length_singleton] at hμ
          have hb := (wordOf_eq_some_iff p h2 h3 k b).mpr ⟨μ', by omega, hpμ⟩
          rw [hk] at hb
          exact Option.some_ne_none b hb.symm
      · have hex : ∀ k, ∃ μ : List ι, μ.length = k ∧ p μ = true := by
          intro k
          induction k with
          | zero => exact ⟨[], rfl, h1⟩
          | succ k ih =>
            obtain ⟨μ, hμ, hp⟩ := ih
            obtain ⟨i, hi⟩ := h4 hf μ hp
            exact ⟨μ ++ [i], by rw [List.length_append, hμ, List.length_singleton], hi⟩
        intro k
        obtain ⟨μ, hμ, hp⟩ := hex k
        obtain ⟨i, hi⟩ := h4 hf μ hp
        rw [(wordOf_eq_some_iff p h2 h3 k i).mpr ⟨μ, hμ, hi⟩]
        exact Option.some_ne_none i
    let w : BoundaryWord ι := ⟨wordOf p, hw⟩
    refine ⟨w, ?_⟩
    funext μ
    induction μ using List.reverseRecOn with
    | nil => rw [prefixes_nil, h1]
    | append_singleton μ a ih =>
      rw [Bool.eq_iff_iff, prefixes_concat_iff]
      constructor
      · rintro ⟨hp, ha⟩
        rw [ih] at hp
        have ha : wordOf p μ.length = some a := ha
        obtain ⟨μ', hμ', hp'⟩ := (wordOf_eq_some_iff p h2 h3 μ.length a).mp ha
        have e := unique_of_chain p h2 h3 μ.length μ' μ hμ' rfl (h2 μ' a hp') hp
        rw [← e]
        exact hp'
      · intro hp
        refine ⟨?_, ?_⟩
        · rw [ih]
          exact h2 μ a hp
        · show wordOf p μ.length = some a
          exact (wordOf_eq_some_iff p h2 h3 μ.length a).mpr ⟨μ, rfl, hp⟩

theorem isClosed_bool2 {Y : Type} [TopologicalSpace Y] (f g : Y → Bool) (hf : Continuous f)
    (hg : Continuous g) (P : Bool → Bool → Prop) : IsClosed {p : Y | P (f p) (g p)} := by
  have h : IsClosed ((fun p : Y => (f p, g p)) ⁻¹' {q : Bool × Bool | P q.1 q.2}) :=
    (isClosed_discrete _).preimage (hf.prodMk hg)
  exact h

theorem isClosed_range_prefixes :
    IsClosed (Set.range (prefixes : BoundaryWord ι → List ι → Bool)) := by
  rw [range_prefixes_eq]
  have c1 : IsClosed {p : List ι → Bool | p [] = true} :=
    isClosed_bool2 (fun p : List ι → Bool => p []) (fun p : List ι → Bool => p [])
      (continuous_apply []) (continuous_apply []) (fun a _ => a = true)
  have c2 : IsClosed {p : List ι → Bool |
      ∀ (μ : List ι) (i : ι), p (μ ++ [i]) = true → p μ = true} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter (fun μ => isClosed_iInter (fun i => ?_))
    exact isClosed_bool2 (fun p : List ι → Bool => p (μ ++ [i])) (fun p : List ι → Bool => p μ)
      (continuous_apply (μ ++ [i])) (continuous_apply μ) (fun a b => a = true → b = true)
  have c3 : IsClosed {p : List ι → Bool |
      ∀ (μ : List ι) (i j : ι), p (μ ++ [i]) = true → p (μ ++ [j]) = true → i = j} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter (fun μ => isClosed_iInter (fun i => isClosed_iInter (fun j => ?_)))
    exact isClosed_bool2 (fun p : List ι → Bool => p (μ ++ [i]))
      (fun p : List ι → Bool => p (μ ++ [j]))
      (continuous_apply (μ ++ [i])) (continuous_apply (μ ++ [j]))
      (fun a b => a = true → b = true → i = j)
  have c4 : IsClosed {p : List ι → Bool |
      Finite ι → ∀ μ : List ι, p μ = true → ∃ i : ι, p (μ ++ [i]) = true} := by
    by_cases hf : Finite ι
    · have e : {p : List ι → Bool |
          Finite ι → ∀ μ : List ι, p μ = true → ∃ i : ι, p (μ ++ [i]) = true} =
          ⋂ μ : List ι, ({p | p μ = false} ∪ ⋃ i : ι, {p | p (μ ++ [i]) = true}) := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_iUnion]
        constructor
        · intro h μ
          cases hp : p μ with
          | false => exact Or.inl rfl
          | true => exact Or.inr (h hf μ hp)
        · intro h _ μ hp
          rcases h μ with h' | h'
          · rw [hp] at h'
            cases h'
          · exact h'
      rw [e]
      refine isClosed_iInter (fun μ => IsClosed.union ?_ (isClosed_iUnion_of_finite (fun i => ?_)))
      · exact isClosed_bool2 (fun p : List ι → Bool => p μ) (fun p : List ι → Bool => p μ)
          (continuous_apply μ) (continuous_apply μ) (fun a _ => a = false)
      · exact isClosed_bool2 (fun p : List ι → Bool => p (μ ++ [i]))
          (fun p : List ι → Bool => p (μ ++ [i]))
          (continuous_apply (μ ++ [i])) (continuous_apply (μ ++ [i])) (fun a _ => a = true)
    · have e : {p : List ι → Bool |
          Finite ι → ∀ μ : List ι, p μ = true → ∃ i : ι, p (μ ++ [i]) = true} = Set.univ := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        intro h
        exact absurd h hf
      rw [e]
      exact isClosed_univ
  exact c1.inter (c2.inter (c3.inter c4))

instance compactSpace_boundaryWord : CompactSpace (BoundaryWord ι) := by
  have hi : Topology.IsInducing (prefixes : BoundaryWord ι → List ι → Bool) := ⟨rfl⟩
  refine ⟨?_⟩
  rw [hi.isCompact_iff, Set.image_univ]
  exact isClosed_range_prefixes.isCompact

/-! ## Arrows -/

/-- Prepend a finite word to the range of an arrow. -/
def catG (μ : List ι) (β : CuntzGroupoid ι) : CuntzGroupoid ι :=
  ⟨(cat μ β.1.1, β.1.2.1 + (μ.length : ℤ), β.1.2.2), by
    obtain ⟨m, n, hk, hx, hy, hs⟩ := β.2
    refine ⟨m + μ.length, n, ?_, ?_, hy, ?_⟩
    · show β.1.2.1 + (μ.length : ℤ) = ((m + μ.length : ℕ) : ℤ) - (n : ℤ)
      rw [hk]
      push_cast
      ring
    · intro k hk'
      show catFn μ β.1.1.1 k ≠ none
      by_cases h : k < μ.length
      · rw [catFn_lt _ _ _ h]
        exact Option.some_ne_none _
      · rw [catFn_ge _ _ _ h]
        exact hx _ (by omega)
    · intro k
      show catFn μ β.1.1.1 (k + (m + μ.length)) = β.1.2.2.1 (k + n)
      rw [← Nat.add_assoc, catFn_add]
      exact hs k⟩

theorem catG_injective (μ : List ι) (β β' : CuntzGroupoid ι) (h : catG μ β = catG μ β') :
    β = β' := by
  have h1 : cat μ β.1.1 = cat μ β'.1.1 := congrArg (fun g : CuntzGroupoid ι => g.1.1) h
  have h2 : β.1.2.1 + (μ.length : ℤ) = β'.1.2.1 + (μ.length : ℤ) :=
    congrArg (fun g : CuntzGroupoid ι => g.1.2.1) h
  have h3 : (catG μ β).1.2.2 = (catG μ β').1.2.2 := by rw [h]
  have h3 : β.1.2.2 = β'.1.2.2 := h3
  apply Subtype.ext
  exact Prod.ext (cat_injective μ _ _ h1) (Prod.ext (add_right_cancel h2) h3)

theorem catG_nil (β : CuntzGroupoid ι) : catG [] β = β := by
  apply Subtype.ext
  refine Prod.ext (cat_nil _) (Prod.ext ?_ rfl)
  show β.1.2.1 + ((0 : ℕ) : ℤ) = β.1.2.1
  rw [Nat.cast_zero, add_zero]

theorem catG_cons (i : ι) (μ : List ι) (β : CuntzGroupoid ι) :
    catG (i :: μ) β = catG [i] (catG μ β) := by
  apply Subtype.ext
  refine Prod.ext (cat_cons i μ _) (Prod.ext ?_ rfl)
  show β.1.2.1 + ((μ.length + 1 : ℕ) : ℤ) = β.1.2.1 + (μ.length : ℤ) + ((1 : ℕ) : ℤ)
  push_cast
  ring

theorem exists_catG (μ : List ι) (γ : CuntzGroupoid ι) (hp : prefixes γ.1.1 μ = true) :
    ∃ β : CuntzGroupoid ι, catG μ β = γ := by
  obtain ⟨m, n, hk, hx, hy, hs⟩ := γ.2
  have hmem : ∃ m' n' : ℕ, γ.1.2.1 - (μ.length : ℤ) = (m' : ℤ) - n' ∧
      LengthAtLeast (dropW μ.length γ.1.1) m' ∧ LengthAtLeast γ.1.2.2 n' ∧
      ∀ k, (dropW μ.length γ.1.1).1 (k + m') = γ.1.2.2.1 (k + n') := by
    by_cases hm : μ.length ≤ m
    · refine ⟨m - μ.length, n, ?_, ?_, hy, ?_⟩
      · omega
      · intro k hk'
        show γ.1.1.1 (k + μ.length) ≠ none
        exact hx _ (by omega)
      · intro k
        show γ.1.1.1 (k + (m - μ.length) + μ.length) = γ.1.2.2.1 (k + n)
        have e : k + (m - μ.length) + μ.length = k + m := by omega
        rw [e]
        exact hs k
    · refine ⟨0, n + (μ.length - m), ?_, ?_, ?_, ?_⟩
      · omega
      · intro k hk'
        exact absurd hk' (Nat.not_lt_zero k)
      · intro k hk'
        by_cases hkn : k < n
        · exact hy k hkn
        · have e : γ.1.2.2.1 k = γ.1.1.1 (k - n + m) := by
            rw [hs (k - n), Nat.sub_add_cancel (Nat.le_of_not_lt hkn)]
          rw [e, (prefixes_iff _ _).mp hp (k - n + m) (by omega)]
          exact Option.some_ne_none _
      · intro k
        show γ.1.1.1 (k + 0 + μ.length) = γ.1.2.2.1 (k + (n + (μ.length - m)))
        have e : k + 0 + μ.length = (k + (μ.length - m)) + m := by omega
        have e' : k + (n + (μ.length - m)) = (k + (μ.length - m)) + n := by omega
        rw [e, e']
        exact hs _
  refine ⟨⟨(dropW μ.length γ.1.1, γ.1.2.1 - (μ.length : ℤ), γ.1.2.2), hmem⟩, ?_⟩
  apply Subtype.ext
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · exact (cat_dropW γ.1.1 μ hp).symm
  · show γ.1.2.1 - (μ.length : ℤ) + (μ.length : ℤ) = γ.1.2.1
    ring

/-- The parametrisation of the basic bisection of a pair of finite words. -/
def phi (μ ν : List ι) (z : BoundaryWord ι) : CuntzGroupoid ι :=
  ⟨(cat μ z, (μ.length : ℤ) - (ν.length : ℤ), cat ν z), ⟨μ.length, ν.length, rfl,
    fun k hk => by
      show catFn μ z.1 k ≠ none
      rw [catFn_lt _ _ _ hk]
      exact Option.some_ne_none _,
    fun k hk => by
      show catFn ν z.1 k ≠ none
      rw [catFn_lt _ _ _ hk]
      exact Option.some_ne_none _,
    fun k => by
      show catFn μ z.1 (k + μ.length) = catFn ν z.1 (k + ν.length)
      rw [catFn_add, catFn_add]⟩⟩

/-- The basic bisection of a pair of finite words, as a set of triples. -/
def ZZ (μ ν : List ι) : Set (BoundaryWord ι × ℤ × BoundaryWord ι) :=
  {t | prefixes t.1 μ = true ∧ prefixes t.2.2 ν = true ∧
    t.2.1 = (μ.length : ℤ) - (ν.length : ℤ) ∧
    ∀ k, t.1.1 (k + μ.length) = t.2.2.1 (k + ν.length)}

theorem isOpen_ZZ (μ ν : List ι) : IsOpen {g : CuntzGroupoid ι | g.1 ∈ ZZ μ ν} := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  refine ⟨Zc μ, Zc ν, μ.length, ν.length, (isClopen_Zc μ).isOpen, (isClopen_Zc ν).isOpen,
    ?_, ?_, rfl⟩
  · intro x hx k hk
    rw [(prefixes_iff x μ).mp hx k hk]
    exact Option.some_ne_none _
  · intro x hx k hk
    rw [(prefixes_iff x ν).mp hx k hk]
    exact Option.some_ne_none _

theorem exists_ZZ (g : CuntzGroupoid ι) : ∃ p : List ι × List ι, g.1 ∈ ZZ p.1 p.2 := by
  obtain ⟨m, n, hk, hx, hy, hs⟩ := g.2
  obtain ⟨μ, hμ, hpμ⟩ := exists_prefix g.1.1 m hx
  obtain ⟨ν, hν, hpν⟩ := exists_prefix g.1.2.2 n hy
  refine ⟨(μ, ν), hpμ, hpν, ?_, ?_⟩
  · show g.1.2.1 = (μ.length : ℤ) - (ν.length : ℤ)
    rw [hμ, hν]
    exact hk
  · intro k
    show g.1.1.1 (k + μ.length) = g.1.2.2.1 (k + ν.length)
    rw [hμ, hν]
    exact hs k

theorem catFn_shift_indep (μ ν : List ι) (m n : ℕ)
    (hlag : (μ.length : ℤ) - (ν.length : ℤ) = (m : ℤ) - (n : ℤ))
    (w w' : ℕ → Option ι) (h : ∀ k, catFn μ w (k + m) = catFn ν w (k + n)) (k : ℕ) :
    catFn μ w' (k + m) = catFn ν w' (k + n) := by
  by_cases h1 : k + m < μ.length
  · have h2 : k + n < ν.length := by omega
    have hk := h k
    rw [catFn_lt μ w _ h1, catFn_lt ν w _ h2] at hk
    rw [catFn_lt μ w' _ h1, catFn_lt ν w' _ h2]
    exact hk
  · have h2 : ¬ k + n < ν.length := by omega
    rw [catFn_ge μ w' _ h1, catFn_ge ν w' _ h2]
    have e : k + m - μ.length = k + n - ν.length := by omega
    rw [e]

theorem phi_preimage (μ ν : List ι) (U V : Set (BoundaryWord ι)) (m n : ℕ) :
    phi μ ν ⁻¹' cylinderPair U V m n = cat μ ⁻¹' U ∩ cat ν ⁻¹' V ∨
      phi μ ν ⁻¹' cylinderPair U V m n = ∅ := by
  by_cases hC : (μ.length : ℤ) - (ν.length : ℤ) = (m : ℤ) - (n : ℤ) ∧
      ∃ z₀ : BoundaryWord ι, ∀ k, catFn μ z₀.1 (k + m) = catFn ν z₀.1 (k + n)
  · left
    obtain ⟨hlag, z₀, hz₀⟩ := hC
    ext z
    constructor
    · rintro ⟨hU, hV, -, -⟩
      exact ⟨hU, hV⟩
    · rintro ⟨hU, hV⟩
      exact ⟨hU, hV, hlag, catFn_shift_indep μ ν m n hlag z₀.1 z.1 hz₀⟩
  · right
    ext z
    constructor
    · rintro ⟨hU, hV, hlag, hall⟩
      exact hC ⟨hlag, z, hall⟩
    · intro h
      exact absurd h (Set.notMem_empty z)

theorem continuous_phi (μ ν : List ι) : Continuous (phi (ι := ι) μ ν) := by
  apply continuous_generateFrom_iff.2
  rintro _ ⟨U, V, m, n, hU, hV, -, -, rfl⟩
  rcases phi_preimage μ ν U V m n with h | h
  · rw [h]
    exact (hU.preimage (continuous_cat μ)).inter (hV.preimage (continuous_cat ν))
  · rw [h]
    exact isOpen_empty

theorem isClopen_phi_ZZ (μ' ν' μ ν : List ι) :
    IsClopen {z : BoundaryWord ι | (phi μ' ν' z).1 ∈ ZZ μ ν} := by
  have e : {z : BoundaryWord ι | (phi μ' ν' z).1 ∈ ZZ μ ν} =
      phi μ' ν' ⁻¹' cylinderPair (Zc μ) (Zc ν) μ.length ν.length := rfl
  rw [e]
  rcases phi_preimage μ' ν' (Zc μ) (Zc ν) μ.length ν.length with h | h
  · rw [h]
    exact ((isClopen_Zc μ).preimage (continuous_cat μ')).inter
      ((isClopen_Zc ν).preimage (continuous_cat ν'))
  · rw [h]
    exact isClopen_empty

/-! ## Point masses -/

/-- The point mass at an arrow. -/
noncomputable def dl (β : CuntzGroupoid ι) : L2 ι := lp.single 2 β (1 : ℂ)

theorem dl_apply (β γ : CuntzGroupoid ι) : dl β γ = if γ = β then 1 else 0 := by
  unfold dl
  rw [lp.single_apply, Pi.single_apply]

theorem l2_ext (f g : L2 ι) (h : ∀ γ, f γ = g γ) : f = g := lp.ext (funext h)

theorem l2_zero_apply (γ : CuntzGroupoid ι) : (0 : L2 ι) γ = 0 := rfl

theorem clm_ext (T T' : L2 ι →L[ℂ] L2 ι) (h : ∀ β, T (dl β) = T' (dl β)) : T = T' := by
  refine ContinuousLinearMap.ext (fun f => ?_)
  have hs := lp.hasSum_single (E := fun _ : CuntzGroupoid ι => ℂ) (p := 2) (by norm_num) f
  have e : ∀ i, lp.single (E := fun _ : CuntzGroupoid ι => ℂ) 2 i (f i) = f i • dl i := by
    intro i
    unfold dl
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  have h1 := hs.mapL T
  have h2 := hs.mapL T'
  have hfun : (fun i => T (lp.single 2 i (f i))) = fun i => T' (lp.single 2 i (f i)) := by
    funext i
    rw [e, map_smul, map_smul, h]
  rw [hfun] at h1
  exact h1.unique h2

theorem clm_ext_coeff (T T' : L2 ι →L[ℂ] L2 ι) (h : ∀ β γ, T (dl β) γ = T' (dl β) γ) : T = T' :=
  clm_ext T T' (fun β => l2_ext _ _ (h β))

theorem star_coeff (T : L2 ι →L[ℂ] L2 ι) (β γ : CuntzGroupoid ι) :
    (star T) (dl γ) β = starRingEnd ℂ (T (dl β) γ) := by
  have h1 : inner ℂ (dl β) ((star T) (dl γ)) = (star T) (dl γ) β := by
    have := lp.inner_single_left (𝕜 := ℂ) (G := fun _ : CuntzGroupoid ι => ℂ) β (1 : ℂ)
      ((star T) (dl γ))
    rw [RCLike.inner_apply, map_one, mul_one] at this
    exact this
  have h2 : inner ℂ (T (dl β)) (dl γ) = starRingEnd ℂ (T (dl β) γ) := by
    have := lp.inner_single_right (𝕜 := ℂ) (G := fun _ : CuntzGroupoid ι => ℂ) γ (1 : ℂ)
      (T (dl β))
    rw [RCLike.inner_apply, one_mul] at this
    exact this
  rw [← h1, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, h2]

/-! ## Kernels -/

/-- The operator has the given matrix entries: the entry from one arrow to another with the same
source is the kernel at the quotient arrow. -/
def HasKernel (K : BoundaryWord ι × ℤ × BoundaryWord ι → ℂ) (T : L2 ι →L[ℂ] L2 ι) : Prop :=
  ∀ β γ : CuntzGroupoid ι, T (dl β) γ =
    if γ.1.2.2 = β.1.2.2 then K (γ.1.1, γ.1.2.1 - β.1.2.1, β.1.1) else 0

theorem HasKernel.unique {K : BoundaryWord ι × ℤ × BoundaryWord ι → ℂ} {T T' : L2 ι →L[ℂ] L2 ι}
    (h : HasKernel K T) (h' : HasKernel K T') : T = T' :=
  clm_ext_coeff T T' (fun β γ => by rw [h β γ, h' β γ])

theorem hasKernel_zero (K : BoundaryWord ι × ℤ × BoundaryWord ι → ℂ) (hK : ∀ t, K t = 0)
    (T : L2 ι →L[ℂ] L2 ι) (hT : HasKernel K T) : T = 0 := by
  refine hT.unique (fun β γ => ?_)
  rw [hK, ite_self]
  rfl

theorem hasKernel_sub_peel (K : BoundaryWord ι × ℤ × BoundaryWord ι → ℂ)
    (Z : Set (BoundaryWord ι × ℤ × BoundaryWord ι)) (T W : L2 ι →L[ℂ] L2 ι)
    (hT : HasKernel K T) (hW : HasKernel (fun t => if t ∈ Z then K t else 0) W) :
    HasKernel (fun t => if t ∈ Z then 0 else K t) (T - W) := by
  intro β γ
  have e : (T - W) (dl β) γ = T (dl β) γ - W (dl β) γ := rfl
  rw [e, hT β γ, hW β γ]
  by_cases h1 : γ.1.2.2 = β.1.2.2
  · simp only [if_pos h1]
    by_cases h2 : (γ.1.1, γ.1.2.1 - β.1.2.1, β.1.1) ∈ Z
    · rw [if_pos h2, if_pos h2, sub_self]
    · rw [if_neg h2, if_neg h2, sub_zero]
  · simp only [if_neg h1]
    exact sub_zero 0

/-- Membership of a triple in the groupoid. -/
def InG (t : BoundaryWord ι × ℤ × BoundaryWord ι) : Prop :=
  ∃ m n : ℕ, t.2.1 = (m : ℤ) - n ∧ LengthAtLeast t.1 m ∧ LengthAtLeast t.2.2 n ∧
    ∀ k, t.1.1 (k + m) = t.2.2.1 (k + n)

/-- A function on the groupoid, extended by zero to all triples. -/
noncomputable def kerOf (f : CompactlySupportedContinuousMap (CuntzGroupoid ι) ℂ) :
    BoundaryWord ι × ℤ × BoundaryWord ι → ℂ :=
  fun t => if h : InG t then f (⟨t, h⟩ : CuntzGroupoid ι) else 0

theorem conv_index (β γ α : CuntzGroupoid ι)
    (h : α.1.2.2 = β.1.1 ∧ (α.1.1, α.1.2.1 + β.1.2.1, β.1.2.2) = γ.1) :
    α.1 = (γ.1.1, γ.1.2.1 - β.1.2.1, β.1.1) ∧ γ.1.2.2 = β.1.2.2 := by
  obtain ⟨h1, h2⟩ := h
  have e1 : α.1.1 = γ.1.1 := by rw [← h2]
  have e2 : α.1.2.1 + β.1.2.1 = γ.1.2.1 := by rw [← h2]
  have e3 : β.1.2.2 = γ.1.2.2 := by rw [← h2]
  refine ⟨Prod.ext e1 (Prod.ext ?_ h1), e3.symm⟩
  show α.1.2.1 = γ.1.2.1 - β.1.2.1
  rw [← e2]
  ring

theorem hasKernel_of_conv (f : CompactlySupportedContinuousMap (CuntzGroupoid ι) ℂ)
    (T : L2 ι →L[ℂ] L2 ι) (hT : IsConvolutionOperator f T) : HasKernel (kerOf f) T := by
  intro β γ
  have h0 : T (dl β) γ = ∑' α : {α : CuntzGroupoid ι //
      α.1.2.2 = β.1.1 ∧ (α.1.1, α.1.2.1 + β.1.2.1, β.1.2.2) = γ.1}, f α.1 := hT β γ
  rw [h0]
  by_cases hc : γ.1.2.2 = β.1.2.2 ∧ InG (γ.1.1, γ.1.2.1 - β.1.2.1, β.1.1)
  · obtain ⟨h1, h2⟩ := hc
    rw [if_pos h1]
    unfold kerOf
    rw [dif_pos h2]
    have hmem : (⟨(γ.1.1, γ.1.2.1 - β.1.2.1, β.1.1), h2⟩ : CuntzGroupoid ι).1.2.2 = β.1.1 ∧
        ((⟨(γ.1.1, γ.1.2.1 - β.1.2.1, β.1.1), h2⟩ : CuntzGroupoid ι).1.1,
          (⟨(γ.1.1, γ.1.2.1 - β.1.2.1, β.1.1), h2⟩ : CuntzGroupoid ι).1.2.1 + β.1.2.1,
          β.1.2.2) = γ.1 := by
      refine ⟨rfl, Prod.ext rfl (Prod.ext ?_ h1.symm)⟩
      show γ.1.2.1 - β.1.2.1 + β.1.2.1 = γ.1.2.1
      ring
    rw [tsum_eq_single (⟨⟨(γ.1.1, γ.1.2.1 - β.1.2.1, β.1.1), h2⟩, hmem⟩ : {α : CuntzGroupoid ι //
      α.1.2.2 = β.1.1 ∧ (α.1.1, α.1.2.1 + β.1.2.1, β.1.2.2) = γ.1})]
    intro α hα
    exfalso
    apply hα
    apply Subtype.ext
    apply Subtype.ext
    exact (conv_index β γ α.1 α.2).1
  · have hemp : IsEmpty {α : CuntzGroupoid ι //
        α.1.2.2 = β.1.1 ∧ (α.1.1, α.1.2.1 + β.1.2.1, β.1.2.2) = γ.1} := by
      refine ⟨fun α => hc ?_⟩
      obtain ⟨e1, e2⟩ := conv_index β γ α.1 α.2
      refine ⟨e2, ?_⟩
      rw [← e1]
      exact α.1.2
    rw [tsum_empty]
    by_cases h1 : γ.1.2.2 = β.1.2.2
    · rw [if_pos h1]
      unfold kerOf
      rw [dif_neg (fun h2 => hc ⟨h1, h2⟩)]
    · rw [if_neg h1]

/-! ## Words in the generators -/

/-- The product of the generators along a finite word. -/
noncomputable def Sw (S : ι → (L2 ι →L[ℂ] L2 ι)) : List ι → (L2 ι →L[ℂ] L2 ι)
  | [] => 1
  | i :: μ => S i * Sw S μ

theorem S_dl (S : ι → (L2 ι →L[ℂ] L2 ι)) (hS : IsStandardGenerators S) (i : ι)
    (β : CuntzGroupoid ι) : S i (dl β) = dl (catG [i] β) := by
  apply l2_ext
  intro γ
  rw [dl_apply]
  have h0 : S i (dl β) γ = if γ.1.1.1 = consFn i β.1.1.1 ∧ γ.1.2.1 = β.1.2.1 + 1 ∧
      γ.1.2.2 = β.1.2.2 then 1 else 0 := hS i β γ
  rw [h0]
  have hiff : (γ.1.1.1 = consFn i β.1.1.1 ∧ γ.1.2.1 = β.1.2.1 + 1 ∧ γ.1.2.2 = β.1.2.2) ↔
      γ = catG [i] β := by
    constructor
    · rintro ⟨h1, h2, h3⟩
      apply Subtype.ext
      refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ h3)
      · show γ.1.1.1 = catFn [i] β.1.1.1
        rw [catFn_cons, catFn_nil]
        exact h1
      · show γ.1.2.1 = β.1.2.1 + ((1 : ℕ) : ℤ)
        rw [h2, Nat.cast_one]
    · intro h
      rw [h]
      refine ⟨?_, ?_, rfl⟩
      · show catFn [i] β.1.1.1 = consFn i β.1.1.1
        rw [catFn_cons, catFn_nil]
      · show β.1.2.1 + ((1 : ℕ) : ℤ) = β.1.2.1 + 1
        rw [Nat.cast_one]
  by_cases h : γ = catG [i] β
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

theorem Sw_dl (S : ι → (L2 ι →L[ℂ] L2 ι)) (hS : IsStandardGenerators S) (μ : List ι)
    (β : CuntzGroupoid ι) : Sw S μ (dl β) = dl (catG μ β) := by
  induction μ with
  | nil =>
    show (1 : L2 ι →L[ℂ] L2 ι) (dl β) = dl (catG [] β)
    rw [catG_nil]
    rfl
  | cons i μ ih =>
    show S i (Sw S μ (dl β)) = dl (catG (i :: μ) β)
    rw [ih, S_dl S hS, ← catG_cons]

theorem star_Sw_dl_pos (S : ι → (L2 ι →L[ℂ] L2 ι)) (hS : IsStandardGenerators S) (ν : List ι)
    (β : CuntzGroupoid ι) : star (Sw S ν) (dl (catG ν β)) = dl β := by
  apply l2_ext
  intro β'
  rw [star_coeff, Sw_dl S hS, dl_apply, dl_apply]
  by_cases h : β' = β
  · rw [if_pos h, if_pos (by rw [h]), map_one]
  · rw [if_neg h, if_neg (fun h' => h (catG_injective ν _ _ h').symm), map_zero]

theorem star_Sw_dl_neg (S : ι → (L2 ι →L[ℂ] L2 ι)) (hS : IsStandardGenerators S) (ν : List ι)
    (γ : CuntzGroupoid ι) (h : ¬ ∃ β, catG ν β = γ) : star (Sw S ν) (dl γ) = 0 := by
  apply l2_ext
  intro β
  rw [star_coeff, Sw_dl S hS, dl_apply, if_neg (fun h' => h ⟨β, h'.symm⟩), map_zero]
  rfl

theorem Sw_mem (S : ι → (L2 ι →L[ℂ] L2 ι)) (A : StarSubalgebra ℂ (L2 ι →L[ℂ] L2 ι))
    (hSA : ∀ i, S i ∈ A) (μ : List ι) : Sw S μ ∈ A := by
  induction μ with
  | nil => exact one_mem A
  | cons i μ ih => exact mul_mem (hSA i) ih

theorem ZZ_iff (μ ν : List ι) (γ γ' : CuntzGroupoid ι) :
    (γ'.1.2.2 = γ.1.2.2 ∧ (γ'.1.1, γ'.1.2.1 - γ.1.2.1, γ.1.1) ∈ ZZ μ ν) ↔
      ∃ β, catG ν β = γ ∧ catG μ β = γ' := by
  constructor
  · rintro ⟨hy, hpμ, hpν, hlag, hs⟩
    obtain ⟨β, hβ⟩ := exists_catG ν γ hpν
    subst hβ
    refine ⟨β, rfl, ?_⟩
    apply Subtype.ext
    refine Prod.ext ?_ (Prod.ext ?_ hy.symm)
    · refine (eq_cat_of γ'.1.1 β.1.1 μ hpμ (fun j => ?_)).symm
      have := hs j
      rw [this]
      exact catFn_add ν β.1.1.1 j
    · have hl : γ'.1.2.1 - (β.1.2.1 + (ν.length : ℤ)) = (μ.length : ℤ) - (ν.length : ℤ) := hlag
      show β.1.2.1 + (μ.length : ℤ) = γ'.1.2.1
      linarith
  · rintro ⟨β, hβ, hβ'⟩
    subst hβ
    subst hβ'
    refine ⟨rfl, prefixes_cat μ _, prefixes_cat ν _, ?_, ?_⟩
    · show β.1.2.1 + (μ.length : ℤ) - (β.1.2.1 + (ν.length : ℤ)) =
        (μ.length : ℤ) - (ν.length : ℤ)
      ring
    · intro k
      show catFn μ β.1.1.1 (k + μ.length) = catFn ν β.1.1.1 (k + ν.length)
      rw [catFn_add, catFn_add]

/-! ## Diagonal operators -/

theorem diag_mem (a : CuntzGroupoid ι → ℂ) (C : ℝ) (ha : ∀ g, ‖a g‖ ≤ C) (ξ : L2 ι) :
    Memℓp (fun g => a g * ξ g) 2 := by
  have hξ := lp.memℓp ξ
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp] at hξ ⊢
  refine Summable.of_nonneg_of_le (fun g => Real.rpow_nonneg (norm_nonneg _) _) (fun g => ?_)
    (hξ.mul_left (C ^ (2 : ℝ≥0∞).toReal))
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (ha g) hp.le)
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem diag_norm_le (a : CuntzGroupoid ι → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ g, ‖a g‖ ≤ C)
    (ξ η : L2 ι) (hη : ∀ g, η g = a g * ξ g) : ‖η‖ ≤ C * ‖ξ‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  refine lp.norm_le_of_tsum_le hp (mul_nonneg hC (norm_nonneg ξ)) ?_
  have hξ := lp.memℓp ξ
  rw [memℓp_gen_iff hp] at hξ
  have hη' := lp.memℓp η
  rw [memℓp_gen_iff hp] at hη'
  rw [Real.mul_rpow hC (norm_nonneg ξ), lp.norm_rpow_eq_tsum hp ξ, ← tsum_mul_left]
  refine hη'.tsum_le_tsum (fun g => ?_) (hξ.mul_left (C ^ (2 : ℝ≥0∞).toReal))
  rw [hη g, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (ha g) hp.le)
    (Real.rpow_nonneg (norm_nonneg _) _)

/-- Multiplication by a continuous function of the range, as a linear map. -/
noncomputable def diagLin (h : C(BoundaryWord ι, ℂ)) : L2 ι →ₗ[ℂ] L2 ι where
  toFun ξ := ⟨fun g => h g.1.1 * ξ g,
    diag_mem (fun g => h g.1.1) ‖h‖ (fun g => h.norm_coe_le_norm g.1.1) ξ⟩
  map_add' ξ η := by
    apply l2_ext
    intro g
    show h g.1.1 * (ξ + η) g = h g.1.1 * ξ g + h g.1.1 * η g
    rw [lp.coeFn_add, Pi.add_apply, mul_add]
  map_smul' c ξ := by
    apply l2_ext
    intro g
    show h g.1.1 * (c • ξ) g = c * (h g.1.1 * ξ g)
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

/-- Multiplication by a continuous function of the range, as an operator. -/
noncomputable def diagOp (h : C(BoundaryWord ι, ℂ)) : L2 ι →L[ℂ] L2 ι :=
  (diagLin h).mkContinuous ‖h‖ (fun ξ =>
    diag_norm_le (fun g => h g.1.1) ‖h‖ (norm_nonneg h) (fun g => h.norm_coe_le_norm g.1.1) ξ
      (diagLin h ξ) (fun _ => rfl))

theorem diagOp_apply (h : C(BoundaryWord ι, ℂ)) (ξ : L2 ι) (g : CuntzGroupoid ι) :
    diagOp h ξ g = h g.1.1 * ξ g := rfl

/-- The diagonal operator, linear in the function. -/
noncomputable def Mlin : C(BoundaryWord ι, ℂ) →ₗ[ℂ] (L2 ι →L[ℂ] L2 ι) where
  toFun := diagOp
  map_add' h h' := by
    refine ContinuousLinearMap.ext (fun ξ => l2_ext _ _ (fun g => ?_))
    show (h + h') g.1.1 * ξ g = h g.1.1 * ξ g + h' g.1.1 * ξ g
    rw [ContinuousMap.add_apply, add_mul]
  map_smul' c h := by
    refine ContinuousLinearMap.ext (fun ξ => l2_ext _ _ (fun g => ?_))
    show (c • h) g.1.1 * ξ g = c * (h g.1.1 * ξ g)
    rw [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]

/-- The diagonal operator, continuous and linear in the function. -/
noncomputable def M : C(BoundaryWord ι, ℂ) →L[ℂ] (L2 ι →L[ℂ] L2 ι) :=
  Mlin.mkContinuous 1 (fun h => by
    rw [one_mul]
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg h) (fun ξ =>
      diag_norm_le (fun g => h g.1.1) ‖h‖ (norm_nonneg h) (fun g => h.norm_coe_le_norm g.1.1) ξ
        (diagOp h ξ) (fun _ => rfl)))

theorem M_apply (h : C(BoundaryWord ι, ℂ)) (ξ : L2 ι) (g : CuntzGroupoid ι) :
    M h ξ g = h g.1.1 * ξ g := rfl

theorem M_dl (h : C(BoundaryWord ι, ℂ)) (β : CuntzGroupoid ι) :
    M h (dl β) = h β.1.1 • dl β := by
  apply l2_ext
  intro g
  rw [M_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, dl_apply]
  by_cases hg : g = β
  · rw [hg]
  · rw [if_neg hg, mul_zero, mul_zero]

theorem M_mul (h h' : C(BoundaryWord ι, ℂ)) : M (h * h') = M h * M h' := by
  refine ContinuousLinearMap.ext (fun ξ => l2_ext _ _ (fun g => ?_))
  show (h * h') g.1.1 * ξ g = h g.1.1 * (h' g.1.1 * ξ g)
  rw [ContinuousMap.mul_apply, mul_assoc]

theorem M_one : M (1 : C(BoundaryWord ι, ℂ)) = 1 := by
  refine ContinuousLinearMap.ext (fun ξ => l2_ext _ _ (fun g => ?_))
  show (1 : C(BoundaryWord ι, ℂ)) g.1.1 * ξ g = ξ g
  rw [ContinuousMap.one_apply, one_mul]

theorem M_star (h : C(BoundaryWord ι, ℂ)) : M (star h) = star (M h) := by
  refine clm_ext_coeff _ _ (fun β γ => ?_)
  rw [star_coeff, M_dl, M_dl, lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply,
    smul_eq_mul, smul_eq_mul, dl_apply, dl_apply, map_mul, ContinuousMap.star_apply]
  by_cases hg : γ = β
  · rw [if_pos hg, if_pos hg.symm, hg, map_one]
    rfl
  · rw [if_neg hg, if_neg (fun h' => hg h'.symm), map_zero, mul_zero, mul_zero]

/-- The indicator of a cylinder, as a continuous function. -/
noncomputable def chi (μ : List ι) : C(BoundaryWord ι, ℂ) :=
  ⟨fun x => if prefixes x μ = true then 1 else 0,
    (continuous_of_discreteTopology (f := fun b : Bool => if b = true then (1 : ℂ) else 0)).comp
      (continuous_prefixes_apply μ)⟩

theorem chi_apply (μ : List ι) (x : BoundaryWord ι) :
    chi μ x = if prefixes x μ = true then 1 else 0 := rfl

theorem M_chi (S : ι → (L2 ι →L[ℂ] L2 ι)) (hS : IsStandardGenerators S) (μ : List ι) :
    M (chi μ) = Sw S μ * star (Sw S μ) := by
  refine clm_ext _ _ (fun γ => ?_)
  show M (chi μ) (dl γ) = Sw S μ (star (Sw S μ) (dl γ))
  rw [M_dl, chi_apply]
  by_cases hp : prefixes γ.1.1 μ = true
  · obtain ⟨β, hβ⟩ := exists_catG μ γ hp
    subst hβ
    rw [if_pos hp, one_smul, star_Sw_dl_pos S hS, Sw_dl S hS]
  · have hex : ¬ ∃ β, catG μ β = γ := by
      rintro ⟨β, hβ⟩
      apply hp
      rw [← hβ]
      exact prefixes_cat μ β.1.1
    rw [if_neg hp, zero_smul, star_Sw_dl_neg S hS μ γ hex, map_zero]

theorem M_mem (S : ι → (L2 ι →L[ℂ] L2 ι)) (hS : IsStandardGenerators S)
    (A : StarSubalgebra ℂ (L2 ι →L[ℂ] L2 ι)) (hA : IsClosed (A : Set (L2 ι →L[ℂ] L2 ι)))
    (hSA : ∀ i, S i ∈ A) (h : C(BoundaryWord ι, ℂ)) : M h ∈ A := by
  have hsep : (StarAlgebra.adjoin ℂ (Set.range (chi (ι := ι)))).SeparatesPoints := by
    intro x y hxy
    obtain ⟨μ, hμ⟩ : ∃ μ, prefixes x μ ≠ prefixes y μ := by
      by_contra hne
      refine hxy (prefixes_inj x y (fun μ => ?_))
      by_contra hμ
      exact hne ⟨μ, hμ⟩
    refine ⟨chi μ, ⟨chi μ, StarAlgebra.subset_adjoin ℂ _ ⟨μ, rfl⟩, rfl⟩, ?_⟩
    show chi μ x ≠ chi μ y
    rw [chi_apply, chi_apply]
    cases hx : prefixes x μ
    · cases hy : prefixes y μ
      · rw [hx, hy] at hμ
        exact absurd rfl hμ
      · simp
    · cases hy : prefixes y μ
      · simp
      · rw [hx, hy] at hμ
        exact absurd rfl hμ
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have hB : ∀ g ∈ StarAlgebra.adjoin ℂ (Set.range (chi (ι := ι))), M g ∈ A := by
    intro g hg
    induction hg using StarAlgebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨μ, rfl⟩ := hx
      rw [M_chi S hS]
      exact mul_mem (Sw_mem S A hSA μ) (star_mem (Sw_mem S A hSA μ))
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, map_smul, M_one]
      exact A.smul_mem (one_mem A) r
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [M_mul]
      exact mul_mem hx hy
    | star x _ hx =>
      rw [M_star]
      exact star_mem hx
  have hcl : IsClosed {g : C(BoundaryWord ι, ℂ) | M g ∈ A} := hA.preimage M.continuous
  have hmem : h ∈ (StarAlgebra.adjoin ℂ (Set.range (chi (ι := ι)))).topologicalClosure := by
    rw [htop]
    exact StarSubalgebra.mem_top
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe] at hmem
  exact closure_minimal (fun g hg => hB g hg) hcl hmem

/-! ## Peeling off one bisection at a time -/

theorem hasKernel_peel (S : ι → (L2 ι →L[ℂ] L2 ι)) (hS : IsStandardGenerators S)
    (K : BoundaryWord ι × ℤ × BoundaryWord ι → ℂ) (μ ν : List ι) (h : C(BoundaryWord ι, ℂ))
    (hh : ∀ z, h z = K (phi μ ν z).1) :
    HasKernel (fun t => if t ∈ ZZ μ ν then K t else 0) (Sw S μ * M h * star (Sw S ν)) := by
  intro γ γ'
  show Sw S μ (M h (star (Sw S ν) (dl γ))) γ' =
    if γ'.1.2.2 = γ.1.2.2 then
      (if (γ'.1.1, γ'.1.2.1 - γ.1.2.1, γ.1.1) ∈ ZZ μ ν then
        K (γ'.1.1, γ'.1.2.1 - γ.1.2.1, γ.1.1) else 0) else 0
  by_cases hex : ∃ β, catG ν β = γ
  · obtain ⟨β, hβ⟩ := hex
    subst hβ
    rw [star_Sw_dl_pos S hS, M_dl, map_smul, Sw_dl S hS, lp.coeFn_smul, Pi.smul_apply, dl_apply,
      smul_eq_mul]
    by_cases hγ' : γ' = catG μ β
    · subst hγ'
      have hz := (ZZ_iff μ ν (catG ν β) (catG μ β)).mpr ⟨β, rfl, rfl⟩
      rw [if_pos rfl, if_pos hz.1, if_pos hz.2, mul_one, hh]
      congr 1
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      show (μ.length : ℤ) - (ν.length : ℤ) =
        β.1.2.1 + (μ.length : ℤ) - (β.1.2.1 + (ν.length : ℤ))
      ring
    · rw [if_neg hγ', mul_zero]
      by_cases hy : γ'.1.2.2 = (catG ν β).1.2.2
      · rw [if_pos hy, if_neg]
        intro hz
        obtain ⟨β', e1, e2⟩ := (ZZ_iff μ ν (catG ν β) γ').mp ⟨hy, hz⟩
        have e3 := catG_injective ν _ _ e1
        subst e3
        exact hγ' e2.symm
      · rw [if_neg hy]
  · rw [star_Sw_dl_neg S hS ν γ hex, map_zero, map_zero, l2_zero_apply]
    by_cases hy : γ'.1.2.2 = γ.1.2.2
    · rw [if_pos hy, if_neg]
      intro hz
      obtain ⟨β', e1, -⟩ := (ZZ_iff μ ν γ γ').mp ⟨hy, hz⟩
      exact hex ⟨β', e1⟩
    · rw [if_neg hy]

theorem peel_induction (S : ι → (L2 ι →L[ℂ] L2 ι)) (hS : IsStandardGenerators S)
    (A : StarSubalgebra ℂ (L2 ι →L[ℂ] L2 ι)) (hA : IsClosed (A : Set (L2 ι →L[ℂ] L2 ι)))
    (hSA : ∀ i, S i ∈ A) (t : Finset (List ι × List ι)) :
    ∀ K : BoundaryWord ι × ℤ × BoundaryWord ι → ℂ,
      (∀ μ ν : List ι, Continuous (fun z => K (phi μ ν z).1)) →
      (∀ τ, K τ ≠ 0 → ∃ p ∈ t, τ ∈ ZZ p.1 p.2) →
      ∀ T : L2 ι →L[ℂ] L2 ι, HasKernel K T → T ∈ A := by
  induction t using Finset.induction_on with
  | empty =>
    intro K _ hsupp T hT
    have hK : ∀ τ, K τ = 0 := by
      intro τ
      by_contra hne
      obtain ⟨p, hp, -⟩ := hsupp τ hne
      exact absurd hp (Finset.notMem_empty p)
    rw [hasKernel_zero K hK T hT]
    exact zero_mem A
  | insert p t hp ih =>
    intro K hcont hsupp T hT
    obtain ⟨μ, ν⟩ := p
    have hW : Sw S μ * M ⟨fun z => K (phi μ ν z).1, hcont μ ν⟩ * star (Sw S ν) ∈ A :=
      mul_mem (mul_mem (Sw_mem S A hSA μ) (M_mem S hS A hA hSA _)) (star_mem (Sw_mem S A hSA ν))
    have hWk := hasKernel_peel S hS K μ ν ⟨fun z => K (phi μ ν z).1, hcont μ ν⟩ (fun z => rfl)
    have hsub := hasKernel_sub_peel K (ZZ μ ν) T _ hT hWk
    have hTW := ih (fun τ => if τ ∈ ZZ μ ν then 0 else K τ) (fun μ' ν' => by
        show Continuous (fun z => if (phi μ' ν' z).1 ∈ ZZ μ ν then (0 : ℂ) else K (phi μ' ν' z).1)
        refine Continuous.if (fun a ha => ?_) continuous_const (hcont μ' ν')
        have hfr := (isClopen_phi_ZZ μ' ν' μ ν).frontier_eq
        rw [hfr] at ha
        exact absurd ha (Set.notMem_empty a)) (fun τ hτ => by
        by_cases hz : τ ∈ ZZ μ ν
        · rw [if_pos hz] at hτ
          exact absurd rfl hτ
        · rw [if_neg hz] at hτ
          obtain ⟨q, hq, hτq⟩ := hsupp τ hτ
          rcases Finset.mem_insert.mp hq with hq' | hq'
          · rw [hq'] at hτq
            exact absurd hτq hz
          · exact ⟨q, hq', hτq⟩) _ hsub
    have e : T = (T - Sw S μ * M ⟨fun z => K (phi μ ν z).1, hcont μ ν⟩ * star (Sw S ν)) +
        Sw S μ * M ⟨fun z => K (phi μ ν z).1, hcont μ ν⟩ * star (Sw S ν) :=
      (sub_add_cancel _ _).symm
    rw [e]
    exact add_mem hTW hW

theorem conv_mem (S : ι → (L2 ι →L[ℂ] L2 ι)) (hS : IsStandardGenerators S)
    (A : StarSubalgebra ℂ (L2 ι →L[ℂ] L2 ι)) (hA : IsClosed (A : Set (L2 ι →L[ℂ] L2 ι)))
    (hSA : ∀ i, S i ∈ A) (f : CompactlySupportedContinuousMap (CuntzGroupoid ι) ℂ)
    (T : L2 ι →L[ℂ] L2 ι) (hT : IsConvolutionOperator f T) : T ∈ A := by
  have hc : IsCompact (tsupport f) := f.hasCompactSupport
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover
    (fun p : List ι × List ι => {g : CuntzGroupoid ι | g.1 ∈ ZZ p.1 p.2})
    (fun p => isOpen_ZZ p.1 p.2)
    (fun g _ => by
      obtain ⟨p, hp⟩ := exists_ZZ g
      exact Set.mem_iUnion.mpr ⟨p, hp⟩)
  refine peel_induction S hS A hA hSA t (kerOf f) (fun μ ν => ?_) (fun τ hτ => ?_) T
    (hasKernel_of_conv f T hT)
  · have e : (fun z => kerOf f (phi μ ν z).1) = fun z => f (phi μ ν z) := by
      funext z
      have hz : InG (phi μ ν z).1 := (phi μ ν z).2
      unfold kerOf
      rw [dif_pos hz]
      rfl
    rw [e]
    exact f.continuous.comp (continuous_phi μ ν)
  · unfold kerOf at hτ
    by_cases hG : InG τ
    · rw [dif_pos hG] at hτ
      have hmem := ht (subset_tsupport f hτ)
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hpt, hp'⟩ := Set.mem_iUnion.mp hp
      exact ⟨p, hpt, hp'⟩
    · rw [dif_neg hG] at hτ
      exact absurd rfl hτ

end Gen

/-- The standard generators generate the reduced algebra, for every alphabet. -/
theorem generation (ι : Type) (S : ι → reducedAlgebra ι)
    (hS : IsStandardGenerators (fun i => (S i : L2 ι →L[ℂ] L2 ι))) :
    (StarAlgebra.adjoin ℂ (Set.range fun i => (S i : L2 ι →L[ℂ] L2 ι))).topologicalClosure =
      reducedAlgebra ι := by
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_minimal
    · rw [StarAlgebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact (S i).2
    · exact StarSubalgebra.isClosed_topologicalClosure _
  · unfold reducedAlgebra
    apply StarSubalgebra.topologicalClosure_minimal
    · rw [StarAlgebra.adjoin_le_iff]
      rintro T ⟨f, hf⟩
      exact Gen.conv_mem _ hS _ (StarSubalgebra.isClosed_topologicalClosure _)
        (fun i => StarSubalgebra.le_topologicalClosure _
          (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self i))) f T hf
    · exact StarSubalgebra.isClosed_topologicalClosure _

/-- The standard generators generate the reduced algebra, finitely many letters. -/
theorem generation_fin (n : ℕ) (_hn : 1 ≤ n) (S : Fin n → reducedAlgebra (Fin n))
    (hS : IsStandardGenerators (fun i => (S i : L2 (Fin n) →L[ℂ] L2 (Fin n)))) :
    (StarAlgebra.adjoin ℂ
      (Set.range fun i => (S i : L2 (Fin n) →L[ℂ] L2 (Fin n)))).topologicalClosure =
      reducedAlgebra (Fin n) :=
  generation (Fin n) S hS

/-- The standard generators generate the reduced algebra, countably many letters. -/
theorem generation_nat (S : ℕ → reducedAlgebra ℕ)
    (hS : IsStandardGenerators (fun i => (S i : L2 ℕ →L[ℂ] L2 ℕ))) :
    (StarAlgebra.adjoin ℂ (Set.range fun i => (S i : L2 ℕ →L[ℂ] L2 ℕ))).topologicalClosure =
      reducedAlgebra ℕ :=
  generation ℕ S hS

end OMA.S_mo_448788

-- ===== MO448788/Final =====
namespace OMA.S_mo_448788

/-- The one missing piece: the standard generators produce the whole reduced algebra. -/
def GenerationHyp (ι : Type) : Prop :=
  ∀ S : ι → reducedAlgebra ι, IsStandardGenerators (fun i => (S i : L2 ι →L[ℂ] L2 ι)) →
    (StarAlgebra.adjoin ℂ (Set.range fun i => (S i : L2 ι →L[ℂ] L2 ι))).topologicalClosure =
      reducedAlgebra ι

theorem main_of_generation (hf : ∀ n : ℕ, 1 ≤ n → GenerationHyp (Fin n)) (hN : GenerationHyp ℕ) :
    (∀ n : ℕ, 1 ≤ n → IsGroupoidModel (Fin n)) ∧ IsGroupoidModel ℕ := by
  constructor
  · intro n hn
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨S, hS, hc⟩ := standard_generators (Fin n)
    have hg := hf n hn S hS
    rcases Nat.lt_or_ge 1 n with h | h
    · haveI := reducedAlgebra_nontrivial (Fin n)
      exact model_fin n h S hc hg
    · obtain rfl : n = 1 := by omega
      exact model_fin_one S hS hg hc
  · obtain ⟨S, hS, hc⟩ := standard_generators ℕ
    haveI := reducedAlgebra_nontrivial ℕ
    exact model_of_keyFact ℕ cuntzKeyFact_nat S hc (hN S hS)

end OMA.S_mo_448788

-- ===== MO448788/Main =====
namespace OMA.S_mo_448788

theorem main_proved : (∀ n : ℕ, 1 ≤ n → IsGroupoidModel (Fin n)) ∧ IsGroupoidModel ℕ :=
  main_of_generation (fun n _ => generation (Fin n)) (generation ℕ)

end OMA.S_mo_448788

theorem OMA.solution : type_of% @OMA.S_mo_448788.main := OMA.S_mo_448788.main_proved
