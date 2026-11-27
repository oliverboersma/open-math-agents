import OMAStatements.S_mo_480222

/-!
# mo-480222: single-file candidate (all Core files + Reduction merged)

Local build version: the first import is the local statement module. For submission replace the first
line by the upstream statement module import and nothing else.
-/

-- ===== CoreAlg =====
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

-- ===== CoreSpan =====
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

-- ===== CoreSpec =====
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

-- ===== CoreInt =====
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

-- ===== CoreCfc =====
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

-- ===== CoreCircle =====
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

-- ===== Reduction =====
/-!
# mo-480222: reduction of the whole statement to one key fact

KeyFact: in a unital C*-algebra generated by Cuntz isometries, every nonzero w has some z
with z * (star w * w) * star z = 1. From it we prove the full statement OMA.S_mo_480222.main.
-/

namespace OMA.S_mo_480222.Reduction

open Filter Topology Matrix

/-- The one key fact the whole statement is reduced to. -/
def KeyFact : Prop :=
  ∀ (n : ℕ), 1 < n → ∀ (A : Type) [CStarAlgebra A] [Nontrivial A] (s : Fin n → A),
    (∀ i, star (s i) * s i = 1) → ∑ i, s i * star (s i) = 1 →
    (StarAlgebra.adjoin ℂ (Set.range s)).topologicalClosure = ⊤ →
    ∀ w : A, w ≠ 0 → ∃ z : A, z * (star w * w) * star z = 1

/-- The Cuntz isometries have orthogonal ranges. -/
theorem cuntz_orthogonal {A : Type*} [CStarAlgebra A] {n : ℕ} (s : Fin n → A)
    (hs : ∀ i, star (s i) * s i = 1) (hsum : ∑ i, s i * star (s i) = 1)
    (i j : Fin n) (hij : i ≠ j) : star (s i) * s j = 0 := by
  let _ := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have h1 : ∑ l, (star (s i) * s l) * star (star (s i) * s l) = 1 := by
    have h : star (s i) * (∑ l, s l * star (s l)) * s i = 1 := by rw [hsum, mul_one, hs]
    rw [← h, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [star_mul, star_star, mul_assoc]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hs i, one_mul, star_one,
    add_eq_left] at h1
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun l _ => mul_star_self_nonneg (star (s i) * s l))).1 h1 j (by simp [hij.symm])
  exact (CStarRing.mul_star_self_eq_zero_iff _).1 h2

theorem star_pow_mul_pow {A : Type*} [Ring A] [StarRing A] (u : A) (hu : star u * u = 1) :
    ∀ p r : ℕ, star (u ^ p) * u ^ (p + r) = u ^ r
  | 0, r => by simp
  | p + 1, r => by
    have e : u ^ (p + 1 + r) = u * u ^ (p + r) := by
      rw [show p + 1 + r = (p + r) + 1 by omega, pow_succ']
    rw [e, pow_succ', star_mul, mul_assoc, ← mul_assoc (star u), hu, one_mul,
      star_pow_mul_pow u hu p r]

/-- Two isometries with orthogonal ranges give an infinite orthonormal family. -/
theorem isometry_family {A : Type*} [Ring A] [StarRing A] (u v : A)
    (hu : star u * u = 1) (hv : star v * v = 1) (huv : star u * v = 0) (p q : ℕ) :
    star (u ^ p * v) * (u ^ q * v) = if p = q then 1 else 0 := by
  have hvu : star v * u = 0 := by
    have := congrArg star huv
    simpa [star_mul] using this
  have lt : ∀ p q : ℕ, p < q → star (u ^ p * v) * (u ^ q * v) = 0 := by
    intro p q hpq
    obtain ⟨r, rfl⟩ : ∃ r, q = p + (r + 1) := ⟨q - p - 1, by omega⟩
    have e : star (u ^ p * v) * (u ^ (p + (r + 1)) * v)
        = star v * (star (u ^ p) * u ^ (p + (r + 1))) * v := by
      simp only [star_mul, mul_assoc]
    rw [e, star_pow_mul_pow u hu, pow_succ', ← mul_assoc, hvu, zero_mul, zero_mul]
  rcases lt_trichotomy p q with h | rfl | h
  · rw [lt p q h, if_neg h.ne]
  · have e : star (u ^ p * v) * (u ^ p * v) = star v * (star (u ^ p) * u ^ (p + 0)) * v := by
      simp only [star_mul, mul_assoc, add_zero]
    rw [e, star_pow_mul_pow u hu, pow_zero, mul_one, hv, if_pos rfl]
  · have := congrArg star (lt q p h)
    rw [star_mul, star_star, star_zero] at this
    rw [this, if_neg h.ne']

/-- Reverse direction: nothing nonzero is below the zero matrix. -/
theorem cuntzLE_imp {A : Type*} [CStarAlgebra A] {k m : ℕ}
    (a : Matrix (Fin k) (Fin k) A) (b : Matrix (Fin m) (Fin m) A) (h : CuntzLE a b) :
    a = 0 ∨ b ≠ 0 := by
  by_cases hb : b = 0
  · left
    obtain ⟨x, hx⟩ := h
    subst hb
    simp only [Matrix.mul_zero, Matrix.zero_mul] at hx
    exact tendsto_nhds_unique hx tendsto_const_nhds
  · exact Or.inr hb

/-- The zero matrix is below everything. -/
theorem cuntzLE_zero_left {A : Type*} [CStarAlgebra A] {k m : ℕ}
    (b : Matrix (Fin m) (Fin m) A) : CuntzLE (0 : Matrix (Fin k) (Fin k) A) b :=
  ⟨fun _ => 0, by simp only [Matrix.zero_mul]; exact tendsto_const_nhds⟩

/-- Forward direction for nonzero b, given an orthonormal family and the key fact. -/
theorem cuntzLE_of_ne_zero {A : Type*} [CStarAlgebra A] (t : ℕ → A)
    (ht : ∀ p q, star (t p) * t q = if p = q then 1 else 0)
    (hkey : ∀ w : A, w ≠ 0 → ∃ z : A, z * (star w * w) * star z = 1)
    {k m : ℕ} (a : Matrix (Fin k) (Fin k) A) (b : Matrix (Fin m) (Fin m) A)
    (ha : IsPositiveMatrix a) (hb : IsPositiveMatrix b) (hb0 : b ≠ 0) : CuntzLE a b := by
  obtain ⟨g, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  obtain ⟨p0, q, hpq⟩ : ∃ p q, y p q ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    apply hb0
    have : y = 0 := by ext p q; exact hc p q
    simp [this]
  set w : A := ∑ p : Fin m, t p * y p q with hwdef
  have hw : ∀ p' : Fin m, star (t p') * w = y p' q := by
    intro p'
    rw [hwdef, Finset.mul_sum]
    simp only [← mul_assoc, ht, Fin.val_inj, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hw0 : w ≠ 0 := fun h => hpq (by rw [← hw p0, h, mul_zero])
  have hww : star w * w = (yᴴ * y) q q := by
    rw [Matrix.mul_apply]
    conv_lhs => rw [hwdef, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [star_mul, mul_assoc, ← hwdef, hw, Matrix.conjTranspose_apply]
  obtain ⟨z, hz⟩ := hkey w hw0
  set B := yᴴ * y with hB
  let c : Fin k → A := fun i => ∑ l : Fin k, star (g l i) * star (t l)
  have hc : ∀ i i', c i * star (c i') = ∑ j, star (g j i) * g j i' := by
    intro i i'
    have e : ∀ j l : Fin k, star (g j i) * star (t j) * (t l * g l i')
        = if j = l then star (g j i) * g l i' else 0 := by
      intro j l
      rw [mul_assoc, ← mul_assoc (star (t j)), ht]
      by_cases h : j = l <;> simp [h, Fin.val_inj]
    simp only [c, star_sum, star_mul, star_star, Finset.sum_mul, Finset.mul_sum, e]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  let x : Matrix (Fin k) (Fin m) A := Matrix.of fun i j => if j = q then c i * z else 0
  have key : x * B * xᴴ = gᴴ * g := by
    ext i i'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, x, Matrix.of_apply, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, apply_ite star, star_zero, mul_ite, mul_zero]
    rw [← hc, star_mul, ← hww]
    calc c i * z * (star w * w) * (star z * star (c i'))
        = c i * (z * (star w * w) * star z) * star (c i') := by
          simp only [mul_assoc]
      _ = c i * star (c i') := by rw [hz, mul_one]
  exact ⟨fun _ => x, by simp only [key]; exact tendsto_const_nhds⟩

/-- The whole statement follows from the key fact. -/
theorem main_of_keyFact (h : KeyFact) : type_of% @OMA.S_mo_480222.main := by
  intro n hn A _ _ s hs hsum hgen k m a b ha hb
  constructor
  · exact cuntzLE_imp a b
  · rintro (rfl | hb0)
    · exact cuntzLE_zero_left b
    · have hkey := h n hn A s hs hsum hgen
      have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, hn⟩ := by simp [Fin.ext_iff]
      exact cuntzLE_of_ne_zero (fun p => s ⟨0, by omega⟩ ^ p * s ⟨1, hn⟩)
        (isometry_family _ _ (hs _) (hs _) (cuntz_orthogonal s hs hsum _ _ h01))
        hkey a b ha hb hb0

end OMA.S_mo_480222.Reduction

theorem OMA.solution : type_of% @OMA.S_mo_480222.main :=
  OMA.S_mo_480222.Reduction.main_of_keyFact OMA.S_mo_480222.key_fact
