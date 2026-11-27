import OMAReductions.R_IrvingLeather_irving_leather_pow_two_R1
import Mathlib.Tactic

-- Step IrvingLeather.irving_leather_pow_two.R1.H1: hypothesis H1 of reduction IrvingLeather.irving_leather_pow_two.R1
-- Credit: @tatashbar
-- Lower bound a_k <= M(2^k) via the XOR profile (man m ranks w at m xor w, woman w ranks m at
-- 2^k - 1 - (m xor w)). Three families of stable matchings, each a product of two copies of the
-- half-size XOR profile (split by the top bit, by the flipped top bit, and by top-xor-second bit),
-- give 3 s_{k+1}^2 <= s_{k+2} + 2 s_k^4 by inclusion-exclusion; a ratio induction then gives
-- a_k <= s_k.
-- The statement is the same as step H2 of the reduction R1 of the growth-rate problem, and the
-- Lean development below (namespace ILGH2) is the one written for that step by a parallel
-- lefttosolve session of the same owner (session 8). The third family and the ratio induction
-- come from this session (session 12).

open StableMarriage IrvingLeather

namespace ILGH2

/-! ## Bit lemmas -/

lemma xor_split (x y j : ℕ) :
    x ^^^ y = 2 ^ j * ((x / 2 ^ j) ^^^ (y / 2 ^ j)) + ((x % 2 ^ j) ^^^ (y % 2 ^ j)) := by
  rw [← Nat.xor_div_two_pow, ← Nat.xor_mod_two_pow, Nat.div_add_mod]

lemma div_mk {j h l : ℕ} (hl : l < 2 ^ j) : (2 ^ j * h + l) / 2 ^ j = h := by
  have hp : 0 < 2 ^ j := by positivity
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hl, Nat.zero_add]

lemma mod_mk {j h l : ℕ} (hl : l < 2 ^ j) : (2 ^ j * h + l) % 2 ^ j = l := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]

lemma xor_mk {j h h' l l' : ℕ} (hl : l < 2 ^ j) (hl' : l' < 2 ^ j) :
    (2 ^ j * h + l) ^^^ (2 ^ j * h' + l') = 2 ^ j * (h ^^^ h') + (l ^^^ l') := by
  rw [xor_split _ _ j, div_mk hl, div_mk hl', mod_mk hl, mod_mk hl']

lemma xor_cancel_right {a b c : ℕ} (h : a ^^^ c = b ^^^ c) : a = b := by
  have := congrArg (· ^^^ c) h
  simpa [Nat.xor_assoc] using this

/-! ## The XOR profile -/

/-- Translation by `m` in the group `(Fin (2^k), xor)`. -/
def xperm {k : ℕ} (m : Fin (2 ^ k)) : Equiv.Perm (Fin (2 ^ k)) where
  toFun w := m ^^^ w
  invFun w := m ^^^ w
  left_inv w := by ext; simp
  right_inv w := by ext; simp

/-- The XOR profile: man `m` ranks woman `w` at `m xor w`, woman `w` ranks man `m` at
`2^k - 1 - (m xor w)`. -/
def X (k : ℕ) : Profile (2 ^ k) where
  manRank m := xperm m
  womanRank w := (xperm w).trans Fin.revPerm

lemma isStable_X_iff {k : ℕ} (μ : Matching (2 ^ k)) :
    IsStable (X k) μ ↔ ∀ m w : Fin (2 ^ k), μ m ≠ w →
      m.val ^^^ w.val < m.val ^^^ (μ m).val →
        (μ.symm w).val ^^^ w.val < m.val ^^^ w.val → False := by
  have hm : ∀ m w w' : Fin (2 ^ k), (X k).manRank m w < (X k).manRank m w' ↔
      m.val ^^^ w.val < m.val ^^^ w'.val := by
    intro m w w'
    show (m ^^^ w) < (m ^^^ w') ↔ _
    rw [Fin.lt_def, Fin.xor_val_of_two_pow, Fin.xor_val_of_two_pow]
  have hw : ∀ w m m' : Fin (2 ^ k), (X k).womanRank w m < (X k).womanRank w m' ↔
      m'.val ^^^ w.val < m.val ^^^ w.val := by
    intro w m m'
    show Fin.rev (w ^^^ m) < Fin.rev (w ^^^ m') ↔ _
    rw [Fin.rev_lt_rev, Fin.lt_def, Fin.xor_val_of_two_pow, Fin.xor_val_of_two_pow,
      Nat.xor_comm w.val, Nat.xor_comm w.val]
  unfold IsStable IsBlockingPair
  simp only [hm, hw]
  constructor
  · intro h m w h1 h2 h3
    exact h m w ⟨h1, h2, h3⟩
  · rintro h m w ⟨h1, h2, h3⟩
    exact h m w h1 h2 h3

/-! ## Splitting a market of size `2^(k+1)` into two copies of size `2^k` -/

section Split

variable {k : ℕ}

/-- Men are `fA (i, a)`, women are `fB (i, b)`; inside block `i` the xor shifts by `c`,
across blocks it leaves the window `[c, c + 2^k)`. -/
def SplitOK (fA fB : Bool × Fin (2 ^ k) → Fin (2 ^ (k + 1))) (c : ℕ) : Prop :=
  (∀ i a b, (fA (i, a)).val ^^^ (fB (i, b)).val = (a.val ^^^ b.val) + c) ∧
  (∀ i a b, (fA (i, a)).val ^^^ (fB (!i, b)).val < c ∨
      c + 2 ^ k ≤ (fA (i, a)).val ^^^ (fB (!i, b)).val)

lemma SplitOK.injA {fA fB : Bool × Fin (2 ^ k) → Fin (2 ^ (k + 1))} {c : ℕ}
    (h : SplitOK fA fB c) : Function.Injective fA := by
  rintro ⟨i, a⟩ ⟨i', a'⟩ he
  have b : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
  by_cases hi : i = i'
  · subst hi
    have h1 := h.1 i a b
    have h2 := h.1 i a' b
    rw [he] at h1
    have h3 : a.val ^^^ b.val = a'.val ^^^ b.val := by omega
    have h4 := xor_cancel_right h3
    rw [Fin.val_inj] at h4
    rw [h4]
  · have hi' : i' = !i := by cases i <;> cases i' <;> simp_all
    subst hi'
    have h1 := h.1 i a b
    have h2 := h.2 (!i) a' b
    rw [Bool.not_not, ← he] at h2
    have hb := Nat.xor_lt_two_pow a.isLt b.isLt
    omega

lemma SplitOK.injB {fA fB : Bool × Fin (2 ^ k) → Fin (2 ^ (k + 1))} {c : ℕ}
    (h : SplitOK fA fB c) : Function.Injective fB := by
  rintro ⟨j, b⟩ ⟨j', b'⟩ he
  have a : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
  by_cases hj : j = j'
  · subst hj
    have h1 := h.1 j a b
    have h2 := h.1 j a b'
    rw [he] at h1
    have h3 : b.val ^^^ a.val = b'.val ^^^ a.val := by
      rw [Nat.xor_comm b.val, Nat.xor_comm b'.val]; omega
    have h4 := xor_cancel_right h3
    rw [Fin.val_inj] at h4
    rw [h4]
  · have hj' : j' = !j := by cases j <;> cases j' <;> simp_all
    subst hj'
    have h1 := h.1 j a b
    have h2 := h.2 j a b'
    rw [← he] at h2
    have hb := Nat.xor_lt_two_pow a.isLt b.isLt
    omega

/-- An injective map `Bool × Fin (2^k) → Fin (2^(k+1))` is a bijection. -/
noncomputable def mkEquiv (f : Bool × Fin (2 ^ k) → Fin (2 ^ (k + 1)))
    (hf : Function.Injective f) : Bool × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
  Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hf, by rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin,
      pow_succ, mul_comm]⟩)

/-- The matching that uses `ν i` inside block `i`. -/
noncomputable def prodM (A B : Bool × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)))
    (ν : Bool → Equiv.Perm (Fin (2 ^ k))) : Equiv.Perm (Fin (2 ^ (k + 1))) :=
  A.symm.trans ((Equiv.prodShear (Equiv.refl Bool) ν).trans B)

lemma prodM_apply (A B : Bool × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)))
    (ν : Bool → Equiv.Perm (Fin (2 ^ k))) (i : Bool) (a : Fin (2 ^ k)) :
    prodM A B ν (A (i, a)) = B (i, ν i a) := by
  simp [prodM, Equiv.prodShear]

lemma prodM_symm_apply (A B : Bool × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)))
    (ν : Bool → Equiv.Perm (Fin (2 ^ k))) (i : Bool) (b : Fin (2 ^ k)) :
    (prodM A B ν).symm (B (i, b)) = A (i, (ν i).symm b) := by
  rw [Equiv.symm_apply_eq, prodM_apply, Equiv.apply_symm_apply]

lemma prodM_injective (A B : Bool × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1))) :
    Function.Injective (prodM A B) := by
  intro ν ν' he
  funext i
  refine Equiv.ext fun a => ?_
  have := congrArg (fun f => f (A (i, a))) he
  simp only [prodM_apply] at this
  simpa using B.injective this

lemma stable_prodM {A B : Bool × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1))} {c : ℕ}
    (h : SplitOK A B c) {ν : Bool → Equiv.Perm (Fin (2 ^ k))}
    (hν : ∀ i, IsStable (X k) (ν i)) : IsStable (X (k + 1)) (prodM A B ν) := by
  rw [isStable_X_iff]
  intro m w hne h1 h2
  obtain ⟨⟨i, a⟩, rfl⟩ := A.surjective m
  obtain ⟨⟨j, b⟩, rfl⟩ := B.surjective w
  rw [prodM_apply] at hne h1
  rw [prodM_symm_apply] at h2
  have e1 := h.1 i a (ν i a)
  have hb1 := Nat.xor_lt_two_pow a.isLt (ν i a).isLt
  by_cases hij : i = j
  · subst hij
    have e2 := h.1 i ((ν i).symm b) b
    have e3 := h.1 i a b
    rw [e1, e3] at h1
    rw [e2, e3] at h2
    exact (isStable_X_iff _).1 (hν i) a b (fun hh => hne (by rw [hh])) (by omega) (by omega)
  · have hj : j = !i := by cases i <;> cases j <;> simp_all
    subst hj
    have e2 := h.1 (!i) ((ν (!i)).symm b) b
    rcases h.2 i a b with hc | hc <;> omega

lemma stable_of_prodM {A B : Bool × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1))} {c : ℕ}
    (h : SplitOK A B c) {ν : Bool → Equiv.Perm (Fin (2 ^ k))}
    (hst : IsStable (X (k + 1)) (prodM A B ν)) (i : Bool) : IsStable (X k) (ν i) := by
  rw [isStable_X_iff]
  intro a b hne h1 h2
  refine (isStable_X_iff _).1 hst (A (i, a)) (B (i, b)) ?_ ?_ ?_
  · rw [prodM_apply]
    intro hh
    exact hne (by simpa using B.injective hh)
  · rw [prodM_apply, h.1, h.1]
    omega
  · rw [prodM_symm_apply, h.1, h.1]
    omega

lemma exists_prodM {A B : Bool × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1))} {c : ℕ}
    (h : SplitOK A B c) (μ : Equiv.Perm (Fin (2 ^ (k + 1))))
    (hμ : ∀ m, c ≤ m.val ^^^ (μ m).val ∧ m.val ^^^ (μ m).val < c + 2 ^ k) :
    ∃ ν, μ = prodM A B ν := by
  have key : ∀ i a, ∃ b, μ (A (i, a)) = B (i, b) := by
    intro i a
    obtain ⟨⟨j, b⟩, hjb⟩ := B.surjective (μ (A (i, a)))
    by_cases hij : i = j
    · subst hij
      exact ⟨b, hjb.symm⟩
    · have hj : j = !i := by cases i <;> cases j <;> simp_all
      subst hj
      have := hμ (A (i, a))
      rw [← hjb] at this
      rcases h.2 i a b with hc | hc <;> omega
  choose g hg using key
  have ginj : ∀ i, Function.Injective (g i) := by
    intro i a a' he
    have h1 := hg i a
    rw [he, ← hg i a'] at h1
    simpa using A.injective (μ.injective h1)
  refine ⟨fun i => Equiv.ofBijective (g i) (Finite.injective_iff_bijective.mp (ginj i)), ?_⟩
  refine Equiv.ext fun m => ?_
  obtain ⟨⟨i, a⟩, rfl⟩ := A.surjective m
  rw [prodM_apply]
  simpa using hg i a

end Split

/-! ## Counting -/

/-- Stable matchings of `X k` all of whose differences `m xor μ m` satisfy `P`. -/
noncomputable def St (k : ℕ) (P : ℕ → Prop) : Finset (Equiv.Perm (Fin (2 ^ k))) := by
  classical
  exact Finset.univ.filter
    (fun μ => IsStable (X k) μ ∧ ∀ m : Fin (2 ^ k), P (m.val ^^^ (μ m).val))

lemma mem_St {k : ℕ} {P : ℕ → Prop} {μ : Equiv.Perm (Fin (2 ^ k))} :
    μ ∈ St k P ↔ IsStable (X k) μ ∧ ∀ m : Fin (2 ^ k), P (m.val ^^^ (μ m).val) := by
  classical
  unfold St
  rw [Finset.mem_filter]
  simp

lemma card_St_split {k : ℕ} {A B : Bool × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1))} {c : ℕ}
    (h : SplitOK A B c) (P J : ℕ → Prop) (hJ : ∀ x, J x → x < 2 ^ k)
    (hPJ : ∀ x, P x ↔ c ≤ x ∧ J (x - c)) :
    (St (k + 1) P).card = (St k J).card ^ 2 := by
  classical
  have himg : St (k + 1) P =
      (Fintype.piFinset fun _ : Bool => St k J).image (prodM A B) := by
    ext μ
    simp only [Finset.mem_image, Fintype.mem_piFinset, mem_St]
    constructor
    · rintro ⟨hst, hP⟩
      have hr : ∀ m, c ≤ m.val ^^^ (μ m).val ∧ m.val ^^^ (μ m).val < c + 2 ^ k := by
        intro m
        have h1 := (hPJ _).1 (hP m)
        have h2 := hJ _ h1.2
        omega
      obtain ⟨ν, rfl⟩ := exists_prodM h μ hr
      refine ⟨ν, fun i => ⟨stable_of_prodM h hst i, fun a => ?_⟩, rfl⟩
      have h1 := (hPJ _).1 (hP (A (i, a)))
      rw [prodM_apply, h.1] at h1
      simpa using h1.2
    · rintro ⟨ν, hν, rfl⟩
      refine ⟨stable_prodM h (fun i => (hν i).1), fun m => ?_⟩
      obtain ⟨⟨i, a⟩, rfl⟩ := A.surjective m
      rw [prodM_apply, h.1, hPJ]
      refine ⟨by omega, ?_⟩
      simpa using (hν i).2 a
  rw [himg, Finset.card_image_of_injective _ (prodM_injective A B), Fintype.card_piFinset,
    Fintype.prod_bool, sq]

/-! ## The three concrete splits -/

def f1 {j : ℕ} : Bool × Fin (2 ^ j) → Fin (2 ^ (j + 1))
  | (i, a) => ⟨2 ^ j * i.toNat + a.val, by
      have := a.isLt
      cases i <;> simp [pow_succ] <;> omega⟩

lemma f1_val {j : ℕ} (i : Bool) (a : Fin (2 ^ j)) : (f1 (i, a)).val = 2 ^ j * i.toNat + a.val :=
  rfl

lemma split1 (j : ℕ) : SplitOK (f1 (j := j)) f1 0 := by
  refine ⟨fun i a b => ?_, fun i a b => ?_⟩
  · rw [f1_val, f1_val, xor_mk a.isLt b.isLt, Nat.xor_self]
    simp
  · right
    rw [f1_val, f1_val, xor_mk a.isLt b.isLt]
    cases i <;> simp

lemma split2 (j : ℕ) : SplitOK (f1 (j := j)) (fun p => f1 (!p.1, p.2)) (2 ^ j) := by
  refine ⟨fun i a b => ?_, fun i a b => ?_⟩
  · simp only
    rw [f1_val, f1_val, xor_mk a.isLt b.isLt]
    cases i <;> simp <;> omega
  · left
    simp only [Bool.not_not]
    rw [f1_val, f1_val, xor_mk a.isLt b.isLt, Nat.xor_self]
    simpa using Nat.xor_lt_two_pow a.isLt b.isLt

lemma div_lt_two {k : ℕ} (a : Fin (2 ^ (k + 1))) : a.val / 2 ^ k < 2 := by
  have h : a.val < 2 ^ k * 2 := by rw [← pow_succ]; exact a.isLt
  exact Nat.div_lt_of_lt_mul h

lemma bit_lt_two (i : Bool) {t : ℕ} (ht : t < 2) : i.toNat ^^^ t < 2 := by
  have hi : i.toNat < 2 ^ 1 := by cases i <;> simp
  exact Nat.xor_lt_two_pow (n := 1) hi (by simpa using ht)

lemma low3_lt {k : ℕ} (i : Bool) (a : Fin (2 ^ (k + 1))) :
    2 ^ k * (i.toNat ^^^ (a.val / 2 ^ k)) + a.val % 2 ^ k < 2 ^ (k + 1) := by
  have h1 := bit_lt_two i (div_lt_two a)
  have h2 : a.val % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  generalize i.toNat ^^^ (a.val / 2 ^ k) = u at *
  interval_cases u <;> simp [pow_succ] <;> omega

def f3 {k : ℕ} : Bool × Fin (2 ^ (k + 1)) → Fin (2 ^ (k + 1 + 1))
  | (i, a) => ⟨2 ^ (k + 1) * (a.val / 2 ^ k) +
      (2 ^ k * (i.toNat ^^^ (a.val / 2 ^ k)) + a.val % 2 ^ k), by
      have h1 := div_lt_two a
      have h2 := low3_lt i a
      have hp : 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
      generalize 2 ^ k * (i.toNat ^^^ (a.val / 2 ^ k)) + a.val % 2 ^ k = l at *
      generalize a.val / 2 ^ k = t at *
      interval_cases t <;> omega⟩

lemma f3_val {k : ℕ} (i : Bool) (a : Fin (2 ^ (k + 1))) : (f3 (i, a)).val =
    2 ^ (k + 1) * (a.val / 2 ^ k) + (2 ^ k * (i.toNat ^^^ (a.val / 2 ^ k)) + a.val % 2 ^ k) :=
  rfl

lemma f3_xor {k : ℕ} (i i' : Bool) (a b : Fin (2 ^ (k + 1))) :
    (f3 (i, a)).val ^^^ (f3 (i', b)).val =
      2 ^ (k + 1) * ((a.val / 2 ^ k) ^^^ (b.val / 2 ^ k)) +
        (2 ^ k * ((i.toNat ^^^ (a.val / 2 ^ k)) ^^^ (i'.toNat ^^^ (b.val / 2 ^ k))) +
          ((a.val % 2 ^ k) ^^^ (b.val % 2 ^ k))) := by
  rw [f3_val, f3_val, xor_mk (low3_lt i a) (low3_lt i' b),
    xor_mk (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.mod_lt _ (Nat.two_pow_pos k))]

lemma split3 (k : ℕ) : SplitOK (f3 (k := k)) (fun p => f3 (!p.1, p.2)) (2 ^ k) := by
  refine ⟨fun i a b => ?_, fun i a b => ?_⟩
  · simp only
    rw [f3_xor, xor_split a.val b.val k]
    have ha := div_lt_two a
    have hb := div_lt_two b
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    generalize a.val / 2 ^ k = t at *
    generalize b.val / 2 ^ k = t' at *
    generalize (a.val % 2 ^ k) ^^^ (b.val % 2 ^ k) = x
    interval_cases t <;> interval_cases t' <;> cases i <;> simp <;> omega
  · simp only [Bool.not_not]
    rw [f3_xor]
    have ha := div_lt_two a
    have hb := div_lt_two b
    have hx : (a.val % 2 ^ k) ^^^ (b.val % 2 ^ k) < 2 ^ k :=
      Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.mod_lt _ (Nat.two_pow_pos k))
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    generalize a.val / 2 ^ k = t at *
    generalize b.val / 2 ^ k = t' at *
    generalize (a.val % 2 ^ k) ^^^ (b.val % 2 ^ k) = x at *
    interval_cases t <;> interval_cases t' <;> cases i <;> simp <;> omega

noncomputable def A1 (j : ℕ) : Bool × Fin (2 ^ j) ≃ Fin (2 ^ (j + 1)) :=
  mkEquiv f1 (split1 j).injA

noncomputable def B2 (j : ℕ) : Bool × Fin (2 ^ j) ≃ Fin (2 ^ (j + 1)) :=
  mkEquiv (fun p => f1 (!p.1, p.2)) (split2 j).injB

noncomputable def A3 (k : ℕ) : Bool × Fin (2 ^ (k + 1)) ≃ Fin (2 ^ (k + 1 + 1)) :=
  mkEquiv f3 (split3 k).injA

noncomputable def B3 (k : ℕ) : Bool × Fin (2 ^ (k + 1)) ≃ Fin (2 ^ (k + 1 + 1)) :=
  mkEquiv (fun p => f3 (!p.1, p.2)) (split3 k).injB

lemma ok1 (j : ℕ) : SplitOK (A1 j) (A1 j) 0 := split1 j
lemma ok2 (j : ℕ) : SplitOK (A1 j) (B2 j) (2 ^ j) := split2 j
lemma ok3 (k : ℕ) : SplitOK (A3 k) (B3 k) (2 ^ k) := split3 k

/-! ## The recursion -/

/-- The number of stable matchings of the XOR profile of size `2^k`. -/
noncomputable def s (k : ℕ) : ℕ := (St k (fun x => x < 2 ^ k)).card

lemma St_sub_all {k : ℕ} (P : ℕ → Prop) : St k P ⊆ St k (fun x => x < 2 ^ k) := by
  intro μ hμ
  rw [mem_St] at hμ ⊢
  exact ⟨hμ.1, fun m => Nat.xor_lt_two_pow m.isLt (μ m).isLt⟩

lemma s_zero_pos : 1 ≤ s 0 := by
  classical
  have h1 : (1 : Equiv.Perm (Fin (2 ^ 0))) ∈ St 0 (fun x => x < 2 ^ 0) := by
    rw [mem_St]
    refine ⟨?_, fun m => Nat.xor_lt_two_pow m.isLt (Fin.isLt _)⟩
    rw [isStable_X_iff]
    intro m w hne
    exact absurd (Fin.ext (by
      have h1 := ((1 : Equiv.Perm (Fin (2 ^ 0))) m).isLt
      have h2 := w.isLt
      simp only [pow_zero] at h1 h2
      omega)) hne
  exact Finset.card_pos.mpr ⟨_, h1⟩

lemma s_double (k : ℕ) : 2 * s k ^ 2 ≤ s (k + 1) := by
  classical
  set F1 := St (k + 1) (fun x => 0 ≤ x ∧ x - 0 < 2 ^ k)
  set F2 := St (k + 1) (fun x => 2 ^ k ≤ x ∧ x - 2 ^ k < 2 ^ k)
  have c1 : F1.card = s k ^ 2 :=
    card_St_split (ok1 k) _ (fun x => x < 2 ^ k) (fun _ h => h) (fun _ => Iff.rfl)
  have c2 : F2.card = s k ^ 2 :=
    card_St_split (ok2 k) _ (fun x => x < 2 ^ k) (fun _ h => h) (fun _ => Iff.rfl)
  have hd : Disjoint F1 F2 := by
    rw [Finset.disjoint_left]
    intro μ h1 h2
    rw [mem_St] at h1 h2
    have := (h1.2 ⟨0, Nat.two_pow_pos _⟩)
    have := (h2.2 ⟨0, Nat.two_pow_pos _⟩)
    omega
  have hsub : F1 ∪ F2 ⊆ St (k + 1) (fun x => x < 2 ^ (k + 1)) :=
    Finset.union_subset (St_sub_all _) (St_sub_all _)
  have hU := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at hU
  have hs1 : s (k + 1) = (St (k + 1) (fun x => x < 2 ^ (k + 1))).card := rfl
  omega

lemma s_rec (k : ℕ) : 3 * s (k + 1) ^ 2 ≤ s (k + 2) + 2 * s k ^ 4 := by
  classical
  set F1 := St (k + 1 + 1) (fun x => 0 ≤ x ∧ x - 0 < 2 ^ (k + 1))
  set F2 := St (k + 1 + 1) (fun x => 2 ^ (k + 1) ≤ x ∧ x - 2 ^ (k + 1) < 2 ^ (k + 1))
  set F3 := St (k + 1 + 1) (fun x => 2 ^ k ≤ x ∧ x - 2 ^ k < 2 ^ (k + 1))
  set G13 := St (k + 1 + 1) (fun x => 0 ≤ x ∧ (2 ^ k ≤ x - 0 ∧ x - 0 - 2 ^ k < 2 ^ k))
  set G23 := St (k + 1 + 1) (fun x => 2 ^ (k + 1) ≤ x ∧ (0 ≤ x - 2 ^ (k + 1) ∧
    x - 2 ^ (k + 1) - 0 < 2 ^ k))
  have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
  have c1 : F1.card = s (k + 1) ^ 2 :=
    card_St_split (ok1 (k + 1)) _ (fun x => x < 2 ^ (k + 1)) (fun _ h => h) (fun _ => Iff.rfl)
  have c2 : F2.card = s (k + 1) ^ 2 :=
    card_St_split (ok2 (k + 1)) _ (fun x => x < 2 ^ (k + 1)) (fun _ h => h) (fun _ => Iff.rfl)
  have c3 : F3.card = s (k + 1) ^ 2 :=
    card_St_split (ok3 k) _ (fun x => x < 2 ^ (k + 1)) (fun _ h => h) (fun _ => Iff.rfl)
  have c13 : G13.card = (s k ^ 2) ^ 2 := by
    rw [card_St_split (ok1 (k + 1)) _ (fun x => 2 ^ k ≤ x ∧ x - 2 ^ k < 2 ^ k)
      (fun x h => by omega) (fun _ => Iff.rfl)]
    rw [card_St_split (ok2 k) _ (fun x => x < 2 ^ k) (fun _ h => h) (fun _ => Iff.rfl)]
    rfl
  have c23 : G23.card = (s k ^ 2) ^ 2 := by
    rw [card_St_split (ok2 (k + 1)) _ (fun x => 0 ≤ x ∧ x - 0 < 2 ^ k)
      (fun x h => by omega) (fun _ => Iff.rfl)]
    rw [card_St_split (ok1 k) _ (fun x => x < 2 ^ k) (fun _ h => h) (fun _ => Iff.rfl)]
    rfl
  have hd : Disjoint F1 F2 := by
    rw [Finset.disjoint_left]
    intro μ h1 h2
    rw [mem_St] at h1 h2
    have := (h1.2 ⟨0, Nat.two_pow_pos _⟩)
    have := (h2.2 ⟨0, Nat.two_pow_pos _⟩)
    omega
  have h13 : F1 ∩ F3 ⊆ G13 := by
    intro μ hμ
    rw [Finset.mem_inter, mem_St, mem_St] at hμ
    rw [mem_St]
    refine ⟨hμ.1.1, fun m => ?_⟩
    have := hμ.1.2 m
    have := hμ.2.2 m
    omega
  have h23 : F2 ∩ F3 ⊆ G23 := by
    intro μ hμ
    rw [Finset.mem_inter, mem_St, mem_St] at hμ
    rw [mem_St]
    refine ⟨hμ.1.1, fun m => ?_⟩
    have := hμ.1.2 m
    have := hμ.2.2 m
    omega
  have hsub : F1 ∪ F2 ∪ F3 ⊆ St (k + 1 + 1) (fun x => x < 2 ^ (k + 1 + 1)) :=
    Finset.union_subset (Finset.union_subset (St_sub_all _) (St_sub_all _)) (St_sub_all _)
  have hU := Finset.card_le_card hsub
  have hIE := Finset.card_union_add_card_inter (F1 ∪ F2) F3
  have h12 := Finset.card_union_of_disjoint hd
  have hI : ((F1 ∪ F2) ∩ F3).card ≤ G13.card + G23.card := by
    rw [Finset.union_inter_distrib_right]
    exact (Finset.card_union_le _ _).trans
      (add_le_add (Finset.card_le_card h13) (Finset.card_le_card h23))
  have e4 : s k ^ 4 = (s k ^ 2) ^ 2 := by ring
  have hs2 : s (k + 2) = (St (k + 1 + 1) (fun x => x < 2 ^ (k + 1 + 1))).card := rfl
  omega

/-! ## Comparison with the Irving–Leather recurrence -/

lemma il_succ_succ (k : ℕ) :
    irvingLeatherCount (k + 1 + 1) =
      3 * irvingLeatherCount (k + 1) ^ 2 - 2 * irvingLeatherCount k ^ 4 := rfl

lemma il_bounds (k : ℕ) :
    1 ≤ irvingLeatherCount k ∧ 2 * irvingLeatherCount k ^ 2 ≤ irvingLeatherCount (k + 1) := by
  induction k with
  | zero => simp [irvingLeatherCount]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hy4 : 2 * irvingLeatherCount k ^ 4 ≤ irvingLeatherCount (k + 1) ^ 2 := by
      have : 2 * irvingLeatherCount k ^ 2 * (2 * irvingLeatherCount k ^ 2) ≤
          irvingLeatherCount (k + 1) * irvingLeatherCount (k + 1) := Nat.mul_le_mul h2 h2
      nlinarith
    refine ⟨by nlinarith, ?_⟩
    rw [il_succ_succ]
    apply Nat.le_sub_of_add_le
    linarith

lemma main_ineq : ∀ k : ℕ, irvingLeatherCount k ≤ s k ∧
    irvingLeatherCount (k + 1) ≤ s (k + 1) ∧
    irvingLeatherCount (k + 1) * s k ^ 2 ≤ s (k + 1) * irvingLeatherCount k ^ 2
  | 0 => by
    have h0 := s_zero_pos
    have h1 := s_double 0
    have h2 : 1 ≤ s 0 ^ 2 := Nat.one_le_pow _ _ h0
    have a0 : irvingLeatherCount 0 = 1 := rfl
    have a1 : irvingLeatherCount (0 + 1) = 2 := rfl
    rw [a0, a1]
    refine ⟨h0, by omega, by simp only [one_pow, mul_one]; omega⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3⟩ := main_ineq k
    refine ⟨h2, ?_⟩
    have hrec := s_rec k
    have hb := il_bounds k
    have hC : irvingLeatherCount (k + 1 + 1) + 2 * irvingLeatherCount k ^ 4 =
        3 * irvingLeatherCount (k + 1) ^ 2 := by
      rw [il_succ_succ]
      have : 2 * irvingLeatherCount k ^ 4 ≤ 3 * irvingLeatherCount (k + 1) ^ 2 := by
        have := Nat.mul_le_mul hb.2 hb.2
        nlinarith
      omega
    generalize irvingLeatherCount k = A at *
    generalize irvingLeatherCount (k + 1) = B at *
    generalize irvingLeatherCount (k + 1 + 1) = C at *
    generalize s k = S at *
    generalize s (k + 1) = T at *
    generalize s (k + 2) = U at *
    have f1 : (B * S ^ 2) ^ 2 ≤ (T * A ^ 2) ^ 2 := Nat.pow_le_pow_left h3 2
    have f2 : 3 * T ^ 2 * B ^ 2 ≤ (U + 2 * S ^ 4) * B ^ 2 := Nat.mul_le_mul_right _ hrec
    have f3 : C * T ^ 2 + 2 * A ^ 4 * T ^ 2 = 3 * B ^ 2 * T ^ 2 := by
      rw [← add_mul, hC]
    have key : C * T ^ 2 ≤ U * B ^ 2 := by
      have e1 : (B * S ^ 2) ^ 2 = S ^ 4 * B ^ 2 := by ring
      have e2 : (T * A ^ 2) ^ 2 = A ^ 4 * T ^ 2 := by ring
      have e3 : (U + 2 * S ^ 4) * B ^ 2 = U * B ^ 2 + 2 * (S ^ 4 * B ^ 2) := by ring
      have e4 : 3 * T ^ 2 * B ^ 2 = 3 * B ^ 2 * T ^ 2 := by ring
      have e5 : 2 * A ^ 4 * T ^ 2 = 2 * (A ^ 4 * T ^ 2) := by ring
      rw [e1, e2] at f1
      rw [e3, e4] at f2
      rw [e5] at f3
      omega
    have hBpos : 0 < B ^ 2 := by
      have : 0 < B := by nlinarith [hb.1]
      positivity
    have hBT : B ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left h2 2
    refine ⟨?_, ?_⟩
    · have : C * B ^ 2 ≤ U * B ^ 2 := (Nat.mul_le_mul_left _ hBT).trans key
      exact Nat.le_of_mul_le_mul_right this hBpos
    · simpa [mul_comm] using key

/-! ## The lower bound -/

lemma s_le_max (k : ℕ) : s k ≤ maxStableMatchings (2 ^ k) := by
  classical
  have h1 : s k ≤ numStableMatchings (X k) := by
    unfold s numStableMatchings
    rw [Fintype.card_subtype]
    apply Finset.card_le_card
    intro μ hμ
    rw [mem_St] at hμ
    simpa using hμ.1
  exact h1.trans (Finset.le_sup (f := fun p => numStableMatchings p) (Finset.mem_univ (X k)))

theorem il_lower : ∀ k : ℕ, irvingLeatherCount k ≤ maxStableMatchings (2 ^ k) :=
  fun k => (main_ineq k).1.trans (s_le_max k)

end ILGH2

theorem OMA.solution : OMA.R_IrvingLeather_irving_leather_pow_two_R1.H1 :=
  ILGH2.il_lower
