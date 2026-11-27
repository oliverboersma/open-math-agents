import FormalConjectures.Arxiv.«2607.08630».BalisterGyoriSchelp

/-!
# The Balister–Győri–Schelp Conjecture

Shared definitions and core lemmas for the proof of the Balister–Győri–Schelp conjecture
following Aryeh Lev Zabokritskiy (arXiv:2611.32557).
-/

open scoped BigOperators

namespace OMA.BGS

/- ### 1. Basic `𝔽₂ s` dot product, symplectic form, and sign -/

def dot2 {s : ℕ} (a b : 𝔽₂ s) : ZMod 2 :=
  ∑ r : Fin s, a r * b r

def symp {s : ℕ} (u v : 𝔽₂ s × 𝔽₂ s) : ZMod 2 :=
  dot2 u.2 v.1 + dot2 v.2 u.1

def sign2 (c : ZMod 2) : ℚ :=
  if c = 0 then 1 else -1

lemma zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  fin_cases c <;> decide

lemma zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 :=
  match c with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl

lemma vec_add_self {s : ℕ} (x : 𝔽₂ s) : x + x = 0 := by
  ext r; exact zmod2_add_self (x r)

lemma dot2_zero_left {s : ℕ} (b : 𝔽₂ s) : dot2 0 b = 0 := by
  simp [dot2]

lemma dot2_zero_right {s : ℕ} (a : 𝔽₂ s) : dot2 a 0 = 0 := by
  simp [dot2]

lemma dot2_add_left {s : ℕ} (a₁ a₂ b : 𝔽₂ s) : dot2 (a₁ + a₂) b = dot2 a₁ b + dot2 a₂ b := by
  simp [dot2, add_mul, Finset.sum_add_distrib]

lemma dot2_add_right {s : ℕ} (a b₁ b₂ : 𝔽₂ s) : dot2 a (b₁ + b₂) = dot2 a b₁ + dot2 a b₂ := by
  simp [dot2, mul_add, Finset.sum_add_distrib]

lemma dot2_comm {s : ℕ} (a b : 𝔽₂ s) : dot2 a b = dot2 b a := by
  simp [dot2, mul_comm]

lemma dot2_single_left {s : ℕ} (j : Fin s) (x : 𝔽₂ s) : dot2 (Pi.single j 1) x = x j := by
  simp [dot2, Pi.single_apply]

lemma dot2_single_right {s : ℕ} (x : 𝔽₂ s) (j : Fin s) : dot2 x (Pi.single j 1) = x j := by
  rw [dot2_comm, dot2_single_left]

lemma dot2_sum_left {s : ℕ} {ι : Type*} (S : Finset ι) (f : ι → 𝔽₂ s) (b : 𝔽₂ s) :
    dot2 (∑ i ∈ S, f i) b = ∑ i ∈ S, dot2 (f i) b := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [dot2_zero_left]
  | insert a S ha ih => simp [Finset.sum_insert ha, dot2_add_left, ih]

lemma dot2_sum_right {s : ℕ} {ι : Type*} (a : 𝔽₂ s) (S : Finset ι) (f : ι → 𝔽₂ s) :
    dot2 a (∑ i ∈ S, f i) = ∑ i ∈ S, dot2 a (f i) := by
  rw [dot2_comm, dot2_sum_left]; exact Finset.sum_congr rfl fun _ _ => dot2_comm _ _

lemma symp_symm {s : ℕ} (u v : 𝔽₂ s × 𝔽₂ s) : symp u v = symp v u := by
  simp [symp, add_comm]

lemma symp_self {s : ℕ} (u : 𝔽₂ s × 𝔽₂ s) : symp u u = 0 := by
  exact zmod2_add_self (dot2 u.2 u.1)

lemma symp_zero_left {s : ℕ} (v : 𝔽₂ s × 𝔽₂ s) : symp 0 v = 0 := by
  simp [symp, dot2_zero_left, dot2_zero_right]

lemma symp_zero_right {s : ℕ} (u : 𝔽₂ s × 𝔽₂ s) : symp u 0 = 0 := by
  simp [symp, dot2_zero_left, dot2_zero_right]

lemma symp_add_left {s : ℕ} (u₁ u₂ v : 𝔽₂ s × 𝔽₂ s) :
    symp (u₁ + u₂) v = symp u₁ v + symp u₂ v := by
  simp only [symp, Prod.fst_add, Prod.snd_add, dot2_add_left, dot2_add_right]
  ring

lemma symp_add_right {s : ℕ} (u v₁ v₂ : 𝔽₂ s × 𝔽₂ s) :
    symp u (v₁ + v₂) = symp u v₁ + symp u v₂ := by
  rw [symp_symm, symp_add_left, symp_symm v₁, symp_symm v₂]

lemma symp_fst_zero {s : ℕ} (δ a β : 𝔽₂ s) : symp (δ, 0) (a, β) = dot2 β δ := by
  simp [symp, dot2_zero_left]

lemma sign2_zero : sign2 0 = 1 := by decide
lemma sign2_one : sign2 1 = -1 := by decide

lemma sign2_add (a b : ZMod 2) : sign2 (a + b) = sign2 a * sign2 b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    simp [sign2_zero, sign2_one, zmod2_add_self]

lemma sign2_mul_self (a : ZMod 2) : sign2 a * sign2 a = 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> norm_num [sign2_zero, sign2_one]

lemma sign2_ne_zero (a : ZMod 2) : sign2 a ≠ 0 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> norm_num [sign2_zero, sign2_one]

lemma sign2_eq_one_or_neg_one (a : ZMod 2) : sign2 a = 1 ∨ sign2 a = -1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> simp [sign2_zero, sign2_one]

/- ### 2. Coordinate height, even basis, functionals, and label classes -/

lemma vecHeight_support_nonempty {s : ℕ} {v : 𝔽₂ s} (hv : v ≠ 0) :
    (Finset.univ.filter fun j : Fin s => v j ≠ 0).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply hv; ext j
  have hj : j ∉ Finset.univ.filter (fun j : Fin s => v j ≠ 0) := by rw [h]; simp
  simpa using hj

def vecHeight {s : ℕ} (v : 𝔽₂ s) (hv : v ≠ 0) : Fin s :=
  (Finset.univ.filter fun j : Fin s => v j ≠ 0).max' (vecHeight_support_nonempty hv)

lemma vecHeight_apply {s : ℕ} {v : 𝔽₂ s} (hv : v ≠ 0) : v (vecHeight v hv) = 1 := by
  have hmem := Finset.max'_mem (Finset.univ.filter fun j : Fin s => v j ≠ 0)
    (vecHeight_support_nonempty hv)
  have hne : v (vecHeight v hv) ≠ 0 := (Finset.mem_filter.1 hmem).2
  rcases zmod2_eq_zero_or_one (v (vecHeight v hv)) with h0 | h1
  · exact (hne h0).elim
  · exact h1

lemma apply_eq_zero_of_vecHeight_lt {s : ℕ} {v : 𝔽₂ s} (hv : v ≠ 0)
    {m : Fin s} (hm : vecHeight v hv < m) : v m = 0 := by
  by_contra hne
  have hle : m ≤ vecHeight v hv :=
    Finset.le_max' _ m (Finset.mem_filter.2 ⟨Finset.mem_univ m, hne⟩)
  exact not_lt.2 hle hm

lemma add_apply_eq_zero_of_vecHeight_eq {s : ℕ} {u w : 𝔽₂ s} (hu : u ≠ 0) (hw : w ≠ 0)
    (heq : vecHeight u hu = vecHeight w hw) {m : Fin s} (hm : vecHeight u hu ≤ m) :
    (u + w) m = 0 := by
  rcases eq_or_lt_of_le hm with rfl | hlt
  · simp only [Pi.add_apply, vecHeight_apply hu]
    rw [heq, vecHeight_apply hw]
    exact zmod2_add_self 1
  · simp [apply_eq_zero_of_vecHeight_lt hu hlt, apply_eq_zero_of_vecHeight_lt hw (heq ▸ hlt)]

def IsEvenBasis {s : ℕ} {ι : Type*} [Fintype ι] (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) : Prop :=
  ∀ j : Fin s, Even (Finset.univ.filter fun i : ι => vecHeight (d i) (hd i) = j).card

def eLast {s : ℕ} (hs : 1 ≤ s) : 𝔽₂ s :=
  Pi.single ⟨s - 1, by omega⟩ 1

def eta {s : ℕ} {ι : Type*} (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (i : ι) : 𝔽₂ s :=
  Pi.single (vecHeight (d i) (hd i)) 1

lemma dot2_eta_self {s : ℕ} {ι : Type*} (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (i : ι) :
    dot2 (eta d hd i) (d i) = 1 := by
  simp [eta, dot2_single_left, vecHeight_apply (hd i)]

lemma dot2_eLast_self {s : ℕ} (hs : 1 ≤ s) : dot2 (eLast hs) (eLast hs) = 1 := by
  simp [eLast, dot2_single_left]

lemma sum_eta_eq_zero {s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (heven : IsEvenBasis d hd) :
    ∑ i : ι, eta d hd i = 0 := by
  ext j
  rw [Finset.sum_apply, Pi.zero_apply]
  have hrew : (∑ i : ι, eta d hd i j) =
      ((Finset.univ.filter fun i : ι => vecHeight (d i) (hd i) = j).card : ZMod 2) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : vecHeight (d i) (hd i) = j
    · simp [eta, h]
    · simp [eta, h, Ne.symm h]
  rw [hrew]
  obtain ⟨k, hk⟩ := heven j
  rw [hk, Nat.cast_add, zmod2_add_self]

def bClass {s : ℕ} {ι : Type*} (hs : 1 ≤ s) (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (i : ι) :
    𝔽₂ s × 𝔽₂ s :=
  (eLast hs + d i, eLast hs + eta d hd i)

def bSum {α : Type*} {s : ℕ} (b : α → 𝔽₂ s × 𝔽₂ s) (S : Finset α) : 𝔽₂ s × 𝔽₂ s :=
  ∑ i ∈ S, b i

lemma bSum_empty {α : Type*} {s : ℕ} (b : α → 𝔽₂ s × 𝔽₂ s) : bSum b ∅ = 0 := by
  simp [bSum]

lemma bSum_singleton {α : Type*} {s : ℕ} (b : α → 𝔽₂ s × 𝔽₂ s) (a : α) : bSum b {a} = b a := by
  simp [bSum]

lemma bSum_union {α : Type*} [DecidableEq α] {s : ℕ} (b : α → 𝔽₂ s × 𝔽₂ s)
    {S₁ S₂ : Finset α} (h : Disjoint S₁ S₂) :
    bSum b (S₁ ∪ S₂) = bSum b S₁ + bSum b S₂ := by
  simp [bSum, Finset.sum_union h]

lemma bSum_univ_eq_zero {s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hs : 1 ≤ s) (hcard : Even (Fintype.card ι))
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    (hsum : ∑ i : ι, d i = 0) (heven : IsEvenBasis d hd) :
    bSum (bClass hs d hd) Finset.univ = (0, 0) := by
  have hev_vec : ∀ x : 𝔽₂ s, (Fintype.card ι : ℕ) • x = 0 := fun x => by
    obtain ⟨k, hk⟩ := hcard
    rw [hk, add_nsmul, vec_add_self]
  apply Prod.ext
  · rw [bSum, Prod.fst_sum]
    simp [bClass, Finset.sum_add_distrib, hev_vec, hsum]
  · rw [bSum, Prod.snd_sum]
    simp [bClass, Finset.sum_add_distrib, hev_vec, sum_eta_eq_zero d hd heven]

/- ### 3. Signed translation matrices `WMat`, `J0Mat`, `JMat`, `BMat`, and Lemma 3.1 -/

def WMat {s : ℕ} (a β : 𝔽₂ s) : Matrix (𝔽₂ s) (𝔽₂ s) ℚ :=
  fun x y => if y = x + a then sign2 (dot2 β x) else 0

def J0Mat {s : ℕ} (hs : 1 ≤ s) : Matrix (𝔽₂ s) (𝔽₂ s) ℚ :=
  WMat (eLast hs) (eLast hs)

def JMat {s : ℕ} {ι : Type*} (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (i : ι) :
    Matrix (𝔽₂ s) (𝔽₂ s) ℚ :=
  WMat (d i) (eta d hd i)

def BMat {s : ℕ} {ι : Type*} (hs : 1 ≤ s) (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (i : ι) :
    Matrix (𝔽₂ s) (𝔽₂ s) ℚ :=
  -(J0Mat hs * JMat d hd i)

def BWord {s : ℕ} {ι : Type*} (hs : 1 ≤ s) (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    (w : List ι) : Matrix (𝔽₂ s) (𝔽₂ s) ℚ :=
  (w.map (BMat hs d hd)).prod

def IsSignedTrans {s : ℕ} (X : Matrix (𝔽₂ s) (𝔽₂ s) ℚ) (κ : 𝔽₂ s × 𝔽₂ s) : Prop :=
  ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧ X = ε • WMat κ.1 κ.2

lemma WMat_zero {s : ℕ} : WMat (0 : 𝔽₂ s) 0 = (1 : Matrix (𝔽₂ s) (𝔽₂ s) ℚ) := by
  ext x y
  by_cases h : x = y
  · subst h; simp [WMat, dot2_zero_left, sign2_zero]
  · simp [WMat, h, Ne.symm h]

lemma WMat_mul {s : ℕ} (a β c γ : 𝔽₂ s) :
    WMat a β * WMat c γ = sign2 (dot2 γ a) • WMat (a + c) (β + γ) := by
  ext x y
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  have hsum : (∑ z : 𝔽₂ s, WMat a β x z * WMat c γ z y) =
      sign2 (dot2 β x) * WMat c γ (x + a) y := by
    rw [Finset.sum_eq_single (x + a)]
    · simp [WMat]
    · intro z _ hz; simp [WMat, hz]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hsum]
  by_cases h : y = x + (a + c)
  · have h' : y = x + a + c := by rw [h, add_assoc]
    simp only [WMat, if_pos h, if_pos h', dot2_add_left, dot2_add_right, sign2_add]
    ring
  · have h' : y ≠ x + a + c := fun h1 => h (by rw [h1, add_assoc])
    simp [WMat, h, h']

lemma WMat_comm {s : ℕ} (a β c γ : 𝔽₂ s) :
    WMat a β * WMat c γ = sign2 (symp (a, β) (c, γ)) • (WMat c γ * WMat a β) := by
  rw [WMat_mul, WMat_mul, add_comm c a, add_comm γ β, smul_smul, ← sign2_add]
  congr 2
  rw [symp, add_comm (dot2 β c) (dot2 γ a), add_assoc, zmod2_add_self, add_zero]

lemma IsSignedTrans.mul {s : ℕ} {X Y : Matrix (𝔽₂ s) (𝔽₂ s) ℚ} {κ₁ κ₂ : 𝔽₂ s × 𝔽₂ s}
    (hX : IsSignedTrans X κ₁) (hY : IsSignedTrans Y κ₂) :
    IsSignedTrans (X * Y) (κ₁ + κ₂) := by
  rcases hX with ⟨ε₁, hε₁, rfl⟩
  rcases hY with ⟨ε₂, hε₂, rfl⟩
  refine ⟨ε₁ * ε₂ * sign2 (dot2 κ₂.2 κ₁.1), ?_, ?_⟩
  · rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl <;>
      rcases sign2_eq_one_or_neg_one (dot2 κ₂.2 κ₁.1) with h | h <;> simp [h]
  · rw [Matrix.smul_mul, Matrix.mul_smul, WMat_mul, smul_smul, smul_smul]
    rfl

lemma IsSignedTrans.comm {s : ℕ} {X Y : Matrix (𝔽₂ s) (𝔽₂ s) ℚ} {κ₁ κ₂ : 𝔽₂ s × 𝔽₂ s}
    (hX : IsSignedTrans X κ₁) (hY : IsSignedTrans Y κ₂) :
    X * Y = sign2 (symp κ₁ κ₂) • (Y * X) := by
  rcases hX with ⟨ε₁, _, rfl⟩
  rcases hY with ⟨ε₂, _, rfl⟩
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    WMat_comm κ₁.1 κ₁.2 κ₂.1 κ₂.2, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1; ring

lemma sum_sign2_dot2_eq_zero {s : ℕ} {β : 𝔽₂ s} (hβ : β ≠ 0) :
    ∑ x : 𝔽₂ s, sign2 (dot2 β x) = 0 := by
  have hex : ∃ j : Fin s, β j ≠ 0 := by
    by_contra hall; push Not at hall; exact hβ (funext hall)
  obtain ⟨j, hj⟩ := hex
  have hj1 : β j = 1 := by
    rcases zmod2_eq_zero_or_one (β j) with h0 | h1
    · exact (hj h0).elim
    · exact h1
  let e : 𝔽₂ s := Pi.single j 1
  have hdot : dot2 β e = 1 := by simp [e, dot2_single_right, hj1]
  have hshift : (∑ x : 𝔽₂ s, sign2 (dot2 β x)) = ∑ x : 𝔽₂ s, sign2 (dot2 β (x + e)) := by
    exact (Equiv.sum_comp (Equiv.addRight e) (fun x => sign2 (dot2 β x))).symm
  have hneg : (∑ x : 𝔽₂ s, sign2 (dot2 β (x + e))) = -∑ x : 𝔽₂ s, sign2 (dot2 β x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [dot2_add_right, hdot, sign2_add, sign2_one, mul_neg_one]
  linarith

lemma trace_WMat {s : ℕ} (a β : 𝔽₂ s) :
    Matrix.trace (WMat a β) = if (a, β) = (0, 0) then (2 ^ s : ℚ) else 0 := by
  rw [Matrix.trace]
  by_cases ha : a = 0
  · subst ha
    by_cases hβ : β = 0
    · subst hβ
      simp only [Matrix.diag_apply, WMat, add_zero, ↓reduceIte, dot2_zero_left, sign2_zero,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hcard : Fintype.card (𝔽₂ s) = 2 ^ s := by
        simp [𝔽₂, 𝔽, ZMod.card]
      rw [hcard]; norm_cast
    · simp only [Prod.mk.injEq, true_and, hβ, ↓reduceIte, Matrix.diag_apply, WMat, add_zero]
      exact sum_sign2_dot2_eq_zero hβ
  · have hpair : (a, β) ≠ (0, 0) := fun h => ha (congrArg Prod.fst h)
    simp only [hpair, ↓reduceIte, Matrix.diag_apply, WMat]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hne : x ≠ x + a := fun h => ha (by simpa using h.symm)
    simp [hne]

lemma trace_of_isSignedTrans {s : ℕ} {X : Matrix (𝔽₂ s) (𝔽₂ s) ℚ} {κ : 𝔽₂ s × 𝔽₂ s}
    (hX : IsSignedTrans X κ) :
    ∃ ε : ℚ, (ε = 1 ∨ ε = -1) ∧
      Matrix.trace X = if κ = (0, 0) then ε * (2 ^ s : ℚ) else 0 := by
  rcases hX with ⟨ε, hε, rfl⟩
  refine ⟨ε, hε, ?_⟩
  rw [Matrix.trace_smul, smul_eq_mul, trace_WMat]
  split_ifs <;> simp

lemma J0Mat_mul_self {s : ℕ} (hs : 1 ≤ s) :
    J0Mat hs * J0Mat hs = -(1 : Matrix (𝔽₂ s) (𝔽₂ s) ℚ) := by
  rw [J0Mat, WMat_mul, dot2_eLast_self hs, sign2_one, vec_add_self, WMat_zero, neg_one_smul]

lemma BMat_isSignedTrans {s : ℕ} {ι : Type*} (hs : 1 ≤ s) (d : ι → 𝔽₂ s)
    (hd : ∀ i, d i ≠ 0) (i : ι) :
    IsSignedTrans (BMat hs d hd i) (bClass hs d hd i) := by
  rw [BMat, J0Mat, JMat, WMat_mul, ← neg_smul]
  refine ⟨-sign2 (dot2 (eta d hd i) (eLast hs)), ?_, rfl⟩
  rcases sign2_eq_one_or_neg_one (dot2 (eta d hd i) (eLast hs)) with h | h <;> simp [h]

lemma BWord_nil {s : ℕ} {ι : Type*} (hs : 1 ≤ s) (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) :
    BWord hs d hd [] = 1 := rfl

lemma BWord_singleton {s : ℕ} {ι : Type*} (hs : 1 ≤ s) (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (i : ι) :
    BWord hs d hd [i] = BMat hs d hd i := by
  simp [BWord]

lemma BWord_append {s : ℕ} {ι : Type*} (hs : 1 ≤ s) (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    (w₁ w₂ : List ι) :
    BWord hs d hd (w₁ ++ w₂) = BWord hs d hd w₁ * BWord hs d hd w₂ := by
  simp [BWord]

lemma BWord_isSignedTrans {s : ℕ} {ι : Type*} [DecidableEq ι] (hs : 1 ≤ s)
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (w : List ι) (hw : w.Nodup) :
    IsSignedTrans (BWord hs d hd w) (bSum (bClass hs d hd) w.toFinset) := by
  induction w with
  | nil =>
    refine ⟨1, Or.inl rfl, ?_⟩
    simp [BWord, bSum, WMat_zero]
  | cons a t ih =>
    rw [List.nodup_cons] at hw
    have h1 : BWord hs d hd (a :: t) = BMat hs d hd a * BWord hs d hd t := by
      simp [BWord]
    rw [h1, List.toFinset_cons]
    have hnotmem : a ∉ t.toFinset := by simpa using hw.1
    rw [bSum, Finset.sum_insert hnotmem]
    exact (BMat_isSignedTrans hs d hd a).mul (ih hw.2)

/- ### 4. Orderings and logarithmic coefficients `Lcoeff` -/

noncomputable def orderings {α : Type*} [DecidableEq α] (S : Finset α) : Finset (List α) :=
  S.toList.permutations.toFinset

lemma mem_orderings {α : Type*} [DecidableEq α] {S : Finset α} {w : List α} :
    w ∈ orderings S ↔ w.Nodup ∧ w.toFinset = S := by
  simp only [orderings, List.mem_toFinset, List.mem_permutations]
  constructor
  · intro hperm
    refine ⟨hperm.nodup_iff.2 (Finset.nodup_toList S), ?_⟩
    ext x
    simp [List.mem_toFinset, hperm.mem_iff]
  · rintro ⟨hnodup, hfin⟩
    refine (List.perm_ext_iff_of_nodup hnodup (Finset.nodup_toList S)).2 fun x => ?_
    have hx : x ∈ w.toFinset ↔ x ∈ S := by rw [hfin]
    simpa [List.mem_toFinset] using hx

lemma length_of_mem_orderings {α : Type*} [DecidableEq α] {S : Finset α} {w : List α}
    (hw : w ∈ orderings S) : w.length = S.card := by
  rcases mem_orderings.1 hw with ⟨hnodup, hfin⟩
  rw [← hfin, List.toFinset_card_of_nodup hnodup]

noncomputable def Lcoeff {s : ℕ} {ι : Type*} [DecidableEq ι] (hs : 1 ≤ s)
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (S : Finset ι) : ℚ :=
  ((-1 : ℚ) ^ (S.card - 1) / (2 * (S.card : ℚ))) *
    ∑ w ∈ orderings S, Matrix.trace (BWord hs d hd w)

/- ### 5. Binary trees as node-sets `Finset (Finset α)` -/

def IsTree {α : Type*} [DecidableEq α] : ℕ → Finset α → Finset (Finset α) → Prop
  | 0, A, N => A.card = 1 ∧ N = {A}
  | k + 1, A, N =>
      ∃ A₁ A₂ N₁ N₂, Disjoint A₁ A₂ ∧ A₁ ∪ A₂ = A ∧
        IsTree k A₁ N₁ ∧ IsTree k A₂ N₂ ∧ N = insert A (N₁ ∪ N₂)

def IsGoodTree {α : Type*} [DecidableEq α] {s : ℕ} (b : α → 𝔽₂ s × 𝔽₂ s)
    (N : Finset (Finset α)) : Prop :=
  ∀ C₁ ∈ N, ∀ C₂ ∈ N, Disjoint C₁ C₂ → C₁.card = C₂.card → C₁ ∪ C₂ ∈ N →
    symp (bSum b C₁) (bSum b C₂) = 0

noncomputable def treesOn {α : Type*} [DecidableEq α] (k : ℕ) (A : Finset α) :
    Finset (Finset (Finset α)) := by
  classical
  exact A.powerset.powerset.filter (IsTree k A)

noncomputable def goodTreesOn {α : Type*} [DecidableEq α] {s : ℕ}
    (b : α → 𝔽₂ s × 𝔽₂ s) (k : ℕ) (A : Finset α) :
    Finset (Finset (Finset α)) := by
  classical
  exact (treesOn k A).filter (IsGoodTree b)

/- ### 6. Lightweight 2-adic valuation predicates on `ℚ` -/

def Val2Ge (m : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), Odd b ∧ q = (2 : ℚ) ^ m * (a : ℚ) / (b : ℚ)

def Val2Eq (m : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (b : ℕ), Odd a ∧ Odd b ∧ q = (2 : ℚ) ^ m * (a : ℚ) / (b : ℚ)

lemma val2Eq_ne_zero {m : ℕ} {q : ℚ} (h : Val2Eq m q) : q ≠ 0 := by
  rcases h with ⟨a, b, ha, hb, rfl⟩
  have ha0 : (a : ℚ) ≠ 0 := by
    exact_mod_cast (show a ≠ 0 from fun h0 => by subst h0; exact Int.not_odd_zero ha)
  have hb0 : (b : ℚ) ≠ 0 := by
    exact_mod_cast (show b ≠ 0 from fun h0 => by subst h0; exact Nat.not_odd_zero hb)
  positivity

lemma val2Ge_zero (m : ℕ) : Val2Ge m 0 :=
  ⟨0, 1, odd_one, by simp⟩

lemma val2Ge_mono {m₁ m₂ : ℕ} {q : ℚ} (h : Val2Ge m₁ q) (hle : m₂ ≤ m₁) : Val2Ge m₂ q := by
  rcases h with ⟨a, b, hb, rfl⟩
  refine ⟨2 ^ (m₁ - m₂) * a, b, hb, ?_⟩
  push_cast
  rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le hle]

lemma val2Ge_add {m : ℕ} {q₁ q₂ : ℚ} (h₁ : Val2Ge m q₁) (h₂ : Val2Ge m q₂) :
    Val2Ge m (q₁ + q₂) := by
  rcases h₁ with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h₂ with ⟨a₂, b₂, hb₂, rfl⟩
  have hb₁0 : (b₁ : ℚ) ≠ 0 := by exact_mod_cast hb₁.pos.ne'
  have hb₂0 : (b₂ : ℚ) ≠ 0 := by exact_mod_cast hb₂.pos.ne'
  refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, hb₁.mul hb₂, ?_⟩
  push_cast
  field_simp

lemma val2Ge_mul {m₁ m₂ : ℕ} {q₁ q₂ : ℚ} (h₁ : Val2Ge m₁ q₁) (h₂ : Val2Ge m₂ q₂) :
    Val2Ge (m₁ + m₂) (q₁ * q₂) := by
  rcases h₁ with ⟨a₁, b₁, hb₁, rfl⟩
  rcases h₂ with ⟨a₂, b₂, hb₂, rfl⟩
  refine ⟨a₁ * a₂, b₁ * b₂, hb₁.mul hb₂, ?_⟩
  push_cast
  rw [pow_add]
  ring

lemma val2Eq_add_val2Ge {m : ℕ} {q₁ q₂ : ℚ} (h₁ : Val2Eq m q₁) (h₂ : Val2Ge (m + 1) q₂) :
    Val2Eq m (q₁ + q₂) := by
  rcases h₁ with ⟨a₁, b₁, ha₁, hb₁, rfl⟩
  rcases h₂ with ⟨a₂, b₂, hb₂, rfl⟩
  have hb₁0 : (b₁ : ℚ) ≠ 0 := by exact_mod_cast hb₁.pos.ne'
  have hb₂0 : (b₂ : ℚ) ≠ 0 := by exact_mod_cast hb₂.pos.ne'
  have hodd : Odd (a₁ * (b₂ : ℤ) + 2 * a₂ * (b₁ : ℤ)) := by
    have h1 : Odd (a₁ * (b₂ : ℤ)) := ha₁.mul ((Int.odd_coe_nat b₂).2 hb₂)
    have h2 : Even (2 * a₂ * (b₁ : ℤ)) := ⟨a₂ * (b₁ : ℤ), by ring⟩
    exact h1.add_even h2
  refine ⟨a₁ * b₂ + 2 * a₂ * b₁, b₁ * b₂, hodd, hb₁.mul hb₂, ?_⟩
  push_cast
  rw [pow_succ]
  field_simp

lemma val2Ge_sum {ι : Type*} (S : Finset ι) (m : ℕ) (f : ι → ℚ)
    (hf : ∀ x ∈ S, Val2Ge m (f x)) : Val2Ge m (∑ x ∈ S, f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using val2Ge_zero m
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact val2Ge_add (hf a (Finset.mem_insert_self a S))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

lemma val2Ge_prod {ι : Type*} (S : Finset ι) (m : ι → ℕ) (f : ι → ℚ)
    (hf : ∀ x ∈ S, Val2Ge (m x) (f x)) : Val2Ge (∑ x ∈ S, m x) (∏ x ∈ S, f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 1, odd_one, by simp⟩
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact val2Ge_mul (hf a (Finset.mem_insert_self a S))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

end OMA.BGS
namespace OMA.BGS

/- ## Part A (§2.1, §2.4, §3): Squarefree Ring, Pfaffian, Jacobi/Log-Det, and Realization Certificate -/

section SqFreeRing

/-- The squarefree quotient ring `ℚ[t_i : i ∈ ι] / (t_i^2)` represented directly as
functions `Finset ι → ℚ` (the coefficient of each squarefree monomial `t_S`). -/
structure SqFreeRing (ι : Type*) where
  coeff : Finset ι → ℚ

namespace SqFreeRing

variable {ι : Type*}

lemma ext {f g : SqFreeRing ι} (h : ∀ S, f.coeff S = g.coeff S) : f = g := by
  cases f; cases g; congr; exact funext h

instance : Zero (SqFreeRing ι) := ⟨⟨fun _ => 0⟩⟩
instance : Add (SqFreeRing ι) := ⟨fun f g => ⟨fun S => f.coeff S + g.coeff S⟩⟩
instance : Neg (SqFreeRing ι) := ⟨fun f => ⟨fun S => -f.coeff S⟩⟩
instance : Sub (SqFreeRing ι) := ⟨fun f g => ⟨fun S => f.coeff S - g.coeff S⟩⟩
instance : SMul ℚ (SqFreeRing ι) := ⟨fun q f => ⟨fun S => q * f.coeff S⟩⟩

@[simp] lemma zero_coeff (S : Finset ι) : (0 : SqFreeRing ι).coeff S = 0 := rfl
@[simp] lemma add_coeff (f g : SqFreeRing ι) (S : Finset ι) :
    (f + g).coeff S = f.coeff S + g.coeff S := rfl
@[simp] lemma neg_coeff (f : SqFreeRing ι) (S : Finset ι) :
    (-f).coeff S = -f.coeff S := rfl
@[simp] lemma sub_coeff (f g : SqFreeRing ι) (S : Finset ι) :
    (f - g).coeff S = f.coeff S - g.coeff S := rfl
@[simp] lemma smul_coeff (q : ℚ) (f : SqFreeRing ι) (S : Finset ι) :
    (q • f).coeff S = q * f.coeff S := rfl

variable [DecidableEq ι]

instance : One (SqFreeRing ι) := ⟨⟨fun S => if S = ∅ then 1 else 0⟩⟩
instance : Mul (SqFreeRing ι) :=
  ⟨fun f g => ⟨fun S => ∑ T ∈ S.powerset, f.coeff T * g.coeff (S \ T)⟩⟩

@[simp] lemma one_coeff (S : Finset ι) :
    (1 : SqFreeRing ι).coeff S = if S = ∅ then 1 else 0 := rfl
lemma mul_coeff (f g : SqFreeRing ι) (S : Finset ι) :
    (f * g).coeff S = ∑ T ∈ S.powerset, f.coeff T * g.coeff (S \ T) := rfl

lemma mul_comm_aux (f g : SqFreeRing ι) : f * g = g * f := by
  refine SqFreeRing.ext fun S => ?_
  simp only [mul_coeff]
  refine Finset.sum_bij (fun T _ => S \ T) ?_ ?_ ?_ ?_
  · intro T hT; exact Finset.mem_powerset.2 Finset.sdiff_subset
  · intro T₁ hT₁ T₂ hT₂ h
    have h1 := Finset.mem_powerset.1 hT₁
    have h2 := Finset.mem_powerset.1 hT₂
    rw [← Finset.sdiff_sdiff_eq_self h1, ← Finset.sdiff_sdiff_eq_self h2, h]
  · intro T hT
    exact ⟨S \ T, Finset.mem_powerset.2 Finset.sdiff_subset,
      Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hT)⟩
  · intro T hT
    rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 hT), mul_comm]

lemma mul_assoc_aux (f g h : SqFreeRing ι) : f * g * h = f * (g * h) := by
  refine SqFreeRing.ext fun S => ?_
  simp only [mul_coeff, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij
    (fun (p : Σ _ : Finset ι, Finset ι) _ => (⟨p.2, p.1 \ p.2⟩ : Σ _ : Finset ι, Finset ι))
    ?_ ?_ ?_ ?_
  · rintro ⟨U, T⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp ⊢
    exact ⟨hp.2.trans hp.1, Finset.sdiff_subset_sdiff hp.1 subset_rfl⟩
  · rintro ⟨U₁, T₁⟩ hp₁ ⟨U₂, T₂⟩ hp₂ heq
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp₁ hp₂
    simp only [Sigma.mk.injEq, heq_eq_eq] at heq
    rcases heq with ⟨rfl, hd⟩
    have hU : U₁ = U₂ := by
      rw [← Finset.union_sdiff_of_subset hp₁.2, ← Finset.union_sdiff_of_subset hp₂.2, hd]
    subst hU; rfl
  · rintro ⟨T, V⟩ hq
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hq
    refine ⟨⟨T ∪ V, T⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_powerset]
      exact ⟨Finset.union_subset hq.1 (hq.2.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
      have hdisj : Disjoint T V := Finset.disjoint_of_subset_right hq.2 disjoint_sdiff_self_right
      exact Finset.union_sdiff_cancel_left hdisj
  · rintro ⟨U, T⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hp
    have hdiff : (S \ T) \ (U \ T) = S \ U := by
      ext x
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨hxS, hxT⟩, hnot⟩
        exact ⟨hxS, fun hxU => hnot ⟨hxU, hxT⟩⟩
      · rintro ⟨hxS, hxU⟩
        exact ⟨⟨hxS, fun hxT => hxU (hp.2 hxT)⟩, fun h => hxU h.1⟩
    rw [hdiff, mul_assoc]

instance : CommRing (SqFreeRing ι) where
  add := (· + ·)
  add_assoc a b c := SqFreeRing.ext fun S => add_assoc _ _ _
  zero := 0
  zero_add a := SqFreeRing.ext fun S => zero_add _
  add_zero a := SqFreeRing.ext fun S => add_zero _
  nsmul := nsmulRec
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg a b := SqFreeRing.ext fun S => sub_eq_add_neg _ _
  zsmul := zsmulRec
  neg_add_cancel a := SqFreeRing.ext fun S => neg_add_cancel _
  add_comm a b := SqFreeRing.ext fun S => add_comm _ _
  mul := (· * ·)
  left_distrib a b c := SqFreeRing.ext fun S => by
    simp only [add_coeff, mul_coeff, mul_add, Finset.sum_add_distrib]
  right_distrib a b c := SqFreeRing.ext fun S => by
    simp only [add_coeff, mul_coeff, add_mul, Finset.sum_add_distrib]
  zero_mul a := SqFreeRing.ext fun S => by simp [mul_coeff]
  mul_zero a := SqFreeRing.ext fun S => by simp [mul_coeff]
  mul_assoc := mul_assoc_aux
  one := 1
  one_mul a := SqFreeRing.ext fun S => by
    rw [mul_coeff, Finset.sum_eq_single ∅]
    · simp
    · intro T _ hT; simp [hT]
    · intro h; exact (h (Finset.mem_powerset.2 (Finset.empty_subset S))).elim
  mul_one a := by
    rw [mul_comm_aux]
    refine SqFreeRing.ext fun S => ?_
    rw [mul_coeff, Finset.sum_eq_single ∅]
    · simp
    · intro T _ hT; simp [hT]
    · intro h; exact (h (Finset.mem_powerset.2 (Finset.empty_subset S))).elim
  mul_comm := mul_comm_aux

def toRatHom : ℚ →+* SqFreeRing ι where
  toFun q := ⟨fun S => if S = ∅ then q else 0⟩
  map_one' := rfl
  map_mul' a b := SqFreeRing.ext fun S => by
    rw [mul_coeff, Finset.sum_eq_single ∅]
    · by_cases hS : S = ∅ <;> simp [hS]
    · intro T _ hT; simp [hT]
    · intro h; exact (h (Finset.mem_powerset.2 (Finset.empty_subset S))).elim
  map_zero' := SqFreeRing.ext fun S => by simp
  map_add' a b := SqFreeRing.ext fun S => by by_cases hS : S = ∅ <;> simp [hS]

instance : Algebra ℚ (SqFreeRing ι) where
  smul := (· • ·)
  algebraMap := toRatHom
  commutes' q f := mul_comm _ _
  smul_def' q f := SqFreeRing.ext fun S => by
    rw [smul_coeff, mul_coeff, Finset.sum_eq_single ∅]
    · simp [toRatHom]
    · intro T _ hT; simp [toRatHom, hT]
    · intro h; exact (h (Finset.mem_powerset.2 (Finset.empty_subset S))).elim

lemma algebraMap_coeff (q : ℚ) (S : Finset ι) :
    (algebraMap ℚ (SqFreeRing ι) q).coeff S = if S = ∅ then q else 0 := rfl

lemma sum_coeff {α : Type*} (s : Finset α) (f : α → SqFreeRing ι) (S : Finset ι) :
    (∑ a ∈ s, f a).coeff S = ∑ a ∈ s, (f a).coeff S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- The squarefree monomial `t_A = ∏ i ∈ A, t_i`. -/
def mon (A : Finset ι) : SqFreeRing ι := ⟨fun S => if S = A then 1 else 0⟩

/-- The generator `t_i = mon {i}`. -/
def var (i : ι) : SqFreeRing ι := mon {i}

@[simp] lemma mon_coeff (A S : Finset ι) : (mon A).coeff S = if S = A then 1 else 0 := rfl
@[simp] lemma var_coeff (i : ι) (S : Finset ι) : (var i).coeff S = if S = {i} then 1 else 0 := rfl
@[simp] lemma mon_empty : mon (∅ : Finset ι) = 1 := rfl

lemma mon_mul_mon (A B : Finset ι) :
    mon A * mon B = if Disjoint A B then mon (A ∪ B) else 0 := by
  refine SqFreeRing.ext fun S => ?_
  rw [mul_coeff]
  by_cases hAB : Disjoint A B
  · simp only [if_pos hAB, mon_coeff]
    by_cases hAS : A ⊆ S
    · rw [Finset.sum_eq_single A]
      · simp only [↓reduceIte, one_mul]
        by_cases hS : S = A ∪ B
        · subst hS; simp [Finset.union_sdiff_cancel_left hAB]
        · have hne : S \ A ≠ B := fun h => hS (by rw [← h, Finset.union_sdiff_of_subset hAS])
          simp [hS, hne]
      · intro T _ hTA; simp [hTA]
      · intro h; exact (h (Finset.mem_powerset.2 hAS)).elim
    · have hne : S ≠ A ∪ B := fun h => hAS (h ▸ Finset.subset_union_left)
      simp only [if_neg hne]
      refine Finset.sum_eq_zero fun T hT => ?_
      have hTA : T ≠ A := fun h => hAS (h ▸ Finset.mem_powerset.1 hT)
      simp [hTA]
  · simp only [if_neg hAB, zero_coeff]
    refine Finset.sum_eq_zero fun T _ => ?_
    by_cases hTA : T = A
    · subst hTA
      have hne : S \ T ≠ B := fun h => hAB (h ▸ disjoint_sdiff_self_right)
      simp [hne]
    · simp [hTA]

lemma list_prod_var (w : List ι) :
    (w.map var).prod = if w.Nodup then mon w.toFinset else 0 := by
  induction w with
  | nil => simp [mon_empty]
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, ih, List.nodup_cons, List.toFinset_cons]
    by_cases ht : t.Nodup
    · simp only [if_pos ht, var, mon_mul_mon]
      by_cases ha : a ∈ t
      · simp [ha]
      · simp [ha, ht, Finset.singleton_union]
    · simp [ht]

/-- Evaluation at 0 (constant term) as a ring hom `SqFreeRing ι →+* ℚ`. -/
def coeffEmptyHom : SqFreeRing ι →+* ℚ where
  toFun f := f.coeff ∅
  map_one' := by simp
  map_mul' f g := by simp [mul_coeff]
  map_zero' := rfl
  map_add' f g := rfl

lemma coeffEmpty_pow (f : SqFreeRing ι) (n : ℕ) :
    (f ^ n).coeff ∅ = (f.coeff ∅) ^ n :=
  map_pow coeffEmptyHom f n

/-- Nilpotency degree bound for products of elements in the maximal ideal `𝔪`. -/
lemma mul_coeff_eq_zero_of_bound {f g : SqFreeRing ι} {a b : ℕ}
    (hf : ∀ S, S.card < a → f.coeff S = 0)
    (hg : ∀ S, S.card < b → g.coeff S = 0) :
    ∀ S, S.card < a + b → (f * g).coeff S = 0 := by
  intro S hS
  rw [mul_coeff]
  refine Finset.sum_eq_zero fun T hT => ?_
  have hTS : T ⊆ S := Finset.mem_powerset.1 hT
  have hcard : T.card + (S \ T).card = S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hTS, Nat.add_sub_of_le (Finset.card_le_card hTS)]
  by_cases ha : T.card < a
  · simp [hf T ha]
  · have hb : (S \ T).card < b := by omega
    simp [hg (S \ T) hb]

lemma pow_coeff_eq_zero_of_card_lt {f : SqFreeRing ι} (hf : f.coeff ∅ = 0) :
    ∀ m : ℕ, ∀ S : Finset ι, S.card < m → (f ^ m).coeff S = 0 := by
  intro m
  induction m with
  | zero => intro S hS; omega
  | succ m ih =>
    rw [pow_succ]
    refine mul_coeff_eq_zero_of_bound ih fun S hS => ?_
    have h0 : S = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [h0, hf]

lemma pow_eq_zero_of_coeff_empty [Fintype ι] {f : SqFreeRing ι} (hf : f.coeff ∅ = 0) :
    f ^ (Fintype.card ι + 1) = 0 := by
  refine SqFreeRing.ext fun S => ?_
  exact pow_coeff_eq_zero_of_card_lt hf (Fintype.card ι + 1) S
    (Nat.lt_succ_of_le (Finset.card_le_univ S))

lemma mul_pow_eq_zero_of_gt [Fintype ι] {a b : SqFreeRing ι}
    (ha : a.coeff ∅ = 0) (hb : b.coeff ∅ = 0) {i j : ℕ} (hij : Fintype.card ι < i + j) :
    a ^ i * b ^ j = 0 := by
  refine SqFreeRing.ext fun S => ?_
  refine mul_coeff_eq_zero_of_bound
    (pow_coeff_eq_zero_of_card_lt ha i) (pow_coeff_eq_zero_of_card_lt hb j) S ?_
  exact lt_of_le_of_lt (Finset.card_le_univ S) hij

lemma isUnit_of_coeff_empty_ne_zero [Fintype ι] {u : SqFreeRing ι} (hu : u.coeff ∅ ≠ 0) :
    IsUnit u := by
  let c : ℚ := u.coeff ∅
  let g : SqFreeRing ι := c⁻¹ • u - 1
  have hg : g.coeff ∅ = 0 := by simp [g, c, inv_mul_cancel₀ hu]
  have hu_eq : u = c • (1 + g) := SqFreeRing.ext fun S => by
    simp [g, c]; field_simp [hu]
  let inv_u : SqFreeRing ι :=
    c⁻¹ • ∑ m ∈ Finset.range (Fintype.card ι + 1), (-g) ^ m
  have hgeom : (1 + g) * ∑ m ∈ Finset.range (Fintype.card ι + 1), (-g) ^ m = 1 := by
    have h := geom_sum_mul (-g) (Fintype.card ι + 1)
    have hnilp : (-g) ^ (Fintype.card ι + 1) = 0 :=
      pow_eq_zero_of_coeff_empty (by simp [hg])
    rw [hnilp, zero_sub] at h
    have h1 : (∑ m ∈ Finset.range (Fintype.card ι + 1), (-g) ^ m) * (-(1 + g)) = -1 := by
      have hneg : -g - 1 = -(1 + g) := by ring
      rwa [hneg] at h
    have h2 : (1 + g) * ∑ m ∈ Finset.range (Fintype.card ι + 1), (-g) ^ m = 1 := by
      calc (1 + g) * ∑ m ∈ Finset.range (Fintype.card ι + 1), (-g) ^ m
          = -((∑ m ∈ Finset.range (Fintype.card ι + 1), (-g) ^ m) * (-(1 + g))) := by ring
        _ = -(-1) := by rw [h1]
        _ = 1 := by ring
    exact h2
  refine isUnit_iff_exists_inv.2 ⟨inv_u, ?_⟩
  rw [hu_eq]
  change (c • (1 + g)) * (c⁻¹ • ∑ m ∈ Finset.range (Fintype.card ι + 1), (-g) ^ m) = 1
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, mul_inv_cancel₀ hu, one_smul, hgeom]

/-- Finite exponential on `SqFreeRing ι` (truncated at `M = Fintype.card ι`). -/
def sfExp [Fintype ι] (g : SqFreeRing ι) : SqFreeRing ι :=
  ∑ m ∈ Finset.range (Fintype.card ι + 1), ((m.factorial : ℚ)⁻¹) • g ^ m

lemma sfExp_zero [Fintype ι] : sfExp (0 : SqFreeRing ι) = 1 := by
  rw [sfExp, Finset.sum_eq_single 0]
  · simp
  · intro m _ hm; simp [zero_pow hm]
  · intro h; exact (h (Finset.mem_range.2 (Nat.succ_pos _))).elim

lemma sfExp_coeff_empty [Fintype ι] {g : SqFreeRing ι} (hg : g.coeff ∅ = 0) :
    (sfExp g).coeff ∅ = 1 := by
  rw [sfExp, sum_coeff, Finset.sum_eq_single 0]
  · simp
  · intro m _ hm; simp [coeffEmpty_pow, hg, zero_pow hm]
  · intro h; exact (h (Finset.mem_range.2 (Nat.succ_pos _))).elim

lemma sfExp_add [Fintype ι] {a b : SqFreeRing ι} (ha : a.coeff ∅ = 0) (hb : b.coeff ∅ = 0) :
    sfExp (a + b) = sfExp a * sfExp b := by
  let M := Fintype.card ι
  rw [sfExp, sfExp, sfExp, Finset.sum_mul]
  have h1 : ∀ m ∈ Finset.range (M + 1),
      ((m.factorial : ℚ)⁻¹) • (a + b) ^ m =
      ∑ i ∈ Finset.range (m + 1),
        (((i.factorial : ℚ)⁻¹) • a ^ i) * ((((m - i).factorial : ℚ)⁻¹) • b ^ (m - i)) := by
    intro m _
    rw [add_pow, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hch_mul : a ^ i * b ^ (m - i) * (m.choose i : SqFreeRing ι) =
        (m.choose i : ℚ) • (a ^ i * b ^ (m - i)) := by
      rw [Algebra.smul_def, mul_comm]
      congr 1
      simp
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hch_mul, smul_smul]
    congr 1
    have hch := Nat.choose_mul_factorial_mul_factorial him
    have hf1 : (i.factorial : ℚ) ≠ 0 := by positivity
    have hf2 : ((m - i).factorial : ℚ) ≠ 0 := by positivity
    have hfm : (m.factorial : ℚ) ≠ 0 := by positivity
    have hq : (m.choose i : ℚ) * (i.factorial : ℚ) * ((m - i).factorial : ℚ) = (m.factorial : ℚ) := by
      exact_mod_cast hch
    field_simp [hf1, hf2, hfm]
    linarith
  rw [Finset.sum_congr rfl h1]
  have hprod :
      (∑ i ∈ Finset.range (M + 1),
        (((i.factorial : ℚ)⁻¹) • a ^ i) *
          ∑ j ∈ Finset.range (M + 1), ((j.factorial : ℚ)⁻¹) • b ^ j) =
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
        (((p.1.factorial : ℚ)⁻¹) • a ^ p.1) * (((p.2.factorial : ℚ)⁻¹) • b ^ p.2) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
  rw [hprod]
  have hsigma :
      (∑ m ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (m + 1),
        (((i.factorial : ℚ)⁻¹) • a ^ i) * ((((m - i).factorial : ℚ)⁻¹) • b ^ (m - i))) =
      ∑ p ∈ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter (fun p => p.1 + p.2 ≤ M),
        (((p.1.factorial : ℚ)⁻¹) • a ^ p.1) * (((p.2.factorial : ℚ)⁻¹) • b ^ p.2) := by
    rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun (p : Σ _ : ℕ, ℕ) _ => (p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
    · rintro ⟨m, i⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_range] at hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨m₁, i₁⟩ hp₁ ⟨m₂, i₂⟩ hp₂ heq
      simp only [Finset.mem_sigma, Finset.mem_range] at hp₁ hp₂
      simp only [Prod.mk.injEq] at heq
      have hi : i₁ = i₂ := heq.1
      have hm : m₁ = m₂ := by omega
      subst hi; subst hm; rfl
    · rintro ⟨i, j⟩ hq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
      refine ⟨⟨i + j, i⟩, by simp [Finset.mem_range]; omega, by simp⟩
    · rintro ⟨m, i⟩ _; rfl
  rw [hsigma]
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro p hp hnot
  simp only [Finset.mem_filter, hp, true_and, not_le] at hnot
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, mul_pow_eq_zero_of_gt ha hb hnot,
    smul_zero, smul_zero]

lemma sfExp_mul_neg [Fintype ι] {a : SqFreeRing ι} (ha : a.coeff ∅ = 0) :
    sfExp a * sfExp (-a) = 1 := by
  rw [← sfExp_add ha (by simp [ha]), add_neg_cancel, sfExp_zero]

/-- Matrix nilpotency bound for matrices over `SqFreeRing ι` with zero constant term. -/
lemma matrix_pow_coeff_eq_zero_of_card_lt {α : Type*} [Fintype α] [DecidableEq α]
    {X : Matrix α α (SqFreeRing ι)} (hX : ∀ x y, (X x y).coeff ∅ = 0) :
    ∀ m : ℕ, ∀ x y : α, ∀ S : Finset ι, S.card < m → ((X ^ m) x y).coeff S = 0 := by
  intro m
  induction m with
  | zero => intro _ _ _ h; omega
  | succ m ih =>
    intro x y S hS
    rw [pow_succ, Matrix.mul_apply, sum_coeff]
    refine Finset.sum_eq_zero fun z _ => ?_
    refine mul_coeff_eq_zero_of_bound (ih x z) (fun T hT => ?_) S hS
    have h0 : T = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [h0, hX z y]

lemma matrix_pow_eq_zero [Fintype ι] {α : Type*} [Fintype α] [DecidableEq α]
    {X : Matrix α α (SqFreeRing ι)} (hX : ∀ x y, (X x y).coeff ∅ = 0) :
    X ^ (Fintype.card ι + 1) = 0 := by
  refine Matrix.ext fun x y => SqFreeRing.ext fun S => ?_
  exact matrix_pow_coeff_eq_zero_of_card_lt hX (Fintype.card ι + 1) x y S
    (Nat.lt_succ_of_le (Finset.card_le_univ S))

/- ### Lemma 2.6: Exponential expansion of `(sfExp Λ).coeff univ` over set partitions -/

/-- Exact formula for `(f ^ m).coeff S` as a sum over `m`-tuples of pairwise disjoint subsets
partitioning `S`. -/
lemma pow_coeff_eq_sum_tuples [Fintype ι] {f : SqFreeRing ι} (hf : f.coeff ∅ = 0) :
    ∀ (m : ℕ) (S : Finset ι),
      (f ^ m).coeff S =
        ∑ tup ∈ (Finset.univ : Finset (Fin m → Finset ι)).filter
          (fun tup => (∀ j, (tup j).Nonempty) ∧
            (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (tup j₁) (tup j₂)) ∧
            Finset.univ.biUnion tup = S),
          ∏ j : Fin m, f.coeff (tup j) := by
  intro m
  induction m with
  | zero =>
    intro S
    by_cases hS : S = ∅
    · subst hS
      have hfilt : (Finset.univ : Finset (Fin 0 → Finset ι)).filter
          (fun tup => (∀ j, (tup j).Nonempty) ∧
            (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (tup j₁) (tup j₂)) ∧
            Finset.univ.biUnion tup = ∅) = Finset.univ := by
        ext tup; simp
      rw [hfilt]
      simp
    · have hfilt : (Finset.univ : Finset (Fin 0 → Finset ι)).filter
          (fun tup => (∀ j, (tup j).Nonempty) ∧
            (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (tup j₁) (tup j₂)) ∧
            Finset.univ.biUnion tup = S) = ∅ := by
        ext tup; simp [Ne.symm hS]
      rw [hfilt]
      simp [hS]
  | succ m ih =>
    intro S
    rw [pow_succ, mul_coeff]
    have hsplit :
        (∑ T ∈ S.powerset, (f ^ m).coeff T * f.coeff (S \ T)) =
        ∑ T ∈ S.powerset.filter (fun T => (S \ T).Nonempty),
          (∑ tup ∈ (Finset.univ : Finset (Fin m → Finset ι)).filter
            (fun tup => (∀ j, (tup j).Nonempty) ∧
              (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (tup j₁) (tup j₂)) ∧
              Finset.univ.biUnion tup = T),
            ∏ j : Fin m, f.coeff (tup j)) * f.coeff (S \ T) := by
      rw [← Finset.sum_subset (Finset.filter_subset (fun T => (S \ T).Nonempty) S.powerset)]
      · refine Finset.sum_congr rfl fun T _ => by rw [ih T]
      · intro T hT hnot
        simp only [Finset.mem_filter, hT, true_and, Finset.not_nonempty_iff_eq_empty] at hnot
        rw [hnot, hf, mul_zero]
    rw [hsplit]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_sigma']
    refine Finset.sum_bij
      (fun p _ => Fin.snoc p.2 (S \ p.1))
      ?_ ?_ ?_ ?_
    · rintro ⟨T, tup⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨hTS, hST_ne⟩, hne, hdisj, hbiu⟩
      refine ⟨fun j => ?_, ?_, ?_⟩
      · refine Fin.lastCases ?_ ?_ j
        · simpa using hST_ne
        · intro k; simpa using hne k
      · intro j₁ j₂ hne_j
        revert hne_j
        refine Fin.lastCases ?_ ?_ j₁ <;> refine Fin.lastCases ?_ ?_ j₂
        · intro hne_j; exact (hne_j rfl).elim
        · intro k _
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          have hsub : tup k ⊆ T := by
            rw [← hbiu]; exact Finset.subset_biUnion_of_mem tup (Finset.mem_univ k)
          exact Finset.disjoint_of_subset_right hsub disjoint_sdiff_self_left
        · intro k _
          simp only [Fin.snoc_last, Fin.snoc_castSucc]
          have hsub : tup k ⊆ T := by
            rw [← hbiu]; exact Finset.subset_biUnion_of_mem tup (Finset.mem_univ k)
          exact Finset.disjoint_of_subset_left hsub disjoint_sdiff_self_right
        · intro k₁ k₂ hne'
          simp only [Fin.snoc_castSucc]
          exact hdisj k₂ k₁ fun h => hne' (by rw [h])
      · ext x
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨j, hj⟩
          revert hj
          refine Fin.lastCases ?_ ?_ j
          · intro hj; simp only [Fin.snoc_last] at hj; exact (Finset.mem_sdiff.1 hj).1
          · intro k hj
            simp only [Fin.snoc_castSucc] at hj
            exact hTS (hbiu ▸ Finset.mem_biUnion.2 ⟨k, Finset.mem_univ k, hj⟩)
        · intro hxS
          by_cases hxT : x ∈ T
          · rw [← hbiu] at hxT
            obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.1 hxT
            exact ⟨k.castSucc, by simpa using hxk⟩
          · exact ⟨Fin.last m, by simpa using Finset.mem_sdiff.2 ⟨hxS, hxT⟩⟩
    · rintro ⟨T₁, tup₁⟩ hp₁ ⟨T₂, tup₂⟩ hp₂ heq
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_univ, true_and] at hp₁ hp₂
      have hlast : S \ T₁ = S \ T₂ := by
        have := congrFun heq (Fin.last m)
        simpa using this
      have hT : T₁ = T₂ := by
        rw [← Finset.sdiff_sdiff_eq_self hp₁.1.1, ← Finset.sdiff_sdiff_eq_self hp₂.1.1, hlast]
      subst hT
      have htup : tup₁ = tup₂ := by
        ext k x
        have := congrFun heq k.castSucc
        simpa using congrArg (x ∈ ·) this
      subst htup; rfl
    · intro tup htup
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at htup
      rcases htup with ⟨hne, hdisj, hbiu⟩
      let tup' : Fin m → Finset ι := fun k => tup k.castSucc
      let T : Finset ι := Finset.univ.biUnion tup'
      have hTS : T ⊆ S := by
        rw [← hbiu]
        intro x hx
        obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.1 hx
        exact Finset.mem_biUnion.2 ⟨k.castSucc, Finset.mem_univ _, hxk⟩
      have hST_eq : S \ T = tup (Fin.last m) := by
        ext x
        simp only [Finset.mem_sdiff, T, Finset.mem_biUnion, Finset.mem_univ, true_and, tup']
        rw [← hbiu, Finset.mem_biUnion]
        constructor
        · rintro ⟨⟨j, _, hxj⟩, hnot⟩
          refine Fin.lastCases (fun h => h) (fun k h => (hnot ⟨k, h⟩).elim) j hxj
        · intro hx
          refine ⟨⟨Fin.last m, Finset.mem_univ _, hx⟩, ?_⟩
          rintro ⟨k, hxk⟩
          exact Finset.disjoint_left.1 (hdisj k.castSucc (Fin.last m) (Fin.castSucc_ne_last k)) hxk hx
      refine ⟨⟨T, tup'⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_powerset,
          Finset.mem_univ, true_and]
        refine ⟨⟨hTS, hST_eq ▸ hne (Fin.last m)⟩, fun k => hne k.castSucc,
          fun k₁ k₂ hk => hdisj _ _ (fun h => hk (Fin.castSucc_injective m h)), rfl⟩
      · ext j x
        refine Fin.lastCases ?_ ?_ j
        · simp [hST_eq]
        · intro k; simp [tup']
    · rintro ⟨T, tup⟩ _
      rw [Fin.prod_univ_castSucc]
      simp

/-- Unordered `m`-block set partitions of `Finset.univ : Finset ι`. -/
def partitionsOf [Fintype ι] (m : ℕ) : Finset (Finset (Finset ι)) :=
  (Finset.univ : Finset (Finset ι)).powerset.filter fun π =>
    π.card = m ∧ (∀ B ∈ π, B.Nonempty) ∧
      Set.Pairwise (π : Set (Finset ι)) Disjoint ∧
      π.biUnion id = Finset.univ

/-- **Lemma 2.6**: `(sfExp Λ).coeff univ = Λ.coeff univ + ∑_{m=2}^M ∑_{π ∈ partitionsOf m} ∏_{B ∈ π} Λ.coeff B`. -/
lemma sfExp_coeff_univ [Fintype ι] {Λ : SqFreeRing ι} (hΛ : Λ.coeff ∅ = 0)
    (hM : 1 ≤ Fintype.card ι) :
    (sfExp Λ).coeff Finset.univ =
      Λ.coeff Finset.univ +
      ∑ m ∈ Finset.Icc 2 (Fintype.card ι),
        ∑ π ∈ partitionsOf (ι := ι) m, ∏ B ∈ π, Λ.coeff B := by
  let M := Fintype.card ι
  rw [sfExp, sum_coeff]
  have h0 : ((0 : ℕ).factorial : ℚ)⁻¹ * (Λ ^ 0).coeff Finset.univ = 0 := by
    have hne : (Finset.univ : Finset ι) ≠ ∅ := by
      intro h; have := congrArg Finset.card h; simp at this; omega
    simp [hne]
  have h1 : ((1 : ℕ).factorial : ℚ)⁻¹ * (Λ ^ 1).coeff Finset.univ = Λ.coeff Finset.univ := by
    simp
  have hrange : Finset.range (M + 1) = insert 0 (insert 1 (Finset.Icc 2 M)) := by
    ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hrange, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  simp only [smul_coeff, h0, h1, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pow_coeff_eq_sum_tuples hΛ m Finset.univ]
  let Tups := (Finset.univ : Finset (Fin m → Finset ι)).filter
    (fun tup => (∀ j, (tup j).Nonempty) ∧
      (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (tup j₁) (tup j₂)) ∧
      Finset.univ.biUnion tup = Finset.univ)
  have hmap : ∀ tup ∈ Tups, Finset.univ.image tup ∈ partitionsOf (ι := ι) m := by
    intro tup htup
    simp only [Tups, Finset.mem_filter, Finset.mem_univ, true_and] at htup
    rcases htup with ⟨hne, hdisj, hbiu⟩
    have hinj : Function.Injective tup := by
      intro j₁ j₂ heq
      by_contra hne_j
      have hd := hdisj j₁ j₂ hne_j
      rw [heq, disjoint_self] at hd
      exact (hne j₂).ne_empty (Finset.bot_eq_empty ▸ hd)
    simp only [partitionsOf, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    · intro B hB
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hB
      exact hne j
    · intro B₁ hB₁ B₂ hB₂ hneB
      obtain ⟨j₁, _, rfl⟩ := Finset.mem_image.1 hB₁
      obtain ⟨j₂, _, rfl⟩ := Finset.mem_image.1 hB₂
      exact hdisj j₁ j₂ fun h => hneB (by rw [h])
    · ext x
      rw [← hbiu]
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, id_eq]
      exact ⟨fun ⟨B, ⟨j, hj⟩, hxB⟩ => ⟨j, hj ▸ hxB⟩, fun ⟨j, hxj⟩ => ⟨tup j, ⟨j, rfl⟩, hxj⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π hπ => ?_
  have hπ_prop := (Finset.mem_filter.1 hπ).2
  rcases hπ_prop with ⟨hπ_card, hπ_ne, hπ_disj, hπ_biu⟩
  have hval : ∀ tup ∈ Tups.filter (fun tup => Finset.univ.image tup = π),
      (∏ j : Fin m, Λ.coeff (tup j)) = ∏ B ∈ π, Λ.coeff B := by
    intro tup htup
    rw [Finset.mem_filter] at htup
    rcases htup with ⟨hT, himg⟩
    simp only [Tups, Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have hinj : Function.Injective tup := by
      intro j₁ j₂ heq
      by_contra hne_j
      have hd := hT.2.1 j₁ j₂ hne_j
      rw [heq, disjoint_self] at hd
      exact (hT.1 j₂).ne_empty (Finset.bot_eq_empty ▸ hd)
    rw [← himg, Finset.prod_image fun a _ b _ h => hinj h]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  -- Count fiber size = m! via Equiv (Fin m) π
  have hfib_card : (Tups.filter (fun tup => Finset.univ.image tup = π)).card = m.factorial := by
    have hcard_eq : Fintype.card (Fin m ≃ π) = m.factorial := by
      have eπ : π ≃ Fin m := Fintype.equivFinOfCardEq (by simp [hπ_card])
      rw [Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin m)) eπ),
        Fintype.card_perm, Fintype.card_fin]
    rw [← hcard_eq]
    refine Finset.card_bij (fun (tup : Fin m → Finset ι) htup =>
      Equiv.ofBijective (fun j => ⟨tup j, by
        rw [← (Finset.mem_filter.1 htup).2]; exact Finset.mem_image_of_mem tup (Finset.mem_univ j)⟩)
        (by
          have hT := (Finset.mem_filter.1 (Finset.mem_filter.1 htup).1).2
          have himg := (Finset.mem_filter.1 htup).2
          have hinj : Function.Injective tup := by
            intro j₁ j₂ heq
            by_contra hne_j
            have hd := hT.2.1 j₁ j₂ hne_j
            rw [heq, disjoint_self] at hd
            exact (hT.1 j₂).ne_empty (Finset.bot_eq_empty ▸ hd)
          refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun ⟨B, hB⟩ => ?_⟩
          rw [← himg] at hB
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hB
          exact ⟨j, rfl⟩))
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro tup₁ _ tup₂ _ heq
      funext j
      exact congrArg (fun (e : Fin m ≃ π) => (e j).1) heq
    · intro e _
      refine ⟨fun j => (e j).1, ?_, ?_⟩
      · simp only [Finset.mem_filter, Tups, Finset.mem_univ, true_and]
        have himg : Finset.univ.image (fun j => (e j).1) = π := by
          ext B
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨fun ⟨j, hj⟩ => hj ▸ (e j).2, fun hB => ⟨e.symm ⟨B, hB⟩, by simp⟩⟩
        refine ⟨⟨fun j => hπ_ne _ (e j).2, fun j₁ j₂ hne => ?_, ?_⟩, himg⟩
        · exact hπ_disj (e j₁).2 (e j₂).2 fun h => hne (e.injective (Subtype.ext h))
        · ext x
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
          have hx : x ∈ π.biUnion id := by rw [hπ_biu]; exact Finset.mem_univ x
          obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.1 hx
          exact ⟨e.symm ⟨B, hB⟩, by simpa using hxB⟩
      · ext j; rfl
  rw [hfib_card, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- Valuation corollary of Lemma 2.6: if every proper nonempty `S` has `Val2Ge S.card (Λ.coeff S)`
and `univ` has `Val2Eq (M - 1) (Λ.coeff univ)`, then `Val2Eq (M - 1) ((sfExp Λ).coeff univ)`. -/
lemma sfExp_coeff_univ_val2Eq [Fintype ι] {Λ : SqFreeRing ι} (hΛ : Λ.coeff ∅ = 0)
    (hM : 1 ≤ Fintype.card ι)
    (hprop : ∀ S : Finset ι, S.Nonempty → S ≠ Finset.univ → Val2Ge S.card (Λ.coeff S))
    (huniv : Val2Eq (Fintype.card ι - 1) (Λ.coeff Finset.univ)) :
    Val2Eq (Fintype.card ι - 1) ((sfExp Λ).coeff Finset.univ) := by
  rw [sfExp_coeff_univ hΛ hM]
  have hM_eq : Fintype.card ι - 1 + 1 = Fintype.card ι := Nat.sub_add_cancel hM
  refine val2Eq_add_val2Ge huniv ?_
  rw [hM_eq]
  refine val2Ge_sum _ _ _ fun m hm => ?_
  have hm2 : 2 ≤ m := (Finset.mem_Icc.1 hm).1
  refine val2Ge_sum _ _ _ fun π hπ => ?_
  rcases (Finset.mem_filter.1 hπ).2 with ⟨hπ_card, hπ_ne, hπ_disj, hπ_biu⟩
  have hsum_card : ∑ B ∈ π, B.card = Fintype.card ι := by
    rw [← Finset.card_biUnion hπ_disj]
    change (π.biUnion id).card = Fintype.card ι
    rw [hπ_biu, Finset.card_univ]
  rw [← hsum_card]
  refine val2Ge_prod π Finset.card (fun B => Λ.coeff B) fun B hB => ?_
  refine hprop B (hπ_ne B hB) ?_
  intro hBuniv
  have hlt : 1 < π.card := by omega
  obtain ⟨B₁, hB₁, B₂, hB₂, hne12⟩ := Finset.one_lt_card.1 hlt
  have hex : ∃ B' ∈ π, B' ≠ B := by
    by_cases h : B₁ = B
    · exact ⟨B₂, hB₂, fun h2 => hne12 (h.trans h2.symm)⟩
    · exact ⟨B₁, hB₁, h⟩
  obtain ⟨B', hB', hne⟩ := hex
  have hdisj := hπ_disj hB hB' hne.symm
  rw [hBuniv] at hdisj
  obtain ⟨x, hx⟩ := hπ_ne B' hB'
  exact Finset.disjoint_left.1 hdisj (Finset.mem_univ x) hx

end SqFreeRing
end SqFreeRing

/- ### Section A2: Polynomial Derivative, Jacobi's Formula, and Trace Formula (Lemma 3.2) -/

section JacobiLogDet

open Polynomial

/-- Over any `ℚ`-algebra `K`, two polynomials with equal derivative and equal value at `0`
are equal. -/
lemma poly_eq_of_derivative_eq_of_eval_zero {K : Type*} [CommRing K] [Algebra ℚ K]
    {P Q : Polynomial K} (hder : P.derivative = Q.derivative) (h0 : P.eval 0 = Q.eval 0) :
    P = Q := by
  ext n
  cases n with
  | zero =>
    simpa [Polynomial.coeff_zero_eq_eval_zero] using h0
  | succ n =>
    have hcoeff := congrArg (fun R : Polynomial K => R.coeff n) hder
    simp only [Polynomial.coeff_derivative] at hcoeff
    have hinv : ((n + 1 : ℚ)⁻¹ : ℚ) • (P.coeff (n + 1) * ((n : K) + 1)) =
        ((n + 1 : ℚ)⁻¹ : ℚ) • (Q.coeff (n + 1) * ((n : K) + 1)) := by
      rw [hcoeff]
    have h1 : ∀ x : K, ((n + 1 : ℚ)⁻¹ : ℚ) • (x * ((n : K) + 1)) = x := fun x => by
      rw [Algebra.smul_def, mul_comm x, ← mul_assoc]
      have hcast : (algebraMap ℚ K ((n + 1 : ℚ)⁻¹)) * ((n : K) + 1) = 1 := by
        have hq : ((n : K) + 1) = algebraMap ℚ K (n + 1 : ℚ) := by simp
        rw [hq, ← map_mul, inv_mul_cancel₀ (by positivity), map_one]
      rw [hcast, one_mul]
    rw [h1, h1] at hinv
    exact hinv

/-- Leibniz rule for the derivative of a `Finset.prod` of polynomials. -/
lemma poly_derivative_prod {α K : Type*} [DecidableEq α] [CommRing K]
    (s : Finset α) (f : α → Polynomial K) :
    (∏ i ∈ s, f i).derivative =
      ∑ i ∈ s, (f i).derivative * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Polynomial.derivative_mul, ih, Finset.sum_insert ha,
      Finset.erase_insert ha, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hia.symm, Finset.prod_insert (by simp [ha])]
    ring

lemma det_updateRow_finset_sum {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]
    (B : Matrix α α R) (r : α) (s : Finset β) (u : β → α → R) :
    (B.updateRow r (∑ i ∈ s, u i)).det = ∑ i ∈ s, (B.updateRow r (u i)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact Matrix.det_eq_zero_of_row_eq_zero r fun c => by simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Matrix.det_updateRow_add, ih, Finset.sum_insert ha]

/-- **Jacobi's formula** over `Polynomial K`:
`(B.det).derivative = Matrix.trace (B.adjugate * B.map Polynomial.derivative)`. -/
lemma det_derivative_eq_trace_adjugate {α K : Type*} [Fintype α] [DecidableEq α] [CommRing K]
    (B : Matrix α α (Polynomial K)) :
    B.det.derivative = Matrix.trace (B.adjugate * B.map Polynomial.derivative) := by
  have h1 : B.det.derivative =
      ∑ r : α, (B.updateRow r (fun c => (B r c).derivative)).det := by
    rw [← Matrix.det_transpose, Matrix.det_apply, Polynomial.derivative_sum]
    have hterm : ∀ σ : Equiv.Perm α,
        (((Equiv.Perm.sign σ : ℤ) : Polynomial K) * ∏ j : α, B j (σ j)).derivative =
        ∑ r : α, ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
          ((B r (σ r)).derivative * ∏ j ∈ Finset.univ.erase r, B j (σ j)) := fun σ => by
      rw [Polynomial.derivative_mul, Polynomial.derivative_intCast, zero_mul, zero_add,
        poly_derivative_prod, Finset.mul_sum]
    have htr : ∀ σ : Equiv.Perm α, (∏ j : α, B.transpose (σ j) j) = ∏ j : α, B j (σ j) := fun _ => rfl
    simp_rw [Units.smul_def, zsmul_eq_mul, htr, hterm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Matrix.det_transpose, Matrix.det_apply]
    simp_rw [Units.smul_def, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => (B.updateRow r (fun c => (B r c).derivative)).transpose (σ j) j) (Finset.mem_univ r)]
    have hself : (B.updateRow r (fun c => (B r c).derivative)).transpose (σ r) r = (B r (σ r)).derivative := by
      simp [Matrix.transpose_apply, Matrix.updateRow_self]
    rw [hself]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    exact (congrFun (Matrix.updateRow_ne (Finset.ne_of_mem_erase hj)) (σ j)).symm
  rw [h1, Matrix.trace]
  simp_rw [Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hrow : (fun c => (B r c).derivative) =
      ∑ i : α, (B r i).derivative • Pi.single i (1 : Polynomial K) := by
    ext c; simp [Finset.sum_apply, Pi.single_apply]
  rw [hrow, det_updateRow_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.det_updateRow_smul, Matrix.map_apply, mul_comm, ← Matrix.adjugate_apply]

/-- Derivative of a power of a polynomial. -/
lemma poly_derivative_pow {K : Type*} [CommRing K] (p : Polynomial K) (n : ℕ) :
    (p ^ n).derivative = (n : Polynomial K) * p ^ (n - 1) * p.derivative := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [pow_succ, Polynomial.derivative_mul, ih]
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- **Matrix Exponential–Determinant–Trace Identity** in `SqFreeRing ι`:
for any matrix `X` over `SqFreeRing ι` whose entries have zero constant term,
`(1 + X).det = sfExp (∑ m ∈ Icc 1 M, ((-1)^(m-1) / m) • trace (X^m))`. -/
theorem det_one_add_eq_sfExp_trace {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (X : Matrix α α (SqFreeRing ι)) (hX : ∀ x y, (X x y).coeff ∅ = 0) :
    (1 + X).det =
      SqFreeRing.sfExp (∑ m ∈ Finset.Icc 1 (Fintype.card ι),
        ((-1 : ℚ) ^ (m - 1) / (m : ℚ)) • Matrix.trace (X ^ m)) := by
  let M := Fintype.card ι
  let A := SqFreeRing ι
  -- Work in Polynomial A with parameter s = Polynomial.X
  let B : Matrix α α (Polynomial A) :=
    (1 : Matrix α α (Polynomial A)) + (Polynomial.X : Polynomial A) • X.map Polynomial.C
  let Λp : Polynomial A :=
    ∑ m ∈ Finset.Icc 1 M,
      Polynomial.C (((-1 : ℚ) ^ (m - 1) / (m : ℚ)) • Matrix.trace (X ^ m)) * Polynomial.X ^ m
  -- All coefficients of Λp lie in 𝔪 (constant term 0)
  have hΛp_coeff_empty : ∀ d : ℕ, (Λp.coeff d).coeff ∅ = 0 := by
    intro d
    simp only [Λp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [SqFreeRing.sum_coeff]
    refine Finset.sum_eq_zero fun m hm => ?_
    split_ifs with hd
    · rw [mul_one, SqFreeRing.smul_coeff, Matrix.trace, SqFreeRing.sum_coeff]
      have hm1 : 0 < m := (Finset.mem_Icc.1 hm).1
      have hz : ∑ x : α, ((X ^ m).diag x).coeff ∅ = 0 :=
        Finset.sum_eq_zero fun x _ =>
          SqFreeRing.matrix_pow_coeff_eq_zero_of_card_lt hX m x x ∅ (by simpa using hm1)
      rw [hz, mul_zero]
    · simp
  have hΛp_der_coeff_empty : ∀ d : ℕ, (Λp.derivative.coeff d).coeff ∅ = 0 := by
    intro d
    rw [Polynomial.coeff_derivative]
    change SqFreeRing.coeffEmptyHom (Λp.coeff (d + 1) * ((d : A) + 1)) = 0
    rw [map_mul, show SqFreeRing.coeffEmptyHom (Λp.coeff (d + 1)) = 0 from hΛp_coeff_empty (d + 1),
      zero_mul]
  -- Degree-in-ι bound for any polynomial whose coefficients all lie in 𝔪
  have hpoly_nilp : ∀ (p : Polynomial A), (∀ d, (p.coeff d).coeff ∅ = 0) →
      ∀ k d : ℕ, ∀ S : Finset ι, S.card < k → ((p ^ k).coeff d).coeff S = 0 := by
    intro p hp k
    induction k with
    | zero => intro _ _ h; omega
    | succ k ih =>
      intro d S hS
      rw [pow_succ, Polynomial.coeff_mul, SqFreeRing.sum_coeff]
      refine Finset.sum_eq_zero fun uv _ => ?_
      refine SqFreeRing.mul_coeff_eq_zero_of_bound (ih uv.1) (fun T hT => ?_) S hS
      have h0 : T = ∅ := Finset.card_eq_zero.1 (by omega)
      rw [h0, hp uv.2]
  have hΛp_pow_mul_der : (-Λp) ^ M * (-Λp).derivative = 0 := by
    refine Polynomial.ext fun d => SqFreeRing.ext fun S => ?_
    rw [Polynomial.coeff_mul, SqFreeRing.sum_coeff, Polynomial.coeff_zero, SqFreeRing.zero_coeff]
    refine Finset.sum_eq_zero fun uv _ => ?_
    refine SqFreeRing.mul_coeff_eq_zero_of_bound
      (hpoly_nilp (-Λp) (fun d => by rw [Polynomial.coeff_neg, SqFreeRing.neg_coeff, hΛp_coeff_empty d, neg_zero]) M uv.1)
      (fun T (hT : T.card < 1) => ?_) S (Nat.lt_succ_of_le (Finset.card_le_univ S))
    have h0 : T = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [h0, Polynomial.derivative_neg, Polynomial.coeff_neg, SqFreeRing.neg_coeff,
      hΛp_der_coeff_empty uv.2, neg_zero]
  -- Define E(s) = ∑_{k=0}^M ((-Λp)^k / k!)
  let E : Polynomial A :=
    ∑ k ∈ Finset.range (M + 1), Polynomial.C ((k.factorial : ℚ)⁻¹ • (1 : A)) * (-Λp) ^ k
  -- E'(s) = (-Λp)' * E(s)
  have hE_der : E.derivative = (-Λp).derivative * E := by
    rw [Polynomial.derivative_sum]
    have h0 : (Polynomial.C (((0 : ℕ).factorial : ℚ)⁻¹ • (1 : A)) * (-Λp) ^ 0).derivative = 0 := by
      simp
    rw [Finset.sum_range_succ', h0, add_zero]
    have hterm : ∀ k ∈ Finset.range M,
        (Polynomial.C ((((k + 1).factorial : ℚ)⁻¹) • (1 : A)) * (-Λp) ^ (k + 1)).derivative =
        (-Λp).derivative * (Polynomial.C (((k.factorial : ℚ)⁻¹) • (1 : A)) * (-Λp) ^ k) := by
      intro k _
      rw [Polynomial.derivative_C_mul, poly_derivative_pow]
      simp only [Nat.add_sub_cancel]
      have hfac : (((k + 1).factorial : ℚ)⁻¹) • (1 : A) * ((k + 1 : ℕ) : A) =
          ((k.factorial : ℚ)⁻¹) • (1 : A) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one]
        have hnat : ((k + 1 : ℕ) : A) = algebraMap ℚ A ((k + 1 : ℕ) : ℚ) := by simp
        rw [hnat, ← map_mul]
        congr 1
        rw [Nat.factorial_succ, Nat.cast_mul]
        have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        have hkf : (k.factorial : ℚ) ≠ 0 := by positivity
        field_simp [hk1, hkf]
      have hC : Polynomial.C ((((k + 1).factorial : ℚ)⁻¹) • (1 : A)) * ((k + 1 : ℕ) : Polynomial A) =
          Polynomial.C (((k.factorial : ℚ)⁻¹) • (1 : A)) := by
        rw [← Polynomial.C_eq_natCast, ← map_mul, hfac]
      calc Polynomial.C ((((k + 1).factorial : ℚ)⁻¹) • (1 : A)) *
              ((((k + 1 : ℕ) : Polynomial A)) * (-Λp) ^ k * (-Λp).derivative)
          = (Polynomial.C ((((k + 1).factorial : ℚ)⁻¹) • (1 : A)) *
              ((k + 1 : ℕ) : Polynomial A)) * (-Λp) ^ k * (-Λp).derivative := by ring
        _ = Polynomial.C (((k.factorial : ℚ)⁻¹) • (1 : A)) * (-Λp) ^ k * (-Λp).derivative := by rw [hC]
        _ = (-Λp).derivative * (Polynomial.C (((k.factorial : ℚ)⁻¹) • (1 : A)) * (-Λp) ^ k) := by ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have hE_split : E = (∑ k ∈ Finset.range M,
        Polynomial.C ((k.factorial : ℚ)⁻¹ • (1 : A)) * (-Λp) ^ k) +
        Polynomial.C ((M.factorial : ℚ)⁻¹ • (1 : A)) * (-Λp) ^ M :=
      Finset.sum_range_succ _ M
    rw [hE_split, mul_add]
    have hlast : (-Λp).derivative * (Polynomial.C ((M.factorial : ℚ)⁻¹ • (1 : A)) * (-Λp) ^ M) = 0 := by
      calc (-Λp).derivative * (Polynomial.C ((M.factorial : ℚ)⁻¹ • (1 : A)) * (-Λp) ^ M)
          = Polynomial.C ((M.factorial : ℚ)⁻¹ • (1 : A)) * ((-Λp) ^ M * (-Λp).derivative) := by ring
        _ = 0 := by rw [hΛp_pow_mul_der, mul_zero]
    rw [hlast, add_zero]
  -- Compute B⁻¹ = ∑_{j=0}^M (-s X)^j and prove B * Binv = 1
  let sX : Matrix α α (Polynomial A) := (Polynomial.X : Polynomial A) • X.map Polynomial.C
  have hsX_pow : ∀ m : ℕ, sX ^ m = ((Polynomial.X : Polynomial A) ^ m) • (X ^ m).map Polynomial.C := by
    intro m
    induction m with
    | zero =>
      ext x y
      by_cases h : x = y <;> simp [h]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ, pow_succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ext x y
      simp [Matrix.mul_apply, map_sum, map_mul]
  have hsX_nilp : sX ^ (M + 1) = 0 := by
    rw [hsX_pow, SqFreeRing.matrix_pow_eq_zero hX]
    ext x y; simp
  let Binv : Matrix α α (Polynomial A) := ∑ j ∈ Finset.range (M + 1), (-sX) ^ j
  have hB_mul_Binv : B * Binv = 1 := by
    have h := geom_sum_mul (-sX) (M + 1)
    have hnilp : (-sX) ^ (M + 1) = 0 := by
      rw [neg_pow, hsX_nilp, mul_zero]
    rw [hnilp, zero_sub] at h
    have hneg : -sX - 1 = -B := by simp [B]; abel
    rw [hneg] at h
    have hmul : Binv * B = 1 := by
      calc Binv * B = -(Binv * (-B)) := by simp
        _ = -(-1) := by rw [h]
        _ = 1 := by simp
    -- Binv and B commute since both are polynomials in sX
    have hcomm : B * Binv = Binv * B := by
      simp only [B, Binv, add_mul, mul_add, one_mul, mul_one, Finset.mul_sum, Finset.sum_mul,
        Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      exact ((Commute.refl sX).neg_right.pow_right j).eq
    rw [hcomm, hmul]
  -- Adjugate = det • Binv
  have hadj : B.adjugate = B.det • Binv := by
    have h1 := Matrix.mul_adjugate B
    have h2 : Binv * (B * B.adjugate) = Binv * (B.det • (1 : Matrix α α (Polynomial A))) := by
      rw [h1]
    have hcomm : Binv * B = 1 := by
      have h := geom_sum_mul (-sX) (M + 1)
      have hnilp : (-sX) ^ (M + 1) = 0 := by rw [neg_pow, hsX_nilp, mul_zero]
      rw [hnilp, zero_sub] at h
      have hneg : -sX - 1 = -B := by simp [B]; abel
      rw [hneg] at h
      calc Binv * B = -(Binv * (-B)) := by simp
        _ = -(-1) := by rw [h]
        _ = 1 := by simp
    rw [← Matrix.mul_assoc, hcomm, one_mul, Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2
  -- Derivative of B is X.map C
  have hB_der : B.map Polynomial.derivative = X.map Polynomial.C := by
    ext x y
    simp only [B, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_X, one_mul,
      Polynomial.derivative_C, mul_zero, add_zero]
    by_cases h : x = y <;> simp [Matrix.one_apply, h]
  -- Derivative of Λp equals trace (Binv * X.map C)
  have hΛp_der : Λp.derivative = Matrix.trace (Binv * X.map Polynomial.C) := by
    rw [Polynomial.derivative_sum]
    have h1 : ∀ m ∈ Finset.Icc 1 M,
        (Polynomial.C (((-1 : ℚ) ^ (m - 1) / (m : ℚ)) • Matrix.trace (X ^ m)) *
          Polynomial.X ^ m).derivative =
        Polynomial.C (((-1 : ℚ) ^ (m - 1)) • Matrix.trace (X ^ m)) * Polynomial.X ^ (m - 1) := by
      intro m hm
      have hm0 : (m : ℚ) ≠ 0 := by
        have hm1 := (Finset.mem_Icc.1 hm).1
        exact_mod_cast (by omega : m ≠ 0)
      rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
      have hmul : (((-1 : ℚ) ^ (m - 1) / (m : ℚ)) • Matrix.trace (X ^ m)) * (m : A) =
          ((-1 : ℚ) ^ (m - 1)) • Matrix.trace (X ^ m) := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_assoc, mul_comm (Matrix.trace (X ^ m)), ← mul_assoc]
        congr 1
        have hnat : (m : A) = algebraMap ℚ A (m : ℚ) := by simp
        rw [hnat, ← map_mul, div_mul_cancel₀ _ hm0]
      calc Polynomial.C (((-1 : ℚ) ^ (m - 1) / (m : ℚ)) • Matrix.trace (X ^ m)) *
              ((m : Polynomial A) * Polynomial.X ^ (m - 1))
          = (Polynomial.C (((-1 : ℚ) ^ (m - 1) / (m : ℚ)) • Matrix.trace (X ^ m)) *
              Polynomial.C (m : A)) * Polynomial.X ^ (m - 1) := by simp [mul_assoc]
        _ = Polynomial.C (((-1 : ℚ) ^ (m - 1)) • Matrix.trace (X ^ m)) * Polynomial.X ^ (m - 1) := by
              rw [← map_mul, hmul]
    rw [Finset.sum_congr rfl h1]
    -- Reindex m ∈ Icc 1 M to j = m - 1 ∈ range M
    have hreidx :
        (∑ m ∈ Finset.Icc 1 M,
          Polynomial.C (((-1 : ℚ) ^ (m - 1)) • Matrix.trace (X ^ m)) * Polynomial.X ^ (m - 1)) =
        ∑ j ∈ Finset.range M,
          Polynomial.C (((-1 : ℚ) ^ j) • Matrix.trace (X ^ (j + 1))) * Polynomial.X ^ j := by
      refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
      · intro m hm; simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_range]; omega
      · intro m₁ hm₁ m₂ hm₂ h
        simp only [Finset.mem_Icc] at hm₁ hm₂; omega
      · intro j hj; simp only [Finset.mem_range] at hj
        exact ⟨j + 1, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
      · intro m hm
        have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Finset.mem_Icc.1 hm).1
        rw [hm1]
    rw [hreidx]
    -- Expand RHS: trace (Binv * X.map C)
    simp only [Binv, Finset.sum_mul, Matrix.trace_sum]
    rw [Finset.sum_range_succ]
    have hneg_pow : ∀ k : ℕ, (-sX) ^ k = ((-1 : Polynomial A) ^ k) • sX ^ k := fun k => by
      rw [← neg_one_smul (Polynomial A) sX, _root_.smul_pow]
    have hM_term : Matrix.trace ((-sX) ^ M * X.map Polynomial.C) = 0 := by
      rw [hneg_pow, Matrix.smul_mul, hsX_pow, Matrix.smul_mul]
      have hprod : (X ^ M).map Polynomial.C * X.map Polynomial.C = (X ^ (M + 1)).map Polynomial.C := by
        rw [pow_succ]; ext x y; simp [Matrix.mul_apply, map_sum, map_mul]
      rw [hprod, SqFreeRing.matrix_pow_eq_zero hX]
      have hz : ((0 : Matrix α α A).map Polynomial.C) = 0 := by ext x y; simp
      rw [hz, smul_zero, smul_zero, Matrix.trace_zero]
    rw [hM_term, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hneg_pow, Matrix.smul_mul, hsX_pow, Matrix.smul_mul]
    have hprod : (X ^ j).map Polynomial.C * X.map Polynomial.C = (X ^ (j + 1)).map Polynomial.C := by
      rw [pow_succ]; ext x y; simp [Matrix.mul_apply, map_sum, map_mul]
    rw [hprod, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    have htr : Matrix.trace ((X ^ (j + 1)).map Polynomial.C) = Polynomial.C (Matrix.trace (X ^ (j + 1))) := by
      simp [Matrix.trace, map_sum]
    rw [htr]
    have hneg1 : ((-1 : Polynomial A) ^ j) = Polynomial.C (((-1 : ℚ) ^ j) • (1 : A)) := by
      rw [Algebra.smul_def, mul_one, map_pow, map_neg, map_one, map_pow, map_neg, map_one]
    rw [hneg1]
    have hCsmul : Polynomial.C (((-1 : ℚ) ^ j) • Matrix.trace (X ^ (j + 1))) =
        Polynomial.C (((-1 : ℚ) ^ j) • (1 : A)) * Polynomial.C (Matrix.trace (X ^ (j + 1))) := by
      rw [← map_mul, Algebra.smul_mul_assoc, one_mul]
    rw [hCsmul]; ring
  -- Hence (E * B.det)' = 0!
  have hQ_der : (E * B.det).derivative = 0 := by
    rw [Polynomial.derivative_mul, hE_der, det_derivative_eq_trace_adjugate, hadj, hB_der,
      Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← hΛp_der, Polynomial.derivative_neg]
    ring
  have hQ_zero : (E * B.det).eval 0 = 1 := by
    rw [Polynomial.eval_mul]
    have hΛ0 : Λp.eval 0 = 0 := by
      simp only [Λp, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      refine Finset.sum_eq_zero fun m hm => ?_
      have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.1 hm).1; omega
      simp [zero_pow hm0]
    have hE0 : E.eval 0 = 1 := by
      simp only [E, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_neg, hΛ0, neg_zero]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk; simp [zero_pow hk]
      · intro h; exact (h (Finset.mem_range.2 (Nat.succ_pos _))).elim
    have hB0 : B.det.eval 0 = 1 := by
      change (Polynomial.evalRingHom (0 : A)) B.det = 1
      rw [RingHom.map_det]
      have hmap : (Polynomial.evalRingHom (0 : A)).mapMatrix B = 1 := by
        ext x y
        by_cases h : x = y <;> simp [B, Matrix.one_apply, h]
      rw [hmap, Matrix.det_one]
    rw [hE0, hB0, mul_one]
  have hQ_eq : E * B.det = 1 :=
    poly_eq_of_derivative_eq_of_eval_zero (by rw [hQ_der, Polynomial.derivative_one])
      (by rw [hQ_zero, Polynomial.eval_one])
  -- Evaluate at s = 1
  have h1 := congrArg (Polynomial.eval (1 : A)) hQ_eq
  rw [Polynomial.eval_mul, Polynomial.eval_one] at h1
  let Λ : A := ∑ m ∈ Finset.Icc 1 M, ((-1 : ℚ) ^ (m - 1) / (m : ℚ)) • Matrix.trace (X ^ m)
  have hΛ1 : Λp.eval 1 = Λ := by
    simp [Λp, Λ, Polynomial.eval_finsetSum]
  have hE1 : E.eval 1 = SqFreeRing.sfExp (-Λ) := by
    simp only [E, SqFreeRing.sfExp, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_neg, hΛ1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_mul_assoc, one_mul]
  have hB1 : B.det.eval 1 = (1 + X).det := by
    change (Polynomial.evalRingHom (1 : A)) B.det = (1 + X).det
    rw [RingHom.map_det]
    congr 1
    refine Matrix.ext fun x y => ?_
    by_cases h : x = y <;> simp [B, h]
  rw [hE1, hB1] at h1
  have hΛ_empty : Λ.coeff ∅ = 0 := by
    rw [SqFreeRing.sum_coeff]
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [SqFreeRing.smul_coeff, Matrix.trace, SqFreeRing.sum_coeff]
    have hm1 : 0 < m := (Finset.mem_Icc.1 hm).1
    have hz : ∑ x : α, ((X ^ m).diag x).coeff ∅ = 0 :=
      Finset.sum_eq_zero fun x _ =>
        SqFreeRing.matrix_pow_coeff_eq_zero_of_card_lt hX m x x ∅ (by simpa using hm1)
    rw [hz, mul_zero]
  calc (1 + X).det = 1 * (1 + X).det := (one_mul _).symm
    _ = (SqFreeRing.sfExp Λ * SqFreeRing.sfExp (-Λ)) * (1 + X).det := by
          rw [SqFreeRing.sfExp_mul_neg hΛ_empty]
    _ = SqFreeRing.sfExp Λ * (SqFreeRing.sfExp (-Λ) * (1 + X).det) := by rw [mul_assoc]
    _ = SqFreeRing.sfExp Λ := by rw [h1, mul_one]

/-- Coefficient formula for `X = ∑ i, var i • BMat i`:
`((1/2) • ∑ m ∈ Icc 1 M, ((-1)^(m-1)/m) • trace (X^m)).coeff S = Lcoeff S` for nonempty `S`. -/
lemma logDet_half_coeff_eq_Lcoeff {s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hs : 1 ≤ s) (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) :
    let X : Matrix (𝔽₂ s) (𝔽₂ s) (SqFreeRing ι) :=
      ∑ i : ι, SqFreeRing.var i • (BMat hs d hd i).map (algebraMap ℚ (SqFreeRing ι))
    let Λ : SqFreeRing ι :=
      (1 / 2 : ℚ) • ∑ m ∈ Finset.Icc 1 (Fintype.card ι),
        ((-1 : ℚ) ^ (m - 1) / (m : ℚ)) • Matrix.trace (X ^ m)
    Λ.coeff ∅ = 0 ∧ ∀ S : Finset ι, S.Nonempty → Λ.coeff S = Lcoeff hs d hd S := by
  intro X Λ
  have hX_pow : ∀ m : ℕ,
      X ^ m = ∑ f : Fin m → ι,
        ((List.ofFn f).map SqFreeRing.var).prod •
          (BWord hs d hd (List.ofFn f)).map (algebraMap ℚ (SqFreeRing ι)) := by
    intro m
    induction m with
    | zero =>
      have hu : (Finset.univ : Finset (Fin 0 → ι)) = {Fin.elim0} := by
        ext f; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; ext i; exact Fin.elim0 i
      rw [pow_zero, hu, Finset.sum_singleton]
      refine Matrix.ext fun x y => SqFreeRing.ext fun S => ?_
      by_cases h : x = y <;> simp [BWord, h, Matrix.one_apply]
    | succ m ih =>
      rw [pow_succ', ih, Finset.sum_mul]
      simp_rw [Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hsplit := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => ι)).symm
        (fun f : Fin (m + 1) → ι =>
          ((List.ofFn f).map SqFreeRing.var).prod •
            (BWord hs d hd (List.ofFn f)).map (algebraMap ℚ (SqFreeRing ι)))
        (fun p : ι × (Fin m → ι) =>
          (SqFreeRing.var p.1 * ((List.ofFn p.2).map SqFreeRing.var).prod) •
            ((BMat hs d hd p.1).map (algebraMap ℚ (SqFreeRing ι)) *
              (BWord hs d hd (List.ofFn p.2)).map (algebraMap ℚ (SqFreeRing ι))))
        (fun f => by
          have hcons : List.ofFn f = f 0 :: List.ofFn (fun j : Fin m => f j.succ) :=
            List.ofFn_succ
          simp only [Fin.consEquiv_symm_apply, hcons, List.map_cons, List.prod_cons, BWord]
          congr 1
          ext x y
          simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]
          rfl)
      rw [hsplit, Fintype.sum_prod_type]
  have htr_pow : ∀ m : ℕ, ∀ S : Finset ι,
      (Matrix.trace (X ^ m)).coeff S =
        if S.card = m then ∑ w ∈ orderings S, Matrix.trace (BWord hs d hd w) else 0 := by
    intro m S
    rw [hX_pow m, Matrix.trace_sum, SqFreeRing.sum_coeff]
    have hterm : ∀ f : Fin m → ι,
        (Matrix.trace (((List.ofFn f).map SqFreeRing.var).prod •
          (BWord hs d hd (List.ofFn f)).map (algebraMap ℚ (SqFreeRing ι)))).coeff S =
        if (List.ofFn f).Nodup ∧ (List.ofFn f).toFinset = S then
          Matrix.trace (BWord hs d hd (List.ofFn f))
        else 0 := by
      intro f
      rw [Matrix.trace_smul, smul_eq_mul, SqFreeRing.list_prod_var]
      have htrC : Matrix.trace ((BWord hs d hd (List.ofFn f)).map (algebraMap ℚ (SqFreeRing ι))) =
          algebraMap ℚ (SqFreeRing ι) (Matrix.trace (BWord hs d hd (List.ofFn f))) := by
        simp [Matrix.trace, map_sum]
      rw [htrC, mul_comm, ← Algebra.smul_def]
      by_cases hnd : (List.ofFn f).Nodup
      · simp only [if_pos hnd, SqFreeRing.smul_coeff, SqFreeRing.mon_coeff]
        by_cases hfin : (List.ofFn f).toFinset = S
        · simp [hnd, hfin]
        · simp [hfin, Ne.symm hfin]
      · simp [hnd]
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    by_cases hcard : S.card = m
    · rw [if_pos hcard]
      refine Finset.sum_bij (fun f _ => List.ofFn f) ?_ ?_ ?_ ?_
      · intro f hf
        rw [Finset.mem_filter] at hf
        exact mem_orderings.2 hf.2
      · intro f₁ _ f₂ _ heq
        exact List.ofFn_injective heq
      · intro w hw
        have hlen : w.length = m := (length_of_mem_orderings hw).trans hcard
        refine ⟨fun i => w[i.val]'(by omega), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hof : List.ofFn (fun i : Fin m => w[i.val]'(by omega)) = w := by
            refine List.ext_get (by simp [hlen]) fun i h1 h2 => by simp
          rw [hof]
          exact mem_orderings.1 hw
        · refine List.ext_get (by simp [hlen]) fun i h1 h2 => by simp
      · intro _ _; rfl
    · rw [if_neg hcard]
      refine Finset.sum_eq_zero fun f hf => ?_
      rw [Finset.mem_filter] at hf
      have hlen : S.card = m := by
        rw [← hf.2.2, List.toFinset_card_of_nodup hf.2.1, List.length_ofFn]
      exact (hcard hlen).elim
  constructor
  · simp only [Λ, SqFreeRing.smul_coeff, SqFreeRing.sum_coeff]
    have h0 : ∑ m ∈ Finset.Icc 1 (Fintype.card ι),
        ((-1 : ℚ) ^ (m - 1) / (m : ℚ)) * (Matrix.trace (X ^ m)).coeff ∅ = 0 := by
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [htr_pow m ∅]
      have hm0 : (0 : ℕ) ≠ m := by have := (Finset.mem_Icc.1 hm).1; omega
      simp [hm0]
    rw [h0, mul_zero]
  · intro S hSne
    simp only [Λ, SqFreeRing.smul_coeff, SqFreeRing.sum_coeff]
    have hcard_mem : S.card ∈ Finset.Icc 1 (Fintype.card ι) :=
      Finset.mem_Icc.2 ⟨Finset.card_pos.2 hSne, Finset.card_le_univ S⟩
    rw [Finset.sum_eq_single S.card]
    · rw [htr_pow S.card S, if_pos rfl, Lcoeff]
      ring
    · intro m _ hm
      rw [htr_pow m S, if_neg (Ne.symm hm), mul_zero]
    · intro h; exact (h hcard_mem).elim

end JacobiLogDet

/- ### Section A3: Pfaffian, `Pf(A)^2 = det(A)`, `Pf(J0) = ±1`, and Lemma 2.1 -/

section Pfaffian

/-- Base fixed-point-free involution swapping `(k, 0) ↔ (k, 1)` on `Fin M × Fin 2`. -/
def baseInv (M : ℕ) : Equiv.Perm (Fin M × Fin 2) where
  toFun p := (p.1, 1 - p.2)
  invFun p := (p.1, 1 - p.2)
  left_inv p := by rcases p with ⟨k, b⟩; fin_cases b <;> rfl
  right_inv p := by rcases p with ⟨k, b⟩; fin_cases b <;> rfl

/-- Pfaffian of a matrix indexed by `Fin M × Fin 2` over a `ℚ`-algebra `K`. -/
def pfaffian {M : ℕ} {K : Type*} [CommRing K] [Algebra ℚ K]
    (A : Matrix (Fin M × Fin 2) (Fin M × Fin 2) K) : K :=
  (((2 ^ M * M.factorial : ℕ) : ℚ)⁻¹) •
    ∑ π : Equiv.Perm (Fin M × Fin 2),
      ((Equiv.Perm.sign π : ℤ) : K) * ∏ k : Fin M, A (π (k, 0)) (π (k, 1))

/-- The set of fixed-point-free involutions on `α`. -/
def fpfInvolutions (α : Type*) [Fintype α] [DecidableEq α] : Finset (Equiv.Perm α) :=
  Finset.univ.filter fun ι => ι * ι = 1 ∧ ∀ x, ι x ≠ x

/-- The hyperoctahedral subgroup centralizing `baseInv M`: pair permutations + pair flips. -/
def pairAction {M : ℕ} (σ : Equiv.Perm (Fin M)) (fl : Fin M → Bool) :
    Equiv.Perm (Fin M × Fin 2) where
  toFun p := (σ p.1, if fl p.1 then 1 - p.2 else p.2)
  invFun p := (σ.symm p.1, if fl (σ.symm p.1) then 1 - p.2 else p.2)
  left_inv p := by
    rcases p with ⟨k, b⟩
    simp only [Equiv.symm_apply_apply]
    cases fl k <;> fin_cases b <;> rfl
  right_inv p := by
    rcases p with ⟨k, b⟩
    simp only [Equiv.apply_symm_apply]
    cases fl (σ.symm k) <;> fin_cases b <;> rfl

lemma pairPerm_sign {M : ℕ} (σ : Equiv.Perm (Fin M)) :
    Equiv.Perm.sign (pairAction σ (fun _ => false)) = 1 := by
  let leftEmb : Equiv.Perm (Fin M) →* Equiv.Perm (Fin M × Fin 2) :=
    { toFun := fun τ =>
        { toFun := fun p => if p.2 = 0 then (τ p.1, 0) else p
          invFun := fun p => if p.2 = 0 then (τ.symm p.1, 0) else p
          left_inv := fun ⟨k, b⟩ => by fin_cases b <;> simp
          right_inv := fun ⟨k, b⟩ => by fin_cases b <;> simp }
      map_one' := Equiv.Perm.ext fun ⟨k, b⟩ => by fin_cases b <;> rfl
      map_mul' := fun τ₁ τ₂ => Equiv.Perm.ext fun ⟨k, b⟩ => by fin_cases b <;> rfl }
  let rightEmb : Equiv.Perm (Fin M) →* Equiv.Perm (Fin M × Fin 2) :=
    { toFun := fun τ =>
        { toFun := fun p => if p.2 = 1 then (τ p.1, 1) else p
          invFun := fun p => if p.2 = 1 then (τ.symm p.1, 1) else p
          left_inv := fun ⟨k, b⟩ => by fin_cases b <;> simp
          right_inv := fun ⟨k, b⟩ => by fin_cases b <;> simp }
      map_one' := Equiv.Perm.ext fun ⟨k, b⟩ => by fin_cases b <;> rfl
      map_mul' := fun τ₁ τ₂ => Equiv.Perm.ext fun ⟨k, b⟩ => by fin_cases b <;> rfl }
  have hfactor : pairAction σ (fun _ => false) = leftEmb σ * rightEmb σ :=
    Equiv.Perm.ext fun ⟨k, b⟩ => by fin_cases b <;> rfl
  have hconj : rightEmb σ = baseInv M * leftEmb σ * (baseInv M)⁻¹ :=
    Equiv.Perm.ext fun ⟨k, b⟩ => by fin_cases b <;> simp [leftEmb, rightEmb, baseInv]
  rw [hfactor, map_mul, hconj, map_mul, map_mul, map_inv]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (leftEmb σ)) with h1 | h1 <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign (baseInv M)) with h2 | h2 <;>
    simp [h1, h2]

lemma pairFlip_sign {M : ℕ} (fl : Fin M → Bool) :
    ((Equiv.Perm.sign (pairAction 1 fl) : ℤ) : ℚ) =
      ∏ k : Fin M, if fl k then (-1 : ℚ) else 1 := by
  let S : Finset (Fin M) := Finset.univ.filter (fun k => fl k = true)
  have hprod_eq : pairAction 1 fl =
      (S.toList.map fun k => Equiv.swap ((k, (0 : Fin 2))) ((k, (1 : Fin 2)))).prod := by
    have haux : ∀ L : List (Fin M), L.Nodup →
        ∀ p : Fin M × Fin 2,
          ((L.map fun k => Equiv.swap ((k, (0 : Fin 2))) ((k, (1 : Fin 2)))).prod) p =
          (p.1, if p.1 ∈ L then 1 - p.2 else p.2) := by
      intro L hnd
      induction L with
      | nil => intro ⟨k, b⟩; simp
      | cons a t ih =>
        rw [List.nodup_cons] at hnd
        intro ⟨k, b⟩
        simp only [List.map_cons, List.prod_cons, Equiv.Perm.coe_mul, Function.comp_apply,
          ih hnd.2, List.mem_cons]
        by_cases hka : k = a
        · subst hka
          have hnt : k ∉ t := hnd.1
          simp only [hnt, ↓reduceIte, true_or]
          fin_cases b
          · simp [Equiv.swap_apply_left]
          · simp [Equiv.swap_apply_right]
        · simp only [hka, false_or]
          have hne0 : ((k, if k ∈ t then 1 - b else b) : Fin M × Fin 2) ≠ (a, 0) :=
            fun h => hka (congrArg Prod.fst h)
          have hne1 : ((k, if k ∈ t then 1 - b else b) : Fin M × Fin 2) ≠ (a, 1) :=
            fun h => hka (congrArg Prod.fst h)
          rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]
    refine Equiv.Perm.ext fun ⟨k, b⟩ => ?_
    have h := haux S.toList (Finset.nodup_toList S) (k, b)
    rw [h]
    apply Prod.ext
    · rfl
    · have hmem : k ∈ S.toList ↔ fl k = true := by simp [S]
      by_cases hf : fl k = true
      · simp [pairAction, hf, hmem.2 hf]
      · have hnf : k ∉ S.toList := fun hc => hf (hmem.1 hc)
        simp [pairAction, hf, hnf]
  rw [hprod_eq, map_list_prod]
  have hlist : ((S.toList.map fun k => Equiv.swap (k, (0 : Fin 2)) (k, (1 : Fin 2))).map
      Equiv.Perm.sign).prod = (-1 : ℤˣ) ^ S.card := by
    rw [List.map_map]
    have hconst : (S.toList.map (Equiv.Perm.sign ∘ fun k => Equiv.swap (k, (0 : Fin 2)) (k, (1 : Fin 2)))) =
        List.replicate S.toList.length (-1 : ℤˣ) := by
      refine List.eq_replicate_iff.2 ⟨by simp, fun x hx => ?_⟩
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hx
      exact Equiv.Perm.sign_swap fun h => (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.snd h)
    rw [hconst, List.prod_replicate, Finset.length_toList]
  rw [hlist]
  have hcast : ((((-1 : ℤˣ) ^ S.card : ℤˣ) : ℤ) : ℚ) = (-1 : ℚ) ^ S.card := by
    induction S.card with
    | zero => simp
    | succ n _ => simp [pow_succ]
  rw [hcast]
  have hprod : (∏ k : Fin M, if fl k then (-1 : ℚ) else 1) = (-1 : ℚ) ^ S.card := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => fl k = true)]
    have h1 : (∏ k ∈ Finset.univ.filter (fun k => fl k = true),
        if fl k then (-1 : ℚ) else 1) = (-1 : ℚ) ^ S.card := by
      calc (∏ k ∈ Finset.univ.filter (fun k => fl k = true), if fl k then (-1 : ℚ) else 1)
          = ∏ _k ∈ Finset.univ.filter (fun k => fl k = true), (-1 : ℚ) :=
            Finset.prod_congr rfl fun k hk => by simp [(Finset.mem_filter.1 hk).2]
        _ = (-1 : ℚ) ^ S.card := by simp [S]
    have h2 : (∏ k ∈ Finset.univ.filter (fun k => ¬ fl k = true),
        if fl k then (-1 : ℚ) else 1) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      have hfk : fl k = false := Bool.eq_false_iff.2 (Finset.mem_filter.1 hk).2
      simp [hfk]
    rw [h1, h2, mul_one]
  exact hprod.symm

lemma pairAction_term_eq {M : ℕ} {K : Type*} [CommRing K] [Algebra ℚ K]
    {A : Matrix (Fin M × Fin 2) (Fin M × Fin 2) K}
    (hskew : ∀ x y, A y x = -A x y)
    (π : Equiv.Perm (Fin M × Fin 2)) (σ : Equiv.Perm (Fin M)) (fl : Fin M → Bool) :
    ((Equiv.Perm.sign (π * pairAction σ fl) : ℤ) : K) *
      ∏ k : Fin M, A ((π * pairAction σ fl) (k, 0)) ((π * pairAction σ fl) (k, 1)) =
    ((Equiv.Perm.sign π : ℤ) : K) * ∏ k : Fin M, A (π (k, 0)) (π (k, 1)) := by
  have hsplit : pairAction σ fl = pairAction σ (fun _ => false) * pairAction 1 fl := by
    ext ⟨k, b⟩ <;> cases fl k <;> fin_cases b <;> simp [pairAction]
  have hsign : ((Equiv.Perm.sign (pairAction σ fl) : ℤ) : K) =
      ∏ k : Fin M, if fl k then (-1 : K) else 1 := by
    rw [hsplit, map_mul, pairPerm_sign, one_mul]
    have hq := congrArg (algebraMap ℚ K) (pairFlip_sign fl)
    simpa [map_prod, apply_ite] using hq
  rw [map_mul, Units.val_mul, Int.cast_mul, hsign, mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  have hterm : ∀ k : Fin M,
      (if fl k then (-1 : K) else 1) *
        A ((π * pairAction σ fl) (k, 0)) ((π * pairAction σ fl) (k, 1)) =
      A (π (σ k, 0)) (π (σ k, 1)) := fun k => by
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, pairAction, Equiv.coe_fn_mk]
    cases fl k
    · simp
    · simp only [↓reduceIte, neg_one_mul]
      have h0 : (1 : Fin 2) - 0 = 1 := by decide
      have h1 : (1 : Fin 2) - 1 = 0 := by decide
      rw [h0, h1, hskew, neg_neg]
  rw [Finset.prod_congr rfl fun k _ => hterm k]
  exact Equiv.prod_comp σ (fun k => A (π (k, 0)) (π (k, 1)))

/-- Every fixed-point-free involution `ι` on `Fin M × Fin 2` is conjugate to `baseInv M`. -/
lemma exists_perm_realizing_fpfInv {M : ℕ} {ι : Equiv.Perm (Fin M × Fin 2)}
    (hι : ι ∈ fpfInvolutions (Fin M × Fin 2)) :
    ∃ π : Equiv.Perm (Fin M × Fin 2), π * baseInv M * π⁻¹ = ι := by
  rcases (Finset.mem_filter.1 hι).2 with ⟨hsq, hfpf⟩
  have hinv : ∀ x, ι (ι x) = x := fun x => by
    have := Equiv.Perm.congr_fun hsq x; simpa using this
  -- Use finProdFinEquiv to pick the smaller element of each 2-element orbit
  let idx : Fin M × Fin 2 → ℕ := fun x => (finProdFinEquiv x).val
  have hidx_inj : Function.Injective idx := fun a b h =>
    finProdFinEquiv.injective (Fin.ext h)
  let S : Finset (Fin M × Fin 2) := Finset.univ.filter fun x => idx x < idx (ι x)
  have hS_disj : Disjoint S (S.image ι) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx2
    have h1 := (Finset.mem_filter.1 hx1).2
    have h2 := (Finset.mem_filter.1 hy).2
    rw [hinv] at h1
    omega
  have hS_union : S ∪ S.image ι = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
    have hne : idx x ≠ idx (ι x) := fun h => hfpf x (hidx_inj h).symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlt⟩)
    · refine Or.inr ⟨ι x, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hinv x⟩
      rw [hinv]; exact hgt
  have hS_card : S.card = M := by
    have h1 := congrArg Finset.card hS_union
    rw [Finset.card_union_of_disjoint hS_disj, Finset.card_image_of_injective _ ι.injective,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h1
    omega
  let eS : Fin M ≃ S := (Fintype.equivFinOfCardEq (by simp [hS_card])).symm
  let πFun : Fin M × Fin 2 → Fin M × Fin 2 := fun p =>
    if p.2 = 0 then (eS p.1).1 else ι (eS p.1).1
  have hπ_inj : Function.Injective πFun := by
    rintro ⟨k₁, b₁⟩ ⟨k₂, b₂⟩ h
    fin_cases b₁ <;> fin_cases b₂
    · simp only [πFun] at h
      exact Prod.ext (eS.injective (Subtype.ext (by simpa using h))) rfl
    · have h' : (eS k₁).1 = ι (eS k₂).1 := by simpa [πFun] using h
      exfalso
      exact Finset.disjoint_left.1 hS_disj (eS k₁).2
        (h' ▸ Finset.mem_image_of_mem ι (eS k₂).2)
    · have h' : ι (eS k₁).1 = (eS k₂).1 := by simpa [πFun] using h
      exfalso
      exact Finset.disjoint_left.1 hS_disj (eS k₂).2
        (h'.symm ▸ Finset.mem_image_of_mem ι (eS k₁).2)
    · have h' : ι (eS k₁).1 = ι (eS k₂).1 := by simpa [πFun] using h
      exact Prod.ext (eS.injective (Subtype.ext (ι.injective h'))) rfl
  let π : Equiv.Perm (Fin M × Fin 2) := Equiv.ofBijective πFun (Finite.injective_iff_bijective.1 hπ_inj)
  refine ⟨π, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  refine Equiv.Perm.ext fun ⟨k, b⟩ => ?_
  fin_cases b
  · simp [π, πFun, baseInv]
  · simp [π, πFun, baseInv, hinv]

lemma exists_pairAction_of_comm_baseInv {M : ℕ} {g : Equiv.Perm (Fin M × Fin 2)}
    (hg_comm : g * baseInv M = baseInv M * g) :
    ∃ σ : Equiv.Perm (Fin M), ∃ fl : Fin M → Bool, g = pairAction σ fl := by
  have hg_pair : ∀ k : Fin M, (g (k, 1)).1 = (g (k, 0)).1 ∧ (g (k, 1)).2 = 1 - (g (k, 0)).2 := by
    intro k
    have h := Equiv.Perm.congr_fun hg_comm (k, 0)
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, baseInv, Equiv.coe_fn_mk] at h
    have h10 : (1 : Fin 2) - 0 = 1 := by decide
    rw [h10] at h
    exact ⟨by simpa using congrArg Prod.fst h, by simpa using congrArg Prod.snd h⟩
  let σFun : Fin M → Fin M := fun k => (g (k, 0)).1
  have hσ_inj : Function.Injective σFun := by
    intro k₁ k₂ hk
    by_cases hb : (g (k₁, 0)).2 = (g (k₂, 0)).2
    · exact congrArg Prod.fst (g.injective (Prod.ext hk hb))
    · have hb' : (g (k₁, 1)).2 = (g (k₂, 0)).2 := by
        rw [(hg_pair k₁).2]
        generalize ha : (g (k₁, 0)).2 = a at hb ⊢
        generalize hc : (g (k₂, 0)).2 = c at hb ⊢
        fin_cases a <;> fin_cases c <;> simp_all
      have heq := g.injective (Prod.ext ((hg_pair k₁).1.trans hk) hb')
      exact ((by decide : (1 : Fin 2) ≠ 0) (congrArg Prod.snd heq)).elim
  let σ : Equiv.Perm (Fin M) := Equiv.ofBijective σFun (Finite.injective_iff_bijective.1 hσ_inj)
  let fl : Fin M → Bool := fun k => decide ((g (k, 0)).2 = 1)
  refine ⟨σ, fl, Equiv.Perm.ext fun ⟨k, b⟩ => ?_⟩
  rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
  · apply Prod.ext
    · rfl
    · simp only [pairAction, Equiv.coe_fn_mk, fl]
      generalize ha : (g (k, 0)).2 = a
      rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl <;> rfl
  · apply Prod.ext
    · exact (hg_pair k).1
    · simp only [pairAction, Equiv.coe_fn_mk, fl]
      rw [(hg_pair k).2]
      generalize ha : (g (k, 0)).2 = a
      rcases (show a = 0 ∨ a = 1 by fin_cases a <;> simp) with rfl | rfl <;> rfl

/-- Canonical Pfaffian summand of a fixed-point-free involution `ι`. -/
noncomputable def pfTerm {M : ℕ} {K : Type*} [CommRing K]
    (A : Matrix (Fin M × Fin 2) (Fin M × Fin 2) K)
    (ι : Equiv.Perm (Fin M × Fin 2)) : K :=
  if h : ι ∈ fpfInvolutions (Fin M × Fin 2) then
    let π := Classical.choose (exists_perm_realizing_fpfInv h)
    ((Equiv.Perm.sign π : ℤ) : K) * ∏ k : Fin M, A (π (k, 0)) (π (k, 1))
  else 0

lemma pfTerm_eq_of_realizing {M : ℕ} {K : Type*} [CommRing K] [Algebra ℚ K]
    {A : Matrix (Fin M × Fin 2) (Fin M × Fin 2) K}
    (hskew : ∀ x y, A y x = -A x y)
    {ι : Equiv.Perm (Fin M × Fin 2)} (hι : ι ∈ fpfInvolutions (Fin M × Fin 2))
    {π : Equiv.Perm (Fin M × Fin 2)} (hπ : π * baseInv M * π⁻¹ = ι) :
    pfTerm A ι = ((Equiv.Perm.sign π : ℤ) : K) * ∏ k : Fin M, A (π (k, 0)) (π (k, 1)) := by
  simp only [pfTerm, dif_pos hι]
  set π₀ := Classical.choose (exists_perm_realizing_fpfInv hι)
  have hπ₀ : π₀ * baseInv M * π₀⁻¹ = ι := Classical.choose_spec (exists_perm_realizing_fpfInv hι)
  let g : Equiv.Perm (Fin M × Fin 2) := π⁻¹ * π₀
  have hg_comm : g * baseInv M = baseInv M * g := by
    have h1 : π * baseInv M * π⁻¹ = π₀ * baseInv M * π₀⁻¹ := hπ.trans hπ₀.symm
    have h2 : baseInv M * (π⁻¹ * π₀) = (π⁻¹ * π₀) * baseInv M := by
      calc baseInv M * (π⁻¹ * π₀)
          = π⁻¹ * (π * baseInv M * π⁻¹) * π₀ := by group
        _ = π⁻¹ * (π₀ * baseInv M * π₀⁻¹) * π₀ := by rw [h1]
        _ = (π⁻¹ * π₀) * baseInv M := by group
    exact h2.symm
  obtain ⟨σ, fl, hg_eq⟩ := exists_pairAction_of_comm_baseInv hg_comm
  have hπ₀_eq : π₀ = π * pairAction σ fl := by rw [← hg_eq]; simp [g]
  rw [hπ₀_eq]
  exact pairAction_term_eq hskew π σ fl

/-- **Matching-sum formula for Pfaffian**: `pfaffian A = ∑ ι ∈ fpfInvolutions, pfTerm A ι`. -/
lemma pfaffian_eq_sum_fpfInvolutions {M : ℕ} {K : Type*} [CommRing K] [Algebra ℚ K]
    {A : Matrix (Fin M × Fin 2) (Fin M × Fin 2) K}
    (hskew : ∀ x y, A y x = -A x y) :
    pfaffian A = ∑ ι ∈ fpfInvolutions (Fin M × Fin 2), pfTerm A ι := by
  rw [pfaffian]
  let proj : Equiv.Perm (Fin M × Fin 2) → Equiv.Perm (Fin M × Fin 2) :=
    fun π => π * baseInv M * π⁻¹
  have hproj_mem : ∀ π ∈ (Finset.univ : Finset (Equiv.Perm (Fin M × Fin 2))),
      proj π ∈ fpfInvolutions (Fin M × Fin 2) := by
    intro π _
    simp only [fpfInvolutions, Finset.mem_filter, Finset.mem_univ, true_and, proj]
    refine ⟨?_, ?_⟩
    · have hbase : baseInv M * baseInv M = 1 :=
        Equiv.Perm.ext fun ⟨k, b⟩ => by
          fin_cases b <;> simp [baseInv]
      calc (π * baseInv M * π⁻¹) * (π * baseInv M * π⁻¹)
          = π * (baseInv M * baseInv M) * π⁻¹ := by group
        _ = 1 := by rw [hbase]; group
    · intro x hx
      have h1 : baseInv M (π⁻¹ x) = π⁻¹ x := by
        apply π.injective
        simpa [Equiv.Perm.coe_mul] using hx
      rcases hpx : π⁻¹ x with ⟨k, b⟩
      rw [hpx] at h1
      fin_cases b <;> simp [baseInv] at h1
  rw [← Finset.sum_fiberwise_of_maps_to hproj_mem, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ι hι => ?_
  have hconst : ∀ π ∈ Finset.univ.filter (fun π => proj π = ι),
      ((Equiv.Perm.sign π : ℤ) : K) * ∏ k : Fin M, A (π (k, 0)) (π (k, 1)) = pfTerm A ι := by
    intro π hπ
    exact (pfTerm_eq_of_realizing hskew hι (Finset.mem_filter.1 hπ).2).symm
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  -- Fiber cardinality = 2^M * M!
  obtain ⟨π₀, hπ₀⟩ := exists_perm_realizing_fpfInv hι
  have hfib : (Finset.univ.filter (fun π => proj π = ι)).card = 2 ^ M * M.factorial := by
    have hcard : Fintype.card (Equiv.Perm (Fin M) × (Fin M → Bool)) = 2 ^ M * M.factorial := by
      rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, mul_comm]
    rw [← hcard]
    refine Finset.card_bij (fun (p : Equiv.Perm (Fin M) × (Fin M → Bool)) _ => π₀ * pairAction p.1 p.2)
      ?_ ?_ ?_ |>.symm
    · intro ⟨σ, fl⟩ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, proj]
      have hcomm : pairAction σ fl * baseInv M = baseInv M * pairAction σ fl :=
        Equiv.Perm.ext fun ⟨k, b⟩ => by
          cases hfk : fl k <;> fin_cases b <;> simp [pairAction, baseInv, hfk]
      calc (π₀ * pairAction σ fl) * baseInv M * (π₀ * pairAction σ fl)⁻¹
          = π₀ * (pairAction σ fl * baseInv M) * (pairAction σ fl)⁻¹ * π₀⁻¹ := by group
        _ = π₀ * (baseInv M * pairAction σ fl) * (pairAction σ fl)⁻¹ * π₀⁻¹ := by rw [hcomm]
        _ = π₀ * baseInv M * π₀⁻¹ := by group
        _ = ι := hπ₀
    · rintro ⟨σ₁, fl₁⟩ _ ⟨σ₂, fl₂⟩ _ heq
      have h1 : pairAction σ₁ fl₁ = pairAction σ₂ fl₂ := mul_left_cancel heq
      have hσ : σ₁ = σ₂ := Equiv.Perm.ext fun k => by
        have := congrArg Prod.fst (Equiv.Perm.congr_fun h1 (k, 0))
        simpa [pairAction] using this
      subst hσ
      have hfl : fl₁ = fl₂ := by
        ext k
        have := congrArg Prod.snd (Equiv.Perm.congr_fun h1 (k, 0))
        simp only [pairAction, Equiv.coe_fn_mk] at this
        cases h1k : fl₁ k <;> cases h2k : fl₂ k <;> simp_all
      subst hfl; rfl
    · intro π hπ
      have hproj : π * baseInv M * π⁻¹ = ι := (Finset.mem_filter.1 hπ).2
      let g := π₀⁻¹ * π
      have hg_comm : g * baseInv M = baseInv M * g := by
        calc g * baseInv M = π₀⁻¹ * (π * baseInv M * π⁻¹) * π := by simp [g]; group
          _ = π₀⁻¹ * (π₀ * baseInv M * π₀⁻¹) * π := by rw [hproj, ← hπ₀]
          _ = baseInv M * g := by simp [g]; group
      obtain ⟨σ, fl, hg_eq⟩ := exists_pairAction_of_comm_baseInv hg_comm
      exact ⟨(σ, fl), Finset.mem_univ _, by rw [← hg_eq]; simp [g]⟩
  rw [hfib, Algebra.smul_def, ← mul_assoc]
  have hcancel : algebraMap ℚ K ((2 ^ M * M.factorial : ℕ) : ℚ)⁻¹ * ((2 ^ M * M.factorial : ℕ) : K) = 1 := by
    have hnat : ((2 ^ M * M.factorial : ℕ) : K) = algebraMap ℚ K ((2 ^ M * M.factorial : ℕ) : ℚ) :=
      (map_natCast (algebraMap ℚ K) _).symm
    rw [hnat, ← map_mul, inv_mul_cancel₀ (by positivity), map_one]
  rw [hcancel, one_mul]

lemma perm_apply_inv {α : Type*} (ρ : Equiv.Perm α) (x : α) : ρ (ρ⁻¹ x) = x :=
  ρ.apply_symm_apply x

lemma perm_inv_apply {α : Type*} (ρ : Equiv.Perm α) (x : α) : ρ⁻¹ (ρ x) = x :=
  ρ.symm_apply_apply x

lemma perm_mem_periodicPts {α : Type*} [Fintype α] (ρ : Equiv.Perm α) (x : α) :
    x ∈ Function.periodicPts ρ := by
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => ρ^[n] x)
  have hlt : ∃ i j : ℕ, i < j ∧ ρ^[i] x = ρ^[j] x := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, heq⟩
    · exact ⟨b, a, h, heq.symm⟩
  obtain ⟨i, j, hij, h⟩ := hlt
  refine ⟨j - i, by omega, ?_⟩
  change ρ^[j - i] x = x
  have h1 : ρ^[i] (ρ^[j - i] x) = ρ^[i] x := by
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hij.le, h]
  exact ρ.injective.iterate i h1

/-- Orbit of `x` under a permutation `ρ` on a finite type. -/
noncomputable def permOrbit {α : Type*} [Fintype α] [DecidableEq α] (ρ : Equiv.Perm α) (x : α) :
    Finset α :=
  (Finset.range (Function.minimalPeriod ρ x)).image fun t => ρ^[t] x

lemma mem_permOrbit_self {α : Type*} [Fintype α] [DecidableEq α] (ρ : Equiv.Perm α) (x : α) :
    x ∈ permOrbit ρ x := by
  have hpos : 0 < Function.minimalPeriod ρ x :=
    Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts ρ x)
  exact Finset.mem_image.2 ⟨0, Finset.mem_range.2 hpos, rfl⟩

lemma mem_permOrbit_iff {α : Type*} [Fintype α] [DecidableEq α] (ρ : Equiv.Perm α) (x y : α) :
    y ∈ permOrbit ρ x ↔ ∃ t : ℕ, ρ^[t] x = y := by
  constructor
  · intro hy
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    have hpos : 0 < Function.minimalPeriod ρ x :=
      Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts ρ x)
    refine Finset.mem_image.2 ⟨t % Function.minimalPeriod ρ x,
      Finset.mem_range.2 (Nat.mod_lt t hpos), ?_⟩
    exact Function.iterate_mod_minimalPeriod_eq

lemma permOrbit_apply {α : Type*} [Fintype α] [DecidableEq α] (ρ : Equiv.Perm α) (x : α) :
    permOrbit ρ (ρ x) = permOrbit ρ x := by
  ext y
  rw [mem_permOrbit_iff, mem_permOrbit_iff]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t + 1, by rw [Function.iterate_succ_apply]⟩
  · rintro ⟨t, rfl⟩
    cases t with
    | zero =>
      have hpos : 0 < Function.minimalPeriod ρ x :=
        Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts ρ x)
      refine ⟨Function.minimalPeriod ρ x - 1, ?_⟩
      rw [← Function.iterate_succ_apply ρ, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos,
        Function.iterate_minimalPeriod]
      rfl
    | succ t => exact ⟨t, by rw [Function.iterate_succ_apply]⟩

lemma permOrbit_eq_of_mem {α : Type*} [Fintype α] [DecidableEq α] {ρ : Equiv.Perm α} {x y : α}
    (hy : y ∈ permOrbit ρ x) : permOrbit ρ y = permOrbit ρ x := by
  obtain ⟨t, rfl⟩ := (mem_permOrbit_iff ρ x y).1 hy
  clear hy
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', permOrbit_apply, ih]

lemma minimalPeriod_perm_apply {α : Type*} [Fintype α] [DecidableEq α] (ρ : Equiv.Perm α) (x : α) :
    Function.minimalPeriod ρ (ρ x) = Function.minimalPeriod ρ x := by
  have h1 : (permOrbit ρ x).card = Function.minimalPeriod ρ x := by
    rw [permOrbit, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab
  have h2 : (permOrbit ρ (ρ x)).card = Function.minimalPeriod ρ (ρ x) := by
    rw [permOrbit, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab
  rw [← h2, permOrbit_apply, h1]

lemma minimalPeriod_eq_of_mem_permOrbit {α : Type*} [Fintype α] [DecidableEq α]
    {ρ : Equiv.Perm α} {x y : α} (hy : y ∈ permOrbit ρ x) :
    Function.minimalPeriod ρ y = Function.minimalPeriod ρ x := by
  obtain ⟨t, rfl⟩ := (mem_permOrbit_iff ρ x y).1 hy
  clear hy
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', minimalPeriod_perm_apply, ih]

lemma minimalPeriod_inv_eq {α : Type*} [Fintype α] [DecidableEq α] (ρ : Equiv.Perm α) (x : α) :
    Function.minimalPeriod (ρ⁻¹ : Equiv.Perm α) x = Function.minimalPeriod ρ x := by
  have hper : ∀ t : ℕ, (ρ⁻¹ : Equiv.Perm α)^[t] x = x ↔ ρ^[t] x = x := fun t => by
    have h1 : (ρ⁻¹ : Equiv.Perm α)^[t] x = (ρ⁻¹ ^ t) x := by
      rw [← Equiv.Perm.coe_pow]
    have h2 : ρ^[t] x = (ρ ^ t) x := by
      rw [← Equiv.Perm.coe_pow]
    rw [h1, h2, inv_pow]
    exact ⟨fun h => by simpa [perm_apply_inv] using congrArg (fun y => (ρ ^ t) y) h.symm,
      fun h => by simpa [perm_inv_apply] using congrArg (fun y => (ρ ^ t)⁻¹ y) h.symm⟩
  refine Nat.dvd_antisymm ?_ ?_
  · exact Function.IsPeriodicPt.minimalPeriod_dvd ((hper _).2 Function.iterate_minimalPeriod)
  · exact Function.IsPeriodicPt.minimalPeriod_dvd ((hper _).1 Function.iterate_minimalPeriod)

/-- Permutations on `α` whose every cycle has even length. -/
noncomputable def evenCyclePerms (α : Type*) [Fintype α] [DecidableEq α] : Finset (Equiv.Perm α) := by
  classical
  exact Finset.univ.filter fun ρ => ∀ x : α, Even (Function.minimalPeriod ρ x)

/-- Odd-cycle cancellation: for an alternating matrix `A` (`A x x = 0`, `A y x = -A x y`),
`A.det` equals the Leibniz sum restricted to `evenCyclePerms`. -/
lemma det_eq_sum_evenCyclePerms {M : ℕ} {K : Type*} [CommRing K] [Algebra ℚ K]
    {A : Matrix (Fin M × Fin 2) (Fin M × Fin 2) K}
    (hdiag : ∀ x, A x x = 0) (hskew : ∀ x y, A y x = -A x y) :
    A.det = ∑ ρ ∈ evenCyclePerms (Fin M × Fin 2),
      ((Equiv.Perm.sign ρ : ℤ) : K) * ∏ x : Fin M × Fin 2, A x (ρ x) := by
  classical
  let α := Fin M × Fin 2
  rw [← Matrix.det_transpose, Matrix.det_apply]
  change (∑ σ : Equiv.Perm α, Equiv.Perm.sign σ • ∏ i : α, A i (σ i)) = _
  simp_rw [Units.smul_def, zsmul_eq_mul]
  -- Step 1: drop permutations with a fixed point (their product contains A x x = 0)
  let fpfPerms : Finset (Equiv.Perm α) := Finset.univ.filter fun ρ => ∀ x, ρ x ≠ x
  have hdrop_fp :
      (∑ ρ : Equiv.Perm α, ((Equiv.Perm.sign ρ : ℤ) : K) * ∏ x : α, A x (ρ x)) =
      ∑ ρ ∈ fpfPerms, ((Equiv.Perm.sign ρ : ℤ) : K) * ∏ x : α, A x (ρ x) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun ρ _ hnot => ?_).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    push Not at hnot
    obtain ⟨x₀, hx₀⟩ := hnot
    have hp0 : ∏ x : α, A x (ρ x) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ x₀) (by rw [hx₀, hdiag])
    rw [hp0, mul_zero]
  rw [hdrop_fp]
  -- Split fpfPerms into evenCyclePerms and oddFpfPerms
  have heven_sub : evenCyclePerms α ⊆ fpfPerms := by
    intro ρ hρ
    simp only [fpfPerms, Finset.mem_filter, Finset.mem_univ, true_and]
    have hev := (Finset.mem_filter.1 hρ).2
    intro x hx
    have hp1 : Function.minimalPeriod ρ x = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.2 hx
    have : Even 1 := hp1 ▸ hev x
    exact Nat.not_even_one this
  let oddFpfPerms : Finset (Equiv.Perm α) := fpfPerms \ evenCyclePerms α
  have hsplit : fpfPerms = evenCyclePerms α ∪ oddFpfPerms :=
    (Finset.union_sdiff_of_subset heven_sub).symm
  rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
  -- Show the sum over oddFpfPerms is 0 via odd-cycle reversal involution
  suffices hzero : ∑ ρ ∈ oddFpfPerms,
      ((Equiv.Perm.sign ρ : ℤ) : K) * ∏ x : α, A x (ρ x) = 0 by
    rw [hzero, add_zero]
  -- Define index order on α via finProdFinEquiv
  let idx : α → ℕ := fun x => (finProdFinEquiv x).val
  have hidx_inj : Function.Injective idx := fun a b h =>
    finProdFinEquiv.injective (Fin.ext h)
  -- For any ρ ∈ oddFpfPerms, let x₀(ρ) minimize idx among elements with odd minimalPeriod
  let oddElts (ρ : Equiv.Perm α) : Finset α :=
    Finset.univ.filter fun x => Odd (Function.minimalPeriod ρ x)
  have hodd_ne : ∀ ρ ∈ oddFpfPerms, (oddElts ρ).Nonempty := by
    intro ρ hρ
    have hnot : ¬ ∀ x, Even (Function.minimalPeriod ρ x) := by
      intro h; exact (Finset.mem_sdiff.1 hρ).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    push Not at hnot
    obtain ⟨x, hx⟩ := hnot
    exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, Nat.not_even_iff_odd.1 hx⟩⟩
  let minOdd (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms) : α :=
    let m := ((oddElts ρ).image idx).min' ((hodd_ne ρ hρ).image idx)
    finProdFinEquiv.symm ⟨m, by
      have hm := Finset.min'_mem ((oddElts ρ).image idx) ((hodd_ne ρ hρ).image idx)
      obtain ⟨y, _, hy⟩ := Finset.mem_image.1 hm
      dsimp only [m]; rw [← hy]; exact (finProdFinEquiv y).isLt⟩
  have hminOdd_mem : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms),
      minOdd ρ hρ ∈ oddElts ρ := by
    intro ρ hρ
    have hm := Finset.min'_mem ((oddElts ρ).image idx) ((hodd_ne ρ hρ).image idx)
    obtain ⟨y, hy, hy_eq⟩ := Finset.mem_image.1 hm
    have heq : minOdd ρ hρ = y := by
      apply hidx_inj
      dsimp only [minOdd, idx]
      rw [Equiv.apply_symm_apply]
      exact hy_eq.symm
    rwa [heq]
  have hminOdd_le : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms) (y : α),
      y ∈ oddElts ρ → idx (minOdd ρ hρ) ≤ idx y := by
    intro ρ hρ y hy
    have : idx (minOdd ρ hρ) = ((oddElts ρ).image idx).min' ((hodd_ne ρ hρ).image idx) := by
      dsimp only [minOdd, idx]; rw [Equiv.apply_symm_apply]
    rw [this]
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem idx hy)
  -- Cycle restriction c_O(ρ) supported on O = permOrbit ρ (minOdd ρ)
  let cycOf (ρ : Equiv.Perm α) (O : Finset α)
      (hO : ∀ y, ρ y ∈ O ↔ y ∈ O) : Equiv.Perm α :=
    { toFun := fun y => if y ∈ O then ρ y else y
      invFun := fun y => if y ∈ O then ρ⁻¹ y else y
      left_inv := fun y => by
        dsimp only
        by_cases hy : y ∈ O
        · have hρy : ρ y ∈ O := (hO y).2 hy
          rw [if_pos hy, if_pos hρy, perm_inv_apply]
        · rw [if_neg hy, if_neg hy]
      right_inv := fun y => by
        dsimp only
        by_cases hy : y ∈ O
        · have hinv : ρ⁻¹ y ∈ O := (hO (ρ⁻¹ y)).1 (by simpa using hy)
          rw [if_pos hy, if_pos hinv, perm_apply_inv]
        · rw [if_neg hy, if_neg hy] }
  have horb_inv : ∀ (ρ : Equiv.Perm α) (x y : α), ρ y ∈ permOrbit ρ x ↔ y ∈ permOrbit ρ x := by
    intro ρ x y
    rw [mem_permOrbit_iff, mem_permOrbit_iff]
    constructor
    · rintro ⟨t, ht⟩
      have hpos : 0 < Function.minimalPeriod ρ x :=
        Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts ρ x)
      cases t with
      | zero =>
        refine ⟨Function.minimalPeriod ρ x - 1, ?_⟩
        apply ρ.injective
        rw [← Function.iterate_succ_apply' ρ, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos,
          Function.iterate_minimalPeriod]
        exact ht
      | succ t =>
        exact ⟨t, ρ.injective (by rw [← Function.iterate_succ_apply' ρ]; exact ht)⟩
    · rintro ⟨t, rfl⟩; exact ⟨t + 1, by rw [Function.iterate_succ_apply']⟩
  -- Define reversal map rev(ρ) = c⁻¹ * c⁻¹ * ρ on O = permOrbit ρ (minOdd ρ)
  let rev (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms) : Equiv.Perm α :=
    let O := permOrbit ρ (minOdd ρ hρ)
    let c := cycOf ρ O (horb_inv ρ (minOdd ρ hρ))
    c⁻¹ * c⁻¹ * ρ
  have hrev_apply : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms) (y : α),
      rev ρ hρ y = if y ∈ permOrbit ρ (minOdd ρ hρ) then ρ⁻¹ y else ρ y := by
    intro ρ hρ y
    simp only [rev, Equiv.Perm.coe_mul, Function.comp_apply]
    set O := permOrbit ρ (minOdd ρ hρ)
    have hO := horb_inv ρ (minOdd ρ hρ)
    by_cases hy : y ∈ O
    · have hρy : ρ y ∈ O := (hO y).2 hy
      dsimp only [O] at hy hρy
      simp only [cycOf, Equiv.Perm.inv_def, Equiv.symm_mk, Equiv.coe_fn_mk]
      rw [if_pos hρy, Equiv.symm_apply_apply, if_pos hy, if_pos hy]
    · have hρy : ρ y ∉ O := fun h => hy ((hO y).1 h)
      dsimp only [O] at hy hρy
      simp only [cycOf, Equiv.Perm.inv_def, Equiv.symm_mk, Equiv.coe_fn_mk]
      rw [if_neg hρy, if_neg hρy, if_neg hy]
  have hrev_period : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms) (y : α),
      Function.minimalPeriod (rev ρ hρ) y = Function.minimalPeriod ρ y := by
    intro ρ hρ y
    set O := permOrbit ρ (minOdd ρ hρ)
    have hO := horb_inv ρ (minOdd ρ hρ)
    by_cases hy : y ∈ O
    · have hiter : ∀ t : ℕ, (rev ρ hρ)^[t] y = (ρ⁻¹ : Equiv.Perm α)^[t] y := by
        intro t
        induction t with
        | zero => rfl
        | succ t ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          have hmem : (ρ⁻¹ : Equiv.Perm α)^[t] y ∈ O := by
            clear ih
            induction t with
            | zero => exact hy
            | succ t iht =>
              rw [Function.iterate_succ_apply']
              exact (hO _).1 (by simpa using iht)
          rw [hrev_apply ρ hρ, if_pos hmem]
      have h1 : Function.minimalPeriod (rev ρ hρ) y = Function.minimalPeriod (ρ⁻¹ : Equiv.Perm α) y := by
        refine Nat.dvd_antisymm ?_ ?_
        · exact Function.IsPeriodicPt.minimalPeriod_dvd
            (show (rev ρ hρ)^[Function.minimalPeriod (ρ⁻¹ : Equiv.Perm α) y] y = y by
              rw [hiter]; exact Function.iterate_minimalPeriod)
        · exact Function.IsPeriodicPt.minimalPeriod_dvd
            (show (ρ⁻¹ : Equiv.Perm α)^[Function.minimalPeriod (rev ρ hρ) y] y = y by
              rw [← hiter]; exact Function.iterate_minimalPeriod)
      rw [h1, minimalPeriod_inv_eq]
    · have hiter : ∀ t : ℕ, (rev ρ hρ)^[t] y = ρ^[t] y := by
        intro t
        induction t with
        | zero => rfl
        | succ t ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          have hnotmem : ρ^[t] y ∉ O := by
            clear ih
            induction t with
            | zero => exact hy
            | succ t iht =>
              rw [Function.iterate_succ_apply']
              exact fun h => iht ((hO _).1 h)
          rw [hrev_apply ρ hρ, if_neg hnotmem]
      refine Nat.dvd_antisymm ?_ ?_
      · exact Function.IsPeriodicPt.minimalPeriod_dvd
          (show (rev ρ hρ)^[Function.minimalPeriod ρ y] y = y by
            rw [hiter]; exact Function.iterate_minimalPeriod)
      · exact Function.IsPeriodicPt.minimalPeriod_dvd
          (show ρ^[Function.minimalPeriod (rev ρ hρ) y] y = y by
            rw [← hiter]; exact Function.iterate_minimalPeriod)
  have hrev_mem : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms), rev ρ hρ ∈ oddFpfPerms := by
    intro ρ hρ
    have hfpf := (Finset.mem_filter.1 (Finset.mem_sdiff.1 hρ).1).2
    refine Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, fun y => ?_⟩, ?_⟩
    · rw [hrev_apply ρ hρ]
      split_ifs
      · intro h; exact hfpf y (by simpa using congrArg ρ h.symm)
      · exact hfpf y
    · intro hev
      have hev' := (Finset.mem_filter.1 hev).2
      apply (Finset.mem_sdiff.1 hρ).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun y => ?_⟩
      rw [← hrev_period ρ hρ y]; exact hev' y
  have hrev_minOdd : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms),
      minOdd (rev ρ hρ) (hrev_mem ρ hρ) = minOdd ρ hρ := by
    intro ρ hρ
    have hodd_eq : oddElts (rev ρ hρ) = oddElts ρ := by
      ext y; simp [oddElts, hrev_period ρ hρ y]
    apply hidx_inj
    have h1 : idx (minOdd (rev ρ hρ) (hrev_mem ρ hρ)) =
        ((oddElts (rev ρ hρ)).image idx).min' ((hodd_ne _ (hrev_mem ρ hρ)).image idx) := by
      dsimp only [minOdd, idx]; rw [Equiv.apply_symm_apply]
    have h2 : idx (minOdd ρ hρ) =
        ((oddElts ρ).image idx).min' ((hodd_ne ρ hρ).image idx) := by
      dsimp only [minOdd, idx]; rw [Equiv.apply_symm_apply]
    rw [h1, h2]
    congr 1; simp [hodd_eq]
  have hrev_orbit : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms),
      permOrbit (rev ρ hρ) (minOdd (rev ρ hρ) (hrev_mem ρ hρ)) = permOrbit ρ (minOdd ρ hρ) := by
    intro ρ hρ
    rw [hrev_minOdd ρ hρ]
    set x₀ := minOdd ρ hρ
    set O := permOrbit ρ x₀
    have hO := horb_inv ρ x₀
    ext y
    rw [mem_permOrbit_iff]
    constructor
    · rintro ⟨t, rfl⟩
      induction t with
      | zero => exact mem_permOrbit_self ρ x₀
      | succ t ih =>
        rw [Function.iterate_succ_apply', hrev_apply ρ hρ, if_pos ih]
        exact (hO _).1 (by simpa using ih)
    · intro hy
      obtain ⟨t, rfl⟩ := (mem_permOrbit_iff ρ x₀ y).1 hy
      -- ρ^[t] x₀ = (rev ρ)^[m * period - t] x₀
      let p := Function.minimalPeriod ρ x₀
      have hp_pos : 0 < p :=
        Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts ρ x₀)
      have hrev_iter : ∀ k : ℕ, (rev ρ hρ)^[k] x₀ = (ρ⁻¹ : Equiv.Perm α)^[k] x₀ := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
          have hmem : (ρ⁻¹ : Equiv.Perm α)^[k] x₀ ∈ O := by
            clear ih
            induction k with
            | zero => exact mem_permOrbit_self ρ x₀
            | succ k ihk =>
              rw [Function.iterate_succ_apply']
              exact (hO _).1 (by simpa using ihk)
          rw [hrev_apply ρ hρ, if_pos hmem]
      refine ⟨(t + 1) * p - t, ?_⟩
      rw [hrev_iter, ← Equiv.Perm.coe_pow, ← Equiv.Perm.coe_pow, inv_pow]
      have hmul_p : (ρ ^ ((t + 1) * p)) x₀ = x₀ := by
        rw [Equiv.Perm.coe_pow, mul_comm, Function.iterate_mul]
        have hfix : ∀ n : ℕ, (ρ^[p])^[n] x₀ = x₀ := by
          intro n; induction n with
          | zero => rfl
          | succ n ihn => rw [Function.iterate_succ_apply', ihn]; exact Function.iterate_minimalPeriod
        exact hfix (t + 1)
      have hle : t ≤ (t + 1) * p := by nlinarith
      apply (ρ ^ ((t + 1) * p - t)).injective
      rw [perm_apply_inv]
      symm
      change ((ρ ^ ((t + 1) * p - t)) * (ρ ^ t)) x₀ = x₀
      rw [← pow_add, Nat.sub_add_cancel hle, hmul_p]
  have hrev_invol : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms),
      rev (rev ρ hρ) (hrev_mem ρ hρ) = ρ := by
    intro ρ hρ
    refine Equiv.Perm.ext fun y => ?_
    rw [hrev_apply (rev ρ hρ) (hrev_mem ρ hρ) y, hrev_orbit ρ hρ]
    by_cases hy : y ∈ permOrbit ρ (minOdd ρ hρ)
    · rw [if_pos hy]
      apply (rev ρ hρ).injective
      rw [perm_apply_inv, hrev_apply ρ hρ, if_pos ((horb_inv ρ _ y).2 hy),
        perm_inv_apply]
    · rw [if_neg hy, hrev_apply ρ hρ, if_neg hy]
  have hrev_term : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ oddFpfPerms),
      ((Equiv.Perm.sign (rev ρ hρ) : ℤ) : K) * ∏ x : α, A x (rev ρ hρ x) =
      -(((Equiv.Perm.sign ρ : ℤ) : K) * ∏ x : α, A x (ρ x)) := by
    intro ρ hρ
    have hsign : Equiv.Perm.sign (rev ρ hρ) = Equiv.Perm.sign ρ := by
      simp only [rev, map_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (cycOf ρ (permOrbit ρ (minOdd ρ hρ))
          (horb_inv ρ (minOdd ρ hρ)))⁻¹) with h | h <;> simp [h]
    rw [hsign, ← mul_neg]
    congr 1
    set O := permOrbit ρ (minOdd ρ hρ)
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x => x ∈ O),
      ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x => x ∈ O), ← neg_mul]
    congr 1
    · have hfilt : Finset.univ.filter (fun x => x ∈ O) = O := by ext x; simp
      rw [hfilt]
      have h1 : (∏ x ∈ O, A x (rev ρ hρ x)) = ∏ x ∈ O, A x (ρ⁻¹ x) :=
        Finset.prod_congr rfl fun x hx => by rw [hrev_apply ρ hρ, if_pos hx]
      rw [h1]
      -- Reindex x ↦ ρ x on O
      have hbij : (∏ x ∈ O, A x (ρ⁻¹ x)) = ∏ x ∈ O, A (ρ x) x := by
        refine (Finset.prod_bij (fun x _ => ρ x)
          (fun x hx => (horb_inv ρ _ x).2 hx)
          (fun x₁ _ x₂ _ h => ρ.injective h)
          (fun y hy => ⟨ρ⁻¹ y, (horb_inv ρ _ _).1 (by simpa using hy), by simp⟩)
          (fun x _ => by simp)).symm
      rw [hbij]
      have hskew_prod : (∏ x ∈ O, A (ρ x) x) = (-1 : K) ^ O.card * ∏ x ∈ O, A x (ρ x) := by
        calc (∏ x ∈ O, A (ρ x) x)
            = ∏ x ∈ O, ((-1 : K) * A x (ρ x)) :=
              Finset.prod_congr rfl fun x _ => by rw [hskew x (ρ x), neg_one_mul]
          _ = (-1 : K) ^ O.card * ∏ x ∈ O, A x (ρ x) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const]
      rw [hskew_prod]
      have hO_card : O.card = Function.minimalPeriod ρ (minOdd ρ hρ) := by
        dsimp only [O]
        rw [permOrbit, Finset.card_image_of_injOn, Finset.card_range]
        intro a ha b hb hab
        exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) hab
      have hodd : Odd O.card := hO_card ▸ (Finset.mem_filter.1 (hminOdd_mem ρ hρ)).2
      rw [hodd.neg_one_pow, neg_one_mul]
    · refine Finset.prod_congr rfl fun x hx => ?_
      rw [hrev_apply ρ hρ, if_neg (Finset.mem_filter.1 hx).2]
  -- Sum over oddFpfPerms satisfies S = -S, hence 2 * S = 0, hence S = 0 (since K is a ℚ-algebra!)
  let Ssum : K := ∑ ρ ∈ oddFpfPerms, ((Equiv.Perm.sign ρ : ℤ) : K) * ∏ x : α, A x (ρ x)
  have hS_neg : Ssum = -Ssum := by
    have h1 : Ssum = ∑ ρ ∈ oddFpfPerms.attach,
        ((Equiv.Perm.sign ρ.1 : ℤ) : K) * ∏ x : α, A x (ρ.1 x) :=
      (Finset.sum_attach oddFpfPerms _).symm
    have h2 : (∑ ρ ∈ oddFpfPerms.attach,
        ((Equiv.Perm.sign ρ.1 : ℤ) : K) * ∏ x : α, A x (ρ.1 x)) =
        ∑ ρ ∈ oddFpfPerms.attach,
        ((Equiv.Perm.sign (rev ρ.1 ρ.2) : ℤ) : K) * ∏ x : α, A x (rev ρ.1 ρ.2 x) := by
      refine (Finset.sum_bij (fun ρ _ => ⟨rev ρ.1 ρ.2, hrev_mem ρ.1 ρ.2⟩)
        (fun _ _ => Finset.mem_attach _ _) ?_ ?_ (fun _ _ => rfl)).symm
      · intro ρ₁ _ ρ₂ _ heq
        have h : rev ρ₁.1 ρ₁.2 = rev ρ₂.1 ρ₂.2 := congrArg Subtype.val heq
        have hcongr : ∀ (a b : Equiv.Perm α) (ha : a ∈ oddFpfPerms) (hb : b ∈ oddFpfPerms),
            a = b → rev a ha = rev b hb := by
          intro a b ha hb hab; subst hab; rfl
        have h' : rev (rev ρ₁.1 ρ₁.2) (hrev_mem ρ₁.1 ρ₁.2) =
            rev (rev ρ₂.1 ρ₂.2) (hrev_mem ρ₂.1 ρ₂.2) :=
          hcongr _ _ (hrev_mem ρ₁.1 ρ₁.2) (hrev_mem ρ₂.1 ρ₂.2) h
        rw [hrev_invol ρ₁.1 ρ₁.2, hrev_invol ρ₂.1 ρ₂.2] at h'
        exact Subtype.ext h'
      · intro ρ _
        exact ⟨⟨rev ρ.1 ρ.2, hrev_mem ρ.1 ρ.2⟩, Finset.mem_attach _ _,
          Subtype.ext (hrev_invol ρ.1 ρ.2)⟩
    calc Ssum
        = ∑ ρ ∈ oddFpfPerms.attach,
            ((Equiv.Perm.sign ρ.1 : ℤ) : K) * ∏ x : α, A x (ρ.1 x) := h1
      _ = ∑ ρ ∈ oddFpfPerms.attach,
            ((Equiv.Perm.sign (rev ρ.1 ρ.2) : ℤ) : K) * ∏ x : α, A x (rev ρ.1 ρ.2 x) := h2
      _ = ∑ ρ ∈ oddFpfPerms.attach,
            -(((Equiv.Perm.sign ρ.1 : ℤ) : K) * ∏ x : α, A x (ρ.1 x)) :=
          Finset.sum_congr rfl fun ρ _ => hrev_term ρ.1 ρ.2
      _ = -Ssum := by rw [Finset.sum_neg_distrib, ← h1]
  have h2S : (2 : ℚ) • Ssum = 0 := by
    rw [two_smul]
    calc Ssum + Ssum = Ssum + (-Ssum) := by conv_rhs => rw [← hS_neg]
      _ = 0 := add_neg_cancel Ssum
  have := congrArg ((2 : ℚ)⁻¹ • ·) h2S
  simpa [smul_smul] using this

/-- Alternating walk `x, ι₁ x, ι₂ (ι₁ x), ι₁ (ι₂ (ι₁ x)), ...`. -/
def altWalk {α : Type*} (ι₁ ι₂ : Equiv.Perm α) (x : α) : ℕ → α
  | 0 => x
  | t + 1 => if Even t then ι₁ (altWalk ι₁ ι₂ x t) else ι₂ (altWalk ι₁ ι₂ x t)

lemma altWalk_even {α : Type*} (ι₁ ι₂ : Equiv.Perm α) (x : α) (k : ℕ) :
    altWalk ι₁ ι₂ x (2 * k) = ((ι₂ * ι₁) ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h1, altWalk, if_neg (by simp), altWalk, if_pos (even_two_mul k), ih,
      pow_succ']
    rfl

lemma altWalk_odd {α : Type*} (ι₁ ι₂ : Equiv.Perm α) (x : α) (k : ℕ) :
    altWalk ι₁ ι₂ x (2 * k + 1) = ι₁ (((ι₂ * ι₁) ^ k) x) := by
  rw [altWalk, if_pos (even_two_mul k), altWalk_even]

/-- Disjointness of even and odd steps of an alternating walk of two fixed-point-free involutions. -/
lemma altWalk_even_ne_odd {α : Type*} [Fintype α] [DecidableEq α]
    {ι₁ ι₂ : Equiv.Perm α}
    (h₁ : ι₁ ∈ fpfInvolutions α) (h₂ : ι₂ ∈ fpfInvolutions α) (x : α) (j k : ℕ) :
    ((ι₂ * ι₁) ^ j) x ≠ ι₁ (((ι₂ * ι₁) ^ k) x) := by
  rcases (Finset.mem_filter.1 h₁).2 with ⟨hsq₁, hfpf₁⟩
  rcases (Finset.mem_filter.1 h₂).2 with ⟨hsq₂, hfpf₂⟩
  have hinv₁ : ι₁⁻¹ = ι₁ := inv_eq_of_mul_eq_one_right hsq₁
  have hinv₂ : ι₂⁻¹ = ι₂ := inv_eq_of_mul_eq_one_right hsq₂
  let σ := ι₂ * ι₁
  have hconj : ∀ m : ℕ, ι₁ * σ ^ m = (σ⁻¹) ^ m * ι₁ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hstep : ι₁ * σ = σ⁻¹ * ι₁ := by
        simp only [σ, mul_inv_rev, hinv₁, hinv₂]
        calc ι₁ * (ι₂ * ι₁) = (ι₁ * ι₂) * ι₁ := by group
          _ = ι₁ * ι₂ * ι₁ := rfl
      calc ι₁ * σ ^ (m + 1) = (ι₁ * σ) * σ ^ m := by rw [pow_succ']; group
        _ = σ⁻¹ * (ι₁ * σ ^ m) := by rw [hstep]; group
        _ = σ⁻¹ * ((σ⁻¹) ^ m * ι₁) := by rw [ih]
        _ = (σ⁻¹) ^ (m + 1) * ι₁ := by rw [pow_succ']; group
  intro heq
  have hsum : (σ ^ (j + k)) x = ι₁ x := by
    have h1 : (σ ^ k * σ ^ j) x = (σ ^ k * (ι₁ * σ ^ k)) x := by
      simp only [Equiv.Perm.coe_mul, Function.comp_apply]; rw [heq]
    rw [← pow_add, add_comm k j] at h1
    have hcancel : σ ^ k * σ⁻¹ ^ k = 1 := by rw [inv_pow, mul_inv_cancel]
    rw [hconj k, ← mul_assoc, hcancel, one_mul] at h1
    exact h1
  rcases Nat.even_or_odd (j + k) with ⟨r, hr⟩ | ⟨r, hr⟩
  · rw [hr, pow_add] at hsum
    have hfix : (σ ^ r) x = ι₁ ((σ ^ r) x) := by
      have h1 : (σ⁻¹ ^ r * (σ ^ r * σ ^ r)) x = (σ⁻¹ ^ r * ι₁) x :=
        congrArg (σ⁻¹ ^ r) hsum
      have hcancel' : σ⁻¹ ^ r * σ ^ r = 1 := by rw [inv_pow, inv_mul_cancel]
      rw [← mul_assoc, hcancel', one_mul, ← hconj r] at h1
      exact h1
    exact hfpf₁ ((σ ^ r) x) hfix.symm
  · rw [hr, show 2 * r + 1 = r + (r + 1) by omega, pow_add, pow_succ'] at hsum
    have hfix : σ ((σ ^ r) x) = ι₁ ((σ ^ r) x) := by
      have h1 : (σ⁻¹ ^ r * (σ ^ r * (σ * σ ^ r))) x = (σ⁻¹ ^ r * ι₁) x :=
        congrArg (σ⁻¹ ^ r) hsum
      have hcancel' : σ⁻¹ ^ r * σ ^ r = 1 := by rw [inv_pow, inv_mul_cancel]
      rw [← mul_assoc, hcancel', one_mul, ← hconj r] at h1
      exact h1
    exact hfpf₂ (ι₁ ((σ ^ r) x)) hfix

/-- **Cayley's Identity**: For any alternating matrix `A` on `Fin M × Fin 2` over a `ℚ`-algebra `K`,
`pfaffian A ^ 2 = A.det`. -/
theorem pfaffian_sq_eq_det {M : ℕ} {K : Type*} [CommRing K] [Algebra ℚ K]
    {A : Matrix (Fin M × Fin 2) (Fin M × Fin 2) K}
    (hdiag : ∀ x, A x x = 0) (hskew : ∀ x y, A y x = -A x y) :
    pfaffian A ^ 2 = A.det := by
  classical
  let α := Fin M × Fin 2
  rw [sq, pfaffian_eq_sum_fpfInvolutions hskew, det_eq_sum_evenCyclePerms hdiag hskew,
    Finset.sum_mul_sum]
  -- Index order on α
  let idx : α → ℕ := fun x => (finProdFinEquiv x).val
  have hidx_inj : Function.Injective idx := fun a b h =>
    finProdFinEquiv.injective (Fin.ext h)
  -- Minimum element of any nonempty Finset α under idx
  let minByIdx (S : Finset α) (hS : S.Nonempty) : α :=
    let m := (S.image idx).min' (hS.image idx)
    finProdFinEquiv.symm ⟨m, by
      have hm := Finset.min'_mem (S.image idx) (hS.image idx)
      obtain ⟨y, _, hy⟩ := Finset.mem_image.1 hm
      dsimp only [m]; rw [← hy]; exact (finProdFinEquiv y).isLt⟩
  have hminByIdx_mem : ∀ (S : Finset α) (hS : S.Nonempty), minByIdx S hS ∈ S := by
    intro S hS
    have hm := Finset.min'_mem (S.image idx) (hS.image idx)
    obtain ⟨y, hy, hy_eq⟩ := Finset.mem_image.1 hm
    have heq : minByIdx S hS = y := by
      apply hidx_inj
      dsimp only [minByIdx, idx]
      rw [Equiv.apply_symm_apply]
      exact hy_eq.symm
    rwa [heq]
  have hminByIdx_le : ∀ (S : Finset α) (hS : S.Nonempty) (y : α), y ∈ S →
      idx (minByIdx S hS) ≤ idx y := by
    intro S hS y hy
    have h1 : idx (minByIdx S hS) = (S.image idx).min' (hS.image idx) := by
      dsimp only [minByIdx, idx]; rw [Equiv.apply_symm_apply]
    rw [h1]
    exact Finset.min'_le _ _ (Finset.mem_image_of_mem idx hy)
  have hminByIdx_eq : ∀ {S₁ S₂ : Finset α} (h₁ : S₁.Nonempty) (h₂ : S₂.Nonempty),
      S₁ = S₂ → minByIdx S₁ h₁ = minByIdx S₂ h₂ := by
    intro S₁ S₂ h₁ h₂ heq; subst heq; rfl
  -- For ρ ∈ evenCyclePerms, define minElt ρ x and distElt ρ x
  let minElt (ρ : Equiv.Perm α) (x : α) : α :=
    minByIdx (permOrbit ρ x) ⟨x, mem_permOrbit_self ρ x⟩
  have hminElt_apply : ∀ (ρ : Equiv.Perm α) (x : α), minElt ρ (ρ x) = minElt ρ x := fun ρ x =>
    hminByIdx_eq ⟨ρ x, mem_permOrbit_self ρ (ρ x)⟩ ⟨x, mem_permOrbit_self ρ x⟩ (permOrbit_apply ρ x)
  have hminElt_mem : ∀ (ρ : Equiv.Perm α) (x : α), x ∈ permOrbit ρ (minElt ρ x) := fun ρ x => by
    have h1 : minElt ρ x ∈ permOrbit ρ x := hminByIdx_mem (permOrbit ρ x) ⟨x, mem_permOrbit_self ρ x⟩
    rw [permOrbit_eq_of_mem h1]
    exact mem_permOrbit_self ρ x
  let distElt (ρ : Equiv.Perm α) (x : α) : ℕ :=
    Classical.choose (Finset.mem_image.1 (hminElt_mem ρ x))
  have hdist_lt : ∀ (ρ : Equiv.Perm α) (x : α),
      distElt ρ x < Function.minimalPeriod ρ (minElt ρ x) := fun ρ x =>
    Finset.mem_range.1 (Classical.choose_spec (Finset.mem_image.1 (hminElt_mem ρ x))).1
  have hdist_spec : ∀ (ρ : Equiv.Perm α) (x : α),
      ρ^[distElt ρ x] (minElt ρ x) = x := fun ρ x =>
    (Classical.choose_spec (Finset.mem_image.1 (hminElt_mem ρ x))).2
  have hdist_unique : ∀ (ρ : Equiv.Perm α) (x : α) (t : ℕ),
      t < Function.minimalPeriod ρ (minElt ρ x) → ρ^[t] (minElt ρ x) = x → t = distElt ρ x := by
    intro ρ x t ht htx
    exact Function.iterate_injOn_Iio_minimalPeriod ht (hdist_lt ρ x)
      (htx.trans (hdist_spec ρ x).symm)
  have hdist_parity_step : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ evenCyclePerms α) (x : α),
      Even (distElt ρ (ρ x)) ↔ ¬ Even (distElt ρ x) := by
    intro ρ hρ x
    have hev_p : Even (Function.minimalPeriod ρ (minElt ρ x)) := (Finset.mem_filter.1 hρ).2 _
    have hlt := hdist_lt ρ x
    by_cases hlast : distElt ρ x + 1 < Function.minimalPeriod ρ (minElt ρ x)
    · have heq : distElt ρ (ρ x) = distElt ρ x + 1 := by
        symm
        apply hdist_unique ρ (ρ x)
        · rw [hminElt_apply]; exact hlast
        · rw [hminElt_apply, Function.iterate_succ_apply', hdist_spec]
      rw [heq, Nat.even_add_one]
    · have htop : distElt ρ x + 1 = Function.minimalPeriod ρ (minElt ρ x) := by omega
      have heq : distElt ρ (ρ x) = 0 := by
        symm
        apply hdist_unique ρ (ρ x)
        · rw [hminElt_apply]
          exact Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts ρ _)
        · rw [hminElt_apply]
          have hiter : ρ^[distElt ρ x + 1] (minElt ρ x) = minElt ρ x := by
            rw [htop]; exact Function.iterate_minimalPeriod
          rw [Function.iterate_succ_apply', hdist_spec] at hiter
          exact hiter.symm
      rw [heq]
      have hodd_d : ¬ Even (distElt ρ x) := by
        intro hd
        have : Odd (Function.minimalPeriod ρ (minElt ρ x)) := by
          rw [← htop]; exact hd.add_one
        exact (Nat.not_even_iff_odd.2 this) hev_p
      simp [hodd_d]
  -- Forward map: ρ ∈ evenCyclePerms ↦ (ι₁ ρ, ι₂ ρ) ∈ fpfInvolutions × fpfInvolutions
  let mkInv1 (ρ : Equiv.Perm α) (hρ : ρ ∈ evenCyclePerms α) : Equiv.Perm α :=
    { toFun := fun x => if Even (distElt ρ x) then ρ x else ρ⁻¹ x
      invFun := fun x => if Even (distElt ρ x) then ρ x else ρ⁻¹ x
      left_inv := fun x => by
        dsimp only
        by_cases hx : Even (distElt ρ x)
        · rw [if_pos hx, if_neg (fun h => (hdist_parity_step ρ hρ x).1 h hx), perm_inv_apply]
        · rw [if_neg hx]
          have hinv_ev : Even (distElt ρ (ρ⁻¹ x)) := by
            by_contra hnot
            exact hx ((hdist_parity_step ρ hρ (ρ⁻¹ x)).2 hnot |> fun h => by simpa using h)
          rw [if_pos hinv_ev, perm_apply_inv]
      right_inv := fun x => by
        dsimp only
        by_cases hx : Even (distElt ρ x)
        · rw [if_pos hx, if_neg (fun h => (hdist_parity_step ρ hρ x).1 h hx), perm_inv_apply]
        · rw [if_neg hx]
          have hinv_ev : Even (distElt ρ (ρ⁻¹ x)) := by
            by_contra hnot
            exact hx ((hdist_parity_step ρ hρ (ρ⁻¹ x)).2 hnot |> fun h => by simpa using h)
          rw [if_pos hinv_ev, perm_apply_inv] }
  let mkInv2 (ρ : Equiv.Perm α) (hρ : ρ ∈ evenCyclePerms α) : Equiv.Perm α :=
    { toFun := fun x => if Even (distElt ρ x) then ρ⁻¹ x else ρ x
      invFun := fun x => if Even (distElt ρ x) then ρ⁻¹ x else ρ x
      left_inv := fun x => by
        dsimp only
        by_cases hx : Even (distElt ρ x)
        · rw [if_pos hx]
          have hinv_odd : ¬ Even (distElt ρ (ρ⁻¹ x)) :=
            (hdist_parity_step ρ hρ (ρ⁻¹ x)).1 (by simpa using hx)
          rw [if_neg hinv_odd, perm_apply_inv]
        · rw [if_neg hx, if_pos ((hdist_parity_step ρ hρ x).2 hx), perm_inv_apply]
      right_inv := fun x => by
        dsimp only
        by_cases hx : Even (distElt ρ x)
        · rw [if_pos hx]
          have hinv_odd : ¬ Even (distElt ρ (ρ⁻¹ x)) :=
            (hdist_parity_step ρ hρ (ρ⁻¹ x)).1 (by simpa using hx)
          rw [if_neg hinv_odd, perm_apply_inv]
        · rw [if_neg hx, if_pos ((hdist_parity_step ρ hρ x).2 hx), perm_inv_apply] }
  have hmkInv_mem : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ evenCyclePerms α),
      mkInv1 ρ hρ ∈ fpfInvolutions α ∧ mkInv2 ρ hρ ∈ fpfInvolutions α := by
    intro ρ hρ
    have hfpf : ∀ x, ρ x ≠ x := fun x hx => by
      have hp1 : Function.minimalPeriod ρ x = 1 :=
        Function.minimalPeriod_eq_one_iff_isFixedPt.2 hx
      exact Nat.not_even_one (hp1 ▸ (Finset.mem_filter.1 hρ).2 x)
    constructor
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, fun x => ?_⟩
      · exact Equiv.Perm.ext fun x => (mkInv1 ρ hρ).left_inv x
      · simp only [mkInv1, Equiv.coe_fn_mk]
        split_ifs
        · exact hfpf x
        · intro h; exact hfpf x (by simpa using congrArg ρ h.symm)
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, fun x => ?_⟩
      · exact Equiv.Perm.ext fun x => (mkInv2 ρ hρ).left_inv x
      · simp only [mkInv2, Equiv.coe_fn_mk]
        split_ifs
        · intro h; exact hfpf x (by simpa using congrArg ρ h.symm)
        · exact hfpf x
  -- Bijection between evenCyclePerms.attach and fpfInvolutions ×ˢ fpfInvolutions
  rw [← Finset.sum_product', ← Finset.sum_attach (evenCyclePerms α)]
  refine (Finset.sum_bij
    (fun (ρ : {ρ // ρ ∈ evenCyclePerms α}) _ => (mkInv1 ρ.1 ρ.2, mkInv2 ρ.1 ρ.2))
    ?_ ?_ ?_ ?_).symm
  · intro ρ _
    exact Finset.mem_product.2 (hmkInv_mem ρ.1 ρ.2)
  · -- Injectivity: ρ is uniquely recovered from (mkInv1 ρ, mkInv2 ρ)
    intro ρ₁ _ ρ₂ _ heq
    have h1 : mkInv1 ρ₁.1 ρ₁.2 = mkInv1 ρ₂.1 ρ₂.2 := congrArg Prod.fst heq
    have h2 : mkInv2 ρ₁.1 ρ₁.2 = mkInv2 ρ₂.1 ρ₂.2 := congrArg Prod.snd heq
    -- Show altWalk (mkInv1 ρ) (mkInv2 ρ) (minElt ρ x) t = ρ^[t] (minElt ρ x)
    have hwalk : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ evenCyclePerms α) (x : α) (t : ℕ),
        altWalk (mkInv1 ρ hρ) (mkInv2 ρ hρ) (minElt ρ x) t = ρ^[t] (minElt ρ x) := by
      intro ρ hρ x t
      have hpar : ∀ k : ℕ, Even (distElt ρ (ρ^[k] (minElt ρ x))) ↔ Even k := by
        intro k
        induction k with
        | zero =>
          have h0 : distElt ρ (minElt ρ x) = 0 := by
            symm
            apply hdist_unique ρ (minElt ρ x) 0
            · exact Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts ρ _)
            · exact hminByIdx_eq ⟨_, mem_permOrbit_self ρ _⟩ ⟨x, mem_permOrbit_self ρ x⟩
                (permOrbit_eq_of_mem (hminByIdx_mem (permOrbit ρ x) ⟨x, mem_permOrbit_self ρ x⟩))
          simp [h0]
        | succ k ih =>
          rw [Function.iterate_succ_apply', hdist_parity_step ρ hρ, ih, Nat.even_add_one]
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [altWalk, ih, Function.iterate_succ_apply']
        by_cases ht : Even t
        · rw [if_pos ht]
          simp only [mkInv1, Equiv.coe_fn_mk, if_pos ((hpar t).2 ht)]
        · rw [if_neg ht]
          simp only [mkInv2, Equiv.coe_fn_mk, if_neg (mt (hpar t).1 ht)]
    -- Show permOrbit ρ₁ x = permOrbit ρ₂ x for every x
    have horb_eq : ∀ x : α, permOrbit ρ₁.1 x = permOrbit ρ₂.1 x := by
      intro x
      -- Reachable set under (mkInv1, mkInv2) equals permOrbit
      have hreach : ∀ (ρ : Equiv.Perm α) (hρ : ρ ∈ evenCyclePerms α) (a b : α),
          b ∈ permOrbit ρ a → (mkInv1 ρ hρ b ∈ permOrbit ρ a ∧ mkInv2 ρ hρ b ∈ permOrbit ρ a) := by
        intro ρ hρ a b hb
        have hstep : ∀ y, ρ y ∈ permOrbit ρ a ↔ y ∈ permOrbit ρ a := by
          intro y
          rw [mem_permOrbit_iff, mem_permOrbit_iff]
          constructor
          · rintro ⟨t, ht⟩
            have hpos : 0 < Function.minimalPeriod ρ a :=
              Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts ρ a)
            cases t with
            | zero =>
              refine ⟨Function.minimalPeriod ρ a - 1, ?_⟩
              apply ρ.injective
              rw [← Function.iterate_succ_apply' ρ, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos,
                Function.iterate_minimalPeriod]
              exact ht
            | succ t => exact ⟨t, ρ.injective (by rw [← Function.iterate_succ_apply' ρ]; exact ht)⟩
          · rintro ⟨t, rfl⟩; exact ⟨t + 1, by rw [Function.iterate_succ_apply']⟩
        have hinv_mem : ρ⁻¹ b ∈ permOrbit ρ a := (hstep (ρ⁻¹ b)).1 (by simpa using hb)
        constructor
        · simp only [mkInv1, Equiv.coe_fn_mk]; split_ifs
          · exact (hstep b).2 hb
          · exact hinv_mem
        · simp only [mkInv2, Equiv.coe_fn_mk]; split_ifs
          · exact hinv_mem
          · exact (hstep b).2 hb
      have hsub : ∀ (ρa ρb : {ρ // ρ ∈ evenCyclePerms α}),
          mkInv1 ρa.1 ρa.2 = mkInv1 ρb.1 ρb.2 → mkInv2 ρa.1 ρa.2 = mkInv2 ρb.1 ρb.2 →
          ∀ y, permOrbit ρa.1 y ⊆ permOrbit ρb.1 y := by
        intro ρa ρb h1' h2' y z hz
        have hz' : z ∈ permOrbit ρa.1 (minElt ρa.1 y) := by
          rw [permOrbit_eq_of_mem (hminByIdx_mem (permOrbit ρa.1 y) ⟨y, mem_permOrbit_self ρa.1 y⟩)]; exact hz
        have hmin_in_b : minElt ρa.1 y ∈ permOrbit ρb.1 y → z ∈ permOrbit ρb.1 y := by
          intro hm
          obtain ⟨t, rfl⟩ := (mem_permOrbit_iff ρa.1 (minElt ρa.1 y) z).1 hz'
          rw [← hwalk ρa.1 ρa.2 y t, h1', h2']
          clear hz hz'
          induction t with
          | zero => exact hm
          | succ t ih =>
            rw [altWalk]
            split_ifs
            · exact (hreach ρb.1 ρb.2 y _ ih).1
            · exact (hreach ρb.1 ρb.2 y _ ih).2
        -- First show y ∈ permOrbit ρa (minElt ρa y) so walk from minElt reaches y;
        -- conversely reverse walk from y reaches minElt ρa y inside permOrbit ρb y!
        have hy_in_orb : ∀ (a : α) (t : ℕ),
            altWalk (mkInv1 ρb.1 ρb.2) (mkInv2 ρb.1 ρb.2) a t ∈ permOrbit ρb.1 a := by
          intro a t
          induction t with
          | zero => exact mem_permOrbit_self ρb.1 a
          | succ t ih =>
            rw [altWalk]
            split_ifs
            · exact (hreach ρb.1 ρb.2 a _ ih).1
            · exact (hreach ρb.1 ρb.2 a _ ih).2
        have hm_in_b : minElt ρa.1 y ∈ permOrbit ρb.1 y := by
          -- y = altWalk (mkInv1 ρa) (mkInv2 ρa) (minElt ρa y) (distElt ρa y)
          -- so y ∈ permOrbit ρb (minElt ρa y), hence minElt ρa y ∈ permOrbit ρb y!
          have hy_eq : y = altWalk (mkInv1 ρb.1 ρb.2) (mkInv2 ρb.1 ρb.2)
              (minElt ρa.1 y) (distElt ρa.1 y) := by
            rw [← h1', ← h2', hwalk ρa.1 ρa.2 y, hdist_spec]
          have hmem : y ∈ permOrbit ρb.1 (minElt ρa.1 y) := by
            have := hy_in_orb (minElt ρa.1 y) (distElt ρa.1 y)
            rwa [← hy_eq] at this
          rw [permOrbit_eq_of_mem hmem]
          exact mem_permOrbit_self ρb.1 (minElt ρa.1 y)
        exact hmin_in_b hm_in_b
      exact Finset.Subset.antisymm (hsub ρ₁ ρ₂ h1 h2 x) (hsub ρ₂ ρ₁ h1.symm h2.symm x)
    apply Subtype.ext; refine Equiv.Perm.ext fun x => ?_
    have hmin_eq : minElt ρ₁.1 x = minElt ρ₂.1 x :=
      hminByIdx_eq ⟨x, mem_permOrbit_self ρ₁.1 x⟩ ⟨x, mem_permOrbit_self ρ₂.1 x⟩ (horb_eq x)
    have hwalk_eq : ∀ t : ℕ, ρ₁.1^[t] (minElt ρ₁.1 x) = ρ₂.1^[t] (minElt ρ₂.1 x) := fun t => by
      rw [← hwalk ρ₁.1 ρ₁.2 x t, ← hwalk ρ₂.1 ρ₂.2 x t, h1, h2, hmin_eq]
    have hx1 := hdist_spec ρ₁.1 x
    have hnext := hwalk_eq (distElt ρ₁.1 x + 1)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hx1,
      ← hwalk_eq (distElt ρ₁.1 x), hx1] at hnext
    exact hnext
  · -- Surjectivity: construct ρ from (ι₁, ι₂) ∈ fpfInvolutions × fpfInvolutions
    rintro ⟨ι₁, ι₂⟩ hmem
    rcases Finset.mem_product.1 hmem with ⟨h₁, h₂⟩
    rcases (Finset.mem_filter.1 h₁).2 with ⟨hsq₁, hfpf₁⟩
    rcases (Finset.mem_filter.1 h₂).2 with ⟨hsq₂, hfpf₂⟩
    let σ := ι₂ * ι₁
    -- Orbit component comp(x) = {σ^k x | k < period σ x} ∪ {ι₁ (σ^k x) | k < period σ x}
    let comp (x : α) : Finset α :=
      (Finset.range (2 * Function.minimalPeriod σ x)).image (altWalk ι₁ ι₂ x)
    have hcomp_self : ∀ x, x ∈ comp x := fun x => by
      have hpos : 0 < Function.minimalPeriod σ x :=
        Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts σ x)
      exact Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), rfl⟩
    have hcomp_iff : ∀ x y, y ∈ comp x ↔ ∃ t : ℕ, altWalk ι₁ ι₂ x t = y := by
      intro x y
      constructor
      · intro hy; obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 hy; exact ⟨t, rfl⟩
      · rintro ⟨t, rfl⟩
        let L := Function.minimalPeriod σ x
        have hL : 0 < L :=
          Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts σ x)
        rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hk, ← two_mul, altWalk_even]
          refine Finset.mem_image.2 ⟨2 * (k % L), Finset.mem_range.2 (by
            have := Nat.mod_lt k hL; omega), ?_⟩
          rw [altWalk_even, Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
          exact Function.iterate_mod_minimalPeriod_eq
        · rw [hk, altWalk_odd]
          refine Finset.mem_image.2 ⟨2 * (k % L) + 1, Finset.mem_range.2 (by
            have := Nat.mod_lt k hL; omega), ?_⟩
          rw [altWalk_odd, Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
          congr 1; exact Function.iterate_mod_minimalPeriod_eq
    have hcomp_closed : ∀ x y, y ∈ comp x → ι₁ y ∈ comp x ∧ ι₂ y ∈ comp x := by
      intro x y hy
      obtain ⟨t, rfl⟩ := (hcomp_iff x y).1 hy
      have hinv₁ : ∀ z, ι₁ (ι₁ z) = z := fun z => by
        have := Equiv.Perm.congr_fun hsq₁ z; simpa using this
      have hinv₂ : ∀ z, ι₂ (ι₂ z) = z := fun z => by
        have := Equiv.Perm.congr_fun hsq₂ z; simpa using this
      rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [hk, ← two_mul]
        constructor
        · exact (hcomp_iff x _).2 ⟨2 * k + 1, by rw [altWalk_odd, altWalk_even]⟩
        · -- ι₂ (σ^k x) = ι₁ (σ^(k - 1) x) mod L
          let L := Function.minimalPeriod σ x
          have hL : 0 < L :=
            Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts σ x)
          have hσL : (σ ^ L) x = x := by rw [Equiv.Perm.coe_pow]; exact Function.iterate_minimalPeriod
          refine (hcomp_iff x _).2 ⟨2 * ((k + L - 1) % L) + 1, ?_⟩
          rw [altWalk_odd, altWalk_even, Equiv.Perm.coe_pow, Function.iterate_mod_minimalPeriod_eq,
            ← Equiv.Perm.coe_pow]
          apply ι₂.injective
          rw [hinv₂]
          change (σ * σ ^ (k + L - 1)) x = (σ ^ k) x
          rw [← pow_succ', show k + L - 1 + 1 = k + L by omega, pow_add,
            Equiv.Perm.coe_mul, Function.comp_apply, hσL]
      · rw [hk]
        constructor
        · refine (hcomp_iff x _).2 ⟨2 * k, ?_⟩
          rw [altWalk_odd, altWalk_even, hinv₁]
        · refine (hcomp_iff x _).2 ⟨2 * (k + 1), ?_⟩
          rw [altWalk_odd, altWalk_even, pow_succ']; rfl
    have hcomp_eq : ∀ x y, y ∈ comp x → comp y = comp x := by
      intro x y hy
      have hsub : ∀ a b, b ∈ comp a → comp b ⊆ comp a := by
        intro a b hb z hz
        obtain ⟨t, rfl⟩ := (hcomp_iff b z).1 hz
        clear hz
        induction t with
        | zero => exact hb
        | succ t ih =>
          rw [altWalk]; split_ifs
          · exact (hcomp_closed a _ ih).1
          · exact (hcomp_closed a _ ih).2
      have hsymm : x ∈ comp y := by
        obtain ⟨t, rfl⟩ := (hcomp_iff x y).1 hy
        clear hy
        have hinv₁ : ∀ z, ι₁ (ι₁ z) = z := fun z => by
          have := Equiv.Perm.congr_fun hsq₁ z; simpa using this
        have hinv₂ : ∀ z, ι₂ (ι₂ z) = z := fun z => by
          have := Equiv.Perm.congr_fun hsq₂ z; simpa using this
        induction t with
        | zero => exact hcomp_self x
        | succ t ih =>
          rw [altWalk]
          split_ifs
          · have h1 : altWalk ι₁ ι₂ x t ∈ comp (ι₁ (altWalk ι₁ ι₂ x t)) := by
              have := (hcomp_closed _ _ (hcomp_self (ι₁ (altWalk ι₁ ι₂ x t)))).1
              rwa [hinv₁] at this
            exact hsub _ _ h1 ih
          · have h2 : altWalk ι₁ ι₂ x t ∈ comp (ι₂ (altWalk ι₁ ι₂ x t)) := by
              have := (hcomp_closed _ _ (hcomp_self (ι₂ (altWalk ι₁ ι₂ x t)))).2
              rwa [hinv₂] at this
            exact hsub _ _ h2 ih
      exact Finset.Subset.antisymm (hsub x y hy) (hsub y x hsymm)
    -- Minimum of comp(x) and parity of position from minComp(x)
    let minComp (x : α) : α := minByIdx (comp x) ⟨x, hcomp_self x⟩
    have hminComp_inv : ∀ x, minComp (ι₁ x) = minComp x ∧ minComp (ι₂ x) = minComp x := fun x =>
      ⟨hminByIdx_eq ⟨ι₁ x, hcomp_self (ι₁ x)⟩ ⟨x, hcomp_self x⟩
          (hcomp_eq x (ι₁ x) (hcomp_closed x x (hcomp_self x)).1),
       hminByIdx_eq ⟨ι₂ x, hcomp_self (ι₂ x)⟩ ⟨x, hcomp_self x⟩
          (hcomp_eq x (ι₂ x) (hcomp_closed x x (hcomp_self x)).2)⟩
    let isEvenPos (x : α) : Prop := ∃ k : ℕ, (σ ^ k) (minComp x) = x
    have hisEven_ι₁ : ∀ x, isEvenPos (ι₁ x) ↔ ¬ isEvenPos x := by
      intro x
      have hinv₁ : ∀ z, ι₁ (ι₁ z) = z := fun z => by
        have := Equiv.Perm.congr_fun hsq₁ z; simpa using this
      simp only [isEvenPos, (hminComp_inv x).1]
      constructor
      · rintro ⟨j, hj⟩ ⟨k, hk⟩
        exact altWalk_even_ne_odd h₁ h₂ (minComp x) j k (hj.trans (congrArg ι₁ hk.symm))
      · intro hnot
        have hx : x ∈ comp (minComp x) := by
          rw [hcomp_eq x (minComp x) (hminByIdx_mem (comp x) ⟨x, hcomp_self x⟩)]; exact hcomp_self x
        obtain ⟨t, ht⟩ := (hcomp_iff (minComp x) x).1 hx
        rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hk, ← two_mul, altWalk_even] at ht
          exact (hnot ⟨k, ht⟩).elim
        · rw [hk, altWalk_odd] at ht
          exact ⟨k, by have h := congrArg ι₁ ht; rwa [hinv₁] at h⟩
    have hisEven_ι₂ : ∀ x, isEvenPos (ι₂ x) ↔ ¬ isEvenPos x := by
      intro x
      have hinv₂ : ∀ z, ι₂ (ι₂ z) = z := fun z => by
        have := Equiv.Perm.congr_fun hsq₂ z; simpa using this
      have hinv₁ : ∀ z, ι₁ (ι₁ z) = z := fun z => by
        have := Equiv.Perm.congr_fun hsq₁ z; simpa using this
      simp only [isEvenPos, (hminComp_inv x).2]
      constructor
      · rintro ⟨j, hj⟩ ⟨k, hk⟩
        -- ι₂ x = σ^j m and x = σ^k m ⇒ σ^k m = ι₂ (σ^j m) = ι₁ (σ^(j-1) m)
        let L := Function.minimalPeriod σ (minComp x)
        have hL : 0 < L :=
          Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts σ _)
        have hσL : (σ ^ L) (minComp x) = minComp x := by
          rw [Equiv.Perm.coe_pow]; exact Function.iterate_minimalPeriod
        have h1 : (σ ^ (j + L)) (minComp x) = ι₂ x := by
          rw [pow_add, Equiv.Perm.coe_mul, Function.comp_apply, hσL, hj]
        have h2 : ι₂ (ι₂ x) = ι₁ ((σ ^ (j + L - 1)) (minComp x)) := by
          have hstep : σ ^ (j + L) = σ * σ ^ (j + L - 1) := by
            conv_lhs => rw [show j + L = (j + L - 1) + 1 by omega]
            rw [pow_succ']
          rw [← h1, hstep]
          simp only [σ, Equiv.Perm.coe_mul, Function.comp_apply, hinv₂]
        rw [hinv₂] at h2
        exact altWalk_even_ne_odd h₁ h₂ (minComp x) k (j + L - 1) (hk.trans h2)
      · intro hnot
        have hx : x ∈ comp (minComp x) := by
          rw [hcomp_eq x (minComp x) (hminByIdx_mem (comp x) ⟨x, hcomp_self x⟩)]; exact hcomp_self x
        obtain ⟨t, ht⟩ := (hcomp_iff (minComp x) x).1 hx
        rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hk, ← two_mul, altWalk_even] at ht
          exact (hnot ⟨k, ht⟩).elim
        · rw [hk, altWalk_odd] at ht
          exact ⟨k + 1, by rw [pow_succ']; simp [σ, ht]⟩
    let ρ : Equiv.Perm α :=
      { toFun := fun x => if isEvenPos x then ι₁ x else ι₂ x
        invFun := fun x => if isEvenPos x then ι₂ x else ι₁ x
        left_inv := fun x => by
          dsimp only
          have hinv₁ : ι₁ (ι₁ x) = x := by
            have := Equiv.Perm.congr_fun hsq₁ x; simpa using this
          have hinv₂ : ι₂ (ι₂ x) = x := by
            have := Equiv.Perm.congr_fun hsq₂ x; simpa using this
          by_cases hx : isEvenPos x
          · rw [if_pos hx, if_neg (fun h => (hisEven_ι₁ x).1 h hx), hinv₁]
          · rw [if_neg hx, if_pos ((hisEven_ι₂ x).2 hx), hinv₂]
        right_inv := fun x => by
          dsimp only
          have hinv₁ : ι₁ (ι₁ x) = x := by
            have := Equiv.Perm.congr_fun hsq₁ x; simpa using this
          have hinv₂ : ι₂ (ι₂ x) = x := by
            have := Equiv.Perm.congr_fun hsq₂ x; simpa using this
          by_cases hx : isEvenPos x
          · rw [if_pos hx, if_neg (fun h => (hisEven_ι₂ x).1 h hx), hinv₂]
          · rw [if_neg hx, if_pos ((hisEven_ι₁ x).2 hx), hinv₁] }
    -- ρ^[t] (minComp x) = altWalk ι₁ ι₂ (minComp x) t
    have hρ_walk : ∀ (x : α) (t : ℕ), ρ^[t] (minComp x) = altWalk ι₁ ι₂ (minComp x) t := by
      intro x t
      induction t with
      | zero => rfl
      | succ t ih =>
        rw [Function.iterate_succ_apply', ih, altWalk]
        rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
        · rw [hk, ← two_mul, if_pos (even_two_mul k), altWalk_even]
          have hmc : minComp ((σ ^ k) (minComp x)) = minComp x := by
            have hm : (σ ^ k) (minComp x) ∈ comp (minComp x) :=
              (hcomp_iff _ _).2 ⟨2 * k, altWalk_even ι₁ ι₂ _ k⟩
            have hmc_eq : comp ((σ ^ k) (minComp x)) = comp x := by
              rw [hcomp_eq _ _ hm, hcomp_eq x (minComp x) (hminByIdx_mem (comp x) ⟨x, hcomp_self x⟩)]
            exact hminByIdx_eq ⟨_, hcomp_self _⟩ ⟨x, hcomp_self x⟩ hmc_eq
          have hev : isEvenPos (((ι₂ * ι₁) ^ k) (minComp x)) := ⟨k, by rw [hmc]⟩
          simp only [ρ, Equiv.coe_fn_mk, if_pos hev]
        · rw [hk, if_neg (by simp), altWalk_odd]
          have hmc : minComp (ι₁ ((σ ^ k) (minComp x))) = minComp x := by
            have hm : ι₁ ((σ ^ k) (minComp x)) ∈ comp (minComp x) :=
              (hcomp_iff _ _).2 ⟨2 * k + 1, altWalk_odd ι₁ ι₂ _ k⟩
            have hmc_eq : comp (ι₁ ((σ ^ k) (minComp x))) = comp x := by
              rw [hcomp_eq _ _ hm, hcomp_eq x (minComp x) (hminByIdx_mem (comp x) ⟨x, hcomp_self x⟩)]
            exact hminByIdx_eq ⟨_, hcomp_self _⟩ ⟨x, hcomp_self x⟩ hmc_eq
          have hnot : ¬ isEvenPos (ι₁ (((ι₂ * ι₁) ^ k) (minComp x))) := by
            rintro ⟨j, hj⟩
            change (σ ^ j) (minComp (ι₁ ((σ ^ k) (minComp x)))) = _ at hj
            rw [hmc] at hj
            exact altWalk_even_ne_odd h₁ h₂ (minComp x) j k hj
          simp only [ρ, Equiv.coe_fn_mk, if_neg hnot]
    -- permOrbit ρ x = comp x and minimalPeriod ρ (minComp x) = 2 * minimalPeriod σ (minComp x)
    have hρ_orb : ∀ x, permOrbit ρ x = comp x := by
      intro x
      have h1 : permOrbit ρ (minComp x) = comp (minComp x) := by
        ext y; rw [mem_permOrbit_iff, hcomp_iff]
        exact ⟨fun ⟨t, ht⟩ => ⟨t, (hρ_walk x t).symm.trans ht⟩,
          fun ⟨t, ht⟩ => ⟨t, (hρ_walk x t).trans ht⟩⟩
      have hx_in : x ∈ permOrbit ρ (minComp x) := by
        rw [h1, hcomp_eq x (minComp x) (hminByIdx_mem (comp x) ⟨x, hcomp_self x⟩)]; exact hcomp_self x
      rw [permOrbit_eq_of_mem hx_in, h1,
        hcomp_eq x (minComp x) (hminByIdx_mem (comp x) ⟨x, hcomp_self x⟩)]
    have hρ_even : ρ ∈ evenCyclePerms α := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x => ?_⟩
      have hmin_eq : minElt ρ x = minComp x :=
        hminByIdx_eq ⟨x, mem_permOrbit_self ρ x⟩ ⟨x, hcomp_self x⟩ (hρ_orb x)
      rw [← minimalPeriod_eq_of_mem_permOrbit
            (hminByIdx_mem (permOrbit ρ x) ⟨x, mem_permOrbit_self ρ x⟩),
        show minByIdx (permOrbit ρ x) ⟨x, mem_permOrbit_self ρ x⟩ = minComp x from hmin_eq]
      let L := Function.minimalPeriod σ (minComp x)
      have hper : Function.minimalPeriod ρ (minComp x) = 2 * L := by
        have hpos : 0 < Function.minimalPeriod ρ (minComp x) :=
          Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts ρ _)
        have hdvd : Function.minimalPeriod ρ (minComp x) ∣ 2 * L :=
          Function.IsPeriodicPt.minimalPeriod_dvd (show ρ^[2 * L] (minComp x) = minComp x by
            rw [hρ_walk, altWalk_even, Equiv.Perm.coe_pow]
            exact Function.iterate_minimalPeriod)
        have hge : 2 * L ≤ Function.minimalPeriod ρ (minComp x) := by
          set p := Function.minimalPeriod ρ (minComp x)
          have hp_eq : altWalk ι₁ ι₂ (minComp x) p = minComp x := by
            rw [← hρ_walk]; exact Function.iterate_minimalPeriod
          rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
          · rw [hk, ← two_mul, altWalk_even] at hp_eq
            have hk_pos : 0 < k := by omega
            have hdvdL : L ∣ k :=
              Function.IsPeriodicPt.minimalPeriod_dvd (show σ^[k] (minComp x) = minComp x by
                rwa [← Equiv.Perm.coe_pow])
            have hLk := Nat.le_of_dvd hk_pos hdvdL
            omega
          · rw [hk, altWalk_odd] at hp_eq
            exact (altWalk_even_ne_odd h₁ h₂ (minComp x) 0 k (by simpa using hp_eq.symm)).elim
        exact le_antisymm (Nat.le_of_dvd (by
          have := Function.minimalPeriod_pos_of_mem_periodicPts (perm_mem_periodicPts σ (minComp x))
          omega) hdvd) hge
      rw [hper]; exact even_two_mul L
    refine ⟨⟨ρ, hρ_even⟩, Finset.mem_attach _ _, ?_⟩
    have hpar_eq : ∀ x, Even (distElt ρ x) ↔ isEvenPos x := by
      intro x
      have hmin_eq : minElt ρ x = minComp x :=
        hminByIdx_eq ⟨x, mem_permOrbit_self ρ x⟩ ⟨x, hcomp_self x⟩ (hρ_orb x)
      have hx_walk : altWalk ι₁ ι₂ (minComp x) (distElt ρ x) = x := by
        rw [← hρ_walk, ← hmin_eq, hdist_spec]
      constructor
      · rintro ⟨k, hk⟩
        rw [hk, ← two_mul, altWalk_even] at hx_walk
        exact ⟨k, hx_walk⟩
      · rintro ⟨j, hj⟩
        by_contra hnot
        rcases Nat.not_even_iff_odd.1 hnot with ⟨k, hk⟩
        rw [hk, altWalk_odd] at hx_walk
        exact altWalk_even_ne_odd h₁ h₂ (minComp x) j k (hj.trans hx_walk.symm)
    apply Prod.ext
    · refine Equiv.Perm.ext fun x => ?_
      simp only [mkInv1, Equiv.coe_fn_mk, ρ, hpar_eq x]
      by_cases hx : isEvenPos x <;> simp [hx]
    · refine Equiv.Perm.ext fun x => ?_
      simp only [mkInv2, Equiv.coe_fn_mk, ρ, hpar_eq x]
      by_cases hx : isEvenPos x <;> simp [hx]
  · -- Term equality: pfTerm A (mkInv1 ρ) * pfTerm A (mkInv2 ρ) = sign ρ * ∏ x, A x (ρ x)
    rintro ⟨ρ, hρ⟩ _
    let Eset : Finset α := Finset.univ.filter fun x => Even (distElt ρ x)
    have hdisj : Disjoint Eset (Eset.image ρ) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx2
      exact (hdist_parity_step ρ hρ y).1 (Finset.mem_filter.1 hx1).2 (Finset.mem_filter.1 hy).2
    have hunion : Eset ∪ Eset.image ρ = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
      by_cases hx : Even (distElt ρ x)
      · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩)
      · refine Or.inr ⟨ρ⁻¹ x, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, by simp⟩
        by_contra hnot
        exact hx ((hdist_parity_step ρ hρ (ρ⁻¹ x)).2 hnot |> fun h => by simpa using h)
    have hE_card : Eset.card = M := by
      have h1 := congrArg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ ρ.injective,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h1
      omega
    let eE : Fin M ≃ Eset := (Fintype.equivFinOfCardEq (by simp [hE_card])).symm
    let π₁Fun : Fin M × Fin 2 → α := fun p => if p.2 = 0 then (eE p.1).1 else ρ (eE p.1).1
    have hπ₁_inj : Function.Injective π₁Fun := by
      rintro ⟨k₁, b₁⟩ ⟨k₂, b₂⟩ h
      rcases (show b₁ = 0 ∨ b₁ = 1 by fin_cases b₁ <;> simp) with rfl | rfl <;>
        rcases (show b₂ = 0 ∨ b₂ = 1 by fin_cases b₂ <;> simp) with rfl | rfl
      · exact Prod.ext (eE.injective (Subtype.ext (by simpa [π₁Fun] using h))) rfl
      · have h' : (eE k₁).1 = ρ (eE k₂).1 := by simpa [π₁Fun] using h
        exact (Finset.disjoint_left.1 hdisj (eE k₁).2 (h' ▸ Finset.mem_image_of_mem ρ (eE k₂).2)).elim
      · have h' : ρ (eE k₁).1 = (eE k₂).1 := by simpa [π₁Fun] using h
        exact (Finset.disjoint_left.1 hdisj (eE k₂).2 (h'.symm ▸ Finset.mem_image_of_mem ρ (eE k₁).2)).elim
      · have h' : ρ (eE k₁).1 = ρ (eE k₂).1 := by simpa [π₁Fun] using h
        exact Prod.ext (eE.injective (Subtype.ext (ρ.injective h'))) rfl
    let π₁ : Equiv.Perm α := Equiv.ofBijective π₁Fun (Finite.injective_iff_bijective.1 hπ₁_inj)
    let π₂ : Equiv.Perm α := ρ * π₁
    have hπ₁_real : π₁ * baseInv M * π₁⁻¹ = mkInv1 ρ hρ := by
      rw [mul_inv_eq_iff_eq_mul]
      refine Equiv.Perm.ext fun ⟨k, b⟩ => ?_
      rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
      · have hev : Even (distElt ρ (eE k).1) := (Finset.mem_filter.1 (eE k).2).2
        simp [π₁, π₁Fun, baseInv, mkInv1, hev]
      · have hodd : ¬ Even (distElt ρ (ρ (eE k).1)) :=
          fun h => (hdist_parity_step ρ hρ (eE k).1).1 h (Finset.mem_filter.1 (eE k).2).2
        simp [π₁, π₁Fun, baseInv, mkInv1, hodd]
    have hπ₂_real : π₂ * baseInv M * π₂⁻¹ = mkInv2 ρ hρ := by
      rw [mul_inv_eq_iff_eq_mul]
      refine Equiv.Perm.ext fun ⟨k, b⟩ => ?_
      rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
      · have hodd : ¬ Even (distElt ρ (ρ (eE k).1)) :=
          fun h => (hdist_parity_step ρ hρ (eE k).1).1 h (Finset.mem_filter.1 (eE k).2).2
        simp [π₂, π₁, π₁Fun, baseInv, mkInv2, hodd]
      · have hev : Even (distElt ρ (ρ (ρ (eE k).1))) :=
          (hdist_parity_step ρ hρ (ρ (eE k).1)).2
            (fun h => (hdist_parity_step ρ hρ (eE k).1).1 h (Finset.mem_filter.1 (eE k).2).2)
        simp [π₂, π₁, π₁Fun, baseInv, mkInv2, hev]
    rw [pfTerm_eq_of_realizing hskew (hmkInv_mem ρ hρ).1 hπ₁_real,
      pfTerm_eq_of_realizing hskew (hmkInv_mem ρ hρ).2 hπ₂_real]
    have hsign_mul : ((Equiv.Perm.sign π₁ : ℤ) : K) * ((Equiv.Perm.sign π₂ : ℤ) : K) =
        ((Equiv.Perm.sign ρ : ℤ) : K) := by
      simp only [π₂, map_mul, Units.val_mul, Int.cast_mul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign π₁) with h | h <;> simp [h]
    have hprod_mul :
        (∏ k : Fin M, A (π₁ (k, 0)) (π₁ (k, 1))) * (∏ k : Fin M, A (π₂ (k, 0)) (π₂ (k, 1))) =
        ∏ x : α, A x (ρ x) := by
      have h1 : (∏ k : Fin M, A (π₁ (k, 0)) (π₁ (k, 1))) = ∏ x ∈ Eset, A x (ρ x) := by
        rw [← Finset.prod_coe_sort Eset]
        exact (Equiv.prod_comp eE (fun x : Eset => A x.1 (ρ x.1)))
      have h2 : (∏ k : Fin M, A (π₂ (k, 0)) (π₂ (k, 1))) = ∏ x ∈ Eset.image ρ, A x (ρ x) := by
        rw [Finset.prod_image (fun a _ b _ h => ρ.injective h), ← Finset.prod_coe_sort Eset]
        exact Equiv.prod_comp eE (fun x : Eset => A (ρ x.1) (ρ (ρ x.1)))
      rw [h1, h2, ← Finset.prod_union hdisj, hunion]
    symm
    calc (((Equiv.Perm.sign π₁ : ℤ) : K) * ∏ k : Fin M, A (π₁ (k, 0)) (π₁ (k, 1))) *
          (((Equiv.Perm.sign π₂ : ℤ) : K) * ∏ k : Fin M, A (π₂ (k, 0)) (π₂ (k, 1)))
        = (((Equiv.Perm.sign π₁ : ℤ) : K) * ((Equiv.Perm.sign π₂ : ℤ) : K)) *
          ((∏ k : Fin M, A (π₁ (k, 0)) (π₁ (k, 1))) * (∏ k : Fin M, A (π₂ (k, 0)) (π₂ (k, 1)))) := by
            ring
      _ = ((Equiv.Perm.sign ρ : ℤ) : K) * ∏ x : α, A x (ρ x) := by rw [hsign_mul, hprod_mul]

/-- Any `WMat a β` with `dot2 β a = 1` is alternating (`A x x = 0` and `A y x = -A x y`). -/
lemma WMat_alternating {s : ℕ} {a β : 𝔽₂ s} (hba : dot2 β a = 1) :
    (∀ x, WMat a β x x = 0) ∧ (∀ x y, WMat a β y x = -WMat a β x y) := by
  have ha : a ≠ 0 := by intro h; subst h; simp [dot2_zero_right] at hba
  constructor
  · intro x
    have hne : x ≠ x + a := fun h => ha (by simpa using h.symm)
    simp [WMat, hne]
  · intro x y
    by_cases h : y = x + a
    · subst h
      have hback : x = x + a + a := by rw [add_assoc, vec_add_self, add_zero]
      simp only [WMat, if_pos hback, ↓reduceIte, dot2_add_right, hba, sign2_add, sign2_one,
        mul_neg_one]
    · have hback : x ≠ y + a := fun h' => h (by rw [h', add_assoc, vec_add_self, add_zero])
      simp [WMat, h, hback]

/-- `pfaffian` of `J0Mat` (pulled back along any equivalence `e₀ : Fin M × Fin 2 ≃ 𝔽₂ s`) is `±1`. -/
lemma pfaffian_J0_eq_pm_one {s : ℕ} (hs : 2 ≤ s)
    (e₀ : Fin (2 ^ (s - 1)) × Fin 2 ≃ 𝔽₂ s) :
    let J0' := (J0Mat (by omega : 1 ≤ s)).submatrix e₀ e₀
    pfaffian J0' = 1 ∨ pfaffian J0' = -1 := by
  intro J0'
  have halt := WMat_alternating (dot2_eLast_self (by omega : 1 ≤ s))
  have hskew' : ∀ x y, J0' y x = -J0' x y := fun x y => halt.2 (e₀ x) (e₀ y)
  rw [pfaffian_eq_sum_fpfInvolutions hskew']
  -- Translation by eLast on Fin M × Fin 2
  let ι₀ : Equiv.Perm (Fin (2 ^ (s - 1)) × Fin 2) :=
    e₀.symm.permCongr (Equiv.addRight (eLast (by omega : 1 ≤ s)))
  have hι₀_apply : ∀ x, e₀ (ι₀ x) = e₀ x + eLast (by omega : 1 ≤ s) := fun x => by
    simp [ι₀]
  have heLast_ne : eLast (by omega : 1 ≤ s) ≠ 0 := by
    intro h
    have := congrFun h ⟨s - 1, by omega⟩
    simp [eLast] at this
  have hι₀_mem : ι₀ ∈ fpfInvolutions (Fin (2 ^ (s - 1)) × Fin 2) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, fun x hx => ?_⟩
    · refine Equiv.Perm.ext fun x => e₀.injective ?_
      simp [hι₀_apply, add_assoc, vec_add_self]
    · have := hι₀_apply x
      rw [hx] at this
      exact heLast_ne (by simpa using this.symm)
  rw [Finset.sum_eq_single ι₀]
  · obtain ⟨π, hπ⟩ := exists_perm_realizing_fpfInv hι₀_mem
    rw [pfTerm_eq_of_realizing hskew' hι₀_mem hπ]
    have hprod_pm : ∀ k : Fin (2 ^ (s - 1)), J0' (π (k, 0)) (π (k, 1)) = 1 ∨
        J0' (π (k, 0)) (π (k, 1)) = -1 := fun k => by
      have hstep : ι₀ (π (k, 0)) = π (k, 1) := by
        rw [← hπ]; simp [baseInv]
      have heq : e₀ (π (k, 1)) = e₀ (π (k, 0)) + eLast (by omega : 1 ≤ s) := by
        rw [← hstep, hι₀_apply]
      simp only [J0', Matrix.submatrix_apply, J0Mat, WMat, if_pos heq]
      exact sign2_eq_one_or_neg_one _
    have hall : (∏ k : Fin (2 ^ (s - 1)), J0' (π (k, 0)) (π (k, 1))) = 1 ∨
        (∏ k : Fin (2 ^ (s - 1)), J0' (π (k, 0)) (π (k, 1))) = -1 := by
      have hgen : ∀ S : Finset (Fin (2 ^ (s - 1))),
          (∏ k ∈ S, J0' (π (k, 0)) (π (k, 1))) = 1 ∨
          (∏ k ∈ S, J0' (π (k, 0)) (π (k, 1))) = -1 := by
        intro S
        induction S using Finset.induction_on with
        | empty => left; simp
        | insert a S ha ih =>
          rw [Finset.prod_insert ha]
          rcases hprod_pm a with h1 | h1 <;> rcases ih with h2 | h2 <;> simp [h1, h2]
      exact hgen Finset.univ
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h1 | h1 <;>
      rcases hall with h2 | h2 <;> simp [h1, h2]
  · intro ι hι hne
    obtain ⟨π, hπ⟩ := exists_perm_realizing_fpfInv hι
    rw [pfTerm_eq_of_realizing hskew' hι hπ]
    -- Since ι ≠ ι₀, some pair (π (k,0), π (k,1)) does not differ by eLast
    have hex : ∃ k : Fin (2 ^ (s - 1)), e₀ (π (k, 1)) ≠ e₀ (π (k, 0)) + eLast (by omega : 1 ≤ s) := by
      by_contra hall; push Not at hall
      apply hne
      refine Equiv.Perm.ext fun x => ?_
      obtain ⟨⟨k, b⟩, rfl⟩ := π.surjective x
      apply e₀.injective
      have h1 : ι (π (k, 0)) = π (k, 1) := by rw [← hπ]; simp [baseInv]
      have h2 : ι (π (k, 1)) = π (k, 0) := by rw [← hπ]; simp [baseInv]
      rcases (show b = 0 ∨ b = 1 by fin_cases b <;> simp) with rfl | rfl
      · rw [h1, hι₀_apply, hall k]
      · rw [h2, hι₀_apply, hall k, add_assoc, vec_add_self, add_zero]
    obtain ⟨k₀, hk₀⟩ := hex
    have hz : J0' (π (k₀, 0)) (π (k₀, 1)) = 0 := by
      simp [J0', Matrix.submatrix_apply, J0Mat, WMat, hk₀]
    rw [Finset.prod_eq_zero (Finset.mem_univ k₀) hz, mul_zero]
  · intro h; exact (h hι₀_mem).elim

/-- **Lemma 2.1 (Realization certificate)**: if the `t_univ` coefficient of
`pfaffian (J0 + ∑ t_i J_i)` (in `SqFreeRing (Fin M)`) is nonzero, then `d` has a realization! -/
lemma exists_realization_of_pfaffian_coeff_ne_zero {s : ℕ} (hs : 2 ≤ s)
    (d : Fin (2 ^ (s - 1)) → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    (e₀ : Fin (2 ^ (s - 1)) × Fin 2 ≃ 𝔽₂ s)
    (hne : (pfaffian (Matrix.submatrix ((J0Mat (by omega : 1 ≤ s)).map
      (algebraMap ℚ (SqFreeRing (Fin (2 ^ (s - 1))))) +
      ∑ i : Fin (2 ^ (s - 1)),
        SqFreeRing.var i • (JMat d hd i).map
          (algebraMap ℚ (SqFreeRing (Fin (2 ^ (s - 1)))))) e₀ e₀)).coeff Finset.univ ≠ 0) :
    ∃ e : Fin (2 ^ (s - 1)) × Fin 2 ≃ 𝔽₂ s, ∀ i, e (i, 0) + e (i, 1) = d i := by
  let M := 2 ^ (s - 1)
  let A : Matrix (Fin M × Fin 2) (Fin M × Fin 2) (SqFreeRing (Fin M)) :=
    Matrix.submatrix ((J0Mat (by omega : 1 ≤ s)).map (algebraMap ℚ (SqFreeRing (Fin M))) +
      ∑ i : Fin M, SqFreeRing.var i • (JMat d hd i).map (algebraMap ℚ (SqFreeRing (Fin M)))) e₀ e₀
  change (pfaffian A).coeff Finset.univ ≠ 0 at hne
  rw [pfaffian, SqFreeRing.smul_coeff, SqFreeRing.sum_coeff] at hne
  have hsum_ne : (∑ π : Equiv.Perm (Fin M × Fin 2),
      (((Equiv.Perm.sign π : ℤ) : SqFreeRing (Fin M)) *
        ∏ k : Fin M, A (π (k, 0)) (π (k, 1))).coeff Finset.univ) ≠ 0 :=
    fun h => hne (by rw [h, mul_zero])
  obtain ⟨π, _, hπ_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  -- Expand ∏ k : Fin M, A (π (k, 0)) (π (k, 1))
  have hprod_ne : (∏ k : Fin M, A (π (k, 0)) (π (k, 1))).coeff Finset.univ ≠ 0 := by
    intro h0
    apply hπ_ne
    have hsign_c : ((Equiv.Perm.sign π : ℤ) : SqFreeRing (Fin M)) =
        algebraMap ℚ (SqFreeRing (Fin M)) ((Equiv.Perm.sign π : ℤ) : ℚ) := by simp
    rw [hsign_c, ← Algebra.smul_def, SqFreeRing.smul_coeff, h0, mul_zero]
  -- Write A x y = ∑ o : Option (Fin M), term o x y
  let term (k : Fin M) (o : Option (Fin M)) : SqFreeRing (Fin M) :=
    match o with
    | none => algebraMap ℚ _ (J0Mat (by omega : 1 ≤ s) (e₀ (π (k, 0))) (e₀ (π (k, 1))))
    | some i => SqFreeRing.var i * algebraMap ℚ _ (JMat d hd i (e₀ (π (k, 0))) (e₀ (π (k, 1))))
  have hA_eq : ∀ k : Fin M, A (π (k, 0)) (π (k, 1)) = ∑ o : Option (Fin M), term k o := by
    intro k
    rw [Fintype.sum_option]
    simp only [A, Matrix.submatrix_apply, Matrix.add_apply, Matrix.map_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, term]
  simp_rw [hA_eq, Fintype.prod_sum, SqFreeRing.sum_coeff] at hprod_ne
  obtain ⟨f, _, hf_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hprod_ne
  -- Every f k must be `some (σ k)` with σ surjective (hence bijective), otherwise monomial has card < M!
  have hall_some : ∀ k : Fin M, ∃ i : Fin M, f k = some i := by
    intro k
    cases hfk : f k with
    | some i => exact ⟨i, rfl⟩
    | none =>
      exfalso
      apply hf_ne
      -- Show every subset in support of ∏ j, term j (f j) has card ≤ M - 1
      have hdeg : ∀ (S : Finset (Fin M)) (T : Finset (Fin M)),
          (∀ j ∈ S, f j = none → T.card < 0) ∨ True := fun _ _ => Or.inr trivial
      -- Stronger: count of `some` among f j is ≤ M - 1, so coeff at univ (card M) is 0!
      have hbound : ∀ (U : Finset (Fin M)) (T : Finset (Fin M)),
          (U.filter fun j => (f j).isSome).card < T.card →
          (∏ j ∈ U, term j (f j)).coeff T = 0 := by
        intro U
        induction U using Finset.induction_on with
        | empty =>
          intro T hT
          have hTne : T ≠ ∅ := (Finset.card_pos.1 (by simpa using hT)).ne_empty
          simp [hTne]
        | insert a U ha ih =>
          intro T hT
          rw [Finset.prod_insert ha, SqFreeRing.mul_coeff]
          refine Finset.sum_eq_zero fun V hV => ?_
          have hVS : V ⊆ T := Finset.mem_powerset.1 hV
          cases hfa : f a with
          | none =>
            have hfilt : ((insert a U).filter fun j => (f j).isSome) = U.filter fun j => (f j).isSome := by
              rw [Finset.filter_insert, if_neg (by simp [hfa])]
            rw [hfilt] at hT
            by_cases hV0 : V = ∅
            · subst hV0
              rw [Finset.sdiff_empty, ih T hT, mul_zero]
            · simp [term, SqFreeRing.algebraMap_coeff, hV0]
          | some i =>
            have hfilt : ((insert a U).filter fun j => (f j).isSome).card =
                (U.filter fun j => (f j).isSome).card + 1 := by
              rw [Finset.filter_insert, if_pos (by simp [hfa]), Finset.card_insert_of_notMem
                (by simp [ha])]
            rw [hfilt] at hT
            by_cases hVi : V = {i}
            · subst hVi
              have hcard : (T \ {i}).card = T.card - 1 := by
                rw [Finset.card_sdiff, Finset.inter_eq_left.2 hVS, Finset.card_singleton]
              rw [ih (T \ {i}) (by omega), mul_zero]
            · have hz : (term a (some i)).coeff V = 0 := by
                simp only [term, mul_comm (SqFreeRing.var i), ← Algebra.smul_def,
                  SqFreeRing.smul_coeff, SqFreeRing.var_coeff, if_neg hVi, mul_zero]
              rw [hz, zero_mul]
      apply hbound Finset.univ Finset.univ
      have hlt : (Finset.univ.filter fun j => (f j).isSome) ⊂ Finset.univ :=
        Finset.ssubset_univ_iff.2 fun h => by
          have : k ∈ Finset.univ.filter fun j => (f j).isSome := by rw [h]; exact Finset.mem_univ k
          simp [hfk] at this
      exact Finset.card_lt_card hlt
  choose σ hσ using hall_some
  -- Also σ must be injective (otherwise two `var` equal → product is 0!)
  have hσ_inj : Function.Injective σ := by
    intro k₁ k₂ hσeq
    by_contra hne_k
    apply hf_ne
    have hvar_zero : SqFreeRing.var (σ k₁) * SqFreeRing.var (σ k₂) = 0 := by
      rw [hσeq, SqFreeRing.var, SqFreeRing.mon_mul_mon, if_neg (by simp)]
    have hprod_zero : ∏ k : Fin M, term k (f k) = 0 := by
      have h1 : (∏ k : Fin M, term k (f k)) =
          (term k₁ (f k₁) * term k₂ (f k₂)) *
            ∏ k ∈ (Finset.univ.erase k₁).erase k₂, term k (f k) := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₁),
          ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hne_k, Finset.mem_univ k₂⟩),
          mul_assoc]
      rw [h1, hσ k₁, hσ k₂]
      have hpair : term k₁ (some (σ k₁)) * term k₂ (some (σ k₂)) = 0 := by
        simp only [term]
        rw [mul_mul_mul_comm, hvar_zero, zero_mul]
      rw [hpair, zero_mul]
    rw [hprod_zero, SqFreeRing.zero_coeff]
  let σEquiv : Equiv.Perm (Fin M) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσ_inj)
  -- For every k, JMat (σ k) (e₀ (π (k, 0))) (e₀ (π (k, 1))) ≠ 0!
  have hJ_ne : ∀ k : Fin M, JMat d hd (σ k) (e₀ (π (k, 0))) (e₀ (π (k, 1))) ≠ 0 := by
    intro k h0
    apply hf_ne
    have htk : term k (f k) = 0 := by rw [hσ k]; simp [term, h0]
    rw [Finset.prod_eq_zero (Finset.mem_univ k) htk, SqFreeRing.zero_coeff]
  -- Build e(i, b) := e₀ (π (σEquiv.symm i, b))
  let e : Fin M × Fin 2 ≃ 𝔽₂ s :=
    (Equiv.prodCongr σEquiv.symm (Equiv.refl (Fin 2))).trans (π.trans e₀)
  refine ⟨e, fun i => ?_⟩
  have hne_i := hJ_ne (σEquiv.symm i)
  have hσ_symm : σ (σEquiv.symm i) = i := σEquiv.apply_symm_apply i
  rw [hσ_symm] at hne_i
  simp only [JMat, WMat] at hne_i
  have heq : e₀ (π (σEquiv.symm i, 1)) = e₀ (π (σEquiv.symm i, 0)) + d i := by
    by_contra hnot; exact hne_i (if_neg hnot)
  simp only [e, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  rw [heq, ← add_assoc, vec_add_self, zero_add]

end Pfaffian

/- ### Section A4: Main Part A Bridge Theorem -/

/-- **Part A Main Theorem**: Assuming `Lcoeff` satisfies Proposition 2.7 (`Val2Ge S.card` on
proper nonempty `S`) and Proposition 2.8 (`Val2Eq (M - 1)` on `univ`), there exists a
realizing perfect matching `e : Fin (2^(s-1)) × Fin 2 ≃ 𝔽₂ s`. -/
theorem exists_realization_of_Lcoeff_valuation {s : ℕ} (hs : 2 ≤ s)
    (d : Fin (2 ^ (s - 1)) → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    (hprop : ∀ S : Finset (Fin (2 ^ (s - 1))), S.Nonempty → S ≠ Finset.univ →
      Val2Ge S.card (Lcoeff (by omega : 1 ≤ s) d hd S))
    (huniv : Val2Eq (2 ^ (s - 1) - 1) (Lcoeff (by omega : 1 ≤ s) d hd Finset.univ)) :
    ∃ e : Fin (2 ^ (s - 1)) × Fin 2 ≃ 𝔽₂ s, ∀ i, e (i, 0) + e (i, 1) = d i := by
  let M := 2 ^ (s - 1)
  have hcard_eq : Fintype.card (Fin M × Fin 2) = Fintype.card (𝔽₂ s) := by
    simp [M, 𝔽₂, 𝔽, ZMod.card, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ s)]
  let e₀ : Fin M × Fin 2 ≃ 𝔽₂ s := Fintype.equivOfCardEq hcard_eq
  let hs1 : 1 ≤ s := by omega
  let A : Matrix (𝔽₂ s) (𝔽₂ s) (SqFreeRing (Fin M)) :=
    (J0Mat hs1).map (algebraMap ℚ (SqFreeRing (Fin M))) +
      ∑ i : Fin M, SqFreeRing.var i • (JMat d hd i).map (algebraMap ℚ (SqFreeRing (Fin M)))
  let X : Matrix (𝔽₂ s) (𝔽₂ s) (SqFreeRing (Fin M)) :=
    ∑ i : Fin M, SqFreeRing.var i • (BMat hs1 d hd i).map (algebraMap ℚ (SqFreeRing (Fin M)))
  let Λ : SqFreeRing (Fin M) :=
    (1 / 2 : ℚ) • ∑ m ∈ Finset.Icc 1 (Fintype.card (Fin M)),
      ((-1 : ℚ) ^ (m - 1) / (m : ℚ)) • Matrix.trace (X ^ m)
  -- 1. A = J0 * (1 + X)
  have hA_factor : A = (J0Mat hs1).map (algebraMap ℚ (SqFreeRing (Fin M))) * (1 + X) := by
    dsimp only [A, X]
    rw [Matrix.mul_add, Matrix.mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul]
    congr 1
    have hmul_map : (J0Mat hs1).map (algebraMap ℚ (SqFreeRing (Fin M))) *
        (BMat hs1 d hd i).map (algebraMap ℚ (SqFreeRing (Fin M))) =
        (J0Mat hs1 * BMat hs1 d hd i).map (algebraMap ℚ (SqFreeRing (Fin M))) := by
      ext x y; simp [Matrix.mul_apply, map_sum, map_mul]
    rw [hmul_map]
    congr 1
    rw [BMat, Matrix.mul_neg, ← Matrix.mul_assoc, J0Mat_mul_self hs1, Matrix.neg_mul,
      Matrix.one_mul, neg_neg]
  -- 2. A is alternating, so pfaffian (A.submatrix e₀ e₀) ^ 2 = A.det
  have hA_alt : (∀ x, A x x = 0) ∧ (∀ x y, A y x = -A x y) := by
    have h0 := WMat_alternating (dot2_eLast_self hs1)
    have hi : ∀ i, (∀ x, JMat d hd i x x = 0) ∧ (∀ x y, JMat d hd i y x = -JMat d hd i x y) :=
      fun i => WMat_alternating (dot2_eta_self d hd i)
    constructor
    · intro x
      simp only [A, Matrix.add_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        J0Mat, h0.1 x, map_zero, zero_add]
      refine Finset.sum_eq_zero fun i _ => by rw [(hi i).1 x, map_zero, smul_zero]
    · intro x y
      simp only [A, Matrix.add_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        neg_add, ← Finset.sum_neg_distrib]
      congr 1
      · rw [J0Mat, h0.2 x y, map_neg]
      · refine Finset.sum_congr rfl fun i _ => by rw [(hi i).2 x y, map_neg, smul_neg]
  let A' := A.submatrix e₀ e₀
  have hpf_sq : pfaffian A' ^ 2 = A.det := by
    rw [pfaffian_sq_eq_det (A := A') (fun x => hA_alt.1 (e₀ x)) (fun x y => hA_alt.2 (e₀ x) (e₀ y))]
    exact Matrix.det_reindex_self e₀.symm A
  -- 3. Pfaffian of J0' is ±1, hence J0'.det = 1 and pfaffian A' / pfaffian J0' = F
  let J0' := (J0Mat hs1).submatrix e₀ e₀
  have hpfJ0_pm : pfaffian J0' = 1 ∨ pfaffian J0' = -1 := pfaffian_J0_eq_pm_one hs e₀
  have hpfJ0_sq : pfaffian J0' ^ 2 = 1 := by rcases hpfJ0_pm with h | h <;> simp [h]
  have hJ0_det : ((J0Mat hs1).map (algebraMap ℚ (SqFreeRing (Fin M)))).det = 1 := by
    have hmap_det : ((J0Mat hs1).map (algebraMap ℚ (SqFreeRing (Fin M)))).det =
        algebraMap ℚ (SqFreeRing (Fin M)) (J0Mat hs1).det :=
      (RingHom.map_det (algebraMap ℚ (SqFreeRing (Fin M))) (J0Mat hs1)).symm
    rw [hmap_det]
    have hdetJ0 : (J0Mat hs1).det = 1 := by
      have h0 := WMat_alternating (dot2_eLast_self hs1)
      have hsq := pfaffian_sq_eq_det (A := J0') (fun x => h0.1 (e₀ x)) (fun x y => h0.2 (e₀ x) (e₀ y))
      rw [hpfJ0_sq, show J0'.det = (J0Mat hs1).det from Matrix.det_reindex_self e₀.symm (J0Mat hs1)] at hsq
      exact hsq.symm
    rw [hdetJ0, map_one]
  -- 4. F := pfaffian J0' • pfaffian A' satisfies F^2 = (1 + X).det and F.coeff ∅ = 1
  let F : SqFreeRing (Fin M) := pfaffian J0' • pfaffian A'
  have hF_sq : F ^ 2 = (1 + X).det := by
    simp only [F, Algebra.smul_def, mul_pow, ← map_pow, hpfJ0_sq, map_one, one_mul, hpf_sq,
      hA_factor, Matrix.det_mul, hJ0_det, one_mul]
  have hF_empty : F.coeff ∅ = 1 := by
    have hA'_empty : (pfaffian A').coeff ∅ = pfaffian J0' := by
      have hmap : SqFreeRing.coeffEmptyHom (pfaffian A') = pfaffian J0' := by
        simp only [pfaffian, Algebra.smul_def, map_mul, map_sum, map_prod, map_intCast]
        have hhom : SqFreeRing.coeffEmptyHom (algebraMap ℚ (SqFreeRing (Fin M))
            ((2 ^ M * M.factorial : ℕ) : ℚ)⁻¹) = ((2 ^ M * M.factorial : ℕ) : ℚ)⁻¹ := by
          simp only [SqFreeRing.coeffEmptyHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
            SqFreeRing.algebraMap_coeff, ↓reduceIte]
        rw [hhom]
        change ((2 ^ M * M.factorial : ℕ) : ℚ)⁻¹ * _ = ((2 ^ M * M.factorial : ℕ) : ℚ)⁻¹ * _
        congr 1
        refine Finset.sum_congr rfl fun π _ => ?_
        congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        simp only [A', A, J0', Matrix.submatrix_apply, Matrix.add_apply, Matrix.map_apply,
          Matrix.sum_apply, Matrix.smul_apply, SqFreeRing.coeffEmptyHom, RingHom.coe_mk,
          MonoidHom.coe_mk, OneHom.coe_mk, SqFreeRing.add_coeff, SqFreeRing.algebraMap_coeff,
          ↓reduceIte, SqFreeRing.sum_coeff]
        have hsum0 : ∑ i : Fin M, (SqFreeRing.var i •
            algebraMap ℚ (SqFreeRing (Fin M)) (JMat d hd i (e₀ (π (k, 0))) (e₀ (π (k, 1))))).coeff ∅ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [smul_eq_mul, SqFreeRing.mul_coeff]
          simp [SqFreeRing.var]
        rw [hsum0, add_zero]
      exact hmap
    simp only [F, SqFreeRing.smul_coeff, hA'_empty, ← sq, hpfJ0_sq]
  -- 5. By Jacobi/Log-Det + sfExp_add, (1 + X).det = sfExp (2 • Λ) = (sfExp Λ) ^ 2
  have hX_empty : ∀ x y, (X x y).coeff ∅ = 0 := fun x y => by
    simp only [X, Matrix.sum_apply, Matrix.smul_apply, SqFreeRing.sum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [smul_eq_mul, SqFreeRing.mul_coeff]
    simp [SqFreeRing.var]
  have hdet_eq : (1 + X).det = SqFreeRing.sfExp Λ ^ 2 := by
    have hΛ_coeff := logDet_half_coeff_eq_Lcoeff hs1 d hd
    have hΛ_empty : Λ.coeff ∅ = 0 := hΛ_coeff.1
    rw [det_one_add_eq_sfExp_trace X hX_empty, sq, ← SqFreeRing.sfExp_add hΛ_empty hΛ_empty]
    congr 1
    simp only [Λ, ← two_smul ℚ, smul_smul]
    norm_num
  -- 6. Unique square root with constant term 1 in SqFreeRing (Fin M): F = sfExp Λ!
  have hΛ_coeff := logDet_half_coeff_eq_Lcoeff hs1 d hd
  have hF_eq : F = SqFreeRing.sfExp Λ := by
    have hdiff : (F - SqFreeRing.sfExp Λ) * (F + SqFreeRing.sfExp Λ) = 0 := by
      calc (F - SqFreeRing.sfExp Λ) * (F + SqFreeRing.sfExp Λ)
          = F ^ 2 - SqFreeRing.sfExp Λ ^ 2 := by ring
        _ = 0 := by rw [hF_sq, hdet_eq, sub_self]
    have hunit : IsUnit (F + SqFreeRing.sfExp Λ) := by
      refine SqFreeRing.isUnit_of_coeff_empty_ne_zero ?_
      rw [SqFreeRing.add_coeff, hF_empty, SqFreeRing.sfExp_coeff_empty hΛ_coeff.1]
      norm_num
    exact sub_eq_zero.1 (hunit.mul_left_eq_zero.1 hdiff)
  -- 7. Apply Lemma 2.6 valuation bound → F.coeff univ ≠ 0 → pfaffian A'.coeff univ ≠ 0 → Lemma 2.1!
  have hM1 : 1 ≤ Fintype.card (Fin M) := by
    rw [Fintype.card_fin]; exact Nat.one_le_two_pow
  have hval : Val2Eq (Fintype.card (Fin M) - 1) (F.coeff Finset.univ) := by
    rw [hF_eq]
    refine SqFreeRing.sfExp_coeff_univ_val2Eq hΛ_coeff.1 hM1 ?_ ?_
    · intro S hSne hSnu
      rw [hΛ_coeff.2 S hSne]
      exact hprop S hSne hSnu
    · have huniv_ne : (Finset.univ : Finset (Fin M)).Nonempty :=
        Finset.card_pos.1 (by rw [Finset.card_univ]; exact hM1)
      rw [hΛ_coeff.2 Finset.univ huniv_ne, Fintype.card_fin]
      exact huniv
  have hF_ne : F.coeff Finset.univ ≠ 0 := val2Eq_ne_zero hval
  have hpf_ne : (pfaffian A').coeff Finset.univ ≠ 0 := by
    intro h0; apply hF_ne; simp [F, h0]
  exact exists_realization_of_pfaffian_coeff_ne_zero hs d hd e₀ hpf_ne

end OMA.BGS

-- ===== BEGIN PART B (§4: Binary Trees, Ordering Sums, Prop 2.7, Prop 4.5) =====

namespace OMA.BGS

/- ### 7. Binary tree structural properties (`IsTree`, `IsGoodTree`, `treesOn`) -/

lemma IsTree.card {α : Type*} [DecidableEq α] :
    ∀ {k : ℕ} {A : Finset α} {N : Finset (Finset α)}, IsTree k A N → A.card = 2 ^ k
  | 0, _, _, h => h.1
  | k + 1, _, _, h => by
    obtain ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h₁, h₂, _⟩ := h
    rw [← hunion, Finset.card_union_of_disjoint hdisj, h₁.card, h₂.card]
    ring

lemma IsTree.mem_self {α : Type*} [DecidableEq α] {k : ℕ} {A : Finset α}
    {N : Finset (Finset α)} (h : IsTree k A N) : A ∈ N := by
  cases k with
  | zero => rw [h.2]; exact Finset.mem_singleton_self A
  | succ k =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h
    exact Finset.mem_insert_self A _

lemma IsTree.subset_root {α : Type*} [DecidableEq α] :
    ∀ {k : ℕ} {A : Finset α} {N : Finset (Finset α)}, IsTree k A N → ∀ C ∈ N, C ⊆ A
  | 0, _, _, h, C, hC => by
    rw [h.2] at hC
    rw [Finset.mem_singleton.1 hC]
  | k + 1, _, _, h, C, hC => by
    obtain ⟨A₁, A₂, N₁, N₂, _, hunion, h₁, h₂, rfl⟩ := h
    rcases Finset.mem_insert.1 hC with rfl | hC
    · exact Finset.Subset.refl _
    · rcases Finset.mem_union.1 hC with hC | hC
      · exact (h₁.subset_root C hC).trans (hunion ▸ Finset.subset_union_left)
      · exact (h₂.subset_root C hC).trans (hunion ▸ Finset.subset_union_right)

lemma IsTree.nonempty_node {α : Type*} [DecidableEq α] :
    ∀ {k : ℕ} {A : Finset α} {N : Finset (Finset α)}, IsTree k A N → ∀ C ∈ N, C.Nonempty
  | 0, A, _, h, C, hC => by
    have hcard : A.card = 1 := h.1
    rw [h.2] at hC
    rw [Finset.mem_singleton.1 hC]
    exact Finset.card_pos.1 (by omega)
  | k + 1, A, _, h, C, hC => by
    have hcard : A.card = 2 ^ (k + 1) := h.card
    obtain ⟨_, _, _, _, _, _, h₁, h₂, rfl⟩ := h
    rcases Finset.mem_insert.1 hC with rfl | hC
    · exact Finset.card_pos.1 (by rw [hcard]; positivity)
    · rcases Finset.mem_union.1 hC with hC | hC
      · exact h₁.nonempty_node C hC
      · exact h₂.nonempty_node C hC

lemma IsTree.card_eq_root {α : Type*} [DecidableEq α] {k : ℕ} {A : Finset α}
    {N : Finset (Finset α)} (h : IsTree k A N) {C : Finset α} (hC : C ∈ N)
    (hcard : C.card = 2 ^ k) : C = A :=
  Finset.eq_of_subset_of_card_le (h.subset_root C hC) (by rw [h.card, hcard])

lemma mem_treesOn {α : Type*} [DecidableEq α] {k : ℕ} {A : Finset α}
    {N : Finset (Finset α)} : N ∈ treesOn k A ↔ IsTree k A N := by
  classical
  simp only [treesOn, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  intro C hC
  exact Finset.mem_powerset.2 (h.subset_root C hC)

lemma IsTree.children_unique {α : Type*} [DecidableEq α] {k : ℕ} {A : Finset α}
    {A₁ A₂ B₁ B₂ : Finset α} {N₁ N₂ M₁ M₂ : Finset (Finset α)}
    (hdisjA : Disjoint A₁ A₂) (hunionA : A₁ ∪ A₂ = A)
    (hA₁ : IsTree k A₁ N₁) (hA₂ : IsTree k A₂ N₂)
    (hdisjB : Disjoint B₁ B₂) (hunionB : B₁ ∪ B₂ = A)
    (hB₁ : IsTree k B₁ M₁) (hB₂ : IsTree k B₂ M₂)
    (heq : insert A (N₁ ∪ N₂) = insert A (M₁ ∪ M₂)) :
    (A₁ = B₁ ∧ A₂ = B₂ ∧ N₁ = M₁ ∧ N₂ = M₂) ∨
    (A₁ = B₂ ∧ A₂ = B₁ ∧ N₁ = M₂ ∧ N₂ = M₁) := by
  classical
  have hAcard : A.card = 2 ^ (k + 1) := by
    rw [← hunionA, Finset.card_union_of_disjoint hdisjA, hA₁.card, hA₂.card]; ring
  have hB1_mem : B₁ ∈ insert A (N₁ ∪ N₂) := by
    rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hB₁.mem_self)
  have hB1_ne_A : B₁ ≠ A := by
    intro h
    have := congrArg Finset.card h
    rw [hB₁.card, hAcard] at this
    have : 0 < 2 ^ k := by positivity
    omega
  have hB1_in : B₁ ∈ N₁ ∪ N₂ := (Finset.mem_insert.1 hB1_mem).resolve_left hB1_ne_A
  have hsub_recover : ∀ {X₁ X₂ : Finset α} {K₁ K₂ : Finset (Finset α)},
      Disjoint X₁ X₂ → X₁ ∪ X₂ = A → IsTree k X₁ K₁ → IsTree k X₂ K₂ →
      (insert A (K₁ ∪ K₂)).filter (fun C => C ⊆ X₁) = K₁ := by
    intro X₁ X₂ K₁ K₂ hd hu hK₁ hK₂
    ext C
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨rfl | hC | hC, hsub⟩
      · have := Finset.card_le_card hsub
        rw [hAcard, hK₁.card] at this
        have : 0 < 2 ^ k := by positivity
        omega
      · exact hC
      · obtain ⟨x, hx⟩ := hK₂.nonempty_node C hC
        exact (Finset.disjoint_left.1 hd (hsub hx) (hK₂.subset_root C hC hx)).elim
    · intro hC
      exact ⟨Or.inr (Or.inl hC), hK₁.subset_root C hC⟩
  have hsub_recover₂ : ∀ {X₁ X₂ : Finset α} {K₁ K₂ : Finset (Finset α)},
      Disjoint X₁ X₂ → X₁ ∪ X₂ = A → IsTree k X₁ K₁ → IsTree k X₂ K₂ →
      (insert A (K₁ ∪ K₂)).filter (fun C => C ⊆ X₂) = K₂ := by
    intro X₁ X₂ K₁ K₂ hd hu hK₁ hK₂
    rw [Finset.union_comm K₁ K₂]
    exact hsub_recover hd.symm (by rw [Finset.union_comm, hu]) hK₂ hK₁
  rcases Finset.mem_union.1 hB1_in with hB1_N1 | hB1_N2
  · have h1 : A₁ = B₁ := (hA₁.card_eq_root hB1_N1 hB₁.card).symm
    have h2 : A₂ = B₂ := by
      have hA2 : A \ A₁ = A₂ := by rw [← hunionA, Finset.union_sdiff_cancel_left hdisjA]
      have hB2 : A \ B₁ = B₂ := by rw [← hunionB, Finset.union_sdiff_cancel_left hdisjB]
      rw [← hA2, ← hB2, h1]
    have hN1 : N₁ = M₁ := by
      rw [← hsub_recover hdisjA hunionA hA₁ hA₂, heq, h1, hsub_recover hdisjB hunionB hB₁ hB₂]
    have hN2 : N₂ = M₂ := by
      rw [← hsub_recover₂ hdisjA hunionA hA₁ hA₂, heq, h2, hsub_recover₂ hdisjB hunionB hB₁ hB₂]
    exact Or.inl ⟨h1, h2, hN1, hN2⟩
  · have h1 : A₂ = B₁ := (hA₂.card_eq_root hB1_N2 hB₁.card).symm
    have h2 : A₁ = B₂ := by
      have hA1 : A \ A₂ = A₁ := by rw [← hunionA, Finset.union_sdiff_cancel_right hdisjA]
      have hB2 : A \ B₁ = B₂ := by rw [← hunionB, Finset.union_sdiff_cancel_left hdisjB]
      rw [← hA1, ← hB2, h1]
    have hN1 : N₁ = M₂ := by
      rw [← hsub_recover hdisjA hunionA hA₁ hA₂, heq, h2, hsub_recover₂ hdisjB hunionB hB₁ hB₂]
    have hN2 : N₂ = M₁ := by
      rw [← hsub_recover₂ hdisjA hunionA hA₁ hA₂, heq, h1, hsub_recover hdisjB hunionB hB₁ hB₂]
    exact Or.inr ⟨h2, h1, hN1, hN2⟩

lemma isGoodTree_zero {α : Type*} [DecidableEq α] {s : ℕ} (b : α → 𝔽₂ s × 𝔽₂ s)
    {A : Finset α} (hA : A.card = 1) : IsGoodTree b ({A} : Finset (Finset α)) := by
  intro C₁ hC₁ C₂ hC₂ hdisj _ _
  rw [Finset.mem_singleton.1 hC₁, Finset.mem_singleton.1 hC₂] at hdisj
  obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < A.card)
  exact (Finset.disjoint_left.1 hdisj hx hx).elim

lemma isGoodTree_succ_iff {α : Type*} [DecidableEq α] {s : ℕ} (b : α → 𝔽₂ s × 𝔽₂ s)
    {k : ℕ} {A A₁ A₂ : Finset α} {N₁ N₂ : Finset (Finset α)}
    (hdisj : Disjoint A₁ A₂) (hunion : A₁ ∪ A₂ = A)
    (h₁ : IsTree k A₁ N₁) (h₂ : IsTree k A₂ N₂) :
    IsGoodTree b (insert A (N₁ ∪ N₂)) ↔
      IsGoodTree b N₁ ∧ IsGoodTree b N₂ ∧ symp (bSum b A₁) (bSum b A₂) = 0 := by
  constructor
  · intro hg
    refine ⟨?_, ?_, ?_⟩
    · intro C₁ hC₁ C₂ hC₂ hd hc hu
      exact hg C₁ (Finset.mem_insert_of_mem (Finset.mem_union_left _ hC₁))
        C₂ (Finset.mem_insert_of_mem (Finset.mem_union_left _ hC₂)) hd hc
        (Finset.mem_insert_of_mem (Finset.mem_union_left _ hu))
    · intro C₁ hC₁ C₂ hC₂ hd hc hu
      exact hg C₁ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hC₁))
        C₂ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hC₂)) hd hc
        (Finset.mem_insert_of_mem (Finset.mem_union_right _ hu))
    · refine hg A₁ (Finset.mem_insert_of_mem (Finset.mem_union_left _ h₁.mem_self))
        A₂ (Finset.mem_insert_of_mem (Finset.mem_union_right _ h₂.mem_self))
        hdisj (by rw [h₁.card, h₂.card]) ?_
      rw [hunion]
      exact Finset.mem_insert_self A _
  · rintro ⟨hg₁, hg₂, hsymp⟩ C₁ hC₁ C₂ hC₂ hd hc hu
    have htree : IsTree (k + 1) A (insert A (N₁ ∪ N₂)) :=
      ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h₁, h₂, rfl⟩
    have hC1ne : C₁ ≠ A := by
      rintro rfl
      obtain ⟨x, hx⟩ := htree.nonempty_node C₂ hC₂
      exact Finset.disjoint_left.1 hd (htree.subset_root C₂ hC₂ hx) hx
    have hC2ne : C₂ ≠ A := by
      rintro rfl
      obtain ⟨x, hx⟩ := htree.nonempty_node C₁ hC₁
      exact Finset.disjoint_right.1 hd (htree.subset_root C₁ hC₁ hx) hx
    have hC1' := (Finset.mem_insert.1 hC₁).resolve_left hC1ne
    have hC2' := (Finset.mem_insert.1 hC₂).resolve_left hC2ne
    rcases Finset.mem_union.1 hC1' with hC1_1 | hC1_2 <;>
    rcases Finset.mem_union.1 hC2' with hC2_1 | hC2_2
    · have hu1 : C₁ ∪ C₂ ∈ N₁ := by
        rcases Finset.mem_insert.1 hu with huA | hu12
        · exfalso
          obtain ⟨x, hx⟩ := h₂.nonempty_node A₂ h₂.mem_self
          have hxA : x ∈ A := hunion ▸ Finset.mem_union_right A₁ hx
          rw [← huA] at hxA
          rcases Finset.mem_union.1 hxA with hx1 | hx2
          · exact Finset.disjoint_left.1 hdisj (h₁.subset_root C₁ hC1_1 hx1) hx
          · exact Finset.disjoint_left.1 hdisj (h₁.subset_root C₂ hC2_1 hx2) hx
        · rcases Finset.mem_union.1 hu12 with h1 | h2
          · exact h1
          · exfalso
            obtain ⟨x, hx⟩ := h₁.nonempty_node C₁ hC1_1
            exact Finset.disjoint_left.1 hdisj (h₁.subset_root C₁ hC1_1 hx)
              (h₂.subset_root _ h2 (Finset.mem_union_left _ hx))
      exact hg₁ C₁ hC1_1 C₂ hC2_1 hd hc hu1
    · have huA : C₁ ∪ C₂ = A := by
        rcases Finset.mem_insert.1 hu with huA | hu12
        · exact huA
        · rcases Finset.mem_union.1 hu12 with h1 | h2
          · exfalso
            obtain ⟨x, hx⟩ := h₂.nonempty_node C₂ hC2_2
            exact Finset.disjoint_left.1 hdisj
              (h₁.subset_root _ h1 (Finset.mem_union_right _ hx)) (h₂.subset_root C₂ hC2_2 hx)
          · exfalso
            obtain ⟨x, hx⟩ := h₁.nonempty_node C₁ hC1_1
            exact Finset.disjoint_left.1 hdisj (h₁.subset_root C₁ hC1_1 hx)
              (h₂.subset_root _ h2 (Finset.mem_union_left _ hx))
      have hC1_eq : C₁ = A₁ := by
        apply Finset.Subset.antisymm (h₁.subset_root C₁ hC1_1)
        intro x hx
        have hxU : x ∈ C₁ ∪ C₂ := huA.symm ▸ hunion ▸ Finset.mem_union_left A₂ hx
        rcases Finset.mem_union.1 hxU with hx1 | hx2
        · exact hx1
        · exact (Finset.disjoint_left.1 hdisj hx (h₂.subset_root C₂ hC2_2 hx2)).elim
      have hC2_eq : C₂ = A₂ := by
        apply Finset.Subset.antisymm (h₂.subset_root C₂ hC2_2)
        intro x hx
        have hxU : x ∈ C₁ ∪ C₂ := huA.symm ▸ hunion ▸ Finset.mem_union_right A₁ hx
        rcases Finset.mem_union.1 hxU with hx1 | hx2
        · exact (Finset.disjoint_left.1 hdisj (h₁.subset_root C₁ hC1_1 hx1) hx).elim
        · exact hx2
      rw [hC1_eq, hC2_eq]; exact hsymp
    · have huA : C₁ ∪ C₂ = A := by
        rcases Finset.mem_insert.1 hu with huA | hu12
        · exact huA
        · rcases Finset.mem_union.1 hu12 with h1 | h2
          · exfalso
            obtain ⟨x, hx⟩ := h₂.nonempty_node C₁ hC1_2
            exact Finset.disjoint_left.1 hdisj
              (h₁.subset_root _ h1 (Finset.mem_union_left _ hx)) (h₂.subset_root C₁ hC1_2 hx)
          · exfalso
            obtain ⟨x, hx⟩ := h₁.nonempty_node C₂ hC2_1
            exact Finset.disjoint_left.1 hdisj (h₁.subset_root C₂ hC2_1 hx)
              (h₂.subset_root _ h2 (Finset.mem_union_right _ hx))
      have hC1_eq : C₁ = A₂ := by
        apply Finset.Subset.antisymm (h₂.subset_root C₁ hC1_2)
        intro x hx
        have hxU : x ∈ C₁ ∪ C₂ := huA.symm ▸ hunion ▸ Finset.mem_union_right A₁ hx
        rcases Finset.mem_union.1 hxU with hx1 | hx2
        · exact hx1
        · exact (Finset.disjoint_left.1 hdisj (h₁.subset_root C₂ hC2_1 hx2) hx).elim
      have hC2_eq : C₂ = A₁ := by
        apply Finset.Subset.antisymm (h₁.subset_root C₂ hC2_1)
        intro x hx
        have hxU : x ∈ C₁ ∪ C₂ := huA.symm ▸ hunion ▸ Finset.mem_union_left A₂ hx
        rcases Finset.mem_union.1 hxU with hx1 | hx2
        · exact (Finset.disjoint_left.1 hdisj hx (h₂.subset_root C₁ hC1_2 hx1)).elim
        · exact hx2
      rw [hC1_eq, hC2_eq, symp_symm]; exact hsymp
    · have hu2 : C₁ ∪ C₂ ∈ N₂ := by
        rcases Finset.mem_insert.1 hu with huA | hu12
        · exfalso
          obtain ⟨x, hx⟩ := h₁.nonempty_node A₁ h₁.mem_self
          have hxA : x ∈ A := hunion ▸ Finset.mem_union_left A₂ hx
          rw [← huA] at hxA
          rcases Finset.mem_union.1 hxA with hx1 | hx2
          · exact Finset.disjoint_left.1 hdisj hx (h₂.subset_root C₁ hC1_2 hx1)
          · exact Finset.disjoint_left.1 hdisj hx (h₂.subset_root C₂ hC2_2 hx2)
        · rcases Finset.mem_union.1 hu12 with h1 | h2
          · exfalso
            obtain ⟨x, hx⟩ := h₂.nonempty_node C₁ hC1_2
            exact Finset.disjoint_left.1 hdisj
              (h₁.subset_root _ h1 (Finset.mem_union_left _ hx)) (h₂.subset_root C₁ hC1_2 hx)
          · exact h2
      exact hg₂ C₁ hC1_2 C₂ hC2_2 hd hc hu2

/- ### 8. Splitting orderings (`List α`), `treeOfList`, Lemma 4.2, and Lemma 4.3 -/

lemma orderings_singleton {α : Type*} [DecidableEq α] (x : α) :
    orderings ({x} : Finset α) = {[x]} := by
  ext w
  rw [mem_orderings, Finset.mem_singleton]
  constructor
  · rintro ⟨hnd, hfin⟩
    have hlen : w.length = 1 := by
      rw [← List.toFinset_card_of_nodup hnd, hfin, Finset.card_singleton]
    rcases List.length_eq_one_iff.1 hlen with ⟨a, rfl⟩
    have ha : a = x := by
      have : a ∈ ({x} : Finset α) := hfin ▸ List.mem_toFinset.2 (List.mem_singleton_self a)
      exact Finset.mem_singleton.1 this
    rw [ha]
  · rintro rfl
    exact ⟨List.nodup_singleton x, by simp⟩

lemma sum_orderings_split {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {A : Finset α} {a b : ℕ} (hcard : A.card = a + b) (f : List α → β) :
    ∑ w ∈ orderings A, f w =
      ∑ A₁ ∈ A.powersetCard a, ∑ w₁ ∈ orderings A₁, ∑ w₂ ∈ orderings (A \ A₁),
        f (w₁ ++ w₂) := by
  let S_rhs : Finset (Σ _A₁ : Finset α, List α × List α) :=
    (A.powersetCard a).sigma (fun A₁ => (orderings A₁) ×ˢ (orderings (A \ A₁)))
  have hrhs : ∑ p ∈ S_rhs, f (p.2.1 ++ p.2.2) =
      ∑ A₁ ∈ A.powersetCard a, ∑ w₁ ∈ orderings A₁, ∑ w₂ ∈ orderings (A \ A₁),
        f (w₁ ++ w₂) := by
    simp only [S_rhs, Finset.sum_sigma, Finset.sum_product]
  rw [← hrhs]
  refine Finset.sum_bij (fun w _ => ⟨(w.take a).toFinset, (w.take a, w.drop a)⟩) ?_ ?_ ?_ ?_
  · intro w hw
    rcases mem_orderings.1 hw with ⟨hnd, hfin⟩
    have hlen : w.length = a + b := (length_of_mem_orderings hw).trans hcard
    have hnd_app : (w.take a ++ w.drop a).Nodup := by rwa [List.take_append_drop]
    obtain ⟨hnd1, hnd2, hdisj_list⟩ := List.nodup_append.1 hnd_app
    have hdisj : Disjoint (w.take a).toFinset (w.drop a).toFinset :=
      Finset.disjoint_left.2 fun x hx1 hx2 =>
        hdisj_list x (List.mem_toFinset.1 hx1) x (List.mem_toFinset.1 hx2) rfl
    have hunion : (w.take a).toFinset ∪ (w.drop a).toFinset = A := by
      rw [← List.toFinset_append, List.take_append_drop, hfin]
    have hsub1 : (w.take a).toFinset ⊆ A := hunion ▸ Finset.subset_union_left
    have hcard1 : (w.take a).toFinset.card = a := by
      rw [List.toFinset_card_of_nodup hnd1, List.length_take, hlen]
      omega
    have hdrop_eq : (w.drop a).toFinset = A \ (w.take a).toFinset := by
      rw [← hunion, Finset.union_sdiff_cancel_left hdisj]
    simp only [S_rhs, Finset.mem_sigma, Finset.mem_product, Finset.mem_powersetCard]
    exact ⟨⟨hsub1, hcard1⟩, mem_orderings.2 ⟨hnd1, rfl⟩, mem_orderings.2 ⟨hnd2, hdrop_eq⟩⟩
  · intro w₁ _ w₂ _ h
    have hp : (w₁.take a, w₁.drop a) = (w₂.take a, w₂.drop a) :=
      congrArg (fun p : Σ _A₁ : Finset α, List α × List α => p.2) h
    obtain ⟨ht, hd⟩ := Prod.mk.inj hp
    rw [← List.take_append_drop a w₁, ← List.take_append_drop a w₂, ht, hd]
  · intro p hp
    rcases p with ⟨A₁, ⟨u, v⟩⟩
    simp only [S_rhs, Finset.mem_sigma, Finset.mem_product, Finset.mem_powersetCard] at hp
    obtain ⟨⟨hA₁sub, hA₁card⟩, hu, hv⟩ := hp
    rcases mem_orderings.1 hu with ⟨hund, hufin⟩
    rcases mem_orderings.1 hv with ⟨hvnd, hvfin⟩
    have hulen : u.length = a := (length_of_mem_orderings hu).trans hA₁card
    have hnd_uv : (u ++ v).Nodup := by
      refine List.nodup_append.2 ⟨hund, hvnd, fun x hx y hy hxy => ?_⟩
      subst hxy
      have hx1 : x ∈ A₁ := hufin ▸ List.mem_toFinset.2 hx
      have hx2 : x ∈ A \ A₁ := hvfin ▸ List.mem_toFinset.2 hy
      exact (Finset.mem_sdiff.1 hx2).2 hx1
    have hfin_uv : (u ++ v).toFinset = A := by
      rw [List.toFinset_append, hufin, hvfin, Finset.union_sdiff_of_subset hA₁sub]
    refine ⟨u ++ v, mem_orderings.2 ⟨hnd_uv, hfin_uv⟩, ?_⟩
    simp [List.take_left' hulen, List.drop_left' hulen, hufin]
  · intro w _
    rw [List.take_append_drop]

lemma card_orderings {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) (S : Finset α), S.card = n → (orderings S).card = n.factorial
  | 0, S, hS => by
    rw [Finset.card_eq_zero.1 hS]
    have hemp : orderings (∅ : Finset α) = {[]} := by
      ext w
      rw [mem_orderings, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hfin⟩
        cases w with
        | nil => rfl
        | cons x xs =>
          have : x ∈ (∅ : Finset α) := hfin ▸ List.mem_toFinset.2 (List.mem_cons_self ..)
          exact (Finset.notMem_empty x this).elim
      · rintro rfl; simp
    rw [hemp, Finset.card_singleton]; rfl
  | n + 1, S, hS => by
    have hsplit := sum_orderings_split (a := 1) (b := n) (by omega : S.card = 1 + n)
      (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsplit
    rw [hsplit]
    have hterm : ∀ A₁ ∈ S.powersetCard 1,
        (orderings A₁).card * (orderings (S \ A₁)).card = n.factorial := by
      intro A₁ hA₁
      obtain ⟨hsub, hcard1⟩ := Finset.mem_powersetCard.1 hA₁
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hcard1
      rw [orderings_singleton, Finset.card_singleton, one_mul]
      exact card_orderings n (S \ {x}) (by rw [Finset.card_sdiff_of_subset hsub, hS, Finset.card_singleton]; omega)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, hS,
      Nat.choose_one_right, smul_eq_mul, Nat.factorial_succ]

def treeOfList {α : Type*} [DecidableEq α] : ℕ → List α → Finset (Finset α)
  | 0, w => {w.toFinset}
  | k + 1, w => insert w.toFinset
      (treeOfList k (w.take (2 ^ k)) ∪ treeOfList k (w.drop (2 ^ k)))

lemma treeOfList_append {α : Type*} [DecidableEq α] {k : ℕ} {w₁ w₂ : List α}
    (hlen : w₁.length = 2 ^ k) :
    treeOfList (k + 1) (w₁ ++ w₂) =
      insert (w₁.toFinset ∪ w₂.toFinset) (treeOfList k w₁ ∪ treeOfList k w₂) := by
  simp [treeOfList, List.take_left' hlen, List.drop_left' hlen, List.toFinset_append]

lemma treeOfList_isTree {α : Type*} [DecidableEq α] :
    ∀ (k : ℕ) {A : Finset α} {w : List α},
      w ∈ orderings A → A.card = 2 ^ k → IsTree k A (treeOfList k w)
  | 0, A, w, hw, hA => by
    rcases mem_orderings.1 hw with ⟨_, hfin⟩
    exact ⟨hA, by simp [treeOfList, hfin]⟩
  | k + 1, A, w, hw, hA => by
    rcases mem_orderings.1 hw with ⟨hnd, hfin⟩
    have hlen : w.length = 2 ^ k + 2 ^ k := by
      rw [length_of_mem_orderings hw, hA]; ring
    have hnd_app : (w.take (2 ^ k) ++ w.drop (2 ^ k)).Nodup := by rwa [List.take_append_drop]
    obtain ⟨hnd1, hnd2, hdisj_list⟩ := List.nodup_append.1 hnd_app
    have hdisj : Disjoint (w.take (2 ^ k)).toFinset (w.drop (2 ^ k)).toFinset :=
      Finset.disjoint_left.2 fun x hx1 hx2 =>
        hdisj_list x (List.mem_toFinset.1 hx1) x (List.mem_toFinset.1 hx2) rfl
    have hunion : (w.take (2 ^ k)).toFinset ∪ (w.drop (2 ^ k)).toFinset = A := by
      rw [← List.toFinset_append, List.take_append_drop, hfin]
    have hcard1 : (w.take (2 ^ k)).toFinset.card = 2 ^ k := by
      rw [List.toFinset_card_of_nodup hnd1, List.length_take, hlen]; omega
    have hcard2 : (w.drop (2 ^ k)).toFinset.card = 2 ^ k := by
      rw [List.toFinset_card_of_nodup hnd2, List.length_drop, hlen]; omega
    refine ⟨(w.take (2 ^ k)).toFinset, (w.drop (2 ^ k)).toFinset,
      treeOfList k (w.take (2 ^ k)), treeOfList k (w.drop (2 ^ k)),
      hdisj, hunion,
      treeOfList_isTree k (mem_orderings.2 ⟨hnd1, rfl⟩) hcard1,
      treeOfList_isTree k (mem_orderings.2 ⟨hnd2, rfl⟩) hcard2, ?_⟩
    simp [treeOfList, hfin]

lemma sum_inducing_tree_succ {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    {k : ℕ} {A A₁ A₂ : Finset α} {N₁ N₂ : Finset (Finset α)}
    (hdisj : Disjoint A₁ A₂) (hunion : A₁ ∪ A₂ = A)
    (h₁ : IsTree k A₁ N₁) (h₂ : IsTree k A₂ N₂) (f : List α → β) :
    ∑ w ∈ orderings A, (if treeOfList (k + 1) w = insert A (N₁ ∪ N₂) then f w else 0) =
      (∑ w₁ ∈ orderings A₁, ∑ w₂ ∈ orderings A₂,
        if treeOfList k w₁ = N₁ ∧ treeOfList k w₂ = N₂ then f (w₁ ++ w₂) else 0) +
      (∑ w₁ ∈ orderings A₂, ∑ w₂ ∈ orderings A₁,
        if treeOfList k w₁ = N₂ ∧ treeOfList k w₂ = N₁ then f (w₁ ++ w₂) else 0) := by
  have hAcard : A.card = 2 ^ k + 2 ^ k := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, h₁.card, h₂.card]
  rw [sum_orderings_split hAcard]
  have hA₁mem : A₁ ∈ A.powersetCard (2 ^ k) :=
    Finset.mem_powersetCard.2 ⟨hunion ▸ Finset.subset_union_left, h₁.card⟩
  have hA₂mem : A₂ ∈ A.powersetCard (2 ^ k) :=
    Finset.mem_powersetCard.2 ⟨hunion ▸ Finset.subset_union_right, h₂.card⟩
  have hA₁neA₂ : A₁ ≠ A₂ := by
    intro heq
    obtain ⟨x, hx⟩ := h₁.nonempty_node A₁ h₁.mem_self
    exact Finset.disjoint_left.1 hdisj hx (heq ▸ hx)
  have hzero_other : ∀ X ∈ A.powersetCard (2 ^ k), X ≠ A₁ → X ≠ A₂ →
      (∑ w₁ ∈ orderings X, ∑ w₂ ∈ orderings (A \ X),
        if treeOfList (k + 1) (w₁ ++ w₂) = insert A (N₁ ∪ N₂) then f (w₁ ++ w₂) else 0) = 0 := by
    intro X hX hX1 hX2
    obtain ⟨hXsub, hXcard⟩ := Finset.mem_powersetCard.1 hX
    have hXc2 : (A \ X).card = 2 ^ k := by
      rw [Finset.card_sdiff_of_subset hXsub, hAcard, hXcard]; omega
    apply Finset.sum_eq_zero; intro w₁ hw₁
    apply Finset.sum_eq_zero; intro w₂ hw₂
    have hlen1 : w₁.length = 2 ^ k := (length_of_mem_orderings hw₁).trans hXcard
    have hfin1 : w₁.toFinset = X := (mem_orderings.1 hw₁).2
    have hfin2 : w₂.toFinset = A \ X := (mem_orderings.1 hw₂).2
    rw [treeOfList_append hlen1, hfin1, hfin2, Finset.union_sdiff_of_subset hXsub, if_neg]
    intro heq
    have huniq := IsTree.children_unique
      Finset.disjoint_sdiff (Finset.union_sdiff_of_subset hXsub)
      (treeOfList_isTree k hw₁ hXcard) (treeOfList_isTree k hw₂ hXc2)
      hdisj hunion h₁ h₂ heq
    rcases huniq with ⟨h1, -, -, -⟩ | ⟨h1, -, -, -⟩
    · exact hX1 h1
    · exact hX2 h1
  rw [Finset.sum_eq_add A₁ A₂ hA₁neA₂ (fun X hX ⟨hX1, hX2⟩ => hzero_other X hX hX1 hX2)
    (fun h => (h hA₁mem).elim) (fun h => (h hA₂mem).elim)]
  have hsdiff1 : A \ A₁ = A₂ := by rw [← hunion, Finset.union_sdiff_cancel_left hdisj]
  have hsdiff2 : A \ A₂ = A₁ := by rw [← hunion, Finset.union_sdiff_cancel_right hdisj]
  rw [hsdiff1, hsdiff2]
  congr 1
  · apply Finset.sum_congr rfl; intro w₁ hw₁
    apply Finset.sum_congr rfl; intro w₂ hw₂
    have hlen1 : w₁.length = 2 ^ k := (length_of_mem_orderings hw₁).trans h₁.card
    have hfin1 : w₁.toFinset = A₁ := (mem_orderings.1 hw₁).2
    have hfin2 : w₂.toFinset = A₂ := (mem_orderings.1 hw₂).2
    rw [treeOfList_append hlen1, hfin1, hfin2, hunion]
    have hiff : insert A (treeOfList k w₁ ∪ treeOfList k w₂) = insert A (N₁ ∪ N₂) ↔
        treeOfList k w₁ = N₁ ∧ treeOfList k w₂ = N₂ := by
      constructor
      · intro heq
        have huniq := IsTree.children_unique hdisj hunion
          (treeOfList_isTree k hw₁ h₁.card) (treeOfList_isTree k hw₂ h₂.card)
          hdisj hunion h₁ h₂ heq
        rcases huniq with ⟨-, -, hN1, hN2⟩ | ⟨h12, -, -, -⟩
        · exact ⟨hN1, hN2⟩
        · exact (hA₁neA₂ h12).elim
      · rintro ⟨h1, h2⟩; rw [h1, h2]
    simp only [hiff]
  · apply Finset.sum_congr rfl; intro w₁ hw₁
    apply Finset.sum_congr rfl; intro w₂ hw₂
    have hlen1 : w₁.length = 2 ^ k := (length_of_mem_orderings hw₁).trans h₂.card
    have hfin1 : w₁.toFinset = A₂ := (mem_orderings.1 hw₁).2
    have hfin2 : w₂.toFinset = A₁ := (mem_orderings.1 hw₂).2
    rw [treeOfList_append hlen1, hfin1, hfin2, Finset.union_comm, hunion]
    have hiff : insert A (treeOfList k w₁ ∪ treeOfList k w₂) = insert A (N₁ ∪ N₂) ↔
        treeOfList k w₁ = N₂ ∧ treeOfList k w₂ = N₁ := by
      constructor
      · intro heq
        have huniq := IsTree.children_unique hdisj.symm (by rw [Finset.union_comm, hunion])
          (treeOfList_isTree k hw₁ h₂.card) (treeOfList_isTree k hw₂ h₁.card)
          hdisj hunion h₁ h₂ heq
        rcases huniq with ⟨h21, -, -, -⟩ | ⟨-, -, hN1, hN2⟩
        · exact (hA₁neA₂ h21.symm).elim
        · exact ⟨hN1, hN2⟩
      · rintro ⟨h1, h2⟩; rw [h1, h2, Finset.union_comm]
    simp only [hiff]

/-- Lemma 4.2(a): Every tree on `A` (`|A| = 2^k`) is induced by exactly `2^(2^k - 1)` orderings. -/
theorem lemma_4_2_fibers {α : Type*} [DecidableEq α] :
    ∀ (k : ℕ) {A : Finset α} {N : Finset (Finset α)}, IsTree k A N →
      ((orderings A).filter (fun w => treeOfList k w = N)).card = 2 ^ (2 ^ k - 1)
  | 0, A, N, h => by
    obtain ⟨hAcard, rfl⟩ := h
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hAcard
    rw [orderings_singleton]
    have hfilt : ({[x]} : Finset (List α)).filter (fun w => treeOfList 0 w = {{x}}) = {[x]} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
      rintro rfl
      simp [treeOfList]
    rw [hfilt, Finset.card_singleton]
    norm_num
  | k + 1, A, N, h => by
    obtain ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h₁, h₂, rfl⟩ := h
    have hcard_eq : ((orderings A).filter (fun w => treeOfList (k + 1) w = insert A (N₁ ∪ N₂))).card =
        ∑ w ∈ orderings A,
          if treeOfList (k + 1) w = insert A (N₁ ∪ N₂) then (1 : ℕ) else 0 := by
      rw [Finset.card_filter]
    rw [hcard_eq, sum_inducing_tree_succ hdisj hunion h₁ h₂ (fun _ => (1 : ℕ))]
    have hprod : ∀ {X₁ X₂ : Finset α} {M₁ M₂ : Finset (Finset α)},
        IsTree k X₁ M₁ → IsTree k X₂ M₂ →
        (∑ w₁ ∈ orderings X₁, ∑ w₂ ∈ orderings X₂,
          if treeOfList k w₁ = M₁ ∧ treeOfList k w₂ = M₂ then (1 : ℕ) else 0) =
          2 ^ (2 ^ k - 1) * 2 ^ (2 ^ k - 1) := by
      intro X₁ X₂ M₁ M₂ hX₁ hX₂
      have hite : ∀ (w₁ w₂ : List α),
          (if treeOfList k w₁ = M₁ ∧ treeOfList k w₂ = M₂ then (1 : ℕ) else 0) =
            (if treeOfList k w₁ = M₁ then 1 else 0) * (if treeOfList k w₂ = M₂ then 1 else 0) := by
        intro w₁ w₂; split_ifs <;> simp_all
      simp_rw [hite, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.card_filter]
      rw [lemma_4_2_fibers k hX₁, lemma_4_2_fibers k hX₂]
    rw [hprod h₁ h₂, hprod h₂ h₁]
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hexp : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + (2 ^ k - 1) + 1 := by
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      omega
    rw [hexp, pow_succ, pow_add]
    ring

/-- Lemma 4.2(b): `(treesOn k A).card * 2^(2^k - 1) = (2^k)!`. -/
theorem lemma_4_2_card {α : Type*} [DecidableEq α] (k : ℕ) {A : Finset α}
    (hA : A.card = 2 ^ k) :
    (treesOn k A).card * 2 ^ (2 ^ k - 1) = (2 ^ k).factorial := by
  have hmaps : ∀ w ∈ orderings A, treeOfList k w ∈ treesOn k A :=
    fun w hw => mem_treesOn.2 (treeOfList_isTree k hw hA)
  have hpart := Finset.card_eq_sum_card_fiberwise hmaps
  rw [card_orderings (2 ^ k) A hA] at hpart
  have hconst : ∑ N ∈ treesOn k A,
      ((orderings A).filter (fun w => treeOfList k w = N)).card =
      (treesOn k A).card * 2 ^ (2 ^ k - 1) := by
    calc
      ∑ N ∈ treesOn k A, ((orderings A).filter (fun w => treeOfList k w = N)).card
        = ∑ _N ∈ treesOn k A, 2 ^ (2 ^ k - 1) :=
            Finset.sum_congr rfl (fun N hN => lemma_4_2_fibers k (mem_treesOn.1 hN))
      _ = (treesOn k A).card * 2 ^ (2 ^ k - 1) := by simp
  rw [← hconst, ← hpart]

/-- Sum of `BWord` over all orderings of `A` inducing the tree `N`. -/
noncomputable def treeSum {s : ℕ} {ι : Type*} [DecidableEq ι] (hs : 1 ≤ s)
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (k : ℕ) (A : Finset ι)
    (N : Finset (Finset ι)) : Matrix (𝔽₂ s) (𝔽₂ s) ℚ :=
  ∑ w ∈ orderings A, if treeOfList k w = N then BWord hs d hd w else 0

/-- Lemma 4.3: For a tree `N` on `A` (`|A| = 2^k`):
- if `N` is good, every ordering `w` inducing `N` gives the same signed translation `B_N` of class
  `bSum (bClass hs d hd) A`, and `treeSum hs d hd k A N = (2 : ℚ)^(2^k - 1) • B_N`;
- if `N` is not good, `treeSum hs d hd k A N = 0`. -/
theorem lemma_4_3 {s : ℕ} {ι : Type*} [DecidableEq ι] (hs : 1 ≤ s)
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) :
    ∀ (k : ℕ) {A : Finset ι} {N : Finset (Finset ι)}, IsTree k A N →
      (IsGoodTree (bClass hs d hd) N → ∃ B_N : Matrix (𝔽₂ s) (𝔽₂ s) ℚ,
        IsSignedTrans B_N (bSum (bClass hs d hd) A) ∧
        (∀ w ∈ orderings A, treeOfList k w = N → BWord hs d hd w = B_N) ∧
        treeSum hs d hd k A N = ((2 : ℚ) ^ (2 ^ k - 1)) • B_N) ∧
      (¬ IsGoodTree (bClass hs d hd) N → treeSum hs d hd k A N = 0)
  | 0, A, N, h => by
    obtain ⟨hAcard, rfl⟩ := h
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hAcard
    refine ⟨fun _ => ?_, fun hng => (hng (isGoodTree_zero _ (Finset.card_singleton x))).elim⟩
    refine ⟨BMat hs d hd x, ?_, ?_, ?_⟩
    · rw [bSum_singleton]; exact BMat_isSignedTrans hs d hd x
    · intro w hw _
      rw [orderings_singleton, Finset.mem_singleton] at hw
      rw [hw, BWord_singleton]
    · unfold treeSum
      rw [orderings_singleton, Finset.sum_singleton]
      have htr : treeOfList 0 [x] = {{x}} := by simp [treeOfList]
      simp [htr, BWord_singleton]
  | k + 1, A, N, h => by
    obtain ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h₁, h₂, rfl⟩ := h
    have ih₁ := lemma_4_3 hs d hd k h₁
    have ih₂ := lemma_4_3 hs d hd k h₂
    have hsplit : treeSum hs d hd (k + 1) A (insert A (N₁ ∪ N₂)) =
        treeSum hs d hd k A₁ N₁ * treeSum hs d hd k A₂ N₂ +
        treeSum hs d hd k A₂ N₂ * treeSum hs d hd k A₁ N₁ := by
      unfold treeSum
      rw [sum_inducing_tree_succ hdisj hunion h₁ h₂ (BWord hs d hd)]
      have hterm : ∀ {X₁ X₂ : Finset ι} {M₁ M₂ : Finset (Finset ι)},
          (∑ w₁ ∈ orderings X₁, ∑ w₂ ∈ orderings X₂,
            if treeOfList k w₁ = M₁ ∧ treeOfList k w₂ = M₂ then
              BWord hs d hd (w₁ ++ w₂)
            else 0) =
            (∑ w₁ ∈ orderings X₁, if treeOfList k w₁ = M₁ then BWord hs d hd w₁ else 0) *
            (∑ w₂ ∈ orderings X₂, if treeOfList k w₂ = M₂ then BWord hs d hd w₂ else 0) := by
        intro X₁ X₂ M₁ M₂
        have hstep : ∀ (w₁ w₂ : List ι),
            (if treeOfList k w₁ = M₁ ∧ treeOfList k w₂ = M₂ then
              BWord hs d hd (w₁ ++ w₂)
            else 0) =
            (if treeOfList k w₁ = M₁ then BWord hs d hd w₁ else 0) *
            (if treeOfList k w₂ = M₂ then BWord hs d hd w₂ else 0) := by
          intro w₁ w₂
          rw [BWord_append]
          split_ifs <;> simp_all
        simp_rw [hstep, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hterm, hterm]
    have hgood_iff := isGoodTree_succ_iff (bClass hs d hd) hdisj hunion h₁ h₂
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hexp : 2 ^ (k + 1) - 1 = (2 ^ k - 1) + (2 ^ k - 1) + 1 := by
      have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      omega
    constructor
    · intro hg
      obtain ⟨hg₁, hg₂, hsymp⟩ := hgood_iff.1 hg
      obtain ⟨B₁, hB₁st, hB₁ord, hB₁sum⟩ := ih₁.1 hg₁
      obtain ⟨B₂, hB₂st, hB₂ord, hB₂sum⟩ := ih₂.1 hg₂
      have hcomm : B₂ * B₁ = B₁ * B₂ := by
        rw [hB₂st.comm hB₁st, symp_symm, hsymp, sign2_zero, one_smul]
      refine ⟨B₁ * B₂, ?_, ?_, ?_⟩
      · rw [← hunion, bSum_union _ hdisj]
        exact hB₁st.mul hB₂st
      · intro w hw htr
        rcases mem_orderings.1 hw with ⟨hnd, hfin⟩
        have hAcard : A.card = 2 ^ k + 2 ^ k := by
          rw [← hunion, Finset.card_union_of_disjoint hdisj, h₁.card, h₂.card]
        have hlen : w.length = 2 ^ k + 2 ^ k := (length_of_mem_orderings hw).trans hAcard
        have hnd_app : (w.take (2 ^ k) ++ w.drop (2 ^ k)).Nodup := by rwa [List.take_append_drop]
        obtain ⟨hnd1, hnd2, hdisj_l⟩ := List.nodup_append.1 hnd_app
        have hdisj_w : Disjoint (w.take (2 ^ k)).toFinset (w.drop (2 ^ k)).toFinset :=
          Finset.disjoint_left.2 fun x hx1 hx2 =>
            hdisj_l x (List.mem_toFinset.1 hx1) x (List.mem_toFinset.1 hx2) rfl
        have hunion_w : (w.take (2 ^ k)).toFinset ∪ (w.drop (2 ^ k)).toFinset = A := by
          rw [← List.toFinset_append, List.take_append_drop, hfin]
        have hcard1 : (w.take (2 ^ k)).toFinset.card = 2 ^ k := by
          rw [List.toFinset_card_of_nodup hnd1, List.length_take, hlen]; omega
        have hcard2 : (w.drop (2 ^ k)).toFinset.card = 2 ^ k := by
          rw [List.toFinset_card_of_nodup hnd2, List.length_drop, hlen]; omega
        have hw1 : w.take (2 ^ k) ∈ orderings (w.take (2 ^ k)).toFinset :=
          mem_orderings.2 ⟨hnd1, rfl⟩
        have hw2 : w.drop (2 ^ k) ∈ orderings (w.drop (2 ^ k)).toFinset :=
          mem_orderings.2 ⟨hnd2, rfl⟩
        have htr' : insert A (treeOfList k (w.take (2 ^ k)) ∪ treeOfList k (w.drop (2 ^ k))) =
            insert A (N₁ ∪ N₂) := by simpa [treeOfList, hfin] using htr
        have huniq := IsTree.children_unique hdisj_w hunion_w
          (treeOfList_isTree k hw1 hcard1) (treeOfList_isTree k hw2 hcard2)
          hdisj hunion h₁ h₂ htr'
        have hbw : BWord hs d hd w =
            BWord hs d hd (w.take (2 ^ k)) * BWord hs d hd (w.drop (2 ^ k)) := by
          rw [← BWord_append, List.take_append_drop]
        rw [hbw]
        rcases huniq with ⟨hX1, hX2, hM1, hM2⟩ | ⟨hX1, hX2, hM1, hM2⟩
        · rw [hB₁ord _ (hX1 ▸ hw1) hM1, hB₂ord _ (hX2 ▸ hw2) hM2]
        · rw [hB₂ord _ (hX1 ▸ hw1) hM1, hB₁ord _ (hX2 ▸ hw2) hM2, hcomm]
      · rw [hsplit, hB₁sum, hB₂sum, smul_mul_smul_comm, smul_mul_smul_comm, hcomm,
          ← add_smul, hexp, pow_succ, pow_add]
        congr 1; ring
    · intro hng
      rw [hsplit]
      by_cases hg₁ : IsGoodTree (bClass hs d hd) N₁
      · by_cases hg₂ : IsGoodTree (bClass hs d hd) N₂
        · have hsymp1 : symp (bSum (bClass hs d hd) A₁) (bSum (bClass hs d hd) A₂) = 1 := by
            have hne : symp (bSum (bClass hs d hd) A₁) (bSum (bClass hs d hd) A₂) ≠ 0 :=
              fun h0 => hng (hgood_iff.2 ⟨hg₁, hg₂, h0⟩)
            exact (zmod2_eq_zero_or_one _).resolve_left hne
          obtain ⟨B₁, hB₁st, -, hB₁sum⟩ := ih₁.1 hg₁
          obtain ⟨B₂, hB₂st, -, hB₂sum⟩ := ih₂.1 hg₂
          have hanti : B₂ * B₁ = -(B₁ * B₂) := by
            rw [hB₂st.comm hB₁st, symp_symm, hsymp1, sign2_one, neg_one_smul]
          rw [hB₁sum, hB₂sum, smul_mul_smul_comm, smul_mul_smul_comm, hanti, smul_neg,
            add_neg_cancel]
        · rw [ih₂.2 hg₂, mul_zero, zero_mul, add_zero]
      · rw [ih₁.2 hg₁, zero_mul, mul_zero, add_zero]

/-- Summing `BWord` over all orderings of `A` (`|A| = 2^k`) equals `2^(2^k - 1)` times the sum
over good trees on `A`. -/
lemma sum_BWord_pow_two {s : ℕ} {ι : Type*} [DecidableEq ι] (hs : 1 ≤ s)
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    (k : ℕ) {A : Finset ι} (hA : A.card = 2 ^ k) :
    ∃ B_of : Finset (Finset ι) → Matrix (𝔽₂ s) (𝔽₂ s) ℚ,
      (∀ N ∈ goodTreesOn (bClass hs d hd) k A,
        IsSignedTrans (B_of N) (bSum (bClass hs d hd) A)) ∧
      (∑ w ∈ orderings A, BWord hs d hd w) =
        ((2 : ℚ) ^ (2 ^ k - 1)) • ∑ N ∈ goodTreesOn (bClass hs d hd) k A, B_of N := by
  classical
  have hex : ∀ N ∈ goodTreesOn (bClass hs d hd) k A,
      ∃ M : Matrix (𝔽₂ s) (𝔽₂ s) ℚ,
        IsSignedTrans M (bSum (bClass hs d hd) A) ∧
        treeSum hs d hd k A N = ((2 : ℚ) ^ (2 ^ k - 1)) • M := by
    intro N hN
    have htr : IsTree k A N := mem_treesOn.1 (Finset.mem_filter.1 hN).1
    have hgd : IsGoodTree (bClass hs d hd) N := (Finset.mem_filter.1 hN).2
    obtain ⟨M, hMst, -, hMsum⟩ := (lemma_4_3 hs d hd k htr).1 hgd
    exact ⟨M, hMst, hMsum⟩
  let B_of : Finset (Finset ι) → Matrix (𝔽₂ s) (𝔽₂ s) ℚ :=
    fun N => if hN : N ∈ goodTreesOn (bClass hs d hd) k A then (hex N hN).choose else 0
  have hB_of : ∀ N ∈ goodTreesOn (bClass hs d hd) k A,
      IsSignedTrans (B_of N) (bSum (bClass hs d hd) A) ∧
      treeSum hs d hd k A N = ((2 : ℚ) ^ (2 ^ k - 1)) • B_of N := by
    intro N hN
    simp only [B_of, dif_pos hN]
    exact (hex N hN).choose_spec
  refine ⟨B_of, fun N hN => (hB_of N hN).1, ?_⟩
  have hpart : ∑ w ∈ orderings A, BWord hs d hd w =
      ∑ N ∈ treesOn k A, treeSum hs d hd k A N := by
    unfold treeSum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.sum_ite_eq, if_pos (mem_treesOn.2 (treeOfList_isTree k hw hA))]
  rw [hpart]
  have hfilt : ∑ N ∈ treesOn k A, treeSum hs d hd k A N =
      ∑ N ∈ goodTreesOn (bClass hs d hd) k A, treeSum hs d hd k A N := by
    unfold goodTreesOn
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro N hN
    split_ifs with hgd
    · rfl
    · exact (lemma_4_3 hs d hd k (mem_treesOn.1 hN)).2 hgd
  rw [hfilt, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun N hN => (hB_of N hN).2)

/- ### 9. Binary digit sum, Corollary 4.4, Proposition 2.7, and Proposition 4.5 -/

def popcount : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)

lemma popcount_zero : popcount 0 = 0 := by rw [popcount]

lemma popcount_pos_eq (n : ℕ) (hn : 0 < n) : popcount n = n % 2 + popcount (n / 2) := by
  cases n with
  | zero => omega
  | succ m => rw [popcount]

lemma popcount_one : popcount 1 = 1 := by
  rw [popcount_pos_eq 1 (by omega)]
  norm_num [popcount_zero]

lemma popcount_two_mul (n : ℕ) : popcount (2 * n) = popcount n := by
  cases n with
  | zero => simp [popcount_zero]
  | succ m =>
    rw [popcount_pos_eq (2 * (m + 1)) (by omega)]
    have h1 : 2 * (m + 1) % 2 = 0 := by omega
    have h2 : 2 * (m + 1) / 2 = m + 1 := by omega
    rw [h1, h2, zero_add]

lemma popcount_two_mul_add_one (n : ℕ) : popcount (2 * n + 1) = 1 + popcount n := by
  rw [popcount_pos_eq (2 * n + 1) (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]

lemma popcount_pow_two (a : ℕ) : popcount (2 ^ a) = 1 := by
  induction a with
  | zero => simpa using popcount_one
  | succ a ih =>
    rw [show 2 ^ (a + 1) = 2 * 2 ^ a by ring, popcount_two_mul, ih]

lemma popcount_pow_two_mul (v u : ℕ) : popcount (2 ^ v * u) = popcount u := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [show 2 ^ (v + 1) * u = 2 * (2 ^ v * u) by ring, popcount_two_mul, ih]

lemma popcount_pow_two_add : ∀ {a m : ℕ}, m < 2 ^ a → popcount (2 ^ a + m) = 1 + popcount m
  | 0, m, hm => by
    have : m = 0 := by omega
    subst this
    simp [popcount_zero, popcount_one]
  | a + 1, m, hm => by
    rcases Nat.even_or_odd m with ⟨q, hqeq⟩ | ⟨q, hqeq⟩
    · have hq' : m = 2 * q := by omega
      have hqlt : q < 2 ^ a := by
        have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
        omega
      rw [hq', show 2 ^ (a + 1) + 2 * q = 2 * (2 ^ a + q) by ring,
        popcount_two_mul, popcount_two_mul, popcount_pow_two_add hqlt]
    · have hqlt : q < 2 ^ a := by
        have : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
        omega
      rw [hqeq, show 2 ^ (a + 1) + (2 * q + 1) = 2 * (2 ^ a + q) + 1 by ring,
        popcount_two_mul_add_one, popcount_two_mul_add_one, popcount_pow_two_add hqlt]

lemma popcount_le_self (n : ℕ) : popcount n ≤ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [popcount_zero]
    | succ m =>
      rw [popcount_pos_eq (m + 1) (by omega)]
      have hlt : (m + 1) / 2 < m + 1 := by omega
      have := ih _ hlt
      omega

lemma popcount_le_of_lt_pow_two : ∀ {m n : ℕ}, n < 2 ^ m → popcount n ≤ m
  | 0, n, hn => by
    have : n = 0 := by omega
    subst this; simp [popcount_zero]
  | m + 1, n, hn => by
    cases n with
    | zero => simp [popcount_zero]
    | succ k =>
      rw [popcount_pos_eq (k + 1) (by omega)]
      have hdiv : (k + 1) / 2 < 2 ^ m := by
        have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        omega
      have h1 : (k + 1) % 2 ≤ 1 := by omega
      have h2 := popcount_le_of_lt_pow_two hdiv
      omega

lemma exists_odd_mul_pow_two (k : ℕ) (hk : 1 ≤ k) :
    ∃ v u : ℕ, Odd u ∧ k = 2 ^ v * u := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rcases Nat.even_or_odd k with ⟨q, hq⟩ | hodd
    · have hq1 : 1 ≤ q := by omega
      have hqlt : q < k := by omega
      obtain ⟨v, u, hu, hqu⟩ := ih q hqlt hq1
      refine ⟨v + 1, u, hu, ?_⟩
      rw [show 2 ^ (v + 1) * u = 2 * (2 ^ v * u) by ring, ← hqu]
      omega
    · exact ⟨0, k, hodd, by simp⟩

lemma popcount_add_val2_le {s k v u : ℕ} (hks : k < 2 ^ (s - 1))
    (hu : Odd u) (hk : k = 2 ^ v * u) : popcount k + v ≤ s - 1 := by
  have hu1 : 1 ≤ u := by obtain ⟨r, rfl⟩ := hu; omega
  have hvlt : v < s - 1 := by
    have hpow : 2 ^ v < 2 ^ (s - 1) := by
      calc
        2 ^ v = 2 ^ v * 1 := (mul_one _).symm
        _ ≤ 2 ^ v * u := Nat.mul_le_mul_left _ hu1
        _ = k := hk.symm
        _ < 2 ^ (s - 1) := hks
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hpow
  have hult : u < 2 ^ (s - 1 - v) := by
    have hmul : 2 ^ v * u < 2 ^ v * 2 ^ (s - 1 - v) := by
      rw [← pow_add, show v + (s - 1 - v) = s - 1 by omega, ← hk]
      exact hks
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hpop : popcount k = popcount u := by rw [hk, popcount_pow_two_mul]
  have hle := popcount_le_of_lt_pow_two hult
  omega

lemma trace_finset_sum {ι : Type*} {s : ℕ} (I : Finset ι)
    (f : ι → Matrix (𝔽₂ s) (𝔽₂ s) ℚ) :
    Matrix.trace (∑ i ∈ I, f i) = ∑ i ∈ I, Matrix.trace (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [Matrix.trace_zero]
  | insert a I ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.trace_add, ih]

/-- Integer multiple of `WMat κ.1 κ.2` (closed under sums and products). -/
def IsSignedTransSum {s : ℕ} (M : Matrix (𝔽₂ s) (𝔽₂ s) ℚ) (κ : 𝔽₂ s × 𝔽₂ s) : Prop :=
  ∃ z : ℤ, M = (z : ℚ) • WMat κ.1 κ.2

lemma IsSignedTransSum.zero {s : ℕ} (κ : 𝔽₂ s × 𝔽₂ s) : IsSignedTransSum 0 κ :=
  ⟨0, by simp⟩

lemma IsSignedTransSum.of_isSignedTrans {s : ℕ} {X : Matrix (𝔽₂ s) (𝔽₂ s) ℚ}
    {κ : 𝔽₂ s × 𝔽₂ s} (hX : IsSignedTrans X κ) : IsSignedTransSum X κ := by
  rcases hX with ⟨ε, rfl | rfl, rfl⟩
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩

lemma IsSignedTransSum.add {s : ℕ} {M₁ M₂ : Matrix (𝔽₂ s) (𝔽₂ s) ℚ} {κ : 𝔽₂ s × 𝔽₂ s}
    (h₁ : IsSignedTransSum M₁ κ) (h₂ : IsSignedTransSum M₂ κ) :
    IsSignedTransSum (M₁ + M₂) κ := by
  obtain ⟨z₁, rfl⟩ := h₁
  obtain ⟨z₂, rfl⟩ := h₂
  exact ⟨z₁ + z₂, by push_cast; rw [add_smul]⟩

lemma IsSignedTransSum.sum {ι : Type*} {s : ℕ} {κ : 𝔽₂ s × 𝔽₂ s} (I : Finset ι)
    (f : ι → Matrix (𝔽₂ s) (𝔽₂ s) ℚ) (hf : ∀ i ∈ I, IsSignedTransSum (f i) κ) :
    IsSignedTransSum (∑ i ∈ I, f i) κ := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using IsSignedTransSum.zero κ
  | insert a I ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a I)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma IsSignedTransSum.mul {s : ℕ} {M₁ M₂ : Matrix (𝔽₂ s) (𝔽₂ s) ℚ} {κ₁ κ₂ : 𝔽₂ s × 𝔽₂ s}
    (h₁ : IsSignedTransSum M₁ κ₁) (h₂ : IsSignedTransSum M₂ κ₂) :
    IsSignedTransSum (M₁ * M₂) (κ₁ + κ₂) := by
  obtain ⟨z₁, rfl⟩ := h₁
  obtain ⟨z₂, rfl⟩ := h₂
  rw [smul_mul_smul_comm, WMat_mul, smul_smul]
  rcases sign2_eq_one_or_neg_one (dot2 κ₂.2 κ₁.1) with h | h
  · exact ⟨z₁ * z₂, by simp [h]⟩
  · exact ⟨-(z₁ * z₂), by simp [h]⟩

lemma IsSignedTransSum.trace_int {s : ℕ} {M : Matrix (𝔽₂ s) (𝔽₂ s) ℚ} {κ : 𝔽₂ s × 𝔽₂ s}
    (hM : IsSignedTransSum M κ) :
    ∃ z : ℤ, Matrix.trace M = (z : ℚ) * (2 : ℚ) ^ s := by
  obtain ⟨z₁, rfl⟩ := hM
  rw [Matrix.trace_smul, smul_eq_mul, trace_WMat]
  split_ifs
  · exact ⟨z₁, rfl⟩
  · exact ⟨0, by simp⟩

/-- Corollary 4.4 (matrix level): `∑ w ∈ orderings S, BWord hs d hd w = 2^(k - popcount k) • M`
for an integer multiple `M` of `WMat (bSum _ S).1 (bSum _ S).2`. -/
theorem cor_4_4_matrix {s : ℕ} {ι : Type*} [DecidableEq ι] (hs : 1 ≤ s)
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) :
    ∀ (k : ℕ) (S : Finset ι), 1 ≤ k → S.card = k →
      ∃ M : Matrix (𝔽₂ s) (𝔽₂ s) ℚ,
        IsSignedTransSum M (bSum (bClass hs d hd) S) ∧
        (∑ w ∈ orderings S, BWord hs d hd w) = ((2 : ℚ) ^ (k - popcount k)) • M := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro S hk1 hScard
    let a : ℕ := Nat.log 2 k
    have hpow_le : 2 ^ a ≤ k := Nat.pow_log_le_self 2 (by omega)
    have hlt_pow : k < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
    by_cases hpow_eq : k = 2 ^ a
    · obtain ⟨B_of, hB_of, hord⟩ := sum_BWord_pow_two hs d hd a (hScard.trans hpow_eq)
      refine ⟨∑ N ∈ goodTreesOn (bClass hs d hd) a S, B_of N,
        IsSignedTransSum.sum _ _ (fun N hN => IsSignedTransSum.of_isSignedTrans (hB_of N hN)), ?_⟩
      rw [hord, hpow_eq, popcount_pow_two]
    · set r : ℕ := k - 2 ^ a
      have hr1 : 1 ≤ r := by omega
      have hrlt : r < 2 ^ a := by
        have : 2 ^ (a + 1) = 2 ^ a + 2 ^ a := by ring
        omega
      have hrltk : r < k := by omega
      have hk_eq : k = 2 ^ a + r := by omega
      have hpop : popcount k = 1 + popcount r := by
        rw [hk_eq, popcount_pow_two_add hrlt]
      have hterm : ∀ S₁ ∈ S.powersetCard (2 ^ a),
          ∃ M : Matrix (𝔽₂ s) (𝔽₂ s) ℚ,
            IsSignedTransSum M (bSum (bClass hs d hd) S) ∧
            (∑ w₁ ∈ orderings S₁, BWord hs d hd w₁) *
              (∑ w₂ ∈ orderings (S \ S₁), BWord hs d hd w₂) =
              ((2 : ℚ) ^ (k - popcount k)) • M := by
        intro S₁ hS₁
        obtain ⟨hS₁sub, hS₁card⟩ := Finset.mem_powersetCard.1 hS₁
        have hS₂card : (S \ S₁).card = r := by
          rw [Finset.card_sdiff_of_subset hS₁sub, hScard, hS₁card]
        obtain ⟨B_of, hB_of, hord₁⟩ := sum_BWord_pow_two hs d hd a hS₁card
        obtain ⟨M₂, hM₂, hord₂⟩ := ih r hrltk (S \ S₁) hr1 hS₂card
        let M₁ := ∑ N ∈ goodTreesOn (bClass hs d hd) a S₁, B_of N
        have hM₁ : IsSignedTransSum M₁ (bSum (bClass hs d hd) S₁) :=
          IsSignedTransSum.sum _ _ (fun N hN => IsSignedTransSum.of_isSignedTrans (hB_of N hN))
        refine ⟨M₁ * M₂, ?_, ?_⟩
        · have hbs : bSum (bClass hs d hd) S =
              bSum (bClass hs d hd) S₁ + bSum (bClass hs d hd) (S \ S₁) := by
            rw [← bSum_union _ Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hS₁sub]
          rw [hbs]
          exact hM₁.mul hM₂
        · rw [hord₁, hord₂, smul_mul_smul_comm, ← pow_add]
          have hpopr : popcount r ≤ r := popcount_le_self r
          have hpow1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
          have hexp : (2 ^ a - 1) + (r - popcount r) = k - popcount k := by omega
          rw [hexp]
      let M_of : Finset ι → Matrix (𝔽₂ s) (𝔽₂ s) ℚ :=
        fun S₁ => if hS₁ : S₁ ∈ S.powersetCard (2 ^ a) then (hterm S₁ hS₁).choose else 0
      have hM_of : ∀ S₁ ∈ S.powersetCard (2 ^ a),
          IsSignedTransSum (M_of S₁) (bSum (bClass hs d hd) S) ∧
          (∑ w₁ ∈ orderings S₁, BWord hs d hd w₁) *
            (∑ w₂ ∈ orderings (S \ S₁), BWord hs d hd w₂) =
            ((2 : ℚ) ^ (k - popcount k)) • M_of S₁ := by
        intro S₁ hS₁
        simp only [M_of, dif_pos hS₁]
        exact (hterm S₁ hS₁).choose_spec
      refine ⟨∑ S₁ ∈ S.powersetCard (2 ^ a), M_of S₁,
        IsSignedTransSum.sum _ _ (fun S₁ hS₁ => (hM_of S₁ hS₁).1), ?_⟩
      rw [sum_orderings_split (hScard.trans hk_eq), Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro S₁ hS₁
      simp_rw [BWord_append, ← Finset.mul_sum, ← Finset.sum_mul]
      exact (hM_of S₁ hS₁).2

/-- Corollary 4.4 (trace form): `∑ w ∈ orderings S, trace (BWord hs d hd w) = 2^(|S| - s₂(|S|) + s) * c`
for some integer `c : ℤ`. -/
theorem cor_4_4_trace {s : ℕ} {ι : Type*} [DecidableEq ι] (hs : 1 ≤ s)
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    {S : Finset ι} (hS : S.Nonempty) :
    ∃ c : ℤ, (∑ w ∈ orderings S, Matrix.trace (BWord hs d hd w)) =
      (2 : ℚ) ^ (S.card - popcount S.card + s) * (c : ℚ) := by
  obtain ⟨M, hM, hord⟩ := cor_4_4_matrix hs d hd S.card S (Finset.card_pos.2 hS) rfl
  obtain ⟨c, htr⟩ := hM.trace_int
  refine ⟨c, ?_⟩
  rw [← trace_finset_sum, hord, Matrix.trace_smul, smul_eq_mul, htr, pow_add]
  ring

/-- Proposition 2.7: For every nonempty proper subset `S` (`1 ≤ |S| < 2^(s - 1)`),
`Val2Ge S.card (Lcoeff hs d hd S)`. -/
theorem prop_2_7 {s : ℕ} {ι : Type*} [DecidableEq ι] (hs : 1 ≤ s)
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    {S : Finset ι} (hk1 : 1 ≤ S.card) (hks : S.card < 2 ^ (s - 1)) :
    Val2Ge S.card (Lcoeff hs d hd S) := by
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  set k := S.card
  obtain ⟨c, htr⟩ := cor_4_4_trace hs d hd hSne
  obtain ⟨v, u, hu, hku⟩ := exists_odd_mul_pow_two k hk1
  have hle := popcount_add_val2_le hks hu hku
  have hpopk : popcount k ≤ k := popcount_le_self k
  set e : ℕ := (k - popcount k + s) - (k + (v + 1))
  have hexp : k - popcount k + s = k + (v + 1) + e := by omega
  have hu_ne : (u : ℚ) ≠ 0 := by exact_mod_cast hu.pos.ne'
  have h2_ne : (2 : ℚ) ^ (v + 1) ≠ 0 := by positivity
  refine ⟨(-1 : ℤ) ^ (k - 1) * c * (2 : ℤ) ^ e, u, hu, ?_⟩
  unfold Lcoeff
  rw [htr]
  change ((-1 : ℚ) ^ (k - 1) / (2 * (k : ℚ))) * ((2 : ℚ) ^ (k - popcount k + s) * (c : ℚ)) = _
  rw [hexp]
  have hpow : (2 : ℚ) ^ (k + (v + 1) + e) = (2 : ℚ) ^ k * (2 : ℚ) ^ (v + 1) * (2 : ℚ) ^ e := by
    rw [pow_add, pow_add]
  rw [hpow, hku]
  push_cast
  have hden : 2 * ((2 : ℚ) ^ v * (u : ℚ)) = (2 : ℚ) ^ (v + 1) * (u : ℚ) := by
    rw [pow_succ]; ring
  rw [hden]
  field_simp [h2_ne, hu_ne]

/-- Proposition 4.5: For `S` of size `M = 2^(s - 1)` (`s ≥ 2`), if `bSum (bClass _ d hd) S = (0, 0)`
and `Odd (goodTreesOn (bClass _ d hd) (s - 1) S).card`, then `Val2Eq (2^(s - 1) - 1) (Lcoeff _ d hd S)`. -/
theorem prop_4_5 {s : ℕ} {ι : Type*} [DecidableEq ι] (hs : 2 ≤ s)
    (d : ι → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    {S : Finset ι} (hScard : S.card = 2 ^ (s - 1))
    (hbzero : bSum (bClass (by omega) d hd) S = (0, 0))
    (hodd : Odd (goodTreesOn (bClass (by omega) d hd) (s - 1) S).card) :
    Val2Eq (2 ^ (s - 1) - 1) (Lcoeff (by omega) d hd S) := by
  classical
  have hs1 : 1 ≤ s := by omega
  obtain ⟨B_of, hB_of, hord⟩ := sum_BWord_pow_two hs1 d hd (s - 1) hScard
  have htr_each : ∀ N ∈ goodTreesOn (bClass hs1 d hd) (s - 1) S,
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Matrix.trace (B_of N) = (ε : ℚ) * (2 : ℚ) ^ s := by
    intro N hN
    obtain ⟨εq, hεq, htr⟩ := trace_of_isSignedTrans (hbzero ▸ hB_of N hN)
    simp only [↓reduceIte] at htr
    rcases hεq with rfl | rfl
    · exact ⟨1, Or.inl rfl, by simpa using htr⟩
    · exact ⟨-1, Or.inr rfl, by simpa using htr⟩
  let eps : Finset (Finset ι) → ℤ :=
    fun N => if hN : N ∈ goodTreesOn (bClass hs1 d hd) (s - 1) S then (htr_each N hN).choose else 1
  have heps : ∀ N ∈ goodTreesOn (bClass hs1 d hd) (s - 1) S,
      (eps N = 1 ∨ eps N = -1) ∧ Matrix.trace (B_of N) = (eps N : ℚ) * (2 : ℚ) ^ s := by
    intro N hN
    simp only [eps, dif_pos hN]
    exact (htr_each N hN).choose_spec
  let tot : ℤ := ∑ N ∈ goodTreesOn (bClass hs1 d hd) (s - 1) S, eps N
  have htr_tot : (∑ w ∈ orderings S, Matrix.trace (BWord hs1 d hd w)) =
      (2 : ℚ) ^ (2 ^ (s - 1) - 1) * (2 : ℚ) ^ s * (tot : ℚ) := by
    rw [← trace_finset_sum, hord, Matrix.trace_smul, smul_eq_mul, trace_finset_sum]
    have hsum : ∑ N ∈ goodTreesOn (bClass hs1 d hd) (s - 1) S, Matrix.trace (B_of N) =
        (2 : ℚ) ^ s * (tot : ℚ) := by
      calc
        ∑ N ∈ goodTreesOn (bClass hs1 d hd) (s - 1) S, Matrix.trace (B_of N)
          = ∑ N ∈ goodTreesOn (bClass hs1 d hd) (s - 1) S, (eps N : ℚ) * (2 : ℚ) ^ s :=
              Finset.sum_congr rfl (fun N hN => (heps N hN).2)
        _ = (∑ N ∈ goodTreesOn (bClass hs1 d hd) (s - 1) S, (eps N : ℚ)) * (2 : ℚ) ^ s :=
              (Finset.sum_mul _ _ _).symm
        _ = (2 : ℚ) ^ s * (tot : ℚ) := by
              rw [mul_comm]; congr 1; simp [tot]
    rw [hsum]; ring
  have htot_odd : Odd tot := by
    have hmod : ∀ N ∈ goodTreesOn (bClass hs1 d hd) (s - 1) S, eps N % 2 = 1 := by
      intro N hN
      rcases (heps N hN).1 with h1 | h1 <;> rw [h1] <;> norm_num
    have hsum_mod : tot % 2 = ((goodTreesOn (bClass hs1 d hd) (s - 1) S).card : ℤ) % 2 := by
      have hcon : ∀ G : Finset (Finset (Finset ι)),
          (∀ N ∈ G, eps N % 2 = 1) → (∑ N ∈ G, eps N) % 2 = (G.card : ℤ) % 2 := by
        intro G
        induction G using Finset.induction_on with
        | empty => intro _; simp
        | insert a G ha ih =>
          intro hG
          rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
          push_cast
          have h1 := hG a (Finset.mem_insert_self a G)
          have h2 := ih (fun N hN => hG N (Finset.mem_insert_of_mem hN))
          omega
      exact hcon (goodTreesOn (bClass hs1 d hd) (s - 1) S) hmod
    obtain ⟨k, hk⟩ := hodd
    have hcard_mod : ((goodTreesOn (bClass hs1 d hd) (s - 1) S).card : ℤ) % 2 = 1 := by
      rw [hk]; push_cast; omega
    have htot_mod : tot % 2 = 1 := hsum_mod.trans hcard_mod
    exact ⟨tot / 2, by omega⟩
  have hsign_odd : Odd ((-1 : ℤ) ^ (2 ^ (s - 1) - 1) * tot) := by
    have h1 : (-1 : ℤ) ^ (2 ^ (s - 1) - 1) = 1 ∨ (-1 : ℤ) ^ (2 ^ (s - 1) - 1) = -1 :=
      neg_one_pow_eq_or ℤ (2 ^ (s - 1) - 1)
    rcases h1 with h1 | h1
    · rw [h1, one_mul]; exact htot_odd
    · rw [h1, neg_one_mul]; exact htot_odd.neg
  have h2M : (2 : ℚ) * ((2 ^ (s - 1) : ℕ) : ℚ) = (2 : ℚ) ^ s := by
    push_cast
    rw [← pow_succ', show s - 1 + 1 = s by omega]
  have h2s_ne : (2 : ℚ) ^ s ≠ 0 := by positivity
  refine ⟨(-1 : ℤ) ^ (2 ^ (s - 1) - 1) * tot, 1, hsign_odd, odd_one, ?_⟩
  unfold Lcoeff
  rw [htr_tot, hScard, h2M]
  push_cast
  field_simp [h2s_ne]

/-- Exact bridge theorem #1 for assembly (`#262`): proper nonempty subsets have `Val2Ge S.card`. -/
theorem Lcoeff_proper_val2Ge {s : ℕ} (hs : 2 ≤ s)
    (d : Fin (2 ^ (s - 1)) → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    (S : Finset (Fin (2 ^ (s - 1)))) (hne : S.Nonempty) (hnu : S ≠ Finset.univ) :
    Val2Ge S.card (Lcoeff (by omega : 1 ≤ s) d hd S) := by
  have hk1 : 1 ≤ S.card := Finset.card_pos.2 hne
  have hks : S.card < 2 ^ (s - 1) := by
    have hlt : S.card < (Finset.univ : Finset (Fin (2 ^ (s - 1)))).card :=
      Finset.card_lt_card (Finset.ssubset_univ_iff.2 hnu)
    simpa using hlt
  exact prop_2_7 (by omega : 1 ≤ s) d hd hk1 hks

/-- Exact bridge theorem #2 for assembly (`#262`): full label set has `Val2Eq (2^(s - 1) - 1)`. -/
theorem Lcoeff_univ_val2Eq {s : ℕ} (hs : 2 ≤ s)
    (d : Fin (2 ^ (s - 1)) → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    (hsum : ∑ i, d i = 0) (heven : IsEvenBasis d hd)
    (hodd : Odd (goodTreesOn (bClass (by omega : 1 ≤ s) d hd) (s - 1) Finset.univ).card) :
    Val2Eq (2 ^ (s - 1) - 1) (Lcoeff (by omega : 1 ≤ s) d hd Finset.univ) := by
  have hScard : (Finset.univ : Finset (Fin (2 ^ (s - 1)))).card = 2 ^ (s - 1) := by simp
  have hcard_even : Even (Fintype.card (Fin (2 ^ (s - 1)))) := by
    rw [Fintype.card_fin]
    exact ⟨2 ^ (s - 2), by
      have h1 : s - 1 = (s - 2) + 1 := by omega
      rw [h1, pow_succ]; ring⟩
  have hbzero : bSum (bClass (by omega : 1 ≤ s) d hd) Finset.univ = (0, 0) :=
    bSum_univ_eq_zero (by omega : 1 ≤ s) hcard_even d hd hsum heven
  exact prop_4_5 hs d hd hScard hbzero hodd

end OMA.BGS
namespace OMA.BGS

namespace PartC

open Finset BigOperators

open scoped Classical

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

private lemma zmod2_nat_cast_eq_zero_iff (n : ℕ) : (n : ZMod 2) = 0 ↔ Even n := by
  rw [ZMod.natCast_eq_zero_iff, even_iff_two_dvd]

private lemma zmod2_nat_cast_eq_one_iff (n : ℕ) : (n : ZMod 2) = 1 ↔ Odd n := by
  constructor
  · intro h
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have h0 : (n : ZMod 2) = 0 := (zmod2_nat_cast_eq_zero_iff n).mpr hne
    rw [h0] at h
    exact zero_ne_one h
  · intro h
    have hne : (n : ZMod 2) ≠ 0 := fun h0 =>
      (Nat.not_even_iff_odd.mpr h) ((zmod2_nat_cast_eq_zero_iff n).mp h0)
    exact zmod2_eq_one_of_ne_zero hne

private lemma symp_bSum_right {α : Type*} {s : ℕ} (u : 𝔽₂ s × 𝔽₂ s) (b : α → 𝔽₂ s × 𝔽₂ s)
    (S : Finset α) : symp u (bSum b S) = ∑ i ∈ S, symp u (b i) := by
  induction S using Finset.induction_on with
  | empty => simp [bSum, symp_zero_right]
  | @insert a T ha ih =>
    rw [bSum, Finset.sum_insert ha, ← bSum, symp_add_right, ih, Finset.sum_insert ha]

private lemma vecHeight_apply_ne_zero {s : ℕ} (v : 𝔽₂ s) (hv : v ≠ 0) : v (vecHeight v hv) ≠ 0 := by
  rw [vecHeight_apply hv]; decide

private lemma vecHeight_eq_of_eq_one_of_gt_zero {s : ℕ} {v : 𝔽₂ s} (hv : v ≠ 0) {j : Fin s}
    (h1 : v j ≠ 0) (h2 : ∀ m : Fin s, j < m → v m = 0) : vecHeight v hv = j := by
  apply le_antisymm
  · by_contra hgt
    push Not at hgt
    exact vecHeight_apply_ne_zero v hv (h2 _ hgt)
  · exact Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h1⟩)

/- ========================================================================= -/
/- Section 2.2: Lemma 2.3 (Existence of an Even Flag / Adapted Basis)        -/
/- ========================================================================= -/

section EvenFlag

private lemma exists_even_fiber {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (S : Finset β) (hS_odd : Odd S.card) (hα_even : Even (Fintype.card α))
    (hmem : ∀ a : α, f a ∈ S) :
    ∃ b ∈ S, Even (Finset.univ.filter (fun a : α => f a = b)).card := by
  by_contra hall
  push Not at hall
  have hsum : ∑ b ∈ S, (Finset.univ.filter (fun a : α => f a = b)).card = Fintype.card α := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (f := f) (fun a _ => hmem a)).symm
  have hcast : (∑ b ∈ S, ((Finset.univ.filter (fun a : α => f a = b)).card : ZMod 2)) =
      (Fintype.card α : ZMod 2) := by
    rw [← Nat.cast_sum, hsum]
  have hlhs : (∑ b ∈ S, ((Finset.univ.filter (fun a : α => f a = b)).card : ZMod 2)) =
      (S.card : ZMod 2) := by
    have hone : ∀ b ∈ S, ((Finset.univ.filter (fun a : α => f a = b)).card : ZMod 2) = 1 :=
      fun b hb => (zmod2_nat_cast_eq_one_iff _).mpr (Nat.not_even_iff_odd.mp (hall b hb))
    rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hlhs, (zmod2_nat_cast_eq_zero_iff _).mpr hα_even,
    (zmod2_nat_cast_eq_one_iff _).mpr hS_odd] at hcast
  exact one_ne_zero hcast

private noncomputable def linearEquiv_map_to_e0 {s : ℕ} (w : 𝔽₂ (s + 1)) (hw : w ≠ 0) :
    {ψ : 𝔽₂ (s + 1) ≃ₗ[ZMod 2] 𝔽₂ (s + 1) // ψ w = Pi.single 0 (1 : ZMod 2)} := by
  have hex_r : ∃ r : Fin (s + 1), w r ≠ 0 := by
    by_contra h; push Not at h; exact hw (funext h)
  let r : Fin (s + 1) := hex_r.choose
  have hr : w r = 1 := zmod2_eq_one_of_ne_zero hex_r.choose_spec
  let σ : Equiv.Perm (Fin (s + 1)) := Equiv.swap 0 r
  let swapE : 𝔽₂ (s + 1) ≃ₗ[ZMod 2] 𝔽₂ (s + 1) :=
    { toFun := fun x k => x (σ k)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl
      invFun := fun x k => x (σ k)
      left_inv := fun x => by ext k; simp [σ]
      right_inv := fun x => by ext k; simp [σ] }
  let w₁ : 𝔽₂ (s + 1) := swapE w
  have hw₁0 : w₁ 0 = 1 := by simp [w₁, swapE, σ, hr]
  let shear : 𝔽₂ (s + 1) ≃ₗ[ZMod 2] 𝔽₂ (s + 1) :=
    { toFun := fun x k => if k = 0 then x 0 else x k + x 0 * w₁ k
      map_add' := fun x y => by
        ext k; by_cases hk : k = 0 <;> simp [hk, add_mul]; ring
      map_smul' := fun c x => by
        ext k; by_cases hk : k = 0 <;> simp [hk, mul_add, mul_assoc]
      invFun := fun x k => if k = 0 then x 0 else x k + x 0 * w₁ k
      left_inv := fun x => by
        ext k
        by_cases hk : k = 0
        · simp [hk]
        · simp only [hk, ↓reduceIte, add_assoc, zmod2_add_self, add_zero]
      right_inv := fun x => by
        ext k
        by_cases hk : k = 0
        · simp [hk]
        · simp only [hk, ↓reduceIte, add_assoc, zmod2_add_self, add_zero] }
  refine ⟨swapE.trans shear, ?_⟩
  ext k
  change shear w₁ k = (Pi.single 0 (1 : ZMod 2) : 𝔽₂ (s + 1)) k
  by_cases hk : k = 0
  · subst hk; simp [shear, hw₁0]
  · simp [shear, hk, hw₁0, zmod2_add_self]

private def consEquiv {s : ℕ} (φ : 𝔽₂ s ≃ₗ[ZMod 2] 𝔽₂ s) :
    𝔽₂ (s + 1) ≃ₗ[ZMod 2] 𝔽₂ (s + 1) where
  toFun x := Fin.cons (x 0) (φ (Fin.tail x))
  map_add' x y := by
    ext k
    refine Fin.cases (by simp) (fun j => ?_) k
    have ht : Fin.tail (x + y) = Fin.tail x + Fin.tail y := rfl
    simp [ht]
  map_smul' c x := by
    ext k
    refine Fin.cases (by simp) (fun j => ?_) k
    have ht : Fin.tail (c • x) = c • Fin.tail x := rfl
    simp [ht]
  invFun x := Fin.cons (x 0) (φ.symm (Fin.tail x))
  left_inv x := by
    ext k
    refine Fin.cases (by simp) (fun j => ?_) k
    simp [Fin.tail_cons, Fin.tail]
  right_inv x := by
    ext k
    refine Fin.cases (by simp) (fun j => ?_) k
    simp [Fin.tail_cons, Fin.tail]

/-- Lemma 2.3 (inductive form): every even-length list of nonzero vectors in `𝔽₂ s`
    admits an invertible linear map making every height fiber have even cardinality. -/
lemma exists_even_basis_aux :
    ∀ (s : ℕ) {ι : Type} [Fintype ι], Even (Fintype.card ι) →
      ∀ (v : ι → 𝔽₂ s) (hv : ∀ i, v i ≠ 0),
        ∃ φ : 𝔽₂ s ≃ₗ[ZMod 2] 𝔽₂ s,
          IsEvenBasis (fun i => φ (v i)) (fun i h => hv i (φ.injective (by simpa using h)))
  | 0, ι, _, _, v, _ => ⟨LinearEquiv.refl _ _, fun j => j.elim0⟩
  | s + 1, ι, _, heven, v, hv => by
    let S : Finset (𝔽₂ (s + 1)) := Finset.univ.erase 0
    have hS_odd : Odd S.card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
      have hcard : Fintype.card (𝔽₂ (s + 1)) = 2 ^ (s + 1) := by
        simp [𝔽₂, 𝔽, ZMod.card]
      rw [hcard, pow_succ']
      refine ⟨2 ^ s - 1, ?_⟩
      have hpos : 1 ≤ 2 ^ s := Nat.one_le_pow s 2 (by norm_num)
      omega
    rcases exists_even_fiber v S hS_odd heven (fun i => Finset.mem_erase.mpr ⟨hv i, Finset.mem_univ _⟩)
      with ⟨w₀, hw₀S, hw₀_even⟩
    have hw₀ : w₀ ≠ 0 := (Finset.mem_erase.mp hw₀S).1
    rcases linearEquiv_map_to_e0 w₀ hw₀ with ⟨ψ, hψw₀⟩
    let v' : ι → 𝔽₂ (s + 1) := fun i => ψ (v i)
    have hv' : ∀ i, v' i ≠ 0 := fun i h => hv i (ψ.injective (by simpa [v'] using h))
    let I₀ : Finset ι := Finset.univ.filter (fun i => v' i = Pi.single 0 (1 : ZMod 2))
    have hI₀_eq : I₀ = Finset.univ.filter (fun i => v i = w₀) := by
      ext i
      simp only [I₀, Finset.mem_filter, Finset.mem_univ, true_and, v']
      constructor
      · intro h; exact ψ.injective (h.trans hψw₀.symm)
      · intro h; rw [h, hψw₀]
    have hI₀_even : Even I₀.card := hI₀_eq ▸ hw₀_even
    let I_rest : Finset ι := Finset.univ \ I₀
    have hIrest_even : Even I_rest.card := by
      have hsum : I_rest.card + I₀.card = Fintype.card ι := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ I₀), Finset.card_univ]
        have hle : I₀.card ≤ Fintype.card ι := Finset.card_le_univ I₀
        omega
      rcases heven with ⟨a, ha⟩
      rcases hI₀_even with ⟨b, hb⟩
      refine ⟨a - b, ?_⟩
      omega
    have htail_ne : ∀ i : I_rest, Fin.tail (v' i.1) ≠ 0 := by
      intro i ht0
      have hi_not : v' i.1 ≠ Pi.single 0 (1 : ZMod 2) := by
        have hmem := (Finset.mem_sdiff.mp i.2).2
        simp only [I₀, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact hmem
      have hv0 : v' i.1 0 ≠ 0 := by
        intro h0
        apply hv' i.1
        ext k
        refine Fin.cases h0 (fun j => ?_) k
        exact congrFun ht0 j
      apply hi_not
      ext k
      refine Fin.cases (by simp [zmod2_eq_one_of_ne_zero hv0]) (fun j => ?_) k
      rw [Pi.single_eq_of_ne (Fin.succ_ne_zero j)]
      exact congrFun ht0 j
    have hcard_rest : Even (Fintype.card I_rest) := by
      simpa only [Fintype.card_coe] using hIrest_even
    rcases exists_even_basis_aux s hcard_rest (fun i : I_rest => Fin.tail (v' i.1)) htail_ne
      with ⟨φ_tail, hφ_even⟩
    let φ : 𝔽₂ (s + 1) ≃ₗ[ZMod 2] 𝔽₂ (s + 1) := ψ.trans (consEquiv φ_tail)
    refine ⟨φ, fun j => ?_⟩
    have hφ_ne : ∀ i : ι, φ (v i) ≠ 0 := fun i h => hv i (φ.injective (by simpa using h))
    have hφ_apply : ∀ i : ι, φ (v i) = Fin.cons (v' i 0) (φ_tail (Fin.tail (v' i))) := fun _ => rfl
    refine Fin.cases ?_ (fun k => ?_) j
    · have hfib0 : Finset.univ.filter (fun i : ι => vecHeight (φ (v i)) (hφ_ne i) = 0) = I₀ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, I₀]
        constructor
        · intro hh
          have htail0 : φ_tail (Fin.tail (v' i)) = 0 := by
            ext m
            have hm := apply_eq_zero_of_vecHeight_lt (hφ_ne i)
              (show vecHeight (φ (v i)) (hφ_ne i) < m.succ by rw [hh]; exact Fin.succ_pos m)
            simpa [hφ_apply] using hm
          have hti : Fin.tail (v' i) = 0 := φ_tail.injective (by simpa using htail0)
          have h0 : v' i 0 = 1 := by
            have h1 := vecHeight_apply (hφ_ne i)
            rw [hh] at h1
            simpa [hφ_apply] using h1
          ext m
          refine Fin.cases (by simp [h0]) (fun r => ?_) m
          rw [Pi.single_eq_of_ne (Fin.succ_ne_zero r)]
          exact congrFun hti r
        · intro hi
          have hti : Fin.tail (v' i) = 0 := by
            ext r; simp [Fin.tail, hi]
          have h0 : v' i 0 = 1 := by simp [hi]
          apply vecHeight_eq_of_eq_one_of_gt_zero (hφ_ne i)
          · simp [hφ_apply, h0]
          · intro m
            refine Fin.cases (fun hm => absurd hm (lt_irrefl _)) (fun r _ => ?_) m
            simp [hφ_apply, hti]
      rw [hfib0]
      exact hI₀_even
    · let lhs := Finset.univ.filter (fun i : ι => vecHeight (φ (v i)) (hφ_ne i) = k.succ)
      let rhs := Finset.univ.filter (fun i : I_rest =>
        vecHeight (φ_tail (Fin.tail (v' i.1)))
          (fun h => htail_ne i (φ_tail.injective (by simpa using h))) = k)
      have hcard_eq : lhs.card = rhs.card := by
        refine Finset.card_bij (fun (i : ι) (hi : i ∈ lhs) =>
          ⟨i, by
            rw [Finset.mem_sdiff]; refine ⟨Finset.mem_univ i, fun hi0 => ?_⟩
            have hh := (Finset.mem_filter.mp hi).2
            have hti : Fin.tail (v' i) = 0 := by
              have hi0' : v' i = Pi.single 0 (1 : ZMod 2) := (Finset.mem_filter.mp hi0).2
              ext r; simp [Fin.tail, hi0']
            have h1 := vecHeight_apply_ne_zero (φ (v i)) (hφ_ne i)
            rw [hh, hφ_apply] at h1
            simp [hti] at h1⟩) ?_ ?_ ?_
        · intro i hi
          simp only [rhs, Finset.mem_filter, Finset.mem_univ, true_and]
          have hh := (Finset.mem_filter.mp hi).2
          apply vecHeight_eq_of_eq_one_of_gt_zero
          · have h1 := vecHeight_apply_ne_zero (φ (v i)) (hφ_ne i)
            rw [hh, hφ_apply] at h1; simpa using h1
          · intro m hm
            have h0 := apply_eq_zero_of_vecHeight_lt (hφ_ne i)
              (show vecHeight (φ (v i)) (hφ_ne i) < m.succ by
                rw [hh]; exact Fin.succ_lt_succ_iff.mpr hm)
            simpa [hφ_apply] using h0
        · intro i₁ _ i₂ _ hEq; exact congrArg Subtype.val hEq
        · intro ⟨i, hi_rest⟩ hr
          simp only [rhs, Finset.mem_filter, Finset.mem_univ, true_and] at hr
          refine ⟨i, ?_, rfl⟩
          simp only [lhs, Finset.mem_filter, Finset.mem_univ, true_and]
          apply vecHeight_eq_of_eq_one_of_gt_zero (hφ_ne i)
          · have h1 := vecHeight_apply_ne_zero (φ_tail (Fin.tail (v' i)))
              (fun h => htail_ne ⟨i, hi_rest⟩ (φ_tail.injective (by simpa using h)))
            rw [hr] at h1; simpa [hφ_apply] using h1
          · intro m
            refine Fin.cases (fun hm => absurd hm (not_lt_of_ge (Fin.zero_le _))) (fun r hm => ?_) m
            have hkr : k < r := Fin.succ_lt_succ_iff.mp hm
            have hne_ft : φ_tail (Fin.tail (v' i)) ≠ 0 :=
              fun h => htail_ne ⟨i, hi_rest⟩ (φ_tail.injective (by simpa using h))
            have h0 := apply_eq_zero_of_vecHeight_lt hne_ft (by rw [hr]; exact hkr)
            simpa [hφ_apply] using h0
      rw [hcard_eq]
      exact hφ_even k

end EvenFlag

/- ========================================================================= -/
/- Binary Tree Node-Set Theory (used by both §4 and §5)                      -/
/- ========================================================================= -/

section TreeTheory

variable {α : Type*} [DecidableEq α]

lemma IsTree.card_eq {k : ℕ} {A : Finset α} {N : Finset (Finset α)} (h : IsTree k A N) :
    A.card = 2 ^ k := by
  induction k generalizing A N with
  | zero => exact h.1
  | succ k ih =>
    rcases h with ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, _⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj, ih h1, ih h2, pow_succ']; ring

lemma IsTree.root_mem {k : ℕ} {A : Finset α} {N : Finset (Finset α)} (h : IsTree k A N) :
    A ∈ N := by
  cases k with
  | zero => rw [h.2]; exact Finset.mem_singleton_self A
  | succ k => rcases h with ⟨_, _, _, _, _, _, _, _, rfl⟩; exact Finset.mem_insert_self A _

lemma IsTree.subset_root {k : ℕ} {A : Finset α} {N : Finset (Finset α)} (h : IsTree k A N) :
    ∀ C ∈ N, C ⊆ A := by
  induction k generalizing A N with
  | zero =>
    intro C hC; rw [h.2] at hC; rw [Finset.mem_singleton.mp hC]
  | succ k ih =>
    rcases h with ⟨A₁, A₂, N₁, N₂, _, hunion, h1, h2, rfl⟩
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hU
    · exact subset_rfl
    · rcases Finset.mem_union.mp hU with hC1 | hC2
      · exact (ih h1 C hC1).trans (hunion ▸ Finset.subset_union_left)
      · exact (ih h2 C hC2).trans (hunion ▸ Finset.subset_union_right)

lemma IsTree.card_pow_le {k : ℕ} {A : Finset α} {N : Finset (Finset α)} (h : IsTree k A N) :
    ∀ C ∈ N, ∃ m ≤ k, C.card = 2 ^ m := by
  induction k generalizing A N with
  | zero =>
    intro C hC; rw [h.2] at hC; rw [Finset.mem_singleton.mp hC]
    exact ⟨0, le_rfl, h.1⟩
  | succ k ih =>
    rcases h with ⟨A₁, A₂, N₁, N₂, _, _, h1, h2, rfl⟩
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hU
    · exact ⟨k + 1, le_rfl, (IsTree.card_eq (k := k + 1) ⟨A₁, A₂, N₁, N₂, ‹_›, ‹_›, h1, h2, rfl⟩)⟩
    · rcases Finset.mem_union.mp hU with hC1 | hC2
      · rcases ih h1 C hC1 with ⟨m, hm, hmc⟩; exact ⟨m, by omega, hmc⟩
      · rcases ih h2 C hC2 with ⟨m, hm, hmc⟩; exact ⟨m, by omega, hmc⟩

lemma IsTree.card_pos {k : ℕ} {A : Finset α} {N : Finset (Finset α)} (h : IsTree k A N)
    {C : Finset α} (hC : C ∈ N) : 0 < C.card := by
  rcases IsTree.card_pow_le h C hC with ⟨m, _, hm⟩
  rw [hm]; exact Nat.two_pow_pos m

lemma IsTree.card_le_root {k : ℕ} {A : Finset α} {N : Finset (Finset α)} (h : IsTree k A N)
    {C : Finset α} (hC : C ∈ N) : C.card ≤ 2 ^ k := by
  rcases IsTree.card_pow_le h C hC with ⟨m, hm, hmc⟩
  rw [hmc]; exact Nat.pow_le_pow_right (by norm_num) hm

lemma mem_treesOn_iff {k : ℕ} {A : Finset α} {N : Finset (Finset α)} :
    N ∈ treesOn k A ↔ IsTree k A N := by
  simp only [treesOn, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact And.right
  · intro h
    refine ⟨fun C hC => Finset.mem_powerset.mpr (IsTree.subset_root h C hC), h⟩

lemma IsTree.laminar {k : ℕ} {A : Finset α} {N : Finset (Finset α)} (h : IsTree k A N) :
    ∀ C₁ ∈ N, ∀ C₂ ∈ N, C₁.card ≤ C₂.card → C₁ ⊆ C₂ ∨ Disjoint C₁ C₂ := by
  induction k generalizing A N with
  | zero =>
    intro C₁ h1 C₂ h2 _
    rw [h.2] at h1 h2
    rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]
    exact Or.inl subset_rfl
  | succ k ih =>
    rcases h with ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl⟩
    have htree : IsTree (k + 1) A (insert A (N₁ ∪ N₂)) :=
      ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl⟩
    intro C₁ hC₁ C₂ hC₂ hle
    rcases Finset.mem_insert.mp hC₂ with rfl | hC₂U
    · exact Or.inl (IsTree.subset_root htree C₁ hC₁)
    · rcases Finset.mem_insert.mp hC₁ with rfl | hC₁U
      · exfalso
        have hA : C₁.card = 2 ^ (k + 1) := (IsTree.card_eq htree)
        have hC₂le : C₂.card ≤ 2 ^ k := by
          rcases Finset.mem_union.mp hC₂U with hc | hc
          · exact IsTree.card_le_root h1 hc
          · exact IsTree.card_le_root h2 hc
        have hlt : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      · rcases Finset.mem_union.mp hC₁U with h11 | h12 <;>
        rcases Finset.mem_union.mp hC₂U with h21 | h22
        · exact ih h1 C₁ h11 C₂ h21 hle
        · exact Or.inr (Disjoint.mono (IsTree.subset_root h1 C₁ h11) (IsTree.subset_root h2 C₂ h22) hdisj)
        · exact Or.inr (Disjoint.mono (IsTree.subset_root h2 C₁ h12) (IsTree.subset_root h1 C₂ h21) hdisj.symm)
        · exact ih h2 C₁ h12 C₂ h22 hle

lemma IsTree.chain_unique {k : ℕ} {A : Finset α} {N : Finset (Finset α)} (h : IsTree k A N) :
    ∀ x ∈ A, ∀ m ≤ k, ∃! C ∈ N, x ∈ C ∧ C.card = 2 ^ m := by
  induction k generalizing A N with
  | zero =>
    intro x hx m hm
    have hm0 : m = 0 := by omega
    subst hm0
    refine ⟨A, ⟨(IsTree.root_mem h), hx, h.1⟩, ?_⟩
    rintro C ⟨hC, _, _⟩
    rw [h.2] at hC; exact Finset.mem_singleton.mp hC
  | succ k ih =>
    rcases h with ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl⟩
    have htree : IsTree (k + 1) A (insert A (N₁ ∪ N₂)) :=
      ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl⟩
    intro x hx m hm
    by_cases hmk : m = k + 1
    · subst hmk
      refine ⟨A, ⟨Finset.mem_insert_self A _, hx, (IsTree.card_eq htree)⟩, ?_⟩
      rintro C ⟨hC, _, hCc⟩
      rcases Finset.mem_insert.mp hC with rfl | hU
      · rfl
      · exfalso
        have hle : C.card ≤ 2 ^ k := by
          rcases Finset.mem_union.mp hU with hc | hc
          · exact IsTree.card_le_root h1 hc
          · exact IsTree.card_le_root h2 hc
        have hlt : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
    · have hmk' : m ≤ k := by omega
      have hneA : 2 ^ m ≠ A.card := by
        rw [(IsTree.card_eq htree)]
        exact ne_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
      rw [← hunion] at hx
      rcases Finset.mem_union.mp hx with hx1 | hx2
      · rcases ih h1 x hx1 m hmk' with ⟨C, ⟨hCN₁, hxC, hCc⟩, huniq⟩
        refine ⟨C, ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ hCN₁), hxC, hCc⟩, ?_⟩
        rintro D ⟨hDN, hxD, hDc⟩
        rcases Finset.mem_insert.mp hDN with rfl | hDU
        · exact absurd hDc.symm hneA
        · rcases Finset.mem_union.mp hDU with hD1 | hD2
          · exact huniq D ⟨hD1, hxD, hDc⟩
          · exact absurd (IsTree.subset_root h2 D hD2 hxD) (Finset.disjoint_left.mp hdisj hx1)
      · rcases ih h2 x hx2 m hmk' with ⟨C, ⟨hCN₂, hxC, hCc⟩, huniq⟩
        refine ⟨C, ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ hCN₂), hxC, hCc⟩, ?_⟩
        rintro D ⟨hDN, hxD, hDc⟩
        rcases Finset.mem_insert.mp hDN with rfl | hDU
        · exact absurd hDc.symm hneA
        · rcases Finset.mem_union.mp hDU with hD1 | hD2
          · exact absurd (IsTree.subset_root h1 D hD1 hxD) (Finset.disjoint_right.mp hdisj hx2)
          · exact huniq D ⟨hD2, hxD, hDc⟩

lemma IsTree.singleton_mem {k : ℕ} {A : Finset α} {N : Finset (Finset α)} (h : IsTree k A N)
    {x : α} (hx : x ∈ A) : {x} ∈ N := by
  rcases IsTree.chain_unique h x hx 0 (Nat.zero_le k) with ⟨C, ⟨hCN, hxC, hCc⟩, _⟩
  rw [pow_zero] at hCc
  rcases Finset.card_eq_one.mp hCc with ⟨y, rfl⟩
  have hxy : x = y := Finset.mem_singleton.mp hxC
  subst hxy
  exact hCN

lemma IsTree.subset_of_mem_of_card_le {k : ℕ} {A : Finset α} {N : Finset (Finset α)}
    (h : IsTree k A N) {C₁ C₂ : Finset α} (h1 : C₁ ∈ N) (h2 : C₂ ∈ N)
    {x : α} (hx1 : x ∈ C₁) (hx2 : x ∈ C₂) (hle : C₁.card ≤ C₂.card) : C₁ ⊆ C₂ := by
  rcases IsTree.laminar h C₁ h1 C₂ h2 hle with hsub | hdisj
  · exact hsub
  · exact absurd hx2 (Finset.disjoint_left.mp hdisj hx1)

lemma IsTree.eq_of_mem_of_card_eq {k : ℕ} {A : Finset α} {N : Finset (Finset α)}
    (h : IsTree k A N) {C₁ C₂ : Finset α} (h1 : C₁ ∈ N) (h2 : C₂ ∈ N)
    {x : α} (hx1 : x ∈ C₁) (hx2 : x ∈ C₂) (heq : C₁.card = C₂.card) : C₁ = C₂ :=
  Finset.Subset.antisymm (IsTree.subset_of_mem_of_card_le h h1 h2 hx1 hx2 heq.le)
    (IsTree.subset_of_mem_of_card_le h h2 h1 hx2 hx1 heq.ge)

lemma IsTree.filter_subset_left {k : ℕ} {A A₁ A₂ : Finset α} {N₁ N₂ : Finset (Finset α)}
    (hdisj : Disjoint A₁ A₂) (hunion : A₁ ∪ A₂ = A)
    (h1 : IsTree k A₁ N₁) (h2 : IsTree k A₂ N₂) :
    (insert A (N₁ ∪ N₂)).filter (fun C => C ⊆ A₁) = N₁ := by
  ext C
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨rfl | hC1 | hC2, hsub⟩
    · exfalso
      have htree : IsTree (k + 1) C (insert C (N₁ ∪ N₂)) :=
        ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl⟩
      have hA : C.card = 2 ^ (k + 1) := (IsTree.card_eq htree)
      have hle : C.card ≤ A₁.card := Finset.card_le_card hsub
      rw [hA, (IsTree.card_eq h1)] at hle
      have hlt : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    · exact hC1
    · exfalso
      rcases Finset.card_pos.mp (IsTree.card_pos h2 hC2) with ⟨x, hx⟩
      exact Finset.disjoint_left.mp hdisj (hsub hx) (IsTree.subset_root h2 C hC2 hx)
  · intro hC1
    exact ⟨Or.inr (Or.inl hC1), IsTree.subset_root h1 C hC1⟩

lemma IsTree.children_unique_of_mem {k : ℕ} {A : Finset α} {N : Finset (Finset α)}
    {A₁ A₂ B₁ B₂ : Finset α} {N₁ N₂ M₁ M₂ : Finset (Finset α)}
    (hdisjA : Disjoint A₁ A₂) (hunionA : A₁ ∪ A₂ = A) (hA1 : IsTree k A₁ N₁) (hA2 : IsTree k A₂ N₂)
    (hNA : N = insert A (N₁ ∪ N₂))
    (hdisjB : Disjoint B₁ B₂) (hunionB : B₁ ∪ B₂ = A) (hB1 : IsTree k B₁ M₁) (hB2 : IsTree k B₂ M₂)
    (hNB : N = insert A (M₁ ∪ M₂))
    {a₀ : α} (haA : a₀ ∈ A₁) (haB : a₀ ∈ B₁) :
    A₁ = B₁ ∧ A₂ = B₂ ∧ N₁ = M₁ ∧ N₂ = M₂ := by
  have htree : IsTree (k + 1) A N := ⟨A₁, A₂, N₁, N₂, hdisjA, hunionA, hA1, hA2, hNA⟩
  have hA1N : A₁ ∈ N := by rw [hNA]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (IsTree.root_mem hA1))
  have hB1N : B₁ ∈ N := by rw [hNB]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (IsTree.root_mem hB1))
  have hAB1 : A₁ = B₁ := IsTree.eq_of_mem_of_card_eq htree hA1N hB1N haA haB (by rw [(IsTree.card_eq hA1), (IsTree.card_eq hB1)])
  have hAB2 : A₂ = B₂ := by
    have h1 : A \ A₁ = A₂ := by rw [← hunionA, Finset.union_sdiff_cancel_left hdisjA]
    have h2 : A \ B₁ = B₂ := by rw [← hunionB, Finset.union_sdiff_cancel_left hdisjB]
    rw [← h1, hAB1, h2]
  have hNM1 : N₁ = M₁ := by
    have h1 := IsTree.filter_subset_left hdisjA hunionA hA1 hA2
    have h2 := IsTree.filter_subset_left hdisjB hunionB hB1 hB2
    rw [← hNA] at h1; rw [← hNB, ← hAB1] at h2
    exact h1.symm.trans h2
  have hNM2 : N₂ = M₂ := by
    have h1 := IsTree.filter_subset_left hdisjA.symm (by rw [Finset.union_comm, hunionA]) hA2 hA1
    have h2 := IsTree.filter_subset_left hdisjB.symm (by rw [Finset.union_comm, hunionB]) hB2 hB1
    rw [Finset.union_comm N₂ N₁, ← hNA] at h1
    rw [Finset.union_comm M₂ M₁, ← hNB, ← hAB2] at h2
    exact h1.symm.trans h2
  exact ⟨hAB1, hAB2, hNM1, hNM2⟩

lemma odd_choose_pow_two_sub_one (r : ℕ) :
    ∀ m < 2 ^ r, Odd ((2 ^ r - 1).choose m) := by
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : m < 2 ^ r := by omega
    have hprev : Odd ((2 ^ r - 1).choose m) := ih hm'
    have hid : (2 ^ r - 1).choose (m + 1) * (m + 1) =
        (2 ^ r - 1).choose m * (2 ^ r - 1 - m) := Nat.choose_succ_right_eq (2 ^ r - 1) m
    have hm1_pos : 0 < m + 1 := Nat.succ_pos m
    let a : ℕ := (m + 1).factorization 2
    have hdvd : 2 ^ a ∣ m + 1 := Nat.ordProj_dvd (m + 1) 2
    rcases hdvd with ⟨b, hb⟩
    have hb_odd : Odd b := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      intro h2b
      rcases h2b with ⟨c, rfl⟩
      have hdvd2 : 2 ^ (a + 1) ∣ m + 1 := ⟨c, by rw [hb, pow_succ]; ring⟩
      have hle : a + 1 ≤ (m + 1).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).mp hdvd2
      omega
    have ha_lt_r : a < r := by
      have hle : 2 ^ a ≤ m + 1 := Nat.le_of_dvd hm1_pos ⟨b, hb⟩
      have hlt : 2 ^ a < 2 ^ r := lt_of_le_of_lt hle hm
      exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    have hpow_split : 2 ^ r = 2 ^ a * 2 ^ (r - a) := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt ha_lt_r)]
    have hsub_eq : 2 ^ r - 1 - m = 2 ^ a * (2 ^ (r - a) - b) := by
      have h1 : 2 ^ r - 1 - m = 2 ^ r - (m + 1) := by omega
      rw [h1, hpow_split, hb, ← Nat.mul_sub_left_distrib]
    have hcancel : (2 ^ r - 1).choose (m + 1) * b =
        (2 ^ r - 1).choose m * (2 ^ (r - a) - b) := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a)
      calc 2 ^ a * ((2 ^ r - 1).choose (m + 1) * b)
          = (2 ^ r - 1).choose (m + 1) * (2 ^ a * b) := by ring
        _ = (2 ^ r - 1).choose (m + 1) * (m + 1) := by rw [← hb]
        _ = (2 ^ r - 1).choose m * (2 ^ r - 1 - m) := hid
        _ = (2 ^ r - 1).choose m * (2 ^ a * (2 ^ (r - a) - b)) := by rw [hsub_eq]
        _ = 2 ^ a * ((2 ^ r - 1).choose m * (2 ^ (r - a) - b)) := by ring
    have hsub_odd : Odd (2 ^ (r - a) - b) := by
      have h2even : Even (2 ^ (r - a)) := by
        rw [show r - a = (r - a - 1) + 1 by omega, pow_succ']; exact even_two_mul _
      have hb_lt : b < 2 ^ (r - a) := by
        have h1 : 2 ^ a * b < 2 ^ a * 2 ^ (r - a) := by rw [← hb, ← hpow_split]; exact hm
        exact lt_of_mul_lt_mul_left h1 (Nat.zero_le _)
      rcases h2even with ⟨u, hu⟩
      rcases hb_odd with ⟨v, hv⟩
      refine ⟨u - v - 1, ?_⟩
      omega
    have hrhs_odd : Odd ((2 ^ r - 1).choose m * (2 ^ (r - a) - b)) := hprev.mul hsub_odd
    rw [← hcancel] at hrhs_odd
    exact (Nat.odd_mul.mp hrhs_odd).1

private lemma odd_sum_of_odd {β : Type*} (S : Finset β) (f : β → ℕ)
    (hS : Odd S.card) (hf : ∀ x ∈ S, Odd (f x)) : Odd (∑ x ∈ S, f x) := by
  rw [← zmod2_nat_cast_eq_one_iff, Nat.cast_sum]
  have h1 : ∀ x ∈ S, (f x : ZMod 2) = 1 := fun x hx => (zmod2_nat_cast_eq_one_iff _).mpr (hf x hx)
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact (zmod2_nat_cast_eq_one_iff _).mpr hS

/-- Direct parity theorem for the total number of binary trees on a set of size `2 ^ k`
    (corresponds to `(2^k)! / 2^(2^k - 1)` being odd, proved without Legendre's formula). -/
lemma odd_card_treesOn :
    ∀ (k : ℕ) (A : Finset α), A.card = 2 ^ k → Odd (treesOn k A).card
  | 0, A, hA => by
    have heq : treesOn 0 A = {{A}} := by
      ext N; simp [mem_treesOn_iff, IsTree, hA]
    rw [heq]; simp
  | k + 1, A, hA => by
    have hAne : A.Nonempty := Finset.card_pos.mp (by rw [hA]; exact Nat.two_pow_pos _)
    rcases hAne with ⟨a₀, ha₀⟩
    let B := A.erase a₀
    let choices := B.powersetCard (2 ^ k - 1)
    let piece : Finset α → Finset (Finset (Finset α)) := fun S =>
      (treesOn k (insert a₀ S) ×ˢ treesOn k (A \ insert a₀ S)).image
        (fun p => insert A (p.1 ∪ p.2))
    have hpart : treesOn (k + 1) A = choices.biUnion piece := by
      ext N
      simp only [mem_treesOn_iff, Finset.mem_biUnion, piece, Finset.mem_image, Finset.mem_product,
        choices, Finset.mem_powersetCard, B]
      constructor
      · intro hN
        rcases hN with ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl⟩
        have hcase : ∃ X₁ X₂ M₁ M₂, Disjoint X₁ X₂ ∧ X₁ ∪ X₂ = A ∧
            IsTree k X₁ M₁ ∧ IsTree k X₂ M₂ ∧ insert A (N₁ ∪ N₂) = insert A (M₁ ∪ M₂) ∧
            a₀ ∈ X₁ := by
          rw [← hunion] at ha₀
          rcases Finset.mem_union.mp ha₀ with h | h
          · exact ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl, h⟩
          · exact ⟨A₂, A₁, N₂, N₁, hdisj.symm, by rw [Finset.union_comm, hunion], h2, h1,
              by rw [Finset.union_comm], h⟩
        rcases hcase with ⟨X₁, X₂, M₁, M₂, hdisjX, hunionX, hX1, hX2, hEqN, haX1⟩
        let S := X₁.erase a₀
        have hSX₁ : insert a₀ S = X₁ := Finset.insert_erase haX1
        have hSX₂ : A \ insert a₀ S = X₂ := by
          rw [hSX₁, ← hunionX, Finset.union_sdiff_cancel_left hdisjX]
        have hSsub : S ⊆ A.erase a₀ := by
          intro x hx
          rcases Finset.mem_erase.mp hx with ⟨hne, hx1⟩
          exact Finset.mem_erase.mpr ⟨hne, hunionX ▸ Finset.mem_union_left _ hx1⟩
        have hScard : S.card = 2 ^ k - 1 := by
          rw [Finset.card_erase_of_mem haX1, (IsTree.card_eq hX1)]
        refine ⟨S, ⟨hSsub, hScard⟩, (M₁, M₂), ⟨?_, ?_⟩, hEqN.symm⟩
        · rw [hSX₁]; exact hX1
        · rw [hSX₂]; exact hX2
      · rintro ⟨S, ⟨hSsub, _⟩, ⟨N₁, N₂⟩, ⟨h1, h2⟩, rfl⟩
        have hsubA : insert a₀ S ⊆ A := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · exact ha₀
          · exact (Finset.mem_erase.mp (hSsub hxS)).2
        exact ⟨insert a₀ S, A \ insert a₀ S, N₁, N₂, Finset.disjoint_sdiff,
          Finset.union_sdiff_of_subset hsubA, h1, h2, rfl⟩
    have hdisj_pieces : Set.PairwiseDisjoint (choices : Set (Finset α)) piece := by
      intro S₁ hS₁ S₂ hS₂ hne
      simp only [Function.onFun, Finset.disjoint_left, piece, Finset.mem_image, Finset.mem_product,
        mem_treesOn_iff]
      rintro N ⟨⟨N₁, N₂⟩, ⟨h1, h2⟩, rfl⟩ ⟨⟨M₁, M₂⟩, ⟨h1', h2'⟩, hEq⟩
      have hS₁sub : insert a₀ S₁ ⊆ A := fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · exact ha₀
        · exact (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hS₁).1 hxS)).2
      have hS₂sub : insert a₀ S₂ ⊆ A := fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · exact ha₀
        · exact (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hS₂).1 hxS)).2
      have hu := IsTree.children_unique_of_mem Finset.disjoint_sdiff
        (Finset.union_sdiff_of_subset hS₁sub) h1 h2 rfl
        Finset.disjoint_sdiff (Finset.union_sdiff_of_subset hS₂sub) h1' h2' hEq.symm
        (Finset.mem_insert_self a₀ S₁) (Finset.mem_insert_self a₀ S₂)
      have ha1 : a₀ ∉ S₁ := fun h => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hS₁).1 h)).1 rfl
      have ha2 : a₀ ∉ S₂ := fun h => (Finset.mem_erase.mp ((Finset.mem_powersetCard.mp hS₂).1 h)).1 rfl
      have hS12 : S₁ = S₂ := by
        have := congrArg (fun T => T.erase a₀) hu.1
        simpa [Finset.erase_insert ha1, Finset.erase_insert ha2] using this
      exact hne hS12
    rw [hpart, Finset.card_biUnion hdisj_pieces]
    have hchoices_odd : Odd choices.card := by
      simp only [choices, B, Finset.card_powersetCard, Finset.card_erase_of_mem ha₀, hA]
      exact odd_choose_pow_two_sub_one (k + 1) (2 ^ k - 1)
        (by have hlt : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega); omega)
    refine odd_sum_of_odd choices (fun S => (piece S).card) hchoices_odd (fun S hS => ?_)
    have hSsub : S ⊆ A.erase a₀ := (Finset.mem_powersetCard.mp hS).1
    have hScard : S.card = 2 ^ k - 1 := (Finset.mem_powersetCard.mp hS).2
    have haS : a₀ ∉ S := fun h => (Finset.mem_erase.mp (hSsub h)).1 rfl
    have hsubA : insert a₀ S ⊆ A := fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact ha₀
      · exact (Finset.mem_erase.mp (hSsub hxS)).2
    have hinj : Set.InjOn (fun p : Finset (Finset α) × Finset (Finset α) => insert A (p.1 ∪ p.2))
        ((treesOn k (insert a₀ S) ×ˢ treesOn k (A \ insert a₀ S) :
          Finset (Finset (Finset α) × Finset (Finset α))) :
          Set (Finset (Finset α) × Finset (Finset α))) := by
      intro p₁ hp₁ p₂ hp₂ hEq
      simp only [Finset.mem_coe, Finset.mem_product, mem_treesOn_iff] at hp₁ hp₂
      have hu := IsTree.children_unique_of_mem Finset.disjoint_sdiff
        (Finset.union_sdiff_of_subset hsubA) hp₁.1 hp₁.2 rfl
        Finset.disjoint_sdiff (Finset.union_sdiff_of_subset hsubA) hp₂.1 hp₂.2 hEq
        (Finset.mem_insert_self a₀ S) (Finset.mem_insert_self a₀ S)
      exact Prod.ext hu.2.2.1 hu.2.2.2
    rw [Finset.card_image_of_injOn hinj, Finset.card_product]
    have hc1 : (insert a₀ S).card = 2 ^ k := by
      rw [Finset.card_insert_of_notMem haS, hScard]
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      omega
    have hc2 : (A \ insert a₀ S).card = 2 ^ k := by
      rw [Finset.card_sdiff_of_subset hsubA, hA, hc1, pow_succ']; omega
    exact (odd_card_treesOn k (insert a₀ S) hc1).mul (odd_card_treesOn k (A \ insert a₀ S) hc2)

end TreeTheory

/- ========================================================================= -/
/- Section 5: Parity of the Number of Good Trees (Lemmas 5.2–5.5, Prop 5.1)  -/
/- ========================================================================= -/

section GoodTreeParity

/-- Relabeling a tree node-set by a permutation `τ`. -/
def mapTree {α : Type*} [DecidableEq α] (τ : Equiv.Perm α) (N : Finset (Finset α)) :
    Finset (Finset α) :=
  N.image (fun C => C.image τ)

lemma mapTree_invol {α : Type*} [DecidableEq α] {τ : Equiv.Perm α}
    (hτ : ∀ x, τ (τ x) = x) (N : Finset (Finset α)) :
    mapTree τ (mapTree τ N) = N := by
  ext C
  simp only [mapTree, Finset.mem_image]
  constructor
  · rintro ⟨D, ⟨E, hE, rfl⟩, rfl⟩
    have hEE : (E.image τ).image τ = E := by
      ext x; simp only [Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; rwa [hτ]
      · intro hx; exact ⟨τ x, ⟨x, hx, rfl⟩, hτ x⟩
    rwa [hEE]
  · intro hC
    refine ⟨C.image τ, ⟨C, hC, rfl⟩, ?_⟩
    ext x; simp only [Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; rwa [hτ]
    · intro hx; exact ⟨τ x, ⟨x, hx, rfl⟩, hτ x⟩

lemma IsTree.mapTree {α : Type*} [DecidableEq α] {k : ℕ} {A : Finset α}
    {N : Finset (Finset α)} (τ : Equiv.Perm α) (h : IsTree k A N) :
    IsTree k (A.image τ) (PartC.mapTree τ N) := by
  induction k generalizing A N with
  | zero =>
    refine ⟨by rw [Finset.card_image_of_injective _ τ.injective, h.1], ?_⟩
    simp [PartC.mapTree, h.2]
  | succ k ih =>
    rcases h with ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl⟩
    refine ⟨A₁.image τ, A₂.image τ, PartC.mapTree τ N₁, PartC.mapTree τ N₂, ?_, ?_, ih h1, ih h2, ?_⟩
    · rw [Finset.disjoint_left]
      intro y hy1 hy2
      rcases Finset.mem_image.mp hy1 with ⟨x1, hx1, rfl⟩
      rcases Finset.mem_image.mp hy2 with ⟨x2, hx2, heq⟩
      have := τ.injective heq; subst this
      exact Finset.disjoint_left.mp hdisj hx1 hx2
    · rw [← Finset.image_union, hunion]
    · simp only [PartC.mapTree, Finset.image_insert, Finset.image_union]

lemma mapTree_univ_mem_treesOn {α : Type*} [DecidableEq α] [Fintype α] {k : ℕ}
    (τ : Equiv.Perm α) {N : Finset (Finset α)} (hN : IsTree k Finset.univ N) :
    IsTree k Finset.univ (mapTree τ N) := by
  have huniv : (Finset.univ : Finset α).image τ = Finset.univ := by
    ext x; simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    exact ⟨τ.symm x, by simp⟩
  simpa only [huniv] using IsTree.mapTree τ hN

/-- Lemma 5.2: properties of two labels `u, v` of the same height `j`. -/
lemma lemma_5_2 {s : ℕ} {α : Type*} (hs : 1 ≤ s) (d : α → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    {u v : α} (huv : vecHeight (d u) (hd u) = vecHeight (d v) (hd v)) :
    let j := vecHeight (d u) (hd u)
    let δ := d u + d v
    let b := bClass hs d hd
    (∀ m : Fin s, j ≤ m → δ m = 0) ∧
    (b u + b v = (δ, 0)) ∧
    (∀ i : α, j ≤ vecHeight (d i) (hd i) → symp (δ, 0) (b i) = 0) ∧
    (∀ i i' : α, vecHeight (d i) (hd i) = vecHeight (d i') (hd i') →
      symp (δ, 0) (b i + b i') = 0) ∧
    (symp (b u) (b v) = 0) := by
  intro j δ b
  have h1 : ∀ m : Fin s, j ≤ m → δ m = 0 :=
    fun m hm => add_apply_eq_zero_of_vecHeight_eq (hd u) (hd v) huv hm
  have h2 : b u + b v = (δ, 0) := by
    apply Prod.ext
    · simp only [b, bClass, Prod.fst_add, δ]
      ext m; simp only [Pi.add_apply]
      have h0 := zmod2_add_self (eLast hs m)
      calc eLast hs m + d u m + (eLast hs m + d v m)
          = (eLast hs m + eLast hs m) + (d u m + d v m) := by ring
        _ = d u m + d v m := by rw [h0, zero_add]
    · simp only [b, bClass, Prod.snd_add, eta, huv]
      exact vec_add_self _
  have h3 : ∀ i : α, j ≤ vecHeight (d i) (hd i) → symp (δ, 0) (b i) = 0 := by
    intro i hi
    simp only [b, bClass, symp_fst_zero, dot2_add_left, eLast, eta, dot2_single_left]
    have hlast : j ≤ ⟨s - 1, by omega⟩ := Fin.le_def.mpr (Nat.le_sub_one_of_lt j.isLt)
    rw [h1 ⟨s - 1, by omega⟩ hlast, h1 _ hi, add_zero]
  have h4 : ∀ i i' : α, vecHeight (d i) (hd i) = vecHeight (d i') (hd i') →
      symp (δ, 0) (b i + b i') = 0 := by
    intro i i' hii'
    have hsnd : (b i + b i').2 = 0 := by
      simp only [b, bClass, Prod.snd_add, eta, hii']
      exact vec_add_self _
    have heq : b i + b i' = ((b i + b i').1, 0) := Prod.ext rfl hsnd
    rw [heq, symp_fst_zero, dot2_zero_left]
  have h5 : symp (b u) (b v) = 0 := by
    have hbv : b v = b u + (δ, 0) := by
      rw [← h2]
      apply Prod.ext
      · simp only [Prod.fst_add]; ext m
        simp only [Pi.add_apply]
        have h0 := zmod2_add_self ((b u).1 m)
        calc (b v).1 m = 0 + (b v).1 m := (zero_add _).symm
          _ = ((b u).1 m + (b u).1 m) + (b v).1 m := by rw [h0]
          _ = (b u).1 m + ((b u).1 m + (b v).1 m) := by ring
      · simp only [Prod.snd_add]; ext m
        simp only [Pi.add_apply]
        have h0 := zmod2_add_self ((b u).2 m)
        calc (b v).2 m = 0 + (b v).2 m := (zero_add _).symm
          _ = ((b u).2 m + (b u).2 m) + (b v).2 m := by rw [h0]
          _ = (b u).2 m + ((b u).2 m + (b v).2 m) := by ring
    rw [hbv, symp_add_right, symp_self, zero_add, symp_symm]
    exact h3 u le_rfl
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Lemma 5.3: `T^{uv} = T` iff `{u, v}` is a cherry of `T`. -/
lemma mapTree_swap_eq_iff {α : Type*} [DecidableEq α] [Fintype α] {k : ℕ} (hk : 1 ≤ k)
    {N : Finset (Finset α)} (hN : IsTree k Finset.univ N) {u v : α} (huv : u ≠ v) :
    mapTree (Equiv.swap u v) N = N ↔ ({u, v} : Finset α) ∈ N := by
  let τ := Equiv.swap u v
  constructor
  · intro hfix
    by_contra hnot
    rcases IsTree.chain_unique hN u (Finset.mem_univ u) 1 hk with ⟨C, ⟨hCN, huC, hCc⟩, _⟩
    rw [pow_one] at hCc
    have hCer : (C.erase u).card = 1 := by rw [Finset.card_erase_of_mem huC, hCc]
    rcases Finset.card_eq_one.mp hCer with ⟨w, hw⟩
    have hCw : C = {u, w} := by
      have := Finset.insert_erase huC
      rw [hw] at this; exact this.symm
    have hwu : w ≠ u := by
      have : w ∈ C.erase u := by rw [hw]; exact Finset.mem_singleton_self w
      exact (Finset.mem_erase.mp this).1
    have hwv : w ≠ v := by
      intro h; subst h; rw [hCw] at hCN; exact hnot hCN
    have hCimg : C.image τ = {v, w} := by
      rw [hCw, Finset.image_insert, Finset.image_singleton]
      simp [τ, Equiv.swap_apply_of_ne_of_ne hwu hwv]
    have hvwN : ({v, w} : Finset α) ∈ N := by
      rw [← hfix, ← hCimg]; exact Finset.mem_image_of_mem _ hCN
    have heq : ({u, w} : Finset α) = {v, w} :=
      IsTree.eq_of_mem_of_card_eq hN (hCw ▸ hCN) hvwN
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self w))
        (by rw [Finset.card_pair hwu.symm, Finset.card_pair hwv.symm])
    have hu_in : u ∈ ({v, w} : Finset α) := heq ▸ Finset.mem_insert_self u {w}
    rcases Finset.mem_insert.mp hu_in with h1 | h2
    · exact huv h1
    · exact hwu (Finset.mem_singleton.mp h2).symm
  · intro hcherry
    have hsub : mapTree τ N ⊆ N := by
      intro D hD
      rcases Finset.mem_image.mp hD with ⟨C, hCN, rfl⟩
      rcases IsTree.card_pow_le hN C hCN with ⟨m, _, hmc⟩
      cases m with
      | zero =>
        rw [pow_zero] at hmc
        rcases Finset.card_eq_one.mp hmc with ⟨x, rfl⟩
        rw [Finset.image_singleton]
        exact IsTree.singleton_mem hN (Finset.mem_univ (τ x))
      | succ m' =>
        have h2le : ({u, v} : Finset α).card ≤ C.card := by
          rw [Finset.card_pair huv, hmc, pow_succ']
          have := Nat.one_le_pow m' 2 (by norm_num); omega
        rcases IsTree.laminar hN {u, v} hcherry C hCN h2le with huvC | hdisj
        · have hfixC : C.image τ = C := by
            ext x; simp only [Finset.mem_image]
            constructor
            · rintro ⟨y, hy, rfl⟩
              by_cases hyu : y = u
              · rw [hyu]; simpa [τ] using huvC (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
              · by_cases hyv : y = v
                · rw [hyv]; simpa [τ] using huvC (Finset.mem_insert_self u {v})
                · rwa [Equiv.swap_apply_of_ne_of_ne hyu hyv]
            · intro hx
              refine ⟨τ x, ?_, by simp [τ]⟩
              by_cases hxu : x = u
              · rw [hxu]; simpa [τ] using huvC (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
              · by_cases hxv : x = v
                · rw [hxv]; simpa [τ] using huvC (Finset.mem_insert_self u {v})
                · rwa [Equiv.swap_apply_of_ne_of_ne hxu hxv]
          rwa [hfixC]
        · have hfixC : C.image τ = C := by
            ext x; simp only [Finset.mem_image]
            have hu_not : u ∉ C := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self u {v})
            have hv_not : v ∉ C := Finset.disjoint_left.mp hdisj
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
            constructor
            · rintro ⟨y, hy, rfl⟩
              have hyu : y ≠ u := fun h => hu_not (h ▸ hy)
              have hyv : y ≠ v := fun h => hv_not (h ▸ hy)
              rwa [Equiv.swap_apply_of_ne_of_ne hyu hyv]
            · intro hx
              have hxu : x ≠ u := fun h => hu_not (h ▸ hx)
              have hxv : x ≠ v := fun h => hv_not (h ▸ hx)
              exact ⟨x, hx, Equiv.swap_apply_of_ne_of_ne hxu hxv⟩
          rwa [hfixC]
    have hcard_eq : (mapTree τ N).card = N.card := by
      refine Finset.card_image_of_injective N (fun C₁ C₂ hEq => ?_)
      have h1 := congrArg (fun D => D.image τ) hEq
      have hinv : ∀ D : Finset α, (D.image τ).image τ = D := fun D => by
        ext x; simp only [Finset.mem_image]
        constructor
        · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; simpa [τ] using hy
        · intro hx; exact ⟨τ x, ⟨x, hx, rfl⟩, by simp [τ]⟩
      simpa only [hinv] using h1
    exact Finset.eq_of_subset_of_card_le hsub hcard_eq.ge

/-- Involution parity principle: on a finite set, the cardinality has the same parity
    as the number of fixed points of any involution. -/
private lemma card_mod_two_eq_fixed_of_invol {β : Type*} [DecidableEq β]
    (S : Finset β) (f : β → β) (hclosed : ∀ x ∈ S, f x ∈ S)
    (hinvol : ∀ x ∈ S, f (f x) = x) :
    S.card % 2 = (S.filter (fun x => f x = x)).card % 2 := by
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases hnonfix : ∃ x ∈ S, f x ≠ x
    · rcases hnonfix with ⟨x, hxS, hfx⟩
      let S' := (S.erase x).erase (f x)
      have hfxS : f x ∈ S := hclosed x hxS
      have hfx_in : f x ∈ S.erase x := Finset.mem_erase.mpr ⟨hfx, hfxS⟩
      have hS'card : S'.card + 2 = S.card := by
        have h1 : S'.card = (S.erase x).card - 1 := by
          rw [Finset.card_erase_of_mem hfx_in]
        have h2 : (S.erase x).card = S.card - 1 := by
          rw [Finset.card_erase_of_mem hxS]
        have hge2 : 2 ≤ S.card := by
          have : ({x, f x} : Finset β) ⊆ S := by
            intro y hy; rcases Finset.mem_insert.mp hy with rfl | h
            · exact hxS
            · rw [Finset.mem_singleton.mp h]; exact hfxS
          have := Finset.card_le_card this
          rwa [Finset.card_pair hfx.symm] at this
        omega
      have hclosed' : ∀ y ∈ S', f y ∈ S' := by
        intro y hy
        have h1 := Finset.mem_erase.mp hy
        have h2 := Finset.mem_erase.mp h1.2
        refine Finset.mem_erase.mpr ⟨fun hfyfx => h2.1 ?_, Finset.mem_erase.mpr ⟨fun hfyx => h1.1 ?_, hclosed y h2.2⟩⟩
        · have := congrArg f hfyfx; rwa [hinvol y h2.2, hinvol x hxS] at this
        · have := congrArg f hfyx; rwa [hinvol y h2.2] at this
      have hinvol' : ∀ y ∈ S', f (f y) = y := fun y hy =>
        hinvol y (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).2
      have hfix_eq : S'.filter (fun y => f y = y) = S.filter (fun y => f y = y) := by
        ext y
        simp only [S', Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, _, hyS⟩, hfy⟩; exact ⟨hyS, hfy⟩
        · rintro ⟨hyS, hfy⟩
          refine ⟨⟨fun h1 => hfx ?_, fun h2 => hfx ?_, hyS⟩, hfy⟩
          · have hff : f (f x) = f x := by rw [← h1, hfy]
            rw [hinvol x hxS] at hff; exact hff.symm
          · rw [← h2, hfy]
      have hrec := ih S'.card (by omega) S' hclosed' hinvol' rfl
      rw [hfix_eq] at hrec
      omega
    · push Not at hnonfix
      have hfeq : S.filter (fun x => f x = x) = S := Finset.filter_true_of_mem hnonfix
      rw [hfeq, hcard]

/-- Helper: partition any even-sized finset into a list of disjoint unordered pairs. -/
private lemma exists_pair_list {α : Type*} [DecidableEq α] (S : Finset α) (hS : Even S.card) :
    ∃ L : List (α × α),
      (∀ p ∈ L, p.1 ≠ p.2 ∧ p.1 ∈ S ∧ p.2 ∈ S) ∧
      (∀ x ∈ S, ∃ p ∈ L, x = p.1 ∨ x = p.2) ∧
      (∀ i j : Fin L.length, i ≠ j → Disjoint ({(L.get i).1, (L.get i).2} : Finset α)
        ({(L.get j).1, (L.get j).2} : Finset α)) ∧
      2 * L.length = S.card := by
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | _ n ih =>
    by_cases h0 : S = ∅
    · subst h0; exact ⟨[], by simp, by simp, fun i => i.elim0, by simp at hcard; omega⟩
    · have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h0
      rcases hne with ⟨a, ha⟩
      have hne2 : (S.erase a).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_erase_of_mem ha]
        rcases hS with ⟨m, hm⟩
        have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a, ha⟩
        omega
      rcases hne2 with ⟨b, hb⟩
      have hab : b ≠ a := (Finset.mem_erase.mp hb).1
      have hbS : b ∈ S := (Finset.mem_erase.mp hb).2
      let S' := (S.erase a).erase b
      have hS'card : S'.card + 2 = S.card := by
        rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
        have h2 : 2 ≤ S.card := by
          have := Finset.card_le_card (show ({a, b} : Finset α) ⊆ S from by
            intro x hx; rcases Finset.mem_insert.mp hx with rfl | h
            · exact ha
            · rw [Finset.mem_singleton.mp h]; exact hbS)
          rwa [Finset.card_pair hab.symm] at this
        omega
      have hS'even : Even S'.card := by
        rcases hS with ⟨m, hm⟩; refine ⟨m - 1, ?_⟩; omega
      rcases ih S'.card (by omega) S' hS'even rfl with ⟨L', hmem', hcov', hdisj', hlen'⟩
      refine ⟨(a, b) :: L', ?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨hab.symm, ha, hbS⟩
        · rcases hmem' p hp' with ⟨hne, h1, h2⟩
          exact ⟨hne, (Finset.mem_erase.mp (Finset.mem_erase.mp h1).2).2,
            (Finset.mem_erase.mp (Finset.mem_erase.mp h2).2).2⟩
      · intro x hx
        by_cases hxa : x = a
        · exact ⟨(a, b), List.mem_cons_self, Or.inl hxa⟩
        · by_cases hxb : x = b
          · exact ⟨(a, b), List.mem_cons_self, Or.inr hxb⟩
          · have hx' : x ∈ S' := Finset.mem_erase.mpr ⟨hxb, Finset.mem_erase.mpr ⟨hxa, hx⟩⟩
            rcases hcov' x hx' with ⟨p, hp, hpx⟩
            exact ⟨p, List.mem_cons_of_mem _ hp, hpx⟩
      · intro i j
        refine Fin.cases ?_ (fun i' => ?_) i
        · refine Fin.cases (fun h => absurd rfl h) (fun j' _ => ?_) j
          have hp := hmem' (L'.get j') (List.get_mem L' j')
          have h1 := Finset.mem_erase.mp hp.2.1
          have h2 := Finset.mem_erase.mp h1.2
          have h3 := Finset.mem_erase.mp hp.2.2
          have h4 := Finset.mem_erase.mp h3.2
          simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
            List.getElem_cons_zero, List.getElem_cons_succ,
            Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
          rintro x (rfl | rfl) (hx | hx)
          · exact h2.1 hx.symm
          · exact h4.1 hx.symm
          · exact h1.1 hx.symm
          · exact h3.1 hx.symm
        · refine Fin.cases (fun _ => ?_) (fun j' hij' => ?_) j
          · have hp := hmem' (L'.get i') (List.get_mem L' i')
            have h1 := Finset.mem_erase.mp hp.2.1
            have h2 := Finset.mem_erase.mp h1.2
            have h3 := Finset.mem_erase.mp hp.2.2
            have h4 := Finset.mem_erase.mp h3.2
            simp only [List.get_eq_getElem, Fin.val_zero, Fin.val_succ,
              List.getElem_cons_zero, List.getElem_cons_succ,
              Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
            rintro x (rfl | rfl) (hx | hx)
            · exact h2.1 hx
            · exact h1.1 hx
            · exact h4.1 hx
            · exact h3.1 hx
          · have hij'' : i' ≠ j' := fun h => hij' (congrArg Fin.succ h)
            simpa only [List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ] using hdisj' i' j' hij''
      · simp only [List.length_cons]; omega

/-- Partition an even-flag label set into nondecreasing-height equal-height pairs `P_1, ..., P_m`. -/
private lemma exists_height_pairing {s m : ℕ} (d : Fin (2 * m) → 𝔽₂ s) (hd : ∀ i, d i ≠ 0)
    (heven : IsEvenBasis d hd) :
    ∃ (pU pV : Fin m → Fin (2 * m)) (pH : Fin m → Fin s),
      Monotone pH ∧
      (∀ r : Fin m, pU r ≠ pV r) ∧
      (∀ r : Fin m, vecHeight (d (pU r)) (hd (pU r)) = pH r ∧
                    vecHeight (d (pV r)) (hd (pV r)) = pH r) ∧
      (∀ r₁ r₂ : Fin m, r₁ ≠ r₂ →
        Disjoint ({pU r₁, pV r₁} : Finset (Fin (2 * m))) ({pU r₂, pV r₂} : Finset (Fin (2 * m)))) ∧
      (∀ x : Fin (2 * m), ∃ r : Fin m, x ∈ ({pU r, pV r} : Finset (Fin (2 * m)))) := by
  let fib : Fin s → Finset (Fin (2 * m)) :=
    fun j => Finset.univ.filter (fun i => vecHeight (d i) (hd i) = j)
  have hfib_pair : ∀ j : Fin s, ∃ L : List (Fin (2 * m) × Fin (2 * m)),
      (∀ p ∈ L, p.1 ≠ p.2 ∧ p.1 ∈ fib j ∧ p.2 ∈ fib j) ∧
      (∀ x ∈ fib j, ∃ p ∈ L, x = p.1 ∨ x = p.2) ∧
      (∀ i₁ i₂ : Fin L.length, i₁ ≠ i₂ →
        Disjoint ({(L.get i₁).1, (L.get i₁).2} : Finset (Fin (2 * m)))
                 ({(L.get i₂).1, (L.get i₂).2} : Finset (Fin (2 * m)))) ∧
      2 * L.length = (fib j).card := fun j => exists_pair_list (fib j) (heven j)
  let Lf : Fin s → List (Fin (2 * m) × Fin (2 * m)) := fun j => (hfib_pair j).choose
  have hLf : ∀ j : Fin s,
      (∀ p ∈ Lf j, p.1 ≠ p.2 ∧ p.1 ∈ fib j ∧ p.2 ∈ fib j) ∧
      (∀ x ∈ fib j, ∃ p ∈ Lf j, x = p.1 ∨ x = p.2) ∧
      (∀ i₁ i₂ : Fin (Lf j).length, i₁ ≠ i₂ →
        Disjoint ({((Lf j).get i₁).1, ((Lf j).get i₁).2} : Finset (Fin (2 * m)))
                 ({((Lf j).get i₂).1, ((Lf j).get i₂).2} : Finset (Fin (2 * m)))) ∧
      2 * (Lf j).length = (fib j).card := fun j => (hfib_pair j).choose_spec
  let allList : List (Fin s × (Fin (2 * m) × Fin (2 * m))) :=
    (List.finRange s).flatMap (fun j => (Lf j).map (fun p => (j, p)))
  have hlen : allList.length = m := by
    have h2len : 2 * allList.length = 2 * m := by
      have h1 : allList.length = ∑ j : Fin s, (Lf j).length := by
        simp only [allList, List.length_flatMap, List.length_map]
        rw [← Fin.sum_univ_def (fun j : Fin s => (Lf j).length)]
      rw [h1, Finset.mul_sum]
      have h2 : ∑ j : Fin s, 2 * (Lf j).length = ∑ j : Fin s, (fib j).card :=
        Finset.sum_congr rfl (fun j _ => (hLf j).2.2.2)
      rw [h2]
      have h3 : ∑ j : Fin s, (fib j).card = (Finset.univ : Finset (Fin (2 * m))).card :=
        (Finset.card_eq_sum_card_fiberwise (f := fun i : Fin (2 * m) => vecHeight (d i) (hd i))
          (fun _ _ => Finset.mem_univ _)).symm
      rw [h3, Finset.card_univ, Fintype.card_fin]
    omega
  let pU : Fin m → Fin (2 * m) := fun r => (allList.get (r.cast hlen.symm)).2.1
  let pV : Fin m → Fin (2 * m) := fun r => (allList.get (r.cast hlen.symm)).2.2
  let pH : Fin m → Fin s := fun r => (allList.get (r.cast hlen.symm)).1
  have hmem_all : ∀ r : Fin m,
      pU r ≠ pV r ∧ pU r ∈ fib (pH r) ∧ pV r ∈ fib (pH r) := by
    intro r
    have hmem := List.get_mem allList (r.cast hlen.symm)
    simp only [allList, List.mem_flatMap, List.mem_map] at hmem
    rcases hmem with ⟨j, _, p, hp, hEq⟩
    have hj : pH r = j := congrArg Prod.fst hEq.symm
    have hu : pU r = p.1 := congrArg (fun x => x.2.1) hEq.symm
    have hv : pV r = p.2 := congrArg (fun x => x.2.2) hEq.symm
    rw [hj, hu, hv]
    exact (hLf j).1 p hp
  have hmono : Monotone pH := by
    have hpw : allList.Pairwise (fun x y => x.1 ≤ y.1) := by
      rw [List.pairwise_flatMap]
      refine ⟨fun j _ => ?_, ?_⟩
      · rw [List.pairwise_map]; exact List.pairwise_iff_getElem.mpr (fun _ _ _ _ _ => le_rfl)
      · exact (List.pairwise_lt_finRange s).imp (fun {j₁ j₂} hlt x hx y hy => by
          rcases List.mem_map.mp hx with ⟨_, _, rfl⟩
          rcases List.mem_map.mp hy with ⟨_, _, rfl⟩
          exact le_of_lt hlt)
    intro r₁ r₂ hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact le_rfl
    · exact List.pairwise_iff_get.mp hpw (r₁.cast hlen.symm) (r₂.cast hlen.symm) hlt
  have hdisj : ∀ r₁ r₂ : Fin m, r₁ ≠ r₂ →
      Disjoint ({pU r₁, pV r₁} : Finset (Fin (2 * m))) ({pU r₂, pV r₂} : Finset (Fin (2 * m))) := by
    have hpw : allList.Pairwise (fun x y =>
        Disjoint ({x.2.1, x.2.2} : Finset (Fin (2 * m))) ({y.2.1, y.2.2} : Finset (Fin (2 * m)))) := by
      rw [List.pairwise_flatMap]
      refine ⟨fun j _ => ?_, ?_⟩
      · rw [List.pairwise_map]
        rw [List.pairwise_iff_get]
        intro i₁ i₂ hlt
        exact (hLf j).2.2.1 i₁ i₂ (ne_of_lt hlt)
      · exact (List.pairwise_lt_finRange s).imp (fun {j₁ j₂} hlt x hx y hy => by
          rcases List.mem_map.mp hx with ⟨p₁, hp₁, rfl⟩
          rcases List.mem_map.mp hy with ⟨p₂, hp₂, rfl⟩
          have h1 := (hLf j₁).1 p₁ hp₁
          have h2 := (hLf j₂).1 p₂ hp₂
          rw [Finset.disjoint_left]
          intro z hz1 hz2
          have hz_j1 : vecHeight (d z) (hd z) = j₁ := by
            rcases Finset.mem_insert.mp hz1 with rfl | h
            · exact (Finset.mem_filter.mp h1.2.1).2
            · rw [Finset.mem_singleton.mp h]; exact (Finset.mem_filter.mp h1.2.2).2
          have hz_j2 : vecHeight (d z) (hd z) = j₂ := by
            rcases Finset.mem_insert.mp hz2 with rfl | h
            · exact (Finset.mem_filter.mp h2.2.1).2
            · rw [Finset.mem_singleton.mp h]; exact (Finset.mem_filter.mp h2.2.2).2
          exact ne_of_lt hlt (hz_j1.symm.trans hz_j2))
    intro r₁ r₂ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact List.pairwise_iff_get.mp hpw (r₁.cast hlen.symm) (r₂.cast hlen.symm) hlt
    · exact (List.pairwise_iff_get.mp hpw (r₂.cast hlen.symm) (r₁.cast hlen.symm) hgt).symm
  have hcov : ∀ x : Fin (2 * m), ∃ r : Fin m, x ∈ ({pU r, pV r} : Finset (Fin (2 * m))) := by
    intro x
    let j := vecHeight (d x) (hd x)
    have hxj : x ∈ fib j := Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩
    rcases (hLf j).2.1 x hxj with ⟨p, hp, hpx⟩
    have hmem : (j, p) ∈ allList := by
      simp only [allList, List.mem_flatMap, List.mem_map]
      exact ⟨j, List.mem_finRange j, p, hp, rfl⟩
    rcases List.mem_iff_get.mp hmem with ⟨idx, hidx⟩
    refine ⟨idx.cast hlen, ?_⟩
    have hEq : allList.get ((idx.cast hlen).cast hlen.symm) = (j, p) := by simpa using hidx
    simp only [pU, pV, hEq, Finset.mem_insert, Finset.mem_singleton]
    exact hpx
  refine ⟨pU, pV, pH, hmono, fun r => (hmem_all r).1, fun r => ?_, hdisj, hcov⟩
  exact ⟨(Finset.mem_filter.mp (hmem_all r).2.1).2, (Finset.mem_filter.mp (hmem_all r).2.2).2⟩

/-- Helper: collapsing a tree on `D.biUnion P` with all cherries `P r` (`r ∈ D`) to a tree on `D`. -/
private lemma collapse_isTree {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : β → Finset α) (hP_card : ∀ r, (P r).card = 2)
    (hP_disj : ∀ r₁ r₂, r₁ ≠ r₂ → Disjoint (P r₁) (P r₂)) :
    ∀ (k : ℕ) (D : Finset β) (N : Finset (Finset α)),
      IsTree (k + 1) (D.biUnion P) N → (∀ r ∈ D, P r ∈ N) →
      IsTree k D ((N.filter (fun C => 2 ≤ C.card)).image (fun C => D.filter (fun r => P r ⊆ C)))
  | 0, D, N, hN, hPmem => by
    have hDcard : D.card = 1 := by
      have hbi : (D.biUnion P).card = 2 * D.card := by
        rw [Finset.card_biUnion (fun r₁ _ r₂ _ hne => hP_disj r₁ r₂ hne)]
        rw [Finset.sum_congr rfl (fun r _ => hP_card r), Finset.sum_const, smul_eq_mul, mul_comm]
      have h2 := (IsTree.card_eq hN)
      rw [hbi] at h2; omega
    refine ⟨hDcard, ?_⟩
    rcases Finset.card_eq_one.mp hDcard with ⟨r₀, rfl⟩
    have hroot : ({r₀} : Finset β).biUnion P = P r₀ := by simp
    rw [hroot] at hN
    ext E
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨C, ⟨hCN, hC2⟩, rfl⟩
      have hCsub : C ⊆ P r₀ := IsTree.subset_root hN C hCN
      have hCeq : C = P r₀ := Finset.eq_of_subset_of_card_le hCsub (by rw [hP_card r₀]; exact hC2)
      subst hCeq
      ext r; simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
      rintro rfl; exact subset_rfl
    · rintro rfl
      refine ⟨P r₀, ⟨(IsTree.root_mem hN), by rw [hP_card r₀]⟩, ?_⟩
      ext r; simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
      rintro rfl; exact subset_rfl
  | k + 1, D, N, hN, hPmem => by
    rcases hN with ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl⟩
    have htree : IsTree (k + 2) (D.biUnion P) (insert (D.biUnion P) (N₁ ∪ N₂)) :=
      ⟨A₁, A₂, N₁, N₂, hdisj, hunion, h1, h2, rfl⟩
    let D₁ := D.filter (fun r => P r ⊆ A₁)
    let D₂ := D.filter (fun r => P r ⊆ A₂)
    have hsplit_r : ∀ r ∈ D, P r ⊆ A₁ ∨ P r ⊆ A₂ := by
      intro r hr
      have hPrN : P r ∈ insert (D.biUnion P) (N₁ ∪ N₂) := hPmem r hr
      have hA1N : A₁ ∈ insert (D.biUnion P) (N₁ ∪ N₂) :=
        Finset.mem_insert_of_mem (Finset.mem_union_left _ (IsTree.root_mem h1))
      have hA2N : A₂ ∈ insert (D.biUnion P) (N₁ ∪ N₂) :=
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (IsTree.root_mem h2))
      have h2le1 : (P r).card ≤ A₁.card := by
        rw [hP_card r, (IsTree.card_eq h1), pow_succ']; have := Nat.one_le_pow k 2 (by norm_num); omega
      have h2le2 : (P r).card ≤ A₂.card := by
        rw [hP_card r, (IsTree.card_eq h2), pow_succ']; have := Nat.one_le_pow k 2 (by norm_num); omega
      rcases Finset.card_pos.mp (by rw [hP_card r]; omega : 0 < (P r).card) with ⟨x, hx⟩
      have hxA : x ∈ A₁ ∪ A₂ := by
        rw [hunion]; exact Finset.mem_biUnion.mpr ⟨r, hr, hx⟩
      rcases Finset.mem_union.mp hxA with hx1 | hx2
      · exact Or.inl (IsTree.subset_of_mem_of_card_le htree hPrN hA1N hx hx1 h2le1)
      · exact Or.inr (IsTree.subset_of_mem_of_card_le htree hPrN hA2N hx hx2 h2le2)
    have hDdisj : Disjoint D₁ D₂ := by
      rw [Finset.disjoint_left]; intro r h1r h2r
      rcases Finset.card_pos.mp (by rw [hP_card r]; omega : 0 < (P r).card) with ⟨x, hx⟩
      exact Finset.disjoint_left.mp hdisj
        ((Finset.mem_filter.mp h1r).2 hx) ((Finset.mem_filter.mp h2r).2 hx)
    have hDunion : D₁ ∪ D₂ = D := by
      ext r; simp only [D₁, D₂, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hr, _⟩ | ⟨hr, _⟩) <;> exact hr
      · intro hr; rcases hsplit_r r hr with h | h
        · exact Or.inl ⟨hr, h⟩
        · exact Or.inr ⟨hr, h⟩
    have hA1_eq : D₁.biUnion P = A₁ := by
      ext x; simp only [Finset.mem_biUnion, D₁, Finset.mem_filter]
      constructor
      · rintro ⟨r, ⟨_, hsub⟩, hx⟩; exact hsub hx
      · intro hx1
        have hxU : x ∈ D.biUnion P := by rw [← hunion]; exact Finset.mem_union_left _ hx1
        rcases Finset.mem_biUnion.mp hxU with ⟨r, hr, hxr⟩
        rcases hsplit_r r hr with hsub1 | hsub2
        · exact ⟨r, ⟨hr, hsub1⟩, hxr⟩
        · exact absurd (hsub2 hxr) (Finset.disjoint_left.mp hdisj hx1)
    have hA2_eq : D₂.biUnion P = A₂ := by
      ext x; simp only [Finset.mem_biUnion, D₂, Finset.mem_filter]
      constructor
      · rintro ⟨r, ⟨_, hsub⟩, hx⟩; exact hsub hx
      · intro hx2
        have hxU : x ∈ D.biUnion P := by rw [← hunion]; exact Finset.mem_union_right _ hx2
        rcases Finset.mem_biUnion.mp hxU with ⟨r, hr, hxr⟩
        rcases hsplit_r r hr with hsub1 | hsub2
        · exact absurd (hsub1 hxr) (Finset.disjoint_right.mp hdisj hx2)
        · exact ⟨r, ⟨hr, hsub2⟩, hxr⟩
    have hP1 : ∀ r ∈ D₁, P r ∈ N₁ := by
      intro r hr
      have hrD := (Finset.mem_filter.mp hr).1
      have hsub := (Finset.mem_filter.mp hr).2
      have hfilt := IsTree.filter_subset_left hdisj hunion h1 h2
      rw [← hfilt]; exact Finset.mem_filter.mpr ⟨hPmem r hrD, hsub⟩
    have hP2 : ∀ r ∈ D₂, P r ∈ N₂ := by
      intro r hr
      have hrD := (Finset.mem_filter.mp hr).1
      have hsub := (Finset.mem_filter.mp hr).2
      have hfilt := IsTree.filter_subset_left hdisj.symm (by rw [Finset.union_comm, hunion]) h2 h1
      rw [Finset.union_comm N₂ N₁] at hfilt
      rw [← hfilt]; exact Finset.mem_filter.mpr ⟨hPmem r hrD, hsub⟩
    have hT1 := collapse_isTree P hP_card hP_disj k D₁ N₁ (hA1_eq.symm ▸ h1) hP1
    have hT2 := collapse_isTree P hP_card hP_disj k D₂ N₂ (hA2_eq.symm ▸ h2) hP2
    refine ⟨D₁, D₂, _, _, hDdisj, hDunion, hT1, hT2, ?_⟩
    ext E
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
    constructor
    · rintro ⟨C, ⟨rfl | hC1 | hC2, hC2le⟩, rfl⟩
      · left; ext r; simp only [Finset.mem_filter, and_iff_left_iff_imp]
        intro hr x hx; exact Finset.mem_biUnion.mpr ⟨r, hr, hx⟩
      · right; left
        refine ⟨C, ⟨hC1, hC2le⟩, ?_⟩
        ext r; simp only [D₁, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hr, _⟩, hsub⟩; exact ⟨hr, hsub⟩
        · rintro ⟨hr, hsub⟩; exact ⟨⟨hr, hsub.trans (IsTree.subset_root h1 C hC1)⟩, hsub⟩
      · right; right
        refine ⟨C, ⟨hC2, hC2le⟩, ?_⟩
        ext r; simp only [D₂, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hr, _⟩, hsub⟩; exact ⟨hr, hsub⟩
        · rintro ⟨hr, hsub⟩; exact ⟨⟨hr, hsub.trans (IsTree.subset_root h2 C hC2)⟩, hsub⟩
    · rintro (hEqE | ⟨C, ⟨hC1, hC2le⟩, rfl⟩ | ⟨C, ⟨hC2, hC2le⟩, rfl⟩)
      · subst hEqE
        refine ⟨E.biUnion P, ⟨Or.inl rfl, ?_⟩, ?_⟩
        · rw [(IsTree.card_eq htree), pow_succ', pow_succ']; have := Nat.one_le_pow k 2 (by norm_num); omega
        · ext r; simp only [Finset.mem_filter, and_iff_left_iff_imp]
          intro hr x hx; exact Finset.mem_biUnion.mpr ⟨r, hr, hx⟩
      · refine ⟨C, ⟨Or.inr (Or.inl hC1), hC2le⟩, ?_⟩
        ext r; simp only [D₁, Finset.mem_filter]
        constructor
        · rintro ⟨hr, hsub⟩; exact ⟨⟨hr, hsub.trans (IsTree.subset_root h1 C hC1)⟩, hsub⟩
        · rintro ⟨⟨hr, _⟩, hsub⟩; exact ⟨hr, hsub⟩
      · refine ⟨C, ⟨Or.inr (Or.inr hC2), hC2le⟩, ?_⟩
        ext r; simp only [D₂, Finset.mem_filter]
        constructor
        · rintro ⟨hr, hsub⟩; exact ⟨⟨hr, hsub.trans (IsTree.subset_root h2 C hC2)⟩, hsub⟩
        · rintro ⟨⟨hr, _⟩, hsub⟩; exact ⟨hr, hsub⟩

/-- Helper: expanding a tree on `D` by replacing each leaf `r ∈ D` with cherry `P r`. -/
private lemma expand_isTree {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : β → Finset α) (hP_card : ∀ r, (P r).card = 2)
    (hP_disj : ∀ r₁ r₂, r₁ ≠ r₂ → Disjoint (P r₁) (P r₂)) :
    ∀ (k : ℕ) (D : Finset β) (M : Finset (Finset β)),
      IsTree k D M →
      IsTree (k + 1) (D.biUnion P)
        ((M.image (fun E => E.biUnion P)) ∪ (D.biUnion P).image (fun x => {x})) ∧
      (∀ r ∈ D, P r ∈ (M.image (fun E => E.biUnion P)) ∪ (D.biUnion P).image (fun x => {x}))
  | 0, D, M, hM => by
    rcases Finset.card_eq_one.mp hM.1 with ⟨r₀, rfl⟩
    have hM_eq : M = {{r₀}} := hM.2
    rcases Finset.card_eq_two.mp (hP_card r₀) with ⟨a, b, hab, hPr⟩
    have hbi : ({r₀} : Finset β).biUnion P = {a, b} := by simp [hPr]
    have hN_eq : (M.image (fun E => E.biUnion P)) ∪ (({r₀} : Finset β).biUnion P).image (fun x => {x}) =
        insert ({a, b} : Finset α) ({{a}} ∪ {{b}}) := by
      rw [hM_eq, hbi]
      ext C; simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton,
        Finset.mem_insert]
      constructor
      · rintro (⟨_, rfl, rfl⟩ | ⟨x, rfl | rfl, rfl⟩)
        · left; simp [hPr]
        · right; left; rfl
        · right; right; rfl
      · rintro (rfl | rfl | rfl)
        · left; exact ⟨{r₀}, rfl, by simp [hPr]⟩
        · right; exact ⟨a, Or.inl rfl, rfl⟩
        · right; exact ⟨b, Or.inr rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hN_eq, hbi]
      exact ⟨{a}, {b}, {{a}}, {{b}}, Finset.disjoint_singleton.mpr hab,
        by ext x; simp, ⟨by simp, rfl⟩, ⟨by simp, rfl⟩, rfl⟩
    · intro r hr
      rw [Finset.mem_singleton.mp hr]
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨{r₀}, (IsTree.root_mem hM), by simp⟩
  | k + 1, D, M, hM => by
    rcases hM with ⟨D₁, D₂, M₁, M₂, hDdisj, hDunion, hM1, hM2, rfl⟩
    have h1 := expand_isTree P hP_card hP_disj k D₁ M₁ hM1
    have h2 := expand_isTree P hP_card hP_disj k D₂ M₂ hM2
    have hPdisj : Disjoint (D₁.biUnion P) (D₂.biUnion P) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_biUnion.mp hx1 with ⟨r₁, hr₁, hxr₁⟩
      rcases Finset.mem_biUnion.mp hx2 with ⟨r₂, hr₂, hxr₂⟩
      have hne : r₁ ≠ r₂ := fun h => Finset.disjoint_left.mp hDdisj hr₁ (h ▸ hr₂)
      exact Finset.disjoint_left.mp (hP_disj r₁ r₂ hne) hxr₁ hxr₂
    have hPunion : D₁.biUnion P ∪ D₂.biUnion P = D.biUnion P := by
      rw [← hDunion, Finset.union_biUnion]
    have hset : ((insert D (M₁ ∪ M₂)).image (fun E => E.biUnion P)) ∪
          (D.biUnion P).image (fun x => {x}) =
        insert (D.biUnion P)
          (((M₁.image (fun E => E.biUnion P)) ∪ (D₁.biUnion P).image (fun x => {x})) ∪
           ((M₂.image (fun E => E.biUnion P)) ∪ (D₂.biUnion P).image (fun x => {x}))) := by
      rw [Finset.image_insert, Finset.image_union, ← hPunion, Finset.image_union]
      ext C; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    refine ⟨?_, ?_⟩
    · rw [hset]
      exact ⟨D₁.biUnion P, D₂.biUnion P, _, _, hPdisj, hPunion, h1.1, h2.1, rfl⟩
    · intro r hr
      rw [hset]
      rw [← hDunion] at hr
      rcases Finset.mem_union.mp hr with hr1 | hr2
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (h1.2 r hr1))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (h2.2 r hr2))

/-- Proposition 5.1: For any `s ≥ 2` and any even-flag list `d : Fin (2^(s-1)) → 𝔽₂ s`
    of nonzero vectors, the number of good binary trees on `Fin (2^(s-1))` is odd. -/
theorem odd_card_goodTreesOn_aux {s : ℕ} (hs : 2 ≤ s)
    (d : Fin (2 ^ (s - 1)) → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (heven : IsEvenBasis d hd) :
    Odd (goodTreesOn (bClass (by omega : 1 ≤ s) d hd) (s - 1) Finset.univ).card := by
  let b := bClass (by omega : 1 ≤ s) d hd
  let m : ℕ := 2 ^ (s - 2)
  have hM : 2 ^ (s - 1) = 2 * m := by
    simp only [m]; rw [show s - 1 = (s - 2) + 1 by omega, pow_succ']
  let eM : Fin (2 * m) ≃ Fin (2 ^ (s - 1)) := finCongr hM.symm
  have heven' : IsEvenBasis (fun i => d (eM i)) (fun i => hd (eM i)) := by
    intro j
    have hcard_eq : (Finset.univ.filter (fun i : Fin (2 * m) =>
          vecHeight (d (eM i)) (hd (eM i)) = j)).card =
        (Finset.univ.filter (fun i : Fin (2 ^ (s - 1)) => vecHeight (d i) (hd i) = j)).card := by
      refine Finset.card_bij (fun i _ => eM i)
        (fun i hi => by simpa using hi)
        (fun _ _ _ _ h => eM.injective h)
        (fun i hi => ⟨eM.symm i, by simpa using hi, by simp⟩)
    rw [hcard_eq]; exact heven j
  rcases exists_height_pairing (fun i => d (eM i)) (fun i => hd (eM i)) heven'
    with ⟨pU', pV', pH, hpH_mono, hpUV_ne', hpH_eq', hP_disj', hP_cov'⟩
  let pU : Fin m → Fin (2 ^ (s - 1)) := fun r => eM (pU' r)
  let pV : Fin m → Fin (2 ^ (s - 1)) := fun r => eM (pV' r)
  let P : Fin m → Finset (Fin (2 ^ (s - 1))) := fun r => {pU r, pV r}
  have hpUV_ne : ∀ r, pU r ≠ pV r := fun r h => hpUV_ne' r (eM.injective h)
  have hpH_eq : ∀ r, vecHeight (d (pU r)) (hd (pU r)) = pH r ∧
                     vecHeight (d (pV r)) (hd (pV r)) = pH r := hpH_eq'
  have hP_card : ∀ r, (P r).card = 2 := fun r => Finset.card_pair (hpUV_ne r)
  have hP_disj : ∀ r₁ r₂, r₁ ≠ r₂ → Disjoint (P r₁) (P r₂) := by
    intro r₁ r₂ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : eM.symm x ∈ ({pU' r₁, pV' r₁} : Finset (Fin (2 * m))) := by
      rcases Finset.mem_insert.mp hx1 with rfl | h
      · simp [pU]
      · rw [Finset.mem_singleton.mp h]; simp [pV]
    have h2 : eM.symm x ∈ ({pU' r₂, pV' r₂} : Finset (Fin (2 * m))) := by
      rcases Finset.mem_insert.mp hx2 with rfl | h
      · simp [pU]
      · rw [Finset.mem_singleton.mp h]; simp [pV]
    exact Finset.disjoint_left.mp (hP_disj' r₁ r₂ hne) h1 h2
  have hP_cov : ∀ x : Fin (2 ^ (s - 1)), ∃ r : Fin m, x ∈ P r := by
    intro x
    rcases hP_cov' (eM.symm x) with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rcases Finset.mem_insert.mp hr with h | h
    · have hx : x = pU r := by simpa [pU] using congrArg eM h
      rw [hx]; exact Finset.mem_insert_self _ _
    · have hx : x = pV r := by simpa [pV] using congrArg eM (Finset.mem_singleton.mp h)
      rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  let Gset : ℕ → Finset (Finset (Finset (Fin (2 ^ (s - 1))))) := fun ℓ =>
    (goodTreesOn b (s - 1) Finset.univ).filter (fun N => ∀ r : Fin m, r.1 < ℓ → P r ∈ N)
  -- Lemma 5.4: `(Gset ℓ).card % 2 = (Gset (ℓ + 1)).card % 2` for `ℓ < m`.
  have hstep : ∀ (ℓ : ℕ) (hℓ : ℓ < m), (Gset ℓ).card % 2 = (Gset (ℓ + 1)).card % 2 := by
    intro ℓ hℓ
    let r₀ : Fin m := ⟨ℓ, hℓ⟩
    let u := pU r₀
    let v := pV r₀
    have huv : u ≠ v := hpUV_ne r₀
    have huv_h : vecHeight (d u) (hd u) = vecHeight (d v) (hd v) :=
      (hpH_eq r₀).1.trans (hpH_eq r₀).2.symm
    let j := vecHeight (d u) (hd u)
    have hj_eq : j = pH r₀ := (hpH_eq r₀).1
    let δ := d u + d v
    have h52 := lemma_5_2 (by omega : 1 ≤ s) d hd huv_h
    have hb_uv : b u + b v = (δ, 0) := h52.2.1
    have hsymp_ge : ∀ i, j ≤ vecHeight (d i) (hd i) → symp (δ, 0) (b i) = 0 := h52.2.2.1
    have hsymp_pair : ∀ i i', vecHeight (d i) (hd i) = vecHeight (d i') (hd i') →
        symp (δ, 0) (b i + b i') = 0 := h52.2.2.2.1
    let τ : Equiv.Perm (Fin (2 ^ (s - 1))) := Equiv.swap u v
    have hτ_invol : ∀ x, τ (τ x) = x := fun x => Equiv.swap_apply_self u v x
    have hclosed : ∀ N ∈ Gset ℓ, mapTree τ N ∈ Gset ℓ := by
      intro N hN
      simp only [Gset, goodTreesOn, Finset.mem_filter, mem_treesOn_iff] at hN ⊢
      rcases hN with ⟨⟨hNtree, hNgood⟩, hNch⟩
      have hTτ : IsTree (s - 1) Finset.univ (mapTree τ N) := mapTree_univ_mem_treesOn τ hNtree
      -- Equation (5.2): `symp (δ, 0) (bSum b C) = 0` for every node `C ∈ N` not a singleton of height `< j`.
      have heq52 : ∀ C ∈ N, (2 ≤ C.card ∨ (∃ i, C = {i} ∧ j ≤ vecHeight (d i) (hd i))) →
          symp (δ, 0) (bSum b C) = 0 := by
        intro C hCN hcond
        rcases hcond with hC2 | ⟨i, rfl, hi⟩
        · let Clow := C.filter (fun i => vecHeight (d i) (hd i) < j)
          let Chigh := C.filter (fun i => j ≤ vecHeight (d i) (hd i))
          have hCsplit : C = Clow ∪ Chigh := by
            ext i; simp only [Clow, Chigh, Finset.mem_union, Finset.mem_filter]
            constructor
            · intro hi; rcases lt_or_ge (vecHeight (d i) (hd i)) j with h | h
              · exact Or.inl ⟨hi, h⟩
              · exact Or.inr ⟨hi, h⟩
            · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
          have hCdisj : Disjoint Clow Chigh :=
            Finset.disjoint_filter.mpr (fun _ _ h1 h2 => not_lt_of_ge h2 h1)
          rw [hCsplit, bSum_union b hCdisj, symp_add_right]
          have hhigh0 : symp (δ, 0) (bSum b Chigh) = 0 := by
            rw [symp_bSum_right]
            exact Finset.sum_eq_zero (fun i hi => hsymp_ge i (Finset.mem_filter.mp hi).2)
          have hlow0 : symp (δ, 0) (bSum b Clow) = 0 := by
            let Rlow := (Finset.univ : Finset (Fin m)).filter (fun r => pH r < j ∧ P r ⊆ C)
            have hClow_eq : Clow = Rlow.biUnion P := by
              ext x
              simp only [Clow, Rlow, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨hxC, hxj⟩
                rcases hP_cov x with ⟨r, hxr⟩
                have hrh : pH r = vecHeight (d x) (hd x) := by
                  rcases Finset.mem_insert.mp hxr with rfl | h
                  · exact (hpH_eq r).1.symm
                  · rw [Finset.mem_singleton.mp h]; exact (hpH_eq r).2.symm
                have hrlt : r.1 < ℓ := by
                  by_contra hge; push Not at hge
                  have hle : pH r₀ ≤ pH r := hpH_mono (Fin.le_def.mpr hge)
                  rw [← hj_eq, hrh] at hle
                  exact not_lt_of_ge hle hxj
                have hPrN : P r ∈ N := hNch r hrlt
                have hPrSub : P r ⊆ C :=
                  IsTree.subset_of_mem_of_card_le hNtree hPrN hCN hxr hxC (by rw [hP_card r]; exact hC2)
                exact ⟨r, ⟨hrh.symm ▸ hxj, hPrSub⟩, hxr⟩
              · rintro ⟨r, ⟨hrj, hPrSub⟩, hxr⟩
                have hPr_eq : vecHeight (d x) (hd x) = pH r := by
                  rcases Finset.mem_insert.mp hxr with rfl | h
                  · exact (hpH_eq r).1
                  · rw [Finset.mem_singleton.mp h]; exact (hpH_eq r).2
                exact ⟨hPrSub hxr, hPr_eq.symm ▸ hrj⟩
            rw [hClow_eq, symp_bSum_right,
              Finset.sum_biUnion (fun r₁ _ r₂ _ hne => hP_disj r₁ r₂ hne)]
            refine Finset.sum_eq_zero (fun r _ => ?_)
            simp only [P, Finset.sum_pair (hpUV_ne r)]
            rw [← symp_add_right]
            exact hsymp_pair (pU r) (pV r) ((hpH_eq r).1.trans (hpH_eq r).2.symm)
          rw [hlow0, hhigh0, add_zero]
        · rw [bSum_singleton]; exact hsymp_ge i hi
      have hb_shift : ∀ C : Finset (Fin (2 ^ (s - 1))),
          bSum b (C.image τ) = bSum b C ∨ bSum b (C.image τ) = bSum b C + (δ, 0) := by
        intro C
        by_cases huC : u ∈ C <;> by_cases hvC : v ∈ C
        · left
          have hfix : C.image τ = C := by
            ext x; simp only [Finset.mem_image]
            constructor
            · rintro ⟨y, hy, rfl⟩
              by_cases h1 : y = u
              · subst h1; simpa [τ] using hvC
              · by_cases h2 : y = v
                · subst h2; simpa [τ] using huC
                · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
            · intro hx
              refine ⟨τ x, ?_, hτ_invol x⟩
              by_cases h1 : x = u
              · subst h1; simpa [τ] using hvC
              · by_cases h2 : x = v
                · subst h2; simpa [τ] using huC
                · rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
          rw [hfix]
        · right
          have hCimg : C.image τ = insert v (C.erase u) := by
            ext x; simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨y, hy, rfl⟩
              by_cases h1 : y = u
              · subst h1; left; simp [τ]
              · have h2 : y ≠ v := fun h => hvC (h ▸ hy)
                right; rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact ⟨h1, hy⟩
            · rintro (rfl | ⟨hxu, hxC⟩)
              · exact ⟨u, huC, by simp [τ]⟩
              · have hxv : x ≠ v := fun h => hvC (h ▸ hxC)
                exact ⟨x, hxC, Equiv.swap_apply_of_ne_of_ne hxu hxv⟩
          have hv_not_er : v ∉ C.erase u := fun h => hvC (Finset.mem_erase.mp h).2
          rw [hCimg, bSum, Finset.sum_insert hv_not_er, ← hb_uv]
          have hCu : bSum b C = b u + ∑ x ∈ C.erase u, b x := by
            simp only [bSum, Finset.add_sum_erase C b huC]
          rw [hCu]
          apply Prod.ext
          · simp only [Prod.fst_add]; ext k; simp only [Pi.add_apply]
            have h0 := zmod2_add_self ((b u).1 k)
            calc (b v).1 k + (∑ x ∈ C.erase u, b x).1 k
                = ((b u).1 k + (b u).1 k) + (b v).1 k + (∑ x ∈ C.erase u, b x).1 k := by rw [h0, zero_add]
              _ = (b u).1 k + (∑ x ∈ C.erase u, b x).1 k + ((b u).1 k + (b v).1 k) := by ring
          · simp only [Prod.snd_add]; ext k; simp only [Pi.add_apply]
            have h0 := zmod2_add_self ((b u).2 k)
            calc (b v).2 k + (∑ x ∈ C.erase u, b x).2 k
                = ((b u).2 k + (b u).2 k) + (b v).2 k + (∑ x ∈ C.erase u, b x).2 k := by rw [h0, zero_add]
              _ = (b u).2 k + (∑ x ∈ C.erase u, b x).2 k + ((b u).2 k + (b v).2 k) := by ring
        · right
          have hCimg : C.image τ = insert u (C.erase v) := by
            ext x; simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨y, hy, rfl⟩
              by_cases h2 : y = v
              · subst h2; left; simp [τ]
              · have h1 : y ≠ u := fun h => huC (h ▸ hy)
                right; rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; exact ⟨h2, hy⟩
            · rintro (rfl | ⟨hxv, hxC⟩)
              · exact ⟨v, hvC, by simp [τ]⟩
              · have hxu : x ≠ u := fun h => huC (h ▸ hxC)
                exact ⟨x, hxC, Equiv.swap_apply_of_ne_of_ne hxu hxv⟩
          have hu_not_er : u ∉ C.erase v := fun h => huC (Finset.mem_erase.mp h).2
          rw [hCimg, bSum, Finset.sum_insert hu_not_er, ← hb_uv]
          have hCv : bSum b C = b v + ∑ x ∈ C.erase v, b x := by
            simp only [bSum, Finset.add_sum_erase C b hvC]
          rw [hCv]
          apply Prod.ext
          · simp only [Prod.fst_add]; ext k; simp only [Pi.add_apply]
            have h0 := zmod2_add_self ((b v).1 k)
            calc (b u).1 k + (∑ x ∈ C.erase v, b x).1 k
                = ((b v).1 k + (b v).1 k) + (b u).1 k + (∑ x ∈ C.erase v, b x).1 k := by rw [h0, zero_add]
              _ = (b v).1 k + (∑ x ∈ C.erase v, b x).1 k + ((b u).1 k + (b v).1 k) := by ring
          · simp only [Prod.snd_add]; ext k; simp only [Pi.add_apply]
            have h0 := zmod2_add_self ((b v).2 k)
            calc (b u).2 k + (∑ x ∈ C.erase v, b x).2 k
                = ((b v).2 k + (b v).2 k) + (b u).2 k + (∑ x ∈ C.erase v, b x).2 k := by rw [h0, zero_add]
              _ = (b v).2 k + (∑ x ∈ C.erase v, b x).2 k + ((b u).2 k + (b v).2 k) := by ring
        · left
          have hfix : C.image τ = C := by
            ext x; simp only [Finset.mem_image]
            constructor
            · rintro ⟨y, hy, rfl⟩
              have h1 : y ≠ u := fun h => huC (h ▸ hy)
              have h2 : y ≠ v := fun h => hvC (h ▸ hy)
              rwa [Equiv.swap_apply_of_ne_of_ne h1 h2]
            · intro hx
              have h1 : x ≠ u := fun h => huC (h ▸ hx)
              have h2 : x ≠ v := fun h => hvC (h ▸ hx)
              exact ⟨x, hx, Equiv.swap_apply_of_ne_of_ne h1 h2⟩
          rw [hfix]
      -- Goodness of `mapTree τ N`:
      refine ⟨⟨hTτ, ?_⟩, ?_⟩
      · intro D₁ hD₁ D₂ hD₂ hDdisj hDcard hDunion
        rcases Finset.mem_image.mp hD₁ with ⟨C₁, hC₁N, rfl⟩
        rcases Finset.mem_image.mp hD₂ with ⟨C₂, hC₂N, rfl⟩
        have hCdisj : Disjoint C₁ C₂ := by
          rw [Finset.disjoint_left]; intro x hx1 hx2
          exact Finset.disjoint_left.mp hDdisj (Finset.mem_image_of_mem τ hx1)
            (Finset.mem_image_of_mem τ hx2)
        have hCcard : C₁.card = C₂.card := by
          simpa only [Finset.card_image_of_injective _ τ.injective] using hDcard
        have hCunion : C₁ ∪ C₂ ∈ N := by
          rcases Finset.mem_image.mp hDunion with ⟨C, hCN, hCeq⟩
          have hinv : C₁ ∪ C₂ = C := by
            have h1 := congrArg (fun E => E.image τ) hCeq
            have hinv' : ∀ E : Finset (Fin (2 ^ (s - 1))), (E.image τ).image τ = E := fun E => by
              ext x; simp only [Finset.mem_image]
              constructor
              · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; simpa [hτ_invol] using hy
              · intro hx; exact ⟨τ x, ⟨x, hx, rfl⟩, hτ_invol x⟩
            rw [Finset.image_union] at h1
            simpa only [hinv'] using h1.symm
          rwa [hinv]
        have hgoodC : symp (bSum b C₁) (bSum b C₂) = 0 := hNgood C₁ hC₁N C₂ hC₂N hCdisj hCcard hCunion
        -- Helper: if `C` contains `u` or `v` (not both), then its sibling `C'` cannot be a singleton of height `< j`.
        have hsib_ok : ∀ {X Y : Finset (Fin (2 ^ (s - 1)))},
            X ∈ N → Y ∈ N → Disjoint X Y → X.card = Y.card → X ∪ Y ∈ N →
            bSum b (X.image τ) ≠ bSum b X → symp (δ, 0) (bSum b Y) = 0 := by
          intro X Y hXN hYN hXYd hXYc hXYu hshift
          refine heq52 Y hYN ?_
          rcases IsTree.card_pow_le hNtree Y hYN with ⟨my, _, hmyc⟩
          cases my with
          | zero =>
            right
            rw [pow_zero] at hmyc
            rcases Finset.card_eq_one.mp hmyc with ⟨i, rfl⟩
            refine ⟨i, rfl, ?_⟩
            by_contra hlt; push Not at hlt
            rcases hP_cov i with ⟨r, hir⟩
            have hrh : pH r = vecHeight (d i) (hd i) := by
              rcases Finset.mem_insert.mp hir with rfl | h
              · exact (hpH_eq r).1.symm
              · rw [Finset.mem_singleton.mp h]; exact (hpH_eq r).2.symm
            have hrlt : r.1 < ℓ := by
              by_contra hge; push Not at hge
              have hle : pH r₀ ≤ pH r := hpH_mono (Fin.le_def.mpr hge)
              rw [← hj_eq, hrh] at hle
              exact not_lt_of_ge hle hlt
            have hPrN : P r ∈ N := hNch r hrlt
            have hXY2 : (X ∪ {i}).card = 2 := by
              rw [Finset.card_union_of_disjoint hXYd, hXYc, Finset.card_singleton]
            have hXY_eq_Pr : X ∪ {i} = P r :=
              IsTree.eq_of_mem_of_card_eq hNtree hXYu hPrN
                (Finset.mem_union_right _ (Finset.mem_singleton_self i)) hir
                (by rw [hXY2, hP_card r])
            have hXsub : X ⊆ P r := hXY_eq_Pr ▸ Finset.subset_union_left
            have hrne0 : r₀ ≠ r := fun h => by
              have hval : r₀.val = r.val := congrArg Fin.val h
              simp only [r₀] at hval; omega
            have hu_not : u ∉ P r := Finset.disjoint_left.mp (hP_disj r₀ r hrne0)
              (Finset.mem_insert_self u {v})
            have hv_not : v ∉ P r := Finset.disjoint_left.mp (hP_disj r₀ r hrne0)
              (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
            have hXfix : X.image τ = X := by
              ext x; simp only [Finset.mem_image]
              constructor
              · rintro ⟨y, hy, rfl⟩
                have hyu : y ≠ u := fun h => hu_not (hXsub (h ▸ hy))
                have hyv : y ≠ v := fun h => hv_not (hXsub (h ▸ hy))
                rwa [Equiv.swap_apply_of_ne_of_ne hyu hyv]
              · intro hx
                have hxu : x ≠ u := fun h => hu_not (hXsub (h ▸ hx))
                have hxv : x ≠ v := fun h => hv_not (hXsub (h ▸ hx))
                exact ⟨x, hx, Equiv.swap_apply_of_ne_of_ne hxu hxv⟩
            exact hshift (by rw [hXfix])
          | succ my' =>
            left; rw [hmyc, pow_succ']; have := Nat.one_le_pow my' 2 (by norm_num); omega
        by_cases h1eq : bSum b (C₁.image τ) = bSum b C₁
        · by_cases h2eq : bSum b (C₂.image τ) = bSum b C₂
          · rw [h1eq, h2eq, hgoodC]
          · have h2s : bSum b (C₂.image τ) = bSum b C₂ + (δ, 0) := (hb_shift C₂).resolve_left h2eq
            have h0 := hsib_ok hC₂N hC₁N hCdisj.symm hCcard.symm
              (by rw [Finset.union_comm]; exact hCunion) h2eq
            rw [h1eq, h2s, symp_add_right, hgoodC, zero_add, symp_symm, h0]
        · have h1s : bSum b (C₁.image τ) = bSum b C₁ + (δ, 0) := (hb_shift C₁).resolve_left h1eq
          have h01 := hsib_ok hC₁N hC₂N hCdisj hCcard hCunion h1eq
          by_cases h2eq : bSum b (C₂.image τ) = bSum b C₂
          · rw [h1s, h2eq, symp_add_left, hgoodC, h01, add_zero]
          · have h2s : bSum b (C₂.image τ) = bSum b C₂ + (δ, 0) := (hb_shift C₂).resolve_left h2eq
            have h02 := hsib_ok hC₂N hC₁N hCdisj.symm hCcard.symm
              (by rw [Finset.union_comm]; exact hCunion) h2eq
            rw [h1s, h2s, symp_add_left, symp_add_right, symp_add_right,
              hgoodC, symp_symm (bSum b C₁) (δ, 0), h02, h01, symp_self]
            decide
      · intro r hr
        have hrne : r ≠ r₀ := fun h => by
          have hval : r.val = r₀.val := congrArg Fin.val h
          simp only [r₀] at hval; omega
        have hu_not : u ∉ P r := Finset.disjoint_left.mp (hP_disj r₀ r hrne.symm)
          (Finset.mem_insert_self u {v})
        have hv_not : v ∉ P r := Finset.disjoint_left.mp (hP_disj r₀ r hrne.symm)
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
        have hPr_fix : (P r).image τ = P r := by
          ext x; simp only [Finset.mem_image]
          constructor
          · rintro ⟨y, hy, rfl⟩
            have hyu : y ≠ u := fun h => hu_not (h ▸ hy)
            have hyv : y ≠ v := fun h => hv_not (h ▸ hy)
            rwa [Equiv.swap_apply_of_ne_of_ne hyu hyv]
          · intro hx
            have hxu : x ≠ u := fun h => hu_not (h ▸ hx)
            have hxv : x ≠ v := fun h => hv_not (h ▸ hx)
            exact ⟨x, hx, Equiv.swap_apply_of_ne_of_ne hxu hxv⟩
        rw [← hPr_fix]
        exact Finset.mem_image_of_mem _ (hNch r hr)
    have hfix_set : (Gset ℓ).filter (fun N => mapTree τ N = N) = Gset (ℓ + 1) := by
      ext N
      simp only [Gset, goodTreesOn, Finset.mem_filter, mem_treesOn_iff]
      constructor
      · rintro ⟨⟨⟨hNtree, hNgood⟩, hNch⟩, hfix⟩
        have hP0 : P r₀ ∈ N := (mapTree_swap_eq_iff (by omega : 1 ≤ s - 1) hNtree huv).mp hfix
        refine ⟨⟨hNtree, hNgood⟩, fun r hr => ?_⟩
        by_cases hlt : r.1 < ℓ
        · exact hNch r hlt
        · have heq : r = r₀ := Fin.ext (by simp only [r₀]; omega)
          rw [heq]; exact hP0
      · rintro ⟨⟨hNtree, hNgood⟩, hNch⟩
        refine ⟨⟨⟨hNtree, hNgood⟩, fun r hr => hNch r (by omega)⟩, ?_⟩
        exact (mapTree_swap_eq_iff (by omega : 1 ≤ s - 1) hNtree huv).mpr
          (hNch r₀ (by simp only [r₀]; omega))
    rw [← hfix_set]
    exact card_mod_two_eq_fixed_of_invol (Gset ℓ) (mapTree τ) hclosed
      (fun N _ => mapTree_invol hτ_invol N)
  -- Chain `hstep` from `0` to `m`:
  have hchain : ∀ k ≤ m, (Gset 0).card % 2 = (Gset k).card % 2 := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih => rw [ih (by omega), hstep k (by omega)]
  -- Lemma 5.5: Every tree with all `P r` as cherries is good, and `Gset m ≃ treesOn (s - 2) univ`.
  have hGset_m_eq : Gset m = (treesOn (s - 1) Finset.univ).filter (fun N => ∀ r : Fin m, P r ∈ N) := by
    ext N
    simp only [Gset, goodTreesOn, Finset.mem_filter, mem_treesOn_iff]
    constructor
    · rintro ⟨⟨hT, _⟩, hP⟩; exact ⟨hT, fun r => hP r r.2⟩
    · rintro ⟨hT, hP⟩
      refine ⟨⟨hT, ?_⟩, fun r _ => hP r⟩
      intro C₁ hC₁ C₂ hC₂ hCdisj hCcard hCunion
      rcases IsTree.card_pow_le hT C₁ hC₁ with ⟨m1, _, hm1c⟩
      cases m1 with
      | zero =>
        rw [pow_zero] at hm1c
        rcases Finset.card_eq_one.mp hm1c with ⟨x₁, rfl⟩
        rcases Finset.card_eq_one.mp (hCcard.symm.trans hm1c) with ⟨x₂, rfl⟩
        rcases hP_cov x₁ with ⟨r, hx₁r⟩
        have hUcard : ({x₁} ∪ {x₂} : Finset (Fin (2 ^ (s - 1)))).card = 2 := by
          rw [Finset.card_union_of_disjoint hCdisj, Finset.card_singleton, Finset.card_singleton]
        have hUeq : ({x₁} ∪ {x₂} : Finset (Fin (2 ^ (s - 1)))) = P r :=
          IsTree.eq_of_mem_of_card_eq hT hCunion (hP r)
            (Finset.mem_union_left _ (Finset.mem_singleton_self x₁)) hx₁r
            (by rw [hUcard, hP_card r])
        have h52r := lemma_5_2 (by omega : 1 ≤ s) d hd ((hpH_eq r).1.trans (hpH_eq r).2.symm)
        have hx₁_in : x₁ ∈ ({pU r, pV r} : Finset _) := by
          change x₁ ∈ P r; rw [← hUeq]; exact Finset.mem_union_left _ (Finset.mem_singleton_self x₁)
        have hx₂_in : x₂ ∈ ({pU r, pV r} : Finset _) := by
          change x₂ ∈ P r; rw [← hUeq]; exact Finset.mem_union_right _ (Finset.mem_singleton_self x₂)
        have hne12 : x₁ ≠ x₂ := Finset.disjoint_singleton.mp hCdisj
        simp only [bSum_singleton]
        rcases Finset.mem_insert.mp hx₁_in with rfl | h1
        · rcases Finset.mem_insert.mp hx₂_in with h2 | h2
          · exact absurd h2.symm hne12
          · rw [Finset.mem_singleton.mp h2]; exact h52r.2.2.2.2
        · rw [Finset.mem_singleton.mp h1] at hne12 ⊢
          rcases Finset.mem_insert.mp hx₂_in with rfl | h2
          · rw [symp_symm]; exact h52r.2.2.2.2
          · exact absurd (Finset.mem_singleton.mp h2).symm hne12
      | succ m1' =>
        have h2le1 : 2 ≤ C₁.card := by
          rw [hm1c, pow_succ']; have := Nat.one_le_pow m1' 2 (by norm_num); omega
        have h2le2 : 2 ≤ C₂.card := hCcard ▸ h2le1
        have hsnd0 : ∀ C ∈ N, 2 ≤ C.card → (bSum b C).2 = 0 := by
          intro C hCN hC2
          let RC := (Finset.univ : Finset (Fin m)).filter (fun r => P r ⊆ C)
          have hCeq : C = RC.biUnion P := by
            ext x; simp only [RC, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hxC
              rcases hP_cov x with ⟨r, hxr⟩
              exact ⟨r, IsTree.subset_of_mem_of_card_le hT (hP r) hCN hxr hxC (by rw [hP_card r]; exact hC2), hxr⟩
            · rintro ⟨r, hsub, hxr⟩; exact hsub hxr
          rw [hCeq, bSum, Finset.sum_biUnion (fun r₁ _ r₂ _ hne => hP_disj r₁ r₂ hne)]
          rw [Prod.snd_sum]
          refine Finset.sum_eq_zero (fun r _ => ?_)
          simp only [P, Finset.sum_pair (hpUV_ne r)]
          have h52r := lemma_5_2 (by omega : 1 ≤ s) d hd ((hpH_eq r).1.trans (hpH_eq r).2.symm)
          exact congrArg Prod.snd h52r.2.1
        have heq1 : bSum b C₁ = ((bSum b C₁).1, 0) := Prod.ext rfl (hsnd0 C₁ hC₁ h2le1)
        have heq2 : bSum b C₂ = ((bSum b C₂).1, 0) := Prod.ext rfl (hsnd0 C₂ hC₂ h2le2)
        rw [heq1, heq2, symp_fst_zero, dot2_zero_left]
  -- Bijection between `Gset m` and `treesOn (s - 2) (Finset.univ : Finset (Fin m))`:
  have hbiU : (Finset.univ : Finset (Fin m)).biUnion P = Finset.univ := by
    ext x; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]; exact hP_cov x
  have hcard_Gm : (Gset m).card = (treesOn (s - 2) (Finset.univ : Finset (Fin m))).card := by
    rw [hGset_m_eq]
    refine Finset.card_bij
      (fun N _ => (N.filter (fun C => 2 ≤ C.card)).image
        (fun C => (Finset.univ : Finset (Fin m)).filter (fun r => P r ⊆ C)))
      ?_ ?_ ?_
    · intro N hN
      simp only [Finset.mem_filter, mem_treesOn_iff] at hN ⊢
      have hN' : IsTree ((s - 2) + 1) ((Finset.univ : Finset (Fin m)).biUnion P) N := by
        rw [hbiU, show (s - 2) + 1 = s - 1 by omega]; exact hN.1
      exact collapse_isTree P hP_card hP_disj (s - 2) Finset.univ N hN' (fun r _ => hN.2 r)
    · intro N₁ hN₁ N₂ hN₂ hEq
      simp only [Finset.mem_filter, mem_treesOn_iff] at hN₁ hN₂
      have hreconst : ∀ N : Finset (Finset (Fin (2 ^ (s - 1)))),
          IsTree (s - 1) Finset.univ N → (∀ r : Fin m, P r ∈ N) →
          N = ((N.filter (fun C => 2 ≤ C.card)).image
                (fun C => (Finset.univ : Finset (Fin m)).filter (fun r => P r ⊆ C))).image
                (fun E => E.biUnion P) ∪
              (Finset.univ : Finset (Fin (2 ^ (s - 1)))).image (fun x => {x}) := by
        intro N hTN hPN
        ext C
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hCN
          rcases IsTree.card_pow_le hTN C hCN with ⟨mc, _, hmc⟩
          cases mc with
          | zero =>
            rw [pow_zero] at hmc
            rcases Finset.card_eq_one.mp hmc with ⟨x, rfl⟩
            exact Or.inr ⟨x, rfl⟩
          | succ mc' =>
            have hC2 : 2 ≤ C.card := by
              rw [hmc, pow_succ']; have := Nat.one_le_pow mc' 2 (by norm_num); omega
            left
            refine ⟨(Finset.univ : Finset (Fin m)).filter (fun r => P r ⊆ C),
              ⟨C, ⟨hCN, hC2⟩, rfl⟩, ?_⟩
            ext x; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨r, hsub, hxr⟩; exact hsub hxr
            · intro hxC
              rcases hP_cov x with ⟨r, hxr⟩
              exact ⟨r, IsTree.subset_of_mem_of_card_le hTN (hPN r) hCN hxr hxC
                (by rw [hP_card r]; exact hC2), hxr⟩
        · rintro (⟨_, ⟨D, ⟨hDN, hD2⟩, rfl⟩, rfl⟩ | ⟨x, rfl⟩)
          · have hDeq : ((Finset.univ : Finset (Fin m)).filter (fun r => P r ⊆ D)).biUnion P = D := by
              ext x; simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨r, hsub, hxr⟩; exact hsub hxr
              · intro hxD
                rcases hP_cov x with ⟨r, hxr⟩
                exact ⟨r, IsTree.subset_of_mem_of_card_le hTN (hPN r) hDN hxr hxD
                  (by rw [hP_card r]; exact hD2), hxr⟩
            rwa [hDeq]
          · exact IsTree.singleton_mem hTN (Finset.mem_univ x)
      rw [hreconst N₁ hN₁.1 hN₁.2, hreconst N₂ hN₂.1 hN₂.2, hEq]
    · intro M hM
      rw [mem_treesOn_iff] at hM
      let N := (M.image (fun E => E.biUnion P)) ∪ (Finset.univ : Finset (Fin (2 ^ (s - 1)))).image (fun x => {x})
      have hexp := expand_isTree P hP_card hP_disj (s - 2) Finset.univ M hM
      rw [hbiU, show (s - 2) + 1 = s - 1 by omega] at hexp
      refine ⟨N, Finset.mem_filter.mpr ⟨mem_treesOn_iff.mpr hexp.1, fun r => hexp.2 r (Finset.mem_univ r)⟩, ?_⟩
      ext E
      simp only [Finset.mem_image, Finset.mem_filter, N, Finset.mem_union, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨C, ⟨⟨E', hE'M, rfl⟩ | ⟨x, rfl⟩, hC2⟩, rfl⟩
        · have hEeq : (Finset.univ : Finset (Fin m)).filter (fun r => P r ⊆ E'.biUnion P) = E' := by
            ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hsub
              rcases Finset.card_pos.mp (by rw [hP_card r]; omega : 0 < (P r).card) with ⟨x, hxr⟩
              rcases Finset.mem_biUnion.mp (hsub hxr) with ⟨r', hr', hxr'⟩
              have heq : r = r' := by
                by_contra hne; exact Finset.disjoint_left.mp (hP_disj r r' hne) hxr hxr'
              rwa [heq]
            · intro hr x hxr; exact Finset.mem_biUnion.mpr ⟨r, hr, hxr⟩
          rwa [hEeq]
        · simp at hC2
      · intro hEM
        have hEne : E.Nonempty := Finset.card_pos.mp (IsTree.card_pos hM hEM)
        have hC2 : 2 ≤ (E.biUnion P).card := by
          rcases hEne with ⟨r, hr⟩
          have : P r ⊆ E.biUnion P := fun x hx => Finset.mem_biUnion.mpr ⟨r, hr, hx⟩
          calc 2 = (P r).card := (hP_card r).symm
            _ ≤ (E.biUnion P).card := Finset.card_le_card this
        refine ⟨E.biUnion P, ⟨Or.inl ⟨E, hEM, rfl⟩, hC2⟩, ?_⟩
        ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hsub
          rcases Finset.card_pos.mp (by rw [hP_card r]; omega : 0 < (P r).card) with ⟨x, hxr⟩
          rcases Finset.mem_biUnion.mp (hsub hxr) with ⟨r', hr', hxr'⟩
          have heq : r = r' := by
            by_contra hne; exact Finset.disjoint_left.mp (hP_disj r r' hne) hxr hxr'
          rwa [heq]
        · intro hr x hxr; exact Finset.mem_biUnion.mpr ⟨r, hr, hxr⟩
  have hodd_Gm : Odd (Gset m).card := by
    rw [hcard_Gm]
    exact odd_card_treesOn (s - 2) Finset.univ (by simp [m])
  have hG0 : Gset 0 = goodTreesOn b (s - 1) Finset.univ := by
    ext N; simp [Gset]
  rw [Nat.odd_iff, ← hG0, hchain m le_rfl]
  exact Nat.odd_iff.mp hodd_Gm

end GoodTreeParity

end PartC

/-- Bridge Theorem 1 (Lemma 2.3): existence of a linear automorphism of `𝔽₂ s` putting any
    `2 ^ (s - 1)` nonzero vectors into standard-basis even-flag position. -/
theorem exists_even_basis {s : ℕ} (hs : 2 ≤ s) (v : Fin (2 ^ (s - 1)) → 𝔽₂ s)
    (hv : ∀ i, v i ≠ 0) :
    ∃ φ : 𝔽₂ s ≃ₗ[ZMod 2] 𝔽₂ s,
      IsEvenBasis (fun i => φ (v i)) (fun i => by simp [hv i]) := by
  have heven : Even (Fintype.card (Fin (2 ^ (s - 1)))) := by
    rw [Fintype.card_fin, show s - 1 = (s - 2) + 1 by omega, pow_succ']
    exact even_two_mul _
  rcases PartC.exists_even_basis_aux s heven v hv with ⟨φ, hφ⟩
  exact ⟨φ, hφ⟩

/-- Bridge Theorem 2 (Proposition 5.1): for any `s ≥ 2` and any even-basis list of `2 ^ (s - 1)`
    nonzero vectors in `𝔽₂ s`, the number of good binary trees is odd. -/
theorem odd_card_goodTreesOn {s : ℕ} (hs : 2 ≤ s)
    (d : Fin (2 ^ (s - 1)) → 𝔽₂ s) (hd : ∀ i, d i ≠ 0) (heven : IsEvenBasis d hd) :
    Odd (goodTreesOn (bClass (by omega : 1 ≤ s) d hd) (s - 1) Finset.univ).card :=
  PartC.odd_card_goodTreesOn_aux hs d hd heven

end OMA.BGS

namespace OMA.BGS

/-- **Balister–Győri–Schelp Conjecture** (proved via Zabokritskiy, arXiv:2611.32557):
for every `s ≥ 2` and every list `v : Fin (2^(s-1)) → 𝔽₂ s` of nonzero vectors summing to `0`,
there exists a perfect matching `e : Fin (2^(s-1)) × Fin 2 ≃ 𝔽₂ s` with
`e (i, 0) + e (i, 1) = v i` for all `i`. -/
theorem balister_gyori_schelp_proof (s : ℕ) (hs : 2 ≤ s)
    (v : Fin (2 ^ (s - 1)) → 𝔽₂ s)
    (hv_nonzero : ∀ i, v i ≠ 0)
    (hv_sum : ∑ i, v i = 0) :
    ∃ e : Fin (2 ^ (s - 1)) × Fin 2 ≃ 𝔽₂ s,
      ∀ i, e (i, 0) + e (i, 1) = v i := by
  obtain ⟨φ, heven⟩ := exists_even_basis hs v hv_nonzero
  let d : Fin (2 ^ (s - 1)) → 𝔽₂ s := fun i => φ (v i)
  have hd : ∀ i, d i ≠ 0 := fun i => by simp [d, hv_nonzero i]
  have hd_sum : ∑ i, d i = 0 := by simp [d, ← map_sum, hv_sum]
  have hodd := odd_card_goodTreesOn hs d hd heven
  have hprop := fun S hne hnu => Lcoeff_proper_val2Ge hs d hd S hne hnu
  have huniv := Lcoeff_univ_val2Eq hs d hd hd_sum heven hodd
  obtain ⟨e', he'⟩ := exists_realization_of_Lcoeff_valuation hs d hd hprop huniv
  refine ⟨e'.trans φ.symm.toEquiv, fun i => ?_⟩
  simp only [Equiv.trans_apply, LinearEquiv.coe_toEquiv]
  rw [← map_add, he' i]
  simp [d]

end OMA.BGS

theorem OMA.solution : type_of% @Arxiv.«2607.08630».balister_gyori_schelp_conjecture := by
  intro s hs v hv_nonzero hv_sum
  exact OMA.BGS.balister_gyori_schelp_proof s hs v hv_nonzero hv_sum
