import FormalConjectures.Wikipedia.Koethe
import Mathlib

/-! A construction of a nil ideal with a nonnil matrix ideal. -/

namespace KoetheDisproof

open scoped BigOperators
open MvPolynomial

noncomputable section

abbrev K := AlgebraicClosure ℚ

section CommonZero

variable {h : ℕ}

abbrev E (h : ℕ) := (Fin h × Fin 3) →₀ ℕ
abbrev P (h : ℕ) := MvPolynomial (Fin h × Fin 3) K

def degree (d : E h) (b : Fin h) : ℕ := ∑ j, d (b, j)

@[simp] theorem degree_zero (b : Fin h) : degree 0 b = 0 := by
  simp [degree]

@[simp] theorem degree_add (a d : E h) (b : Fin h) :
    degree (a + d) b = degree a b + degree d b := by
  simp [degree, Finsupp.add_apply, Finset.sum_add_distrib]

def Balanced (d : E h) : Prop := ∃ t : ℕ, ∀ b, degree d b = t

theorem balanced_zero : Balanced (0 : E h) := ⟨0, by simp⟩

theorem balanced_add {a d : E h} (ha : Balanced a) (hd : Balanced d) :
    Balanced (a + d) := by
  obtain ⟨t, ht⟩ := ha
  obtain ⟨u, hu⟩ := hd
  exact ⟨t + u, fun b => by rw [degree_add, ht, hu]⟩

theorem balanced_cancel {a d : E h} (ha : Balanced a) (had : Balanced (a + d)) :
    Balanced d := by
  obtain ⟨t, ht⟩ := ha
  obtain ⟨u, hu⟩ := had
  refine ⟨u - t, fun b => ?_⟩
  specialize ht b
  specialize hu b
  rw [degree_add] at hu
  omega

def Supported (T : E h → Prop) (p : P h) : Prop :=
  ∀ d, coeff d p ≠ 0 → T d

theorem supported_monomial {T : E h → Prop} {d : E h} (hd : T d) (c : K) :
    Supported T (monomial d c) := by
  intro e he
  by_cases hde : d = e
  · exact hde ▸ hd
  · classical
    exact (he (by simp [coeff_monomial, hde])).elim

theorem supported_C {T : E h → Prop} (hT : T 0) (c : K) :
    Supported T (C c) := supported_monomial hT c

theorem supported_add {T : E h → Prop} {a b : P h}
    (ha : Supported T a) (hb : Supported T b) : Supported T (a + b) := by
  intro d hd
  classical
  by_cases he : coeff d a = 0
  · exact hb d (by simpa [he] using hd)
  · exact ha d he

theorem supported_sum {ι : Type*} {T : E h → Prop}
    (s : Finset ι) (p : ι → P h) (hp : ∀ i ∈ s, Supported T (p i)) :
    Supported T (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Supported]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact supported_add (hp a (Finset.mem_insert_self _ _))
      (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))

theorem supported_mul {S T U : E h → Prop} {a b : P h}
    (ha : Supported S a) (hb : Supported T b)
    (hU : ∀ d e, S d → T e → U (d + e)) : Supported U (a * b) := by
  classical
  intro d hd
  by_contra hn
  apply hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro (e, f) hef
  have hdf : e + f = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
  by_cases he : coeff e a = 0
  · simp [he]
  by_cases hf : coeff f b = 0
  · simp [hf]
  exact (hn (hdf ▸ hU e f (ha e he) (hb f hf))).elim

def chooseExp (w : Fin h → Fin 3) : E h :=
  Finsupp.equivFunOnFinite.symm (fun x => if x.2 = w x.1 then 1 else 0)

@[simp] theorem chooseExp_apply (w : Fin h → Fin 3) (b : Fin h) (j : Fin 3) :
    chooseExp w (b,j) = if j = w b then 1 else 0 := by
  exact congrFun ((Finsupp.equivFunOnFinite (α := Fin h × Fin 3) (M := ℕ)).apply_symm_apply
    (fun x => if x.2 = w x.1 then 1 else 0)) (b,j)

@[simp] theorem chooseExp_degree (w : Fin h → Fin 3) (b : Fin h) :
    degree (chooseExp w) b = 1 := by
  simp [degree]

def segre (w : Fin h → Fin 3) : P h := monomial (chooseExp w) 1

def diagonal (h : ℕ) : Subalgebra K (P h) := Algebra.adjoin K (Set.range segre)

theorem segre_mem (w : Fin h → Fin 3) : segre w ∈ diagonal h :=
  Algebra.subset_adjoin ⟨w, rfl⟩

theorem diagonal_supported {p : P h} (hp : p ∈ diagonal h) :
    Supported Balanced p := by
  refine Algebra.adjoin_induction (p := fun a _ => Supported Balanced a) ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨w, rfl⟩
    exact supported_monomial ⟨1, chooseExp_degree w⟩ _
  · exact supported_C balanced_zero
  · exact fun _ _ _ _ hx hy => supported_add hx hy
  · exact fun _ _ _ _ hx hy => supported_mul hx hy fun _ _ => balanced_add

theorem chooseExp_le {d : E h} {t : ℕ} (ht : 0 < t)
    (hd : ∀ b, degree d b = t) :
    ∃ w : Fin h → Fin 3, chooseExp w ≤ d := by
  classical
  have hw (b : Fin h) : ∃ j, 0 < d (b,j) := by
    by_contra! hz
    have : degree d b = 0 := Finset.sum_eq_zero fun j _ => by have := hz j; omega
    rw [hd b] at this
    omega
  choose w hw using hw
  refine ⟨w, Finsupp.le_def.mpr ?_⟩
  rintro ⟨b,j⟩
  rw [chooseExp_apply]
  split
  · subst j
    exact hw b
  · exact Nat.zero_le _

theorem degree_tsub (a d : E h) (had : a ≤ d) (b : Fin h) :
    degree (d - a) b + degree a b = degree d b := by
  rw [← degree_add, tsub_add_cancel_of_le had]

theorem diagonal_monomial {d : E h} (hd : Balanced d) (c : K) :
    monomial d c ∈ diagonal h := by
  obtain ⟨t, hd⟩ := hd
  induction t generalizing d with
  | zero =>
    have he : d = 0 := by
      ext ⟨b,j⟩
      have hj := Finset.single_le_sum (f := fun j => d (b,j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
      exact Nat.eq_zero_of_le_zero (hd b ▸ hj)
    subst d
    exact (diagonal h).algebraMap_mem c
  | succ t ih =>
    obtain ⟨w, hw⟩ := chooseExp_le (Nat.succ_pos _) hd
    have hh (b) : degree (d - chooseExp w) b = t := by
      have := degree_tsub _ _ hw b
      rw [chooseExp_degree, hd] at this
      omega
    have he : segre w * monomial (d - chooseExp w) c = monomial d c := by
      rw [segre, monomial_mul, one_mul, add_comm, tsub_add_cancel_of_le hw]
    rw [← he]
    exact mul_mem (segre_mem w) (ih hh)

theorem supported_diagonal {p : P h} (hp : Supported Balanced p) : p ∈ diagonal h := by
  have hs : (∑ d ∈ p.support, monomial d (coeff d p)) ∈ diagonal h :=
    sum_mem fun d hd => diagonal_monomial (hp d (mem_support_iff.mp hd)) _
  exact p.as_sum.symm ▸ hs

def projection (p : P h) : P h := by
  classical
  exact AddMonoidAlgebra.ofCoeff (Finsupp.filter Balanced (AddMonoidAlgebra.coeff p))

@[simp] theorem coeff_projection (p : P h) (d : E h) :
    coeff d (projection p) = @ite K (Balanced d) (Classical.propDecidable _) (coeff d p) 0 := by
  exact @Finsupp.filter_apply _ _ _ _ (Classical.decPred _) _ _

theorem projection_mem (p : P h) : projection p ∈ diagonal h := by
  apply supported_diagonal
  intro d hd
  classical
  by_contra hn
  simp [hn] at hd

theorem projection_fix {p : P h} (hp : p ∈ diagonal h) : projection p = p := by
  ext d
  classical
  by_cases hd : Balanced d
  · simp [hd]
  · have he : coeff d p = 0 := by by_contra he; exact hd (diagonal_supported hp d he)
    simp [hd, he]

theorem projection_add (a b : P h) : projection (a + b) = projection a + projection b := by
  ext d
  classical
  by_cases hd : Balanced d <;> simp [hd, coeff_add]

theorem projection_mul {a : P h} (ha : a ∈ diagonal h) (b : P h) :
    projection (a * b) = a * projection b := by
  classical
  ext d
  rw [coeff_projection, coeff_mul, coeff_mul]
  by_cases hd : Balanced d
  · rw [if_pos hd]
    refine Finset.sum_congr rfl ?_
    intro (e,f) hef
    have he : e + f = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
    by_cases hz : coeff e a = 0
    · simp [hz]
    have hf := balanced_cancel (diagonal_supported ha e hz) (he.symm ▸ hd)
    simp [hf]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro (e,f) hef
    have he : e + f = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
    by_cases hz : coeff e a = 0
    · simp [hz]
    have hf : ¬ Balanced f := fun hf =>
      hd (he ▸ balanced_add (diagonal_supported ha e hz) hf)
    simp [hf]

theorem diagonal_contract (J : Ideal (diagonal h)) (x : diagonal h)
    (hx : x.1 ∈ J.map (diagonal h).val.toRingHom) : x ∈ J := by
  let pr : P h →ₗ[diagonal h] diagonal h :=
    { toFun := fun p => ⟨projection p, projection_mem p⟩
      map_add' := fun a b => Subtype.ext (projection_add a b)
      map_smul' := fun a b => Subtype.ext (projection_mul a.property b) }
  have hp (p : P h) (hp : p ∈ J.map (diagonal h).val.toRingHom) :
      ∀ a : P h, pr (a * p) ∈ J := by
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨y, hy, rfl⟩ := hp
      intro a
      rw [show a * (diagonal h).val.toRingHom y = y • a from mul_comm _ _,
        map_smul, smul_eq_mul]
      exact J.mul_mem_right _ hy
    | zero => simp
    | add p q _ _ hp hq =>
      intro a
      rw [mul_add, map_add]
      exact J.add_mem (hp a) (hq a)
    | smul a p _ hp =>
      intro b
      exact (mul_assoc b a p) ▸ hp (b * a)
  have hy := hp _ hx 1
  rw [one_mul, show pr x.1 = x from Subtype.ext (projection_fix x.property)] at hy
  exact hy

theorem segre_prod (w : Fin h → Fin 3) :
    segre w = ∏ b, (X (b, w b) : P h) := by
  rw [segre, monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp [chooseExp_apply]

def variableIndex (x : Fin h × Fin 3) : ℕ :=
  if x.2 = 0 then 2 * h else 2 * x.1.val + (x.2.val - 1)

theorem variableIndex_le (x : Fin h × Fin 3) : variableIndex x ≤ 2 * h := by
  unfold variableIndex
  have hb := x.1.isLt
  have hj := x.2.isLt
  split <;> omega

def mask (i : ℕ) (x : Fin h × Fin 3) : P h :=
  if variableIndex x < i then 0 else X x

def cutoff (h i : ℕ) : Ideal (diagonal h) :=
  RingHom.ker ((bind₁ (mask i : Fin h × Fin 3 → P h)).toRingHom.comp (diagonal h).val.toRingHom)

instance cutoff_prime (i : ℕ) : (cutoff h i).IsPrime := RingHom.ker_isPrime _

theorem cutoff_mono {i j : ℕ} (hij : i ≤ j) : cutoff h i ≤ cutoff h j := by
  have hc : (bind₁ (mask j : Fin h × Fin 3 → P h)).comp (bind₁ (mask i)) = bind₁ (mask j) := by
    apply MvPolynomial.algHom_ext
    intro x
    by_cases hi : variableIndex x < i
    · simp [mask, hi, lt_of_lt_of_le hi hij]
    · simp [mask, hi]
  intro p hp
  change bind₁ (mask i) p.1 = 0 at hp
  change bind₁ (mask j) p.1 = 0
  rw [← hc]
  change bind₁ (mask j) (bind₁ (mask i) p.1) = 0
  rw [hp, map_zero]

theorem cutoff_step (hh : 0 < h) {i : ℕ} (hi : i ≤ 2 * h) :
    cutoff h i < cutoff h (i + 1) := by
  classical
  have hw : ∃ w : Fin h → Fin 3,
      (∀ b, i ≤ variableIndex (b,w b)) ∧ (∃ b, variableIndex (b,w b) = i) := by
    rcases eq_or_lt_of_le hi with he | he
    · subst i
      exact ⟨fun _ => 0, fun _ => by simp [variableIndex], ⟨⟨0, hh⟩, by simp [variableIndex]⟩⟩
    · let b : Fin h := ⟨i / 2, by omega⟩
      let j : Fin 3 := ⟨i % 2 + 1, by omega⟩
      have hj : j ≠ 0 := by
        intro hj
        have := congrArg Fin.val hj
        change i % 2 + 1 = 0 at this
        omega
      have hij : variableIndex (b,j) = i := by
        simp [variableIndex, hj, b, j]
        omega
      refine ⟨fun x => if x = b then j else 0, ?_, ⟨b, by simp [hij]⟩⟩
      intro x
      by_cases hx : x = b
      · simp [hx, hij]
      · simpa [hx, variableIndex] using hi
  obtain ⟨w, hw, b, hb⟩ := hw
  refine lt_of_le_of_ne (cutoff_mono (Nat.le_succ i)) ?_
  intro he
  let z : diagonal h := ⟨segre w, segre_mem w⟩
  have hz : z ∈ cutoff h (i+1) := by
    change bind₁ (mask (i+1)) (segre w) = 0
    rw [segre_prod, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    simp [mask, hb]
  have hn : z ∉ cutoff h i := by
    change bind₁ (mask i) (segre w) ≠ 0
    rw [segre_prod, map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro b _
    simp [mask, not_lt.mpr (hw b), X_ne_zero]
  exact hn (he.symm ▸ hz)

def irrelevant (h : ℕ) : Ideal (diagonal h) := cutoff h (2*h+1)

instance irrelevant_prime : (irrelevant h).IsPrime := cutoff_prime _

theorem irrelevant_height (hh : 0 < h) : (↑(2*h+1) : ℕ∞) ≤ (irrelevant h).height := by
  have hl (i : ℕ) (hi : i ≤ 2*h+1) : (i : ℕ∞) ≤ (cutoff h i).height := by
    induction i with
    | zero => simp
    | succ i ih =>
      have hm := Ideal.height_add_one_le_of_lt_of_isPrime (cutoff_step hh (i := i) (by omega))
      rw [ENat.natCast_add]
      exact (add_le_add_left (ih (by omega)) 1).trans hm
  exact hl _ le_rfl

theorem mem_irrelevant (p : diagonal h) :
    p ∈ irrelevant h ↔ coeff 0 p.1 = 0 := by
  have hm : (mask (2*h+1) : Fin h × Fin 3 → P h) = 0 := by
    funext x
    exact if_pos (Nat.lt_succ_of_le (variableIndex_le x))
  change bind₁ (mask _) p.1 = 0 ↔ _
  rw [hm]
  have hc : (bind₁ (0 : Fin h × Fin 3 → P h)) =
      (Algebra.ofId K (P h)).comp
      (show P h →ₐ[K] K from aeval (0 : Fin h × Fin 3 → K)) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp
  rw [hc]
  change C (eval (0 : Fin h × Fin 3 → K) p.1) = 0 ↔ _
  rw [eval_zero, constantCoeff_eq]
  exact ⟨fun hz => C_injective (Fin h × Fin 3) K (hz.trans C_0.symm), fun hz => hz.symm ▸ C_0⟩

def segreIn (w : Fin h → Fin 3) : diagonal h := ⟨segre w, segre_mem w⟩

theorem irrelevant_span (hh : 0 < h) : irrelevant h = Ideal.span (Set.range (segreIn (h := h))) := by
  apply le_antisymm
  · intro p hp
    let J : Ideal (diagonal h) := Ideal.span (Set.range (segreIn (h := h)))
    have hm (d : E h) (hd : d ∈ p.1.support) :
        ∃ x : diagonal h, x ∈ J ∧ x.1 = monomial d (coeff d p.1) := by
      obtain ⟨t, ht⟩ := diagonal_supported p.property d (mem_support_iff.mp hd)
      have h0 : d ≠ 0 := by
        rintro rfl
        exact (mem_support_iff.mp hd) ((mem_irrelevant p).mp hp)
      have ht0 : 0 < t := by
        by_contra! hz
        apply h0
        ext ⟨b,j⟩
        have hj := Finset.single_le_sum (f := fun j => d (b,j)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
        have hzb := ht b
        unfold degree at hzb
        change d (b,j) = 0
        omega
      obtain ⟨w, hw⟩ := chooseExp_le ht0 ht
      have hbal : Balanced (d - chooseExp w) := ⟨t-1, fun b => by
        have := degree_tsub _ _ hw b
        rw [ht, chooseExp_degree] at this
        omega⟩
      let y : diagonal h := ⟨monomial (d - chooseExp w) (coeff d p.1), diagonal_monomial hbal _⟩
      refine ⟨segreIn w * y, J.mul_mem_right y (Ideal.subset_span ⟨w, rfl⟩), ?_⟩
      change segre w * monomial (d - chooseExp w) _ = _
      rw [segre, monomial_mul, one_mul, add_comm, tsub_add_cancel_of_le hw]
    classical
    let g (d : E h) : diagonal h := if hd : d ∈ p.1.support then (hm d hd).choose else 0
    have hg : (∑ d ∈ p.1.support, g d) = p := by
      apply Subtype.ext
      change (diagonal h).val (∑ d ∈ p.1.support, g d) = p.1
      rw [map_sum]
      exact (Finset.sum_congr rfl fun d hd => by
        change (g d).1 = _
        simpa only [g, dif_pos hd] using (hm d hd).choose_spec.2).trans p.1.as_sum.symm
    rw [← hg]
    exact sum_mem fun d hd => by simpa only [g, dif_pos hd] using (hm d hd).choose_spec.1
  · apply Ideal.span_le.mpr
    rintro _ ⟨w, rfl⟩
    change _ ∈ irrelevant h
    rw [mem_irrelevant]
    have he : chooseExp w ≠ 0 := by
      intro he
      have := chooseExp_degree w ⟨0, hh⟩
      simp [he] at this
    simp [segreIn, segre, coeff_monomial, he]

theorem common_zero {q r : ℕ} (hh : 0 < h) (hr : 0 < r) (hq : q ≤ 2*h)
    (f : Fin q → P h)
    (hf : ∀ i, Supported (fun d => ∀ b, degree d b = r) (f i)) :
    ∃ ξ : Fin h × Fin 3 → K,
      (∀ i, aeval ξ (f i) = 0) ∧ ∀ b, ∃ j, ξ (b,j) ≠ 0 := by
  classical
  let A := diagonal h
  have hfin : (Set.range (segre (h := h))).Finite := Set.finite_range _
  let _ : Algebra.FiniteType K A := Algebra.FiniteType.adjoin_of_finite hfin
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  let g (i : Fin q) : A := ⟨f i, supported_diagonal fun d hd => ⟨r, hf i d hd⟩⟩
  let s : Finset A := Finset.univ.image g
  let J : Ideal A := Ideal.span (s : Set A)
  have hs : s.card ≤ q := by simpa [s] using (Finset.card_image_le (s := Finset.univ) (f := g))
  have hgi (i : Fin q) : g i ∈ J :=
    Ideal.subset_span (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hJ : J ≤ irrelevant h := by
    apply Ideal.span_le.mpr
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    change g i ∈ irrelevant h
    rw [mem_irrelevant]
    by_contra h0
    have := hf i 0 h0 ⟨0, hh⟩
    simp at this
    omega
  obtain ⟨p, hp, hpm⟩ := Ideal.exists_minimalPrimes_le hJ
  have hpJ : J ≤ p := hp.1.2
  have hpP : p.IsPrime := hp.1.1
  have hht : p.height ≤ (q : ℕ∞) :=
    (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hp).trans (by exact_mod_cast hs)
  have hn : ¬ irrelevant h ≤ p := by
    intro hn
    have hh0 := (irrelevant_height hh).trans ((Ideal.height_mono hn).trans hht)
    exact (Nat.not_succ_le_self (2*h)) ((by exact_mod_cast hh0 : 2*h+1 ≤ q).trans hq)
  have hw : ∃ w, segreIn (h := h) w ∉ p := by
    by_contra! hw
    apply hn
    rw [irrelevant_span hh, Ideal.span_le]
    rintro _ ⟨w, rfl⟩
    exact hw w
  obtain ⟨w, hw⟩ := hw
  let L := J.map A.val.toRingHom
  have hm : segre w ∉ L.radical := by
    rintro ⟨n, hn⟩
    apply hw
    apply hpP.mem_of_pow_mem n
    exact hpJ (diagonal_contract J (segreIn w ^ n) hn)
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)] at hm
  simp only [MvPolynomial.mem_vanishingIdeal_iff, not_forall] at hm
  obtain ⟨ξ, hξ, hwξ⟩ := hm
  refine ⟨ξ, fun i => ?_, fun b => ⟨w b, ?_⟩⟩
  · exact (MvPolynomial.mem_zeroLocus_iff.mp hξ) _ (Ideal.mem_map_of_mem A.val.toRingHom (hgi i))
  · intro hz
    apply hwξ
    rw [segre_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (by simpa using hz)

end CommonZero

section Pencils

open Matrix Polynomial

structure Pencil (s : ℕ) where
  constant : Fin 3 → Matrix (Fin s) (Fin s) ℚ
  linear : Fin 3 → Fin s → ℚ

instance (s : ℕ) : Countable (Pencil s) := by
  refine Function.Injective.countable (f := fun p : Pencil s => ((fun (t : Fin 3) (i j : Fin s) => p.constant t i j), p.linear)) ?_
  rintro ⟨a,b⟩ ⟨c,d⟩ hp
  have he : a = c := funext fun t => Matrix.ext fun i j =>
    congrFun (congrFun (congrFun (congrArg Prod.fst hp) t) i) j
  have hf : b = d := congrArg Prod.snd hp
  subst c
  subst d
  rfl

def pencil {s : ℕ} (p : Pencil s) {R : Type*} [CommRing R] [Algebra K R]
    (z : Fin 3 → R) : Matrix (Fin s) (Fin s) (Polynomial R) :=
  Matrix.of fun i j => ∑ t, Polynomial.C (z t) *
    (Polynomial.C (algebraMap K R (algebraMap ℚ K (p.constant t i j))) +
      if i.val = 0 then Polynomial.X *
        Polynomial.C (algebraMap K R (algebraMap ℚ K (p.linear t j))) else 0)

def segment {M : Type*} [Monoid M] (a : ℕ → M) (i : ℕ) : ℕ → M
  | 0 => 1
  | n+1 => segment a i n * a (i+n)

@[simp] theorem segment_zero {M : Type*} [Monoid M] (a : ℕ → M) (i : ℕ) :
    segment a i 0 = 1 := rfl

theorem segment_succ {M : Type*} [Monoid M] (a : ℕ → M) (i n : ℕ) :
    segment a i (n+1) = segment a i n * a (i+n) := rfl

theorem segment_add {M : Type*} [Monoid M] (a : ℕ → M) (i n m : ℕ) :
    segment a i (n+m) = segment a i n * segment a (i+n) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, segment_succ, ih, segment_succ, mul_assoc, Nat.add_assoc]

theorem segment_first {M : Type*} [Monoid M] (a : ℕ → M) (i n : ℕ) :
    segment a i (n+1) = a i * segment a (i+1) n := by
  rw [Nat.add_comm, segment_add, segment_succ, segment_zero, one_mul, Nat.add_zero]

theorem segment_congr {M : Type*} [Monoid M] {a b : ℕ → M} {i n : ℕ}
    (h : ∀ j, j < n → a (i+j) = b (i+j)) : segment a i n = segment b i n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [segment_succ, segment_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

theorem segment_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N)
    (a : ℕ → M) (i n : ℕ) : f (segment a i n) = segment (fun j => f (a j)) i n := by
  induction n with
  | zero => simp
  | succ n ih => rw [segment_succ, map_mul, ih, segment_succ]

theorem det_submatrix_noninjective {R : Type*} [CommRing R] {s r : ℕ}
    (A : Matrix (Fin s) (Fin s) R) (I J : Fin r → Fin s)
    (hI : ¬ Function.Injective I) : (A.submatrix I J).det = 0 := by
  obtain ⟨x,y,hxy,hne⟩ := Function.not_injective_iff.mp hI
  exact Matrix.det_zero_of_row_eq hne (funext fun j => congrArg (fun i => A i (J j)) hxy)

theorem det_submatrix_mul_rows {R : Type*} [CommRing R] {s r : ℕ}
    (A B : Matrix (Fin s) (Fin s) R) (I J : Fin r → Fin s) :
    ((A * B).submatrix I J).det =
      ∑ f : Fin r → Fin s, (∏ i, A (I i) (f i)) * (B.submatrix f J).det := by
  classical
  let F := (Matrix.detRowAlternating (R := R) (n := Fin r)).toMultilinearMap
  change F ((A * B).submatrix I J) = _
  have hh : (A * B).submatrix I J =
      fun i => ∑ j : Fin s, A (I i) j • (fun k => B j (J k)) := by
    ext i k
    simp [Matrix.mul_apply, Matrix.submatrix_apply, Finset.sum_apply]
  rw [hh, F.map_sum_finset]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [F.map_smul_univ]
  rfl

theorem sum_natDegree_le {R : Type*} [Semiring R] {ι : Type*} (s : Finset ι)
    (a : ι → Polynomial R) (d : ℕ) (ha : ∀ i ∈ s, (a i).natDegree ≤ d) :
    (∑ i ∈ s, a i).natDegree ≤ d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (Polynomial.natDegree_add_le _ _).trans (max_le
      (ha i (Finset.mem_insert_self _ _)) (ih fun j hj => ha j (Finset.mem_insert_of_mem hj)))

theorem pencil_degree {R : Type*} [CommRing R] [Algebra K R] {s : ℕ}
    (p : Pencil s) (z : Fin 3 → R) (i j : Fin s) :
    (pencil p z i j).natDegree ≤ if i.val = 0 then 1 else 0 := by
  simp only [pencil, Matrix.of_apply]
  apply sum_natDegree_le
  intro t _
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  split_ifs with hi
  · apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp [Polynomial.natDegree_X_le])
  · simp

theorem segment_minor_degree {R : Type*} [CommRing R] [Algebra K R] {s r : ℕ}
    (p : Pencil s) (z : ℕ → Fin 3 → R) (start n : ℕ) (I J : Fin r → Fin s) :
    ((segment (fun i => pencil p (z i)) start n).submatrix I J).det.natDegree ≤ n := by
  classical
  induction n generalizing start I J with
  | zero =>
    simp only [segment_zero]
    rw [Matrix.det_apply']
    apply sum_natDegree_le
    intro σ _
    refine Polynomial.natDegree_mul_le.trans ?_
    have h (i : Fin r) :
        ((1 : Matrix (Fin s) (Fin s) (Polynomial R)).submatrix I J (σ i) i).natDegree = 0 := by
      simp only [Matrix.submatrix_apply, Matrix.one_apply]
      split <;> simp
    have hprod := Polynomial.natDegree_prod_le Finset.univ
      (fun i => (1 : Matrix (Fin s) (Fin s) (Polynomial R)).submatrix I J (σ i) i)
    simp only [h, Finset.sum_const_zero] at hprod
    norm_cast
    simpa using hprod
  | succ n ih =>
    by_cases hi : Function.Injective I
    · rw [segment_first, det_submatrix_mul_rows]
      apply sum_natDegree_le
      intro f _
      have hf : (∏ i, pencil p (z start) (I i) (f i)).natDegree ≤ 1 := by
        refine (Polynomial.natDegree_prod_le _ _).trans ?_
        refine (Finset.sum_le_sum (fun i _ => pencil_degree p (z start) (I i) (f i))).trans ?_
        by_cases hs : ∃ i, (I i).val = 0
        · obtain ⟨i,hi0⟩ := hs
          have hh (j : Fin r) : (I j).val = 0 ↔ j = i := by
            constructor
            · intro hj
              exact hi (Fin.ext (hj.trans hi0.symm))
            · rintro rfl
              exact hi0
          simp [hh]
        · have hn (i : Fin r) : (I i).val ≠ 0 := fun hi => hs ⟨i,hi⟩
          simp [hn]
      exact Polynomial.natDegree_mul_le.trans (by
        have := ih (start+1) f J
        omega)
    · rw [det_submatrix_noninjective _ I J hi]
      simp

section Minors

variable {F : Type*} [Field F] {s r : ℕ}

theorem factor_of_minors (A : Matrix (Fin s) (Fin s) F) (I J : Fin r → Fin s)
    (hB : (A.submatrix I J).det ≠ 0)
    (hA : ∀ i j : Fin (r+1) → Fin s, (A.submatrix i j).det = 0) :
    A = A.submatrix id J * (A.submatrix I J)⁻¹ * A.submatrix I id := by
  classical
  let B := A.submatrix I J
  ext i j
  let C : Matrix (Fin r) (Fin 1) F := A.submatrix I (fun _ => j)
  let D : Matrix (Fin 1) (Fin r) F := A.submatrix (fun _ => i) J
  let E : Matrix (Fin 1) (Fin 1) F := A.submatrix (fun _ => i) (fun _ => j)
  have hb : (Matrix.fromBlocks B C D E).det = 0 := by
    have he : Matrix.fromBlocks B C D E = A.submatrix
        (Sum.elim I (fun _ => i)) (Sum.elim J (fun _ => j)) := by
      ext (x | x) (y | y) <;> rfl
    rw [he, ← Matrix.det_submatrix_equiv_self finSumFinEquiv.symm]
    exact hA _ _
  let _ : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB)
  rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv] at hb
  have hn := (mul_eq_zero.mp hb).resolve_left hB
  rw [Matrix.det_unique, Matrix.sub_apply, sub_eq_zero] at hn
  simpa [E, D, C, B, Matrix.mul_apply] using hn

theorem minors_sandwich (A T : Matrix (Fin s) (Fin s) F) (I J : Fin r → Fin s)
    (hB : (A.submatrix I J).det ≠ 0)
    (hA : ∀ i j : Fin (r+1) → Fin s, (A.submatrix i j).det = 0)
    (h : ((A * T * A).submatrix I J).det = 0) :
    ∀ i j : Fin r → Fin s, ((A * T * A).submatrix i j).det = 0 := by
  classical
  let B := A.submatrix I J
  let X := A.submatrix id J
  let Y := A.submatrix I id
  have hA' : A = X * B⁻¹ * Y := factor_of_minors A I J hB hA
  have hT (i j : Fin r → Fin s) :
      (A * T * A).submatrix i j = A.submatrix i id * T * A.submatrix id j := by
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
    simp
  have hmid : (Y * T * X).det = 0 := (hT I J) ▸ h
  intro i j
  have hleft : A.submatrix i id = (X.submatrix i id * B⁻¹) * Y := by
    conv_lhs => rw [hA']
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
    simp
  have hright : A.submatrix id j = X * (B⁻¹ * Y.submatrix id j) := by
    conv_lhs => rw [hA']
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      Matrix.submatrix_mul _ _ _ id _ Function.bijective_id]
    simp [Matrix.mul_assoc]
  rw [hT, hleft, hright]
  have he : (X.submatrix i id * B⁻¹ * Y) * T * (X * (B⁻¹ * Y.submatrix id j)) =
      (X.submatrix i id * B⁻¹) * (Y * T * X) * (B⁻¹ * Y.submatrix id j) := by
    simp only [Matrix.mul_assoc]
  rw [he, Matrix.det_mul, Matrix.det_mul, hmid, mul_zero, zero_mul]

end Minors

section Homogeneous

variable {h : ℕ}

def Hom (b : Fin h) (n : ℕ) (p : P h) : Prop :=
  Supported (fun d => degree d b = n) p

def PolyHom (b : Fin h) (n : ℕ) (p : Polynomial (P h)) : Prop :=
  ∀ a, Hom b n (p.coeff a)

theorem hom_zero (b : Fin h) (n : ℕ) : Hom b n 0 := by simp [Hom, Supported]

theorem hom_mul {b : Fin h} {n m : ℕ} {a c : P h}
    (ha : Hom b n a) (hc : Hom b m c) : Hom b (n+m) (a*c) :=
  supported_mul ha hc fun d e hd he => by
    rw [degree_add, hd, he]

theorem hom_constant (b : Fin h) (c : K) : Hom b 0 (algebraMap K (P h) c) :=
  supported_C (degree_zero b) c

theorem hom_variable (b c : Fin h) (j : Fin 3) :
    Hom b (if c = b then 1 else 0) (MvPolynomial.X (c,j) : P h) := by
  classical
  apply supported_monomial
  by_cases hb : c = b
  · subst c
    have he (i : Fin 3) : Finsupp.single (b,j) 1 (b,i) = (if i = j then 1 else 0 : ℕ) := by
      simp [Finsupp.single_apply, eq_comm]
    simp [degree, he]
  · have he (i : Fin 3) : Finsupp.single (c,j) 1 (b,i) = (0 : ℕ) := by
      simp [Ne.symm hb]
    simp [degree, he, hb]

theorem polyHom_zero (b : Fin h) (n : ℕ) : PolyHom b n 0 := by
  intro a
  simpa using hom_zero b n

theorem polyHom_monomial {b : Fin h} {n : ℕ} {p : P h}
    (hp : Hom b n p) (a : ℕ) : PolyHom b n (Polynomial.monomial a p) := by
  intro c
  rw [Polynomial.coeff_monomial]
  split
  · exact hp
  · exact hom_zero _ _

theorem polyHom_C {b : Fin h} {n : ℕ} {p : P h}
    (hp : Hom b n p) : PolyHom b n (Polynomial.C p) := polyHom_monomial hp 0

theorem polyHom_X (b : Fin h) : PolyHom b 0 Polynomial.X :=
  polyHom_monomial (hom_constant b 1) 1

theorem polyHom_one (b : Fin h) : PolyHom b 0 1 :=
  polyHom_C (hom_constant b 1)

theorem polyHom_mul {b : Fin h} {n m : ℕ} {a c : Polynomial (P h)}
    (ha : PolyHom b n a) (hc : PolyHom b m c) : PolyHom b (n+m) (a*c) := by
  intro t
  rw [Polynomial.coeff_mul]
  exact supported_sum _ _ fun i _ => hom_mul (ha i.1) (hc i.2)

theorem polyHom_add {b : Fin h} {n : ℕ} {a c : Polynomial (P h)}
    (ha : PolyHom b n a) (hc : PolyHom b n c) : PolyHom b n (a+c) := by
  intro t
  rw [Polynomial.coeff_add]
  exact supported_add (ha t) (hc t)

theorem polyHom_sum {ι : Type*} {b : Fin h} {n : ℕ} (s : Finset ι)
    (a : ι → Polynomial (P h)) (ha : ∀ i ∈ s, PolyHom b n (a i)) :
    PolyHom b n (∑ i ∈ s, a i) := by
  intro t
  rw [Polynomial.finsetSum_coeff]
  exact supported_sum _ _ fun i hi => ha i hi t

theorem polyHom_prod {ι : Type*} {b : Fin h} {n : ℕ} (s : Finset ι)
    (a : ι → Polynomial (P h)) (ha : ∀ i ∈ s, PolyHom b n (a i)) :
    PolyHom b (s.card*n) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyHom_one b
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, one_mul, add_comm]
    exact polyHom_mul (ha i (Finset.mem_insert_self _ _))
      (ih fun j hj => ha j (Finset.mem_insert_of_mem hj))

theorem polyHom_det {b : Fin h} {n r : ℕ}
    (A : Matrix (Fin r) (Fin r) (Polynomial (P h)))
    (ha : ∀ i j, PolyHom b n (A i j)) : PolyHom b (r*n) A.det := by
  classical
  rw [Matrix.det_apply']
  apply polyHom_sum
  intro σ _
  have hs : PolyHom b 0 (↑↑(Equiv.Perm.sign σ)) := by
    rw [← map_intCast (Polynomial.C : P h →+* Polynomial (P h)), ← map_intCast (algebraMap K (P h))]
    exact polyHom_C (hom_constant b _)
  simpa using polyHom_mul hs (polyHom_prod Finset.univ _ fun i _ => ha (σ i) i)

theorem pencil_hom {b : Fin h} {n s : ℕ}
    (p : Pencil s) (z : Fin 3 → P h) (hz : ∀ t, Hom b n (z t)) (i j : Fin s) :
    PolyHom b n (pencil p z i j) := by
  simp only [pencil, Matrix.of_apply]
  apply polyHom_sum
  intro t _
  have hc := polyHom_C (hom_constant b (algebraMap ℚ K (p.constant t i j)))
  have hd := polyHom_C (hom_constant b (algebraMap ℚ K (p.linear t j)))
  have hlin : PolyHom b 0 (if i.val = 0 then Polynomial.X *
      Polynomial.C (algebraMap K (P h) (algebraMap ℚ K (p.linear t j))) else 0) := by
    split
    · exact polyHom_mul (polyHom_X b) hd
    · exact polyHom_zero _ _
  simpa using polyHom_mul (polyHom_C (hz t)) (polyHom_add hc hlin)

theorem matrix_hom_mul {b : Fin h} {n m s : ℕ}
    {A B : Matrix (Fin s) (Fin s) (Polynomial (P h))}
    (ha : ∀ i j, PolyHom b n (A i j)) (hb : ∀ i j, PolyHom b m (B i j)) (i j : Fin s) :
    PolyHom b (n+m) ((A * B) i j) := by
  rw [Matrix.mul_apply]
  exact polyHom_sum _ _ fun t _ => polyHom_mul (ha i t) (hb t j)

theorem segment_hom_zero {b : Fin h} {s : ℕ} (p : Pencil s) (z : ℕ → Fin 3 → P h)
    (start n : ℕ) (hz : ∀ i < n, ∀ t, Hom b 0 (z (start+i) t)) (i j : Fin s) :
    PolyHom b 0 (segment (fun k => pencil p (z k)) start n i j) := by
  induction n generalizing i j with
  | zero =>
    rw [segment_zero, Matrix.one_apply]
    split
    · exact polyHom_one _
    · exact polyHom_zero _ _
  | succ n ih =>
    rw [segment_succ]
    exact matrix_hom_mul (n := 0) (m := 0)
      (A := segment (fun k => pencil p (z k)) start n) (B := pencil p (z (start+n)))
      (fun i j => ih (fun k hk => hz k (by omega)) i j)
      (pencil_hom p _ (hz n (by omega))) i j

theorem segment_hom_one {b : Fin h} {s : ℕ} (p : Pencil s) (z : ℕ → Fin 3 → P h)
    (n a : ℕ) (ha : a < n) (hz : ∀ i < n, ∀ t, Hom b (if i = a then 1 else 0) (z i t))
    (i j : Fin s) : PolyHom b 1 (segment (fun k => pencil p (z k)) 0 n i j) := by
  have he : n = a+1+(n-a-1) := by omega
  have hs : segment (fun k => pencil p (z k)) 0 n =
      (segment (fun k => pencil p (z k)) 0 a * pencil p (z a)) *
        segment (fun k => pencil p (z k)) (a+1) (n-a-1) := by
    conv_lhs => rw [he, segment_add, segment_succ]
    simp
  rw [hs]
  apply matrix_hom_mul (n := 1) (m := 0)
  · apply matrix_hom_mul (n := 0) (m := 1)
    · intro i j
      apply segment_hom_zero
      intro k hk t
      simpa [show k ≠ a by omega] using hz k (by omega) t
    · intro i j
      apply pencil_hom
      intro t
      simpa using hz a ha t
  · intro i j
    apply segment_hom_zero
    intro k hk t
    simpa [show a+1+k ≠ a by omega] using hz (0+a+1+k) (by omega) t

theorem map_pencil {s : ℕ} (p : Pencil s) (ξ : Fin h × Fin 3 → K) (z : Fin 3 → P h) :
    (pencil p z).map (Polynomial.map (MvPolynomial.aeval ξ).toRingHom) =
      pencil p (fun t => MvPolynomial.aeval ξ (z t)) := by
  ext i j : 1
  change (Polynomial.mapRingHom (MvPolynomial.aeval ξ).toRingHom) (pencil p z i j) = _
  simp only [pencil, Matrix.of_apply, map_sum, map_mul, map_add]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hi : i.val = 0 <;> simp [hi, Polynomial.mapRingHom]

end Homogeneous

section Prescriptions

abbrev Letter := {z : Fin 3 → K // z ≠ 0}

def initialLetter : Letter := ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩

structure Prescription where
  period : ℕ
  positive : 0 < period
  slots : Fin period → Option Letter
  sparse : period < 2 * Fintype.card {i : Fin period // slots i = none}

def Prescription.atPos (D : Prescription) (i : ℕ) : Option Letter :=
  D.slots ⟨i % D.period, Nat.mod_lt _ D.positive⟩

theorem prescription_period (D : Prescription) {n : ℕ} (hn : D.period ∣ n) (i : ℕ) :
    D.atPos (n+i) = D.atPos i := by
  unfold Prescription.atPos
  congr 1
  apply Fin.ext
  change (n+i)%D.period = i%D.period
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hn, zero_add, Nat.mod_mod]

def Compatible (D : Prescription) (w : ℕ → Letter) (n : ℕ) : Prop :=
  ∀ i < n, ∀ z, D.atPos i = some z → w i = z

def appendSeq {α : Type*} (u : ℕ → α) (n : ℕ) (v : ℕ → α) (i : ℕ) : α :=
  if i < n then u i else v (i-n)

theorem segment_translate {M : Type*} [Monoid M] (a : ℕ → M) (i n : ℕ) :
    segment a i n = segment (fun j => a (i+j)) 0 n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [segment_succ, segment_succ, ← ih, Nat.zero_add]

theorem segment_append {α M : Type*} [Monoid M] (f : α → M)
    (u v : ℕ → α) (n m : ℕ) :
    segment (fun i => f (appendSeq u n v i)) 0 (n+m) =
      segment (fun i => f (u i)) 0 n * segment (fun i => f (v i)) 0 m := by
  rw [segment_add, segment_translate (fun i => f (appendSeq u n v i)) (0+n), Nat.zero_add]
  congr 1
  · apply segment_congr
    intro i hi
    simp [appendSeq, hi]
  · apply segment_congr
    intro i _
    simp [appendSeq, show ¬ n+i < n by omega]

theorem compatible_append {D : Prescription} {w u : ℕ → Letter} {n m : ℕ}
    (hn : D.period ∣ n) (hw : Compatible D w n) (hu : Compatible D u m) :
    Compatible D (appendSeq w n u) (n+m) := by
  intro i hi z hz
  by_cases hin : i < n
  · simpa [appendSeq, hin] using hw i hin z hz
  · rw [appendSeq, if_neg hin]
    apply hu _ (by omega)
    rw [← prescription_period D hn (i-n), show n+(i-n) = i by omega]
    exact hz

abbrev Free (D : Prescription) := {i : Fin D.period // D.slots i = none}

abbrev FreePosition (D : Prescription) (m : ℕ) :=
  {i : Fin (m * D.period) // D.atPos i.val = none}

theorem freePosition_card (D : Prescription) (m : ℕ) :
    Fintype.card (FreePosition D m) = m * Fintype.card (Free D) := by
  classical
  let e : Fin (m*D.period) ≃ Fin m × Fin D.period := finProdFinEquiv.symm
  have he (i : Fin (m*D.period)) : D.atPos i.val = D.slots (e i).2 := by
    rw [show e i = (i.divNat, i.modNat) from finProdFinEquiv_symm_apply i]
    rfl
  let f : FreePosition D m ≃ Fin m × Free D :=
    { toFun := fun i => ((e i.1).1, ⟨(e i.1).2, (he i.1).symm.trans i.2⟩)
      invFun := fun j => ⟨e.symm (j.1,j.2.1), by rw [he, e.apply_symm_apply]; exact j.2.2⟩
      left_inv := fun i => Subtype.ext (e.symm_apply_apply i.1)
      right_inv := fun j => by
        have h := e.apply_symm_apply (j.1,j.2.1)
        have h₁ : (e (e.symm (j.1,j.2.1))).1 = j.1 := congrArg Prod.fst h
        have h₂ : (e (e.symm (j.1,j.2.1))).2 = j.2.1 := congrArg Prod.snd h
        exact Prod.ext h₁ (Subtype.ext h₂) }
  rw [Fintype.card_congr f, Fintype.card_prod, Fintype.card_fin]

def value {s : ℕ} (p : Pencil s) (w : ℕ → Letter) (n : ℕ) :
    Matrix (Fin s) (Fin s) (Polynomial K) :=
  segment (fun i => pencil p (w i).1) 0 n

theorem value_append {s : ℕ} (p : Pencil s) (w u : ℕ → Letter) (n m : ℕ) :
    value p (appendSeq w n u) (n+m) = value p w n * value p u m :=
  segment_append (fun a : Letter => pencil p a.1) w u n m

theorem vanish_minor {s r : ℕ} (D : Prescription) (p : Pencil s)
    (w : ℕ → Letter) (n : ℕ) (hr : 0 < r) (I J : Fin r → Fin s) :
    ∃ m : ℕ, 0 < m ∧ ∃ u : ℕ → Letter, Compatible D u (m*D.period) ∧
      ((value p w n * value p u (m*D.period) * value p w n).submatrix I J).det = 0 := by
  classical
  let m := 2*n+1
  let L := m*D.period
  let H := Fintype.card (FreePosition D m)
  have hH : H = m * Fintype.card (Free D) := freePosition_card D m
  have hcount : n+(L+n)+1 ≤ 2*H := by
    have hd := Nat.mul_le_mul_left m (Nat.succ_le_of_lt D.sparse)
    dsimp [L, m] at *
    rw [hH]
    nlinarith
  have hh : 0 < H := by omega
  let e : Fin H ≃ FreePosition D m := (Fintype.equivFin _).symm
  let c (i : ℕ) (j : Fin 3) : P H := algebraMap K (P H) ((w i).1 j)
  let z (i : ℕ) (j : Fin 3) : P H :=
    if hi : i < L then
      if hf : D.atPos i = none then
        MvPolynomial.X (e.symm ⟨⟨i,hi⟩,hf⟩,j)
      else algebraMap K (P H) (((D.atPos i).getD initialLetter).1 j)
    else 0
  let Z := appendSeq c n (appendSeq z L c)
  let Δ := ((segment (fun t => pencil p (Z t)) 0 (n+(L+n))).submatrix I J).det
  have hdeg := segment_minor_degree p Z 0 (n+(L+n)) I J
  have hhom (b : Fin H) : PolyHom b r Δ := by
    have hb : (e b).1.val < L := (e b).1.isLt
    have hpos : n+(e b).1.val < n+(L+n) := by omega
    have he (i : ℕ) (_hi : i < n+(L+n)) (t : Fin 3) :
        Hom b (if i = n+(e b).1.val then 1 else 0) (Z i t) := by
      by_cases hn : i < n
      · simp only [Z, appendSeq, if_pos hn, if_neg (show i ≠ n+(e b).1.val by omega)]
        exact hom_constant b _
      have hn' : i = n+(i-n) := by omega
      by_cases hL : i-n < L
      · simp only [Z, appendSeq, if_neg hn, if_pos hL, z, dif_pos hL]
        by_cases hF : D.atPos (i-n) = none
        · rw [dif_pos hF]
          have hbe : e.symm ⟨⟨i-n,hL⟩,hF⟩ = b ↔ i = n+(e b).1.val := by
            rw [Equiv.symm_apply_eq]
            constructor
            · intro he
              have := congrArg (fun x : FreePosition D m => x.1.val) he
              dsimp at this
              omega
            · intro he
              exact Subtype.ext (Fin.ext (by dsimp; omega))
          simpa only [hbe] using hom_variable b (e.symm ⟨⟨i-n,hL⟩,hF⟩) t
        · rw [dif_neg hF]
          have hne : i ≠ n+(e b).1.val := by
            intro he
            apply hF
            rw [show i-n = (e b).1.val by omega]
            exact (e b).2
          rw [if_neg hne]
          exact hom_constant b _
      · simp only [Z, appendSeq, if_neg hn, if_neg hL,
          if_neg (show i ≠ n+(e b).1.val by omega)]
        exact hom_constant b _
    have hdet := polyHom_det (b := b) (n := 1)
      ((segment (fun t => pencil p (Z t)) 0 (n+(L+n))).submatrix I J)
      (fun i j => segment_hom_one p Z _ _ hpos he (I i) (J j))
    simpa only [Nat.mul_one] using hdet
  obtain ⟨ξ,hξ,hξne⟩ := common_zero hh hr hcount
    (fun i => Δ.coeff i.val) (fun i d hd b => hhom b i.val d hd)
  let f : P H →+* K := (MvPolynomial.aeval ξ).toRingHom
  have hΔ : Polynomial.map f Δ = 0 := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hi : i < n+(L+n)+1
    · exact hξ ⟨i,hi⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega)), map_zero]
  have hnonzero (i : ℕ) (hi : i < L) : (fun j => f (z i j)) ≠ 0 := by
    by_cases hF : D.atPos i = none
    · obtain ⟨j,hj⟩ := hξne (e.symm ⟨⟨i,hi⟩,hF⟩)
      intro hz
      apply hj
      simpa [z, hi, hF, f] using congrFun hz j
    · intro hz
      apply ((D.atPos i).getD initialLetter).2
      funext j
      simpa [z, hi, hF, f] using congrFun hz j
  let u (i : ℕ) : Letter := if hi : i < L then ⟨fun j => f (z i j), hnonzero i hi⟩
    else initialLetter
  have hu : Compatible D u L := by
    intro i hi a ha
    apply Subtype.ext
    funext j
    simp [u, z, hi, ha, f]
  refine ⟨m, by dsimp [m]; omega, u, hu, ?_⟩
  have hm (v : ℕ → Fin 3 → P H) (N : ℕ) :
      (Polynomial.mapRingHom f).mapMatrix (segment (fun i => pencil p (v i)) 0 N) =
        segment (fun i => pencil p (fun j => f (v i j))) 0 N := by
    change ((Polynomial.mapRingHom f).mapMatrix (m := Fin s)).toMonoidHom
      (segment (fun i => pencil p (v i)) 0 N) = _
    rw [segment_map]
    apply segment_congr
    intro i _
    exact map_pencil p ξ (v (0+i))
  have hc : segment (fun i => pencil p (fun j => f (c i j))) 0 n = value p w n := by
    apply segment_congr
    intro i _
    congr 1
    funext j
    simp [c, f]
  have hz : segment (fun i => pencil p (fun j => f (z i j))) 0 L = value p u L := by
    apply segment_congr
    intro i hi
    simp [u, hi]
  change Polynomial.mapRingHom f Δ = 0 at hΔ
  unfold Δ Z at hΔ
  rw [segment_append, segment_append, ← Matrix.mul_assoc, RingHom.map_det] at hΔ
  change (((Polynomial.mapRingHom f).mapMatrix
    ((segment (fun i => pencil p (c i)) 0 n *
      segment (fun i => pencil p (z i)) 0 L *
      segment (fun i => pencil p (c i)) 0 n).submatrix I J))).det = 0 at hΔ
  change ((((Polynomial.mapRingHom f).mapMatrix
    (segment (fun i => pencil p (c i)) 0 n *
      segment (fun i => pencil p (z i)) 0 L *
      segment (fun i => pencil p (c i)) 0 n)).submatrix I J)).det = 0 at hΔ
  rw [map_mul, map_mul, hm, hm, hc, hz] at hΔ
  exact hΔ

end Prescriptions

section UniformWords

def MinorsVanish {s : ℕ} (M : Matrix (Fin s) (Fin s) (Polynomial K)) (r : ℕ) : Prop :=
  ∀ I J : Fin r → Fin s, (M.submatrix I J).det = 0

theorem compatible_zero {s : ℕ} (D : Prescription) (p : Pencil s) :
    ∃ k : ℕ, 0 < k ∧ ∃ w : ℕ → Letter, Compatible D w (k*D.period) ∧
      value p w (k*D.period) = 0 := by
  classical
  let good (r : ℕ) := ∃ k : ℕ, 0 < k ∧ ∃ w : ℕ → Letter,
    Compatible D w (k*D.period) ∧ MinorsVanish (value p w (k*D.period)) (r+1)
  have hex : ∃ r, good r := by
    refine ⟨s, 1, by omega, fun i => (D.atPos i).getD initialLetter, ?_, ?_⟩
    · intro i _ z hz
      simp [hz]
    · intro I J
      apply det_submatrix_noninjective
      intro hI
      have := Fintype.card_le_of_injective I hI
      simp at this
  let r := Nat.find hex
  obtain ⟨k,hk,w,hw,hvan⟩ : good r := Nat.find_spec hex
  by_cases hr : r = 0
  · refine ⟨k,hk,w,hw,?_⟩
    ext i j : 1
    have hvan' : MinorsVanish (value p w (k*D.period)) 1 := by simpa [hr] using hvan
    have hz := hvan' (fun _ => i) (fun _ => j)
    rw [Matrix.det_unique] at hz
    exact hz
  have hr0 : 0 < r := Nat.pos_of_ne_zero hr
  have hn : ¬ MinorsVanish (value p w (k*D.period)) r := by
    intro h
    have hg : good (r-1) := ⟨k,hk,w,hw,by simpa only [Nat.sub_add_cancel hr0] using h⟩
    have : r ≤ r-1 := Nat.find_min' hex hg
    omega
  unfold MinorsVanish at hn
  simp only [not_forall] at hn
  obtain ⟨I,J,hIJ⟩ := hn
  let n := k*D.period
  obtain ⟨m,hm,u,hu,hmiddle⟩ := vanish_minor D p w n hr0 I J
  let F := FractionRing (Polynomial K)
  let f := algebraMap (Polynomial K) F
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have lift {A : Matrix (Fin s) (Fin s) (Polynomial K)} {l : ℕ} (i j : Fin l → Fin s) :
      ((f.mapMatrix A).submatrix i j).det = f (A.submatrix i j).det :=
    (f.map_det _).symm
  have hv : MinorsVanish (value p w n * value p u (m*D.period) * value p w n) r := by
    intro i j
    apply hf
    rw [map_zero, ← lift, map_mul, map_mul]
    apply minors_sandwich _ _ I J
    · rw [lift]
      exact fun h => hIJ (hf (h.trans (map_zero f).symm))
    · intro i j
      rw [lift, hvan i j, map_zero]
    · rw [← map_mul, ← map_mul, lift, hmiddle, map_zero]
  let v := appendSeq w n (appendSeq u (m*D.period) w)
  have he : (k+(m+k))*D.period = n+(m*D.period+n) := by simp [n, Nat.add_mul]
  have hg : good (r-1) := by
    refine ⟨k+(m+k), by omega, v, ?_, ?_⟩
    · rw [he]
      exact compatible_append (dvd_mul_left _ _) hw
        (compatible_append (dvd_mul_left _ _) hu hw)
    · rw [he, show r-1+1 = r by omega, value_append, value_append, ← Matrix.mul_assoc]
      exact hv
  have : r ≤ r-1 := Nat.find_min' hex hg
  omega

def extendPrescription (D : Prescription) (w : ℕ → Letter) (n : ℕ) : Prescription := by
  classical
  let m := 2*n+1
  let Q := m*D.period
  let slots (i : Fin Q) := if i.val < n then some (w i.val) else D.atPos i.val
  refine ⟨Q, Nat.mul_pos (by dsimp [m]; omega) D.positive, slots, ?_⟩
  have hcard : m * Fintype.card (Free D) ≤ n + Fintype.card {i : Fin Q // slots i = none} := by
    rw [← freePosition_card]
    let inj (i : FreePosition D m) : Fin n ⊕ {i : Fin Q // slots i = none} :=
      if hi : i.1.val < n then Sum.inl ⟨i.1.val,hi⟩
      else Sum.inr ⟨i.1, by simp [slots, hi, i.2]⟩
    have hi : Function.Injective inj := by
      intro i j hij
      by_cases hi : i.1.val < n <;> by_cases hj : j.1.val < n
      · simp only [inj, dif_pos hi, dif_pos hj, Sum.inl.injEq] at hij
        have h : i.1.val = j.1.val := congrArg (fun a : Fin n => a.val) hij
        exact Subtype.ext (Fin.ext h)
      · simp [inj, hi, hj] at hij
      · simp [inj, hi, hj] at hij
      · simp only [inj, dif_neg hi, dif_neg hj, Sum.inr.injEq] at hij
        have h : i.1 = j.1 := congrArg (fun a : {i : Fin Q // slots i = none} => a.val) hij
        exact Subtype.ext h
    simpa using Fintype.card_le_of_injective inj hi
  have hm := Nat.mul_le_mul_left m (Nat.succ_le_of_lt D.sparse)
  change Q < 2 * Fintype.card {i : Fin Q // slots i = none}
  dsimp [Q, m] at *
  nlinarith

theorem extend_period (D : Prescription) (w : ℕ → Letter) (n : ℕ) :
    (extendPrescription D w n).period = (2*n+1)*D.period := rfl

theorem extend_keeps (D : Prescription) (w : ℕ → Letter) (n : ℕ) (hw : Compatible D w n)
    (i : ℕ) (z : Letter) (hz : D.atPos i = some z) :
    (extendPrescription D w n).atPos i = some z := by
  let Q := (2*n+1)*D.period
  have hd : D.period ∣ Q := dvd_mul_left _ _
  have hmod : D.atPos (i%Q) = D.atPos i := by
    unfold Prescription.atPos
    congr 1
    exact Fin.ext (Nat.mod_mod_of_dvd i hd)
  change (if i%Q < n then some (w (i%Q)) else D.atPos (i%Q)) = some z
  rw [hmod]
  split
  · rename_i hi
    rw [hw _ hi z (hmod.trans hz)]
  · exact hz

theorem extend_records (D : Prescription) (w : ℕ → Letter) {n a i : ℕ}
    (hi : i < n) :
    (extendPrescription D w n).atPos (a*(extendPrescription D w n).period+i) = some (w i) := by
  let Q := (extendPrescription D w n).period
  have hQ : n < Q := by
    dsimp [Q]
    rw [extend_period]
    have := Nat.le_mul_of_pos_right (2*n+1) D.positive
    omega
  rw [prescription_period _ (dvd_mul_left _ _)]
  change (if i%Q < n then some (w (i%Q)) else D.atPos (i%Q)) = some (w i)
  rw [Nat.mod_eq_of_lt (hi.trans hQ), if_pos hi]

def emptyPrescription : Prescription where
  period := 1
  positive := by decide
  slots := fun _ => none
  sparse := by
    have h : Fintype.card {i : Fin 1 // (none : Option Letter) = none} = 1 := by
      simp
    omega

abbrev SomePencil := Σ s : ℕ, Pencil s

instance : Nonempty SomePencil := ⟨⟨0, ⟨fun _ => 0, fun _ _ => 0⟩⟩⟩

theorem uniform_pencils :
    ∃ v : ℕ → Letter, ∀ (s : ℕ) (p : Pencil s), ∃ N : ℕ, 0 < N ∧
      ∀ i, segment (fun a => pencil p (v a).1) i N = 0 := by
  classical
  obtain ⟨enumerate,hsurj⟩ := exists_surjective_nat SomePencil
  let witness (D : Prescription) (j : ℕ) :=
    compatible_zero D (enumerate j).2
  let k (D : Prescription) (j : ℕ) := (witness D j).choose
  let w (D : Prescription) (j : ℕ) := (witness D j).choose_spec.2.choose
  let D : ℕ → Prescription := fun j =>
    Nat.rec emptyPrescription (fun a T => extendPrescription T (w T a) (k T a*T.period)) j
  let n (j : ℕ) := k (D j) j * (D j).period
  have hD (j : ℕ) : D (j+1) = extendPrescription (D j) (w (D j) j) (n j) := rfl
  have hk (j : ℕ) : 0 < k (D j) j := (witness (D j) j).choose_spec.1
  have hw (j : ℕ) : Compatible (D j) (w (D j) j) (n j) :=
    (witness (D j) j).choose_spec.2.choose_spec.1
  have hw0 (j : ℕ) : value (enumerate j).2 (w (D j) j) (n j) = 0 :=
    (witness (D j) j).choose_spec.2.choose_spec.2
  have hlen (j : ℕ) : (D j).period ≤ n j := Nat.le_mul_of_pos_left _ (hk j)
  have hnext (j : ℕ) : n j < (D (j+1)).period := by
    rw [hD, extend_period]
    have := Nat.le_mul_of_pos_right (2*n j+1) (D j).positive
    omega
  have hsize (j : ℕ) : j+1 ≤ (D j).period := by
    induction j with
    | zero => exact le_rfl
    | succ j ih => have := hnext j; have := hlen j; omega
  have hkeep {a b : ℕ} (hab : a ≤ b) {i : ℕ} {z : Letter}
      (hz : (D a).atPos i = some z) : (D b).atPos i = some z := by
    induction b, hab using Nat.le_induction with
    | base => exact hz
    | succ b _ ih =>
      rw [hD]
      exact extend_keeps _ _ _ (hw b) _ _ ih
  have hi (i : ℕ) : i < n i := by have := hsize i; have := hlen i; omega
  let v (i : ℕ) : Letter := w (D i) i i
  have hvi (i : ℕ) : (D (i+1)).atPos i = some (v i) := by
    rw [hD]
    simpa using extend_records (D i) (w (D i) i) (a := 0) (hi i)
  have hv (a i : ℕ) (z : Letter) (hz : (D a).atPos i = some z) : v i = z := by
    rcases le_total a (i+1) with h | h
    · exact Option.some.inj ((hvi i).symm.trans (hkeep h hz))
    · exact Option.some.inj ((hkeep h (hvi i)).symm.trans hz)
  refine ⟨v, ?_⟩
  intro s p
  obtain ⟨j,hj⟩ := hsurj (⟨s,p⟩ : SomePencil)
  have hP : ∃ N : ℕ, 0 < N ∧ ∀ i, segment (fun a => pencil (enumerate j).2 (v a).1) i N = 0 := by
    let Q := (D (j+1)).period
    have hQ : 0 < Q := (D (j+1)).positive
    let L := n j
    have hL : L < Q := hnext j
    refine ⟨2*Q, by omega, ?_⟩
    intro i
    let a := i/Q+1
    let d := a*Q-i
    have he : a*Q = i+(Q-i%Q) := by
      have hmod := Nat.mod_add_div i Q
      have hlt := Nat.mod_lt i hQ
      dsimp [a]
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (i/Q) Q]
      omega
    have hd : d ≤ Q := by dsimp [d]; omega
    have ha : i+d = a*Q := by dsimp [d]; omega
    have hz : segment (fun t => pencil (enumerate j).2 (v t).1) (a*Q) L = 0 := by
      rw [segment_translate, ← hw0 j]
      apply segment_congr
      intro t ht
      simp only [Nat.zero_add]
      have hpres := extend_records (D j) (w (D j) j) (a := a) ht
      rw [← hD] at hpres
      rw [hv (j+1) _ _ hpres]
    have hsplit : 2*Q = d+L+(2*Q-d-L) := by omega
    rw [hsplit, segment_add, segment_add, ha, hz, mul_zero, zero_mul]
  rw [show enumerate j = ⟨s,p⟩ from hj] at hP
  exact hP

end UniformWords

end Pencils

section BandMatrices

open IncidenceAlgebra Matrix Polynomial

def banded (R : Type*) [CommRing R] : Subalgebra R (IncidenceAlgebra R ℕ) where
  carrier := {a | ∃ d : ℕ, ∀ i j, d < j-i → a i j = 0}
  zero_mem' := ⟨0, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨d,hd⟩ ⟨e,he⟩
    exact ⟨max d e, fun i j h => by
      rw [IncidenceAlgebra.add_apply, hd i j ((le_max_left _ _).trans_lt h),
        he i j ((le_max_right _ _).trans_lt h), add_zero]⟩
  one_mem' := ⟨0, fun i j h => by rw [IncidenceAlgebra.one_apply, if_neg (by omega)]⟩
  mul_mem' := by
    rintro a b ⟨d,hd⟩ ⟨e,he⟩
    refine ⟨d+e, fun i j h => ?_⟩
    rw [IncidenceAlgebra.mul_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have h₁ := (Finset.mem_Icc.mp hk).1
    have h₂ := (Finset.mem_Icc.mp hk).2
    by_cases hh : d < k-i
    · simp [hd i k hh]
    · simp [he k j (by omega)]
  algebraMap_mem' := fun c => ⟨0, fun i j hij => by
    change (c • (1 : IncidenceAlgebra R ℕ)) i j = 0
    simp [IncidenceAlgebra.one_apply, show i ≠ j by omega]⟩

def B (R : Type*) [CommRing R] := ↥(banded R)

instance bandRing (R : Type*) [CommRing R] : Ring (B R) := (banded R).toRing

instance bandAlgebra (R : Type*) [CommRing R] : Algebra R (B R) := (banded R).algebra

def entry {R : Type*} [CommRing R] (a : B R) (i j : ℕ) : R := a.1 i j

theorem band_ext {R : Type*} [CommRing R] {a b : B R}
    (h : ∀ i j, entry a i j = entry b i j) : a = b :=
  Subtype.ext (IncidenceAlgebra.ext (fun i j _ => h i j))

@[simp] theorem entry_zero {R : Type*} [CommRing R] (i j : ℕ) :
    entry (0 : B R) i j = 0 := rfl

@[simp] theorem entry_add {R : Type*} [CommRing R] (a b : B R) (i j : ℕ) :
    entry (a+b) i j = entry a i j + entry b i j := rfl

@[simp] theorem entry_sub {R : Type*} [CommRing R] (a b : B R) (i j : ℕ) :
    entry (a-b) i j = entry a i j - entry b i j := rfl

@[simp] theorem entry_one {R : Type*} [CommRing R] (i j : ℕ) :
    entry (1 : B R) i j = if i = j then 1 else 0 := rfl

theorem entry_mul {R : Type*} [CommRing R] (a b : B R) (i j : ℕ) :
    entry (a*b) i j = ∑ t ∈ Finset.Icc i j, entry a i t * entry b t j := rfl

theorem entry_mul_diag {R : Type*} [CommRing R] (a b : B R) (i : ℕ) :
    entry (a*b) i i = entry a i i * entry b i i := by simp [entry_mul]

theorem entry_band {R : Type*} [CommRing R] (a : B R) :
    ∃ d : ℕ, ∀ i j, d < j-i → entry a i j = 0 := a.property

theorem entry_lower {R : Type*} [CommRing R] (a : B R) {i j : ℕ} (h : j < i) :
    entry a i j = 0 := IncidenceAlgebra.apply_eq_zero_of_not_le (by omega) _

def entryHom {R : Type*} [CommRing R] (i j : ℕ) : B R →+ R where
  toFun a := entry a i j
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem entry_sum {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (a : ι → B R) (i j : ℕ) :
    entry (∑ t ∈ s, a t) i j = ∑ t ∈ s, entry (a t) i j := map_sum (entryHom i j) _ _

theorem entry_algebraMap {R : Type*} [CommRing R] (c : R) (i j : ℕ) :
    entry (algebraMap R (B R) c) i j = if i = j then c else 0 := by
  change c * (if i = j then 1 else 0) = _
  split <;> simp

theorem entry_smul {R : Type*} [CommRing R] (c : R) (a : B R) (i j : ℕ) :
    entry (c • a) i j = c * entry a i j := rfl

def bandMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : B R →+* B S where
  toFun a :=
    ⟨⟨fun i j => f (entry a i j), fun i j h => by rw [entry_lower a (by omega), map_zero]⟩,
      by
        obtain ⟨d,hd⟩ := entry_band a
        exact ⟨d, fun i j h => by change f (entry a i j) = 0; rw [hd i j h, map_zero]⟩⟩
  map_one' := by
    apply band_ext
    intro i j
    change f (if i = j then 1 else 0) = _
    rw [entry_one]
    split <;> simp
  map_zero' := by
    apply band_ext
    intro i j
    exact map_zero f
  map_add' a b := by
    apply band_ext
    intro i j
    exact map_add f _ _
  map_mul' a b := by
    apply band_ext
    intro i j
    change f (∑ t ∈ Finset.Icc i j, entry a i t * entry b t j) =
      ∑ t ∈ Finset.Icc i j, f (entry a i t) * f (entry b t j)
    simp only [map_sum, map_mul]

@[simp] theorem entry_bandMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (a : B R) (i j : ℕ) : entry (bandMap f a) i j = f (entry a i j) := rfl

def shift {R : Type*} [CommRing R] (a : ℕ → R) : B R :=
  ⟨⟨fun i j => if j = i+1 then a i else 0, fun i j hij => if_neg (by omega)⟩,
    ⟨1, fun i j h => if_neg (by omega)⟩⟩

@[simp] theorem entry_shift {R : Type*} [CommRing R] (a : ℕ → R) (i j : ℕ) :
    entry (shift a) i j = if j = i+1 then a i else 0 := rfl

theorem shift_mul_entry {R : Type*} [CommRing R] (a : ℕ → R) (b : B R) (i j : ℕ) :
    entry (shift a * b) i j = a i * entry b (i+1) j := by
  rw [entry_mul]
  by_cases h : i+1 ≤ j
  · rw [Finset.sum_eq_single_of_mem (i+1) (Finset.mem_Icc.mpr ⟨by omega,h⟩)]
    · simp
    · intro t _ ht
      simp [ht]
  · rw [entry_lower b (by omega), mul_zero]
    apply Finset.sum_eq_zero
    intro t ht
    have := (Finset.mem_Icc.mp ht).2
    simp [show t ≠ i+1 by omega]

def matrixShift {R : Type*} [CommRing R] {s : ℕ}
    (a : ℕ → Matrix (Fin s) (Fin s) R) : Matrix (Fin s) (Fin s) (B R) :=
  Matrix.of fun i j => shift (fun n => a n i j)

theorem entry_matrixShift_pow {R : Type*} [CommRing R] {s : ℕ}
    (a : ℕ → Matrix (Fin s) (Fin s) R) (n i j : ℕ) (c d : Fin s) :
    entry ((matrixShift a ^ n) c d) i j =
      if j = i+n then segment a i n c d else 0 := by
  induction n generalizing i c with
  | zero =>
    simp only [pow_zero, segment_zero, Matrix.one_apply, Nat.add_zero]
    by_cases h : i = j
    · subst j
      split <;> simp
    · split <;> simp [h, Ne.symm h]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, entry_sum]
    simp only [show ∀ t, matrixShift a c t = shift (fun n => a n c t) from fun _ => rfl,
      shift_mul_entry, ih]
    rw [segment_first, Matrix.mul_apply]
    by_cases h : j = i+(n+1)
    · simp [h, show i + (n+1) = i+1+n by omega]
    · have h' : j ≠ i+1+n := by omega
      simp [h,h']

theorem matrixShift_nil {R : Type*} [CommRing R] {s : ℕ}
    (a : ℕ → Matrix (Fin s) (Fin s) R) {n : ℕ}
    (hz : ∀ i, segment a i n = 0) :
    matrixShift a ^ n = 0 := by
  ext c d : 1
  apply band_ext
  intro i j
  simp [entry_matrixShift_pow, hz]

def Xband : B (Polynomial K) := algebraMap (Polynomial K) _ Polynomial.X

def polynomialBand : Polynomial (B K) →+* B (Polynomial K) :=
  Polynomial.eval₂RingHom' (bandMap Polynomial.C) Xband
    (fun a => (Algebra.commutes _ (bandMap Polynomial.C a)).symm)

@[simp] theorem polynomialBand_C (a : B K) :
    polynomialBand (Polynomial.C a) = bandMap Polynomial.C a := Polynomial.eval₂_C _ _

@[simp] theorem polynomialBand_X : polynomialBand Polynomial.X = Xband :=
  Polynomial.eval₂_X _ _

theorem entry_polynomialBand (p : Polynomial (B K)) (i j n : ℕ) :
    (entry (polynomialBand p) i j).coeff n = entry (p.coeff n) i j := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [polynomialBand.map_add, entry_add, Polynomial.coeff_add, hp, hq,
      Polynomial.coeff_add, entry_add]
  | monomial m a =>
    have h :
        polynomialBand (Polynomial.monomial m a) =
          (Polynomial.X : Polynomial K) ^ m • bandMap Polynomial.C a := by
      change Polynomial.eval₂ _ _ _ = _
      rw [Polynomial.eval₂_monomial, Algebra.smul_def, Xband,
        ← map_pow (algebraMap (Polynomial K) (B (Polynomial K)))]
      exact (Algebra.commutes _ _).symm
    rw [h, entry_smul, entry_bandMap, mul_comm, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_monomial]
    by_cases hn : n = m <;> simp [hn, eq_comm]

theorem polynomialBand_injective : Function.Injective polynomialBand := by
  intro p q hpq
  apply Polynomial.ext
  intro n
  apply band_ext
  intro i j
  rw [← entry_polynomialBand, ← entry_polynomialBand, hpq]

end BandMatrices

section NilAlgebra

open Matrix Polynomial

instance bandRatAlgebra : Algebra ℚ (B K) :=
  Algebra.compHom (B K) (algebraMap ℚ K)

theorem band_rat_smul (q : ℚ) (a : B K) (i j : ℕ) :
    entry (q • a) i j = algebraMap ℚ K q * entry a i j := by
  rw [Algebra.smul_def]
  change entry ((algebraMap K (B K) (algebraMap ℚ K q))*a) i j = _
  rw [← Algebra.smul_def, entry_smul]

def generator (v : ℕ → Letter) (t : Fin 3) : B K := shift (fun n => (v n).1 t)

abbrev Word := Fin 3 × List (Fin 3)
abbrev Term := ℚ × Word

def wordValue (v : ℕ → Letter) (w : Word) : B K :=
  generator v w.1 * (w.2.map (generator v)).prod

def termValue (v : ℕ → Letter) (w : Term) : B K := w.1 • wordValue v w.2

theorem wordValue_mul (v : ℕ → Letter) (a b : Word) :
    wordValue v a * wordValue v b = wordValue v (a.1,a.2 ++ b.1 :: b.2) := by
  simp [wordValue, List.prod_append, mul_assoc]

theorem termValue_mul (v : ℕ → Letter) (a b : Term) :
    termValue v a * termValue v b =
      termValue v (a.1*b.1,a.2.1,a.2.2 ++ b.2.1 :: b.2.2) := by
  simp [termValue, smul_smul, wordValue_mul, mul_comm a.1 b.1]

def HasExpression (v : ℕ → Letter) (x : B K) : Prop :=
  ∃ l : List Term, x = (l.map (termValue v)).sum

theorem expression_add {v : ℕ → Letter} {x y : B K}
    (hx : HasExpression v x) (hy : HasExpression v y) : HasExpression v (x+y) := by
  obtain ⟨l,hl⟩ := hx
  obtain ⟨m,hm⟩ := hy
  exact ⟨l++m, by rw [hl, hm, List.map_append, List.sum_append]⟩

theorem expression_mul {v : ℕ → Letter} {x y : B K}
    (hx : HasExpression v x) (hy : HasExpression v y) : HasExpression v (x*y) := by
  obtain ⟨l,rfl⟩ := hx
  obtain ⟨m,rfl⟩ := hy
  induction l with
  | nil => exact ⟨[], by simp⟩
  | cons a l ih =>
    obtain ⟨n,hn⟩ := ih
    let l' := m.map fun b => (a.1*b.1,a.2.1,a.2.2 ++ b.2.1 :: b.2.2)
    refine ⟨l'++n,?_⟩
    rw [List.map_cons, List.sum_cons, add_mul, hn, List.map_append, List.sum_append]
    congr 1
    unfold l'
    rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    exact List.map_congr_left fun b _ => termValue_mul v a b

theorem expression_smul {v : ℕ → Letter} {x : B K}
    (q : ℚ) (hx : HasExpression v x) : HasExpression v (q • x) := by
  obtain ⟨l,rfl⟩ := hx
  refine ⟨l.map fun w => (q*w.1,w.2),?_⟩
  simp [List.map_map, Function.comp_def, termValue, smul_smul, List.smul_sum]

theorem expression_neg {v : ℕ → Letter} {x : B K} (hx : HasExpression v x) :
    HasExpression v (-x) := by
  have he : (-1 : ℚ) • x = -x := by
    rw [Algebra.smul_def, map_neg, map_one, neg_mul, one_mul]
  exact he ▸ expression_smul (-1) hx

def generated (v : ℕ → Letter) : NonUnitalSubring (B K) where
  carrier := {x | HasExpression v x}
  zero_mem' := ⟨[],rfl⟩
  add_mem' := expression_add
  mul_mem' := expression_mul
  neg_mem' := expression_neg

theorem generator_mem (v : ℕ → Letter) (t : Fin 3) : generator v t ∈ generated v :=
  ⟨[(1,t,[])], by simp [termValue, wordValue]⟩

def shiftPencil {ι : Type*} (v : ℕ → Letter) (root : ι)
    (c : Fin 3 → ι → ι → ℚ) (d : Fin 3 → ι → ℚ) [DecidableEq ι] :
    Matrix ι ι (Polynomial (B K)) :=
  Matrix.of fun i j => ∑ t, (Polynomial.C (c t i j • generator v t) +
    if i = root then Polynomial.X * Polynomial.C (d t j • generator v t) else 0)

def Uniform (v : ℕ → Letter) : Prop :=
  ∀ (s : ℕ) (p : Pencil s), ∃ N : ℕ, 0 < N ∧
      ∀ i, segment (fun a => pencil p (v a).1) i N = 0

theorem shiftPencil_nil_fin {s : ℕ} (v : ℕ → Letter) (hv : Uniform v) (p : Pencil s)
    (root : Fin s) (hr : root.val = 0) :
    IsNilpotent (shiftPencil v root (fun t => p.constant t) p.linear) := by
  classical
  obtain ⟨N,_,hN⟩ := hv s p
  let T := shiftPencil v root (fun t => p.constant t) p.linear
  let f : Matrix (Fin s) (Fin s) (Polynomial (B K)) →+* _ := polynomialBand.mapMatrix
  have hf : Function.Injective f := by
    intro A B h
    ext i j : 1
    apply polynomialBand_injective
    exact congrArg (fun M => M i j) h
  have hm : f T = matrixShift (fun i => pencil p (v i).1) := by
    ext c d : 1
    apply band_ext
    intro i j
    have hc : c = root ↔ c.val = 0 := by
      rw [← hr, Fin.val_inj]
    have hmC (q : ℚ) (t : Fin 3) :
        entry (polynomialBand (Polynomial.C (q • generator v t))) i j =
          if j = i+1 then Polynomial.C ((algebraMap ℚ K q) * (v i).1 t) else 0 := by
      rw [polynomialBand_C, entry_bandMap, band_rat_smul, generator, entry_shift]
      split <;> simp
    have hmX (q : ℚ) (t : Fin 3) :
        entry (polynomialBand (Polynomial.X * Polynomial.C (q • generator v t))) i j =
          Polynomial.X * entry (polynomialBand (Polynomial.C (q • generator v t))) i j := by
      rw [polynomialBand.map_mul, polynomialBand_X, Xband, ← Algebra.smul_def, entry_smul]
    change entry (polynomialBand (T c d)) i j =
      entry (shift (fun i => pencil p (v i).1 c d)) i j
    simp only [T, shiftPencil, Matrix.of_apply, map_sum polynomialBand, polynomialBand.map_add,
      entry_sum, entry_add, hc, entry_shift]
    by_cases h : j = i+1 <;> by_cases h0 : c.val = 0
    · simp only [if_pos h, if_pos h0, hmX, hmC, pencil, Matrix.of_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro t _
      simp only [map_mul]
      ring
    · simp only [if_pos h, if_neg h0, hmC, map_zero, entry_zero, add_zero, pencil,
        Matrix.of_apply, Algebra.algebraMap_self, RingHom.id_apply]
      apply Finset.sum_congr rfl
      intro t _
      rw [map_mul, mul_comm]
    · simp only [if_neg h, if_pos h0, hmX, hmC, mul_zero, add_zero, Finset.sum_const_zero]
    · simp only [if_neg h, if_neg h0, hmC, map_zero, entry_zero, add_zero, Finset.sum_const_zero]
  refine ⟨N, hf ?_⟩
  rw [map_pow, hm, map_zero]
  exact matrixShift_nil _ hN

theorem shiftPencil_nil {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ℕ → Letter)
    (hv : Uniform v) (root : ι) (c : Fin 3 → ι → ι → ℚ) (d : Fin 3 → ι → ℚ) :
    IsNilpotent (shiftPencil v root c d) := by
  classical
  let s := Fintype.card ι
  have hs : 0 < s := Fintype.card_pos_iff.mpr ⟨root⟩
  let e : ι ≃ Fin s := (Fintype.equivFin ι).trans (Equiv.swap (Fintype.equivFin ι root) ⟨0,hs⟩)
  have he : (e root).val = 0 := by simp [e]
  let p : Pencil s := ⟨fun t => Matrix.of fun i j => c t (e.symm i) (e.symm j),
    fun t j => d t (e.symm j)⟩
  have hT : Matrix.reindexRingEquiv (Polynomial (B K)) e (shiftPencil v root c d) =
      shiftPencil v (e root) (fun t => p.constant t) p.linear := by
    ext i j : 1
    change shiftPencil v root c d (e.symm i) (e.symm j) = _
    simp [shiftPencil, p, Equiv.symm_apply_eq]
  have hnil := shiftPencil_nil_fin v hv p (e root) he
  rw [← hT] at hnil
  simpa using hnil.map (Matrix.reindexRingEquiv (Polynomial (B K)) e).symm

theorem nil_of_polynomial_inverse {R : Type*} [Ring R] (x : R) (u : Polynomial R)
    (hu : (1 - Polynomial.X * Polynomial.C x)*u = 1) : IsNilpotent x := by
  have h : u = 1 + Polynomial.X * (Polynomial.C x*u) := by
    rwa [sub_mul, one_mul, mul_assoc, sub_eq_iff_eq_add] at hu
  have hc (n : ℕ) : u.coeff n = x^n := by
    induction n with
    | zero =>
      have hh := congrArg (fun p : Polynomial R => p.coeff 0) h
      simpa using hh
    | succ n ih =>
      have hh := congrArg (fun p : Polynomial R => p.coeff (n+1)) h
      simpa [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_mul, ih, pow_succ'] using hh
  refine ⟨u.natDegree+1, ?_⟩
  rw [← hc, Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)]

abbrev Node (l : List Term) := Σ i : Fin l.length, Fin (l.get i).2.2.length

def target (l : List Term) (i : Fin l.length) (j : ℕ) : Option (Node l) :=
  if h : j < (l.get i).2.2.length then some ⟨i,⟨j,h⟩⟩ else none

def pathConstant (l : List Term) (t : Fin 3) (a b : Option (Node l)) : ℚ :=
  match a with
  | none => 0
  | some ⟨i,j⟩ =>
    if t = (l.get i).2.2.get j ∧ b = target l i (j.val+1) then 1 else 0

def pathLinear (l : List Term) (t : Fin 3) (a : Option (Node l)) : ℚ :=
  ∑ i : Fin l.length, if t = (l.get i).2.1 ∧ a = target l i 0 then (l.get i).1 else 0

theorem single_transition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℕ → Letter) (q : ι → Polynomial (B K)) (a : ι) (t : Fin 3) (c : ℚ) :
    (∑ j, (∑ u, Polynomial.C ((if u = t ∧ j = a then c else 0) • generator v u)) * q j) =
      Polynomial.C (c • generator v t) * q a := by
  classical
  have he (j : ι) :
      (∑ u, Polynomial.C ((if u = t ∧ j = a then c else 0) • generator v u)) =
        if j = a then Polynomial.C (c • generator v t) else 0 := by
    by_cases h : j = a
    · rw [if_pos h]
      have hf (u : Fin 3) :
          Polynomial.C ((if u = t ∧ j = a then c else 0) • generator v u) =
            if u = t then Polynomial.C (c • generator v u) else 0 := by
        by_cases hu : u = t <;>
          simp only [hu, h, and_self, false_and, if_true, if_false, zero_smul, map_zero]
      simp_rw [hf]
      simp
    · simp only [h, and_false, if_false, zero_smul, map_zero, Finset.sum_const_zero]
  simp_rw [he]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, zero_mul]

theorem path_rows (v : ℕ → Letter) (l : List Term)
    (q : Option (Node l) → Polynomial (B K)) (i : Fin l.length) (j : Fin (l.get i).2.2.length) :
    (∑ a, shiftPencil v none (pathConstant l) (pathLinear l) (some ⟨i,j⟩) a * q a) =
      Polynomial.C (generator v ((l.get i).2.2.get j)) * q (target l i (j.val+1)) := by
  classical
  simpa [shiftPencil, pathConstant] using
    (single_transition v q (target l i (j.val+1)) ((l.get i).2.2.get j) 1)

theorem path_root (v : ℕ → Letter) (l : List Term)
    (q : Option (Node l) → Polynomial (B K)) :
    (∑ a, shiftPencil v none (pathConstant l) (pathLinear l) none a * q a) =
      Polynomial.X * ∑ i : Fin l.length,
        Polynomial.C ((l.get i).1 • generator v (l.get i).2.1) * q (target l i 0) := by
  classical
  let F (a : Option (Node l)) (t : Fin 3) (i : Fin l.length) :=
    Polynomial.C ((if t = (l.get i).2.1 ∧ a = target l i 0 then (l.get i).1 else 0) •
      generator v t)
  have hrow (a : Option (Node l)) :
      shiftPencil v none (pathConstant l) (pathLinear l) none a =
        Polynomial.X * ∑ t, ∑ i, F a t i := by
    simp only [shiftPencil, Matrix.of_apply, pathConstant, zero_smul, map_zero,
      if_pos, zero_add, pathLinear, F, Finset.sum_smul, map_sum, Finset.mul_sum]
  simp_rw [hrow, mul_assoc]
  rw [← Finset.mul_sum]
  apply congrArg (fun y => Polynomial.X * y)
  simp_rw [Finset.sum_mul]
  calc
    (∑ a, ∑ t, ∑ i, F a t i * q a) = ∑ a, ∑ i, ∑ t, F a t i * q a :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ t, F a t i * q a := Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp_rw [← Finset.sum_mul]
      exact single_transition v q (target l i 0) (l.get i).2.1 (l.get i).1

def finiteInverse {R : Type*} [Ring R] (x : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range n, x^i

theorem finiteInverse_left {R : Type*} [Ring R] {x : R} {n : ℕ} (h : x^n = 0) :
    (1-x)*finiteInverse x n = 1 := by
  rw [finiteInverse, mul_neg_geom_sum, h, sub_zero]

theorem finiteInverse_right {R : Type*} [Ring R] {x : R} {n : ℕ} (h : x^n = 0) :
    finiteInverse x n*(1-x) = 1 := by
  rw [finiteInverse, geom_sum_mul_neg, h, sub_zero]

theorem nil_expression (v : ℕ → Letter) (hv : Uniform v) (l : List Term) :
    IsNilpotent (l.map (termValue v)).sum := by
  classical
  let T := shiftPencil v (none : Option (Node l)) (pathConstant l) (pathLinear l)
  obtain ⟨n,hn⟩ := shiftPencil_nil v hv none (pathConstant l) (pathLinear l)
  let G := finiteInverse T n
  let q (a : Option (Node l)) := G a none
  have hg : (1-T)*G = 1 := finiteInverse_left hn
  have he (a : Option (Node l)) :
      q a - (∑ j, T a j * q j) = if a = none then 1 else 0 := by
    have h := congrArg (fun M : Matrix (Option (Node l)) (Option (Node l)) (Polynomial (B K)) =>
      M a none) hg
    rw [Matrix.sub_mul, one_mul, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have hstep (i : Fin l.length) (j : Fin (l.get i).2.2.length) :
      q (some ⟨i,j⟩) =
        Polynomial.C (generator v ((l.get i).2.2.get j)) * q (target l i (j.val+1)) := by
    have h := he (some ⟨i,j⟩)
    rw [if_neg (Option.some_ne_none _), show (∑ a, T (some ⟨i,j⟩) a * q a) =
      Polynomial.C (generator v ((l.get i).2.2.get j)) * q (target l i (j.val+1)) from
      path_rows v l q i j] at h
    exact sub_eq_zero.mp h
  have htail (i : Fin l.length) (j : ℕ) :
      q (target l i j) =
        Polynomial.C ((((l.get i).2.2.drop j).map (generator v)).prod) * q none := by
    let L := (l.get i).2.2
    have step (d j : ℕ) (hd : L.length-j = d) :
        q (target l i j) = Polynomial.C (((L.drop j).map (generator v)).prod) * q none := by
      induction d using Nat.strong_induction_on generalizing j with
      | h d ih =>
        by_cases hj : j < L.length
        · have hs := hstep i ⟨j,hj⟩
          rw [show target l i j = some ⟨i,⟨j,hj⟩⟩ by rw [target, dif_pos hj], hs]
          rw [ih (L.length-(j+1)) (by omega) (j+1) rfl]
          rw [List.drop_eq_getElem_cons hj, List.map_cons, List.prod_cons, map_mul, mul_assoc]
          rfl
        · have hnil : L.drop j = [] := List.drop_eq_nil_of_le (by omega)
          rw [target, dif_neg hj, hnil, List.map_nil, List.prod_nil, map_one, one_mul]
    exact step _ j rfl
  have hsum :
      (∑ i : Fin l.length,
        Polynomial.C ((l.get i).1 • generator v (l.get i).2.1) * q (target l i 0)) =
        Polynomial.C ((l.map (termValue v)).sum) * q none := by
    have hvalue (i : Fin l.length) :
        Polynomial.C ((l.get i).1 • generator v (l.get i).2.1) * q (target l i 0) =
          Polynomial.C (termValue v (l.get i)) * q none := by
      rw [htail, List.drop_zero, ← mul_assoc, ← map_mul, smul_mul_assoc, termValue, wordValue]
    simp_rw [hvalue]
    rw [← Finset.sum_mul, ← map_sum, ← List.sum_ofFn]
    exact congrArg (fun w : List (B K) => Polynomial.C w.sum * q none)
      (List.ofFn_getElem_eq_map l (termValue v))
  have hroot := he none
  rw [if_pos rfl, show (∑ a, T none a * q a) =
    Polynomial.X * ∑ i : Fin l.length,
      Polynomial.C ((l.get i).1 • generator v (l.get i).2.1) * q (target l i 0) from
    path_root v l q, hsum, ← mul_assoc] at hroot
  apply nil_of_polynomial_inverse _ (q none)
  rw [sub_mul, one_mul]
  exact hroot

theorem generated_nil (v : ℕ → Letter) (hv : Uniform v) :
    ∀ x : B K, x ∈ generated v → IsNilpotent x := by
  intro x hx
  obtain ⟨l,rfl⟩ := (show HasExpression v x from hx)
  exact nil_expression v hv l

end NilAlgebra

section Counterexample

open Matrix Polynomial

def weightedPoly (v : ℕ → Letter) : Polynomial (B K) :=
  Polynomial.C (generator v 0) + Polynomial.X * Polynomial.C (generator v 1) +
     Polynomial.X^2 * Polynomial.C (generator v 2)

def weight (v : ℕ → Letter) (i : ℕ) : Polynomial K :=
  Polynomial.C ((v i).1 0) + Polynomial.X * Polynomial.C ((v i).1 1) +
     Polynomial.X^2 * Polynomial.C ((v i).1 2)

theorem weight_ne (v : ℕ → Letter) (i : ℕ) : weight v i ≠ 0 := by
  intro h
  apply (v i).2
  funext t
  have ht := congrArg (fun p : Polynomial K => p.coeff t.val) h
  fin_cases t <;>
    simpa [weight, Polynomial.X_mul_C, (Polynomial.commute_X_pow _ 2).eq,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_add] using ht

theorem weightedPoly_map (v : ℕ → Letter) :
    polynomialBand (weightedPoly v) = shift (weight v) := by
  apply band_ext
  intro i j
  have hsm (x : Polynomial K) (a : B (Polynomial K)) :
      entry (algebraMap (Polynomial K) _ x * a) i j = x * entry a i j := by
    rw [← Algebra.smul_def, entry_smul]
  rw [weightedPoly, polynomialBand.map_add, polynomialBand.map_add,
    polynomialBand.map_mul, polynomialBand.map_mul, polynomialBand.map_pow,
    polynomialBand_X, polynomialBand_C, polynomialBand_C, polynomialBand_C]
  change entry (bandMap Polynomial.C (generator v 0) +
    algebraMap (Polynomial K) _ Polynomial.X * bandMap Polynomial.C (generator v 1) +
    (algebraMap (Polynomial K) _ Polynomial.X)^2 * bandMap Polynomial.C (generator v 2)) i j = _
  rw [← map_pow (algebraMap (Polynomial K) (B (Polynomial K)))]
  rw [entry_add, entry_add, hsm, hsm]
  by_cases h : j = i+1
  · simp [generator, h, weight]
  · simp [generator, h]

theorem weightedPoly_noInverse (v : ℕ → Letter) (Y : Polynomial (B K)) :
    ((1 : Polynomial (B K))-weightedPoly v)*Y ≠ 1 := by
  intro he
  let U := polynomialBand Y
  have h : (1-shift (weight v))*U = 1 := by
    calc
      _ = polynomialBand (((1 : Polynomial (B K))-weightedPoly v)*Y) := by
        rw [polynomialBand.map_mul]
        have hsub : polynomialBand ((1 : Polynomial (B K))-weightedPoly v) =
            1-shift (weight v) := by
          exact (polynomialBand.map_sub _ _).trans
            (congrArg₂ (fun a b : B (Polynomial K) => a-b)
              polynomialBand.map_one (weightedPoly_map v))
        exact (congrArg (fun a : B (Polynomial K) => a*U) hsub).symm
      _ = 1 := by rw [he, polynomialBand.map_one]
  have hentry (i j : ℕ) :
      entry U i j - weight v i * entry U (i+1) j = if i = j then 1 else 0 := by
    have hm := congrArg (fun a => entry a i j) h
    rwa [sub_mul, one_mul, entry_sub, shift_mul_entry, entry_one] at hm
  have hne (n i : ℕ) : entry U i (i+n) ≠ 0 := by
    induction n generalizing i with
    | zero =>
      have hm := hentry i i
      rw [entry_lower U (i := i+1) (j := i) (by omega), mul_zero, sub_zero, if_pos rfl] at hm
      simp [hm]
    | succ n ih =>
      have hm := hentry i (i+n+1)
      rw [if_neg (by omega), sub_eq_zero] at hm
      rw [show i+(n+1) = i+n+1 by omega, hm, show i+n+1 = (i+1)+n by omega]
      exact mul_ne_zero (weight_ne v i) (ih (i+1))
  obtain ⟨d,hd⟩ := entry_band U
  exact hne (d+1) 0 (hd 0 (0+(d+1)) (by omega))

def companion {R : Type*} [Ring R] (b c : R) : Matrix (Fin 2) (Fin 2) R :=
  !![b,c;1,0]

theorem companion_inverse {R : Type*} [Ring R] (b c : R)
    (h : IsNilpotent (companion b c)) :
    ∃ u : Polynomial R,
      (1-Polynomial.X*Polynomial.C b-Polynomial.X^2*Polynomial.C c)*u = 1 := by
  classical
  let f : Matrix (Fin 2) (Fin 2) R →+* _ := Polynomial.C.mapMatrix
  let M := f (companion b c)
  let D : Matrix (Fin 2) (Fin 2) (Polynomial R) := Matrix.diagonal (fun _ => Polynomial.X)
  have hDM : Commute D M := by
    show D*M = M*D
    ext i j : 1
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact (Polynomial.commute_X _).eq
  obtain ⟨n,hn⟩ := h
  have hnil : (D*M)^n = 0 := by
    rw [hDM.mul_pow]
    have hM := congrArg f hn
    rw [map_pow, map_zero] at hM
    exact hM ▸ mul_zero (D^n)
  let G := finiteInverse (D*M) n
  have hG : (1-D*M)*G = 1 := finiteInverse_left hnil
  let u := G 0 0
  let v := G 1 0
  have h0 : u - (Polynomial.X*Polynomial.C b*u + Polynomial.X*Polynomial.C c*v) = 1 := by
    have hp := congrArg (fun A => A 0 0) hG
    rw [Matrix.sub_mul, one_mul, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two] at hp
    simpa [u,v,D,M,f,companion, Matrix.diagonal_mul] using hp
  have h1 : v - Polynomial.X*u = 0 := by
    have hp := congrArg (fun A => A 1 0) hG
    rw [Matrix.sub_mul, one_mul, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two] at hp
    simpa [u,v,D,M,f,companion, Matrix.diagonal_mul] using hp
  have hc : Polynomial.X * Polynomial.C c * (Polynomial.X*u) =
      Polynomial.X^2 * Polynomial.C c * u := by
    calc
      _ = Polynomial.X*(Polynomial.C c*Polynomial.X)*u := by simp only [mul_assoc]
      _ = _ := by rw [← Polynomial.X_mul_C, ← mul_assoc, pow_two]
  refine ⟨u,?_⟩
  rw [sub_eq_zero.mp h1, hc] at h0
  rw [sub_mul, sub_mul, one_mul, sub_sub]
  exact h0

theorem companion_not_nil (v : ℕ → Letter) {g : B K}
    (hg : (1-generator v 0)*g = 1) :
    ¬ IsNilpotent (companion (g*generator v 1) (g*generator v 2)) := by
  intro hn
  obtain ⟨u,hu⟩ := companion_inverse _ _ hn
  have hC : ((1 : Polynomial (B K))-Polynomial.C (generator v 0))*Polynomial.C g = 1 := by
    have hm := congrArg (Polynomial.C : B K →+* Polynomial (B K)) hg
    simpa only [map_mul, map_sub, map_one] using hm
  have hfac : (1 : Polynomial (B K))-weightedPoly v =
      ((1 : Polynomial (B K))-Polynomial.C (generator v 0)) *
        (1-Polynomial.X*Polynomial.C (g*generator v 1)-
          Polynomial.X^2*Polynomial.C (g*generator v 2)) := by
    let f : Polynomial (B K) := 1-Polynomial.C (generator v 0)
    have hgb : f * (Polynomial.X * Polynomial.C (g*generator v 1)) =
        Polynomial.X * Polynomial.C (generator v 1) := by
      rw [← mul_assoc, (Polynomial.commute_X f).symm.eq, mul_assoc, map_mul,
        ← mul_assoc f, show f * Polynomial.C g = 1 from hC, one_mul]
    have hgc : f * (Polynomial.X^2 * Polynomial.C (g*generator v 2)) =
        Polynomial.X^2 * Polynomial.C (generator v 2) := by
      rw [← mul_assoc, (Polynomial.commute_X_pow f 2).symm.eq, mul_assoc, map_mul,
        ← mul_assoc f, show f * Polynomial.C g = 1 from hC, one_mul]
    change (1 : Polynomial (B K))-weightedPoly v = f*(1-Polynomial.X*Polynomial.C (g*generator v 1)-
      Polynomial.X^2*Polynomial.C (g*generator v 2))
    rw [mul_sub, mul_sub, mul_one, hgb, hgc]
    unfold f weightedPoly
    abel
  apply weightedPoly_noInverse v (u * Polynomial.C g)
  rw [hfac, mul_assoc, ← mul_assoc _ u, hu, one_mul, hC]

def rationalScalar : ℚ →+* B K := algebraMap ℚ (B K)

theorem scalar_mul_mem {v : ℕ → Letter} {x : B K} (q : ℚ) (hx : x ∈ generated v) :
    rationalScalar q * x ∈ generated v := by
  change HasExpression v (algebraMap ℚ (B K) q * x)
  rw [← Algebra.smul_def]
  exact expression_smul q hx

theorem mul_scalar_mem {v : ℕ → Letter} {x : B K} (q : ℚ) (hx : x ∈ generated v) :
    x * rationalScalar q ∈ generated v :=
  (Algebra.commutes q x) ▸ scalar_mul_mem q hx

def withIdentity (v : ℕ → Letter) : Subring (B K) where
  carrier := {x | ∃ q : ℚ, ∃ y ∈ generated v, x = rationalScalar q + y}
  zero_mem' := ⟨0,0,zero_mem _,by simp⟩
  one_mem' := ⟨1,0,zero_mem _,by simp⟩
  add_mem' := by
    rintro a b ⟨q,x,hx,rfl⟩ ⟨r,y,hy,rfl⟩
    exact ⟨q+r,x+y,add_mem hx hy,by rw [map_add]; abel⟩
  neg_mem' := by
    rintro a ⟨q,x,hx,rfl⟩
    exact ⟨-q,-x,neg_mem hx,by rw [map_neg, neg_add]⟩
  mul_mem' := by
    rintro a b ⟨q,x,hx,rfl⟩ ⟨r,y,hy,rfl⟩
    refine ⟨q*r,rationalScalar q * y + x * rationalScalar r + x*y,
      add_mem (add_mem (scalar_mul_mem q hy) (mul_scalar_mem r hx)) (mul_mem hx hy),?_⟩
    rw [map_mul, add_mul, mul_add, mul_add]
    abel

def nilIdeal (v : ℕ → Letter) : TwoSidedIdeal (withIdentity v) :=
  TwoSidedIdeal.mk' {x | x.val ∈ generated v}
    (show (0 : B K) ∈ generated v from zero_mem _)
    (fun {a b} ha hb => show a.val + b.val ∈ generated v from add_mem ha hb)
    (fun {a} ha => show -a.val ∈ generated v from neg_mem ha)
    (by
      intro a b hb
      obtain ⟨q,y,hy,ha⟩ := a.property
      change a.val*b.val ∈ generated v
      rw [ha, add_mul]
      exact add_mem (scalar_mul_mem q hb) (mul_mem hy hb))
    (by
      intro a b ha
      obtain ⟨q,y,hy,hb⟩ := b.property
      change a.val*b.val ∈ generated v
      rw [hb, mul_add]
      exact add_mem (mul_scalar_mem q ha) (mul_mem ha hy))

@[simp] theorem mem_nilIdeal (v : ℕ → Letter) (x : withIdentity v) :
    x ∈ nilIdeal v ↔ x.val ∈ generated v := by
  simp [nilIdeal]

theorem concrete :
    ∃ (R : Type) (_inst : Ring R), ∃ (I : TwoSidedIdeal R) (W : Matrix (Fin 2) (Fin 2) R),
      Koethe.IsNil I ∧ W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  classical
  obtain ⟨v,hv⟩ := uniform_pencils
  let R := withIdentity v
  let φ : R →+* B K := R.subtype
  let I := nilIdeal v
  have hI : Koethe.IsNil I := by
    intro x hx
    obtain ⟨m,hm⟩ := generated_nil v hv x.val ((mem_nilIdeal v x).mp hx)
    refine ⟨m, Subtype.ext ?_⟩
    exact hm
  let a (t : Fin 3) : R :=
    ⟨generator v t, ⟨0,generator v t,generator_mem v t,by simp⟩⟩
  have ha (t : Fin 3) : a t ∈ I := (mem_nilIdeal v (a t)).mpr (generator_mem v t)
  have hφa (t : Fin 3) : φ (a t) = generator v t := rfl
  obtain ⟨n,hn⟩ := hI (a 0) (ha 0)
  let g : R := finiteInverse (a 0) n
  have hg : (1 - a 0)*g = 1 := finiteInverse_left hn
  let b := g*a 1
  let c := g*a 2
  have hb : b ∈ I := I.mul_mem_left _ _ (ha 1)
  have hc : c ∈ I := I.mul_mem_left _ _ (ha 2)
  let W : Matrix (Fin 2) (Fin 2) R := !![b^2+c,b*c;b,c]
  have hW : companion b c ^ 2 = W := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, W, companion, Matrix.mul_apply, Fin.sum_univ_two]
  have hWI : W ∈ TwoSidedIdeal.matrix (Fin 2) I := by
    rw [TwoSidedIdeal.mem_matrix]
    intro i j
    fin_cases i <;> fin_cases j
    · have hb2 : b^2 ∈ I := by rw [pow_two]; exact I.mul_mem_right b b hb
      exact I.add_mem hb2 hc
    · exact I.mul_mem_left _ _ hc
    · exact hb
    · exact hc
  refine ⟨R,inferInstance,I,W,hI,hWI,?_⟩
  intro hw
  obtain ⟨m,hm⟩ := hw
  have hH : IsNilpotent (companion b c) := ⟨2*m, by rw [pow_mul, hW, hm]⟩
  have hMapped := hH.map φ.mapMatrix
  have hφg : (1-generator v 0)*φ g = 1 := by
    have hp := congrArg φ hg
    simpa only [map_mul, map_sub, map_one, hφa] using hp
  apply companion_not_nil v hφg
  have hcomp : φ.mapMatrix (companion b c) =
      companion (φ g*generator v 1) (φ g*generator v 2) := by
    ext i j : 1
    fin_cases i <;> fin_cases j <;>
      simp [companion, b,c, hφa, RingHom.mapMatrix_apply]
  exact hcomp ▸ hMapped

end Counterexample
end
end KoetheDisproof

theorem OMA.disproof : ¬ (type_of% @Koethe.KotherConjecture.variants.le_KotherRadical) := by
  classical
  intro h
  have hk : ∀ {S : Type _} [Ring S] (A B : Ideal S),
      Koethe.IsNil A → Koethe.IsNil B → Koethe.IsNil (A + B) := by
    intro S _ A B hA hB x hx
    rw [Submodule.add_eq_sup, Submodule.mem_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    exact Koethe.isNil_kotheRadical S _ (add_mem (h hA hy) (h hB hz))
  obtain ⟨R, inst, I, W, hI, hW, hnon⟩ := KoetheDisproof.concrete
  let _ : Ring R := inst
  let e : ULift R ≃+* R := ULift.ringEquiv
  let J : TwoSidedIdeal (ULift R) := I.comap e.toRingHom
  have hJ : Koethe.IsNil J := by
    intro x hx
    obtain ⟨n, hn⟩ := hI (e x) hx
    refine ⟨n, e.injective ?_⟩
    rw [map_pow, map_zero, hn]
  have hmat' : Koethe.IsNil (TwoSidedIdeal.matrix (Fin 2) J) := by
    intro M hM
    exact Koethe.isNil_iSup_of_kotheConjecture hk (fun j => Koethe.isNil_columnIdeal hJ j) M
      (Koethe.mem_iSup_columnIdeal hM)
  let W' := e.symm.toRingHom.mapMatrix W
  have hW' : W' ∈ TwoSidedIdeal.matrix (Fin 2) J := by
    intro i j
    change e (e.symm (W i j)) ∈ I
    rw [e.apply_symm_apply]
    exact hW i j
  apply hnon
  obtain ⟨n, hn⟩ := hmat' W' hW'
  have he : e.toRingHom.mapMatrix W' = W := by
    ext i j : 1
    exact e.apply_symm_apply _
  refine ⟨n, ?_⟩
  have hm := congrArg e.toRingHom.mapMatrix hn
  simpa only [map_pow, he, map_zero] using hm
