import FormalConjectures.HilbertProblems.«17»
import Mathlib

-- Assembly of Hilbert17.hilbert_17th_problem (Hilbert's 17th problem)
-- Credit: @green-notes (reductions R1 and R1.H3.R1, and leaf R1.H3.R1.H1)
-- Credit: @jared-jasinski (leaf R1.H1)
-- Credit: leaf R1.H2 adapts work of Florent Schaffhauser and Artie Khovanov (Apache-2.0), as stated in its header
-- Credit: authors of leaves R1.H3.R1.H2 and R1.H3.R1.H3 are not recorded in their files
-- Credit: @LordMike (assembly)

section Red1

-- Reduction Hilbert17.hilbert_17th_problem.R1 of Hilbert17.hilbert_17th_problem
-- Credit: @green-notes

/-!
Reduces Hilbert's 17th problem (`Hilbert17.hilbert_17th_problem`) to the three pillars of
Artin's 1927 proof, while proving in-file that `MvRatFunc (Fin n) ℝ` is semireal:
1. `H1` (Artin-Schreier preordering theorem): in any semireal field `K`, any element `a` that is
   not a sum of squares is negative in some total field ordering on `K`.
2. `H2` (Existence of real closure): any ordered field embeds order-preservingly into a real
   closed ordered field.
3. `H3` (Tarski transfer principle): any multivariate real polynomial taking a negative value
   in some real closed extension of `ℝ` already takes a negative value on `ℝ`.
-/

namespace OMA.R_Hilbert17_hilbert_17th_problem_R1

open MvPolynomial

def H1 : Prop :=
  ∀ {K : Type} [Field K] [IsSemireal K] {a : K}, ¬ IsSumSq a →
    ∃ (_ : LinearOrder K) (_ : IsStrictOrderedRing K), a < 0

def H2 : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K],
    ∃ (R : Type) (_ : Field R) (_ : LinearOrder R) (_ : IsStrictOrderedRing R)
      (_ : IsRealClosed R) (ι : K →+* R), ∀ x : K, 0 ≤ x → 0 ≤ ι x

def H3 : Prop :=
  ∀ {n : ℕ} {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (j : ℝ →+* R) (f : MvPolynomial (Fin n) ℝ),
    (∃ y : Fin n → R, MvPolynomial.eval₂ j y f < 0) →
    ∃ x : Fin n → ℝ, f.eval x < 0

section Helpers

lemma isSumSq_to_fin_sum {R : Type*} [CommRing R] {x : R} (hx : IsSumSq x) :
    ∃ (m : ℕ) (g : Fin m → R), x = ∑ i, (g i) ^ 2 := by
  induction hx with
  | zero => exact ⟨0, 0, by simp⟩
  | @sq_add a s _ ih =>
    obtain ⟨m, g, rfl⟩ := ih
    refine ⟨m + 1, Fin.cons a g, ?_⟩
    rw [Fin.sum_univ_succ]
    simp [pow_two]

lemma mvRatFunc_isSumSq_denom {n : ℕ} :
    ∀ s : MvRatFunc (Fin n) ℝ, IsSumSq s →
      ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
        ∃ P : MvPolynomial (Fin n) ℝ, (∀ x : Fin n → ℝ, 0 ≤ P.eval x) ∧
          algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D ^ 2 * s =
            algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) P := by
  intro s hs
  induction hs with
  | zero => exact ⟨1, one_ne_zero, 0, fun _ => le_rfl, by simp⟩
  | @sq_add a s _ ih =>
    obtain ⟨D, hD, P, hP, hEq⟩ := ih
    obtain ⟨⟨num, ⟨den, hden⟩⟩, ha_eq⟩ :=
      IsLocalization.surj (nonZeroDivisors (MvPolynomial (Fin n) ℝ)) a
    have hden0 : den ≠ 0 := nonZeroDivisors.ne_zero hden
    refine ⟨den * D, mul_ne_zero hden0 hD, (num * D) ^ 2 + den ^ 2 * P, fun x => ?_, ?_⟩
    · simp only [map_add, map_pow, map_mul]
      have hx := hP x
      positivity
    · have hcalc :
          algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (den * D) ^ 2 * (a * a + s) =
            (a * algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) den *
              algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D) ^ 2 +
            algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) den ^ 2 *
              (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D ^ 2 * s) := by
        rw [map_mul]
        ring
      rw [hcalc, ha_eq, hEq]
      simp only [map_add, map_pow, map_mul]

lemma mvRatFunc_isSemireal (n : ℕ) : IsSemireal (MvRatFunc (Fin n) ℝ) := by
  refine ⟨fun {s} hs h1s => ?_⟩
  obtain ⟨D, hD, P, hP, hEq⟩ := mvRatFunc_isSumSq_denom s hs
  have h0 : algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (D ^ 2 + P) = 0 := by
    calc
      algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (D ^ 2 + P) =
          algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D ^ 2 +
            algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) P := by simp
      _ = algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) D ^ 2 * (1 + s) := by
          rw [← hEq]
          ring
      _ = 0 := by rw [h1s, mul_zero]
  have hDP : D ^ 2 + P = 0 :=
    IsFractionRing.injective (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (by simpa using h0)
  have hDeval : ∀ x : Fin n → ℝ, D.eval x = 0 := by
    intro x
    have hx := congrArg (MvPolynomial.eval x) hDP
    simp only [map_add, map_pow, map_zero] at hx
    have hsq : (D.eval x) ^ 2 = 0 := by nlinarith [sq_nonneg (D.eval x), hP x]
    exact sq_eq_zero_iff.mp hsq
  exact hD (MvPolynomial.funext fun x => by simpa using hDeval x)

end Helpers

theorem main : H1 → H2 → H3 → type_of% @Hilbert17.hilbert_17th_problem := by
  intro h1 h2 h3 n _ f hf
  by_contra hnot
  letI : IsSemireal (MvRatFunc (Fin n) ℝ) := mvRatFunc_isSemireal n
  have hnsq : ¬ IsSumSq (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f) :=
    fun hsq => hnot (isSumSq_to_fin_sum hsq)
  obtain ⟨ordK, hordK, hltK⟩ := h1 hnsq
  letI := ordK
  letI := hordK
  obtain ⟨R, fR, ordR, hordR, hrcR, ι, hι⟩ := h2 (K := MvRatFunc (Fin n) ℝ)
  letI := fR
  letI := ordR
  letI := hordR
  letI := hrcR
  let j : ℝ →+* R :=
    (ι.comp (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ))).comp MvPolynomial.C
  let y : Fin n → R :=
    fun i => ι (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) (MvPolynomial.X i))
  have heval : MvPolynomial.eval₂ j y f =
      ι (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f) := by
    suffices ∀ p : MvPolynomial (Fin n) ℝ, MvPolynomial.eval₂ j y p =
        ι (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) p) from this f
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [j]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p i hp => simp [y, map_mul, hp]
  have hltR : MvPolynomial.eval₂ j y f < 0 := by
    rw [heval]
    have hneg_pos : 0 < -(algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f) :=
      neg_pos.mpr hltK
    have hle_neg : 0 ≤ ι (-(algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f)) :=
      hι _ hneg_pos.le
    have hne_neg : ι (-(algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ) f)) ≠ 0 :=
      (map_ne_zero ι).mpr hneg_pos.ne'
    rw [map_neg] at hle_neg hne_neg
    exact neg_pos.mp (lt_of_le_of_ne hle_neg hne_neg.symm)
  obtain ⟨x, hx⟩ := h3 j f ⟨y, hltR⟩
  exact not_lt_of_ge (hf x) hx

end OMA.R_Hilbert17_hilbert_17th_problem_R1

end Red1

section Leaf1
namespace OMA.Leaf1

-- Step Hilbert17.hilbert_17th_problem.R1.H1 (Artin-Schreier preordering theorem)
-- Credit: @jared-jasinski

namespace Hilbert17H1

private structure IsPreorder {K : Type} [Field K] (P : Set K) : Prop where
  sq_mem : ∀ x : K, x * x ∈ P
  add_mem : ∀ {x y : K}, x ∈ P → y ∈ P → x + y ∈ P
  mul_mem : ∀ {x y : K}, x ∈ P → y ∈ P → x * y ∈ P
  neg_one_not_mem : (-1 : K) ∉ P

private lemma IsPreorder.zero_mem {K : Type} [Field K] {P : Set K} (hP : IsPreorder P) :
    (0 : K) ∈ P := by
  simpa using hP.sq_mem 0

private lemma IsPreorder.one_mem {K : Type} [Field K] {P : Set K} (hP : IsPreorder P) :
    (1 : K) ∈ P := by
  simpa using hP.sq_mem 1

-- Initial preordering P0 = { s + (-a) * t | IsSumSq s ∧ IsSumSq t }.
private lemma init_preorder {K : Type} [Field K] [hSR : IsSemireal K] {a : K} (ha : ¬ IsSumSq a) :
    let P0 : Set K := {x | ∃ s t : K, IsSumSq s ∧ IsSumSq t ∧ x = s + (-a) * t}
    IsPreorder P0 ∧ (-a) ∈ P0 := by
  intro P0
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨0, 1, IsSumSq.zero, IsSumSq.one, by ring⟩⟩
  · intro x
    exact ⟨x * x, 0, IsSumSq.mul_self x, IsSumSq.zero, by ring⟩
  · rintro x y ⟨s1, t1, hs1, ht1, rfl⟩ ⟨s2, t2, hs2, ht2, rfl⟩
    exact ⟨s1 + s2, t1 + t2, hs1.add hs2, ht1.add ht2, by ring⟩
  · rintro x y ⟨s1, t1, hs1, ht1, rfl⟩ ⟨s2, t2, hs2, ht2, rfl⟩
    refine ⟨s1 * s2 + (a * a) * (t1 * t2), s1 * t2 + s2 * t1,
      (hs1.mul hs2).add ((IsSumSq.mul_self a).mul (ht1.mul ht2)),
      (hs1.mul ht2).add (hs2.mul ht1), by ring⟩
  · rintro ⟨s, t, hs, ht, hneg⟩
    by_cases ht0 : t = 0
    · subst ht0
      have h1s : 1 + s = 0 := by linear_combination -hneg
      exact hSR.1 hs h1s
    · have hat : a * t = 1 + s := by linear_combination hneg
      have ha_eq : a = (1 + s) * t * (t⁻¹ * t⁻¹) := by
        field_simp [ht0]
        linear_combination hat
      have hsq : IsSumSq a := by
        rw [ha_eq]
        exact ((IsSumSq.one.add hs).mul ht).mul (IsSumSq.mul_self t⁻¹)
      exact ha hsq

-- Adjoining an element x to a preordering P produces a preordering unless -1 is generated.
private lemma adjoin_total {K : Type} [Field K] {P : Set K} (hP : IsPreorder P)
    (hmax : ∀ Q : Set K, IsPreorder Q → P ⊆ Q → Q = P) (x : K) :
    x ∈ P ∨ -x ∈ P := by
  by_contra hneither
  push Not at hneither
  let Q : Set K := {z | ∃ u v : K, u ∈ P ∧ v ∈ P ∧ z = u + x * v}
  have hPQ : P ⊆ Q := fun u hu => ⟨u, 0, hu, hP.zero_mem, by ring⟩
  have hxQ : x ∈ Q := ⟨0, 1, hP.zero_mem, hP.one_mem, by ring⟩
  have hQ_not_prop : (-1 : K) ∈ Q := by
    by_contra hneg1
    have hQ : IsPreorder Q := by
      refine ⟨?_, ?_, ?_, hneg1⟩
      · intro z; exact hPQ (hP.sq_mem z)
      · rintro z1 z2 ⟨u1, v1, hu1, hv1, rfl⟩ ⟨u2, v2, hu2, hv2, rfl⟩
        exact ⟨u1 + u2, v1 + v2, hP.add_mem hu1 hu2, hP.add_mem hv1 hv2, by ring⟩
      · rintro z1 z2 ⟨u1, v1, hu1, hv1, rfl⟩ ⟨u2, v2, hu2, hv2, rfl⟩
        exact ⟨u1 * u2 + (x * x) * (v1 * v2), u1 * v2 + u2 * v1,
          hP.add_mem (hP.mul_mem hu1 hu2) (hP.mul_mem (hP.sq_mem x) (hP.mul_mem hv1 hv2)),
          hP.add_mem (hP.mul_mem hu1 hv2) (hP.mul_mem hu2 hv1), by ring⟩
    have hQP : Q = P := hmax Q hQ hPQ
    exact hneither.1 (hQP ▸ hxQ)
  obtain ⟨u, v, hu, hv, hneg⟩ := hQ_not_prop
  by_cases hv0 : v = 0
  · subst hv0
    have h1u : (-1 : K) = u := by linear_combination hneg
    exact hP.neg_one_not_mem (h1u ▸ hu)
  · have hxv : -x * v = 1 + u := by linear_combination hneg
    have hnx_eq : -x = (1 + u) * v * (v⁻¹ * v⁻¹) := by
      field_simp [hv0]
      linear_combination hxv
    have hnx_mem : -x ∈ P := by
      rw [hnx_eq]
      exact hP.mul_mem (hP.mul_mem (hP.add_mem hP.one_mem hu) hv) (hP.sq_mem v⁻¹)
    exact hneither.2 hnx_mem

private lemma antisymm_of_preorder {K : Type} [Field K] {P : Set K} (hP : IsPreorder P)
    {x : K} (hx : x ∈ P) (hnx : -x ∈ P) : x = 0 := by
  by_contra hx0
  have hneg1 : (-1 : K) = (-x) * x * (x⁻¹ * x⁻¹) := by
    field_simp [hx0]
  exact hP.neg_one_not_mem (hneg1 ▸ hP.mul_mem (hP.mul_mem hnx hx) (hP.sq_mem x⁻¹))

-- Maximal preordering extending P0 via Zorn's lemma.
private lemma exists_max_preorder {K : Type} [Field K] {P0 : Set K} (hP0 : IsPreorder P0) :
    ∃ P : Set K, P0 ⊆ P ∧ IsPreorder P ∧ ∀ Q : Set K, IsPreorder Q → P ⊆ Q → Q = P := by
  let S : Set (Set K) := {Q | P0 ⊆ Q ∧ IsPreorder Q}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hch hne
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨s0, hs0⟩ := hne
      exact (hc hs0).1.trans (Set.subset_sUnion_of_mem hs0)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro x
        obtain ⟨s0, hs0⟩ := hne
        exact Set.mem_sUnion.mpr ⟨s0, hs0, (hc hs0).2.sq_mem x⟩
      · intro x y hx hy
        obtain ⟨s1, hs1, hx1⟩ := Set.mem_sUnion.mp hx
        obtain ⟨s2, hs2, hy2⟩ := Set.mem_sUnion.mp hy
        rcases hch.total hs1 hs2 with h12 | h21
        · exact Set.mem_sUnion.mpr ⟨s2, hs2, (hc hs2).2.add_mem (h12 hx1) hy2⟩
        · exact Set.mem_sUnion.mpr ⟨s1, hs1, (hc hs1).2.add_mem hx1 (h21 hy2)⟩
      · intro x y hx hy
        obtain ⟨s1, hs1, hx1⟩ := Set.mem_sUnion.mp hx
        obtain ⟨s2, hs2, hy2⟩ := Set.mem_sUnion.mp hy
        rcases hch.total hs1 hs2 with h12 | h21
        · exact Set.mem_sUnion.mpr ⟨s2, hs2, (hc hs2).2.mul_mem (h12 hx1) hy2⟩
        · exact Set.mem_sUnion.mpr ⟨s1, hs1, (hc hs1).2.mul_mem hx1 (h21 hy2)⟩
      · intro hneg1
        obtain ⟨s0, hs0, hmem⟩ := Set.mem_sUnion.mp hneg1
        exact (hc hs0).2.neg_one_not_mem hmem
  obtain ⟨P, hP0P, hPmax⟩ := zorn_subset_nonempty S hchain P0 ⟨Set.Subset.rfl, hP0⟩
  have hPS : P ∈ S := hPmax.prop
  refine ⟨P, hP0P, hPS.2, fun Q hQ hPQ => ?_⟩
  exact (hPmax.eq_of_subset ⟨hP0P.trans hPQ, hQ⟩ hPQ).symm

end Hilbert17H1

theorem solve : OMA.R_Hilbert17_hilbert_17th_problem_R1.H1 := by
  classical
  intro K _ _ a ha
  obtain ⟨hP0, hna0⟩ := Hilbert17H1.init_preorder ha
  obtain ⟨P, hP0P, hP, hmax⟩ := Hilbert17H1.exists_max_preorder hP0
  have htotal : ∀ x : K, x ∈ P ∨ -x ∈ P := Hilbert17H1.adjoin_total hP hmax
  letI leInst : LE K := ⟨fun x y => y - x ∈ P⟩
  letI ltInst : LT K := ⟨fun x y => y - x ∈ P ∧ x ≠ y⟩
  have hle_iff : ∀ x y : K, x ≤ y ↔ y - x ∈ P := fun _ _ => Iff.rfl
  have hlt_iff : ∀ x y : K, x < y ↔ y - x ∈ P ∧ x ≠ y := fun _ _ => Iff.rfl
  let linOrd : LinearOrder K :=
    { le := leInst.le
      lt := ltInst.lt
      le_refl := fun x => by change x - x ∈ P; simpa using hP.zero_mem
      le_trans := fun x y z hxy hyz => by
        change z - x ∈ P
        have : z - x = (z - y) + (y - x) := by ring
        rw [this]
        exact hP.add_mem hyz hxy
      le_antisymm := fun x y hxy hyx => by
        have hneg : -(y - x) = x - y := by ring
        have h0 : y - x = 0 := Hilbert17H1.antisymm_of_preorder hP hxy (hneg ▸ hyx)
        exact (sub_eq_zero.mp h0).symm
      lt_iff_le_not_ge := fun x y => by
        change (y - x ∈ P ∧ x ≠ y) ↔ (y - x ∈ P ∧ ¬ x - y ∈ P)
        constructor
        · rintro ⟨hxy, hne⟩
          refine ⟨hxy, fun hyx => hne ?_⟩
          have hneg : -(y - x) = x - y := by ring
          exact (sub_eq_zero.mp (Hilbert17H1.antisymm_of_preorder hP hxy (hneg ▸ hyx))).symm
        · rintro ⟨hxy, hnot⟩
          refine ⟨hxy, ?_⟩
          rintro rfl
          exact hnot (by simpa using hP.zero_mem)
      le_total := fun x y => by
        change y - x ∈ P ∨ x - y ∈ P
        rcases htotal (y - x) with h | h
        · exact Or.inl h
        · exact Or.inr (by convert h using 1; ring)
      toDecidableLE := Classical.decRel _ }
  letI : LinearOrder K := linOrd
  have hstrict : IsStrictOrderedRing K :=
    { add_le_add_left := fun x y hxy z => by
        change (y + z) - (x + z) ∈ P
        have : (y + z) - (x + z) = y - x := by ring
        rw [this]
        exact hxy
      le_of_add_le_add_left := fun x y z h => by
        change z - y ∈ P
        have h' : (x + z) - (x + y) ∈ P := h
        have : z - y = (x + z) - (x + y) := by ring
        rw [this]
        exact h'
      zero_le_one := by
        change (1 : K) - 0 ∈ P
        simpa using hP.one_mem
      mul_lt_mul_of_pos_left := fun x hx y z hyz => by
        have hxP : x ∈ P := by simpa using hx.1
        have hx0 : x ≠ 0 := hx.2.symm
        have hyzP : z - y ∈ P := hyz.1
        have hyz0 : z - y ≠ 0 := sub_ne_zero.mpr hyz.2.symm
        refine ⟨?_, ?_⟩
        · change x * z - x * y ∈ P
          have : x * z - x * y = x * (z - y) := by ring
          rw [this]
          exact hP.mul_mem hxP hyzP
        · intro heq
          have : x * (z - y) = 0 := by linear_combination -heq
          exact mul_ne_zero hx0 hyz0 this
      mul_lt_mul_of_pos_right := fun x hx y z hyz => by
        have hxP : x ∈ P := by simpa using hx.1
        have hx0 : x ≠ 0 := hx.2.symm
        have hyzP : z - y ∈ P := hyz.1
        have hyz0 : z - y ≠ 0 := sub_ne_zero.mpr hyz.2.symm
        refine ⟨?_, ?_⟩
        · change z * x - y * x ∈ P
          have : z * x - y * x = (z - y) * x := by ring
          rw [this]
          exact hP.mul_mem hyzP hxP
        · intro heq
          have : (z - y) * x = 0 := by linear_combination -heq
          exact mul_ne_zero hyz0 hx0 this }
  refine ⟨linOrd, hstrict, ?_⟩
  change (0 : K) - a ∈ P ∧ a ≠ 0
  refine ⟨by simpa using hP0P hna0, fun ha0 => ha (ha0 ▸ IsSumSq.zero)⟩

end OMA.Leaf1
end Leaf1

section Leaf2
namespace OMA.Leaf2

/- The preordering argument and odd irreducible factor lemma adapt work of
Florent Schaffhauser and Artie Khovanov in artie2000/real_closed_field,
RealClosedField/Algebra/Order/Ring/Ordering/Extend.lean and RealClosedField/Upstream.lean,
revision 24ec7b819140a17848e88e7d6decde198a140918. Used under Apache-2.0.
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Copyright (c) 2025 Artie Khovanov. All rights reserved.

For odd-degree extensions, lift a putative sum of squares equal to negative one
to a positive polynomial. A smaller odd-degree factor would vanish in an
ordered extension by induction, contradicting positivity there.
Finally use Zorn on signed cones in an algebraic closure to absorb both kinds
of ordered algebraic extensions. -/
open Polynomial
namespace LocalReal17

lemma order_preordering {F : Type} [Field F] (P : RingPreordering F) :
    ∃ (_ : LinearOrder F) (_ : IsStrictOrderedRing F), ∀ z ∈ P, 0 ≤ z := by
  classical
  let good (B : Subsemiring F) := (∀ x : F, x*x ∈ B) ∧ -1 ∉ B
  have chain : ∀ c ⊆ {B | good B}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ B ∈ {B | good B}, ∀ u ∈ c, u ≤ B := by
    intro c hc hdir y hy
    letI : Nonempty c := ⟨⟨y,hy⟩⟩
    let B := ⨆ u : c, u.val
    have mem (x : F) : x ∈ B ↔ ∃ u : c, x ∈ u.val :=
      Subsemiring.mem_iSup_of_directed hdir.directedOn.directed_val
    refine ⟨B,⟨fun x => (mem _).mpr ⟨⟨y,hy⟩,(hc hy).1 x⟩,?_⟩,fun u hu => le_iSup (fun v : c => v.val) ⟨u,hu⟩⟩
    intro h
    obtain ⟨u,hu⟩ := (mem _).mp h
    exact (hc u.property).2 hu
  obtain ⟨B,hPB,hB⟩ := zorn_le_nonempty₀ {B | good B} chain P.toSubsemiring
    ⟨P.mul_self_mem,P.neg_one_notMem⟩
  let M := RingPreordering.mk' (B : Set F) B.add_mem B.mul_mem hB.prop.1 hB.prop.2
  have total (a : F) : a ∈ B ∨ -a ∈ B := by
    by_cases ha : -a ∈ B
    · exact Or.inr ha
    let T := Subsemiring.closure (insert a (B : Set F))
    have inc : B ≤ T := fun x hx => Subsemiring.subset_closure (Set.mem_insert_of_mem _ hx)
    have repr {x : F} (hx : x ∈ T) : ∃ u ∈ B, ∃ v ∈ B, x = u+a*v := by
      induction hx using Subsemiring.closure_induction with
      | mem x hx =>
        rcases hx with rfl|hx
        · exact ⟨0,B.zero_mem,1,B.one_mem,by ring⟩
        · exact ⟨x,hx,0,B.zero_mem,by ring⟩
      | zero => exact ⟨0,B.zero_mem,0,B.zero_mem,by ring⟩
      | one => exact ⟨1,B.one_mem,0,B.zero_mem,by ring⟩
      | add x y _ _ hx hy =>
        obtain ⟨u,hu,v,hv,rfl⟩ := hx
        obtain ⟨s,hs,t,ht,rfl⟩ := hy
        exact ⟨u+s,B.add_mem hu hs,v+t,B.add_mem hv ht,by ring⟩
      | mul x y _ _ hx hy =>
        obtain ⟨u,hu,v,hv,rfl⟩ := hx
        obtain ⟨s,hs,t,ht,rfl⟩ := hy
        exact ⟨u*s + a*a*(v*t),B.add_mem (B.mul_mem hu hs) (B.mul_mem (hB.prop.1 a) (B.mul_mem hv ht)),
          u*t+s*v,B.add_mem (B.mul_mem hu ht) (B.mul_mem hs hv),by ring⟩
    have proper : -1 ∉ T := by
      intro h
      obtain ⟨u,hu,v,hv,e⟩ := repr h
      by_cases h0 : v = 0
      · have hu' : (-1 : F) = u := by simpa [h0] using e
        exact hB.prop.2 (hu' ▸ hu)
      · have eq : -a = (1+u)*v⁻¹ := by field_simp; linear_combination e
        exact ha (eq ▸ B.mul_mem (B.add_mem B.one_mem hu) (RingPreordering.inv_mem (P := M) hv))
    exact Or.inl <| hB.le_of_ge ⟨fun x => inc (hB.prop.1 x),proper⟩ inc
      (Subsemiring.subset_closure (Set.mem_insert a _))
  let C : RingCone F := ⟨B,fun hx hn => M.eq_zero_of_mem_of_neg_mem hx hn⟩
  letI : HasMemOrNegMem C := ⟨total⟩
  letI : LinearOrder F := .mkOfAddGroupCone C
  letI : IsOrderedRing F := IsOrderedRing.mkOfCone C
  refine ⟨inferInstance,inferInstance,fun z hz => ?_⟩
  change z-0 ∈ B
  simpa using hPB hz

lemma quad_re_nonneg {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {a c : F} (ha : 0 ≤ a) (hc : 0 ≤ c) (y : QuadraticAlgebra F a 0) :
    0 ≤ ((algebraMap F (QuadraticAlgebra F a 0) c) * (y*y)).re := by
  rw [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im,
    mul_zero, zero_mul, add_zero, QuadraticAlgebra.re_mul]
  exact mul_nonneg hc (add_nonneg (mul_self_nonneg _) (by nlinarith [mul_nonneg ha (mul_self_nonneg y.im)]))

lemma square_extension (order : ∀ {E : Type} [Field E] (P : RingPreordering E),
    ∃ (_ : LinearOrder E) (_ : IsStrictOrderedRing E), ∀ z ∈ P, 0 ≤ z)
    {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (a : F) (ha : 0 ≤ a) (hns : ¬ IsSquare a) :
    ∃ (E : Type) (_ : Field E) (_ : LinearOrder E) (_ : IsStrictOrderedRing E)
      (_ : Algebra F E) (_ : Algebra.IsAlgebraic F E),
      (∀ x : F, 0 ≤ x → 0 ≤ algebraMap F E x) ∧ IsSquare (algebraMap F E a) := by
  classical
  letI : Fact (∀ r : F, r ^ 2 ≠ a + 0 * r) := ⟨fun r h => hns ⟨r,by simpa [pow_two] using h.symm⟩⟩
  let E := QuadraticAlgebra F a 0
  let W : Set E := {z | ∃ c : F, 0 ≤ c ∧ ∃ y : E, z = algebraMap F E c * (y*y)}
  let S := AddSubmonoid.closure W
  have mulc {x y : E} (hx : x ∈ S) (hy : y ∈ S) : x*y ∈ S := by
    apply AddSubmonoid.closure_induction₂ (motive := fun x y _ _ => x*y ∈ S) ?_ ?_ ?_ ?_ ?_ hx hy
    · rintro _ _ ⟨c,hc,u,rfl⟩ ⟨d,hd,v,rfl⟩
      exact AddSubmonoid.subset_closure ⟨c*d,mul_nonneg hc hd,u*v,by rw [map_mul]; ring⟩
    · intro y _; simpa using S.zero_mem
    · intro x _; simpa using S.zero_mem
    · intro x y z _ _ _ h k; simpa [add_mul] using S.add_mem h k
    · intro x y z _ _ _ h k; simpa [mul_add] using S.add_mem h k
  have positive {x : E} (hx : x ∈ S) : 0 ≤ x.re := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨c,hc,y,rfl⟩ := hx
      exact quad_re_nonneg ha hc y
    | zero => exact le_rfl
    | add x y _ _ hx hy => exact add_nonneg hx hy
  let P := RingPreordering.mk' (S : Set E) S.add_mem mulc
    (fun y => AddSubmonoid.subset_closure ⟨1,zero_le_one,y,by simp⟩)
    (fun h => by have h' := positive h; change (0 : F) ≤ -1 at h'; linarith)
  obtain ⟨lo,strict,hP⟩ := order P
  refine ⟨E,inferInstance,lo,strict,inferInstance,inferInstance,?_,?_⟩
  · intro x hx
    exact hP _ (AddSubmonoid.subset_closure ⟨x,hx,1,by simp⟩)
  · refine ⟨QuadraticAlgebra.omega,?_⟩
    exact (QuadraticAlgebra.omega_mul_omega_eq_mk (R := F) (a := a) (b := 0)).symm

lemma odd_factor {F : Type} [Field F] {f : F[X]} (hf : Odd f.natDegree) :
    ∃ g : F[X], Odd g.natDegree ∧ g.Monic ∧ Irreducible g ∧ g ∣ f := by
  induction h : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    have hu : ¬ IsUnit f := not_isUnit_of_natDegree_pos _ (Odd.pos hf)
    rcases exists_monic_irreducible_factor f hu with ⟨g,gm,gi,gd⟩
    by_cases ho : Odd g.natDegree
    · exact ⟨g,ho,gm,gi,gd⟩
    · rcases gd with ⟨k,rfl⟩
      have ke : k ≠ 0 := by rintro rfl; simp at hf
      have deg := natDegree_mul gi.ne_zero ke
      have kg : Odd k.natDegree := by grind
      obtain ⟨p,hp,pm,pi,pd⟩ := ih k.natDegree (by have := gi.natDegree_pos; omega) kg rfl
      exact ⟨p,hp,pm,pi,dvd_trans pd (dvd_mul_left ..)⟩

lemma pos_even_add {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {p q : F[X]} (hp : 0 < p.leadingCoeff) (hq : 0 < q.leadingCoeff)
    (he : Even p.natDegree) (hf : Even q.natDegree) :
    0 < (p+q).leadingCoeff ∧ Even (p+q).natDegree := by
  rcases lt_trichotomy p.degree q.degree with h|h|h
  · simpa [leadingCoeff_add_of_degree_lt h,natDegree_add_eq_right_of_degree_lt h] using And.intro hq hf
  · have hn := (add_pos hp hq).ne'
    have hd : (p+q).degree = p.degree := by rw [degree_add_eq_of_leadingCoeff_add_ne_zero hn,h,max_self]
    exact ⟨by rw [leadingCoeff_add_of_degree_eq h hn]; exact add_pos hp hq,
      by rwa [natDegree,hd]⟩
  · simpa [leadingCoeff_add_of_degree_lt' h,natDegree_add_eq_left_of_degree_lt h] using And.intro hp he

lemma lift_positive {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {f : F[X]} (hf : f.Monic) (hi : Irreducible f) {s : AdjoinRoot f} (hs : IsSumSq s) :
    ∃ p : F[X], AdjoinRoot.mk f p = 1+s ∧ 0 < p.leadingCoeff ∧ Even p.natDegree ∧
      p.natDegree < 2*f.natDegree ∧
      ∀ (E : Type) [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra F E]
        (r : E), 0 < p.aeval r := by
  have hn := hi.natDegree_pos
  induction hs with
  | zero =>
    refine ⟨1,by simp,by simp,by simp,by simp; omega,?_⟩
    intro E _ _ _ _ r; simp
  | @sq_add y s _ ih =>
    obtain ⟨p,hp,hc,he,hd,hpos⟩ := ih
    obtain ⟨b,hb⟩ := AdjoinRoot.mk_surjective (g := f) y
    let t := b %ₘ f
    have hdeg : t.natDegree < f.natDegree := natDegree_modByMonic_lt b hf (fun e => hi.not_isUnit (e ▸ isUnit_one))
    have ht : AdjoinRoot.mk f t = y := by
      rw [← hb]; simpa [t] using AdjoinRoot.mk_leftInverse hf (AdjoinRoot.mk f b)
    refine ⟨t*t+p,by rw [map_add,map_mul,ht,hp]; ring,?_,?_,?_,?_⟩
    · by_cases hz : t = 0
      · simpa [hz] using hc
      · exact (pos_even_add (p := t*t) (by rw [leadingCoeff_mul]; exact mul_self_pos.mpr (leadingCoeff_ne_zero.mpr hz)) hc
          (by rw [natDegree_mul hz hz]; exact Even.add_self _) he).1
    · by_cases hz : t = 0
      · simpa [hz] using he
      · exact (pos_even_add (p := t*t) (by rw [leadingCoeff_mul]; exact mul_self_pos.mpr (leadingCoeff_ne_zero.mpr hz)) hc
          (by rw [natDegree_mul hz hz]; exact Even.add_self _) he).2
    · apply lt_of_le_of_lt (natDegree_add_le ..)
      exact max_lt (by have := natDegree_mul_le (p := t) (q := t); omega) hd
    · intro E _ _ _ _ r
      simpa only [map_add,map_mul] using add_pos_of_nonneg_of_pos (mul_self_nonneg (t.aeval r)) (hpos E r)

lemma odd_extension (order : ∀ {E : Type} [Field E] (P : RingPreordering E),
    ∃ (_ : LinearOrder E) (_ : IsStrictOrderedRing E), ∀ z ∈ P, 0 ≤ z)
    {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (sq : ∀ a : F, 0 ≤ a → IsSquare a) (f : F[X]) (hf : Odd f.natDegree) :
    ∃ (E : Type) (_ : Field E) (_ : LinearOrder E) (_ : IsStrictOrderedRing E)
      (_ : Algebra F E) (_ : Algebra.IsAlgebraic F E),
      (∀ x : F, 0 ≤ x → 0 ≤ algebraMap F E x) ∧ ∃ y : E, f.aeval y = 0 := by
  classical
  induction n : f.natDegree using Nat.strong_induction_on generalizing f with | h n ih =>
    obtain ⟨g,go,gm,gi,gd⟩ := odd_factor hf
    have fne : f ≠ 0 := by rintro rfl; simp at hf
    have gle := natDegree_le_of_dvd gd fne
    letI : Fact (Irreducible g) := ⟨gi⟩
    have proper : ¬ IsSumSq (-1 : AdjoinRoot g) := by
      intro hs
      obtain ⟨p,hp,hc,he,hd,hpos⟩ := lift_positive gm gi hs
      obtain ⟨q,hq⟩ := AdjoinRoot.mk_eq_zero.mp (show AdjoinRoot.mk g p = 0 by simpa using hp)
      have pne : p ≠ 0 := by intro h; simp [h] at hc
      have qne : q ≠ 0 := by rintro rfl; simp_all
      have ds : p.natDegree = g.natDegree + q.natDegree := by rw [hq,natDegree_mul gi.ne_zero qne]
      have qo : Odd q.natDegree := by grind
      obtain ⟨E,_,_,_,_,_,_,r,hr⟩ := ih q.natDegree (by omega) q qo rfl
      have hz : p.aeval r = 0 := by rw [hq,map_mul,hr,mul_zero]
      exact (hpos E r).ne' hz
    let P := RingPreordering.mk' {z : AdjoinRoot g | IsSumSq z}
      (fun h k => IsSumSq.add h k) (fun h k => IsSumSq.mul h k) IsSumSq.mul_self proper
    obtain ⟨lo,strict,hP⟩ := order P
    letI : Module.Finite F (AdjoinRoot g) := Module.Finite.of_basis (AdjoinRoot.powerBasis gi.ne_zero).basis
    refine ⟨AdjoinRoot g,inferInstance,lo,strict,inferInstance,inferInstance,?_,AdjoinRoot.root g,?_⟩
    · intro x hx
      obtain ⟨r,hr⟩ := sq x hx
      rw [hr,map_mul]
      exact mul_self_nonneg _
    · rw [AdjoinRoot.aeval_eq]
      exact AdjoinRoot.mk_eq_zero.mpr gd

lemma image_properties {F Ω : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Field Ω]
    (j : F →+* Ω) :
    let P := (RingCone.nonneg F).toSubsemiring.map j
    (∀ x ∈ P, -x ∈ P → x = 0) ∧ (∀ x ∈ P, x⁻¹ ∈ P) ∧
    ∀ x ∈ P, ∀ y ∈ P, x-y ∈ P ∨ y-x ∈ P := by
  constructor
  · rintro _ ⟨a,ha,rfl⟩ ⟨b,hb,e⟩
    change 0 ≤ a at ha
    change 0 ≤ b at hb
    have he : b = -a := j.injective (by simpa using e)
    rw [he] at hb
    simp [show a=0 by linarith]
  constructor
  · rintro _ ⟨a,ha,rfl⟩
    exact ⟨a⁻¹, inv_nonneg.mpr ha, map_inv₀ _ _⟩
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    rcases le_total b a with h|h
    · exact Or.inl ⟨a-b, sub_nonneg.mpr h, map_sub _ _ _⟩
    · exact Or.inr ⟨b-a, sub_nonneg.mpr h, map_sub _ _ _⟩

lemma cone_field {Ω : Type} [Field Ω] (P : Subsemiring Ω)
    (hinv : ∀ x ∈ P, x⁻¹ ∈ P) (hdiff : ∀ x ∈ P, ∀ y ∈ P, x-y ∈ P ∨ y-x ∈ P) :
    ∃ L : Subfield Ω, ∀ x : Ω, x ∈ L ↔ x ∈ P ∨ -x ∈ P := by
  refine ⟨{
    carrier := {x | x ∈ P ∨ -x ∈ P}
    zero_mem' := Or.inl P.zero_mem
    one_mem' := Or.inl P.one_mem
    neg_mem' := fun h => by rcases h with h|h; exact Or.inr (by simpa only [neg_neg] using h); exact Or.inl h
    inv_mem' := fun x h => by rcases h with h|h; exact Or.inl (hinv _ h); exact Or.inr (by simpa only [inv_neg] using hinv _ h)
    mul_mem' := fun {a b} ha hb => by
      rcases ha with h|h <;> rcases hb with k|k
      · exact Or.inl (P.mul_mem h k)
      · exact Or.inr (by simpa only [mul_neg,neg_mul,neg_neg] using P.mul_mem h k)
      · exact Or.inr (by simpa only [mul_neg,neg_mul,neg_neg] using P.mul_mem h k)
      · exact Or.inl (by simpa only [mul_neg,neg_mul,neg_neg] using P.mul_mem h k)
    add_mem' := fun {a b} ha hb => by
      rcases ha with h|h <;> rcases hb with k|k
      · exact Or.inl (P.add_mem h k)
      · simpa [sub_eq_add_neg, neg_add, neg_neg, add_comm] using hdiff _ h _ k
      · simpa [sub_eq_add_neg, neg_add, neg_neg, add_comm] using hdiff _ k _ h
      · exact Or.inr (by simpa [neg_add, add_comm] using P.add_mem h k) },fun _ => Iff.rfl⟩

lemma maximal_extension (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ∃ (F : Type) (_ : Field F) (_ : LinearOrder F) (_ : IsStrictOrderedRing F)
      (j : K →+* F), (∀ a : K, 0 ≤ a → 0 ≤ j a) ∧
      ∀ (E : Type) [Field E] [LinearOrder E] [IsStrictOrderedRing E] [Algebra F E]
      [Algebra.IsAlgebraic F E], (∀ a : F, 0 ≤ a → 0 ≤ algebraMap F E a) →
        Function.Surjective (algebraMap F E) := by
  classical
  let Ω := AlgebraicClosure K
  let j := algebraMap K Ω
  let good (P : Subsemiring Ω) : Prop :=
    (∀ x ∈ P, -x ∈ P → x = 0) ∧ (∀ x ∈ P, x⁻¹ ∈ P) ∧
    ∀ x ∈ P, ∀ y ∈ P, x-y ∈ P ∨ y-x ∈ P
  let P₀ := (RingCone.nonneg K).toSubsemiring.map j
  have init : good P₀ := image_properties j
  have chain : ∀ c ⊆ {P | good P}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {P | good P}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    letI : Nonempty c := ⟨⟨y,hy⟩⟩
    let U := ⨆ u : c, u.val
    have dir : Directed (· ≤ ·) (fun u : c => u.val) := hchain.directedOn.directed_val
    have mem (x : Ω) : x ∈ U ↔ ∃ u : c, x ∈ u.val := Subsemiring.mem_iSup_of_directed dir
    have both {a b : Ω} (ha : a ∈ U) (hb : b ∈ U) :
        ∃ u : c, a ∈ u.val ∧ b ∈ u.val := by
      obtain ⟨A,hA⟩ := (mem a).mp ha
      obtain ⟨B,hB⟩ := (mem b).mp hb
      obtain ⟨C,hAC,hBC⟩ := dir A B
      exact ⟨C,hAC hA,hBC hB⟩
    refine ⟨U, ⟨?_,?_,?_⟩, fun z hz => le_iSup (fun u : c => u.val) ⟨z,hz⟩⟩
    · intro x hx hn
      obtain ⟨u,ha,hb⟩ := both hx hn
      exact (hc u.property).1 x ha hb
    · intro x hx
      obtain ⟨u,hx⟩ := (mem x).mp hx
      exact (mem _).mpr ⟨u,(hc u.property).2.1 _ hx⟩
    · intro x hx y hy
      obtain ⟨u,ha,hb⟩ := both hx hy
      exact ((hc u.property).2.2 _ ha _ hb).imp (fun h => (mem _).mpr ⟨u,h⟩)
        (fun h => (mem _).mpr ⟨u,h⟩)
  obtain ⟨P,hP₀,hmax⟩ := zorn_le_nonempty₀ {P | good P} chain P₀ init
  obtain ⟨hpt,hinv,hdiff⟩ := hmax.prop
  obtain ⟨L,hL⟩ := cone_field P hinv hdiff
  let C : RingCone L := ⟨P.comap L.subtype, fun {a} ha hn => Subtype.ext (hpt a ha hn)⟩
  letI : HasMemOrNegMem C := ⟨fun x => (hL _).mp x.property⟩
  letI : LinearOrder L := .mkOfAddGroupCone C
  letI : IsOrderedRing L := IsOrderedRing.mkOfCone C
  have nonneg (x : L) : 0 ≤ x ↔ x.val ∈ P := by
    change (x-0 : L).val ∈ P ↔ _
    simp
  have base {x : K} (hx : 0≤x) : j x ∈ P := hP₀ ⟨x,hx,rfl⟩
  let ι : K →+* L := j.codRestrict L fun x => by
    apply (hL _).mpr
    rcases le_total 0 x with h|h
    · exact Or.inl (base h)
    · exact Or.inr (by simpa using base (neg_nonneg.mpr h))
  refine ⟨L,inferInstance,inferInstance,inferInstance,ι,fun a ha => (nonneg _).mpr (base ha), ?_⟩
  intro E _ _ _ _ _ hE
  let e : E →ₐ[L] Ω := IsAlgClosed.lift
  let Q := (RingCone.nonneg E).toSubsemiring.map (e : E →+* Ω)
  have hPQ : P ≤ Q := by
    intro x hx
    let a : L := ⟨x,(hL _).mpr (Or.inl hx)⟩
    exact ⟨algebraMap L E a,hE a ((nonneg a).mpr hx),e.commutes a⟩
  have hQP : Q ≤ P := hmax.le_of_ge (image_properties (e : E →+* Ω)) hPQ
  intro y
  have hy : e y ∈ L := by
    apply (hL _).mpr
    rcases le_total 0 y with h|h
    · exact Or.inl (hQP ⟨y,h,rfl⟩)
    · exact Or.inr (hQP ⟨-y,neg_nonneg.mpr h,map_neg _ _⟩)
  exact ⟨⟨e y,hy⟩, e.injective (e.commutes _)⟩

end LocalReal17
open LocalReal17

theorem solve : OMA.R_Hilbert17_hilbert_17th_problem_R1.H2 := by
  intro K _ _ _
  obtain ⟨F,_,_,_,ι,hi,hmax⟩ := maximal_extension K
  have sq (a : F) (ha : 0 ≤ a) : IsSquare a := by
    by_contra h
    obtain ⟨E,_,_,_,_,_,hE,y,hy⟩ := square_extension order_preordering a ha h
    obtain ⟨r,hr⟩ := hmax E hE y
    exact h ⟨r,(algebraMap F E).injective (by simpa [map_mul,hr] using hy)⟩
  refine ⟨F,inferInstance,inferInstance,inferInstance,IsRealClosed.of_linearOrderedField
    (fun h => sq _ h) (fun {f} hf => ?_),ι,hi⟩
  obtain ⟨E,_,_,_,_,_,hE,y,hy⟩ := odd_extension order_preordering sq f hf
  obtain ⟨r,hr⟩ := hmax E hE y
  refine ⟨r,(algebraMap F E).injective ?_⟩
  simpa [Polynomial.IsRoot, ← hr, Polynomial.aeval_algebraMap_apply] using hy


end OMA.Leaf2
end Leaf2

section Red3

-- Reduction Hilbert17.hilbert_17th_problem.R1.H3.R1 of Hilbert17.hilbert_17th_problem.R1.H3
-- Credit: @green-notes

/-!
Reduces the Tarski-Seidenberg transfer hypothesis (`Hilbert17.hilbert_17th_problem.R1.H3`) to three
independent pillars of the Cohen-Hormander decision method:
1. `H1`: Intermediate Value Theorem for polynomials over any ordered real closed field.
2. `H2`: Polynomial Mean Value Theorem and asymptotic leading-coefficient sign dominance for any
   ordered field satisfying Polynomial IVT.
3. `H3`: One-variable Cohen-Hormander sign-system transfer over a commutative ring `A` between two
   ordered fields satisfying IVT, MVT, and asymptotic sign dominance.
-/

namespace OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1

def H1 : Prop :=
  ∀ {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (p : Polynomial R) {a b : R}, a < b → p.eval a < 0 → 0 < p.eval b →
    ∃ c : R, a < c ∧ c < b ∧ p.eval c = 0

def H2 : Prop :=
  ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K],
    (∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0) →
    (∀ (p : Polynomial K) {u v : K}, u < v →
      ∃ c : K, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c) ∧
    (∀ (p : Polynomial K), p ≠ 0 →
      ∃ M : K, ∀ x : K, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))

def H3 : Prop :=
  ∀ {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂],
    (∀ (p : Polynomial K₁) {a b : K₁}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₁, a < c ∧ c < b ∧ p.eval c = 0) →
    (∀ (p : Polynomial K₂) {a b : K₂}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₂, a < c ∧ c < b ∧ p.eval c = 0) →
    (∀ (p : Polynomial K₁) {u v : K₁}, u < v →
      ∃ c : K₁, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c) →
    (∀ (p : Polynomial K₂) {u v : K₂}, u < v →
      ∃ c : K₂, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c) →
    (∀ (p : Polynomial K₁), p ≠ 0 →
      ∃ M : K₁, ∀ x : K₁, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0)) →
    (∀ (p : Polynomial K₂), p ≠ 0 →
      ∃ M : K₂, ∀ x : K₂, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0)) →
    ∀ (φ₁ : A →+* K₁) (P : List (Polynomial A)),
      ∃ Q : List A, ∀ (φ₂ : A →+* K₂),
        (∀ r ∈ Q, (φ₁ r < 0 ↔ φ₂ r < 0) ∧ (φ₁ r = 0 ↔ φ₂ r = 0)) →
        ∀ t₁ : K₁, ∃ t₂ : K₂, ∀ p ∈ P,
          ((p.map φ₁).eval t₁ < 0 ↔ (p.map φ₂).eval t₂ < 0) ∧
          ((p.map φ₁).eval t₁ = 0 ↔ (p.map φ₂).eval t₂ = 0)

section Helpers

lemma real_ivt (p : Polynomial ℝ) {a b : ℝ} (hab : a < b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ c : ℝ, a < c ∧ c < b ∧ p.eval c = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) := ⟨ha, hb⟩
  obtain ⟨c, hcIoo, hce⟩ := intermediate_value_Ioo hab.le p.continuous.continuousOn hmem
  exact ⟨c, hcIoo.1, hcIoo.2, hce⟩

lemma real_hom_sign {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (j : ℝ →+* R) (r : ℝ) :
    (j r < 0 ↔ r < 0) ∧ (j r = 0 ↔ r = 0) := by
  have hnonneg : ∀ x : ℝ, 0 ≤ x → 0 ≤ j x := by
    intro x hx
    have hsq : x = (Real.sqrt x) ^ 2 := (Real.sq_sqrt hx).symm
    rw [hsq, map_pow]
    exact sq_nonneg (j (Real.sqrt x))
  have heq : j r = 0 ↔ r = 0 := map_eq_zero j
  refine ⟨?_, heq⟩
  constructor
  · intro hj
    by_contra hnr
    have hr : 0 ≤ r := le_of_not_gt hnr
    exact not_lt_of_ge (hnonneg r hr) hj
  · intro hr
    have hpos : 0 ≤ -r := neg_nonneg.mpr hr.le
    have hj_le : j r ≤ 0 := by
      have h0 := hnonneg (-r) hpos
      rw [map_neg] at h0
      linarith
    have hj_ne : j r ≠ 0 := fun h => hr.ne (heq.mp h)
    exact lt_of_le_of_ne hj_le hj_ne

lemma eval₂_finCons {n : ℕ} {R : Type} [CommRing R] (j : ℝ →+* R) (y : R) (s : Fin n → R)
    (f : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial.eval₂ j (Fin.cons y s) f =
      Polynomial.eval y
        (Polynomial.map (MvPolynomial.eval₂Hom j s) (MvPolynomial.finSuccEquiv ℝ n f)) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq =>
    simp [map_add, hp, hq]
  | mul_X p i hp =>
    refine Fin.cases ?_ ?_ i
    · simp [hp, MvPolynomial.finSuccEquiv_X_zero]
    · intro k
      simp [hp, MvPolynomial.finSuccEquiv_X_succ]

lemma transfer_list {n : ℕ} {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] (h1 : H1) (h2 : H2) (h3 : H3) (j : ℝ →+* R) :
    ∀ (L : List (MvPolynomial (Fin n) ℝ)) (y : Fin n → R),
      ∃ x : Fin n → ℝ, ∀ p ∈ L,
        (MvPolynomial.eval₂ j y p < 0 ↔ MvPolynomial.eval x p < 0) ∧
        (MvPolynomial.eval₂ j y p = 0 ↔ MvPolynomial.eval x p = 0) := by
  induction n with
  | zero =>
    intro L y
    refine ⟨Fin.elim0, fun p _ => ?_⟩
    have hp : p = MvPolynomial.C (p.coeff 0) := MvPolynomial.eq_C_of_isEmpty p
    conv_lhs => rw [hp]
    conv_rhs => rw [hp]
    simp only [MvPolynomial.eval₂_C, MvPolynomial.eval_C]
    exact real_hom_sign j (p.coeff 0)
  | succ n ih =>
    intro L y
    have hIVTR : ∀ (p : Polynomial R) {a b : R}, a < b → p.eval a < 0 → 0 < p.eval b →
        ∃ c : R, a < c ∧ c < b ∧ p.eval c = 0 := fun p {_ _} hab => h1 p hab
    obtain ⟨hMVTR, hAsympR⟩ := h2 hIVTR
    obtain ⟨hMVTReal, hAsympReal⟩ := h2 real_ivt
    let P : List (Polynomial (MvPolynomial (Fin n) ℝ)) := L.map (MvPolynomial.finSuccEquiv ℝ n)
    let y' : Fin n → R := Fin.tail y
    let t₁ : R := y 0
    let φ₁ : MvPolynomial (Fin n) ℝ →+* R := MvPolynomial.eval₂Hom j y'
    obtain ⟨Q, hQ⟩ := h3 hIVTR real_ivt hMVTR hMVTReal hAsympR hAsympReal φ₁ P
    obtain ⟨x', hx'⟩ := ih Q y'
    let φ₂ : MvPolynomial (Fin n) ℝ →+* ℝ := MvPolynomial.eval x'
    have hagree : ∀ r ∈ Q, (φ₁ r < 0 ↔ φ₂ r < 0) ∧ (φ₁ r = 0 ↔ φ₂ r = 0) := by
      intro r hr
      simpa [φ₁, φ₂] using hx' r hr
    obtain ⟨t₂, ht₂⟩ := hQ φ₂ hagree t₁
    refine ⟨Fin.cons t₂ x', fun p hp => ?_⟩
    have hpP : MvPolynomial.finSuccEquiv ℝ n p ∈ P := List.mem_map_of_mem hp
    have hsigns := ht₂ (MvPolynomial.finSuccEquiv ℝ n p) hpP
    have hy_eq : y = Fin.cons t₁ y' := (Fin.cons_self_tail y).symm
    have hlhs : MvPolynomial.eval₂ j y p =
        (Polynomial.map φ₁ (MvPolynomial.finSuccEquiv ℝ n p)).eval t₁ := by
      conv_lhs => rw [hy_eq]
      exact eval₂_finCons j t₁ y' p
    have hrhs : MvPolynomial.eval (Fin.cons t₂ x') p =
        (Polynomial.map φ₂ (MvPolynomial.finSuccEquiv ℝ n p)).eval t₂ :=
      MvPolynomial.eval_eq_eval_mv_eval' x' t₂ p
    rw [hlhs, hrhs]
    exact hsigns

end Helpers

theorem main : H1 → H2 → H3 → OMA.R_Hilbert17_hilbert_17th_problem_R1.H3 := by
  intro h1 h2 h3 n R _ _ _ _ j f ⟨y, hy⟩
  obtain ⟨x, hx⟩ := transfer_list h1 h2 h3 j [f] y
  exact ⟨x, (hx f (List.mem_singleton_self f)).1.mp hy⟩

end OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1

end Red3

section Leaf3
namespace OMA.Leaf3

-- Step Hilbert17.hilbert_17th_problem.R1.H3.R1.H1 (Polynomial IVT for real closed fields)
-- Credit: @green-notes

/-!
Proves the Intermediate Value Theorem for polynomials over any ordered real closed field
(`Hilbert17.hilbert_17th_problem.R1.H3.R1.H1`) by showing every irreducible polynomial over `R`
has degree at most `2` (via Galois theory and 2-Sylow subgroups on the splitting field of
`(X ^ 2 + 1) * f`), then applying strong induction on polynomial degree.
-/

namespace Hilbert17H3R1H1

open Polynomial

private lemma irreducible_X_sq_add_one {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  have hdeg : (X ^ 2 + 1 : R[X]).natDegree = 2 := by compute_degree!
  have hno : ∀ r : R, (X ^ 2 + 1 : R[X]).eval r ≠ 0 := by
    intro r
    simp only [eval_add, eval_pow, eval_X, eval_one]
    have : 0 < r ^ 2 + 1 := by positivity
    exact this.ne'
  have hne : (X ^ 2 + 1 : R[X]) ≠ 0 := fun h => hno 0 (by simp [h])
  have hnu : ¬ IsUnit (X ^ 2 + 1 : R[X]) := by
    intro hu
    have hd := natDegree_eq_zero_of_isUnit hu
    omega
  refine ⟨hnu, fun a b hab => ?_⟩
  have ha0 : a ≠ 0 := fun h => hne (by simp [hab, h])
  have hb0 : b ≠ 0 := fun h => hne (by simp [hab, h])
  have hsum : a.natDegree + b.natDegree = 2 := by
    rw [← natDegree_mul ha0 hb0, ← hab, hdeg]
  by_cases ha : a.natDegree = 0
  · left
    obtain ⟨c, hceq⟩ := Polynomial.natDegree_eq_zero.mp ha
    rw [← hceq] at ha0 ⊢
    exact Polynomial.isUnit_C.mpr (Ne.isUnit (by simpa using ha0))
  · by_cases hb : b.natDegree = 0
    · right
      obtain ⟨c, hceq⟩ := Polynomial.natDegree_eq_zero.mp hb
      rw [← hceq] at hb0 ⊢
      exact Polynomial.isUnit_C.mpr (Ne.isUnit (by simpa using hb0))
    · have ha1 : a.natDegree = 1 := by omega
      have hlc : a.coeff 1 ≠ 0 := by
        simpa [leadingCoeff, ha1] using leadingCoeff_ne_zero.mpr ha0
      have ha_eq : a = C (a.coeff 1) * X + C (a.coeff 0) := by
        ext n
        rcases n with _ | _ | n
        · simp
        · simp
        · simp only [coeff_add, coeff_C_mul, coeff_X, coeff_C_succ, mul_ite, mul_one, mul_zero, add_zero]
          simp [coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < n + 2)]
      let r : R := -(a.coeff 0) / a.coeff 1
      have har : a.eval r = 0 := by
        rw [ha_eq]
        simp only [eval_add, eval_mul, eval_C, eval_X, r]
        rw [mul_div_cancel₀ _ hlc]
        ring
      exfalso
      apply hno r
      rw [hab, eval_mul, har, zero_mul]

private lemma isSquare_of_adjoin_i {R L : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] [Field L] [Algebra R L] {i_L : L} (hi : i_L ^ 2 + 1 = 0)
    (z : IntermediateField.adjoin R {i_L}) : IsSquare z := by
  have hred : ∀ p : R[X], ∃ a b : R, aeval i_L p = algebraMap R L a + algebraMap R L b * i_L := by
    intro p
    let q := p % (X ^ 2 + 1)
    have hqdeg : q.natDegree < 2 := by
      have hdeg2 : (X ^ 2 + 1 : R[X]).natDegree = 2 := by compute_degree!
      rw [← hdeg2]
      exact natDegree_mod_lt p (by simp [hdeg2])
    have hpq : aeval i_L p = aeval i_L q := by
      have hdiv := EuclideanDomain.div_add_mod p (X ^ 2 + 1)
      conv_lhs => rw [← hdiv]
      simp [q, hi]
    have hq_eq : q = C (q.coeff 0) + C (q.coeff 1) * X := by
      ext n
      rcases n with _ | _ | n
      · simp
      · simp
      · simp only [coeff_add, coeff_C_succ, coeff_C_mul_X, zero_add]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
    refine ⟨q.coeff 0, q.coeff 1, ?_⟩
    rw [hpq, hq_eq]
    simp
  obtain ⟨p, s, hzs⟩ := (IntermediateField.mem_adjoin_simple_iff (F := R) (α := i_L) (z : L)).mp z.2
  obtain ⟨a₁, b₁, hp1⟩ := hred p
  obtain ⟨a₂, b₂, hs1⟩ := hred s
  have hz_pair : ∃ a b : R, (z : L) = algebraMap R L a + algebraMap R L b * i_L := by
    by_cases h0 : a₂ = 0 ∧ b₂ = 0
    · refine ⟨0, 0, ?_⟩
      rw [hzs, hs1, h0.1, h0.2]
      simp
    · have hden_pos : 0 < a₂ ^ 2 + b₂ ^ 2 := by
        rcases not_and_or.mp h0 with ha2 | hb2
        · have : 0 < a₂ ^ 2 := sq_pos_of_ne_zero ha2
          nlinarith [sq_nonneg b₂]
        · have : 0 < b₂ ^ 2 := sq_pos_of_ne_zero hb2
          nlinarith [sq_nonneg a₂]
      have hs_ne : aeval i_L s ≠ 0 := by
        intro hsz
        rw [hs1] at hsz
        have hmul : (algebraMap R L a₂ + algebraMap R L b₂ * i_L) *
            (algebraMap R L a₂ - algebraMap R L b₂ * i_L) = algebraMap R L (a₂ ^ 2 + b₂ ^ 2) := by
          simp only [map_add, map_pow]
          linear_combination -(algebraMap R L b₂ ^ 2) * hi
        rw [hsz, zero_mul] at hmul
        have hzero : algebraMap R L (a₂ ^ 2 + b₂ ^ 2) = 0 := hmul.symm
        have : a₂ ^ 2 + b₂ ^ 2 = 0 := (map_eq_zero (algebraMap R L)).mp hzero
        linarith
      let den := a₂ ^ 2 + b₂ ^ 2
      refine ⟨(a₁ * a₂ + b₁ * b₂) / den, (b₁ * a₂ - a₁ * b₂) / den, ?_⟩
      rw [hzs, div_eq_iff hs_ne]
      rw [hp1, hs1]
      have hden_ne : (den : R) ≠ 0 := hden_pos.ne'
      have hmul_eq : algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den * a₂ - (b₁ * a₂ - a₁ * b₂) / den * b₂) =
          algebraMap R L a₁ := by
        congr 1
        field_simp [hden_ne]
        ring
      have hmul_eq2 : algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den * b₂ + (b₁ * a₂ - a₁ * b₂) / den * a₂) =
          algebraMap R L b₁ := by
        congr 1
        field_simp [hden_ne]
        ring
      calc
        algebraMap R L a₁ + algebraMap R L b₁ * i_L
          = algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den * a₂ - (b₁ * a₂ - a₁ * b₂) / den * b₂) +
            algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den * b₂ + (b₁ * a₂ - a₁ * b₂) / den * a₂) * i_L := by
              rw [hmul_eq, hmul_eq2]
        _ = (algebraMap R L ((a₁ * a₂ + b₁ * b₂) / den) +
              algebraMap R L ((b₁ * a₂ - a₁ * b₂) / den) * i_L) *
            (algebraMap R L a₂ + algebraMap R L b₂ * i_L) := by
              simp only [map_sub, map_add, map_mul]
              linear_combination -(algebraMap R L ((b₁ * a₂ - a₁ * b₂) / den) * algebraMap R L b₂) * hi
  obtain ⟨a, b, hz_eq⟩ := hz_pair
  have hdd : ∃ d : R, 0 ≤ d ∧ d ^ 2 = a ^ 2 + b ^ 2 := by
    obtain ⟨d, hd⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R)).mp (by positivity : 0 ≤ a ^ 2 + b ^ 2)
    rcases le_total 0 d with h0d | hd0
    · exact ⟨d, h0d, by linear_combination -hd⟩
    · exact ⟨-d, neg_nonneg.mpr hd0, by linear_combination -hd⟩
  obtain ⟨d, hd0, hdsq⟩ := hdd
  have hda : a ^ 2 ≤ d ^ 2 := by nlinarith [sq_nonneg b]
  have habs : |a| ≤ d := by
    rw [← abs_of_nonneg hd0]
    exact sq_le_sq.mp hda
  have hda1 : 0 ≤ (d + a) / 2 := by
    have := neg_le_of_abs_le habs
    linarith
  have hda2 : 0 ≤ (d - a) / 2 := by
    have := le_of_abs_le habs
    linarith
  have hu_ex : ∃ u : R, 0 ≤ u ∧ u ^ 2 = (d + a) / 2 := by
    obtain ⟨u, hu⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R)).mp hda1
    rcases le_total 0 u with h0u | hu0
    · exact ⟨u, h0u, by linear_combination -hu⟩
    · exact ⟨-u, neg_nonneg.mpr hu0, by linear_combination -hu⟩
  have hv_ex : ∃ v : R, 0 ≤ v ∧ v ^ 2 = (d - a) / 2 := by
    obtain ⟨v, hv⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R)).mp hda2
    rcases le_total 0 v with h0v | hv0
    · exact ⟨v, h0v, by linear_combination -hv⟩
    · exact ⟨-v, neg_nonneg.mpr hv0, by linear_combination -hv⟩
  obtain ⟨u, hu0, husq⟩ := hu_ex
  obtain ⟨v, hv0, hvsq⟩ := hv_ex
  have huv_sq : (2 * u * v) ^ 2 = b ^ 2 := by
    have : 4 * (u ^ 2 * v ^ 2) = d ^ 2 - a ^ 2 := by rw [husq, hvsq]; ring
    nlinarith [hdsq]
  have huv_eq : 2 * u * v = |b| := by
    have h0 : 0 ≤ 2 * u * v := by positivity
    rw [← sq_abs b] at huv_sq
    exact (sq_eq_sq₀ h0 (abs_nonneg b)).mp huv_sq
  let v' : R := if 0 ≤ b then v else -v
  have hv'sq : v' ^ 2 = (d - a) / 2 := by
    by_cases hb : 0 ≤ b <;> simp [v', hb, hvsq]
  have huv' : 2 * u * v' = b := by
    by_cases hb : 0 ≤ b
    · simp only [v', hb, ↓reduceIte]
      rw [huv_eq, abs_of_nonneg hb]
    · simp only [v', hb, ↓reduceIte, mul_neg]
      rw [huv_eq, abs_of_neg (lt_of_not_ge hb), neg_neg]
  let wL : L := algebraMap R L u + algebraMap R L v' * i_L
  have hwL_mem : wL ∈ IntermediateField.adjoin R {i_L} := by
    apply add_mem
    · exact IntermediateField.algebraMap_mem _ u
    · exact mul_mem (IntermediateField.algebraMap_mem _ v') (IntermediateField.mem_adjoin_simple_self R i_L)
  refine ⟨⟨wL, hwL_mem⟩, Subtype.ext ?_⟩
  simp only [MulMemClass.coe_mul, wL]
  calc
    (z : L) = algebraMap R L a + algebraMap R L b * i_L := hz_eq
    _ = algebraMap R L (u ^ 2 - v' ^ 2) + algebraMap R L (2 * u * v') * i_L := by
        rw [husq, hv'sq, huv']
        have : (d + a) / 2 - (d - a) / 2 = a := by ring
        rw [this]
    _ = (algebraMap R L u + algebraMap R L v' * i_L) * (algebraMap R L u + algebraMap R L v' * i_L) := by
        simp only [map_sub, map_pow, map_mul, map_ofNat]
        linear_combination -(algebraMap R L v' ^ 2) * hi

private lemma natDegree_le_two_of_irreducible {R : Type} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] {f : R[X]} (hf : Irreducible f) :
    f.natDegree ≤ 2 := by
  let g : R[X] := (X ^ 2 + 1) * f
  have hf0 : f ≠ 0 := hf.ne_zero
  have hg0 : g ≠ 0 := mul_ne_zero (irreducible_X_sq_add_one (R := R)).ne_zero hf0
  let L := g.SplittingField
  have : FiniteDimensional R L := inferInstance
  have : Normal R L := inferInstance
  have : Algebra.IsSeparable R L := inferInstance
  have : IsGalois R L := ⟨⟩
  let G := L ≃ₐ[R] L
  have : Finite G := inferInstance
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPGroup : IsPGroup 2 G := by
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 G))
    let E := IntermediateField.fixedField (S : Subgroup G)
    have hE_fin : Module.finrank R E = (S : Subgroup G).index := by
      have h1 : Module.finrank R E * Module.finrank E L = Module.finrank R L :=
        Module.finrank_mul_finrank R E L
      have h2 : Module.finrank E L = Nat.card (S : Subgroup G) :=
        IntermediateField.finrank_fixedField_eq_card (S : Subgroup G)
      have h3 : Module.finrank R L = Nat.card G :=
        (IsGalois.card_aut_eq_finrank R L).symm
      have h4 : (S : Subgroup G).index * Nat.card (S : Subgroup G) = Nat.card G :=
        Subgroup.index_mul_card (S : Subgroup G)
      have hpos : 0 < Nat.card (S : Subgroup G) := Nat.card_pos
      nlinarith
    have hodd : Odd (Module.finrank R E) := by
      rw [hE_fin, Nat.odd_iff]
      have hndvd : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
      omega
    obtain ⟨α, hα⟩ := Field.exists_primitive_element R E
    have hmin_deg : (minpoly R α).natDegree = Module.finrank R E := by
      rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite R α), hα, IntermediateField.finrank_top']
    have hodd_min : Odd (minpoly R α).natDegree := hmin_deg ▸ hodd
    obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree hodd_min
    have hirr : Irreducible (minpoly R α) := minpoly.irreducible (IsIntegral.of_finite R α)
    have hdeg1 : (minpoly R α).natDegree = 1 := by
      obtain ⟨s, hs⟩ := Polynomial.dvd_iff_isRoot.mpr hr
      rcases hirr.isUnit_or_isUnit hs with hunit | hunit
      · exfalso
        have := natDegree_eq_zero_of_isUnit hunit
        rw [natDegree_X_sub_C] at this
        omega
      · rw [hs, natDegree_mul (X_sub_C_ne_zero r) hunit.ne_zero, natDegree_X_sub_C,
          natDegree_eq_zero_of_isUnit hunit]
    have hidx1 : (S : Subgroup G).index = 1 := by omega
    have hStop : (S : Subgroup G) = ⊤ := Subgroup.index_eq_one.mp hidx1
    have hG_eq : IsPGroup 2 (⊤ : Subgroup G) := hStop ▸ S.isPGroup'
    exact hG_eq.of_equiv Subgroup.topEquiv
  have hsplits_g : Splits (g.map (algebraMap R L)) := Polynomial.SplittingField.splits g
  have hsplits_i : Splits ((X ^ 2 + 1 : R[X]).map (algebraMap R L)) :=
    hsplits_g.of_dvd (Polynomial.map_ne_zero hg0) (Polynomial.map_dvd _ (dvd_mul_right _ _))
  obtain ⟨i_L, hi_L⟩ := hsplits_i.exists_eval_eq_zero (by
    rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree (irreducible_X_sq_add_one (R := R)).ne_zero]
    have : (X ^ 2 + 1 : R[X]).natDegree = 2 := by compute_degree!
    simp [this])
  have hi_sq : i_L ^ 2 + 1 = 0 := by
    simpa [Polynomial.eval_map] using hi_L
  let K₀ : IntermediateField R L := IntermediateField.adjoin R {i_L}
  have : FiniteDimensional K₀ L := FiniteDimensional.right R K₀ L
  have hfinK0L_one : Module.finrank K₀ L = 1 := by
    obtain ⟨k, hk⟩ := hPGroup.exists_card_eq
    have hdvd_pow : Module.finrank K₀ L ∣ 2 ^ k := by
      rw [← hk, IsGalois.card_aut_eq_finrank R L, ← Module.finrank_mul_finrank R K₀ L]
      exact dvd_mul_left _ _
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd_pow
    by_cases hm0 : m = 0
    · rw [hm, hm0, pow_zero]
    · exfalso
      have hm1 : 1 ≤ m := Nat.pos_of_ne_zero hm0
      let G₀ := L ≃ₐ[K₀] L
      have : Finite G₀ := inferInstance
      have hG₀_card : Nat.card G₀ = 2 ^ m := by
        rw [IsGalois.card_aut_eq_finrank K₀ L, hm]
      have hdvd_sub : 2 ^ (m - 1) ∣ Nat.card G₀ := by
        rw [hG₀_card]
        exact Nat.pow_dvd_pow 2 (Nat.sub_le m 1)
      obtain ⟨M, hMcard⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd_sub
      let K₁ : IntermediateField K₀ L := IntermediateField.fixedField M
      have hfinK1 : Module.finrank K₁ L = 2 ^ (m - 1) := by
        rw [IntermediateField.finrank_fixedField_eq_card]
        exact hMcard
      have hfin01 : Module.finrank K₀ K₁ = 2 := by
        have hmul : Module.finrank K₀ K₁ * Module.finrank K₁ L = Module.finrank K₀ L :=
          Module.finrank_mul_finrank K₀ K₁ L
        rw [hfinK1, hm] at hmul
        have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hm1, pow_succ']
        have hpos : 0 < 2 ^ (m - 1) := by positivity
        nlinarith
      have hfin_dim : FiniteDimensional K₀ K₁ :=
        Module.finite_of_finrank_pos (by omega : 0 < Module.finrank K₀ K₁)
      have hne_bot : (⊥ : IntermediateField K₀ K₁) ≠ ⊤ := by
        intro hbot
        have := congrArg (fun E : IntermediateField K₀ K₁ => Module.finrank K₀ E) hbot
        simp only [IntermediateField.finrank_bot, IntermediateField.finrank_top', hfin01] at this
        omega
      have hmem_ex : ∃ β : K₁, β ∉ (⊥ : IntermediateField K₀ K₁) := by
        by_contra hall
        push Not at hall
        apply hne_bot
        ext x
        simp [hall x]
      obtain ⟨β, hβ⟩ := hmem_ex
      have hβ_int : IsIntegral K₀ β := IsIntegral.of_finite K₀ β
      have hdvd2 : (minpoly K₀ β).natDegree ∣ 2 := by
        rw [← hfin01]
        exact minpoly.degree_dvd hβ_int
      have hdeg_ne1 : (minpoly K₀ β).natDegree ≠ 1 := by
        intro h1
        apply hβ
        have htop1 : Module.finrank K₀ (IntermediateField.adjoin K₀ {β}) = 1 := by
          rw [IntermediateField.adjoin.finrank hβ_int, h1]
        have hbot1 : IntermediateField.adjoin K₀ {β} = ⊥ :=
          IntermediateField.finrank_eq_one_iff.mp htop1
        rw [← hbot1]
        exact IntermediateField.mem_adjoin_simple_self K₀ β
      have hdeg2 : (minpoly K₀ β).natDegree = 2 := by
        have hpos : 0 < (minpoly K₀ β).natDegree := minpoly.natDegree_pos hβ_int
        have hle2 : (minpoly K₀ β).natDegree ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
        omega
      let q := minpoly K₀ β
      have hq_monic : q.Monic := minpoly.monic hβ_int
      have hq_deg2 : q.natDegree = 2 := hdeg2
      have hq2 : q.coeff 2 = 1 := by simpa [q, hdeg2] using hq_monic.coeff_natDegree
      have hq_eq : q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
        ext n
        rcases n with _ | _ | _ | n
        · simp
        · simp
        · simp [hq2]
        · simp only [coeff_add, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C_succ,
            mul_ite, mul_one, mul_zero, add_zero]
          have h2 : n + 3 ≠ 2 := by omega
          simp [h2, coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < n + 3)]
      let disc : K₀ := (q.coeff 1) ^ 2 - 4 * q.coeff 0
      obtain ⟨d, hd⟩ := isSquare_of_adjoin_i hi_sq disc
      have hd_sq : d ^ 2 = disc := by linear_combination -hd
      let r : K₀ := (-(q.coeff 1) + d) / 2
      have hr_root : q.IsRoot r := by
        rw [Polynomial.IsRoot]
        have h2 : (2 : K₀) ≠ 0 := two_ne_zero
        have h4 : 4 * q.eval r = (2 * r + q.coeff 1) ^ 2 - ((q.coeff 1) ^ 2 - 4 * q.coeff 0) := by
          conv_lhs => rw [hq_eq]
          simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C]
          ring
        have hr2 : 2 * r + q.coeff 1 = d := by
          dsimp [r]
          rw [mul_div_cancel₀ _ h2]
          ring
        have h40 : 4 * q.eval r = 0 := by rw [h4, hr2]; dsimp [disc] at hd_sq; rw [hd_sq, sub_self]
        exact (mul_eq_zero.mp h40).resolve_left (by norm_num)
      have hirr_q : Irreducible q := minpoly.irreducible hβ_int
      have hq_deg1 : q.natDegree = 1 := by
        obtain ⟨s, hs⟩ := Polynomial.dvd_iff_isRoot.mpr hr_root
        rcases hirr_q.isUnit_or_isUnit hs with hunit | hunit
        · exfalso
          have := natDegree_eq_zero_of_isUnit hunit
          rw [natDegree_X_sub_C] at this
          omega
        · rw [hs, natDegree_mul (X_sub_C_ne_zero r) hunit.ne_zero, natDegree_X_sub_C,
            natDegree_eq_zero_of_isUnit hunit]
      omega
  have hfinK0 : Module.finrank R K₀ ≤ 2 := by
    have hi_int : IsIntegral R i_L := ⟨X ^ 2 + 1, by monicity!, by simp [hi_sq]⟩
    rw [IntermediateField.adjoin.finrank hi_int]
    have hdvd_i : minpoly R i_L ∣ (X ^ 2 + 1 : R[X]) := minpoly.dvd R i_L (by simp [hi_sq])
    have hle_i := Polynomial.natDegree_le_of_dvd hdvd_i (irreducible_X_sq_add_one (R := R)).ne_zero
    exact hle_i.trans (by compute_degree!)
  have hfinL : Module.finrank R L ≤ 2 := by
    rw [← Module.finrank_mul_finrank R K₀ L, hfinK0L_one, mul_one]
    exact hfinK0
  have hsplits_f : Splits (f.map (algebraMap R L)) :=
    hsplits_g.of_dvd (Polynomial.map_ne_zero hg0) (Polynomial.map_dvd _ (dvd_mul_left _ _))
  have hdvd_fin : f.natDegree ∣ Module.finrank R L := hf.natDegree_dvd_finrank hsplits_f
  have hpos_fin : 0 < Module.finrank R L := Module.finrank_pos
  exact (Nat.le_of_dvd hpos_fin hdvd_fin).trans hfinL

end Hilbert17H3R1H1

open Polynomial in
theorem solve : OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1.H1 := by
  intro R _ _ _ _ p a b hab ha hb
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h d ih =>
    by_cases hdeg0 : p.natDegree = 0
    · obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdeg0
      simp only [eval_C] at ha hb
      linarith
    · by_cases hirr : Irreducible p
      · have hd2 : p.natDegree ≤ 2 := Hilbert17H3R1H1.natDegree_le_two_of_irreducible hirr
        have hcases : p.natDegree = 1 ∨ p.natDegree = 2 := by omega
        rcases hcases with h1 | h2
        · let u := p.coeff 1
          let v := p.coeff 0
          have hu : u ≠ 0 := by
            intro h
            have hlc : p.leadingCoeff = 0 := by simpa [u, leadingCoeff, h1] using h
            exact leadingCoeff_ne_zero.mpr hirr.ne_zero hlc
          have hp_eq : p = C u * X + C v := by
            ext n
            rcases n with _ | _ | n
            · simp [v]
            · simp [u]
            · simp only [coeff_add, coeff_C_mul_X, coeff_C_succ, add_zero]
              split_ifs with h
              · omega
              · exact coeff_eq_zero_of_natDegree_lt (by omega)
          have hpa : u * a + v < 0 := by simpa [hp_eq] using ha
          have hpb : 0 < u * b + v := by simpa [hp_eq] using hb
          have hu_pos : 0 < u := by nlinarith
          refine ⟨-v / u, ?_, ?_, ?_⟩
          · rw [lt_div_iff₀ hu_pos]; linarith
          · rw [div_lt_iff₀ hu_pos]; linarith
          · simp [hp_eq, mul_div_cancel₀ _ hu]
        · let u := p.coeff 2
          let v := p.coeff 1
          let w := p.coeff 0
          have hu : u ≠ 0 := by
            intro h
            have hlc : p.leadingCoeff = 0 := by simpa [u, leadingCoeff, h2] using h
            exact leadingCoeff_ne_zero.mpr hirr.ne_zero hlc
          have hp_eq : p = C u * X ^ 2 + C v * X + C w := by
            ext n
            rcases n with _ | _ | _ | n
            · simp [w]
            · simp [v]
            · simp [u]
            · simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, mul_ite, mul_one, mul_zero,
                coeff_C_succ]
              have h2 : n + 3 ≠ 2 := by omega
              simp [h2, coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n + 3)]
          have hdisc_neg : v ^ 2 - 4 * u * w < 0 := by
            by_contra hdisc
            have hdisc_nn : 0 ≤ v ^ 2 - 4 * u * w := le_of_not_gt hdisc
            obtain ⟨disc_sqrt, hd⟩ := (IsRealClosed.nonneg_iff_isSquare (R := R)).mp hdisc_nn
            have hdsq : disc_sqrt ^ 2 = v ^ 2 - 4 * u * w := by linear_combination -hd
            let r : R := (-v + disc_sqrt) / (2 * u)
            have hr_root : p.IsRoot r := by
              rw [Polynomial.IsRoot]
              have h2u : 2 * u ≠ 0 := mul_ne_zero two_ne_zero hu
              have h4 : 4 * u * p.eval r = (2 * u * r + v) ^ 2 - (v ^ 2 - 4 * u * w) := by
                rw [hp_eq]
                simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
                ring
              have hr2 : 2 * u * r + v = disc_sqrt := by
                dsimp [r]
                rw [mul_div_cancel₀ _ h2u]
                ring
              have h40 : 4 * u * p.eval r = 0 := by rw [h4, hr2, hdsq, sub_self]
              exact (mul_eq_zero.mp h40).resolve_left (mul_ne_zero (by norm_num) hu)
            have : p.natDegree = 1 := by
              obtain ⟨s, hs⟩ := Polynomial.dvd_iff_isRoot.mpr hr_root
              rcases hirr.isUnit_or_isUnit hs with hunit | hunit
              · exfalso
                have := natDegree_eq_zero_of_isUnit hunit
                rw [natDegree_X_sub_C] at this
                omega
              · rw [hs, natDegree_mul (X_sub_C_ne_zero r) hunit.ne_zero, natDegree_X_sub_C,
                  natDegree_eq_zero_of_isUnit hunit]
            omega
          have h4ua : 0 < 4 * u * p.eval a := by
            rw [hp_eq]
            simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
            nlinarith [sq_nonneg (2 * u * a + v)]
          have h4ub : 0 < 4 * u * p.eval b := by
            rw [hp_eq]
            simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C]
            nlinarith [sq_nonneg (2 * u * b + v)]
          nlinarith
      · have hp0 : p ≠ 0 := by intro h; simp [h] at ha
        have hpnu : ¬ IsUnit p := fun hu => hdeg0 (natDegree_eq_zero_of_isUnit hu)
        rw [irreducible_iff] at hirr
        push Not at hirr
        obtain ⟨q, r, hpqr, hqnu, hrnu⟩ := hirr hpnu
        have hq0 : q ≠ 0 := fun h => hp0 (by simp [hpqr, h])
        have hr0 : r ≠ 0 := fun h => hp0 (by simp [hpqr, h])
        have hqdeg : 0 < q.natDegree := by
          by_contra h0
          obtain ⟨c, hceq⟩ := Polynomial.natDegree_eq_zero.mp (by omega : q.natDegree = 0)
          rw [← hceq] at hqnu hq0
          exact hqnu (Polynomial.isUnit_C.mpr (Ne.isUnit (by simpa using hq0)))
        have hrdeg : 0 < r.natDegree := by
          by_contra h0
          obtain ⟨c, hceq⟩ := Polynomial.natDegree_eq_zero.mp (by omega : r.natDegree = 0)
          rw [← hceq] at hrnu hr0
          exact hrnu (Polynomial.isUnit_C.mpr (Ne.isUnit (by simpa using hr0)))
        have hsum : q.natDegree + r.natDegree = d := by
          rw [← natDegree_mul hq0 hr0, ← hpqr, hn]
        have hqa : q.eval a ≠ 0 := fun h => by
          have : p.eval a = 0 := by rw [hpqr, eval_mul, h, zero_mul]
          linarith
        have hqb : q.eval b ≠ 0 := fun h => by
          have : p.eval b = 0 := by rw [hpqr, eval_mul, h, zero_mul]
          linarith
        have hra : r.eval a ≠ 0 := fun h => by
          have : p.eval a = 0 := by rw [hpqr, eval_mul, h, mul_zero]
          linarith
        have hrb : r.eval b ≠ 0 := fun h => by
          have : p.eval b = 0 := by rw [hpqr, eval_mul, h, mul_zero]
          linarith
        have hpa_mul : q.eval a * r.eval a < 0 := by simpa [hpqr] using ha
        have hpb_mul : 0 < q.eval b * r.eval b := by simpa [hpqr] using hb
        rcases lt_or_gt_of_ne hqa with hqa_lt | hqa_gt
        · rcases lt_or_gt_of_ne hqb with hqb_lt | hqb_gt
          · have hra_gt : 0 < r.eval a := by nlinarith
            have hrb_lt : r.eval b < 0 := by nlinarith
            obtain ⟨c, hac, hcb, hrc⟩ := ih r.natDegree (by omega) (-r) (by simp [hra_gt]) (by simp [hrb_lt]) (natDegree_neg r)
            exact ⟨c, hac, hcb, by rw [hpqr, eval_mul, show r.eval c = 0 by simpa using hrc, mul_zero]⟩
          · obtain ⟨c, hac, hcb, hqc⟩ := ih q.natDegree (by omega) q hqa_lt hqb_gt rfl
            exact ⟨c, hac, hcb, by rw [hpqr, eval_mul, hqc, zero_mul]⟩
        · rcases lt_or_gt_of_ne hqb with hqb_lt | hqb_gt
          · obtain ⟨c, hac, hcb, hqc⟩ := ih q.natDegree (by omega) (-q) (by simp [hqa_gt]) (by simp [hqb_lt]) (natDegree_neg q)
            exact ⟨c, hac, hcb, by rw [hpqr, eval_mul, show q.eval c = 0 by simpa using hqc, zero_mul]⟩
          · have hra_lt : r.eval a < 0 := by nlinarith
            have hrb_gt : 0 < r.eval b := by nlinarith
            obtain ⟨c, hac, hcb, hrc⟩ := ih r.natDegree (by omega) r hra_lt hrb_gt rfl
            exact ⟨c, hac, hcb, by rw [hpqr, eval_mul, hrc, mul_zero]⟩

end OMA.Leaf3
end Leaf3

section Leaf4
namespace OMA.Leaf4

namespace Hilbert17H2Proof

lemma mul_pos_of_abs_sub_lt {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x y : K} (h : |x - y| < |y|) : 0 < x * y := by
  have hsq : (x - y) ^ 2 < y ^ 2 := by
    simpa [sq_abs] using sq_lt_sq.mpr h
  nlinarith [sq_nonneg x]

lemma sign_equiv_of_mul_pos {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x y : K} (h : 0 < x * y) : (0 < x ↔ 0 < y) ∧ (x < 0 ↔ y < 0) := by
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at h
    exact lt_irrefl 0 h
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have hx : x < 0 := neg_of_mul_pos_left h hy.le
    exact ⟨⟨fun h1 => absurd h1 (not_lt.mpr hx.le), fun h2 => absurd h2 (not_lt.mpr hy.le)⟩,
      ⟨fun _ => hy, fun _ => hx⟩⟩
  · exact absurd rfl hy0
  · have hx : 0 < x := pos_of_mul_pos_left h hy.le
    exact ⟨⟨fun _ => hy, fun _ => hx⟩,
      ⟨fun h1 => absurd h1 (not_lt.mpr hx.le), fun h2 => absurd h2 (not_lt.mpr hy.le)⟩⟩

lemma asymptotic_leading_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ M : K, ∀ x : K, M < x →
      (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0) := by
  by_cases hn : p.natDegree = 0
  · refine ⟨0, fun x _ => ?_⟩
    have hpeq : p = Polynomial.C p.leadingCoeff := by
      simpa [Polynomial.leadingCoeff, hn] using Polynomial.eq_C_of_natDegree_eq_zero hn
    have hev : p.eval x = p.leadingCoeff := by
      conv_lhs => rw [hpeq]
      simp
    rw [hev]
    exact ⟨Iff.rfl, Iff.rfl⟩
  · have hn_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hn
    set n := p.natDegree
    set a := p.leadingCoeff
    have ha : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    set S : K := ∑ i ∈ Finset.range n, |p.coeff i|
    have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    refine ⟨1 + S / |a|, fun x hx => ?_⟩
    have ha_pos : 0 < |a| := abs_pos.mpr ha
    have h1x : 1 < x := by
      have : 0 ≤ S / |a| := div_nonneg hS ha_pos.le
      linarith
    have hx_pos : 0 < x := lt_trans zero_lt_one h1x
    have hSx : S < |a| * x := by
      have hdiv : S / |a| < x := by linarith
      simpa [mul_comm] using (div_lt_iff₀ ha_pos).mp hdiv
    have heval : p.eval x = (∑ i ∈ Finset.range n, p.coeff i * x ^ i) + a * x ^ n := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
      rfl
    have hpow_le : ∀ i ∈ Finset.range n, x ^ i ≤ x ^ (n - 1) := by
      intro i hi
      rw [Finset.mem_range] at hi
      exact pow_le_pow_right₀ h1x.le (Nat.le_sub_one_of_lt hi)
    have hrem : |p.eval x - a * x ^ n| < |a * x ^ n| := by
      have hsub : p.eval x - a * x ^ n = ∑ i ∈ Finset.range n, p.coeff i * x ^ i := by
        rw [heval]
        ring
      rw [hsub]
      calc
        |∑ i ∈ Finset.range n, p.coeff i * x ^ i|
            ≤ ∑ i ∈ Finset.range n, |p.coeff i * x ^ i| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ Finset.range n, |p.coeff i| * x ^ i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [abs_mul, abs_pow, abs_of_pos hx_pos]
        _ ≤ ∑ i ∈ Finset.range n, |p.coeff i| * x ^ (n - 1) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          exact mul_le_mul_of_nonneg_left (hpow_le i hi) (abs_nonneg _)
        _ = S * x ^ (n - 1) := by rw [← Finset.sum_mul]
        _ < (|a| * x) * x ^ (n - 1) := by
          exact mul_lt_mul_of_pos_right hSx (pow_pos hx_pos _)
        _ = |a| * (x ^ 1 * x ^ (n - 1)) := by rw [pow_one]; ring
        _ = |a| * x ^ n := by
          rw [← pow_add, Nat.add_sub_cancel' hn_pos]
        _ = |a * x ^ n| := by
          rw [abs_mul, abs_pow, abs_of_pos hx_pos]
    have hmul : 0 < p.eval x * (a * x ^ n) := mul_pos_of_abs_sub_lt hrem
    have hpow_pos : 0 < x ^ n := pow_pos hx_pos n
    have hmul' : 0 < p.eval x * a := by
      have : p.eval x * (a * x ^ n) = (p.eval x * a) * x ^ n := by ring
      rw [this] at hmul
      exact pos_of_mul_pos_left hmul hpow_pos.le
    exact sign_equiv_of_mul_pos hmul'

lemma eval_near_zero_mul_pos {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : Polynomial K) (m : ℕ) (hzero : ∀ i < m, p.coeff i = 0) (hcm : p.coeff m ≠ 0) :
    ∃ δ : K, 0 < δ ∧ ∀ t : K, t ≠ 0 → |t| < δ → 0 < p.eval t * (p.coeff m * t ^ m) := by
  set N := p.natDegree
  have hmN : m ≤ N := Polynomial.le_natDegree_of_ne_zero hcm
  set S : K := ∑ i ∈ Finset.Ico (m + 1) (N + 1), |p.coeff i|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hcm_pos : 0 < |p.coeff m| := abs_pos.mpr hcm
  refine ⟨min 1 (|p.coeff m| / (S + 1)), lt_min zero_lt_one (div_pos hcm_pos (by linarith)), ?_⟩
  intro t ht0 ht
  have ht1 : |t| ≤ 1 := (lt_of_lt_of_le ht (min_le_left _ _)).le
  have htS : S * |t| < |p.coeff m| := by
    have hdiv : |t| < |p.coeff m| / (S + 1) := lt_of_lt_of_le ht (min_le_right _ _)
    have h1 : (S + 1) * |t| < |p.coeff m| := (lt_div_iff₀' (by linarith)).mp hdiv
    have h2 : S * |t| ≤ (S + 1) * |t| := by nlinarith [abs_nonneg t]
    exact lt_of_le_of_lt h2 h1
  have hsplit : p.eval t - p.coeff m * t ^ m = ∑ i ∈ Finset.Ico (m + 1) (N + 1), p.coeff i * t ^ i := by
    rw [Polynomial.eval_eq_sum_range]
    have h1 : ∑ i ∈ Finset.range (N + 1), p.coeff i * t ^ i =
        (∑ i ∈ Finset.range (m + 1), p.coeff i * t ^ i) +
        ∑ i ∈ Finset.Ico (m + 1) (N + 1), p.coeff i * t ^ i := by
      rw [← Nat.Ico_zero_eq_range, ← Nat.Ico_zero_eq_range]
      exact (Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)).symm
    have h2 : ∑ i ∈ Finset.range (m + 1), p.coeff i * t ^ i = p.coeff m * t ^ m := by
      rw [Finset.sum_range_succ]
      have h0 : ∑ i ∈ Finset.range m, p.coeff i * t ^ i = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        rw [hzero i hi, zero_mul]
      rw [h0, zero_add]
    rw [h1, h2]
    ring
  have hpow_pos : 0 < |t| ^ m := pow_pos (abs_pos.mpr ht0) m
  have hbound : |p.eval t - p.coeff m * t ^ m| < |p.coeff m * t ^ m| := by
    rw [hsplit]
    calc
      |∑ i ∈ Finset.Ico (m + 1) (N + 1), p.coeff i * t ^ i|
          ≤ ∑ i ∈ Finset.Ico (m + 1) (N + 1), |p.coeff i * t ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.Ico (m + 1) (N + 1), |p.coeff i| * |t| ^ i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [abs_mul, abs_pow]
      _ ≤ ∑ i ∈ Finset.Ico (m + 1) (N + 1), |p.coeff i| * (|t| ^ m * |t|) := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [Finset.mem_Ico] at hi
        have hi_eq : i = m + 1 + (i - (m + 1)) := by omega
        have hpow_i : |t| ^ i ≤ |t| ^ m * |t| := by
          conv_lhs => rw [hi_eq, pow_add, pow_add, pow_one]
          have hrem_le : |t| ^ (i - (m + 1)) ≤ 1 := pow_le_one₀ (abs_nonneg t) ht1
          calc
            |t| ^ m * |t| * |t| ^ (i - (m + 1))
                ≤ |t| ^ m * |t| * 1 := mul_le_mul_of_nonneg_left hrem_le (mul_nonneg (pow_nonneg (abs_nonneg t) m) (abs_nonneg t))
            _ = |t| ^ m * |t| := mul_one _
        exact mul_le_mul_of_nonneg_left hpow_i (abs_nonneg _)
      _ = (S * |t|) * |t| ^ m := by rw [← Finset.sum_mul]; ring
      _ < |p.coeff m| * |t| ^ m := mul_lt_mul_of_pos_right htS hpow_pos
      _ = |p.coeff m * t ^ m| := by rw [abs_mul, abs_pow]
  exact mul_pos_of_abs_sub_lt hbound

lemma local_poly_deriv_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Polynomial K) (a : K) (hf : f ≠ 0) (hfa : f.eval a = 0) :
    ∃ δ : K, 0 < δ ∧ ∀ t : K, 0 < t → t < δ →
      0 < f.eval (a + t) * f.derivative.eval (a + t) ∧
      f.eval (a - t) * f.derivative.eval (a - t) < 0 := by
  set g : Polynomial K := f.comp (Polynomial.X + Polynomial.C a)
  have hg : g ≠ 0 := by
    intro h0
    have hcomp : g.comp (Polynomial.X - Polynomial.C a) = f := by
      dsimp [g]
      rw [Polynomial.comp_assoc]
      simp
    rw [h0, Polynomial.zero_comp] at hcomp
    exact hf hcomp.symm
  have hex : ∃ i, g.coeff i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hg (Polynomial.ext (fun i => by simpa using hnone i))
  classical
  set k := Nat.find hex
  have hck : g.coeff k ≠ 0 := Nat.find_spec hex
  have hk_min : ∀ i < k, g.coeff i = 0 := fun i hi => by
    by_contra hne
    exact Nat.find_min hex hi hne
  have hk_pos : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    have hg0 : g.eval 0 = 0 := by
      dsimp [g]
      simpa [Polynomial.eval_comp] using hfa
    have hcoeff0 : g.coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      exact hg0
    rw [hk0] at hck
    exact hck hcoeff0
  set m := k - 1
  have hkm : k = m + 1 := by omega
  have hderiv_zero : ∀ j < m, g.derivative.coeff j = 0 := by
    intro j hj
    rw [Polynomial.coeff_derivative]
    have hjk : j + 1 < k := by omega
    rw [hk_min (j + 1) hjk, zero_mul]
  have hk_cast : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hm_cast : (m : K) + 1 = (k : K) := by exact_mod_cast hkm.symm
  have hderiv_m : g.derivative.coeff m ≠ 0 := by
    rw [Polynomial.coeff_derivative, hm_cast, ← hkm]
    exact mul_ne_zero hck hk_cast
  obtain ⟨δ₁, hδ₁, h1⟩ := eval_near_zero_mul_pos g k hk_min hck
  obtain ⟨δ₂, hδ₂, h2⟩ := eval_near_zero_mul_pos g.derivative m hderiv_zero hderiv_m
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht_pos ht_lt => ?_⟩
  have ht1 : |t| < δ₁ := by
    rw [abs_of_pos ht_pos]
    exact lt_of_lt_of_le ht_lt (min_le_left _ _)
  have ht2 : |t| < δ₂ := by
    rw [abs_of_pos ht_pos]
    exact lt_of_lt_of_le ht_lt (min_le_right _ _)
  have hnt1 : |-t| < δ₁ := by simpa [abs_neg] using ht1
  have hnt2 : |-t| < δ₂ := by simpa [abs_neg] using ht2
  have hgderiv : g.derivative = f.derivative.comp (Polynomial.X + Polynomial.C a) := by
    dsimp [g]
    rw [Polynomial.derivative_comp]
    simp
  have heval_add : g.eval t = f.eval (a + t) := by
    dsimp [g]
    rw [Polynomial.eval_comp]
    simp [add_comm]
  have hdeval_add : g.derivative.eval t = f.derivative.eval (a + t) := by
    rw [hgderiv, Polynomial.eval_comp]
    simp [add_comm]
  have heval_sub : g.eval (-t) = f.eval (a - t) := by
    dsimp [g]
    rw [Polynomial.eval_comp]
    simp [sub_eq_neg_add]
  have hdeval_sub : g.derivative.eval (-t) = f.derivative.eval (a - t) := by
    rw [hgderiv, Polynomial.eval_comp]
    simp [sub_eq_neg_add]
  have hpos_add : 0 < g.eval t * (g.coeff k * t ^ k) := h1 t ht_pos.ne' ht1
  have hpos_dadd : 0 < g.derivative.eval t * (g.derivative.coeff m * t ^ m) := h2 t ht_pos.ne' ht2
  have hdm_eq : g.derivative.coeff m = g.coeff k * (k : K) := by
    rw [Polynomial.coeff_derivative, hm_cast, ← hkm]
  have hmul_pos_add : 0 < f.eval (a + t) * f.derivative.eval (a + t) := by
    rw [← heval_add, ← hdeval_add]
    have hprod : 0 < (g.eval t * (g.coeff k * t ^ k)) * (g.derivative.eval t * (g.derivative.coeff m * t ^ m)) :=
      mul_pos hpos_add hpos_dadd
    have hcoeff_pos : 0 < g.coeff k * t ^ k * (g.derivative.coeff m * t ^ m) := by
      rw [hdm_eq]
      have hk_gt : (0 : K) < k := Nat.cast_pos.mpr hk_pos
      have hsq : 0 < (g.coeff k) ^ 2 := sq_pos_of_ne_zero hck
      have ht_k : 0 < t ^ k := pow_pos ht_pos k
      have ht_m : 0 < t ^ m := pow_pos ht_pos m
      have : g.coeff k * t ^ k * (g.coeff k * (k : K) * t ^ m) = (g.coeff k) ^ 2 * (k : K) * t ^ k * t ^ m := by ring
      rw [this]
      exact mul_pos (mul_pos (mul_pos hsq hk_gt) ht_k) ht_m
    have hprod' : 0 < (g.eval t * g.derivative.eval t) * (g.coeff k * t ^ k * (g.derivative.coeff m * t ^ m)) := by
      have : (g.eval t * (g.coeff k * t ^ k)) * (g.derivative.eval t * (g.derivative.coeff m * t ^ m)) =
          (g.eval t * g.derivative.eval t) * (g.coeff k * t ^ k * (g.derivative.coeff m * t ^ m)) := by ring
      rwa [← this]
    exact pos_of_mul_pos_left hprod' hcoeff_pos.le
  have hpos_sub : 0 < g.eval (-t) * (g.coeff k * (-t) ^ k) := h1 (-t) (neg_ne_zero.mpr ht_pos.ne') hnt1
  have hpos_dsub : 0 < g.derivative.eval (-t) * (g.derivative.coeff m * (-t) ^ m) := h2 (-t) (neg_ne_zero.mpr ht_pos.ne') hnt2
  have hmul_neg_sub : f.eval (a - t) * f.derivative.eval (a - t) < 0 := by
    rw [← heval_sub, ← hdeval_sub]
    have hprod : 0 < (g.eval (-t) * (g.coeff k * (-t) ^ k)) * (g.derivative.eval (-t) * (g.derivative.coeff m * (-t) ^ m)) :=
      mul_pos hpos_sub hpos_dsub
    have hcoeff_neg : g.coeff k * (-t) ^ k * (g.derivative.coeff m * (-t) ^ m) < 0 := by
      have hpow_k : (-t) ^ k = (-t) ^ m * (-t) := by rw [hkm, pow_succ]
      rw [hdm_eq, hpow_k]
      have hk_gt : (0 : K) < k := Nat.cast_pos.mpr hk_pos
      have hsq1 : 0 < (g.coeff k) ^ 2 := sq_pos_of_ne_zero hck
      have hsq2 : 0 < ((-t) ^ m) ^ 2 := sq_pos_of_ne_zero (pow_ne_zero m (neg_ne_zero.mpr ht_pos.ne'))
      have hneg : (-t) < 0 := neg_lt_zero.mpr ht_pos
      have : g.coeff k * ((-t) ^ m * (-t)) * (g.coeff k * (k : K) * (-t) ^ m) =
          (g.coeff k) ^ 2 * (k : K) * ((-t) ^ m) ^ 2 * (-t) := by ring
      rw [this]
      exact mul_neg_of_pos_of_neg (mul_pos (mul_pos hsq1 hk_gt) hsq2) hneg
    have hprod' : 0 < (g.eval (-t) * g.derivative.eval (-t)) * (g.coeff k * (-t) ^ k * (g.derivative.coeff m * (-t) ^ m)) := by
      have : (g.eval (-t) * (g.coeff k * (-t) ^ k)) * (g.derivative.eval (-t) * (g.derivative.coeff m * (-t) ^ m)) =
          (g.eval (-t) * g.derivative.eval (-t)) * (g.coeff k * (-t) ^ k * (g.derivative.coeff m * (-t) ^ m)) := by ring
      rwa [← this]
    exact neg_of_mul_pos_left hprod' hcoeff_neg.le
  exact ⟨hmul_pos_add, hmul_neg_sub⟩

lemma rolle_no_root_pos_contra {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (r : Polynomial K) {u v : K} (huv : u < v) (hruv : r.eval u = r.eval v)
    (hpos : ∀ c : K, u < c → c < v → 0 < r.derivative.eval c) : False := by
  set h : Polynomial K := r - Polynomial.C (r.eval u)
  have hhu : h.eval u = 0 := by simp [h]
  have hhv : h.eval v = 0 := by simp [h, hruv]
  have hhderiv : h.derivative = r.derivative := by simp [h]
  have hh_ne : h ≠ 0 := by
    intro h0
    have hd0 : r.derivative = 0 := by rw [← hhderiv, h0, Polynomial.derivative_zero]
    have hm : 0 < r.derivative.eval ((u + v) / 2) := hpos ((u + v) / 2) (by linarith) (by linarith)
    rw [hd0, Polynomial.eval_zero] at hm
    exact lt_irrefl 0 hm
  obtain ⟨δ, hδ_pos, hloc_u⟩ := local_poly_deriv_sign h u hh_ne hhu
  set t₀ := min (δ / 2) ((v - u) / 2)
  have ht₀_pos : 0 < t₀ := lt_min (half_pos hδ_pos) (half_pos (sub_pos.mpr huv))
  have ht₀_lt : t₀ < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
  set a₀ := u + t₀
  have hua₀ : u < a₀ := lt_add_of_pos_right u ht₀_pos
  have ha₀v : a₀ < v := by
    have : t₀ ≤ (v - u) / 2 := min_le_right _ _
    linarith
  have ha₀_pos : 0 < h.eval a₀ := by
    have hmul : 0 < h.eval a₀ * h.derivative.eval a₀ := (hloc_u t₀ ht₀_pos ht₀_lt).1
    have hd_pos : 0 < h.derivative.eval a₀ := by rw [hhderiv]; exact hpos a₀ hua₀ ha₀v
    exact pos_of_mul_pos_left hmul hd_pos.le
  classical
  set S : Finset K := h.roots.toFinset.filter (fun x => a₀ < x ∧ x ≤ v)
  have hv_mem : v ∈ S := by
    rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hh_ne]
    exact ⟨hhv, ha₀v, le_rfl⟩
  have hS_ne : S.Nonempty := ⟨v, hv_mem⟩
  set w := S.min' hS_ne
  have hw_mem : w ∈ S := Finset.min'_mem S hS_ne
  have hw_root : h.eval w = 0 := by
    rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hh_ne] at hw_mem
    exact hw_mem.1
  have ha₀w : a₀ < w := (Finset.mem_filter.mp hw_mem).2.1
  have hwv : w ≤ v := (Finset.mem_filter.mp hw_mem).2.2
  have hw_pos : ∀ x : K, a₀ ≤ x → x < w → 0 < h.eval x := by
    intro x hax hxw
    rcases eq_or_lt_of_le hax with rfl | hax_lt
    · exact ha₀_pos
    · by_contra hxle
      have hx_ne : h.eval x ≠ 0 := by
        intro hx0
        have hxS : x ∈ S := by
          rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hh_ne]
          exact ⟨hx0, hax_lt, le_trans hxw.le hwv⟩
        have hle : w ≤ x := Finset.min'_le S x hxS
        exact not_lt.mpr hle hxw
      have hx_neg : h.eval x < 0 := lt_of_le_of_ne (not_lt.mp hxle) hx_ne
      obtain ⟨c, hac, hcx, hc0⟩ := hIVT (-h) hax_lt (by simpa using ha₀_pos) (by simpa using hx_neg)
      have hcS : c ∈ S := by
        rw [Finset.mem_filter, Multiset.mem_toFinset, Polynomial.mem_roots hh_ne]
        refine ⟨?_, hac, le_trans (lt_trans hcx hxw).le hwv⟩
        simpa using hc0
      have hle : w ≤ c := Finset.min'_le S c hcS
      exact not_lt.mpr hle (lt_trans hcx hxw)
  obtain ⟨ε, hε_pos, hloc_w⟩ := local_poly_deriv_sign h w hh_ne hw_root
  set t₁ := min (ε / 2) ((w - a₀) / 2)
  have ht₁_pos : 0 < t₁ := lt_min (half_pos hε_pos) (half_pos (sub_pos.mpr ha₀w))
  have ht₁_lt : t₁ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε_pos)
  set y := w - t₁
  have hay : a₀ < y := by
    have : t₁ ≤ (w - a₀) / 2 := min_le_right _ _
    linarith
  have hyw : y < w := sub_lt_self w ht₁_pos
  have hy_pos : 0 < h.eval y := hw_pos y hay.le hyw
  have hdy_pos : 0 < h.derivative.eval y := by
    rw [hhderiv]
    exact hpos y (lt_trans hua₀ hay) (lt_of_lt_of_le hyw hwv)
  have hmul_neg : h.eval y * h.derivative.eval y < 0 := (hloc_w t₁ ht₁_pos ht₁_lt).2
  exact lt_irrefl 0 (lt_trans (mul_pos hy_pos hdy_pos) hmul_neg)

lemma poly_rolle {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (r : Polynomial K) {u v : K} (huv : u < v) (hruv : r.eval u = r.eval v) :
    ∃ c : K, u < c ∧ c < v ∧ r.derivative.eval c = 0 := by
  by_contra hno
  push Not at hno
  set m := (u + v) / 2
  have hum : u < m := by dsimp [m]; linarith
  have hmv : m < v := by dsimp [m]; linarith
  have hm_ne : r.derivative.eval m ≠ 0 := hno m hum hmv
  rcases lt_trichotomy (r.derivative.eval m) 0 with hm_neg | hm0 | hm_pos
  · have hneg_all : ∀ c : K, u < c → c < v → r.derivative.eval c < 0 := by
      intro c huc hcv
      rcases lt_trichotomy c m with hcm | rfl | hmc
      · by_contra hge
        have hpos_c : 0 < r.derivative.eval c := lt_of_le_of_ne (not_lt.mp hge) (hno c huc hcv).symm
        obtain ⟨z, hcz, hzm, hz0⟩ := hIVT (-r.derivative) hcm (by simpa using hpos_c) (by simpa using hm_neg)
        exact hno z (lt_trans huc hcz) (lt_trans hzm hmv) (by simpa using hz0)
      · exact hm_neg
      · by_contra hge
        have hpos_c : 0 < r.derivative.eval c := lt_of_le_of_ne (not_lt.mp hge) (hno c huc hcv).symm
        obtain ⟨z, hmz, hzc, hz0⟩ := hIVT r.derivative hmc hm_neg hpos_c
        exact hno z (lt_trans hum hmz) (lt_trans hzc hcv) hz0
    have hpos_neg : ∀ c : K, u < c → c < v → 0 < (-r).derivative.eval c := by
      intro c huc hcv
      rw [Polynomial.derivative_neg, Polynomial.eval_neg]
      exact neg_pos.mpr (hneg_all c huc hcv)
    exact rolle_no_root_pos_contra hIVT (-r) huv (by simp [hruv]) hpos_neg
  · exact hm_ne hm0
  · have hpos_all : ∀ c : K, u < c → c < v → 0 < r.derivative.eval c := by
      intro c huc hcv
      rcases lt_trichotomy c m with hcm | rfl | hmc
      · by_contra hle
        have hneg_c : r.derivative.eval c < 0 := lt_of_le_of_ne (not_lt.mp hle) (hno c huc hcv)
        obtain ⟨z, hcz, hzm, hz0⟩ := hIVT r.derivative hcm hneg_c hm_pos
        exact hno z (lt_trans huc hcz) (lt_trans hzm hmv) hz0
      · exact hm_pos
      · by_contra hle
        have hneg_c : r.derivative.eval c < 0 := lt_of_le_of_ne (not_lt.mp hle) (hno c huc hcv)
        obtain ⟨z, hmz, hzc, hz0⟩ := hIVT (-r.derivative) hmc (by simpa using hm_pos) (by simpa using hneg_c)
        exact hno z (lt_trans hum hmz) (lt_trans hzc hcv) (by simpa using hz0)
    exact rolle_no_root_pos_contra hIVT r huv hruv hpos_all

end Hilbert17H2Proof

theorem solve : OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1.H2 := by
  intro K _ _ _ hIVT
  refine ⟨?_, Hilbert17H2Proof.asymptotic_leading_sign⟩
  intro p u v huv
  set r : Polynomial K := Polynomial.C (v - u) * p - Polynomial.C (p.eval v - p.eval u) * Polynomial.X
  have hruv : r.eval u = r.eval v := by
    dsimp [r]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  obtain ⟨c, huc, hcv, hc0⟩ := Hilbert17H2Proof.poly_rolle hIVT r huv hruv
  refine ⟨c, huc, hcv, ?_⟩
  have hrderiv : r.derivative = Polynomial.C (v - u) * p.derivative - Polynomial.C (p.eval v - p.eval u) := by
    dsimp [r]
    simp
  rw [hrderiv] at hc0
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C] at hc0
  linarith

end OMA.Leaf4
end Leaf4

section Leaf5
namespace OMA.Leaf5

namespace Hilbert17H3Proof

section BasicHelpers

def sameSign {K₁ K₂ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂]
    (x : K₁) (y : K₂) : Prop :=
  (x < 0 ↔ y < 0) ∧ (x = 0 ↔ y = 0)

lemma sameSign_pos {K₁ K₂ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂]
    {x : K₁} {y : K₂} (h : sameSign x y) : 0 < x ↔ 0 < y := by
  constructor
  · intro hx
    have h1 : ¬ (x < 0) := not_lt.mpr hx.le
    have h2 : x ≠ 0 := hx.ne'
    have hy1 : ¬ (y < 0) := fun hy => h1 (h.1.mpr hy)
    have hy2 : y ≠ 0 := fun hy => h2 (h.2.mpr hy)
    exact lt_of_le_of_ne (not_lt.mp hy1) hy2.symm
  · intro hy
    have h1 : ¬ (y < 0) := not_lt.mpr hy.le
    have h2 : y ≠ 0 := hy.ne'
    have hx1 : ¬ (x < 0) := fun hx => h1 (h.1.mp hx)
    have hx2 : x ≠ 0 := fun hx => h2 (h.2.mp hx)
    exact lt_of_le_of_ne (not_lt.mp hx1) hx2.symm

lemma sameSign_symm {K₁ K₂ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂]
    {x : K₁} {y : K₂} (h : sameSign x y) : sameSign y x :=
  ⟨h.1.symm, h.2.symm⟩

lemma sameSign_refl {K : Type} [LinearOrder K] [Zero K] (x : K) : sameSign x x :=
  ⟨Iff.rfl, Iff.rfl⟩

lemma sameSign_trans {K₁ K₂ K₃ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂]
    [LinearOrder K₃] [Zero K₃] {x : K₁} {y : K₂} {z : K₃}
    (h1 : sameSign x y) (h2 : sameSign y z) : sameSign x z :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

lemma sameSign_of_mul_pos {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x y : K} (h : 0 < x * y) : sameSign x y := by
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, mul_zero] at h
    exact lt_irrefl 0 h
  rcases lt_trichotomy y 0 with hy | rfl | hy
  · have hx : x < 0 := neg_of_mul_pos_left h hy.le
    exact ⟨⟨fun _ => hy, fun _ => hx⟩, ⟨fun hx0 => absurd hx0 hx.ne, fun hy0' => absurd hy0' hy.ne⟩⟩
  · exact absurd rfl hy0
  · have hx : 0 < x := pos_of_mul_pos_left h hy.le
    exact ⟨⟨fun hx' => absurd hx' (not_lt.mpr hx.le), fun hy' => absurd hy' (not_lt.mpr hy.le)⟩,
      ⟨fun hx0 => absurd hx0 hx.ne', fun hy0' => absurd hy0' hy.ne'⟩⟩

lemma sameSign_mul {K₁ K₂ : Type} [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    {a₁ b₁ : K₁} {a₂ b₂ : K₂} (ha : sameSign a₁ a₂) (hb : sameSign b₁ b₂) :
    sameSign (a₁ * b₁) (a₂ * b₂) := by
  have h0 : a₁ * b₁ = 0 ↔ a₂ * b₂ = 0 := by
    simp only [mul_eq_zero, ha.2, hb.2]
  refine ⟨?_, h0⟩
  rcases lt_trichotomy a₁ 0 with ha1 | ha1 | ha1
  · have ha2 : a₂ < 0 := ha.1.mp ha1
    rcases lt_trichotomy b₁ 0 with hb1 | hb1 | hb1
    · have hb2 : b₂ < 0 := hb.1.mp hb1
      have h1 : 0 < a₁ * b₁ := mul_pos_of_neg_of_neg ha1 hb1
      have h2 : 0 < a₂ * b₂ := mul_pos_of_neg_of_neg ha2 hb2
      exact ⟨fun h => absurd h (not_lt.mpr h1.le), fun h => absurd h (not_lt.mpr h2.le)⟩
    · subst hb1
      have hb2 : b₂ = 0 := hb.2.mp rfl
      simp [hb2]
    · have hb2 : 0 < b₂ := (sameSign_pos hb).mp hb1
      exact ⟨fun _ => mul_neg_of_neg_of_pos ha2 hb2, fun _ => mul_neg_of_neg_of_pos ha1 hb1⟩
  · subst ha1
    have ha2 : a₂ = 0 := ha.2.mp rfl
    simp [ha2]
  · have ha2 : 0 < a₂ := (sameSign_pos ha).mp ha1
    rcases lt_trichotomy b₁ 0 with hb1 | hb1 | hb1
    · have hb2 : b₂ < 0 := hb.1.mp hb1
      exact ⟨fun _ => mul_neg_of_pos_of_neg ha2 hb2, fun _ => mul_neg_of_pos_of_neg ha1 hb1⟩
    · subst hb1
      have hb2 : b₂ = 0 := hb.2.mp rfl
      simp [hb2]
    · have hb2 : 0 < b₂ := (sameSign_pos hb).mp hb1
      have h1 : 0 < a₁ * b₁ := mul_pos ha1 hb1
      have h2 : 0 < a₂ * b₂ := mul_pos ha2 hb2
      exact ⟨fun h => absurd h (not_lt.mpr h1.le), fun h => absurd h (not_lt.mpr h2.le)⟩

lemma sameSign_zero {K₁ K₂ : Type} [LinearOrder K₁] [Zero K₁] [LinearOrder K₂] [Zero K₂] :
    sameSign (0 : K₁) (0 : K₂) :=
  ⟨by simp, by simp⟩

lemma sameSign_neg_one_pow {K₁ K₂ : Type} [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂] (d : ℕ) :
    sameSign ((-1 : K₁) ^ d) ((-1 : K₂) ^ d) := by
  induction d with
  | zero =>
    simp only [pow_zero]
    exact ⟨by simp [not_lt.mpr zero_le_one], by simp⟩
  | succ d ih =>
    rw [pow_succ, pow_succ]
    exact sameSign_mul ih ⟨by simp, by simp⟩

end BasicHelpers

section AnalyticHelpers

lemma poly_const_sign_no_root {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (p : Polynomial K) {a b : K} (hab : a ≤ b)
    (hno : ∀ c : K, a ≤ c → c ≤ b → p.eval c ≠ 0) :
    sameSign (p.eval a) (p.eval b) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact sameSign_refl _
  · have ha_ne : p.eval a ≠ 0 := hno a le_rfl hab
    have hb_ne : p.eval b ≠ 0 := hno b hab le_rfl
    rcases lt_trichotomy (p.eval a) 0 with ha | ha | ha <;>
    rcases lt_trichotomy (p.eval b) 0 with hb | hb | hb
    · exact ⟨⟨fun _ => hb, fun _ => ha⟩, ⟨fun h => absurd h ha_ne, fun h => absurd h hb_ne⟩⟩
    · exact absurd hb hb_ne
    · obtain ⟨c, hac, hcb, hc0⟩ := hIVT p hlt ha hb
      exact absurd hc0 (hno c hac.le hcb.le)
    · exact absurd ha ha_ne
    · exact absurd ha ha_ne
    · exact absurd ha ha_ne
    · obtain ⟨c, hac, hcb, hc0⟩ := hIVT (-p) hlt (by simpa using ha) (by simpa using hb)
      exact absurd (by simpa using hc0) (hno c hac.le hcb.le)
    · exact absurd hb hb_ne
    · exact ⟨⟨fun h => absurd h (not_lt.mpr ha.le), fun h => absurd h (not_lt.mpr hb.le)⟩,
        ⟨fun h => absurd h ha_ne, fun h => absurd h hb_ne⟩⟩

lemma poly_const_sign_open {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (p : Polynomial K) {x y : K} (hno : ∀ c : K, min x y ≤ c → c ≤ max x y → p.eval c ≠ 0) :
    sameSign (p.eval x) (p.eval y) := by
  rcases le_total x y with hxy | hyx
  · exact poly_const_sign_no_root hIVT p hxy (fun c hc1 hc2 =>
      hno c (by simpa [min_eq_left hxy] using hc1) (by simpa [max_eq_right hxy] using hc2))
  · exact sameSign_symm (poly_const_sign_no_root hIVT p hyx (fun c hc1 hc2 =>
      hno c (by simpa [min_eq_right hyx] using hc1) (by simpa [max_eq_left hyx] using hc2)))

lemma poly_unique_root_no_deriv {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hMVT : ∀ (p : Polynomial K) {u v : K}, u < v →
      ∃ c : K, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (p : Polynomial K) {r₁ r₂ : K}
    (hr₁ : p.eval r₁ = 0) (hr₂ : p.eval r₂ = 0)
    (hd : ∀ c : K, min r₁ r₂ < c → c < max r₁ r₂ → p.derivative.eval c ≠ 0) :
    r₁ = r₂ := by
  rcases lt_trichotomy r₁ r₂ with hlt | heq | hgt
  · obtain ⟨c, hc1, hc2, hmeq⟩ := hMVT p hlt
    rw [hr₁, hr₂, sub_zero] at hmeq
    have hc_ne : p.derivative.eval c ≠ 0 := hd c (by simpa [min_eq_left hlt.le] using hc1) (by simpa [max_eq_right hlt.le] using hc2)
    have hvu : r₂ - r₁ ≠ 0 := (sub_pos.mpr hlt).ne'
    have hmul : (r₂ - r₁) * p.derivative.eval c = 0 := hmeq.symm
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hvu
    · exact absurd h hc_ne
  · exact heq
  · obtain ⟨c, hc1, hc2, hmeq⟩ := hMVT p hgt
    rw [hr₁, hr₂, sub_zero] at hmeq
    have hc_ne : p.derivative.eval c ≠ 0 := hd c (by simpa [min_eq_right hgt.le] using hc1) (by simpa [max_eq_left hgt.le] using hc2)
    have hvu : r₁ - r₂ ≠ 0 := (sub_pos.mpr hgt).ne'
    have hmul : (r₁ - r₂) * p.derivative.eval c = 0 := hmeq.symm
    rcases mul_eq_zero.mp hmul with h | h
    · exact absurd h hvu
    · exact absurd h hc_ne

lemma poly_root_iff_opp_sign_on_bounded {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (hMVT : ∀ (p : Polynomial K) {u v : K}, u < v →
      ∃ c : K, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (p : Polynomial K) {a b : K} (hab : a < b)
    (hd : ∀ c : K, a < c → c < b → p.derivative.eval c ≠ 0) :
    (∃ r : K, a < r ∧ r < b ∧ p.eval r = 0) ↔ p.eval a * p.eval b < 0 := by
  constructor
  · rintro ⟨r, har, hrb, hr0⟩
    have hda : p.eval a ≠ 0 := by
      intro ha0
      obtain ⟨c, h1, h2, hmeq⟩ := hMVT p har
      rw [ha0, hr0, sub_zero] at hmeq
      rcases mul_eq_zero.mp hmeq.symm with h | h
      · exact (sub_pos.mpr har).ne' h
      · exact hd c h1 (lt_trans h2 hrb) h
    have hdb : p.eval b ≠ 0 := by
      intro hb0
      obtain ⟨c, h1, h2, hmeq⟩ := hMVT p hrb
      rw [hb0, hr0, sub_zero] at hmeq
      rcases mul_eq_zero.mp hmeq.symm with h | h
      · exact (sub_pos.mpr hrb).ne' h
      · exact hd c (lt_trans har h1) h2 h
    by_contra hnot
    have hnonneg : 0 ≤ p.eval a * p.eval b := not_lt.mp hnot
    have hpos : 0 < p.eval a * p.eval b := lt_of_le_of_ne hnonneg (mul_ne_zero hda hdb).symm
    obtain ⟨c₁, hac₁, hc₁r, hm₁⟩ := hMVT p har
    obtain ⟨c₂, hrc₂, hc₂b, hm₂⟩ := hMVT p hrb
    rw [hr0, zero_sub] at hm₁
    rw [hr0, sub_zero] at hm₂
    have hdc₁_ne : p.derivative.eval c₁ ≠ 0 := hd c₁ hac₁ (lt_trans hc₁r hrb)
    have hdc₂_ne : p.derivative.eval c₂ ≠ 0 := hd c₂ (lt_trans har hrc₂) hc₂b
    have hc₁c₂ : c₁ < c₂ := lt_trans hc₁r hrc₂
    have hprod_d : p.derivative.eval c₁ * p.derivative.eval c₂ < 0 := by
      have h1 : (r - a) * (b - r) > 0 := mul_pos (sub_pos.mpr har) (sub_pos.mpr hrb)
      have hmul_eq : ((r - a) * (b - r)) * (p.derivative.eval c₁ * p.derivative.eval c₂) =
          -(p.eval a * p.eval b) := by
        have e1 : (r - a) * p.derivative.eval c₁ = -p.eval a := hm₁.symm
        have e2 : (b - r) * p.derivative.eval c₂ = p.eval b := hm₂.symm
        calc
          ((r - a) * (b - r)) * (p.derivative.eval c₁ * p.derivative.eval c₂)
              = ((r - a) * p.derivative.eval c₁) * ((b - r) * p.derivative.eval c₂) := by ring
          _ = (-p.eval a) * p.eval b := by rw [e1, e2]
          _ = -(p.eval a * p.eval b) := by ring
      have hneg : ((r - a) * (b - r)) * (p.derivative.eval c₁ * p.derivative.eval c₂) < 0 := by
        rw [hmul_eq]
        exact neg_lt_zero.mpr hpos
      exact neg_of_mul_neg_right hneg h1.le
    rcases lt_trichotomy (p.derivative.eval c₁) 0 with hd₁ | hd₁ | hd₁
    · have hd₂ : 0 < p.derivative.eval c₂ := pos_of_mul_neg_right hprod_d hd₁.le
      obtain ⟨z, hz1, hz2, hz0⟩ := hIVT p.derivative hc₁c₂ hd₁ hd₂
      exact hd z (lt_trans hac₁ hz1) (lt_trans hz2 hc₂b) hz0
    · exact hdc₁_ne hd₁
    · have hd₂ : p.derivative.eval c₂ < 0 := neg_of_mul_neg_right hprod_d hd₁.le
      obtain ⟨z, hz1, hz2, hz0⟩ := hIVT (-p.derivative) hc₁c₂ (by simpa using hd₁) (by simpa using hd₂)
      exact hd z (lt_trans hac₁ hz1) (lt_trans hz2 hc₂b) (by simpa using hz0)
  · intro hmul
    rcases lt_trichotomy (p.eval a) 0 with ha | ha | ha
    · have hb : 0 < p.eval b := pos_of_mul_neg_right hmul ha.le
      exact hIVT p hab ha hb
    · rw [ha, zero_mul] at hmul
      exact absurd hmul (lt_irrefl 0)
    · have hb : p.eval b < 0 := neg_of_mul_neg_right hmul ha.le
      obtain ⟨c, hac, hcb, hc0⟩ := hIVT (-p) hab (by simpa using ha) (by simpa using hb)
      exact ⟨c, hac, hcb, by simpa using hc0⟩

lemma poly_no_root_bounded_left_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (p : Polynomial K) {a b x : K} (hax : a < x) (hxb : x < b)
    (hno : ∀ c : K, a < c → c < b → p.eval c ≠ 0) (ha_ne : p.eval a ≠ 0) :
    sameSign (p.eval x) (p.eval a) :=
  sameSign_symm (poly_const_sign_no_root hIVT p hax.le (fun c hc1 hc2 => by
    rcases eq_or_lt_of_le hc1 with rfl | h1
    · exact ha_ne
    · exact hno c h1 (lt_of_le_of_lt hc2 hxb)))

lemma poly_no_root_bounded_right_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (p : Polynomial K) {a b x : K} (hax : a < x) (hxb : x < b)
    (hno : ∀ c : K, a < c → c < b → p.eval c ≠ 0) (hb_ne : p.eval b ≠ 0) :
    sameSign (p.eval x) (p.eval b) :=
  poly_const_sign_no_root hIVT p hxb.le (fun c hc1 hc2 => by
    rcases eq_or_lt_of_le hc2 with rfl | h2
    · exact hb_ne
    · exact hno c (lt_of_lt_of_le hax hc1) h2)

lemma poly_asymp_neg {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hAsymp : ∀ (p : Polynomial K), p ≠ 0 →
      ∃ M : K, ∀ x : K, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ M : K, ∀ x : K, x < M →
      sameSign (p.eval x) ((-1 : K) ^ p.natDegree * p.leadingCoeff) := by
  set q : Polynomial K := p.comp (-Polynomial.X)
  have hq : q ≠ 0 := by
    intro h0
    have hcomp : q.comp (-Polynomial.X) = p := by
      dsimp [q]
      rw [Polynomial.comp_assoc]
      simp
    rw [h0, Polynomial.zero_comp] at hcomp
    exact hp hcomp.symm
  have hdeg : q.natDegree = p.natDegree := by
    dsimp [q]
    rw [Polynomial.natDegree_comp]
    simp
  have hlead : q.leadingCoeff = p.leadingCoeff * (-1 : K) ^ p.natDegree := by
    dsimp [q]
    rw [Polynomial.leadingCoeff_comp]
    · simp
    · simp
  obtain ⟨M, hM⟩ := hAsymp q hq
  refine ⟨-M, fun x hx => ?_⟩
  have hnx : M < -x := by linarith
  have hqnx := hM (-x) hnx
  have hev : q.eval (-x) = p.eval x := by
    dsimp [q]
    rw [Polynomial.eval_comp]
    simp
  rw [hev, hlead] at hqnx
  have hne : p.leadingCoeff * (-1 : K) ^ p.natDegree ≠ 0 :=
    mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) (pow_ne_zero _ (by norm_num))
  have hpx_ne : p.eval x ≠ 0 := by
    intro hp0
    rw [hp0] at hqnx
    rcases lt_trichotomy (p.leadingCoeff * (-1 : K) ^ p.natDegree) 0 with hl | hl | hl
    · exact lt_irrefl 0 (hqnx.2.mpr hl)
    · exact hne hl
    · exact lt_irrefl 0 (hqnx.1.mpr hl)
  have hss : sameSign (p.eval x) (p.leadingCoeff * (-1 : K) ^ p.natDegree) :=
    ⟨hqnx.2, ⟨fun h => absurd h hpx_ne, fun h => absurd h hne⟩⟩
  simpa [mul_comm] using hss

lemma poly_asymp_pos {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hAsymp : ∀ (p : Polynomial K), p ≠ 0 →
      ∃ M : K, ∀ x : K, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ M : K, ∀ x : K, M < x → sameSign (p.eval x) p.leadingCoeff := by
  obtain ⟨M, hM⟩ := hAsymp p hp
  refine ⟨M, fun x hx => ?_⟩
  have hx' := hM x hx
  have hne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hpx_ne : p.eval x ≠ 0 := by
    intro hp0
    rw [hp0] at hx'
    rcases lt_trichotomy p.leadingCoeff 0 with hl | hl | hl
    · exact lt_irrefl 0 (hx'.2.mpr hl)
    · exact hne hl
    · exact lt_irrefl 0 (hx'.1.mpr hl)
  exact ⟨hx'.2, ⟨fun h => absurd h hpx_ne, fun h => absurd h hne⟩⟩

end AnalyticHelpers

section RootListAndCells

noncomputable def rootFinset {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : List (Polynomial K)) : Finset K := by
  classical
  exact (L.filter (fun p => decide (p ≠ 0))).toFinset.biUnion (fun p => p.roots.toFinset)

noncomputable def rootList {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : List (Polynomial K)) : List K :=
  (rootFinset L).sort (· ≤ ·)

lemma pairwise_lt_of_le_of_nodup {K : Type} [LinearOrder K] :
    ∀ {l : List K}, l.Pairwise (· ≤ ·) → l.Nodup → l.Pairwise (· < ·)
  | [], _, _ => List.Pairwise.nil
  | a :: t, hp, hn => by
    rw [List.pairwise_cons] at hp ⊢
    rw [List.nodup_cons] at hn
    exact ⟨fun b hb => lt_of_le_of_ne (hp.1 b hb) (fun h => hn.1 (h ▸ hb)),
      pairwise_lt_of_le_of_nodup hp.2 hn.2⟩

lemma rootList_pairwise_lt {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : List (Polynomial K)) : (rootList L).Pairwise (· < ·) :=
  pairwise_lt_of_le_of_nodup (Finset.pairwise_sort (rootFinset L) (· ≤ ·)) ((rootFinset L).sort_nodup (· ≤ ·))

lemma mem_rootList {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : List (Polynomial K)} {x : K} :
    x ∈ rootList L ↔ ∃ p ∈ L, p ≠ 0 ∧ p.eval x = 0 := by
  classical
  rw [rootList, Finset.mem_sort, rootFinset, Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, hxp⟩
    rw [List.mem_toFinset, List.mem_filter] at hp
    have hp0 : p ≠ 0 := by simpa using hp.2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0] at hxp
    exact ⟨p, hp.1, hp0, hxp⟩
  · rintro ⟨p, hpL, hp0, hpx⟩
    refine ⟨p, ?_, ?_⟩
    · rw [List.mem_toFinset, List.mem_filter]
      exact ⟨hpL, by simpa using hp0⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
      exact hpx

lemma list_eq_of_pairwise_lt_of_mem_iff {K : Type} [LinearOrder K] :
    ∀ {l₁ l₂ : List K}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
      (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: t₂, _, _, hmem => by
    have : b ∈ ([] : List K) := (hmem b).mpr (by simp)
    simp at this
  | a :: t₁, [], _, _, hmem => by
    have : a ∈ ([] : List K) := (hmem a).mp (by simp)
    simp at this
  | a :: t₁, b :: t₂, h1, h2, hmem => by
    rw [List.pairwise_cons] at h1 h2
    have ha2 : a = b ∨ a ∈ t₂ := List.mem_cons.mp ((hmem a).mp (by simp))
    have hb1 : b = a ∨ b ∈ t₁ := List.mem_cons.mp ((hmem b).mpr (by simp))
    have hab : a = b := by
      rcases ha2 with rfl | ha_t2
      · rfl
      · rcases hb1 with rfl | hb_t1
        · rfl
        · exact absurd (lt_trans (h2.1 a ha_t2) (h1.1 b hb_t1)) (lt_irrefl b)
    subst hab
    congr 1
    refine list_eq_of_pairwise_lt_of_mem_iff h1.2 h2.2 (fun x => ?_)
    have hx := hmem x
    simp only [List.mem_cons] at hx
    constructor
    · intro hxt1
      have hxa : x ≠ a := (h1.1 x hxt1).ne'
      rcases hx.mp (Or.inr hxt1) with rfl | hxt2
      · exact absurd rfl hxa
      · exact hxt2
    · intro hxt2
      have hxa : x ≠ a := (h2.1 x hxt2).ne'
      rcases hx.mpr (Or.inr hxt2) with rfl | hxt1
      · exact absurd rfl hxa
      · exact hxt1

lemma getElem_le_of_pairwise_lt {K : Type} [LinearOrder K] {R : List K}
    (hR : R.Pairwise (· < ·)) {i j : ℕ} (hi : i < R.length) (hj : j < R.length) (hij : i ≤ j) :
    R[i] ≤ R[j] := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact (List.pairwise_iff_getElem.mp hR i j hi hj hlt).le

def inCell {K : Type} [LinearOrder K] (R : List K) (j : ℕ) (x : K) : Prop :=
  (∀ i (hi : i < R.length), i < j → R[i] < x) ∧
  (∀ i (hi : i < R.length), j ≤ i → x < R[i])

lemma inCell_not_mem {K : Type} [LinearOrder K] {R : List K} {j : ℕ} {x : K}
    (hx : inCell R j x) : x ∉ R := by
  intro hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
  rcases lt_or_ge i j with hij | hji
  · exact lt_irrefl _ (hx.1 i hi hij)
  · exact lt_irrefl _ (hx.2 i hi hji)

lemma inCell_unique {K : Type} [LinearOrder K] {R : List K} {j₁ j₂ : ℕ} {x : K}
    (h1 : j₁ ≤ R.length) (h2 : j₂ ≤ R.length)
    (hx1 : inCell R j₁ x) (hx2 : inCell R j₂ x) : j₁ = j₂ := by
  rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
  · have hj1 : j₁ < R.length := lt_of_lt_of_le hlt h2
    exact absurd (lt_trans (hx2.1 j₁ hj1 hlt) (hx1.2 j₁ hj1 le_rfl)) (lt_irrefl _)
  · exact heq
  · have hj2 : j₂ < R.length := lt_of_lt_of_le hgt h1
    exact absurd (lt_trans (hx1.1 j₂ hj2 hgt) (hx2.2 j₂ hj2 le_rfl)) (lt_irrefl _)

lemma exists_inCell_of_not_mem {K : Type} [LinearOrder K] :
    ∀ {R : List K}, R.Pairwise (· < ·) → ∀ {x : K}, x ∉ R → ∃ j ≤ R.length, inCell R j x
  | [], _, x, _ => ⟨0, le_rfl, ⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi⟩⟩
  | a :: t, hR, x, hx => by
    rw [List.pairwise_cons] at hR
    have hxa : x ≠ a := fun h => hx (by simp [h])
    have hxt : x ∉ t := fun h => hx (by simp [h])
    rcases lt_trichotomy x a with hlt | rfl | hgt
    · refine ⟨0, Nat.zero_le _, ⟨fun _ _ h => by omega, fun i hi _ => ?_⟩⟩
      cases i with
      | zero => exact hlt
      | succ i =>
        have hi' : i < t.length := by simpa using hi
        exact lt_trans hlt (hR.1 t[i] (List.getElem_mem hi'))
    · exact absurd rfl hxa
    · obtain ⟨j, hj_le, hj⟩ := exists_inCell_of_not_mem hR.2 hxt
      refine ⟨j + 1, Nat.succ_le_succ hj_le, ⟨?_, ?_⟩⟩
      · intro i hi hij
        cases i with
        | zero => exact hgt
        | succ i => exact hj.1 i (by simpa using hi) (Nat.succ_lt_succ_iff.mp hij)
      · intro i hi hij
        cases i with
        | zero => omega
        | succ i => exact hj.2 i (by simpa using hi) (Nat.succ_le_succ_iff.mp hij)

lemma exists_point_inCell {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {R : List K} (hR : R.Pairwise (· < ·)) {j : ℕ} (hj : j ≤ R.length) :
    ∃ x : K, inCell R j x := by
  by_cases hlen : R.length = 0
  · refine ⟨0, ⟨fun _ hi => by omega, fun _ hi => by omega⟩⟩
  · have hpos : 0 < R.length := Nat.pos_of_ne_zero hlen
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨R[0] - 1, ⟨fun _ _ h => by omega, fun i hi _ => ?_⟩⟩
      have hle : R[0] ≤ R[i] := getElem_le_of_pairwise_lt hR hpos hi (Nat.zero_le i)
      linarith
    · by_cases hjm : j = R.length
      · subst hjm
        refine ⟨R[R.length - 1] + 1, ⟨fun i hi hij => ?_, fun _ hi hji => by omega⟩⟩
        have hle : R[i] ≤ R[R.length - 1] := getElem_le_of_pairwise_lt hR hi (Nat.sub_lt hpos zero_lt_one) (Nat.le_sub_one_of_lt hij)
        linarith
      · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
        have hj_lt : j < R.length := lt_of_le_of_ne hj hjm
        have hjm1 : j - 1 < R.length := lt_trans (Nat.sub_lt hj_pos zero_lt_one) hj_lt
        have hlt_adj : R[j - 1] < R[j] := List.pairwise_iff_getElem.mp hR (j - 1) j hjm1 hj_lt (by omega)
        set x := (R[j - 1] + R[j]) / 2
        have hx1 : R[j - 1] < x := by dsimp [x]; linarith
        have hx2 : x < R[j] := by dsimp [x]; linarith
        refine ⟨x, ⟨fun i hi hij => ?_, fun i hi hij => ?_⟩⟩
        · have hle : R[i] ≤ R[j - 1] := getElem_le_of_pairwise_lt hR hi hjm1 (Nat.le_sub_one_of_lt hij)
          exact lt_of_le_of_lt hle hx1
        · have hle : R[j] ≤ R[i] := getElem_le_of_pairwise_lt hR hj_lt hi hij
          exact lt_of_lt_of_le hx2 hle

lemma inCell_interval_no_root {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {L : List (Polynomial K)} {j : ℕ} {x y : K}
    (hx : inCell (rootList L) j x) (hy : inCell (rootList L) j y)
    {p : Polynomial K} (hpL : p ∈ L) (hp0 : p ≠ 0) :
    ∀ c : K, min x y ≤ c → c ≤ max x y → p.eval c ≠ 0 := by
  intro c hc1 hc2 hc0
  have hcR : c ∈ rootList L := mem_rootList.mpr ⟨p, hpL, hp0, hc0⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcR
  rcases lt_or_ge i j with hij | hji
  · have h1 := hx.1 i hi hij
    have h2 := hy.1 i hi hij
    have : (rootList L)[i] < min x y := lt_min h1 h2
    exact lt_irrefl _ (lt_of_lt_of_le this hc1)
  · have h1 := hx.2 i hi hji
    have h2 := hy.2 i hi hji
    have : max x y < (rootList L)[i] := max_lt h1 h2
    exact lt_irrefl _ (lt_of_le_of_lt hc2 this)

lemma inCell_const_sign {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    {L : List (Polynomial K)} {j : ℕ} {x y : K}
    (hx : inCell (rootList L) j x) (hy : inCell (rootList L) j y)
    {p : Polynomial K} (hpL : p ∈ L) :
    sameSign (p.eval x) (p.eval y) := by
  by_cases hp0 : p = 0
  · subst hp0; simp [sameSign_refl]
  · exact poly_const_sign_open hIVT p (inCell_interval_no_root hx hy hpL hp0)

end RootListAndCells

section SignTableAndFilter

def SignTableMatch {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (φ₁ : A →+* K₁) (φ₂ : A →+* K₂) (P : List (Polynomial A)) : Prop :=
  let R₁ := rootList (P.map (Polynomial.map φ₁))
  let R₂ := rootList (P.map (Polynomial.map φ₂))
  R₁.length = R₂.length ∧
  (∀ (i : ℕ) (h₁ : i < R₁.length) (h₂ : i < R₂.length), ∀ p ∈ P,
    sameSign ((p.map φ₁).eval R₁[i]) ((p.map φ₂).eval R₂[i])) ∧
  (∀ (j : ℕ) (x₁ : K₁) (x₂ : K₂),
    j ≤ R₁.length → inCell R₁ j x₁ → inCell R₂ j x₂ → ∀ p ∈ P,
    sameSign ((p.map φ₁).eval x₁) ((p.map φ₂).eval x₂))

lemma poly_map_eq_zero_iff_of_signTableMatch {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    {φ₁ : A →+* K₁} {φ₂ : A →+* K₂} {P : List (Polynomial A)}
    (hST : SignTableMatch φ₁ φ₂ P) {p : Polynomial A} (hp : p ∈ P) :
    p.map φ₁ = 0 ↔ p.map φ₂ = 0 := by
  set R₁ := rootList (P.map (Polynomial.map φ₁))
  set R₂ := rootList (P.map (Polynomial.map φ₂))
  have hR₁ : R₁.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₂ : R₂.Pairwise (· < ·) := rootList_pairwise_lt _
  obtain ⟨x₁, hx₁⟩ := exists_point_inCell hR₁ (Nat.zero_le R₁.length)
  have hbase_lt : ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
      (R : List K), R.Pairwise (· < ·) → ∀ (k : ℕ),
      inCell R 0 ((if h : R.length = 0 then (0 : K) else R[0]) - ((k + 1 : ℕ) : K)) := by
    intro K _ _ _ R hR k
    refine ⟨fun _ _ h => by omega, fun i hi _ => ?_⟩
    have hk_pos : (0 : K) < ((k + 1 : ℕ) : K) := Nat.cast_pos.mpr (Nat.succ_pos k)
    by_cases hlen : R.length = 0
    · omega
    · simp only [dif_neg hlen]
      have hpos : 0 < R.length := Nat.pos_of_ne_zero hlen
      have hle : R[0] ≤ R[i] := getElem_le_of_pairwise_lt hR hpos hi (Nat.zero_le i)
      linarith
  constructor
  · intro hp1
    by_contra hp2
    set N := (p.map φ₂).natDegree
    have hroots : ∀ k : ℕ, (k : ℕ) ≤ N →
        (if h : R₂.length = 0 then (0 : K₂) else R₂[0]) - ((k + 1 : ℕ) : K₂) ∈ (p.map φ₂).roots := by
      intro k _
      rw [Polynomial.mem_roots hp2]
      have hx₂ := hbase_lt R₂ hR₂ k
      have hss := hST.2.2 0 x₁ _ (Nat.zero_le _) hx₁ hx₂ p hp
      rw [hp1, Polynomial.eval_zero] at hss
      exact hss.2.mp rfl
    set b : K₂ := if h : R₂.length = 0 then 0 else R₂[0]
    set S : Finset K₂ := (Finset.range (N + 1)).image (fun k => b - ((k + 1 : ℕ) : K₂))
    have hinj : Set.InjOn (fun k : ℕ => b - ((k + 1 : ℕ) : K₂)) (Finset.range (N + 1)) := by
      intro k₁ _ k₂ _ heq
      have hcast : ((k₁ + 1 : ℕ) : K₂) = ((k₂ + 1 : ℕ) : K₂) := by linarith
      exact Nat.succ.inj (Nat.cast_injective hcast)
    have hcard : S.card = N + 1 := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hsub : S ⊆ (p.map φ₂).roots.toFinset := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      rw [Finset.mem_range] at hk
      rw [Multiset.mem_toFinset]
      exact hroots k (Nat.lt_succ_iff.mp hk)
    have hle1 : S.card ≤ (p.map φ₂).roots.toFinset.card := Finset.card_le_card hsub
    have hle2 : (p.map φ₂).roots.toFinset.card ≤ (p.map φ₂).roots.card := Multiset.toFinset_card_le _
    have hle3 : (p.map φ₂).roots.card ≤ N := Polynomial.card_roots' (p.map φ₂)
    omega
  · intro hp2
    by_contra hp1
    obtain ⟨x₂, hx₂⟩ := exists_point_inCell hR₂ (Nat.zero_le R₂.length)
    set N := (p.map φ₁).natDegree
    have hroots : ∀ k : ℕ, (k : ℕ) ≤ N →
        (if h : R₁.length = 0 then (0 : K₁) else R₁[0]) - ((k + 1 : ℕ) : K₁) ∈ (p.map φ₁).roots := by
      intro k _
      rw [Polynomial.mem_roots hp1]
      have hx₁' := hbase_lt R₁ hR₁ k
      have hss := hST.2.2 0 _ x₂ (Nat.zero_le _) hx₁' hx₂ p hp
      rw [hp2, Polynomial.eval_zero] at hss
      exact hss.2.mpr rfl
    set b : K₁ := if h : R₁.length = 0 then 0 else R₁[0]
    set S : Finset K₁ := (Finset.range (N + 1)).image (fun k => b - ((k + 1 : ℕ) : K₁))
    have hinj : Set.InjOn (fun k : ℕ => b - ((k + 1 : ℕ) : K₁)) (Finset.range (N + 1)) := by
      intro k₁ _ k₂ _ heq
      have hcast : ((k₁ + 1 : ℕ) : K₁) = ((k₂ + 1 : ℕ) : K₁) := by linarith
      exact Nat.succ.inj (Nat.cast_injective hcast)
    have hcard : S.card = N + 1 := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hsub : S ⊆ (p.map φ₁).roots.toFinset := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      rw [Finset.mem_range] at hk
      rw [Multiset.mem_toFinset]
      exact hroots k (Nat.lt_succ_iff.mp hk)
    have hle1 : S.card ≤ (p.map φ₁).roots.toFinset.card := Finset.card_le_card hsub
    have hle2 : (p.map φ₁).roots.toFinset.card ≤ (p.map φ₁).roots.card := Multiset.toFinset_card_le _
    have hle3 : (p.map φ₁).roots.card ≤ N := Polynomial.card_roots' (p.map φ₁)
    omega

lemma forall₂_filter_and_cell {K₁ K₂ : Type} [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (b₁ : K₁ → Bool) (b₂ : K₂ → Bool) :
    ∀ {l₁ : List K₁} {l₂ : List K₂},
      List.Forall₂ (fun x y => b₁ x = b₂ y) l₁ l₂ →
      (l₁.filter b₁).length = (l₂.filter b₂).length ∧
      ∀ (j : ℕ), j ≤ (l₁.filter b₁).length →
        ∃ j' ≤ l₁.length, ∀ (y₁ : K₁) (y₂ : K₂),
          inCell l₁ j' y₁ → inCell l₂ j' y₂ →
          inCell (l₁.filter b₁) j y₁ ∧ inCell (l₂.filter b₂) j y₂
  | [], [], _ => ⟨rfl, fun _ hj => ⟨0, le_rfl, fun _ _ _ _ => ⟨⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi⟩, ⟨fun _ hi => by simp at hi, fun _ hi => by simp at hi⟩⟩⟩⟩
  | a₁ :: t₁, a₂ :: t₂, hF => by
    rw [List.forall₂_cons] at hF
    obtain ⟨hlen_t, hcell_t⟩ := forall₂_filter_and_cell b₁ b₂ hF.2
    by_cases ha : b₁ a₁ = true
    · have ha2 : b₂ a₂ = true := hF.1.symm.trans ha
      simp only [List.filter_cons, ha, ha2, ↓reduceIte, List.length_cons]
      refine ⟨by omega, fun j hj => ?_⟩
      cases j with
      | zero =>
        refine ⟨0, Nat.zero_le _, fun y₁ y₂ hy₁ hy₂ => ⟨⟨fun _ _ h => by omega, fun i hi _ => ?_⟩, ⟨fun _ _ h => by omega, fun i hi _ => ?_⟩⟩⟩
        · cases i with
          | zero => exact hy₁.2 0 (by simp) le_rfl
          | succ i =>
            have hi' : i < (t₁.filter b₁).length := by simpa using hi
            have hmem : (t₁.filter b₁)[i]'hi' ∈ a₁ :: t₁ :=
              List.mem_cons_of_mem a₁ (List.mem_of_mem_filter (List.getElem_mem hi'))
            obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem
            change y₁ < (t₁.filter b₁)[i]'hi'
            rw [← hkeq]
            exact hy₁.2 k hk (Nat.zero_le k)
        · cases i with
          | zero => exact hy₂.2 0 (by simp) le_rfl
          | succ i =>
            have hi' : i < (t₂.filter b₂).length := by simpa using hi
            have hmem : (t₂.filter b₂)[i]'hi' ∈ a₂ :: t₂ :=
              List.mem_cons_of_mem a₂ (List.mem_of_mem_filter (List.getElem_mem hi'))
            obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem
            change y₂ < (t₂.filter b₂)[i]'hi'
            rw [← hkeq]
            exact hy₂.2 k hk (Nat.zero_le k)
      | succ j =>
        obtain ⟨j', hj', hcell'⟩ := hcell_t j (Nat.succ_le_succ_iff.mp hj)
        refine ⟨j' + 1, Nat.succ_le_succ hj', fun y₁ y₂ hy₁ hy₂ => ?_⟩
        have hy₁_t : inCell t₁ j' y₁ :=
          ⟨fun i hi hij => hy₁.1 (i + 1) (by simpa using hi) (Nat.succ_lt_succ hij),
           fun i hi hij => hy₁.2 (i + 1) (by simpa using hi) (Nat.succ_le_succ hij)⟩
        have hy₂_t : inCell t₂ j' y₂ :=
          ⟨fun i hi hij => hy₂.1 (i + 1) (by simpa using hi) (Nat.succ_lt_succ hij),
           fun i hi hij => hy₂.2 (i + 1) (by simpa using hi) (Nat.succ_le_succ hij)⟩
        obtain ⟨hc1, hc2⟩ := hcell' y₁ y₂ hy₁_t hy₂_t
        refine ⟨⟨fun i hi hij => ?_, fun i hi hij => ?_⟩, ⟨fun i hi hij => ?_, fun i hi hij => ?_⟩⟩
        · cases i with
          | zero => exact hy₁.1 0 (by simp) (Nat.zero_lt_succ j')
          | succ i => exact hc1.1 i (by simpa using hi) (Nat.succ_lt_succ_iff.mp hij)
        · cases i with
          | zero => omega
          | succ i => exact hc1.2 i (by simpa using hi) (Nat.succ_le_succ_iff.mp hij)
        · cases i with
          | zero => exact hy₂.1 0 (by simp) (Nat.zero_lt_succ j')
          | succ i => exact hc2.1 i (by simpa using hi) (Nat.succ_lt_succ_iff.mp hij)
        · cases i with
          | zero => omega
          | succ i => exact hc2.2 i (by simpa using hi) (Nat.succ_le_succ_iff.mp hij)
    · have ha1f : b₁ a₁ = false := Bool.eq_false_iff.mpr ha
      have ha2f : b₂ a₂ = false := hF.1.symm.trans ha1f
      simp only [List.filter_cons, ha1f, ha2f, Bool.false_eq_true, ↓reduceIte]
      refine ⟨hlen_t, fun j hj => ?_⟩
      obtain ⟨j', hj', hcell'⟩ := hcell_t j hj
      refine ⟨j' + 1, Nat.succ_le_succ hj', fun y₁ y₂ hy₁ hy₂ => ?_⟩
      have hy₁_t : inCell t₁ j' y₁ :=
        ⟨fun i hi hij => hy₁.1 (i + 1) (by simpa using hi) (Nat.succ_lt_succ hij),
         fun i hi hij => hy₁.2 (i + 1) (by simpa using hi) (Nat.succ_le_succ hij)⟩
      have hy₂_t : inCell t₂ j' y₂ :=
        ⟨fun i hi hij => hy₂.1 (i + 1) (by simpa using hi) (Nat.succ_lt_succ hij),
         fun i hi hij => hy₂.2 (i + 1) (by simpa using hi) (Nat.succ_le_succ hij)⟩
      exact hcell' y₁ y₂ hy₁_t hy₂_t

lemma forall₂_filter_getElem {K₁ K₂ : Type}
    (b₁ : K₁ → Bool) (b₂ : K₂ → Bool) (rel : K₁ → K₂ → Prop) :
    ∀ {l₁ : List K₁} {l₂ : List K₂},
      List.Forall₂ (fun x y => b₁ x = b₂ y ∧ rel x y) l₁ l₂ →
      List.Forall₂ rel (l₁.filter b₁) (l₂.filter b₂)
  | [], [], _ => List.Forall₂.nil
  | a₁ :: t₁, a₂ :: t₂, hF => by
    rw [List.forall₂_cons] at hF
    have ih := forall₂_filter_getElem b₁ b₂ rel hF.2
    by_cases ha : b₁ a₁ = true
    · have ha2 : b₂ a₂ = true := hF.1.1.symm.trans ha
      simp only [List.filter_cons, ha, ha2, ↓reduceIte]
      exact List.Forall₂.cons hF.1.2 ih
    · have ha1f : b₁ a₁ = false := Bool.eq_false_iff.mpr ha
      have ha2f : b₂ a₂ = false := hF.1.1.symm.trans ha1f
      simp only [List.filter_cons, ha1f, ha2f, Bool.false_eq_true, ↓reduceIte]
      exact ih

lemma forall₂_getElem {α β : Type} {rel : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ rel l₁ l₂) (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length) :
    rel l₁[i] l₂[i] :=
  (List.forall₂_iff_get.mp h).2 i h₁ h₂

lemma forall₂_of_getElem {α β : Type} {rel : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (hlen : l₁.length = l₂.length)
    (h : ∀ (i : ℕ) (h₁ : i < l₁.length) (h₂ : i < l₂.length), rel l₁[i] l₂[i]) :
    List.Forall₂ rel l₁ l₂ :=
  List.forall₂_iff_get.mpr ⟨hlen, h⟩

lemma forall₂_append_of {α β : Type} {rel : α → β → Prop} :
    ∀ {l₁ l₁' : List α} {l₂ l₂' : List β},
      List.Forall₂ rel l₁ l₂ → List.Forall₂ rel l₁' l₂' → List.Forall₂ rel (l₁ ++ l₁') (l₂ ++ l₂')
  | [], _, [], _, _, h2 => h2
  | _ :: _, _, _ :: _, _, List.Forall₂.cons h1 t1, h2 => List.Forall₂.cons h1 (forall₂_append_of t1 h2)

lemma countP_eq_of_forall₂ {α β : Type} (p₁ : α → Bool) (p₂ : β → Bool) :
    ∀ {l₁ : List α} {l₂ : List β},
      List.Forall₂ (fun x y => p₁ x = p₂ y) l₁ l₂ →
      l₁.countP p₁ = l₂.countP p₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons hhead htail => by
    rw [List.countP_cons, List.countP_cons, hhead, countP_eq_of_forall₂ p₁ p₂ htail]

lemma filterSignTable_extra {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (hIVT₁ : ∀ (p : Polynomial K₁) {a b : K₁}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₁, a < c ∧ c < b ∧ p.eval c = 0)
    (hIVT₂ : ∀ (p : Polynomial K₂) {a b : K₂}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₂, a < c ∧ c < b ∧ p.eval c = 0)
    {φ₁ : A →+* K₁} {φ₂ : A →+* K₂} {P P' : List (Polynomial A)}
    (hsub : ∀ p ∈ P, p ∈ P') (hST : SignTableMatch φ₁ φ₂ P') :
    SignTableMatch φ₁ φ₂ P ∧
    (∀ (i : ℕ) (h₁ : i < (rootList (P.map (Polynomial.map φ₁))).length)
        (h₂ : i < (rootList (P.map (Polynomial.map φ₂))).length), ∀ q ∈ P',
      sameSign ((q.map φ₁).eval (rootList (P.map (Polynomial.map φ₁)))[i])
               ((q.map φ₂).eval (rootList (P.map (Polynomial.map φ₂)))[i])) := by
  classical
  set R₁' := rootList (P'.map (Polynomial.map φ₁))
  set R₂' := rootList (P'.map (Polynomial.map φ₂))
  set R₁ := rootList (P.map (Polynomial.map φ₁))
  set R₂ := rootList (P.map (Polynomial.map φ₂))
  have hR₁' : R₁'.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₂' : R₂'.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₁ : R₁.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₂ : R₂.Pairwise (· < ·) := rootList_pairwise_lt _
  let b₁ : K₁ → Bool := fun r => P.any (fun p => decide (p.map φ₁ ≠ 0 ∧ (p.map φ₁).eval r = 0))
  let b₂ : K₂ → Bool := fun r => P.any (fun p => decide (p.map φ₂ ≠ 0 ∧ (p.map φ₂).eval r = 0))
  have hR₁_eq : R₁ = R₁'.filter b₁ := by
    refine list_eq_of_pairwise_lt_of_mem_iff hR₁ (hR₁'.filter b₁) (fun x => ?_)
    dsimp only [R₁, R₁']
    rw [mem_rootList, List.mem_filter, mem_rootList]
    simp only [b₁, List.any_eq_true, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨p, hpP, rfl⟩, hp0, hpx⟩
      exact ⟨⟨p.map φ₁, ⟨p, hsub p hpP, rfl⟩, hp0, hpx⟩, ⟨p, hpP, hp0, hpx⟩⟩
    · rintro ⟨_, ⟨p, hpP, hp0, hpx⟩⟩
      exact ⟨p.map φ₁, ⟨p, hpP, rfl⟩, hp0, hpx⟩
  have hR₂_eq : R₂ = R₂'.filter b₂ := by
    refine list_eq_of_pairwise_lt_of_mem_iff hR₂ (hR₂'.filter b₂) (fun x => ?_)
    dsimp only [R₂, R₂']
    rw [mem_rootList, List.mem_filter, mem_rootList]
    simp only [b₂, List.any_eq_true, decide_eq_true_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨p, hpP, rfl⟩, hp0, hpx⟩
      exact ⟨⟨p.map φ₂, ⟨p, hsub p hpP, rfl⟩, hp0, hpx⟩, ⟨p, hpP, hp0, hpx⟩⟩
    · rintro ⟨_, ⟨p, hpP, hp0, hpx⟩⟩
      exact ⟨p.map φ₂, ⟨p, hpP, rfl⟩, hp0, hpx⟩
  have hF_base : List.Forall₂ (fun r₁ r₂ => b₁ r₁ = b₂ r₂ ∧ ∀ p ∈ P', sameSign ((p.map φ₁).eval r₁) ((p.map φ₂).eval r₂)) R₁' R₂' := by
    refine forall₂_of_getElem hST.1 (fun i hi₁ hi₂ => ⟨?_, fun p hp => hST.2.1 i hi₁ hi₂ p hp⟩)
    rw [Bool.eq_iff_iff]
    simp only [b₁, b₂, List.any_eq_true, decide_eq_true_eq]
    constructor <;> rintro ⟨p, hpP, hp0, hpx⟩ <;> refine ⟨p, hpP, ?_, ?_⟩
    · exact (poly_map_eq_zero_iff_of_signTableMatch hST (hsub p hpP)).not.mp hp0
    · exact (hST.2.1 i hi₁ hi₂ p (hsub p hpP)).2.mp hpx
    · exact (poly_map_eq_zero_iff_of_signTableMatch hST (hsub p hpP)).not.mpr hp0
    · exact (hST.2.1 i hi₁ hi₂ p (hsub p hpP)).2.mpr hpx
  have hF_bool : List.Forall₂ (fun r₁ r₂ => b₁ r₁ = b₂ r₂) R₁' R₂' :=
    List.Forall₂.imp (fun _ _ h => h.1) hF_base
  have hF_filt := forall₂_filter_getElem b₁ b₂ (fun r₁ r₂ => ∀ p ∈ P', sameSign ((p.map φ₁).eval r₁) ((p.map φ₂).eval r₂)) hF_base
  rw [← hR₁_eq, ← hR₂_eq] at hF_filt
  obtain ⟨hlen_f, hcell_f⟩ := forall₂_filter_and_cell b₁ b₂ hF_bool
  rw [← hR₁_eq, ← hR₂_eq] at hlen_f hcell_f
  refine ⟨⟨hlen_f, fun i hi₁ hi₂ p hp => forall₂_getElem hF_filt i hi₁ hi₂ p (hsub p hp), ?_⟩,
    fun i hi₁ hi₂ q hq => forall₂_getElem hF_filt i hi₁ hi₂ q hq⟩
  intro j x₁ x₂ hj hx₁ hx₂ p hp
  obtain ⟨j', hj', hcells⟩ := hcell_f j hj
  obtain ⟨y₁, hy₁⟩ := exists_point_inCell hR₁' hj'
  obtain ⟨y₂, hy₂⟩ := exists_point_inCell hR₂' (hST.1 ▸ hj')
  obtain ⟨hy₁_f, hy₂_f⟩ := hcells y₁ y₂ hy₁ hy₂
  have h1 : sameSign ((p.map φ₁).eval x₁) ((p.map φ₁).eval y₁) :=
    inCell_const_sign hIVT₁ hx₁ hy₁_f (List.mem_map_of_mem hp)
  have h2 : sameSign ((p.map φ₁).eval y₁) ((p.map φ₂).eval y₂) :=
    hST.2.2 j' y₁ y₂ hj' hy₁ hy₂ p (hsub p hp)
  have h3 : sameSign ((p.map φ₂).eval y₂) ((p.map φ₂).eval x₂) :=
    inCell_const_sign hIVT₂ hy₂_f hx₂ (List.mem_map_of_mem hp)
  exact sameSign_trans h1 (sameSign_trans h2 h3)

end SignTableAndFilter

section StripAndPrem
open Classical

noncomputable def stripLeadAux {A K₁ : Type} [CommRing A] [Field K₁]
    (φ₁ : A →+* K₁) : ℕ → Polynomial A → Polynomial A × List A
  | 0, p => if φ₁ (p.coeff 0) = 0 then (0, [p.coeff 0]) else (p, [p.coeff 0])
  | n + 1, p =>
    if φ₁ (p.coeff (n + 1)) = 0 then
      let res := stripLeadAux φ₁ n (p.erase (n + 1))
      (res.1, p.coeff (n + 1) :: res.2)
    else (p, [p.coeff (n + 1)])

lemma stripLeadAux_spec {A K₁ K₂ : Type} [CommRing A] [Field K₁] [Field K₂]
    (φ₁ : A →+* K₁) :
    ∀ (n : ℕ) (p : Polynomial A), p.natDegree ≤ n →
      let (p', Q) := stripLeadAux φ₁ n p
      p'.natDegree ≤ p.natDegree ∧
      p'.map φ₁ = p.map φ₁ ∧
      (p' = 0 ∨ (φ₁ p'.leadingCoeff ≠ 0 ∧ p'.leadingCoeff ∈ Q)) ∧
      (∀ (φ₂ : A →+* K₂), (∀ r ∈ Q, φ₁ r = 0 ↔ φ₂ r = 0) → p'.map φ₂ = p.map φ₂)
  | 0, p, hdeg => by
    have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
    dsimp [stripLeadAux]
    by_cases h0 : φ₁ (p.coeff 0) = 0
    · rw [if_pos h0]
      refine ⟨Nat.zero_le _, ?_, Or.inl rfl, fun φ₂ hQ => ?_⟩
      · conv_rhs => rw [hpC]
        simp [h0]
      · conv_rhs => rw [hpC]
        have h2 : φ₂ (p.coeff 0) = 0 := (hQ (p.coeff 0) (by simp)).mp h0
        simp [h2]
    · rw [if_neg h0]
      have hlead : p.leadingCoeff = p.coeff 0 := by
        rw [Polynomial.leadingCoeff, Nat.le_zero.mp hdeg]
      refine ⟨le_rfl, rfl, Or.inr ⟨hlead ▸ h0, by simp [hlead]⟩, fun _ _ => rfl⟩
  | n + 1, p, hdeg => by
    dsimp [stripLeadAux]
    by_cases h0 : φ₁ (p.coeff (n + 1)) = 0
    · rw [if_pos h0]
      have herase_deg : (p.erase (n + 1)).natDegree ≤ n := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        by_cases hmeq : m = n + 1
        · subst hmeq; simp
        · rw [Polynomial.coeff_erase, if_neg hmeq]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))
      have herase_le : (p.erase (n + 1)).natDegree ≤ p.natDegree := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        by_cases hmeq : m = n + 1
        · subst hmeq; simp
        · rw [Polynomial.coeff_erase, if_neg hmeq]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt hm
      have hdecomp : p = p.erase (n + 1) + Polynomial.monomial (n + 1) (p.coeff (n + 1)) := by
        ext m
        rw [Polynomial.coeff_add, Polynomial.coeff_monomial]
        by_cases hm : m = n + 1
        · subst hm; simp
        · simp [hm, Ne.symm hm]
      have ih := stripLeadAux_spec (K₂ := K₂) φ₁ n (p.erase (n + 1)) herase_deg
      refine ⟨le_trans ih.1 herase_le, ?_, ?_, fun φ₂ hQ => ?_⟩
      · rw [ih.2.1]
        conv_rhs => rw [hdecomp]
        simp [Polynomial.map_add, Polynomial.map_monomial, h0]
      · rcases ih.2.2.1 with hzero | ⟨hl, hm⟩
        · exact Or.inl hzero
        · exact Or.inr ⟨hl, List.mem_cons_of_mem _ hm⟩
      · rw [ih.2.2.2 φ₂ (fun r hr => hQ r (List.mem_cons_of_mem _ hr))]
        have h2 : φ₂ (p.coeff (n + 1)) = 0 := (hQ (p.coeff (n + 1)) (by simp)).mp h0
        conv_rhs => rw [hdecomp]
        simp [Polynomial.map_add, Polynomial.map_monomial, h2]
    · rw [if_neg h0]
      have hp_deg : p.natDegree = n + 1 :=
        le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero (fun hc => h0 (by simp [hc])))
      have hlead : p.leadingCoeff = p.coeff (n + 1) := by
        rw [Polynomial.leadingCoeff, hp_deg]
      refine ⟨le_rfl, rfl, Or.inr ⟨hlead ▸ h0, by simp [hlead]⟩, fun _ _ => rfl⟩

noncomputable def stripLead {A K₁ : Type} [CommRing A] [Field K₁]
    (φ₁ : A →+* K₁) (p : Polynomial A) : Polynomial A × List A :=
  stripLeadAux φ₁ p.natDegree p

noncomputable def stripList {A K₁ : Type} [CommRing A] [Field K₁]
    (φ₁ : A →+* K₁) : List (Polynomial A) → List (Polynomial A) × List A
  | [] => ([], [])
  | p :: ps =>
    let r1 := stripLead φ₁ p
    let r2 := stripList φ₁ ps
    if r1.1 = 0 then (r2.1, r1.2 ++ r2.2)
    else (r1.1 :: r2.1, r1.2 ++ r2.2)

lemma stripList_spec {A K₁ K₂ : Type} [CommRing A] [Field K₁] [Field K₂]
    (φ₁ : A →+* K₁) :
    ∀ (P : List (Polynomial A)),
      let (P', Q) := stripList φ₁ P
      (∀ p' ∈ P', p' ≠ 0 ∧ φ₁ p'.leadingCoeff ≠ 0 ∧ p'.leadingCoeff ∈ Q) ∧
      (∀ d : ℕ, (∀ p ∈ P, p.natDegree ≤ d) → ∀ p' ∈ P', p'.natDegree ≤ d) ∧
      (∀ d : ℕ, (∀ p ∈ P, p.natDegree ≤ d) →
        (P'.countP (fun p => decide (p.natDegree = d))) ≤ P.countP (fun p => decide (p.natDegree = d))) ∧
      (∀ (φ₂ : A →+* K₂), (∀ r ∈ Q, φ₁ r = 0 ↔ φ₂ r = 0) →
        ∀ (p : Polynomial A), p ∈ P →
          (p.map φ₁ = 0 ∧ p.map φ₂ = 0) ∨
          (∃ p' ∈ P', p'.map φ₁ = p.map φ₁ ∧ p'.map φ₂ = p.map φ₂))
  | [] => ⟨fun _ h => by simp at h, fun _ _ _ h => by simp at h, fun _ _ => le_rfl, fun _ _ _ h => by simp at h⟩
  | p :: ps => by
    classical
    dsimp [stripList]
    have h1 := stripLeadAux_spec (K₂ := K₂) φ₁ p.natDegree p le_rfl
    have h2 := stripList_spec (K₂ := K₂) φ₁ ps
    set r1 := stripLead φ₁ p
    set r2 := stripList φ₁ ps
    by_cases hr0 : r1.1 = 0
    · simp only [hr0, ↓reduceIte]
      refine ⟨fun p' hp' => ?_, fun d hd p' hp' => h2.2.1 d (fun q hq => hd q (List.mem_cons_of_mem p hq)) p' hp', fun d hd => ?_, fun φ₂ hQ q hq => ?_⟩
      · have hp'' := h2.1 p' hp'
        exact ⟨hp''.1, hp''.2.1, List.mem_append_right _ hp''.2.2⟩
      · refine le_trans (h2.2.2.1 d (fun q hq => hd q (List.mem_cons_of_mem p hq))) ?_
        rw [List.countP_cons]
        exact Nat.le_add_right _ _
      · rcases List.mem_cons.mp hq with rfl | hqps
        · left
          dsimp only [r1, stripLead] at hr0
          refine ⟨?_, ?_⟩
          · rw [← h1.2.1, hr0, Polynomial.map_zero]
          · rw [← h1.2.2.2 φ₂ (fun r hr => hQ r (List.mem_append_left _ hr)), hr0, Polynomial.map_zero]
        · exact h2.2.2.2 φ₂ (fun r hr => hQ r (List.mem_append_right _ hr)) q hqps
    · simp only [hr0, ↓reduceIte]
      have hlead1 : φ₁ r1.1.leadingCoeff ≠ 0 ∧ r1.1.leadingCoeff ∈ r1.2 :=
        (h1.2.2.1).resolve_left hr0
      refine ⟨fun p' hp' => ?_, fun d hd p' hp' => ?_, fun d hd => ?_, fun φ₂ hQ q hq => ?_⟩
      · rcases List.mem_cons.mp hp' with rfl | hp'ps
        · exact ⟨hr0, hlead1.1, List.mem_append_left _ hlead1.2⟩
        · have hp'' := h2.1 p' hp'ps
          exact ⟨hp''.1, hp''.2.1, List.mem_append_right _ hp''.2.2⟩
      · rcases List.mem_cons.mp hp' with rfl | hp'ps
        · exact le_trans h1.1 (hd p (by simp))
        · exact h2.2.1 d (fun q hq => hd q (List.mem_cons_of_mem p hq)) p' hp'ps
      · rw [List.countP_cons, List.countP_cons]
        have hle_ps := h2.2.2.1 d (fun q hq => hd q (List.mem_cons_of_mem p hq))
        dsimp only [r2] at hle_ps ⊢
        by_cases h1d : r1.1.natDegree = d
        · have hp_le : p.natDegree ≤ d := hd p (by simp)
          have h1_le : r1.1.natDegree ≤ p.natDegree := h1.1
          have hpd : p.natDegree = d := by omega
          simp only [h1d, hpd, decide_true, ↓reduceIte]
          omega
        · simp only [h1d, decide_false, Bool.false_eq_true, ↓reduceIte]
          exact le_trans hle_ps (Nat.le_add_right _ _)
      · rcases List.mem_cons.mp hq with rfl | hqps
        · right
          refine ⟨r1.1, by simp, h1.2.1, h1.2.2.2 φ₂ (fun r hr => hQ r (List.mem_append_left _ hr))⟩
        · rcases h2.2.2.2 φ₂ (fun r hr => hQ r (List.mem_append_right _ hr)) q hqps with hzero | ⟨p', hp', hm1, hm2⟩
          · exact Or.inl hzero
          · exact Or.inr ⟨p', List.mem_cons_of_mem _ hp', hm1, hm2⟩

noncomputable def premAux {A : Type} [CommRing A] (g : Polynomial A) :
    ℕ → Polynomial A → Polynomial A
  | 0, f => f
  | k + 1, f =>
    if f = 0 ∨ f.natDegree < g.natDegree then f
    else
      let b := g.leadingCoeff
      let a := f.leadingCoeff
      let step := Polynomial.C (b ^ 2) * f -
        Polynomial.C (b * a) * Polynomial.X ^ (f.natDegree - g.natDegree) * g
      premAux g k step

noncomputable def prem {A : Type} [CommRing A] (f g : Polynomial A) : Polynomial A :=
  premAux g (f.natDegree + 1) f

lemma premAux_zero {A : Type} [CommRing A] (g : Polynomial A) :
    ∀ k : ℕ, premAux g k 0 = 0
  | 0 => rfl
  | _ + 1 => by simp [premAux]

lemma premAux_deg {A : Type} [CommRing A] {g : Polynomial A} (hg : g ≠ 0) :
    ∀ (k : ℕ) (f : Polynomial A), f.natDegree < k →
      premAux g k f = 0 ∨ (premAux g k f).natDegree < g.natDegree
  | 0, f, hk => by omega
  | k + 1, f, hk => by
    dsimp [premAux]
    split_ifs with hf
    · rcases hf with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr hlt
    · push Not at hf
      obtain ⟨hf0, hge⟩ := hf
      set b := g.leadingCoeff
      set a := f.leadingCoeff
      set d := f.natDegree - g.natDegree
      set step := Polynomial.C (b ^ 2) * f - Polynomial.C (b * a) * Polynomial.X ^ d * g
      have hstep_coeff : ∀ i : ℕ, f.natDegree ≤ i → step.coeff i = 0 := by
        intro i hi
        dsimp [step]
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
        rcases eq_or_lt_of_le hi with rfl | hgt
        · have hsub : f.natDegree - d = g.natDegree := by omega
          rw [if_pos (Nat.sub_le _ _), hsub]
          change b ^ 2 * a - b * a * b = 0
          ring
        · have hf_i : f.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
          have hgt_g : g.natDegree < i - d := by omega
          have hg_i : g.coeff (i - d) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt_g
          rw [hf_i, mul_zero, zero_sub]
          split_ifs <;> simp [hg_i]
      by_cases hs0 : step = 0
      · rw [hs0, premAux_zero]
        exact Or.inl rfl
      · have hs_lt : step.natDegree < f.natDegree := by
          by_contra hnot
          have hle : f.natDegree ≤ step.natDegree := not_lt.mp hnot
          exact Polynomial.leadingCoeff_ne_zero.mpr hs0 (hstep_coeff step.natDegree hle)
        exact premAux_deg hg k step (lt_of_lt_of_le hs_lt (Nat.lt_succ_iff.mp hk))

lemma prem_deg {A : Type} [CommRing A] {f g : Polynomial A} (hg : g ≠ 0) :
    prem f g = 0 ∨ (prem f g).natDegree < g.natDegree :=
  premAux_deg hg (f.natDegree + 1) f (Nat.lt_succ_self _)

lemma premAux_sameSign {A K : Type} [CommRing A]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (φ : A →+* K) (g : Polynomial A) (hgb : φ g.leadingCoeff ≠ 0) :
    ∀ (k : ℕ) (f : Polynomial A) (x : K), (g.map φ).eval x = 0 →
      sameSign (((premAux g k f).map φ).eval x) ((f.map φ).eval x)
  | 0, f, x, _ => sameSign_refl _
  | k + 1, f, x, hxg => by
    dsimp [premAux]
    split_ifs with hf
    · exact sameSign_refl _
    · set b := g.leadingCoeff
      set a := f.leadingCoeff
      set d := f.natDegree - g.natDegree
      set step := Polynomial.C (b ^ 2) * f - Polynomial.C (b * a) * Polynomial.X ^ d * g
      have ih := premAux_sameSign φ g hgb k step x hxg
      have heval : (step.map φ).eval x = (φ b) ^ 2 * (f.map φ).eval x := by
        dsimp [step]
        simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
          Polynomial.map_X, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, hxg, mul_zero, sub_zero, map_pow]
      have hss_step : sameSign ((step.map φ).eval x) ((f.map φ).eval x) := by
        rw [heval]
        have hb2 : 0 < (φ b) ^ 2 := sq_pos_of_ne_zero hgb
        exact ⟨⟨fun h => neg_of_mul_neg_right h hb2.le, fun h => mul_neg_of_pos_of_neg hb2 h⟩,
               ⟨fun h => (mul_eq_zero.mp h).resolve_left hb2.ne', fun h => by rw [h, mul_zero]⟩⟩
      exact sameSign_trans ih hss_step

lemma prem_sameSign {A K : Type} [CommRing A]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (φ : A →+* K) {f g : Polynomial A} (hgb : φ g.leadingCoeff ≠ 0)
    {x : K} (hxg : (g.map φ).eval x = 0) :
    sameSign (((prem f g).map φ).eval x) ((f.map φ).eval x) :=
  premAux_sameSign φ g hgb (f.natDegree + 1) f x hxg

end StripAndPrem

section CellRootAnalysis

noncomputable def cellLeftVal {K : Type} [CommRing K] (p : Polynomial K) (R : List K) (j : ℕ) : K :=
  if hj : 0 < j ∧ j - 1 < R.length then p.eval R[j - 1]
  else (-1 : K) ^ p.natDegree * p.leadingCoeff

noncomputable def cellRightVal {K : Type} [CommRing K] (p : Polynomial K) (R : List K) (j : ℕ) : K :=
  if hj : j < R.length then p.eval R[j]
  else p.leadingCoeff

lemma cell_root_analysis {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hIVT : ∀ (p : Polynomial K) {a b : K}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K, a < c ∧ c < b ∧ p.eval c = 0)
    (hMVT : ∀ (p : Polynomial K) {u v : K}, u < v →
      ∃ c : K, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hAsymp : ∀ (p : Polynomial K), p ≠ 0 →
      ∃ M : K, ∀ x : K, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (p : Polynomial K) (hp : p ≠ 0) (R : List K) (hR : R.Pairwise (· < ·))
    (j : ℕ) (hj : j ≤ R.length)
    (hderiv : ∀ x : K, inCell R j x → p.derivative.eval x ≠ 0) :
    ¬ (cellLeftVal p R j = 0 ∧ cellRightVal p R j = 0) ∧
    ((∃ r : K, inCell R j r ∧ p.eval r = 0) ↔ cellLeftVal p R j * cellRightVal p R j < 0) ∧
    (∀ r₁ r₂ : K, inCell R j r₁ → inCell R j r₂ → p.eval r₁ = 0 → p.eval r₂ = 0 → r₁ = r₂) ∧
    ((¬ ∃ r : K, inCell R j r ∧ p.eval r = 0) → ∀ x : K, inCell R j x →
      (cellLeftVal p R j ≠ 0 → sameSign (p.eval x) (cellLeftVal p R j)) ∧
      (cellRightVal p R j ≠ 0 → sameSign (p.eval x) (cellRightVal p R j))) ∧
    (∀ r : K, inCell R j r → p.eval r = 0 → ∀ x : K, inCell R j x →
      (x < r → cellLeftVal p R j ≠ 0 ∧ sameSign (p.eval x) (cellLeftVal p R j)) ∧
      (r < x → cellRightVal p R j ≠ 0 ∧ sameSign (p.eval x) (cellRightVal p R j))) := by
  classical
  obtain ⟨M₁, hM₁⟩ := poly_asymp_neg hAsymp p hp
  obtain ⟨M₂, hM₂⟩ := poly_asymp_pos hAsymp p hp
  let a : K := if h : 0 < j ∧ j - 1 < R.length then R[j - 1]
    else if hRpos : 0 < R.length then min (M₁ - 1) (R[0] - 1) else M₁ - 1
  let b : K := if h : j < R.length then R[j]
    else if hRpos : 0 < R.length then max (M₂ + 1) (R[R.length - 1] + 1) else max (M₂ + 1) (a + 1)
  have ha_sign : sameSign (p.eval a) (cellLeftVal p R j) := by
    dsimp [a, cellLeftVal]
    split_ifs with h1 h2
    · exact sameSign_refl _
    · exact hM₁ _ (by have := min_le_left (M₁ - 1) (R[0] - 1); linarith)
    · exact hM₁ _ (by linarith)
  have hb_sign : sameSign (p.eval b) (cellRightVal p R j) := by
    dsimp [b, cellRightVal]
    split_ifs with h1 h2
    · exact sameSign_refl _
    · exact hM₂ _ (by have := le_max_left (M₂ + 1) (R[R.length - 1] + 1); linarith)
    · exact hM₂ _ (by have := le_max_left (M₂ + 1) (a + 1); linarith)
  have hab : a < b := by
    by_cases h1 : 0 < j ∧ j - 1 < R.length <;> by_cases h2 : j < R.length <;> by_cases hRpos : 0 < R.length
    · have ha_eq : a = R[j - 1] := dif_pos h1
      have hb_eq : b = R[j] := dif_pos h2
      rw [ha_eq, hb_eq]
      exact List.pairwise_iff_getElem.mp hR (j - 1) j h1.2 h2 (by omega)
    · omega
    · have ha_eq : a = R[j - 1] := dif_pos h1
      have hb_eq : b = max (M₂ + 1) (R[R.length - 1] + 1) := by simp only [b, dif_neg h2, dif_pos hRpos]
      rw [ha_eq, hb_eq]
      have hle : R[j - 1] ≤ R[R.length - 1] := getElem_le_of_pairwise_lt hR h1.2 (Nat.sub_lt hRpos zero_lt_one) (by omega)
      have hmax : R[R.length - 1] + 1 ≤ max (M₂ + 1) (R[R.length - 1] + 1) := le_max_right _ _
      linarith
    · omega
    · have ha_eq : a = min (M₁ - 1) (R[0] - 1) := by simp only [a, dif_neg h1, dif_pos hRpos]
      have hb_eq : b = R[j] := dif_pos h2
      rw [ha_eq, hb_eq]
      have hmin : min (M₁ - 1) (R[0] - 1) ≤ R[0] - 1 := min_le_right _ _
      have hle : R[0] ≤ R[j] := getElem_le_of_pairwise_lt hR hRpos h2 (Nat.zero_le j)
      linarith
    · omega
    · have ha_eq : a = min (M₁ - 1) (R[0] - 1) := by simp only [a, dif_neg h1, dif_pos hRpos]
      have hb_eq : b = max (M₂ + 1) (R[R.length - 1] + 1) := by simp only [b, dif_neg h2, dif_pos hRpos]
      rw [ha_eq, hb_eq]
      have hmin : min (M₁ - 1) (R[0] - 1) ≤ R[0] - 1 := min_le_right _ _
      have hle : R[0] ≤ R[R.length - 1] := getElem_le_of_pairwise_lt hR hRpos (Nat.sub_lt hRpos zero_lt_one) (Nat.zero_le _)
      have hmax : R[R.length - 1] + 1 ≤ max (M₂ + 1) (R[R.length - 1] + 1) := le_max_right _ _
      linarith
    · have ha_eq : a = M₁ - 1 := by simp only [a, dif_neg h1, dif_neg hRpos]
      have hb_eq : b = max (M₂ + 1) (a + 1) := by simp only [b, dif_neg h2, dif_neg hRpos]
      rw [hb_eq]
      have hmax : a + 1 ≤ max (M₂ + 1) (a + 1) := le_max_right _ _
      linarith
  have hIoo_inCell : ∀ c : K, a < c → c < b → inCell R j c := by
    intro c hca hcb
    refine ⟨fun i hi hij => ?_, fun i hi hji => ?_⟩
    · have hj_pos : 0 < j := by omega
      have hjm : j - 1 < R.length := by omega
      have ha_eq : a = R[j - 1] := by simp [a, hj_pos, hjm]
      have hle : R[i] ≤ R[j - 1] := getElem_le_of_pairwise_lt hR hi hjm (by omega)
      linarith
    · have hj_lt : j < R.length := lt_of_le_of_lt hji hi
      have hb_eq : b = R[j] := by simp [b, hj_lt]
      have hle : R[j] ≤ R[i] := getElem_le_of_pairwise_lt hR hj_lt hi hji
      linarith
  have hderiv_ab : ∀ c : K, a < c → c < b → p.derivative.eval c ≠ 0 :=
    fun c hca hcb => hderiv c (hIoo_inCell c hca hcb)
  have hleft_far : ∀ x : K, inCell R j x → x ≤ a → j = 0 ∧ sameSign (p.eval x) (cellLeftVal p R j) := by
    intro x hx hxa
    have hj0 : j = 0 := by
      by_contra hjp
      have hpos : 0 < j := Nat.pos_of_ne_zero hjp
      have hjm : j - 1 < R.length := by omega
      have ha_eq : a = R[j - 1] := by simp [a, hpos, hjm]
      have hlt : R[j - 1] < x := hx.1 (j - 1) hjm (by omega)
      linarith
    refine ⟨hj0, ?_⟩
    have ha_le_M : a < M₁ := by
      dsimp [a]
      split_ifs with h1 h2
      · omega
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · linarith
    have hss := hM₁ x (lt_of_le_of_lt hxa ha_le_M)
    have hlv : cellLeftVal p R j = (-1 : K) ^ p.natDegree * p.leadingCoeff := by
      simp [cellLeftVal, hj0]
    rwa [hlv]
  have hright_far : ∀ x : K, inCell R j x → b ≤ x → j = R.length ∧ sameSign (p.eval x) (cellRightVal p R j) := by
    intro x hx hbx
    have hjm : j = R.length := by
      by_contra hne
      have hj_lt : j < R.length := lt_of_le_of_ne hj hne
      have hb_eq : b = R[j] := by simp [b, hj_lt]
      have hlt : x < R[j] := hx.2 j hj_lt le_rfl
      linarith
    refine ⟨hjm, ?_⟩
    have hM_le_b : M₂ < b := by
      dsimp [b]
      split_ifs with h1 h2
      · omega
      · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
      · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hss := hM₂ x (lt_of_lt_of_le hM_le_b hbx)
    have hrv : cellRightVal p R j = p.leadingCoeff := by
      simp [cellRightVal, hjm]
    rwa [hrv]
  have hroot_in_ab : ∀ r : K, inCell R j r → p.eval r = 0 → a < r ∧ r < b := by
    intro r hr hr0
    refine ⟨?_, ?_⟩
    · by_contra hle
      obtain ⟨hj0, hss⟩ := hleft_far r hr (not_lt.mp hle)
      have hne : (-1 : K) ^ p.natDegree * p.leadingCoeff ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (Polynomial.leadingCoeff_ne_zero.mpr hp)
      have hlv_ne : cellLeftVal p R j ≠ 0 := by simpa [cellLeftVal, hj0] using hne
      exact hlv_ne (hss.2.mp hr0)
    · by_contra hle
      obtain ⟨hjm, hss⟩ := hright_far r hr (not_lt.mp hle)
      have hne : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
      have hrv_ne : cellRightVal p R j ≠ 0 := by simpa [cellRightVal, hjm] using hne
      exact hrv_ne (hss.2.mp hr0)
  have hnot_both_zero : ¬ (cellLeftVal p R j = 0 ∧ cellRightVal p R j = 0) := by
    rintro ⟨hl0, hr0⟩
    have ha0 : p.eval a = 0 := ha_sign.2.mpr hl0
    have hb0 : p.eval b = 0 := hb_sign.2.mpr hr0
    obtain ⟨c, hac, hcb, hmeq⟩ := hMVT p hab
    rw [ha0, hb0, sub_zero] at hmeq
    rcases mul_eq_zero.mp hmeq.symm with h | h
    · exact (sub_pos.mpr hab).ne' h
    · exact hderiv_ab c hac hcb h
  have hiff_root : (∃ r : K, inCell R j r ∧ p.eval r = 0) ↔ cellLeftVal p R j * cellRightVal p R j < 0 := by
    have hiff1 : (∃ r : K, inCell R j r ∧ p.eval r = 0) ↔ (∃ r : K, a < r ∧ r < b ∧ p.eval r = 0) := by
      constructor
      · rintro ⟨r, hr, hr0⟩
        obtain ⟨har, hrb⟩ := hroot_in_ab r hr hr0
        exact ⟨r, har, hrb, hr0⟩
      · rintro ⟨r, har, hrb, hr0⟩
        exact ⟨r, hIoo_inCell r har hrb, hr0⟩
    have hiff2 := poly_root_iff_opp_sign_on_bounded hIVT hMVT p hab hderiv_ab
    have hprod_ss : sameSign (p.eval a * p.eval b) (cellLeftVal p R j * cellRightVal p R j) :=
      sameSign_mul ha_sign hb_sign
    exact hiff1.trans (hiff2.trans hprod_ss.1)
  have huniq : ∀ r₁ r₂ : K, inCell R j r₁ → inCell R j r₂ → p.eval r₁ = 0 → p.eval r₂ = 0 → r₁ = r₂ := by
    intro r₁ r₂ hr₁ hr₂ hr₁0 hr₂0
    refine poly_unique_root_no_deriv hMVT p hr₁0 hr₂0 (fun c hc1 hc2 => ?_)
    have hc_in : inCell R j c := by
      refine ⟨fun i hi hij => ?_, fun i hi hji => ?_⟩
      · exact lt_trans (lt_min (hr₁.1 i hi hij) (hr₂.1 i hi hij)) hc1
      · exact lt_trans hc2 (max_lt (hr₁.2 i hi hji) (hr₂.2 i hi hji))
    exact hderiv c hc_in
  have hcell_between : ∀ x y : K, inCell R j x → inCell R j y → ∀ c : K, min x y ≤ c → c ≤ max x y → inCell R j c := by
    intro x y hx hy c hc1 hc2
    refine ⟨fun i hi hij => ?_, fun i hi hji => ?_⟩
    · exact lt_of_lt_of_le (lt_min (hx.1 i hi hij) (hy.1 i hi hij)) hc1
    · exact lt_of_le_of_lt hc2 (max_lt (hx.2 i hi hji) (hy.2 i hi hji))
  have hno_root_sign : (¬ ∃ r : K, inCell R j r ∧ p.eval r = 0) → ∀ x : K, inCell R j x →
      (cellLeftVal p R j ≠ 0 → sameSign (p.eval x) (cellLeftVal p R j)) ∧
      (cellRightVal p R j ≠ 0 → sameSign (p.eval x) (cellRightVal p R j)) := by
    intro hno x hx
    set m := (a + b) / 2
    have ham : a < m := by dsimp [m]; linarith
    have hmb : m < b := by dsimp [m]; linarith
    have hm_in : inCell R j m := hIoo_inCell m ham hmb
    have hxm : sameSign (p.eval x) (p.eval m) :=
      poly_const_sign_open hIVT p (fun c hc1 hc2 hc0 =>
        hno ⟨c, hcell_between x m hx hm_in c hc1 hc2, hc0⟩)
    have hno_ab : ∀ c : K, a < c → c < b → p.eval c ≠ 0 :=
      fun c hca hcb hc0 => hno ⟨c, hIoo_inCell c hca hcb, hc0⟩
    refine ⟨fun hl => ?_, fun hr => ?_⟩
    · have ha_ne : p.eval a ≠ 0 := fun ha0 => hl (ha_sign.2.mp ha0)
      have hma := poly_no_root_bounded_left_sign hIVT p ham hmb hno_ab ha_ne
      exact sameSign_trans hxm (sameSign_trans hma ha_sign)
    · have hb_ne : p.eval b ≠ 0 := fun hb0 => hr (hb_sign.2.mp hb0)
      have hmb' := poly_no_root_bounded_right_sign hIVT p ham hmb hno_ab hb_ne
      exact sameSign_trans hxm (sameSign_trans hmb' hb_sign)
  have hwith_root_sign : ∀ r : K, inCell R j r → p.eval r = 0 → ∀ x : K, inCell R j x →
      (x < r → cellLeftVal p R j ≠ 0 ∧ sameSign (p.eval x) (cellLeftVal p R j)) ∧
      (r < x → cellRightVal p R j ≠ 0 ∧ sameSign (p.eval x) (cellRightVal p R j)) := by
    intro r hr hr0 x hx
    obtain ⟨har, hrb⟩ := hroot_in_ab r hr hr0
    have hl_ne : cellLeftVal p R j ≠ 0 := by
      intro hl0
      have ha0 : p.eval a = 0 := ha_sign.2.mpr hl0
      obtain ⟨c, hac, hcr, hmeq⟩ := hMVT p har
      rw [ha0, hr0, sub_zero] at hmeq
      rcases mul_eq_zero.mp hmeq.symm with h | h
      · exact (sub_pos.mpr har).ne' h
      · exact hderiv_ab c hac (lt_trans hcr hrb) h
    have hr_ne : cellRightVal p R j ≠ 0 := by
      intro hr0'
      have hb0 : p.eval b = 0 := hb_sign.2.mpr hr0'
      obtain ⟨c, hrc, hcb, hmeq⟩ := hMVT p hrb
      rw [hr0, hb0, sub_zero] at hmeq
      rcases mul_eq_zero.mp hmeq.symm with h | h
      · exact (sub_pos.mpr hrb).ne' h
      · exact hderiv_ab c (lt_trans har hrc) hcb h
    refine ⟨fun hxr => ⟨hl_ne, ?_⟩, fun hrx => ⟨hr_ne, ?_⟩⟩
    · set m := (a + r) / 2
      have ham : a < m := by dsimp [m]; linarith
      have hmr : m < r := by dsimp [m]; linarith
      have hm_in : inCell R j m := hIoo_inCell m ham (lt_trans hmr hrb)
      have hxm : sameSign (p.eval x) (p.eval m) :=
        poly_const_sign_open hIVT p (fun c hc1 hc2 hc0 => by
          have hc_lt : c < r := lt_of_le_of_lt hc2 (max_lt hxr hmr)
          have hcr_eq := huniq c r (hcell_between x m hx hm_in c hc1 hc2) hr hc0 hr0
          exact hc_lt.ne hcr_eq)
      have ha_ne : p.eval a ≠ 0 := fun ha0 => hl_ne (ha_sign.2.mp ha0)
      have hno_ar : ∀ c : K, a < c → c < r → p.eval c ≠ 0 :=
        fun c hca hcr hc0 => hcr.ne (huniq c r (hIoo_inCell c hca (lt_trans hcr hrb)) hr hc0 hr0)
      have hma := poly_no_root_bounded_left_sign hIVT p ham hmr hno_ar ha_ne
      exact sameSign_trans hxm (sameSign_trans hma ha_sign)
    · set m := (r + b) / 2
      have hrm : r < m := by dsimp [m]; linarith
      have hmb : m < b := by dsimp [m]; linarith
      have hm_in : inCell R j m := hIoo_inCell m (lt_trans har hrm) hmb
      have hxm : sameSign (p.eval x) (p.eval m) :=
        poly_const_sign_open hIVT p (fun c hc1 hc2 hc0 => by
          have hrc_lt : r < c := lt_of_lt_of_le (lt_min hrx hrm) hc1
          have hcr_eq := huniq c r (hcell_between x m hx hm_in c hc1 hc2) hr hc0 hr0
          exact hrc_lt.ne' hcr_eq)
      have hb_ne : p.eval b ≠ 0 := fun hb0 => hr_ne (hb_sign.2.mp hb0)
      have hno_rb : ∀ c : K, r < c → c < b → p.eval c ≠ 0 :=
        fun c hrc hcb hc0 => hrc.ne' (huniq c r (hIoo_inCell c (lt_trans har hrc) hcb) hr hc0 hr0)
      have hmb' := poly_no_root_bounded_right_sign hIVT p hrm hmb hno_rb hb_ne
      exact sameSign_trans hxm (sameSign_trans hmb' hb_sign)
  exact ⟨hnot_both_zero, hiff_root, huniq, hno_root_sign, hwith_root_sign⟩

noncomputable def mergeCells {K : Type} (R : List K) (opt : ℕ → List K) (j : ℕ) : List K :=
  if hj : j < R.length then opt j ++ [R[j]] ++ mergeCells R opt (j + 1)
  else opt R.length
termination_by R.length - j

lemma mergeCells_mem_and_pairwise {K : Type} [LinearOrder K]
    (R : List K) (hR : R.Pairwise (· < ·)) (opt : ℕ → List K)
    (hopt_in : ∀ j ≤ R.length, ∀ x ∈ opt j, inCell R j x)
    (hopt_pw : ∀ j ≤ R.length, (opt j).Pairwise (· < ·)) :
    ∀ (j : ℕ), j ≤ R.length →
      (mergeCells R opt j).Pairwise (· < ·) ∧
      (∀ x ∈ mergeCells R opt j, ∀ i < j, ∀ hi : i < R.length, R[i] < x) ∧
      (∀ x, x ∈ mergeCells R opt j ↔ (∃ (i : ℕ) (hi : i < R.length), j ≤ i ∧ x = R[i]) ∨ (∃ k, j ≤ k ∧ k ≤ R.length ∧ x ∈ opt k)) := by
  intro j hj
  suffices h : ∀ n (j : ℕ), R.length - j = n → j ≤ R.length →
      (mergeCells R opt j).Pairwise (· < ·) ∧
      (∀ x ∈ mergeCells R opt j, ∀ i < j, ∀ hi : i < R.length, R[i] < x) ∧
      (∀ x, x ∈ mergeCells R opt j ↔ (∃ (i : ℕ) (hi : i < R.length), j ≤ i ∧ x = R[i]) ∨ (∃ k, j ≤ k ∧ k ≤ R.length ∧ x ∈ opt k)) from
    h (R.length - j) j rfl hj
  intro n
  induction n with
  | zero =>
    intro j hsub hj_le
    have hj_eq : j = R.length := by omega
    subst hj_eq
    have hmc : mergeCells R opt R.length = opt R.length := by
      unfold mergeCells
      simp
    rw [hmc]
    refine ⟨hopt_pw R.length le_rfl, fun x hx i hi hilen => (hopt_in R.length le_rfl x hx).1 i hilen hi, fun x => ?_⟩
    constructor
    · intro hx
      exact Or.inr ⟨R.length, le_rfl, le_rfl, hx⟩
    · rintro (⟨i, hi2, hi1, _⟩ | ⟨k, hk1, hk2, hx⟩)
      · omega
      · have : k = R.length := by omega
        subst this
        exact hx
  | succ n ih =>
    intro j hsub hj_le
    have hj_lt : j < R.length := by omega
    have hmc : mergeCells R opt j = opt j ++ [R[j]] ++ mergeCells R opt (j + 1) := by
      conv_lhs => unfold mergeCells; rw [dif_pos hj_lt]
    obtain ⟨ih_pw, ih_gt, ih_mem⟩ := ih (j + 1) (by omega) hj_lt
    have hoptj_pw := hopt_pw j hj_lt.le
    have hoptj_lt_Rj : ∀ x ∈ opt j, x < R[j] := fun x hx => (hopt_in j hj_lt.le x hx).2 j hj_lt le_rfl
    have hRj_lt_rest : ∀ y ∈ mergeCells R opt (j + 1), R[j] < y :=
      fun y hy => ih_gt y hy j (Nat.lt_succ_self j) hj_lt
    have hoptj_lt_rest : ∀ x ∈ opt j, ∀ y ∈ mergeCells R opt (j + 1), x < y :=
      fun x hx y hy => lt_trans (hoptj_lt_Rj x hx) (hRj_lt_rest y hy)
    rw [hmc]
    refine ⟨?_, ?_, fun x => ?_⟩
    · rw [List.append_assoc, List.pairwise_append]
      refine ⟨hoptj_pw, List.pairwise_cons.mpr ⟨hRj_lt_rest, ih_pw⟩, fun x hx y hy => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hoptj_lt_Rj x hx
      · exact hoptj_lt_rest x hx y hy
    · intro x hx i hij hi
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (hx | rfl) | hx
      · exact (hopt_in j hj_lt.le x hx).1 i hi hij
      · exact List.pairwise_iff_getElem.mp hR i j hi hj_lt hij
      · exact ih_gt x hx i (Nat.lt_succ_of_lt hij) hi
    · simp only [List.mem_append, List.mem_singleton, ih_mem]
      constructor
      · rintro ((hx | rfl) | (⟨i, hi2, hi1, rfl⟩ | ⟨k, hk1, hk2, hx⟩))
        · exact Or.inr ⟨j, le_rfl, hj_lt.le, hx⟩
        · exact Or.inl ⟨j, hj_lt, le_rfl, rfl⟩
        · exact Or.inl ⟨i, hi2, Nat.le_of_succ_le hi1, rfl⟩
        · exact Or.inr ⟨k, Nat.le_of_succ_le hk1, hk2, hx⟩
      · rintro (⟨i, hi2, hi1, rfl⟩ | ⟨k, hk1, hk2, hx⟩)
        · rcases eq_or_lt_of_le hi1 with rfl | hlt
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr (Or.inl ⟨i, hi2, hlt, rfl⟩)
        · rcases eq_or_lt_of_le hk1 with rfl | hlt
          · exact Or.inl (Or.inl hx)
          · exact Or.inr (Or.inr ⟨k, hlt, hk2, hx⟩)

lemma mergeCells_forall₂ {K₁ K₂ : Type}
    (R₁ : List K₁) (R₂ : List K₂) (hlen : R₁.length = R₂.length)
    (opt₁ : ℕ → List K₁) (opt₂ : ℕ → List K₂) (rel : K₁ → K₂ → Prop)
    (hrel_R : ∀ (j : ℕ) (h₁ : j < R₁.length) (h₂ : j < R₂.length), rel R₁[j] R₂[j])
    (hrel_opt : ∀ j ≤ R₁.length, List.Forall₂ rel (opt₁ j) (opt₂ j)) :
    ∀ (j : ℕ), j ≤ R₁.length →
      List.Forall₂ rel (mergeCells R₁ opt₁ j) (mergeCells R₂ opt₂ j) := by
  intro j hj
  suffices h : ∀ n (j : ℕ), R₁.length - j = n → j ≤ R₁.length →
      List.Forall₂ rel (mergeCells R₁ opt₁ j) (mergeCells R₂ opt₂ j) from
    h (R₁.length - j) j rfl hj
  intro n
  induction n with
  | zero =>
    intro j hsub hj_le
    have hj_eq : j = R₁.length := by omega
    subst hj_eq
    have hm1 : mergeCells R₁ opt₁ R₁.length = opt₁ R₁.length := by
      unfold mergeCells; simp
    have hm2 : mergeCells R₂ opt₂ R₁.length = opt₂ R₂.length := by
      unfold mergeCells; simp [hlen]
    rw [hm1, hm2, ← hlen]
    exact hrel_opt R₁.length le_rfl
  | succ n ih =>
    intro j hsub hj_le
    have hj1 : j < R₁.length := by omega
    have hj2 : j < R₂.length := hlen ▸ hj1
    have hm1 : mergeCells R₁ opt₁ j = opt₁ j ++ [R₁[j]] ++ mergeCells R₁ opt₁ (j + 1) := by
      conv_lhs => unfold mergeCells; rw [dif_pos hj1]
    have hm2 : mergeCells R₂ opt₂ j = opt₂ j ++ [R₂[j]] ++ mergeCells R₂ opt₂ (j + 1) := by
      conv_lhs => unfold mergeCells; rw [dif_pos hj2]
    rw [hm1, hm2]
    exact forall₂_append_of
      (forall₂_append_of (hrel_opt j hj1.le) (List.Forall₂.cons (hrel_R j hj1 hj2) List.Forall₂.nil))
      (ih (j + 1) (by omega) hj1)

lemma countP_take_lt_of_iff {K : Type} [LinearOrder K] :
    ∀ {R RF : List K}, RF.Pairwise (· < ·) → R.Pairwise (· < ·) →
      (∀ r, r ∈ R → r ∈ RF) →
      ∀ {i : ℕ} {x : K}, i ≤ RF.length →
      (∀ k (hk : k < RF.length), RF[k] ∈ R → (k < i ↔ RF[k] < x)) →
      ∀ {j : ℕ}, j ≤ R.length → inCell R j x →
      j = (RF.take i).countP (fun r => decide (r ∈ R)) := by
  classical
  intro R RF hRF hR hsub i x hi_le hiff j hj_le hjx
  have h1 : (RF.take i).countP (fun r => decide (r ∈ R)) = (RF.filter (fun r => decide (r ∈ R ∧ r < x))).length := by
    have hfilt : ∀ {l : List K} (k : ℕ), k ≤ l.length → l.Pairwise (· < ·) →
        (∀ m (hm : m < l.length), l[m] ∈ R → (m < k ↔ l[m] < x)) →
        (l.take k).countP (fun r => decide (r ∈ R)) = (l.filter (fun r => decide (r ∈ R ∧ r < x))).length := by
      intro l
      induction l with
      | nil =>
        intro k hk _ _
        simp at hk
        subst hk
        simp
      | cons a t ih =>
        intro k hk hpw hm_iff
        rw [List.pairwise_cons] at hpw
        cases k with
        | zero =>
          simp only [List.take_zero, List.countP_nil]
          symm
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro r hr
          simp only [decide_eq_true_eq, not_and, not_lt]
          intro hrR
          rcases List.mem_cons.mp hr with rfl | hrt
          · have h0 := hm_iff 0 (by simp) hrR
            by_contra hlt
            exact absurd (h0.mpr (not_le.mp hlt)) (Nat.not_lt_zero 0)
          · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hrt
            have hm' := hm_iff (m + 1) (by simp [hm]) hrR
            by_contra hlt
            exact absurd (hm'.mpr (not_le.mp hlt)) (Nat.not_lt_zero (m + 1))
        | succ k =>
          have hk' : k ≤ t.length := Nat.succ_le_succ_iff.mp hk
          have hm_iff' : ∀ m (hm : m < t.length), t[m] ∈ R → (m < k ↔ t[m] < x) := by
            intro m hm hmR
            have := hm_iff (m + 1) (by simp [hm]) hmR
            simpa [Nat.succ_lt_succ_iff] using this
          have ih' := ih k hk' hpw.2 hm_iff'
          rw [List.take_succ_cons, List.countP_cons, List.filter_cons]
          by_cases haR : a ∈ R
          · have hax : a < x := (hm_iff 0 (by simp) haR).mp (Nat.zero_lt_succ k)
            simp [haR, hax, ih', Nat.add_comm]
          · simp [haR, ih']
    exact hfilt i hi_le hRF hiff
  have h2 : (RF.filter (fun r => decide (r ∈ R ∧ r < x))).length = (R.filter (fun r => decide (r < x))).length := by
    have hp1 : (RF.filter (fun r => decide (r ∈ R ∧ r < x))).Pairwise (· < ·) := hRF.filter _
    have hp2 : (R.filter (fun r => decide (r < x))).Pairwise (· < ·) := hR.filter _
    have heq_l : RF.filter (fun r => decide (r ∈ R ∧ r < x)) = R.filter (fun r => decide (r < x)) := by
      refine list_eq_of_pairwise_lt_of_mem_iff hp1 hp2 (fun r => ?_)
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨_, hrR, hrx⟩; exact ⟨hrR, hrx⟩
      · rintro ⟨hrR, hrx⟩; exact ⟨hsub r hrR, hrR, hrx⟩
    rw [heq_l]
  have h3 : (R.filter (fun r => decide (r < x))).length = j := by
    have hfiltR : ∀ {l : List K} (k : ℕ), k ≤ l.length → l.Pairwise (· < ·) →
        (∀ m (hm : m < l.length), m < k → l[m] < x) →
        (∀ m (hm : m < l.length), k ≤ m → x < l[m]) →
        (l.filter (fun r => decide (r < x))).length = k := by
      intro l
      induction l with
      | nil =>
        intro k hk _ _ _
        simp at hk; subst hk; simp
      | cons a t ih =>
        intro k hk hpw hlt hgt
        rw [List.pairwise_cons] at hpw
        cases k with
        | zero =>
          have ha_gt : x < a := hgt 0 (by simp) le_rfl
          rw [List.filter_cons, if_neg (by simp [not_lt.mpr ha_gt.le])]
          rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro r hr
          simp only [decide_eq_true_eq, not_lt]
          obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hr
          exact (hgt (m + 1) (by simp [hm]) (Nat.zero_le _)).le
        | succ k =>
          have hax : a < x := hlt 0 (by simp) (Nat.zero_lt_succ k)
          rw [List.filter_cons, if_pos (by simp [hax]), List.length_cons]
          have ih' := ih k (Nat.succ_le_succ_iff.mp hk) hpw.2
            (fun m hm hmk => hlt (m + 1) (by simp [hm]) (Nat.succ_lt_succ hmk))
            (fun m hm hkm => hgt (m + 1) (by simp [hm]) (Nat.succ_le_succ hkm))
          omega
    exact hfiltR j hj_le hR hjx.1 hjx.2
  omega

lemma addPolySignTable {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (hIVT₁ : ∀ (p : Polynomial K₁) {a b : K₁}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₁, a < c ∧ c < b ∧ p.eval c = 0)
    (hIVT₂ : ∀ (p : Polynomial K₂) {a b : K₂}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₂, a < c ∧ c < b ∧ p.eval c = 0)
    (hMVT₁ : ∀ (p : Polynomial K₁) {u v : K₁}, u < v →
      ∃ c : K₁, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hMVT₂ : ∀ (p : Polynomial K₂) {u v : K₂}, u < v →
      ∃ c : K₂, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hAsymp₁ : ∀ (p : Polynomial K₁), p ≠ 0 →
      ∃ M : K₁, ∀ x : K₁, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (hAsymp₂ : ∀ (p : Polynomial K₂), p ≠ 0 →
      ∃ M : K₂, ∀ x : K₂, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    {φ₁ : A →+* K₁} {φ₂ : A →+* K₂} {P₁ : List (Polynomial A)} {f : Polynomial A}
    (hf_nz : φ₁ f.leadingCoeff ≠ 0) (hf_deriv : f.derivative ∈ P₁)
    (hP₁_nz : ∀ g ∈ P₁, g ≠ 0 ∧ φ₁ g.leadingCoeff ≠ 0)
    (hlead_f : sameSign (φ₁ f.leadingCoeff) (φ₂ f.leadingCoeff))
    (hlead_P : ∀ g ∈ P₁, sameSign (φ₁ g.leadingCoeff) (φ₂ g.leadingCoeff))
    (hST : SignTableMatch φ₁ φ₂ P₁)
    (hprem : ∀ g ∈ P₁, ∀ (i : ℕ) (h₁ : i < (rootList (P₁.map (Polynomial.map φ₁))).length)
        (h₂ : i < (rootList (P₁.map (Polynomial.map φ₂))).length),
      (g.map φ₁).eval (rootList (P₁.map (Polynomial.map φ₁)))[i] = 0 →
      sameSign (((prem f g).map φ₁).eval (rootList (P₁.map (Polynomial.map φ₁)))[i])
               (((prem f g).map φ₂).eval (rootList (P₁.map (Polynomial.map φ₂)))[i])) :
    SignTableMatch φ₁ φ₂ (P₁ ++ [f]) := by
  classical
  set R₁ := rootList (P₁.map (Polynomial.map φ₁))
  set R₂ := rootList (P₁.map (Polynomial.map φ₂))
  have hR₁ : R₁.Pairwise (· < ·) := rootList_pairwise_lt _
  have hR₂ : R₂.Pairwise (· < ·) := rootList_pairwise_lt _
  set f₁ := f.map φ₁
  set f₂ := f.map φ₂
  have hf₂_lc : φ₂ f.leadingCoeff ≠ 0 := fun h => hf_nz (hlead_f.2.mpr h)
  have hf₁_ne : f₁ ≠ 0 := by
    intro h0
    have hlc : f₁.leadingCoeff = φ₁ f.leadingCoeff := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₁ hf_nz
    rw [h0, Polynomial.leadingCoeff_zero] at hlc
    exact hf_nz hlc.symm
  have hf₂_ne : f₂ ≠ 0 := by
    intro h0
    have hlc : f₂.leadingCoeff = φ₂ f.leadingCoeff := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₂ hf₂_lc
    rw [h0, Polynomial.leadingCoeff_zero] at hlc
    exact hf₂_lc hlc.symm
  have hf₁_deg : f₁.natDegree = f.natDegree := Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ₁ hf_nz
  have hf₂_deg : f₂.natDegree = f.natDegree := Polynomial.natDegree_map_of_leadingCoeff_ne_zero φ₂ hf₂_lc
  have hf₁_lc : f₁.leadingCoeff = φ₁ f.leadingCoeff := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₁ hf_nz
  have hf₂_lc_eq : f₂.leadingCoeff = φ₂ f.leadingCoeff := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₂ hf₂_lc
  have hf_at_R : ∀ (i : ℕ) (h₁ : i < R₁.length) (h₂ : i < R₂.length),
      sameSign (f₁.eval R₁[i]) (f₂.eval R₂[i]) := by
    intro i hi₁ hi₂
    have hmem : R₁[i] ∈ R₁ := List.getElem_mem hi₁
    rw [mem_rootList] at hmem
    obtain ⟨pK, hpK, hpK0, hpKx⟩ := hmem
    rw [List.mem_map] at hpK
    obtain ⟨g, hgP, rfl⟩ := hpK
    have hgb₁ : φ₁ g.leadingCoeff ≠ 0 := (hP₁_nz g hgP).2
    have hgb₂ : φ₂ g.leadingCoeff ≠ 0 := fun h => hgb₁ ((hlead_P g hgP).2.mpr h)
    have hgx₂ : (g.map φ₂).eval R₂[i] = 0 := (hST.2.1 i hi₁ hi₂ g hgP).2.mp hpKx
    have h1 := prem_sameSign (f := f) φ₁ hgb₁ hpKx
    have h2 := hprem g hgP i hi₁ hi₂ hpKx
    have h3 := prem_sameSign (f := f) φ₂ hgb₂ hgx₂
    exact sameSign_trans (sameSign_symm h1) (sameSign_trans h2 h3)
  have hderiv₁ : ∀ j ≤ R₁.length, ∀ x : K₁, inCell R₁ j x → f₁.derivative.eval x ≠ 0 := by
    intro j _ x hx h0
    have hfd_ne : f.derivative.map φ₁ ≠ 0 := by
      intro hz
      have hfd_mem := List.mem_map_of_mem (f := Polynomial.map φ₁) hf_deriv
      have hfd_lc : φ₁ f.derivative.leadingCoeff ≠ 0 := (hP₁_nz f.derivative hf_deriv).2
      have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₁ hfd_lc
      rw [hz, Polynomial.leadingCoeff_zero] at this
      exact hfd_lc this.symm
    have hx_mem : x ∈ R₁ := mem_rootList.mpr ⟨f.derivative.map φ₁, List.mem_map_of_mem hf_deriv, hfd_ne, by
      simpa [f₁, Polynomial.derivative_map] using h0⟩
    exact inCell_not_mem hx hx_mem
  have hderiv₂ : ∀ j ≤ R₂.length, ∀ x : K₂, inCell R₂ j x → f₂.derivative.eval x ≠ 0 := by
    intro j _ x hx h0
    have hfd_lc₁ : φ₁ f.derivative.leadingCoeff ≠ 0 := (hP₁_nz f.derivative hf_deriv).2
    have hfd_lc₂ : φ₂ f.derivative.leadingCoeff ≠ 0 := fun h => hfd_lc₁ ((hlead_P f.derivative hf_deriv).2.mpr h)
    have hfd_ne : f.derivative.map φ₂ ≠ 0 := by
      intro hz
      have := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ₂ hfd_lc₂
      rw [hz, Polynomial.leadingCoeff_zero] at this
      exact hfd_lc₂ this.symm
    have hx_mem : x ∈ R₂ := mem_rootList.mpr ⟨f.derivative.map φ₂, List.mem_map_of_mem hf_deriv, hfd_ne, by
      simpa [f₂, Polynomial.derivative_map] using h0⟩
    exact inCell_not_mem hx hx_mem
  have hL_ss : ∀ j ≤ R₁.length, sameSign (cellLeftVal f₁ R₁ j) (cellLeftVal f₂ R₂ j) := by
    intro j hj
    dsimp [cellLeftVal]
    by_cases hcond : 0 < j ∧ j - 1 < R₁.length
    · have hcond2 : 0 < j ∧ j - 1 < R₂.length := ⟨hcond.1, hST.1 ▸ hcond.2⟩
      simp only [dif_pos hcond, dif_pos hcond2]
      exact hf_at_R (j - 1) hcond.2 hcond2.2
    · have hcond2 : ¬ (0 < j ∧ j - 1 < R₂.length) := by rwa [← hST.1]
      simp only [dif_neg hcond, dif_neg hcond2, hf₁_deg, hf₂_deg, hf₁_lc, hf₂_lc_eq]
      exact sameSign_mul (sameSign_neg_one_pow f.natDegree) hlead_f
  have hR_ss : ∀ j ≤ R₁.length, sameSign (cellRightVal f₁ R₁ j) (cellRightVal f₂ R₂ j) := by
    intro j hj
    dsimp [cellRightVal]
    by_cases hcond : j < R₁.length
    · have hcond2 : j < R₂.length := hST.1 ▸ hcond
      simp only [dif_pos hcond, dif_pos hcond2]
      exact hf_at_R j hcond hcond2
    · have hcond2 : ¬ j < R₂.length := by rwa [← hST.1]
      simp only [dif_neg hcond, dif_neg hcond2, hf₁_lc, hf₂_lc_eq]
      exact hlead_f
  have hca₁ : ∀ j ≤ R₁.length, _ := fun j hj => cell_root_analysis hIVT₁ hMVT₁ hAsymp₁ f₁ hf₁_ne R₁ hR₁ j hj (hderiv₁ j hj)
  have hca₂ : ∀ j ≤ R₂.length, _ := fun j hj => cell_root_analysis hIVT₂ hMVT₂ hAsymp₂ f₂ hf₂_ne R₂ hR₂ j hj (hderiv₂ j hj)
  have hroot_iff : ∀ j ≤ R₁.length,
      (∃ r : K₁, inCell R₁ j r ∧ f₁.eval r = 0) ↔ (∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0) := by
    intro j hj
    rw [(hca₁ j hj).2.1, (hca₂ j (hST.1 ▸ hj)).2.1]
    exact (sameSign_mul (hL_ss j hj) (hR_ss j hj)).1
  let opt₁ : ℕ → List K₁ := fun j => if h : ∃ r : K₁, inCell R₁ j r ∧ f₁.eval r = 0 then [Classical.choose h] else []
  let opt₂ : ℕ → List K₂ := fun j => if h : ∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0 then [Classical.choose h] else []
  have hopt₁_in : ∀ j ≤ R₁.length, ∀ x ∈ opt₁ j, inCell R₁ j x := by
    intro j _ x hx
    dsimp [opt₁] at hx
    split_ifs at hx with h
    · simp only [List.mem_singleton] at hx
      subst hx
      exact (Classical.choose_spec h).1
    · simp at hx
  have hopt₂_in : ∀ j ≤ R₂.length, ∀ x ∈ opt₂ j, inCell R₂ j x := by
    intro j _ x hx
    dsimp [opt₂] at hx
    split_ifs at hx with h
    · simp only [List.mem_singleton] at hx
      subst hx
      exact (Classical.choose_spec h).1
    · simp at hx
  have hopt₁_pw : ∀ j ≤ R₁.length, (opt₁ j).Pairwise (· < ·) := by
    intro j _
    dsimp [opt₁]
    split_ifs <;> simp
  have hopt₂_pw : ∀ j ≤ R₂.length, (opt₂ j).Pairwise (· < ·) := by
    intro j _
    dsimp [opt₂]
    split_ifs <;> simp
  set RF₁ := rootList ((P₁ ++ [f]).map (Polynomial.map φ₁))
  set RF₂ := rootList ((P₁ ++ [f]).map (Polynomial.map φ₂))
  have hmc₁ := mergeCells_mem_and_pairwise R₁ hR₁ opt₁ hopt₁_in hopt₁_pw 0 (Nat.zero_le _)
  have hmc₂ := mergeCells_mem_and_pairwise R₂ hR₂ opt₂ hopt₂_in hopt₂_pw 0 (Nat.zero_le _)
  have hRF₁_eq : RF₁ = mergeCells R₁ opt₁ 0 := by
    refine list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise_lt _) hmc₁.1 (fun x => ?_)
    rw [hmc₁.2.2 x, mem_rootList]
    simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨q, hq | rfl, hq0, hqx⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_rootList.mpr ⟨q, hq, hq0, hqx⟩)
        exact Or.inl ⟨i, hi, Nat.zero_le _, rfl⟩
      · by_cases hxR : x ∈ R₁
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxR
          exact Or.inl ⟨i, hi, Nat.zero_le _, rfl⟩
        · obtain ⟨j, hj_le, hjx⟩ := exists_inCell_of_not_mem hR₁ hxR
          have hex : ∃ r : K₁, inCell R₁ j r ∧ f₁.eval r = 0 := ⟨x, hjx, hqx⟩
          have hchoose := Classical.choose_spec hex
          have hxeq : x = Classical.choose hex := (hca₁ j hj_le).2.2.1 x _ hjx hchoose.1 hqx hchoose.2
          refine Or.inr ⟨j, Nat.zero_le _, hj_le, ?_⟩
          dsimp [opt₁]
          rw [dif_pos hex, List.mem_singleton]
          exact hxeq
    · rintro (⟨i, hi, _, rfl⟩ | ⟨k, _, hk, hxk⟩)
      · obtain ⟨q, hq, hq0, hqx⟩ := mem_rootList.mp (List.getElem_mem hi)
        exact ⟨q, Or.inl hq, hq0, hqx⟩
      · refine ⟨f₁, Or.inr rfl, hf₁_ne, ?_⟩
        dsimp [opt₁] at hxk
        split_ifs at hxk with h
        · simp only [List.mem_singleton] at hxk
          subst hxk
          exact (Classical.choose_spec h).2
        · simp at hxk
  have hRF₂_eq : RF₂ = mergeCells R₂ opt₂ 0 := by
    refine list_eq_of_pairwise_lt_of_mem_iff (rootList_pairwise_lt _) hmc₂.1 (fun x => ?_)
    rw [hmc₂.2.2 x, mem_rootList]
    simp only [List.map_append, List.map_singleton, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨q, hq | rfl, hq0, hqx⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_rootList.mpr ⟨q, hq, hq0, hqx⟩)
        exact Or.inl ⟨i, hi, Nat.zero_le _, rfl⟩
      · by_cases hxR : x ∈ R₂
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxR
          exact Or.inl ⟨i, hi, Nat.zero_le _, rfl⟩
        · obtain ⟨j, hj_le, hjx⟩ := exists_inCell_of_not_mem hR₂ hxR
          have hex : ∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0 := ⟨x, hjx, hqx⟩
          have hchoose := Classical.choose_spec hex
          have hxeq : x = Classical.choose hex := (hca₂ j hj_le).2.2.1 x _ hjx hchoose.1 hqx hchoose.2
          refine Or.inr ⟨j, Nat.zero_le _, hj_le, ?_⟩
          dsimp [opt₂]
          rw [dif_pos hex, List.mem_singleton]
          exact hxeq
    · rintro (⟨i, hi, _, rfl⟩ | ⟨k, _, hk, hxk⟩)
      · obtain ⟨q, hq, hq0, hqx⟩ := mem_rootList.mp (List.getElem_mem hi)
        exact ⟨q, Or.inl hq, hq0, hqx⟩
      · refine ⟨f₂, Or.inr rfl, hf₂_ne, ?_⟩
        dsimp [opt₂] at hxk
        split_ifs at hxk with h
        · simp only [List.mem_singleton] at hxk
          subst hxk
          exact (Classical.choose_spec h).2
        · simp at hxk
  let rel : K₁ → K₂ → Prop := fun r₁ r₂ =>
    (r₁ ∈ R₁ ↔ r₂ ∈ R₂) ∧
    (∀ p ∈ P₁ ++ [f], sameSign ((p.map φ₁).eval r₁) ((p.map φ₂).eval r₂))
  have hF_mc : List.Forall₂ rel (mergeCells R₁ opt₁ 0) (mergeCells R₂ opt₂ 0) := by
    refine mergeCells_forall₂ R₁ R₂ hST.1 opt₁ opt₂ rel ?_ ?_ 0 (Nat.zero_le _)
    · intro j hj₁ hj₂
      refine ⟨⟨fun _ => List.getElem_mem hj₂, fun _ => List.getElem_mem hj₁⟩, fun p hp => ?_⟩
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hST.2.1 j hj₁ hj₂ p hp
      · exact hf_at_R j hj₁ hj₂
    · intro j hj
      dsimp [opt₁, opt₂]
      by_cases h1 : ∃ r : K₁, inCell R₁ j r ∧ f₁.eval r = 0
      · have h2 : ∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0 := (hroot_iff j hj).mp h1
        rw [dif_pos h1, dif_pos h2]
        refine List.Forall₂.cons ⟨?_, fun p hp => ?_⟩ List.Forall₂.nil
        · constructor
          · intro hm; exact absurd hm (inCell_not_mem (Classical.choose_spec h1).1)
          · intro hm; exact absurd hm (inCell_not_mem (Classical.choose_spec h2).1)
        · simp only [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · exact hST.2.2 j _ _ hj (Classical.choose_spec h1).1 (Classical.choose_spec h2).1 p hp
          · rw [(Classical.choose_spec h1).2, (Classical.choose_spec h2).2]
            exact sameSign_zero
      · have h2 : ¬ ∃ r : K₂, inCell R₂ j r ∧ f₂.eval r = 0 := fun hx => h1 ((hroot_iff j hj).mpr hx)
        rw [dif_neg h1, dif_neg h2]
        exact List.Forall₂.nil
  rw [← hRF₁_eq, ← hRF₂_eq] at hF_mc
  refine ⟨(List.forall₂_iff_get.mp hF_mc).1, fun i hi₁ hi₂ p hp => (forall₂_getElem hF_mc i hi₁ hi₂).2 p hp, ?_⟩
  intro i x₁ x₂ hi_le hx₁ hx₂ q hq
  have hx₁_nR : x₁ ∉ R₁ := fun hm => by
    have hxRF : x₁ ∈ RF₁ := by
      obtain ⟨p', hp', hp0, hpx⟩ := mem_rootList.mp hm
      exact mem_rootList.mpr ⟨p', by simp [hp'], hp0, hpx⟩
    exact inCell_not_mem hx₁ hxRF
  have hx₂_nR : x₂ ∉ R₂ := fun hm => by
    have hxRF : x₂ ∈ RF₂ := by
      obtain ⟨p', hp', hp0, hpx⟩ := mem_rootList.mp hm
      exact mem_rootList.mpr ⟨p', by simp [hp'], hp0, hpx⟩
    exact inCell_not_mem hx₂ hxRF
  obtain ⟨j₁, hj₁_le, hj₁_in⟩ := exists_inCell_of_not_mem hR₁ hx₁_nR
  obtain ⟨j₂, hj₂_le, hj₂_in⟩ := exists_inCell_of_not_mem hR₂ hx₂_nR
  have hRF₁_pw : RF₁.Pairwise (· < ·) := rootList_pairwise_lt _
  have hRF₂_pw : RF₂.Pairwise (· < ·) := rootList_pairwise_lt _
  have hsub₁ : ∀ r, r ∈ R₁ → r ∈ RF₁ := fun r hr => by
    obtain ⟨p', hp', hp0, hpx⟩ := mem_rootList.mp hr
    exact mem_rootList.mpr ⟨p', by simp [hp'], hp0, hpx⟩
  have hsub₂ : ∀ r, r ∈ R₂ → r ∈ RF₂ := fun r hr => by
    obtain ⟨p', hp', hp0, hpx⟩ := mem_rootList.mp hr
    exact mem_rootList.mpr ⟨p', by simp [hp'], hp0, hpx⟩
  have hRF_len : RF₁.length = RF₂.length := (List.forall₂_iff_get.mp hF_mc).1
  have hj₁_eq := countP_take_lt_of_iff hRF₁_pw hR₁ hsub₁ hi_le
    (fun k hk _ => ⟨fun hki => hx₁.1 k hk hki, fun hkx => by
      by_contra hge
      exact lt_irrefl _ (lt_trans hkx (hx₁.2 k hk (not_lt.mp hge)))⟩)
    hj₁_le hj₁_in
  have hj₂_eq := countP_take_lt_of_iff hRF₂_pw hR₂ hsub₂ (hRF_len ▸ hi_le)
    (fun k hk _ => ⟨fun hki => hx₂.1 k hk hki, fun hkx => by
      by_contra hge
      exact lt_irrefl _ (lt_trans hkx (hx₂.2 k hk (not_lt.mp hge)))⟩)
    hj₂_le hj₂_in
  have htake_eq : (RF₁.take i).countP (fun r => decide (r ∈ R₁)) = (RF₂.take i).countP (fun r => decide (r ∈ R₂)) := by
    refine countP_eq_of_forall₂ _ _ (forall₂_of_getElem (by simp [hRF_len]) (fun k hk₁ hk₂ => ?_))
    have hki : k < i := by
      have : k < (RF₁.take i).length := hk₁
      rw [List.length_take] at this
      exact (lt_min_iff.mp this).1
    have hk_RF₁ : k < RF₁.length := lt_of_lt_of_le hki hi_le
    have hk_RF₂ : k < RF₂.length := hRF_len ▸ hk_RF₁
    change decide ((RF₁.take i)[k] ∈ R₁) = decide ((RF₂.take i)[k] ∈ R₂)
    rw [List.getElem_take, List.getElem_take]
    simpa [decide_eq_true_eq] using (forall₂_getElem hF_mc k hk_RF₁ hk_RF₂).1
  have hj_eq : j₁ = j₂ := by omega
  subst hj_eq
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hST.2.2 j₁ x₁ x₂ hj₁_le hj₁_in hj₂_in q hq
  · by_cases hopt : ∃ r : K₁, inCell R₁ j₁ r ∧ f₁.eval r = 0
    · have hopt2 : ∃ r : K₂, inCell R₂ j₁ r ∧ f₂.eval r = 0 := (hroot_iff j₁ hj₁_le).mp hopt
      set r₁ := Classical.choose hopt
      set r₂ := Classical.choose hopt2
      have hr₁_spec := Classical.choose_spec hopt
      have hr₂_spec := Classical.choose_spec hopt2
      have hr₁_RF : r₁ ∈ RF₁ := mem_rootList.mpr ⟨f₁, by simp [f₁], hf₁_ne, hr₁_spec.2⟩
      obtain ⟨idx, hidx₁, hidx_eq⟩ := List.mem_iff_getElem.mp hr₁_RF
      have hidx_eq' : RF₁[idx] = Classical.choose hopt := hidx_eq
      have hidx₂ : idx < RF₂.length := hRF_len ▸ hidx₁
      have hr₂'_nR : RF₂[idx] ∉ R₂ := fun hm => by
        have hmem1 : RF₁[idx] ∈ R₁ := (forall₂_getElem hF_mc idx hidx₁ hidx₂).1.mpr hm
        exact inCell_not_mem hr₁_spec.1 (hidx_eq' ▸ hmem1)
      have hr₂'_f : f₂.eval RF₂[idx] = 0 := by
        have := (forall₂_getElem hF_mc idx hidx₁ hidx₂).2 q (by simp)
        change sameSign (f₁.eval RF₁[idx]) (f₂.eval RF₂[idx]) at this
        rw [hidx_eq', hr₁_spec.2] at this
        exact this.2.mp rfl
      have hr₂'_in : inCell R₂ j₁ RF₂[idx] := by
        obtain ⟨j', hj'_le, hj'_in⟩ := exists_inCell_of_not_mem hR₂ hr₂'_nR
        have hj'_eq_j₁ : j' = j₁ := by
          have hc1 : j₁ = (RF₁.take idx).countP (fun r => decide (r ∈ R₁)) := by
            refine countP_take_lt_of_iff hRF₁_pw hR₁ hsub₁ hidx₁.le (fun k hk hkR => ?_) hj₁_le hr₁_spec.1
            have hk_ne : k ≠ idx := fun he => by
              have : RF₁[idx] ∈ R₁ := he ▸ hkR
              exact inCell_not_mem hr₁_spec.1 (hidx_eq' ▸ this)
            constructor
            · intro hki
              rw [← hidx_eq']
              exact List.pairwise_iff_getElem.mp hRF₁_pw k idx hk hidx₁ hki
            · intro hlt
              rw [← hidx_eq'] at hlt
              by_contra hge
              rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hgt
              · exact hk_ne rfl
              · exact lt_irrefl _ (lt_trans hlt (List.pairwise_iff_getElem.mp hRF₁_pw idx k hidx₁ hk hgt))
          have hc2 : j' = (RF₂.take idx).countP (fun r => decide (r ∈ R₂)) := by
            refine countP_take_lt_of_iff hRF₂_pw hR₂ hsub₂ hidx₂.le (fun k hk hkR => ?_) hj'_le hj'_in
            have hk_ne : k ≠ idx := fun he => hr₂'_nR (he ▸ hkR)
            constructor
            · intro hki
              exact List.pairwise_iff_getElem.mp hRF₂_pw k idx hk hidx₂ hki
            · intro hlt
              by_contra hge
              rcases eq_or_lt_of_le (not_lt.mp hge) with rfl | hgt
              · exact hk_ne rfl
              · exact lt_irrefl _ (lt_trans hlt (List.pairwise_iff_getElem.mp hRF₂_pw idx k hidx₂ hk hgt))
          have htake_idx : (RF₁.take idx).countP (fun r => decide (r ∈ R₁)) = (RF₂.take idx).countP (fun r => decide (r ∈ R₂)) := by
            refine countP_eq_of_forall₂ _ _ (forall₂_of_getElem (by simp [hRF_len]) (fun k hk₁ hk₂ => ?_))
            have hki : k < idx := by
              have : k < (RF₁.take idx).length := hk₁
              rw [List.length_take] at this
              exact (lt_min_iff.mp this).1
            have hk_RF₁ : k < RF₁.length := lt_of_lt_of_le hki hidx₁.le
            have hk_RF₂ : k < RF₂.length := hRF_len ▸ hk_RF₁
            change decide ((RF₁.take idx)[k] ∈ R₁) = decide ((RF₂.take idx)[k] ∈ R₂)
            rw [List.getElem_take, List.getElem_take]
            simpa [decide_eq_true_eq] using (forall₂_getElem hF_mc k hk_RF₁ hk_RF₂).1
          omega
        subst hj'_eq_j₁
        exact hj'_in
      have hr₂_eq : RF₂[idx] = r₂ := (hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.1 (RF₂[idx]) r₂ hr₂'_in hr₂_spec.1 hr₂'_f hr₂_spec.2
      rcases lt_or_ge idx i with hidx_lt | hidx_ge
      · have hr₁_lt : r₁ < x₁ := by rw [← hidx_eq]; exact hx₁.1 idx hidx₁ hidx_lt
        have hr₂_lt : r₂ < x₂ := by rw [← hr₂_eq]; exact hx₂.1 idx hidx₂ hidx_lt
        have h1 := ((hca₁ j₁ hj₁_le).2.2.2.2 r₁ hr₁_spec.1 hr₁_spec.2 x₁ hj₁_in).2 hr₁_lt
        have h2 := ((hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.2.2 r₂ hr₂_spec.1 hr₂_spec.2 x₂ hj₂_in).2 hr₂_lt
        exact sameSign_trans h1.2 (sameSign_trans (hR_ss j₁ hj₁_le) (sameSign_symm h2.2))
      · have hx₁_lt : x₁ < r₁ := by rw [← hidx_eq]; exact hx₁.2 idx hidx₁ hidx_ge
        have hx₂_lt : x₂ < r₂ := by rw [← hr₂_eq]; exact hx₂.2 idx hidx₂ hidx_ge
        have h1 := ((hca₁ j₁ hj₁_le).2.2.2.2 r₁ hr₁_spec.1 hr₁_spec.2 x₁ hj₁_in).1 hx₁_lt
        have h2 := ((hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.2.2 r₂ hr₂_spec.1 hr₂_spec.2 x₂ hj₂_in).1 hx₂_lt
        exact sameSign_trans h1.2 (sameSign_trans (hL_ss j₁ hj₁_le) (sameSign_symm h2.2))
    · have hopt2 : ¬ ∃ r : K₂, inCell R₂ j₁ r ∧ f₂.eval r = 0 := fun h => hopt ((hroot_iff j₁ hj₁_le).mpr h)
      have hnbz := (hca₁ j₁ hj₁_le).1
      by_cases hlv₁ : cellLeftVal f₁ R₁ j₁ = 0
      · have hrv₁ : cellRightVal f₁ R₁ j₁ ≠ 0 := fun h => hnbz ⟨hlv₁, h⟩
        have hrv₂ : cellRightVal f₂ R₂ j₁ ≠ 0 := fun h => hrv₁ ((hR_ss j₁ hj₁_le).2.mpr h)
        have h1 := ((hca₁ j₁ hj₁_le).2.2.2.1 hopt x₁ hj₁_in).2 hrv₁
        have h2 := ((hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.2.1 hopt2 x₂ hj₂_in).2 hrv₂
        exact sameSign_trans h1 (sameSign_trans (hR_ss j₁ hj₁_le) (sameSign_symm h2))
      · have hlv₂ : cellLeftVal f₂ R₂ j₁ ≠ 0 := fun h => hlv₁ ((hL_ss j₁ hj₁_le).2.mpr h)
        have h1 := ((hca₁ j₁ hj₁_le).2.2.2.1 hopt x₁ hj₁_in).1 hlv₁
        have h2 := ((hca₂ j₁ (hST.1 ▸ hj₁_le)).2.2.2.1 hopt2 x₂ hj₂_in).1 hlv₂
        exact sameSign_trans h1 (sameSign_trans (hL_ss j₁ hj₁_le) (sameSign_symm h2))

end CellRootAnalysis

section MainInduction

lemma signTableMatch_exists {A K₁ K₂ : Type} [CommRing A]
    [Field K₁] [LinearOrder K₁] [IsStrictOrderedRing K₁]
    [Field K₂] [LinearOrder K₂] [IsStrictOrderedRing K₂]
    (hIVT₁ : ∀ (p : Polynomial K₁) {a b : K₁}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₁, a < c ∧ c < b ∧ p.eval c = 0)
    (hIVT₂ : ∀ (p : Polynomial K₂) {a b : K₂}, a < b → p.eval a < 0 → 0 < p.eval b →
      ∃ c : K₂, a < c ∧ c < b ∧ p.eval c = 0)
    (hMVT₁ : ∀ (p : Polynomial K₁) {u v : K₁}, u < v →
      ∃ c : K₁, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hMVT₂ : ∀ (p : Polynomial K₂) {u v : K₂}, u < v →
      ∃ c : K₂, u < c ∧ c < v ∧ p.eval v - p.eval u = (v - u) * p.derivative.eval c)
    (hAsymp₁ : ∀ (p : Polynomial K₁), p ≠ 0 →
      ∃ M : K₁, ∀ x : K₁, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (hAsymp₂ : ∀ (p : Polynomial K₂), p ≠ 0 →
      ∃ M : K₂, ∀ x : K₂, M < x →
        (0 < p.eval x ↔ 0 < p.leadingCoeff) ∧ (p.eval x < 0 ↔ p.leadingCoeff < 0))
    (φ₁ : A →+* K₁) :
    ∀ (d c : ℕ) (P : List (Polynomial A)),
      (∀ p ∈ P, p ≠ 0 ∧ φ₁ p.leadingCoeff ≠ 0) →
      (∀ p ∈ P, p.natDegree ≤ d) →
      P.countP (fun p => decide (p.natDegree = d)) ≤ c →
      ∃ Q : List A, ∀ (φ₂ : A →+* K₂),
        (∀ r ∈ Q, sameSign (φ₁ r) (φ₂ r)) →
        SignTableMatch φ₁ φ₂ P := by
  classical
  intro d
  induction d with
  | zero =>
    intro c P hvalid hdeg _
    refine ⟨P.map Polynomial.leadingCoeff, fun φ₂ hQ => ?_⟩
    have hR₁_nil : rootList (P.map (Polynomial.map φ₁)) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      rw [mem_rootList] at hx
      obtain ⟨pK, hpK, hpK0, hpKx⟩ := hx
      rw [List.mem_map] at hpK
      obtain ⟨p, hpP, rfl⟩ := hpK
      have hp0 : p.natDegree = 0 := Nat.le_zero.mp (hdeg p hpP)
      have hpC : p = Polynomial.C p.leadingCoeff := by
        simpa [Polynomial.leadingCoeff, hp0] using Polynomial.eq_C_of_natDegree_eq_zero hp0
      rw [hpC, Polynomial.map_C, Polynomial.eval_C] at hpKx
      exact (hvalid p hpP).2 hpKx
    have hR₂_nil : rootList (P.map (Polynomial.map φ₂)) = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro x hx
      rw [mem_rootList] at hx
      obtain ⟨pK, hpK, hpK0, hpKx⟩ := hx
      rw [List.mem_map] at hpK
      obtain ⟨p, hpP, rfl⟩ := hpK
      have hp0 : p.natDegree = 0 := Nat.le_zero.mp (hdeg p hpP)
      have hpC : p = Polynomial.C p.leadingCoeff := by
        simpa [Polynomial.leadingCoeff, hp0] using Polynomial.eq_C_of_natDegree_eq_zero hp0
      rw [hpC, Polynomial.map_C, Polynomial.eval_C] at hpKx
      have hss := hQ p.leadingCoeff (List.mem_map_of_mem hpP)
      exact (hvalid p hpP).2 (hss.2.mpr hpKx)
    refine ⟨by simp [hR₁_nil, hR₂_nil], fun i hi₁ => by rw [hR₁_nil] at hi₁; simp at hi₁, ?_⟩
    intro j x₁ x₂ _ _ _ p hpP
    have hp0 : p.natDegree = 0 := Nat.le_zero.mp (hdeg p hpP)
    have hpC : p = Polynomial.C p.leadingCoeff := by
      simpa [Polynomial.leadingCoeff, hp0] using Polynomial.eq_C_of_natDegree_eq_zero hp0
    rw [hpC, Polynomial.map_C, Polynomial.eval_C, Polynomial.map_C, Polynomial.eval_C]
    exact hQ p.leadingCoeff (List.mem_map_of_mem hpP)
  | succ d ih_d =>
    intro c
    induction c with
    | zero =>
      intro P hvalid hdeg hcnt
      have hdeg' : ∀ p ∈ P, p.natDegree ≤ d := by
        intro p hp
        have hle := hdeg p hp
        have hne : p.natDegree ≠ d + 1 := by
          intro heq
          have hpos : 0 < P.countP (fun q => decide (q.natDegree = d + 1)) :=
            List.countP_pos_iff.mpr ⟨p, hp, by simp [heq]⟩
          omega
        omega
      exact ih_d P.length P hvalid hdeg' (List.countP_le_length)
    | succ c ih_c =>
      intro P hvalid hdeg hcnt
      by_cases hle_c : P.countP (fun p => decide (p.natDegree = d + 1)) ≤ c
      · exact ih_c P hvalid hdeg hle_c
      · have hpos_cnt : 0 < P.countP (fun p => decide (p.natDegree = d + 1)) := by omega
        obtain ⟨f, hfP, hfd⟩ := List.countP_pos_iff.mp hpos_cnt
        simp only [decide_eq_true_eq] at hfd
        obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hfP
        set P_rest := L₁ ++ L₂
        have hf_valid := hvalid f (by simp)
        have hderiv_coeff : f.derivative.coeff d = f.leadingCoeff * ((d + 1 : ℕ) : A) := by
          rw [Polynomial.coeff_derivative, Polynomial.leadingCoeff, hfd]
          push_cast
          ring
        have hderiv_phi_coeff : φ₁ (f.derivative.coeff d) ≠ 0 := by
          rw [hderiv_coeff, map_mul, map_natCast]
          exact mul_ne_zero hf_valid.2 (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d))
        have hderiv_le : f.derivative.natDegree ≤ d := by
          have := Polynomial.natDegree_derivative_le f
          omega
        have hderiv_deg : f.derivative.natDegree = d :=
          le_antisymm hderiv_le (Polynomial.le_natDegree_of_ne_zero (fun hc => hderiv_phi_coeff (by simp [hc])))
        have hderiv_ne : f.derivative ≠ 0 := fun h0 => hderiv_phi_coeff (by simp [h0])
        have hderiv_lc : φ₁ f.derivative.leadingCoeff ≠ 0 := by
          rwa [Polynomial.leadingCoeff, hderiv_deg]
        set P₁ := P_rest ++ [f.derivative]
        have hP₁_valid : ∀ g ∈ P₁, g ≠ 0 ∧ φ₁ g.leadingCoeff ≠ 0 := by
          intro g hg
          simp only [P₁, List.mem_append, List.mem_singleton] at hg
          rcases hg with hg | rfl
          · have : g ∈ L₁ ++ f :: L₂ := by
              simp only [P_rest, List.mem_append] at hg
              rcases hg with h1 | h2
              · exact List.mem_append_left _ h1
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
            exact hvalid g this
          · exact ⟨hderiv_ne, hderiv_lc⟩
        set P_rem := P₁.map (prem f)
        set sr := stripList φ₁ P_rem
        set P_rem' := sr.1
        set Q_rem := sr.2
        have hsr := stripList_spec (K₂ := K₂) φ₁ P_rem
        set P_sub := P₁ ++ P_rem'
        have hP_rem_deg : ∀ r ∈ P_rem, r.natDegree ≤ d := by
          intro r hr
          rw [List.mem_map] at hr
          obtain ⟨g, hgP₁, rfl⟩ := hr
          rcases prem_deg (f := f) (hP₁_valid g hgP₁).1 with h0 | hlt
          · rw [h0, Polynomial.natDegree_zero]; exact Nat.zero_le d
          · have hg_le : g.natDegree ≤ d + 1 := by
              simp only [P₁, List.mem_append, List.mem_singleton] at hgP₁
              rcases hgP₁ with hg | rfl
              · exact hdeg g (by
                  simp only [P_rest, List.mem_append] at hg
                  rcases hg with h1 | h2
                  · exact List.mem_append_left _ h1
                  · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2))
              · omega
            omega
        have hP_rem'_deg : ∀ r ∈ P_rem', r.natDegree ≤ d := hsr.2.1 d hP_rem_deg
        have hP_sub_valid : ∀ p ∈ P_sub, p ≠ 0 ∧ φ₁ p.leadingCoeff ≠ 0 := by
          intro p hp
          simp only [P_sub, List.mem_append] at hp
          rcases hp with hp | hp
          · exact hP₁_valid p hp
          · have := hsr.1 p hp
            exact ⟨this.1, this.2.1⟩
        have hP_sub_deg : ∀ p ∈ P_sub, p.natDegree ≤ d + 1 := by
          intro p hp
          simp only [P_sub, List.mem_append] at hp
          rcases hp with hp | hp
          · simp only [P₁, List.mem_append, List.mem_singleton] at hp
            rcases hp with hp | rfl
            · exact hdeg p (by
                simp only [P_rest, List.mem_append] at hp
                rcases hp with h1 | h2
                · exact List.mem_append_left _ h1
                · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2))
            · omega
          · exact Nat.le_succ_of_le (hP_rem'_deg p hp)
        have hP_sub_cnt : P_sub.countP (fun p => decide (p.natDegree = d + 1)) ≤ c := by
          have hP_rem'_cnt : P_rem'.countP (fun p => decide (p.natDegree = d + 1)) = 0 := by
            rw [List.countP_eq_zero]
            intro p hp
            have := hP_rem'_deg p hp
            simp only [decide_eq_true_eq]
            omega
          have hP_rest_cnt : P_rest.countP (fun p => decide (p.natDegree = d + 1)) ≤ c := by
            have htot : (L₁ ++ f :: L₂).countP (fun p => decide (p.natDegree = d + 1)) =
                P_rest.countP (fun p => decide (p.natDegree = d + 1)) + 1 := by
              simp only [P_rest, List.countP_append, List.countP_cons, hfd, decide_true, ↓reduceIte]
              omega
            omega
          have hP₁_cnt : P₁.countP (fun p => decide (p.natDegree = d + 1)) =
              P_rest.countP (fun p => decide (p.natDegree = d + 1)) := by
            simp only [P₁, List.countP_append, List.countP_cons, List.countP_nil, hderiv_deg]
            simp
          rw [List.countP_append, hP₁_cnt, hP_rem'_cnt, add_zero]
          exact hP_rest_cnt
        obtain ⟨Q_sub, hQ_sub⟩ := ih_c P_sub hP_sub_valid hP_sub_deg hP_sub_cnt
        refine ⟨f.leadingCoeff :: P₁.map Polynomial.leadingCoeff ++ Q_rem ++ Q_sub, fun φ₂ hQ => ?_⟩
        have hQ_sub_ok : ∀ r ∈ Q_sub, sameSign (φ₁ r) (φ₂ r) :=
          fun r hr => hQ r (by simp [hr])
        have hQ_rem_ok : ∀ r ∈ Q_rem, φ₁ r = 0 ↔ φ₂ r = 0 :=
          fun r hr => (hQ r (by simp [hr])).2
        have hST_sub : SignTableMatch φ₁ φ₂ P_sub := hQ_sub φ₂ hQ_sub_ok
        obtain ⟨hST₁, hR₁_extra⟩ := filterSignTable_extra hIVT₁ hIVT₂
          (P := P₁) (P' := P_sub) (fun p hp => List.mem_append_left _ hp) hST_sub
        have hlead_f : sameSign (φ₁ f.leadingCoeff) (φ₂ f.leadingCoeff) := hQ f.leadingCoeff (by simp)
        have hlead_P₁ : ∀ g ∈ P₁, sameSign (φ₁ g.leadingCoeff) (φ₂ g.leadingCoeff) :=
          fun g hg => hQ g.leadingCoeff (by simp [List.mem_map_of_mem hg])
        have hprem_ok : ∀ g ∈ P₁, ∀ (i : ℕ) (h₁ : i < (rootList (P₁.map (Polynomial.map φ₁))).length)
            (h₂ : i < (rootList (P₁.map (Polynomial.map φ₂))).length),
            (g.map φ₁).eval (rootList (P₁.map (Polynomial.map φ₁)))[i] = 0 →
            sameSign (((prem f g).map φ₁).eval (rootList (P₁.map (Polynomial.map φ₁)))[i])
                     (((prem f g).map φ₂).eval (rootList (P₁.map (Polynomial.map φ₂)))[i]) := by
          intro g hg i hi₁ hi₂ _
          have hmem : prem f g ∈ P_rem := List.mem_map_of_mem hg
          rcases hsr.2.2.2 φ₂ hQ_rem_ok (prem f g) hmem with ⟨hz1, hz2⟩ | ⟨r', hr', hm1, hm2⟩
          · rw [hz1, hz2, Polynomial.eval_zero, Polynomial.eval_zero]
            exact sameSign_zero
          · rw [← hm1, ← hm2]
            exact hR₁_extra i hi₁ hi₂ r' (List.mem_append_right _ hr')
        have hST_full : SignTableMatch φ₁ φ₂ (P₁ ++ [f]) :=
          addPolySignTable hIVT₁ hIVT₂ hMVT₁ hMVT₂ hAsymp₁ hAsymp₂
            hf_valid.2 (by simp [P₁]) hP₁_valid hlead_f hlead_P₁ hST₁ hprem_ok
        refine (filterSignTable_extra hIVT₁ hIVT₂ (P := L₁ ++ f :: L₂) (P' := P₁ ++ [f]) ?_ hST_full).1
        intro p hp
        simp only [P₁, P_rest, List.mem_append, List.mem_singleton] at hp ⊢
        rcases hp with hp | hp
        · exact Or.inl (Or.inl (Or.inl hp))
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact Or.inr rfl
          · exact Or.inl (Or.inl (Or.inr hp))

end MainInduction

end Hilbert17H3Proof

theorem solve : OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1.H3 := by
  intro A K₁ K₂ _ _ _ _ _ _ _ hIVT₁ hIVT₂ hMVT₁ hMVT₂ hAsymp₁ hAsymp₂ φ₁ P
  set sr := Hilbert17H3Proof.stripList φ₁ P
  set P' := sr.1
  set Q₀ := sr.2
  have hsr := Hilbert17H3Proof.stripList_spec (K₂ := K₂) φ₁ P
  set d := P'.foldl (fun acc p => max acc p.natDegree) 0
  have hdeg : ∀ p ∈ P', p.natDegree ≤ d := by
    have hfold : ∀ (l : List (Polynomial A)) (init : ℕ),
        (∀ p ∈ l, p.natDegree ≤ l.foldl (fun acc p => max acc p.natDegree) init) ∧
        init ≤ l.foldl (fun acc p => max acc p.natDegree) init := by
      intro l
      induction l with
      | nil => intro init; exact ⟨fun _ h => by simp at h, le_rfl⟩
      | cons a t ih =>
        intro init
        rw [List.foldl_cons]
        obtain ⟨ih1, ih2⟩ := ih (max init a.natDegree)
        refine ⟨fun p hp => ?_, le_trans (le_max_left _ _) ih2⟩
        rcases List.mem_cons.mp hp with rfl | hpt
        · exact le_trans (le_max_right _ _) ih2
        · exact ih1 p hpt
    exact (hfold P' 0).1
  have hvalid : ∀ p ∈ P', p ≠ 0 ∧ φ₁ p.leadingCoeff ≠ 0 :=
    fun p hp => ⟨(hsr.1 p hp).1, (hsr.1 p hp).2.1⟩
  obtain ⟨Q₁, hQ₁⟩ := Hilbert17H3Proof.signTableMatch_exists
    hIVT₁ hIVT₂ hMVT₁ hMVT₂ hAsymp₁ hAsymp₂ φ₁ d P'.length P' hvalid hdeg List.countP_le_length
  refine ⟨Q₀ ++ Q₁, fun φ₂ hQ t₁ => ?_⟩
  have hQ₀_ok : ∀ r ∈ Q₀, φ₁ r = 0 ↔ φ₂ r = 0 :=
    fun r hr => (hQ r (List.mem_append_left _ hr)).2
  have hQ₁_ok : ∀ r ∈ Q₁, Hilbert17H3Proof.sameSign (φ₁ r) (φ₂ r) :=
    fun r hr => hQ r (List.mem_append_right _ hr)
  have hST : Hilbert17H3Proof.SignTableMatch φ₁ φ₂ P' := hQ₁ φ₂ hQ₁_ok
  set R₁ := Hilbert17H3Proof.rootList (P'.map (Polynomial.map φ₁))
  set R₂ := Hilbert17H3Proof.rootList (P'.map (Polynomial.map φ₂))
  have hR₁ : R₁.Pairwise (· < ·) := Hilbert17H3Proof.rootList_pairwise_lt _
  have hR₂ : R₂.Pairwise (· < ·) := Hilbert17H3Proof.rootList_pairwise_lt _
  by_cases ht₁ : t₁ ∈ R₁
  · obtain ⟨i, hi₁, rfl⟩ := List.mem_iff_getElem.mp ht₁
    have hi₂ : i < R₂.length := hST.1 ▸ hi₁
    refine ⟨R₂[i], fun p hp => ?_⟩
    rcases hsr.2.2.2 φ₂ hQ₀_ok p hp with ⟨hz1, hz2⟩ | ⟨p', hp', hm1, hm2⟩
    · rw [hz1, hz2, Polynomial.eval_zero, Polynomial.eval_zero]
      exact ⟨by simp, by simp⟩
    · rw [← hm1, ← hm2]
      exact hST.2.1 i hi₁ hi₂ p' hp'
  · obtain ⟨j, hj₁, hj_in⟩ := Hilbert17H3Proof.exists_inCell_of_not_mem hR₁ ht₁
    have hj₂ : j ≤ R₂.length := hST.1 ▸ hj₁
    obtain ⟨t₂, ht₂⟩ := Hilbert17H3Proof.exists_point_inCell hR₂ hj₂
    refine ⟨t₂, fun p hp => ?_⟩
    rcases hsr.2.2.2 φ₂ hQ₀_ok p hp with ⟨hz1, hz2⟩ | ⟨p', hp', hm1, hm2⟩
    · rw [hz1, hz2, Polynomial.eval_zero, Polynomial.eval_zero]
      exact ⟨by simp, by simp⟩
    · rw [← hm1, ← hm2]
      exact hST.2.2 j t₁ t₂ hj₁ hj_in ht₂ p' hp'


end OMA.Leaf5
end Leaf5

theorem OMA.solution : type_of% @Hilbert17.hilbert_17th_problem :=
  OMA.R_Hilbert17_hilbert_17th_problem_R1.main
    OMA.Leaf1.solve OMA.Leaf2.solve
    (OMA.R_Hilbert17_hilbert_17th_problem_R1_H3_R1.main OMA.Leaf3.solve OMA.Leaf4.solve OMA.Leaf5.solve)
