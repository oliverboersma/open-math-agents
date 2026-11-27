import FormalConjectures.ErdosProblems.«210»
import Mathlib

/-!
# Csima–Sawyer bound for ordinary lines (Erdős Problem 210)

Proves `Erdos210.erdos_210.variants.csima_sawyer`: every non-collinear set of `n ≥ 8`
points in `ℝ²` determines at least `⌈6n/13⌉` ordinary lines (`6 * n ≤ 13 * Erdos210.f n`).

Assembled from:
- Attachment reduction, two-pencil case, and four-attachment lemma (`H2`): Credit `@dk8827`
  (`reductions/Erdos210.erdos_210.variants.csima_sawyer.R1.lean`,
   `reductions/Erdos210.erdos_210.variants.csima_sawyer.R1.H1.R1.lean`,
   `proofs/Erdos210.erdos_210.variants.csima_sawyer.R1.H2.lean`).
- Adjacent type-(2, 0) exclusion (`H3`): Credit `@sobrien032`
  (`proofs/Erdos210.erdos_210.variants.csima_sawyer.R1.H3.lean`).
- Kelly–Moser local attachment bounds (`d w = 0 → 3 ≤ A w` and `d w = 1 → 2 ≤ A w`) via
  2D polar duality centered at `w` and strictly exposed dual vertices (`Erdos210KM`).
-/

section

/-
# The Csima–Sawyer bound via attachments

Use a homogeneous normal `(x, y, 1)` for the projective dual of each point.
An attachment corresponds to a triangular cell: after choosing signs for
the three boundary normals, every other normal lies in their positive cone
or its negative. H1 is the local Kelly–Moser attachment bound (including
the two-pencil case). H2 is the four-attachment bound. H3 excludes adjacent
type (2, 0) lines for arrangements of at least eight lines.
See Jonathan Lenchner, IBM Research Report RC24181, Lemmas 1, 4, 5 and 10.
-/

-- Credit: @dk8827

open EuclideanGeometry Finset
open scoped BigOperators Classical

namespace OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1

private theorem incidence_sum {P Q : Type} (s : Finset P) (t : Finset Q) (I : P → Q → Prop) :
    (∑ p ∈ s, (t.filter (I p)).card) = ∑ q ∈ t, (s.filter (fun p => I p q)).card := by
  classical
  simp only [Finset.card_filter]
  exact Finset.sum_comm

def H1 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  s.card ≤ 2 * O.card ∨
    ∀ p ∈ s, 3 ≤ d p + A p ∨ (d p = 2 ∧ A p = 0)

def H2 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  let O := ordinaryLines s
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  ∀ L ∈ O, (s.filter (fun p => attached p L)).card ≤ 4

def H3 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  ∀ L ∈ O, ∀ p ∈ s, ∀ q ∈ s, p ∈ L → q ∈ L →
    d p = 2 → A p = 0 → d q = 2 → A q = 0 → p = q

set_option maxHeartbeats 900000 in
theorem main : H1 → H2 → H3 → type_of% @Erdos210.erdos_210.variants.csima_sawyer := by
  classical
  intro hlocal hcapacity hseparate n hn
  obtain ⟨s, hs, hcol, hmin⟩ := Erdos210.f_attained (by omega : 3 ≤ n)
  have hsize : 8 ≤ s.card := hs.symm ▸ hn
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  have hd : (∑ p ∈ s, d p) = 2 * O.card := by
    unfold d
    rw [incidence_sum s O (fun p L => p ∈ L)]
    calc
      _ = ∑ _L ∈ O, (2 : ℕ) := sum_congr rfl (fun _L hL => (mem_ordinaryLines.1 hL).2)
      _ = _ := by simp [mul_comm]
  have ha : (∑ p ∈ s, A p) ≤ 4 * O.card := by
    calc
      _ = ∑ p ∈ s, ∑ L ∈ O, (if attached p L then 1 else 0 : ℕ) := by
        apply sum_congr rfl
        intro p _
        exact Finset.card_filter (attached p) O
      _ = ∑ L ∈ O, ∑ p ∈ s, (if attached p L then 1 else 0 : ℕ) := Finset.sum_comm
      _ = ∑ L ∈ O, (s.filter (fun p => attached p L)).card := by
        apply sum_congr rfl
        intro L _
        exact (Finset.card_filter (fun p => attached p L) s).symm
      _ ≤ ∑ _L ∈ O, (4 : ℕ) := sum_le_sum (hcapacity s hsize hcol)
      _ = _ := by simp [mul_comm]
  change O.card = Erdos210.f n at hmin
  rcases hlocal s hsize hcol with hbig | hprofile
  · change s.card ≤ 2 * O.card at hbig
    omega
  let bad := s.filter (fun p => d p = 2 ∧ A p = 0)
  have hbad (L : AffineSubspace ℝ ℝ²) (hL : L ∈ O) :
      (bad.filter (fun p => p ∈ L)).card ≤ 1 := by
    apply card_le_one.2
    intro p hp q hq
    obtain ⟨hp, hpL⟩ := mem_filter.1 hp
    obtain ⟨hq, hqL⟩ := mem_filter.1 hq
    obtain ⟨hps, hpd, hpa⟩ := mem_filter.1 hp
    obtain ⟨hqs, hqd, hqa⟩ := mem_filter.1 hq
    exact hseparate s hsize hcol L hL p hps q hqs hpL hqL hpd hpa hqd hqa
  have hcount_bad : 2 * bad.card ≤ O.card := by
    calc
      _ = ∑ p ∈ bad, d p := by
        rw [show (∑ p ∈ bad, d p) = ∑ _p ∈ bad, (2 : ℕ) from
          sum_congr rfl (fun _p hp => (mem_filter.1 hp).2.1)]
        simp [mul_comm]
      _ = ∑ L ∈ O, (bad.filter (fun p => p ∈ L)).card :=
        incidence_sum bad O (fun p L => p ∈ L)
      _ ≤ ∑ _L ∈ O, (1 : ℕ) := sum_le_sum hbad
      _ = _ := by simp
  have htotal : 3 * s.card ≤ (∑ p ∈ s, d p) + (∑ p ∈ s, A p) + bad.card := by
    calc
      _ = ∑ _p ∈ s, (3 : ℕ) := by simp [mul_comm]
      _ ≤ ∑ p ∈ s, (d p + A p + if d p = 2 ∧ A p = 0 then 1 else 0) := by
        apply sum_le_sum
        intro p hp
        rcases hprofile p hp with h | h
        · exact h.trans (Nat.le_add_right _ _)
        · change d p = 2 ∧ A p = 0 at h
          simp [h]
      _ = _ := by
        simp only [sum_add_distrib]
        rw [← Finset.card_filter]
  omega

end OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1

end

section

/-
The two-pencil case is counted by pairs from the exclusive parts of
the two covering lines. The remaining local inequalities are the two
Kelly–Moser attachment lemmas, restated in Lenchner, CCCG 2005, §2.
-/

-- Credit: @dk8827

open EuclideanGeometry Finset
open scoped Pointwise BigOperators Classical

namespace OMA.TwoPencils

private theorem generated {L : AffineSubspace ℝ ℝ²}
    (hL : Module.finrank ℝ L.direction = 1) {a b : ℝ²}
    (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) : line[ℝ, a, b] = L := by
  apply (AffineSubspace.eq_iff_direction_eq_of_mem
    (left_mem_affineSpan_pair ℝ a b) ha).2
  apply Submodule.eq_of_le_of_finrank_eq
  · exact AffineSubspace.direction_le (affineSpan_pair_le_of_mem_of_mem ha hb)
  · rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hab)]
    exact hL.symm

private theorem collinear_subset {s : Set ℝ²} {L : AffineSubspace ℝ ℝ²}
    (hL : Module.finrank ℝ L.direction = 1) (hs : s ⊆ L) : Collinear ℝ s := by
  rw [collinear_iff_finrank_le_one]
  have hle : vectorSpan ℝ s ≤ L.direction := by
    rw [← direction_affineSpan]
    exact AffineSubspace.direction_le (affineSpan_le.2 hs)
  exact (Submodule.finrank_mono hle).trans hL.le

theorem count (s : Finset ℝ²) (hs : 4 ≤ s.card) (hc : ¬ Collinear ℝ (s : Set ℝ²))
    (L M : AffineSubspace ℝ ℝ²) (hL : Module.finrank ℝ L.direction = 1)
    (hM : Module.finrank ℝ M.direction = 1) (hcov : ∀ p ∈ s, p ∈ L ∨ p ∈ M) :
    s.card ≤ 2 * (ordinaryLines s).card := by
  classical
  let A := s.filter (fun p => p ∈ L ∧ p ∉ M)
  let B := s.filter (fun p => p ∈ M ∧ p ∉ L)
  let I := s.filter (fun p => p ∈ L ∧ p ∈ M)
  have hLM : L ≠ M := by
    rintro rfl
    exact hc (collinear_subset hL (fun p hp => (hcov p hp).elim id id))
  have hA : A.Nonempty := by
    by_contra h
    apply hc (collinear_subset hM ?_)
    intro p hp
    by_contra hpm
    have hpl := (hcov p hp).resolve_right hpm
    exact h ⟨p, mem_filter.2 ⟨hp, hpl, hpm⟩⟩
  have hB : B.Nonempty := by
    by_contra h
    apply hc (collinear_subset hL ?_)
    intro p hp
    by_contra hpl
    have hpm := (hcov p hp).resolve_left hpl
    exact h ⟨p, mem_filter.2 ⟨hp, hpm, hpl⟩⟩
  have hI : I.card ≤ 1 := by
    apply card_le_one.2
    intro a ha b hb
    by_contra h
    obtain ⟨_, haL, haM⟩ := mem_filter.1 ha
    obtain ⟨_, hbL, hbM⟩ := mem_filter.1 hb
    exact hLM ((generated hL haL hbL h).symm.trans (generated hM haM hbM h))
  have hcard : s.card ≤ A.card + B.card + 1 := by
    have hsub : s ⊆ A ∪ B ∪ I := by
      intro p hp
      by_cases hpL : p ∈ L <;> by_cases hpM : p ∈ M
      · exact mem_union_right _ (mem_filter.2 ⟨hp, hpL, hpM⟩)
      · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hp, hpL, hpM⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hp, hpM, hpL⟩))
      · exact ((hcov p hp).elim hpL hpM).elim
    have h₁ := card_le_card hsub
    have h₂ := card_union_le (A ∪ B) I
    have h₃ := card_union_le A B
    omega
  have hcut (a b : ℝ²) (ha : a ∈ A) (hb : b ∈ B) :
      s.filter (fun p => p ∈ line[ℝ, a, b]) = {a, b} := by
    obtain ⟨has, haL, haM⟩ := mem_filter.1 ha
    obtain ⟨hbs, hbM, hbL⟩ := mem_filter.1 hb
    have hab : a ≠ b := fun h => hbL (h ▸ haL)
    let N : AffineSubspace ℝ ℝ² := line[ℝ, a, b]
    have haN : a ∈ N := left_mem_affineSpan_pair ℝ a b
    have hbN : b ∈ N := right_mem_affineSpan_pair ℝ a b
    have hN : Module.finrank ℝ N.direction = 1 := by
      rw [show N = line[ℝ, a, b] from rfl, direction_affineSpan, vectorSpan_pair,
        finrank_span_singleton (vsub_ne_zero.mpr hab)]
    ext z
    constructor
    · intro hz
      obtain ⟨hzs, hzN⟩ := mem_filter.1 hz
      rcases hcov z hzs with hzL | hzM
      · have hza : z = a := by
          by_contra hh
          have he := (generated hN hzN haN hh).symm.trans (generated hL hzL haL hh)
          exact hbL (he ▸ hbN)
        simp [hza]
      · have hzb : z = b := by
          by_contra hh
          have he := (generated hN hzN hbN hh).symm.trans (generated hM hzM hbM hh)
          exact haM (he ▸ haN)
        simp [hzb]
    · intro hz
      rcases mem_insert.1 hz with rfl | hz
      · exact mem_filter.2 ⟨has, haN⟩
      · obtain rfl := mem_singleton.1 hz
        exact mem_filter.2 ⟨hbs, hbN⟩
  have hcross : A.card * B.card ≤ (ordinaryLines s).card := by
    rw [← card_product]
    apply card_le_card_of_injOn (fun z : ℝ² × ℝ² => line[ℝ, z.1, z.2])
    · rintro ⟨a, b⟩ h
      obtain ⟨ha, hb⟩ := mem_product.1 h
      obtain ⟨has, haL, _⟩ := mem_filter.1 ha
      obtain ⟨hbs, _, hbL⟩ := mem_filter.1 hb
      have hab : a ≠ b := fun he => hbL (he ▸ haL)
      exact mem_ordinaryLines.2 ⟨⟨a, has, b, hbs, hab, rfl⟩, by rw [hcut a b ha hb]; simp [hab]⟩
    · rintro ⟨a, b⟩ h ⟨c, d⟩ h' he
      obtain ⟨ha, hb⟩ := mem_product.1 h
      obtain ⟨hc, hd⟩ := mem_product.1 h'
      change line[ℝ, a, b] = line[ℝ, c, d] at he
      have habcd : ({a, b} : Finset ℝ²) = {c, d} := by
        rw [← hcut a b ha hb, ← hcut c d hc hd, he]
      have hca : a = c := by
        have hm : a ∈ ({c, d} : Finset ℝ²) := habcd ▸ by simp
        have hmem := mem_insert.1 hm
        refine hmem.resolve_right ?_
        intro had
        exact (mem_filter.1 hd).2.2 ((mem_singleton.1 had) ▸ (mem_filter.1 ha).2.1)
      have hdb : b = d := by
        have hm : b ∈ ({c, d} : Finset ℝ²) := habcd ▸ by simp
        have hmem := mem_insert.1 hm
        refine mem_singleton.1 (hmem.resolve_left ?_)
        intro hbc
        exact (mem_filter.1 hc).2.2 (hbc ▸ (mem_filter.1 hb).2.1)
      exact Prod.ext hca hdb
  have hA0 := card_pos.2 hA
  have hB0 := card_pos.2 hB
  have hsizes : A.card + B.card ≤ A.card * B.card + 1 := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero hA0.ne'
    obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hB0.ne'
    rw [ha, hb, Nat.succ_mul, Nat.mul_succ]
    omega
  omega

end OMA.TwoPencils

namespace OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1_H1_R1

def H1 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
    Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M) →
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  ∀ p ∈ s, d p = 0 → 3 ≤ A p

def H2 : Prop :=
  ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
  ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
    Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M) →
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  ∀ p ∈ s, d p = 1 → 2 ≤ A p

theorem main : H1 → H2 → OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1.H1 := by
  classical
  intro zero one s hs hcol
  let O := ordinaryLines s
  let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
  let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
  let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
  let A := fun p => (O.filter (attached p)).card
  change s.card ≤ 2 * O.card ∨
    ∀ p ∈ s, 3 ≤ d p + A p ∨ (d p = 2 ∧ A p = 0)
  by_cases hcover : ∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M
  · obtain ⟨L, M, hL, hM, hcov⟩ := hcover
    exact Or.inl (OMA.TwoPencils.count s (by omega) hcol L M hL hM hcov)
  · right
    intro p hp
    by_cases hd₀ : d p = 0
    · have hA : 3 ≤ A p := zero s hs hcol hcover p hp hd₀
      omega
    by_cases hd₁ : d p = 1
    · have hA : 2 ≤ A p := one s hs hcol hcover p hp hd₁
      omega
    omega

end OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1_H1_R1

end

section

/-
Algebraic form of the four-attachment lemma. At an ordinary point in the
dual arrangement, the two signed boundary coordinates and height determine
the incident sector up to an overall sign. Two triangular cells in the same
sector would force each third normal into the other's signed cone, so the
two third normals are proportional and determine the same line.
See Jonathan Lenchner, IBM Research Report RC24181, Lemma 1.
-/

-- Credit: @dk8827

open EuclideanGeometry Finset
open scoped BigOperators Classical

namespace OMA.OrdinaryAttachment

private abbrev HVec := Fin 3 → ℝ

private def homogeneous (p : ℝ²) : HVec := ![p 0, p 1, 1]

private def height (p q : ℝ²) : HVec →ₗ[ℝ] ℝ where
  toFun v := (q 0 - p 0) * (v 1 - p 1 * v 2) - (q 1 - p 1) * (v 0 - p 0 * v 2)
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem hp_height (p q : ℝ²) : height p q (homogeneous p) = 0 := by
  simp [height, homogeneous]

private theorem hq_height (p q : ℝ²) : height p q (homogeneous q) = 0 := by
  simp [height, homogeneous]
  ring

private theorem point_eq {p q : ℝ²} (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) : p = q := by
  ext i
  fin_cases i
  · exact h₀
  · exact h₁

private theorem height_ne_zero {p q w : ℝ²} (hpq : p ≠ q)
    (hw : w ∉ line[ℝ, p, q]) : height p q (homogeneous w) ≠ 0 := by
  intro h
  apply hw
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.2
  have hh : (q 0 - p 0) * (w 1 - p 1) = (q 1 - p 1) * (w 0 - p 0) := by
    simpa [height, homogeneous, sub_eq_zero] using h
  by_cases h₀ : p 0 = q 0
  · have h₁ : q 1 - p 1 ≠ 0 := fun hz => hpq (point_eq h₀ (sub_eq_zero.1 hz).symm)
    have hw₀ : w 0 = p 0 := by
      have he : (q 1 - p 1) * (w 0 - p 0) = 0 := by simpa [h₀] using hh.symm
      exact sub_eq_zero.1 ((mul_eq_zero.1 he).resolve_left h₁)
    let t := (w 1 - p 1) / (q 1 - p 1)
    refine ⟨t, point_eq ?_ ?_⟩
    · rw [AffineMap.lineMap_apply_module']
      change t * (q 0 - p 0) + p 0 = w 0
      simp [h₀, hw₀]
    · rw [AffineMap.lineMap_apply_module']
      change ((w 1 - p 1) / (q 1 - p 1)) * (q 1 - p 1) + p 1 = w 1
      rw [div_mul_cancel₀ _ h₁, sub_add_cancel]
  · have h₀' : q 0 - p 0 ≠ 0 := sub_ne_zero.2 (Ne.symm h₀)
    let t := (w 0 - p 0) / (q 0 - p 0)
    refine ⟨t, point_eq ?_ ?_⟩
    · rw [AffineMap.lineMap_apply_module']
      change ((w 0 - p 0) / (q 0 - p 0)) * (q 0 - p 0) + p 0 = w 0
      rw [div_mul_cancel₀ _ h₀', sub_add_cancel]
    · rw [AffineMap.lineMap_apply_module']
      change ((w 0 - p 0) / (q 0 - p 0)) * (q 1 - p 1) + p 1 = w 1
      have hw₁ : ((w 0 - p 0) / (q 0 - p 0)) * (q 1 - p 1) = w 1 - p 1 := by
        apply (mul_right_cancel₀ h₀')
        calc
          _ = (q 1 - p 1) * (w 0 - p 0) := by
            rw [mul_right_comm, div_mul_cancel₀ _ h₀', mul_comm]
          _ = _ := by rw [← hh, mul_comm]
      rw [hw₁, sub_add_cancel]

private theorem pair_coeff {p q : ℝ²} (hpq : p ≠ q) {a b : ℝ}
    (h : a • homogeneous p + b • homogeneous q = 0) : a = 0 ∧ b = 0 := by
  have h2 : a + b = 0 := by simpa [homogeneous] using congrFun h 2
  have key (i : Fin 2) : b * (q i - p i) = 0 := by
    have hi : a * p i + b * q i = 0 := by
      fin_cases i
      · simpa [homogeneous] using congrFun h 0
      · simpa [homogeneous] using congrFun h 1
    linear_combination hi - (p i) * h2
  have hb : b = 0 := by
    by_contra hb
    exact hpq (point_eq ((sub_eq_zero.1 ((mul_eq_zero.1 (key 0)).resolve_left hb)).symm)
      ((sub_eq_zero.1 ((mul_eq_zero.1 (key 1)).resolve_left hb)).symm))
  exact ⟨by simpa [hb] using h2, hb⟩

private theorem sign_cases {a : ℝ} (ha : a ^ 2 = 1) : a = 1 ∨ a = -1 := by
  have hz : (a - 1) * (a + 1) = 0 := by nlinarith only [ha]
  rcases mul_eq_zero.1 hz with h | h
  · exact Or.inl (by linarith only [h])
  · exact Or.inr (by linarith only [h])

private theorem orient_nonneg {p q w z : ℝ²} {ε δ δ' : ℝ}
    (hδ' : δ' ^ 2 = 1)
    (hsign : (δ' * height p q (homogeneous z)) * (δ * height p q (homogeneous w)) > 0)
    (hex : ∃ a b c : ℝ,
      homogeneous z = a • homogeneous p + b • (ε • homogeneous q) + c • (δ • homogeneous w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))) :
    ∃ a b c : ℝ, δ' • homogeneous z =
      a • homogeneous p + b • (ε • homogeneous q) + c • (δ • homogeneous w) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 < c := by
  obtain ⟨a, b, c, hz, hcone⟩ := hex
  have hheight : height p q (homogeneous z) = c * (δ * height p q (homogeneous w)) := by
    conv_lhs => rw [hz]
    simp [hp_height, hq_height]
  have hcc : 0 < δ' * c := by
    have hs : 0 < (δ' * c) * (δ * height p q (homogeneous w)) ^ 2 := by
      calc
        _ < (δ' * height p q (homogeneous z)) * (δ * height p q (homogeneous w)) := hsign
        _ = _ := by rw [hheight]; ring
    exact pos_of_mul_pos_left hs (sq_nonneg _)
  have hab : 0 ≤ δ' * a ∧ 0 ≤ δ' * b := by
    rcases sign_cases hδ' with rfl | rfl
    · rw [one_mul, one_mul]
      rw [one_mul] at hcc
      rcases hcone with h | h
      · exact ⟨h.1, h.2.1⟩
      · exact (hcc.not_ge h.2.2).elim
    · simp only [neg_mul, one_mul] at hcc ⊢
      rcases hcone with h | h
      · exfalso
        linarith only [hcc, h.2.2]
      · exact ⟨by linarith only [h.1], by linarith only [h.2.1]⟩
  refine ⟨δ' * a, δ' * b, δ' * c, ?_, hab.1, hab.2, hcc⟩
  conv_lhs => rw [hz]
  module


private theorem cones_unique {p q w z : ℝ²} (hpq : p ≠ q)
    {ε δ δ' : ℝ} (hε : ε ≠ 0) (hδ' : δ' ≠ 0)
    (hw : δ * height p q (homogeneous w) ≠ 0)
    (hf : ∃ a b c : ℝ, δ' • homogeneous z =
      a • homogeneous p + b • (ε • homogeneous q) + c • (δ • homogeneous w) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 < c)
    (hg : ∃ a b c : ℝ, δ • homogeneous w =
      a • homogeneous p + b • (ε • homogeneous q) + c • (δ' • homogeneous z) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 < c) :
    w = z := by
  obtain ⟨a, b, c, hf, ha, hb, hc⟩ := hf
  obtain ⟨a', b', c', hg, ha', hb', hc'⟩ := hg
  have hzw : δ' * height p q (homogeneous z) = c * (δ * height p q (homogeneous w)) := by
    simpa [hp_height, hq_height] using congrArg (height p q) hf
  have hwz : δ * height p q (homogeneous w) = c' * (δ' * height p q (homogeneous z)) := by
    simpa [hp_height, hq_height] using congrArg (height p q) hg
  rw [hzw] at hwz
  have hcc : c' * c = 1 := by
    apply mul_right_cancel₀ hw
    simpa only [one_mul, mul_assoc] using hwz.symm
  have hsum : δ • homogeneous w =
      (a' + c' * a) • homogeneous p + (b' + c' * b) • (ε • homogeneous q) +
      (c' * c) • (δ • homogeneous w) := by
    calc
      _ = _ := hg
      _ = _ := by
        conv_lhs => rw [hf]
        module
  rw [hcc, one_smul] at hsum
  have hs0 : (a' + c' * a) • homogeneous p + (b' + c' * b) • (ε • homogeneous q) = 0 := by
    simpa using congrArg (fun v : HVec => v - δ • homogeneous w) hsum.symm
  obtain ⟨hsa, hsb⟩ := pair_coeff hpq (by simpa only [smul_smul] using hs0)
  have ha0 : a = 0 := by
    have hz : c' * a = 0 := le_antisymm (by linarith only [hsa, ha']) (mul_nonneg hc'.le ha)
    exact (mul_eq_zero.1 hz).resolve_left hc'.ne'
  have hb0 : b = 0 := by
    have hsb' := (mul_eq_zero.1 hsb).resolve_right hε
    have hz : c' * b = 0 := le_antisymm (by linarith only [hsb', hb']) (mul_nonneg hc'.le hb)
    exact (mul_eq_zero.1 hz).resolve_left hc'.ne'
  simp only [ha0, hb0, zero_smul, zero_add] at hf
  have he : δ' = c * δ := by
    simpa [homogeneous] using congrFun hf 2
  have hcoord (i : Fin 2) : δ' * z i = (c * δ) * w i := by
    fin_cases i
    · simpa [homogeneous, mul_assoc] using congrFun hf 0
    · simpa [homogeneous, mul_assoc] using congrFun hf 1
  have hwz (i : Fin 2) : w i = z i := by
    apply mul_left_cancel₀ hδ'
    rw [hcoord, he]
  exact point_eq (hwz 0) (hwz 1)

private theorem swap_order {s : Finset ℝ²} {p q w : ℝ²} {ε δ : ℝ}
    (hε : ε ^ 2 = 1)
    (h : ∀ z ∈ s, ∃ a b c : ℝ,
      homogeneous z = a • homogeneous q + b • (ε • homogeneous p) + c • (δ • homogeneous w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))) :
    ∀ z ∈ s, ∃ a b c : ℝ,
      homogeneous z = a • homogeneous p + b • (ε • homogeneous q) + c • ((ε * δ) • homogeneous w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)) := by
  intro z hz
  obtain ⟨a, b, c, he, hs⟩ := h z hz
  rcases sign_cases hε with rfl | rfl
  · exact ⟨b, a, c, by simpa [add_comm] using he, hs.imp
      (fun h => ⟨h.2.1, h.1, h.2.2⟩) (fun h => ⟨h.2.1, h.1, h.2.2⟩)⟩
  · refine ⟨-b, -a, -c, ?_, ?_⟩
    · rw [he]
      module
    · rcases hs with h₀ | h₀
      · exact Or.inr ⟨neg_nonpos.2 h₀.2.1, neg_nonpos.2 h₀.1, neg_nonpos.2 h₀.2.2⟩
      · exact Or.inl ⟨neg_nonneg.2 h₀.2.1, neg_nonneg.2 h₀.1, neg_nonneg.2 h₀.2.2⟩


theorem four_attachments (s : Finset ℝ²) (L : AffineSubspace ℝ ℝ²)
    (hL : L ∈ ordinaryLines s) :
    (s.filter (fun w =>
      ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
        ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
          ∀ z ∈ s, ∃ a b c : ℝ,
            homogeneous z = a • homogeneous p + b • (ε • homogeneous q) +
              c • (δ • homogeneous w) ∧
            ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)))).card ≤ 4 := by
  classical
  obtain ⟨p, q, hpq, hpqL⟩ := card_eq_two.1 ((mem_ordinaryLines.1 hL).2)
  let W := s.filter (fun w =>
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
      ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
        ∀ z ∈ s, ∃ a b c : ℝ,
          homogeneous z = a • homogeneous p + b • (ε • homogeneous q) +
            c • (δ • homogeneous w) ∧
          ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)))
  have hmem (x : ℝ²) : x ∈ s ∧ x ∈ L ↔ x = p ∨ x = q := by
    rw [← mem_filter, hpqL]
    simp
  have hpL : p ∈ L := ((hmem p).2 (Or.inl rfl)).2
  have hqL : q ∈ L := ((hmem q).2 (Or.inr rfl)).2
  have hchoice (w : W) : ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧ (w : ℝ²) ∉ L ∧
      ∀ z ∈ s, ∃ a b c : ℝ,
        homogeneous z = a • homogeneous p + b • (ε • homogeneous q) +
          c • (δ • homogeneous w) ∧
        ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)) := by
    obtain ⟨p', hp', q', hq', hn, hp'L, hq'L, hw, ε, δ, hε, hδ, hcone⟩ := (mem_filter.1 w.2).2
    rcases (hmem p').1 ⟨hp', hp'L⟩ with rfl | rfl
    · rcases (hmem q').1 ⟨hq', hq'L⟩ with rfl | rfl
      · exact (hn rfl).elim
      · exact ⟨ε, δ, hε, hδ, hw, hcone⟩
    · rcases (hmem q').1 ⟨hq', hq'L⟩ with rfl | rfl
      · exact ⟨ε, ε * δ, hε, by rw [mul_pow, hε, hδ, one_mul], hw, swap_order hε hcone⟩
      · exact (hn rfl).elim
  choose ε δ hε hδ houtside hcone using hchoice
  let depth (w : W) := δ w * height p q (homogeneous w)
  have depth_ne (w : W) : depth w ≠ 0 := by
    have hd0 : δ w ≠ 0 := by
      intro hd
      simpa [hd] using hδ w
    exact mul_ne_zero hd0
      (height_ne_zero hpq (fun h => houtside w (affineSpan_pair_le_of_mem_of_mem hpL hqL h)))
  let label (w : W) : Bool × Bool := (decide (ε w = 1), decide (0 < depth w))
  have inj : Function.Injective label := by
    intro w z he
    have h₁ : decide (ε w = 1) = decide (ε z = 1) := congrArg Prod.fst he
    have h₂ : decide (0 < depth w) = decide (0 < depth z) := congrArg Prod.snd he
    have heps : ε w = ε z := by
      rcases sign_cases (hε w) with hw | hw <;> rcases sign_cases (hε z) with hz | hz
      · exact hw.trans hz.symm
      · norm_num [hw, hz] at h₁
      · norm_num [hw, hz] at h₁
      · exact hw.trans hz.symm
    have signs : 0 < depth z * depth w := by
      have hequiv : 0 < depth w ↔ 0 < depth z := by simpa using h₂
      rcases lt_or_gt_of_ne (depth_ne w) with hw | hw
      · have hz : depth z < 0 := lt_of_le_of_ne
          (le_of_not_gt (fun hz => hw.not_gt (hequiv.2 hz))) (depth_ne z)
        exact mul_pos_of_neg_of_neg hz hw
      · exact mul_pos (hequiv.1 hw) hw
    have hzS : (z : ℝ²) ∈ s := (mem_filter.1 z.2).1
    have hwS : (w : ℝ²) ∈ s := (mem_filter.1 w.2).1
    have hfor := orient_nonneg (hδ z) signs (hcone w z hzS)
    have hback := orient_nonneg (hδ w) (by simpa [mul_comm] using signs) (hcone z w hwS)
    rw [← heps] at hback
    have hε0 : ε w ≠ 0 := by
      intro h
      simpa [h] using hε w
    have hδ0 : δ z ≠ 0 := by
      intro h
      simpa [h] using hδ z
    exact Subtype.ext (cones_unique hpq hε0 hδ0 (depth_ne w) hfor hback)
  have hcard := Fintype.card_le_of_injective label inj
  change W.card ≤ 4
  simpa using hcard

end OMA.OrdinaryAttachment

theorem OMA.OrdinaryAttachment.h2_proof : OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1.H2 := by
  intro s _ _
  dsimp only
  intro L hL
  exact OMA.OrdinaryAttachment.four_attachments s L hL

end

section

/-
# The two exceptional endpoints in the Csima–Sawyer arrangement lemma

Credit: @sobrien032. Formalization by the coordinating Codex session and three
Codex solver sessions. Mathematical source: J. Csima and E. Sawyer (1993);
J. Lenchner, IBM Research Report RC24181 (2007), Lemmas 8–10.

Send the two distinct endpoints of the ordinary line to the two coordinate
directions at infinity. In the remaining grid each direction has a unique
singleton row and no ordinary separating secant. Extremal secants in a
reciprocal chart force all four corners of the bounding rectangle and exclude
further boundary points. A last-crossing argument forces all interior points
onto one diagonal, where uniqueness of the singleton row allows at most one.
This leaves at most five finite points and the two original endpoints.
-/

section

/- Projective coordinates for the two ordinary points in the Csima–Sawyer step. -/

open EuclideanGeometry Finset
open scoped Classical

namespace OMA.E210

abbrev Vector3 := Fin 3 → ℝ

def liftPoint (p : ℝ²) : Vector3 := ![p 0, p 1, 1]

def liftPair (p : ℝ × ℝ) : Vector3 := ![p.1, p.2, 1]

def onJoin (p q z : Vector3) : Prop :=
  ∃ a b : ℝ, z = a • p + b • q

theorem mem_line_iff_join (p q z : ℝ²) :
    z ∈ line[ℝ, p, q] ↔ onJoin (liftPoint p) (liftPoint q) (liftPoint z) := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨1 - t, t, ?_⟩
    ext i
    fin_cases i <;> simp [liftPoint, AffineMap.lineMap_apply_module'] <;> ring
  · rintro ⟨a, b, h⟩
    have h₂ : 1 = a + b := by simpa [liftPoint] using congrFun h 2
    refine ⟨b, ?_⟩
    ext i
    fin_cases i
    · have h₀ := congrFun h 0
      simp [liftPoint] at h₀
      simp [AffineMap.lineMap_apply_module']
      linear_combination -h₀ + (p 0) * h₂
    · have h₁ := congrFun h 1
      simp [liftPoint] at h₁
      simp [AffineMap.lineMap_apply_module']
      linear_combination -h₁ + (p 1) * h₂

theorem onJoin_equiv (E : Vector3 ≃ₗ[ℝ] Vector3) (p q z : Vector3) :
    onJoin (E p) (E q) (E z) ↔ onJoin p q z := by
  constructor
  · rintro ⟨a,b,h⟩
    exact ⟨a, b, E.injective (by simpa using h)⟩
  · rintro ⟨a,b,rfl⟩
    exact ⟨a,b,by simp⟩

theorem onJoin_rescale {p q z : Vector3} {c d e : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) :
    onJoin (c • p) (d • q) (e • z) ↔ onJoin p q z := by
  constructor
  · rintro ⟨a,b,h⟩
    refine ⟨e⁻¹ * (a*c), e⁻¹ * (b*d), ?_⟩
    simpa [smul_add, smul_smul, he, mul_assoc] using congrArg (e⁻¹ • ·) h
  · rintro ⟨a,b,rfl⟩
    exact ⟨e*a/c, e*b/d, by simp [smul_add, smul_smul, hc, hd]⟩

private theorem chart_from_det (p q : ℝ²) (r : Vector3)
    (hr : (Matrix.of ![liftPoint p, liftPoint q, r]).det ≠ 0) :
    ∃ E : Vector3 ≃ₗ[ℝ] Vector3,
      E (liftPoint p) = ![1,0,0] ∧ E (liftPoint q) = ![0,1,0] := by
  let rows : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![liftPoint p, liftPoint q, r]
  have hi := Matrix.linearIndependent_rows_of_det_ne_zero (A := rows) hr
  let B := basisOfLinearIndependentOfCardEqFinrank hi (by simp)
  have hB (i : Fin 3) : B i = rows i := by
    change (basisOfLinearIndependentOfCardEqFinrank hi _) i = rows i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨B.equivFun, ?_, ?_⟩
  · change B.equivFun (rows 0) = _
    rw [← hB]
    ext i
    rw [B.equivFun_self]
    fin_cases i <;> norm_num
  · change B.equivFun (rows 1) = _
    rw [← hB]
    ext i
    rw [B.equivFun_self]
    fin_cases i <;> norm_num

theorem chart_for_pair {p q : ℝ²} (hpq : p ≠ q) :
    ∃ E : Vector3 ≃ₗ[ℝ] Vector3,
      E (liftPoint p) = ![1,0,0] ∧ E (liftPoint q) = ![0,1,0] := by
  by_cases h : p 0 = q 0
  · have h' : p 1 ≠ q 1 := by
      intro hy
      apply hpq
      ext i
      fin_cases i
      · exact h
      · exact hy
    apply chart_from_det p q ![1,0,0]
    simpa [Matrix.det_fin_three, liftPoint, sub_ne_zero] using h'
  · apply chart_from_det p q ![0,1,0]
    simp [Matrix.det_fin_three, liftPoint]
    intro he
    exact h (by linarith)

theorem join_ideal_pair (v : Vector3) :
    onJoin ![1,0,0] ![0,1,0] v ↔ v 2 = 0 := by
  constructor
  · rintro ⟨a,b,rfl⟩
    simp
  · intro h
    refine ⟨v 0, v 1, ?_⟩
    ext i
    fin_cases i <;> simp_all

noncomputable def chartPoint (E : Vector3 ≃ₗ[ℝ] Vector3) (z : ℝ²) : ℝ × ℝ :=
  let v := E (liftPoint z)
  (v 0 / v 2, v 1 / v 2)

theorem chart_last_ne {E : Vector3 ≃ₗ[ℝ] Vector3} {p q z : ℝ²}
    (hp : E (liftPoint p) = ![1,0,0]) (hq : E (liftPoint q) = ![0,1,0])
    (hz : z ∉ line[ℝ, p, q]) : E (liftPoint z) 2 ≠ 0 := by
  intro h
  apply hz
  apply (mem_line_iff_join _ _ _).2
  apply (onJoin_equiv E _ _ _).1
  rw [hp, hq, join_ideal_pair]
  exact h

theorem chart_expand (E : Vector3 ≃ₗ[ℝ] Vector3) (z : ℝ²) (hz : E (liftPoint z) 2 ≠ 0) :
    E (liftPoint z) = E (liftPoint z) 2 • liftPair (chartPoint E z) := by
  ext i
  fin_cases i <;> simp [chartPoint, liftPair, hz, mul_div_cancel₀]

theorem chart_inj {E : Vector3 ≃ₗ[ℝ] Vector3} {u v : ℝ²}
    (hu : E (liftPoint u) 2 ≠ 0) (hv : E (liftPoint v) 2 ≠ 0)
    (h : chartPoint E u = chartPoint E v) : u = v := by
  let a := E (liftPoint u) 2
  let b := E (liftPoint v) 2
  have hab : b • liftPoint u = a • liftPoint v := by
    apply E.injective
    simp only [map_smul]
    calc
      b • E (liftPoint u) = (b*a) • liftPair (chartPoint E u) := by
        conv_lhs => rw [chart_expand E u hu, smul_smul]
      _ = (a*b) • liftPair (chartPoint E v) := by rw [h, mul_comm]
      _ = a • E (liftPoint v) := by
        conv_rhs => rw [chart_expand E v hv, smul_smul]
  have hba : b = a := by simpa [liftPoint] using congrFun hab 2
  rw [hba] at hab
  have h' : liftPoint u = liftPoint v := (smul_right_injective _ hu) hab
  ext i
  fin_cases i
  · exact congrFun h' 0
  · exact congrFun h' 1

end OMA.E210

end

section

/- In a projective chart whose horizontal and vertical directions both belong to the
configuration, a finite pair of different heights admits a horizontal attachment
exactly when its line separates the two blocks of occupied rows with the indicated
orientation. The statement also applies when the pair's line contains the vertical
direction; that pair then fails the separate ordinariness test. -/

namespace OMA.E210.Chart

abbrev Vec := Fin 3 → ℝ

def point (z : ℝ × ℝ) : Vec := ![z.1, z.2, 1]
def horizontal : Vec := ![1, 0, 0]
def vertical : Vec := ![0, 1, 0]

def chart (S : Set (ℝ × ℝ)) (t : Vec) : Prop :=
  t = horizontal ∨ t = vertical ∨ ∃ z ∈ S, t = point z

def covered (S : Vec → Prop) (u v w : Vec) : Prop :=
  ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧ ∀ t, S t → ∃ a b c : ℝ,
    t = a • u + b • (ε • v) + c • (δ • w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))

private theorem coefficients {u v : ℝ × ℝ} {m k a b c ε δ : ℝ} {t : Vec}
    (hu : u.1 = m * u.2 + k) (hv : v.1 = m * v.2 + k)
    (ht : t = a • point u + b • (ε • point v) + c • (δ • horizontal)) :
    (v.2 - u.2) * a = v.2 * t 2 - t 1 ∧
    (v.2 - u.2) * (b * ε) = t 1 - u.2 * t 2 ∧
    c * δ = t 0 - m * t 1 - k * t 2 := by
  rw [ht]
  refine ⟨?_, ?_, ?_⟩ <;> simp [point, horizontal, smul_eq_mul, hu, hv] <;> ring

private theorem reconstruct {u v : ℝ × ℝ} {m k δ : ℝ}
    (hu : u.1 = m * u.2 + k) (hv : v.1 = m * v.2 + k) (hy : u.2 < v.2)
    (hδ : δ ^ 2 = 1) (t : Vec) :
    t = ((v.2 * t 2 - t 1) / (v.2 - u.2)) • point u +
      ((u.2 * t 2 - t 1) / (v.2 - u.2)) • ((-1 : ℝ) • point v) +
      (δ * (t 0 - m * t 1 - k * t 2)) • (δ • horizontal) := by
  have hd := sub_ne_zero.mpr hy.ne'
  have hz (x : ℝ) : δ * x * δ = x := by linear_combination x * hδ
  ext i
  fin_cases i <;> simp [point, horizontal, smul_eq_mul, hu, hv, hz] <;>
    field_simp [hd] <;> ring

/-- The sign `δ` selects the increasing or decreasing separating line. -/
theorem horizontal_covered_iff (S : Set (ℝ × ℝ)) (u v : ℝ × ℝ) (m k : ℝ)
    (hu : u.1 = m * u.2 + k) (hv : v.1 = m * v.2 + k) (h : u.2 < v.2) :
    covered (chart S) (point u) (point v) horizontal ↔
      ∃ δ : ℝ, δ ^ 2 = 1 ∧ 0 ≤ δ * m ∧ ∀ z ∈ S,
        (z.2 ≤ u.2 ∧ 0 ≤ δ * (z.1 - m * z.2 - k)) ∨
        (v.2 ≤ z.2 ∧ δ * (z.1 - m * z.2 - k) ≤ 0) := by
  have hd : 0 < v.2 - u.2 := sub_pos.mpr h
  constructor
  · rintro ⟨ε, δ, hε, hδ, hc⟩
    obtain ⟨a,b,c,he,hs⟩ := hc vertical (Or.inr (Or.inl rfl))
    obtain ⟨ha,hb,hslope⟩ := coefficients hu hv he
    simp [vertical] at ha hb hslope
    have han : a < 0 := by
      by_contra! hn
      linarith [mul_nonneg hd.le hn]
    obtain ⟨hbn,hcn⟩ : b ≤ 0 ∧ c ≤ 0 := hs.elim (fun e => (han.not_ge e.1).elim) (fun e => e.2)
    have hep : ε = -1 := by
      rcases sq_eq_one_iff.mp hε with he' | he'
      · rw [he', mul_one] at hb
        linarith [mul_nonpos_of_nonneg_of_nonpos hd.le hbn]
      · exact he'
    subst ε
    have hec : c = -(δ * m) := by
      calc
        c = δ * (c * δ) := by linear_combination -c * hδ
        _ = -(δ * m) := by rw [hslope]; ring
    refine ⟨δ, hδ, by linarith, ?_⟩
    intro z hz
    obtain ⟨a',b',c',hrep,hsame⟩ := hc (point z) (Or.inr (Or.inr ⟨z, hz, rfl⟩))
    obtain ⟨h1,h2,h3⟩ := coefficients hu hv hrep
    simp [point] at h1 h2 h3
    have h4 : δ * (z.1 - m * z.2 - k) = c' := by
      rw [← h3]
      linear_combination c' * hδ
    rw [h4]
    rcases hsame with ⟨_,hb',hc'⟩ | ⟨ha',_,hc'⟩
    · exact Or.inl ⟨by nlinarith [mul_nonneg hd.le hb'], hc'⟩
    · exact Or.inr ⟨by linarith [mul_nonpos_of_nonneg_of_nonpos hd.le ha'], hc'⟩
  · rintro ⟨δ,hδ,hm,hz⟩
    refine ⟨-1, δ, by norm_num, hδ, ?_⟩
    intro t ht
    refine ⟨_, _, _, reconstruct hu hv h hδ t, ?_⟩
    rcases ht with rfl | rfl | ⟨z, hz', rfl⟩
    · simpa [horizontal] using (le_total 0 δ : 0 ≤ δ ∨ δ ≤ 0)
    · right
      simp [vertical]
      exact ⟨div_nonpos_of_nonpos_of_nonneg (by norm_num) hd.le, hm⟩
    · simp [point]
      rcases hz z hz' with ⟨hl,hs⟩ | ⟨hr,hs⟩
      · exact Or.inl ⟨div_nonneg (sub_nonneg.mpr (hl.trans h.le)) hd.le,
          div_nonneg (sub_nonneg.mpr hl) hd.le, hs⟩
      · exact Or.inr ⟨div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hd.le,
          div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (h.le.trans hr)) hd.le, hs⟩

end OMA.E210.Chart

end

section

namespace OMA.E210.Chart

private def same (a b c : ℝ) : Prop :=
  (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)

private theorem same_mul (t : ℝ) {a b c : ℝ} (h : same a b c) :
    same (t*a) (t*b) (t*c) := by
  rcases le_total 0 t with ht | ht <;> rcases h with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
  · exact Or.inl ⟨mul_nonneg ht ha, mul_nonneg ht hb, mul_nonneg ht hc⟩
  · exact Or.inr ⟨mul_nonpos_of_nonneg_of_nonpos ht ha, mul_nonpos_of_nonneg_of_nonpos ht hb,
      mul_nonpos_of_nonneg_of_nonpos ht hc⟩
  · exact Or.inr ⟨mul_nonpos_of_nonpos_of_nonneg ht ha, mul_nonpos_of_nonpos_of_nonneg ht hb,
      mul_nonpos_of_nonpos_of_nonneg ht hc⟩
  · exact Or.inl ⟨mul_nonneg_of_nonpos_of_nonpos ht ha, mul_nonneg_of_nonpos_of_nonpos ht hb,
      mul_nonneg_of_nonpos_of_nonpos ht hc⟩

private theorem choice_sign (a : ℝ) : ∃ e : ℝ, e^2 = 1 ∧ e * a = |a| := by
  rcases le_total 0 a with h | h
  · exact ⟨1, by norm_num, by simp [abs_of_nonneg h]⟩
  · exact ⟨-1, by norm_num, by simp [abs_of_nonpos h]⟩

private theorem covered_rescale {S : Vec → Prop} {u v w : Vec} (A B C : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (h : covered S u v w) :
    covered S (A • u) (B • v) (C • w) := by
  rcases h with ⟨ε,δ,hε,hδ,hh⟩
  obtain ⟨i,hi,hai⟩ := choice_sign A
  obtain ⟨j,hj,hbj⟩ := choice_sign B
  obtain ⟨k,hk,hck⟩ := choice_sign C
  refine ⟨i*ε*j, i*δ*k, by simp [mul_pow,hi,hj,hε], by simp [mul_pow,hi,hk,hδ], ?_⟩
  rintro t ht
  obtain ⟨a,b,c,eq,hsgn⟩ := hh t ht
  refine ⟨i*(a/|A|),i*(b/|B|),i*(c/|C|),?_,?_⟩
  · have E1 : i * (a/|A|) * A = a := by
      calc _ = (a/|A|) * (i*A) := by ring
           _ = a := by simp [hai,hA]
    have E2 : i * (b/|B|) * ((i*ε*j)*B) = b*ε := by
      calc _ = (b/|B|)*(j*B)*(i^2)*ε := by ring
           _ = b*ε := by simp [hbj,hi,hB]
    have E3 : i * (c/|C|) * ((i*δ*k)*C) = c*δ := by
      calc _ = (c/|C|)*(k*C)*(i^2)*δ := by ring
           _ = c*δ := by simp [hck,hi,hC]
    simpa [smul_smul, E1, E2, E3] using eq
  · apply same_mul
    rcases hsgn with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
    · exact Or.inl ⟨div_nonneg ha (abs_nonneg _), div_nonneg hb (abs_nonneg _), div_nonneg hc (abs_nonneg _)⟩
    · exact Or.inr ⟨div_nonpos_of_nonpos_of_nonneg ha (abs_nonneg _),
        div_nonpos_of_nonpos_of_nonneg hb (abs_nonneg _), div_nonpos_of_nonpos_of_nonneg hc (abs_nonneg _)⟩

theorem covered_rescale_basis_iff {S : Vec → Prop} {u v w : Vec} {A B C : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    covered S (A • u) (B • v) (C • w) ↔ covered S u v w := by
  constructor
  · intro h
    simpa [smul_smul, hA,hB,hC] using
      covered_rescale A⁻¹ B⁻¹ C⁻¹ (inv_ne_zero hA) (inv_ne_zero hB) (inv_ne_zero hC) h
  · exact covered_rescale A B C hA hB hC

/-- The indexed family can be reparametrized by any invertible linear change of
coordinates and by independently rescaling each vector representing a projective point. -/
private theorem covered_projective {α : Type*} {s : Set α} {v w : α → Vec}
    (E : Vec ≃ₗ[ℝ] Vec) (scale : α → ℝ) (hn : ∀ z ∈ s, scale z ≠ 0)
    (he : ∀ z ∈ s, E (v z) = scale z • w z)
    {i j k : α} (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s)
    (hc : covered (v '' s) (v i) (v j) (v k)) :
    covered (w '' s) (w i) (w j) (w k) := by
  apply (covered_rescale_basis_iff (hn i hi) (hn j hj) (hn k hk)).mp
  rw [← he i hi, ← he j hj, ← he k hk]
  rcases hc with ⟨ε,δ,hε,hδ,hw⟩
  refine ⟨ε,δ,hε,hδ,?_⟩
  rintro t ⟨z,hz,rfl⟩
  obtain ⟨a,b,c,hr,hs⟩ := hw (v z) ⟨z,hz,rfl⟩
  refine ⟨(scale z)⁻¹*a,(scale z)⁻¹*b,(scale z)⁻¹*c,?_,same_mul _ hs⟩
  calc
    w z = (scale z)⁻¹ • E (v z) := by rw [he z hz]; simp [smul_smul, hn z hz]
    _ = _ := by rw [hr]; simp [smul_add, smul_smul, mul_assoc]

theorem covered_projective_iff {α : Type*} {s : Set α} {v w : α → Vec}
    (E : Vec ≃ₗ[ℝ] Vec) (scale : α → ℝ) (hn : ∀ z ∈ s, scale z ≠ 0)
    (he : ∀ z ∈ s, E (v z) = scale z • w z)
    {i j k : α} (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    covered (v '' s) (v i) (v j) (v k) ↔ covered (w '' s) (w i) (w j) (w k) := by
  refine ⟨covered_projective E scale hn he hi hj hk,
    covered_projective E.symm (fun z => (scale z)⁻¹) (fun z hz => inv_ne_zero (hn z hz)) ?_ hi hj hk⟩
  intro z hz
  apply E.injective
  simp [he z hz, smul_smul, hn z hz]

end OMA.E210.Chart

end

section

/- Incidence and ordinary lines in a projective chart of the finite set. -/

open EuclideanGeometry Finset
open scoped Classical

namespace OMA.E210

structure GridModel (s : Finset ℝ²) (P : Finset (ℝ × ℝ)) where
  E : Vector3 ≃ₗ[ℝ] Vector3
  rep : ℝ² → Vector3
  scale : ℝ² → ℝ
  nonzero : ∀ z ∈ s, scale z ≠ 0
  expand : ∀ z ∈ s, E (liftPoint z) = scale z • rep z
  image_eq : ∀ v, Chart.chart (P : Set _) v ↔ ∃ z ∈ s, rep z = v

variable {s : Finset ℝ²} {P : Finset (ℝ × ℝ)}

theorem GridModel.rep_injective (M : GridModel s P) {u v : ℝ²} (hu : u ∈ s) (hv : v ∈ s)
    (h : M.rep u = M.rep v) : u = v := by
  have hh : M.scale v • liftPoint u = M.scale u • liftPoint v := by
    apply M.E.injective
    simp only [map_smul, M.expand _ hu, M.expand _ hv, h, smul_smul, mul_comm]
  have hsc : M.scale v = M.scale u := by simpa [liftPoint] using congrFun hh 2
  rw [hsc] at hh
  have he := smul_right_injective _ (M.nonzero u hu) hh
  ext i
  fin_cases i
  · exact congrFun he 0
  · exact congrFun he 1

theorem GridModel.mem_line (M : GridModel s P) {u v z : ℝ²}
    (hu : u ∈ s) (hv : v ∈ s) (hz : z ∈ s) :
    z ∈ line[ℝ, u, v] ↔ onJoin (M.rep u) (M.rep v) (M.rep z) := by
  rw [mem_line_iff_join, ← onJoin_equiv M.E, M.expand _ hu, M.expand _ hv, M.expand _ hz]
  exact onJoin_rescale (M.nonzero _ hu) (M.nonzero _ hv) (M.nonzero _ hz)

theorem ordinary_pair_iff {u v : ℝ²} (hu : u ∈ s) (hv : v ∈ s) (hne : u ≠ v) :
    line[ℝ, u, v] ∈ ordinaryLines s ↔
      ∀ z ∈ s, z ∈ line[ℝ, u, v] → z = u ∨ z = v := by
  classical
  let F := s.filter fun z => z ∈ line[ℝ, u, v]
  have sub : ({u,v} : Finset ℝ²) ⊆ F := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact mem_filter.mpr ⟨hu, left_mem_affineSpan_pair ..⟩
    · obtain rfl := mem_singleton.mp hz
      exact mem_filter.mpr ⟨hv, right_mem_affineSpan_pair ..⟩
  have two : ({u,v} : Finset ℝ²).card = 2 := by simp [hne]
  constructor
  · intro h z hz hzL
    have sz : F.card = 2 := (mem_ordinaryLines.mp h).2
    have eqn := eq_of_subset_of_card_le sub (le_of_eq (sz.trans two.symm))
    have hzf : z ∈ F := mem_filter.mpr ⟨hz, hzL⟩
    simpa [← eqn] using hzf
  · intro h
    have eqn : F = {u,v} := by
      apply Subset.antisymm _ sub
      intro z hz
      obtain ⟨hz, hL⟩ := mem_filter.mp hz
      simpa using h z hz hL
    exact mem_ordinaryLines.mpr ⟨⟨u,hu,v,hv,hne,rfl⟩, show F.card = 2 by rw [eqn,two]⟩

theorem ordinary_line_eq {L : AffineSubspace ℝ ℝ²} (hL : L ∈ ordinaryLines s) {p q : ℝ²}
    (hp : p ∈ L) (hq : q ∈ L) (hne : p ≠ q) : line[ℝ,p,q] = L := by
  obtain ⟨⟨a,_,b,_,_,rfl⟩,_⟩ := mem_ordinaryLines.mp hL
  exact affineSpan_pair_eq_of_mem_of_mem_of_ne hp hq hne

theorem initial_grid {p q : ℝ²} (hp : p ∈ s) (hq : q ∈ s) (hne : p ≠ q)
    (hO : line[ℝ,p,q] ∈ ordinaryLines s) :
    ∃ (P : Finset (ℝ × ℝ)) (M : GridModel s P),
      M.rep p = Chart.horizontal ∧ M.rep q = Chart.vertical ∧ s.card = P.card + 2 := by
  classical
  obtain ⟨E, ep, eq⟩ := chart_for_pair hne
  let T := (s.erase p).erase q
  have memT {z} : z ∈ T ↔ z ≠ q ∧ z ≠ p ∧ z ∈ s := by simp [T]
  have nz (z) (h : z ∈ T) : E (liftPoint z) 2 ≠ 0 := by
    obtain ⟨hqz,hpz,hz⟩ := memT.mp h
    apply chart_last_ne ep eq
    intro hl
    exact ((ordinary_pair_iff hp hq hne).mp hO z hz hl).elim hpz hqz
  let f := chartPoint E
  let P := T.image f
  let rep := fun z => if z = p then Chart.horizontal else if z = q then Chart.vertical else Chart.point (f z)
  let scale := fun z => if z = p ∨ z = q then (1:ℝ) else E (liftPoint z) 2
  have rp : rep p = Chart.horizontal := by simp [rep]
  have rq : rep q = Chart.vertical := by simp [rep,hne.symm]
  have rt (z) (h : z ∈ T) : rep z = Chart.point (f z) := by
    obtain ⟨h₁,h₂,_⟩ := memT.mp h
    simp [rep,h₁,h₂]
  have total (z) (hz : z ∈ s) : z = p ∨ z = q ∨ z ∈ T := by
    by_cases h : z=p <;> by_cases i : z=q <;> simp [h,i,memT,hz]
  refine ⟨P, ⟨E, rep, scale, ?_, ?_, ?_⟩, rp, rq, ?_⟩
  · intro z hz
    rcases total z hz with rfl | rfl | ht
    · simp [scale]
    · simp [scale]
    · obtain ⟨h₁,h₂,_⟩ := memT.mp ht
      simpa [scale,h₁,h₂] using nz z ht
  · intro z hz
    rcases total z hz with rfl | rfl | ht
    · simpa [rp,scale,Chart.horizontal] using ep
    · simpa [rq,scale,Chart.vertical] using eq
    · obtain ⟨h₁,h₂,_⟩ := memT.mp ht
      rw [rt z ht]
      simpa [scale,h₁,h₂,Chart.point,liftPair,f] using chart_expand E z (nz z ht)
  · intro v
    constructor
    · rintro (rfl | rfl | ⟨t, ht, rfl⟩)
      · exact ⟨p,hp,rp⟩
      · exact ⟨q,hq,rq⟩
      · obtain ⟨z,hz,rfl⟩ := mem_image.mp ht
        exact ⟨z,(memT.mp hz).2.2,rt z hz⟩
    · rintro ⟨z,hz,rfl⟩
      rcases total z hz with rfl | rfl | ht
      · exact Or.inl rp
      · exact Or.inr (Or.inl rq)
      · exact Or.inr (Or.inr ⟨_,mem_image_of_mem f ht,rt z ht⟩)
  · have hP : P.card = T.card := card_image_of_injOn (fun a ha b hb he => chart_inj (nz a ha) (nz b hb) he)
    have h₁ := card_erase_add_one hp
    have h₂ := card_erase_add_one ((mem_erase.mpr ⟨hne.symm,hq⟩) : q ∈ s.erase p)
    dsimp [T] at hP
    omega

end OMA.E210

end

section

namespace OMA.E210

abbrev GridPoint := ℝ × ℝ

/-- The intercept with the horizontal axis of the line of slope dx/dy = m. -/
def offset (m : ℝ) (a : GridPoint) : ℝ := a.1 - m * a.2

/-- After shearing by a maximal secant slope, each row lies weakly to the
left of every earlier row. -/
def RowsOrdered (P : Finset GridPoint) (m : ℝ) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, a.2 < b.2 → offset m b ≤ offset m a

def SingletonRow (P : Finset GridPoint) (a : GridPoint) : Prop :=
  a ∈ P ∧ ∀ b ∈ P, b.2 = a.2 → b = a

theorem eq_of_offset_of_row {m : ℝ} {a b : GridPoint} (hy : a.2 = b.2)
    (hf : offset m a = offset m b) : a = b := by
  apply Prod.ext _ hy
  simpa only [offset, hy, sub_left_inj] using hf

theorem rowsOrdered_of_bound {P : Finset GridPoint} {m : ℝ}
    (h : ∀ a ∈ P, ∀ b ∈ P, a.2 < b.2 → (b.1-a.1)/(b.2-a.2) ≤ m) :
    RowsOrdered P m := by
  intro a ha b hb hab
  have h' := (div_le_iff₀ (sub_pos.mpr hab)).mp (h a ha b hb hab)
  dsimp [offset]
  linarith only [h']

theorem offset_between {P : Finset GridPoint} {m : ℝ}
    (ord : RowsOrdered P m) {a b c : GridPoint} (ha : a ∈ P) (hb : b ∈ P)
    (hc : c ∈ P) (hab : a.2 < b.2) (hbc : b.2 < c.2)
    (hac : offset m a = offset m c) :
    offset m b = offset m a :=
  le_antisymm (ord a ha b hb hab) (hac ▸ ord b hb c hc hbc)

theorem singletonRow_between {P : Finset GridPoint} {m : ℝ}
    (ord : RowsOrdered P m) {a b c : GridPoint} (ha : a ∈ P) (hb : b ∈ P)
    (hc : c ∈ P) (hab : a.2 < b.2) (hbc : b.2 < c.2)
    (hac : offset m a = offset m c) : SingletonRow P b := by
  refine ⟨hb, ?_⟩
  intro t ht hty
  apply eq_of_offset_of_row hty (m := m)
  exact (offset_between ord ha ht hc (hty ▸ hab) (hty ▸ hbc) hac).trans
    (offset_between ord ha hb hc hab hbc hac).symm

/-- A secant through three points at an extremal slope has exactly those
three points. Its middle point is the unique singleton row, and there
are no other occupied horizontal levels between the two endpoints. -/
theorem extremal_triple {P : Finset GridPoint} {m : ℝ} (ord : RowsOrdered P m)
    (unique : ∀ u v, SingletonRow P u → SingletonRow P v → u = v)
    {a b c : GridPoint} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P)
    (hab : a.2 < b.2) (hbc : b.2 < c.2)
    (fab : offset m a = offset m b) (fbc : offset m b = offset m c) :
    SingletonRow P b ∧ (∀ t ∈ P, a.2 < t.2 → t.2 < c.2 → t = b) ∧
      ∀ t ∈ P, offset m t = offset m a → t = a ∨ t = b ∨ t = c := by
  have fac := fab.trans fbc
  have sb := singletonRow_between ord ha hb hc hab hbc fac
  have mid (t : GridPoint) (ht : t ∈ P) (hat : a.2 < t.2) (htc : t.2 < c.2) : t = b :=
    unique t b (singletonRow_between ord ha ht hc hat htc fac) sb
  refine ⟨sb, mid, ?_⟩
  intro t ht ft
  rcases lt_trichotomy t.2 a.2 with hta | hta | hat
  · have sa := singletonRow_between ord ht ha hb hta hab (ft.trans fab)
    exact (hab.ne (congrArg Prod.snd (unique _ _ sa sb))).elim
  · exact Or.inl (eq_of_offset_of_row hta ft)
  rcases lt_trichotomy t.2 c.2 with htc | htc | hct
  · exact Or.inr (Or.inl (mid t ht hat htc))
  · exact Or.inr (Or.inr (eq_of_offset_of_row htc (ft.trans fac)))
  · have sc := singletonRow_between ord hb hc ht hbc hct (ft.trans fab).symm
    exact (hbc.ne (congrArg Prod.snd (unique _ _ sb sc))).elim

/-- If an extremal line is ordinary, its intercept separates all rows
at a gap. The sign conditions here are the finite point part of
`Chart.horizontal_covered_iff` with sign +1. -/
theorem extremal_separates {P : Finset GridPoint} {m : ℝ} (ord : RowsOrdered P m)
    {a b : GridPoint} (ha : a ∈ P) (hb : b ∈ P) (hab : a.2 < b.2)
    (fab : offset m a = offset m b)
    (ordinary : ∀ t ∈ P, offset m t = offset m a → t = a ∨ t = b) :
    ∀ z ∈ P, (z.2 ≤ a.2 ∧ offset m a ≤ offset m z) ∨
      (b.2 ≤ z.2 ∧ offset m z ≤ offset m a) := by
  intro z hz
  by_cases hza : z.2 ≤ a.2
  · exact Or.inl ⟨hza, fab ▸ ord z hz b hb (hza.trans_lt hab)⟩
  have haz := lt_of_not_ge hza
  by_cases hbz : b.2 ≤ z.2
  · exact Or.inr ⟨hbz, ord a ha z hz haz⟩
  have hzb := lt_of_not_ge hbz
  have fz := offset_between ord ha hz hb haz hzb fab
  rcases ordinary z hz fz with rfl | rfl
  · exact (lt_irrefl _ haz).elim
  · exact (lt_irrefl _ hzb).elim

/-- A nonordinary extremal secant passes through the unique singleton row,
with points on both sides and no further occupied intermediate rows. -/
theorem extremal_through_singleton {P : Finset GridPoint} {m : ℝ}
    (ord : RowsOrdered P m) {s : GridPoint}
    (unique : ∀ z, SingletonRow P z → z = s)
    {a b : GridPoint} (ha : a ∈ P) (hb : b ∈ P) (hab : a.2 < b.2)
    (fab : offset m a = offset m b)
    (extra : ∃ u ∈ P, offset m u = offset m a ∧ u ≠ a ∧ u ≠ b) :
    ∃ l ∈ P, ∃ h ∈ P, l.2 < s.2 ∧ s.2 < h.2 ∧
      offset m s = offset m a ∧ offset m l = offset m a ∧ offset m h = offset m a ∧
      (∀ z ∈ P, l.2 < z.2 → z.2 < h.2 → z = s) ∧
      (∀ z ∈ P, offset m z = offset m a → z = l ∨ z = s ∨ z = h) := by
  have run (l v h : GridPoint) (hl : l ∈ P) (hv : v ∈ P) (hh : h ∈ P)
      (hlv : l.2 < v.2) (hvh : v.2 < h.2)
      (fl : offset m l = offset m a) (fv : offset m v = offset m a)
      (fh : offset m h = offset m a) :
      ∃ l ∈ P, ∃ h ∈ P, l.2 < s.2 ∧ s.2 < h.2 ∧
        offset m s = offset m a ∧ offset m l = offset m a ∧ offset m h = offset m a ∧
        (∀ z ∈ P, l.2 < z.2 → z.2 < h.2 → z = s) ∧
        (∀ z ∈ P, offset m z = offset m a → z = l ∨ z = s ∨ z = h) := by
    obtain ⟨hv', between, all⟩ := extremal_triple ord
      (fun u w hu hw => (unique u hu).trans (unique w hw).symm)
      hl hv hh hlv hvh (fl.trans fv.symm) (fv.trans fh.symm)
    have vs := unique _ hv'
    subst v
    exact ⟨l, hl, h, hh, hlv, hvh, fv, fl, fh, between,
      fun z hz fz => all _ hz (fz.trans fl.symm)⟩
  obtain ⟨u, hu, fu, hua, hub⟩ := extra
  rcases lt_trichotomy u.2 a.2 with h₁ | h₁ | h₁
  · exact run u a b hu ha hb h₁ hab fu rfl fab.symm
  · exact (hua (eq_of_offset_of_row h₁ fu)).elim
  rcases lt_trichotomy u.2 b.2 with h₂ | h₂ | h₂
  · exact run a u b ha hu hb h₁ h₂ rfl fu fab.symm
  · exact (hub (eq_of_offset_of_row h₂ (fu.trans fab))).elim
  · exact run a b u ha hb hu hab h₂ rfl fab.symm fu

/-- A finite set with some pair of distinct heights has a largest slope
over every such pair, attained by a pair ordered by height. -/
theorem exists_max_secant (P : Finset GridPoint)
    {u v : GridPoint} (hu : u ∈ P) (hv : v ∈ P) (huv : u.2 < v.2) :
    ∃ (m : ℝ) (a b : GridPoint), a ∈ P ∧ b ∈ P ∧ a.2 < b.2 ∧
      offset m a = offset m b ∧ RowsOrdered P m ∧
      (v.1-u.1)/(v.2-u.2) ≤ m := by
  classical
  let pairs := (P ×ˢ P).filter (fun p => p.1.2 < p.2.2)
  let slope (p : GridPoint × GridPoint) := (p.2.1-p.1.1)/(p.2.2-p.1.2)
  have mem (a b : GridPoint) : (a,b) ∈ pairs ↔ a ∈ P ∧ b ∈ P ∧ a.2 < b.2 := by
    simp [pairs, and_assoc]
  have huv' := (mem u v).mpr ⟨hu,hv,huv⟩
  obtain ⟨⟨a,b⟩, hab, top⟩ := Finset.exists_max_image pairs slope ⟨(u,v),huv'⟩
  obtain ⟨ha,hb,hy⟩ := (mem a b).mp hab
  let m := slope (a,b)
  have he : m * (b.2-a.2) = b.1-a.1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hy.ne')
  refine ⟨m,a,b,ha,hb,hy,?_,?_,top _ huv'⟩
  · dsimp only [offset]
    linarith only [he]
  · apply rowsOrdered_of_bound
    intro l hl h hh hh'
    exact top (l,h) ((mem l h).mpr ⟨hl,hh,hh'⟩)

/-- Positive extremal secants of a point set with no horizontal attachment
always have a third point. -/
def ForceThird (P : Finset GridPoint) : Prop :=
  ∀ (m : ℝ), 0 < m → RowsOrdered P m →
    ∀ a ∈ P, ∀ b ∈ P, a.2 < b.2 → offset m a = offset m b →
    ∃ z ∈ P, offset m z = offset m a ∧ z ≠ a ∧ z ≠ b

noncomputable def orientX (e : ℝ) (z : GridPoint) : GridPoint := (e*z.1,z.2)

noncomputable def swapPoint (s : GridPoint) (e : ℝ) (z : GridPoint) : GridPoint :=
  (e * (z.1-s.1)/(z.2-s.2),1/(z.2-s.2))

noncomputable def swapGrid (P : Finset GridPoint) (s : GridPoint) (e : ℝ) : Finset GridPoint := by
  classical
  exact insert (0,0) ((P.filter (fun z => z.2 ≠ s.2)).image (swapPoint s e))

private theorem orient_inj {e : ℝ} (he : e ≠ 0) : Function.Injective (orientX e) := by
  intro u v h
  have hy : u.2 = v.2 := (congrArg Prod.snd h : (orientX e u).2 = (orientX e v).2)
  have hx : e*u.1 = e*v.1 := (congrArg Prod.fst h : (orientX e u).1 = (orientX e v).1)
  exact Prod.ext (mul_left_cancel₀ he hx) hy

private theorem oriented_row {P : Finset GridPoint} {s : GridPoint}
    (unique : ∀ z, SingletonRow P z → z = s) {e : ℝ} (he : e ≠ 0)
    (w : GridPoint) (hw : SingletonRow (P.image (orientX e)) w) : w = orientX e s := by
  classical
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw.1
  have us := unique u ⟨hu, fun v hv hvu => orient_inj he (hw.2 _ (Finset.mem_image_of_mem _ hv) hvu)⟩
  rw [us]

private theorem oriented_frame {P : Finset GridPoint} {s : GridPoint}
    (unique : ∀ z, SingletonRow P z → z = s)
    (force : ForceThird P) {u v : GridPoint} (hu : u ∈ P) (hv : v ∈ P)
    (huy : u.2 < v.2) (hux : u.1 < v.1) :
    ∃ (m : ℝ) (l h : GridPoint), 0 < m ∧ RowsOrdered P m ∧
      l ∈ P ∧ h ∈ P ∧ l.2 < s.2 ∧ s.2 < h.2 ∧
      offset m l = offset m s ∧ offset m h = offset m s ∧
      (∀ z ∈ P, l.2 < z.2 → z.2 < h.2 → z = s) ∧
      (∀ z ∈ P, offset m z = offset m s → z = l ∨ z = s ∨ z = h) := by
  obtain ⟨m,a,b,ha,hb,hy,fab,ord,hm⟩ := exists_max_secant P hu hv huy
  have pos : 0 < m := lt_of_lt_of_le (div_pos (sub_pos.mpr hux) (sub_pos.mpr huy)) hm
  obtain ⟨l,hl,h,hh,hls,hsh,fs,fl,fh,gap,all⟩ :=
    extremal_through_singleton ord unique ha hb hy fab (force m pos ord a ha b hb hy fab)
  exact ⟨m,l,h,pos,ord,hl,hh,hls,hsh,fl.trans fs.symm,fh.trans fs.symm,gap,
    fun z hz fz => all _ hz (fz.trans fs)⟩

/-- In a grid with a unique singleton horizontal row and no extremal ordinary
line in either x orientation, its sole point lies strictly inside the bounding
box in both coordinates. -/
theorem singleton_interior {P : Finset GridPoint} {s : GridPoint}
    (unique : ∀ z, SingletonRow P z → z = s)
    (force : ∀ e, e = 1 ∨ e = -1 → ForceThird (P.image (orientX e)))
    {u v : GridPoint} (hu : u ∈ P) (hv : v ∈ P) (hy : u.2 < v.2) (hx : u.1 ≠ v.1) :
    (∃ l ∈ P, l.2 < s.2) ∧ (∃ h ∈ P, s.2 < h.2) ∧
    (∃ l ∈ P, l.1 < s.1) ∧ (∃ h ∈ P, s.1 < h.1) := by
  classical
  obtain ⟨e,he,huv⟩ : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ e*u.1 < e*v.1 := by
    rcases lt_or_gt_of_ne hx with h | h
    · exact ⟨1,Or.inl rfl,by simpa using h⟩
    · exact ⟨-1,Or.inr rfl,by simpa using h⟩
  have en : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  obtain ⟨m,l,h,hm,_,hl,hh,hly,hhy,fl,fh,_,_⟩ :=
    oriented_frame (s := orientX e s) (oriented_row unique en) (force _ he)
      (Finset.mem_image_of_mem (orientX e) hu) (Finset.mem_image_of_mem (orientX e) hv) hy huv
  obtain ⟨l',hl',rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨h',hh',rfl⟩ := Finset.mem_image.mp hh
  refine ⟨⟨l',hl',hly⟩,⟨h',hh',hhy⟩,?_⟩
  change l'.2 < s.2 at hly
  change s.2 < h'.2 at hhy
  dsimp [offset,orientX] at fl fh
  have lp := mul_pos hm (sub_pos.mpr hly)
  have hp := mul_pos hm (sub_pos.mpr hhy)
  rcases he with rfl | rfl
  · exact ⟨⟨l',hl',by linarith⟩,⟨h',hh',by linarith⟩⟩
  · exact ⟨⟨h',hh',by linarith⟩,⟨l',hl',by linarith⟩⟩

private theorem swap_y_eq {s u v : GridPoint} {e : ℝ}
    (h : (swapPoint s e u).2 = (swapPoint s e v).2) : u.2 = v.2 := by
  simpa only [swapPoint, one_div, inv_inj, sub_left_inj] using h

private theorem swap_inj {s u v : GridPoint} {e : ℝ} (he : e ≠ 0) (hu : u.2 ≠ s.2)
    (h : swapPoint s e u = swapPoint s e v) : u = v := by
  have hy := swap_y_eq (congrArg Prod.snd h)
  apply Prod.ext _ hy
  have hx := congrArg Prod.fst h
  change e*(u.1-s.1)/(u.2-s.2) = e*(v.1-s.1)/(v.2-s.2) at hx
  rw [←hy] at hx
  have h' := (div_left_inj' (sub_ne_zero.mpr hu)).mp hx
  exact sub_left_inj.mp (mul_left_cancel₀ he h')

private theorem swap_mem {P : Finset GridPoint} {s z : GridPoint} {e : ℝ}
    (hz : z ∈ P) (hy : z.2 ≠ s.2) : swapPoint s e z ∈ swapGrid P s e := by
  classical
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hz,hy⟩))

private theorem swap_ne_origin {s z : GridPoint} {e : ℝ} (hy : z.2 ≠ s.2) :
    swapPoint s e z ≠ (0,0) := by
  intro h
  exact (one_div_ne_zero (sub_ne_zero.mpr hy)) (congrArg Prod.snd h)

private theorem origin_mem (P : Finset GridPoint) (s : GridPoint) (e : ℝ) :
    ((0,0) : GridPoint) ∈ swapGrid P s e := by
  classical
  exact Finset.mem_insert_self _ _

theorem singleton_swap {P : Finset GridPoint} {s : GridPoint} {e : ℝ} (he : e ≠ 0)
    (unique : ∀ z, SingletonRow P z → z = s) (w : GridPoint)
    (hw : SingletonRow (swapGrid P s e) w) : w = (0,0) := by
  classical
  rcases Finset.mem_insert.mp hw.1 with h0 | h
  · exact h0
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
  obtain ⟨hz,hn⟩ := Finset.mem_filter.mp hz
  have hs := unique z ⟨hz,fun v hv hvz =>
    swap_inj he (hvz ▸ hn) (hw.2 _ (swap_mem hv (hvz ▸ hn))
      (by simp [swapPoint,hvz]))⟩
  exact (hn (congrArg Prod.snd hs)).elim

private theorem swap_offset {s z : GridPoint} {m e : ℝ} :
    offset m (swapPoint s e z) = (e*(z.1-s.1)-m)*(1/(z.2-s.2)) := by
  dsimp [offset,swapPoint]
  ring

private theorem swap_frame {P : Finset GridPoint} {s : GridPoint} {e : ℝ}
    (he : e ≠ 0) (hs : SingletonRow P s)
    (unique : ∀ z, SingletonRow P z → z = s)
    (force : ForceThird (swapGrid P s e))
    {w : GridPoint} (hw : w ∈ P) (pos : 0 < e * (w.1-s.1)) :
    ∃ (m : ℝ) (l h : GridPoint), 0 < m ∧ RowsOrdered (swapGrid P s e) m ∧
      l ∈ P ∧ h ∈ P ∧ l.2 < s.2 ∧ s.2 < h.2 ∧
      e*(l.1-s.1) = m ∧ e*(h.1-s.1) = m ∧
      (∀ z ∈ swapGrid P s e, (swapPoint s e l).2 < z.2 →
        z.2 < (swapPoint s e h).2 → z = (0,0)) ∧
      (∀ z ∈ swapGrid P s e, offset m z = 0 →
        z = swapPoint s e l ∨ z = (0,0) ∨ z = swapPoint s e h) := by
  classical
  have hn : w.2 ≠ s.2 := by
    intro eq
    have ws := hs.2 w hw eq
    simp [ws] at pos
  have wt := swap_mem (e := e) hw hn
  let O : GridPoint := (0,0)
  have om := origin_mem P s e
  obtain ⟨u,v,hu,hv,huv,hux⟩ :
      ∃ u v : GridPoint, u ∈ swapGrid P s e ∧ v ∈ swapGrid P s e ∧
        u.2 < v.2 ∧ u.1 < v.1 := by
    rcases lt_or_gt_of_ne hn with h | h
    · have den := sub_neg.mpr h
      exact ⟨_, O, wt, om, div_neg_of_pos_of_neg one_pos den, div_neg_of_pos_of_neg pos den⟩
    · have den := sub_pos.mpr h
      exact ⟨O, _, om, wt, div_pos one_pos den, div_pos pos den⟩
  obtain ⟨m,lo,hi,hm,ord,hlo,hhi,lneg,hpos,fl,fh,gap,all⟩ :=
    oriented_frame (singleton_swap he unique) force hu hv huv hux
  have reflO : offset m O = 0 := by simp [offset,O]
  have hl' : lo ∈ (P.filter (fun z => z.2 ≠ s.2)).image (swapPoint s e) := by
    rcases Finset.mem_insert.mp hlo with eq | tr
    · subst lo; exact (lt_irrefl _ lneg).elim
    · exact tr
  have hh' : hi ∈ (P.filter (fun z => z.2 ≠ s.2)).image (swapPoint s e) := by
    rcases Finset.mem_insert.mp hhi with eq | tr
    · subst hi; exact (lt_irrefl _ hpos).elim
    · exact tr
  obtain ⟨l,pl,rfl⟩ := Finset.mem_image.mp hl'
  obtain ⟨h,ph,rfl⟩ := Finset.mem_image.mp hh'
  obtain ⟨pl,ln⟩ := Finset.mem_filter.mp pl
  obtain ⟨ph,hn'⟩ := Finset.mem_filter.mp ph
  change 1/(l.2-s.2) < 0 at lneg
  change 0 < 1/(h.2-s.2) at hpos
  have ly := sub_neg.mp (one_div_neg.mp lneg)
  have hy := sub_pos.mp (one_div_pos.mp hpos)
  rw [swap_offset, reflO] at fl fh
  exact ⟨m,l,h,hm,ord,pl,ph,ly,hy,
    sub_eq_zero.mp ((mul_eq_zero.mp fl).resolve_right lneg.ne),
    sub_eq_zero.mp ((mul_eq_zero.mp fh).resolve_right hpos.ne'),gap,
    fun z hz f => all z hz (f.trans reflO.symm)⟩

/-- The extreme column on side `e` has exactly two points. Their heights
are the lowest and the highest occupied rows. -/
theorem boundary_column {P : Finset GridPoint} {s : GridPoint} {e : ℝ}
    (he : e ≠ 0) (hs : SingletonRow P s)
    (unique : ∀ z, SingletonRow P z → z = s)
    (force : ForceThird (swapGrid P s e))
    {w : GridPoint} (hw : w ∈ P) (pos : 0 < e*(w.1-s.1)) :
    ∃ l ∈ P, ∃ h ∈ P, l.1 = h.1 ∧ l.2 < s.2 ∧ s.2 < h.2 ∧ e*s.1 < e*l.1 ∧
      (∀ z ∈ P, l.2 ≤ z.2 ∧ z.2 ≤ h.2 ∧ e*z.1 ≤ e*l.1) ∧
      (∀ z ∈ P, z.1 = l.1 → z = l ∨ z = h) := by
  classical
  obtain ⟨m,l,h,hm,ord,hl,hh,ly,hy,fl,fh,gap,all⟩ := swap_frame he hs unique force hw pos
  have lx : l.1 = h.1 := sub_left_inj.mp (mul_left_cancel₀ he (fl.trans fh.symm))
  have inside : e*s.1 < e*l.1 := by linarith [fl]
  refine ⟨l,hl,h,hh,lx,ly,hy,inside,?_,?_⟩
  · intro z hz
    have low : l.2 ≤ z.2 := by
      by_contra! hzl
      have hzs := hzl.trans ly
      have t := swap_mem (e := e) hz hzs.ne
      have ll : (swapPoint s e l).2 < (swapPoint s e z).2 :=
        (one_div_lt_one_div_of_neg (sub_neg.mpr ly) (sub_neg.mpr hzs)).mpr (sub_lt_sub_right hzl _)
      have rr : (swapPoint s e z).2 < (swapPoint s e h).2 :=
        lt_trans (div_neg_of_pos_of_neg one_pos (sub_neg.mpr hzs)) (div_pos one_pos (sub_pos.mpr hy))
      exact swap_ne_origin hzs.ne (gap _ t ll rr)
    have high : z.2 ≤ h.2 := by
      by_contra! hhz
      have hsz := hy.trans hhz
      have t := swap_mem (e := e) hz hsz.ne'
      have ll : (swapPoint s e l).2 < (swapPoint s e z).2 :=
        lt_trans (div_neg_of_pos_of_neg one_pos (sub_neg.mpr ly)) (div_pos one_pos (sub_pos.mpr hsz))
      have rr : (swapPoint s e z).2 < (swapPoint s e h).2 :=
        one_div_lt_one_div_of_lt (sub_pos.mpr hy) (sub_lt_sub_right hhz _)
      exact swap_ne_origin hsz.ne' (gap _ t ll rr)
    refine ⟨low,high,?_⟩
    rcases lt_trichotomy z.2 s.2 with hzs | eq | hsz
    · have yn : 1/(z.2-s.2) < 0 := div_neg_of_pos_of_neg one_pos (sub_neg.mpr hzs)
      have f := ord _ (swap_mem (e := e) hz hzs.ne) _ (origin_mem P s e) yn
      rw [swap_offset] at f
      change 0-m*0 ≤ _ at f
      have t : e*(z.1-s.1)-m ≤ 0 := by
        by_contra! nh
        linarith only [mul_neg_of_pos_of_neg nh yn, f]
      linarith only [t,fl]
    · rw [hs.2 _ hz eq]
      exact inside.le
    · have yp : 0 < 1/(z.2-s.2) := div_pos one_pos (sub_pos.mpr hsz)
      have f := ord _ (origin_mem P s e) _ (swap_mem (e := e) hz hsz.ne') yp
      rw [swap_offset] at f
      change _ ≤ 0-m*0 at f
      have t : e*(z.1-s.1)-m ≤ 0 := by
        by_contra! nh
        linarith only [mul_pos nh yp, f]
      linarith only [t,fl]
  · intro z hz eq
    have hn : z.2 ≠ s.2 := by
      intro hy'
      have zs := hs.2 _ hz hy'
      rw [zs] at eq
      linarith [congrArg (fun t : ℝ => e*t) eq]
    have fz : offset m (swapPoint s e z) = 0 := by rw [swap_offset,eq,fl,sub_self,zero_mul]
    rcases all _ (swap_mem hz hn) fz with eq' | zero | eq'
    · exact Or.inl (swap_inj he hn eq')
    · exact (swap_ne_origin hn zero).elim
    · exact Or.inr (swap_inj he hn eq')

private theorem exists_sloping {P : Finset GridPoint}
    {a b c d : GridPoint} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P)
    (hx : a.1 ≠ b.1) (hy : c.2 ≠ d.2) :
    ∃ u ∈ P, ∃ v ∈ P, u.2 < v.2 ∧ u.1 ≠ v.1 := by
  by_contra! bad
  have vertical (u : GridPoint) (hu : u ∈ P) (v : GridPoint) (hv : v ∈ P)
      (diff : u.2 ≠ v.2) : u.1 = v.1 := by
    rcases lt_or_gt_of_ne diff with hh | hh
    · exact bad u hu v hv hh
    · exact (bad v hv u hu hh).symm
  have ab : a.2 = b.2 := by
    by_contra hn
    exact hx (vertical a ha b hb hn)
  obtain ⟨w,hw,hwa⟩ : ∃ w ∈ P, w.2 ≠ a.2 := by
    by_cases hca : c.2 = a.2
    · exact ⟨d,hd,fun hh => hy (hca.trans hh.symm)⟩
    · exact ⟨c,hc,hca⟩
  have v₁ := vertical a ha w hw hwa.symm
  have v₂ := vertical w hw b hb (ab ▸ hwa)
  exact hx (v₁.trans v₂)

/-- Saturation in unit coordinates: all four corners are occupied and both
extreme columns contain just their endpoints. -/
theorem unit_sides {P : Finset GridPoint} {s : GridPoint}
    (hs : SingletonRow P s) (unique : ∀ z, SingletonRow P z → z = s)
    (primary : ∀ e : ℝ, e = 1 ∨ e = -1 → ForceThird (P.image (orientX e)))
    (recip : ∀ e : ℝ, e = 1 ∨ e = -1 → ForceThird (swapGrid P s e))
    (bounds : ∀ z ∈ P, 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1)
    (x0 : ∃ z ∈ P, z.1 = 0) (x1 : ∃ z ∈ P, z.1 = 1)
    (y0 : ∃ z ∈ P, z.2 = 0) (y1 : ∃ z ∈ P, z.2 = 1) :
    (∀ x y : ℝ, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → (x,y) ∈ P) ∧
    (∀ z ∈ P, (z.1 = 0 ∨ z.1 = 1) → z.2 = 0 ∨ z.2 = 1) := by
  obtain ⟨xl,hxl,exl⟩ := x0
  obtain ⟨xr,hxr,exr⟩ := x1
  obtain ⟨yb,hyb,eyb⟩ := y0
  obtain ⟨yt,hyt,eyt⟩ := y1
  have hx : xl.1 ≠ xr.1 := by rw [exl,exr]; norm_num
  have hy : yb.2 ≠ yt.2 := by rw [eyb,eyt]; norm_num
  obtain ⟨u,hu,v,hv,uvy,uvx⟩ := exists_sloping hxl hxr hyb hyt hx hy
  obtain ⟨_,_,⟨v₀,hv₀,h₀⟩,⟨v₁,hv₁,h₁⟩⟩ := singleton_interior unique primary hu hv uvy uvx
  have side (e : ℝ) (he : e = 1 ∨ e = -1) (x : ℝ) (wx : GridPoint) (hwx : wx ∈ P)
      (target : wx.1 = x) (limit : ∀ z ∈ P, e*z.1 ≤ e*x) :
      (x,0) ∈ P ∧ (x,1) ∈ P ∧ (∀ z ∈ P, z.1 = x → z.2 = 0 ∨ z.2 = 1) := by
    have en : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    obtain ⟨v,hv,hv'⟩ : ∃ v ∈ P, 0 < e * (v.1-s.1) := by
      rcases he with rfl | rfl
      · exact ⟨v₁,hv₁,by linarith⟩
      · exact ⟨v₀,hv₀,by linarith⟩
    obtain ⟨l,hl,h,hh,lx,_,_,_,extreme,only⟩ :=
      boundary_column en hs unique (recip _ he) hv hv'
    obtain ⟨ll,_,_⟩ := extreme _ hyb
    obtain ⟨_,tt,_⟩ := extreme _ hyt
    have ex : l.1 = x := mul_left_cancel₀ en (le_antisymm (limit _ hl)
      (target ▸ (extreme _ hwx).2.2))
    have el : l.2 = 0 := le_antisymm (ll.trans_eq eyb) (bounds _ hl).2.2.1
    have eh : h.2 = 1 := le_antisymm (bounds _ hh).2.2.2 (eyt ▸ tt)
    refine ⟨(Prod.ext ex el : l = (x,0)) ▸ hl, (Prod.ext (lx.symm.trans ex) eh : h = (x,1)) ▸ hh, ?_⟩
    intro z hz zx
    rcases only z hz (zx.trans ex.symm) with rfl | rfl
    · exact Or.inl el
    · exact Or.inr eh
  obtain ⟨a,b,c⟩ := side 1 (Or.inl rfl) 1 xr hxr exr (fun z hz => by simpa using (bounds _ hz).2.1)
  obtain ⟨d,f,g⟩ := side (-1) (Or.inr rfl) 0 xl hxl exl
    (fun z hz => by simpa using (bounds _ hz).1)
  constructor
  · rintro x y (rfl | rfl) (rfl | rfl) <;> assumption
  · rintro z hz (hx | hx)
    · exact g _ hz hx
    · exact c _ hz hx

end OMA.E210

end

section

namespace OMA.E210.Rect

abbrev Pt := ℝ × ℝ
abbrev Coord := Pt → ℝ

def F (x y : Coord) (t : ℝ) (a : Pt) := x a + t * y a

def Single (P : Finset Pt) (y : Coord) (a : Pt) : Prop :=
  a ∈ P ∧ ∀ b ∈ P, y b = y a → b = a

/-- In these oriented coordinates the ordinary line of slope -t has a horizontal attachment. -/
def Cut (P : Finset Pt) (x y : Coord) : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, ∃ t h : ℝ, 0 < t ∧ y a < y b ∧ F x y t a = h ∧ F x y t b = h ∧
    (∀ z ∈ P, F x y t z = h → z = a ∨ z = b) ∧
    ∀ z ∈ P, (y z ≤ y a ∧ F x y t z ≤ h) ∨ (y b ≤ y z ∧ h ≤ F x y t z)

private noncomputable def cross (x y : Coord) (a b : Pt) := (x a - x b) / (y b - y a)

private lemma cross_eq (x y : Coord) {a b : Pt} (hab : y a < y b) :
    F x y (cross x y a b) a = F x y (cross x y a b) b := by
  dsimp [F, cross]
  field_simp [sub_ne_zero.mpr hab.ne']
  ring

private lemma eq_cross (x y : Coord) {a b : Pt} (hab : y a < y b)
    {t : ℝ} (hf : F x y t a = F x y t b) : cross x y a b = t := by
  apply (div_eq_iff (sub_ne_zero.mpr hab.ne')).mpr
  dsimp [F] at hf
  linarith

private lemma cross_later (x y : Coord) {a b : Pt} (hab : y a < y b)
    {t : ℝ} (hf : F x y t b < F x y t a) : t < cross x y a b := by
  apply (lt_div_iff₀ (sub_pos.mpr hab)).mpr
  dsimp [F] at hf
  linarith

private lemma above_later (x y : Coord) {a u : Pt} (hay : y u ≤ y a)
    {t t' : ℝ} (ht : t ≤ t') (h : F x y t u ≤ F x y t a) :
    F x y t' u ≤ F x y t' a := by
  dsimp [F] at *
  nlinarith only [h, mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hay)]

/-- The last crossing above a supporting ray yields an ordinary attached line or
a singleton row strictly between the ray's starting height and the top. -/
theorem last_crossing {P : Finset Pt} {x y : Coord}
    (inj : ∀ a b, x a = x b → y a = y b → a = b)
    {U C : Pt} (hU : U ∈ P) (hC : C ∈ P) (hUC : y U < y C)
    (top : ∀ z ∈ P, y z ≤ y C)
    {m : ℝ} (hm : 0 < m) (hinit : F x y m U = F x y m C)
    (barrier : ∀ z ∈ P, y z < y U → F x y m z < F x y m U) :
    Cut P x y ∨ ∃ z, Single P y z ∧ y U < y z ∧ y z < y C := by
  classical
  let feasible (w : Pt × Pt) := y w.1 < y w.2 ∧ m ≤ cross x y w.1 w.2 ∧
    F x y (cross x y w.1 w.2) U ≤ F x y (cross x y w.1 w.2) w.1
  let pairs := (P ×ˢ P).filter feasible
  have hstart : (U,C) ∈ pairs := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hU, hC⟩, hUC, ?_, ?_⟩
    · exact (eq_cross x y hUC hinit).ge
    · exact le_rfl
  obtain ⟨⟨a,b⟩, hw, hlast⟩ := pairs.exists_max_image
    (fun w => cross x y w.1 w.2) ⟨_, hstart⟩
  obtain ⟨hwmem, hab, hm', hbase⟩ := Finset.mem_filter.mp hw
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hwmem
  let t := cross x y a b
  let h := F x y t a
  have fhb : F x y t b = h := (cross_eq x y hab).symm
  have fhu : F x y t U ≤ h := hbase
  have hmt : m ≤ t := hm'
  have allabove (z : Pt) (hz : z ∈ P) (fh : F x y t z = h) : y U ≤ y z := by
    by_contra! hy
    have hbar := barrier z hz hy
    have prog := mul_nonneg (sub_nonneg.mpr hmt) (sub_nonneg.mpr hy.le)
    dsimp [F] at hbar fhu fh
    nlinarith only [hbar, fhu, fh, prog]
  have no_future (z w : Pt) (hz : z ∈ P) (hw' : w ∈ P) (hyw : y z < y w)
      (hf : F x y t w < F x y t z)
      (crossAbove : F x y (cross x y z w) U ≤ F x y (cross x y z w) z) : False := by
    have fut := cross_later x y hyw hf
    have mem : (z,w) ∈ pairs :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hz,hw'⟩, hyw, hmt.trans fut.le, crossAbove⟩
    exact (not_lt_of_ge (hlast (z,w) mem)) fut
  let hits := P.filter (fun z => F x y t z = h)
  have ah : a ∈ hits := Finset.mem_filter.mpr ⟨ha,rfl⟩
  have bh : b ∈ hits := Finset.mem_filter.mpr ⟨hb,fhb⟩
  obtain ⟨l,hl,lo⟩ := hits.exists_min_image y ⟨a,ah⟩
  obtain ⟨r,hr,hi⟩ := hits.exists_max_image y ⟨b,bh⟩
  obtain ⟨hpl, fhl⟩ := Finset.mem_filter.mp hl
  obtain ⟨hpr, fhr⟩ := Finset.mem_filter.mp hr
  have hlr : y l < y r := (lo a ah).trans_lt (hab.trans_le (hi b bh))
  have below (z : Pt) (hz : z ∈ P) (hy : y z < y r) : F x y t z ≤ h := by
    by_contra! hf
    have hf' : F x y t r < F x y t z := fhr ▸ hf
    apply no_future z r hz hpr hy hf'
    rw [cross_eq x y hy]
    exact above_later x y (allabove r hpr fhr) (cross_later x y hy hf').le (fhr ▸ fhu)
  have above (z : Pt) (hz : z ∈ P) (hy : y l < y z) : h ≤ F x y t z := by
    by_contra! hf
    have hf' : F x y t z < F x y t l := fhl ▸ hf
    exact no_future l z hpl hz hy hf' (above_later x y (allabove l hpl fhl)
      (cross_later x y hy hf').le (fhl ▸ fhu))
  have coord_eq (z v : Pt) (fy : y z = y v) (fx : F x y t z = F x y t v) : z = v := by
    apply inj z v _ fy
    simpa [F,fy] using fx
  by_cases mid : ∃ z ∈ P, y l < y z ∧ y z < y r
  · obtain ⟨z,hz,h1,h2⟩ := mid
    right
    refine ⟨z, ⟨hz, ?_⟩, (allabove l hpl fhl).trans_lt h1, h2.trans_le (top r hpr)⟩
    intro v hv hvy
    apply coord_eq v z hvy
    exact (le_antisymm (below v hv (hvy ▸ h2)) (above v hv (hvy ▸ h1))).trans
      (le_antisymm (below z hz h2) (above z hz h1)).symm
  · left
    refine ⟨l,hpl,r,hpr,t,h,hm.trans_le hmt,hlr,fhl,fhr,?_,?_⟩
    · intro z hz hzz
      have mem : z ∈ hits := Finset.mem_filter.mpr ⟨hz,hzz⟩
      by_cases eq : y z = y l
      · exact Or.inl (coord_eq z l eq (hzz.trans fhl.symm))
      · have lt := lt_of_le_of_ne (lo z mem) (Ne.symm eq)
        have eqr : y z = y r := le_antisymm (hi z mem) (le_of_not_gt fun hh =>
          mid ⟨z,hz,lt,hh⟩)
        exact Or.inr (coord_eq z r eqr (hzz.trans fhr.symm))
    · intro z hz
      by_cases low : y z ≤ y l
      · exact Or.inl ⟨low,below z hz (low.trans_lt hlr)⟩
      · have hi' := lt_of_not_ge low
        exact Or.inr ⟨le_of_not_gt (fun h' => mid ⟨z,hz,hi',h'⟩), above z hz hi'⟩

/-- With no attached line, any secant out of the top-left corner with ratio
greater than one forces a singleton row strictly above a maximizing point. -/
theorem corner_wedge {P : Finset Pt} {x y : Coord}
    (inj : ∀ a b, x a = x b → y a = y b → a = b)
    (bounds : ∀ z ∈ P, 0 ≤ x z ∧ x z ≤ 1 ∧ 0 ≤ y z ∧ y z ≤ 1)
    (corner : ∃ C ∈ P, x C = 0 ∧ y C = 1)
    (flag : ∃ z ∈ P, y z < 1 ∧ 1 - y z < x z)
    (noCut : ¬ Cut P x y) :
    ∃ U ∈ P, ∃ m : ℝ, 1 < m ∧ 0 < y U ∧ y U < 1 ∧ x U = m * (1 - y U) ∧
      (∀ z ∈ P, y z < 1 → x z ≤ m * (1 - y z)) ∧
      ∃ z, Single P y z ∧ y U < y z ∧ y z < 1 := by
  classical
  obtain ⟨C,hC,hxC,hyC⟩ := corner
  obtain ⟨w,hw,hyw,hxw⟩ := flag
  let inner := P.filter (fun a => y a < 1)
  let ratio (a : Pt) := x a / (1-y a)
  have win : w ∈ inner := Finset.mem_filter.mpr ⟨hw,hyw⟩
  obtain ⟨v,hv,maxi⟩ := inner.exists_max_image ratio ⟨_,win⟩
  let m := ratio v
  have hm : 1 < m := lt_of_lt_of_le (b := ratio w) (by
    apply (lt_div_iff₀ (by linarith : 0 < 1-y w)).mpr
    linarith) (maxi w win)
  let winners := inner.filter (fun a => ratio a = m)
  obtain ⟨U,hU,low⟩ := winners.exists_min_image y ⟨v, Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  have uin := (Finset.mem_filter.mp hU).1
  obtain ⟨hpu,hyu⟩ := Finset.mem_filter.mp uin
  have e := (Finset.mem_filter.mp hU).2
  have hu : x U = m * (1-y U) := (div_eq_iff (by linarith : (1:ℝ)-y U≠0)).mp e
  have major (z : Pt) (hz : z ∈ P) (hy : y z < 1) : x z ≤ m * (1-y z) :=
    (div_le_iff₀ (by linarith : 0 < 1-y z)).mp (maxi z (Finset.mem_filter.mpr ⟨hz,hy⟩))
  have hu0 : 0 < y U := by
    have ⟨_,hh,hh',_⟩ := bounds U hpu
    by_contra! he
    have eq := le_antisymm he hh'
    rw [eq,sub_zero,mul_one] at hu
    linarith
  have heF : F x y m U = F x y m C := by dsimp [F]; rw [hxC,hyC,hu]; ring
  have bar (z : Pt) (hz : z ∈ P) (hy : y z < y U) : F x y m z < F x y m U := by
    have hzi : z ∈ inner := Finset.mem_filter.mpr ⟨hz,hy.trans hyu⟩
    have neq : ratio z ≠ m := fun ez =>
      (not_le.mpr hy) (low z (Finset.mem_filter.mpr ⟨hzi,ez⟩))
    have small : ratio z < m := lt_of_le_of_ne (maxi z hzi) neq
    have := (div_lt_iff₀ (by linarith : (0:ℝ) < 1-y z)).mp small
    dsimp [F]
    linarith only [this,hu]
  have alt := last_crossing inj hpu hC (hyC ▸ hyu) (fun z hz => hyC ▸ (bounds z hz).2.2.2)
    (zero_lt_one.trans hm) heF bar
  rw [hyC] at alt
  exact ⟨U,hpu,m,hm,hu0,hyu,hu,major,alt.resolve_left noCut⟩

theorem adjacent_flags_impossible {P : Finset Pt} {x y : Coord}
    (inj : ∀ a b, x a = x b → y a = y b → a = b)
    (bounds : ∀ z ∈ P, 0 ≤ x z ∧ x z ≤ 1 ∧ 0 ≤ y z ∧ y z ≤ 1)
    (topLeft : ∃ C ∈ P, x C = 0 ∧ y C = 1)
    (botLeft : ∃ C ∈ P, x C = 0 ∧ y C = 0)
    (unique : ∀ a b, Single P y a → Single P y b → a = b)
    (noCut : ¬ Cut P x y) (noCut' : ¬ Cut P x (fun z => 1-y z))
    (topFlag : ∃ z ∈ P, y z < 1 ∧ 1-y z < x z)
    (botFlag : ∃ z ∈ P, 0 < y z ∧ y z < x z) : False := by
  obtain ⟨u,hu,m,hm,hu0,hu1,hxu,major,up,supAbove,hy1,_⟩ :=
    corner_wedge inj bounds topLeft topFlag noCut
  let y' (z : Pt) := 1-y z
  have hinj' (a b : Pt) (hx : x a = x b) (hy : y' a = y' b) : a = b := by
    apply inj a b hx
    simpa [y'] using hy
  have bounds' (z : Pt) (hz : z ∈ P) : 0 ≤ x z ∧ x z ≤ 1 ∧ 0 ≤ y' z ∧ y' z ≤ 1 := by
    obtain ⟨a,b,c,d⟩ := bounds z hz
    exact ⟨a,b,sub_nonneg.mpr d,sub_le_self _ c⟩
  obtain ⟨C,hC,cx,cy⟩ := botLeft
  obtain ⟨w,hw,hw0,hwx⟩ := botFlag
  have wflag : ∃ z ∈ P, y' z < 1 ∧ 1-y' z < x z :=
    ⟨w,hw,by dsimp [y']; linarith,by dsimp [y']; linarith⟩
  obtain ⟨d,hd,n,hn,hd0,hd1,hxd,major',dn,supBelow,hy2,_⟩ :=
    corner_wedge hinj' bounds' ⟨C,hC,cx,by simp [y',cy]⟩ wflag noCut'
  have sd : Single P y dn :=
    ⟨supBelow.1,fun z hz hy => supBelow.2 z hz (by dsimp [y']; rw [hy])⟩
  have same := unique up dn supAbove sd
  dsimp [y'] at hd0 hd1 hxd major' hy2
  have ud := major d hd (by linarith)
  have du := major' u hu (by linarith)
  rw [same] at hy1
  have neg := mul_neg_of_pos_of_neg (show 0 < m+n by linarith) (show y u-y d < 0 by linarith)
  nlinarith only [neg,hxu,hxd,ud,du]


def orient (b : Bool) (x : Coord) : Coord := if b then (fun z => 1-x z) else x

def NoCuts (P : Finset Pt) (x y : Coord) : Prop :=
  ∀ a b : Bool, ¬ Cut P (orient a x) (orient b y)

def Corners (P : Finset Pt) (x y : Coord) : Prop :=
  ∀ a b : ℝ, (a = 0 ∨ a = 1) → (b = 0 ∨ b = 1) → ∃ z ∈ P, x z = a ∧ y z = b

def InSquare (x y : Coord) (z : Pt) : Prop := 0 ≤ x z ∧ x z ≤ 1 ∧ 0 ≤ y z ∧ y z ≤ 1

def Interior (z : Pt) : Prop := (0 < z.1 ∧ z.1 < 1) ∧ (0 < z.2 ∧ z.2 < 1)

private theorem adjacent_oriented {P : Finset Pt} {x y : Coord}
    (inj : ∀ a b, x a = x b → y a = y b → a = b)
    (bounds : ∀ z ∈ P, InSquare x y z)
    (corners : Corners P x y)
    (unique : ∀ a b, Single P y a → Single P y b → a = b)
    (safe : NoCuts P x y) (c : Bool)
    (tf : ∃ z ∈ P, y z < 1 ∧ 1-y z < orient c x z)
    (bf : ∃ z ∈ P, 0 < y z ∧ y z < orient c x z) : False := by
  apply adjacent_flags_impossible (x := orient c x) (y := y) _ _ _ _ unique
    (safe c false) (safe c true) tf bf
  · intro a b hx hy
    apply inj a b _ hy
    cases c <;> simpa [orient] using hx
  · intro z hz
    obtain ⟨h1,h2,h3,h4⟩ := bounds z hz
    cases c
    · exact ⟨h1,h2,h3,h4⟩
    · exact ⟨sub_nonneg.mpr h2,sub_le_self _ h1,h3,h4⟩
  · cases c
    · exact corners 0 1 (.inl rfl) (.inr rfl)
    · obtain ⟨a,ha,hx,hy⟩ := corners 1 1 (.inr rfl) (.inr rfl)
      exact ⟨a,ha,by simp [orient,hx],hy⟩
  · cases c
    · exact corners 0 0 (.inl rfl) (.inl rfl)
    · obtain ⟨a,ha,hx,hy⟩ := corners 1 0 (.inr rfl) (.inl rfl)
      exact ⟨a,ha,by simp [orient,hx],hy⟩

/-- All strictly interior points lie on one of the two diagonals. -/
theorem common_diagonal {P : Finset Pt} (bounds : ∀ z ∈ P, InSquare Prod.fst Prod.snd z)
    (corners : Corners P Prod.fst Prod.snd)
    (uy : ∀ a b, Single P Prod.snd a → Single P Prod.snd b → a = b)
    (ux : ∀ a b, Single P Prod.fst a → Single P Prod.fst b → a = b)
    (safe : NoCuts P Prod.fst Prod.snd) (swSafe : NoCuts P Prod.snd Prod.fst) :
    (∀ z ∈ P, Interior z → z.1 = z.2) ∨ (∀ z ∈ P, Interior z → z.1+z.2 = 1) := by
  classical
  by_contra! avoid
  obtain ⟨⟨u,hu,hui,une⟩,v,hv,hvi,vne⟩ := avoid
  obtain ⟨⟨ux0,ux1⟩,uy0,uy1⟩ := hui
  obtain ⟨⟨vx0,vx1⟩,vy0,vy1⟩ := hvi
  have st := adjacent_oriented (x := Prod.fst) (y := Prod.snd) (fun _ _ => Prod.ext)
    bounds corners uy safe
  have bs (z : Pt) (hz : z ∈ P) : InSquare Prod.snd Prod.fst z := by
    obtain ⟨a,b,c,d⟩ := bounds z hz
    exact ⟨c,d,a,b⟩
  have cc : Corners P Prod.snd Prod.fst := by
    intro a b ha hb
    obtain ⟨z,hz,h1,h2⟩ := corners b a hb ha
    exact ⟨z,hz,h2,h1⟩
  have sw := adjacent_oriented (x := Prod.snd) (y := Prod.fst)
    (fun _ _ hy hx => Prod.ext hx hy) bs cc ux swSafe
  rcases lt_or_gt_of_ne vne with vlt | vgt <;> rcases lt_or_gt_of_ne une with ult | ugt
  · apply st true ⟨u,hu,uy1,?_⟩ ⟨v,hv,vy0,?_⟩ <;> simp only [orient, if_true] <;> linarith
  · apply sw true ⟨u,hu,ux1,?_⟩ ⟨v,hv,vx0,?_⟩ <;> simp only [orient, if_true] <;> linarith
  · apply sw false ⟨v,hv,vx1,?_⟩ ⟨u,hu,ux0,?_⟩ <;> simp only [orient, Bool.false_eq_true, if_false] <;> linarith
  · apply st false ⟨v,hv,vy1,?_⟩ ⟨u,hu,uy0,?_⟩ <;> simp only [orient, Bool.false_eq_true, if_false] <;> linarith

/-- If each boundary point is a corner, both directions having type (2,0)
forces the four corners and at most one interior point. -/
theorem rectangle_card_le_five (P : Finset Pt) (bounds : ∀ z ∈ P, InSquare Prod.fst Prod.snd z)
    (corners : Corners P Prod.fst Prod.snd)
    (boundary : ∀ z ∈ P, Interior z ∨ ((z.1 = 0 ∨ z.1 = 1) ∧ (z.2 = 0 ∨ z.2 = 1)))
    (uy : ∀ a b, Single P Prod.snd a → Single P Prod.snd b → a = b)
    (ux : ∀ a b, Single P Prod.fst a → Single P Prod.fst b → a = b)
    (safe : NoCuts P Prod.fst Prod.snd) (swSafe : NoCuts P Prod.snd Prod.fst) : P.card ≤ 5 := by
  classical
  have diag := common_diagonal bounds corners uy ux safe swSafe
  let interior := P.filter Interior
  have single (v : Pt) (hv : v ∈ interior) : Single P Prod.snd v := by
    obtain ⟨hvp,hvi⟩ := Finset.mem_filter.mp hv
    refine ⟨hvp,?_⟩
    intro z hz hzy
    have hzi : Interior z := by
      rcases boundary z hz with hi | ⟨_,eq | eq⟩
      · exact hi
      · exact False.elim (by have := hvi.2.1; change z.2 = v.2 at hzy; linarith)
      · exact False.elim (by have := hvi.2.2; change z.2 = v.2 at hzy; linarith)
    apply Prod.ext _ hzy
    change z.2 = v.2 at hzy
    rcases diag with d | d <;> have a := d v hvp hvi <;> have b := d z hz hzi <;> linarith
  have hc : interior.card ≤ 1 := Finset.card_le_one.mpr
    (fun z hz v hv => uy z v (single z hz) (single v hv))
  let corners4 := ({0,1} : Finset ℝ) ×ˢ ({0,1} : Finset ℝ)
  have h4 : corners4.card = 4 := by norm_num [corners4,Finset.card_product]
  have incl : P ⊆ corners4 ∪ interior := by
    intro z hz
    rcases boundary z hz with hi | ⟨h1,h2⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hz,hi⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_product.mpr
      simpa using And.intro h1 h2
  have ca := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  omega

end OMA.E210.Rect

end

section

/- The two ordinary lines through a direction leave exactly one singleton finite row. -/

open EuclideanGeometry Finset
open scoped Classical
namespace OMA.E210

noncomputable def pencil (s : Finset ℝ²) (p : ℝ²) := (ordinaryLines s).filter (fun L => p ∈ L)

theorem chart_point_inj {u v : ℝ × ℝ} (h : Chart.point u = Chart.point v) : u = v :=
  Prod.ext (congrFun h 0) (congrFun h 1)

theorem chart_point_ne_h (u : ℝ × ℝ) : Chart.point u ≠ Chart.horizontal := by
  intro h
  have : (1 : ℝ) = 0 := congrFun h 2
  exact one_ne_zero this

theorem chart_point_ne_v (u : ℝ × ℝ) : Chart.point u ≠ Chart.vertical := by
  intro h
  have : (1 : ℝ) = 0 := congrFun h 2
  exact one_ne_zero this

theorem chart_h_ne_v : Chart.horizontal ≠ Chart.vertical := by
  intro h
  have : (1 : ℝ) = 0 := congrFun h 0
  exact one_ne_zero this

theorem onJoin_row {u v : ℝ × ℝ} :
    onJoin Chart.horizontal (Chart.point u) (Chart.point v) ↔ v.2 = u.2 := by
  constructor
  · rintro ⟨a,b,h⟩
    have hb : 1 = b := by simpa [Chart.horizontal, Chart.point] using congrFun h 2
    simpa [Chart.horizontal, Chart.point, ← hb] using congrFun h 1
  · intro h
    refine ⟨v.1-u.1, 1, ?_⟩
    ext i
    fin_cases i <;> simp [Chart.horizontal, Chart.point, h]

theorem not_vertical_on_row (u : ℝ × ℝ) :
    ¬onJoin Chart.horizontal (Chart.point u) Chart.vertical := by
  rintro ⟨a,b,he⟩
  have hb : (0:ℝ) = b := by simpa [Chart.horizontal,Chart.vertical,Chart.point] using congrFun he 2
  simpa [Chart.horizontal,Chart.vertical,Chart.point,← hb] using congrFun he 1

variable {s : Finset ℝ²} {P : Finset (ℝ × ℝ)}

theorem GridModel.row_ordinary (M : GridModel s P) {p z : ℝ²} (hp : p ∈ s) (hz : z ∈ s)
    (rp : M.rep p = Chart.horizontal) {u : ℝ × ℝ} (hu : u ∈ P) (rz : M.rep z = Chart.point u) :
    line[ℝ,p,z] ∈ ordinaryLines s ↔ SingletonRow P u := by
  have hpz : p ≠ z := fun h => chart_point_ne_h u (rz.symm.trans (h ▸ rp))
  rw [ordinary_pair_iff hp hz hpz]
  constructor
  · intro h
    refine ⟨hu, ?_⟩
    intro v hv hy
    obtain ⟨b,hb,rb⟩ := (M.image_eq _).mp (Or.inr (Or.inr ⟨v,hv,rfl⟩))
    have hL : b ∈ line[ℝ,p,z] := by
      rw [M.mem_line hp hz hb,rp,rz,rb,onJoin_row]
      exact hy
    rcases h b hb hL with rfl | rfl
    · exact False.elim (chart_point_ne_h v (rb.symm.trans rp))
    · exact chart_point_inj (rb.symm.trans rz)
  · intro h b hb hL
    have hj := (M.mem_line hp hz hb).mp hL
    rw [rp,rz] at hj
    rcases (M.image_eq _).mpr ⟨b,hb,rfl⟩ with i | i | ⟨v,hv,i⟩
    · exact Or.inl (M.rep_injective hb hp (i.trans rp.symm))
    · exact ((not_vertical_on_row u) (i ▸ hj)).elim
    · obtain rfl := h.2 _ hv (onJoin_row.mp (i ▸ hj))
      exact Or.inr (M.rep_injective hb hz (i.trans rz.symm))

theorem GridModel.unique_row (M : GridModel s P) {p q : ℝ²} (hp : p ∈ s) (hq : q ∈ s)
    (rp : M.rep p = Chart.horizontal) (rq : M.rep q = Chart.vertical)
    (hI : line[ℝ,p,q] ∈ ordinaryLines s) (hd : (pencil s p).card = 2) :
    ∃! u, SingletonRow P u := by
  let I := line[ℝ,p,q]
  have hIp : I ∈ pencil s p := mem_filter.mpr ⟨hI,left_mem_affineSpan_pair ..⟩
  have one : ((pencil s p).erase I).card = 1 := by rw [card_erase_of_mem hIp,hd]
  obtain ⟨L,hLset⟩ := card_eq_one.mp one
  have Lmem : L ∈ (pencil s p).erase I := by rw [hLset]; simp
  obtain ⟨hLI,hL⟩ := mem_erase.mp Lmem
  obtain ⟨Lo, pL⟩ := mem_filter.mp hL
  obtain ⟨⟨a,ha,b,hb,hab,habL⟩,_⟩ := mem_ordinaryLines.mp Lo
  have ap : a ∈ L := habL ▸ left_mem_affineSpan_pair ℝ a b
  have bp : b ∈ L := habL ▸ right_mem_affineSpan_pair ℝ a b
  have getz : ∃ z ∈ s, z ∈ L ∧ z ≠ p := by
    by_cases h : a = p
    · exact ⟨b,hb,bp,h ▸ hab.symm⟩
    · exact ⟨a,ha,ap,h⟩
  obtain ⟨z,hz,zL,hzp⟩ := getz
  have lineL := ordinary_line_eq Lo pL zL hzp.symm
  have rzfin : ∃ u ∈ P, M.rep z = Chart.point u := by
    rcases (M.image_eq _).mpr ⟨z,hz,rfl⟩ with i | i | last
    · exact (hzp (M.rep_injective hz hp (i.trans rp.symm))).elim
    · obtain rfl := M.rep_injective hz hq (i.trans rq.symm)
      exact (hLI lineL.symm).elim
    · exact last
  obtain ⟨u,hu,rz⟩ := rzfin
  have single := (M.row_ordinary hp hz rp hu rz).mp (lineL ▸ Lo)
  refine ⟨u,single,?_⟩
  intro v hv
  obtain ⟨w,hw,rw'⟩ := (M.image_eq _).mp (Or.inr (Or.inr ⟨v,hv.1,rfl⟩))
  have how := (M.row_ordinary hp hw rp hv.1 rw').mpr hv
  have hne : line[ℝ,p,w] ≠ I := by
    intro eqn
    have hwI : w ∈ I := eqn ▸ right_mem_affineSpan_pair ℝ p w
    have hj := (M.mem_line hp hq hw).mp hwI
    rw [rp,rq,rw'] at hj
    have bad := (join_ideal_pair _).mp hj
    exact one_ne_zero bad
  have hin : line[ℝ,p,w] ∈ (pencil s p).erase I :=
    mem_erase.mpr ⟨hne, mem_filter.mpr ⟨how,left_mem_affineSpan_pair ..⟩⟩
  rw [hLset, mem_singleton] at hin
  have wL := right_mem_affineSpan_pair ℝ p w
  rw [hin, ← lineL] at wL
  have join := (M.mem_line hp hz hw).mp wL
  rw [rp,rz,rw',onJoin_row] at join
  exact single.2 _ hv.1 join

theorem GridModel.ideal_line_ordinary (M : GridModel s P) {p q : ℝ²} (hp : p ∈ s) (hq : q ∈ s)
    (rp : M.rep p = Chart.horizontal) (rq : M.rep q = Chart.vertical) :
    line[ℝ,p,q] ∈ ordinaryLines s := by
  apply (ordinary_pair_iff hp hq (fun e => chart_h_ne_v (rp.symm.trans (e ▸ rq)))).mpr
  intro z hz hl
  have hj := (M.mem_line hp hq hz).mp hl
  rw [rp,rq] at hj
  have last := (join_ideal_pair _).mp hj
  rcases (M.image_eq _).mpr ⟨z,hz,rfl⟩ with i | i | ⟨u,_,i⟩
  · exact Or.inl (M.rep_injective hz hp (i.trans rp.symm))
  · exact Or.inr (M.rep_injective hz hq (i.trans rq.symm))
  · rw [i] at last
    exact (one_ne_zero last).elim

theorem GridModel.single_row_of_degree (M : GridModel s P) {p : ℝ²} (hp : p ∈ s)
    (rp : M.rep p = Chart.horizontal) (hd : (pencil s p).card = 2) : ∃! u, SingletonRow P u := by
  obtain ⟨q,hq,rq⟩ := (M.image_eq Chart.vertical).mp (Or.inr (Or.inl rfl))
  exact M.unique_row hp hq rp rq (M.ideal_line_ordinary hp hq rp rq) hd

end OMA.E210

end

section

/- Changes of a grid chart that keep the underlying configuration and its incidences. -/

open EuclideanGeometry Finset
open scoped Classical

namespace OMA.E210
namespace Chart

noncomputable def chartCases {A : Type*} (h v : A) (f : (ℝ × ℝ) → A) (p : Vec) : A :=
  if p 2 = 0 then if p 0 = 1 then h else v else f (p 0, p 1)

@[simp] theorem cases_horizontal {A : Type*} (h v : A) (f : (ℝ × ℝ) → A) :
    chartCases h v f horizontal = h := by simp [chartCases,horizontal]
@[simp] theorem cases_vertical {A : Type*} (h v : A) (f : (ℝ × ℝ) → A) :
    chartCases h v f vertical = v := by simp [chartCases,vertical]
@[simp] theorem cases_point {A : Type*} (h v : A) (f : (ℝ × ℝ) → A) (z : ℝ × ℝ) :
    chartCases h v f (point z) = f z := by simp [chartCases,point]

noncomputable def affineCoord (a b c d : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (a*p.1+b,c*p.2+d)

private noncomputable def affineRaw (a b c d : ℝ) (p : Vec) : Vec :=
  ![a * p 0 + b * p 2, c * p 1 + d * p 2, p 2]

noncomputable def affineEquiv (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) : Vec ≃ₗ[ℝ] Vec where
  toFun := affineRaw a b c d
  invFun := affineRaw (1/a) (-b/a) (1/c) (-d/c)
  map_add' x y := by ext i; fin_cases i <;> simp [affineRaw] <;> ring
  map_smul' t x := by ext i; fin_cases i <;> simp [affineRaw,smul_eq_mul] <;> ring
  left_inv x := by ext i; fin_cases i <;> simp [affineRaw] <;> field_simp [ha,hc] <;> ring
  right_inv x := by ext i; fin_cases i <;> simp [affineRaw] <;> field_simp [ha,hc] <;> ring

@[simp] theorem affineEquiv_horizontal (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    affineEquiv a b c d ha hc horizontal = a • horizontal := by
  ext i; fin_cases i <;> simp [affineEquiv,affineRaw,horizontal]
@[simp] theorem affineEquiv_vertical (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    affineEquiv a b c d ha hc vertical = c • vertical := by
  ext i; fin_cases i <;> simp [affineEquiv,affineRaw,vertical]
@[simp] theorem affineEquiv_point (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) (z : ℝ × ℝ) :
    affineEquiv a b c d ha hc (point z) = point (affineCoord a b c d z) := by
  ext i; fin_cases i <;> simp [affineEquiv,affineRaw,point,affineCoord]

private def xy (z : Vec) : Vec := ![z 1,z 0,z 2]
private def yz (z : Vec) : Vec := ![z 0,z 2,z 1]
def swapXY : Vec ≃ₗ[ℝ] Vec where
  toFun := xy
  invFun := xy
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' t x := by ext i; fin_cases i <;> rfl
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl

def swapYZ : Vec ≃ₗ[ℝ] Vec where
  toFun := yz
  invFun := yz
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' t x := by ext i; fin_cases i <;> rfl
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl

end Chart
open Chart

variable {s : Finset ℝ²} {P Q : Finset (ℝ × ℝ)}

/-- A projective coordinate change specified separately on the two ideal
points and on the finite points of the initial chart. -/
noncomputable def GridModel.rechart (M : GridModel s P) (F : Vector3 ≃ₗ[ℝ] Vector3)
    (u v : Vector3) (f : (ℝ × ℝ) → Vector3) (a b : ℝ) (g : (ℝ × ℝ) → ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hg : ∀ t ∈ P, g t ≠ 0)
    (hu : F horizontal = a • u) (hv : F vertical = b • v)
    (hf : ∀ t ∈ P, F (point t) = g t • f t)
    (hQ : ∀ z, chart (Q : Set _) z ↔ z = u ∨ z = v ∨ ∃ t ∈ P, z = f t) : GridModel s Q where
  E := M.E.trans F
  rep z := chartCases u v f (M.rep z)
  scale z := M.scale z * chartCases a b g (M.rep z)
  nonzero z hz := by
    apply mul_ne_zero (M.nonzero _ hz)
    rcases (M.image_eq _).mpr ⟨z,hz,rfl⟩ with h | h | ⟨t,ht,h⟩
    · simpa [h] using ha
    · simpa [h] using hb
    · simpa [h] using hg t ht
  expand z hz := by
    change F (M.E (liftPoint z)) = _
    rw [M.expand _ hz,map_smul]
    rcases (M.image_eq _).mpr ⟨z,hz,rfl⟩ with h | h | ⟨t,ht,h⟩
    · simp [h,hu,smul_smul]
    · simp [h,hv,smul_smul]
    · simp [h,hf t ht,smul_smul]
  image_eq t := by
    rw [hQ]
    constructor
    · rintro (rfl | rfl | ⟨z,hz,rfl⟩)
      · obtain ⟨w,hw,he⟩ := (M.image_eq _).mp (Or.inl rfl)
        exact ⟨w,hw,by simp [he]⟩
      · obtain ⟨w,hw,he⟩ := (M.image_eq _).mp (Or.inr (Or.inl rfl))
        exact ⟨w,hw,by simp [he]⟩
      · obtain ⟨w,hw,he⟩ := (M.image_eq _).mp (Or.inr (Or.inr ⟨z,hz,rfl⟩))
        exact ⟨w,hw,by simp [he]⟩
    · rintro ⟨z,hz,rfl⟩
      rcases (M.image_eq _).mpr ⟨z,hz,rfl⟩ with h | h | ⟨t,ht,h⟩
      · exact Or.inl (by simp [h])
      · exact Or.inr (Or.inl (by simp [h]))
      · exact Or.inr (Or.inr ⟨t,ht,by simp [h]⟩)

noncomputable def GridModel.affineModel (M : GridModel s P) (a b c d : ℝ) (ha : a ≠ 0) (hc : c ≠ 0) :
    GridModel s (P.image (affineCoord a b c d)) :=
  M.rechart (affineEquiv a b c d ha hc) horizontal vertical (point ∘ affineCoord a b c d) a c (fun _ => 1)
    ha hc (by simp) (by simp) (by simp) (by simp) (by
      intro z; simp only [chart, mem_coe, mem_image, Function.comp_apply]
      grind)

noncomputable def GridModel.swapModel (M : GridModel s P) : GridModel s (P.image Prod.swap) :=
  M.rechart swapXY vertical horizontal (point ∘ Prod.swap) 1 1 (fun _ => 1)
    one_ne_zero one_ne_zero (by simp)
    (by rw [one_smul]; ext i; fin_cases i <;> rfl)
    (by rw [one_smul]; ext i; fin_cases i <;> rfl)
    (by intro t _; rw [one_smul]; ext i; fin_cases i <;> rfl)
    (by intro z; simp only [chart,mem_coe,mem_image,Function.comp_apply]; grind)

/-- The singleton row becomes the vertical ideal point. The old vertical ideal
point becomes the origin. The horizontal direction is preserved. -/
noncomputable def GridModel.recipModel (M : GridModel s P) (t : GridPoint) (e : ℝ)
    (he : e ≠ 0) (ht : SingletonRow P t) : GridModel s (swapGrid P t e) := by
  classical
  let F := (affineEquiv e (-e*t.1) 1 (-t.2) he one_ne_zero).trans swapYZ
  let f := fun z : GridPoint => if z.2 = t.2 then vertical else point (swapPoint t e z)
  let g := fun z : GridPoint => if z.2 = t.2 then 1 else z.2 - t.2
  refine M.rechart F horizontal (point (0,0)) f e 1 g he one_ne_zero ?_ ?_ ?_ ?_ ?_
  · intro z hz
    by_cases h : z.2 = t.2
    · simp [g,h]
    · simpa [g,h] using sub_ne_zero.mpr h
  · change swapYZ (affineEquiv _ _ _ _ _ _ horizontal) = _
    rw [affineEquiv_horizontal,map_smul]
    rfl
  · change swapYZ (affineEquiv _ _ _ _ _ _ vertical) = _
    rw [affineEquiv_vertical,one_smul,one_smul]
    rfl
  · intro z hz
    change swapYZ (affineEquiv _ _ _ _ _ _ (point z)) = _
    rw [affineEquiv_point]
    by_cases h : z.2 = t.2
    · obtain rfl := ht.2 z hz h
      ext i; fin_cases i <;> simp [swapYZ,yz,affineCoord,f,g,point,vertical]
    · have hd := sub_ne_zero.mpr h
      ext i; fin_cases i <;> simp [swapYZ,yz,affineCoord,f,g,h,swapPoint,point,smul_eq_mul] <;>
        field_simp [hd] <;> ring
  · intro v
    constructor
    · rintro (rfl | rfl | ⟨w,hw,rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨t,ht.1,by simp [f]⟩)
      · change w ∈ insert (0,0) ((P.filter _).image (swapPoint t e)) at hw
        rcases mem_insert.mp hw with rfl | hw
        · exact Or.inr (Or.inl rfl)
        · obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
          obtain ⟨hp,hy⟩ := mem_filter.mp hz
          exact Or.inr (Or.inr ⟨z,hp,by simp [f,hy]⟩)
    · rintro (rfl | rfl | ⟨z,hz,rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨(0,0),by simp [swapGrid],rfl⟩)
      · by_cases h : z.2 = t.2
        · exact Or.inr (Or.inl (by simp [f,h]))
        · exact Or.inr (Or.inr ⟨swapPoint t e z, by
            apply mem_insert_of_mem
            exact mem_image_of_mem _ (mem_filter.mpr ⟨hz,h⟩), by simp [f,h]⟩)

@[simp] theorem GridModel.affineModel_rep (M : GridModel s P) (a b c d : ℝ)
    (ha : a ≠ 0) (hc : c ≠ 0) (z : ℝ²) :
    (M.affineModel a b c d ha hc).rep z =
      chartCases horizontal vertical (point ∘ affineCoord a b c d) (M.rep z) := rfl

@[simp] theorem GridModel.swapModel_rep (M : GridModel s P) (z : ℝ²) :
    M.swapModel.rep z = chartCases vertical horizontal (point ∘ Prod.swap) (M.rep z) := rfl

@[simp] theorem GridModel.recipModel_rep (M : GridModel s P) (t : GridPoint) (e : ℝ)
    (he : e ≠ 0) (ht : SingletonRow P t) (z : ℝ²) :
    (M.recipModel t e he ht).rep z =
      chartCases horizontal (point (0,0)) (fun w : GridPoint =>
        if w.2 = t.2 then vertical else point (swapPoint t e w)) (M.rep z) := rfl

end OMA.E210

end

section

namespace OMA.E210

/-- Every finite ordinary secant with a nonzero slope fails to have the
horizontal ideal point as an attachment. -/
def FreeHorizontal (P : Finset GridPoint) : Prop :=
  ∀ (a b : ℝ × ℝ) (m k : ℝ), a ∈ P → b ∈ P → a.2 < b.2 → m ≠ 0 →
    a.1 = m*a.2 + k → b.1 = m*b.2 + k →
    (∀ z ∈ P, z.1 = m*z.2+k → z=a ∨ z=b) →
    ¬ Chart.covered (Chart.chart (P : Set _)) (Chart.point a) (Chart.point b) Chart.horizontal

theorem FreeHorizontal.forceThird {P : Finset GridPoint} (free : FreeHorizontal P) :
    ForceThird P := by
  intro m pos ord a ha b hb hy eq
  classical
  by_contra! no
  have only (z : GridPoint) (hz : z ∈ P) (fz : offset m z = offset m a) : z = a ∨ z = b := by
    by_cases za : z = a
    · exact Or.inl za
    · exact Or.inr (no z hz fz za)
  have fa : a.1 = m*a.2 + offset m a := by dsimp [offset]; ring
  have fb : b.1 = m*b.2 + offset m a := by dsimp [offset] at eq ⊢; linarith only [eq]
  apply free a b m (offset m a) ha hb hy pos.ne' fa fb (fun z hz fz => only _ hz (by dsimp [offset] at *; linarith only [fz]))
  apply (Chart.horizontal_covered_iff _ _ _ _ _ fa fb hy).mpr
  refine ⟨1, by norm_num, by simpa using pos.le, ?_⟩
  intro z hz
  obtain ⟨h,h'⟩ | ⟨h,h'⟩ := extremal_separates ord ha hb hy eq only z hz
  · exact Or.inl ⟨h,by dsimp [offset] at h' ⊢; linarith⟩
  · exact Or.inr ⟨h,by dsimp [offset] at h' ⊢; linarith⟩

theorem FreeHorizontal.noCut {P : Finset GridPoint} (free : FreeHorizontal P) :
    ¬ Rect.Cut P Prod.fst Prod.snd := by
  rintro ⟨a,ha,b,hb,t,k,ht,hy,ea,eb,ordinary,sep⟩
  have fa : a.1 = (-t)*a.2 + k := by dsimp [Rect.F] at ea; linarith only [ea]
  have fb : b.1 = (-t)*b.2 + k := by dsimp [Rect.F] at eb; linarith only [eb]
  have no := free a b (-t) k ha hb hy (neg_ne_zero.mpr ht.ne') fa fb (fun z hz fz =>
    ordinary _ hz (by dsimp [Rect.F]; linarith only [fz]))
  apply no
  apply (Chart.horizontal_covered_iff _ _ _ _ _ fa fb hy).mpr
  refine ⟨-1, by norm_num, by simpa using ht.le, ?_⟩
  intro z hz
  obtain ⟨h,h'⟩ | ⟨h,h'⟩ := sep z hz
  · exact Or.inl ⟨h,by dsimp [Rect.F] at h'; linarith⟩
  · exact Or.inr ⟨h,by dsimp [Rect.F] at h'; linarith⟩

end OMA.E210

end

section

/- Transfer a signed-cone attachment in a finite chart back to the board's coordinates. -/

open EuclideanGeometry Finset
open scoped Classical
namespace OMA.E210

def attachedTo (s : Finset ℝ²) (w : ℝ²) (L : AffineSubspace ℝ ℝ²) : Prop :=
  ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
    ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧ ∀ z ∈ s, ∃ a b c : ℝ,
      liftPoint z = a • liftPoint p + b • (ε • liftPoint q) + c • (δ • liftPoint w) ∧
      ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))

theorem join_on_graph {a b : ℝ × ℝ} {m k : ℝ} {t : Vector3}
    (ha : a.1 = m*a.2 + k) (hb : b.1 = m*b.2 + k)
    (h : onJoin (Chart.point a) (Chart.point b) t) : t 0 = m * t 1 + k * t 2 := by
  obtain ⟨c,d,rfl⟩ := h
  simp [Chart.point,ha,hb]
  ring

variable {s : Finset ℝ²} {P : Finset (ℝ × ℝ)}

theorem GridModel.no_ordinary_covered (M : GridModel s P) {p : ℝ²} (hp : p ∈ s)
    (rp : M.rep p = Chart.horizontal) (hfree : ∀ L ∈ ordinaryLines s, ¬attachedTo s p L)
    (a b : ℝ × ℝ) (m k : ℝ) (ha : a ∈ P) (hb : b ∈ P)
    (hab : a.2 < b.2) (hm : m ≠ 0)
    (hA : a.1 = m*a.2 + k) (hB : b.1 = m*b.2 + k)
    (hOrd : ∀ z ∈ P, z.1 = m*z.2 + k → z=a ∨ z=b) :
    ¬ Chart.covered (Chart.chart (P : Set _)) (Chart.point a) (Chart.point b) Chart.horizontal := by
  intro hcov
  obtain ⟨u,hu,ru⟩ := (M.image_eq _).mp (Or.inr (Or.inr ⟨a,ha,rfl⟩))
  obtain ⟨v,hv,rv⟩ := (M.image_eq _).mp (Or.inr (Or.inr ⟨b,hb,rfl⟩))
  have huv : u ≠ v := by
    rintro rfl
    exact hab.ne (congrArg Prod.snd (chart_point_inj (ru.symm.trans rv)))
  have graph {z : ℝ²} (hz : z ∈ s) (hl : z ∈ line[ℝ,u,v]) :
      M.rep z 0 = m * M.rep z 1 + k * M.rep z 2 := by
    have hj := (M.mem_line hu hv hz).mp hl
    rw [ru,rv] at hj
    exact join_on_graph hA hB hj
  have ho : line[ℝ,u,v] ∈ ordinaryLines s := by
    apply (ordinary_pair_iff hu hv huv).mpr
    intro z hz hl
    have he := graph hz hl
    rcases (M.image_eq _).mpr ⟨z,hz,rfl⟩ with h | h | ⟨c,hc,h⟩
    · simp [h,Chart.horizontal] at he
    · simp [h,Chart.vertical] at he
      exact (hm he.symm).elim
    · rw [h] at he
      have hc' : c.1 = m*c.2+k := by simpa [Chart.point] using he
      rcases hOrd c hc hc' with rfl | rfl
      · exact Or.inl (M.rep_injective hz hu (h.trans ru.symm))
      · exact Or.inr (M.rep_injective hz hv (h.trans rv.symm))
  have hpL : p ∉ line[ℝ,u,v] := by
    intro hl
    have := graph hp hl
    simp [rp,Chart.horizontal] at this
  apply hfree _ ho
  refine ⟨u,hu,v,hv,huv,left_mem_affineSpan_pair ..,right_mem_affineSpan_pair ..,hpL,?_⟩
  have hset : (M.rep '' (s : Set ℝ²)) = Chart.chart (P : Set _) := by
    ext t
    exact (M.image_eq t).symm
  have hc : Chart.covered (M.rep '' (s : Set ℝ²)) (M.rep u) (M.rep v) (M.rep p) := by
    rw [hset,ru,rv,rp]
    exact hcov
  obtain ⟨ε,δ,hε,hδ,hc⟩ :=
    (Chart.covered_projective_iff M.E M.scale M.nonzero M.expand hu hv hp).mpr hc
  exact ⟨ε,δ,hε,hδ,fun z hz => hc _ ⟨z,hz,rfl⟩⟩

theorem free_of_zero {s : Finset ℝ²} {p : ℝ²}
    (h : ((ordinaryLines s).filter (attachedTo s p)).card = 0) :
    ∀ L ∈ ordinaryLines s, ¬attachedTo s p L := by
  intro L hL ha
  have hm : L ∈ (ordinaryLines s).filter (attachedTo s p) := mem_filter.mpr ⟨hL,ha⟩
  rw [card_eq_zero.mp h] at hm
  exact notMem_empty _ hm

end OMA.E210

end

section

/- Assemble the finite grid classification with changes of projective coordinates. -/

open Finset EuclideanGeometry
open scoped Classical

namespace OMA.E210

private theorem cut_image {P : Finset Rect.Pt} {g : Rect.Pt → Rect.Pt}
    {x y : Rect.Coord} (hx : ∀ z, (g z).1 = x z) (hy : ∀ z, (g z).2 = y z)
    (cut : Rect.Cut P x y) : Rect.Cut (P.image g) Prod.fst Prod.snd := by
  rcases cut with ⟨a,ha,b,hb,t,h,ht,hab,al,bl,ord,sep⟩
  have F (z) : Rect.F Prod.fst Prod.snd t (g z) = Rect.F x y t z := by simp [Rect.F,hx,hy]
  refine ⟨g a,mem_image_of_mem _ ha,g b,mem_image_of_mem _ hb,t,h,ht,?_,?_,?_,?_,?_⟩
  · simpa only [hy] using hab
  · exact (F a).trans al
  · exact (F b).trans bl
  · rintro z hz heq
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    exact (ord w hw ((F w).symm.trans heq)).imp (congrArg g) (congrArg g)
  · rintro z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    simpa only [hy,F] using sep w hw

/-- Select the affine rescaling sending the extrema of one coordinate to 0 and 1. -/
private theorem coordinate_scale (P : Finset Rect.Pt) (f : Rect.Coord)
    (large : 5 < P.card) (single : ∃ a, Rect.Single P f a) :
    ∃ A B : ℝ, 0 < A ∧ (∀ z ∈ P, 0 ≤ A*f z+B ∧ A*f z+B ≤ 1) ∧
    (∃ z ∈ P, A*f z+B = 0) ∧ (∃ z ∈ P, A*f z+B = 1) := by
  classical
  obtain ⟨a,ha,hs⟩ := single
  obtain ⟨l,hl,lo⟩ := P.exists_min_image f ⟨a,ha⟩
  obtain ⟨r,hr,hi⟩ := P.exists_max_image f ⟨a,ha⟩
  have lt : f l < f r := by
    by_contra! h
    have sing (z : Rect.Pt) (hz : z ∈ P) : z = a := by
      apply hs z hz
      exact le_antisymm ((hi z hz).trans (h.trans (lo a ha))) ((hi a ha).trans (h.trans (lo z hz)))
    have := Finset.card_le_one.mpr (fun z hz v hv => (sing z hz).trans (sing v hv).symm)
    omega
  let A := (f r - f l)⁻¹
  have pos : 0 < A := inv_pos.mpr (sub_pos.mpr lt)
  have unit : A * (f r - f l) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr lt.ne')
  refine ⟨A,-(A*f l),pos,?_,⟨l,hl,by ring⟩,⟨r,hr,by linarith only [unit]⟩⟩
  intro z hz
  constructor
  · linarith only [mul_le_mul_of_nonneg_left (lo z hz) pos.le]
  · linarith only [mul_le_mul_of_nonneg_left (hi z hz) pos.le,unit]

private theorem single_swap_iff {P : Finset Rect.Pt} {a : Rect.Pt} :
    Rect.Single P Prod.fst a ↔ SingletonRow (P.image Prod.swap) a.swap := by
  constructor
  · rintro ⟨ha,uq⟩
    refine ⟨mem_image_of_mem _ ha,?_⟩
    intro z hz hy
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
    exact congrArg Prod.swap (uq v hv hy)
  · rintro ⟨ha,uq⟩
    have hs : a ∈ P := by
      obtain ⟨v,hv,heq⟩ := mem_image.mp ha
      exact Prod.swap_injective heq ▸ hv
    exact ⟨hs,fun v hv heq => Prod.swap_injective (uq v.swap (mem_image_of_mem _ hv) heq)⟩


private def UnitData (P : Finset Rect.Pt) : Prop :=
  (∀ z ∈ P, Rect.InSquare Prod.fst Prod.snd z) ∧
  (∃ z ∈ P, z.1=0) ∧ (∃ z ∈ P, z.1=1) ∧ (∃ z ∈ P, z.2=0) ∧ (∃ z ∈ P, z.2=1)

private def SideData (P : Finset Rect.Pt) : Prop :=
  (∀ x y : ℝ, (x=0 ∨ x=1) → (y=0 ∨ y=1) → (x,y) ∈ P) ∧
  (∀ z ∈ P, (z.1=0 ∨ z.1=1) → (z.2=0 ∨ z.2=1))

private theorem swap_unit {P : Finset Rect.Pt} (u : UnitData P) :
    UnitData (P.image Prod.swap) := by
  obtain ⟨ub,⟨a,ha,ea⟩,⟨b,hb,eb⟩,⟨c,hc,ec⟩,d,hd,ed⟩ := u
  refine ⟨?_,⟨c.swap,mem_image_of_mem _ hc,ec⟩,⟨d.swap,mem_image_of_mem _ hd,ed⟩,
    ⟨a.swap,mem_image_of_mem _ ha,ea⟩,⟨b.swap,mem_image_of_mem _ hb,eb⟩⟩
  intro z hz
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
  obtain ⟨v1,v2,v3,v4⟩ := ub v hv
  exact ⟨v3,v4,v1,v2⟩

private theorem unit_finish {P : Finset Rect.Pt} (u : UnitData P)
    (sides : SideData P) (ssides : SideData (P.image Prod.swap))
    (uy : ∃! z, SingletonRow P z) (ux : ∃! z, SingletonRow (P.image Prod.swap) z)
    (safe : Rect.NoCuts P Prod.fst Prod.snd)
    (safe' : Rect.NoCuts (P.image Prod.swap) Prod.fst Prod.snd) : P.card ≤ 5 := by
  classical
  have xc : Rect.Corners P Prod.fst Prod.snd :=
    fun a b aa bb => ⟨(a,b),sides.1 a b aa bb,rfl,rfl⟩
  have boundary (z : Rect.Pt) (hz : z ∈ P) :
      Rect.Interior z ∨ ((z.1=0 ∨ z.1=1) ∧ (z.2=0 ∨ z.2=1)) := by
    by_cases onX : z.1=0 ∨ z.1=1
    · exact Or.inr ⟨onX,sides.2 z hz onX⟩
    · have onY : ¬(z.2=0 ∨ z.2=1) := fun h => onX (ssides.2 z.swap (mem_image_of_mem _ hz) h)
      obtain ⟨x0,x1,y0,y1⟩ := u.1 z hz
      rcases not_or.mp onX with ⟨n0,n1⟩
      rcases not_or.mp onY with ⟨m0,m1⟩
      exact Or.inl ⟨⟨lt_of_le_of_ne x0 (Ne.symm n0),lt_of_le_of_ne x1 n1⟩,
        lt_of_le_of_ne y0 (Ne.symm m0),lt_of_le_of_ne y1 m1⟩
  obtain ⟨sy,_,uniy⟩ := uy
  obtain ⟨sx,_,unix⟩ := ux
  apply Rect.rectangle_card_le_five P u.1 xc boundary
    (fun a b ha hb => (uniy _ ha).trans (uniy _ hb).symm)
    (fun a b ha hb => Prod.swap_injective
      ((unix _ (single_swap_iff.mp ha)).trans (unix _ (single_swap_iff.mp hb)).symm)) safe
  intro c d cut
  apply safe' c d
  rcases cut with ⟨a,ha,b,hb,t,h,ht,lt,fa,fb,ordinary,sep⟩
  have vx (z : Rect.Pt) : Rect.orient c Prod.fst z.swap = Rect.orient c Prod.snd z := by cases c <;> rfl
  have vy (z : Rect.Pt) : Rect.orient d Prod.snd z.swap = Rect.orient d Prod.fst z := by cases d <;> rfl
  have F (z) : Rect.F (Rect.orient c Prod.fst) (Rect.orient d Prod.snd) t z.swap =
       Rect.F (Rect.orient c Prod.snd) (Rect.orient d Prod.fst) t z := by simp [Rect.F,vx,vy]
  refine ⟨a.swap,mem_image_of_mem _ ha,b.swap,mem_image_of_mem _ hb,t,h,ht,?_,
    (F a).trans fa,(F b).trans fb,?_,?_⟩
  · simpa only [vy] using lt
  · intro z hz zz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    exact (ordinary _ hw ((F w).symm.trans zz)).imp (congrArg Prod.swap) (congrArg Prod.swap)
  · intro z hz
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    simpa only [vy,F] using sep w hw


private def Marked {s : Finset ℝ²} {P : Finset GridPoint} (M : GridModel s P)
    (p q : ℝ²) : Prop := M.rep p = Chart.horizontal ∨ M.rep q = Chart.horizontal

private theorem affine_marked {s : Finset ℝ²} {P : Finset GridPoint} {p q : ℝ²}
    (M : GridModel s P) (mark : Marked M p q)
    {a b c d : ℝ} (ha : a ≠ 0) (hc : c ≠ 0) :
    Marked (M.affineModel a b c d ha hc) p q := by
  rcases mark with hp | hq
  · exact Or.inl (by simp [hp])
  · exact Or.inr (by simp [hq])

private theorem recip_marked {s : Finset ℝ²} {P : Finset GridPoint} {p q : ℝ²}
    (M : GridModel s P) (mark : Marked M p q)
    (v : GridPoint) (e : ℝ) (he : e ≠ 0) (hv : SingletonRow P v) :
    Marked (M.recipModel v e he hv) p q := by
  rcases mark with hp | hq
  · exact Or.inl (by simp [hp])
  · exact Or.inr (by simp [hq])

private def reflectionFactor (b : Bool) : ℝ := if b then -1 else 1
private def reflectionOffset (b : Bool) : ℝ := if b then 1 else 0

private lemma reflectionFactor_ne (b : Bool) : reflectionFactor b ≠ 0 := by
  cases b <;> norm_num [reflectionFactor]

private theorem model_noCuts {s : Finset ℝ²} {P : Finset GridPoint} {p q : ℝ²}
    (M : GridModel s P) (mark : Marked M p q)
    (facts : ∀ {Q : Finset GridPoint} (N : GridModel s Q), Marked N p q →
      (∃! u, SingletonRow Q u) ∧ FreeHorizontal Q) :
    Rect.NoCuts P Prod.fst Prod.snd := by
  intro c d cut
  let g := Chart.affineCoord (reflectionFactor c) (reflectionOffset c) (reflectionFactor d) (reflectionOffset d)
  let N := M.affineModel (reflectionFactor c) (reflectionOffset c) (reflectionFactor d) (reflectionOffset d)
      (reflectionFactor_ne c) (reflectionFactor_ne d)
  have nc := (facts N (affine_marked M mark _ _)).2.noCut
  apply nc
  apply cut_image (g := g) _ _ cut
  · intro z
    cases c <;> simp [g, Chart.affineCoord,Rect.orient,reflectionFactor,reflectionOffset]
    ring
  · intro z
    cases d <;> simp [g, Chart.affineCoord,Rect.orient,reflectionFactor,reflectionOffset]
    ring

private theorem model_sides {s : Finset ℝ²} {P : Finset GridPoint} {p q : ℝ²}
    (M : GridModel s P) (mark : Marked M p q)
    (facts : ∀ {Q : Finset GridPoint} (N : GridModel s Q), Marked N p q →
      (∃! u, SingletonRow Q u) ∧ FreeHorizontal Q)
    (u : UnitData P) : SideData P := by
  obtain ⟨z,hz,uz⟩ := (facts M mark).1
  obtain ⟨bounds,a,b,c,d⟩ := u
  apply unit_sides hz uz _ _ bounds a b c d
  · intro e he
    have en : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    let N := M.affineModel e 0 1 0 en one_ne_zero
    have force := (facts N (affine_marked M mark _ _)).2.forceThird
    have agree : Chart.affineCoord e 0 1 0 = orientX e := by
      funext a
      simp [Chart.affineCoord,orientX]
    exact agree ▸ force
  · intro e he
    have en : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
    exact (facts (M.recipModel z e en hz) (recip_marked M mark z e en hz)).2.forceThird

/-- Projective grid criterion for excluding two exceptional points on an ordinary line. -/
theorem grid_card_le_five {s : Finset ℝ²} {P : Finset GridPoint} {p q : ℝ²}
    (M : GridModel s P) (hp : M.rep p = Chart.horizontal) (hq : M.rep q = Chart.vertical)
    (facts : ∀ {Q : Finset GridPoint} (N : GridModel s Q),
      (N.rep p = Chart.horizontal ∨ N.rep q = Chart.horizontal) →
      (∃! u, SingletonRow Q u) ∧ FreeHorizontal Q) : P.card ≤ 5 := by
  classical
  by_contra! large
  have singleY := (facts M (.inl hp)).1.exists
  have singleX := (facts M.swapModel (.inr (by simp [hq]))).1.exists
  obtain ⟨w,hw⟩ := singleX
  obtain ⟨z,hz,hwz⟩ := mem_image.mp hw.1
  have sx : Rect.Single P Prod.fst z := single_swap_iff.mpr (hwz ▸ hw)
  obtain ⟨a,b,ha,xb,xa0,xa1⟩ := coordinate_scale P Prod.fst large ⟨z,sx⟩
  obtain ⟨c,d,hc,yb,ya0,ya1⟩ := coordinate_scale P Prod.snd large singleY
  let g := Chart.affineCoord a b c d
  let Q := P.image g
  let N := M.affineModel a b c d ha.ne' hc.ne'
  have mark : Marked N p q := affine_marked M (Or.inl hp) _ _
  have mark' : Marked N.swapModel p q := Or.inr (by simp [N,hq])
  obtain ⟨x0,hx0,e0⟩ := xa0
  obtain ⟨x1,hx1,e1⟩ := xa1
  obtain ⟨y0,hy0,f0⟩ := ya0
  obtain ⟨y1,hy1,f1⟩ := ya1
  have unit : UnitData Q := by
    refine ⟨?_,⟨g x0,mem_image_of_mem _ hx0,e0⟩,⟨g x1,mem_image_of_mem _ hx1,e1⟩,
      ⟨g y0,mem_image_of_mem _ hy0,f0⟩,⟨g y1,mem_image_of_mem _ hy1,f1⟩⟩
    intro v hv
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    exact ⟨(xb u hu).1,(xb u hu).2,(yb u hu).1,(yb u hu).2⟩
  have inj : Function.Injective g := by
    intro u v e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    apply Prod.ext (mul_left_cancel₀ ha.ne' _) (mul_left_cancel₀ hc.ne' _)
    · simpa [g,Chart.affineCoord] using e1
    · simpa [g,Chart.affineCoord] using e2
  have cq : Q.card ≤ 5 := unit_finish unit (model_sides N mark facts unit)
    (model_sides N.swapModel mark' facts (swap_unit unit))
    (facts N mark).1 (facts N.swapModel mark').1 (model_noCuts N mark facts)
    (model_noCuts N.swapModel mark' facts)
  have eqn : Q.card = P.card := card_image_of_injective _ inj
  omega

end OMA.E210

end

section

/- The eight-point hypothesis rules out two exceptional endpoints on an ordinary line. -/
open EuclideanGeometry Finset OMA.E210
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem OMA.E210.h3_proof : OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1.H3 := by
  classical
  intro s hs _
  dsimp only
  intro L hL p hp q hq hpL hqL hdP haP hdQ haQ
  have dp : (pencil s p).card = 2 := hdP
  have dq : (pencil s q).card = 2 := hdQ
  have ap : ∀ l ∈ ordinaryLines s, ¬attachedTo s p l :=
    fun _ hl ha => (filter_eq_empty_iff.mp (card_eq_zero.mp haP)) hl ha
  have aq : ∀ l ∈ ordinaryLines s, ¬attachedTo s q l :=
    fun _ hl ha => (filter_eq_empty_iff.mp (card_eq_zero.mp haQ)) hl ha
  by_contra hne
  have hO : line[ℝ,p,q] ∈ ordinaryLines s := by rwa [ordinary_line_eq hL hpL hqL hne]
  obtain ⟨P,M,rp,rq,hcard⟩ := initial_grid hp hq hne hO
  have hgrid := grid_card_le_five M rp rq (by
    intro Q N h
    rcases h with h | h
    · exact ⟨N.single_row_of_degree hp h dp, N.no_ordinary_covered hp h ap⟩
    · exact ⟨N.single_row_of_degree hq h dq, N.no_ordinary_covered hq h aq⟩)
  omega

end

end

section

/-
Kelly–Moser local attachment lemmas (`d w = 0 → 3 ≤ A w` and `d w = 1 → 2 ≤ A w`) via polar
duality centered at `w` and strictly exposed vertices of the dual line arrangement.
-/

namespace Erdos210KM

open EuclideanGeometry Finset
open scoped BigOperators Classical

private noncomputable def det2 (u v : ℝ²) : ℝ :=
  u.ofLp 0 * v.ofLp 1 - u.ofLp 1 * v.ofLp 0

private noncomputable def dot2 (u v : ℝ²) : ℝ :=
  u.ofLp 0 * v.ofLp 0 + u.ofLp 1 * v.ofLp 1

private noncomputable def perp (u : ℝ²) : ℝ² :=
  !₂[-u.ofLp 1, u.ofLp 0]

private lemma dot2_comm (u v : ℝ²) : dot2 u v = dot2 v u := by
  dsimp [dot2]; ring

private lemma dot2_add_left (u v w : ℝ²) : dot2 (u + v) w = dot2 u w + dot2 v w := by
  simp only [dot2, PiLp.add_apply]; ring

private lemma dot2_add_right (u v w : ℝ²) : dot2 u (v + w) = dot2 u v + dot2 u w := by
  simp only [dot2, PiLp.add_apply]; ring

private lemma dot2_sub_left (u v w : ℝ²) : dot2 (u - v) w = dot2 u w - dot2 v w := by
  simp only [dot2, PiLp.sub_apply]; ring

private lemma dot2_sub_right (u v w : ℝ²) : dot2 u (v - w) = dot2 u v - dot2 u w := by
  simp only [dot2, PiLp.sub_apply]; ring

private lemma dot2_smul_left (c : ℝ) (u v : ℝ²) : dot2 (c • u) v = c * dot2 u v := by
  simp only [dot2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma dot2_smul_right (c : ℝ) (u v : ℝ²) : dot2 u (c • v) = c * dot2 u v := by
  simp only [dot2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma dot2_self_pos {u : ℝ²} (hu : u ≠ 0) : 0 < dot2 u u := by
  have hnn : 0 ≤ dot2 u u := by dsimp [dot2]; nlinarith
  rcases eq_or_lt_of_le hnn with h0 | hpos
  · exfalso; apply hu; ext i
    dsimp [dot2] at h0
    match i with
    | 0 => change u.ofLp 0 = 0; nlinarith
    | 1 => change u.ofLp 1 = 0; nlinarith
  · exact hpos

private lemma det2_anticomm (u v : ℝ²) : det2 u v = -det2 v u := by
  dsimp [det2]; ring

private lemma det2_self (u : ℝ²) : det2 u u = 0 := by
  dsimp [det2]; ring

private lemma det2_add_left (u v w : ℝ²) : det2 (u + v) w = det2 u w + det2 v w := by
  simp only [det2, PiLp.add_apply]; ring

private lemma det2_smul_left (c : ℝ) (u v : ℝ²) : det2 (c • u) v = c * det2 u v := by
  simp only [det2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma det2_smul_right (c : ℝ) (u v : ℝ²) : det2 u (c • v) = c * det2 u v := by
  simp only [det2, PiLp.smul_apply, smul_eq_mul]; ring

private lemma dot2_perp_left (u v : ℝ²) : dot2 (perp u) v = det2 u v := by
  simp only [dot2, perp, det2, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

private lemma dot2_perp_right (u v : ℝ²) : dot2 u (perp v) = -det2 u v := by
  simp only [dot2, perp, det2, Matrix.cons_val_zero, Matrix.cons_val_one]; ring

private lemma dot2_self_perp (u : ℝ²) : dot2 u (perp u) = 0 := by
  rw [dot2_perp_right, det2_self, neg_zero]

private lemma perp_ne_zero {u : ℝ²} (hu : u ≠ 0) : perp u ≠ 0 := by
  intro h; apply hu; ext i
  have h0 := congrArg (fun x : ℝ² => x.ofLp 0) h
  have h1 := congrArg (fun x : ℝ² => x.ofLp 1) h
  simp only [perp, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  change -u.ofLp 1 = 0 at h0
  change u.ofLp 0 = 0 at h1
  match i with
  | 0 => exact h1
  | 1 => change u.ofLp 1 = 0; linarith

private lemma eq_of_det2_eq_zero {u v : ℝ²} (hu : u ≠ 0) (hdet : det2 u v = 0) :
    ∃ t : ℝ, v = t • u := by
  by_cases h0 : u.ofLp 0 ≠ 0
  · refine ⟨v.ofLp 0 / u.ofLp 0, ?_⟩
    ext i; match i with
    | 0 => change v.ofLp 0 = (v.ofLp 0 / u.ofLp 0) * u.ofLp 0; field_simp [h0]
    | 1 =>
      change v.ofLp 1 = (v.ofLp 0 / u.ofLp 0) * u.ofLp 1
      dsimp [det2] at hdet; field_simp [h0]; linarith
  · push Not at h0
    have h1 : u.ofLp 1 ≠ 0 := by
      intro h1; apply hu; ext i; match i with | 0 => exact h0 | 1 => exact h1
    refine ⟨v.ofLp 1 / u.ofLp 1, ?_⟩
    ext i; match i with
    | 0 =>
      change v.ofLp 0 = (v.ofLp 1 / u.ofLp 1) * u.ofLp 0
      dsimp [det2] at hdet; rw [h0] at hdet ⊢
      have hv0 : v.ofLp 0 = 0 := (mul_eq_zero.mp (show u.ofLp 1 * v.ofLp 0 = 0 by linarith)).resolve_left h1
      rw [hv0, mul_zero]
    | 1 => change v.ofLp 1 = (v.ofLp 1 / u.ofLp 1) * u.ofLp 1; field_simp [h1]

private lemma mem_line_iff_det2 {a b c : ℝ²} (hab : a ≠ b) :
    c ∈ line[ℝ, a, b] ↔ det2 (b - a) (c - a) = 0 := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    have : AffineMap.lineMap a b t - a = t • (b - a) := by
      rw [AffineMap.lineMap_apply_module']; abel
    rw [this, det2_smul_right, det2_self, mul_zero]
  · intro hdet
    obtain ⟨t, ht⟩ := eq_of_det2_eq_zero (sub_ne_zero.mpr hab.symm) hdet
    refine ⟨t, ?_⟩
    rw [AffineMap.lineMap_apply_module']
    have : c = t • (b - a) + a := eq_add_of_sub_eq ht
    exact this.symm

private lemma basis_decomp {u v : ℝ²} (hdet : det2 u v ≠ 0) (z : ℝ²) :
    ∃ a b : ℝ, z = a • u + b • v := by
  set D := det2 u v
  refine ⟨det2 z v / D, det2 u z / D, ?_⟩
  ext i; match i with
  | 0 =>
    change z.ofLp 0 = (det2 z v / D) * u.ofLp 0 + (det2 u z / D) * v.ofLp 0
    field_simp [hdet]; dsimp [D, det2]; ring
  | 1 =>
    change z.ofLp 1 = (det2 z v / D) * u.ofLp 1 + (det2 u z / D) * v.ofLp 1
    field_simp [hdet]; dsimp [D, det2]; ring

private lemma decomp_orth {h : ℝ²} (hh : h ≠ 0) (r : ℝ²) (hr : dot2 h r = 1) :
    r = (1 / dot2 h h) • h + (dot2 (perp h) r / dot2 h h) • perp h := by
  set D := dot2 h h
  have hpos : 0 < D := dot2_self_pos hh
  have hne : D ≠ 0 := hpos.ne'
  ext i; match i with
  | 0 =>
    change r.ofLp 0 = (1 / D) * h.ofLp 0 + (dot2 (perp h) r / D) * (perp h).ofLp 0
    field_simp [hne]
    simp only [D, dot2, perp, Matrix.cons_val_zero, Matrix.cons_val_one] at hr ⊢
    linear_combination h.ofLp 0 * hr
  | 1 =>
    change r.ofLp 1 = (1 / D) * h.ofLp 1 + (dot2 (perp h) r / D) * (perp h).ofLp 1
    field_simp [hne]
    simp only [D, dot2, perp, Matrix.cons_val_zero, Matrix.cons_val_one] at hr ⊢
    linear_combination h.ofLp 1 * hr

/- ### Polar duality centered at `w` -/

private noncomputable def evalDual (w z u : ℝ²) : ℝ :=
  dot2 (z - w) u + 1

private noncomputable def dualInter (w p q : ℝ²) : ℝ² :=
  let dp := p - w
  let dq := q - w
  let D := det2 dp dq
  !₂[(dp.ofLp 1 - dq.ofLp 1) / D, (dq.ofLp 0 - dp.ofLp 0) / D]

private lemma evalDual_dualInter_left {w p q : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0) :
    evalDual w p (dualInter w p q) = 0 := by
  set D := det2 (p - w) (q - w)
  change (p - w).ofLp 0 * (((p - w).ofLp 1 - (q - w).ofLp 1) / D) +
    (p - w).ofLp 1 * (((q - w).ofLp 0 - (p - w).ofLp 0) / D) + 1 = 0
  field_simp [hdet]; dsimp [D, det2]; ring

private lemma evalDual_dualInter_right {w p q : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0) :
    evalDual w q (dualInter w p q) = 0 := by
  set D := det2 (p - w) (q - w)
  change (q - w).ofLp 0 * (((p - w).ofLp 1 - (q - w).ofLp 1) / D) +
    (q - w).ofLp 1 * (((q - w).ofLp 0 - (p - w).ofLp 0) / D) + 1 = 0
  field_simp [hdet]; dsimp [D, det2]; ring

private lemma dualInter_unique {w p q u : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0)
    (hp : evalDual w p u = 0) (hq : evalDual w q u = 0) :
    u = dualInter w p q := by
  set d := u - dualInter w p q
  have hp' : dot2 (p - w) d = 0 := by
    dsimp [d]; rw [dot2_sub_right]
    have h1 : dot2 (p - w) u = -1 := by dsimp [evalDual] at hp; linarith
    have h2 : dot2 (p - w) (dualInter w p q) = -1 := by
      have := evalDual_dualInter_left hdet; dsimp [evalDual] at this; linarith
    linarith
  have hq' : dot2 (q - w) d = 0 := by
    dsimp [d]; rw [dot2_sub_right]
    have h1 : dot2 (q - w) u = -1 := by dsimp [evalDual] at hq; linarith
    have h2 : dot2 (q - w) (dualInter w p q) = -1 := by
      have := evalDual_dualInter_right hdet; dsimp [evalDual] at this; linarith
    linarith
  have h0 : d = 0 := by
    dsimp [dot2] at hp' hq'
    dsimp [det2] at hdet
    ext i; match i with
    | 0 =>
      change d.ofLp 0 = 0
      have : ((p.ofLp 0 - w.ofLp 0) * (q.ofLp 1 - w.ofLp 1) - (p.ofLp 1 - w.ofLp 1) * (q.ofLp 0 - w.ofLp 0)) * d.ofLp 0 = 0 := by
        linear_combination (q.ofLp 1 - w.ofLp 1) * hp' - (p.ofLp 1 - w.ofLp 1) * hq'
      exact (mul_eq_zero.mp this).resolve_left hdet
    | 1 =>
      change d.ofLp 1 = 0
      have : ((p.ofLp 0 - w.ofLp 0) * (q.ofLp 1 - w.ofLp 1) - (p.ofLp 1 - w.ofLp 1) * (q.ofLp 0 - w.ofLp 0)) * d.ofLp 1 = 0 := by
        linear_combination (p.ofLp 0 - w.ofLp 0) * hq' - (q.ofLp 0 - w.ofLp 0) * hp'
      exact (mul_eq_zero.mp this).resolve_left hdet
  exact sub_eq_zero.mp h0

private lemma mem_line_iff_evalDual_zero {w p q z : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0) :
    z ∈ line[ℝ, p, q] ↔ evalDual w z (dualInter w p q) = 0 := by
  have hpq : p ≠ q := by
    intro h; subst h; exact hdet (det2_self _)
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    have hsub : AffineMap.lineMap p q t - w = (1 - t) • (p - w) + t • (q - w) := by
      rw [AffineMap.lineMap_apply_module']; module
    dsimp [evalDual]
    rw [hsub, dot2_add_left, dot2_smul_left, dot2_smul_left]
    have h1 := evalDual_dualInter_left hdet
    have h2 := evalDual_dualInter_right hdet
    dsimp [evalDual] at h1 h2
    have h1' : dot2 (p - w) (dualInter w p q) = -1 := by linarith
    have h2' : dot2 (q - w) (dualInter w p q) = -1 := by linarith
    rw [h1', h2']; ring
  · intro hz
    obtain ⟨a, b, hab⟩ := basis_decomp hdet (z - w)
    have hsum : a + b = 1 := by
      dsimp [evalDual] at hz
      rw [hab, dot2_add_left, dot2_smul_left, dot2_smul_left] at hz
      have h1 := evalDual_dualInter_left hdet
      have h2 := evalDual_dualInter_right hdet
      dsimp [evalDual] at h1 h2
      have h1' : dot2 (p - w) (dualInter w p q) = -1 := by linarith
      have h2' : dot2 (q - w) (dualInter w p q) = -1 := by linarith
      rw [h1', h2'] at hz; linarith
    refine ⟨b, ?_⟩
    rw [AffineMap.lineMap_apply_module']
    have ha : a = 1 - b := by linarith
    rw [ha] at hab
    have : z = b • (q - p) + p := by
      calc z = (z - w) + w := (sub_add_cancel z w).symm
        _ = (1 - b) • (p - w) + b • (q - w) + w := by rw [hab]
        _ = b • (q - p) + p := by module
    exact this.symm

private lemma not_mem_line_of_det2_ne_zero {w p q : ℝ²} (hdet : det2 (p - w) (q - w) ≠ 0) :
    w ∉ line[ℝ, p, q] := by
  rw [mem_line_iff_evalDual_zero hdet]
  simp [evalDual, dot2]

/- ### Perturbed maximization produces strictly exposed vertices -/

private lemma exists_strictly_exposed (s V : Finset ℝ²) (w : ℝ²)
    (hV : V.Nonempty) (h₀ : ℝ²) (hh₀ : h₀ ≠ 0) :
    ∃ X ∈ V, ∃ h : ℝ², h ≠ 0 ∧
      (∀ Y ∈ V, Y ≠ X → dot2 h Y < dot2 h X) ∧
      (∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0) ∧
      (∀ Y ∈ V, dot2 h₀ Y ≤ dot2 h₀ X) := by
  obtain ⟨X₀, hX₀V, hmax₀⟩ := V.exists_max_image (fun Y => dot2 h₀ Y) hV
  let V₀ := V.filter (fun Y => dot2 h₀ Y = dot2 h₀ X₀)
  have hV₀_ne : V₀.Nonempty := ⟨X₀, Finset.mem_filter.mpr ⟨hX₀V, rfl⟩⟩
  let h₁ := perp h₀
  obtain ⟨X, hXV₀, hmax₁⟩ := V₀.exists_max_image (fun Y => dot2 h₁ Y) hV₀_ne
  obtain ⟨hXV, hX_eq⟩ := Finset.mem_filter.mp hXV₀
  have hmax₀X : ∀ Y ∈ V, dot2 h₀ Y ≤ dot2 h₀ X := fun Y hY => hX_eq ▸ hmax₀ Y hY
  -- Compute gap threshold for ε > 0 so h = h₀ + ε • h₁ exposes X strictly
  let V_out := V.filter (fun Y => dot2 h₀ Y < dot2 h₀ X)
  have hε_bound : ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ∀ Y ∈ V_out, dot2 (h₀ + ε • h₁) Y < dot2 (h₀ + ε • h₁) X := by
    by_cases hout : V_out.Nonempty
    · have hexY : ∀ Y ∈ V_out, ∃ δY : ℝ, 0 < δY ∧
          ∀ ε : ℝ, 0 < ε → ε < δY → dot2 (h₀ + ε • h₁) Y < dot2 (h₀ + ε • h₁) X := by
        intro Y hY
        have hlt : dot2 h₀ Y < dot2 h₀ X := (Finset.mem_filter.mp hY).2
        let gap := dot2 h₀ X - dot2 h₀ Y
        have hgap : 0 < gap := sub_pos.mpr hlt
        let diff := dot2 h₁ Y - dot2 h₁ X
        refine ⟨gap / (|diff| + 1), by positivity, fun ε hε0 hεδ => ?_⟩
        rw [dot2_add_left, dot2_add_left, dot2_smul_left, dot2_smul_left]
        have h1 : ε * (|diff| + 1) < gap := (lt_div_iff₀ (by positivity : (0 : ℝ) < |diff| + 1)).mp hεδ
        have h2 : diff ≤ |diff| := le_abs_self _
        have h3 : ε * diff < gap := by nlinarith
        dsimp [gap, diff] at h3
        linarith
      choose δY hδY_pos hδY_ok using hexY
      let δs := V_out.attach.image (fun y => δY y.1 y.2)
      have hδs_ne : δs.Nonempty := by
        obtain ⟨y, hy⟩ := hout
        exact ⟨δY y hy, Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩⟩
      let δ := δs.min' hδs_ne
      have hδ_pos : 0 < δ := by
        obtain ⟨y, _, hy⟩ := Finset.mem_image.mp (δs.min'_mem hδs_ne)
        change 0 < δs.min' hδs_ne; rw [← hy]; exact hδY_pos y.1 y.2
      refine ⟨δ, hδ_pos, fun ε hε0 hεδ Y hY => hδY_ok Y hY ε hε0 (lt_of_lt_of_le hεδ ?_)⟩
      exact δs.min'_le _ (Finset.mem_image.mpr ⟨⟨Y, hY⟩, Finset.mem_attach _ _, rfl⟩)
    · refine ⟨1, zero_lt_one, fun _ _ _ Y hY => absurd ⟨Y, hY⟩ hout⟩
  obtain ⟨δ, hδ_pos, hδ_ok⟩ := hε_bound
  -- Avoid the finitely many ε where det2 (h₀ + ε • h₁) (z - w) = 0
  let bad : Finset ℝ :=
    (s.filter (fun z => z ≠ w)).image (fun z => -det2 h₀ (z - w) / det2 h₁ (z - w))
  have hex_ε : ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε ∉ bad := by
    have hinf : (Set.Ioo (0 : ℝ) δ).Infinite := Set.Ioo_infinite hδ_pos
    obtain ⟨ε, hεI, hεB⟩ := (hinf.sdiff (bad.finite_toSet)).nonempty
    exact ⟨ε, hεI.1, hεI.2, hεB⟩
  obtain ⟨ε, hε0, hεδ, hε_not_bad⟩ := hex_ε
  let h := h₀ + ε • h₁
  have hh_ne : h ≠ 0 := by
    intro hzero
    have hdot := congrArg (fun v => dot2 h₀ v) hzero
    rw [dot2_add_right, dot2_smul_right, dot2_self_perp, mul_zero, add_zero] at hdot
    have hpos := dot2_self_pos hh₀
    have hz0 : dot2 h₀ 0 = 0 := by simp [dot2]
    linarith
  refine ⟨X, hXV, h, hh_ne, ?_, ?_, hmax₀X⟩
  · intro Y hYV hYX
    rcases lt_or_eq_of_le (hmax₀X Y hYV) with hlt | heq
    · exact hδ_ok ε hε0 hεδ Y (Finset.mem_filter.mpr ⟨hYV, hlt⟩)
    · have hYV₀ : Y ∈ V₀ := Finset.mem_filter.mpr ⟨hYV, heq.trans hX_eq⟩
      have hle₁ := hmax₁ Y hYV₀
      have hne₁ : dot2 h₁ Y ≠ dot2 h₁ X := by
        intro heq₁
        apply hYX
        have hdot0 : dot2 h₀ (Y - X) = 0 := by rw [dot2_sub_right]; linarith
        have hdot1 : dot2 (perp h₀) (Y - X) = 0 := by rw [dot2_sub_right]; linarith
        have hdet : det2 h₀ (Y - X) = 0 := by rw [← dot2_perp_left]; exact hdot1
        obtain ⟨t, ht⟩ := eq_of_det2_eq_zero hh₀ hdet
        rw [ht, dot2_smul_right] at hdot0
        have ht0 : t = 0 := (mul_eq_zero.mp hdot0).resolve_right (dot2_self_pos hh₀).ne'
        rw [ht0, zero_smul] at ht
        exact sub_eq_zero.mp ht
      have hlt₁ : dot2 h₁ Y < dot2 h₁ X := lt_of_le_of_ne hle₁ hne₁
      dsimp [h]
      rw [dot2_add_left, dot2_add_left, dot2_smul_left, dot2_smul_left]
      nlinarith
  · intro z hzs hzw hdet0
    dsimp [h] at hdet0
    rw [det2_add_left, det2_smul_left] at hdet0
    by_cases hd1 : det2 h₁ (z - w) = 0
    · rw [hd1, mul_zero, add_zero] at hdet0
      have hdot : dot2 h₀ (z - w) = 0 := by
        have : det2 (perp h₀) (z - w) = -dot2 h₀ (z - w) := by
          simp only [det2, perp, dot2, Matrix.cons_val_zero, Matrix.cons_val_one]; ring
        linarith
      obtain ⟨t, ht⟩ := eq_of_det2_eq_zero hh₀ hdet0
      rw [ht, dot2_smul_right] at hdot
      have ht0 : t = 0 := (mul_eq_zero.mp hdot).resolve_right (dot2_self_pos hh₀).ne'
      rw [ht0, zero_smul] at ht
      exact hzw (sub_eq_zero.mp ht)
    · have hε_eq : ε = -det2 h₀ (z - w) / det2 h₁ (z - w) := by
        field_simp [hd1]; linarith
      apply hε_not_bad
      exact Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzs, hzw⟩, hε_eq.symm⟩

/- ### Main Kelly–Moser local attachment theorem -/

private lemma exists_three_directions {s : Finset ℝ²} (hcol : ¬ Collinear ℝ (s : Set ℝ²))
    (hno2 : ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M))
    {w : ℝ²} (hw : w ∈ s) :
    ∃ p₁ ∈ s, ∃ p₂ ∈ s, ∃ p₃ ∈ s,
      det2 (p₁ - w) (p₂ - w) ≠ 0 ∧ det2 (p₁ - w) (p₃ - w) ≠ 0 ∧ det2 (p₂ - w) (p₃ - w) ≠ 0 := by
  have hex1 : ∃ p₁ ∈ s, p₁ ≠ w := by
    by_contra! hall
    apply hcol
    refine (collinear_singleton ℝ w).subset fun z hz => ?_
    simp [hall z hz]
  obtain ⟨p₁, hp₁s, hp₁ne⟩ := hex1
  have hL1 : Module.finrank ℝ (line[ℝ, w, p₁]).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hp₁ne.symm)]
  have hex2 : ∃ p₂ ∈ s, p₂ ∉ line[ℝ, w, p₁] := by
    by_contra! hall
    apply hcol
    rw [collinear_iff_finrank_le_one]
    have hle : vectorSpan ℝ (s : Set ℝ²) ≤ (line[ℝ, w, p₁]).direction := by
      rw [← direction_affineSpan]
      exact AffineSubspace.direction_le (affineSpan_le.mpr fun z hz => hall z hz)
    exact (Submodule.finrank_mono hle).trans hL1.le
  obtain ⟨p₂, hp₂s, hp₂not⟩ := hex2
  have hp₂ne : p₂ ≠ w := fun h => hp₂not (h ▸ left_mem_affineSpan_pair ℝ w p₁)
  have hL2 : Module.finrank ℝ (line[ℝ, w, p₂]).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hp₂ne.symm)]
  have hex3 : ∃ p₃ ∈ s, p₃ ∉ line[ℝ, w, p₁] ∧ p₃ ∉ line[ℝ, w, p₂] := by
    by_contra! hall
    apply hno2
    refine ⟨line[ℝ, w, p₁], line[ℝ, w, p₂], hL1, hL2, fun z hz => ?_⟩
    by_cases h1 : z ∈ line[ℝ, w, p₁]
    · exact Or.inl h1
    · exact Or.inr (hall z hz h1)
  obtain ⟨p₃, hp₃s, hp₃not1, hp₃not2⟩ := hex3
  refine ⟨p₁, hp₁s, p₂, hp₂s, p₃, hp₃s, ?_, ?_, ?_⟩
  · exact (mem_line_iff_det2 hp₁ne.symm).not.mp hp₂not
  · exact (mem_line_iff_det2 hp₁ne.symm).not.mp hp₃not1
  · exact (mem_line_iff_det2 hp₂ne.symm).not.mp hp₃not2

/-- The dual vertex set `V` of all pairwise intersections of dual lines `ℓ_p, ℓ_q` (`p, q ∈ s \ {w}`). -/
private noncomputable def dualVerts (s : Finset ℝ²) (w : ℝ²) : Finset ℝ² :=
  ((s ×ˢ s).filter (fun pq => det2 (pq.1 - w) (pq.2 - w) ≠ 0)).image (fun pq => dualInter w pq.1 pq.2)

private lemma dualVerts_not_collinear {s : Finset ℝ²} (hcol : ¬ Collinear ℝ (s : Set ℝ²))
    (hno2 : ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M))
    {w : ℝ²} (hw : w ∈ s) :
    ¬ Collinear ℝ (dualVerts s w : Set ℝ²) := by
  obtain ⟨p₁, hp₁s, p₂, hp₂s, p₃, hp₃s, h12, h13, h23⟩ :=
    exists_three_directions hcol hno2 hw
  have hmemV : ∀ {a b : ℝ²}, a ∈ s → b ∈ s → det2 (a - w) (b - w) ≠ 0 →
      dualInter w a b ∈ dualVerts s w := fun {a b} ha hb hd =>
    Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hd⟩, rfl⟩
  let X12 := dualInter w p₁ p₂
  let X13 := dualInter w p₁ p₃
  let X23 := dualInter w p₂ p₃
  have hX12 : X12 ∈ dualVerts s w := hmemV hp₁s hp₂s h12
  have hX13 : X13 ∈ dualVerts s w := hmemV hp₁s hp₃s h13
  have hX23 : X23 ∈ dualVerts s w := hmemV hp₂s hp₃s h23
  intro hVcol
  -- Case 1: all points of dualVerts equal X12
  by_cases hall_eq : ∀ X ∈ dualVerts s w, X = X12
  · -- Then every z ∈ s \ {w} lies on line[p₁, p₂]
    have hp₁p₂ : p₁ ≠ p₂ := fun h => h12 (h ▸ det2_self _)
    have hp₁w : p₁ ≠ w := fun h => h12 (by rw [h, sub_self]; simp [det2])
    have hL12 : Module.finrank ℝ (line[ℝ, p₁, p₂]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hp₁p₂)]
    have hLw1 : Module.finrank ℝ (line[ℝ, w, p₁]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hp₁w.symm)]
    apply hno2
    refine ⟨line[ℝ, p₁, p₂], line[ℝ, w, p₁], hL12, hLw1, fun z hz => ?_⟩
    by_cases hzw : z = w
    · exact Or.inr (hzw ▸ left_mem_affineSpan_pair ℝ w p₁)
    · by_cases hdz1 : det2 (p₁ - w) (z - w) = 0
      · exact Or.inr ((mem_line_iff_det2 hp₁w.symm).mpr hdz1)
      · left
        rw [mem_line_iff_evalDual_zero h12]
        have hXz : dualInter w p₁ z = dualInter w p₁ p₂ := hall_eq _ (hmemV hp₁s hz hdz1)
        rw [← hXz]
        exact evalDual_dualInter_right hdz1
  · -- There exists X' ∈ dualVerts with X' ≠ X12
    push Not at hall_eq
    obtain ⟨X', hX'V, hX'ne⟩ := hall_eq
    -- Every X ∈ dualVerts lies on line[X12, X']
    have honM : ∀ X ∈ dualVerts s w, X ∈ line[ℝ, X12, X'] := fun X hXV =>
      hVcol.mem_affineSpan_of_mem_of_ne hX12 hX'V hXV hX'ne.symm
    -- Show X12 = X13 = X23
    have hX13_eq : X13 = X12 := by
      by_contra hne
      -- Both X12, X13 lie on line[X12, X'] and satisfy evalDual w p₁ _ = 0
      -- Hence every point of line[X12, X'] satisfies evalDual w p₁ _ = 0
      have hp1_on_M : ∀ Y ∈ line[ℝ, X12, X'], evalDual w p₁ Y = 0 := by
        intro Y hY
        have hM_eq : line[ℝ, X12, X'] = line[ℝ, X12, X13] :=
          (affineSpan_pair_eq_of_mem_of_mem_of_ne
            (left_mem_affineSpan_pair ℝ X12 X') (honM X13 hX13) (Ne.symm hne)).symm
        rw [hM_eq, mem_affineSpan_pair_iff_exists_lineMap_eq] at hY
        obtain ⟨t, rfl⟩ := hY
        have hsub : AffineMap.lineMap X12 X13 t = (1 - t) • X12 + t • X13 := by
          rw [AffineMap.lineMap_apply_module']; module
        dsimp [evalDual]
        rw [hsub, dot2_add_right, dot2_smul_right, dot2_smul_right]
        have e1 : dot2 (p₁ - w) X12 + 1 = 0 := evalDual_dualInter_left h12
        have e2 : dot2 (p₁ - w) X13 + 1 = 0 := evalDual_dualInter_left h13
        linear_combination (1 - t) * e1 + t * e2
      -- Since X23 ∈ line[X12, X'], evalDual w p₁ X23 = 0, so X23 = X12 = X13!
      have he1 : evalDual w p₁ X23 = 0 := hp1_on_M X23 (honM X23 hX23)
      have h23_12 : X23 = X12 := dualInter_unique h12 he1 (evalDual_dualInter_left h23)
      have h23_13 : X23 = X13 := dualInter_unique h13 he1 (evalDual_dualInter_right h23)
      exact hne (h23_13.symm.trans h23_12)
    have hX23_eq : X23 = X12 := by
      have hp2 : evalDual w p₂ X12 = 0 := evalDual_dualInter_right h12
      have hp3 : evalDual w p₃ X12 = 0 := by rw [← hX13_eq]; exact evalDual_dualInter_right h13
      exact (dualInter_unique h23 hp2 hp3).symm
    -- Now X12 lies on ℓ_{p₁}, ℓ_{p₂}, ℓ_{p₃} and X' ≠ X12 lies on M = line[X12, X'].
    -- At most one of ℓ_{p₁}, ℓ_{p₂}, ℓ_{p₃} contains X'!
    have hnot_two : ∀ {a b : ℝ²}, det2 (a - w) (b - w) ≠ 0 →
        evalDual w a X12 = 0 → evalDual w b X12 = 0 →
        ¬ (evalDual w a X' = 0 ∧ evalDual w b X' = 0) := by
      rintro a b hab ha12 hb12 ⟨ha', hb'⟩
      have h1 : X12 = dualInter w a b := dualInter_unique hab ha12 hb12
      have h2 : X' = dualInter w a b := dualInter_unique hab ha' hb'
      exact hX'ne (h2.trans h1.symm)
    -- Therefore we can pick two of {p₁, p₂, p₃}, say q₁, q₂, with evalDual w q₁ X' ≠ 0 and evalDual w q₂ X' ≠ 0
    have hex_pair : ∃ q₁ ∈ s, ∃ q₂ ∈ s, det2 (q₁ - w) (q₂ - w) ≠ 0 ∧
        evalDual w q₁ X12 = 0 ∧ evalDual w q₂ X12 = 0 ∧
        evalDual w q₁ X' ≠ 0 ∧ evalDual w q₂ X' ≠ 0 := by
      have e1 : evalDual w p₁ X12 = 0 := evalDual_dualInter_left h12
      have e2 : evalDual w p₂ X12 = 0 := evalDual_dualInter_right h12
      have e3 : evalDual w p₃ X12 = 0 := hX13_eq ▸ evalDual_dualInter_right h13
      by_cases h1' : evalDual w p₁ X' = 0
      · have h2' : evalDual w p₂ X' ≠ 0 := fun h => hnot_two h12 e1 e2 ⟨h1', h⟩
        have h3' : evalDual w p₃ X' ≠ 0 := fun h => hnot_two h13 e1 e3 ⟨h1', h⟩
        exact ⟨p₂, hp₂s, p₃, hp₃s, h23, e2, e3, h2', h3'⟩
      · by_cases h2' : evalDual w p₂ X' = 0
        · have h3' : evalDual w p₃ X' ≠ 0 := fun h => hnot_two h23 e2 e3 ⟨h2', h⟩
          exact ⟨p₁, hp₁s, p₃, hp₃s, h13, e1, e3, h1', h3'⟩
        · exact ⟨p₁, hp₁s, p₂, hp₂s, h12, e1, e2, h1', h2'⟩
    obtain ⟨q₁, hq₁s, q₂, hq₂s, hq12, eq1, eq2, hq1', hq2'⟩ := hex_pair
    -- Any Y ∈ line[X12, X'] with evalDual w qᵢ Y = 0 must equal X12!
    have huniq_on_M : ∀ {q Y : ℝ²}, evalDual w q X12 = 0 → evalDual w q X' ≠ 0 →
        Y ∈ line[ℝ, X12, X'] → evalDual w q Y = 0 → Y = X12 := by
      intro q Y hq0 hqne hYM hqY
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hYM
      obtain ⟨t, rfl⟩ := hYM
      have hsub : AffineMap.lineMap X12 X' t = (1 - t) • X12 + t • X' := by
        rw [AffineMap.lineMap_apply_module']; module
      dsimp [evalDual] at hq0 hqne hqY
      rw [hsub, dot2_add_right, dot2_smul_right, dot2_smul_right] at hqY
      have ht0 : t = 0 := by
        have : t * (dot2 (q - w) X' + 1) = 0 := by linear_combination hqY - (1 - t) * hq0
        exact (mul_eq_zero.mp this).resolve_right hqne
      simp [ht0]
    -- Hence EVERY z ∈ s \ {w} satisfies evalDual w z X12 = 0!
    have hall_zero : ∀ z ∈ s, z ≠ w → evalDual w z X12 = 0 := by
      intro z hzs hzw
      by_cases hd1 : det2 (q₁ - w) (z - w) = 0
      · have hd2 : det2 (q₂ - w) (z - w) ≠ 0 := by
          have hq1w : q₁ - w ≠ 0 := fun h => hq12 (by rw [h]; simp [det2])
          obtain ⟨t, ht⟩ := eq_of_det2_eq_zero hq1w hd1
          have ht0 : t ≠ 0 := fun h => hzw (sub_eq_zero.mp (by rw [ht, h, zero_smul]))
          rw [ht, det2_smul_right, det2_anticomm]
          exact mul_ne_zero ht0 (neg_ne_zero.mpr hq12)
        have hY : dualInter w q₂ z = X12 :=
          huniq_on_M eq2 hq2' (honM _ (hmemV hq₂s hzs hd2)) (evalDual_dualInter_left hd2)
        rw [← hY]; exact evalDual_dualInter_right hd2
      · have hY : dualInter w q₁ z = X12 :=
          huniq_on_M eq1 hq1' (honM _ (hmemV hq₁s hzs hd1)) (evalDual_dualInter_left hd1)
        rw [← hY]; exact evalDual_dualInter_right hd1
    -- Contradiction: X' ∈ dualVerts must equal X12!
    obtain ⟨⟨a, b⟩, habf, rfl⟩ := Finset.mem_image.mp hX'V
    obtain ⟨habp, hdet_ab⟩ := Finset.mem_filter.mp habf
    obtain ⟨has, hbs⟩ := Finset.mem_product.mp habp
    have haw : a ≠ w := fun h => hdet_ab (by rw [h, sub_self]; simp [det2])
    have hbw : b ≠ w := fun h => hdet_ab (by rw [h, sub_self]; simp [det2])
    exact hX'ne (dualInter_unique hdet_ab (hall_zero a has haw) (hall_zero b hbs hbw)).symm

/-- Given a strictly exposed vertex `X ∈ dualVerts s w` with supporting normal `h`,
the normalized ray direction `r_z` along `ℓ_z` has `dot2 (z - w) r_z = 0` and `dot2 h r_z = 1`. -/
private noncomputable def rayDir (w h z : ℝ²) : ℝ² :=
  (1 / (-det2 h (z - w))) • perp (z - w)

private lemma dot2_rayDir_self {w h z : ℝ²} :
    dot2 (z - w) (rayDir w h z) = 0 := by
  rw [rayDir, dot2_smul_right, dot2_self_perp, mul_zero]

private lemma dot2_h_rayDir {w h z : ℝ²} (hdet : det2 h (z - w) ≠ 0) :
    dot2 h (rayDir w h z) = 1 := by
  rw [rayDir, dot2_smul_right, dot2_perp_right]
  field_simp [hdet]

/-- Slope coordinate of `rayDir w h z` along `perp h`. -/
private noncomputable def raySlope (w h z : ℝ²) : ℝ :=
  dot2 (perp h) (rayDir w h z) / dot2 h h

private lemma rayDir_sub_eq {w h a b : ℝ²} (hh : h ≠ 0)
    (ha : det2 h (a - w) ≠ 0) (hb : det2 h (b - w) ≠ 0) :
    rayDir w h a - rayDir w h b = (raySlope w h a - raySlope w h b) • perp h := by
  have ha' := decomp_orth hh (rayDir w h a) (dot2_h_rayDir ha)
  have hb' := decomp_orth hh (rayDir w h b) (dot2_h_rayDir hb)
  dsimp [raySlope]
  conv_lhs => rw [ha', hb']
  module

private lemma dot2_rayDir_eq {w h a b : ℝ²} (hh : h ≠ 0)
    (ha : det2 h (a - w) ≠ 0) (hb : det2 h (b - w) ≠ 0) :
    dot2 (b - w) (rayDir w h a) = (raySlope w h a - raySlope w h b) * dot2 (b - w) (perp h) := by
  have hsub := rayDir_sub_eq hh ha hb
  have : rayDir w h a = (raySlope w h a - raySlope w h b) • perp h + rayDir w h b :=
    eq_add_of_sub_eq hsub
  rw [this, dot2_add_right, dot2_rayDir_self, add_zero, dot2_smul_right]

private lemma raySlope_ne_of_ne_through_X {w h X a b : ℝ²} (hh : h ≠ 0)
    (ha : det2 h (a - w) ≠ 0) (hb : det2 h (b - w) ≠ 0)
    (haX : evalDual w a X = 0) (hbX : evalDual w b X = 0) (hab : a ≠ b) :
    raySlope w h a ≠ raySlope w h b := by
  intro heq
  have hreq : rayDir w h a = rayDir w h b := by
    have := rayDir_sub_eq hh ha hb
    rw [heq, sub_self, zero_smul] at this
    exact sub_eq_zero.mp this
  have hdot : dot2 (a - w) (rayDir w h b) = 0 := hreq ▸ dot2_rayDir_self
  rw [rayDir, dot2_smul_right, dot2_perp_right] at hdot
  have hdet0 : det2 (a - w) (b - w) = 0 := by
    have := (mul_eq_zero.mp hdot).resolve_left (by simp [hb])
    linarith
  have haw : a - w ≠ 0 := fun h0 => ha (by rw [h0]; simp [det2])
  obtain ⟨t, ht⟩ := eq_of_det2_eq_zero haw hdet0
  dsimp [evalDual] at haX hbX
  rw [ht, dot2_smul_left] at hbX
  have haX' : dot2 (a - w) X = -1 := by linarith
  rw [haX'] at hbX
  have ht1 : t = 1 := by linarith
  rw [ht1, one_smul] at ht
  exact hab (sub_left_inj.mp ht.symm)

/-- Claim A: At a strictly exposed vertex `X` with supporting normal `h`, if three distinct points
`p₁, p₂, p₃ ∈ s \ {w}` pass through `X` with `raySlope p₁ < raySlope p₂ < raySlope p₃`, then
`p₂` has NO parallel partner in `s \ {w}` (i.e., `line[w, p₂]` is an ordinary line of `s`). -/
private lemma no_parallel_of_middle_at_exposed {s : Finset ℝ²} {w X h p₁ p₂ p₃ : ℝ²}
    (hh : h ≠ 0)
    (hmax : ∀ Y ∈ dualVerts s w, Y ≠ X → dot2 h Y < dot2 h X)
    (hdet : ∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0)
    (hp₁ : p₁ ∈ s) (hp₁w : p₁ ≠ w) (hp₂ : p₂ ∈ s) (hp₂w : p₂ ≠ w) (hp₃ : p₃ ∈ s) (hp₃w : p₃ ≠ w)
    (hX₁ : evalDual w p₁ X = 0) (hX₂ : evalDual w p₂ X = 0) (hX₃ : evalDual w p₃ X = 0)
    (hs12 : raySlope w h p₁ < raySlope w h p₂) (hs23 : raySlope w h p₂ < raySlope w h p₃) :
    ∀ z ∈ s, z ≠ w → z ≠ p₂ → det2 (p₂ - w) (z - w) ≠ 0 := by
  intro z hzs hzw hzp2 hpar
  obtain ⟨lam, hlam⟩ := eq_of_det2_eq_zero (sub_ne_zero.mpr hp₂w) hpar
  have hlam0 : lam ≠ 0 := fun h0 => hzw (sub_eq_zero.mp (by rw [hlam, h0, zero_smul]))
  have hlam1 : lam ≠ 1 := fun h1 => hzp2 (sub_left_inj.mp (by rw [hlam, h1, one_smul]))
  have hd1 := hdet p₁ hp₁ hp₁w
  have hd2 := hdet p₂ hp₂ hp₂w
  have hd3 := hdet p₃ hp₃ hp₃w
  have hdp2_perp : dot2 (p₂ - w) (perp h) ≠ 0 := by
    rw [dot2_perp_right, det2_anticomm, neg_neg]; exact hd2
  have hg1 : dot2 (p₂ - w) (rayDir w h p₁) = (raySlope w h p₁ - raySlope w h p₂) * dot2 (p₂ - w) (perp h) :=
    dot2_rayDir_eq hh hd1 hd2
  have hg3 : dot2 (p₂ - w) (rayDir w h p₃) = (raySlope w h p₃ - raySlope w h p₂) * dot2 (p₂ - w) (perp h) :=
    dot2_rayDir_eq hh hd3 hd2
  have hprod_neg : dot2 (p₂ - w) (rayDir w h p₁) * dot2 (p₂ - w) (rayDir w h p₃) < 0 := by
    rw [hg1, hg3]
    have hsq : 0 < dot2 (p₂ - w) (perp h) ^ 2 := sq_pos_of_ne_zero hdp2_perp
    have hss : (raySlope w h p₁ - raySlope w h p₂) * (raySlope w h p₃ - raySlope w h p₂) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    have heq : (raySlope w h p₁ - raySlope w h p₂) * dot2 (p₂ - w) (perp h) *
        ((raySlope w h p₃ - raySlope w h p₂) * dot2 (p₂ - w) (perp h)) =
        ((raySlope w h p₁ - raySlope w h p₂) * (raySlope w h p₃ - raySlope w h p₂)) *
        dot2 (p₂ - w) (perp h) ^ 2 := by ring
    rw [heq]
    exact mul_neg_of_neg_of_pos hss hsq
  have h1m : 1 - 1 / lam ≠ 0 := by
    intro h0; apply hlam1; field_simp [hlam0] at h0; linarith
  -- Helper: if t > 0 solves evalDual w z (X + t • rayDir w h p) = 0, contradiction with hmax
  have kill : ∀ p : ℝ², p ∈ s → p ≠ w → evalDual w p X = 0 →
      det2 (p₂ - w) (p - w) ≠ 0 →
      0 < (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p) → False := by
    intro p hps hpw hXp hdet_p2p htpos
    set t := (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p)
    have hdp_ne : dot2 (p₂ - w) (rayDir w h p) ≠ 0 := by
      intro h0; simp [t, h0] at htpos
    have hdet_zp : det2 (z - w) (p - w) ≠ 0 := by
      rw [hlam, det2_smul_left]; exact mul_ne_zero hlam0 hdet_p2p
    let Y := X + t • rayDir w h p
    have hYp : evalDual w p Y = 0 := by
      dsimp [evalDual, Y]; rw [dot2_add_right, dot2_smul_right, dot2_rayDir_self, mul_zero, add_zero]
      exact hXp
    have hYz : evalDual w z Y = 0 := by
      dsimp [evalDual, Y]
      rw [hlam, dot2_smul_left, dot2_add_right, dot2_smul_right]
      have hX2' : dot2 (p₂ - w) X = -1 := by dsimp [evalDual] at hX₂; linarith
      rw [hX2']
      dsimp [t]
      field_simp [hlam0, hdp_ne]; ring
    have hY_eq : Y = dualInter w z p := dualInter_unique hdet_zp hYz hYp
    have hYV : Y ∈ dualVerts s w := by
      rw [hY_eq]
      exact Finset.mem_image.mpr ⟨(z, p), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzs, hps⟩, hdet_zp⟩, rfl⟩
    have hdotY : dot2 h Y = dot2 h X + t := by
      dsimp [Y]; rw [dot2_add_right, dot2_smul_right, dot2_h_rayDir (hdet p hps hpw), mul_one]
    have hYne : Y ≠ X := fun h => by rw [h] at hdotY; linarith
    have hlt := hmax Y hYV hYne
    linarith
  have hdet_p2p1 : det2 (p₂ - w) (p₁ - w) ≠ 0 := by
    intro h0
    have hdot : dot2 (p₂ - w) (rayDir w h p₁) = 0 := by
      rw [rayDir, dot2_smul_right, dot2_perp_right, h0, neg_zero, mul_zero]
    rw [hdot] at hprod_neg; linarith
  have hdet_p2p3 : det2 (p₂ - w) (p₃ - w) ≠ 0 := by
    intro h0
    have hdot : dot2 (p₂ - w) (rayDir w h p₃) = 0 := by
      rw [rayDir, dot2_smul_right, dot2_perp_right, h0, neg_zero, mul_zero]
    rw [hdot] at hprod_neg; linarith
  by_cases ht1 : 0 < (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₁)
  · exact kill p₁ hp₁ hp₁w hX₁ hdet_p2p1 ht1
  · have ht3 : 0 < (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₃) := by
      have h1ne : dot2 (p₂ - w) (rayDir w h p₁) ≠ 0 := by intro h0; rw [h0, zero_mul] at hprod_neg; linarith
      have h3ne : dot2 (p₂ - w) (rayDir w h p₃) ≠ 0 := by intro h0; rw [h0, mul_zero] at hprod_neg; linarith
      have hdiv_prod : ((1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₁)) *
          ((1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₃)) < 0 := by
        rw [div_mul_div_comm]
        exact div_neg_of_pos_of_neg (mul_self_pos.mpr h1m) hprod_neg
      have hne0 : (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₁) ≠ 0 := div_ne_zero h1m h1ne
      have hlt0 : (1 - 1 / lam) / dot2 (p₂ - w) (rayDir w h p₁) < 0 := lt_of_le_of_ne (not_lt.mp ht1) hne0
      nlinarith
    exact kill p₃ hp₃ hp₃w hX₃ hdet_p2p3 ht3

/-- An ordinary strictly exposed vertex `X ∈ dualVerts s w` yields an ordinary line of `s`
attached to `w`. -/
private lemma ordinary_exposed_gives_attached {s : Finset ℝ²} {w X h : ℝ²}
    (hh : h ≠ 0)
    (hXV : X ∈ dualVerts s w)
    (hmax : ∀ Y ∈ dualVerts s w, Y ≠ X → dot2 h Y < dot2 h X)
    (hdet : ∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0)
    (hord : (s.filter (fun z => evalDual w z X = 0)).card ≤ 2) :
    ∃ L ∈ ordinaryLines s,
      (∀ z ∈ s, z ∈ L ↔ evalDual w z X = 0) ∧
      (∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
        ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
          ∀ z ∈ s, ∃ a b c : ℝ,
            (![z 0, z 1, 1] : Fin 3 → ℝ) =
              a • (![p 0, p 1, 1] : Fin 3 → ℝ) +
              b • (ε • (![q 0, q 1, 1] : Fin 3 → ℝ)) +
              c • (δ • (![w 0, w 1, 1] : Fin 3 → ℝ)) ∧
            ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))) := by
  obtain ⟨⟨p, q⟩, hpqf, rfl⟩ := Finset.mem_image.mp hXV
  obtain ⟨hpqp, hdet_pq⟩ := Finset.mem_filter.mp hpqf
  obtain ⟨hps, hqs⟩ := Finset.mem_product.mp hpqp
  have hpw : p ≠ w := fun h0 => hdet_pq (by rw [h0, sub_self]; simp [det2])
  have hqw : q ≠ w := fun h0 => hdet_pq (by rw [h0, sub_self]; simp [det2])
  have hpq : p ≠ q := fun h0 => hdet_pq (h0 ▸ det2_self _)
  set X := dualInter w p q
  let L := line[ℝ, p, q]
  have hmemL : ∀ z ∈ s, z ∈ L ↔ evalDual w z X = 0 := fun z _ => mem_line_iff_evalDual_zero hdet_pq
  have hL_ord : L ∈ ordinaryLines s := by
    rw [mem_ordinaryLines]
    refine ⟨⟨p, hps, q, hqs, hpq, rfl⟩, ?_⟩
    have hfilt : s.filter (fun z => z ∈ L) = s.filter (fun z => evalDual w z X = 0) :=
      Finset.filter_congr fun z hz => hmemL z hz
    rw [hfilt]
    have hsub : ({p, q} : Finset ℝ²) ⊆ s.filter (fun z => evalDual w z X = 0) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hps, evalDual_dualInter_left hdet_pq⟩
      · exact Finset.mem_filter.mpr ⟨hqs, evalDual_dualInter_right hdet_pq⟩
    have hge : 2 ≤ (s.filter (fun z => evalDual w z X = 0)).card := by
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hpq] at hle
      exact hle
    omega
  -- Now construct ε, δ ∈ {±1} for the attachment certificate!
  have hdp := hdet p hps hpw
  have hdq := hdet q hqs hqw
  have hα_ne : dot2 (p - w) (rayDir w h q) ≠ 0 := by
    rw [rayDir, dot2_smul_right, dot2_perp_right]
    exact mul_ne_zero (by simp [hdq]) (neg_ne_zero.mpr hdet_pq)
  have hβ_ne : dot2 (q - w) (rayDir w h p) ≠ 0 := by
    rw [rayDir, dot2_smul_right, dot2_perp_right]
    refine mul_ne_zero (by simp [hdp]) (neg_ne_zero.mpr ?_)
    rw [det2_anticomm]; exact neg_ne_zero.mpr hdet_pq
  let εp : ℝ := if 0 < dot2 (p - w) (rayDir w h q) then 1 else -1
  let εq : ℝ := if 0 < dot2 (q - w) (rayDir w h p) then 1 else -1
  have hεp_sq : εp ^ 2 = 1 := by dsimp [εp]; split_ifs <;> norm_num
  have hεq_sq : εq ^ 2 = 1 := by dsimp [εq]; split_ifs <;> norm_num
  have hα_pos : 0 < εp * dot2 (p - w) (rayDir w h q) := by
    dsimp [εp]; split_ifs with h1
    · linarith
    · have := lt_of_le_of_ne (not_lt.mp h1) hα_ne; linarith
  have hβ_pos : 0 < εq * dot2 (q - w) (rayDir w h p) := by
    dsimp [εq]; split_ifs with h1
    · linarith
    · have := lt_of_le_of_ne (not_lt.mp h1) hβ_ne; linarith
  refine ⟨L, hL_ord, hmemL, p, hps, q, hqs, hpq, left_mem_affineSpan_pair ℝ p q,
    right_mem_affineSpan_pair ℝ p q, not_mem_line_of_det2_ne_zero hdet_pq,
    εp * εq, εp, by rw [mul_pow, hεp_sq, hεq_sq, one_mul], hεp_sq, fun z hzs => ?_⟩
  by_cases hzw : z = w
  · subst hzw
    refine ⟨0, 0, εp, ?_, ?_⟩
    · have hsq : εp * εp = 1 := by nlinarith [hεp_sq]
      ext i; fin_cases i <;> simp [← mul_assoc, hsq]
    · dsimp [εp]; split_ifs <;> [exact Or.inl (by norm_num); exact Or.inr (by norm_num)]
  by_cases hzp : z = p
  · subst hzp
    exact ⟨1, 0, 0, by ext i; fin_cases i <;> simp, Or.inl (by norm_num)⟩
  by_cases hzq : z = q
  · subst hzq
    refine ⟨0, εp * εq, 0, ?_, ?_⟩
    · ext i
      have hsq : (εp * εq) * (εp * εq) = 1 := by nlinarith [hεp_sq, hεq_sq]
      fin_cases i <;> simp [← mul_assoc, hsq]
    · dsimp [εp, εq]; split_ifs <;> [exact Or.inl (by norm_num); exact Or.inr (by norm_num);
        exact Or.inr (by norm_num); exact Or.inl (by norm_num)]
  -- General z ∉ {w, p, q}: evalDual w z X ≠ 0!
  have hzX_ne : evalDual w z X ≠ 0 := by
    intro h0
    have hsub : ({p, q, z} : Finset ℝ²) ⊆ s.filter (fun u => evalDual w u X = 0) := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hps, evalDual_dualInter_left hdet_pq⟩
      · exact Finset.mem_filter.mpr ⟨hqs, evalDual_dualInter_right hdet_pq⟩
      · exact Finset.mem_filter.mpr ⟨hzs, h0⟩
    have h3 : ({p, q, z} : Finset ℝ²).card = 3 :=
      Finset.card_eq_three.mpr ⟨p, q, z, hpq, Ne.symm hzp, Ne.symm hzq, rfl⟩
    have := Finset.card_le_card hsub
    omega
  -- Key sign lemma: evalDual w z X and dot2 (z - w) (rayDir w h r) cannot have opposite strict signs!
  have same_sign_ray : ∀ r : ℝ², r ∈ s → r ≠ w → evalDual w r X = 0 →
      0 ≤ evalDual w z X * dot2 (z - w) (rayDir w h r) := by
    intro r hrs hrw hXr
    by_contra hneg
    push Not at hneg
    have hg_ne : dot2 (z - w) (rayDir w h r) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hneg; linarith
    have hdet_zr : det2 (z - w) (r - w) ≠ 0 := by
      intro h0
      rw [rayDir, dot2_smul_right, dot2_perp_right, h0, neg_zero, mul_zero] at hg_ne
      exact hg_ne rfl
    set t := -evalDual w z X / dot2 (z - w) (rayDir w h r)
    have ht_pos : 0 < t := by
      dsimp [t]
      rw [div_pos_iff]
      rcases lt_or_gt_of_ne hzX_ne with h1 | h1
      · left; exact ⟨by linarith, by nlinarith⟩
      · right; exact ⟨by linarith, by nlinarith⟩
    let Y := X + t • rayDir w h r
    have hYr : evalDual w r Y = 0 := by
      dsimp [evalDual, Y]; rw [dot2_add_right, dot2_smul_right, dot2_rayDir_self, mul_zero, add_zero]
      exact hXr
    have hYz : evalDual w z Y = 0 := by
      dsimp [evalDual, Y]; rw [dot2_add_right, dot2_smul_right]
      dsimp [t, evalDual]; field_simp [hg_ne]; ring
    have hY_eq : Y = dualInter w z r := dualInter_unique hdet_zr hYz hYr
    have hYV : Y ∈ dualVerts s w := by
      rw [hY_eq]
      exact Finset.mem_image.mpr ⟨(z, r), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hzs, hrs⟩, hdet_zr⟩, rfl⟩
    have hdotY : dot2 h Y = dot2 h X + t := by
      dsimp [Y]; rw [dot2_add_right, dot2_smul_right, dot2_h_rayDir (hdet r hrs hrw), mul_one]
    have hYne : Y ≠ X := fun h => by rw [h] at hdotY; linarith
    linarith [hmax Y hYV hYne]
  have hsp : 0 ≤ evalDual w z X * dot2 (z - w) (rayDir w h p) :=
    same_sign_ray p hps hpw (evalDual_dualInter_left hdet_pq)
  have hsq : 0 ≤ evalDual w z X * dot2 (z - w) (rayDir w h q) :=
    same_sign_ray q hqs hqw (evalDual_dualInter_right hdet_pq)
  -- Express z - w = a • (p - w) + (b * (εp * εq)) • (q - w)
  obtain ⟨a₀, b₀, hab⟩ := basis_decomp hdet_pq (z - w)
  let a := a₀
  let b := b₀ * (εp * εq)
  let c := εp * evalDual w z X
  have hb_eq : b * (εp * εq) = b₀ := by
    dsimp [b]
    calc b₀ * (εp * εq) * (εp * εq) = b₀ * (εp ^ 2 * εq ^ 2) := by ring
      _ = b₀ := by rw [hεp_sq, hεq_sq]; ring
  have hce : c * εp = evalDual w z X := by
    dsimp [c]
    calc εp * evalDual w z X * εp = εp ^ 2 * evalDual w z X := by ring
      _ = evalDual w z X := by rw [hεp_sq, one_mul]
  have ha_dot : dot2 (z - w) (rayDir w h q) = a * dot2 (p - w) (rayDir w h q) := by
    rw [hab, dot2_add_left, dot2_smul_left, dot2_smul_left, dot2_rayDir_self, mul_zero, add_zero]
  have hb_dot : dot2 (z - w) (rayDir w h p) = b₀ * dot2 (q - w) (rayDir w h p) := by
    rw [hab, dot2_add_left, dot2_smul_left, dot2_smul_left, dot2_rayDir_self, mul_zero, zero_add]
  have hsum1 : a + b * (εp * εq) + c * εp = 1 := by
    rw [hb_eq, hce]
    dsimp [evalDual]
    rw [hab, dot2_add_left, dot2_smul_left, dot2_smul_left]
    have ep : dot2 (p - w) X = -1 := by
      have h := evalDual_dualInter_left hdet_pq; dsimp [evalDual] at h; linarith
    have eq : dot2 (q - w) X = -1 := by
      have h := evalDual_dualInter_right hdet_pq; dsimp [evalDual] at h; linarith
    change a₀ + b₀ + (a₀ * dot2 (p - w) X + b₀ * dot2 (q - w) X + 1) = 1
    rw [ep, eq]; ring
  have hs0 : a₀ + b₀ + c * εp = 1 := by rw [← hb_eq]; exact hsum1
  refine ⟨a, b, c, ?_, ?_⟩
  · ext i
    have h0 := congrArg (fun v : ℝ² => v.ofLp 0) hab
    have h1 := congrArg (fun v : ℝ² => v.ofLp 1) hab
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h0 h1
    fin_cases i
    · change z.ofLp 0 = a₀ * p.ofLp 0 + b * (εp * εq * q.ofLp 0) + c * (εp * w.ofLp 0)
      have hb0 : b * (εp * εq * q.ofLp 0) = b₀ * q.ofLp 0 := by rw [← mul_assoc, hb_eq]
      rw [hb0]
      linear_combination h0 - w.ofLp 0 * hs0
    · change z.ofLp 1 = a₀ * p.ofLp 1 + b * (εp * εq * q.ofLp 1) + c * (εp * w.ofLp 1)
      have hb1 : b * (εp * εq * q.ofLp 1) = b₀ * q.ofLp 1 := by rw [← mul_assoc, hb_eq]
      rw [hb1]
      linear_combination h1 - w.ofLp 1 * hs0
    · change (1 : ℝ) = a * 1 + b * (εp * εq * 1) + c * (εp * 1)
      linarith [hsum1]
  · -- Check all three of a, b, c have the same sign as c = εp * evalDual w z X!
    have hca : 0 ≤ c * a := by
      have h1 : (c * a) * (εp * dot2 (p - w) (rayDir w h q)) =
          evalDual w z X * dot2 (z - w) (rayDir w h q) := by
        rw [ha_dot]; dsimp [c]
        calc εp * evalDual w z X * a * (εp * dot2 (p - w) (rayDir w h q))
            = εp ^ 2 * (evalDual w z X * (a * dot2 (p - w) (rayDir w h q))) := by ring
          _ = evalDual w z X * (a * dot2 (p - w) (rayDir w h q)) := by rw [hεp_sq, one_mul]
      nlinarith
    have hcb : 0 ≤ c * b := by
      have h1 : (c * b) * (εq * dot2 (q - w) (rayDir w h p)) =
          evalDual w z X * dot2 (z - w) (rayDir w h p) := by
        rw [hb_dot]; dsimp [c, b]
        calc εp * evalDual w z X * (b₀ * (εp * εq)) * (εq * dot2 (q - w) (rayDir w h p))
            = (εp ^ 2) * (εq ^ 2) * (evalDual w z X * (b₀ * dot2 (q - w) (rayDir w h p))) := by ring
          _ = evalDual w z X * (b₀ * dot2 (q - w) (rayDir w h p)) := by rw [hεp_sq, hεq_sq]; ring
      nlinarith
    have hc_ne : c ≠ 0 := by
      dsimp [c]; exact mul_ne_zero (by dsimp [εp]; split_ifs <;> norm_num) hzX_ne
    rcases lt_or_gt_of_ne hc_ne with hcneg | hcpos
    · right; exact ⟨by nlinarith, by nlinarith, hcneg.le⟩
    · left; exact ⟨by nlinarith, by nlinarith, hcpos.le⟩

/-- Distinct dual vertices give distinct ordinary lines (when each characterizes its line). -/
private lemma line_ne_of_vert_ne {s : Finset ℝ²} {w X₁ X₂ : ℝ²}
    {L₁ L₂ : AffineSubspace ℝ ℝ²}
    (hX₁ : X₁ ∈ dualVerts s w) (hX₂ : X₂ ∈ dualVerts s w) (hne : X₁ ≠ X₂)
    (h1 : ∀ z ∈ s, z ∈ L₁ ↔ evalDual w z X₁ = 0)
    (h2 : ∀ z ∈ s, z ∈ L₂ ↔ evalDual w z X₂ = 0) : L₁ ≠ L₂ := by
  intro heq
  obtain ⟨⟨p, q⟩, hpqf, rfl⟩ := Finset.mem_image.mp hX₁
  obtain ⟨hpqp, hdet⟩ := Finset.mem_filter.mp hpqf
  obtain ⟨hps, hqs⟩ := Finset.mem_product.mp hpqp
  have hp2 : evalDual w p X₂ = 0 := (h2 p hps).mp (heq ▸ (h1 p hps).mpr (evalDual_dualInter_left hdet))
  have hq2 : evalDual w q X₂ = 0 := (h2 q hqs).mp (heq ▸ (h1 q hqs).mpr (evalDual_dualInter_right hdet))
  exact hne (dualInter_unique hdet hp2 hq2).symm

/-- If a strictly exposed vertex `X` has ≥ 3 incident dual lines, there are 3 with strictly ordered slopes. -/
private lemma three_sorted_of_card_gt_two {s : Finset ℝ²} {w X h : ℝ²}
    (hh : h ≠ 0)
    (hdet : ∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0)
    (hgt : 2 < (s.filter (fun z => evalDual w z X = 0)).card) :
    ∃ p₁ ∈ s, ∃ p₂ ∈ s, ∃ p₃ ∈ s,
      p₁ ≠ w ∧ p₂ ≠ w ∧ p₃ ≠ w ∧
      evalDual w p₁ X = 0 ∧ evalDual w p₂ X = 0 ∧ evalDual w p₃ X = 0 ∧
      raySlope w h p₁ < raySlope w h p₂ ∧ raySlope w h p₂ < raySlope w h p₃ := by
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hgt
  obtain ⟨has, haX⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbs, hbX⟩ := Finset.mem_filter.mp hb
  obtain ⟨hcs, hcX⟩ := Finset.mem_filter.mp hc
  have haw : a ≠ w := fun h0 => by rw [h0] at haX; simp [evalDual, dot2] at haX
  have hbw : b ≠ w := fun h0 => by rw [h0] at hbX; simp [evalDual, dot2] at hbX
  have hcw : c ≠ w := fun h0 => by rw [h0] at hcX; simp [evalDual, dot2] at hcX
  have sab : raySlope w h a ≠ raySlope w h b :=
    raySlope_ne_of_ne_through_X hh (hdet a has haw) (hdet b hbs hbw) haX hbX hab
  have sac : raySlope w h a ≠ raySlope w h c :=
    raySlope_ne_of_ne_through_X hh (hdet a has haw) (hdet c hcs hcw) haX hcX hac
  have sbc : raySlope w h b ≠ raySlope w h c :=
    raySlope_ne_of_ne_through_X hh (hdet b hbs hbw) (hdet c hcs hcw) hbX hcX hbc
  rcases lt_or_gt_of_ne sab with h1 | h1 <;>
  rcases lt_or_gt_of_ne sac with h2 | h2 <;>
  rcases lt_or_gt_of_ne sbc with h3 | h3
  · exact ⟨a, has, b, hbs, c, hcs, haw, hbw, hcw, haX, hbX, hcX, h1, h3⟩
  · exact ⟨a, has, c, hcs, b, hbs, haw, hcw, hbw, haX, hcX, hbX, h2, h3⟩
  · linarith
  · exact ⟨c, hcs, a, has, b, hbs, hcw, haw, hbw, hcX, haX, hbX, h2, h1⟩
  · exact ⟨b, hbs, a, has, c, hcs, hbw, haw, hcw, hbX, haX, hcX, h1, h2⟩
  · linarith
  · exact ⟨b, hbs, c, hcs, a, has, hbw, hcw, haw, hbX, hcX, haX, h3, h2⟩
  · exact ⟨c, hcs, b, hbs, a, has, hcw, hbw, haw, hcX, hbX, haX, h3, h1⟩

/-- If `z ∈ s \ {w}` has NO parallel partner in `s \ {w}`, then `line[w, z]` is an ordinary line through `w`. -/
private lemma ordinary_through_w_of_no_parallel {s : Finset ℝ²} {w z : ℝ²}
    (hw : w ∈ s) (hz : z ∈ s) (hzw : z ≠ w)
    (hno : ∀ u ∈ s, u ≠ w → u ≠ z → det2 (z - w) (u - w) ≠ 0) :
    line[ℝ, w, z] ∈ ordinaryLines s ∧ w ∈ line[ℝ, w, z] := by
  refine ⟨?_, left_mem_affineSpan_pair ℝ w z⟩
  rw [mem_ordinaryLines]
  refine ⟨⟨w, hw, z, hz, hzw.symm, rfl⟩, ?_⟩
  have heq : s.filter (fun u => u ∈ line[ℝ, w, z]) = {w, z} := by
    ext u; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hus, huL⟩
      by_cases huw : u = w
      · exact Or.inl huw
      · by_cases huz : u = z
        · exact Or.inr huz
        · exfalso; exact hno u hus huw huz ((mem_line_iff_det2 hzw.symm).mp huL)
    · rintro (hu | hu)
      · rw [hu]; exact ⟨hw, left_mem_affineSpan_pair ℝ w z⟩
      · rw [hu]; exact ⟨hz, right_mem_affineSpan_pair ℝ w z⟩
  rw [heq, Finset.card_pair hzw.symm]

/-- Existence of three distinct strictly exposed vertices of any non-collinear finite set `V`. -/
private lemma exists_three_exposed (s V : Finset ℝ²) (w : ℝ²)
    (hVcol : ¬ Collinear ℝ (V : Set ℝ²)) :
    ∃ (X₁ X₂ X₃ : ℝ²), X₁ ∈ V ∧ X₂ ∈ V ∧ X₃ ∈ V ∧ X₁ ≠ X₂ ∧ X₁ ≠ X₃ ∧ X₂ ≠ X₃ ∧
      (∃ h₁ : ℝ², h₁ ≠ 0 ∧ (∀ Y ∈ V, Y ≠ X₁ → dot2 h₁ Y < dot2 h₁ X₁) ∧
        (∀ z ∈ s, z ≠ w → det2 h₁ (z - w) ≠ 0)) ∧
      (∃ h₂ : ℝ², h₂ ≠ 0 ∧ (∀ Y ∈ V, Y ≠ X₂ → dot2 h₂ Y < dot2 h₂ X₂) ∧
        (∀ z ∈ s, z ≠ w → det2 h₂ (z - w) ≠ 0)) ∧
      (∃ h₃ : ℝ², h₃ ≠ 0 ∧ (∀ Y ∈ V, Y ≠ X₃ → dot2 h₃ Y < dot2 h₃ X₃) ∧
        (∀ z ∈ s, z ≠ w → det2 h₃ (z - w) ≠ 0)) := by
  have hVne : V.Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hVcol (by simp [h, collinear_empty])
  let e₀ : ℝ² := !₂[1, 0]
  have he₀ : e₀ ≠ 0 := by intro h; have := congrArg (fun x : ℝ² => x.ofLp 0) h; norm_num [e₀] at this
  obtain ⟨X₁, hX₁V, h₁, hh₁, hmax₁, hdet₁, hle₁⟩ := exists_strictly_exposed s V w hVne e₀ he₀
  obtain ⟨X₂, hX₂V, h₂, hh₂, hmax₂, hdet₂, hle₂⟩ :=
    exists_strictly_exposed s V w hVne (-e₀) (neg_ne_zero.mpr he₀)
  have hX₁₂ : X₁ ≠ X₂ := by
    intro heq; subst heq
    -- Every Y ∈ V has dot2 e₀ Y = dot2 e₀ X₁, so V lies on a vertical line (collinear!)
    apply hVcol
    have hall : ∀ Y ∈ V, Y.ofLp 0 = X₁.ofLp 0 := fun Y hY => by
      have h1 := hle₁ Y hY
      have h2 := hle₂ Y hY
      simp only [dot2, e₀, PiLp.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
      linarith
    have hsub : (V : Set ℝ²) ⊆ line[ℝ, X₁, X₁ + !₂[0, 1]] := by
      intro Y hY
      change Y ∈ line[ℝ, X₁, X₁ + !₂[0, 1]]
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
      refine ⟨Y.ofLp 1 - X₁.ofLp 1, ?_⟩
      ext i; rw [AffineMap.lineMap_apply_module']
      match i with
      | 0 => simp [hall Y hY]
      | 1 => simp
    rw [collinear_iff_finrank_le_one]
    have hdir : Module.finrank ℝ (line[ℝ, X₁, X₁ + !₂[(0 : ℝ), 1]]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton]
      intro h0
      have := congrArg (fun x : ℝ² => x.ofLp 1) h0
      simp at this
    exact (Submodule.finrank_mono (by rw [← direction_affineSpan]; exact AffineSubspace.direction_le (affineSpan_le.mpr hsub))).trans hdir.le
  let n₁₂ := perp (X₂ - X₁)
  have hn₁₂ : n₁₂ ≠ 0 := perp_ne_zero (sub_ne_zero.mpr hX₁₂.symm)
  have h12_eq : dot2 n₁₂ X₁ = dot2 n₁₂ X₂ := by
    have : dot2 n₁₂ (X₂ - X₁) = 0 := by rw [dot2_comm, dot2_self_perp]
    rw [dot2_sub_right] at this; linarith
  have hex_off : ∃ Y ∈ V, dot2 n₁₂ Y ≠ dot2 n₁₂ X₁ := by
    by_contra! hall
    apply hVcol
    have hsub : (V : Set ℝ²) ⊆ line[ℝ, X₁, X₂] := by
      intro Y hY
      change Y ∈ line[ℝ, X₁, X₂]
      rw [mem_line_iff_det2 hX₁₂]
      have h0 : dot2 n₁₂ (Y - X₁) = 0 := by rw [dot2_sub_right, hall Y hY, sub_self]
      rw [← dot2_perp_left]; exact h0
    rw [collinear_iff_finrank_le_one]
    have hdir : Module.finrank ℝ (line[ℝ, X₁, X₂]).direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hX₁₂)]
    exact (Submodule.finrank_mono (by rw [← direction_affineSpan]; exact AffineSubspace.direction_le (affineSpan_le.mpr hsub))).trans hdir.le
  obtain ⟨Y₀, hY₀V, hY₀ne⟩ := hex_off
  rcases lt_or_gt_of_ne hY₀ne with hlt | hgt
  · obtain ⟨X₃, hX₃V, h₃, hh₃, hmax₃, hdet₃, hle₃⟩ :=
      exists_strictly_exposed s V w hVne (-n₁₂) (neg_ne_zero.mpr hn₁₂)
    have hlt3 : dot2 n₁₂ X₃ < dot2 n₁₂ X₁ := by
      have := hle₃ Y₀ hY₀V
      simp only [dot2, PiLp.neg_apply] at this hlt ⊢; linarith
    exact ⟨X₁, X₂, X₃, hX₁V, hX₂V, hX₃V, hX₁₂,
      fun h => by rw [h] at hlt3; linarith,
      fun h => by rw [← h, ← h12_eq] at hlt3; linarith,
      ⟨h₁, hh₁, hmax₁, hdet₁⟩, ⟨h₂, hh₂, hmax₂, hdet₂⟩, ⟨h₃, hh₃, hmax₃, hdet₃⟩⟩
  · obtain ⟨X₃, hX₃V, h₃, hh₃, hmax₃, hdet₃, hle₃⟩ :=
      exists_strictly_exposed s V w hVne n₁₂ hn₁₂
    have hgt3 : dot2 n₁₂ X₁ < dot2 n₁₂ X₃ := lt_of_lt_of_le hgt (hle₃ Y₀ hY₀V)
    exact ⟨X₁, X₂, X₃, hX₁V, hX₂V, hX₃V, hX₁₂,
      fun h => by rw [h] at hgt3; linarith,
      fun h => by rw [← h, ← h12_eq] at hgt3; linarith,
      ⟨h₁, hh₁, hmax₁, hdet₁⟩, ⟨h₂, hh₂, hmax₂, hdet₂⟩, ⟨h₃, hh₃, hmax₃, hdet₃⟩⟩

theorem kelly_moser_zero :
    ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
    ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M) →
    let O := ordinaryLines s
    let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
    let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
    let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
      ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
        ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
          ∀ z ∈ s, ∃ a b c : ℝ,
            v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
            ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
    let A := fun p => (O.filter (attached p)).card
    ∀ w ∈ s, d w = 0 → 3 ≤ A w := by
  intro s _ hcol hno2 O d v attached A w hw hdw
  have hVcol := dualVerts_not_collinear hcol hno2 hw
  obtain ⟨X₁, X₂, X₃, hX₁, hX₂, hX₃, h12, h13, h23,
    ⟨h₁, hh₁, hmax₁, hdet₁⟩, ⟨h₂, hh₂, hmax₂, hdet₂⟩, ⟨h₃, hh₃, hmax₃, hdet₃⟩⟩ :=
    exists_three_exposed s (dualVerts s w) w hVcol
  have ord_of_exposed : ∀ {X h : ℝ²}, h ≠ 0 →
      (∀ Y ∈ dualVerts s w, Y ≠ X → dot2 h Y < dot2 h X) →
      (∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0) →
      (s.filter (fun z => evalDual w z X = 0)).card ≤ 2 := by
    intro X h hh hmax hdet
    by_contra! hgt
    obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, hp₁w, hp₂w, hp₃w, hX₁', hX₂', hX₃', hs12, hs23⟩ :=
      three_sorted_of_card_gt_two hh hdet hgt
    have hno_par := no_parallel_of_middle_at_exposed hh hmax hdet hp₁ hp₁w hp₂ hp₂w hp₃ hp₃w hX₁' hX₂' hX₃' hs12 hs23
    obtain ⟨hord, hmem⟩ := ordinary_through_w_of_no_parallel hw hp₂ hp₂w hno_par
    have hpos : 0 < d w := Finset.card_pos.mpr ⟨line[ℝ, w, p₂], Finset.mem_filter.mpr ⟨hord, hmem⟩⟩
    omega
  obtain ⟨L₁, hL₁O, hL₁m, hL₁a⟩ := ordinary_exposed_gives_attached hh₁ hX₁ hmax₁ hdet₁ (ord_of_exposed hh₁ hmax₁ hdet₁)
  obtain ⟨L₂, hL₂O, hL₂m, hL₂a⟩ := ordinary_exposed_gives_attached hh₂ hX₂ hmax₂ hdet₂ (ord_of_exposed hh₂ hmax₂ hdet₂)
  obtain ⟨L₃, hL₃O, hL₃m, hL₃a⟩ := ordinary_exposed_gives_attached hh₃ hX₃ hmax₃ hdet₃ (ord_of_exposed hh₃ hmax₃ hdet₃)
  have hL12 : L₁ ≠ L₂ := line_ne_of_vert_ne hX₁ hX₂ h12 hL₁m hL₂m
  have hL13 : L₁ ≠ L₃ := line_ne_of_vert_ne hX₁ hX₃ h13 hL₁m hL₃m
  have hL23 : L₂ ≠ L₃ := line_ne_of_vert_ne hX₂ hX₃ h23 hL₂m hL₃m
  have hsub : ({L₁, L₂, L₃} : Finset (AffineSubspace ℝ ℝ²)) ⊆ O.filter (attached w) := by
    intro L hL; simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hL₁O, hL₁a⟩
    · exact Finset.mem_filter.mpr ⟨hL₂O, hL₂a⟩
    · exact Finset.mem_filter.mpr ⟨hL₃O, hL₃a⟩
  have h3 : ({L₁, L₂, L₃} : Finset (AffineSubspace ℝ ℝ²)).card = 3 :=
    Finset.card_eq_three.mpr ⟨L₁, L₂, L₃, hL12, hL13, hL23, rfl⟩
  exact h3 ▸ Finset.card_le_card hsub

theorem kelly_moser_one :
    ∀ (s : Finset ℝ²), 8 ≤ s.card → ¬ Collinear ℝ (s : Set ℝ²) →
    ¬ (∃ L M : AffineSubspace ℝ ℝ², Module.finrank ℝ L.direction = 1 ∧
      Module.finrank ℝ M.direction = 1 ∧ ∀ p ∈ s, p ∈ L ∨ p ∈ M) →
    let O := ordinaryLines s
    let d := fun p : ℝ² => (O.filter (fun L => p ∈ L)).card
    let v := fun p : ℝ² => (![p 0, p 1, 1] : Fin 3 → ℝ)
    let attached := fun (w : ℝ²) (L : AffineSubspace ℝ ℝ²) =>
      ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ p ∈ L ∧ q ∈ L ∧ w ∉ L ∧
        ∃ ε δ : ℝ, ε ^ 2 = 1 ∧ δ ^ 2 = 1 ∧
          ∀ z ∈ s, ∃ a b c : ℝ,
            v z = a • v p + b • (ε • v q) + c • (δ • v w) ∧
            ((0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c) ∨ (a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0))
    let A := fun p => (O.filter (attached p)).card
    ∀ w ∈ s, d w = 1 → 2 ≤ A w := by
  intro s _ hcol hno2 O d v attached A w hw hdw
  have hVcol := dualVerts_not_collinear hcol hno2 hw
  have hVne : (dualVerts s w).Nonempty := by
    by_contra h; rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hVcol (by simp [h, collinear_empty])
  -- Extract the unique ordinary line L* through w, and its other point z* ∈ s \ {w}
  obtain ⟨Lstar, hLstar⟩ := Finset.card_eq_one.mp hdw
  have hLstar_mem : Lstar ∈ O.filter (fun L => w ∈ L) := by
    rw [hLstar]; exact Finset.mem_singleton_self Lstar
  obtain ⟨hLstarO, hwLstar⟩ := Finset.mem_filter.mp hLstar_mem
  obtain ⟨⟨a0, ha0, b0, hb0, hab0, hLstar_eq⟩, hLstar_card⟩ := mem_ordinaryLines.mp hLstarO
  obtain ⟨zstar, hzstar_s, hzstar_w, hLstar_wz⟩ : ∃ z ∈ s, z ≠ w ∧ Lstar = line[ℝ, w, z] := by
    by_cases hwa : w = a0
    · exact ⟨b0, hb0, fun h => hab0 (hwa.symm.trans h.symm), hwa ▸ hLstar_eq.symm⟩
    · refine ⟨a0, ha0, Ne.symm hwa, ?_⟩
      rw [← hLstar_eq] at hwLstar ⊢
      exact (affineSpan_pair_eq_of_mem_of_mem_of_ne hwLstar
        (left_mem_affineSpan_pair ℝ a0 b0) hwa).symm
  -- Every z ∈ s \ {w, zstar} HAS a parallel partner in s \ {w}
  have has_parallel_of_ne : ∀ z ∈ s, z ≠ w → z ≠ zstar →
      ∃ z' ∈ s, z' ≠ w ∧ z' ≠ z ∧ det2 (z - w) (z' - w) = 0 := by
    intro z hzs hzw hzzs
    by_contra! hno
    obtain ⟨hord, hmem⟩ := ordinary_through_w_of_no_parallel hw hzs hzw hno
    have hmem' : line[ℝ, w, z] ∈ O.filter (fun L => w ∈ L) := Finset.mem_filter.mpr ⟨hord, hmem⟩
    rw [hLstar, Finset.mem_singleton] at hmem'
    have hsub : ({w, zstar, z} : Finset ℝ²) ⊆ s.filter (fun u => u ∈ Lstar) := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with hu | hu | hu
      · rw [hu]; exact Finset.mem_filter.mpr ⟨hw, hwLstar⟩
      · rw [hu]; exact Finset.mem_filter.mpr ⟨hzstar_s, hLstar_wz ▸ right_mem_affineSpan_pair ℝ w zstar⟩
      · rw [hu]; exact Finset.mem_filter.mpr ⟨hzs, hmem' ▸ right_mem_affineSpan_pair ℝ w z⟩
    have h3 : ({w, zstar, z} : Finset ℝ²).card = 3 :=
      Finset.card_eq_three.mpr ⟨w, zstar, z, hzstar_w.symm, hzw.symm, Ne.symm hzzs, rfl⟩
    have := Finset.card_le_card hsub
    omega
  -- Helper: any strictly exposed vertex X with evalDual w zstar X ≠ 0 is ordinary!
  have ord_of_not_on_zstar : ∀ {X h : ℝ²}, h ≠ 0 →
      (∀ Y ∈ dualVerts s w, Y ≠ X → dot2 h Y < dot2 h X) →
      (∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0) →
      evalDual w zstar X ≠ 0 →
      (s.filter (fun z => evalDual w z X = 0)).card ≤ 2 := by
    intro X h hh hmax hdet hne_zs
    by_contra! hgt
    obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, hp₁w, hp₂w, hp₃w, hX₁', hX₂', hX₃', hs12, hs23⟩ :=
      three_sorted_of_card_gt_two hh hdet hgt
    have hp₂ne : p₂ ≠ zstar := fun h0 => hne_zs (h0 ▸ hX₂')
    obtain ⟨z', hz's, hz'w, hz'ne, hpar⟩ := has_parallel_of_ne p₂ hp₂ hp₂w hp₂ne
    exact no_parallel_of_middle_at_exposed hh hmax hdet hp₁ hp₁w hp₂ hp₂w hp₃ hp₃w hX₁' hX₂' hX₃' hs12 hs23
      z' hz's hz'w hz'ne hpar
  -- Helper: from two distinct ordinary strictly exposed vertices, get 2 ≤ A w
  have finish_two : ∀ {X₁ X₂ h₁ h₂ : ℝ²}, X₁ ∈ dualVerts s w → X₂ ∈ dualVerts s w → X₁ ≠ X₂ →
      h₁ ≠ 0 → (∀ Y ∈ dualVerts s w, Y ≠ X₁ → dot2 h₁ Y < dot2 h₁ X₁) →
      (∀ z ∈ s, z ≠ w → det2 h₁ (z - w) ≠ 0) → (s.filter (fun z => evalDual w z X₁ = 0)).card ≤ 2 →
      h₂ ≠ 0 → (∀ Y ∈ dualVerts s w, Y ≠ X₂ → dot2 h₂ Y < dot2 h₂ X₂) →
      (∀ z ∈ s, z ≠ w → det2 h₂ (z - w) ≠ 0) → (s.filter (fun z => evalDual w z X₂ = 0)).card ≤ 2 →
      2 ≤ A w := by
    intro X₁ X₂ h₁ h₂ hX₁ hX₂ h12 hh₁ hmax₁ hdet₁ hord₁ hh₂ hmax₂ hdet₂ hord₂
    obtain ⟨L₁, hL₁O, hL₁m, hL₁a⟩ := ordinary_exposed_gives_attached hh₁ hX₁ hmax₁ hdet₁ hord₁
    obtain ⟨L₂, hL₂O, hL₂m, hL₂a⟩ := ordinary_exposed_gives_attached hh₂ hX₂ hmax₂ hdet₂ hord₂
    have hL12 : L₁ ≠ L₂ := line_ne_of_vert_ne hX₁ hX₂ h12 hL₁m hL₂m
    have hsub : ({L₁, L₂} : Finset (AffineSubspace ℝ ℝ²)) ⊆ O.filter (attached w) := by
      intro L hL; simp only [Finset.mem_insert, Finset.mem_singleton] at hL
      rcases hL with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hL₁O, hL₁a⟩
      · exact Finset.mem_filter.mpr ⟨hL₂O, hL₂a⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_pair hL12] at hle
    exact hle
  -- Pick 3 distinct strictly exposed vertices; if at least 2 are ordinary we are done!
  obtain ⟨X₁, X₂, X₃, hX₁, hX₂, hX₃, h12, h13, h23,
    ⟨h₁, hh₁, hmax₁, hdet₁⟩, ⟨h₂, hh₂, hmax₂, hdet₂⟩, ⟨h₃, hh₃, hmax₃, hdet₃⟩⟩ :=
    exists_three_exposed s (dualVerts s w) w hVcol
  -- If any exposed vertex X has card > 2, then zstar is its middle line and V has points on BOTH sides of ℓ_{zstar}!
  have both_sides_of_nonord : ∀ {X h : ℝ²}, h ≠ 0 →
      (∀ Y ∈ dualVerts s w, Y ≠ X → dot2 h Y < dot2 h X) →
      (∀ z ∈ s, z ≠ w → det2 h (z - w) ≠ 0) →
      2 < (s.filter (fun z => evalDual w z X = 0)).card →
      2 ≤ A w := by
    intro X h hh hmax hdet hgt
    obtain ⟨p₁, hp₁, p₂, hp₂, p₃, hp₃, hp₁w, hp₂w, hp₃w, hX₁', hX₂', hX₃', hs12, hs23⟩ :=
      three_sorted_of_card_gt_two hh hdet hgt
    have hp₂_eq : p₂ = zstar := by
      by_contra hne
      obtain ⟨z', hz's, hz'w, hz'ne, hpar⟩ := has_parallel_of_ne p₂ hp₂ hp₂w hne
      exact no_parallel_of_middle_at_exposed hh hmax hdet hp₁ hp₁w hp₂ hp₂w hp₃ hp₃w hX₁' hX₂' hX₃' hs12 hs23
        z' hz's hz'w hz'ne hpar
    rw [hp₂_eq] at hX₂' hs12 hs23
    have hp₁ne : p₁ ≠ zstar := fun h0 => by rw [h0] at hs12; linarith
    have hp₃ne : p₃ ≠ zstar := fun h0 => by rw [h0] at hs23; linarith
    obtain ⟨p₁', hp₁'s, hp₁'w, hp₁'ne, hpar1⟩ := has_parallel_of_ne p₁ hp₁ hp₁w hp₁ne
    obtain ⟨p₃', hp₃'s, hp₃'w, hp₃'ne, hpar3⟩ := has_parallel_of_ne p₃ hp₃ hp₃w hp₃ne
    -- Construct Y₁ = dualInter w p₁' p₃ and Y₃ = dualInter w p₃' p₁!
    have hd1 := hdet p₁ hp₁ hp₁w
    have hd2 := hdet zstar hzstar_s hzstar_w
    have hd3 := hdet p₃ hp₃ hp₃w
    have hdet13 : det2 (p₁ - w) (p₃ - w) ≠ 0 := by
      intro h0
      have hdot : dot2 (p₁ - w) (rayDir w h p₃) = 0 := by
        rw [rayDir, dot2_smul_right, dot2_perp_right, h0, neg_zero, mul_zero]
      rw [dot2_rayDir_eq hh hd3 hd1] at hdot
      have hdp1 : dot2 (p₁ - w) (perp h) ≠ 0 := by
        rw [dot2_perp_right, det2_anticomm, neg_neg]; exact hd1
      rcases mul_eq_zero.mp hdot with hslope | hdp
      · linarith
      · exact hdp1 hdp
    obtain ⟨lam1, hlam1⟩ := eq_of_det2_eq_zero (sub_ne_zero.mpr hp₁w) hpar1
    obtain ⟨lam3, hlam3⟩ := eq_of_det2_eq_zero (sub_ne_zero.mpr hp₃w) hpar3
    have hlam10 : lam1 ≠ 0 := fun h0 => hp₁'w (sub_eq_zero.mp (by rw [hlam1, h0, zero_smul]))
    have hlam11 : lam1 ≠ 1 := fun h1 => hp₁'ne (sub_left_inj.mp (by rw [hlam1, h1, one_smul]))
    have hlam30 : lam3 ≠ 0 := fun h0 => hp₃'w (sub_eq_zero.mp (by rw [hlam3, h0, zero_smul]))
    have hlam31 : lam3 ≠ 1 := fun h1 => hp₃'ne (sub_left_inj.mp (by rw [hlam3, h1, one_smul]))
    have hdet_1'3 : det2 (p₁' - w) (p₃ - w) ≠ 0 := by
      rw [hlam1, det2_smul_left]; exact mul_ne_zero hlam10 hdet13
    have hdet_3'1 : det2 (p₃' - w) (p₁ - w) ≠ 0 := by
      rw [hlam3, det2_smul_left, det2_anticomm]; exact mul_ne_zero hlam30 (neg_ne_zero.mpr hdet13)
    let Y₁ := dualInter w p₁' p₃
    let Y₃ := dualInter w p₃' p₁
    have hY₁V : Y₁ ∈ dualVerts s w :=
      Finset.mem_image.mpr ⟨(p₁', p₃), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp₁'s, hp₃⟩, hdet_1'3⟩, rfl⟩
    have hY₃V : Y₃ ∈ dualVerts s w :=
      Finset.mem_image.mpr ⟨(p₃', p₁), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp₃'s, hp₁⟩, hdet_3'1⟩, rfl⟩
    have hY₁ne : Y₁ ≠ X := fun heq => by
      have h0 := evalDual_dualInter_left hdet_1'3
      rw [show dualInter w p₁' p₃ = X from heq] at h0
      dsimp [evalDual] at h0 hX₁'
      have hx : dot2 (p₁ - w) X = -1 := by linarith
      rw [hlam1, dot2_smul_left, hx] at h0; apply hlam11; linarith
    have hY₃ne : Y₃ ≠ X := fun heq => by
      have h0 := evalDual_dualInter_left hdet_3'1
      rw [show dualInter w p₃' p₁ = X from heq] at h0
      dsimp [evalDual] at h0 hX₃'
      have hx : dot2 (p₃ - w) X = -1 := by linarith
      rw [hlam3, dot2_smul_left, hx] at h0; apply hlam31; linarith
    -- Express Y₁ = X + t₁ • rayDir w h p₃ and Y₃ = X + t₃ • rayDir w h p₁ with t₁ < 0, t₃ < 0!
    have hY₁_ray : ∃ t₁ : ℝ, t₁ < 0 ∧ Y₁ = X + t₁ • rayDir w h p₃ := by
      have hsub : dot2 (p₃ - w) (Y₁ - X) = 0 := by
        rw [dot2_sub_right]
        have e1 := evalDual_dualInter_right hdet_1'3
        dsimp [evalDual] at e1 hX₃'; linarith
      have hdet0 : det2 (rayDir w h p₃) (Y₁ - X) = 0 := by
        have hperp2 : perp (perp (p₃ - w)) = -(p₃ - w) := by
          ext i; match i with | 0 => simp [perp] | 1 => simp [perp]
        have hdp : det2 (perp (p₃ - w)) (Y₁ - X) = 0 := by
          rw [← dot2_perp_left, hperp2,
            show dot2 (-(p₃ - w)) (Y₁ - X) = -dot2 (p₃ - w) (Y₁ - X) by simp [dot2]; ring,
            hsub, neg_zero]
        rw [rayDir, det2_smul_left, hdp, mul_zero]
      have hr_ne : rayDir w h p₃ ≠ 0 := by
        intro h0; have := dot2_h_rayDir hd3; rw [h0] at this; simp [dot2] at this
      obtain ⟨t₁, ht₁⟩ := eq_of_det2_eq_zero hr_ne hdet0
      have hYeq : Y₁ = X + t₁ • rayDir w h p₃ := by
        have := eq_add_of_sub_eq ht₁; rw [add_comm] at this; exact this
      have hdot := hmax Y₁ hY₁V hY₁ne
      rw [hYeq, dot2_add_right, dot2_smul_right, dot2_h_rayDir hd3, mul_one] at hdot
      exact ⟨t₁, by linarith, hYeq⟩
    have hY₃_ray : ∃ t₃ : ℝ, t₃ < 0 ∧ Y₃ = X + t₃ • rayDir w h p₁ := by
      have hsub : dot2 (p₁ - w) (Y₃ - X) = 0 := by
        rw [dot2_sub_right]
        have e1 := evalDual_dualInter_right hdet_3'1
        dsimp [evalDual] at e1 hX₁'; linarith
      have hdet0 : det2 (rayDir w h p₁) (Y₃ - X) = 0 := by
        have hperp2 : perp (perp (p₁ - w)) = -(p₁ - w) := by
          ext i; match i with | 0 => simp [perp] | 1 => simp [perp]
        have hdp : det2 (perp (p₁ - w)) (Y₃ - X) = 0 := by
          rw [← dot2_perp_left, hperp2,
            show dot2 (-(p₁ - w)) (Y₃ - X) = -dot2 (p₁ - w) (Y₃ - X) by simp [dot2]; ring,
            hsub, neg_zero]
        rw [rayDir, det2_smul_left, hdp, mul_zero]
      have hr_ne : rayDir w h p₁ ≠ 0 := by
        intro h0; have := dot2_h_rayDir hd1; rw [h0] at this; simp [dot2] at this
      obtain ⟨t₃, ht₃⟩ := eq_of_det2_eq_zero hr_ne hdet0
      have hYeq : Y₃ = X + t₃ • rayDir w h p₁ := by
        have := eq_add_of_sub_eq ht₃; rw [add_comm] at this; exact this
      have hdot := hmax Y₃ hY₃V hY₃ne
      rw [hYeq, dot2_add_right, dot2_smul_right, dot2_h_rayDir hd1, mul_one] at hdot
      exact ⟨t₃, by linarith, hYeq⟩
    obtain ⟨t₁, ht₁, hY₁eq⟩ := hY₁_ray
    obtain ⟨t₃, ht₃, hY₃eq⟩ := hY₃_ray
    -- Evaluate evalDual w zstar at Y₁ and Y₃: opposite signs!
    have hf1 : evalDual w zstar Y₁ = t₁ * ((raySlope w h p₃ - raySlope w h zstar) * dot2 (zstar - w) (perp h)) := by
      dsimp [evalDual]; rw [hY₁eq, dot2_add_right, dot2_smul_right, dot2_rayDir_eq hh hd3 hd2]
      dsimp [evalDual] at hX₂'; linarith
    have hf3 : evalDual w zstar Y₃ = t₃ * ((raySlope w h p₁ - raySlope w h zstar) * dot2 (zstar - w) (perp h)) := by
      dsimp [evalDual]; rw [hY₃eq, dot2_add_right, dot2_smul_right, dot2_rayDir_eq hh hd1 hd2]
      dsimp [evalDual] at hX₂'; linarith
    have hdp2 : dot2 (zstar - w) (perp h) ≠ 0 := by
      rw [dot2_perp_right, det2_anticomm, neg_neg]; exact hd2
    have hprod_neg : evalDual w zstar Y₁ * evalDual w zstar Y₃ < 0 := by
      rw [hf1, hf3]
      have hsq : 0 < dot2 (zstar - w) (perp h) ^ 2 := sq_pos_of_ne_zero hdp2
      have htt : 0 < t₁ * t₃ := mul_pos_of_neg_of_neg ht₁ ht₃
      have hss : (raySlope w h p₃ - raySlope w h zstar) * (raySlope w h p₁ - raySlope w h zstar) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (by linarith)
      nlinarith [mul_pos htt hsq]
    -- Maximize and minimize dot2 (zstar - w) over V!
    have hzs_ne : zstar - w ≠ 0 := sub_ne_zero.mpr hzstar_w
    obtain ⟨XL, hXLV, hL, hhL, hmaxL, hdetL, hleL⟩ :=
      exists_strictly_exposed s (dualVerts s w) w hVne (zstar - w) hzs_ne
    obtain ⟨XR, hXRV, hR, hhR, hmaxR, hdetR, hleR⟩ :=
      exists_strictly_exposed s (dualVerts s w) w hVne (-(zstar - w)) (neg_ne_zero.mpr hzs_ne)
    have hpos_exists : ∃ Y ∈ dualVerts s w, 0 < evalDual w zstar Y := by
      by_cases h1 : 0 < evalDual w zstar Y₁
      · exact ⟨Y₁, hY₁V, h1⟩
      · exact ⟨Y₃, hY₃V, by nlinarith⟩
    have hneg_exists : ∃ Y ∈ dualVerts s w, evalDual w zstar Y < 0 := by
      by_cases h1 : evalDual w zstar Y₁ < 0
      · exact ⟨Y₁, hY₁V, h1⟩
      · exact ⟨Y₃, hY₃V, by nlinarith⟩
    obtain ⟨Yp, hYpV, hYp⟩ := hpos_exists
    obtain ⟨Yn, hYnV, hYn⟩ := hneg_exists
    have hXL_pos : 0 < evalDual w zstar XL := by
      have := hleL Yp hYpV; dsimp [evalDual] at hYp ⊢; linarith
    have hXR_neg : evalDual w zstar XR < 0 := by
      have := hleR Yn hYnV
      simp only [dot2, PiLp.neg_apply, PiLp.sub_apply] at this
      dsimp [evalDual, dot2] at hYn ⊢; linarith
    have hXLR : XL ≠ XR := fun heq => by rw [heq] at hXL_pos; linarith
    exact finish_two hXLV hXRV hXLR hhL hmaxL hdetL
      (ord_of_not_on_zstar hhL hmaxL hdetL hXL_pos.ne')
      hhR hmaxR hdetR (ord_of_not_on_zstar hhR hmaxR hdetR hXR_neg.ne)
  -- Finally dispatch on whether X₁ or X₂ is non-ordinary!
  by_cases h1 : (s.filter (fun z => evalDual w z X₁ = 0)).card ≤ 2
  · by_cases h2 : (s.filter (fun z => evalDual w z X₂ = 0)).card ≤ 2
    · exact finish_two hX₁ hX₂ h12 hh₁ hmax₁ hdet₁ h1 hh₂ hmax₂ hdet₂ h2
    · exact both_sides_of_nonord hh₂ hmax₂ hdet₂ (by omega)
  · exact both_sides_of_nonord hh₁ hmax₁ hdet₁ (by omega)

end Erdos210KM

end

theorem OMA.solution : type_of% @Erdos210.erdos_210.variants.csima_sawyer :=
  OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1.main
    (OMA.R_Erdos210_erdos_210_variants_csima_sawyer_R1_H1_R1.main
      Erdos210KM.kelly_moser_zero
      Erdos210KM.kelly_moser_one)
    OMA.OrdinaryAttachment.h2_proof
    OMA.E210.h3_proof
