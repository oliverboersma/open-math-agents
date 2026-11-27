import OMAReductions.R_Green87_green_87_variants_order_R2
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
Proposition 1.3 of Eberhard, Ford and Green, arXiv:1507.04465.
For the lower bound a single distinguished cycle completes a subset sum from
the upper half of the attainable sums. A separate equal-length tail covers
the endpoint, including the small values of k. For the upper bound we mark a
cycle on each side of an invariant set and sum over both removed lengths.
This avoids both the two-cycle length restriction and conditioning on a maximum.
-/

/- The independent Poisson series in Proposition 1.3 of Eberhard, Ford and Green. -/

namespace Green87Local
open Finset
noncomputable section

def atom (j v : ℕ) : ℝ :=
  Real.exp (-(1 / (j : ℝ))) / ((v.factorial : ℝ) * (j : ℝ) ^ v)

def law {k : ℕ} (a : Fin k → ℕ) : ℝ := ∏ j, atom (j.val + 1) (a j)

def values {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  univ.image (fun b : (j : Fin k) → Fin (a j + 1) ↦ ∑ j, (j.val + 1) * (b j).val)

def expectation (k : ℕ) : ℝ := ∑' a : Fin k → ℕ, ((values a).card : ℝ) * law a

lemma atom_nonneg (j v : ℕ) : 0 ≤ atom j v := by unfold atom; positivity

lemma law_nonneg {k : ℕ} (a : Fin k → ℕ) : 0 ≤ law a :=
  prod_nonneg fun _ _ ↦ atom_nonneg _ _

lemma hasSum_atom (j : ℕ) : HasSum (atom j) 1 := by
  let r : NNReal := ⟨1 / (j : ℝ), by positivity⟩
  apply (ProbabilityTheory.hasSum_one_poissonMeasure r).congr_fun
  intro v
  change Real.exp (-(1 / (j : ℝ))) / _ =
    Real.exp (-(1 / (j : ℝ))) * (1 / (j : ℝ)) ^ v / _
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

lemma atom_shift (j v : ℕ) (hj : 0 < j) :
    (v + 1 : ℕ) * atom j (v + 1) = (1 / (j : ℝ)) * atom j v := by
  unfold atom
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  have hj' : (j : ℝ) ≠ 0 := by positivity
  have hv : (v.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma hasSum_atom_first {j : ℕ} (hj : 0 < j) :
    HasSum (fun v : ℕ ↦ (v : ℝ) * atom j v) (1 / j) := by
  apply (hasSum_nat_add_iff' 1).1
  simpa only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero, mul_one] using
    (((hasSum_atom j).mul_left (1 / (j : ℝ))).congr_fun (fun v ↦ atom_shift j v hj))

lemma hasSum_atom_envelope {j : ℕ} (hj : 0 < j) :
    HasSum (fun v : ℕ ↦ ((v : ℝ) + 1) * atom j v) (1 + 1 / j) := by
  apply ((hasSum_atom j).add (hasSum_atom_first hj)).congr_fun
  intro v
  ring

lemma hasSum_finite_product {k : ℕ} (f : Fin k → ℕ → ℝ) (z : Fin k → ℝ)
    (hp : ∀ j v, 0 ≤ f j v) (hs : ∀ j, HasSum (f j) (z j)) :
    HasSum (fun a : Fin k → ℕ ↦ ∏ j, f j (a j)) (∏ j, z j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let e := Fin.consEquiv (fun _ : Fin (k + 1) ↦ ℕ)
    apply e.hasSum_iff.mp
    have ht := ih (fun j ↦ f j.succ) (fun j ↦ z j.succ) (fun j ↦ hp j.succ) (fun j ↦ hs j.succ)
    have hnn (a : Fin k → ℕ) : 0 ≤ ∏ j, f j.succ (a j) :=
      prod_nonneg fun j _ ↦ hp j.succ (a j)
    let g : (Fin k → ℕ) → ℝ := fun a ↦ ∏ j, f j.succ (a j)
    have hg : HasSum g (∏ j : Fin k, z j.succ) := ht
    have hm : Summable (fun x : ℕ × (Fin k → ℕ) ↦ f 0 x.1 * g x.2) :=
      Summable.mul_of_nonneg (f := f 0) (g := g) (hs 0).summable hg.summable (hp 0) hnn
    have h := HasSum.mul (f := f 0) (g := g) (hs 0) hg hm
    rw [Fin.prod_univ_succ z]
    apply h.congr_fun
    intro x
    change (∏ i : Fin (k+1), f i (Fin.cons (α := fun _ ↦ ℕ) x.1 x.2 i)) = _
    simp [Fin.prod_univ_succ, g]

lemma hasSum_law (k : ℕ) : HasSum (@law k) 1 := by
  unfold law
  simpa using hasSum_finite_product (fun j : Fin k ↦ atom (j.val+1)) (fun _ ↦ 1)
    (fun j v ↦ atom_nonneg _ _) (fun _ ↦ hasSum_atom _)

lemma product_mean (k : ℕ) : (∏ j : Fin k, (1 + 1 / ((j.val + 1 : ℕ) : ℝ))) = k + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    push_cast
    field_simp

lemma hasSum_envelope (k : ℕ) :
    HasSum (fun a : Fin k → ℕ ↦ (∏ j, ((a j : ℝ) + 1)) * law a) (k + 1) := by
  rw [← product_mean]
  simpa only [law, ← prod_mul_distrib] using
    hasSum_finite_product (fun j : Fin k ↦ fun v : ℕ ↦ ((v : ℝ) + 1) * atom (j.val+1) v)
      (fun j ↦ 1 + 1 / ((j.val + 1 : ℕ) : ℝ))
      (fun j v ↦ mul_nonneg (by positivity) (atom_nonneg _ _))
      (fun j ↦ hasSum_atom_envelope (Nat.succ_pos _))

lemma values_card_le {k : ℕ} (a : Fin k → ℕ) : (values a).card ≤ ∏ j, (a j + 1) := by
  unfold values
  simpa only [card_univ, Fintype.card_pi, Fintype.card_fin] using
    (card_image_le (s := univ) (f := fun b : (j : Fin k) → Fin (a j + 1) ↦
      ∑ j, (j.val + 1) * (b j).val))

lemma values_zero {k : ℕ} (a : Fin k → ℕ) : 0 ∈ values a := by
  refine mem_image.mpr ⟨fun _ ↦ 0, mem_univ _, ?_⟩
  simp

lemma envelope_bound {k : ℕ} (a : Fin k → ℕ) :
    (values a).card * law a ≤ (∏ j, ((a j : ℝ) + 1)) * law a :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast values_card_le a) (law_nonneg _)

lemma summable_expectation (k : ℕ) :
    Summable (fun a : Fin k → ℕ ↦ ((values a).card : ℝ) * law a) :=
  (hasSum_envelope k).summable.of_nonneg_of_le (fun a ↦ mul_nonneg (by positivity) (law_nonneg _))
    envelope_bound

lemma expectation_bounds (k : ℕ) : 1 ≤ expectation k ∧ expectation k ≤ k + 1 := by
  constructor
  · rw [← (hasSum_law k).tsum_eq]
    apply (hasSum_law k).summable.tsum_le_tsum _ (summable_expectation k)
    intro a
    have h : 1 ≤ (values a).card := card_pos.mpr ⟨0, values_zero a⟩
    simpa using mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ (values a).card by exact_mod_cast h)
      (law_nonneg a)
  · rw [← (hasSum_envelope k).tsum_eq]
    exact (summable_expectation k).tsum_le_tsum envelope_bound (hasSum_envelope k).summable

end
end Green87Local

/- Finite partitions of a prescribed total and their Cauchy weights. -/

namespace Green87Local
open Finset

noncomputable section

def shapes (n : ℕ) : Finset (Multiset ℕ) :=
  univ.image (Nat.Partition.parts : n.Partition → Multiset ℕ)

lemma mem_shapes {n : ℕ} {b : Multiset ℕ} :
    b ∈ shapes n ↔ b.sum = n ∧ ∀ j ∈ b, 0 < j := by
  constructor
  · rintro h
    obtain ⟨p, _, rfl⟩ := mem_image.mp h
    exact ⟨p.parts_sum, fun _ h ↦ p.parts_pos h⟩
  · rintro ⟨hs, hp⟩
    exact mem_image.mpr ⟨⟨b, fun {j} hj ↦ hp j hj, hs⟩, mem_univ _, rfl⟩

def sums (b : Multiset ℕ) : Finset ℕ := b.powerset.toFinset.image Multiset.sum

lemma mem_sums {b : Multiset ℕ} {v : ℕ} :
    v ∈ sums b ↔ ∃ t ≤ b, t.sum = v := by simp [sums]

lemma mem_sums_le {t : Multiset ℕ} {j : ℕ} (h : j ∈ sums t) : j ≤ t.sum := by
  obtain ⟨b, hb, rfl⟩ := mem_sums.mp h
  obtain ⟨c, rfl⟩ := Multiset.le_iff_exists_add.mp hb
  simp

def multiplicity (b : Multiset ℕ) : ℕ := ∏ j ∈ b.toFinset, (b.count j).factorial

lemma multiplicity_over (s : Finset ℕ) (b : Multiset ℕ) (h : b.toFinset ⊆ s) :
    multiplicity b = ∏ j ∈ s, (b.count j).factorial := by
  apply prod_subset h
  intro i _ hi
  simp only [Multiset.mem_toFinset] at hi
  simp [Multiset.count_eq_zero.mpr hi]

lemma multiplicity_cons (b : Multiset ℕ) (j : ℕ) :
    multiplicity (j ::ₘ b) = (b.count j + 1) * multiplicity b := by
  classical
  let s := insert j b.toFinset
  have hj : j ∈ s := mem_insert_self _ _
  rw [multiplicity_over s _ (by simp [s]), multiplicity_over s _ (subset_insert _ _)]
  rw [← mul_prod_erase s (fun i ↦ ((j ::ₘ b).count i).factorial) hj,
    ← mul_prod_erase s (fun i ↦ (b.count i).factorial) hj]
  rw [Multiset.count_cons_self, Nat.factorial_succ, mul_assoc]
  congr 2
  apply prod_congr rfl
  intro i hi
  rw [Multiset.count_cons_of_ne (ne_of_mem_erase hi)]

def denominator (b : Multiset ℕ) : ℕ := b.prod * multiplicity b

def weight (b : Multiset ℕ) : ℝ := (denominator b : ℝ)⁻¹

lemma multiplicity_pos (b : Multiset ℕ) : 0 < multiplicity b :=
  prod_pos fun _ _ ↦ Nat.factorial_pos _

lemma denominator_pos {b : Multiset ℕ} (h : ∀ j ∈ b, 0 < j) : 0 < denominator b := by
  unfold denominator
  exact Nat.mul_pos (Multiset.prod_pos h) (multiplicity_pos _)

lemma weight_nonneg (b : Multiset ℕ) : 0 ≤ weight b := by unfold weight; positivity

lemma denominator_cons (b : Multiset ℕ) (j : ℕ) :
    denominator (j ::ₘ b) = (j * (b.count j + 1)) * denominator b := by
  simp only [denominator, Multiset.prod_cons, multiplicity_cons]
  ring

lemma weight_cons (b : Multiset ℕ) (j : ℕ) :
    weight (j ::ₘ b) = weight b / ((j : ℝ) * (b.count j + 1)) := by
  simp [weight, denominator_cons, div_eq_mul_inv, mul_comm, mul_left_comm]

lemma weight_mark (b : Multiset ℕ) {j : ℕ} (hj : 0 < j) (hb : j ∈ b) :
    (j : ℝ) * (b.count j) * weight b = weight (b.erase j) := by
  rw [← Multiset.cons_erase hb] at ⊢
  rw [weight_cons, Multiset.count_cons_self, Multiset.erase_cons_head]
  push_cast
  have hj' : (j : ℝ) ≠ 0 := by positivity
  field_simp

lemma weight_disjoint (a b : Multiset ℕ) (hd : ∀ i ∈ a, i ∉ b) :
    weight (a + b) = weight a * weight b := by
  induction a using Multiset.induction_on with
  | empty => simp [weight, denominator, multiplicity]
  | cons j a ih =>
    rw [Multiset.cons_add, weight_cons, weight_cons,
      ih (fun i hi ↦ hd i (Multiset.mem_cons_of_mem hi)), Multiset.count_add,
      Multiset.count_eq_zero.mpr (hd j (Multiset.mem_cons_self _ _)), add_zero]
    ring

@[simp] lemma weight_zero : weight 0 = 1 := by simp [weight, denominator, multiplicity]

def rough (m n : ℕ) : Finset (Multiset ℕ) :=
  (shapes n).filter (fun b ↦ ∀ j ∈ b, m ≤ j)

def sieve (m n : ℕ) : ℝ := ∑ b ∈ rough m n, weight b

lemma mem_rough {m n : ℕ} {b : Multiset ℕ} (hm : 0 < m) :
    b ∈ rough m n ↔ b.sum = n ∧ ∀ j ∈ b, m ≤ j := by
  simp only [rough, mem_filter, mem_shapes]
  grind

lemma sieve_zero (m : ℕ) : sieve m 0 = 1 := by
  have h : rough m 0 = {0} := by
    ext b
    simp only [rough, mem_filter, mem_shapes, mem_singleton]
    constructor
    · rintro ⟨⟨hs, hp⟩, _⟩
      by_contra hn
      obtain ⟨j, hj⟩ := Multiset.exists_mem_of_ne_zero hn
      have := Multiset.le_sum_of_mem hj
      have := hp j hj
      omega
    · rintro rfl
      simp
  simp [sieve, h]

lemma sieve_below {m n : ℕ} (hn : 0 < n) (hnm : n < m) : sieve m n = 0 := by
  have h : rough m n = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨hs, ha⟩ := (mem_rough (by omega)).mp hb
    have hne : b ≠ 0 := by intro he; simp [he] at hs; omega
    obtain ⟨j, hj⟩ := Multiset.exists_mem_of_ne_zero hne
    have := Multiset.le_sum_of_mem hj
    have := ha j hj
    omega
  simp [sieve, h]

end
end Green87Local

/- Invariant sets, full cycle partitions including fixed points, and the finite probability. -/

namespace Green87Local
open Equiv Finset
noncomputable section
open scoped Classical

def nontrivialParts (b : Multiset ℕ) := b.filter (2 ≤ ·)

lemma split_ones {b : Multiset ℕ} (hp : ∀ j ∈ b, 0 < j) :
    b = nontrivialParts b + Multiset.replicate (b.sum - (nontrivialParts b).sum) 1 := by
  let c := b.filter (fun i ↦ ¬ 2 ≤ i)
  have h : nontrivialParts b + c = b := Multiset.filter_add_not _ _
  have hr : c = Multiset.replicate c.card 1 := Multiset.eq_replicate_card.mpr (by
    intro j hj
    obtain ⟨hj, hlt⟩ := Multiset.mem_filter.mp hj
    have := hp j hj
    omega)
  have hn := congrArg Multiset.sum h
  rw [Multiset.sum_add] at hn
  have hsum : c.sum = c.card := by rw [hr]; simp
  rw [← hn, Nat.add_sub_cancel_left, hsum, ← hr, h]

lemma parts_eq_of_core {a b : Multiset ℕ} (ha : ∀ j ∈ a, 0 < j) (hb : ∀ j ∈ b, 0 < j)
    (hs : a.sum = b.sum) (hf : nontrivialParts a = nontrivialParts b) : a = b := by
  calc
    a = _ := split_ones ha
    _ = _ := by rw [hs, hf]
    _ = b := (split_ones hb).symm

lemma full_parts_realized (α : Type*) [Fintype α] [DecidableEq α] {a : Multiset ℕ}
    (hs : a.sum = Fintype.card α) (hp : ∀ j ∈ a, 0 < j) :
    ∃ p : Perm α, p.partition.parts = a := by
  have hle : (nontrivialParts a).sum ≤ a.sum := by
    have h := congrArg Multiset.sum (Multiset.filter_add_not (2 ≤ ·) a)
    change (nontrivialParts a + _).sum = _ at h
    rw [Multiset.sum_add] at h
    omega
  obtain ⟨p, he⟩ := (Perm.exists_with_cycleType_iff α (m := nontrivialParts a)).mpr
    ⟨hle.trans_eq hs, fun j hj ↦ (Multiset.mem_filter.mp hj).2⟩
  exact ⟨p, parts_eq_of_core (fun _ h ↦ p.partition.parts_pos h) hp
    (p.partition.parts_sum.trans hs.symm) (Perm.filter_parts_partition_eq_cycleType.trans he)⟩

-- The stable-set image criterion and transport follow the local reference
-- proofs/Green87.green_87.variants.exists_tendsto.R1.H1.lean, PR 1571.
def stable {α : Type*} (p : Perm α) (s : Finset α) := ∀ x, p x ∈ s ↔ x ∈ s

lemma image_stable {α : Type*} [DecidableEq α] (p : Perm α) (s : Finset α) :
    s.image p = s ↔ stable p s := by
  constructor
  · intro e x
    calc
      p x ∈ s ↔ p x ∈ s.image p := by rw [e]
      _ ↔ _ := p.injective.mem_finset_image
  · intro h
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
      exact (h a).mpr ha
    · intro hx
      exact mem_image.mpr ⟨p.symm x, (h (p.symm x)).mp (by simpa), p.apply_symm_apply x⟩

lemma split_perm {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α)
    (p : Perm {x // x ∈ s}) (q : Perm {x // x ∉ s}) :
    (p.subtypeCongr q).partition.parts = p.partition.parts + q.partition.parts := by
  have hd : p.ofSubtype.Disjoint q.ofSubtype := by
    intro x
    by_cases hx : x ∈ s
    · exact Or.inr (Perm.ofSubtype_apply_of_not_mem q (not_not.mpr hx))
    · exact Or.inl (Perm.ofSubtype_apply_of_not_mem p hx)
  have he : p.subtypeCongr q = p.ofSubtype * q.ofSubtype := by
    ext x
    by_cases hx : x ∈ s
    · rw [Perm.subtypeCongr.left_apply p q hx, Perm.mul_apply,
        Perm.ofSubtype_apply_of_not_mem q (not_not.mpr hx), Perm.ofSubtype_apply_of_mem p hx]
    · rw [Perm.subtypeCongr.right_apply p q hx, Perm.mul_apply,
        Perm.ofSubtype_apply_of_mem q hx, Perm.ofSubtype_apply_of_not_mem p (q ⟨x,hx⟩).property]
  apply parts_eq_of_core (fun _ h ↦ (p.subtypeCongr q).partition.parts_pos h)
  · intro j hj
    exact (Multiset.mem_add.mp hj).elim (fun h ↦ p.partition.parts_pos h)
      (fun h ↦ q.partition.parts_pos h)
  · rw [Multiset.sum_add, Nat.Partition.parts_sum, Nat.Partition.parts_sum, Nat.Partition.parts_sum,
      Fintype.card_subtype_compl]
    exact (Nat.add_sub_of_le (Fintype.card_subtype_le _)).symm
  · simp only [nontrivialParts, Multiset.filter_add, Perm.filter_parts_partition_eq_cycleType]
    rw [he, hd.cycleType_mul, Perm.cycleType_ofSubtype, Perm.cycleType_ofSubtype]

lemma fixes_iff_parts {n k : ℕ} (p : Perm (Fin n)) :
    Green87.FixesSet p k ↔ k ∈ sums p.partition.parts := by
  constructor
  · rintro ⟨s, hc, hi⟩
    have h := (image_stable p s).mp hi
    let u := p.subtypePerm h
    let v : Perm {x // x ∉ s} := p.subtypePerm (fun x ↦ (h x).not)
    have he : u.subtypeCongr v = p := by
      ext x
      by_cases hx : x ∈ s
      · rw [Perm.subtypeCongr.left_apply _ _ hx]; rfl
      · rw [Perm.subtypeCongr.right_apply _ _ hx]; rfl
    rw [← he, split_perm]
    exact mem_sums.mpr ⟨u.partition.parts, by simp, by simpa [hc] using u.partition.parts_sum⟩
  · intro hk
    obtain ⟨a, ha, hka⟩ := mem_sums.mp hk
    obtain ⟨b, hb⟩ := Multiset.le_iff_exists_add.mp ha
    have hsum := p.partition.parts_sum
    rw [hb, Multiset.sum_add, Fintype.card_fin, hka] at hsum
    obtain ⟨s, _, hsk⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := k)
      (by simpa using (show k ≤ n by omega))
    have hp (j) (hj : j ∈ a + b) : 0 < j := p.partition.parts_pos (hb ▸ hj)
    obtain ⟨u, hu⟩ := full_parts_realized s (by simpa [hsk] using hka)
      (fun j hj ↦ hp j (Multiset.mem_add.mpr (Or.inl hj)))
    obtain ⟨v, hv⟩ := full_parts_realized {x : Fin n // x ∉ s} (a := b)
      (by rw [Fintype.card_subtype_compl]; simp [hsk]; omega)
      (fun j hj ↦ hp j (Multiset.mem_add.mpr (Or.inr hj)))
    let q := u.subtypeCongr v
    have hq : q.partition = p.partition := Nat.Partition.ext (by
      change (u.subtypeCongr v).partition.parts = _
      rw [split_perm, hu, hv, hb])
    have hqfix : stable q s := by
      intro x
      by_cases hx : x ∈ s
      · rw [show q x = _ from Perm.subtypeCongr.left_apply u v hx]
        exact iff_of_true (u ⟨x,hx⟩).property hx
      · rw [show q x = _ from Perm.subtypeCongr.right_apply u v hx]
        exact iff_of_false (v ⟨x,hx⟩).property hx
    obtain ⟨e, he⟩ := isConj_iff.mp (Perm.partition_eq_of_isConj.mpr hq)
    refine ⟨s.image e, (card_image_of_injective _ e.injective).trans hsk, (image_stable _ _).mpr ?_⟩
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← he]
    simpa [Perm.mul_apply] using hqfix y

lemma denominator_disjoint (a b : Multiset ℕ) (hd : ∀ i ∈ a, i ∉ b) :
    denominator (a + b) = denominator a * denominator b := by
  induction a using Multiset.induction_on with
  | empty => simp [denominator, multiplicity]
  | cons j a ih =>
    rw [Multiset.cons_add, denominator_cons, denominator_cons,
      ih (fun i hi ↦ hd i (Multiset.mem_cons_of_mem hi)), Multiset.count_add,
      Multiset.count_eq_zero.mpr (hd j (Multiset.mem_cons_self _ _)), add_zero]
    ring

lemma denominator_ones (r : ℕ) : denominator (Multiset.replicate r 1) = r.factorial := by
  induction r with
  | zero => simp [denominator, multiplicity]
  | succ r ih => simp [Multiset.replicate_succ, denominator_cons, ih, Nat.factorial_succ]

lemma prob_shape {n : ℕ} {b : Multiset ℕ} (hb : b ∈ shapes n) :
    (((univ : Finset (Perm (Fin n))).filter (fun p ↦ p.partition.parts = b)).card : ℝ) /
      n.factorial = weight b := by
  obtain ⟨hs, hp⟩ := mem_shapes.mp hb
  let u := nontrivialParts b
  have hf : (univ : Finset (Perm (Fin n))).filter (fun p ↦ p.partition.parts = b) =
      univ.filter (fun p ↦ p.cycleType = u) := by
    ext p
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      change p.cycleType = nontrivialParts b
      rw [← h]
      exact Perm.filter_parts_partition_eq_cycleType.symm
    · intro h
      apply parts_eq_of_core (fun j hj ↦ p.partition.parts_pos hj) hp
      · simpa [hs] using p.partition.parts_sum
      · exact Perm.filter_parts_partition_eq_cycleType.trans h
  have hsplit : b = u + Multiset.replicate (n - u.sum) 1 := by simpa [u,hs] using split_ones hp
  have hlarge (j) (hj : j ∈ u) : 2 ≤ j := (Multiset.mem_filter.mp hj).2
  have hsum : u.sum ≤ n := by
    have he := congrArg Multiset.sum hsplit
    rw [Multiset.sum_add, hs] at he
    omega
  have hden : denominator b = denominator u * (n-u.sum).factorial := by
    conv_lhs => rw [hsplit]
    rw [denominator_disjoint, denominator_ones]
    intro i hi h
    have := Multiset.eq_of_mem_replicate h
    have := hlarge i hi
    omega
  have hc := Perm.card_of_cycleType_mul_eq (Fin n) u
  simp only [Fintype.card_fin, if_pos (And.intro hsum hlarge)] at hc
  have hcn : ((univ : Finset (Perm (Fin n))).filter (fun p ↦ p.cycleType = u)).card *
      denominator b = n.factorial := by
    rw [hden]
    convert hc using 1
    unfold denominator multiplicity
    ring
  rw [hf, weight]
  have hd : (0 : ℝ) < (denominator b : ℝ) := by exact_mod_cast denominator_pos hp
  have hn : (0 : ℝ) < n.factorial := by positivity
  rw [div_eq_iff hn.ne', inv_mul_eq_div, eq_div_iff hd.ne']
  exact_mod_cast hcn

lemma probability_formula (n k : ℕ) :
    Green87.i n k = ∑ b ∈ (shapes n).filter (fun b ↦ k ∈ sums b), weight b := by
  classical
  let f := fun p : Perm (Fin n) ↦ p.partition.parts
  let s := (univ : Finset (Perm (Fin n))).filter (fun p ↦ Green87.FixesSet p k)
  let t := (shapes n).filter (fun b ↦ k ∈ sums b)
  have hmaps : ∀ p ∈ s, f p ∈ t := by
    intro p hp
    exact mem_filter.mpr ⟨mem_shapes.mpr ⟨by simpa [f] using p.partition.parts_sum,
      fun _ h ↦ p.partition.parts_pos h⟩, (fixes_iff_parts p).mp (mem_filter.mp hp).2⟩
  have hc : Nat.card {p : Perm (Fin n) // Green87.FixesSet p k} = s.card := by
    simp [s, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hd : Nat.card (Perm (Fin n)) = n.factorial := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [Green87.i, hc, hd, card_eq_sum_card_fiberwise hmaps, Nat.cast_sum, sum_div]
  refine sum_congr rfl fun b hb ↦ ?_
  have he : s.filter (fun p ↦ f p = b) = univ.filter (fun p : Perm (Fin n) ↦ p.partition.parts = b) := by
    ext p
    simp only [s, mem_filter, mem_univ, true_and, f, and_iff_right_iff_imp]
    exact fun h ↦ (fixes_iff_parts p).mpr (h ▸ (mem_filter.mp hb).2)
  rw [he]
  exact prob_shape (mem_filter.mp hb).1

end
end Green87Local

/- Removing a marked cycle and the uniform sieve of Lemma 2.3. -/
namespace Green87Local
open Finset
noncomputable section

lemma cycle_total (b : Multiset ℕ) (s : Finset ℕ) (h : ∀ j ∈ b, j ∈ s) :
    (∑ j ∈ s, j * b.count j) = b.sum := by
  calc
    _ = ∑ j ∈ b.toFinset, j * b.count j := by
      symm
      apply sum_subset (fun j hj ↦ h j (Multiset.mem_toFinset.mp hj))
      intro j _ hj
      simp [Multiset.count_eq_zero.mpr (mt Multiset.mem_toFinset.mpr hj)]
    _ = _ := by simpa [nsmul_eq_mul, mul_comm] using (sum_multiset_map_count b id).symm

lemma mark_part {m n j : ℕ} (hm : 0 < m) (hj : m ≤ j) (hn : j ≤ n)
    (F : Multiset ℕ → ℝ) :
    (∑ b ∈ rough m n, ((j : ℝ) * b.count j * weight b) * F (b.erase j)) =
      ∑ a ∈ rough m (n-j), weight a * F a := by
  classical
  have he : (rough m n).filter (j ∈ ·) = (rough m (n-j)).image (Multiset.cons j) := by
    ext b
    constructor
    · intro h
      obtain ⟨hb, hjb⟩ := mem_filter.mp h
      obtain ⟨hs, hmin⟩ := (mem_rough hm).mp hb
      refine mem_image.mpr ⟨b.erase j, (mem_rough hm).mpr ⟨?_, ?_⟩, Multiset.cons_erase hjb⟩
      · have hx := congrArg Multiset.sum (Multiset.cons_erase hjb)
        simp only [Multiset.sum_cons, hs] at hx
        omega
      · exact fun i hi ↦ hmin i (Multiset.mem_of_le (Multiset.erase_le _ _) hi)
    · rintro h
      obtain ⟨a, ha, rfl⟩ := mem_image.mp h
      obtain ⟨hs, hmin⟩ := (mem_rough hm).mp ha
      exact mem_filter.mpr ⟨(mem_rough hm).mpr
        ⟨by simp [hs, Nat.add_sub_of_le hn], by simpa using And.intro hj hmin⟩,
        Multiset.mem_cons_self _ _⟩
  calc
    _ = ∑ b ∈ (rough m n).filter (j ∈ ·), ((j : ℝ) * b.count j * weight b) * F (b.erase j) := by
      symm
      apply sum_subset (filter_subset _ _)
      intro b hb h
      have h' : j ∉ b := fun hjb ↦ h (mem_filter.mpr ⟨hb, hjb⟩)
      simp [Multiset.count_eq_zero.mpr h']
    _ = ∑ b ∈ (rough m n).filter (j ∈ ·), weight (b.erase j) * F (b.erase j) := by
      apply sum_congr rfl
      intro b hb
      rw [weight_mark _ (hm.trans_le hj) (mem_filter.mp hb).2]
    _ = _ := by
      rw [he, sum_image]
      · simp
      · intro a _ b _ h
        exact (Multiset.cons_inj_right j).mp h

lemma sieve_recurrence {m n : ℕ} (hm : 0 < m) :
    n * sieve m n = ∑ j ∈ Icc m n, sieve m (n-j) := by
  unfold sieve
  rw [mul_sum]
  calc
    _ = ∑ b ∈ rough m n, ∑ j ∈ Icc m n, (j : ℝ) * b.count j * weight b := by
      apply sum_congr rfl
      intro b hb
      obtain ⟨hs, hmin⟩ := (mem_rough hm).mp hb
      have h := cycle_total b (Icc m n) (fun j hj ↦
        mem_Icc.mpr ⟨hmin j hj, hs ▸ Multiset.le_sum_of_mem hj⟩)
      rw [← sum_mul]
      congr 1
      exact_mod_cast (h.trans hs).symm
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun j hj ↦ ?_
      obtain ⟨h1,h2⟩ := mem_Icc.mp hj
      simpa only [mul_one] using mark_part hm h1 h2 (fun _ ↦ 1)

lemma sieve_bounds {m n : ℕ} (hm : 0 < m) (hn : m ≤ n) :
    1 / (2 * m : ℝ) ≤ sieve m n ∧ sieve m n ≤ 1 / (m : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn' : (0 : ℝ) < n := by exact_mod_cast hm.trans_le hn
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hrec := sieve_recurrence (n := n) hm
    have hnmem : n ∈ Icc m n := mem_Icc.mpr ⟨hn, le_rfl⟩
    rw [← add_sum_erase _ _ hnmem, Nat.sub_self, sieve_zero] at hrec
    let t := Icc m (n - m)
    have he : ∑ j ∈ (Icc m n).erase n, sieve m (n-j) = ∑ j ∈ t, sieve m (n-j) := by
      symm
      apply sum_subset
      · intro j hj
        obtain ⟨h1,h2⟩ := mem_Icc.mp hj
        exact mem_erase.mpr ⟨by omega, mem_Icc.mpr ⟨h1,by omega⟩⟩
      · intro j hj ht
        obtain ⟨hj1,hj2⟩ := mem_erase.mp hj
        have := mem_Icc.mp hj2
        exact sieve_below (by omega) (by
          by_contra! hh
          exact ht (mem_Icc.mpr ⟨this.1, by omega⟩))
    rw [he] at hrec
    have hb (j) (hj : j ∈ t) := ih (n-j) (by
      obtain ⟨h1,h2⟩ := mem_Icc.mp hj
      omega) (by obtain ⟨h1,h2⟩ := mem_Icc.mp hj; omega)
    have hlo := sum_le_sum (s := t) (fun j hj ↦ (hb j hj).1)
    have hhi := sum_le_sum (s := t) (fun j hj ↦ (hb j hj).2)
    simp only [sum_const, nsmul_eq_mul] at hlo hhi
    have hc : t.card = n - m + 1 - m := Nat.card_Icc _ _
    have hcl : n ≤ 2*m + t.card := by omega
    have hcu : m + t.card ≤ n := by omega
    have hl : (n : ℝ) ≤ 2 * m + (t.card : ℝ) := by exact_mod_cast hcl
    have hu : (m : ℝ) + (t.card : ℝ) ≤ n := by exact_mod_cast hcu
    constructor
    · apply (div_le_iff₀ (show (0:ℝ) < 2*m by positivity)).mpr
      apply le_of_mul_le_mul_left (a := (n:ℝ)) _ hn'
      rw [mul_one, ← mul_assoc, hrec]
      have hh : (t.card : ℝ) ≤ (∑ j ∈ t, sieve m (n-j)) * (2*m) := by
        calc
          _ = ((t.card : ℝ) * (1/(2*m))) * (2*m) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right hlo (by positivity)
      linarith
    · apply (le_div_iff₀ hm').mpr
      apply le_of_mul_le_mul_left (a := (n:ℝ)) _ hn'
      rw [mul_one, ← mul_assoc, hrec]
      have hh : (∑ j ∈ t, sieve m (n-j)) * m ≤ t.card := by
        calc
          _ ≤ ((t.card : ℝ) * (1/m)) * m := mul_le_mul_of_nonneg_right hhi hm'.le
          _ = _ := by field_simp
      linarith

end
end Green87Local

/- Bounded families of partitions and estimates for attainable sums. -/
namespace Green87Local
open Finset
noncomputable section

lemma sum_injection {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β)
    (f : α → β) (u : α → ℝ) (v : β → ℝ)
    (hm : ∀ x ∈ s, f x ∈ t) (hi : Set.InjOn f (s : Set α))
    (hle : ∀ x ∈ s, u x ≤ v (f x)) (hn : ∀ y ∈ t, 0 ≤ v y) :
    ∑ x ∈ s, u x ≤ ∑ y ∈ t, v y := by
  calc
    _ ≤ ∑ x ∈ s, v (f x) := sum_le_sum hle
    _ = ∑ y ∈ s.image f, v y := (sum_image hi).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by rintro _ hy; obtain ⟨x,hx,rfl⟩ := mem_image.mp hy; exact hm x hx) (fun y hy _ ↦ hn y hy)

def boundedShapes (n : ℕ) : Finset (Multiset ℕ) := (range (n+1)).biUnion shapes

lemma mem_bounded {b : Multiset ℕ} {n : ℕ} :
    b ∈ boundedShapes n ↔ b.sum ≤ n ∧ ∀ j ∈ b, 0 < j := by
  simp only [boundedShapes, mem_biUnion, mem_range, mem_shapes]
  constructor
  · rintro ⟨i, hi, he, hp⟩
    exact ⟨by omega,hp⟩
  · rintro ⟨hn,hp⟩
    exact ⟨b.sum,by omega,rfl,hp⟩

def shortParts (k : ℕ) (b : Multiset ℕ) := b.filter (· ≤ k)
def longParts (k : ℕ) (b : Multiset ℕ) := b.filter (fun j ↦ ¬ j ≤ k)

lemma split_parts (k : ℕ) (b : Multiset ℕ) : shortParts k b + longParts k b = b :=
  Multiset.filter_add_not _ _

lemma split_weight (k : ℕ) (b : Multiset ℕ) :
    weight b = weight (shortParts k b) * weight (longParts k b) := by
  rw [← weight_disjoint, split_parts]
  exact fun j hj hl ↦ (Multiset.mem_filter.mp hl).2 (Multiset.mem_filter.mp hj).2

lemma sum_le_of_le {b c : Multiset ℕ} (h : b ≤ c) : b.sum ≤ c.sum := by
  obtain ⟨t,rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp

lemma sums_mono {b c : Multiset ℕ} (h : b ≤ c) : sums b ⊆ sums c := by
  intro j hj
  obtain ⟨a,ha,rfl⟩ := mem_sums.mp hj
  exact mem_sums.mpr ⟨a,ha.trans h,rfl⟩

lemma short_sums {b : Multiset ℕ} {r k : ℕ} (h : r ∈ sums b) (hr : r ≤ k) :
    r ∈ sums (shortParts k b) := by
  obtain ⟨a,ha,rfl⟩ := mem_sums.mp h
  have he : a.filter (· ≤ k) = a :=
    Multiset.filter_eq_self.mpr (fun j hj ↦ (Multiset.le_sum_of_mem hj).trans hr)
  exact mem_sums.mpr ⟨a, he ▸ Multiset.filter_le_filter _ ha, rfl⟩

lemma sums_add_rep_le (b : Multiset ℕ) (j v : ℕ) :
    (sums (b + Multiset.replicate v j)).card ≤ (sums b).card * (v+1) := by
  let f : ℕ × ℕ → ℕ := fun p ↦ p.1 + p.2*j
  have h : sums (b + Multiset.replicate v j) ⊆ ((sums b) ×ˢ range (v+1)).image f := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_sums.mp hx
    have hb : a - b ≤ Multiset.replicate v j := Multiset.sub_le_iff_le_add'.mpr ha
    obtain ⟨z, hz, he⟩ := Multiset.le_replicate_iff.mp hb
    have ht := congrArg Multiset.sum (Multiset.sub_add_inter a b)
    rw [Multiset.sum_add, he, Multiset.sum_replicate, nsmul_eq_mul] at ht
    refine mem_image.mpr ⟨((a ∩ b).sum,z), mem_product.mpr ⟨?_,mem_range.mpr (by omega)⟩,(Nat.add_comm _ _).trans ht⟩
    exact mem_sums.mpr ⟨_, Multiset.inter_le_right, rfl⟩
  exact (card_le_card h).trans (card_image_le.trans (by simp))

lemma sums_cons_le (a : Multiset ℕ) (j : ℕ) : (sums (j ::ₘ a)).card ≤ 2 * (sums a).card := by
  simpa [← Multiset.singleton_add, add_comm a, mul_comm] using sums_add_rep_le a j 1

end
end Green87Local

/- Conversion between multiplicity vectors and multisets of cycle lengths. -/
namespace Green87Local
open Finset
noncomputable section

def pack {k : ℕ} (a : Fin k → ℕ) : Multiset ℕ := ∑ j, Multiset.replicate (a j) (j.val+1)

lemma count_pack {k : ℕ} (a : Fin k → ℕ) (j : Fin k) : (pack a).count (j.val+1) = a j := by
  classical
  simp only [pack, Multiset.count_sum', Multiset.count_replicate]
  rw [sum_eq_single j]
  · simp
  · intro i _ h
    have h' : i.val + 1 ≠ j.val + 1 := fun he ↦ h (Fin.ext (by omega))
    exact if_neg h'
  · simp

lemma mem_pack {k : ℕ} {a : Fin k → ℕ} {i : ℕ} (hi : i ∈ pack a) : i ∈ Icc 1 k := by
  obtain ⟨j, _, hj⟩ := Multiset.mem_sum.mp hi
  have he := Multiset.eq_of_mem_replicate hj
  exact mem_Icc.mpr ⟨by omega, by have := j.isLt; omega⟩

def counts (k : ℕ) (b : Multiset ℕ) (j : Fin k) : ℕ := b.count (j.val+1)

lemma pack_counts {k : ℕ} {b : Multiset ℕ} (h : ∀ i ∈ b, i ∈ Icc 1 k) :
    pack (counts k b) = b := by
  ext i
  by_cases hi : i ∈ Icc 1 k
  · obtain ⟨h1,h2⟩ := mem_Icc.mp hi
    let j : Fin k := ⟨i-1, by omega⟩
    have he : j.val+1 = i := by dsimp [j]; omega
    simpa only [counts, he] using count_pack (counts k b) j
  · rw [Multiset.count_eq_zero.mpr (fun hh ↦ hi (mem_pack hh)),
      Multiset.count_eq_zero.mpr (fun hh ↦ hi (h i hh))]

lemma sum_pack {k : ℕ} (a : Fin k → ℕ) : (pack a).sum = ∑ j, (j.val+1) * a j := by
  simp [pack, Multiset.sum_sum, Multiset.sum_replicate, mul_comm]

lemma pack_mono {k : ℕ} {a b : Fin k → ℕ} (h : ∀ j, a j ≤ b j) : pack a ≤ pack b :=
  sum_le_sum fun j _ ↦ Multiset.replicate_mono _ (h j)

lemma sums_pack {k : ℕ} (a : Fin k → ℕ) : sums (pack a) = values a := by
  ext v
  rw [mem_sums]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' := pack_counts (fun i (hi : i ∈ t) ↦ mem_pack (Multiset.mem_of_le ht hi))
    let b (j : Fin k) : Fin (a j+1) := ⟨(counts k t) j,
      Nat.lt_succ_of_le (by simpa [counts,count_pack] using
        (Multiset.le_iff_count.mp ht (j.val+1)))⟩
    exact mem_image.mpr ⟨b, mem_univ _, (sum_pack (counts k t)).symm.trans (congrArg Multiset.sum ht')⟩
  · intro h
    obtain ⟨b, _, rfl⟩ := mem_image.mp h
    exact ⟨pack (fun j ↦ (b j).val), pack_mono (fun j ↦ Nat.le_of_lt_succ (b j).isLt), sum_pack _⟩

lemma pack_snoc {k : ℕ} (a : Fin k → ℕ) (v : ℕ) :
    pack (Fin.snoc (α := fun _ ↦ ℕ) a v) = pack a + Multiset.replicate v (k+1) := by
  simp [pack, Fin.sum_univ_castSucc]

lemma denom_replicate (v j : ℕ) : denominator (Multiset.replicate v j) = v.factorial * j ^ v := by
  induction v with
  | zero => simp [denominator, multiplicity]
  | succ v ih =>
    rw [Multiset.replicate_succ, denominator_cons, ih, Multiset.count_replicate_self,
      Nat.factorial_succ, pow_succ]
    ring

lemma weight_pack {k : ℕ} (a : Fin k → ℕ) :
    weight (pack a) = ∏ j, (1 / ((a j).factorial * ((j.val + 1 : ℕ) : ℝ) ^ a j)) := by
  induction k with
  | zero => simp [pack]
  | succ k ih =>
    let e := Fin.snocEquiv (fun _ : Fin (k+1) ↦ ℕ)
    obtain ⟨⟨v,c⟩,rfl⟩ := e.surjective a
    change weight (pack (Fin.snoc c v)) = _
    rw [pack_snoc, weight_disjoint, ih c, Fin.prod_univ_castSucc]
    · simp [e, Fin.snocEquiv, weight, denom_replicate, one_div]
    · intro i hi hi'
      have hle := (mem_Icc.mp (mem_pack hi)).2
      have he := Multiset.eq_of_mem_replicate hi'
      omega

lemma law_pack {k : ℕ} (a : Fin k → ℕ) :
    law a = Real.exp (-(harmonic k : ℝ)) * weight (pack a) := by
  rw [law, weight_pack]
  convert_to (∏ j : Fin k, atom (j.val+1) (a j)) =
    (∏ j : Fin k, Real.exp (-(1/((j.val+1 : ℕ) : ℝ)))) *
    ∏ j : Fin k, 1 / ((a j).factorial * ((j.val + 1 : ℕ) : ℝ) ^ a j)
  · congr 1
    rw [← Real.exp_sum]
    congr 1
    simp [harmonic, ← Fin.sum_univ_eq_sum_range, sum_neg_distrib, one_div]
  simp [atom, prod_mul_distrib, div_eq_mul_inv]

def weightedValues (b : Multiset ℕ) : ℝ := (sums b).card * weight b

lemma weighted_nonneg (b : Multiset ℕ) : 0 ≤ weightedValues b := mul_nonneg (by positivity) (weight_nonneg _)

lemma hasSum_raw (k : ℕ) :
    HasSum (fun a : Fin k → ℕ ↦ weightedValues (pack a)) (Real.exp (harmonic k) * expectation k) := by
  apply ((summable_expectation k).hasSum.mul_left (Real.exp (harmonic k))).congr_fun
  intro a
  rw [weightedValues, sums_pack, law_pack, Real.exp_neg]
  have h := (Real.exp_pos (harmonic k)).ne'
  field_simp

lemma exp_harmonic_lower (k : ℕ) : (k : ℝ) + 1 ≤ Real.exp (harmonic k) := by
  have h := Real.exp_le_exp.mpr (log_add_one_le_harmonic k)
  push_cast at h
  rwa [Real.exp_log (by positivity)] at h

lemma exp_harmonic_upper {k : ℕ} (hk : 0 < k) : Real.exp (harmonic k) ≤ Real.exp 1 * k := by
  have h := Real.exp_le_exp.mpr (harmonic_le_one_add_log k)
  simpa only [Real.exp_add, Real.exp_log (by positivity : (0:ℝ) < k)] using h

end
end Green87Local

/- Mark one point on each side of an invariant set and remove their cycles. -/
namespace Green87Local
open Finset
noncomputable section

lemma rough_one (n : ℕ) : rough 1 n = shapes n := by
  ext a
  rw [mem_rough (by decide), mem_shapes]
  rfl

def markScore (k j q : ℕ) (a : Multiset ℕ) : ℝ :=
  if k-j ∈ sums ((a.erase j).erase q) then
    (j : ℝ) * a.count j * weight a * ((q : ℝ) * (a.erase j).count q) else 0

lemma markScore_nonneg (k j q : ℕ) (a : Multiset ℕ) : 0 ≤ markScore k j q a := by
  unfold markScore
  split_ifs
  · exact mul_nonneg (mul_nonneg (by positivity) (weight_nonneg _)) (by positivity)
  · rfl

/-- For a fixed invariant split, mark a point on either side. The second count
uses the partition after the first deletion, even when the lengths agree. -/
lemma marked_split {a : Multiset ℕ} {k l : ℕ} (ha : a ∈ shapes (k+l)) (hk : k ∈ sums a) :
    (k : ℝ) * l * weight a ≤
      ∑ j ∈ Icc 1 k, ∑ q ∈ Icc 1 l, markScore k j q a := by
  obtain ⟨u,hu,hk'⟩ := mem_sums.mp hk
  obtain ⟨v,rfl⟩ := Multiset.le_iff_exists_add.mp hu
  obtain ⟨hs,hp⟩ := mem_shapes.mp ha
  rw [Multiset.sum_add, hk'] at hs
  have hl : v.sum = l := by omega
  have htot (b : Multiset ℕ) (hb : ∀ i ∈ b, 0 < i) :
      (b.sum : ℝ) = ∑ j ∈ Icc 1 b.sum, (j : ℝ) * b.count j := by
    exact_mod_cast (cycle_total b _ (fun j hj ↦ mem_Icc.mpr ⟨hb j hj,Multiset.le_sum_of_mem hj⟩)).symm
  have hu' := htot u (fun i hi ↦ hp i (Multiset.mem_add.mpr (Or.inl hi)))
  have hv' := htot v (fun i hi ↦ hp i (Multiset.mem_add.mpr (Or.inr hi)))
  rw [hk'] at hu'
  rw [hl] at hv'
  calc
    _ = ∑ j ∈ Icc 1 k, ∑ q ∈ Icc 1 l,
        ((j : ℝ) * u.count j) * (q * (v.count q : ℝ)) * weight (u+v) := by
      simp only [← sum_mul, ← mul_sum, ← hu', ← hv']
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro q hq
      by_cases hju : j ∈ u
      · by_cases hqv : q ∈ v
        · have he1 : (u+v).erase j = u.erase j + v := Multiset.erase_add_left_pos _ hju
          have he2 : ((u+v).erase j).erase q = u.erase j + v.erase q := by
            rw [he1, add_comm, Multiset.erase_add_left_pos _ hqv, add_comm]
          have hsub : k-j ∈ sums (((u+v).erase j).erase q) := by
            rw [he2]
            refine mem_sums.mpr ⟨u.erase j, by simp, ?_⟩
            have h := congrArg Multiset.sum (Multiset.cons_erase hju)
            rw [Multiset.sum_cons, hk'] at h
            omega
          rw [markScore, if_pos hsub, he1]
          have h1 : (u.count j : ℝ) ≤ (u+v).count j := by simp
          have h2 : (v.count q : ℝ) ≤ (u.erase j + v).count q := by simp
          calc
            _ = ((j : ℝ) * u.count j * weight (u+v)) * (q * (v.count q : ℝ)) := by ring
            _ ≤ _ := by
              have hw := weight_nonneg (u+v)
              gcongr
        · simp only [Multiset.count_eq_zero.mpr hqv, Nat.cast_zero, mul_zero, zero_mul]
          exact markScore_nonneg _ _ _ _
      · simp only [Multiset.count_eq_zero.mpr hju, Nat.cast_zero, mul_zero, zero_mul]
        exact markScore_nonneg _ _ _ _

lemma marked_remove {k l j q : ℕ} (hj : j ∈ Icc 1 k) (hq : q ∈ Icc 1 l) :
    (∑ a ∈ shapes (k+l), markScore k j q a) =
      ∑ b ∈ shapes (k+l-j-q), if k-j ∈ sums b then weight b else 0 := by
  have hj' := mem_Icc.mp hj
  have hq' := mem_Icc.mp hq
  let F := fun b : Multiset ℕ ↦ if k-j ∈ sums b then (1:ℝ) else 0
  let G := fun b : Multiset ℕ ↦ ((q : ℝ) * b.count q) * F (b.erase q)
  have h1 := mark_part (n := k+l) (j := j) (by decide : 0 < 1) hj'.1 (by omega) G
  have h2 := mark_part (n := k+l-j) (j := q) (by decide : 0 < 1) hq'.1 (by omega) F
  rw [rough_one, rough_one] at h1 h2
  calc
    _ = ∑ a ∈ shapes (k+l), ((j : ℝ) * a.count j * weight a) * G (a.erase j) := by
      apply sum_congr rfl
      intro a _
      simp [G, F, markScore, mul_ite]
    _ = _ := h1
    _ = ∑ a ∈ shapes (k+l-j), ((q : ℝ) * a.count q * weight a) * F (a.erase q) := by
      apply sum_congr rfl
      intro a _
      dsimp [G]
      ring
    _ = _ := h2
    _ = _ := by simp [F, mul_ite]

lemma marked_bound (k l : ℕ) :
    (k : ℝ) * l * Green87.i (k+l) k ≤ ∑ j ∈ Icc 1 k, ∑ q ∈ Icc 1 l,
      ∑ b ∈ shapes (k+l-j-q), if k-j ∈ sums b then weight b else 0 := by
  rw [probability_formula, mul_sum]
  calc
    _ ≤ ∑ a ∈ (shapes (k+l)).filter (fun a ↦ k ∈ sums a),
          ∑ j ∈ Icc 1 k, ∑ q ∈ Icc 1 l, markScore k j q a :=
      sum_le_sum (fun a ha ↦ marked_split (mem_filter.mp ha).1 (mem_filter.mp ha).2)
    _ ≤ ∑ a ∈ shapes (k+l), ∑ j ∈ Icc 1 k, ∑ q ∈ Icc 1 l, markScore k j q a :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        (fun a _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ markScore_nonneg _ _ _ _)
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [sum_comm]
      exact sum_congr rfl fun q hq ↦ marked_remove hj hq

/-- Once the residual partition is fixed, its total determines the second removed
length from the first. The first lengths inject into its short subset sums. -/
lemma marked_average (k l : ℕ) :
    (k : ℝ) * l * Green87.i (k+l) k ≤
      ∑ b ∈ boundedShapes (k+l), (sums (shortParts k b)).card * weight b := by
  apply (marked_bound k l).trans
  let F (j : ℕ) (b : Multiset ℕ) : ℝ := if k-j ∈ sums b then weight b else 0
  calc
    _ ≤ ∑ j ∈ Icc 1 k, ∑ b ∈ boundedShapes (k+l), F j b := by
      apply sum_le_sum
      intro j hj
      have hj' := mem_Icc.mp hj
      have hd : (SetLike.coe (Icc 1 l) : Set ℕ).PairwiseDisjoint
          (fun q ↦ shapes (k+l-j-q)) := by
        intro q hq p hp hne
        apply disjoint_left.mpr
        intro a ha hb
        have h1 := (mem_shapes.mp ha).1
        have h2 := (mem_shapes.mp hb).1
        have h3 := mem_Icc.mp hq
        have h4 := mem_Icc.mp hp
        omega
      trans ∑ b ∈ (Icc 1 l).biUnion (fun q ↦ shapes (k+l-j-q)), F j b
      · exact (sum_biUnion hd).symm.le
      · apply sum_le_sum_of_subset_of_nonneg
        · intro b hb
          obtain ⟨q, hq, hh⟩ := mem_biUnion.mp hb
          obtain ⟨hs,hp⟩ := mem_shapes.mp hh
          exact mem_bounded.mpr ⟨by omega,hp⟩
        · intro b _ _
          dsimp [F]
          split_ifs <;> first | exact weight_nonneg _ | rfl
    _ ≤ _ := by
      rw [sum_comm]
      apply sum_le_sum
      intro b _
      rw [show (∑ j ∈ Icc 1 k, F j b) = (((Icc 1 k).filter (fun j ↦ k-j ∈ sums b)).card : ℝ) * weight b by
        simp only [F, ← sum_filter, sum_const, nsmul_eq_mul]]
      apply mul_le_mul_of_nonneg_right _ (weight_nonneg _)
      exact_mod_cast card_le_card_of_injOn (fun j ↦ k-j)
        (fun j hj ↦ short_sums (mem_filter.mp hj).2 (Nat.sub_le _ _))
        (fun j hj q hq he ↦ by
          have h1 := (mem_Icc.mp (mem_filter.mp hj).1).2
          have h2 := (mem_Icc.mp (mem_filter.mp hq).1).2
          dsimp at he
          omega)

end
end Green87Local

/- Growth in the dimension and truncation of the weighted first moment. -/
namespace Green87Local
open Finset
noncomputable section

lemma pack_injective (k : ℕ) : Function.Injective (@pack k) := by
  intro a b h
  funext j
  simpa only [count_pack] using congrArg (Multiset.count (j.val+1)) h

lemma sum_raw_le (k : ℕ) (s : Finset (Multiset ℕ))
    (h : ∀ b ∈ s, ∀ j ∈ b, j ∈ Icc 1 k) :
    ∑ b ∈ s, weightedValues b ≤ Real.exp (harmonic k) * expectation k := by
  classical
  have hh (b) (hb : b ∈ s) := pack_counts (h b hb)
  calc
    _ = ∑ a ∈ s.image (counts k), weightedValues (pack a) := by
      rw [sum_image]
      · exact sum_congr rfl fun b hb ↦ by rw [hh b hb]
      · intro a ha b hb he
        rw [← hh a ha, ← hh b hb, he]
    _ ≤ _ := by
      rw [← (hasSum_raw k).tsum_eq]
      exact (hasSum_raw k).summable.sum_le_tsum _ (fun a _ ↦ weighted_nonneg _)

lemma growth_one (k : ℕ) :
    expectation (k+1) ≤ (1 + 1/((k+1 : ℕ) : ℝ)) * expectation k := by
  let e := Fin.snocEquiv (fun _ : Fin (k+1) ↦ ℕ)
  let f : ℕ → ℝ := fun v ↦ (v+1 : ℝ) * atom (k+1) v
  let g : (Fin k → ℕ) → ℝ := fun a ↦ (values a).card * law a
  have hf : HasSum f (1 + 1/((k+1 : ℕ) : ℝ)) := hasSum_atom_envelope (Nat.succ_pos k)
  have hg : HasSum g (expectation k) := (summable_expectation k).hasSum
  have hf0 : 0 ≤ f := fun v ↦ mul_nonneg (by positivity) (atom_nonneg _ _)
  have hg0 : 0 ≤ g := fun a ↦ mul_nonneg (by positivity) (law_nonneg _)
  have hprod := HasSum.mul (f := f) (g := g) hf hg
    (Summable.mul_of_nonneg (f := f) (g := g) hf.summable hg.summable hf0 hg0)
  rw [← hprod.tsum_eq, expectation, ← e.tsum_eq]
  apply ((e.hasSum_iff.mpr (summable_expectation (k+1)).hasSum).summable).tsum_le_tsum _ hprod.summable
  rintro ⟨v,a⟩
  change (values (Fin.snoc a v)).card * law (Fin.snoc a v) ≤ f v * g a
  have hc : ((values (Fin.snoc a v)).card : ℝ) ≤ (values a).card * (v+1 : ℝ) := by
    rw [← sums_pack, pack_snoc, ← sums_pack]
    exact_mod_cast sums_add_rep_le (pack a) (k+1) v
  have hp : law (Fin.snoc (α := fun _ ↦ ℕ) a v) = law a * atom (k+1) v := by
    simp [law, Fin.prod_univ_castSucc]
  rw [hp]
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (mul_nonneg (law_nonneg _) (atom_nonneg _ _))
    _ = _ := by dsimp [f,g]; ring

lemma growth {r k : ℕ} (h : r ≤ k) :
    expectation k / (k+1 : ℝ) ≤ expectation r / (r+1 : ℝ) := by
  induction k, h using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    apply le_trans _ ih
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right (growth_one k) (show (0:ℝ) ≤ k+1 by positivity)
    convert hh using 1
    push_cast
    field_simp

def truncShapes (r : ℕ) := (boundedShapes (4*r)).filter (fun b ↦ ∀ j ∈ b, j ≤ r)

def truncated (r : ℕ) : ℝ := ∑ b ∈ truncShapes r, weightedValues b

lemma moment_count (r : ℕ) (s : Finset (Multiset ℕ))
    (hs : ∀ b ∈ s, ∀ j ∈ b, j ∈ Icc 1 r) :
    ∑ b ∈ s, (b.sum : ℝ) * weightedValues b ≤
      2 * r * (Real.exp (harmonic r) * expectation r) := by
  classical
  let W := Real.exp (harmonic r) * expectation r
  calc
    _ = ∑ j ∈ Icc 1 r, ∑ b ∈ s, (j : ℝ) * b.count j * weightedValues b := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [← sum_mul]
      congr 1
      exact_mod_cast (cycle_total a _ (hs a ha)).symm
    _ ≤ ∑ _j ∈ Icc 1 r, 2 * W := by
      apply sum_le_sum
      intro j hj
      let t := s.filter (j ∈ ·)
      have ht : (∑ b ∈ s, (j : ℝ) * b.count j * weightedValues b) =
          ∑ b ∈ t, (j : ℝ) * b.count j * weightedValues b := by
        symm
        apply sum_subset (filter_subset ..)
        intro b hb hn
        have hnot : j ∉ b := fun hi ↦ hn (mem_filter.mpr ⟨hb,hi⟩)
        simp [Multiset.count_eq_zero.mpr hnot]
      rw [ht]
      calc
        _ ≤ ∑ b ∈ t, 2 * weightedValues (b.erase j) := by
          apply sum_le_sum
          intro b hb
          have hm := (mem_filter.mp hb).2
          have he := weight_mark b (mem_Icc.mp hj).1 hm
          have hc := sums_cons_le (b.erase j) j
          rw [Multiset.cons_erase hm] at hc
          unfold weightedValues
          calc
            _ = (sums b).card * weight (b.erase j) := by rw [← he]; ring
            _ ≤ _ := by
              rw [← mul_assoc]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (weight_nonneg _)
        _ = 2 * ∑ b ∈ t.image (fun b ↦ b.erase j), weightedValues b := by
          rw [sum_image, mul_sum]
          intro a ha b hb he
          change a.erase j = b.erase j at he
          rw [← Multiset.cons_erase (mem_filter.mp ha).2, ← Multiset.cons_erase (mem_filter.mp hb).2, he]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply sum_raw_le
          intro b hb i hi
          obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
          exact hs a (mem_filter.mp ha).1 i (Multiset.mem_of_le (Multiset.erase_le _ _) hi)
    _ = _ := by simp [Nat.card_Icc, W]; ring

/-- Removing one marked short cycle bounds the weighted size moment. Any
partition outside the truncation has total at least four times r plus one. -/
lemma truncation (r : ℕ) : Real.exp (harmonic r) * expectation r ≤ 2 * truncated r := by
  let W := Real.exp (harmonic r) * expectation r
  let d : ℝ := 4*r+1
  have hW : 0 ≤ W := mul_nonneg (Real.exp_pos _).le ((expectation_bounds r).1.trans' zero_le_one)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hT : 0 ≤ truncated r := sum_nonneg fun _ _ ↦ weighted_nonneg _
  have hresult : d * W ≤ d * truncated r + 2*r*W := by
    have ss := (hasSum_raw r).mul_left d
    rw [← ss.tsum_eq]
    apply ss.summable.tsum_le_of_sum_le
    intro A
    let B := A.image (@pack r)
    have hB (b) (hb : b ∈ B) (j) (hj : j ∈ b) : j ∈ Icc 1 r := by
      obtain ⟨a,_,rfl⟩ := mem_image.mp hb
      exact mem_pack hj
    have he : ∑ a ∈ A, d * weightedValues (pack a) = ∑ b ∈ B, d * weightedValues b :=
      (sum_image (s := A) (f := fun b ↦ d * weightedValues b) (pack_injective r).injOn).symm
    rw [he]
    calc
      _ ≤ ∑ b ∈ B, ((if b ∈ truncShapes r then d*weightedValues b else 0) +
          (b.sum : ℝ)*weightedValues b) := by
        apply sum_le_sum
        intro b hb
        split_ifs with h
        · exact le_add_of_nonneg_right (mul_nonneg (by positivity) (weighted_nonneg _))
        · have hh : 4*r < b.sum := by
            by_contra! hz
            exact h (mem_filter.mpr ⟨mem_bounded.mpr ⟨hz,fun i hi ↦ (mem_Icc.mp (hB b hb i hi)).1⟩,
              fun i hi ↦ (mem_Icc.mp (hB b hb i hi)).2⟩)
          rw [zero_add]
          exact mul_le_mul_of_nonneg_right (by dsimp [d]; exact_mod_cast hh) (weighted_nonneg _)
      _ ≤ _ := by
        rw [sum_add_distrib, ← sum_filter]
        apply add_le_add _ (moment_count r B hB)
        rw [truncated, mul_sum]
        exact sum_le_sum_of_subset_of_nonneg (fun b hb ↦ (mem_filter.mp hb).2)
          (fun b _ _ ↦ mul_nonneg hd (weighted_nonneg _))
  change W ≤ 2 * truncated r
  dsimp [d] at hresult
  by_contra! h
  nlinarith [mul_nonneg (Nat.cast_nonneg r : (0:ℝ) ≤ r) (sub_nonneg.mpr h.le)]

end
end Green87Local

/- Complete a short partition with one distinguished cycle and a rough tail. -/
namespace Green87Local
open Finset
noncomputable section

def upperHalf (b : Multiset ℕ) := (sums b).filter (fun s ↦ b.sum ≤ 2*s)

lemma reflected_sum {b : Multiset ℕ} {s : ℕ} (hs : s ∈ sums b) : b.sum-s ∈ sums b := by
  obtain ⟨t, ht, rfl⟩ := mem_sums.mp hs
  obtain ⟨d, rfl⟩ := Multiset.le_iff_exists_add.mp ht
  exact mem_sums.mpr ⟨d, by simp, by simp⟩

lemma half_card (b : Multiset ℕ) : (sums b).card ≤ 2 * (upperHalf b).card := by
  let lo := (sums b).filter (fun x ↦ ¬ b.sum ≤ 2*x)
  have h : lo.card ≤ (upperHalf b).card := by
    apply card_le_card_of_injOn (fun s ↦ b.sum-s)
    · intro s hs
      obtain ⟨h1,h2⟩ := mem_filter.mp hs
      exact mem_filter.mpr ⟨reflected_sum h1, by change b.sum ≤ 2*(b.sum-s); omega⟩
    · intro x hx y hy hxy
      have h1 := mem_sums_le (mem_filter.mp hx).1
      have h2 := mem_sums_le (mem_filter.mp hy).1
      dsimp at hxy
      omega
  have hc := card_filter_add_card_filter_not (s := sums b) (fun s ↦ b.sum ≤ 2*s)
  change (upperHalf b).card + lo.card = _ at hc
  omega

/-- At exact equality there must be two cycles of the distinguished length.
For a larger residual total use a strictly larger minimum tail length. -/
def tails (l N : ℕ) : Finset (Multiset ℕ) :=
  if N = l then {({l} : Multiset ℕ)} else rough (l+1) N

lemma tail_spec {l N : ℕ} {d : Multiset ℕ} (h : d ∈ tails l N) :
    d.sum = N ∧ ∀ j ∈ d, l ≤ j := by
  by_cases he : N = l
  · simp [tails, he] at h
    subst d
    simp [he]
  · rw [tails, if_neg he] at h
    obtain ⟨hs,hm⟩ := (mem_rough (Nat.succ_pos _)).mp h
    exact ⟨hs,fun j hj ↦ (Nat.le_succ _).trans (hm j hj)⟩

lemma wt_single (l : ℕ) : weight {l} = 1 / (l : ℝ) := by
  simpa using weight_cons (0 : Multiset ℕ) l

lemma tail_lower {l N k : ℕ} (hl : 0 < l) (hk : l ≤ k) (hN : l ≤ N) :
    1 ≤ (2 * ((k:ℝ)+1)^2) * ∑ d ∈ tails l N, weight (l ::ₘ d) := by
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hk' : (l : ℝ) ≤ k := by exact_mod_cast hk
  by_cases he : N = l
  · rw [tails, if_pos he, sum_singleton, weight_cons, wt_single]
    simp only [Multiset.count_singleton_self, Nat.cast_one]
    field_simp
    nlinarith [sq_nonneg ((k:ℝ)-l), mul_nonneg (sub_nonneg.mpr hk') hl'.le]
  · have hN' : l+1 ≤ N := by omega
    have hh := (sieve_bounds (Nat.succ_pos _) hN').1
    have heq : (∑ d ∈ tails l N, weight (l ::ₘ d)) = sieve (l+1) N / (l : ℝ) := by
      rw [tails, if_neg he, sieve, sum_div]
      apply sum_congr rfl
      intro b hb
      have hnot : l ∉ b := fun h ↦ Nat.not_succ_le_self _ (((mem_rough (Nat.succ_pos _)).mp hb).2 _ h)
      simp [weight_cons, Multiset.count_eq_zero.mpr hnot]
    rw [heq]
    have h : (1 : ℝ) ≤ sieve (l+1) N * (2*((l:ℝ)+1)) := by
      push_cast at hh
      exact (div_le_iff₀ (by positivity)).mp hh
    have hn : 0 ≤ sieve (l+1) N := sum_nonneg fun _ _ ↦ weight_nonneg _
    have hle : (2 : ℝ) * (l+1) * l ≤ 2 * ((k:ℝ)+1)^2 := by
      nlinarith [sq_nonneg ((k:ℝ)-l), mul_nonneg (sub_nonneg.mpr hk') hl'.le]
    rw [← mul_div_assoc, le_div_iff₀ hl', one_mul]
    calc
      (l : ℝ) ≤ (2*(l+1)*l) * sieve (l+1) N := by
        nlinarith [mul_le_mul_of_nonneg_right h hl'.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right hle hn

def completions (B : Finset (Multiset ℕ)) (k n : ℕ) :=
  B.sigma fun a ↦ (upperHalf a).sigma fun s ↦ tails (k-s) (n-a.sum-(k-s))

def completeShape (k : ℕ) (x : (_a : Multiset ℕ) × (_s : ℕ) × Multiset ℕ) : Multiset ℕ :=
  x.1 + ((k-x.2.1) ::ₘ x.2.2)

lemma completion_aux {k n r : ℕ} {a : Multiset ℕ} {s : ℕ} (hk : 0 < k)
    (hn : 2*k ≤ n) (hr : 16*r ≤ k) (ha : a.sum ≤ 4*r) (hs : s ∈ upperHalf a) :
    r < k-s ∧ s ≤ k ∧ k-s ≤ n-a.sum-(k-s) := by
  obtain ⟨h1,h2⟩ := mem_filter.mp hs
  have := mem_sums_le h1
  omega

lemma completion_short {r k : ℕ} {a d : Multiset ℕ} {s : ℕ} (hs : r < k-s)
    (ha : ∀ i ∈ a, i ≤ r) (hd : ∀ i ∈ d, k-s ≤ i) :
    shortParts r (a + ((k-s) ::ₘ d)) = a := by
  unfold shortParts
  rw [Multiset.filter_add, Multiset.filter_eq_self.mpr ha, Multiset.filter_cons_of_neg _ (by omega),
    Multiset.filter_eq_nil.mpr (fun i hi ↦ by have := hd i hi; omega), add_zero]

lemma completion_weight {r k : ℕ} {a d : Multiset ℕ} {s : ℕ} (hs : r < k-s)
    (ha : ∀ i ∈ a, i ≤ r) (hd : ∀ i ∈ d, k-s ≤ i) :
    weight (a + ((k-s) ::ₘ d)) = weight a * weight ((k-s) ::ₘ d) := by
  apply weight_disjoint
  intro i hi him
  have := ha i hi
  rcases Multiset.mem_cons.mp him with h | h
  · omega
  · have := hd i h
    omega

/-- Filtering recovers the short partition. The smallest remaining length
recovers the distinguished cycle and its complementary subset sum. -/
lemma completions_injective {r k n : ℕ} (B : Finset (Multiset ℕ)) (hk : 0 < k)
    (hn : 2*k ≤ n) (hr : 16*r ≤ k)
    (hB : ∀ a ∈ B, a.sum ≤ 4*r ∧ ∀ j ∈ a, j ≤ r) :
    Set.InjOn (completeShape k) (completions B k n : Set _) := by
  rintro ⟨a,s,d⟩ hx ⟨b,t,e⟩ hy he
  obtain ⟨ha,hx⟩ := mem_sigma.mp hx
  obtain ⟨hs,hd⟩ := mem_sigma.mp hx
  obtain ⟨hb,hy⟩ := mem_sigma.mp hy
  obtain ⟨ht,he'⟩ := mem_sigma.mp hy
  have hA := completion_aux hk hn hr (hB a ha).1 hs
  have hT := completion_aux hk hn hr (hB b hb).1 ht
  change a + ((k-s) ::ₘ d) = b + ((k-t) ::ₘ e) at he
  have hshort := congrArg (shortParts r) he
  rw [completion_short hA.1 (hB a ha).2 (tail_spec hd).2,
    completion_short hT.1 (hB b hb).2 (tail_spec he').2] at hshort
  subst b
  have hde := add_left_cancel he
  have hmin {i j : ℕ} {u v : Multiset ℕ} (h : i ::ₘ u = j ::ₘ v) (hv : ∀ x ∈ v, j ≤ x) : j ≤ i := by
    have hm : i ∈ j ::ₘ v := h ▸ Multiset.mem_cons_self _ _
    exact (Multiset.mem_cons.mp hm).elim (fun heq ↦ heq.ge) (hv i)
  have h1 := hmin hde (tail_spec he').2
  have h2 := hmin hde.symm (tail_spec hd).2
  have hsk : s ≤ k := hA.2.1
  have htk : t ≤ k := hT.2.1
  change k-t ≤ k-s at h1
  change k-s ≤ k-t at h2
  have hst : s = t := by omega
  subst t
  obtain rfl := (Multiset.cons_inj_right _).mp hde
  rfl

lemma completion_good {k n r : ℕ} {a : Multiset ℕ} {s : ℕ} {d : Multiset ℕ}
    (hk : 0 < k) (hn : 2*k ≤ n) (hr : 16*r ≤ k) (ha : a.sum ≤ 4*r)
    (hp : ∀ j ∈ a, 0 < j) (hs : s ∈ upperHalf a) (hd : d ∈ tails (k-s) (n-a.sum-(k-s))) :
    a + ((k-s) ::ₘ d) ∈ (shapes n).filter (fun b ↦ k ∈ sums b) := by
  obtain ⟨h1,h2,h3⟩ := completion_aux hk hn hr ha hs
  obtain ⟨hd1,hd2⟩ := tail_spec hd
  obtain ⟨t,ht,he⟩ := mem_sums.mp (mem_filter.mp hs).1
  refine mem_filter.mpr ⟨mem_shapes.mpr ⟨by rw [Multiset.sum_add, Multiset.sum_cons,hd1]; omega,?_⟩,?_⟩
  · intro j hj
    rcases Multiset.mem_add.mp hj with h | h
    · exact hp j h
    · rcases Multiset.mem_cons.mp h with h | h
      · omega
      · have := hd2 j h; omega
  · refine mem_sums.mpr ⟨t + {k-s},add_le_add ht ?_,by simp [he]; omega⟩
    change (k-s) ::ₘ 0 ≤ (k-s) ::ₘ d
    exact Multiset.cons_le_cons _ (Multiset.zero_le _)

end
end Green87Local

/- The averaged marked-cycle count gives the upper comparison directly. -/
namespace Green87Local
open Finset
noncomputable section

def longShapes (k n : ℕ) := (range (n+1)).biUnion (rough (k+1))

lemma long_budget (k n : ℕ) :
    ∑ d ∈ longShapes k n, weight d ≤ 1 + n / ((k+1 : ℕ) : ℝ) := by
  have hd : (SetLike.coe (range (n+1)) : Set ℕ).PairwiseDisjoint (rough (k+1)) := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro b hi hj
    exact hij ((mem_rough (Nat.succ_pos _)).mp hi |>.1.symm.trans
      ((mem_rough (Nat.succ_pos _)).mp hj).1)
  rw [longShapes, sum_biUnion hd]
  change ∑ i ∈ range (n+1), sieve (k+1) i ≤ _
  rw [sum_range_succ', sieve_zero, add_comm]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _i ∈ range n, 1 / ((k+1 : ℕ) : ℝ) := by
      refine sum_le_sum fun i _ ↦ ?_
      by_cases h : k+1 ≤ i+1
      · exact (sieve_bounds (Nat.succ_pos _) h).2
      · rw [sieve_below (Nat.succ_pos _) (by omega)]
        positivity
    _ = _ := by simp [div_eq_mul_inv]

lemma short_budget (k n : ℕ) :
    (∑ b ∈ boundedShapes n, (sums (shortParts k b)).card * weight b) ≤
      (Real.exp (harmonic k) * expectation k) * (1 + n / ((k+1 : ℕ) : ℝ)) := by
  let s := (boundedShapes n).image (shortParts k)
  let t := longShapes k n
  let f := fun b ↦ (shortParts k b, longParts k b)
  have hm (b) (hb : b ∈ boundedShapes n) : f b ∈ s ×ˢ t := by
    refine mem_product.mpr ⟨mem_image_of_mem _ hb, ?_⟩
    have hn := (mem_bounded.mp hb).1
    have hd : (longParts k b).sum ≤ n :=
      (sum_le_of_le (Multiset.filter_le _ _)).trans hn
    exact mem_biUnion.mpr ⟨_, mem_range.mpr (Nat.lt_succ_of_le hd),
      (mem_rough (Nat.succ_pos _)).mpr ⟨rfl,fun i hi ↦ by
        have := (Multiset.mem_filter.mp hi).2
        omega⟩⟩
  have hv : ∑ b ∈ s, weightedValues b ≤ Real.exp (harmonic k) * expectation k := by
    apply sum_raw_le
    intro a ha j hj
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    obtain ⟨hbj,hj'⟩ := Multiset.mem_filter.mp hj
    exact mem_Icc.mpr ⟨(mem_bounded.mp hb).2 j hbj,hj'⟩
  calc
    _ ≤ ∑ z ∈ s ×ˢ t, weightedValues z.1 * weight z.2 := by
      apply sum_injection _ _ f _ _ hm
      · intro a _ b _ h
        have h1 : shortParts k a = shortParts k b := congrArg Prod.fst h
        have h2 : longParts k a = longParts k b := congrArg Prod.snd h
        rw [← split_parts k a, h1,h2,split_parts]
      · intro b _
        dsimp [f,weightedValues]
        rw [split_weight k b, mul_assoc]
      · exact fun z _ ↦ mul_nonneg (weighted_nonneg _) (weight_nonneg _)
    _ = (∑ b ∈ s, weightedValues b) * ∑ d ∈ t, weight d := by
      rw [sum_product, sum_mul]
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
    _ ≤ _ := mul_le_mul hv (long_budget k n) (sum_nonneg fun _ _ ↦ weight_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (expectation_bounds k).1))

lemma upper_compare {k n : ℕ} (hk : 0 < k) (hn : 2*k ≤ n) :
    Green87.i n k ≤ (3 * Real.exp 1) * (expectation k / k) := by
  let l := n-k
  have hkl : k ≤ l := by dsimp [l]; omega
  have hn' : n = k+l := by dsimp [l]; omega
  have h0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (0 : ℝ) < l := by exact_mod_cast hk.trans_le hkl
  have he : 0 ≤ expectation k := zero_le_one.trans (expectation_bounds k).1
  have hh := (marked_average k l).trans (short_budget k (k+l))
  have budget : 1 + ((k+l : ℕ) : ℝ) / ((k+1 : ℕ) : ℝ) ≤ 3*(l:ℝ)/k := by
    have hkl' : (k:ℝ) ≤ l := by exact_mod_cast hkl
    push_cast
    field_simp
    nlinarith [mul_nonneg h0.le (sub_nonneg.mpr hkl')]
  have htop : (k : ℝ)*l*Green87.i n k ≤ (3*Real.exp 1) * expectation k * l := by
    rw [hn']
    apply hh.trans
    calc
      _ ≤ (Real.exp 1 * k * expectation k) * (3*(l:ℝ)/k) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (exp_harmonic_upper hk) he) budget
          (by positivity) (by positivity)
      _ = _ := by field_simp
  rw [mul_div_assoc', le_div_iff₀ h0]
  apply le_of_mul_le_mul_left (a := (l:ℝ)) _ h1
  linarith

end
end Green87Local

/- Sum the disjoint one-cycle completions, including the boundary case n = 2k. -/
namespace Green87Local
open Finset
noncomputable section

lemma truncated_count {k n r : ℕ} (hk : 0 < k) (hn : 2*k ≤ n) (hr : 16*r ≤ k) :
    truncated r ≤ 4 * ((k:ℝ)+1)^2 * Green87.i n k := by
  let B := truncShapes r
  let K : ℝ := 2*((k:ℝ)+1)^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB (a) (ha : a ∈ B) : a.sum ≤ 4*r ∧ ∀ j ∈ a, j ≤ r :=
    ⟨(mem_bounded.mp (mem_filter.mp ha).1).1,(mem_filter.mp ha).2⟩
  have hpos (a) (ha : a ∈ B) : ∀ j ∈ a, 0 < j := (mem_bounded.mp (mem_filter.mp ha).1).2
  have hone (a) (ha : a ∈ B) (s) (hs : s ∈ upperHalf a) :
      weight a ≤ K * ∑ d ∈ tails (k-s) (n-a.sum-(k-s)), weight (a + ((k-s) ::ₘ d)) := by
    have hh := completion_aux hk hn hr (hB a ha).1 hs
    have ht := tail_lower (k := k) (Nat.zero_lt_of_lt hh.1) (Nat.sub_le k s) hh.2.2
    have hmul := mul_le_mul_of_nonneg_left ht (weight_nonneg a)
    rw [mul_one] at hmul
    apply hmul.trans_eq
    change weight a * (K * _) = _
    rw [mul_left_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun d hd ↦ ?_
    exact (completion_weight hh.1 (hB a ha).2 (tail_spec hd).2).symm
  have hcount (a) (ha : a ∈ B) :
      weightedValues a ≤ 2*K * ∑ s ∈ upperHalf a,
        ∑ d ∈ tails (k-s) (n-a.sum-(k-s)), weight (a + ((k-s) ::ₘ d)) := by
    calc
      weightedValues a ≤ 2 * ∑ _s ∈ upperHalf a, weight a := by
        rw [sum_const, nsmul_eq_mul, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast half_card a) (weight_nonneg _)
      _ ≤ 2 * ∑ s ∈ upperHalf a, K *
          ∑ d ∈ tails (k-s) (n-a.sum-(k-s)), weight (a + ((k-s) ::ₘ d)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum (hone a ha)) (by norm_num)
      _ = _ := by rw [← mul_sum]; exact (mul_assoc 2 K _).symm
  have hsum : (∑ x ∈ completions B k n, weight (completeShape k x)) ≤ Green87.i n k := by
    rw [probability_formula]
    have hm : ∀ x ∈ completions B k n, completeShape k x ∈
        (shapes n).filter (fun b ↦ k ∈ sums b) := by
      rintro ⟨a,s,d⟩ hx
      obtain ⟨ha,hx⟩ := mem_sigma.mp hx
      obtain ⟨hs,hd⟩ := mem_sigma.mp hx
      exact completion_good hk hn hr (hB a ha).1 (hpos a ha) hs hd
    calc
      _ = ∑ b ∈ (completions B k n).image (completeShape k), weight b :=
        (sum_image (f := weight) (completions_injective B hk hn hr hB)).symm
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg _ (fun b _ _ ↦ weight_nonneg b)
        intro b hb
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
        exact hm x hx
  change ∑ a ∈ B, weightedValues a ≤ _
  apply (sum_le_sum hcount).trans
  rw [← mul_sum]
  calc
    _ = 2*K * ∑ x ∈ completions B k n, weight (completeShape k x) := by
      congr 1
      simp only [completions, sum_sigma, completeShape]
    _ ≤ 2*K * Green87.i n k := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [K]; ring

lemma lower_compare {k n : ℕ} (hk : 0 < k) (hn : 2*k ≤ n) :
    (1/4096 : ℝ) * (expectation k / k) ≤ Green87.i n k := by
  let r := k / 16
  have hrk : r ≤ k := Nat.div_le_self _ _
  have hr : 16*r ≤ k := by dsimp [r]; omega
  have h16 : k+1 ≤ 16*(r+1) := by dsimp [r]; omega
  have hka : (k:ℝ) + 1 ≤ 16*((r:ℝ)+1) := by exact_mod_cast h16
  have h0 : (0:ℝ) < k := by exact_mod_cast hk
  have hE : 0 ≤ expectation r := zero_le_one.trans (expectation_bounds _).1
  have hi : 0 ≤ Green87.i n k := by unfold Green87.i; positivity
  have hg := (div_le_div_iff₀ (by positivity) (by positivity)).mp (growth hrk)
  have hex := mul_le_mul_of_nonneg_right (exp_harmonic_lower r) hE
  have hl := (truncation r).trans (mul_le_mul_of_nonneg_left (truncated_count hk hn hr) (by norm_num))
  have h1 : expectation k ≤ 16 * expectation r := by
    have hg' := hg.trans (mul_le_mul_of_nonneg_left hka hE)
    apply le_of_mul_le_mul_right (a := ((r:ℝ)+1)) _ (by positivity)
    linarith
  have h2 : expectation r ≤ (128 * ((k:ℝ)+1)) * Green87.i n k := by
    have hh := hex.trans hl
    have hd : (k:ℝ)+1 ≤ 16*((r:ℝ)+1) := hka
    have he : (r:ℝ)+1 > 0 := by positivity
    apply le_of_mul_le_mul_left (a := ((r:ℝ)+1)) _ he
    apply hh.trans
    have hm := mul_le_mul_of_nonneg_left hd
      (show 0 ≤ (8:ℝ)*((k:ℝ)+1)*Green87.i n k by positivity)
    nlinarith
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have h3 : expectation k ≤ 4096 * (k:ℝ) * Green87.i n k := by
    have hh := h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))
    have hm := mul_le_mul_of_nonneg_right hk' hi
    linarith
  rw [← mul_div_assoc, div_le_iff₀ h0]
  linarith

end
end Green87Local

open Green87Local

theorem OMA.solution : OMA.R_Green87_green_87_variants_order_R2.H1 := by
  refine ⟨3 * Real.exp 1, 1 / 4096, by norm_num, ?_⟩
  intro k hk n hn
  change ‖Green87.i n k‖ ≤ (3 * Real.exp 1) * ‖expectation k / k‖ ∧
    (1 / 4096 : ℝ) * ‖expectation k / k‖ ≤ ‖Green87.i n k‖
  have hi : 0 ≤ Green87.i n k := by unfold Green87.i; positivity
  have he : 0 ≤ expectation k / k := div_nonneg
    (zero_le_one.trans (expectation_bounds k).1) (Nat.cast_nonneg k)
  rw [Real.norm_of_nonneg hi, Real.norm_of_nonneg he]
  exact ⟨upper_compare hk hn, lower_compare hk hn⟩
