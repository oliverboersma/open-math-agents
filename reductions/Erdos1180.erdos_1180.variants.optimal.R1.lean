import FormalConjectures.ErdosProblems.«1180»

/-! A reduction for the sufficiently-large-primes version of the reciprocal sum problem.
The eightfold bilinear covering lemma and multiset conversion are ported from Linmiao Xu,
linrock/math-proofs/erdos-1180 at ba96303b34a95ac458958c1eb0bbdee54733484a, Apache-2.0.
Copyright 2026 Linmiao Xu. Copyright 2026 The Formal Conjectures Authors.
The small-prime disproof in that project concerns a different quantifier. Here only
power-sized growth of a sumset is required, and it may still miss most residues. -/
-- Credit: @marcusbuffett
namespace OMA.R_Erdos1180_erdos_1180_variants_optimal_R1
open Erdos1180 Filter Topology Real Finset
open scoped BigOperators Pointwise Combinatorics.Additive

private def AdmissibleDenom (ε : ℝ) (p n : ℕ) : Prop :=
  1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p

theorem represents_zero (ε : ℝ) (p : ℕ) : Represents ε p 0 0 := by
  refine ⟨?_, ?_⟩
  · intro n hn
    simp at hn
  · simp

theorem represents_singleton {ε : ℝ} {p n : ℕ} (h : AdmissibleDenom ε p n) :
    Represents ε p (n : ZMod p)⁻¹ {n} := by
  refine ⟨?_, by simp⟩
  intro m hm
  rw [Multiset.mem_singleton] at hm
  subst hm
  exact h

theorem represents_add {ε : ℝ} {p : ℕ} {a b : ZMod p} {s₁ s₂ : Multiset ℕ}
    (h₁ : Represents ε p a s₁) (h₂ : Represents ε p b s₂) :
    Represents ε p (a + b) (s₁ + s₂) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rw [Multiset.mem_add] at hn
    rcases hn with hn₁ | hn₂
    · exact h₁.1 n hn₁
    · exact h₂.1 n hn₂
  · rw [Multiset.map_add, Multiset.sum_add, h₁.2, h₂.2]

theorem admissibleDenom_mono_eps {ε₁ ε₂ : ℝ} {p n : ℕ} (hε : ε₁ ≤ ε₂) (hp : 1 ≤ p)
    (h : AdmissibleDenom ε₁ p n) : AdmissibleDenom ε₂ p n := by
  refine ⟨h.1, ?_, h.2.2⟩
  exact h.2.1.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) hε)

private noncomputable def admissibleFinset (ε : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊(p : ℝ) ^ ε⌋₊).filter (fun n ↦ n.Coprime p)

theorem mem_admissibleFinset_iff {ε : ℝ} {p n : ℕ} :
    n ∈ admissibleFinset ε p ↔ AdmissibleDenom ε p n := by
  unfold admissibleFinset AdmissibleDenom
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨h1, ?_, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨⟨h1, ?_⟩, h3⟩⟩
  · exact (Nat.cast_le.mpr h2).trans (Nat.floor_le (by positivity))
  · exact Nat.le_floor h2

private noncomputable def invSet (ε : ℝ) (p : ℕ) : Finset (ZMod p) :=
  (admissibleFinset ε p).image (fun n : ℕ ↦ (n : ZMod p)⁻¹)

theorem mem_invSet_iff_exists_admissibleDenom {ε : ℝ} {p : ℕ} {a : ZMod p} :
    a ∈ invSet ε p ↔ ∃ n : ℕ, AdmissibleDenom ε p n ∧ (n : ZMod p)⁻¹ = a := by
  unfold invSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, mem_admissibleFinset_iff.mp hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, mem_admissibleFinset_iff.mpr hn, rfl⟩

theorem exists_represents_card_eq_of_mem_nsmul_invSet {ε : ℝ} {p : ℕ} :
    ∀ (k : ℕ) {a : ZMod p}, a ∈ k • invSet ε p →
      ∃ s : Multiset ℕ, s.card = k ∧ Represents ε p a s
  | 0, a, ha => by
      rw [zero_nsmul, Finset.mem_zero] at ha
      subst ha
      exact ⟨0, rfl, represents_zero ε p⟩
  | k + 1, a, ha => by
      rw [succ_nsmul, Finset.mem_add] at ha
      rcases ha with ⟨b, hb, c, hc, rfl⟩
      obtain ⟨s, hscard, hsrep⟩ := exists_represents_card_eq_of_mem_nsmul_invSet k hb
      obtain ⟨n, hnadm, rfl⟩ := mem_invSet_iff_exists_admissibleDenom.mp hc
      refine ⟨s + {n}, ?_, represents_add hsrep (represents_singleton hnadm)⟩
      simp [hscard]

theorem admissibleDenom_mul {δ₁ δ₂ : ℝ} {p m n : ℕ} (hp : 1 ≤ p)
    (hm : AdmissibleDenom δ₁ p m) (hn : AdmissibleDenom δ₂ p n) :
    AdmissibleDenom (δ₁ + δ₂) p (m * n) := by
  refine ⟨Nat.mul_pos hm.1 hn.1, ?_, hm.2.2.mul_left hn.2.2⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Nat.cast_mul, Real.rpow_add hp0]
  exact mul_le_mul hm.2.1 hn.2.1 (Nat.cast_nonneg n) (Real.rpow_nonneg hp0.le δ₁)

theorem invSet_mul_subset_invSet_add {δ₁ δ₂ : ℝ} {p : ℕ} (hp : p.Prime) :
    invSet δ₁ p * invSet δ₂ p ⊆ invSet (δ₁ + δ₂) p := by
  have : Fact p.Prime := ⟨hp⟩
  intro z hz
  rcases Finset.mem_mul.mp hz with ⟨a, ha, b, hb, rfl⟩
  obtain ⟨m, hm, rfl⟩ := mem_invSet_iff_exists_admissibleDenom.mp ha
  obtain ⟨n, hn, rfl⟩ := mem_invSet_iff_exists_admissibleDenom.mp hb
  rw [mem_invSet_iff_exists_admissibleDenom]
  refine ⟨m * n, admissibleDenom_mul hp.one_le hm hn, ?_⟩
  rw [Nat.cast_mul, mul_inv_rev, mul_comm]

theorem invSet_mono_eps {δ ε : ℝ} {p : ℕ} (hp : 1 ≤ p) (hδε : δ ≤ ε) :
    invSet δ p ⊆ invSet ε p := by
  intro z hz
  obtain ⟨n, hn, rfl⟩ := mem_invSet_iff_exists_admissibleDenom.mp hz
  exact mem_invSet_iff_exists_admissibleDenom.mpr ⟨n, admissibleDenom_mono_eps hδε hp hn, rfl⟩

theorem add_subset_add {p : ℕ} {A₁ A₂ B₁ B₂ : Finset (ZMod p)}
    (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) : A₁ + A₂ ⊆ B₁ + B₂ := by
  intro z hz
  rcases Finset.mem_add.mp hz with ⟨a, ha, b, hb, rfl⟩
  exact Finset.add_mem_add (h₁ ha) (h₂ hb)

theorem mul_subset_mul {p : ℕ} {A₁ A₂ B₁ B₂ : Finset (ZMod p)}
    (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) : A₁ * A₂ ⊆ B₁ * B₂ := by
  intro z hz
  rcases Finset.mem_mul.mp hz with ⟨a, ha, b, hb, rfl⟩
  exact Finset.mul_mem_mul (h₁ ha) (h₂ hb)

theorem nsmul_subset_nsmul {p : ℕ} {A B : Finset (ZMod p)} (h : A ⊆ B) :
    ∀ k : ℕ, k • A ⊆ k • B
  | 0 => by simp
  | k + 1 => by
      rw [succ_nsmul, succ_nsmul]
      exact add_subset_add (nsmul_subset_nsmul h k) h

theorem singleton_mul_nsmul_subset {p : ℕ} {x : ZMod p} {S T : Finset (ZMod p)} (hx : x ∈ S) :
    ∀ k : ℕ, ({x} : Finset (ZMod p)) * (k • T) ⊆ k • (S * T)
  | 0 => by
      intro z hz
      rcases Finset.mem_mul.mp hz with ⟨a, _, b, hb, rfl⟩
      rw [zero_nsmul, Finset.mem_zero] at hb
      subst hb; simp
  | k + 1 => by
      intro z hz
      rcases Finset.mem_mul.mp hz with ⟨a, ha, b, hb, rfl⟩
      rw [Finset.mem_singleton] at ha; subst ha
      rw [succ_nsmul, Finset.mem_add] at hb
      rcases hb with ⟨u, hu, v, hv, rfl⟩
      rw [mul_add, succ_nsmul]
      exact Finset.add_mem_add
        (singleton_mul_nsmul_subset hx k (Finset.mul_mem_mul (Finset.mem_singleton_self a) hu))
        (Finset.mul_mem_mul hx hv)

theorem nsmul_mul_nsmul_subset {p : ℕ} (S T : Finset (ZMod p)) :
    ∀ k₁ k₂ : ℕ, (k₁ • S) * (k₂ • T) ⊆ (k₁ * k₂) • (S * T)
  | 0, _ => by
      intro z hz
      rcases Finset.mem_mul.mp hz with ⟨a, ha, _, _, rfl⟩
      rw [zero_nsmul, Finset.mem_zero] at ha
      subst ha; simp
  | k₁ + 1, k₂ => by
      intro z hz
      rcases Finset.mem_mul.mp hz with ⟨a, ha, b, hb, rfl⟩
      rw [succ_nsmul, Finset.mem_add] at ha
      rcases ha with ⟨u, hu, x, hx, rfl⟩
      rw [add_mul, add_mul, one_mul, add_nsmul]
      exact Finset.add_mem_add
        (nsmul_mul_nsmul_subset S T k₁ k₂ (Finset.mul_mem_mul hu hb))
        (singleton_mul_nsmul_subset hx k₂ (Finset.mul_mem_mul (Finset.mem_singleton_self x) hb))

section AdditiveEnergyCover
variable {p : ℕ}

theorem add_self_eq_univ_of_lt_two_mul_card [NeZero p] (hp : p.Prime)
    {S : Finset (ZMod p)} (hS : p < 2 * S.card) : S + S = univ := by
  have hne : S.Nonempty := card_pos.mp (by omega)
  have hcd := ZMod.cauchy_davenport hp hne hne
  apply eq_univ_of_card
  apply le_antisymm (card_le_univ _)
  rw [ZMod.card]
  exact (by omega : p ≤ min p (S.card + S.card - 1)).trans hcd

theorem zero_mem_add_self_of_lt_two_mul_card [NeZero p] (hp : p.Prime)
    {S : Finset (ZMod p)} (hS : p < 2 * S.card) : (0 : ZMod p) ∈ S + S := by
  rw [add_self_eq_univ_of_lt_two_mul_card hp hS]
  exact mem_univ 0

theorem card_sq_mul_card_sq_le_addEnergy (u : (ZMod p)ˣ) (U V : Finset (ZMod p)) :
    U.card ^ 2 * V.card ^ 2 ≤ (U + u • V).card * E[U, u • V] := by
  simpa [card_smul_finset] using le_card_add_mul_addEnergy U (u • V)

theorem addEnergy_unit_smul_eq (u : (ZMod p)ˣ) (U V : Finset (ZMod p)) :
    E[U, u • V] =
      #{w ∈ (U ×ˢ U) ×ˢ (V ×ˢ V) |
        w.1.1 + (u : ZMod p) * w.2.1 = w.1.2 + (u : ZMod p) * w.2.2} := by
  classical
  unfold Finset.addEnergy
  let e : (ZMod p × ZMod p) × (ZMod p × ZMod p) ≃ (ZMod p × ZMod p) × (ZMod p × ZMod p) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (MulAction.toPerm u) (MulAction.toPerm u))
  refine (card_equiv e ?_).symm
  rintro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  simp only [mem_filter, mem_product, e, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map,
    MulAction.toPerm_apply, smul_mem_smul_finset_iff]
  rfl

theorem addEnergy_neg_unit_smul (u : (ZMod p)ˣ) (U V : Finset (ZMod p)) :
    E[U, (-u) • V] = E[U, u • V] := by
  classical
  rw [addEnergy_unit_smul_eq, addEnergy_unit_smul_eq]
  refine card_equiv (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)) ?_
  rintro ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
  simp only [mem_filter, mem_product, Equiv.prodCongr_apply, Equiv.refl_apply,
    Equiv.prodComm_apply, Prod.map, Prod.fst_swap, Prod.snd_swap, Units.val_neg, neg_mul]
  refine and_congr (and_congr_right' and_comm) ?_
  constructor <;> intro h <;> linear_combination h

theorem unit_eq_div_of_linear_eq [Fact p.Prime] {u : (ZMod p)ˣ} {x₁ x₂ y₁ y₂ : ZMod p}
    (hy : y₁ ≠ y₂) (h : x₁ + (u : ZMod p) * y₁ = x₂ + (u : ZMod p) * y₂) :
    (u : ZMod p) = (x₂ - x₁) / (y₁ - y₂) :=
  (eq_div_iff (sub_ne_zero.mpr hy)).mpr (by linear_combination h)

theorem sum_units_addEnergy_le [NeZero p] (hp : p.Prime) (U V : Finset (ZMod p)) :
    (∑ u : (ZMod p)ˣ, E[U, u • V]) ≤
      (p - 1) * (U.card * V.card) + U.card ^ 2 * V.card ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let Q := (U ×ˢ U) ×ˢ (V ×ˢ V)
  have hswap : (∑ u : (ZMod p)ˣ, E[U, u • V]) =
      ∑ w ∈ Q, #{u : (ZMod p)ˣ | w.1.1 + (u : ZMod p) * w.2.1 = w.1.2 + (u : ZMod p) * w.2.2} := by
    simp_rw [addEnergy_unit_smul_eq, card_filter]
    exact sum_comm
  rw [hswap, ← sum_filter_add_sum_filter_not Q (fun w ↦ w ∈ U.diag ×ˢ V.diag)]
  have hsub : Q.filter (fun w ↦ w ∈ U.diag ×ˢ V.diag) ⊆ U.diag ×ˢ V.diag :=
    fun _ hw ↦ (mem_filter.mp hw).2
  have hdiag : (∑ w ∈ Q.filter (fun w ↦ w ∈ U.diag ×ˢ V.diag),
      #{u : (ZMod p)ˣ | w.1.1 + (u : ZMod p) * w.2.1 = w.1.2 + (u : ZMod p) * w.2.2}) ≤
      (p - 1) * (U.card * V.card) := by
    calc
      _ ≤ ∑ _w ∈ Q.filter (fun w ↦ w ∈ U.diag ×ˢ V.diag), Fintype.card (ZMod p)ˣ :=
        sum_le_sum fun w _ ↦ card_le_univ _
      _ ≤ (U.diag ×ˢ V.diag).card * Fintype.card (ZMod p)ˣ := by
        rw [sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (card_le_card hsub)
      _ = (p - 1) * (U.card * V.card) := by
        simp [ZMod.card_units_eq_totient, Nat.totient_prime hp, mul_comm]
  have hoff : (∑ w ∈ Q.filter (fun w ↦ w ∉ U.diag ×ˢ V.diag),
      #{u : (ZMod p)ˣ | w.1.1 + (u : ZMod p) * w.2.1 = w.1.2 + (u : ZMod p) * w.2.2}) ≤
      U.card ^ 2 * V.card ^ 2 := by
    calc
      _ ≤ ∑ _w ∈ Q.filter (fun w ↦ w ∉ U.diag ×ˢ V.diag), 1 := by
        refine sum_le_sum fun w hw ↦ card_le_one.mpr fun u₁ hu₁ u₂ hu₂ ↦ ?_
        rcases mem_filter.mp hw with ⟨hwQ, hnot⟩
        rcases mem_product.mp hwQ with ⟨hxU, hyV⟩
        have eq₁ : w.1.1 + (u₁ : ZMod p) * w.2.1 = w.1.2 + (u₁ : ZMod p) * w.2.2 := (mem_filter.mp hu₁).2
        have eq₂ : w.1.1 + (u₂ : ZMod p) * w.2.1 = w.1.2 + (u₂ : ZMod p) * w.2.2 := (mem_filter.mp hu₂).2
        have hy : w.2.1 ≠ w.2.2 := by
          intro hy
          apply hnot
          rw [mem_product, mem_diag, mem_diag]
          refine ⟨⟨(mem_product.mp hxU).1, by linear_combination eq₁ - (u₁ : ZMod p) * hy⟩,
            ⟨(mem_product.mp hyV).1, hy⟩⟩
        exact Units.ext ((unit_eq_div_of_linear_eq hy eq₁).trans (unit_eq_div_of_linear_eq hy eq₂).symm)
      _ ≤ Q.card := by simp [card_filter_le]
      _ = U.card ^ 2 * V.card ^ 2 := by simp [Q, sq]
  exact add_le_add hdiag hoff

theorem exists_unit_smul_both_gt_half [NeZero p] (hp : p.Prime) (hp2 : 2 < p)
    (U V : Finset (ZMod p)) (hprod : p < U.card * V.card) :
    ∃ u : (ZMod p)ˣ, p < 2 * (U + u • V).card ∧ p < 2 * (U + (-u) • V).card := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcard_u : (univ : Finset (ZMod p)ˣ).card = p - 1 := by
    rw [card_univ, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hne : (univ : Finset (ZMod p)ˣ).Nonempty := card_pos.mp (by omega)
  have hsum : (∑ u : (ZMod p)ˣ, (p - 1) * E[U, u • V]) ≤
      ∑ _u : (ZMod p)ˣ, ((p - 1) * (U.card * V.card) + U.card ^ 2 * V.card ^ 2) := by
    rw [← mul_sum, sum_const, hcard_u, smul_eq_mul]
    exact Nat.mul_le_mul_left (p - 1) (sum_units_addEnergy_le hp U V)
  obtain ⟨u, _, hu⟩ := exists_le_of_sum_le hne hsum
  have hhalf : ∀ w : (ZMod p)ˣ,
      (p - 1) * E[U, w • V] ≤ (p - 1) * (U.card * V.card) + U.card ^ 2 * V.card ^ 2 →
        p < 2 * (U + w • V).card := by
    intro w hw
    by_contra hle
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    have hle1 : 2 * (U + w • V).card ≤ p - 1 := by omega
    have hcs := card_sq_mul_card_sq_le_addEnergy w U V
    have hmul : 2 * (U.card ^ 2 * V.card ^ 2) ≤ (p - 1) * E[U, w • V] := by
      calc
        2 * (U.card ^ 2 * V.card ^ 2) ≤ 2 * ((U + w • V).card * E[U, w • V]) :=
          Nat.mul_le_mul_left 2 hcs
        _ = (2 * (U + w • V).card) * E[U, w • V] := by ring
        _ ≤ (p - 1) * E[U, w • V] := Nat.mul_le_mul_right _ hle1
    have hsq : (U.card * V.card) ^ 2 = U.card ^ 2 * V.card ^ 2 := by ring
    nlinarith
  refine ⟨u, hhalf u hu, hhalf (-u) ?_⟩
  rwa [addEnergy_neg_unit_smul]

theorem unit_smul_subset_two_nsmul_mul_left (w : (ZMod p)ˣ) (U V : Finset (ZMod p))
    {y₁ y₂ : ZMod p} (hy₁ : y₁ ∈ V) (hy₂ : y₂ ∈ V) (hw : (w : ZMod p) = y₁ + y₂) :
    w • U ⊆ (2 : ℕ) • (U * V) := by
  intro z hz
  rcases mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  change (w : ZMod p) * x ∈ (2 : ℕ) • (U * V)
  rw [hw, add_mul, mul_comm y₁ x, mul_comm y₂ x, two_nsmul]
  exact add_mem_add (mul_mem_mul hx hy₁) (mul_mem_mul hx hy₂)

theorem unit_smul_subset_two_nsmul_mul_right (w : (ZMod p)ˣ) (U V : Finset (ZMod p))
    {x₁ x₂ : ZMod p} (hx₁ : x₁ ∈ U) (hx₂ : x₂ ∈ U) (hw : (w : ZMod p) = x₁ + x₂) :
    w • V ⊆ (2 : ℕ) • (U * V) := by
  intro z hz
  rcases mem_smul_finset.mp hz with ⟨y, hy, rfl⟩
  change (w : ZMod p) * y ∈ (2 : ℕ) • (U * V)
  rw [hw, add_mul, two_nsmul]
  exact add_mem_add (mul_mem_mul hx₁ hy) (mul_mem_mul hx₂ hy)

theorem val_mul_neg_eq_add_of_sum_eq_zero (w u : (ZMod p)ˣ) {x₁ x₂ y₁ y₂ : ZMod p}
    (hw : (w : ZMod p) = y₁ + y₂) (hsum0 : (x₁ + u • y₁) + (x₂ + u • y₂) = 0) :
    ((w * -u : (ZMod p)ˣ) : ZMod p) = x₁ + x₂ := by
  simp only [Units.val_mul, Units.val_neg, hw]
  simp only [Units.smul_def, smul_eq_mul] at hsum0
  linear_combination -hsum0

theorem eight_nsmul_mul_eq_univ [NeZero p] (hp : p.Prime) (hp2 : 2 < p)
    (U V : Finset (ZMod p)) (hprod : p < U.card * V.card)
    (hanti : ∀ y₁ ∈ V, ∀ y₂ ∈ V, y₁ + y₂ ≠ 0) :
    (8 : ℕ) • (U * V) = univ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu_pos, hu_neg⟩ := exists_unit_smul_both_gt_half hp hp2 U V hprod
  have h0 := zero_mem_add_self_of_lt_two_mul_card hp hu_pos
  rcases mem_add.mp h0 with ⟨a₁, ha₁, a₂, ha₂, hsum0⟩
  rcases mem_add.mp ha₁ with ⟨x₁, hx₁, z₁, hz₁, rfl⟩
  rcases mem_add.mp ha₂ with ⟨x₂, hx₂, z₂, hz₂, rfl⟩
  rcases mem_smul_finset.mp hz₁ with ⟨y₁, hy₁, rfl⟩
  rcases mem_smul_finset.mp hz₂ with ⟨y₂, hy₂, rfl⟩
  let w : (ZMod p)ˣ := Units.mk0 (y₁ + y₂) (hanti y₁ hy₁ y₂ hy₂)
  have hsub4 : w • (U + (-u) • V) ⊆ (4 : ℕ) • (U * V) := by
    rw [smul_add, ← mul_smul,
      show (4 : ℕ) • (U * V) = (2 : ℕ) • (U * V) + (2 : ℕ) • (U * V) by rw [← add_nsmul]]
    exact add_subset_add
      (unit_smul_subset_two_nsmul_mul_left w U V hy₁ hy₂ rfl)
      (unit_smul_subset_two_nsmul_mul_right (w * -u) U V hx₁ hx₂
        (val_mul_neg_eq_add_of_sum_eq_zero w u rfl hsum0))
  have hcard4 : p < 2 * ((4 : ℕ) • (U * V)).card := by
    have hle := card_le_card hsub4
    rw [card_smul_finset] at hle
    exact lt_of_lt_of_le hu_neg (Nat.mul_le_mul_left 2 hle)
  rw [show (8 : ℕ) • (U * V) = (4 : ℕ) • (U * V) + (4 : ℕ) • (U * V) by rw [← add_nsmul]]
  exact add_self_eq_univ_of_lt_two_mul_card hp hcard4

end AdditiveEnergyCover

/-- Short reciprocal denominators supply a set disjoint from its negative. -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime →
    let I := ((Finset.Icc 1 ⌊(p : ℝ) ^ (ε / 2)⌋₊).filter (fun n => n.Coprime p)).image
        (fun n : ℕ => (n : ZMod p)⁻¹)
    ∃ V ⊆ I, (p : ℝ) ^ (ε / 4) < (V.card : ℝ) ∧
      ∀ x ∈ V, ∀ y ∈ V, x + y ≠ 0

/-- Growth of an iterated sumset of small reciprocals to exponent 1-ε/4. -/
def H2 : Prop := ∀ δ : ℝ, 0 < δ → ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
    ∃ k : ℕ, (k : ℝ) ≤ ε⁻¹ ^ (1 + δ) ∧ ∃ P : ℕ, ∀ p : ℕ, P ≤ p → p.Prime →
      let I := ((Finset.Icc 1 ⌊(p : ℝ) ^ (ε / 2)⌋₊).filter (fun n => n.Coprime p)).image
        (fun n : ℕ => (n : ZMod p)⁻¹)
      (p : ℝ) ^ (1 - ε / 4) ≤ ((k • I).card : ℝ)

theorem main : H1 → H2 → type_of% @Erdos1180.erdos_1180.variants.optimal := by
  intro short growth δ hδ
  have hhalf : 0 < δ / 2 := by linarith
  have power : Tendsto (fun ε : ℝ => ε⁻¹ ^ (δ / 2)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_atTop hhalf).comp tendsto_inv_nhdsGT_zero
  filter_upwards [growth (δ / 2) hhalf, self_mem_nhdsWithin,
    (eventually_le_nhds (show (0:ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
    power.eventually_ge_atTop 8] with ε hg he0 he1 he8
  have he : 0 < ε := he0
  obtain ⟨P₁, hv⟩ := short ε he he1
  obtain ⟨k, hk, P₂, hu⟩ := hg
  refine ⟨max 3 (max P₁ P₂), ?_⟩
  intro p hP hp a
  have hp2 : 2 < p := by omega
  letI : NeZero p := ⟨hp.ne_zero⟩
  let I := invSet (ε / 2) p
  let U := k • I
  obtain ⟨V, hV, hcardV, hanti⟩ := hv p (by omega) hp
  have hcardU : (p : ℝ) ^ (1 - ε / 4) ≤ (U.card : ℝ) := hu p (by omega) hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hprod : p < U.card * V.card := by
    have h : (p : ℝ) < (U.card : ℝ) * V.card := calc
      (p : ℝ) = (p : ℝ) ^ (1 - ε / 4) * (p : ℝ) ^ (ε / 4) := by
        rw [← Real.rpow_add hp0]; simp
      _ < _ := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hcardU hcardV
        (Real.rpow_nonneg hp0.le _) (lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) hcardU)
    exact_mod_cast h
  have hcover := eight_nsmul_mul_eq_univ hp hp2 U V hprod hanti
  have hV' : V ⊆ (1 : ℕ) • I := by simpa [I, invSet, admissibleFinset] using hV
  have hUV : U * V ⊆ k • invSet ε p := by
    calc U * V ⊆ (k • I) * ((1 : ℕ) • I) := mul_subset_mul (fun _ h => h) hV'
         _ ⊆ (k * 1) • (I * I) := nsmul_mul_nsmul_subset I I k 1
         _ ⊆ k • invSet ε p := by
           have hII : I * I ⊆ invSet ε p := by
             simpa [I, add_halves] using (invSet_mul_subset_invSet_add
               (δ₁ := ε / 2) (δ₂ := ε / 2) hp)
           simpa using nsmul_subset_nsmul hII k
  have ha : a ∈ (8 * k) • invSet ε p := by
    rw [mul_nsmul']
    exact nsmul_subset_nsmul hUV 8 (hcover.symm ▸ Finset.mem_univ a)
  obtain ⟨s, hs, hrep⟩ := exists_represents_card_eq_of_mem_nsmul_invSet (8*k) ha
  refine ⟨s, ?_, hrep⟩
  rw [hs, Nat.cast_mul, Nat.cast_ofNat]
  calc (8 : ℝ) * k ≤ (ε⁻¹ ^ (δ / 2)) * ε⁻¹ ^ (1 + δ / 2) :=
         mul_le_mul he8 hk (Nat.cast_nonneg k) (by positivity)
       _ = _ := by
         rw [← Real.rpow_add (inv_pos.mpr he)]
         congr 1
         ring

end OMA.R_Erdos1180_erdos_1180_variants_optimal_R1
