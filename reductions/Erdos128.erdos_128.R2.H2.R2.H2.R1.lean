import OMAReductions.R_Erdos128_erdos_128_R2_H2_R2

/-!
# Reduction Erdos128.erdos_128.R2.H2.R2.H2.R1 of Erdos128.erdos_128.R2.H2.R2.H2

Proves directly inside `main` (zero `sorry`):
1. Exact Fractional-to-Integral Sparse-Half Rounding Lemma (Norin–Yepremyan):
   for any finite graph `G` on `V` (`n = |V| ≥ 1`), any fractional half `f : V → ℝ`
   with `0 ≤ f x ≤ 1`, `∑ x, f x = n / 2`, and `25 * ∑ x, ∑ y, [G.Adj x y] * f x * f y ≤ n^2`
   rounds in at most `n` concave pairwise shifts to an integral subset `V' : Set V`
   with `2 * V'.ncard + 1 ≥ n` and `50 * (G.induce V').edgeSet.ncard ≤ n^2`.
2. Homomorphism Lift Lemma: lifts any fractional sparse half on weighted `(Υᵢ⁰⁰, w)`
   (`w z = |φ⁻¹(z)| / n`) to `(G, 1)` without losing edge density.
3. Exact Andrásfai boundary eliminations via `R2.not_hom_andrasfai`:
   - `ψ₁ : Υᵢ⁰⁰ \ {a, v} → Γᵢ` and `ψ₂ : Υᵢ⁰⁰ \ {u, b} → Γᵢ`, forcing `w(a)+w(v) > 0` and `w(u)+w(b) > 0`.
   - `ψ₃ : Υᵢ⁰⁰ \ {v, x} → Γᵢ₊₁` and `ψ₄ : Υᵢ⁰⁰ \ {b, y} → Γᵢ₊₁`, forcing `w(v)+w(x) > 0` and `w(b)+w(y) > 0`.
   - Independent-set ceiling via `R2.five_mul_indep_lt_two_mul_card`: `w(E₀) < 2/5`, `w(E₁) < 2/5`.

Reduces `Erdos128.erdos_128.R2.H2.R2.H2` cleanly to pure continuous quadratic fractional sparse halves:
- `H1`: Base 13-vertex Vega graph `Υ₂⁰⁰` (`i = 2`, which contains the Grötzsch graph).
- `H2`: Higher Vega graphs `Υᵢ⁰⁰` (`i ≥ 3`).
-/

namespace OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1

def H1 : Prop :=
  ∀ w : Fin 5 ⊕ Fin 8 → ℝ,
    (∀ z, 0 ≤ w z) →
    (∑ z, w z) = 1 →
    0 < w (Sum.inr 0) + w (Sum.inr 1) →
    0 < w (Sum.inr 3) + w (Sum.inr 4) →
    0 < w (Sum.inr 1) + w (Sum.inr 6) →
    0 < w (Sum.inr 4) + w (Sum.inr 7) →
    w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 4) + w (Sum.inr 7) < 2 / 5 →
    w (Sum.inr 1) + w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 6) < 2 / 5 →
    ∃ s : Fin 5 ⊕ Fin 8 → ℝ,
      (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧
      (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x : Fin 5 ⊕ Fin 8, ∑ y : Fin 5 ⊕ Fin 8,
        match x, y with
        | Sum.inl p, Sum.inl q =>
            if 2 ≤ (q.val + 5 - p.val) % 5 ∧ (q.val + 5 - p.val) % 5 ≤ 3 then s x * s y else 0
        | Sum.inl p, Sum.inr t =>
            if ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
               ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
               ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val) then s x * s y else 0
        | Sum.inr t, Sum.inl p =>
            if ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
               ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
               ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val) then s x * s y else 0
        | Sum.inr t₁, Sum.inr t₂ =>
            if (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
               (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
               (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
               (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
               (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)) then s x * s y else 0) ≤ 1

def H2 : Prop :=
  ∀ (i : ℕ), 3 ≤ i → ∀ w : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
    (∀ z, 0 ≤ w z) →
    (∑ z, w z) = 1 →
    0 < w (Sum.inr 0) + w (Sum.inr 1) →
    0 < w (Sum.inr 3) + w (Sum.inr 4) →
    0 < w (Sum.inr 1) + w (Sum.inr 6) →
    0 < w (Sum.inr 4) + w (Sum.inr 7) →
    w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 4) + w (Sum.inr 7) < 2 / 5 →
    w (Sum.inr 1) + w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 6) < 2 / 5 →
    ∃ s : Fin (3 * i - 1) ⊕ Fin 8 → ℝ,
      (∀ z, 0 ≤ s z ∧ s z ≤ w z) ∧
      (∑ z, s z) = 1 / 2 ∧
      25 * (∑ x : Fin (3 * i - 1) ⊕ Fin 8, ∑ y : Fin (3 * i - 1) ⊕ Fin 8,
        match x, y with
        | Sum.inl p, Sum.inl q =>
            if i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
               (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1 then s x * s y else 0
        | Sum.inl p, Sum.inr t =>
            if ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
               ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
               ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val) then s x * s y else 0
        | Sum.inr t, Sum.inl p =>
            if ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
               ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
               ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val) then s x * s y else 0
        | Sum.inr t₁, Sum.inr t₂ =>
            if (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
               (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
               (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
               (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
               (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)) then s x * s y else 0) ≤ 1

/- ### Part 1: Fractional-to-Integral Sparse-Half Rounding Lemma -/

lemma quad_shift_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → ℝ) (u v : V) (huv : u ≠ v) (t : ℝ) (ht : 0 ≤ t)
    (hdeg : (∑ y : V, if G.Adj u y then f y else 0) ≤ (∑ y : V, if G.Adj v y then f y else 0)) :
    (∑ x : V, ∑ y : V, if G.Adj x y then
        (if x = u then f u + t else if x = v then f v - t else f x) *
        (if y = u then f u + t else if y = v then f v - t else f y) else 0) ≤
      ∑ x : V, ∑ y : V, if G.Adj x y then f x * f y else 0 := by
  let δ : V → ℝ := fun x => if x = u then t else if x = v then -t else 0
  have hf' : ∀ x, (if x = u then f u + t else if x = v then f v - t else f x) = f x + δ x := by
    intro x
    by_cases h1 : x = u
    · subst h1; simp only [δ, ite_true]
    · by_cases h2 : x = v
      · subst h2; simp only [δ, if_neg h1, ite_true]; ring
      · simp only [δ, if_neg h1, if_neg h2, add_zero]
  simp_rw [hf']
  have hexp : ∀ x y : V,
      (if G.Adj x y then (f x + δ x) * (f y + δ y) else 0) =
      (if G.Adj x y then f x * f y else 0) +
      (if G.Adj x y then δ x * f y else 0) +
      (if G.Adj x y then f x * δ y else 0) +
      (if G.Adj x y then δ x * δ y else 0) := by
    intro x y; split_ifs <;> ring
  simp_rw [hexp, Finset.sum_add_distrib]
  have hterm1 : (∑ x : V, ∑ y : V, if G.Adj x y then δ x * f y else 0) =
      t * ((∑ y : V, if G.Adj u y then f y else 0) - (∑ y : V, if G.Adj v y then f y else 0)) := by
    have h1 : ∀ x : V, (∑ y : V, if G.Adj x y then δ x * f y else 0) =
        δ x * (∑ y : V, if G.Adj x y then f y else 0) := by
      intro x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => ?_; split_ifs <;> ring
    simp_rw [h1]
    have hsplit : ∑ x : V, δ x * (∑ y : V, if G.Adj x y then f y else 0) =
        ∑ x ∈ ({u, v} : Finset V), δ x * (∑ y : V, if G.Adj x y then f y else 0) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp only [δ, if_neg hx.1, if_neg hx.2, zero_mul]
    rw [hsplit, Finset.sum_pair huv]
    simp only [δ, ite_true, if_neg huv.symm]
    ring
  have hterm2 : (∑ x : V, ∑ y : V, if G.Adj x y then f x * δ y else 0) =
      t * ((∑ y : V, if G.Adj u y then f y else 0) - (∑ y : V, if G.Adj v y then f y else 0)) := by
    rw [Finset.sum_comm]
    have hcomm : ∀ y x : V, (if G.Adj x y then f x * δ y else 0) =
        (if G.Adj y x then δ y * f x else 0) := by
      intro y x
      by_cases h : G.Adj x y
      · rw [if_pos h, if_pos h.symm, mul_comm]
      · rw [if_neg h, if_neg (fun h' => h h'.symm)]
    simp_rw [hcomm]
    exact hterm1
  have hterm3 : (∑ x : V, ∑ y : V, if G.Adj x y then δ x * δ y else 0) ≤ 0 := by
    have hsplit : ∑ x : V, ∑ y : V, (if G.Adj x y then δ x * δ y else 0) =
        ∑ x ∈ ({u, v} : Finset V), ∑ y ∈ ({u, v} : Finset V), (if G.Adj x y then δ x * δ y else 0) := by
      symm
      refine Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _) ?_ ?_
      · intro x hx
        have hx' : x ≠ u ∧ x ≠ v := by simpa [Finset.mem_sdiff, not_or] using hx
        refine Finset.sum_eq_zero fun y _ => ?_
        simp only [δ, if_neg hx'.1, if_neg hx'.2, zero_mul, ite_self]
      · intro x _
        refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
        simp only [δ, if_neg hy.1, if_neg hy.2, mul_zero, ite_self]
    rw [hsplit, Finset.sum_pair huv, Finset.sum_pair huv, Finset.sum_pair huv]
    simp only [G.loopless.irrefl, ite_false, zero_add, add_zero, δ, ite_true, if_neg huv.symm]
    by_cases h : G.Adj u v
    · rw [if_pos h, if_pos h.symm]; nlinarith
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]; linarith
  nlinarith

lemma fractional_round {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → ℝ) (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hsum : (∑ x : V, f x) = (Fintype.card V : ℝ) / 2)
    (hquad : 25 * (∑ x : V, ∑ y : V, if G.Adj x y then f x * f y else 0) ≤ (Fintype.card V : ℝ) ^ 2) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  suffices h : ∀ m : ℕ, ∀ g : V → ℝ,
      (Finset.univ.filter (fun x : V => 0 < g x ∧ g x < 1)).card ≤ m →
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
      (∑ x : V, g x) = (Fintype.card V : ℝ) / 2 →
      25 * (∑ x : V, ∑ y : V, if G.Adj x y then g x * g y else 0) ≤ (Fintype.card V : ℝ) ^ 2 →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 from
    h (Fintype.card V) f (Finset.card_filter_le _ _) hf01 hsum hquad
  intro m
  induction m with
  | zero =>
    intro g hcnt hg01 hgsum hgquad
    have hzero : ∀ x : V, g x = 0 ∨ g x = 1 := by
      intro x
      have hx : x ∉ Finset.univ.filter (fun x : V => 0 < g x ∧ g x < 1) := by
        rw [Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcnt)]; simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_lt] at hx
      have := hg01 x
      rcases hx with h1 | h2 <;> [left; right] <;> linarith
    let S : Finset V := Finset.univ.filter (fun x : V => g x = 1)
    refine ⟨(S : Set V), ?_, ?_⟩
    · have hScard : (S.card : ℝ) = (Fintype.card V : ℝ) / 2 := by
        rw [← hgsum]
        have h1 : (∑ x : V, g x) = ∑ x ∈ S, (1 : ℝ) := by
          rw [← Finset.sum_subset (Finset.subset_univ S)]
          · exact Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2
          · intro x _ hx
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
            rcases hzero x with h0 | h1
            · exact h0
            · exact (hx h1).elim
        rw [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [Set.ncard_coe_finset]
      have h2S : (2 * (S.card : ℝ)) = (Fintype.card V : ℝ) := by linarith
      have h2Sn : 2 * S.card = Fintype.card V := by exact_mod_cast h2S
      omega
    · have h2e := OMA.R_Erdos128_erdos_128_R2.two_mul_induce_edgeSet_ncard G S
      have hreal : ((2 * (G.induce (S : Set V)).edgeSet.ncard : ℕ) : ℝ) ≤
          ∑ x : V, ∑ y : V, if G.Adj x y then g x * g y else 0 := by
        rw [h2e, Nat.cast_sum]
        calc
          (∑ x ∈ S, (((S.filter (G.Adj x)).card : ℕ) : ℝ))
              = ∑ x ∈ S, ∑ y ∈ S, (if G.Adj x y then (1 : ℝ) else 0) := by
                refine Finset.sum_congr rfl fun x _ => ?_
                rw [Finset.card_filter, Nat.cast_sum]
                exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
          _ = ∑ x ∈ S, ∑ y ∈ S, (if G.Adj x y then g x * g y else 0) := by
                refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
                rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, mul_one]
          _ ≤ ∑ x : V, ∑ y : V, (if G.Adj x y then g x * g y else 0) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_ |>.trans' ?_
                · intro x _ _
                  refine Finset.sum_nonneg fun y _ => ?_
                  split_ifs
                  · exact mul_nonneg (hg01 x).1 (hg01 y).1
                  · exact le_refl 0
                · refine Finset.sum_le_sum fun x _ => ?_
                  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun y _ _ => ?_
                  split_ifs
                  · exact mul_nonneg (hg01 x).1 (hg01 y).1
                  · exact le_refl 0
      have h50r : ((50 * (G.induce (S : Set V)).edgeSet.ncard : ℕ) : ℝ) ≤ ((Fintype.card V ^ 2 : ℕ) : ℝ) := by
        push_cast at hreal ⊢; linarith
      exact_mod_cast h50r
  | succ m ih =>
    intro g hcnt hg01 hgsum hgquad
    let F : Finset V := Finset.univ.filter (fun x : V => 0 < g x ∧ g x < 1)
    by_cases hF1 : F.card ≤ 1
    · let S : Finset V := Finset.univ.filter (fun x : V => g x = 1)
      refine ⟨(S : Set V), ?_, ?_⟩
      · have hsum_le : (∑ x : V, g x) < (S.card : ℝ) + 1 := by
          have hdisj : Disjoint S F := by
            rw [Finset.disjoint_left]; intro x hxS hxF
            have := (Finset.mem_filter.mp hxS).2
            have := (Finset.mem_filter.mp hxF).2.2
            linarith
          have hsub : (∑ x : V, g x) = (∑ x ∈ S, g x) + ∑ x ∈ F, g x := by
            rw [← Finset.sum_union hdisj]
            symm
            refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
            simp only [Finset.mem_union, S, F, Finset.mem_filter, Finset.mem_univ, true_and,
              not_or, not_and_or, not_lt] at hx
            have := hg01 x
            rcases hx.2 with h0 | h1
            · linarith
            · exfalso; exact hx.1 (by linarith)
          have hSval : ∑ x ∈ S, g x = (S.card : ℝ) := by
            calc ∑ x ∈ S, g x = ∑ _x ∈ S, (1 : ℝ) := Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp hx).2
              _ = (S.card : ℝ) := by simp
          have hFval : ∑ x ∈ F, g x < 1 := by
            rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hF1 with h0 | h1
            · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]; norm_num
            · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp h1
              rw [hw, Finset.sum_singleton]
              have hwm : w ∈ F := by rw [hw]; simp
              exact (Finset.mem_filter.mp hwm).2.2
          linarith
        rw [Set.ncard_coe_finset]
        have hlt : (Fintype.card V : ℝ) < 2 * (S.card : ℝ) + 2 := by linarith
        have hltn : Fintype.card V < 2 * S.card + 2 := by exact_mod_cast hlt
        omega
      · have h2e := OMA.R_Erdos128_erdos_128_R2.two_mul_induce_edgeSet_ncard G S
        have hreal : ((2 * (G.induce (S : Set V)).edgeSet.ncard : ℕ) : ℝ) ≤
            ∑ x : V, ∑ y : V, if G.Adj x y then g x * g y else 0 := by
          rw [h2e, Nat.cast_sum]
          calc
            (∑ x ∈ S, (((S.filter (G.Adj x)).card : ℕ) : ℝ))
                = ∑ x ∈ S, ∑ y ∈ S, (if G.Adj x y then (1 : ℝ) else 0) := by
                  refine Finset.sum_congr rfl fun x _ => ?_
                  rw [Finset.card_filter, Nat.cast_sum]
                  exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
            _ = ∑ x ∈ S, ∑ y ∈ S, (if G.Adj x y then g x * g y else 0) := by
                  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
                  rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, mul_one]
            _ ≤ ∑ x : V, ∑ y : V, (if G.Adj x y then g x * g y else 0) := by
                  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) ?_ |>.trans' ?_
                  · intro x _ _
                    refine Finset.sum_nonneg fun y _ => ?_
                    split_ifs
                    · exact mul_nonneg (hg01 x).1 (hg01 y).1
                    · exact le_refl 0
                  · refine Finset.sum_le_sum fun x _ => ?_
                    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun y _ _ => ?_
                    split_ifs
                    · exact mul_nonneg (hg01 x).1 (hg01 y).1
                    · exact le_refl 0
        have h50r : ((50 * (G.induce (S : Set V)).edgeSet.ncard : ℕ) : ℝ) ≤ ((Fintype.card V ^ 2 : ℕ) : ℝ) := by
          push_cast at hreal ⊢; linarith
        exact_mod_cast h50r
    · have hF2 : 1 < F.card := by omega
      obtain ⟨a, haF, b, hbF, hab⟩ := Finset.one_lt_card.mp hF2
      have ha := (Finset.mem_filter.mp haF).2
      have hb := (Finset.mem_filter.mp hbF).2
      have hor : (∑ y : V, if G.Adj a y then g y else 0) ≤ (∑ y : V, if G.Adj b y then g y else 0) ∨
          (∑ y : V, if G.Adj b y then g y else 0) ≤ (∑ y : V, if G.Adj a y then g y else 0) :=
        le_total _ _
      obtain ⟨u, v, huF, hvF, huv, hdeg⟩ :
          ∃ u v : V, u ∈ F ∧ v ∈ F ∧ u ≠ v ∧
            (∑ y : V, if G.Adj u y then g y else 0) ≤ (∑ y : V, if G.Adj v y then g y else 0) := by
        rcases hor with hle | hle
        · exact ⟨a, b, haF, hbF, hab, hle⟩
        · exact ⟨b, a, hbF, haF, hab.symm, hle⟩
      have hu := (Finset.mem_filter.mp huF).2
      have hv := (Finset.mem_filter.mp hvF).2
      let t : ℝ := min (1 - g u) (g v)
      have ht_pos : 0 < t := lt_min (by linarith) hv.1
      let g' : V → ℝ := fun x => if x = u then g u + t else if x = v then g v - t else g x
      have hg'01 : ∀ x, 0 ≤ g' x ∧ g' x ≤ 1 := by
        intro x
        by_cases h1 : x = u
        · subst h1; simp only [g', ite_true]
          have hle1 : t ≤ 1 - g x := min_le_left _ _
          constructor <;> linarith
        · by_cases h2 : x = v
          · subst h2; simp only [g', if_neg h1, ite_true]
            have hle2 : t ≤ g x := min_le_right _ _
            constructor <;> linarith
          · simp only [g', if_neg h1, if_neg h2]; exact hg01 x
      have hg'sum : (∑ x : V, g' x) = (Fintype.card V : ℝ) / 2 := by
        rw [← hgsum]
        have hdiff : ∑ x : V, (g' x - g x) = 0 := by
          have hsub : ∑ x : V, (g' x - g x) = ∑ x ∈ ({u, v} : Finset V), (g' x - g x) := by
            symm
            refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
            simp only [g', if_neg hx.1, if_neg hx.2, sub_self]
          rw [hsub, Finset.sum_pair huv]
          simp only [g', ite_true, if_neg huv.symm]
          ring
        rw [Finset.sum_sub_distrib] at hdiff
        linarith
      have hg'quad : 25 * (∑ x : V, ∑ y : V, if G.Adj x y then g' x * g' y else 0) ≤ (Fintype.card V : ℝ) ^ 2 := by
        have hle := quad_shift_le G g u v huv t (le_of_lt ht_pos) hdeg
        linarith
      have hF'sub : Finset.univ.filter (fun x : V => 0 < g' x ∧ g' x < 1) ⊂ F := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro x hx
          have hx' := (Finset.mem_filter.mp hx).2
          by_cases h1 : x = u
          · subst h1; exact huF
          · by_cases h2 : x = v
            · subst h2; exact hvF
            · simp only [g', if_neg h1, if_neg h2] at hx'
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩
        · intro heq
          rcases min_cases (1 - g u) (g v) with ⟨ht1, _⟩ | ⟨ht2, _⟩
          · have : u ∈ Finset.univ.filter (fun x : V => 0 < g' x ∧ g' x < 1) := by rw [heq]; exact huF
            have hlt := (Finset.mem_filter.mp this).2.2
            simp only [g', ite_true] at hlt
            dsimp only [t] at hlt; linarith
          · have : v ∈ Finset.univ.filter (fun x : V => 0 < g' x ∧ g' x < 1) := by rw [heq]; exact hvF
            have hgt := (Finset.mem_filter.mp this).2.1
            simp only [g', if_neg huv.symm, ite_true] at hgt
            dsimp only [t] at hgt; linarith
      have hcard_lt : (Finset.univ.filter (fun x : V => 0 < g' x ∧ g' x < 1)).card < F.card :=
        Finset.card_lt_card hF'sub
      dsimp only [F] at hcard_lt
      exact ih g' (by omega) hg'01 hg'sum hg'quad

/- ### Part 2: Homomorphism Lift from Weighted Vega Graph to G -/

lemma hom_lift_fractional {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : W → W → Prop) [DecidableRel R]
    (hn : 0 < Fintype.card V)
    (φ : V → W) (hφ : ∀ x y : V, G.Adj x y → R (φ x) (φ y))
    (s : W → ℝ)
    (hs01 : ∀ z : W, 0 ≤ s z ∧ s z ≤ ((Finset.univ.filter (fun x : V => φ x = z)).card : ℝ) / (Fintype.card V : ℝ))
    (hssum : (∑ z : W, s z) = 1 / 2)
    (hsquad : 25 * (∑ a : W, ∑ b : W, if R a b then s a * s b else 0) ≤ 1) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  have hnR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hn
  let c : W → ℕ := fun z => (Finset.univ.filter (fun x : V => φ x = z)).card
  let f : V → ℝ := fun x => (Fintype.card V : ℝ) * s (φ x) / (c (φ x) : ℝ)
  have hc_pos : ∀ x : V, (0 : ℝ) < (c (φ x) : ℝ) := by
    intro x
    have hmem : x ∈ Finset.univ.filter (fun y : V => φ y = φ x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have : 0 < c (φ x) := Finset.card_pos.mpr ⟨x, hmem⟩
    exact_mod_cast this
  have hf01 : ∀ x : V, 0 ≤ f x ∧ f x ≤ 1 := by
    intro x
    have hcx := hc_pos x
    have hsx := hs01 (φ x)
    dsimp only [f]
    constructor
    · exact div_nonneg (mul_nonneg (le_of_lt hnR) hsx.1) (le_of_lt hcx)
    · rw [div_le_one hcx]
      have hmul : s (φ x) * (Fintype.card V : ℝ) ≤ (c (φ x) : ℝ) := by
        have := mul_le_mul_of_nonneg_right hsx.2 (le_of_lt hnR)
        rwa [div_mul_cancel₀ _ (ne_of_gt hnR)] at this
      linarith
  have hfiber_sum : ∀ z : W, (∑ x ∈ Finset.univ.filter (fun x : V => φ x = z), f x) =
      (Fintype.card V : ℝ) * s z := by
    intro z
    by_cases hcz : c z = 0
    · have hemp : Finset.univ.filter (fun x : V => φ x = z) = ∅ := Finset.card_eq_zero.mp hcz
      rw [hemp, Finset.sum_empty]
      have hsz := hs01 z
      have hczR : ((Finset.univ.filter (fun x : V => φ x = z)).card : ℝ) = 0 := by exact_mod_cast hcz
      rw [hczR, zero_div] at hsz
      have : s z = 0 := le_antisymm hsz.2 hsz.1
      rw [this, mul_zero]
    · have hczR : (c z : ℝ) ≠ 0 := by exact_mod_cast hcz
      have hconst : ∀ x ∈ Finset.univ.filter (fun x : V => φ x = z),
          f x = (Fintype.card V : ℝ) * s z / (c z : ℝ) := by
        intro x hx; dsimp only [f]; rw [(Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
      change (c z : ℝ) * ((Fintype.card V : ℝ) * s z / (c z : ℝ)) = (Fintype.card V : ℝ) * s z
      rw [mul_div_cancel₀ _ hczR]
  have hfsum : (∑ x : V, f x) = (Fintype.card V : ℝ) / 2 := by
    have hpart : (∑ x : V, f x) = ∑ z : W, ∑ x ∈ Finset.univ.filter (fun x : V => φ x = z), f x := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) f
    rw [hpart]
    simp_rw [hfiber_sum, ← Finset.mul_sum, hssum]
    ring
  have hfquad : 25 * (∑ x : V, ∑ y : V, if G.Adj x y then f x * f y else 0) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have hstep1 : (∑ x : V, ∑ y : V, if G.Adj x y then f x * f y else 0) ≤
        ∑ x : V, ∑ y : V, if R (φ x) (φ y) then f x * f y else 0 := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
      by_cases hG : G.Adj x y
      · rw [if_pos hG, if_pos (hφ x y hG)]
      · rw [if_neg hG]
        split_ifs
        · exact mul_nonneg (hf01 x).1 (hf01 y).1
        · exact le_refl 0
    have hstep2 : (∑ x : V, ∑ y : V, if R (φ x) (φ y) then f x * f y else 0) =
        (Fintype.card V : ℝ) ^ 2 * (∑ a : W, ∑ b : W, if R a b then s a * s b else 0) := by
      have hinner : ∀ x : V, (∑ y : V, if R (φ x) (φ y) then f x * f y else 0) =
          f x * ((Fintype.card V : ℝ) * ∑ b : W, if R (φ x) b then s b else 0) := by
        intro x
        have hpart : (∑ y : V, if R (φ x) (φ y) then f x * f y else 0) =
            ∑ b : W, ∑ y ∈ Finset.univ.filter (fun y : V => φ y = b),
              if R (φ x) (φ y) then f x * f y else 0 := by
          symm; exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
        rw [hpart, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hR : R (φ x) b
        · rw [if_pos hR]
          have h1 : ∀ y ∈ Finset.univ.filter (fun y : V => φ y = b),
              (if R (φ x) (φ y) then f x * f y else 0) = f x * f y := by
            intro y hy; rw [(Finset.mem_filter.mp hy).2, if_pos hR]
          rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hfiber_sum b]
        · rw [if_neg hR, mul_zero, mul_zero]
          refine Finset.sum_eq_zero fun y hy => ?_
          rw [(Finset.mem_filter.mp hy).2, if_neg hR]
      simp_rw [hinner]
      have hpart2 : (∑ x : V, f x * ((Fintype.card V : ℝ) * ∑ b : W, if R (φ x) b then s b else 0)) =
          ∑ a : W, ∑ x ∈ Finset.univ.filter (fun x : V => φ x = a),
            f x * ((Fintype.card V : ℝ) * ∑ b : W, if R (φ x) b then s b else 0) := by
        symm; exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
      rw [hpart2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      have h1 : ∀ x ∈ Finset.univ.filter (fun x : V => φ x = a),
          f x * ((Fintype.card V : ℝ) * ∑ b : W, if R (φ x) b then s b else 0) =
          f x * ((Fintype.card V : ℝ) * ∑ b : W, if R a b then s b else 0) := by
        intro x hx; rw [(Finset.mem_filter.mp hx).2]
      rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, hfiber_sum a]
      have h2 : ∑ b : W, (if R a b then s a * s b else 0) = s a * ∑ b : W, (if R a b then s b else 0) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; split_ifs <;> ring
      rw [h2]; ring
    have hmul : 25 * ((Fintype.card V : ℝ) ^ 2 * (∑ a : W, ∑ b : W, if R a b then s a * s b else 0)) ≤
        (Fintype.card V : ℝ) ^ 2 := by
      have hsq : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := sq_nonneg _
      nlinarith
    linarith
  exact fractional_round G f hf01 hfsum hfquad

/- ### Part 3: Triangle-freeness of Υᵢ⁰⁰ and Explicit Andrásfai Boundary Projections -/

lemma vega_adj_symm {i : ℕ} (hi : 2 ≤ i) (x y : Fin (3 * i - 1) ⊕ Fin 8)
    (h : match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) :
    match y, x with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)) := by
  cases x with
  | inl p =>
    cases y with
    | inl q => exact (OMA.R_Erdos128_erdos_128_R2_H2_R2.and_adj_symm (by omega) p.isLt q.isLt).mp h
    | inr t => exact h
  | inr t =>
    cases y with
    | inl p => exact h
    | inr s =>
      rcases h with ⟨h1, h2, h3 | h3⟩ | h | h | h | h
      · exact Or.inl ⟨h2, h1, Or.inr h3⟩
      · exact Or.inl ⟨h2, h1, Or.inl h3⟩
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

lemma and_no_tri {i : ℕ} (hi : 2 ≤ i) (p q r : Fin (3 * i - 1))
    (hpq : i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1)
    (hqr : i ≤ (r.val + (3 * i - 1) - q.val) % (3 * i - 1) ∧ (r.val + (3 * i - 1) - q.val) % (3 * i - 1) ≤ 2 * i - 1)
    (hrp : i ≤ (p.val + (3 * i - 1) - r.val) % (3 * i - 1) ∧ (p.val + (3 * i - 1) - r.val) % (3 * i - 1) ≤ 2 * i - 1) :
    False := by
  have hp := p.isLt; have hq := q.isLt; have hr := r.isLt
  have hdiff : ∀ a b : ℕ, a < 3 * i - 1 → b < 3 * i - 1 →
      (b + (3 * i - 1) - a) % (3 * i - 1) = if a ≤ b then b - a else b + (3 * i - 1) - a := by
    intro a b ha hb
    split_ifs with h
    · have : b + (3 * i - 1) - a = (b - a) + (3 * i - 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [hdiff p.val q.val hp hq] at hpq
  rw [hdiff q.val r.val hq hr] at hqr
  rw [hdiff r.val p.val hr hp] at hrp
  split_ifs at hpq hqr hrp <;> omega

lemma ext_adj_cases (t s : ℕ)
    (h : (t < 6 ∧ s < 6 ∧ ((t + 1) % 6 = s ∨ (s + 1) % 6 = t)) ∨
         (t = 6 ∧ (s = 0 ∨ s = 4 ∨ s = 2 ∨ s = 7)) ∨
         (s = 6 ∧ (t = 0 ∨ t = 4 ∨ t = 2 ∨ t = 7)) ∨
         (t = 7 ∧ (s = 3 ∨ s = 1 ∨ s = 5 ∨ s = 6)) ∨
         (s = 7 ∧ (t = 3 ∨ t = 1 ∨ t = 5 ∨ t = 6))) :
    (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨ (t = 2 ∧ s = 1) ∨
    (t = 2 ∧ s = 3) ∨ (t = 3 ∧ s = 2) ∨ (t = 3 ∧ s = 4) ∨ (t = 4 ∧ s = 3) ∨
    (t = 4 ∧ s = 5) ∨ (t = 5 ∧ s = 4) ∨ (t = 5 ∧ s = 0) ∨ (t = 0 ∧ s = 5) ∨
    (t = 6 ∧ s = 0) ∨ (t = 6 ∧ s = 4) ∨ (t = 6 ∧ s = 2) ∨ (t = 6 ∧ s = 7) ∨
    (t = 0 ∧ s = 6) ∨ (t = 4 ∧ s = 6) ∨ (t = 2 ∧ s = 6) ∨ (t = 7 ∧ s = 6) ∨
    (t = 7 ∧ s = 3) ∨ (t = 7 ∧ s = 1) ∨ (t = 7 ∧ s = 5) ∨
    (t = 3 ∧ s = 7) ∨ (t = 1 ∧ s = 7) ∨ (t = 5 ∧ s = 7) := by
  rcases h with ⟨h1, h2, h3 | h3⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩
  · have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> (norm_num at h3; subst h3; decide)
  · have hcases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> (norm_num at h3; subst h3; decide)
  all_goals decide

lemma ext_same_color_nonadj (t s : ℕ)
    (hcol : ((t = 0 ∨ t = 3) ∧ (s = 0 ∨ s = 3)) ∨
            ((t = 4 ∨ t = 1) ∧ (s = 4 ∨ s = 1)) ∨
            ((t = 2 ∨ t = 5) ∧ (s = 2 ∨ s = 5)))
    (hadj : (t < 6 ∧ s < 6 ∧ ((t + 1) % 6 = s ∨ (s + 1) % 6 = t)) ∨
            (t = 6 ∧ (s = 0 ∨ s = 4 ∨ s = 2 ∨ s = 7)) ∨
            (s = 6 ∧ (t = 0 ∨ t = 4 ∨ t = 2 ∨ t = 7)) ∨
            (t = 7 ∧ (s = 3 ∨ s = 1 ∨ s = 5 ∨ s = 6)) ∨
            (s = 7 ∧ (t = 3 ∨ t = 1 ∨ t = 5 ∨ t = 6))) : False := by
  rcases ext_adj_cases t s hadj with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at hcol

lemma ext_bipartite (t₁ t₂ : ℕ)
    (h : (t₁ < 6 ∧ t₂ < 6 ∧ ((t₁ + 1) % 6 = t₂ ∨ (t₂ + 1) % 6 = t₁)) ∨
         (t₁ = 6 ∧ (t₂ = 0 ∨ t₂ = 4 ∨ t₂ = 2 ∨ t₂ = 7)) ∨
         (t₂ = 6 ∧ (t₁ = 0 ∨ t₁ = 4 ∨ t₁ = 2 ∨ t₁ = 7)) ∨
         (t₁ = 7 ∧ (t₂ = 3 ∨ t₂ = 1 ∨ t₂ = 5 ∨ t₂ = 6)) ∨
         (t₂ = 7 ∧ (t₁ = 3 ∨ t₁ = 1 ∨ t₁ = 5 ∨ t₁ = 6))) :
    (t₁ = 0 ∨ t₁ = 2 ∨ t₁ = 4 ∨ t₁ = 7) ↔ ¬ (t₂ = 0 ∨ t₂ = 2 ∨ t₂ = 4 ∨ t₂ = 7) := by
  rcases h with ⟨h1, h2, h3 | h3⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ |
    ⟨rfl, rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩
  · have hcases : t₁ = 0 ∨ t₁ = 1 ∨ t₁ = 2 ∨ t₁ = 3 ∨ t₁ = 4 ∨ t₁ = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> (norm_num at h3; subst h3; decide)
  · have hcases : t₂ = 0 ∨ t₂ = 1 ∨ t₂ = 2 ∨ t₂ = 3 ∨ t₂ = 4 ∨ t₂ = 5 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> (norm_num at h3; subst h3; decide)
  all_goals decide

lemma vega_cliqueFree_three {V : Type} (G : SimpleGraph V) (i : ℕ) (hi : 2 ≤ i)
    (φ : V → Fin (3 * i - 1) ⊕ Fin 8)
    (hφ : ∀ x y : V, G.Adj x y →
      match φ x, φ y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))) :
    G.CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
  have e1 := hφ a b (hs.1 (by simp) (by simp) hab)
  have e2 := hφ b c (hs.1 (by simp) (by simp) hbc)
  have e3 := hφ c a (hs.1 (by simp) (by simp) hac.symm)
  have hdiff : ∀ p q : Fin (3 * i - 1),
      (q.val + (3 * i - 1) - p.val) % (3 * i - 1) =
      if p.val ≤ q.val then q.val - p.val else q.val + (3 * i - 1) - p.val := by
    intro p q
    have hp := p.isLt; have hq := q.isLt
    split_ifs with h
    · have : q.val + (3 * i - 1) - p.val = (q.val - p.val) + (3 * i - 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  cases hfa : φ a with
  | inl pa =>
    cases hfb : φ b with
    | inl pb =>
      cases hfc : φ c with
      | inl pc =>
        rw [hfa, hfb] at e1; rw [hfb, hfc] at e2; rw [hfc, hfa] at e3
        exact and_no_tri hi pa pb pc e1 e2 e3
      | inr tc =>
        rw [hfa, hfb] at e1; rw [hfb, hfc] at e2; rw [hfc, hfa] at e3
        dsimp only at e1 e2 e3
        rw [hdiff pa pb] at e1
        have := pa.isLt; have := pb.isLt
        rcases e2 with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;> rcases e3 with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;>
          (split_ifs at e1 <;> omega)
    | inr tb =>
      cases hfc : φ c with
      | inl pc =>
        rw [hfa, hfb] at e1; rw [hfb, hfc] at e2; rw [hfc, hfa] at e3
        dsimp only at e1 e2 e3
        rw [hdiff pc pa] at e3
        have := pa.isLt; have := pc.isLt
        rcases e1 with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;> rcases e2 with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;>
          (split_ifs at e3 <;> omega)
      | inr tc =>
        rw [hfa, hfb] at e1; rw [hfb, hfc] at e2; rw [hfc, hfa] at e3
        dsimp only at e1 e2 e3
        have hcol : ((tb.val = 0 ∨ tb.val = 3) ∧ (tc.val = 0 ∨ tc.val = 3)) ∨
            ((tb.val = 4 ∨ tb.val = 1) ∧ (tc.val = 4 ∨ tc.val = 1)) ∨
            ((tb.val = 2 ∨ tb.val = 5) ∧ (tc.val = 2 ∨ tc.val = 5)) := by
          rcases e1 with ⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨h1, _⟩ <;> rcases e3 with ⟨h3, _⟩ | ⟨h3, _, _⟩ | ⟨h3, _⟩ <;>
            first | exact Or.inl ⟨h1, h3⟩ | exact Or.inr (Or.inl ⟨h1, h3⟩) | exact Or.inr (Or.inr ⟨h1, h3⟩) | omega
        exact ext_same_color_nonadj tb.val tc.val hcol e2
  | inr ta =>
    cases hfb : φ b with
    | inl pb =>
      cases hfc : φ c with
      | inl pc =>
        rw [hfa, hfb] at e1; rw [hfb, hfc] at e2; rw [hfc, hfa] at e3
        dsimp only at e1 e2 e3
        rw [hdiff pb pc] at e2
        have := pb.isLt; have := pc.isLt
        rcases e1 with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;> rcases e3 with ⟨_, _⟩ | ⟨_, _, _⟩ | ⟨_, _⟩ <;>
          (split_ifs at e2 <;> omega)
      | inr tc =>
        rw [hfa, hfb] at e1; rw [hfb, hfc] at e2; rw [hfc, hfa] at e3
        dsimp only at e1 e2 e3
        have hcol : ((tc.val = 0 ∨ tc.val = 3) ∧ (ta.val = 0 ∨ ta.val = 3)) ∨
            ((tc.val = 4 ∨ tc.val = 1) ∧ (ta.val = 4 ∨ ta.val = 1)) ∨
            ((tc.val = 2 ∨ tc.val = 5) ∧ (ta.val = 2 ∨ ta.val = 5)) := by
          rcases e2 with ⟨h2, _⟩ | ⟨h2, _, _⟩ | ⟨h2, _⟩ <;> rcases e1 with ⟨h1, _⟩ | ⟨h1, _, _⟩ | ⟨h1, _⟩ <;>
            first | exact Or.inl ⟨h2, h1⟩ | exact Or.inr (Or.inl ⟨h2, h1⟩) | exact Or.inr (Or.inr ⟨h2, h1⟩) | omega
        exact ext_same_color_nonadj tc.val ta.val hcol e3
    | inr tb =>
      cases hfc : φ c with
      | inl pc =>
        rw [hfa, hfb] at e1; rw [hfb, hfc] at e2; rw [hfc, hfa] at e3
        dsimp only at e1 e2 e3
        have hcol : ((ta.val = 0 ∨ ta.val = 3) ∧ (tb.val = 0 ∨ tb.val = 3)) ∨
            ((ta.val = 4 ∨ ta.val = 1) ∧ (tb.val = 4 ∨ tb.val = 1)) ∨
            ((ta.val = 2 ∨ ta.val = 5) ∧ (tb.val = 2 ∨ tb.val = 5)) := by
          rcases e3 with ⟨h3, _⟩ | ⟨h3, _, _⟩ | ⟨h3, _⟩ <;> rcases e2 with ⟨h2, _⟩ | ⟨h2, _, _⟩ | ⟨h2, _⟩ <;>
            first | exact Or.inl ⟨h3, h2⟩ | exact Or.inr (Or.inl ⟨h3, h2⟩) | exact Or.inr (Or.inr ⟨h3, h2⟩) | omega
        exact ext_same_color_nonadj ta.val tb.val hcol e1
      | inr tc =>
        rw [hfa, hfb] at e1; rw [hfb, hfc] at e2; rw [hfc, hfa] at e3
        dsimp only at e1 e2 e3
        have c1 := ext_bipartite ta.val tb.val e1
        have c2 := ext_bipartite tb.val tc.val e2
        have c3 := ext_bipartite tc.val ta.val e3
        by_cases hA : ta.val = 0 ∨ ta.val = 2 ∨ ta.val = 4 ∨ ta.val = 7
        · exact c1.mp hA (c2.mpr fun hC => c3.mp hC hA)
        · exact c2.mp (by by_contra hnB; exact hA (c1.mpr hnB)) (c3.mpr hA)

/- Exact Andrásfai projections on the 4 zero-boundary faces of Υᵢ⁰⁰ -/

lemma and_mod_check (k a b : ℕ) (_hk : 2 ≤ k) (ha : a < 3 * k - 1) (hb : b < 3 * k - 1)
    (h1 : k ≤ if a ≤ b then b - a else b + (3 * k - 1) - a)
    (h2 : (if a ≤ b then b - a else b + (3 * k - 1) - a) < 2 * k) :
    k ≤ (b + (3 * k - 1) - a) % (3 * k - 1) ∧ (b + (3 * k - 1) - a) % (3 * k - 1) < 2 * k := by
  have hdiff : (b + (3 * k - 1) - a) % (3 * k - 1) = if a ≤ b then b - a else b + (3 * k - 1) - a := by
    split_ifs with h
    · have : b + (3 * k - 1) - a = (b - a) + (3 * k - 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [hdiff]; exact ⟨h1, h2⟩

lemma proj_del_av {i : ℕ} (hi : 2 ≤ i) (x y : Fin (3 * i - 1) ⊕ Fin 8)
    (hadj : match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)))
    (hx : x ≠ Sum.inr 0 ∧ x ≠ Sum.inr 1) (hy : y ≠ Sum.inr 0 ∧ y ≠ Sum.inr 1) :
    let ψ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) := fun z =>
      match z with
      | Sum.inl p => p
      | Sum.inr t =>
        if t.val = 2 then ⟨i - 1, by omega⟩
        else if t.val = 3 then ⟨2 * i - 1, by omega⟩
        else if t.val = 4 then ⟨0, by omega⟩
        else if t.val = 5 then ⟨i, by omega⟩
        else if t.val = 6 then ⟨2 * i - 1, by omega⟩
        else ⟨0, by omega⟩
    i ≤ ((ψ y).val + (3 * i - 1) - (ψ x).val) % (3 * i - 1) ∧
    ((ψ y).val + (3 * i - 1) - (ψ x).val) % (3 * i - 1) < 2 * i := by
  intro ψ
  have hval : ∀ t : Fin 8, (ψ (Sum.inr t)).val =
      if t.val = 2 then i - 1 else if t.val = 3 then 2 * i - 1 else if t.val = 4 then 0
      else if t.val = 5 then i else if t.val = 6 then 2 * i - 1 else 0 := by
    intro t; dsimp only [ψ]; split_ifs <;> rfl
  cases x with
  | inl p =>
    cases y with
    | inl q => dsimp only [ψ]; exact ⟨hadj.1, by omega⟩
    | inr t =>
      have ht0 : t.val ≠ 0 := fun h => hy.1 (congrArg Sum.inr (Fin.ext h))
      have ht1 : t.val ≠ 1 := fun h => hy.2 (congrArg Sum.inr (Fin.ext h))
      have hp := p.isLt
      apply and_mod_check i (ψ (Sum.inl p)).val (ψ (Sum.inr t)).val hi (ψ (Sum.inl p)).isLt (ψ (Sum.inr t)).isLt
      all_goals
        rw [hval t]; dsimp only [ψ]
        rcases hadj with ⟨h1 | h1, _⟩ | ⟨h1 | h1, _, _⟩ | ⟨h1 | h1, _⟩ <;>
          (try omega) <;> (rw [h1]; norm_num; (try split_ifs) <;> omega)
  | inr t =>
    cases y with
    | inl p =>
      have ht0 : t.val ≠ 0 := fun h => hx.1 (congrArg Sum.inr (Fin.ext h))
      have ht1 : t.val ≠ 1 := fun h => hx.2 (congrArg Sum.inr (Fin.ext h))
      have hp := p.isLt
      apply and_mod_check i (ψ (Sum.inr t)).val (ψ (Sum.inl p)).val hi (ψ (Sum.inr t)).isLt (ψ (Sum.inl p)).isLt
      all_goals
        rw [hval t]; dsimp only [ψ]
        rcases hadj with ⟨h1 | h1, _⟩ | ⟨h1 | h1, _, _⟩ | ⟨h1 | h1, _⟩ <;>
          (try omega) <;> (rw [h1]; norm_num; (try split_ifs) <;> omega)
    | inr s =>
      have ht0 : t.val ≠ 0 := fun h => hx.1 (congrArg Sum.inr (Fin.ext h))
      have ht1 : t.val ≠ 1 := fun h => hx.2 (congrArg Sum.inr (Fin.ext h))
      have hs0 : s.val ≠ 0 := fun h => hy.1 (congrArg Sum.inr (Fin.ext h))
      have hs1 : s.val ≠ 1 := fun h => hy.2 (congrArg Sum.inr (Fin.ext h))
      have hcases := ext_adj_cases t.val s.val hadj
      apply and_mod_check i (ψ (Sum.inr t)).val (ψ (Sum.inr s)).val hi (ψ (Sum.inr t)).isLt (ψ (Sum.inr s)).isLt
      all_goals
        rw [hval t, hval s]
        rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          (try omega) <;> (rw [e1, e2]; norm_num <;> (try split_ifs) <;> omega)

lemma proj_del_ub {i : ℕ} (hi : 2 ≤ i) (x y : Fin (3 * i - 1) ⊕ Fin 8)
    (hadj : match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)))
    (hx : x ≠ Sum.inr 3 ∧ x ≠ Sum.inr 4) (hy : y ≠ Sum.inr 3 ∧ y ≠ Sum.inr 4) :
    let ψ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) := fun z =>
      match z with
      | Sum.inl p => p
      | Sum.inr t =>
        if t.val = 0 then ⟨2 * i - 1, by omega⟩
        else if t.val = 1 then ⟨0, by omega⟩
        else if t.val = 2 then ⟨i, by omega⟩
        else if t.val = 5 then ⟨i - 1, by omega⟩
        else if t.val = 6 then ⟨0, by omega⟩
        else ⟨2 * i - 1, by omega⟩
    i ≤ ((ψ y).val + (3 * i - 1) - (ψ x).val) % (3 * i - 1) ∧
    ((ψ y).val + (3 * i - 1) - (ψ x).val) % (3 * i - 1) < 2 * i := by
  intro ψ
  have hval : ∀ t : Fin 8, (ψ (Sum.inr t)).val =
      if t.val = 0 then 2 * i - 1 else if t.val = 1 then 0 else if t.val = 2 then i
      else if t.val = 5 then i - 1 else if t.val = 6 then 0 else 2 * i - 1 := by
    intro t; dsimp only [ψ]; split_ifs <;> rfl
  cases x with
  | inl p =>
    cases y with
    | inl q => dsimp only [ψ]; exact ⟨hadj.1, by omega⟩
    | inr t =>
      have ht3 : t.val ≠ 3 := fun h => hy.1 (congrArg Sum.inr (Fin.ext h))
      have ht4 : t.val ≠ 4 := fun h => hy.2 (congrArg Sum.inr (Fin.ext h))
      have hp := p.isLt
      apply and_mod_check i (ψ (Sum.inl p)).val (ψ (Sum.inr t)).val hi (ψ (Sum.inl p)).isLt (ψ (Sum.inr t)).isLt
      all_goals
        rw [hval t]; dsimp only [ψ]
        rcases hadj with ⟨h1 | h1, _⟩ | ⟨h1 | h1, _, _⟩ | ⟨h1 | h1, _⟩ <;>
          (try omega) <;> (rw [h1]; norm_num; (try split_ifs) <;> omega)
  | inr t =>
    cases y with
    | inl p =>
      have ht3 : t.val ≠ 3 := fun h => hx.1 (congrArg Sum.inr (Fin.ext h))
      have ht4 : t.val ≠ 4 := fun h => hx.2 (congrArg Sum.inr (Fin.ext h))
      have hp := p.isLt
      apply and_mod_check i (ψ (Sum.inr t)).val (ψ (Sum.inl p)).val hi (ψ (Sum.inr t)).isLt (ψ (Sum.inl p)).isLt
      all_goals
        rw [hval t]; dsimp only [ψ]
        rcases hadj with ⟨h1 | h1, _⟩ | ⟨h1 | h1, _, _⟩ | ⟨h1 | h1, _⟩ <;>
          (try omega) <;> (rw [h1]; norm_num; (try split_ifs) <;> omega)
    | inr s =>
      have ht3 : t.val ≠ 3 := fun h => hx.1 (congrArg Sum.inr (Fin.ext h))
      have ht4 : t.val ≠ 4 := fun h => hx.2 (congrArg Sum.inr (Fin.ext h))
      have hs3 : s.val ≠ 3 := fun h => hy.1 (congrArg Sum.inr (Fin.ext h))
      have hs4 : s.val ≠ 4 := fun h => hy.2 (congrArg Sum.inr (Fin.ext h))
      have hcases := ext_adj_cases t.val s.val hadj
      apply and_mod_check i (ψ (Sum.inr t)).val (ψ (Sum.inr s)).val hi (ψ (Sum.inr t)).isLt (ψ (Sum.inr s)).isLt
      all_goals
        rw [hval t, hval s]
        rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          (try omega) <;> (rw [e1, e2]; norm_num <;> (try split_ifs) <;> omega)

lemma and_shift_embed {i : ℕ} (hi : 2 ≤ i) (p q : Fin (3 * i - 1))
    (hpq : i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
           (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1) :
    let emb : Fin (3 * i - 1) → Fin (3 * (i + 1) - 1) := fun r =>
      if r.val < i then ⟨r.val, by omega⟩
      else if r.val < 2 * i then ⟨r.val + 1, by omega⟩
      else ⟨r.val + 2, by omega⟩
    i + 1 ≤ ((emb q).val + (3 * (i + 1) - 1) - (emb p).val) % (3 * (i + 1) - 1) ∧
    ((emb q).val + (3 * (i + 1) - 1) - (emb p).val) % (3 * (i + 1) - 1) < 2 * (i + 1) := by
  intro emb
  have hp := p.isLt; have hq := q.isLt
  have hval : ∀ r : Fin (3 * i - 1), (emb r).val =
      if r.val < i then r.val else if r.val < 2 * i then r.val + 1 else r.val + 2 := by
    intro r; dsimp only [emb]; split_ifs <;> rfl
  have hdiff : (q.val + (3 * i - 1) - p.val) % (3 * i - 1) =
      if p.val ≤ q.val then q.val - p.val else q.val + (3 * i - 1) - p.val := by
    split_ifs with h
    · have : q.val + (3 * i - 1) - p.val = (q.val - p.val) + (3 * i - 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [hdiff] at hpq
  apply and_mod_check (i + 1) (emb p).val (emb q).val (by omega) (emb p).isLt (emb q).isLt
  all_goals
    rw [hval p, hval q]
    by_cases hp1 : p.val < i <;> by_cases hp2 : p.val < 2 * i <;>
    by_cases hq1 : q.val < i <;> by_cases hq2 : q.val < 2 * i <;>
    simp only [hp1, hp2, hq1, hq2, ite_true, ite_false] <;>
    split_ifs at hpq ⊢ <;> omega

lemma proj_del_vx {i : ℕ} (hi : 2 ≤ i) (x y : Fin (3 * i - 1) ⊕ Fin 8)
    (hadj : match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)))
    (hx : x ≠ Sum.inr 1 ∧ x ≠ Sum.inr 6) (hy : y ≠ Sum.inr 1 ∧ y ≠ Sum.inr 6) :
    let ψ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * (i + 1) - 1) := fun z =>
      match z with
      | Sum.inl p =>
        if p.val < i then ⟨p.val, by omega⟩
        else if p.val < 2 * i then ⟨p.val + 1, by omega⟩
        else ⟨p.val + 2, by omega⟩
      | Sum.inr t =>
        if t.val = 0 then ⟨2 * i + 1, by omega⟩
        else if t.val = 2 then ⟨i - 1, by omega⟩
        else if t.val = 3 then ⟨2 * i, by omega⟩
        else if t.val = 4 then ⟨3 * i + 1, by omega⟩
        else if t.val = 5 then ⟨i, by omega⟩
        else ⟨3 * i + 1, by omega⟩
    i + 1 ≤ ((ψ y).val + (3 * (i + 1) - 1) - (ψ x).val) % (3 * (i + 1) - 1) ∧
    ((ψ y).val + (3 * (i + 1) - 1) - (ψ x).val) % (3 * (i + 1) - 1) < 2 * (i + 1) := by
  intro ψ
  have hvalL : ∀ p : Fin (3 * i - 1), (ψ (Sum.inl p)).val =
      if p.val < i then p.val else if p.val < 2 * i then p.val + 1 else p.val + 2 := by
    intro p; dsimp only [ψ]; split_ifs <;> rfl
  have hvalR : ∀ t : Fin 8, (ψ (Sum.inr t)).val =
      if t.val = 0 then 2 * i + 1 else if t.val = 2 then i - 1 else if t.val = 3 then 2 * i
      else if t.val = 4 then 3 * i + 1 else if t.val = 5 then i else 3 * i + 1 := by
    intro t; dsimp only [ψ]; split_ifs <;> rfl
  cases x with
  | inl p =>
    cases y with
    | inl q => exact and_shift_embed hi p q hadj
    | inr t =>
      have ht1 : t.val ≠ 1 := fun h => hy.1 (congrArg Sum.inr (Fin.ext h))
      have ht6 : t.val ≠ 6 := fun h => hy.2 (congrArg Sum.inr (Fin.ext h))
      have hp := p.isLt
      apply and_mod_check (i + 1) (ψ (Sum.inl p)).val (ψ (Sum.inr t)).val (by omega)
        (ψ (Sum.inl p)).isLt (ψ (Sum.inr t)).isLt
      all_goals
        rw [hvalL p, hvalR t]
        rcases hadj with ⟨h1 | h1, _⟩ | ⟨h1 | h1, _, _⟩ | ⟨h1 | h1, _⟩ <;>
          (try omega) <;> (rw [h1]; norm_num; (try split_ifs) <;> omega)
  | inr t =>
    cases y with
    | inl p =>
      have ht1 : t.val ≠ 1 := fun h => hx.1 (congrArg Sum.inr (Fin.ext h))
      have ht6 : t.val ≠ 6 := fun h => hx.2 (congrArg Sum.inr (Fin.ext h))
      have hp := p.isLt
      apply and_mod_check (i + 1) (ψ (Sum.inr t)).val (ψ (Sum.inl p)).val (by omega)
        (ψ (Sum.inr t)).isLt (ψ (Sum.inl p)).isLt
      all_goals
        rw [hvalL p, hvalR t]
        rcases hadj with ⟨h1 | h1, _⟩ | ⟨h1 | h1, _, _⟩ | ⟨h1 | h1, _⟩ <;>
          (try omega) <;> (rw [h1]; norm_num; (try split_ifs) <;> omega)
    | inr s =>
      have ht1 : t.val ≠ 1 := fun h => hx.1 (congrArg Sum.inr (Fin.ext h))
      have ht6 : t.val ≠ 6 := fun h => hx.2 (congrArg Sum.inr (Fin.ext h))
      have hs1 : s.val ≠ 1 := fun h => hy.1 (congrArg Sum.inr (Fin.ext h))
      have hs6 : s.val ≠ 6 := fun h => hy.2 (congrArg Sum.inr (Fin.ext h))
      have hcases := ext_adj_cases t.val s.val hadj
      apply and_mod_check (i + 1) (ψ (Sum.inr t)).val (ψ (Sum.inr s)).val (by omega)
        (ψ (Sum.inr t)).isLt (ψ (Sum.inr s)).isLt
      all_goals
        rw [hvalR t, hvalR s]
        rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          (try omega) <;> (rw [e1, e2]; norm_num; (try split_ifs) <;> omega)

lemma proj_del_by {i : ℕ} (hi : 2 ≤ i) (x y : Fin (3 * i - 1) ⊕ Fin 8)
    (hadj : match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)))
    (hx : x ≠ Sum.inr 4 ∧ x ≠ Sum.inr 7) (hy : y ≠ Sum.inr 4 ∧ y ≠ Sum.inr 7) :
    let ψ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * (i + 1) - 1) := fun z =>
      match z with
      | Sum.inl p =>
        if p.val < i then ⟨p.val, by omega⟩
        else if p.val < 2 * i then ⟨p.val + 1, by omega⟩
        else ⟨p.val + 2, by omega⟩
      | Sum.inr t =>
        if t.val = 0 then ⟨2 * i, by omega⟩
        else if t.val = 1 then ⟨3 * i + 1, by omega⟩
        else if t.val = 2 then ⟨i, by omega⟩
        else if t.val = 3 then ⟨2 * i + 1, by omega⟩
        else if t.val = 5 then ⟨i - 1, by omega⟩
        else ⟨3 * i + 1, by omega⟩
    i + 1 ≤ ((ψ y).val + (3 * (i + 1) - 1) - (ψ x).val) % (3 * (i + 1) - 1) ∧
    ((ψ y).val + (3 * (i + 1) - 1) - (ψ x).val) % (3 * (i + 1) - 1) < 2 * (i + 1) := by
  intro ψ
  have hvalL : ∀ p : Fin (3 * i - 1), (ψ (Sum.inl p)).val =
      if p.val < i then p.val else if p.val < 2 * i then p.val + 1 else p.val + 2 := by
    intro p; dsimp only [ψ]; split_ifs <;> rfl
  have hvalR : ∀ t : Fin 8, (ψ (Sum.inr t)).val =
      if t.val = 0 then 2 * i else if t.val = 1 then 3 * i + 1 else if t.val = 2 then i
      else if t.val = 3 then 2 * i + 1 else if t.val = 5 then i - 1 else 3 * i + 1 := by
    intro t; dsimp only [ψ]; split_ifs <;> rfl
  cases x with
  | inl p =>
    cases y with
    | inl q => exact and_shift_embed hi p q hadj
    | inr t =>
      have ht4 : t.val ≠ 4 := fun h => hy.1 (congrArg Sum.inr (Fin.ext h))
      have ht7 : t.val ≠ 7 := fun h => hy.2 (congrArg Sum.inr (Fin.ext h))
      have hp := p.isLt
      apply and_mod_check (i + 1) (ψ (Sum.inl p)).val (ψ (Sum.inr t)).val (by omega)
        (ψ (Sum.inl p)).isLt (ψ (Sum.inr t)).isLt
      all_goals
        rw [hvalL p, hvalR t]
        rcases hadj with ⟨h1 | h1, _⟩ | ⟨h1 | h1, _, _⟩ | ⟨h1 | h1, _⟩ <;>
          (try omega) <;> (rw [h1]; norm_num; (try split_ifs) <;> omega)
  | inr t =>
    cases y with
    | inl p =>
      have ht4 : t.val ≠ 4 := fun h => hx.1 (congrArg Sum.inr (Fin.ext h))
      have ht7 : t.val ≠ 7 := fun h => hx.2 (congrArg Sum.inr (Fin.ext h))
      have hp := p.isLt
      apply and_mod_check (i + 1) (ψ (Sum.inr t)).val (ψ (Sum.inl p)).val (by omega)
        (ψ (Sum.inr t)).isLt (ψ (Sum.inl p)).isLt
      all_goals
        rw [hvalL p, hvalR t]
        rcases hadj with ⟨h1 | h1, _⟩ | ⟨h1 | h1, _, _⟩ | ⟨h1 | h1, _⟩ <;>
          (try omega) <;> (rw [h1]; norm_num; (try split_ifs) <;> omega)
    | inr s =>
      have ht4 : t.val ≠ 4 := fun h => hx.1 (congrArg Sum.inr (Fin.ext h))
      have ht7 : t.val ≠ 7 := fun h => hx.2 (congrArg Sum.inr (Fin.ext h))
      have hs4 : s.val ≠ 4 := fun h => hy.1 (congrArg Sum.inr (Fin.ext h))
      have hs7 : s.val ≠ 7 := fun h => hy.2 (congrArg Sum.inr (Fin.ext h))
      have hcases := ext_adj_cases t.val s.val hadj
      apply and_mod_check (i + 1) (ψ (Sum.inr t)).val (ψ (Sum.inr s)).val (by omega)
        (ψ (Sum.inr t)).isLt (ψ (Sum.inr s)).isLt
      all_goals
        rw [hvalR t, hvalR s]
        rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ |
          ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          (try omega) <;> (rw [e1, e2]; norm_num; (try split_ifs) <;> omega)

/- ### Part 4: Main Reduction Theorem -/

theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R2_H2_R2.H2 := by
  intro h1 h2 V _ G i hi ⟨φ, hφ⟩
  classical
  -- Handle trivial case n = 0
  by_cases hn0 : Fintype.card V = 0
  · refine ⟨∅, by simp [hn0], ?_⟩
    have hemp : (G.induce (∅ : Set V)).edgeSet.ncard = 0 := by
      have := OMA.R_Erdos128_erdos_128_R2.two_mul_induce_edgeSet_ncard G (∅ : Finset V)
      rw [Finset.coe_empty, Finset.sum_empty] at this; omega
    omega
  have hn_pos : 0 < Fintype.card V := Nat.pos_of_ne_zero hn0
  have hnR : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hn_pos
  -- Assume by contradiction that every half-set has > n^2 / 50 edges!
  by_contra hno
  push Not at hno
  have hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2 := fun V' hV' => hno V' hV'
  have hcf : G.CliqueFree 3 := vega_cliqueFree_three G i hi φ hφ
  let w : Fin (3 * i - 1) ⊕ Fin 8 → ℝ :=
    fun z => ((Finset.univ.filter (fun x : V => φ x = z)).card : ℝ) / (Fintype.card V : ℝ)
  have hw0 : ∀ z, 0 ≤ w z := fun z => div_nonneg (Nat.cast_nonneg _) (le_of_lt hnR)
  have hwsum : (∑ z : Fin (3 * i - 1) ⊕ Fin 8, w z) = 1 := by
    dsimp only [w]
    rw [← Finset.sum_div]
    have hcard : (∑ z : Fin (3 * i - 1) ⊕ Fin 8, (Finset.univ.filter (fun x : V => φ x = z)).card) =
        Fintype.card V := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
    have hcardR : (∑ z : Fin (3 * i - 1) ⊕ Fin 8,
        ((Finset.univ.filter (fun x : V => φ x = z)).card : ℝ)) = (Fintype.card V : ℝ) := by
      rw [← Nat.cast_sum, hcard]
    rw [hcardR, div_self (ne_of_gt hnR)]
  -- Helper: if w z1 + w z2 = 0 then no vertex maps to z1 or z2
  have hpair_zero : ∀ z₁ z₂ : Fin (3 * i - 1) ⊕ Fin 8, ¬ (0 < w z₁ + w z₂) →
      ∀ x : V, φ x ≠ z₁ ∧ φ x ≠ z₂ := by
    intro z₁ z₂ hle x
    have h1 := hw0 z₁; have h2 := hw0 z₂
    have hz1 : w z₁ = 0 := by linarith
    have hz2 : w z₂ = 0 := by linarith
    have hc1 : (Finset.univ.filter (fun y : V => φ y = z₁)).card = 0 := by
      dsimp only [w] at hz1
      have : ((Finset.univ.filter (fun y : V => φ y = z₁)).card : ℝ) = 0 :=
        (div_eq_zero_iff.mp hz1).resolve_right (ne_of_gt hnR)
      exact_mod_cast this
    have hc2 : (Finset.univ.filter (fun y : V => φ y = z₂)).card = 0 := by
      dsimp only [w] at hz2
      have : ((Finset.univ.filter (fun y : V => φ y = z₂)).card : ℝ) = 0 :=
        (div_eq_zero_iff.mp hz2).resolve_right (ne_of_gt hnR)
      exact_mod_cast this
    constructor
    · intro h; have : x ∈ Finset.univ.filter (fun y : V => φ y = z₁) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [Finset.card_eq_zero.mp hc1] at this; exact Finset.notMem_empty _ this
    · intro h; have : x ∈ Finset.univ.filter (fun y : V => φ y = z₂) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [Finset.card_eq_zero.mp hc2] at this; exact Finset.notMem_empty _ this
  -- Four Andrásfai boundary eliminations
  have hav : 0 < w (Sum.inr 0) + w (Sum.inr 1) := by
    by_contra hle
    have hne := hpair_zero (Sum.inr 0) (Sum.inr 1) hle
    let ψ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) := fun z =>
      match z with
      | Sum.inl p => p
      | Sum.inr t =>
        if t.val = 2 then ⟨i - 1, by omega⟩
        else if t.val = 3 then ⟨2 * i - 1, by omega⟩
        else if t.val = 4 then ⟨0, by omega⟩
        else if t.val = 5 then ⟨i, by omega⟩
        else if t.val = 6 then ⟨2 * i - 1, by omega⟩
        else ⟨0, by omega⟩
    exact OMA.R_Erdos128_erdos_128_R2.not_hom_andrasfai G hH
      (fun H hHTF hHH => OMA.R_Erdos128_erdos_128_R2.five_mul_edges_lt_sq H hHTF hHH)
      i (by omega) (fun x => ψ (φ x)) (fun x y hxy => proj_del_av hi (φ x) (φ y) (hφ x y hxy) (hne x) (hne y))
  have hub : 0 < w (Sum.inr 3) + w (Sum.inr 4) := by
    by_contra hle
    have hne := hpair_zero (Sum.inr 3) (Sum.inr 4) hle
    let ψ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) := fun z =>
      match z with
      | Sum.inl p => p
      | Sum.inr t =>
        if t.val = 0 then ⟨2 * i - 1, by omega⟩
        else if t.val = 1 then ⟨0, by omega⟩
        else if t.val = 2 then ⟨i, by omega⟩
        else if t.val = 5 then ⟨i - 1, by omega⟩
        else if t.val = 6 then ⟨0, by omega⟩
        else ⟨2 * i - 1, by omega⟩
    exact OMA.R_Erdos128_erdos_128_R2.not_hom_andrasfai G hH
      (fun H hHTF hHH => OMA.R_Erdos128_erdos_128_R2.five_mul_edges_lt_sq H hHTF hHH)
      i (by omega) (fun x => ψ (φ x)) (fun x y hxy => proj_del_ub hi (φ x) (φ y) (hφ x y hxy) (hne x) (hne y))
  have hvx : 0 < w (Sum.inr 1) + w (Sum.inr 6) := by
    by_contra hle
    have hne := hpair_zero (Sum.inr 1) (Sum.inr 6) hle
    let ψ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * (i + 1) - 1) := fun z =>
      match z with
      | Sum.inl p =>
        if p.val < i then ⟨p.val, by omega⟩
        else if p.val < 2 * i then ⟨p.val + 1, by omega⟩
        else ⟨p.val + 2, by omega⟩
      | Sum.inr t =>
        if t.val = 0 then ⟨2 * i + 1, by omega⟩
        else if t.val = 2 then ⟨i - 1, by omega⟩
        else if t.val = 3 then ⟨2 * i, by omega⟩
        else if t.val = 4 then ⟨3 * i + 1, by omega⟩
        else if t.val = 5 then ⟨i, by omega⟩
        else ⟨3 * i + 1, by omega⟩
    exact OMA.R_Erdos128_erdos_128_R2.not_hom_andrasfai G hH
      (fun H hHTF hHH => OMA.R_Erdos128_erdos_128_R2.five_mul_edges_lt_sq H hHTF hHH)
      (i + 1) (by omega) (fun x => ψ (φ x)) (fun x y hxy => proj_del_vx hi (φ x) (φ y) (hφ x y hxy) (hne x) (hne y))
  have hby : 0 < w (Sum.inr 4) + w (Sum.inr 7) := by
    by_contra hle
    have hne := hpair_zero (Sum.inr 4) (Sum.inr 7) hle
    let ψ : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * (i + 1) - 1) := fun z =>
      match z with
      | Sum.inl p =>
        if p.val < i then ⟨p.val, by omega⟩
        else if p.val < 2 * i then ⟨p.val + 1, by omega⟩
        else ⟨p.val + 2, by omega⟩
      | Sum.inr t =>
        if t.val = 0 then ⟨2 * i, by omega⟩
        else if t.val = 1 then ⟨3 * i + 1, by omega⟩
        else if t.val = 2 then ⟨i, by omega⟩
        else if t.val = 3 then ⟨2 * i + 1, by omega⟩
        else if t.val = 5 then ⟨i - 1, by omega⟩
        else ⟨3 * i + 1, by omega⟩
    exact OMA.R_Erdos128_erdos_128_R2.not_hom_andrasfai G hH
      (fun H hHTF hHH => OMA.R_Erdos128_erdos_128_R2.five_mul_edges_lt_sq H hHTF hHH)
      (i + 1) (by omega) (fun x => ψ (φ x)) (fun x y hxy => proj_del_by hi (φ x) (φ y) (hφ x y hxy) (hne x) (hne y))
  -- Independent-set bounds on E₀ = {0, 2, 4, 7} and E₁ = {1, 3, 5, 6}
  have hE0 : w (Sum.inr 0) + w (Sum.inr 2) + w (Sum.inr 4) + w (Sum.inr 7) < 2 / 5 := by
    let S0 : Finset V := Finset.univ.filter (fun x : V =>
      φ x = Sum.inr 0 ∨ φ x = Sum.inr 2 ∨ φ x = Sum.inr 4 ∨ φ x = Sum.inr 7)
    have hI0 : G.IsIndepSet (S0 : Set V) := by
      intro x hx y hy _ hxy
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
      have hadj := hφ x y hxy
      rcases h1 with e1 | e1 | e1 | e1 <;> rcases h2 with e2 | e2 | e2 | e2 <;>
        (rw [e1, e2] at hadj; rcases hadj with ⟨_, _, _ | _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    have hlt := OMA.R_Erdos128_erdos_128_R2.five_mul_indep_lt_two_mul_card G hcf hH (S0 : Set V) hI0
    rw [Set.ncard_coe_finset] at hlt
    have hcard : S0.card =
        (Finset.univ.filter (fun x : V => φ x = Sum.inr 0)).card +
        (Finset.univ.filter (fun x : V => φ x = Sum.inr 2)).card +
        (Finset.univ.filter (fun x : V => φ x = Sum.inr 4)).card +
        (Finset.univ.filter (fun x : V => φ x = Sum.inr 7)).card := by
      have hsum_t : S0.card = ∑ z ∈ ({Sum.inr 0, Sum.inr 2, Sum.inr 4, Sum.inr 7} : Finset (Fin (3 * i - 1) ⊕ Fin 8)),
          (Finset.univ.filter (fun x : V => φ x = z)).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := φ) (s := S0)
          (t := {Sum.inr 0, Sum.inr 2, Sum.inr 4, Sum.inr 7})]
        · refine Finset.sum_congr rfl fun z hz => ?_
          congr 1; ext x; simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          constructor
          · exact fun h => h.2
          · intro hx; exact ⟨by rw [hx]; exact hz, hx⟩
        · intro x hx
          have := (Finset.mem_filter.mp hx).2
          simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using this
      rw [hsum_t]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq,
        Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
      ring
    dsimp only [w]
    have hltR : (5 * (S0.card : ℝ)) < 2 * (Fintype.card V : ℝ) := by exact_mod_cast hlt
    rw [hcard, Nat.cast_add, Nat.cast_add, Nat.cast_add] at hltR
    have hdiv : (5 : ℝ) * ((((Finset.univ.filter (fun x : V => φ x = Sum.inr 0)).card : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 2)).card : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 4)).card : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 7)).card : ℝ)) / (Fintype.card V : ℝ)) < 2 := by
      rw [mul_div_assoc', div_lt_iff₀ hnR]; linarith
    have heq : ((Finset.univ.filter (fun x : V => φ x = Sum.inr 0)).card : ℝ) / (Fintype.card V : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 2)).card : ℝ) / (Fintype.card V : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 4)).card : ℝ) / (Fintype.card V : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 7)).card : ℝ) / (Fintype.card V : ℝ) =
        (((Finset.univ.filter (fun x : V => φ x = Sum.inr 0)).card : ℝ) +
         ((Finset.univ.filter (fun x : V => φ x = Sum.inr 2)).card : ℝ) +
         ((Finset.univ.filter (fun x : V => φ x = Sum.inr 4)).card : ℝ) +
         ((Finset.univ.filter (fun x : V => φ x = Sum.inr 7)).card : ℝ)) / (Fintype.card V : ℝ) := by ring
    rw [heq]; linarith
  have hE1 : w (Sum.inr 1) + w (Sum.inr 3) + w (Sum.inr 5) + w (Sum.inr 6) < 2 / 5 := by
    let S1 : Finset V := Finset.univ.filter (fun x : V =>
      φ x = Sum.inr 1 ∨ φ x = Sum.inr 3 ∨ φ x = Sum.inr 5 ∨ φ x = Sum.inr 6)
    have hI1 : G.IsIndepSet (S1 : Set V) := by
      intro x hx y hy _ hxy
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
      have hadj := hφ x y hxy
      rcases h1 with e1 | e1 | e1 | e1 <;> rcases h2 with e2 | e2 | e2 | e2 <;>
        (rw [e1, e2] at hadj; rcases hadj with ⟨_, _, _ | _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
    have hlt := OMA.R_Erdos128_erdos_128_R2.five_mul_indep_lt_two_mul_card G hcf hH (S1 : Set V) hI1
    rw [Set.ncard_coe_finset] at hlt
    have hcard : S1.card =
        (Finset.univ.filter (fun x : V => φ x = Sum.inr 1)).card +
        (Finset.univ.filter (fun x : V => φ x = Sum.inr 3)).card +
        (Finset.univ.filter (fun x : V => φ x = Sum.inr 5)).card +
        (Finset.univ.filter (fun x : V => φ x = Sum.inr 6)).card := by
      have hsum_t : S1.card = ∑ z ∈ ({Sum.inr 1, Sum.inr 3, Sum.inr 5, Sum.inr 6} : Finset (Fin (3 * i - 1) ⊕ Fin 8)),
          (Finset.univ.filter (fun x : V => φ x = z)).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := φ) (s := S1)
          (t := {Sum.inr 1, Sum.inr 3, Sum.inr 5, Sum.inr 6})]
        · refine Finset.sum_congr rfl fun z hz => ?_
          congr 1; ext x; simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          constructor
          · exact fun h => h.2
          · intro hx; exact ⟨by rw [hx]; exact hz, hx⟩
        · intro x hx
          have := (Finset.mem_filter.mp hx).2
          simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using this
      rw [hsum_t]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq,
        Fin.reduceEq, or_self, not_false_eq_true, Finset.sum_singleton]
      ring
    dsimp only [w]
    have hltR : (5 * (S1.card : ℝ)) < 2 * (Fintype.card V : ℝ) := by exact_mod_cast hlt
    rw [hcard, Nat.cast_add, Nat.cast_add, Nat.cast_add] at hltR
    have hdiv : (5 : ℝ) * ((((Finset.univ.filter (fun x : V => φ x = Sum.inr 1)).card : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 3)).card : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 5)).card : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 6)).card : ℝ)) / (Fintype.card V : ℝ)) < 2 := by
      rw [mul_div_assoc', div_lt_iff₀ hnR]; linarith
    have heq : ((Finset.univ.filter (fun x : V => φ x = Sum.inr 1)).card : ℝ) / (Fintype.card V : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 3)).card : ℝ) / (Fintype.card V : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 5)).card : ℝ) / (Fintype.card V : ℝ) +
        ((Finset.univ.filter (fun x : V => φ x = Sum.inr 6)).card : ℝ) / (Fintype.card V : ℝ) =
        (((Finset.univ.filter (fun x : V => φ x = Sum.inr 1)).card : ℝ) +
         ((Finset.univ.filter (fun x : V => φ x = Sum.inr 3)).card : ℝ) +
         ((Finset.univ.filter (fun x : V => φ x = Sum.inr 5)).card : ℝ) +
         ((Finset.univ.filter (fun x : V => φ x = Sum.inr 6)).card : ℝ)) / (Fintype.card V : ℝ) := by ring
    rw [heq]; linarith
  -- Dispatch to H1 (i = 2) or H2 (i ≥ 3) and lift + round to an integral sparse half!
  by_cases hi2 : i = 2
  · subst hi2
    obtain ⟨s, hs01, hssum, hsquad⟩ := h1 w hw0 hwsum hav hub hvx hby hE0 hE1
    let R2 : Fin 5 ⊕ Fin 8 → Fin 5 ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q => 2 ≤ (q.val + 5 - p.val) % 5 ∧ (q.val + 5 - p.val) % 5 ≤ 3
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    have hqeq : (∑ x : Fin 5 ⊕ Fin 8, ∑ y : Fin 5 ⊕ Fin 8, if R2 x y then s x * s y else 0) =
        ∑ x : Fin 5 ⊕ Fin 8, ∑ y : Fin 5 ⊕ Fin 8,
          match x, y with
          | Sum.inl p, Sum.inl q =>
              if 2 ≤ (q.val + 5 - p.val) % 5 ∧ (q.val + 5 - p.val) % 5 ≤ 3 then s x * s y else 0
          | Sum.inl p, Sum.inr t =>
              if ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
                 ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
                 ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val) then s x * s y else 0
          | Sum.inr t, Sum.inl p =>
              if ((t.val = 0 ∨ t.val = 3) ∧ p.val < 2) ∨
                 ((t.val = 4 ∨ t.val = 1) ∧ 2 ≤ p.val ∧ p.val < 4) ∨
                 ((t.val = 2 ∨ t.val = 5) ∧ 4 ≤ p.val) then s x * s y else 0
          | Sum.inr t₁, Sum.inr t₂ =>
              if (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
                 (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
                 (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
                 (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
                 (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)) then s x * s y else 0 := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      cases x <;> cases y <;> (dsimp only [R2]; split_ifs <;> rfl)
    obtain ⟨V', hV'c, hV'e⟩ := hom_lift_fractional G R2 hn_pos φ
      (fun x y hxy => by
        have h := hφ x y hxy
        cases hfx : φ x <;> cases hfy : φ y <;> (rw [hfx, hfy] at h; exact h))
      s hs01 hssum (by rw [hqeq]; exact hsquad)
    have := hH V' hV'c
    omega
  · have hi3 : 3 ≤ i := by omega
    obtain ⟨s, hs01, hssum, hsquad⟩ := h2 i hi3 w hw0 hwsum hav hub hvx hby hE0 hE1
    let Ri : Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun x y =>
      match x, y with
      | Sum.inl p, Sum.inl q =>
          i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
          (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
      | Sum.inl p, Sum.inr t =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t, Sum.inl p =>
          ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
          ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
          ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
      | Sum.inr t₁, Sum.inr t₂ =>
          (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
          (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
          (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
          (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
          (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))
    have hqeq : (∑ x : Fin (3 * i - 1) ⊕ Fin 8, ∑ y : Fin (3 * i - 1) ⊕ Fin 8, if Ri x y then s x * s y else 0) =
        ∑ x : Fin (3 * i - 1) ⊕ Fin 8, ∑ y : Fin (3 * i - 1) ⊕ Fin 8,
          match x, y with
          | Sum.inl p, Sum.inl q =>
              if i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
                 (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1 then s x * s y else 0
          | Sum.inl p, Sum.inr t =>
              if ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
                 ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
                 ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val) then s x * s y else 0
          | Sum.inr t, Sum.inl p =>
              if ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
                 ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
                 ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val) then s x * s y else 0
          | Sum.inr t₁, Sum.inr t₂ =>
              if (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
                 (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
                 (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
                 (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
                 (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6)) then s x * s y else 0 := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      cases x <;> cases y <;> (dsimp only [Ri]; split_ifs <;> rfl)
    obtain ⟨V', hV'c, hV'e⟩ := hom_lift_fractional G Ri hn_pos φ hφ s hs01 hssum (by rw [hqeq]; exact hsquad)
    have := hH V' hV'c
    omega

end OMA.R_Erdos128_erdos_128_R2_H2_R2_H2_R1
