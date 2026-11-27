import OMAReductions.R_Erdos1013_erdos_1013_variants_lower_R1

-- Adapted from the proof of Erdos1104.erdos_1104.variants.upper by @irwincollin
-- (open-math-agents pull request 7358): the same Davies-Illingworth bound, with the
-- maximum chromatic number written inline as in this step. Only the final statement changed.

/-!
Upper bound for Erdős Problem 1104 (Davies–Illingworth 2022):
triangle-free graphs on `n` vertices have chromatic number at most `(2 + o(1)) * sqrt (n / log n)`,
proved via Bernshteyn's short proof of Molloy's theorem (`(1 + o(1)) * Δ / log Δ`)
and the Davies–Illingworth induction on `n`.
-/

namespace Erdos1104Upper

open Filter SimpleGraph
open scoped Real

noncomputable section

section LLL

private def good {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : I → Finset Ω) (T : Finset I) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ j ∈ T, ω ∉ A j)

private lemma good_empty {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] (A : I → Finset Ω) :
    good A ∅ = Finset.univ := by
  ext ω
  simp [good]

private lemma good_insert {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]
    (A : I → Finset Ω) (i : I) (T : Finset I) :
    good A (insert i T) = (good A T).filter (fun ω => ω ∉ A i) := by
  ext ω
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    forall_eq_or_imp]
  exact and_comm

private lemma good_card_split {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]
    (A : I → Finset Ω) (i : I) (T : Finset I) :
    (good A T).card = (good A (insert i T)).card + (A i ∩ good A T).card := by
  rw [good_insert]
  have hsub : A i ∩ good A T = (good A T).filter (fun ω => ω ∈ A i) := by
    ext ω
    simp [and_comm]
  rw [hsub]
  have h := Finset.card_filter_add_card_filter_not (s := good A T) (p := fun ω => ω ∈ A i)
  omega

private lemma good_antitone {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : I → Finset Ω) {T₁ T₂ : Finset I} (h : T₁ ⊆ T₂) :
    good A T₂ ⊆ good A T₁ := by
  intro ω hω
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  intro j hj
  exact hω j (h hj)

private lemma one_sub_mul_le_pow_aux (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ n : ℕ, 1 - (n : ℝ) * a ≤ (1 - a) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := one_sub_mul_le_pow_aux a ha0 ha1 n
    have hmul : (1 - (n : ℝ) * a) * (1 - a) ≤ (1 - a) ^ n * (1 - a) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have hsq : 0 ≤ (n : ℝ) * a ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg a)
    rw [pow_succ]
    push_cast
    nlinarith

private lemma lll_step_chain {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq I]
    (A : I → Finset Ω) (α : ℝ) (hα1 : α ≤ 1) (n : ℕ)
    (ih : ∀ U : Finset I, U.card < n → ∀ j ∉ U,
      ((good A U).card : ℝ) * (1 - α) ≤ ((good A (insert j U)).card : ℝ)) :
    ∀ S T₂ : Finset I, Disjoint S T₂ → (S ∪ T₂).card ≤ n →
      ((good A T₂).card : ℝ) * (1 - α) ^ S.card ≤ ((good A (S ∪ T₂)).card : ℝ) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro T₂ _ _
    simp
  | @insert x S₀ hx ihS =>
    intro T₂ hdisj hcard
    have hdisj₀ : Disjoint S₀ T₂ := hdisj.mono_left (Finset.subset_insert x S₀)
    have hxT₂ : x ∉ T₂ := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self x S₀)
    have hxU : x ∉ S₀ ∪ T₂ := by simp [hx, hxT₂]
    have hsub : S₀ ∪ T₂ ⊂ insert x S₀ ∪ T₂ := by
      rw [Finset.insert_union]
      exact Finset.ssubset_insert hxU
    have hcard₀_lt : (S₀ ∪ T₂).card < n :=
      lt_of_lt_of_le (Finset.card_lt_card hsub) hcard
    have h1 : ((good A T₂).card : ℝ) * (1 - α) ^ S₀.card ≤ ((good A (S₀ ∪ T₂)).card : ℝ) :=
      ihS T₂ hdisj₀ hcard₀_lt.le
    have h2 : ((good A (S₀ ∪ T₂)).card : ℝ) * (1 - α) ≤
        ((good A (insert x (S₀ ∪ T₂))).card : ℝ) :=
      ih (S₀ ∪ T₂) hcard₀_lt x hxU
    rw [Finset.insert_union, Finset.card_insert_of_notMem hx, pow_succ]
    calc
      ((good A T₂).card : ℝ) * ((1 - α) ^ S₀.card * (1 - α))
          = ((good A T₂).card : ℝ) * (1 - α) ^ S₀.card * (1 - α) := by ring
      _ ≤ ((good A (S₀ ∪ T₂)).card : ℝ) * (1 - α) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ ((good A (insert x (S₀ ∪ T₂))).card : ℝ) := h2

theorem lll_symmetric {Ω I : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype I] [DecidableEq I]
    [Nonempty Ω]
    (A : I → Finset Ω) (Γ : I → Finset I) (p : ℝ) (d : ℕ)
    (hp : 0 ≤ p) (hpd : 4 * p * ((d : ℝ) + 1) ≤ 1)
    (hΓ : ∀ i, (Γ i).card ≤ d)
    (hlop : ∀ i : I, ∀ T : Finset I, i ∉ T → (∀ j ∈ T, j ∉ Γ i) →
      ((A i ∩ good A T).card : ℝ) ≤ p * ((good A T).card : ℝ)) :
    ∃ ω : Ω, ∀ i : I, ω ∉ A i := by
  have hp4 : 4 * p ≤ 1 := by
    have hd0 : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) d]
    nlinarith
  have h2p0 : 0 ≤ 2 * p := by linarith
  have h2p1 : 2 * p ≤ 1 := by linarith
  have hmain : ∀ n : ℕ, ∀ T : Finset I, T.card ≤ n → ∀ i ∉ T,
      ((good A T).card : ℝ) * (1 - 2 * p) ≤ ((good A (insert i T)).card : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hTn i hiT
      let S₁ : Finset I := T ∩ Γ i
      let S₂ : Finset I := T \ Γ i
      have hT_eq : S₁ ∪ S₂ = T := by
        ext x
        simp only [S₁, S₂, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      have hdisj : Disjoint S₁ S₂ := disjoint_sdiff_self_right.mono_left Finset.inter_subset_right
      have hS₁_le : S₁.card ≤ d :=
        (Finset.card_le_card Finset.inter_subset_right).trans (hΓ i)
      have hiS₂ : i ∉ S₂ := fun h => hiT (Finset.sdiff_subset h)
      have hS₂_Γ : ∀ j ∈ S₂, j ∉ Γ i := fun j hj => (Finset.mem_sdiff.mp hj).2
      have hbad_le : ((A i ∩ good A T).card : ℝ) ≤ p * ((good A S₂).card : ℝ) := by
        have hsub : A i ∩ good A T ⊆ A i ∩ good A S₂ :=
          Finset.inter_subset_inter_left (good_antitone A Finset.sdiff_subset)
        have h1 : ((A i ∩ good A T).card : ℝ) ≤ ((A i ∩ good A S₂).card : ℝ) :=
          Nat.cast_le.mpr (Finset.card_le_card hsub)
        exact h1.trans (hlop i S₂ hiS₂ hS₂_Γ)
      have hgood_ge : (1 / 2 : ℝ) * ((good A S₂).card : ℝ) ≤ ((good A T).card : ℝ) := by
        have hih : ∀ U : Finset I, U.card < n → ∀ j ∉ U,
            ((good A U).card : ℝ) * (1 - 2 * p) ≤ ((good A (insert j U)).card : ℝ) :=
          fun U hU => ih U.card hU U le_rfl
        have hchain := lll_step_chain A (2 * p) h2p1 n hih S₁ S₂ hdisj
          (by rw [hT_eq]; exact hTn)
        rw [hT_eq] at hchain
        have hpow_ge : (1 / 2 : ℝ) ≤ (1 - 2 * p) ^ S₁.card := by
          rcases Nat.eq_zero_or_pos S₁.card with h0 | hpos
          · rw [h0, pow_zero]
            norm_num
          · have hpow_mono : (1 - 2 * p) ^ d ≤ (1 - 2 * p) ^ S₁.card :=
              pow_le_pow_of_le_one (by linarith) (by linarith) hS₁_le
            have hbern := one_sub_mul_le_pow_aux (2 * p) h2p0 h2p1 d
            have h4pd : 4 * p * (d : ℝ) ≤ 1 := by
              nlinarith [Nat.cast_nonneg (α := ℝ) d]
            linarith
        calc
          (1 / 2 : ℝ) * ((good A S₂).card : ℝ)
              ≤ (1 - 2 * p) ^ S₁.card * ((good A S₂).card : ℝ) :=
                mul_le_mul_of_nonneg_right hpow_ge (Nat.cast_nonneg _)
          _ = ((good A S₂).card : ℝ) * (1 - 2 * p) ^ S₁.card := mul_comm _ _
          _ ≤ ((good A T).card : ℝ) := hchain
      have hbad_T : ((A i ∩ good A T).card : ℝ) ≤ 2 * p * ((good A T).card : ℝ) := by
        linarith [mul_le_mul_of_nonneg_left hgood_ge (by linarith : 0 ≤ 2 * p)]
      have hsplit : ((good A T).card : ℝ) =
          ((good A (insert i T)).card : ℝ) + ((A i ∩ good A T).card : ℝ) := by
        exact_mod_cast good_card_split A i T
      linarith
  have hpos_all : ∀ S : Finset I, 0 < (good A S).card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [good_empty, Finset.card_univ]
      exact Fintype.card_pos
    | @insert i S hi ih =>
      have hstep := hmain S.card S le_rfl i hi
      have hS_pos : (0 : ℝ) < (good A S).card := Nat.cast_pos.mpr ih
      have h12p : (0 : ℝ) < 1 - 2 * p := by linarith
      have hins : (0 : ℝ) < (good A (insert i S)).card :=
        lt_of_lt_of_le (mul_pos hS_pos h12p) hstep
      exact Nat.cast_pos.mp hins
  obtain ⟨ω, hω⟩ := Finset.card_pos.mp (hpos_all Finset.univ)
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hω
  exact ⟨ω, fun i => hω i trivial⟩

end LLL

section ListColoring

theorem list_colorable_of_small_deg {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : V → Finset C) (ℓ colorDeg : ℕ)
    (hℓ4 : 4 ≤ ℓ) (hL : ∀ v, ℓ ≤ (L v).card) (hdeg : 32 * colorDeg ≤ ℓ)
    (hcdeg : ∀ v : V, ∀ c ∈ L v,
      (Finset.univ.filter (fun w => G.Adj v w ∧ c ∈ L w)).card ≤ colorDeg) :
    ∃ f : V → C, (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v) := by
  choose L' hL'sub hL'card using fun v => Finset.exists_subset_card_eq (hL v)
  let α := fun v : V => {c : C // c ∈ L' v}
  have : ∀ v, Nonempty (α v) := fun v => by
    have hpos : 0 < (L' v).card := by rw [hL'card v]; omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    exact ⟨⟨c, hc⟩⟩
  let Ω := ∀ v : V, α v
  let I := {p : V × V × C // G.Adj p.1 p.2.1 ∧ p.2.2 ∈ L' p.1 ∧ p.2.2 ∈ L' p.2.1}
  let A : I → Finset Ω := fun i =>
    Finset.univ.filter (fun ω : Ω => (ω i.1.1).1 = i.1.2.2 ∧ (ω i.1.2.1).1 = i.1.2.2)
  let Γ : I → Finset I := fun i =>
    Finset.univ.filter (fun j : I => j ≠ i ∧
      (j.1.1 = i.1.1 ∨ j.1.1 = i.1.2.1 ∨ j.1.2.1 = i.1.1 ∨ j.1.2.1 = i.1.2.1))
  have hℓpos : 0 < (ℓ : ℝ) := by positivity
  have hpd : 4 * (1 / (ℓ : ℝ) ^ 2) * ((4 * ℓ * colorDeg : ℕ) + 1 : ℝ) ≤ 1 := by
    have h1 : (ℓ : ℝ) ≥ 4 := by exact_mod_cast hℓ4
    have h2 : 32 * (colorDeg : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hdeg
    have h3 : ((4 * ℓ * colorDeg : ℕ) : ℝ) = 4 * (ℓ : ℝ) * (colorDeg : ℝ) := by push_cast; ring
    rw [h3]
    have h4 : 4 * (1 / (ℓ : ℝ) ^ 2) * (4 * (ℓ : ℝ) * (colorDeg : ℝ) + 1)
        = (16 * (ℓ : ℝ) * (colorDeg : ℝ) + 4) / (ℓ : ℝ) ^ 2 := by ring
    rw [h4, div_le_one (sq_pos_of_pos hℓpos)]
    nlinarith
  have hΓ_card : ∀ i : I, (Γ i).card ≤ 4 * ℓ * colorDeg := by
    intro i
    let atVertex : V → Finset I := fun x =>
      Finset.univ.filter (fun j : I => j.1.1 = x)
    let intoVertex : V → Finset I := fun x =>
      Finset.univ.filter (fun j : I => j.1.2.1 = x)
    have h_at : ∀ x : V, (atVertex x).card ≤ ℓ * colorDeg := by
      intro x
      let tgt : Finset (C × V) := (L' x).biUnion (fun c =>
        (Finset.univ.filter (fun w => G.Adj x w ∧ c ∈ L w)).image (fun w => (c, w)))
      have hinj : Set.MapsTo (fun j : I => (j.1.2.2, j.1.2.1)) (atVertex x) tgt := by
        intro j hj
        simp only [atVertex, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [tgt, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
          Finset.mem_univ, true_and]
        refine ⟨j.1.2.2, ?_, j.1.2.1, ⟨?_, hL'sub _ j.2.2.2⟩, rfl⟩
        · rw [← hj]; exact j.2.2.1
        · rw [← hj]; exact j.2.1
      have hcard_inj : (atVertex x).card ≤ tgt.card := by
        apply Finset.card_le_card_of_injOn (fun j : I => (j.1.2.2, j.1.2.1)) hinj
        intro j₁ hj₁ j₂ hj₂ heq
        simp only [atVertex, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
        ext
        · exact hj₁.trans hj₂.symm
        · exact congrArg Prod.snd heq
        · exact congrArg Prod.fst heq
      have htgt : tgt.card ≤ ℓ * colorDeg := by
        calc tgt.card
            ≤ ∑ c ∈ L' x,
                ((Finset.univ.filter (fun w => G.Adj x w ∧ c ∈ L w)).image (fun w => (c, w))).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ c ∈ L' x, (Finset.univ.filter (fun w => G.Adj x w ∧ c ∈ L w)).card := by
              gcongr; exact Finset.card_image_le
          _ ≤ ∑ _c ∈ L' x, colorDeg := by
              gcongr with c hc
              exact hcdeg x c (hL'sub x hc)
          _ = (L' x).card * colorDeg := Finset.sum_const_nat (fun _ _ => rfl)
          _ = ℓ * colorDeg := by rw [hL'card x]
      exact hcard_inj.trans htgt
    have h_into : ∀ x : V, (intoVertex x).card ≤ ℓ * colorDeg := by
      intro x
      have hswap : (intoVertex x).card ≤ (atVertex x).card := by
        apply Finset.card_le_card_of_injOn
          (fun j : I => ⟨(j.1.2.1, j.1.1, j.1.2.2), j.2.1.symm, j.2.2.2, j.2.2.1⟩)
        · intro j hj
          simp only [intoVertex, atVertex, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
            true_and] at hj ⊢
          exact hj
        · intro j₁ _ j₂ _ heq
          have h1 := congrArg (fun k : I => k.1.1) heq
          have h2 := congrArg (fun k : I => k.1.2.1) heq
          have h3 := congrArg (fun k : I => k.1.2.2) heq
          ext <;> [exact h2; exact h1; exact h3]
      exact hswap.trans (h_at x)
    have hsub : Γ i ⊆ atVertex i.1.1 ∪ atVertex i.1.2.1 ∪ intoVertex i.1.1 ∪ intoVertex i.1.2.1 := by
      intro j hj
      simp only [Γ, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_union, atVertex, intoVertex, Finset.mem_filter, Finset.mem_univ,
        true_and]
      tauto
    calc (Γ i).card
        ≤ (atVertex i.1.1 ∪ atVertex i.1.2.1 ∪ intoVertex i.1.1 ∪ intoVertex i.1.2.1).card :=
          Finset.card_le_card hsub
      _ ≤ (atVertex i.1.1).card + (atVertex i.1.2.1).card +
            (intoVertex i.1.1).card + (intoVertex i.1.2.1).card := by
          have h1 := Finset.card_union_le (atVertex i.1.1 ∪ atVertex i.1.2.1 ∪ intoVertex i.1.1)
            (intoVertex i.1.2.1)
          have h2 := Finset.card_union_le (atVertex i.1.1 ∪ atVertex i.1.2.1) (intoVertex i.1.1)
          have h3 := Finset.card_union_le (atVertex i.1.1) (atVertex i.1.2.1)
          omega
      _ ≤ ℓ * colorDeg + ℓ * colorDeg + ℓ * colorDeg + ℓ * colorDeg := by
          gcongr <;> [exact h_at _; exact h_at _; exact h_into _; exact h_into _]
      _ = 4 * ℓ * colorDeg := by ring
  have hlop : ∀ i : I, ∀ T : Finset I, i ∉ T → (∀ j ∈ T, j ∉ Γ i) →
      ((A i ∩ good A T).card : ℝ) ≤ (1 / (ℓ : ℝ) ^ 2) * ((good A T).card : ℝ) := by
    intro i T hiT hTΓ
    let u := i.1.1
    let v := i.1.2.1
    let c := i.1.2.2
    have huv : u ≠ v := i.2.1.ne
    let W := {w : V // w ≠ u ∧ w ≠ v}
    let ΩW := ∀ w : W, α w.1
    let goodW : Finset ΩW := Finset.univ.filter (fun ωW =>
      ∀ j ∈ T, ∀ hju : j.1.1 ≠ u, ∀ hjv : j.1.1 ≠ v, ∀ hju2 : j.1.2.1 ≠ u, ∀ hjv2 : j.1.2.1 ≠ v,
        ¬ ((ωW ⟨j.1.1, hju, hjv⟩).1 = j.1.2.2 ∧ (ωW ⟨j.1.2.1, hju2, hjv2⟩).1 = j.1.2.2))
    have hT_disj : ∀ j ∈ T, j.1.1 ≠ u ∧ j.1.1 ≠ v ∧ j.1.2.1 ≠ u ∧ j.1.2.1 ≠ v := by
      intro j hjT
      have hne : j ≠ i := fun h => hiT (h ▸ hjT)
      have hnΓ : j ∉ Γ i := hTΓ j hjT
      simp only [Γ, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_or] at hnΓ
      exact hnΓ hne
    let e : Ω ≃ α u × α v × ΩW :=
      { toFun := fun ω => (ω u, ω v, fun w => ω w.1)
        invFun := fun ⟨xu, xv, ωW⟩ w =>
          if hwu : w = u then hwu ▸ xu
          else if hwv : w = v then hwv ▸ xv
          else ωW ⟨w, hwu, hwv⟩
        left_inv := fun ω => by
          funext w
          by_cases hwu : w = u
          · subst hwu; simp
          · by_cases hwv : w = v
            · subst hwv; simp [hwu]
            · simp [hwu, hwv]
        right_inv := fun ⟨xu, xv, ωW⟩ => by
          refine Prod.ext (by simp) (Prod.ext (by simp [huv.symm]) ?_)
          funext ⟨w, hwu, hwv⟩
          simp [hwu, hwv] }
    have hgood_iff : ∀ ω : Ω, ω ∈ good A T ↔ (e ω).2.2 ∈ goodW := by
      intro ω
      simp only [good, goodW, A, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp only [e]
      constructor
      · intro h j hjT _ _ _ _ hpair
        exact h j hjT hpair
      · intro h j hjT hpair
        obtain ⟨h1, h2, h3, h4⟩ := hT_disj j hjT
        exact h j hjT h1 h2 h3 h4 hpair
    have hA_iff : ∀ ω : Ω, ω ∈ A i ∩ good A T ↔
        ((e ω).1.1 = c ∧ (e ω).2.1.1 = c ∧ (e ω).2.2 ∈ goodW) := by
      intro ω
      rw [Finset.mem_inter, hgood_iff]
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, e]
      tauto
    have hcard_good : (good A T).card = ℓ * ℓ * goodW.card := by
      have h1 : (good A T).card =
          (Finset.univ.filter (fun p : α u × α v × ΩW => p.2.2 ∈ goodW)).card := by
        refine Finset.card_bij (fun ω _ => e ω) ?_ ?_ ?_
        · intro ω hω; simpa [hgood_iff] using hω
        · intro ω₁ _ ω₂ _ heq; exact e.injective heq
        · intro p hp
          refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
          rw [hgood_iff, e.apply_symm_apply]
          simpa using hp
      have h2 : Finset.univ.filter (fun p : α u × α v × ΩW => p.2.2 ∈ goodW) =
          (Finset.univ : Finset (α u)) ×ˢ ((Finset.univ : Finset (α v)) ×ˢ goodW) := by
        ext ⟨xu, xv, ωW⟩
        simp
      rw [h1, h2, Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
        Fintype.card_coe, Fintype.card_coe, hL'card u, hL'card v, mul_assoc]
    have hcard_bad : (A i ∩ good A T).card = goodW.card := by
      have hcu : (Finset.univ.filter (fun x : α u => x.1 = c)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨⟨c, i.2.2.1⟩, ?_⟩
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      have hcv : (Finset.univ.filter (fun x : α v => x.1 = c)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨⟨c, i.2.2.2⟩, ?_⟩
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      have h1 : (A i ∩ good A T).card =
          (Finset.univ.filter (fun p : α u × α v × ΩW =>
            p.1.1 = c ∧ p.2.1.1 = c ∧ p.2.2 ∈ goodW)).card := by
        refine Finset.card_bij (fun ω _ => e ω) ?_ ?_ ?_
        · intro ω hω; simpa [hA_iff] using hω
        · intro ω₁ _ ω₂ _ heq; exact e.injective heq
        · intro p hp
          refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
          rw [hA_iff, e.apply_symm_apply]
          simpa using hp
      have h2 : Finset.univ.filter (fun p : α u × α v × ΩW =>
            p.1.1 = c ∧ p.2.1.1 = c ∧ p.2.2 ∈ goodW) =
          (Finset.univ.filter (fun x : α u => x.1 = c)) ×ˢ
            ((Finset.univ.filter (fun x : α v => x.1 = c)) ×ˢ goodW) := by
        ext ⟨xu, xv, ωW⟩
        simp
      rw [h1, h2, Finset.card_product, Finset.card_product, hcu, hcv, one_mul, one_mul]
    rw [hcard_bad, hcard_good]
    push_cast
    rw [one_div_mul_eq_div, le_div_iff₀ (sq_pos_of_pos hℓpos)]
    ring_nf
    exact le_rfl
  obtain ⟨ω, hω⟩ := lll_symmetric A Γ (1 / (ℓ : ℝ) ^ 2) (4 * ℓ * colorDeg)
    (by positivity) hpd hΓ_card hlop
  refine ⟨fun v => (ω v).1, fun v => hL'sub v (ω v).2, ?_⟩
  intro u v huv heq
  dsimp only at heq
  have hv2 : (ω u).1 ∈ L' v := by rw [heq]; exact (ω v).2
  have hi := hω ⟨(u, v, (ω u).1), huv, (ω u).2, hv2⟩
  exact hi (by simp [A, heq])

end ListColoring

section Concentration

private def validPart {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (A : S → Finset C) : Finset (S → Option C) :=
  Finset.univ.filter (fun ω => ∀ s c, ω s = some c → c ∈ A s)

private lemma validPart_card {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (A : S → Finset C) :
    (validPart A).card = ∏ s : S, ((A s).card + 1) := by
  let optA (s : S) : Finset (Option C) := insert none ((A s).image some)
  have heq : validPart A = Fintype.piFinset optA := by
    ext ω
    simp only [validPart, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      optA, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro h s
      cases hs : ω s with
      | none => left; rfl
      | some c => right; exact ⟨c, h s c hs, rfl⟩
    · intro h s c hsc
      rcases h s with h0 | ⟨d, hd, hdeq⟩
      · simp [hsc] at h0
      · rw [hsc] at hdeq
        cases hdeq
        exact hd
  rw [heq, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hnot : none ∉ (A s).image some := by simp
  dsimp only [optA]
  rw [Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injective _ (Option.some_injective C), add_comm]

private lemma validPart_card_pos {S C : Type*} [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C] (A : S → Finset C) :
    0 < (validPart A).card := by
  rw [validPart_card]
  exact Finset.prod_pos fun _ _ => Nat.succ_pos _

theorem chernoff_upper_indep {S C : Type*} [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (A : S → Finset C) (t μ : ℝ)
    (hμ : ∑ s : S, (1 : ℝ) / ((A s).card + 1 : ℝ) ≤ μ) :
    (((validPart A).filter (fun ω =>
        t ≤ ((Finset.univ.filter (fun s : S => ω s = none)).card : ℝ))).card : ℝ)
      ≤ Real.exp (μ - Real.log 2 * t) * ((validPart A).card : ℝ) := by
  let X : (S → Option C) → ℕ := fun ω => (Finset.univ.filter (fun s : S => ω s = none)).card
  let optA (s : S) : Finset (Option C) := insert none ((A s).image some)
  have hpi : validPart A = Fintype.piFinset optA := by
    ext ω
    simp only [validPart, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      optA, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro h s
      cases hs : ω s with
      | none => left; rfl
      | some c => right; exact ⟨c, h s c hs, rfl⟩
    · intro h s c hsc
      rcases h s with h0 | ⟨d, hd, hdeq⟩
      · simp [hsc] at h0
      · rw [hsc] at hdeq
        cases hdeq
        exact hd
  have hexp_sum : ∑ ω ∈ validPart A, (2 : ℝ) ^ (X ω) =
      ∏ s : S, (((A s).card : ℝ) + 2) := by
    have hterm : ∀ ω : S → Option C, (2 : ℝ) ^ (X ω) =
        ∏ s : S, if ω s = none then (2 : ℝ) else 1 := by
      intro ω
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    simp_rw [hterm, hpi]
    rw [← Finset.prod_univ_sum optA (fun _ x => if x = none then (2 : ℝ) else 1)]
    refine Finset.prod_congr rfl fun s _ => ?_
    have hnot : none ∉ (A s).image some := by simp
    dsimp only [optA]
    rw [Finset.sum_insert hnot]
    simp only [↓reduceIte]
    have hs2 : ∑ x ∈ (A s).image some, (if x = none then (2 : ℝ) else (1 : ℝ)) =
        ((A s).card : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ h => Option.some_injective C h)]
      simp
    linarith
  have hprod_bound : (∏ s : S, (((A s).card : ℝ) + 2)) ≤
      Real.exp μ * ((validPart A).card : ℝ) := by
    have hcardΩ : ((validPart A).card : ℝ) = ∏ s : S, (((A s).card : ℝ) + 1) := by
      rw [validPart_card]
      push_cast
      rfl
    have hfac : (∏ s : S, (((A s).card : ℝ) + 2)) =
        (∏ s : S, (1 + (1 : ℝ) / ((A s).card + 1 : ℝ))) *
          (∏ s : S, (((A s).card : ℝ) + 1)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun s _ => ?_
      have hpos : (0 : ℝ) < ((A s).card : ℝ) + 1 := by positivity
      field_simp
      ring
    have hexp_prod : (∏ s : S, (1 + (1 : ℝ) / ((A s).card + 1 : ℝ))) ≤ Real.exp μ := by
      calc (∏ s : S, (1 + (1 : ℝ) / ((A s).card + 1 : ℝ)))
          ≤ ∏ s : S, Real.exp ((1 : ℝ) / ((A s).card + 1 : ℝ)) := by
            refine Finset.prod_le_prod (fun s _ => by positivity) fun s _ => ?_
            linarith [Real.add_one_le_exp ((1 : ℝ) / ((A s).card + 1 : ℝ))]
        _ = Real.exp (∑ s : S, (1 : ℝ) / ((A s).card + 1 : ℝ)) := by
            rw [Real.exp_sum]
        _ ≤ Real.exp μ := Real.exp_le_exp.mpr hμ
    rw [hfac, hcardΩ]
    exact mul_le_mul_of_nonneg_right hexp_prod
      (Finset.prod_nonneg fun s _ => Nat.cast_add_one_pos ((A s).card) |>.le)
  have hmarkov : (2 : ℝ) ^ t *
      (((validPart A).filter (fun ω => t ≤ (X ω : ℝ))).card : ℝ) ≤
      ∑ ω ∈ validPart A, (2 : ℝ) ^ (X ω) := by
    calc (2 : ℝ) ^ t * (((validPart A).filter (fun ω => t ≤ (X ω : ℝ))).card : ℝ)
        = ∑ _ω ∈ (validPart A).filter (fun ω => t ≤ (X ω : ℝ)), (2 : ℝ) ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ ω ∈ (validPart A).filter (fun ω => t ≤ (X ω : ℝ)), (2 : ℝ) ^ (X ω) := by
          refine Finset.sum_le_sum fun ω hω => ?_
          simp only [Finset.mem_filter] at hω
          have hpow : (2 : ℝ) ^ (X ω) = (2 : ℝ) ^ (X ω : ℝ) := (Real.rpow_natCast 2 (X ω)).symm
          rw [hpow]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hω.2
      _ ≤ ∑ ω ∈ validPart A, (2 : ℝ) ^ (X ω) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
  have hrpow : (2 : ℝ) ^ t = Real.exp (Real.log 2 * t) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  have hrpow_pos : (0 : ℝ) < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hsum_le : ∑ ω ∈ validPart A, (2 : ℝ) ^ (X ω) ≤
      Real.exp μ * ((validPart A).card : ℝ) := by
    rw [hexp_sum]
    exact hprod_bound
  have h1 : (2 : ℝ) ^ t *
      (((validPart A).filter (fun ω => t ≤ (X ω : ℝ))).card : ℝ) ≤
      Real.exp μ * ((validPart A).card : ℝ) := hmarkov.trans hsum_le
  have hdiv : (((validPart A).filter (fun ω => t ≤ (X ω : ℝ))).card : ℝ) ≤
      Real.exp μ * ((validPart A).card : ℝ) / (2 : ℝ) ^ t :=
    (le_div_iff₀' hrpow_pos).mpr h1
  calc (((validPart A).filter (fun ω => t ≤ (X ω : ℝ))).card : ℝ)
      ≤ Real.exp μ * ((validPart A).card : ℝ) / (2 : ℝ) ^ t := hdiv
    _ = (Real.exp μ / Real.exp (Real.log 2 * t)) * ((validPart A).card : ℝ) := by
        rw [hrpow]; ring
    _ = Real.exp (μ - Real.log 2 * t) * ((validPart A).card : ℝ) := by
        rw [Real.exp_sub]

private def availColors {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (ω : S → Option C) : Finset C :=
  Finset.univ.filter (fun c : C => ∀ s : S, ω s ≠ some c)

private def blockedColors {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (ω : S → Option C) : Finset C :=
  Finset.univ.filter (fun c : C => ∃ s : S, ω s = some c)

private lemma avail_card_add_blocked_card {S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]
    (ω : S → Option C) :
    (availColors ω).card + (blockedColors ω).card = Fintype.card C := by
  have hcompl : blockedColors ω = Finset.univ \ availColors ω := by
    ext c
    simp [blockedColors, availColors]
  rw [hcompl, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  have hle := Finset.card_le_univ (availColors ω)
  omega

private def hitCount {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (A : S → Finset C) (T : Finset C) : ℕ :=
  ((validPart A).filter (fun ω => ∀ c ∈ T, ∃ s : S, ω s = some c)).card

private lemma hitCount_mono_erase {S C : Type*} [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (A : S → Finset C) (T : Finset C) (x : C) (hx : x ∉ T) (s₀ : S) :
    let A' := fun s : S => if s = s₀ then (A s₀).erase x else A s
    (hitCount A T : ℝ) * ((A' s₀).card + 1 : ℝ) ≤
      (hitCount A' T : ℝ) * ((A s₀).card + 1 : ℝ) := by
  intro A'
  let S' := {s : S // s ≠ s₀}
  let validS' : Finset (S' → Option C) :=
    Finset.univ.filter (fun ω' => ∀ s : S', ∀ c, ω' s = some c → c ∈ A s.1)
  let e : (S → Option C) ≃ Option C × (S' → Option C) :=
    { toFun := fun ω => (ω s₀, fun s => ω s.1)
      invFun := fun ⟨y, ω'⟩ s => if h : s = s₀ then y else ω' ⟨s, h⟩
      left_inv := fun ω => by
        funext s
        by_cases h : s = s₀
        · subst h; simp
        · simp [h]
      right_inv := fun ⟨y, ω'⟩ => by
        refine Prod.ext (by simp) ?_
        funext s
        simp only [s.2, ↓reduceDIte]
        exact congrArg (fun u : S' => ω' u) (Subtype.ext rfl) }
  let rem (ω' : S' → Option C) : Finset C :=
    T.filter (fun c => ¬ ∃ s : S', ω' s = some c)
  have hgood_iff : ∀ (B : S → Finset C) (hB : ∀ s : S', B s.1 = A s.1)
      (y : Option C) (ω' : S' → Option C),
      (e.symm (y, ω') ∈ validPart B ∧ ∀ c ∈ T, ∃ s : S, e.symm (y, ω') s = some c) ↔
      ((∀ c, y = some c → c ∈ B s₀) ∧ ω' ∈ validS' ∧
        ∀ c ∈ rem ω', y = some c) := by
    intro B hB y ω'
    simp only [validPart, validS', Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hv, ht⟩
      refine ⟨?_, ?_, ?_⟩
      · intro c hy
        have h := hv s₀ c
        dsimp only [e] at h
        exact h (by simpa using hy)
      · intro s c hsc
        have h := hv s.1 c
        dsimp only [e] at h
        rw [← hB s]
        exact h (by simpa [s.2] using hsc)
      · intro c hc
        simp only [rem, Finset.mem_filter] at hc
        obtain ⟨s, hs⟩ := ht c hc.1
        by_cases hss₀ : s = s₀
        · subst hss₀
          simpa [e] using hs
        · exfalso
          apply hc.2
          refine ⟨⟨s, hss₀⟩, ?_⟩
          simpa [e, hss₀] using hs
    · rintro ⟨hy, hv', hrem⟩
      refine ⟨?_, ?_⟩
      · intro s c hsc
        by_cases hss₀ : s = s₀
        · subst hss₀
          apply hy
          simpa [e] using hsc
        · rw [hB ⟨s, hss₀⟩]
          apply hv' ⟨s, hss₀⟩ c
          simpa [e, hss₀] using hsc
      · intro c hcT
        by_cases hex : ∃ s : S', ω' s = some c
        · obtain ⟨s, hs⟩ := hex
          refine ⟨s.1, ?_⟩
          simpa [e, s.2] using hs
        · refine ⟨s₀, ?_⟩
          have heq := hrem c (Finset.mem_filter.mpr ⟨hcT, hex⟩)
          simpa [e] using heq
  let fib (B0 : Finset C) (ω' : S' → Option C) : ℕ :=
    (Finset.univ.filter (fun y : Option C =>
      (∀ c, y = some c → c ∈ B0) ∧ ∀ c ∈ rem ω', y = some c)).card
  have hsum : ∀ (B : S → Finset C) (hB : ∀ s : S', B s.1 = A s.1),
      hitCount B T = ∑ ω' ∈ validS', fib (B s₀) ω' := by
    intro B hB
    have hbij : hitCount B T =
        (Finset.univ.filter (fun p : Option C × (S' → Option C) =>
          (∀ c, p.1 = some c → c ∈ B s₀) ∧ p.2 ∈ validS' ∧ ∀ c ∈ rem p.2, p.1 = some c)).card := by
      refine Finset.card_bij (fun ω _ => e ω) ?_ ?_ ?_
      · intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        rw [← hgood_iff B hB (e ω).1 (e ω).2, e.symm_apply_apply]
        exact hω
      · intro ω₁ _ ω₂ _ heq; exact e.injective heq
      · intro p hp
        refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rwa [hgood_iff B hB p.1 p.2]
    rw [hbij]
    have hprod : Finset.univ.filter (fun p : Option C × (S' → Option C) =>
          (∀ c, p.1 = some c → c ∈ B s₀) ∧ p.2 ∈ validS' ∧ ∀ c ∈ rem p.2, p.1 = some c) =
        (validS'.sigma (fun ω' => Finset.univ.filter (fun y : Option C =>
          (∀ c, y = some c → c ∈ B s₀) ∧ ∀ c ∈ rem ω', y = some c))).map
          ⟨fun ⟨ω', y⟩ => (y, ω'), fun ⟨ω₁, y₁⟩ ⟨ω₂, y₂⟩ h => by cases h; rfl⟩ := by
      ext ⟨y, ω'⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_sigma]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨ω', y⟩, ⟨h2, h1, h3⟩, rfl⟩
      · rintro ⟨⟨ω₁, y₁⟩, ⟨h1, h2, h3⟩, heq⟩; cases heq; exact ⟨h2, h1, h3⟩
    rw [hprod, Finset.card_map, Finset.card_sigma]
  have hB_A : ∀ s : S', A s.1 = A s.1 := fun _ => rfl
  have hB_A' : ∀ s : S', A' s.1 = A s.1 := fun s => by simp [A', s.2]
  rw [hsum A hB_A, hsum A' hB_A']
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun ω' _ => ?_
  by_cases h0 : rem ω' = ∅
  · have hfib : ∀ B0 : Finset C, fib B0 ω' = B0.card + 1 := by
      intro B0
      have hset : Finset.univ.filter (fun y : Option C =>
            (∀ c, y = some c → c ∈ B0) ∧ ∀ c ∈ rem ω', y = some c) =
          insert none (B0.image some) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, h0, Finset.notMem_empty,
          IsEmpty.forall_iff, implies_true, and_true, Finset.mem_insert, Finset.mem_image]
        cases y with
        | none => simp
        | some c => simp
      have hnot : none ∉ B0.image some := by simp
      dsimp only [fib]
      rw [hset, Finset.card_insert_of_notMem hnot,
        Finset.card_image_of_injective _ (Option.some_injective C), add_comm]
    rw [hfib (A s₀), hfib (A' s₀)]
    push_cast
    ring_nf
    exact le_rfl
  · obtain ⟨c₀, hc₀⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have hc₀T : c₀ ∈ T := (Finset.mem_filter.mp hc₀).1
    have hc₀_nex : c₀ ≠ x := fun h => hx (h ▸ hc₀T)
    by_cases h1 : ∀ c ∈ rem ω', c = c₀
    · by_cases hc₀A : c₀ ∈ A s₀
      · have hc₀A' : c₀ ∈ A' s₀ := by
          simp only [A', ↓reduceIte, Finset.mem_erase]
          exact ⟨hc₀_nex, hc₀A⟩
        have hfib1 : ∀ B0 : Finset C, c₀ ∈ B0 → fib B0 ω' = 1 := by
          intro B0 hcB
          dsimp only [fib]
          rw [Finset.card_eq_one]
          refine ⟨some c₀, ?_⟩
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨_, hy⟩; exact hy c₀ hc₀
          · rintro rfl
            refine ⟨fun c hc => ?_, fun c hc => ?_⟩
            · cases hc; exact hcB
            · rw [h1 c hc]
        rw [hfib1 (A s₀) hc₀A, hfib1 (A' s₀) hc₀A']
        push_cast
        have hle : (A' s₀).card ≤ (A s₀).card := by
          simp only [A', ↓reduceIte]
          exact Finset.card_erase_le
        gcongr
      · have hfib0 : fib (A s₀) ω' = 0 := by
          dsimp only [fib]
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro y _ ⟨hmem, hy⟩
          exact hc₀A (hmem c₀ (hy c₀ hc₀))
        rw [hfib0]
        simp only [Nat.cast_zero, zero_mul]
        positivity
    · push Not at h1
      obtain ⟨c₁, hc₁, hc₁ne⟩ := h1
      have hfib0 : fib (A s₀) ω' = 0 := by
        dsimp only [fib]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro y _ ⟨_, hy⟩
        have h_eq := (hy c₀ hc₀).symm.trans (hy c₁ hc₁)
        simp only [Option.some.injEq] at h_eq
        exact hc₁ne h_eq.symm
      rw [hfib0]
      simp only [Nat.cast_zero, zero_mul]
      positivity

private lemma hitProb_erase_all {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (A : S → Finset C) (T : Finset C) (x : C) (hx : x ∉ T) :
    ((hitCount A T : ℝ) / ((validPart A).card : ℝ)) ≤
      ((hitCount (fun s => (A s).erase x) T : ℝ) /
        ((validPart (fun s => (A s).erase x)).card : ℝ)) := by
  have hU : ∀ U : Finset S, ∀ A₀ : S → Finset C,
      ((hitCount A₀ T : ℝ) / ((validPart A₀).card : ℝ)) ≤
        ((hitCount (fun s => if s ∈ U then (A₀ s).erase x else A₀ s) T : ℝ) /
          ((validPart (fun s => if s ∈ U then (A₀ s).erase x else A₀ s)).card : ℝ)) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro A₀
      simp
    | @insert s₀ U₀ hs₀ ih =>
      intro A₀
      have hstep1 := ih A₀
      let A₁ := fun s : S => if s ∈ U₀ then (A₀ s).erase x else A₀ s
      have hA_eq : (fun s : S => if s ∈ insert s₀ U₀ then (A₀ s).erase x else A₀ s) =
          (fun s : S => if s = s₀ then (A₁ s₀).erase x else A₁ s) := by
        funext s
        by_cases h1 : s = s₀
        · subst h1; simp [A₁, hs₀]
        · simp [A₁, h1]
      rw [hA_eq]
      refine hstep1.trans ?_
      let A₂ := fun s : S => if s = s₀ then (A₁ s₀).erase x else A₁ s
      have hm := hitCount_mono_erase A₁ T x hx s₀
      have hfac : ∀ B : S → Finset C,
          ((validPart B).card : ℝ) =
            ((B s₀).card + 1 : ℝ) *
              (∏ s ∈ (Finset.univ : Finset S).erase s₀, ((B s).card + 1 : ℝ)) := by
        intro B
        rw [validPart_card]
        push_cast
        have hmul := Finset.mul_prod_erase (Finset.univ : Finset S)
          (fun s : S => ((B s).card + 1 : ℝ)) (Finset.mem_univ s₀)
        exact hmul.symm
      let rest := ∏ s ∈ (Finset.univ : Finset S).erase s₀, ((A₁ s).card + 1 : ℝ)
      have hrest_eq : (∏ s ∈ (Finset.univ : Finset S).erase s₀, ((A₂ s).card + 1 : ℝ)) = rest := by
        refine Finset.prod_congr rfl fun s hs => ?_
        have hne : s ≠ s₀ := (Finset.mem_erase.mp hs).1
        simp [A₂, hne]
      have hden1 : 0 < ((A₁ s₀).card + 1 : ℝ) := Nat.cast_add_one_pos _
      have hden2 : 0 < ((A₂ s₀).card + 1 : ℝ) := Nat.cast_add_one_pos _
      have hrest_pos : 0 < rest := Finset.prod_pos fun s _ => Nat.cast_add_one_pos _
      change ((hitCount A₁ T : ℝ) / ((validPart A₁).card : ℝ)) ≤
        ((hitCount A₂ T : ℝ) / ((validPart A₂).card : ℝ))
      rw [hfac A₁, hfac A₂, hrest_eq]
      rw [div_le_div_iff₀ (mul_pos hden1 hrest_pos) (mul_pos hden2 hrest_pos)]
      calc (hitCount A₁ T : ℝ) * (((A₂ s₀).card + 1 : ℝ) * rest)
          = ((hitCount A₁ T : ℝ) * ((A₂ s₀).card + 1 : ℝ)) * rest := by ring
        _ ≤ ((hitCount A₂ T : ℝ) * ((A₁ s₀).card + 1 : ℝ)) * rest :=
            mul_le_mul_of_nonneg_right hm hrest_pos.le
        _ = (hitCount A₂ T : ℝ) * (((A₁ s₀).card + 1 : ℝ) * rest) := by ring
  simpa using hU Finset.univ A

private lemma hitCount_erase_equiv {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (A : S → Finset C) (T : Finset C) (x : C) :
    hitCount (fun s => (A s).erase x) T =
      ((validPart A).filter (fun ω =>
        (∀ s : S, ω s ≠ some x) ∧ ∀ c ∈ T, ∃ s : S, ω s = some c)).card := by
  simp only [hitCount]
  congr 1
  ext ω
  simp only [validPart, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨hmem, ht⟩
    exact ⟨fun s c hc => (hmem s c hc).2, fun s hs => (hmem s x hs).1 rfl, ht⟩
  · rintro ⟨hmem, hnx, ht⟩
    exact ⟨fun s c hc => ⟨fun hcx => hnx s (hcx ▸ hc), hmem s c hc⟩, ht⟩

private lemma validPart_erase_equiv {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (A : S → Finset C) (x : C) :
    validPart (fun s => (A s).erase x) =
      (validPart A).filter (fun ω => ∀ s : S, ω s ≠ some x) := by
  ext ω
  simp only [validPart, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro h
    exact ⟨fun s c hc => (h s c hc).2, fun s hs => (h s x hs).1 rfl⟩
  · rintro ⟨h, hnx⟩ s c hc
    exact ⟨fun hcx => hnx s (hcx ▸ hc), h s c hc⟩

private lemma hitProb_insert_le {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (A : S → Finset C) (x : C) (T : Finset C) (hx : x ∉ T) :
    let N : ℝ := (validPart A).card
    ((hitCount A (insert x T) : ℝ) / N) ≤
      ((hitCount A {x} : ℝ) / N) * ((hitCount A T : ℝ) / N) := by
  intro N
  let Ω := validPart A
  let ET : Finset (S → Option C) := Ω.filter (fun ω => ∀ c ∈ T, ∃ s : S, ω s = some c)
  let Ex : Finset (S → Option C) := Ω.filter (fun ω => ∃ s : S, ω s = some x)
  let Enx : Finset (S → Option C) := Ω.filter (fun ω => ∀ s : S, ω s ≠ some x)
  have hET_split : ET.card = (ET ∩ Ex).card + (ET ∩ Enx).card := by
    have h1 : ET ∩ Ex = ET.filter (fun ω => ∃ s : S, ω s = some x) := by
      ext ω
      simp only [ET, Ex, Finset.mem_inter, Finset.mem_filter]
      tauto
    have h2 : ET ∩ Enx = ET.filter (fun ω => ¬ ∃ s : S, ω s = some x) := by
      ext ω
      simp only [ET, Enx, Finset.mem_inter, Finset.mem_filter, not_exists]
      tauto
    rw [h1, h2]
    exact (Finset.card_filter_add_card_filter_not (s := ET) (p := fun ω => ∃ s : S, ω s = some x)).symm
  have hEx_Enx : Ex.card + Enx.card = Ω.card := by
    have h2 : Enx = Ω.filter (fun ω => ¬ ∃ s : S, ω s = some x) := by
      ext ω; simp [Enx]
    rw [h2]
    exact Finset.card_filter_add_card_filter_not (s := Ω) (p := fun ω => ∃ s : S, ω s = some x)
  have hETEx : (ET ∩ Ex).card = hitCount A (insert x T) := by
    simp only [hitCount]
    congr 1
    ext ω
    simp only [ET, Ex, Ω, Finset.mem_inter, Finset.mem_filter, Finset.mem_insert, forall_eq_or_imp]
    tauto
  have hEx : Ex.card = hitCount A {x} := by
    simp [hitCount, Ex, Ω]
  have hET : ET.card = hitCount A T := rfl
  have hEnx_eq : Enx = validPart (fun s => (A s).erase x) := (validPart_erase_equiv A x).symm
  have hEnx_pos : 0 < (Enx.card : ℝ) := by
    rw [hEnx_eq]
    exact Nat.cast_pos.mpr (validPart_card_pos _)
  have hN_pos : 0 < N := Nat.cast_pos.mpr (validPart_card_pos A)
  have her := hitProb_erase_all A T x hx
  rw [hitCount_erase_equiv, validPart_erase_equiv] at her
  have hETEnx : ((validPart A).filter (fun ω =>
      (∀ s : S, ω s ≠ some x) ∧ ∀ c ∈ T, ∃ s : S, ω s = some c)).card = (ET ∩ Enx).card := by
    congr 1
    ext ω
    simp only [ET, Enx, Ω, Finset.mem_inter, Finset.mem_filter]
    tauto
  rw [hETEnx, show (validPart A).filter (fun ω => ∀ s : S, ω s ≠ some x) = Enx from rfl] at her
  change (hitCount A T : ℝ) / N ≤ ((ET ∩ Enx).card : ℝ) / (Enx.card : ℝ) at her
  have hmul : (hitCount A T : ℝ) * (Enx.card : ℝ) ≤ ((ET ∩ Enx).card : ℝ) * N :=
    (div_le_div_iff₀ hN_pos hEnx_pos).mp her
  have hsplit_R : (hitCount A T : ℝ) = (hitCount A (insert x T) : ℝ) + ((ET ∩ Enx).card : ℝ) := by
    exact_mod_cast (hET ▸ hETEx ▸ hET_split)
  have hEx_R : (hitCount A {x} : ℝ) + (Enx.card : ℝ) = (Ω.card : ℝ) := by
    exact_mod_cast (hEx ▸ hEx_Enx)
  change (hitCount A {x} : ℝ) + (Enx.card : ℝ) = N at hEx_R
  have hstep : (hitCount A (insert x T) : ℝ) * N ≤ (hitCount A {x} : ℝ) * (hitCount A T : ℝ) := by
    nlinarith
  rw [div_mul_div_comm, div_le_div_iff₀ hN_pos (mul_pos hN_pos hN_pos)]
  nlinarith [mul_le_mul_of_nonneg_right hstep hN_pos.le]

private lemma hitProb_le_prod {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
    (A : S → Finset C) (T : Finset C) :
    let N : ℝ := (validPart A).card
    ((hitCount A T : ℝ) / N) ≤ ∏ c ∈ T, ((hitCount A {c} : ℝ) / N) := by
  intro N
  induction T using Finset.induction_on with
  | empty =>
    have h0 : hitCount A ∅ = (validPart A).card := by
      simp [hitCount]
    have hN : N ≠ 0 := Nat.cast_ne_zero.mpr (validPart_card_pos A).ne'
    change (hitCount A ∅ : ℝ) / N ≤ 1
    rw [h0]
    exact (div_self hN).le
  | @insert x T₀ hx ih =>
    rw [Finset.prod_insert hx]
    have h1 := hitProb_insert_le A x T₀ hx
    have hnonneg : 0 ≤ (hitCount A {x} : ℝ) / N := by positivity
    exact h1.trans (mul_le_mul_of_nonneg_left ih hnonneg)

theorem chernoff_lower_available {S C : Type*} [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (A : S → Finset C) (ℓ : ℕ) (μ : ℝ)
    (hμ : μ ≤ ∑ c : C,
      (((validPart A).filter (fun ω => ∀ s : S, ω s ≠ some c)).card : ℝ) /
        ((validPart A).card : ℝ)) :
    (((validPart A).filter (fun ω => (availColors ω).card < ℓ)).card : ℝ)
      ≤ Real.exp ((ℓ : ℝ) * Real.log 2 - μ / 2) * ((validPart A).card : ℝ) := by
  let Ω := validPart A
  let N : ℝ := Ω.card
  have hN_pos : 0 < N := Nat.cast_pos.mpr (validPart_card_pos A)
  let p : C → ℝ := fun c =>
    ((Ω.filter (fun ω => ∀ s : S, ω s ≠ some c)).card : ℝ) / N
  let q : C → ℝ := fun c => (hitCount A {c} : ℝ) / N
  have hpq : ∀ c : C, p c + q c = 1 := by
    intro c
    have hsplit : (Ω.filter (fun ω => ∀ s : S, ω s ≠ some c)).card +
        hitCount A {c} = Ω.card := by
      have hc2 : Ω.filter (fun ω => ∀ s : S, ω s ≠ some c) =
          Ω.filter (fun ω => ¬ ∃ s : S, ω s = some c) := by
        ext ω; simp
      have hc1 : hitCount A {c} = (Ω.filter (fun ω => ∃ s : S, ω s = some c)).card := by
        simp [hitCount, Ω]
      rw [hc1, hc2, add_comm]
      exact Finset.card_filter_add_card_filter_not (s := Ω)
        (p := fun ω => ∃ s : S, ω s = some c)
    have hR : ((Ω.filter (fun ω => ∀ s : S, ω s ≠ some c)).card : ℝ) +
        (hitCount A {c} : ℝ) = (Ω.card : ℝ) := by exact_mod_cast hsplit
    simp only [p, q]
    change _ + _ = 1
    rw [← add_div, hR, div_self hN_pos.ne']
  have hsum_eq : ∑ ω ∈ Ω, (2 : ℝ) ^ (blockedColors ω).card =
      ∑ T : Finset C, (hitCount A T : ℝ) := by
    have h1 : ∀ ω : S → Option C, (2 : ℝ) ^ (blockedColors ω).card =
        ∑ T : Finset C, if T ⊆ blockedColors ω then (1 : ℝ) else 0 := by
      intro ω
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hf : Finset.univ.filter (fun T : Finset C => T ⊆ blockedColors ω) =
          (blockedColors ω).powerset := by
        ext T; simp
      rw [hf, Finset.card_powerset]
      norm_cast
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    refine congrArg Nat.cast (congrArg Finset.card ?_)
    ext ω
    simp [blockedColors, Finset.subset_iff, Ω]
  have hmoment : ∑ ω ∈ Ω, (2 : ℝ) ^ (blockedColors ω).card ≤
      (2 : ℝ) ^ (Fintype.card C) * Real.exp (-μ / 2) * N := by
    have hstep1 : (∑ T : Finset C, (hitCount A T : ℝ)) / N ≤
        ∑ T : Finset C, ∏ c ∈ T, q c := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun T _ => hitProb_le_prod A T
    have hstep2 : ∑ T : Finset C, ∏ c ∈ T, q c = ∏ c : C, (1 + q c) := by
      have hpow : (Finset.univ : Finset (Finset C)) = (Finset.univ : Finset C).powerset := by
        ext T; simp
      rw [hpow, ← Finset.prod_one_add]
    have hstep3 : ∏ c : C, (1 + q c) = (2 : ℝ) ^ (Fintype.card C) * ∏ c : C, (1 - p c / 2) := by
      have hterm : ∀ c : C, 1 + q c = 2 * (1 - p c / 2) := fun c => by linarith [hpq c]
      simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    have hstep4 : ∏ c : C, (1 - p c / 2) ≤ Real.exp (-μ / 2) := by
      calc ∏ c : C, (1 - p c / 2)
          ≤ ∏ c : C, Real.exp (-p c / 2) := by
            refine Finset.prod_le_prod (fun c _ => ?_) fun c _ => ?_
            · have hp1 : p c ≤ 1 := by
                have hq0 : 0 ≤ q c := by positivity
                linarith [hpq c]
              linarith
            · linarith [Real.add_one_le_exp (-p c / 2)]
        _ = Real.exp (∑ c : C, (-p c / 2)) := by rw [Real.exp_sum]
        _ ≤ Real.exp (-μ / 2) := by
            apply Real.exp_le_exp.mpr
            rw [← Finset.sum_div, Finset.sum_neg_distrib]
            change -(∑ c : C, p c) / 2 ≤ -μ / 2
            linarith [hμ]
    have hdiv_le : (∑ ω ∈ Ω, (2 : ℝ) ^ (blockedColors ω).card) / N ≤
        (2 : ℝ) ^ (Fintype.card C) * Real.exp (-μ / 2) := by
      rw [hsum_eq]
      calc (∑ T : Finset C, (hitCount A T : ℝ)) / N
          ≤ ∑ T : Finset C, ∏ c ∈ T, q c := hstep1
        _ = (2 : ℝ) ^ (Fintype.card C) * ∏ c : C, (1 - p c / 2) := hstep2.trans hstep3
        _ ≤ (2 : ℝ) ^ (Fintype.card C) * Real.exp (-μ / 2) :=
            mul_le_mul_of_nonneg_left hstep4 (by positivity)
    exact (div_le_iff₀ hN_pos).mp hdiv_le
  have hmarkov : (2 : ℝ) ^ (Fintype.card C - ℓ) *
      ((Ω.filter (fun ω => (availColors ω).card < ℓ)).card : ℝ) ≤
      ∑ ω ∈ Ω, (2 : ℝ) ^ (blockedColors ω).card := by
    calc (2 : ℝ) ^ (Fintype.card C - ℓ) *
          ((Ω.filter (fun ω => (availColors ω).card < ℓ)).card : ℝ)
        = ∑ _ω ∈ Ω.filter (fun ω => (availColors ω).card < ℓ),
            (2 : ℝ) ^ (Fintype.card C - ℓ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ ω ∈ Ω.filter (fun ω => (availColors ω).card < ℓ),
            (2 : ℝ) ^ (blockedColors ω).card := by
          refine Finset.sum_le_sum fun ω hω => ?_
          simp only [Finset.mem_filter] at hω
          have hsumc := avail_card_add_blocked_card ω
          have hle : Fintype.card C - ℓ ≤ (blockedColors ω).card := by omega
          exact pow_le_pow_right₀ (by norm_num) hle
      _ ≤ ∑ ω ∈ Ω, (2 : ℝ) ^ (blockedColors ω).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
  rcases le_or_gt ℓ (Fintype.card C) with hℓC | hCℓ
  · have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card C - ℓ) := by positivity
    have h1 := hmarkov.trans hmoment
    have hr : (2 : ℝ) ^ (Fintype.card C) =
        (2 : ℝ) ^ (Fintype.card C - ℓ) * (2 : ℝ) ^ ℓ := by
      rw [← pow_add, Nat.sub_add_cancel hℓC]
    rw [hr] at h1
    have h2 : ((Ω.filter (fun ω => (availColors ω).card < ℓ)).card : ℝ) ≤
        (2 : ℝ) ^ ℓ * Real.exp (-μ / 2) * N := by
      have h1' : (2 : ℝ) ^ (Fintype.card C - ℓ) *
          ((Ω.filter (fun ω => (availColors ω).card < ℓ)).card : ℝ) ≤
          (2 : ℝ) ^ (Fintype.card C - ℓ) * ((2 : ℝ) ^ ℓ * Real.exp (-μ / 2) * N) := by
        linarith
      exact le_of_mul_le_mul_left h1' hpow_pos
    have hpow2 : (2 : ℝ) ^ ℓ = Real.exp ((ℓ : ℝ) * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
    rw [hpow2, ← Real.exp_add] at h2
    have harg : (ℓ : ℝ) * Real.log 2 + -μ / 2 = (ℓ : ℝ) * Real.log 2 - μ / 2 := by ring
    rwa [harg] at h2
  · have hcard0 : (Ω.filter (fun ω => (availColors ω).card < ℓ)).card ≤ Ω.card :=
      Finset.card_filter_le Ω _
    have hμ_le : μ ≤ (Fintype.card C : ℝ) := by
      calc μ ≤ ∑ c : C, p c := hμ
        _ ≤ ∑ _c : C, (1 : ℝ) := Finset.sum_le_sum fun c _ => by
            have hq0 : 0 ≤ q c := by positivity
            linarith [hpq c]
        _ = (Fintype.card C : ℝ) := by simp
    have harg : 0 ≤ (ℓ : ℝ) * Real.log 2 - μ / 2 := by
      have hC_lt : (Fintype.card C : ℝ) < (ℓ : ℝ) := by exact_mod_cast hCℓ
      have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card C)]
    have hexp_ge : 1 ≤ Real.exp ((ℓ : ℝ) * Real.log 2 - μ / 2) :=
      Real.one_le_exp harg
    have hcard0R : ((Ω.filter (fun ω => (availColors ω).card < ℓ)).card : ℝ) ≤ (Ω.card : ℝ) := by
      exact_mod_cast hcard0
    change ((Ω.filter (fun ω => (availColors ω).card < ℓ)).card : ℝ) ≤ N at hcard0R
    calc ((Ω.filter (fun ω => (availColors ω).card < ℓ)).card : ℝ)
        ≤ N := hcard0R
      _ = 1 * N := (one_mul N).symm
      _ ≤ Real.exp ((ℓ : ℝ) * Real.log 2 - μ / 2) * N :=
          mul_le_mul_of_nonneg_right hexp_ge hN_pos.le

end Concentration

section Molloy

private lemma molloy_params_exists (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ Δ₀ : ℕ, ∀ Δ ≥ Δ₀,
      let k := Nat.ceil ((1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ))
      let ℓ := Nat.floor ((Δ : ℝ) ^ (δ / 3))
      16 ≤ Δ ∧ 4 ≤ ℓ ∧ 1 ≤ k ∧ 32 * (k : ℝ) ≤ (Δ : ℝ) ∧
        2 * (ℓ : ℝ) ≤ (k : ℝ) * Real.exp (-(Δ : ℝ) / (k : ℝ)) ∧
        Real.exp ((ℓ : ℝ) * Real.log 2 - (ℓ : ℝ)) ≤ 1 / (32 * (Δ : ℝ) ^ 3) ∧
        Real.exp (4 * Real.log (Δ : ℝ) - Real.log 2 * ((ℓ : ℝ) / 32)) ≤ 1 / (Δ : ℝ) ^ 4 := by
  have h1 : ∀ᶠ x : ℝ in atTop, 64 ≤ x := eventually_ge_atTop 64
  have hlog : ∀ᶠ x : ℝ in atTop, 128 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 128)
  have ho6 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (1 / 2 : ℝ) * ‖x ^ (δ / 6)‖ :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < δ / 6)).bound (by norm_num)
  have ho3a : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (1 / 48 : ℝ) * ‖x ^ (δ / 3)‖ :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < δ / 3)).bound (by norm_num)
  have ho3b : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (Real.log 2 / 512 : ℝ) * ‖x ^ (δ / 3)‖ :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < δ / 3)).bound
      (by have := Real.log_two_gt_d9; positivity)
  have hbig : ∀ᶠ x : ℝ in atTop, 100 ≤ x ^ (δ / 3) :=
    (tendsto_rpow_atTop (by positivity : 0 < δ / 3)).eventually (eventually_ge_atTop 100)
  have hevR : ∀ᶠ x : ℝ in atTop,
      64 ≤ x ∧ 128 ≤ Real.log x ∧ 100 ≤ x ^ (δ / 3) ∧
        Real.log x ≤ (1 / 2) * x ^ (δ / 6) ∧
        Real.log x ≤ (1 / 48) * x ^ (δ / 3) ∧
        Real.log x ≤ (Real.log 2 / 512) * x ^ (δ / 3) := by
    filter_upwards [h1, hlog, hbig, ho6, ho3a, ho3b] with x hx1 hx2 hx4 h6 h3a h3b
    have hlognn : 0 ≤ Real.log x := by linarith
    have hp6 : 0 ≤ x ^ (δ / 6) := Real.rpow_nonneg (by linarith) _
    have hp3 : 0 ≤ x ^ (δ / 3) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg hlognn, Real.norm_of_nonneg hp6] at h6
    rw [Real.norm_of_nonneg hlognn, Real.norm_of_nonneg hp3] at h3a h3b
    exact ⟨hx1, hx2, hx4, h6, h3a, h3b⟩
  have hevN : ∀ᶠ Δ : ℕ in atTop,
      64 ≤ (Δ : ℝ) ∧ 128 ≤ Real.log (Δ : ℝ) ∧
        100 ≤ (Δ : ℝ) ^ (δ / 3) ∧
        Real.log (Δ : ℝ) ≤ (1 / 2) * (Δ : ℝ) ^ (δ / 6) ∧
        Real.log (Δ : ℝ) ≤ (1 / 48) * (Δ : ℝ) ^ (δ / 3) ∧
        Real.log (Δ : ℝ) ≤ (Real.log 2 / 512) * (Δ : ℝ) ^ (δ / 3) :=
    tendsto_natCast_atTop_atTop.eventually hevR
  rw [Filter.eventually_atTop] at hevN
  obtain ⟨Δ₀, hΔ₀⟩ := hevN
  refine ⟨Δ₀, fun Δ hΔ => ?_⟩
  obtain ⟨hx64, hlog128, hxpow100, hlog6, hlog3a, hlog3b⟩ := hΔ₀ Δ hΔ
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by linarith
  have hlogpos : 0 < Real.log (Δ : ℝ) := by linarith
  dsimp only
  set k := Nat.ceil ((1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ))
  set ℓ := Nat.floor ((Δ : ℝ) ^ (δ / 3))
  have hk_ge : (1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ) ≤ (k : ℝ) := Nat.le_ceil _
  have hk_lt : (k : ℝ) < (1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hk_pos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (by positivity) hk_ge
  have hk1 : 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast hk_pos)
  have hk32 : 32 * (k : ℝ) ≤ (Δ : ℝ) := by
    have h1d : 1 + δ ≤ 2 := by linarith
    have hnum : (1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ) ≤ 2 * (Δ : ℝ) / 128 := by
      calc (1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ)
          ≤ 2 * (Δ : ℝ) / Real.log (Δ : ℝ) := by gcongr
        _ ≤ 2 * (Δ : ℝ) / 128 := by gcongr
    linarith
  have hℓ_le : (ℓ : ℝ) ≤ (Δ : ℝ) ^ (δ / 3) := Nat.floor_le (Real.rpow_nonneg hΔpos.le _)
  have hℓ_gt : (Δ : ℝ) ^ (δ / 3) - 1 < (ℓ : ℝ) := Nat.sub_one_lt_floor _
  have hℓ_half : (Δ : ℝ) ^ (δ / 3) ≤ 2 * (ℓ : ℝ) := by linarith
  have hℓ4 : 4 ≤ ℓ := by
    exact_mod_cast (by linarith : (4 : ℝ) ≤ (ℓ : ℝ))
  have hexp_k : 2 * (ℓ : ℝ) ≤ (k : ℝ) * Real.exp (-(Δ : ℝ) / (k : ℝ)) := by
    have h1 : (Δ : ℝ) / (k : ℝ) ≤ Real.log (Δ : ℝ) / (1 + δ) := by
      rw [div_le_div_iff₀ hk_pos (by linarith)]
      have h2 := (div_le_iff₀ hlogpos).mp hk_ge
      nlinarith
    have hΔk : -(Real.log (Δ : ℝ) / (1 + δ)) ≤ -(Δ : ℝ) / (k : ℝ) := by
      rw [neg_div]
      exact neg_le_neg h1
    have hrpow_eq : Real.exp (-(Real.log (Δ : ℝ) / (1 + δ))) = (Δ : ℝ) ^ (-(1 / (1 + δ))) := by
      rw [Real.rpow_def_of_pos hΔpos]
      congr 1
      ring
    have hexp_ge : (Δ : ℝ) ^ (-(1 / (1 + δ))) ≤ Real.exp (-(Δ : ℝ) / (k : ℝ)) := by
      rw [← hrpow_eq]
      exact Real.exp_le_exp.mpr hΔk
    have hprod_ge : ((1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ)) * (Δ : ℝ) ^ (-(1 / (1 + δ))) ≤
        (k : ℝ) * Real.exp (-(Δ : ℝ) / (k : ℝ)) :=
      mul_le_mul hk_ge hexp_ge (Real.rpow_nonneg hΔpos.le _) hk_pos.le
    have hpow_comb : (Δ : ℝ) * (Δ : ℝ) ^ (-(1 / (1 + δ))) = (Δ : ℝ) ^ (δ / (1 + δ)) := by
      conv_lhs => arg 1; rw [← Real.rpow_one (Δ : ℝ)]
      rw [← Real.rpow_add hΔpos]
      congr 1
      field_simp
      ring
    have hexp_split : (Δ : ℝ) ^ (δ / 3) * (Δ : ℝ) ^ (δ / 6) ≤ (Δ : ℝ) ^ (δ / (1 + δ)) := by
      rw [← Real.rpow_add hΔpos]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      have h1d : 1 + δ ≤ 2 := by linarith
      rw [add_comm]
      calc δ / 6 + δ / 3 = δ / 2 := by ring
        _ ≤ δ / (1 + δ) := by gcongr
    have hlhs : 2 * (Δ : ℝ) ^ (δ / 3) ≤
        ((1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ)) * (Δ : ℝ) ^ (-(1 / (1 + δ))) := by
      have h1' : ((1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ)) * (Δ : ℝ) ^ (-(1 / (1 + δ))) =
          (1 + δ) * ((Δ : ℝ) ^ (δ / (1 + δ)) / Real.log (Δ : ℝ)) := by
        rw [← hpow_comb]; ring
      rw [h1']
      have h3 : 2 * (Δ : ℝ) ^ (δ / 3) ≤ (Δ : ℝ) ^ (δ / (1 + δ)) / Real.log (Δ : ℝ) := by
        rw [le_div_iff₀ hlogpos]
        calc 2 * (Δ : ℝ) ^ (δ / 3) * Real.log (Δ : ℝ)
            = (2 * Real.log (Δ : ℝ)) * (Δ : ℝ) ^ (δ / 3) := by ring
          _ ≤ (Δ : ℝ) ^ (δ / 6) * (Δ : ℝ) ^ (δ / 3) := by
              gcongr; linarith
          _ = (Δ : ℝ) ^ (δ / 3) * (Δ : ℝ) ^ (δ / 6) := by ring
          _ ≤ (Δ : ℝ) ^ (δ / (1 + δ)) := hexp_split
      have h4 : (Δ : ℝ) ^ (δ / (1 + δ)) / Real.log (Δ : ℝ) ≤
          (1 + δ) * ((Δ : ℝ) ^ (δ / (1 + δ)) / Real.log (Δ : ℝ)) :=
        le_mul_of_one_le_left (by positivity) (by linarith)
      exact h3.trans h4
    have hℓ_bound : 2 * (ℓ : ℝ) ≤ 2 * (Δ : ℝ) ^ (δ / 3) := by linarith
    exact hℓ_bound.trans (hlhs.trans hprod_ge)
  have hexp_a : Real.exp ((ℓ : ℝ) * Real.log 2 - (ℓ : ℝ)) ≤ 1 / (32 * (Δ : ℝ) ^ 3) := by
    have hlog2 : Real.log 2 < 3 / 4 := by linarith [Real.log_two_lt_d9]
    have hlog32 : Real.log 32 ≤ 4 := by
      have h32 : (32 : ℝ) ≤ Real.exp 4 := by
        have he : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have he4 : Real.exp 4 = (Real.exp 1) ^ 4 := by
          rw [← Real.exp_nat_mul]; norm_num
        rw [he4]
        have hpow : (2.71 : ℝ) ^ 4 ≤ (Real.exp 1) ^ 4 :=
          pow_le_pow_left₀ (by norm_num) he 4
        have hnum32 : (32 : ℝ) ≤ (2.71 : ℝ) ^ 4 := by norm_num
        exact hnum32.trans hpow
      calc Real.log 32 ≤ Real.log (Real.exp 4) := Real.log_le_log (by norm_num) h32
        _ = 4 := Real.log_exp 4
    have h12 : Real.log 32 + 3 * Real.log (Δ : ℝ) ≤ (1 / 4 : ℝ) * (ℓ : ℝ) := by
      calc Real.log 32 + 3 * Real.log (Δ : ℝ)
          ≤ 4 + 3 * Real.log (Δ : ℝ) := by linarith
        _ ≤ 6 * Real.log (Δ : ℝ) := by linarith
        _ ≤ (1 / 8 : ℝ) * (Δ : ℝ) ^ (δ / 3) := by linarith
        _ ≤ (1 / 4 : ℝ) * (ℓ : ℝ) := by linarith
    have harg : (ℓ : ℝ) * Real.log 2 - (ℓ : ℝ) ≤ Real.log (1 / (32 * (Δ : ℝ) ^ 3)) := by
      rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      have hℓ_nn : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc Real.exp ((ℓ : ℝ) * Real.log 2 - (ℓ : ℝ))
        ≤ Real.exp (Real.log (1 / (32 * (Δ : ℝ) ^ 3))) := Real.exp_le_exp.mpr harg
      _ = 1 / (32 * (Δ : ℝ) ^ 3) := Real.exp_log (by positivity)
  have hexp_b : Real.exp (4 * Real.log (Δ : ℝ) - Real.log 2 * ((ℓ : ℝ) / 32)) ≤ 1 / (Δ : ℝ) ^ 4 := by
    have h8 : 8 * Real.log (Δ : ℝ) ≤ Real.log 2 * ((ℓ : ℝ) / 32) := by
      calc 8 * Real.log (Δ : ℝ)
          ≤ (Real.log 2 / 64) * (Δ : ℝ) ^ (δ / 3) := by linarith
        _ ≤ (Real.log 2 / 64) * (2 * (ℓ : ℝ)) := by gcongr
        _ = Real.log 2 * ((ℓ : ℝ) / 32) := by ring
    have harg : 4 * Real.log (Δ : ℝ) - Real.log 2 * ((ℓ : ℝ) / 32) ≤ Real.log (1 / (Δ : ℝ) ^ 4) := by
      rw [one_div, Real.log_inv, Real.log_pow]
      push_cast
      linarith
    calc Real.exp (4 * Real.log (Δ : ℝ) - Real.log 2 * ((ℓ : ℝ) / 32))
        ≤ Real.exp (Real.log (1 / (Δ : ℝ) ^ 4)) := Real.exp_le_exp.mpr harg
      _ = 1 / (Δ : ℝ) ^ 4 := Real.exp_log (by positivity)
  refine ⟨by exact_mod_cast (by linarith : (16 : ℝ) ≤ (Δ : ℝ)), hℓ4, hk1, hk32, hexp_k, hexp_a, hexp_b⟩

private abbrev PartialColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) : Type _ :=
  {f : V → Option (Fin k) // ∀ (u v : V) (c : Fin k), G.Adj u v → f u = some c → f v ≠ some c}

private instance {V : Type*} (G : SimpleGraph V) (k : ℕ) : Nonempty (PartialColoring G k) :=
  ⟨⟨fun _ => none, fun _ _ _ _ h => by simp at h⟩⟩

private def remList {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (f : PartialColoring G k) (u : V) : Finset (Fin k) :=
  Finset.univ.filter (fun c : Fin k => ∀ w : V, G.Adj u w → f.1 w ≠ some c)

private def partialColorDeg {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (f : PartialColoring G k) (u : V) (c : Fin k) : ℕ :=
  (Finset.univ.filter (fun w : V => G.Adj u w ∧ f.1 w = none ∧ c ∈ remList f w)).card

private def badEvent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k ℓ : ℕ) (u : V) :
    Finset (PartialColoring G k) :=
  Finset.univ.filter (fun f => f.1 u = none ∧
    ((remList f u).card < ℓ ∨ ∃ c ∈ remList f u, ℓ / 32 < partialColorDeg f u c))

private def nbhd1 {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Finset V :=
  Finset.univ.filter (fun v => G.Adj u v)

private def molloyGamma {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  let N1 := nbhd1 G u
  let N2 := N1.biUnion (nbhd1 G)
  let N3 := N2.biUnion (nbhd1 G)
  (N1 ∪ N2 ∪ N3).erase u

private lemma molloyGamma_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 1 ≤ Δ)
    (hdeg : ∀ v : V, (nbhd1 G v).card ≤ Δ) (u : V) :
    (molloyGamma G u).card ≤ 3 * Δ ^ 3 := by
  dsimp only [molloyGamma]
  set N1 := nbhd1 G u
  set N2 := N1.biUnion (nbhd1 G)
  set N3 := N2.biUnion (nbhd1 G)
  have h1 : N1.card ≤ Δ := hdeg u
  have h2 : N2.card ≤ Δ ^ 2 := by
    calc N2.card ≤ ∑ v ∈ N1, (nbhd1 G v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ N1, Δ := Finset.sum_le_sum fun v _ => hdeg v
      _ = N1.card * Δ := Finset.sum_const_nat (fun _ _ => rfl)
      _ ≤ Δ * Δ := Nat.mul_le_mul_right Δ h1
      _ = Δ ^ 2 := by ring
  have h3 : N3.card ≤ Δ ^ 3 := by
    calc N3.card ≤ ∑ v ∈ N2, (nbhd1 G v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ N2, Δ := Finset.sum_le_sum fun v _ => hdeg v
      _ = N2.card * Δ := Finset.sum_const_nat (fun _ _ => rfl)
      _ ≤ Δ ^ 2 * Δ := Nat.mul_le_mul_right Δ h2
      _ = Δ ^ 3 := by ring
  have hΔ2 : Δ ≤ Δ ^ 2 := Nat.le_self_pow (by norm_num) Δ
  have hΔ3 : Δ ^ 2 ≤ Δ ^ 3 := by nlinarith
  calc ((N1 ∪ N2 ∪ N3).erase u).card
      ≤ (N1 ∪ N2 ∪ N3).card := Finset.card_erase_le
    _ ≤ (N1 ∪ N2).card + N3.card := Finset.card_union_le _ _
    _ ≤ N1.card + N2.card + N3.card := by linarith [Finset.card_union_le N1 N2]
    _ ≤ Δ + Δ ^ 2 + Δ ^ 3 := by linarith
    _ ≤ 3 * Δ ^ 3 := by linarith

private lemma mem_badEvent_congr {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k ℓ : ℕ) (u v : V)
    (hvu : v ≠ u) (hvΓ : v ∉ molloyGamma G u)
    (f₁ f₂ : PartialColoring G k)
    (hout : ∀ w : V, ¬ G.Adj u w → f₁.1 w = f₂.1 w) :
    f₁ ∈ badEvent G k ℓ v ↔ f₂ ∈ badEvent G k ℓ v := by
  have h_not_adj_u_v : ¬ G.Adj u v := by
    intro hadj
    apply hvΓ
    simp only [molloyGamma, nbhd1, Finset.mem_erase, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨hvu, Or.inl (Or.inl hadj)⟩
  have h_not_dist1 : ∀ w : V, G.Adj v w → ¬ G.Adj u w := by
    intro w hvw huw
    apply hvΓ
    simp only [molloyGamma, nbhd1, Finset.mem_erase, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hvu, Or.inl (Or.inr ⟨w, huw, hvw.symm⟩)⟩
  have h_not_dist2 : ∀ w z : V, G.Adj v w → G.Adj w z → ¬ G.Adj u z := by
    intro w z hvw hwz huz
    apply hvΓ
    simp only [molloyGamma, nbhd1, Finset.mem_erase, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hvu, Or.inr ⟨w, ⟨z, huz, hwz.symm⟩, hvw.symm⟩⟩
  have hrem_v : remList f₁ v = remList f₂ v := by
    ext c
    simp only [remList, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h w hvw; rw [← hout w (h_not_dist1 w hvw)]; exact h w hvw
    · intro h w hvw; rw [hout w (h_not_dist1 w hvw)]; exact h w hvw
  have hdeg_v : ∀ c, partialColorDeg f₁ v c = partialColorDeg f₂ v c := by
    intro c
    simp only [partialColorDeg]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hvw : G.Adj v w
    · have huw : ¬ G.Adj u w := h_not_dist1 w hvw
      have hrem_w : remList f₁ w = remList f₂ w := by
        ext c'
        simp only [remList, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h z hwz; rw [← hout z (h_not_dist2 w z hvw hwz)]; exact h z hwz
        · intro h z hwz; rw [hout z (h_not_dist2 w z hvw hwz)]; exact h z hwz
      simp [hvw, hout w huw, hrem_w]
    · simp [hvw]
  simp only [badEvent, Finset.mem_filter, Finset.mem_univ, true_and, hout v h_not_adj_u_v,
    hrem_v, hdeg_v]

private lemma validPart_split_card {S C : Type*} [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C]
    (A : S → Finset C) (P : S → Prop) [DecidablePred P]
    (Q : (S → Option C) → Prop) [DecidablePred Q]
    (Q₁ : ({s : S // P s} → Option C) → Prop) [DecidablePred Q₁]
    (hQ : ∀ ω : S → Option C, Q ω ↔ Q₁ (fun s => ω s.1)) :
    ((validPart A).filter Q).card =
      ((validPart (fun s : {s : S // P s} => A s.1)).filter Q₁).card *
        (validPart (fun s : {s : S // ¬ P s} => A s.1)).card := by
  let S₁ := {s : S // P s}
  let S₂ := {s : S // ¬ P s}
  let e : (S → Option C) ≃ (S₁ → Option C) × (S₂ → Option C) :=
    { toFun := fun ω => (fun s => ω s.1, fun s => ω s.1)
      invFun := fun ⟨ω₁, ω₂⟩ s => if h : P s then ω₁ ⟨s, h⟩ else ω₂ ⟨s, h⟩
      left_inv := fun ω => by
        funext s; by_cases h : P s <;> simp [h]
      right_inv := fun ⟨ω₁, ω₂⟩ => by
        refine Prod.ext ?_ ?_
        · funext ⟨s, hs⟩; simp [hs]
        · funext ⟨s, hs⟩; simp [hs] }
  let A₁ := fun s : S₁ => A s.1
  let A₂ := fun s : S₂ => A s.1
  have hiff : ∀ ω : S → Option C, ω ∈ (validPart A).filter Q ↔
      (e ω).1 ∈ (validPart A₁).filter Q₁ ∧ (e ω).2 ∈ validPart A₂ := by
    intro ω
    simp only [Finset.mem_filter, validPart, Finset.mem_univ, true_and, e, hQ]
    constructor
    · rintro ⟨hv, hq⟩
      exact ⟨⟨fun s c hsc => hv s.1 c hsc, hq⟩, fun s c hsc => hv s.1 c hsc⟩
    · rintro ⟨⟨hv1, hq⟩, hv2⟩
      refine ⟨fun s c hsc => ?_, hq⟩
      by_cases h : P s
      · exact hv1 ⟨s, h⟩ c hsc
      · exact hv2 ⟨s, h⟩ c hsc
  have h1 : ((validPart A).filter Q).card =
      (((validPart A₁).filter Q₁) ×ˢ (validPart A₂)).card := by
    refine Finset.card_bij (fun ω _ => e ω) ?_ ?_ ?_
    · intro ω hω
      rw [Finset.mem_product]
      exact (hiff ω).mp hω
    · intro ω₁ _ ω₂ _ heq; exact e.injective heq
    · intro p hp
      rw [Finset.mem_product] at hp
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      rw [hiff, e.apply_symm_apply]
      exact hp
  rw [h1, Finset.card_product]

private lemma molloy_prob_c {S : Type*} [Fintype S] [DecidableEq S] {k : ℕ}
    (A : S → Finset (Fin k)) (c : Fin k) :
    (((validPart A).filter (fun ω => ∀ v : S, ω v ≠ some c)).card : ℝ) /
      ((validPart A).card : ℝ) =
    ∏ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
      ((A v).card : ℝ) / ((A v).card + 1 : ℝ) := by
  rw [← validPart_erase_equiv A c, validPart_card, validPart_card]
  push_cast
  have hterm : ∀ s : S, (((A s).erase c).card + 1 : ℝ) =
      (if c ∈ A s then ((A s).card : ℝ) else ((A s).card + 1 : ℝ)) := by
    intro s
    by_cases hcs : c ∈ A s
    · simp only [hcs, ↓reduceIte]
      have h1 : 1 ≤ (A s).card := Finset.card_pos.mpr ⟨c, hcs⟩
      rw [Finset.card_erase_of_mem hcs]
      have hnat : (A s).card - 1 + 1 = (A s).card := Nat.sub_add_cancel h1
      exact_mod_cast hnat
    · simp only [hcs, ↓reduceIte, Finset.erase_eq_of_notMem hcs]
  simp_rw [hterm]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset S) (fun v => c ∈ A v)]
  have h1 : ∏ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
        (if c ∈ A v then ((A v).card : ℝ) else ((A v).card + 1 : ℝ)) =
      ∏ v ∈ Finset.univ.filter (fun v : S => c ∈ A v), ((A v).card : ℝ) := by
    refine Finset.prod_congr rfl fun v hv => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp [hv]
  have h2 : ∏ v ∈ Finset.univ.filter (fun v : S => ¬ c ∈ A v),
        (if c ∈ A v then ((A v).card : ℝ) else ((A v).card + 1 : ℝ)) =
      ∏ v ∈ Finset.univ.filter (fun v : S => ¬ c ∈ A v), (((A v).card : ℝ) + 1) := by
    refine Finset.prod_congr rfl fun v hv => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp [hv]
  have hden : ∏ s : S, (((A s).card : ℝ) + 1) =
      (∏ v ∈ Finset.univ.filter (fun v : S => c ∈ A v), (((A v).card : ℝ) + 1)) *
        (∏ v ∈ Finset.univ.filter (fun v : S => ¬ c ∈ A v), (((A v).card : ℝ) + 1)) :=
    (Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset S) (fun v => c ∈ A v)
      (fun v => ((A v).card : ℝ) + 1)).symm
  rw [h1, h2, hden]
  have hden2 : 0 < ∏ v ∈ Finset.univ.filter (fun v : S => ¬ c ∈ A v), (((A v).card : ℝ) + 1) :=
    Finset.prod_pos fun _ _ => Nat.cast_add_one_pos _
  rw [mul_div_mul_right _ _ hden2.ne', Finset.prod_div_distrib]

private lemma molloy_badA_bound {S : Type*} [Fintype S] [DecidableEq S] {Δ k ℓ : ℕ}
    (A : S → Finset (Fin k))
    (hS_le : Fintype.card S ≤ Δ) (hk1 : 1 ≤ k)
    (hexp_k : 2 * (ℓ : ℝ) ≤ (k : ℝ) * Real.exp (-(Δ : ℝ) / (k : ℝ)))
    (hexp_a : Real.exp ((ℓ : ℝ) * Real.log 2 - (ℓ : ℝ)) ≤ 1 / (32 * (Δ : ℝ) ^ 3)) :
    (((validPart A).filter (fun ω => (availColors ω).card < ℓ)).card : ℝ) ≤
      (1 / (32 * (Δ : ℝ) ^ 3)) * ((validPart A).card : ℝ) := by
  have hpc_ge : ∀ c : Fin k,
      Real.exp (- ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v), (1 : ℝ) / ((A v).card : ℝ)) ≤
      (((validPart A).filter (fun ω => ∀ v : S, ω v ≠ some c)).card : ℝ) /
        ((validPart A).card : ℝ) := by
    intro c
    rw [molloy_prob_c A c, Real.exp_neg, Real.exp_sum, ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun v hv => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hcard1 : (0 : ℝ) < ((A v).card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨c, hv⟩)
    have hle_exp : 1 + 1 / ((A v).card : ℝ) ≤ Real.exp (1 / ((A v).card : ℝ)) := by
      linarith [Real.add_one_le_exp (1 / ((A v).card : ℝ))]
    have hinv : (Real.exp (1 / ((A v).card : ℝ)))⁻¹ ≤ (1 + 1 / ((A v).card : ℝ))⁻¹ :=
      inv_anti₀ (by positivity) hle_exp
    have heq_m : (1 + 1 / ((A v).card : ℝ))⁻¹ = ((A v).card : ℝ) / ((A v).card + 1 : ℝ) := by
      field_simp
    rwa [← heq_m]
  have hsum_dc : ∑ c : Fin k, ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
      (1 : ℝ) / ((A v).card : ℝ) ≤ (Δ : ℝ) := by
    have hswap : (∑ c : Fin k, ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
          (1 : ℝ) / ((A v).card : ℝ)) =
        ∑ v : S, ∑ _c ∈ A v, (1 : ℝ) / ((A v).card : ℝ) := by
      have h1 : ∀ c : Fin k, ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
            (1 : ℝ) / ((A v).card : ℝ) =
          ∑ v : S, if c ∈ A v then (1 : ℝ) / ((A v).card : ℝ) else 0 := by
        intro c; rw [← Finset.sum_filter]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← Finset.sum_filter]
      congr 1
      ext c; simp
    rw [hswap]
    calc ∑ v : S, ∑ _c ∈ A v, (1 : ℝ) / ((A v).card : ℝ)
        ≤ ∑ _v : S, (1 : ℝ) := by
          refine Finset.sum_le_sum fun v _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          by_cases h0 : (A v).card = 0
          · simp [h0]
          · have hpos : (0 : ℝ) < ((A v).card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
            rw [mul_one_div, div_self hpos.ne']
      _ = (Fintype.card S : ℝ) := by simp
      _ ≤ (Δ : ℝ) := by exact_mod_cast hS_le
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
  have hjensen : Real.exp (-(Δ : ℝ) / (k : ℝ)) ≤
      (1 / (k : ℝ)) * ∑ c : Fin k,
        Real.exp (- ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
          (1 : ℝ) / ((A v).card : ℝ)) := by
    have hconv := convexOn_exp.map_sum_le
      (t := (Finset.univ : Finset (Fin k)))
      (w := fun _ => (1 : ℝ) / (k : ℝ))
      (p := fun c => - ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
        (1 : ℝ) / ((A v).card : ℝ))
      (fun _ _ => by positivity)
      (by simp [hk_pos.ne'])
      (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul, ← Finset.mul_sum] at hconv
    have harg_le : -(Δ : ℝ) / (k : ℝ) ≤ (1 / (k : ℝ)) *
        ∑ c : Fin k, - ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
          (1 : ℝ) / ((A v).card : ℝ) := by
      rw [Finset.sum_neg_distrib]
      have : (1 / (k : ℝ)) * -∑ c : Fin k,
          ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v), (1 : ℝ) / ((A v).card : ℝ) =
          -(∑ c : Fin k, ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
            (1 : ℝ) / ((A v).card : ℝ)) / (k : ℝ) := by ring
      rw [this]
      exact div_le_div_of_nonneg_right (neg_le_neg hsum_dc) hk_pos.le
    exact (Real.exp_le_exp.mpr harg_le).trans hconv
  have hμ_ge : 2 * (ℓ : ℝ) ≤ ∑ c : Fin k,
      (((validPart A).filter (fun ω => ∀ v : S, ω v ≠ some c)).card : ℝ) /
        ((validPart A).card : ℝ) := by
    have h1 : (k : ℝ) * Real.exp (-(Δ : ℝ) / (k : ℝ)) ≤
        ∑ c : Fin k, Real.exp (- ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
          (1 : ℝ) / ((A v).card : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hjensen hk_pos.le
      rwa [← mul_assoc, mul_one_div_cancel hk_pos.ne', one_mul] at this
    exact hexp_k.trans (h1.trans (Finset.sum_le_sum fun c _ => hpc_ge c))
  have hch := chernoff_lower_available A ℓ (2 * (ℓ : ℝ)) hμ_ge
  have harg_eq : (ℓ : ℝ) * Real.log 2 - (2 * (ℓ : ℝ)) / 2 = (ℓ : ℝ) * Real.log 2 - (ℓ : ℝ) := by ring
  rw [harg_eq] at hch
  exact hch.trans (mul_le_mul_of_nonneg_right hexp_a (Nat.cast_nonneg _))

private lemma molloy_badB_bound {S : Type*} [Fintype S] [DecidableEq S] {Δ k ℓ : ℕ}
    (A : S → Finset (Fin k))
    (hΔpos : (0 : ℝ) < (Δ : ℝ))
    (hk32 : 32 * (k : ℝ) ≤ (Δ : ℝ))
    (hexp_b : Real.exp (4 * Real.log (Δ : ℝ) - Real.log 2 * ((ℓ : ℝ) / 32)) ≤ 1 / (Δ : ℝ) ^ 4) :
    (((validPart A).filter (fun ω => ∃ c : Fin k, c ∈ availColors ω ∧
        ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card)).card : ℝ) ≤
      (1 / (32 * (Δ : ℝ) ^ 3)) * ((validPart A).card : ℝ) := by
  let badB := (validPart A).filter (fun ω => ∃ c : Fin k, c ∈ availColors ω ∧
    ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card)
  change (badB.card : ℝ) ≤ _
  have hbadB_sub : badB ⊆ Finset.univ.biUnion (fun c : Fin k =>
      (validPart A).filter (fun ω => (∀ v : S, ω v ≠ some c) ∧
        ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card)) := by
    intro ω hω
    simp only [badB, Finset.mem_filter] at hω
    rcases hω.2 with ⟨c, hc, hdeg_c⟩
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    refine ⟨c, hω.1, ?_, hdeg_c⟩
    simp only [availColors, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact hc
  have hcard_union : (badB.card : ℝ) ≤ ∑ c : Fin k,
      (((validPart A).filter (fun ω => (∀ v : S, ω v ≠ some c) ∧
        ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card)).card : ℝ) := by
    have hnat := (Finset.card_le_card hbadB_sub).trans Finset.card_biUnion_le
    exact_mod_cast hnat
  have hper_c : ∀ c : Fin k,
      (((validPart A).filter (fun ω => (∀ v : S, ω v ≠ some c) ∧
        ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card)).card : ℝ) ≤
        (1 / (Δ : ℝ) ^ 4) * ((validPart A).card : ℝ) := by
    intro c
    let S₁ := {v : S // c ∈ A v}
    let A₁ : S₁ → Finset (Fin k) := fun v => A v.1
    let μc := ∑ v : S₁, (1 : ℝ) / ((A₁ v).card + 1 : ℝ)
    by_cases hμ : 4 * Real.log (Δ : ℝ) < μc
    · have hsub : (validPart A).filter (fun ω => (∀ v : S, ω v ≠ some c) ∧
          ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card) ⊆
          (validPart A).filter (fun ω => ∀ v : S, ω v ≠ some c) := by
        intro ω hω
        simp only [Finset.mem_filter] at hω ⊢
        exact ⟨hω.1, hω.2.1⟩
      have hle1 : (((validPart A).filter (fun ω => (∀ v : S, ω v ≠ some c) ∧
          ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card)).card : ℝ) ≤
          (((validPart A).filter (fun ω => ∀ v : S, ω v ≠ some c)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hVpos : (0 : ℝ) < ((validPart A).card : ℝ) :=
        Nat.cast_pos.mpr (validPart_card_pos A)
      have hprob_le : (((validPart A).filter (fun ω => ∀ v : S, ω v ≠ some c)).card : ℝ) /
          ((validPart A).card : ℝ) ≤ 1 / (Δ : ℝ) ^ 4 := by
        rw [molloy_prob_c A c]
        have hprod_exp : (∏ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
            ((A v).card : ℝ) / ((A v).card + 1 : ℝ)) ≤
            Real.exp (- ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
              (1 : ℝ) / ((A v).card + 1 : ℝ)) := by
          rw [Real.exp_neg, Real.exp_sum, ← Finset.prod_inv_distrib]
          calc ∏ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
                ((A v).card : ℝ) / ((A v).card + 1 : ℝ)
              = ∏ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
                  (1 - (1 : ℝ) / ((A v).card + 1 : ℝ)) := by
                refine Finset.prod_congr rfl fun v _ => ?_
                have hpos : (0 : ℝ) < ((A v).card : ℝ) + 1 := Nat.cast_add_one_pos _
                field_simp
                ring
            _ ≤ ∏ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
                  (Real.exp ((1 : ℝ) / ((A v).card + 1 : ℝ)))⁻¹ := by
                refine Finset.prod_le_prod (fun v _ => ?_) fun v _ => ?_
                · have hpos : (0 : ℝ) < ((A v).card : ℝ) + 1 := Nat.cast_add_one_pos _
                  rw [sub_nonneg, div_le_one hpos]
                  linarith [Nat.cast_nonneg (α := ℝ) (A v).card]
                · rw [← Real.exp_neg]
                  linarith [Real.add_one_le_exp (-((1 : ℝ) / ((A v).card + 1 : ℝ)))]
        have hsum_eq : ∑ v ∈ Finset.univ.filter (fun v : S => c ∈ A v),
            (1 : ℝ) / ((A v).card + 1 : ℝ) = μc := by
          dsimp only [μc, A₁]
          rw [← Finset.sum_coe_sort (Finset.univ.filter (fun v : S => c ∈ A v))
            (fun v => (1 : ℝ) / ((A v).card + 1 : ℝ))]
          refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun v => by simp) _ _ fun v => rfl
        rw [hsum_eq] at hprod_exp
        have hexp4 : Real.exp (-μc) ≤ 1 / (Δ : ℝ) ^ 4 := by
          have harg : -μc ≤ Real.log (1 / (Δ : ℝ) ^ 4) := by
            rw [one_div, Real.log_inv, Real.log_pow]
            push_cast
            linarith
          calc Real.exp (-μc) ≤ Real.exp (Real.log (1 / (Δ : ℝ) ^ 4)) := Real.exp_le_exp.mpr harg
            _ = 1 / (Δ : ℝ) ^ 4 := Real.exp_log (by positivity)
        exact hprod_exp.trans hexp4
      exact hle1.trans ((div_le_iff₀ hVpos).mp hprob_le)
    · push Not at hμ
      have hsub : (validPart A).filter (fun ω => (∀ v : S, ω v ≠ some c) ∧
          ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card) ⊆
          (validPart A).filter (fun ω =>
            ((ℓ : ℝ) / 32) ≤ ((Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card : ℝ)) := by
        intro ω hω
        simp only [Finset.mem_filter] at hω ⊢
        refine ⟨hω.1, ?_⟩
        have hlt := hω.2.2
        have hnat : ℓ ≤ 32 * (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card := by omega
        have hR : (ℓ : ℝ) ≤ 32 * ((Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card : ℝ) := by
          exact_mod_cast hnat
        linarith
      have hle1 : (((validPart A).filter (fun ω => (∀ v : S, ω v ≠ some c) ∧
          ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card)).card : ℝ) ≤
          (((validPart A).filter (fun ω =>
            ((ℓ : ℝ) / 32) ≤ ((Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card : ℝ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hsplit := validPart_split_card A (fun v : S => c ∈ A v)
        (fun ω => ((ℓ : ℝ) / 32) ≤ ((Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card : ℝ))
        (fun ω₁ => ((ℓ : ℝ) / 32) ≤ ((Finset.univ.filter (fun v : S₁ => ω₁ v = none)).card : ℝ))
        (fun ω => by
          have hc_eq : (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card =
              (Finset.univ.filter (fun v : S₁ => ω v.1 = none)).card := by
            refine Finset.card_bij (fun v hv => ⟨v, (Finset.mem_filter.mp hv).2.1⟩) ?_ ?_ ?_
            · intro v hv
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
              exact hv.2
            · intro v₁ _ v₂ _ heq; exact congrArg Subtype.val heq
            · intro v hv
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
              exact ⟨v.1, by simp [v.2, hv], Subtype.eta v v.2⟩
          rw [hc_eq])
      have hsplit_all := validPart_split_card A (fun v : S => c ∈ A v)
        (fun _ => True) (fun _ => True) (fun _ => Iff.rfl)
      simp only [Finset.filter_true] at hsplit_all
      have hch := chernoff_upper_indep A₁ ((ℓ : ℝ) / 32) (4 * Real.log (Δ : ℝ)) hμ
      have hch_mul : (((validPart A).filter (fun ω =>
          ((ℓ : ℝ) / 32) ≤ ((Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card : ℝ))).card : ℝ) ≤
          Real.exp (4 * Real.log (Δ : ℝ) - Real.log 2 * ((ℓ : ℝ) / 32)) * ((validPart A).card : ℝ) := by
        rw [hsplit, hsplit_all]
        push_cast
        calc (((validPart A₁).filter (fun ω₁ => ((ℓ : ℝ) / 32) ≤
                ((Finset.univ.filter (fun v : S₁ => ω₁ v = none)).card : ℝ))).card : ℝ) *
              ((validPart (fun s : {s : S // ¬ c ∈ A s} => A s.1)).card : ℝ)
            ≤ (Real.exp (4 * Real.log (Δ : ℝ) - Real.log 2 * ((ℓ : ℝ) / 32)) *
                ((validPart A₁).card : ℝ)) *
                ((validPart (fun s : {s : S // ¬ c ∈ A s} => A s.1)).card : ℝ) :=
              mul_le_mul_of_nonneg_right hch (Nat.cast_nonneg _)
          _ = Real.exp (4 * Real.log (Δ : ℝ) - Real.log 2 * ((ℓ : ℝ) / 32)) *
                (((validPart A₁).card : ℝ) *
                  ((validPart (fun s : {s : S // ¬ c ∈ A s} => A s.1)).card : ℝ)) := by ring
      exact hle1.trans (hch_mul.trans (mul_le_mul_of_nonneg_right hexp_b (Nat.cast_nonneg _)))
  calc (badB.card : ℝ)
      ≤ ∑ c : Fin k, (((validPart A).filter (fun ω => (∀ v : S, ω v ≠ some c) ∧
          ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card)).card : ℝ) :=
        hcard_union
    _ ≤ ∑ _c : Fin k, (1 / (Δ : ℝ) ^ 4) * ((validPart A).card : ℝ) :=
        Finset.sum_le_sum fun c _ => hper_c c
    _ = (k : ℝ) * (1 / (Δ : ℝ) ^ 4) * ((validPart A).card : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ (1 / (32 * (Δ : ℝ) ^ 3)) * ((validPart A).card : ℝ) := by
        have hk_le : (k : ℝ) * (1 / (Δ : ℝ) ^ 4) ≤ 1 / (32 * (Δ : ℝ) ^ 3) := by
          rw [mul_one_div, div_le_div_iff₀ (pow_pos hΔpos 4) (by positivity)]
          calc (k : ℝ) * (32 * (Δ : ℝ) ^ 3) = (32 * (k : ℝ)) * (Δ : ℝ) ^ 3 := by ring
            _ ≤ (Δ : ℝ) * (Δ : ℝ) ^ 3 := by gcongr
            _ = 1 * (Δ : ℝ) ^ 4 := by ring
        exact mul_le_mul_of_nonneg_right hk_le (Nat.cast_nonneg _)

private lemma molloy_fiber_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (htf : G.CliqueFree 3)
    (Δ k ℓ : ℕ)
    (hdeg : ∀ v : V, (nbhd1 G v).card ≤ Δ)
    (_hΔ16 : 16 ≤ Δ) (_hℓ4 : 4 ≤ ℓ) (hk1 : 1 ≤ k)
    (hk32 : 32 * (k : ℝ) ≤ (Δ : ℝ))
    (hexp_k : 2 * (ℓ : ℝ) ≤ (k : ℝ) * Real.exp (-(Δ : ℝ) / (k : ℝ)))
    (hexp_a : Real.exp ((ℓ : ℝ) * Real.log 2 - (ℓ : ℝ)) ≤ 1 / (32 * (Δ : ℝ) ^ 3))
    (hexp_b : Real.exp (4 * Real.log (Δ : ℝ) - Real.log 2 * ((ℓ : ℝ) / 32)) ≤ 1 / (Δ : ℝ) ^ 4)
    (u : V) (J : {w : V // ¬ G.Adj u w} → Option (Fin k))
    (hf₀ : ∃ f₀ : PartialColoring G k, (fun w => f₀.1 w.1) = J) :
    let fiber : Finset (PartialColoring G k) :=
      Finset.univ.filter (fun f => (fun w => f.1 w.1) = J)
    ((badEvent G k ℓ u ∩ fiber).card : ℝ) ≤
      (1 / (16 * (Δ : ℝ) ^ 3)) * (fiber.card : ℝ) := by
  intro fiber
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  by_cases hJu : J ⟨u, G.loopless.irrefl u⟩ = none
  · obtain ⟨f₀, hf₀_eq⟩ := hf₀
    have hJprop : ∀ (w₁ w₂ : {w : V // ¬ G.Adj u w}) (c : Fin k),
        G.Adj w₁.1 w₂.1 → J w₁ = some c → J w₂ ≠ some c := by
      intro w₁ w₂ c hadj h1
      rw [← hf₀_eq] at h1 ⊢
      exact f₀.2 w₁.1 w₂.1 c hadj h1
    let S := {v : V // G.Adj u v}
    let A : S → Finset (Fin k) := fun v =>
      Finset.univ.filter (fun c => ∀ w : {w : V // ¬ G.Adj u w}, G.Adj v.1 w.1 → J w ≠ some c)
    have hno_edge_S : ∀ v₁ v₂ : S, ¬ G.Adj v₁.1 v₂.1 := by
      intro v₁ v₂ hadj
      apply htf {u, v₁.1, v₂.1}
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        · exact (hxy rfl).elim
        · exact v₁.2
        · exact v₂.2
        · exact v₁.2.symm
        · exact (hxy rfl).elim
        · exact hadj
        · exact v₂.2.symm
        · exact hadj.symm
        · exact (hxy rfl).elim
      · have huv1 : u ≠ v₁.1 := v₁.2.ne
        have huv2 : u ≠ v₂.1 := v₂.2.ne
        have hv12 : v₁.1 ≠ v₂.1 := hadj.ne
        rw [Finset.card_insert_of_notMem (by simp [huv1, huv2]),
          Finset.card_insert_of_notMem (by simp [hv12]), Finset.card_singleton]
    let toS : PartialColoring G k → (S → Option (Fin k)) := fun f v => f.1 v.1
    have hbij_mem : ∀ f ∈ fiber, toS f ∈ validPart A := by
      intro f hf
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      simp only [validPart, Finset.mem_filter, Finset.mem_univ, true_and, A, toS]
      intro v c hvc w hvw
      have hfw : f.1 w.1 = J w := congrFun hf w
      rw [← hfw]
      exact f.2 v.1 w.1 c hvw hvc
    let fromS : ∀ ω ∈ validPart A, PartialColoring G k := fun ω hω =>
      ⟨fun x => if h : G.Adj u x then ω ⟨x, h⟩ else J ⟨x, h⟩, by
        intro x y c hadj hx
        simp only [validPart, Finset.mem_filter, Finset.mem_univ, true_and, A] at hω
        by_cases hux : G.Adj u x <;> by_cases huy : G.Adj u y
        · exact (hno_edge_S ⟨x, hux⟩ ⟨y, huy⟩ hadj).elim
        · simp only [hux, ↓reduceDIte] at hx
          simp only [huy, ↓reduceDIte]
          exact hω ⟨x, hux⟩ c hx ⟨y, huy⟩ hadj
        · simp only [hux, ↓reduceDIte] at hx
          simp only [huy, ↓reduceDIte]
          intro hy
          exact hω ⟨y, huy⟩ c hy ⟨x, hux⟩ hadj.symm hx
        · simp only [hux, ↓reduceDIte] at hx
          simp only [huy, ↓reduceDIte]
          exact hJprop ⟨x, hux⟩ ⟨y, huy⟩ c hadj hx⟩
    have hcard_fiber : fiber.card = (validPart A).card := by
      refine Finset.card_bij (fun f _ => toS f) hbij_mem ?_ ?_
      · intro f₁ hf₁ f₂ hf₂ heq
        simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
        apply Subtype.ext
        funext x
        by_cases hux : G.Adj u x
        · exact congrFun heq ⟨x, hux⟩
        · have h1 := congrFun hf₁ ⟨x, hux⟩
          have h2 := congrFun hf₂ ⟨x, hux⟩
          exact h1.trans h2.symm
      · intro ω hω
        refine ⟨fromS ω hω, ?_, ?_⟩
        · simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, fromS]
          funext ⟨w, hw⟩
          simp [hw]
        · funext ⟨v, hv⟩
          simp [toS, fromS, hv]
    have hrem_u : ∀ f ∈ fiber, remList f u = availColors (toS f) := by
      intro f _
      ext c
      simp only [remList, availColors, Finset.mem_filter, Finset.mem_univ, true_and, toS]
      exact ⟨fun h v => h v.1 v.2, fun h w hw => h ⟨w, hw⟩⟩
    have hdeg_u : ∀ f ∈ fiber, ∀ c : Fin k,
        partialColorDeg f u c =
          (Finset.univ.filter (fun v : S => c ∈ A v ∧ toS f v = none)).card := by
      intro f hf c
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      simp only [partialColorDeg]
      refine Finset.card_bij (fun w hw => ⟨w, (Finset.mem_filter.mp hw).2.1⟩) ?_ ?_ ?_
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        refine ⟨?_, hw.2.1⟩
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        intro z hzw
        have hfz : f.1 z.1 = J z := congrFun hf z
        rw [← hfz]
        exact (Finset.mem_filter.mp hw.2.2).2 z.1 hzw
      · intro w₁ _ w₂ _ heq
        exact congrArg Subtype.val heq
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A] at hv
        refine ⟨v.1, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, remList]
        refine ⟨v.2, hv.2, fun z hvz => ?_⟩
        have huz : ¬ G.Adj u z := fun huz => hno_edge_S v ⟨z, huz⟩ hvz
        have hfz : f.1 z = J ⟨z, huz⟩ := congrFun hf ⟨z, huz⟩
        rw [hfz]
        exact hv.1 ⟨z, huz⟩ hvz
    let badA : Finset (S → Option (Fin k)) :=
      (validPart A).filter (fun ω => (availColors ω).card < ℓ)
    let badB : Finset (S → Option (Fin k)) :=
      (validPart A).filter (fun ω => ∃ c : Fin k, c ∈ availColors ω ∧
        ℓ / 32 < (Finset.univ.filter (fun v : S => c ∈ A v ∧ ω v = none)).card)
    have hbad_le : (badEvent G k ℓ u ∩ fiber).card ≤ badA.card + badB.card := by
      have hsub_toS : (badEvent G k ℓ u ∩ fiber).card ≤ (badA ∪ badB).card := by
        refine Finset.card_le_card_of_injOn toS ?_ ?_
        · intro f hf
          simp only [Finset.mem_coe, Finset.mem_inter] at hf
          have hf_fib := hf.2
          have hf_bad := hf.1
          simp only [badEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hf_bad
          rw [hrem_u f hf_fib] at hf_bad
          simp only [Finset.mem_coe, Finset.mem_union, badA, badB, Finset.mem_filter]
          have hmemA := hbij_mem f hf_fib
          rcases hf_bad.2 with ha | ⟨c, hc, hdeg_c⟩
          · left; exact ⟨hmemA, ha⟩
          · right; refine ⟨hmemA, c, hc, ?_⟩
            rwa [← hdeg_u f hf_fib c]
        · intro f₁ hf₁ f₂ hf₂ heq
          simp only [Finset.mem_coe, Finset.mem_inter, fiber, Finset.mem_filter,
            Finset.mem_univ, true_and] at hf₁ hf₂
          apply Subtype.ext
          funext x
          by_cases hux : G.Adj u x
          · exact congrFun heq ⟨x, hux⟩
          · exact (congrFun hf₁.2 ⟨x, hux⟩).trans (congrFun hf₂.2 ⟨x, hux⟩).symm
      exact hsub_toS.trans (Finset.card_union_le badA badB)
    have hS_le : Fintype.card S ≤ Δ := by
      have hsub : Fintype.card S = (nbhd1 G u).card := by
        rw [Fintype.card_subtype]
        congr
      rw [hsub]
      exact hdeg u
    have hbadA := molloy_badA_bound A hS_le hk1 hexp_k hexp_a
    have hbadB := molloy_badB_bound A hΔpos hk32 hexp_b
    calc ((badEvent G k ℓ u ∩ fiber).card : ℝ)
        ≤ (badA.card : ℝ) + (badB.card : ℝ) := by exact_mod_cast hbad_le
      _ ≤ (1 / (32 * (Δ : ℝ) ^ 3)) * ((validPart A).card : ℝ) +
            (1 / (32 * (Δ : ℝ) ^ 3)) * ((validPart A).card : ℝ) := add_le_add hbadA hbadB
      _ = (1 / (16 * (Δ : ℝ) ^ 3)) * ((validPart A).card : ℝ) := by ring
      _ = (1 / (16 * (Δ : ℝ) ^ 3)) * (fiber.card : ℝ) := by rw [hcard_fiber]
  · have hdisj : badEvent G k ℓ u ∩ fiber = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro f hf
      rw [Finset.mem_inter] at hf
      have hf1 : f.1 u = none := (Finset.mem_filter.mp hf.1).2.1
      have hf2 : f.1 u = J ⟨u, G.loopless.irrefl u⟩ :=
        congrFun (Finset.mem_filter.mp hf.2).2 ⟨u, G.loopless.irrefl u⟩
      exact hJu (hf2.symm.trans hf1)
    rw [hdisj, Finset.card_empty, Nat.cast_zero]
    positivity

theorem molloy_triangle_free (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ Δ₀ : ℕ, ∀ Δ ≥ Δ₀, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.CliqueFree 3 → (∀ v : V, (Finset.univ.filter (G.Adj v)).card ≤ Δ) →
      G.Colorable (Nat.ceil ((1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ))) := by
  obtain ⟨Δ₀, hΔ₀⟩ := molloy_params_exists δ hδ0 hδ1
  refine ⟨Δ₀, fun Δ hΔ {V} _ _ G _ htf hdeg => ?_⟩
  obtain ⟨hΔ16, hℓ4, hk1, hk32, hexp_k, hexp_a, hexp_b⟩ := hΔ₀ Δ hΔ
  set k := Nat.ceil ((1 + δ) * (Δ : ℝ) / Real.log (Δ : ℝ))
  set ℓ := Nat.floor ((Δ : ℝ) ^ (δ / 3))
  have hΔpos : (0 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hp0 : 0 ≤ 1 / (16 * (Δ : ℝ) ^ 3) := by positivity
  have hpd : 4 * (1 / (16 * (Δ : ℝ) ^ 3)) * (((3 * Δ ^ 3 : ℕ) : ℝ) + 1) ≤ 1 := by
    have hΔ1 : (1 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast (by omega : 1 ≤ Δ)
    push_cast
    rw [mul_one_div, div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [pow_pos hΔpos 2]
  have hΓ_card : ∀ u : V, (molloyGamma G u).card ≤ 3 * Δ ^ 3 :=
    molloyGamma_card G Δ (by omega) hdeg
  have hlop : ∀ u : V, ∀ T : Finset V, u ∉ T → (∀ v ∈ T, v ∉ molloyGamma G u) →
      ((badEvent G k ℓ u ∩ good (badEvent G k ℓ) T).card : ℝ) ≤
        (1 / (16 * (Δ : ℝ) ^ 3)) * ((good (badEvent G k ℓ) T).card : ℝ) := by
    intro u T huT hTΓ
    let Out := {w : V // ¬ G.Adj u w}
    let proj : PartialColoring G k → (Out → Option (Fin k)) := fun f w => f.1 w.1
    let fibers := (good (badEvent G k ℓ) T).image proj
    have hgood_fib : ((good (badEvent G k ℓ) T).card : ℝ) =
        ∑ J ∈ fibers, ((Finset.univ.filter (fun f : PartialColoring G k => proj f = J)).card : ℝ) := by
      have h1 : (good (badEvent G k ℓ) T).card =
          ∑ J ∈ fibers, ((good (badEvent G k ℓ) T).filter (fun f => proj f = J)).card := by
        exact Finset.card_eq_sum_card_fiberwise (fun f hf => Finset.mem_image_of_mem proj hf)
      rw [h1]
      push_cast
      refine Finset.sum_congr rfl fun J hJ => congrArg Nat.cast (congrArg Finset.card ?_)
      obtain ⟨f₀, hf₀_good, hf₀_proj⟩ := Finset.mem_image.mp hJ
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hf; exact hf.2
      · intro hf_proj
        refine ⟨?_, hf_proj⟩
        simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hf₀_good ⊢
        intro v hvT
        have hvu : v ≠ u := fun h => huT (h ▸ hvT)
        have hcongr := mem_badEvent_congr G k ℓ u v hvu (hTΓ v hvT) f f₀
          (fun w hw => congrFun (hf_proj.trans hf₀_proj.symm) ⟨w, hw⟩)
        rw [hcongr]
        exact hf₀_good v hvT
    have hbad_fib : ((badEvent G k ℓ u ∩ good (badEvent G k ℓ) T).card : ℝ) =
        ∑ J ∈ fibers, ((badEvent G k ℓ u ∩
          Finset.univ.filter (fun f : PartialColoring G k => proj f = J)).card : ℝ) := by
      have h1 : (badEvent G k ℓ u ∩ good (badEvent G k ℓ) T).card =
          ∑ J ∈ fibers, ((badEvent G k ℓ u ∩ good (badEvent G k ℓ) T).filter
            (fun f => proj f = J)).card := by
        refine Finset.card_eq_sum_card_fiberwise (fun f hf => ?_)
        exact Finset.mem_image_of_mem proj (Finset.mem_inter.mp hf).2
      rw [h1]
      push_cast
      refine Finset.sum_congr rfl fun J hJ => congrArg Nat.cast (congrArg Finset.card ?_)
      obtain ⟨f₀, hf₀_good, hf₀_proj⟩ := Finset.mem_image.mp hJ
      ext f
      simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hfbad, _⟩, hfproj⟩; exact ⟨hfbad, hfproj⟩
      · rintro ⟨hfbad, hfproj⟩
        refine ⟨⟨hfbad, ?_⟩, hfproj⟩
        simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hf₀_good ⊢
        intro v hvT
        have hvu : v ≠ u := fun h => huT (h ▸ hvT)
        have hcongr := mem_badEvent_congr G k ℓ u v hvu (hTΓ v hvT) f f₀
          (fun w hw => congrFun (hfproj.trans hf₀_proj.symm) ⟨w, hw⟩)
        rw [hcongr]
        exact hf₀_good v hvT
    rw [hbad_fib, hgood_fib, Finset.mul_sum]
    refine Finset.sum_le_sum fun J hJ => ?_
    obtain ⟨f₀, _, hf₀_proj⟩ := Finset.mem_image.mp hJ
    exact molloy_fiber_bound G htf Δ k ℓ hdeg hΔ16 hℓ4 hk1 hk32 hexp_k hexp_a hexp_b u J ⟨f₀, hf₀_proj⟩
  obtain ⟨f, hf⟩ := lll_symmetric (badEvent G k ℓ) (molloyGamma G)
    (1 / (16 * (Δ : ℝ) ^ 3)) (3 * Δ ^ 3) hp0 hpd hΓ_card hlop
  let U := {u : V // f.1 u = none}
  let GU : SimpleGraph U := G.induce {u : V | f.1 u = none}
  let LU : U → Finset (Fin k) := fun u => remList f u.1
  have hLU_card : ∀ u : U, ℓ ≤ (LU u).card := by
    intro u
    by_contra hlt
    have h1 := hf u.1
    simp only [badEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at h1
    exact h1 u.2 (Or.inl (Nat.lt_of_not_le hlt))
  have hLU_deg : ∀ u : U, ∀ c ∈ LU u,
      (Finset.univ.filter (fun w : U => GU.Adj u w ∧ c ∈ LU w)).card ≤ ℓ / 32 := by
    intro u c hc
    by_contra hlt
    have h1 := hf u.1
    simp only [badEvent, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at h1
    apply h1 u.2
    right
    refine ⟨c, hc, ?_⟩
    have hle : (Finset.univ.filter (fun w : U => GU.Adj u w ∧ c ∈ LU w)).card ≤
        partialColorDeg f u.1 c := by
      refine Finset.card_le_card_of_injOn (fun w : U => w.1) ?_ ?_
      · intro w hw
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        exact ⟨hw.1, w.2, hw.2⟩
      · intro w₁ _ w₂ _ heq; exact Subtype.ext heq
    exact lt_of_lt_of_le (Nat.lt_of_not_le hlt) hle
  obtain ⟨g, hg_mem, hg_adj⟩ := list_colorable_of_small_deg GU LU ℓ (ℓ / 32)
    hℓ4 hLU_card (Nat.mul_div_le ℓ 32) hLU_deg
  let col : V → Fin k := fun v =>
    if h : f.1 v = none then g ⟨v, h⟩
    else (f.1 v).get (Option.isSome_iff_ne_none.mpr h)
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro u v huv heq
  dsimp only [col] at heq
  by_cases hu : f.1 u = none <;> by_cases hv : f.1 v = none
  · simp only [hu, hv, ↓reduceDIte] at heq
    exact hg_adj ⟨u, hu⟩ ⟨v, hv⟩ huv heq
  · obtain ⟨cv, hcv⟩ := Option.ne_none_iff_exists'.mp hv
    simp only [hu, hv, ↓reduceDIte] at heq
    have hmem : g ⟨u, hu⟩ ∈ LU ⟨u, hu⟩ := hg_mem ⟨u, hu⟩
    simp only [LU, remList, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hget : (f.1 v).get (Option.isSome_iff_ne_none.mpr hv) = cv := by simp [hcv]
    rw [hget] at heq
    exact hmem v huv (by rw [hcv, heq])
  · obtain ⟨cu, hcu⟩ := Option.ne_none_iff_exists'.mp hu
    simp only [hu, hv, ↓reduceDIte] at heq
    have hmem : g ⟨v, hv⟩ ∈ LU ⟨v, hv⟩ := hg_mem ⟨v, hv⟩
    simp only [LU, remList, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hget : (f.1 u).get (Option.isSome_iff_ne_none.mpr hu) = cu := by simp [hcu]
    rw [hget] at heq
    exact hmem u huv.symm (by rw [hcu, heq])
  · obtain ⟨cu, hcu⟩ := Option.ne_none_iff_exists'.mp hu
    obtain ⟨cv, hcv⟩ := Option.ne_none_iff_exists'.mp hv
    simp only [hu, hv, ↓reduceDIte] at heq
    have hgetu : (f.1 u).get (Option.isSome_iff_ne_none.mpr hu) = cu := by simp [hcu]
    have hgetv : (f.1 v).get (Option.isSome_iff_ne_none.mpr hv) = cv := by simp [hcv]
    rw [hgetu, hgetv] at heq
    exact f.2 u v cu huv hcu (by rw [hcv, heq])

end Molloy

section DaviesIllingworth

private def diFun (x : ℝ) : ℝ := Real.sqrt (x / Real.log x)

private lemma log_ge_two_of_ge_16 {x : ℝ} (hx : 16 ≤ x) : 2 ≤ Real.log x := by
  have he : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have he2 : Real.exp 2 < 16 := by
    have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    have hpow : (Real.exp 1) ^ 2 ≤ (2.72 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le he 2
    linarith [show (2.72 : ℝ) ^ 2 < 16 by norm_num]
  have hex : Real.exp 2 ≤ x := le_trans he2.le hx
  calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 2) hex

private lemma diFun_hasDerivAt {x : ℝ} (hx : 16 ≤ x) :
    HasDerivAt diFun (((Real.log x - 1) / (Real.log x) ^ 2) / (2 * Real.sqrt (x / Real.log x))) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog2 : 2 ≤ Real.log x := log_ge_two_of_ge_16 hx
  have hlog0 : Real.log x ≠ 0 := by linarith
  have hdiv_pos : 0 < x / Real.log x := div_pos (by linarith) (by linarith)
  have hinner : HasDerivAt (fun t : ℝ => t / Real.log t)
      ((1 * Real.log x - x * x⁻¹) / (Real.log x) ^ 2) x :=
    (hasDerivAt_id x).div (Real.hasDerivAt_log hx0) hlog0
  have hinner' : HasDerivAt (fun t : ℝ => t / Real.log t)
      ((Real.log x - 1) / (Real.log x) ^ 2) x := by
    convert hinner using 2
    rw [one_mul, mul_inv_cancel₀ hx0]
  unfold diFun
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hinner'.sqrt hdiv_pos.ne'

private lemma diFun_monotoneOn : MonotoneOn diFun (Set.Ici 16) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 16)
    (f' := fun x => ((Real.log x - 1) / (Real.log x) ^ 2) / (2 * Real.sqrt (x / Real.log x)))
    ?_ ?_ ?_
  · intro x hx
    exact (diFun_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (diFun_hasDerivAt (le_of_lt hx)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx16 : 16 ≤ x := le_of_lt hx
    have hlog2 : 2 ≤ Real.log x := log_ge_two_of_ge_16 hx16
    have hnum : 0 ≤ Real.log x - 1 := by linarith
    positivity

private lemma diFun_mvt_diff {n : ℕ} {a : ℝ} (ha16 : 16 ≤ a) (han : a < (n : ℝ)) :
    ((n : ℝ) - a) * ((1 - 1 / Real.log a) / (2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))) ≤
      diFun (n : ℝ) - diFun a := by
  have hcont : ContinuousOn diFun (Set.Icc a (n : ℝ)) := fun x hx =>
    (diFun_hasDerivAt (ha16.trans hx.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo a (n : ℝ),
      HasDerivAt diFun (((Real.log x - 1) / (Real.log x) ^ 2) / (2 * Real.sqrt (x / Real.log x))) x :=
    fun x hx => diFun_hasDerivAt (ha16.trans hx.1.le)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope diFun _ han hcont hderiv
  have hc16 : 16 ≤ c := ha16.trans hc.1.le
  have hlog_a : 2 ≤ Real.log a := log_ge_two_of_ge_16 ha16
  have hlog_c : 2 ≤ Real.log c := log_ge_two_of_ge_16 hc16
  have hlog_ac : Real.log a ≤ Real.log c := Real.log_le_log (by linarith) hc.1.le
  have hlog_cn : Real.log c ≤ Real.log (n : ℝ) := Real.log_le_log (by linarith) hc.2.le
  have hden_eq : Real.log c * Real.sqrt (c / Real.log c) = Real.sqrt (c * Real.log c) := by
    have hlogpos : 0 < Real.log c := by linarith
    conv_lhs => arg 1; rw [← Real.sqrt_sq hlogpos.le]
    rw [← Real.sqrt_mul (sq_nonneg (Real.log c))]
    refine congrArg Real.sqrt ?_
    rw [sq, mul_assoc, mul_div_cancel₀ c hlogpos.ne', mul_comm]
  have hderiv_eq : ((Real.log c - 1) / (Real.log c) ^ 2) / (2 * Real.sqrt (c / Real.log c)) =
      (1 - 1 / Real.log c) / (2 * Real.sqrt (c * Real.log c)) := by
    have hlog0 : Real.log c ≠ 0 := by linarith
    calc ((Real.log c - 1) / (Real.log c) ^ 2) / (2 * Real.sqrt (c / Real.log c))
        = ((Real.log c - 1) / Real.log c) / (2 * (Real.log c * Real.sqrt (c / Real.log c))) := by
          field_simp [hlog0]
      _ = (1 - 1 / Real.log c) / (2 * Real.sqrt (c * Real.log c)) := by
          rw [hden_eq]
          congr 1
          field_simp [hlog0]
  have hderiv_ge : (1 - 1 / Real.log a) / (2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      (1 - 1 / Real.log c) / (2 * Real.sqrt (c * Real.log c)) := by
    have hnum : 1 - 1 / Real.log a ≤ 1 - 1 / Real.log c := by
      have : 1 / Real.log c ≤ 1 / Real.log a := one_div_le_one_div_of_le (by linarith) hlog_ac
      linarith
    have hnum_nn : 0 ≤ 1 - 1 / Real.log c := by
      have : 1 / Real.log c ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have hden_le : Real.sqrt (c * Real.log c) ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact mul_le_mul hc.2.le hlog_cn (by linarith) (by linarith)
    have hden_pos : 0 < 2 * Real.sqrt (c * Real.log c) := by
      have : 0 < c * Real.log c := mul_pos (by linarith) (by linarith)
      exact mul_pos (by norm_num) (Real.sqrt_pos.mpr this)
    exact div_le_div₀ hnum_nn hnum hden_pos (by linarith)
  have hsub_pos : 0 < (n : ℝ) - a := sub_pos.mpr han
  have hslope' : (1 - 1 / Real.log a) / (2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ≤
      (diFun (n : ℝ) - diFun a) / ((n : ℝ) - a) := by
    rw [← hslope, hderiv_eq]
    exact hderiv_ge
  exact (le_div_iff₀' hsub_pos).mp hslope'

private lemma di_params_exists (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (Δ₀ : ℕ) :
    ∃ N₀ : ℕ, 100 ≤ N₀ ∧ ∀ n ≥ N₀,
      let d := Nat.floor (Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
      16 ≤ n ∧ Δ₀ ≤ d ∧ 16 ≤ d ∧
        (n : ℝ) / 2 ≤ (n : ℝ) - Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ∧
        1 / Real.log ((n : ℝ) / 2) ≤ δ / 2 ∧
        (Nat.ceil ((1 + δ) * (d : ℝ) / Real.log (d : ℝ)) : ℝ) ≤ (2 + 4 * δ) * diFun (n : ℝ) := by
  have hc_logn : ∀ᶠ x : ℝ in atTop, 100 ≤ x := eventually_ge_atTop 100
  have hlog_ge : ∀ᶠ x : ℝ in atTop, 2 / δ ≤ Real.log (x / 2) :=
    (Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).eventually
      (eventually_ge_atTop (2 / δ))
  have hlog_big : ∀ᶠ x : ℝ in atTop,
      (2 * (2 + δ) * Real.log 2) / δ ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  have ho_id : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (1 / 4 : ℝ) * ‖x ^ (1 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).bound (by norm_num)
  have ho_half : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (δ ^ 2 / 4 : ℝ) * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound (by positivity)
  have hsqrt_big : ∀ᶠ x : ℝ in atTop, ((Δ₀ : ℝ) + 17) ^ 2 ≤ x :=
    eventually_ge_atTop (((Δ₀ : ℝ) + 17) ^ 2)
  have hevR : ∀ᶠ x : ℝ in atTop,
      100 ≤ x ∧ 2 / δ ≤ Real.log (x / 2) ∧
        (2 * (2 + δ) * Real.log 2) / δ ≤ Real.log x ∧
        Real.log x ≤ (1 / 4) * x ∧
        Real.log x ≤ (δ ^ 2 / 4) * Real.sqrt x ∧
        ((Δ₀ : ℝ) + 17) ^ 2 ≤ x := by
    filter_upwards [hc_logn, hlog_ge, hlog_big, ho_id, ho_half, hsqrt_big] with x h1 h2 h3 h4 h5 h6
    have hxpos : 0 ≤ x := by linarith
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg hlognn, Real.rpow_one, Real.norm_of_nonneg hxpos] at h4
    rw [Real.norm_of_nonneg hlognn, ← Real.sqrt_eq_rpow,
      Real.norm_of_nonneg (Real.sqrt_nonneg x)] at h5
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hevN : ∀ᶠ n : ℕ in atTop,
      100 ≤ (n : ℝ) ∧ 2 / δ ≤ Real.log ((n : ℝ) / 2) ∧
        (2 * (2 + δ) * Real.log 2) / δ ≤ Real.log (n : ℝ) ∧
        Real.log (n : ℝ) ≤ (1 / 4) * (n : ℝ) ∧
        Real.log (n : ℝ) ≤ (δ ^ 2 / 4) * Real.sqrt (n : ℝ) ∧
        ((Δ₀ : ℝ) + 17) ^ 2 ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hevR
  rw [Filter.eventually_atTop] at hevN
  obtain ⟨N₁, hN₁⟩ := hevN
  refine ⟨max 100 N₁, le_max_left 100 N₁, fun n hn => ?_⟩
  have hn100 : 100 ≤ n := le_trans (le_max_left 100 N₁) hn
  have hnN₁ : N₁ ≤ n := le_trans (le_max_right 100 N₁) hn
  obtain ⟨hn100R, hlog2_ge, hlog_n_big, hlog_lin, hlog_sqrt, hsqrt_n_big⟩ := hN₁ n hnN₁
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_n_pos : 1 ≤ Real.log (n : ℝ) := by
    have hle : Real.log ((n : ℝ) / 2) ≤ Real.log (n : ℝ) := Real.log_le_log (by linarith) (by linarith)
    have h4 : (4 : ℝ) ≤ 2 / δ := by rw [le_div_iff₀ hδ0]; linarith
    linarith
  dsimp only
  set d := Nat.floor (Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact le_mul_of_one_le_right hnpos.le hlog_n_pos
  have hsqrt_ge : (Δ₀ : ℝ) + 17 ≤ Real.sqrt (n : ℝ) := by
    have h1 : Real.sqrt (((Δ₀ : ℝ) + 17) ^ 2) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hsqrt_n_big
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hd_gt : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) - 1 < (d : ℝ) := Nat.sub_one_lt_floor _
  have hd_le : (d : ℝ) ≤ Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hd_ge_half : Real.sqrt (n : ℝ) / 2 ≤ (d : ℝ) := by linarith
  have hΔd : Δ₀ ≤ d := by exact_mod_cast (by linarith : (Δ₀ : ℝ) ≤ (d : ℝ))
  have hd16 : 16 ≤ d := by exact_mod_cast (by linarith : (16 : ℝ) ≤ (d : ℝ))
  have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
    have hmul : (n : ℝ) * Real.log (n : ℝ) ≤ ((n : ℝ) / 2) ^ 2 := by nlinarith
    have hsqrt : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (n : ℝ) / 2 := by
      calc Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
          ≤ Real.sqrt (((n : ℝ) / 2) ^ 2) := Real.sqrt_le_sqrt hmul
        _ = (n : ℝ) / 2 := Real.sqrt_sq (by linarith)
    linarith
  have hinv_log : 1 / Real.log ((n : ℝ) / 2) ≤ δ / 2 := by
    have h4 : (4 : ℝ) ≤ 2 / δ := by rw [le_div_iff₀ hδ0]; linarith
    have hlpos : 0 < Real.log ((n : ℝ) / 2) := by linarith
    rw [div_le_div_iff₀ hlpos (by norm_num)]
    have hmul := (div_le_iff₀ hδ0).mp hlog2_ge
    nlinarith
  have hceil_le : (Nat.ceil ((1 + δ) * (d : ℝ) / Real.log (d : ℝ)) : ℝ) ≤
      (2 + 4 * δ) * diFun (n : ℝ) := by
    have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith [show (16 : ℝ) ≤ (d : ℝ) by exact_mod_cast hd16]
    have hlogd_ge2 : 2 ≤ Real.log (d : ℝ) := log_ge_two_of_ge_16 (by exact_mod_cast hd16)
    have hlogd_lower : (1 / (2 + δ)) * Real.log (n : ℝ) ≤ Real.log (d : ℝ) := by
      have h1 : Real.log (Real.sqrt (n : ℝ) / 2) ≤ Real.log (d : ℝ) :=
        Real.log_le_log (div_pos (Real.sqrt_pos.mpr hnpos) (by norm_num)) hd_ge_half
      have h2 : Real.log (Real.sqrt (n : ℝ) / 2) = (1 / 2) * Real.log (n : ℝ) - Real.log 2 := by
        rw [Real.log_div (Real.sqrt_pos.mpr hnpos).ne' (by norm_num), Real.sqrt_eq_rpow,
          Real.log_rpow hnpos]
      have h3 : Real.log 2 ≤ (δ / (2 * (2 + δ))) * Real.log (n : ℝ) := by
        have hm := (div_le_iff₀ hδ0).mp hlog_n_big
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (2 + δ))]
        nlinarith
      have h4 : (1 / (2 + δ)) * Real.log (n : ℝ) = (1 / 2) * Real.log (n : ℝ) -
          (δ / (2 * (2 + δ))) * Real.log (n : ℝ) := by
        field_simp
        ring
      linarith
    have hterm_le : (1 + δ) * (d : ℝ) / Real.log (d : ℝ) ≤ (2 + 7 / 2 * δ) * diFun (n : ℝ) := by
      have hmain_div : (1 + δ) * (d : ℝ) / Real.log (d : ℝ) ≤
          (1 + δ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) /
            ((1 / (2 + δ)) * Real.log (n : ℝ)) := by
        apply div_le_div₀ (by positivity)
        · exact mul_le_mul_of_nonneg_left hd_le (by linarith)
        · exact mul_pos (by positivity) (by linarith)
        · exact hlogd_lower
      have hsqrt_id : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / Real.log (n : ℝ) = diFun (n : ℝ) := by
        have hl : 0 < Real.log (n : ℝ) := by linarith
        rw [diFun, Real.sqrt_div hnpos.le, Real.sqrt_mul hnpos.le]
        have hsq : Real.sqrt (Real.log (n : ℝ)) * Real.sqrt (Real.log (n : ℝ)) = Real.log (n : ℝ) :=
          Real.mul_self_sqrt hl.le
        conv_lhs => arg 2; rw [← hsq]
        field_simp [Real.sqrt_ne_zero'.mpr hl]
      have hsimp : (1 + δ) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) /
            ((1 / (2 + δ)) * Real.log (n : ℝ)) =
          ((1 + δ) * (2 + δ)) * diFun (n : ℝ) := by
        rw [← hsqrt_id]
        field_simp [(by linarith : (0 : ℝ) < 2 + δ).ne', (by linarith : (0 : ℝ) < Real.log (n : ℝ)).ne']
      have hcoeff : (1 + δ) * (2 + δ) ≤ 2 + 7 / 2 * δ := by nlinarith
      have hdi_nn : 0 ≤ diFun (n : ℝ) := Real.sqrt_nonneg _
      exact hmain_div.trans (by rw [hsimp]; exact mul_le_mul_of_nonneg_right hcoeff hdi_nn)
    have h1_le_di : 1 ≤ (δ / 2) * diFun (n : ℝ) := by
      have hdi_sq : (2 / δ) ^ 2 ≤ (diFun (n : ℝ)) ^ 2 := by
        have hl : 0 < Real.log (n : ℝ) := by linarith
        rw [diFun, Real.sq_sqrt (div_nonneg hnpos.le hl.le), le_div_iff₀ hl]
        have h1 : (2 / δ) ^ 2 * Real.log (n : ℝ) = (4 / δ ^ 2) * Real.log (n : ℝ) := by ring
        rw [h1]
        have h2 : (4 / δ ^ 2) * Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) := by
          calc (4 / δ ^ 2) * Real.log (n : ℝ)
              ≤ (4 / δ ^ 2) * ((δ ^ 2 / 4) * Real.sqrt (n : ℝ)) :=
                mul_le_mul_of_nonneg_left hlog_sqrt (by positivity)
            _ = Real.sqrt (n : ℝ) := by field_simp [hδ0.ne']
        have h3 : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
          calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) :=
                Real.sqrt_le_sqrt (by nlinarith)
            _ = (n : ℝ) := Real.sqrt_sq hnpos.le
        exact h2.trans h3
      have h2δ : 2 / δ ≤ diFun (n : ℝ) := by
        have hsq := Real.sqrt_le_sqrt hdi_sq
        rw [Real.sqrt_sq (by positivity)] at hsq
        change 2 / δ ≤ Real.sqrt (Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) ^ 2) at hsq
        rwa [Real.sqrt_sq (Real.sqrt_nonneg _)] at hsq
      have hmul := mul_le_mul_of_nonneg_left h2δ (by positivity : 0 ≤ δ / 2)
      rwa [show (δ / 2) * (2 / δ) = 1 by field_simp [hδ0.ne']] at hmul
    have hceil_lt : (Nat.ceil ((1 + δ) * (d : ℝ) / Real.log (d : ℝ)) : ℝ) <
        (1 + δ) * (d : ℝ) / Real.log (d : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith
  refine ⟨by omega, hΔd, hd16, hhalf, hinv_log, hceil_le⟩

private lemma di_remove_nbhd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htf : G.CliqueFree 3) (v : Fin n) :
    let m := (Finset.univ.filter (G.Adj v)).card
    ∃ (G' : SimpleGraph (Fin (n - m))), G'.CliqueFree 3 ∧
      ∀ k' : ℕ, G'.Colorable k' → G.Colorable (k' + 1) := by
  intro m
  let R := Finset.univ.filter (fun w : Fin n => ¬ G.Adj v w)
  have hmR : m + R.card = n := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun w => G.Adj v w)
    simpa [m, R] using h
  have hcard_R : R.card = n - m := by omega
  have hcard_sub : Fintype.card {w : Fin n // ¬ G.Adj v w} = n - m := by
    rw [Fintype.card_subtype]
    exact hcard_R
  let e : {w : Fin n // ¬ G.Adj v w} ≃ Fin (n - m) := Fintype.equivFinOfCardEq hcard_sub
  let G' : SimpleGraph (Fin (n - m)) := SimpleGraph.comap (fun i => (e.symm i).1) G
  refine ⟨G', ?_, ?_⟩
  · intro s hs
    apply htf (s.image (fun i => (e.symm i).1))
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨j, hj, rfl⟩ := hy
      have hij : i ≠ j := fun heq => hxy (by rw [heq])
      exact hs.1 hi hj hij
    · rw [Finset.card_image_of_injective _ (fun i j heq =>
        e.symm.injective (Subtype.ext heq))]
      exact hs.2
  · intro k' ⟨c'⟩
    let col : Fin n → Fin (k' + 1) := fun w =>
      if h : G.Adj v w then Fin.last k'
      else (c' (e ⟨w, h⟩)).castSucc
    refine ⟨SimpleGraph.Coloring.mk col ?_⟩
    intro x y hxy heq
    dsimp only [col] at heq
    by_cases hx : G.Adj v x <;> by_cases hy : G.Adj v y
    · apply htf {v, x, y}
      refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact (hab rfl).elim
        · exact hx
        · exact hy
        · exact hx.symm
        · exact (hab rfl).elim
        · exact hxy
        · exact hy.symm
        · exact hxy.symm
        · exact (hab rfl).elim
      · have hvx : v ≠ x := hx.ne
        have hvy : v ≠ y := hy.ne
        have hxy_ne : x ≠ y := hxy.ne
        rw [Finset.card_insert_of_notMem (by simp [hvx, hvy]),
          Finset.card_insert_of_notMem (by simp [hxy_ne]), Finset.card_singleton]
    · simp only [hx, hy, ↓reduceDIte] at heq
      exact (Fin.castSucc_lt_last _).ne heq.symm
    · simp only [hx, hy, ↓reduceDIte] at heq
      exact (Fin.castSucc_lt_last _).ne heq
    · simp only [hx, hy, ↓reduceDIte] at heq
      have hceq : c' (e ⟨x, hx⟩) = c' (e ⟨y, hy⟩) := Fin.castSucc_injective k' heq
      have hadj' : G'.Adj (e ⟨x, hx⟩) (e ⟨y, hy⟩) := by
        simpa [G'] using hxy
      exact c'.valid hadj' hceq

private lemma di_induction (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
      ∃ k : ℕ, G.Colorable k ∧
        (k : ℝ) ≤ (2 + 4 * δ) * (if n < 16 then 0 else diFun (n : ℝ)) + (N₀ : ℝ) := by
  obtain ⟨Δ₀, hΔ₀⟩ := molloy_triangle_free δ hδ0 (by linarith)
  obtain ⟨N₀, hN₀100, hN₀_prop⟩ := di_params_exists δ hδ0 hδ1 Δ₀
  refine ⟨N₀, by omega, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G htf
    let := Classical.decRel G.Adj
    by_cases hn : n < N₀
    · refine ⟨n, by simpa using G.colorable_of_fintype, ?_⟩
      have hnonneg : 0 ≤ (2 + 4 * δ) * (if n < 16 then 0 else diFun (n : ℝ)) := by
        split_ifs
        · norm_num
        · exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
      have hnle : (n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hn.le
      linarith
    · have hnN₀ : N₀ ≤ n := Nat.le_of_not_lt hn
      obtain ⟨hn16, hΔd, hd16, hhalf, hinv_log, hceil_le⟩ := hN₀_prop n hnN₀
      have hn_not_lt : ¬ n < 16 := not_lt.mpr hn16
      simp only [hn_not_lt, ↓reduceIte]
      set d := Nat.floor (Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
      by_cases hdeg : ∀ v : Fin n, (Finset.univ.filter (G.Adj v)).card ≤ d
      · have hcol := hΔ₀ d hΔd G htf hdeg
        refine ⟨Nat.ceil ((1 + δ) * (d : ℝ) / Real.log (d : ℝ)), hcol, ?_⟩
        have hN₀nn : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
        linarith
      · push Not at hdeg
        obtain ⟨v, hv⟩ := hdeg
        set m := (Finset.univ.filter (G.Adj v)).card
        have hm_pos : 0 < m := by omega
        have hm_le : m ≤ n := by
          simpa [m] using Finset.card_le_univ (Finset.univ.filter (G.Adj v))
        have hn'_lt : n - m < n := Nat.sub_lt (by omega) hm_pos
        obtain ⟨G', hG'tf, hG'lift⟩ := di_remove_nbhd G htf v
        obtain ⟨k', hG'col, hk'le⟩ := ih (n - m) hn'_lt G' hG'tf
        refine ⟨k' + 1, hG'lift k' hG'col, ?_⟩
        have hdm : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) < (m : ℝ) := by
          have hdm_nat : d + 1 ≤ m := hv
          have h1 : (d : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hdm_nat
          have h2 : Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) < (d : ℝ) + 1 := Nat.lt_floor_add_one _
          linarith
        let a := (n : ℝ) - Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
        have han_lt : ((n - m : ℕ) : ℝ) < a := by
          rw [Nat.cast_sub hm_le]
          linarith
        have ha16 : 16 ≤ a := by
          have h16n : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 32 ≤ n)
          linarith
        have han : a < (n : ℝ) := by
          have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
          have hlog_ge2 : 2 ≤ Real.log (n : ℝ) := log_ge_two_of_ge_16 (by exact_mod_cast hn16)
          have hspos : 0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
            Real.sqrt_pos.mpr (mul_pos hnpos (by linarith))
          linarith
        have hg_le : (if n - m < 16 then 0 else diFun ((n - m : ℕ) : ℝ)) ≤ diFun a := by
          split_ifs with h16
          · exact Real.sqrt_nonneg _
          · have hn'16 : (16 : ℝ) ≤ ((n - m : ℕ) : ℝ) := by
              exact_mod_cast (Nat.le_of_not_lt h16)
            exact diFun_monotoneOn hn'16 ha16 han_lt.le
        have hmvt := diFun_mvt_diff ha16 han
        have hdiff_eq : (n : ℝ) - a = Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
          dsimp only [a]; ring
        have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by linarith
        have hlog_half : Real.log ((n : ℝ) / 2) ≤ Real.log a :=
          Real.log_le_log (by linarith) hhalf
        have h32n : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 32 ≤ n)
        have hlog2_pos : 0 < Real.log ((n : ℝ) / 2) :=
          lt_of_lt_of_le (by norm_num) (log_ge_two_of_ge_16 (by linarith))
        have hinv_a : 1 / Real.log a ≤ δ / 2 := by
          have h1 : 1 / Real.log a ≤ 1 / Real.log ((n : ℝ) / 2) :=
            one_div_le_one_div_of_le hlog2_pos hlog_half
          exact h1.trans hinv_log
        have hmul_eq : ((n : ℝ) - a) *
            ((1 - 1 / Real.log a) / (2 * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))) =
            (1 - 1 / Real.log a) / 2 := by
          rw [hdiff_eq]
          field_simp [hsqrt_pos.ne']
        rw [hmul_eq] at hmvt
        have hdiff_ge : (1 - δ / 2) / 2 ≤ diFun (n : ℝ) - diFun a := by linarith
        have hstep_gap : 1 ≤ (2 + 4 * δ) * (diFun (n : ℝ) - diFun a) := by
          have hmul1 : (2 + 4 * δ) * ((1 - δ / 2) / 2) ≤
              (2 + 4 * δ) * (diFun (n : ℝ) - diFun a) :=
            mul_le_mul_of_nonneg_left hdiff_ge (by linarith)
          have hquad : 1 ≤ (2 + 4 * δ) * ((1 - δ / 2) / 2) := by
            have hsimp : (2 + 4 * δ) * ((1 - δ / 2) / 2) = 1 + δ * (3 / 2 - δ) := by ring
            rw [hsimp]
            nlinarith
          exact hquad.trans hmul1
        have hcast : ((k' + 1 : ℕ) : ℝ) = (k' : ℝ) + 1 := by push_cast; ring
        have hk'_a : (k' : ℝ) ≤ (2 + 4 * δ) * diFun a + (N₀ : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_left hg_le (by linarith : 0 ≤ 2 + 4 * δ)
          linarith
        linarith

end DaviesIllingworth

end

end Erdos1104Upper

theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_lower_R1.H1 := by
  intro ε hε
  let δ := min (ε / 5) (1 / 2)
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have h4δ : 4 * δ ≤ (4 / 5) * ε := by
    have : δ ≤ ε / 5 := min_le_left _ _
    linarith
  obtain ⟨N₀, hN₀16, hcol_bound⟩ := Erdos1104Upper.di_induction δ hδ0 hδ1
  have ho_half : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.log x‖ ≤ ((ε / (5 * max (N₀ : ℝ) 1)) ^ 2 / 2 : ℝ) * ‖x ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound (by positivity)
  have hevR : ∀ᶠ x : ℝ in Filter.atTop,
      16 ≤ x ∧
        Real.log x ≤ (ε / (5 * max (N₀ : ℝ) 1)) ^ 2 * Real.sqrt x := by
    filter_upwards [Filter.eventually_ge_atTop 16, ho_half] with x hx16 hlog
    have hlognn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    rw [Real.norm_of_nonneg hlognn, ← Real.sqrt_eq_rpow,
      Real.norm_of_nonneg (Real.sqrt_nonneg x)] at hlog
    have hnn : 0 ≤ (ε / (5 * max (N₀ : ℝ) 1)) ^ 2 * Real.sqrt x := by positivity
    exact ⟨hx16, by linarith⟩
  have hevN : ∀ᶠ n : ℕ in Filter.atTop,
      16 ≤ (n : ℝ) ∧
        Real.log (n : ℝ) ≤ (ε / (5 * max (N₀ : ℝ) 1)) ^ 2 * Real.sqrt (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hevR
  filter_upwards [hevN] with n ⟨hn16R, hlogn_le⟩
  have hn16 : 16 ≤ n := by exact_mod_cast hn16R
  have hn_not_lt : ¬ n < 16 := not_lt.mpr hn16
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog_ge2 : 2 ≤ Real.log (n : ℝ) := by
    have he : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
    have he2 : Real.exp 2 < 16 := by
      have h2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h2]
      have hpow : (Real.exp 1) ^ 2 ≤ (2.72 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le he 2
      linarith [show (2.72 : ℝ) ^ 2 < 16 by norm_num]
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 2) (le_trans he2.le hn16R)
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith
  have hdi_eq : Erdos1104Upper.diFun (n : ℝ) = Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) :=
    Real.sqrt_div hnpos.le _
  have hN₀_le : (N₀ : ℝ) ≤ (ε / 5) * Erdos1104Upper.diFun (n : ℝ) := by
    let c := ε / (5 * max (N₀ : ℝ) 1)
    have hc_pos : 0 < c := by positivity
    have hsqrt_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = (n : ℝ) := Real.sqrt_sq hnpos.le
    have hsq : (1 / c) ^ 2 ≤ (Erdos1104Upper.diFun (n : ℝ)) ^ 2 := by
      rw [Erdos1104Upper.diFun, Real.sq_sqrt (div_nonneg hnpos.le hlogpos.le), le_div_iff₀ hlogpos]
      calc (1 / c) ^ 2 * Real.log (n : ℝ)
          ≤ (1 / c) ^ 2 * (c ^ 2 * Real.sqrt (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hlogn_le (by positivity)
        _ = Real.sqrt (n : ℝ) := by field_simp [hc_pos.ne']
        _ ≤ (n : ℝ) := hsqrt_le_n
    have h1c : 1 / c ≤ Erdos1104Upper.diFun (n : ℝ) := by
      have h1 := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq (by positivity)] at h1
      change 1 / c ≤ Real.sqrt (Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) ^ 2) at h1
      rwa [Real.sqrt_sq (Real.sqrt_nonneg _)] at h1
    have hmul := mul_le_mul_of_nonneg_left h1c (by positivity : 0 ≤ ε / 5)
    have hmax : (ε / 5) * (1 / c) = max (N₀ : ℝ) 1 := by
      dsimp only [c]
      field_simp [hε.ne']
    have hN₀_max : (N₀ : ℝ) ≤ max (N₀ : ℝ) 1 := le_max_left _ _
    linarith
  set K := Nat.floor ((2 + ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)))
  have hK_le : (K : ℝ) ≤ (2 + ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) :=
    Nat.floor_le (by positivity)
  have hsup_le : (sSup {χ : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ} : ℕ) ≤ K := by
    refine csSup_le' ?_
    rintro χ ⟨G, htf, hchr⟩
    obtain ⟨k, hGcol, hk_le⟩ := hcol_bound n G htf
    simp only [hn_not_lt, ↓reduceIte] at hk_le
    have hdi_nn : 0 ≤ Erdos1104Upper.diFun (n : ℝ) := Real.sqrt_nonneg _
    have hk_bound : (k : ℝ) ≤ (2 + ε) * Real.sqrt (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) := by
      rw [mul_div_assoc, ← hdi_eq]
      nlinarith
    have hk_le_K : k ≤ K := Nat.le_floor hk_bound
    have hGcolK : G.Colorable K := hGcol.mono hk_le_K
    have hchr_le : G.chromaticNumber ≤ (K : ℕ∞) :=
      SimpleGraph.chromaticNumber_le_iff_colorable.mpr hGcolK
    rw [hchr] at hchr_le
    exact_mod_cast hchr_le
  have hsup_leR : ((sSup {χ : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = χ} : ℕ) : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hsup_le
  exact hsup_leR.trans hK_le
