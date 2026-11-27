import OMAReductions.R_Erdos500_erdos_500_variants_turan_conjecture_R1

/-! Turán's construction lower bound `(5/9 - ε) * C(n, 3)` via complement counting. -/

open Finset Filter
open scoped Classical

private def col {n : ℕ} (v : Fin n) : Fin 3 :=
  ⟨v.val % 3, Nat.mod_lt _ (by omega)⟩

private def part (n : ℕ) (c : Fin 3) : Finset (Fin n) :=
  univ.filter (fun v => col v = c)

private lemma card_part_le (n : ℕ) (c : Fin 3) : (part n c).card ≤ n / 3 + 1 := by
  have hcard : (part n c).card ≤ (range (n / 3 + 1)).card := by
    refine card_le_card_of_injOn (fun v : Fin n => v.val / 3) ?_ ?_
    · intro v _
      exact mem_coe.mpr (mem_range.mpr (by dsimp only; omega))
    · intro v hv w hw hdiv
      dsimp only at hdiv
      have hvc : v.val % 3 = c.val := congrArg Fin.val (mem_filter.mp (mem_coe.mp hv)).2
      have hwc : w.val % 3 = c.val := congrArg Fin.val (mem_filter.mp (mem_coe.mp hw)).2
      exact Fin.ext (by omega)
  simpa using hcard

private noncomputable def badOf (n : ℕ) (c : Fin 3) : Finset (Finset (Fin n)) :=
  (part n c).powersetCard 3 ∪
    ((part n c).powersetCard 2 ×ˢ part n (c + 2)).image (fun p => insert p.2 p.1)

private noncomputable def badTriples (n : ℕ) : Finset (Finset (Fin n)) :=
  (univ : Finset (Fin 3)).biUnion (badOf n)

private noncomputable def turanEdges (n : ℕ) : Finset (Finset (Fin n)) :=
  ((univ : Finset (Fin n)).powersetCard 3) \ badTriples n

private lemma turanEdges_no_k4 (n : ℕ) :
    ¬ (turanEdges n).ContainsCompleteHypergraph 3 4 := by
  rintro ⟨S, hS4, hsub⟩
  have hsum : ∑ c : Fin 3, (S.filter (fun v => col v = c)).card = 4 := by
    rw [← hS4]
    exact (card_eq_sum_card_fiberwise (f := col) (fun _ _ => mem_univ _)).symm
  rw [Fin.sum_univ_three] at hsum
  have hmono : ∀ c : Fin 3, 3 ≤ (S.filter (fun v => col v = c)).card → False := by
    intro c hc
    obtain ⟨e, he_sub, he_card⟩ := exists_subset_card_eq hc
    have heS : e ⊆ S := he_sub.trans (filter_subset _ _)
    have heT : e ∈ turanEdges n := hsub (mem_powersetCard.mpr ⟨heS, he_card⟩)
    have heP : e ⊆ part n c := fun v hv =>
      mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (he_sub hv)).2⟩
    have heBad : e ∈ badTriples n :=
      mem_biUnion.mpr ⟨c, mem_univ _,
        mem_union_left _ (mem_powersetCard.mpr ⟨heP, he_card⟩)⟩
    exact (mem_sdiff.mp heT).2 heBad
  have hmix : ∀ c : Fin 3, 2 ≤ (S.filter (fun v => col v = c)).card →
      1 ≤ (S.filter (fun v => col v = c + 2)).card → False := by
    intro c hc2 hc1
    obtain ⟨A, hA_sub, hA_card⟩ := exists_subset_card_eq hc2
    obtain ⟨y, hy⟩ := card_pos.mp hc1
    have hyS : y ∈ S := (mem_filter.mp hy).1
    have hycol : col y = c + 2 := (mem_filter.mp hy).2
    have hne : c ≠ c + 2 := by fin_cases c <;> decide
    have hyA : y ∉ A := by
      intro hyin
      exact hne (((mem_filter.mp (hA_sub hyin)).2).symm.trans hycol)
    let e := insert y A
    have heS : e ⊆ S := insert_subset hyS (hA_sub.trans (filter_subset _ _))
    have he_card : e.card = 3 := by
      rw [card_insert_of_notMem hyA, hA_card]
    have heT : e ∈ turanEdges n := hsub (mem_powersetCard.mpr ⟨heS, he_card⟩)
    have hAP : A ∈ (part n c).powersetCard 2 :=
      mem_powersetCard.mpr ⟨fun v hv => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (hA_sub hv)).2⟩,
        hA_card⟩
    have hyP : y ∈ part n (c + 2) := mem_filter.mpr ⟨mem_univ _, hycol⟩
    have heBad : e ∈ badTriples n :=
      mem_biUnion.mpr ⟨c, mem_univ _,
        mem_union_right _ (mem_image.mpr ⟨(A, y), mem_product.mpr ⟨hAP, hyP⟩, rfl⟩)⟩
    exact (mem_sdiff.mp heT).2 heBad
  have hcases : (3 ≤ (S.filter (fun v => col v = 0)).card ∨
      3 ≤ (S.filter (fun v => col v = 1)).card ∨
      3 ≤ (S.filter (fun v => col v = 2)).card) ∨
      ((2 ≤ (S.filter (fun v => col v = 0)).card ∧ 1 ≤ (S.filter (fun v => col v = 2)).card) ∨
       (2 ≤ (S.filter (fun v => col v = 1)).card ∧ 1 ≤ (S.filter (fun v => col v = 0)).card) ∨
       (2 ≤ (S.filter (fun v => col v = 2)).card ∧ 1 ≤ (S.filter (fun v => col v = 1)).card)) := by
    omega
  rcases hcases with (h | h | h) | (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hmono 0 h
  · exact hmono 1 h
  · exact hmono 2 h
  · exact hmix 0 h1 h2
  · exact hmix 1 h1 h2
  · exact hmix 2 h1 h2

private lemma two_mul_choose_two_le (q : ℕ) : 2 * q.choose 2 ≤ q ^ 2 := by
  induction q with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

private lemma six_mul_choose_three_le (q : ℕ) : 6 * q.choose 3 ≤ q ^ 3 := by
  induction q with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ]
    have h2 := two_mul_choose_two_le m
    nlinarith

private lemma choose_two_real (n : ℕ) :
    2 * (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    linarith

private lemma choose_three_real (n : ℕ) :
    6 * (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ]
    have h2 := choose_two_real m
    push_cast
    nlinarith

private lemma card_badTriples_bound (n : ℕ) :
    6 * (badTriples n).card ≤ 12 * (n / 3 + 1) ^ 3 := by
  set q := n / 3 + 1
  have hbadOf (c : Fin 3) : (badOf n c).card ≤ q.choose 3 + q.choose 2 * q := by
    have h1 := card_union_le ((part n c).powersetCard 3)
      (((part n c).powersetCard 2 ×ˢ part n (c + 2)).image (fun p => insert p.2 p.1))
    have h2 : (((part n c).powersetCard 2 ×ˢ part n (c + 2)).image (fun p => insert p.2 p.1)).card ≤
        (part n c).card.choose 2 * (part n (c + 2)).card := by
      calc _ ≤ ((part n c).powersetCard 2 ×ˢ part n (c + 2)).card := card_image_le
        _ = (part n c).card.choose 2 * (part n (c + 2)).card := by
          rw [card_product, card_powersetCard]
    have h3 : (part n c).card.choose 3 ≤ q.choose 3 := Nat.choose_le_choose 3 (card_part_le n c)
    have h4 : (part n c).card.choose 2 * (part n (c + 2)).card ≤ q.choose 2 * q :=
      Nat.mul_le_mul (Nat.choose_le_choose 2 (card_part_le n c)) (card_part_le n (c + 2))
    rw [card_powersetCard] at h1
    dsimp only [badOf]
    omega
  have htot : (badTriples n).card ≤ 3 * (q.choose 3 + q.choose 2 * q) := by
    calc (badTriples n).card
        ≤ ∑ c : Fin 3, (badOf n c).card := card_biUnion_le
      _ ≤ ∑ _c : Fin 3, (q.choose 3 + q.choose 2 * q) := sum_le_sum fun c _ => hbadOf c
      _ = 3 * (q.choose 3 + q.choose 2 * q) := by simp
  have h2 := two_mul_choose_two_le q
  have h3 := six_mul_choose_three_le q
  nlinarith

private lemma turanEdges_le_extremal (n : ℕ) :
    (turanEdges n).card ≤ Hypergraph.cliqueExtremalNumber n 3 4 := by
  unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
  apply le_sup (f := Finset.card)
  simp only [mem_filter, mem_powerset]
  exact ⟨sdiff_subset, turanEdges_no_k4 n⟩

theorem OMA.solution : OMA.R_Erdos500_erdos_500_variants_turan_conjecture_R1.H1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge (40 / ε)
  refine eventually_atTop.mpr ⟨max 10 N, ?_⟩
  intro n hn
  have hn10 : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left 10 N) hn
  have hεn : 40 ≤ ε * (n : ℝ) := by
    have h1 : 40 / ε ≤ (n : ℝ) := hN.trans (by exact_mod_cast le_trans (le_max_right 10 N) hn)
    have h2 := (div_le_iff₀ hε).mp h1
    linarith
  have hcov : n.choose 3 ≤ (turanEdges n).card + (badTriples n).card := by
    have hsub : (univ : Finset (Fin n)).powersetCard 3 ⊆ turanEdges n ∪ badTriples n := by
      intro e he
      by_cases hb : e ∈ badTriples n
      · exact mem_union_right _ hb
      · exact mem_union_left _ (mem_sdiff.mpr ⟨he, hb⟩)
    calc n.choose 3 = ((univ : Finset (Fin n)).powersetCard 3).card := by
          rw [card_powersetCard, card_univ, Fintype.card_fin]
      _ ≤ (turanEdges n ∪ badTriples n).card := card_le_card hsub
      _ ≤ (turanEdges n).card + (badTriples n).card := card_union_le _ _
  have hcovR : (n.choose 3 : ℝ) ≤ (turanEdges n).card + (badTriples n).card := by
    exact_mod_cast hcov
  have hbadR : 6 * ((badTriples n).card : ℝ) ≤ 12 * ((n / 3 + 1 : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast card_badTriples_bound n
  have hq : ((n / 3 + 1 : ℕ) : ℝ) ≤ (n : ℝ) / 3 + 1 := by
    have hdiv : (n / 3 : ℕ) * 3 ≤ n := Nat.div_mul_le_self n 3
    have hdivR : ((n / 3 : ℕ) : ℝ) * 3 ≤ (n : ℝ) := by exact_mod_cast hdiv
    push_cast
    linarith
  have hq0 : (0 : ℝ) ≤ ((n / 3 + 1 : ℕ) : ℝ) := by positivity
  have hbad_poly : 6 * ((badTriples n).card : ℝ) ≤ 12 * ((n : ℝ) / 3 + 1) ^ 3 := by
    have hcube : ((n / 3 + 1 : ℕ) : ℝ) ^ 3 ≤ ((n : ℝ) / 3 + 1) ^ 3 :=
      pow_le_pow_left₀ hq0 hq 3
    linarith
  have hch : 6 * (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) :=
    choose_three_real n
  have hhalf : (1 / 2 : ℝ) * (n : ℝ) ^ 3 ≤ 6 * (n.choose 3 : ℝ) := by
    rw [hch]
    nlinarith [sq_nonneg ((n : ℝ) - 6)]
  have herr : 6 * ((badTriples n).card : ℝ) ≤
      (4 / 9 : ℝ) * (6 * (n.choose 3 : ℝ)) + 20 * (n : ℝ) ^ 2 := by
    rw [hch]
    nlinarith
  have hεterm : 20 * (n : ℝ) ^ 2 ≤ ε * (6 * (n.choose 3 : ℝ)) := by
    have h1 : 20 * (n : ℝ) ^ 2 ≤ ε * ((1 / 2 : ℝ) * (n : ℝ) ^ 3) := by
      nlinarith [sq_nonneg (n : ℝ)]
    have h2 : ε * ((1 / 2 : ℝ) * (n : ℝ) ^ 3) ≤ ε * (6 * (n.choose 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hhalf hε.le
    linarith
  have hmain : (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ ((turanEdges n).card : ℝ) := by
    nlinarith
  have hext : ((turanEdges n).card : ℝ) ≤ (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) := by
    exact_mod_cast turanEdges_le_extremal n
  linarith
