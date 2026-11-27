import FormalConjectures.ErdosProblems.«713»

-- Reduction Erdos713.erdos_713.parts.ii.R3 of Erdős Problem 713 — ii
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos713_erdos_713_parts_ii_R3

open Filter Asymptotics SimpleGraph Finset
open scoped Classical BigOperators

theorem OMA.extremalPowerOrder_of_equivalent {V : Type*} {G : SimpleGraph V} {α c : ℝ}
    (hc : c ≠ 0) (hG : (fun n : ℕ => (extremalNumber n G : ℝ)) ~[atTop]
      (fun n : ℕ => c * (n : ℝ) ^ α)) :
    ((fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) ∧ ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) := by
  refine ⟨hG.isBigO.trans (isBigO_const_mul_self c _ _), ?_⟩
  intro hn
  have reverse : (fun n : ℕ => (n : ℝ) ^ α) =O[atTop]
      (fun n : ℕ => (extremalNumber n G : ℝ)) :=
    (isBigO_self_const_mul hc _ _).trans hG.symm.isBigO
  apply isLittleO_irrefl (f'' := fun n : ℕ => (n : ℝ) ^ α) _ (reverse.trans_isLittleO hn)
  apply Eventually.frequently
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (Real.rpow_pos_of_pos (by exact_mod_cast hn) α).ne'

theorem OMA.extremalNumber_isBigO_of_contained {V W : Type*}
    {F : SimpleGraph V} {G : SimpleGraph W} (h : F ⊑ G) :
    (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop]
      (fun n : ℕ => (extremalNumber n G : ℝ)) := by
  apply IsBigO.of_bound 1
  refine Eventually.of_forall fun n => ?_
  simp only [Real.norm_natCast, one_mul]
  exact_mod_cast h.extremalNumber_le (n := n)

/-- Deleting one edge per copy gives a lower bound on the number of copies. -/
theorem OMA.card_edges_le_extremal_add_copyCount {V W : Type*} [Fintype V]
    (H : SimpleGraph V) (J : SimpleGraph W) (hJ : J ≠ ⊥) :
    H.edgeFinset.card ≤ extremalNumber (Fintype.card V) J + H.copyCount J := by
  apply H.le_card_edgeFinset_killCopies_add_copyCount.trans
  apply Nat.add_le_add_right
  convert! card_edgeFinset_le_extremalNumber (free_killCopies (G := H) hJ)

theorem card_colorings_fixed {E : Type*} [Fintype E] [DecidableEq E] (k : ℕ) (z : Fin k)
    (T : Finset E) :
    (Finset.univ.filter fun f : E → Fin k => ∀ e ∈ T, f e = z).card =
      k ^ (Fintype.card E - T.card) := by
  let opts (e : E) : Finset (Fin k) := if e ∈ T then {z} else Finset.univ
  have hf : (Finset.univ.filter fun f : E → Fin k => ∀ e ∈ T, f e = z) =
      Fintype.piFinset opts := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h e
      by_cases he : e ∈ T
      · simpa [opts, he] using h e he
      · simp [opts, he]
    · intro h e he
      simpa [opts, he] using h e
  rw [hf, Fintype.card_piFinset, ← Finset.card_compl]
  have hcard (e : E) : (opts e).card = if e ∈ T then 1 else k := by
    by_cases he : e ∈ T <;> simp [opts, he]
  simp only [hcard]
  simpa only [Finset.mem_compl, ite_not, Finset.prod_const] using
    Finset.prod_ite_mem_eq Tᶜ (fun _ => k)

theorem sum_card_filter_swap {E C : Type*}
    (S : Finset E) (T : Finset C) (P : E → C → Prop)
    [∀ e c, Decidable (P e c)] :
    (∑ e ∈ S, (T.filter (P e)).card) =
      ∑ c ∈ T, (S.filter (fun e => P e c)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem card_colorGraph {V : Type*} [Fintype V] (H : SimpleGraph V) {k : ℕ}
    (f : Sym2 V → Fin k) (z : Fin k) (G : SimpleGraph V)
    (hG : G = H.deleteEdges {e | f e ≠ z}) :
    G.edgeFinset.card = (H.edgeFinset.filter fun e => f e = z).card := by
  congr 1
  ext e
  rw [Finset.mem_filter, mem_edgeFinset, mem_edgeFinset]
  induction e using Sym2.inductionOn with
  | hf u v =>
    rw [mem_edgeSet, mem_edgeSet, hG]
    simp only [deleteEdges_adj, Set.mem_ofPred_eq, not_not]

theorem card_copiedEdges {V W : Type*} {H : SimpleGraph V} {J : SimpleGraph W}
    [Fintype W] (c : J.Copy H) :
    (J.edgeFinset.map c.toEmbedding.sym2Map).card = J.edgeFinset.card := Finset.card_map _

theorem copy_uses_color {V W : Type*} {H : SimpleGraph V} {J : SimpleGraph W}
    [Fintype W] {k : ℕ} (f : Sym2 V → Fin k) (z : Fin k) (G : SimpleGraph V)
    (hG : G = H.deleteEdges {e | f e ≠ z}) (c : J.Copy H) :
    (∀ e ∈ J.edgeFinset.map c.toEmbedding.sym2Map, f e = z) ↔
      ∀ ⦃u v⦄, J.Adj u v → G.Adj (c u) (c v) := by
  subst hG
  constructor
  · intro hc u v huv
    apply deleteEdges_adj.mpr
    refine ⟨c.toHom.map_rel' huv, ?_⟩
    exact not_not_intro (hc _ (Finset.mem_map.mpr ⟨s(u, v), by simpa using huv, rfl⟩))
  · intro hc e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp he
    induction a using Sym2.inductionOn with
    | hf u v =>
      have huv : J.Adj u v := by simpa using ha
      exact not_not.mp (deleteEdges_adj.mp (hc huv)).2

theorem labelledCopyCount_colorGraph {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (J : SimpleGraph W) {k : ℕ}
    (f : Sym2 V → Fin k) (z : Fin k) (G : SimpleGraph V)
    (hG : G = H.deleteEdges {e | f e ≠ z}) :
    G.labelledCopyCount J =
      (Finset.univ.filter fun c : J.Copy H =>
        ∀ e ∈ J.edgeFinset.map c.toEmbedding.sym2Map, f e = z).card := by
  have hle : G ≤ H := hG ▸ H.deleteEdges_le _
  let incl := Copy.ofLE G H hle
  let e : J.Copy G ≃ {c : J.Copy H // ∀ e ∈ J.edgeFinset.map c.toEmbedding.sym2Map, f e = z} := {
    toFun := fun c => ⟨incl.comp c, (copy_uses_color f z G hG _).2 fun {_ _} h => c.toHom.map_rel' h⟩
    invFun := fun c => ⟨⟨c.1, fun h => (copy_uses_color f z G hG c.1).1 c.2 h⟩, c.1.injective⟩
    left_inv := fun c => Copy.ext fun _ => rfl
    right_inv := fun c => Subtype.ext (Copy.ext fun _ => rfl)
  }
  rw [labelledCopyCount, Fintype.card_congr e]
  exact Fintype.card_ofFinset
    (p := {c : J.Copy H | ∀ e ∈ J.edgeFinset.map c.toEmbedding.sym2Map, f e = z}) _
    (fun c => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq])

/-- Averaging the graphs of one color amplifies the elementary copy-count bound. -/
theorem OMA.coloring_labelledCopyCount_bound {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (J : SimpleGraph W) (hJ : J ≠ ⊥) {k : ℕ} (z : Fin k) :
    k ^ (J.edgeFinset.card - 1) * H.edgeFinset.card ≤
      k ^ J.edgeFinset.card * extremalNumber (Fintype.card V) J + H.labelledCopyCount J := by
  let e := J.edgeFinset.card
  let m := Fintype.card (Sym2 V)
  let X := extremalNumber (Fintype.card V) J
  change k ^ (e - 1) * H.edgeFinset.card ≤ k ^ e * X + H.labelledCopyCount J
  have hk : 0 < k := z.pos
  obtain ⟨cg, hcg⟩ : ∃ cg : (Sym2 V → Fin k) → SimpleGraph V,
      ∀ f, cg f = H.deleteEdges {e | f e ≠ z} := ⟨_, fun _ => rfl⟩
  by_cases hcontained : J ⊑ H
  · obtain ⟨c⟩ := hcontained
    have hem : e ≤ m := by
      change J.edgeFinset.card ≤ Fintype.card (Sym2 V)
      rw [← card_copiedEdges c]
      exact Finset.card_le_univ _
    have he : 0 < e := by
      apply Finset.card_pos.mpr
      by_contra hf
      apply hJ
      apply edgeFinset_inj.mp
      rw [Finset.not_nonempty_iff_eq_empty.mp hf, edgeFinset_bot]
    have hEdge (a : Sym2 V) :
        (univ.filter fun f : Sym2 V → Fin k => f a = z).card = k ^ (m - 1) := by
      simpa using card_colorings_fixed k z {a}
    have edgesSum :
        (∑ f : Sym2 V → Fin k, (cg f).edgeFinset.card) =
          H.edgeFinset.card * k ^ (m - 1) := by
      simp_rw [fun f => card_colorGraph H f z (cg f) (hcg f)]
      rw [sum_card_filter_swap (univ : Finset (Sym2 V → Fin k)) H.edgeFinset
        (fun f a => f a = z)]
      simp [hEdge]
    have copiesSum :
        (∑ f : Sym2 V → Fin k, (cg f).labelledCopyCount J) =
          H.labelledCopyCount J * k ^ (m - e) := by
      simp_rw [fun f => labelledCopyCount_colorGraph H J f z (cg f) (hcg f)]
      rw [sum_card_filter_swap (univ : Finset (Sym2 V → Fin k))
        (univ : Finset (J.Copy H)) (fun f c => ∀ a ∈ (J.edgeFinset.map c.toEmbedding.sym2Map), f a = z)]
      simp_rw [card_colorings_fixed, card_copiedEdges]
      simp [labelledCopyCount, e, m]
    have bound (f : Sym2 V → Fin k) :
        (cg f).edgeFinset.card ≤
          X + (cg f).labelledCopyCount J :=
      (OMA.card_edges_le_extremal_add_copyCount (cg f) J hJ).trans
        (Nat.add_le_add_left (copyCount_le_labelledCopyCount ..) X)
    have summed := Finset.sum_le_sum (s := (univ : Finset (Sym2 V → Fin k))) (fun f _ => bound f)
    rw [edgesSum, Finset.sum_add_distrib, copiesSum] at summed
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin] at summed
    have hm : k ^ m = k ^ (m - e) * k ^ e := by
      rw [← pow_add]
      congr 1
      omega
    have hm1 : k ^ (m - 1) = k ^ (m - e) * k ^ (e - 1) := by
      rw [← pow_add]
      congr 1
      omega
    change H.edgeFinset.card * k ^ (m - 1) ≤
      k ^ m * X + H.labelledCopyCount J * k ^ (m - e) at summed
    rw [hm1, hm] at summed
    apply Nat.le_of_mul_le_mul_left _ (pow_pos hk (m - e))
    calc
      k ^ (m - e) * (k ^ (e - 1) * H.edgeFinset.card) =
          H.edgeFinset.card * (k ^ (m - e) * k ^ (e - 1)) := by ac_rfl
      _ ≤ (k ^ (m - e) * k ^ e) * X + H.labelledCopyCount J * k ^ (m - e) := summed
      _ = k ^ (m - e) * (k ^ e * X + H.labelledCopyCount J) := by rw [Nat.mul_add]; ac_rfl
  · have hbound := card_edgeFinset_le_extremalNumber (show J.Free H from hcontained)
    have hpow : k ^ (e - 1) ≤ k ^ e := pow_le_pow_right₀ (by omega) (by omega)
    exact ((Nat.mul_le_mul hpow hbound).trans (Nat.le_add_right _ _))


/-- Uniform edge coloring of a complete host yields the deletion lower bound
on a subsequence of vertex counts. -/
theorem OMA.extremalNumber_power_subseq_lower {W : Type*} [Fintype W] (J : SimpleGraph W)
    (hJ : 2 ≤ J.edgeFinset.card) {a : ℕ} (ha : 2 ≤ a) :
    let d := J.edgeFinset.card - 1
    let x := Fintype.card W - 2
    (a : ℝ) ^ (2 * d) ≤ 64 * (a : ℝ) ^ x * (extremalNumber (a ^ d) J : ℝ) := by
  intro d x
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hv : 2 ≤ Fintype.card W := by
    by_contra! hv
    have hc := J.card_edgeFinset_le_card_choose_two
    rw [Nat.choose_eq_zero_of_lt hv] at hc
    omega
  have hvx : Fintype.card W = x + 2 := by dsimp [x]; omega
  have hne : J ≠ ⊥ := by
    intro hb
    obtain ⟨b, hb'⟩ := Finset.card_pos.mp (by omega : 0 < J.edgeFinset.card)
    have hmem := mem_edgeFinset.mp hb'
    simp only [hb, edgeSet_bot, Set.mem_empty_iff_false] at hmem
  let n := a ^ d
  let K := 8 * a ^ x
  have hn : 2 ≤ n := calc
    2 ≤ a := ha
    _ = a ^ (1 : ℕ) := by simp
    _ ≤ n := pow_le_pow_right₀ (by omega) hd
  let H : SimpleGraph (Fin n) := ⊤
  let E := (H.edgeFinset.card : ℝ)
  let M := (K : ℝ) ^ d
  have hE : (n : ℝ) ^ (2 : ℕ) ≤ 4 * E := by
    dsimp [E, H]
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, Nat.cast_choose_two]
    have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) by positivity)
      (show 0 ≤ (n : ℝ) - 2 by linarith)]
  have hCopies : H.labelledCopyCount J ≤ n ^ Fintype.card W := by
    have h := Fintype.card_le_of_injective (fun c : J.Copy H => (c : W → Fin n))
      (fun _ _ h => Copy.ext (congrFun h))
    unfold labelledCopyCount
    calc
      _ ≤ Fintype.card (W → Fin n) := by convert! h
      _ = _ := by simp
  have hCopiesR : (H.labelledCopyCount J : ℝ) ≤ (n : ℝ) ^ Fintype.card W := by
    exact_mod_cast hCopies
  have hM : 8 * (n : ℝ) ^ x ≤ M := by
    have h8 : (8 : ℝ) ≤ (8 : ℝ) ^ d := by
      calc
        (8 : ℝ) = (8 : ℝ) ^ (1 : ℕ) := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hd
    dsimp [M, K, n]
    push_cast
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm d x]
    exact mul_le_mul_of_nonneg_right h8 (by positivity)
  have hAbs : 2 * (H.labelledCopyCount J : ℝ) ≤ M * E := by
    calc
      _ ≤ 2 * (n : ℝ) ^ Fintype.card W := mul_le_mul_of_nonneg_left hCopiesR (by norm_num)
      _ = (8 * (n : ℝ) ^ x) * ((n : ℝ) ^ (2 : ℕ) / 4) := by rw [hvx, pow_add]; ring
      _ ≤ _ := mul_le_mul hM (by linarith only [hE]) (by positivity) (by positivity)
  have hK : 0 < K := by
    dsimp [K]
    exact Nat.mul_pos (by decide) (pow_pos (by omega) _)
  have hMpos : 0 < M := by
    have : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    exact pow_pos this _
  have hfin := OMA.coloring_labelledCopyCount_bound H J hne (⟨0, hK⟩ : Fin K)
  rw [Fintype.card_fin] at hfin
  have hf : M * E ≤ M * ((K : ℝ) * (extremalNumber n J : ℝ)) + H.labelledCopyCount J := by
    rw [← mul_assoc]
    have hp : M * (K : ℝ) = (K : ℝ) ^ J.edgeFinset.card := by
      dsimp [M, d]
      rw [← pow_succ, show J.edgeFinset.card - 1 + 1 = J.edgeFinset.card by omega]
    rw [hp]
    dsimp only [M, E, d]
    norm_cast
    convert! hfin
  have hbound : E ≤ 2 * (K : ℝ) * (extremalNumber n J : ℝ) := by
    apply le_of_mul_le_mul_left _ hMpos
    nlinarith only [hf, hAbs]
  have hfinal : (n : ℝ) ^ (2 : ℕ) ≤ 8 * (K : ℝ) * (extremalNumber n J : ℝ) := by
    linarith only [hE, hbound]
  dsimp only [n, K] at hfinal
  push_cast at hfinal
  rw [← pow_mul, Nat.mul_comm d 2] at hfinal
  convert hfinal using 1
  ring

/-- Any power upper bound on the extremal number obeys the classical
random-deletion lower bound on its exponent. -/
theorem OMA.exponent_ge_deletion_bound {W : Type*} [Fintype W] (J : SimpleGraph W)
    (hJ : 2 ≤ J.edgeFinset.card) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n J : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    ((2 : ℝ) - ((Fintype.card W - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ)) ≤ α := by
  let x := Fintype.card W - 2
  let d := J.edgeFinset.card - 1
  change 2 - (x : ℝ) / (d : ℝ) ≤ α
  by_contra! hα
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  let β := ((2 * d : ℕ) : ℝ) - (x : ℝ) - (d : ℝ) * α
  have hβ : 0 < β := by
    have hx : (x : ℝ) / (d : ℝ) < 2 - α := by linarith
    have hx' := (div_lt_iff₀ hdR).mp hx
    dsimp [β]
    push_cast
    nlinarith only [hx']
  obtain ⟨C, hC⟩ := isBigO_iff.mp hO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  have hlarge : ∀ᶠ a : ℕ in atTop, 64 * C < (a : ℝ) ^ β :=
    ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨a, ha, hlarge'⟩ := ((eventually_ge_atTop (max 2 N)).and hlarge).exists
  have ha2 : 2 ≤ a := (le_max_left _ _).trans ha
  have hap : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hpow : a ≤ a ^ d := by
    calc
      a = a ^ (1 : ℕ) := by simp
      _ ≤ a ^ d := pow_le_pow_right₀ (by omega) hd
  have hN' := hN (a ^ d) ((le_max_right _ _).trans (ha.trans hpow))
  rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (a ^ d)) α)] at hN'
  push_cast at hN'
  have hsplit : (a : ℝ) ^ β =
      (a : ℝ) ^ (2 * d) / ((a : ℝ) ^ x * ((a : ℝ) ^ d) ^ α) := by
    dsimp [β]
    rw [Real.rpow_sub hap, Real.rpow_sub hap, Real.rpow_natCast, Real.rpow_natCast,
      Real.rpow_natCast_mul hap.le, div_div]
  apply (not_le_of_gt hlarge')
  rw [hsplit, div_le_iff₀ (by positivity)]
  calc
    _ ≤ 64 * (a : ℝ) ^ x * (extremalNumber (a ^ d) J : ℝ) :=
      OMA.extremalNumber_power_subseq_lower J hJ ha2
    _ ≤ (64 * (a : ℝ) ^ x) * (C * ((a : ℝ) ^ d) ^ α) :=
      mul_le_mul_of_nonneg_left hN' (by positivity)
    _ = _ := by ring

/-- Minimize the total of vertices and edges among copies that retain the power scale. -/
theorem OMA.exists_minimal_extremalPower {q : ℕ} {G : SimpleGraph (Fin q)} {α : ℝ}
    (hG : ((fun n : ℕ => (extremalNumber n G : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) ∧ ¬ (fun n : ℕ => (extremalNumber n G : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α))) :
    ∃ (r : ℕ) (F : SimpleGraph (Fin r)), F ⊑ G ∧ ((fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) ∧ ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) ∧
      ∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →
        s + J.edgeFinset.card < r + F.edgeFinset.card →
        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
  let eligible (k : ℕ) : Prop :=
    ∃ (r : ℕ) (F : SimpleGraph (Fin r)),
      r + F.edgeFinset.card = k ∧ F ⊑ G ∧ ((fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) ∧ ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α))
  have hex : ∃ k, eligible k :=
    ⟨q + G.edgeFinset.card, q, G, rfl, IsContained.refl G, hG⟩
  obtain ⟨r, F, hcard, hFG, hF⟩ := Nat.find_spec hex
  refine ⟨r, F, hFG, hF, fun s J hJF hsmall => ?_⟩
  by_contra hJ
  exact (Nat.not_lt_of_ge (Nat.find_min' hex
    ⟨s, J, rfl, hJF.trans hFG, (OMA.extremalNumber_isBigO_of_contained hJF).trans hF.1, hJ⟩))
      (hsmall.trans_eq hcard)


theorem OMA.mem_tupleCommon {W : Type*} [Fintype W]
    (X : SimpleGraph W) {t : ℕ} (p : Fin t → W) (v : W) :
    v ∈ (univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t) ↔ ∀ i, X.Adj (p i) v := by
  simp

theorem card_tuples_in {W : Type*} [Fintype W] (t : ℕ) (S : Finset W) :
    (univ.filter fun p : Fin t → W => ∀ i, p i ∈ S).card = S.card ^ t := by
  have h : (univ.filter fun p : Fin t → W => ∀ i, p i ∈ S) =
      Fintype.piFinset (fun _ : Fin t => S) := by
    ext p
    simp [Fintype.mem_piFinset]
  rw [h, Fintype.card_piFinset]
  simp

theorem rich_tuples_of_sample_sum {W : Type*} [Fintype W]
    (X : SimpleGraph W) {t : ℕ} (ht : 0 < t) (s : ℕ) (Q : Finset (Fin t → W))
    (hdense : Fintype.card W ^ t * (s ^ t + s) < ∑ q ∈ Q, ((univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t)).card) :
    ∃ q ∈ Q, ∃ A : Finset W, A ⊆ (univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t) ∧ s ≤ A.card ∧
      ∀ p : Fin t → W, (∀ i, p i ∈ A) → s ≤ ((univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t)).card := by
  let bad : Finset (Fin t → W) := univ.filter fun p => ((univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t)).card < s
  let inCommon (q : Fin t → W) := bad.filter fun p => ∀ i, p i ∈ (univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t)
  have hflip (p q : Fin t → W) :
      (∀ i, p i ∈ (univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t)) ↔ (∀ i, q i ∈ (univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t)) := by
    simp only [OMA.mem_tupleCommon]
    exact ⟨fun h i j => (h j i).symm, fun h i j => (h j i).symm⟩
  have hbad : (∑ q ∈ Q, (inCommon q).card) ≤ Fintype.card W ^ t * s ^ t := by
    change (∑ q ∈ Q, (bad.filter fun p => ∀ i, p i ∈ (univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t)).card) ≤ _
    rw [sum_card_filter_swap]
    simp_rw [hflip _ _]
    calc
      _ ≤ ∑ _p ∈ bad, s ^ t := by
        apply sum_le_sum
        intro p hp
        have hsub :
            Q.filter (fun q => ∀ i, q i ∈ (univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t)) ⊆
              univ.filter (fun q => ∀ i, q i ∈ (univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t)) :=
          filter_subset_filter _ (subset_univ Q)
        apply (card_le_card hsub).trans
        rw [card_tuples_in]
        exact Nat.pow_le_pow_left (mem_filter.mp hp).2.le t
      _ = bad.card * s ^ t := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (by simpa using card_le_univ bad)
  have hex : ∃ q ∈ Q, (inCommon q).card + s < ((univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t)).card := by
    by_contra! h
    have hsum := sum_le_sum h
    rw [sum_add_distrib, sum_const, nsmul_eq_mul] at hsum
    have hQ : Q.card ≤ Fintype.card W ^ t := by simpa using card_le_univ Q
    rw [Nat.mul_add] at hdense
    exact (not_lt_of_ge (hsum.trans (Nat.add_le_add hbad (Nat.mul_le_mul_right s hQ)))) hdense
  obtain ⟨q, hqQ, hq⟩ := hex
  let removed := (inCommon q).image fun p => p ⟨0, ht⟩
  let A := (univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t) \ removed
  refine ⟨q, hqQ, A, sdiff_subset, ?_, ?_⟩
  · have hremoved : removed.card ≤ (inCommon q).card := card_image_le
    have hloss := le_card_sdiff removed ((univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t))
    change s ≤ ((univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t) \ removed).card
    omega
  · intro p hp
    by_contra! hfew
    have hpin : p ∈ inCommon q :=
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hfew⟩, fun i => (mem_sdiff.mp (hp i)).1⟩
    exact (mem_sdiff.mp (hp ⟨0, ht⟩)).2 (mem_image.mpr ⟨p, hpin, rfl⟩)

/-- A moment condition yields a large vertex set whose short tuples have many common neighbors. -/
theorem OMA.rich_tuples_of_degree_moment {W : Type*} [Fintype W]
    (X : SimpleGraph W) {t : ℕ} (ht : 0 < t) (s : ℕ)
    (hdense : Fintype.card W ^ t * (s ^ t + s) < ∑ v, X.degree v ^ t) :
    ∃ A : Finset W, s ≤ A.card ∧ ∀ p : Fin t → W,
      (∀ i, p i ∈ A) → s ≤ ((univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t)).card := by
  have htotal : (∑ q : Fin t → W, ((univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t)).card) = ∑ v, X.degree v ^ t := by
    rw [sum_card_filter_swap]
    have hfiber (v : W) :
        (univ.filter fun p : Fin t → W => ∀ i, X.Adj (p i) v).card = X.degree v ^ t := by
      simpa only [mem_neighborFinset, X.adj_comm v, card_neighborFinset_eq_degree] using
        card_tuples_in t (X.neighborFinset v)
    simp_rw [hfiber]
  obtain ⟨_, _, A, _, hA, hrich⟩ :=
    rich_tuples_of_sample_sum X ht s univ (htotal.symm ▸ hdense)
  exact ⟨A, hA, hrich⟩

theorem card_injective_tuples_in {W : Type*} [Fintype W] (t : ℕ) (S : Finset W) :
    ((univ.filter Function.Injective).filter fun p : Fin t → W => ∀ i, p i ∈ S).card =
      S.card.descFactorial t := by
  let T := (univ.filter Function.Injective).filter fun p : Fin t → W => ∀ i, p i ∈ S
  have hEquiv : T ≃ (Fin t ↪ S) := {
    toFun := fun p => ⟨fun i => ⟨p.val i, (mem_filter.mp p.property).2 i⟩,
      fun i j hij => (mem_filter.mp (mem_filter.mp p.property).1).2 (congrArg Subtype.val hij)⟩
    invFun := fun p => ⟨fun i => (p i).val, by
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, fun i => (p i).property⟩
      intro i j hij
      exact p.injective (Subtype.ext hij)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }
  simpa only [Fintype.card_coe, Fintype.card_embedding_eq, Fintype.card_fin] using Fintype.card_congr hEquiv

/-- The rich set can be chosen inside the common neighborhood of an injective sample. -/
theorem OMA.rich_tuples_of_descending_degree_moment {W : Type*} [Fintype W]
    (X : SimpleGraph W) {t : ℕ} (ht : 0 < t) (s : ℕ)
    (hdense : Fintype.card W ^ t * (s ^ t + s) < ∑ v, (X.degree v).descFactorial t) :
    ∃ q : Fin t ↪ W, ∃ A : Finset W, A ⊆ (univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t) ∧ s ≤ A.card ∧
      ∀ p : Fin t → W, (∀ i, p i ∈ A) → s ≤ ((univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t)).card := by
  let Q : Finset (Fin t → W) := univ.filter Function.Injective
  have hmoment : (∑ q ∈ Q, ((univ.filter fun w_t => ∀ i_t, X.Adj (q i_t) w_t)).card) = ∑ v, (X.degree v).descFactorial t := by
    rw [sum_card_filter_swap]
    have hfiber (v : W) :
        (Q.filter fun p : Fin t → W => ∀ i, X.Adj (p i) v).card =
          (X.degree v).descFactorial t := by
      simpa only [Q, mem_neighborFinset, X.adj_comm v, card_neighborFinset_eq_degree] using
        card_injective_tuples_in t (X.neighborFinset v)
    simp_rw [hfiber]
  obtain ⟨q, hq, A, hsub, hA, hrich⟩ :=
    rich_tuples_of_sample_sum X ht s Q (hmoment.symm ▸ hdense)
  exact ⟨⟨q, (mem_filter.mp hq).2⟩, A, hsub, hA, hrich⟩

theorem contained_of_rich_tuples_with_exceptional {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V)
    (E : Finset {v : V // v ∉ R}) (m : E ↪ W) {t s : ℕ}
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ E, F.degree v.val ≤ t) (ht : t ≤ s) (hs : Fintype.card V ≤ s)
    {A : Finset W} (hA : s ≤ A.card)
    (hrich : ∀ p : Fin t → W, (∀ i, p i ∈ A) → s ≤ ((univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t)).card)
    (hattach : ∀ x : E, ∀ w ∈ A, X.Adj (m x) w) :
    F ⊑ X := by
  let L := {v : V // v ∉ R}
  let U := {v : L // v ∉ E}
  let eL : E ⊕ U ≃ L := Equiv.sumCompl (fun v => v ∈ E)
  let e : R ⊕ (E ⊕ U) ≃ V :=
    (Equiv.sumCongr (Equiv.refl R) eL).trans (Equiv.sumCompl (fun v => v ∈ R))
  have hfit : R.card ≤ A.card := (card_le_univ R).trans (hs.trans hA)
  let j : R ↪ A :=
    R.equivFin.toEmbedding.trans ((Fin.castLEEmb hfit).trans A.equivFin.symm.toEmbedding)
  let f : R ↪ W := j.trans (Function.Embedding.subtype _)
  let D : Finset W := univ.map f ∪ univ.map m
  let neighbors (v : U) : Finset R := univ.filter fun u => F.Adj v.val.val u.val
  let choices (v : U) : Finset W := (univ.filter fun w => ∀ u ∈ neighbors v, X.Adj (f u) w) \ D
  have huniv : D.card + Fintype.card U ≤ Fintype.card V := by
    have hD := card_union_le (univ.map f) (univ.map m)
    simp only [card_map, card_univ] at hD
    have hV := Fintype.card_congr e
    simp only [Fintype.card_sum] at hV
    change (univ.map f ∪ univ.map m).card + Fintype.card U ≤ _
    omega
  have hchoices (v : U) : Fintype.card U ≤ (choices v).card := by
    let B := (neighbors v).map f
    have hBA : B ⊆ A := by
      intro w hw
      obtain ⟨u, _, rfl⟩ := mem_map.mp hw
      exact (j u).property
    have hB : B.card ≤ t := by
      rw [card_map]
      let incl : R ↪ V := Function.Embedding.subtype _
      have hsub : (neighbors v).map incl ⊆ F.neighborFinset v.val.val := by
        intro x hx
        obtain ⟨u, hu, rfl⟩ := mem_map.mp hx
        exact (F.mem_neighborFinset _ _).mpr (mem_filter.mp hu).2
      have hc := card_le_card hsub
      rw [card_map, card_neighborFinset_eq_degree] at hc
      exact hc.trans (hdeg v.val v.property)
    obtain ⟨T, hBT, hTA, hT⟩ := exists_subsuperset_card_eq hBA hB (ht.trans hA)
    let b : T ≃ Fin t := T.equivFin.trans (finCongr hT)
    let p (i : Fin t) : W := (b.symm i).val
    have hp : ∀ i, p i ∈ A := fun i => hTA (b.symm i).property
    have hcom : (univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t) \ D ⊆ choices v := by
      intro w hw
      obtain ⟨hw, hD⟩ := mem_sdiff.mp hw
      refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, hD⟩
      intro u hu
      have hfu : f u ∈ T := hBT (mem_map.mpr ⟨u, hu, rfl⟩)
      have he := (OMA.mem_tupleCommon X p w).mp hw (b ⟨f u, hfu⟩)
      simpa [p] using he
    have hloss := le_card_sdiff D ((univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t))
    have hsize := card_le_card hcom
    have hrich' := hrich p hp
    omega
  obtain ⟨g, hg, hgchoice⟩ := (all_card_le_biUnion_card_iff_exists_injective choices).mp (by
    intro S
    rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · simp
    · exact (card_le_univ S).trans ((hchoices v).trans (card_le_card (subset_biUnion_of_mem choices hv))))
  have hmoff (x : E) (y : U) : m x ≠ g y := by
    intro h
    apply (mem_sdiff.mp (hgchoice y)).2
    exact mem_union_right _ (mem_map.mpr ⟨x, mem_univ _, h⟩)
  let mix : E ⊕ U → W := Sum.elim m g
  have hmix : Function.Injective mix := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (m.injective h)
    · exact (hmoff x y h).elim
    · exact (hmoff y x h.symm).elim
    · exact congrArg Sum.inr (hg h)
  have hfoff (x : R) (y : E ⊕ U) : f x ≠ mix y := by
    cases y with
    | inl y => exact (hattach y (f x) (j x).property).ne.symm
    | inr y =>
      intro h
      apply (mem_sdiff.mp (hgchoice y)).2
      exact mem_union_left _ (mem_map.mpr ⟨x, mem_univ _, h⟩)
  let join : R ⊕ (E ⊕ U) → W := Sum.elim f mix
  have hinj : Function.Injective join := by
    rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (f.injective h)
    · exact (hfoff x y h).elim
    · exact (hfoff y x h.symm).elim
    · exact congrArg Sum.inr (hmix h)
  have hcross (u : E ⊕ U) (v : R) (h : F.Adj (e (.inr u)) v.val) :
      X.Adj (mix u) (f v) := by
    cases u with
    | inl w => exact hattach w (f v) (j v).property
    | inr w =>
      have hmem : v ∈ neighbors w := mem_filter.mpr ⟨mem_univ _, h⟩
      exact ((mem_filter.mp (mem_sdiff.mp (hgchoice w)).1).2 v hmem).symm
  have hpres : ∀ u v : R ⊕ (E ⊕ U), F.Adj (e u) (e v) → X.Adj (join u) (join v) := by
    rintro (u | u) (v | v) h
    · exact ((hcolors h).mp u.property v.property).elim
    · exact (hcross v u h.symm).symm
    · exact hcross u v h
    · exact ((eL u).property ((hcolors h).mpr (eL v).property)).elim
  refine ⟨⟨⟨join ∘ e.symm, ?_⟩, hinj.comp e.symm.injective⟩⟩
  intro u v huv
  simpa using hpres (e.symm u) (e.symm v) (by simpa using huv)

theorem contained_of_rich_tuples {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V) {t s : ℕ}
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ R, F.degree v ≤ t) (ht : t ≤ s) (hs : Fintype.card V ≤ s)
    {A : Finset W} (hA : s ≤ A.card)
    (hrich : ∀ p : Fin t → W, (∀ i, p i ∈ A) → s ≤ ((univ.filter fun w_t => ∀ i_t, X.Adj (p i_t) w_t)).card) :
    F ⊑ X := by
  let E : Finset {v : V // v ∉ R} := ∅
  let m : E ↪ W := ⟨fun v => (notMem_empty v.val v.property).elim,
    fun v => (notMem_empty v.val v.property).elim⟩
  exact contained_of_rich_tuples_with_exceptional F X R E m hcolors
    (fun v _ => hdeg v.val v.property) ht hs hA hrich
    (fun v => (notMem_empty v.val v.property).elim)

/-- The one-sided degree bound forces a uniform bound for the degree moment of a free host. -/
theorem OMA.degree_side_moment_bound {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ R, F.degree v ≤ t) (hfree : F.Free X) :
    let s := max t (Fintype.card V)
    (∑ v, X.degree v ^ t) ≤ Fintype.card W ^ t * (s ^ t + s) := by
  intro s
  by_contra! h
  obtain ⟨A, hA, hrich⟩ := OMA.rich_tuples_of_degree_moment X ht s h
  exact hfree (contained_of_rich_tuples F X R hcolors hdeg (le_max_left _ _) (le_max_right _ _) hA hrich)

/-- Up to t vertices on the degree-bounded side may have unrestricted degrees. -/
theorem OMA.degree_side_descending_moment_bound {V W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (X : SimpleGraph W) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (E : Finset {v : V // v ∉ R}) (hE : E.card ≤ t)
    (hdeg : ∀ v ∉ E, F.degree v.val ≤ t) (hfree : F.Free X) :
    let s := max t (Fintype.card V)
    (∑ v, (X.degree v).descFactorial t) ≤ Fintype.card W ^ t * (s ^ t + s) := by
  intro s
  by_contra! h
  obtain ⟨q, A, hsub, hA, hrich⟩ := OMA.rich_tuples_of_descending_degree_moment X ht s h
  let k : E ↪ Fin t := E.equivFin.toEmbedding.trans (Fin.castLEEmb hE)
  let m : E ↪ W := k.trans q
  apply hfree (contained_of_rich_tuples_with_exceptional F X R E m hcolors hdeg
    (le_max_left _ _) (le_max_right _ _) hA hrich ?_)
  intro x w hw
  exact (OMA.mem_tupleCommon X q w).mp (hsub hw) (k x)

theorem degree_moment_le_of_descending {W : Type*} [Fintype W] (X : SimpleGraph W)
    {t C : ℕ} (ht : 0 < t) (hn : 0 < Fintype.card W)
    (hdesc : (∑ v, (X.degree v).descFactorial t) ≤ Fintype.card W ^ t * C) :
    (∑ v, X.degree v ^ t) ≤ Fintype.card W ^ t * (2 ^ t * (C + t ^ t)) := by
  have hterm (d : ℕ) : d ^ t ≤ 2 ^ t * (d.descFactorial t + t ^ t) := by
    have hd : d ≤ 2 * max (d - t) t := by
      have h₁ := le_max_left (d - t) t
      have h₂ := le_max_right (d - t) t
      omega
    have htrunc : (d - t) ^ t ≤ d.descFactorial t :=
      (Nat.pow_le_pow_left (by omega) t).trans (Nat.pow_sub_le_descFactorial d t)
    calc
      _ ≤ (2 * max (d - t) t) ^ t := Nat.pow_le_pow_left hd t
      _ = 2 ^ t * (max (d - t) t) ^ t := mul_pow _ _ _
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        rcases le_total (d - t) t with h | h
        · rw [max_eq_right h]
          exact Nat.le_add_left _ _
        · rw [max_eq_left h]
          exact htrunc.trans (Nat.le_add_right _ _)
  let n := Fintype.card W
  have hnle : n ≤ n ^ t := by
    calc
      n = n ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hn ht
  calc
    (∑ v, X.degree v ^ t) ≤ ∑ v, 2 ^ t * ((X.degree v).descFactorial t + t ^ t) :=
      sum_le_sum fun v _ => hterm _
    _ = 2 ^ t * ((∑ v, (X.degree v).descFactorial t) + n * t ^ t) := by
      rw [← mul_sum, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
      simp [n]
    _ ≤ 2 ^ t * (n ^ t * C + n ^ t * t ^ t) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add hdesc (Nat.mul_le_mul_right _ hnle))
    _ = _ := by simp only [← Nat.mul_add]; ac_rfl

theorem edge_bound_of_degree_moment {W : Type*} [Fintype W] (X : SimpleGraph W)
    (hn : 0 < Fintype.card W) {t C : ℕ} (ht : 0 < t) (hC : 0 < C)
    (hmoment : (∑ v, X.degree v ^ t) ≤ Fintype.card W ^ t * C) :
    (X.edgeFinset.card : ℝ) ≤ (C : ℝ) * (Fintype.card W : ℝ) ^ (2 - 1 / (t : ℝ)) := by
  let n : ℝ := Fintype.card W
  let β : ℝ := 1 - 1 / (t : ℝ)
  have hnpos : 0 < n := Nat.cast_pos.mpr hn
  have htpos : 0 < (t : ℝ) := by exact_mod_cast ht
  have hmean := Real.pow_arith_mean_le_arith_mean_pow (univ : Finset W) (fun _ => n⁻¹)
      (fun v => (X.degree v : ℝ)) (fun _ _ => by positivity)
      (by simp [n, hnpos.ne'])
      (fun _ _ => by positivity) t
  simp_rw [← mul_sum] at hmean
  have hhand : (∑ v, (X.degree v : ℝ)) = 2 * (X.edgeFinset.card : ℝ) := by
    exact_mod_cast X.sum_degrees_eq_twice_card_edges
  rw [hhand] at hmean
  have hm : (∑ v, (X.degree v : ℝ) ^ t) ≤ n ^ t * C := by
    dsimp only [n]
    exact_mod_cast hmoment
  have hb : (n ^ β) ^ t = n ^ t / n := by
    rw [← Real.rpow_natCast (n ^ β) t, ← Real.rpow_mul hnpos.le,
      show β * (t : ℝ) = (t : ℝ) - 1 by dsimp [β]; field_simp,
      Real.rpow_sub hnpos, Real.rpow_natCast, Real.rpow_one]
  have hCpow : (C : ℝ) ≤ (C : ℝ) ^ t := by
    calc
      (C : ℝ) = (C : ℝ) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hC) ht
  have hroot : (2 * (X.edgeFinset.card : ℝ) / n) ^ t ≤ ((C : ℝ) * n ^ β) ^ t := by
    calc
      _ = (n⁻¹ * (2 * (X.edgeFinset.card : ℝ))) ^ t := by rw [div_eq_inv_mul]
      _ ≤ n⁻¹ * (n ^ t * C) := hmean.trans (mul_le_mul_of_nonneg_left hm (by positivity))
      _ = (C : ℝ) * (n ^ β) ^ t := by rw [hb, div_eq_mul_inv]; ring
      _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hCpow (by positivity)
  have hlin : 2 * (X.edgeFinset.card : ℝ) / n ≤ (C : ℝ) * n ^ β :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) ht.ne').mp hroot
  have he : (C : ℝ) * n ^ β * n = (C : ℝ) * n ^ (2 - 1 / (t : ℝ)) := by
    calc
      _ = (C : ℝ) * (n ^ β * n ^ (1 : ℝ)) := by rw [Real.rpow_one, mul_assoc]
      _ = _ := by
        rw [← Real.rpow_add hnpos]
        congr 2
        dsimp [β]
        ring
  have h := (div_le_iff₀ hnpos).mp hlin
  rw [he] at h
  change (X.edgeFinset.card : ℝ) ≤ (C : ℝ) * n ^ (2 - 1 / (t : ℝ))
  linarith only [h, Nat.cast_nonneg (α := ℝ) X.edgeFinset.card]

/-- A bipartition with degree at most t on one side gives an extremal bound of order n^(2 − 1/t). -/
theorem OMA.extremalNumber_le_degree_side_power {V : Type*} [Fintype V]
    (F : SimpleGraph V) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ R, F.degree v ≤ t) (hF : F ≠ ⊥) {n : ℕ} (hn : 0 < n) :
    let s := max t (Fintype.card V)
    (extremalNumber n F : ℝ) ≤ ((s ^ t + s : ℕ) : ℝ) * (n : ℝ) ^ (2 - 1 / (t : ℝ)) := by
  intro s
  obtain ⟨X, _, hX⟩ := exists_isExtremal_free (V := Fin n) hF
  obtain ⟨hfree, he⟩ := isExtremal_free_iff.mp hX
  rw [Fintype.card_fin] at he
  have hs : 0 < s := ht.trans_le (le_max_left _ _)
  have hC : 0 < s ^ t + s := by omega
  rw [← he]
  have h := edge_bound_of_degree_moment X (by simpa using hn) ht hC
    (OMA.degree_side_moment_bound F X R ht hcolors hdeg hfree)
  simp only [Fintype.card_fin] at h
  convert! h

theorem exponent_le_of_extremal_bound {V : Type*} (F : SimpleGraph V)
    {C α β : ℝ} (hα : ((fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) ∧ ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)))
    (hbound : ∀ {n : ℕ}, 0 < n → (extremalNumber n F : ℝ) ≤ C * (n : ℝ) ^ β) :
    α ≤ β := by
  by_contra! hgt
  have hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ β) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact hbound hn
  have hsmall : (fun n : ℕ => (n : ℝ) ^ β) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) := by
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) :=
      (eventually_gt_atTop (0 : ℕ)).mono fun n hn => by exact_mod_cast hn
    apply (isLittleO_iff_tendsto' (hpos.mono fun n hn hzero =>
      ((Real.rpow_pos_of_pos hn α).ne' hzero).elim)).2
    refine ((tendsto_rpow_neg_atTop (sub_pos.mpr hgt)).comp tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [hpos] with n hn
    change (n : ℝ) ^ (-(α - β)) = _
    rw [neg_sub, Real.rpow_sub hn]
  exact hα.2 (hO.trans_isLittleO hsmall)

theorem OMA.exponent_le_degree_side_bound {V : Type*} [Fintype V]
    (F : SimpleGraph V) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (hdeg : ∀ v ∉ R, F.degree v ≤ t) (hF : F ≠ ⊥)
    {α : ℝ} (hα : ((fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) ∧ ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α))) :
    α ≤ 2 - 1 / (t : ℝ) := by
  exact exponent_le_of_extremal_bound F hα
    (fun hn => OMA.extremalNumber_le_degree_side_power F R ht hcolors hdeg hF hn)

/-- The exceptional vertices preserve the upper exponent 2 − 1/t. -/
theorem OMA.extremalNumber_le_exceptional_degree_side_power {V : Type*} [Fintype V]
    (F : SimpleGraph V) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (E : Finset {v : V // v ∉ R}) (hE : E.card ≤ t)
    (hdeg : ∀ v ∉ E, F.degree v.val ≤ t) (hF : F ≠ ⊥) {n : ℕ} (hn : 0 < n) :
    let s := max t (Fintype.card V)
    (extremalNumber n F : ℝ) ≤ ((2 ^ t * (s ^ t + s + t ^ t) : ℕ) : ℝ) *
      (n : ℝ) ^ (2 - 1 / (t : ℝ)) := by
  intro s
  obtain ⟨X, _, hX⟩ := exists_isExtremal_free (V := Fin n) hF
  obtain ⟨hfree, he⟩ := isExtremal_free_iff.mp hX
  rw [Fintype.card_fin] at he
  have hC : 0 < 2 ^ t * (s ^ t + s + t ^ t) :=
    Nat.mul_pos (by positivity) (by have hs : 0 < s := ht.trans_le (le_max_left _ _); omega)
  have hnX : 0 < Fintype.card (Fin n) := by simpa using hn
  have hm := degree_moment_le_of_descending X ht hnX
    (OMA.degree_side_descending_moment_bound F X R ht hcolors E hE hdeg hfree)
  rw [← he]
  have h := edge_bound_of_degree_moment X hnX ht hC hm
  simp only [Fintype.card_fin] at h
  convert! h

theorem OMA.exponent_le_exceptional_degree_side_bound {V : Type*} [Fintype V]
    (F : SimpleGraph V) (R : Finset V) {t : ℕ} (ht : 0 < t)
    (hcolors : ∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R))
    (E : Finset {v : V // v ∉ R}) (hE : E.card ≤ t)
    (hdeg : ∀ v ∉ E, F.degree v.val ≤ t) (hF : F ≠ ⊥)
    {α : ℝ} (hα : ((fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) ∧ ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α))) :
    α ≤ 2 - 1 / (t : ℝ) := by
  exact exponent_le_of_extremal_bound F hα
    (fun hn => OMA.extremalNumber_le_exceptional_degree_side_power F R ht hcolors E hE hdeg hF hn)

theorem ne_bot_of_extremalPowerOrder {r : ℕ} (F : SimpleGraph (Fin r))
    {α : ℝ} (hF : ((fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) ∧ ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α))) : F ≠ ⊥ := by
  intro hbot
  apply hF.2
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [eventually_ge_atTop r] with n hn
  have h : extremalNumber n F ≤ 0 := by
    rw [← Fintype.card_fin n, extremalNumber_le_iff]
    intro X _ hfree
    exact (hfree (by rw [hbot, bot_isContained_iff_card_le]; simpa using hn)).elim
  simp only [Nat.le_zero.mp h, Nat.cast_zero, norm_zero]
  positivity

theorem affine_common_unique {K : Type*} [Field K]
    {a b u v : K × K} (hab : a ≠ b)
    (hau : a.2 + u.2 = a.1 * u.1) (hbu : b.2 + u.2 = b.1 * u.1)
    (hav : a.2 + v.2 = a.1 * v.1) (hbv : b.2 + v.2 = b.1 * v.1) : u = v := by
  have hfst : a.1 ≠ b.1 := by
    intro h
    apply hab
    have hs : a.2 = b.2 := by
      rw [h] at hau
      exact add_right_cancel (hau.trans hbu.symm)
    exact Prod.ext h hs
  have hzero : (a.1 - b.1) * (u.1 - v.1) = 0 := by
    linear_combination hbu - hau + hav - hbv
  have h : u.1 = v.1 := sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hfst))
  apply Prod.ext h
  rw [h] at hau
  exact add_left_cancel (hau.trans hav.symm)

theorem affineBipartiteGraph_free (K : Type*) [Field K]
    (X : SimpleGraph ((K × K) ⊕ (K × K)))
    (h1 : ∀ x y, X.Adj (.inl x) (.inr y) ↔ x.2 + y.2 = x.1 * y.1)
    (h2 : ∀ x y, X.Adj (.inr x) (.inl y) ↔ x.2 + y.2 = x.1 * y.1)
    (h3 : ∀ x y, ¬ X.Adj (.inl x) (.inl y))
    (h4 : ∀ x y, ¬ X.Adj (.inr x) (.inr y)) :
    (completeBipartiteGraph (Fin 2) (Fin 2)).Free X := by
  have hcommon : ∀ a b u v, a ≠ b →
      X.Adj a u → X.Adj b u → X.Adj a v → X.Adj b v → u = v := by
    rintro (a | a) (b | b) (u | u) (v | v) hab hau hbu hav hbv
    all_goals simp_all
    all_goals exact affine_common_unique hab hau hbu hav hbv
  intro h
  let f := h.some
  have hadj (i j : Fin 2) : X.Adj (f (.inl i)) (f (.inr j)) :=
    f.toHom.map_rel' (Or.inl ⟨rfl, rfl⟩)
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hne : f (.inl 0) ≠ f (.inl 1) := fun h => h01 (Sum.inl.inj (f.injective h))
  have heq := hcommon _ _ _ _ hne (hadj 0 0) (hadj 1 0) (hadj 0 1) (hadj 1 1)
  exact h01 (Sum.inr.inj (f.injective heq))

theorem affineBipartiteGraph_edges (K : Type*) [Field K] [Fintype K]
    (X : SimpleGraph ((K × K) ⊕ (K × K))) [Fintype X.edgeSet]
    (h1 : ∀ x y, X.Adj (.inl x) (.inr y) ↔ x.2 + y.2 = x.1 * y.1) :
    Fintype.card K ^ 3 ≤ X.edgeFinset.card := by
  let fn : (K × K) × K → X.edgeFinset := fun z =>
    ⟨s(Sum.inl z.1, Sum.inr (z.2, z.1.1 * z.2 - z.1.2)), by
      apply mem_edgeFinset.mpr
      exact (h1 _ _).mpr (by ring)⟩
  have hinj : Function.Injective fn := by
    intro a b h
    have he := Sym2.eq_iff.mp (congrArg Subtype.val h)
    rcases he with ⟨hl, hr⟩ | ⟨hl, _⟩
    · exact Prod.ext (Sum.inl.inj hl) (congrArg Prod.fst (Sum.inr.inj hr))
    · exact (Sum.inl_ne_inr hl).elim
  simpa only [Fintype.card_coe, Fintype.card_prod, pow_succ, pow_zero, one_mul] using
    Fintype.card_le_of_injective fn hinj

/-- The affine incidence graphs give the four-cycle lower bound on a prime subsequence. -/
theorem OMA.cycle_four_extremal_subseq {p : ℕ} (hp : p.Prime) :
    p ^ 3 ≤ extremalNumber (2 * p ^ 2) (completeBipartiteGraph (Fin 2) (Fin 2)) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let X : SimpleGraph ((ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)) := {
    Adj := fun a b => match a, b with
      | .inl x, .inr y | .inr x, .inl y => x.2 + y.2 = x.1 * y.1
      | _, _ => False
    symm := by
      refine ⟨?_⟩
      rintro (x | x) (y | y) h
      all_goals first | exact h | simpa [add_comm, mul_comm] using h
    loopless := by
      refine ⟨?_⟩
      rintro (x | x) h <;> exact h }
  have h := (affineBipartiteGraph_edges (ZMod p) X (fun _ _ => Iff.rfl)).trans
    (card_edgeFinset_le_extremalNumber (affineBipartiteGraph_free (ZMod p) X
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ h => h) (fun _ _ h => h)))
  simpa [Fintype.card_sum, Fintype.card_prod, ZMod.card, two_mul, pow_two] using h

theorem OMA.exponent_ge_cycle_four {W : Type*} {F : SimpleGraph W}
    (hC4 : completeBipartiteGraph (Fin 2) (Fin 2) ⊑ F) {α : ℝ}
    (hO : (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α)) :
    (3 / 2 : ℝ) ≤ α := by
  by_contra! hα
  obtain ⟨C, hC⟩ := isBigO_iff.mp hO
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  have hβ : 0 < 3 - 2 * α := by linarith
  have hlarge : ∀ᶠ n : ℕ in atTop, C * (2 : ℝ) ^ α < (n : ℝ) ^ (3 - 2 * α) :=
    ((tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  obtain ⟨M, hM⟩ := eventually_atTop.mp hlarge
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max M N)
  have hp0 : 0 < (p : ℝ) := Nat.cast_pos.mpr hprime.pos
  have hpN : N ≤ 2 * p ^ 2 :=
    (le_max_right _ _).trans (hp.trans (by nlinarith only [hprime.two_le]))
  have hupper := hN _ hpN
  rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hupper
  push_cast at hupper
  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast_mul hp0.le] at hupper
  have hlower : (p : ℝ) ^ (3 : ℕ) ≤ (extremalNumber (2 * p ^ 2) F : ℝ) := by
    exact_mod_cast ((OMA.cycle_four_extremal_subseq hprime).trans hC4.extremalNumber_le)
  have hle := hlower.trans hupper
  have hlt := hM p ((le_max_left _ _).trans hp)
  rw [Real.rpow_sub hp0, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast,
    lt_div_iff₀ (Real.rpow_pos_of_pos hp0 _)] at hlt
  exact (not_lt_of_ge hle) (by simpa [mul_assoc] using hlt)

/-- Sub-three-halves case: a C4-free bipartite F, minimal at the power scale n^α with
1 < α < 3/2, α strictly above every random-deletion exponent of a subgraph and strictly
below every dependent-random-choice exponent 2 - 1/t, has rational α. -/
def H1 : Prop :=
  ∀ (r : ℕ) (F : SimpleGraph (Fin r)), F.IsBipartite →
    ¬ completeBipartiteGraph (Fin 2) (Fin 2) ⊑ F →
    ∀ α : ℝ, 1 < α → α < 3 / 2 →
      (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →
        s + J.edgeFinset.card < r + F.edgeFinset.card →
        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) →
      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F → 2 ≤ J.edgeFinset.card →
        (2 : ℝ) - ((s - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ) < α) →
      (∀ (R : Finset (Fin r)) (t : ℕ), 0 < t →
        (∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R)) →
        ∀ E : Finset {v : Fin r // v ∉ R}, E.card ≤ t →
          (∀ v ∉ E, F.degree v.val ≤ t) → α < 2 - 1 / (t : ℝ)) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

/-- Above-three-halves case: a bipartite F, minimal at the power scale n^α with
3/2 < α < 2, α strictly above every random-deletion exponent of a subgraph and strictly
below every dependent-random-choice exponent 2 - 1/t, has rational α. -/
def H2 : Prop :=
  ∀ (r : ℕ) (F : SimpleGraph (Fin r)), F.IsBipartite →
    ∀ α : ℝ, 3 / 2 < α → α < 2 →
      (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →
        s + J.edgeFinset.card < r + F.edgeFinset.card →
        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) →
      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F → 2 ≤ J.edgeFinset.card →
        (2 : ℝ) - ((s - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ) < α) →
      (∀ (R : Finset (Fin r)) (t : ℕ), 0 < t →
        (∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R)) →
        ∀ E : Finset {v : Fin r // v ∉ R}, E.card ≤ t →
          (∀ v ∉ E, F.degree v.val ≤ t) → α < 2 - 1 / (t : ℝ)) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

theorem main : H1 → H2 → type_of% @Erdos713.erdos_713.parts.ii := by
  intro hlow hhigh q G hb _ α c hα hc hG
  rcases eq_or_lt_of_le hα.1 with h1 | h1
  · exact ⟨1, by simp [← h1]⟩
  by_cases hmatch : ∃ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ G ∧
      2 ≤ J.edgeFinset.card ∧
      (2 : ℝ) - ((s - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ) = α
  · obtain ⟨s, J, _, _, heq⟩ := hmatch
    exact ⟨2 - ((s - 2 : ℕ) : ℚ) / ((J.edgeFinset.card - 1 : ℕ) : ℚ), by
      rw [← heq]; push_cast; ring⟩
  obtain ⟨r, F, hFG, hF, hminimal⟩ :=
    OMA.exists_minimal_extremalPower (OMA.extremalPowerOrder_of_equivalent hc.ne' hG)
  by_cases hupper : ∃ t : ℕ, α = 2 - 1 / (t : ℝ)
  · obtain ⟨t, heq⟩ := hupper
    refine ⟨2 - 1 / (t : ℚ), ?_⟩
    push_cast
    exact heq.symm
  have hFb : F.IsBipartite := Colorable.of_hom hFG.some.toHom hb
  have hdel : ∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F → 2 ≤ J.edgeFinset.card →
      (2 : ℝ) - ((s - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ) < α := by
    intro s J hJF hJ
    have hle := OMA.exponent_ge_deletion_bound J hJ
      ((OMA.extremalNumber_isBigO_of_contained hJF).trans hF.1)
    simp only [Fintype.card_fin] at hle
    exact lt_of_le_of_ne hle (fun heq => hmatch ⟨s, J, hJF.trans hFG, hJ, heq⟩)
  have hdrc : ∀ (R : Finset (Fin r)) (t : ℕ), 0 < t →
      (∀ ⦃u v⦄, F.Adj u v → (u ∈ R ↔ v ∉ R)) →
      ∀ E : Finset {v : Fin r // v ∉ R}, E.card ≤ t →
        (∀ v ∉ E, F.degree v.val ≤ t) → α < 2 - 1 / (t : ℝ) := by
    intro R t ht hcolors E hE hdeg
    exact lt_of_le_of_ne
      (OMA.exponent_le_exceptional_degree_side_bound F R ht hcolors E hE hdeg
        (ne_bot_of_extremalPowerOrder F hF) hF)
      (fun heq => hupper ⟨t, heq⟩)
  rcases lt_trichotomy α (3 / 2) with hlt | heq | hgt
  · have hC4 : ¬ completeBipartiteGraph (Fin 2) (Fin 2) ⊑ F := by
      intro hC4
      have hge := OMA.exponent_ge_cycle_four hC4 hF.1
      linarith
    exact hlow r F hFb hC4 α h1 hlt hF.1 hF.2 hminimal hdel hdrc
  · exact ⟨3 / 2, by rw [heq]; push_cast; ring⟩
  · exact hhigh r F hFb α hgt hα.2 hF.1 hF.2 hminimal hdel hdrc

end OMA.R_Erdos713_erdos_713_parts_ii_R3
