import FormalConjectures.ErdosProblems.«713»

-- Reduction Erdos713.erdos_713.parts.ii.R2 of Erdős Problem 713 — ii
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos713_erdos_713_parts_ii_R2

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


/-- Pendant/isolated-vertex case: a graph with a vertex of degree at most one cannot be
minimal at a superlinear power scale (every strictly smaller copy grows like o(n^α)). -/
def H1 : Prop :=
  ∀ (r : ℕ) (F : SimpleGraph (Fin r)), (∃ v, F.degree v < 2) →
    ∀ α : ℝ, 1 < α →
      ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →
        s + J.edgeFinset.card < r + F.edgeFinset.card →
        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) →
      False

/-- Minimum-degree-two core: a bipartite graph of order n^α, α ∈ (1,2), minimal at that
scale, with α strictly above every random-deletion exponent of its subgraphs, has
rational α. -/
def H2 : Prop :=
  ∀ (r : ℕ) (F : SimpleGraph (Fin r)), F.IsBipartite → (∀ v, 2 ≤ F.degree v) →
    ∀ α : ℝ, α ∈ Set.Ioo 1 2 →
      (fun n : ℕ => (extremalNumber n F : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      ¬ (fun n : ℕ => (extremalNumber n F : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α) →
      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F →
        s + J.edgeFinset.card < r + F.edgeFinset.card →
        (fun n : ℕ => (extremalNumber n J : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ α)) →
      (∀ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ F → 2 ≤ J.edgeFinset.card →
        (2 : ℝ) - ((s - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ) < α) →
      α ∈ Set.range ((↑) : ℚ → ℝ)

theorem main : H1 → H2 → type_of% @Erdos713.erdos_713.parts.ii := by
  intro h1 h2 q G hb _ α c hα hc hG
  rcases eq_or_lt_of_le hα.1 with h | h
  · exact ⟨1, by simp [← h]⟩
  by_cases hmatch : ∃ (s : ℕ) (J : SimpleGraph (Fin s)), J ⊑ G ∧
      2 ≤ J.edgeFinset.card ∧
      ((2 : ℝ) - ((s - 2 : ℕ) : ℝ) / ((J.edgeFinset.card - 1 : ℕ) : ℝ)) = α
  · obtain ⟨s, J, _, _, heq⟩ := hmatch
    exact ⟨2 - ((s - 2 : ℕ) : ℚ) / ((J.edgeFinset.card - 1 : ℕ) : ℚ), by push_cast; exact heq⟩
  obtain ⟨r, F, hFG, hF, hminimal⟩ :=
    OMA.exists_minimal_extremalPower (OMA.extremalPowerOrder_of_equivalent hc.ne' hG)
  by_cases hleaf : ∃ v, F.degree v < 2
  · exact (h1 r F hleaf α h hF.2 hminimal).elim
  push Not at hleaf
  apply h2 r F (Colorable.of_hom hFG.some.toHom hb) hleaf α ⟨h, hα.2⟩ hF.1 hF.2 hminimal
  intro s J hJF hJ
  have hle := OMA.exponent_ge_deletion_bound J hJ
    ((OMA.extremalNumber_isBigO_of_contained hJF).trans hF.1)
  simp only [Fintype.card_fin] at hle
  exact lt_of_le_of_ne hle (fun heq => hmatch ⟨s, J, hJF.trans hFG, hJ, heq⟩)

end OMA.R_Erdos713_erdos_713_parts_ii_R2
