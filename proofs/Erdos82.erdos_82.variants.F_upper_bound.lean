import FormalConjectures.ErdosProblems.«82»

/-! # Upper bound on F(n) for Erdős Problem 82 (Alon-Krivelevich-Sudakov) -/

namespace OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1

open SimpleGraph Filter Asymptotics

def H1 : Prop :=
  open scoped Classical in
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ n : ℕ, 1 ≤ n → ∀ U : Finset (Fin n), 2 ≤ U.card →
    (∑ G : SimpleGraph (Fin n),
      (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) *
      (∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        if G.Adj e.1 e.2
        then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
        else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))))
    ≤ (n : ℝ) * (C₁ / (U.card : ℝ)) ^ ((U.card : ℝ) / 2)

def H2 : Prop :=
  open scoped Classical in
  ∀ C₁ : ℝ, 0 < C₁ → ∃ c₂ : ℝ, 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ k : ℕ, Real.sqrt (n : ℝ) ≤ (k : ℝ) → k ≤ n →
      (((Finset.univ : Finset (Finset (Fin n))).filter (fun U =>
        U.card = k ∧ ∃ a b : Fin n, a ≤ b ∧ (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ∧
          (U.filter (· < a)).card ≤ k / (Nat.log 2 k + 1) ∧
          (U.filter (b < ·)).card ≤ k / (Nat.log 2 k + 1))).card : ℝ) *
      ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2)) < 1 / (2 * (n : ℝ) ^ 2)

def H3 : Prop :=
  open scoped Classical in
  ∀ c₂ : ℝ, 0 < c₂ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ k : ℕ, C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) ≤ (k : ℝ) → k ≤ n →
      (∑ G : SimpleGraph (Fin n),
        (if ∃ U : Finset (Fin n), U.card = k ∧
            (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
            (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
              k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
              k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
          then (1 : ℝ) else 0) *
        (∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))))
      < 1 / (2 * (n : ℝ) ^ 2)

section Helpers

open scoped Classical

private lemma prob_factor_bounds {n : ℕ} (hn : 1 ≤ n) (u v : Fin n) :
    0 ≤ (1 / 4 + (u : ℝ) / (2 * n)) * (1 / 4 + (v : ℝ) / (2 * n)) ∧
    (1 / 4 + (u : ℝ) / (2 * n)) * (1 / 4 + (v : ℝ) / (2 * n)) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound (w : Fin n) : 0 ≤ 1 / 4 + (w : ℝ) / (2 * n) ∧ 1 / 4 + (w : ℝ) / (2 * n) ≤ 1 := by
    have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
    have hw1 : (w : ℝ) ≤ n := Nat.cast_le.mpr w.isLt.le
    constructor
    · positivity
    · have h1 : (w : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        linarith
      linarith
  obtain ⟨hu0, hu1⟩ := hbound u
  obtain ⟨hv0, hv1⟩ := hbound v
  exact ⟨mul_nonneg hu0 hv0, mul_le_one₀ hu1 hv0 hv1⟩

private lemma weight_nonneg {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    0 ≤ ∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      if G.Adj e.1 e.2
      then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
      else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n)) := by
  refine Finset.prod_nonneg fun e _ => ?_
  obtain ⟨h0, h1⟩ := prob_factor_bounds hn e.1 e.2
  split_ifs
  · exact h0
  · linarith

private lemma sum_weight_eq_one (n : ℕ) :
    (∑ G : SimpleGraph (Fin n),
      ∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
        if G.Adj e.1 e.2
        then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
        else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))) = 1 := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let eGraph : SimpleGraph (Fin n) ≃ ({p : Fin n × Fin n // p ∈ E} → Bool) :=
    { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv
              simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu
              simpa [hvu, hn] using h⟩
          loopless := ⟨by
            intro u h
            simp at h⟩ }
      left_inv := fun G => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu
          simp [hn, hvu, G.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp [huv] }
  let q : {p : Fin n × Fin n // p ∈ E} → ℝ := fun e =>
    (1 / 4 + (e.1.1 : ℝ) / (2 * n)) * (1 / 4 + (e.1.2 : ℝ) / (2 * n))
  have h1 :
      (∑ G : SimpleGraph (Fin n),
        ∏ e ∈ E,
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))) =
      ∑ f : ({p : Fin n × Fin n // p ∈ E} → Bool),
        ∏ e : {p : Fin n × Fin n // p ∈ E}, if f e = true then q e else 1 - q e := by
    refine Fintype.sum_equiv eGraph _ _ fun G => ?_
    rw [← Finset.prod_coe_sort E]
    refine Finset.prod_congr rfl fun ⟨e, he⟩ _ => ?_
    simp [eGraph, q]
  have hps := Fintype.prod_sum (fun (e : {p : Fin n × Fin n // p ∈ E}) (b : Bool) =>
    if b = true then q e else 1 - q e)
  rw [h1, ← hps]
  refine Finset.prod_eq_one fun e _ => ?_
  simp

private lemma regular_of_isRegularInduced {n : ℕ} {G : SimpleGraph (Fin n)} {S : Subgraph G}
    (hS : Erdos82.IsRegularInduced S) :
    ∃ d : ℕ, ∀ u ∈ S.verts.toFinset, (S.verts.toFinset.filter (fun v => G.Adj u v)).card = d := by
  obtain ⟨hind, d, hd⟩ := hS
  refine ⟨d, fun u hu => ?_⟩
  have hu' : u ∈ S.verts := Set.mem_toFinset.mp hu
  have h1 : (S.verts.toFinset.filter (fun v => G.Adj u v)).card =
      Fintype.card (S.coe.neighborSet ⟨u, hu'⟩) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ?_
    exact
      { toFun := fun ⟨v, hv⟩ => ⟨⟨v, Set.mem_toFinset.mp (Finset.mem_filter.mp hv).1⟩,
          hind.adj.mpr (Finset.mem_filter.mp hv).2⟩
        invFun := fun ⟨⟨v, hv⟩, hadj⟩ => ⟨v, Finset.mem_filter.mpr
          ⟨Set.mem_toFinset.mpr hv, S.coe_adj_sub _ _ hadj⟩⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  rw [h1, Fintype.card_eq_nat_card]
  have h2 := hd ⟨u, hu'⟩
  dsimp only [SimpleGraph.degree, SimpleGraph.neighborFinset] at h2
  rw [@Set.toFinset_card _ _ ((fun v => Subgraph.coeFiniteAt v) ⟨u, hu'⟩),
    @Fintype.card_eq_nat_card _ ((fun v => Subgraph.coeFiniteAt v) ⟨u, hu'⟩)] at h2
  exact h2

private lemma partition_subset {n k : ℕ} (hk : 16 ≤ k) (U : Finset (Fin n)) (hU : U.card = k)
    (c₂ : ℝ) :
    (∃ a b : Fin n, a ≤ b ∧ (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ∧
      (U.filter (· < a)).card ≤ k / (Nat.log 2 k + 1) ∧
      (U.filter (b < ·)).card ≤ k / (Nat.log 2 k + 1)) ∨
    (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
      k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
      k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card) := by
  set m := k / (Nat.log 2 k + 1)
  have hlog : 4 ≤ Nat.log 2 k := by
    have : Nat.log 2 16 ≤ Nat.log 2 k := Nat.log_mono_right hk
    have h16 : Nat.log 2 16 = 4 := by decide
    omega
  have hm5 : 5 * m ≤ k := by
    have hmul : (Nat.log 2 k + 1) * m ≤ k := Nat.mul_div_le k (Nat.log 2 k + 1)
    have hle : 5 * m ≤ (Nat.log 2 k + 1) * m := Nat.mul_le_mul_right m (by omega)
    omega
  have hm_lt : m < k - 1 - m := by omega
  have hbm_lt : k - 1 - m < k := by omega
  let e := U.orderEmbOfFin hU
  let a := e ⟨m, by omega⟩
  let b := e ⟨k - 1 - m, hbm_lt⟩
  have hab : a < b := by
    change e ⟨m, by omega⟩ < e ⟨k - 1 - m, hbm_lt⟩
    rw [e.lt_iff_lt]
    exact Fin.mk_lt_mk.mpr hm_lt
  have hlt_card : (U.filter (· < a)).card = m := by
    have himg : U.filter (· < a) = Finset.image (fun i : Fin m => e ⟨i.1, by omega⟩) Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hxU, hxa⟩
        have hxmem : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hxU
        obtain ⟨j, rfl⟩ := hxmem
        have hj : j < ⟨m, by omega⟩ := (e.lt_iff_lt).mp hxa
        exact ⟨⟨j.1, hj⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨?_, ?_⟩
        · have : e ⟨i.1, by omega⟩ ∈ Set.range e := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · exact (e.lt_iff_lt).mpr (Fin.mk_lt_mk.mpr i.isLt)
    rw [himg, Finset.card_image_of_injective _ (fun i j hij => by
      have := e.injective hij
      exact Fin.ext (by simpa using congrArg Fin.val this)), Finset.card_fin]
  have hgt_card : (U.filter (b < ·)).card = m := by
    have himg : U.filter (b < ·) =
        Finset.image (fun i : Fin m => e ⟨k - 1 - i.1, by omega⟩) Finset.univ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hxU, hbx⟩
        have hxmem : x ∈ Set.range e := by rw [Finset.range_orderEmbOfFin]; exact hxU
        obtain ⟨j, rfl⟩ := hxmem
        have hj : k - 1 - m < j.1 := (e.lt_iff_lt).mp hbx
        refine ⟨⟨k - 1 - j.1, by omega⟩, ?_⟩
        have hidx : (⟨k - 1 - (k - 1 - j.1), by omega⟩ : Fin k) = j := by
          apply Fin.ext
          dsimp
          omega
        rw [hidx]
      · rintro ⟨i, rfl⟩
        refine ⟨?_, ?_⟩
        · have : e ⟨k - 1 - i.1, by omega⟩ ∈ Set.range e := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · exact (e.lt_iff_lt).mpr (Fin.mk_lt_mk.mpr (by omega))
    rw [himg, Finset.card_image_of_injective _ (fun i j hij => by
      have := congrArg Fin.val (e.injective hij)
      dsimp at this
      exact Fin.ext (by omega)), Finset.card_fin]
  by_cases hspan : (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ)
  · left
    exact ⟨a, b, hab.le, hspan, hlt_card.le, hgt_card.le⟩
  · right
    have hle1 : m ≤ (U.filter (· ≤ a)).card := by
      rw [← hlt_card]
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, le_of_lt hx.2⟩
    have hle2 : m ≤ (U.filter (b ≤ ·)).card := by
      rw [← hgt_card]
      refine Finset.card_le_card fun x hx => ?_
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, le_of_lt hx.2⟩
    exact ⟨a, b, hab, le_of_not_ge hspan, hle1, hle2⟩

end Helpers

theorem main : H1 → H2 → H3 → type_of% @Erdos82.erdos_82.variants.F_upper_bound := by
  classical
  intro h1 h2 h3
  obtain ⟨C₁, hC₁, h_single⟩ := h1
  obtain ⟨c₂, hc₂, N₁, h_case1⟩ := h2 C₁ hC₁
  obtain ⟨C, hC, N₂, h_case2⟩ := h3 c₂ hc₂
  have htend : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ))
      atTop atTop := by
    refine Tendsto.atTop_mul_atTop₀ (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) ?_
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog_tend : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp (htend.eventually_ge_atTop (16 / C))
  obtain ⟨N₄, hN₄⟩ := eventually_atTop.mp (hlog_tend.eventually_ge_atTop (1 / C))
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.mp (htend.eventually_ge_atTop 1)
  let N := max (max N₁ N₂) (max (max N₃ N₄) (max N₅ 2))
  have hF_bound : ∀ n : ℕ, N ≤ n →
      (Erdos82.F n : ℝ) ≤ (C + 1) * (Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hnN₁ : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnN₂ : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hnN₃ : N₃ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hn)
    have hnN₄ : N₄ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_right _ _) hn)
    have hnN₅ : N₅ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_right _ _) hn)
    let bound : ℝ := C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)
    let K : ℕ := Nat.ceil bound
    have hbound16 : 16 ≤ bound := by
      have h3 := hN₃ n hnN₃
      dsimp only [bound]
      rw [mul_assoc]
      exact (div_le_iff₀' hC).mp h3
    have hlog1 : 1 ≤ C * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := (div_le_iff₀' hC).mp (hN₄ n hnN₄)
    have hbound_sqrt : Real.sqrt (n : ℝ) ≤ bound := by
      dsimp only [bound]
      calc Real.sqrt (n : ℝ)
          = 1 * Real.sqrt (n : ℝ) := (one_mul _).symm
        _ ≤ (C * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) * Real.sqrt (n : ℝ) :=
            mul_le_mul_of_nonneg_right hlog1 (Real.sqrt_nonneg _)
        _ = C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by ring
    have hK16 : 16 ≤ K := by
      exact_mod_cast (hbound16.trans (Nat.le_ceil bound))
    have hK_real : bound ≤ (K : ℝ) := Nat.le_ceil bound
    have h_exists_G : ∃ G : SimpleGraph (Fin n),
        ∀ S : Subgraph G, Erdos82.IsRegularInduced S → S.verts.ncard < K := by
      by_cases hKn : K ≤ n
      · let w : SimpleGraph (Fin n) → ℝ := fun G =>
          ∏ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
            if G.Adj e.1 e.2
            then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
            else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
        let bad : SimpleGraph (Fin n) → Prop := fun G =>
          ∃ S : Subgraph G, Erdos82.IsRegularInduced S ∧ K ≤ S.verts.ncard
        have hbad_sum : (∑ G : SimpleGraph (Fin n), (if bad G then (1 : ℝ) else 0) * w G) < 1 := by
          have hstep : ∀ k ∈ Finset.Icc K n,
              (∑ G : SimpleGraph (Fin n),
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G) < 1 / (n : ℝ) ^ 2 := by
            intro k hk
            rw [Finset.mem_Icc] at hk
            have hk16 : 16 ≤ k := le_trans hK16 hk.1
            have hk2 : 2 ≤ k := by omega
            have hk_bound : bound ≤ (k : ℝ) := hK_real.trans (Nat.cast_le.mpr hk.1)
            have hk_sqrt : Real.sqrt (n : ℝ) ≤ (k : ℝ) := hbound_sqrt.trans hk_bound
            let Small := (Finset.univ : Finset (Finset (Fin n))).filter (fun U =>
              U.card = k ∧ ∃ a b : Fin n, a ≤ b ∧ (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ∧
                (U.filter (· < a)).card ≤ k / (Nat.log 2 k + 1) ∧
                (U.filter (b < ·)).card ≤ k / (Nat.log 2 k + 1))
            have hpt : ∀ G : SimpleGraph (Fin n),
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G ≤
                (∑ U ∈ Small,
                  (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) * w G) +
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                    (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                      k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                      k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                  then (1 : ℝ) else 0) * w G := by
              intro G
              have hwG := weight_nonneg hn1 G
              by_cases hG : ∃ U : Finset (Fin n), U.card = k ∧
                  (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
              · simp only [hG, ↓reduceIte, one_mul]
                obtain ⟨U, hUk, hUreg⟩ := hG
                rcases partition_subset hk16 U hUk c₂ with hsm | hlg
                · have hUSm : U ∈ Small := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUk, hsm⟩
                  have hle1 : w G ≤ ∑ U' ∈ Small,
                      (if ∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d
                        then (1 : ℝ) else 0) * w G := by
                    refine Finset.single_le_sum (f := fun U' =>
                        (if ∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d
                          then (1 : ℝ) else 0) * w G)
                      (fun U' _ => mul_nonneg (by split_ifs <;> norm_num) hwG) hUSm |>.trans_eq' ?_
                    simp [hUreg]
                  have hle2 : 0 ≤ (if ∃ U : Finset (Fin n), U.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                      (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                      then (1 : ℝ) else 0) * w G := mul_nonneg (by split_ifs <;> norm_num) hwG
                  linarith
                · have hGlg : ∃ U : Finset (Fin n), U.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                      (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card) := ⟨U, hUk, hUreg, hlg⟩
                  have hsum0 : 0 ≤ ∑ U' ∈ Small,
                      (if ∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d
                        then (1 : ℝ) else 0) * w G :=
                    Finset.sum_nonneg fun U' _ => mul_nonneg (by split_ifs <;> norm_num) hwG
                  simp only [hGlg, ↓reduceIte, one_mul]
                  linarith
              · simp only [hG, ↓reduceIte, zero_mul]
                have hsum0 : 0 ≤ ∑ U' ∈ Small,
                    (if ∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d
                      then (1 : ℝ) else 0) * w G :=
                  Finset.sum_nonneg fun U' _ => mul_nonneg (by split_ifs <;> norm_num) hwG
                have hle2 : 0 ≤ (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                    (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                      k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                      k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                    then (1 : ℝ) else 0) * w G := mul_nonneg (by split_ifs <;> norm_num) hwG
                linarith
            have hsum_le :
                (∑ G : SimpleGraph (Fin n),
                  (if ∃ U : Finset (Fin n), U.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                    then (1 : ℝ) else 0) * w G) ≤
                (∑ U ∈ Small, ∑ G : SimpleGraph (Fin n),
                  (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) * w G) +
                (∑ G : SimpleGraph (Fin n),
                  (if ∃ U : Finset (Fin n), U.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                      (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                        k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                    then (1 : ℝ) else 0) * w G) := by
              calc (∑ G : SimpleGraph (Fin n),
                      (if ∃ U : Finset (Fin n), U.card = k ∧
                          (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                        then (1 : ℝ) else 0) * w G)
                  ≤ ∑ G : SimpleGraph (Fin n),
                      ((∑ U ∈ Small,
                        (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d
                          then (1 : ℝ) else 0) * w G) +
                      (if ∃ U : Finset (Fin n), U.card = k ∧
                          (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
                          (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
                            k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
                            k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
                        then (1 : ℝ) else 0) * w G) := Finset.sum_le_sum fun G _ => hpt G
                _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_comm]
            have hb1 :
                (∑ U ∈ Small, ∑ G : SimpleGraph (Fin n),
                  (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) * w G)
                < 1 / (2 * (n : ℝ) ^ 2) := by
              have hb1a :
                  (∑ U ∈ Small, ∑ G : SimpleGraph (Fin n),
                    (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) * w G)
                  ≤ (Small.card : ℝ) * ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2)) := by
                calc _ ≤ ∑ U ∈ Small, (n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2) := by
                        refine Finset.sum_le_sum fun U hU => ?_
                        have hUk : U.card = k := (Finset.mem_filter.mp hU).2.1
                        have hs := h_single n hn1 U (by omega)
                        dsimp only [w]
                        rw [hUk] at hs
                        exact hs
                  _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
              exact hb1a.trans_lt (h_case1 n hnN₁ k hk_sqrt hk.2)
            have hb2 := h_case2 n hnN₂ k hk_bound hk.2
            have heq : 1 / (2 * (n : ℝ) ^ 2) + 1 / (2 * (n : ℝ) ^ 2) = 1 / (n : ℝ) ^ 2 := by ring
            linarith
          have hpt_bad : ∀ G : SimpleGraph (Fin n),
              (if bad G then (1 : ℝ) else 0) * w G ≤
              ∑ k ∈ Finset.Icc K n,
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G := by
            intro G
            have hwG := weight_nonneg hn1 G
            by_cases hG : bad G
            · simp only [hG, ↓reduceIte, one_mul]
              obtain ⟨S, hSreg, hSK⟩ := hG
              let U := S.verts.toFinset
              have hUk : U.card = S.verts.ncard := Set.ncard_eq_toFinset_card' S.verts |>.symm
              have hUle : U.card ≤ n := by
                simpa using (U.card_le_univ.trans_eq (Fintype.card_fin n))
              have hmem : U.card ∈ Finset.Icc K n := Finset.mem_Icc.mpr ⟨by omega, hUle⟩
              have hUreg := regular_of_isRegularInduced hSreg
              have hex : ∃ U' : Finset (Fin n), U'.card = U.card ∧
                  (∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d) := ⟨U, rfl, hUreg⟩
              refine Finset.single_le_sum (f := fun k =>
                  (if ∃ U' : Finset (Fin n), U'.card = k ∧
                      (∃ d : ℕ, ∀ u ∈ U', (U'.filter (fun v => G.Adj u v)).card = d)
                    then (1 : ℝ) else 0) * w G)
                (fun k _ => mul_nonneg (by split_ifs <;> norm_num) hwG) hmem |>.trans_eq' ?_
              simp [hex]
            · simp only [hG, ↓reduceIte, zero_mul]
              exact Finset.sum_nonneg fun k _ => mul_nonneg (by split_ifs <;> norm_num) hwG
          have hsum_bad :
              (∑ G : SimpleGraph (Fin n), (if bad G then (1 : ℝ) else 0) * w G) ≤
              ∑ k ∈ Finset.Icc K n, ∑ G : SimpleGraph (Fin n),
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G := by
            calc _ ≤ ∑ G : SimpleGraph (Fin n), ∑ k ∈ Finset.Icc K n,
                      (if ∃ U : Finset (Fin n), U.card = k ∧
                          (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                        then (1 : ℝ) else 0) * w G := Finset.sum_le_sum fun G _ => hpt_bad G
              _ = _ := Finset.sum_comm
          have hIcc_ne : (Finset.Icc K n).Nonempty := ⟨K, Finset.mem_Icc.mpr ⟨le_rfl, hKn⟩⟩
          have hsum_lt :
              (∑ k ∈ Finset.Icc K n, ∑ G : SimpleGraph (Fin n),
                (if ∃ U : Finset (Fin n), U.card = k ∧
                    (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
                  then (1 : ℝ) else 0) * w G) <
              ∑ _ ∈ Finset.Icc K n, (1 / (n : ℝ) ^ 2) :=
            Finset.sum_lt_sum (fun k hk => (hstep k hk).le) ⟨K, Finset.mem_Icc.mpr ⟨le_rfl, hKn⟩, hstep K (Finset.mem_Icc.mpr ⟨le_rfl, hKn⟩)⟩
          have hcard_le : ((Finset.Icc K n).card : ℝ) ≤ (n : ℝ) := by
            have : (Finset.Icc K n).card ≤ n := by
              rw [Nat.card_Icc]
              omega
            exact_mod_cast this
          have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
          have hbound1 : (∑ _ ∈ Finset.Icc K n, (1 / (n : ℝ) ^ 2)) ≤ 1 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            calc ((Finset.Icc K n).card : ℝ) * (1 / (n : ℝ) ^ 2)
                ≤ (n : ℝ) * (1 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hcard_le (by positivity)
              _ = 1 / (n : ℝ) := by field_simp
              _ ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hn1) (by positivity)
          linarith
        by_contra! hall
        have hsum_eq : (∑ G : SimpleGraph (Fin n), (if bad G then (1 : ℝ) else 0) * w G) = 1 := by
          have h1 : ∀ G : SimpleGraph (Fin n), (if bad G then (1 : ℝ) else 0) * w G = w G := by
            intro G
            obtain ⟨S, hS1, hS2⟩ := hall G
            have hbadG : bad G := ⟨S, hS1, hS2⟩
            simp [hbadG]
          simp_rw [h1]
          exact sum_weight_eq_one n
        linarith
      · refine ⟨⊥, fun S _ => ?_⟩
        have hcard : S.verts.ncard ≤ n := by
          have := S.verts.toFinset.card_le_univ
          rw [Fintype.card_fin] at this
          rwa [Set.ncard_eq_toFinset_card']
        omega
    obtain ⟨G, hG⟩ := h_exists_G
    have hF_le_K : Erdos82.F n ≤ K := by
      rw [Erdos82.F]
      refine csSup_le ⟨0, fun G' => ⟨⊥, ⟨fun _ hv _ => False.elim hv, 0, fun v => False.elim v.2⟩, Nat.zero_le _⟩⟩ ?_
      · intro k hk
        obtain ⟨S, hSreg, hSk⟩ := hk G
        exact le_trans hSk (hG S hSreg).le
    have hK_ub : (K : ℝ) ≤ bound + 1 := by
      have := Nat.ceil_lt_add_one (by linarith : 0 ≤ bound)
      exact le_of_lt this
    have hsq1 : 1 ≤ Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := hN₅ n hnN₅
    calc (Erdos82.F n : ℝ)
        ≤ (K : ℝ) := by exact_mod_cast hF_le_K
      _ ≤ bound + 1 := hK_ub
      _ ≤ bound + Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by linarith
      _ = (C + 1) * (Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) := by
          dsimp only [bound]
          ring
  rw [Asymptotics.isBigO_iff]
  refine ⟨C + 1, eventually_atTop.mpr ⟨N, fun n hn => ?_⟩⟩
  have h1 : 1 ≤ n := by omega
  have hsq : 0 ≤ Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by
    have : 0 ≤ (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast h1)) _
    positivity
  rw [Real.norm_natCast, Real.norm_of_nonneg hsq]
  exact hF_bound n hn

end OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1

namespace E82H1
open scoped Classical

section Helpers

private lemma factorial_mul_exp_ge_pow (j : ℕ) :
    (j : ℝ) ^ j ≤ (Real.exp 1) ^ j * (j.factorial : ℝ) := by
  have hj_pos : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hsum : (j : ℝ) ^ j / (j.factorial : ℝ) ≤ Real.exp (j : ℝ) := by
    have h1 : (j : ℝ) ^ j / (j.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (j + 1), (j : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (j : ℝ) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self j))
    exact h1.trans (Real.sum_le_exp_of_nonneg (Nat.cast_nonneg j) (j + 1))
  have hexp : Real.exp (j : ℝ) = (Real.exp 1) ^ j := by
    rw [← mul_one (j : ℝ), Real.exp_nat_mul]
  rw [hexp, div_le_iff₀ hj_pos] at hsum
  exact hsum

private lemma central_binom_sq_mul_le (r : ℕ) :
    Nat.choose (2 * r) r ^ 2 * (2 * r + 1) ≤ 16 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hstep : (r + 1) * Nat.choose (2 * r + 2) (r + 1) =
        2 * (2 * r + 1) * Nat.choose (2 * r) r := by
      have h1 : (r + 1) * Nat.choose (2 * r + 2) (r + 1) =
          (2 * r + 2) * Nat.choose (2 * r + 1) r := by
        rw [Nat.mul_comm, ← Nat.add_one_mul_choose_eq (2 * r + 1) r]
      have h2 : (r + 1) * Nat.choose (2 * r + 1) r =
          (2 * r + 1) * Nat.choose (2 * r) r := by
        rw [← Nat.choose_symm_half r, Nat.mul_comm (r + 1), ← Nat.add_one_mul_choose_eq (2 * r) r]
      calc (r + 1) * Nat.choose (2 * r + 2) (r + 1)
          = (2 * r + 2) * Nat.choose (2 * r + 1) r := h1
        _ = 2 * ((r + 1) * Nat.choose (2 * r + 1) r) := by ring
        _ = 2 * ((2 * r + 1) * Nat.choose (2 * r) r) := by rw [h2]
        _ = 2 * (2 * r + 1) * Nat.choose (2 * r) r := by ring
    have hmul : (Nat.choose (2 * (r + 1)) (r + 1) ^ 2 * (2 * (r + 1) + 1)) * (r + 1) ^ 2 ≤
        16 ^ (r + 1) * (r + 1) ^ 2 := by
      have h2r : 2 * (r + 1) = 2 * r + 2 := by ring
      rw [h2r]
      calc (Nat.choose (2 * r + 2) (r + 1) ^ 2 * (2 * r + 3)) * (r + 1) ^ 2
          = ((r + 1) * Nat.choose (2 * r + 2) (r + 1)) ^ 2 * (2 * r + 3) := by ring
        _ = (2 * (2 * r + 1) * Nat.choose (2 * r) r) ^ 2 * (2 * r + 3) := by rw [hstep]
        _ = (4 * (2 * r + 1) * (2 * r + 3)) * (Nat.choose (2 * r) r ^ 2 * (2 * r + 1)) := by ring
        _ ≤ (4 * (2 * r + 1) * (2 * r + 3)) * 16 ^ r := Nat.mul_le_mul_left _ ih
        _ ≤ (16 * (r + 1) ^ 2) * 16 ^ r := by
            refine Nat.mul_le_mul_right _ ?_
            nlinarith
        _ = 16 ^ (r + 1) * (r + 1) ^ 2 := by rw [pow_succ]; ring
    exact Nat.le_of_mul_le_mul_right hmul (by positivity)

private lemma choose_div_pow_le_inv_sqrt (R s : ℕ) :
    (Nat.choose R s : ℝ) / (2 : ℝ) ^ R ≤ 1 / Real.sqrt ((R + 1 : ℕ) : ℝ) := by
  have hmid : Nat.choose R s ≤ Nat.choose R (R / 2) := Nat.choose_le_middle s R
  rcases Nat.even_or_odd' R with ⟨r, rfl | rfl⟩
  · have hdiv : 2 * r / 2 = r := by omega
    rw [hdiv] at hmid
    have hnat : Nat.choose (2 * r) r ^ 2 * (2 * r + 1) ≤ 16 ^ r := central_binom_sq_mul_le r
    have hreal : (Nat.choose (2 * r) r : ℝ) ^ 2 * ((2 * r + 1 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (2 * r)) ^ 2 := by
      have h16 : (16 : ℝ) ^ r = ((2 : ℝ) ^ (2 * r)) ^ 2 := by
        calc (16 : ℝ) ^ r = ((2 : ℝ) ^ 4) ^ r := by norm_num
          _ = (2 : ℝ) ^ (4 * r) := by rw [← pow_mul]
          _ = ((2 : ℝ) ^ (2 * r)) ^ 2 := by rw [← pow_mul]; congr 1; ring
      exact (by exact_mod_cast hnat : (Nat.choose (2 * r) r : ℝ) ^ 2 * ((2 * r + 1 : ℕ) : ℝ) ≤ (16 : ℝ) ^ r).trans_eq h16
    have hsq : ((Nat.choose (2 * r) r : ℝ) / (2 : ℝ) ^ (2 * r)) ^ 2 ≤
        (1 / Real.sqrt ((2 * r + 1 : ℕ) : ℝ)) ^ 2 := by
      rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hle : (Nat.choose (2 * r) r : ℝ) / (2 : ℝ) ^ (2 * r) ≤
        1 / Real.sqrt ((2 * r + 1 : ℕ) : ℝ) := by
      by_contra! hgt
      have := mul_self_lt_mul_self (by positivity) hgt
      rw [← sq, ← sq] at this
      linarith
    have hsub : (Nat.choose (2 * r) s : ℝ) / (2 : ℝ) ^ (2 * r) ≤
        (Nat.choose (2 * r) r : ℝ) / (2 : ℝ) ^ (2 * r) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hmid) (by positivity)
    exact hsub.trans hle
  · have hdiv : (2 * r + 1) / 2 = r := by omega
    rw [hdiv] at hmid
    have hdbl : 2 * Nat.choose (2 * r + 1) r = Nat.choose (2 * r + 2) (r + 1) := by
      have hsym : Nat.choose (2 * r + 1) (r + 1) = Nat.choose (2 * r + 1) r := Nat.choose_symm_half r
      rw [Nat.choose_succ_succ (2 * r + 1) r, hsym]
      omega
    have hnat : Nat.choose (2 * (r + 1)) (r + 1) ^ 2 * (2 * (r + 1) + 1) ≤ 16 ^ (r + 1) :=
      central_binom_sq_mul_le (r + 1)
    have h2r : 2 * (r + 1) = 2 * r + 2 := by ring
    rw [h2r] at hnat
    have hreal : (Nat.choose (2 * r + 2) (r + 1) : ℝ) ^ 2 * ((2 * r + 3 : ℕ) : ℝ) ≤
        ((2 : ℝ) ^ (2 * r + 2)) ^ 2 := by
      have h16 : (16 : ℝ) ^ (r + 1) = ((2 : ℝ) ^ (2 * r + 2)) ^ 2 := by
        calc (16 : ℝ) ^ (r + 1) = ((2 : ℝ) ^ 4) ^ (r + 1) := by norm_num
          _ = (2 : ℝ) ^ (4 * (r + 1)) := by rw [← pow_mul]
          _ = ((2 : ℝ) ^ (2 * r + 2)) ^ 2 := by rw [← pow_mul]; congr 1; ring
      have hnat' : Nat.choose (2 * r + 2) (r + 1) ^ 2 * (2 * r + 3) ≤ 16 ^ (r + 1) := by
        simpa [add_assoc] using hnat
      exact (by exact_mod_cast hnat' : (Nat.choose (2 * r + 2) (r + 1) : ℝ) ^ 2 * ((2 * r + 3 : ℕ) : ℝ) ≤ (16 : ℝ) ^ (r + 1)).trans_eq h16
    have hsq : ((Nat.choose (2 * r + 2) (r + 1) : ℝ) / (2 : ℝ) ^ (2 * r + 2)) ^ 2 ≤
        (1 / Real.sqrt ((2 * r + 3 : ℕ) : ℝ)) ^ 2 := by
      rw [div_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hle1 : (Nat.choose (2 * r + 2) (r + 1) : ℝ) / (2 : ℝ) ^ (2 * r + 2) ≤
        1 / Real.sqrt ((2 * r + 3 : ℕ) : ℝ) := by
      by_contra! hgt
      have := mul_self_lt_mul_self (by positivity) hgt
      rw [← sq, ← sq] at this
      linarith
    have hle2 : 1 / Real.sqrt ((2 * r + 3 : ℕ) : ℝ) ≤
        1 / Real.sqrt ((2 * r + 1 + 1 : ℕ) : ℝ) := by
      refine one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) ?_
      refine Real.sqrt_le_sqrt ?_
      norm_cast
      omega
    have heq : (Nat.choose (2 * r + 1) r : ℝ) / (2 : ℝ) ^ (2 * r + 1) =
        (Nat.choose (2 * r + 2) (r + 1) : ℝ) / (2 : ℝ) ^ (2 * r + 2) := by
      have hdbl_r : (2 : ℝ) * (Nat.choose (2 * r + 1) r : ℝ) =
          (Nat.choose (2 * r + 2) (r + 1) : ℝ) := by exact_mod_cast hdbl
      rw [← hdbl_r, pow_succ]
      field_simp
      ring
    have hsub : (Nat.choose (2 * r + 1) s : ℝ) / (2 : ℝ) ^ (2 * r + 1) ≤
        (Nat.choose (2 * r + 1) r : ℝ) / (2 : ℝ) ^ (2 * r + 1) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hmid) (by positivity)
    exact hsub.trans (heq ▸ hle1.trans hle2)

private lemma nat_succ_mul_three_quarters_le (q : ℕ) :
    ((q + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ q ≤ 2 := by
  induction q with
  | zero => norm_num
  | succ q ih =>
    rcases Nat.lt_or_ge q 2 with hq | hq
    · interval_cases q <;> norm_num
    · have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hstep : ((q + 2 : ℕ) : ℝ) * (3 / 4 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      calc ((q + 1 + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ (q + 1)
          = (((q + 2 : ℕ) : ℝ) * (3 / 4 : ℝ)) * (3 / 4 : ℝ) ^ q := by
            rw [pow_succ]; ring_nf
        _ ≤ ((q + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ q :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
        _ ≤ 2 := ih

private lemma bool_subset_card_sum {m : ℕ} (F : Finset (Fin m)) (s₀ : ℕ) :
    (∑ g : ({i : Fin m // i ∈ F} → Bool),
      if (Finset.univ.filter (fun i => g i = true)).card = s₀ then (1 : ℝ) else 0) =
    (Nat.choose F.card s₀ : ℝ) := by
  let S : Finset ({i : Fin m // i ∈ F} → Bool) :=
    Finset.univ.filter (fun g => (Finset.univ.filter (fun i => g i = true)).card = s₀)
  have h1 : (∑ g : ({i : Fin m // i ∈ F} → Bool),
      if (Finset.univ.filter (fun i => g i = true)).card = s₀ then (1 : ℝ) else 0) =
      (S.card : ℝ) := by
    rw [Finset.sum_boole]
  rw [h1]
  let e : ({i : Fin m // i ∈ F} → Bool) ≃ Finset {i : Fin m // i ∈ F} :=
    { toFun := fun g => Finset.univ.filter (fun i => g i = true)
      invFun := fun A i => decide (i ∈ A)
      left_inv := fun g => by ext i; simp
      right_inv := fun A => by ext i; simp }
  have hcard : S.card = ((Finset.univ : Finset (Finset {i : Fin m // i ∈ F})).filter
      (fun A => A.card = s₀)).card := by
    refine Finset.card_bij (fun g _ => e g) ?_ ?_ ?_
    · intro g hg
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      exact hg
    · intro g₁ _ g₂ _ h
      exact e.injective h
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
      refine ⟨e.symm A, ?_, e.apply_symm_apply A⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      change (e (e.symm A)).card = s₀
      rw [e.apply_symm_apply A]
      exact hA
  rw [hcard]
  have hpow : (Finset.univ : Finset (Finset {i : Fin m // i ∈ F})).filter (fun A => A.card = s₀) =
      Finset.univ.powersetCard s₀ := by
    ext A
    simp [Finset.mem_powersetCard]
  rw [hpow, Finset.card_powersetCard, Finset.card_univ, Fintype.card_coe]

private lemma bernoulli_point_le {m : ℕ} (hm : 1 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 1 / 16 ≤ p i ∧ p i ≤ 9 / 16) (t : ℕ) :
    (∑ f : Fin m → Bool,
      (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
      (∏ i : Fin m, if f i = true then p i else 1 - p i)) ≤
    12 / Real.sqrt (m : ℝ) := by
  let w₃ : Fin m → Fin 3 → ℝ := fun i c =>
    match c with
    | ⟨0, _⟩ => p i - 1 / 16
    | ⟨1, _⟩ => 15 / 16 - p i
    | ⟨2, _⟩ => 1 / 8
  let q₃ : Fin m → Fin 3 → Bool → ℝ := fun _ c b =>
    match c with
    | ⟨0, _⟩ => if b = true then 1 else 0
    | ⟨1, _⟩ => if b = false then 1 else 0
    | ⟨2, _⟩ => 1 / 2
  have hw_nonneg : ∀ i c, 0 ≤ w₃ i c := by
    intro i c
    have := hp i
    fin_cases c <;> simp only [w₃] <;> linarith
  have hw_sum : ∀ i, ∑ c : Fin 3, w₃ i c = 1 := by
    intro i
    simp [Fin.sum_univ_three, w₃]
    ring
  have hq_nonneg : ∀ i c b, 0 ≤ q₃ i c b := by
    intro i c b
    fin_cases c <;> cases b <;> simp [q₃]
  have hmix : ∀ i b, (if b = true then p i else 1 - p i) = ∑ c : Fin 3, w₃ i c * q₃ i c b := by
    intro i b
    cases b <;> simp [Fin.sum_univ_three, w₃, q₃] <;> ring
  have hexpand : ∀ f : Fin m → Bool,
      (∏ i : Fin m, if f i = true then p i else 1 - p i) =
      ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) * (∏ i : Fin m, q₃ i (c i) (f i)) := by
    intro f
    calc (∏ i : Fin m, if f i = true then p i else 1 - p i)
        = ∏ i : Fin m, ∑ c : Fin 3, w₃ i c * q₃ i c (f i) := by
          refine Finset.prod_congr rfl fun i _ => hmix i (f i)
      _ = ∑ c : Fin m → Fin 3, ∏ i : Fin m, (w₃ i (c i) * q₃ i (c i) (f i)) :=
          Fintype.prod_sum (fun i c => w₃ i c * q₃ i c (f i))
      _ = ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) * (∏ i : Fin m, q₃ i (c i) (f i)) := by
          refine Finset.sum_congr rfl fun c _ => Finset.prod_mul_distrib
  have hswap :
      (∑ f : Fin m → Bool,
        (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
        (∏ i : Fin m, if f i = true then p i else 1 - p i)) =
      ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) *
        (∑ f : Fin m → Bool,
          (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
          (∏ i : Fin m, q₃ i (c i) (f i))) := by
    simp_rw [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    refine Finset.sum_congr rfl fun f _ => by ring
  have hinner : ∀ c : Fin m → Fin 3,
      (∑ f : Fin m → Bool,
        (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
        (∏ i : Fin m, q₃ i (c i) (f i))) ≤
      1 / Real.sqrt (((Finset.univ.filter (fun i => c i = 2)).card + 1 : ℕ) : ℝ) := by
    intro c
    let F := Finset.univ.filter (fun i : Fin m => c i = 2)
    let eBool : (Fin m → Bool) ≃ ({i : Fin m // i ∈ F} → Bool) × ({i : Fin m // i ∉ F} → Bool) :=
      { toFun := fun f => (fun i => f i.1, fun i => f i.1)
        invFun := fun p i => if h : i ∈ F then p.1 ⟨i, h⟩ else p.2 ⟨i, h⟩
        left_inv := fun f => by ext i; by_cases h : i ∈ F <;> simp [h]
        right_inv := fun p => by ext i <;> simp [i.2] }
    have hsum_split :
        (∑ f : Fin m → Bool,
          (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
          (∏ i : Fin m, q₃ i (c i) (f i))) =
        ∑ f_out : ({i : Fin m // i ∉ F} → Bool),
          (∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) *
          (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
            (if (Finset.univ.filter (fun i => f_in i = true)).card +
                (Finset.univ.filter (fun i => f_out i = true)).card = t then (1 : ℝ) else 0) *
            (1 / 2 : ℝ) ^ F.card) := by
      rw [Fintype.sum_equiv eBool _ (fun p =>
          (if (Finset.univ.filter (fun i => (eBool.symm p) i = true)).card = t then (1 : ℝ) else 0) *
          (∏ i : Fin m, q₃ i (c i) ((eBool.symm p) i)))
        (fun f => by simp)]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun f_out _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f_in _ => ?_
      let g := eBool.symm (f_in, f_out)
      have hcard_g : (Finset.univ.filter (fun i => g i = true)).card =
          (Finset.univ.filter (fun i => f_in i = true)).card +
          (Finset.univ.filter (fun i => f_out i = true)).card := by
        have hpart : Finset.univ.filter (fun i => g i = true) =
            (Finset.univ.filter (fun i => f_in i = true)).map ⟨Subtype.val, Subtype.val_injective⟩ ∪
            (Finset.univ.filter (fun i => f_out i = true)).map ⟨Subtype.val, Subtype.val_injective⟩ := by
          ext i
          simp only [Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coeFn_mk, g, eBool]
          constructor
          · intro hg
            by_cases hi : i ∈ F
            · left; refine ⟨⟨i, hi⟩, ?_, rfl⟩; simpa [hi] using hg
            · right; refine ⟨⟨i, hi⟩, ?_, rfl⟩; simpa [hi] using hg
          · rintro (⟨⟨j, hj⟩, h1, rfl⟩ | ⟨⟨j, hj⟩, h1, rfl⟩)
            · simpa [hj] using h1
            · simpa [hj] using h1
        have hdisj : Disjoint
            ((Finset.univ.filter (fun i => f_in i = true)).map ⟨Subtype.val, Subtype.val_injective⟩)
            ((Finset.univ.filter (fun i => f_out i = true)).map ⟨Subtype.val, Subtype.val_injective⟩) := by
          rw [Finset.disjoint_left]
          rintro x hx1 hx2
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Function.Embedding.coeFn_mk] at hx1 hx2
          rcases hx1 with ⟨⟨j1, hj1⟩, _, rfl⟩
          rcases hx2 with ⟨⟨j2, hj2⟩, _, hjeq⟩
          dsimp only at hjeq
          exact hj2 (hjeq ▸ hj1)
        rw [hpart, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
      have hprod_g : (∏ i : Fin m, q₃ i (c i) (g i)) =
          (∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) * (1 / 2 : ℝ) ^ F.card := by
        have hpart : (∏ i : Fin m, q₃ i (c i) (g i)) =
            (∏ i ∈ F, q₃ i (c i) (g i)) * (∏ i ∈ Finset.univ \ F, q₃ i (c i) (g i)) := by
          rw [← Finset.prod_sdiff (Finset.subset_univ F)]
          ring
        rw [hpart]
        have hF : (∏ i ∈ F, q₃ i (c i) (g i)) = (1 / 2 : ℝ) ^ F.card := by
          calc ∏ i ∈ F, q₃ i (c i) (g i)
              = ∏ _ ∈ F, (1 / 2 : ℝ) := by
                refine Finset.prod_congr rfl fun i hi => ?_
                have hc2 : c i = 2 := (Finset.mem_filter.mp hi).2
                simp [hc2, q₃]
            _ = (1 / 2 : ℝ) ^ F.card := by rw [Finset.prod_const]
        have hFc : (∏ i ∈ Finset.univ \ F, q₃ i (c i) (g i)) =
            ∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i) := by
          rw [← Finset.prod_coe_sort (Finset.univ \ F)]
          refine Finset.prod_bij (fun i _ => ⟨i.1, (Finset.mem_sdiff.mp i.2).2⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b _ h; exact Subtype.ext (congr_arg (fun x : {i : Fin m // i ∉ F} => x.1) h)
          · intro j _
            refine ⟨⟨j.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, j.2⟩⟩, Finset.mem_univ _, rfl⟩
          · intro ⟨i, hi⟩ _
            have hni : i ∉ F := (Finset.mem_sdiff.mp hi).2
            simp [g, eBool, hni]
        rw [hF, hFc, mul_comm]
      rw [hcard_g, hprod_g]
      ring
    rw [hsum_split]
    have hinner_f : ∀ f_out : ({i : Fin m // i ∉ F} → Bool),
        (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
          (if (Finset.univ.filter (fun i => f_in i = true)).card +
              (Finset.univ.filter (fun i => f_out i = true)).card = t then (1 : ℝ) else 0) *
          (1 / 2 : ℝ) ^ F.card) ≤
        1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ) := by
      intro f_out
      set k_out := (Finset.univ.filter (fun i => f_out i = true)).card
      by_cases hkt : k_out ≤ t
      · have heq :
            (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
              (if (Finset.univ.filter (fun i => f_in i = true)).card + k_out = t then (1 : ℝ) else 0) *
              (1 / 2 : ℝ) ^ F.card) =
            (Nat.choose F.card (t - k_out) : ℝ) / (2 : ℝ) ^ F.card := by
          rw [← Finset.sum_mul]
          have hs : (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
              if (Finset.univ.filter (fun i => f_in i = true)).card + k_out = t then (1 : ℝ) else 0) =
              (Nat.choose F.card (t - k_out) : ℝ) := by
            rw [← bool_subset_card_sum F (t - k_out)]
            refine Finset.sum_congr rfl fun f_in _ => ?_
            split_ifs with h1 h2
            · rfl
            · exact absurd (by omega : (Finset.univ.filter (fun i => f_in i = true)).card = t - k_out) h2
            · exact absurd (by omega : (Finset.univ.filter (fun i => f_in i = true)).card + k_out = t) h1
            · rfl
          rw [hs, one_div, inv_pow, ← div_eq_mul_inv]
        rw [heq]
        exact choose_div_pow_le_inv_sqrt F.card (t - k_out)
      · have hzero :
            (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
              (if (Finset.univ.filter (fun i => f_in i = true)).card + k_out = t then (1 : ℝ) else 0) *
              (1 / 2 : ℝ) ^ F.card) = 0 := by
          refine Finset.sum_eq_zero fun f_in _ => ?_
          have : (Finset.univ.filter (fun i => f_in i = true)).card + k_out ≠ t := by omega
          rw [if_neg this, zero_mul]
        rw [hzero]
        positivity
    have hprod_out : (∑ f_out : ({i : Fin m // i ∉ F} → Bool),
        ∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) ≤ 1 := by
      rw [← Fintype.prod_sum (fun (i : {i : Fin m // i ∉ F}) (b : Bool) => q₃ i.1 (c i.1) b)]
      refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
      · exact Finset.sum_nonneg fun b _ => hq_nonneg i.1 (c i.1) b
      · have hni : c i.1 ≠ 2 := by
          intro hc2
          exact i.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc2⟩)
        have hlt3 : (c i.1).val < 3 := (c i.1).isLt
        have h012 : c i.1 = 0 ∨ c i.1 = 1 ∨ c i.1 = 2 := by
          rcases (by omega : (c i.1).val = 0 ∨ (c i.1).val = 1 ∨ (c i.1).val = 2) with h | h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Or.inl (Fin.ext h))
          · exact Or.inr (Or.inr (Fin.ext h))
        rcases h012 with h0 | h1 | h2
        · simp [h0, q₃]
        · simp [h1, q₃]
        · exact absurd h2 hni
    calc ∑ f_out : ({i : Fin m // i ∉ F} → Bool),
          (∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) *
          (∑ f_in : ({i : Fin m // i ∈ F} → Bool),
            (if (Finset.univ.filter (fun i => f_in i = true)).card +
                (Finset.univ.filter (fun i => f_out i = true)).card = t then (1 : ℝ) else 0) *
            (1 / 2 : ℝ) ^ F.card)
        ≤ ∑ f_out : ({i : Fin m // i ∉ F} → Bool),
          (∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) *
          (1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun f_out _ => ?_
          refine mul_le_mul_of_nonneg_left (hinner_f f_out) ?_
          exact Finset.prod_nonneg fun i _ => hq_nonneg i.1 (c i.1) (f_out i)
      _ = (∑ f_out : ({i : Fin m // i ∉ F} → Bool),
            ∏ i : {i : Fin m // i ∉ F}, q₃ i.1 (c i.1) (f_out i)) *
          (1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ)) := (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * (1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hprod_out (by positivity)
      _ = 1 / Real.sqrt ((F.card + 1 : ℕ) : ℝ) := one_mul _
  rw [hswap]
  set q : ℕ := m / 16
  let Rfn (c : Fin m → Fin 3) : ℕ := (Finset.univ.filter (fun i => c i = 2)).card
  have hpoint : ∀ c : Fin m → Fin 3,
      (1 / Real.sqrt ((Rfn c + 1 : ℕ) : ℝ)) ≤
      (1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) + (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ Rfn c := by
    intro c
    by_cases hR : q ≤ Rfn c
    · have h1 : 1 / Real.sqrt ((Rfn c + 1 : ℕ) : ℝ) ≤ 1 / Real.sqrt ((q + 1 : ℕ) : ℝ) := by
        refine one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) ?_
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.add_le_add_right hR 1)
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ Rfn c := by positivity
      linarith
    · have hRlt : Rfn c ≤ q := le_of_not_ge hR
      have h1 : 1 / Real.sqrt ((Rfn c + 1 : ℕ) : ℝ) ≤ 1 := by
        refine div_le_one_of_le₀ ?_ (by positivity)
        rw [Real.le_sqrt (by norm_num) (by positivity)]
        norm_num
      have h2 : 1 ≤ (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ Rfn c := by
        have hp : (2 : ℝ) ^ Rfn c ≤ (2 : ℝ) ^ q := pow_le_pow_right₀ (by norm_num) hRlt
        rw [one_div, inv_pow, ← div_eq_mul_inv, one_le_div (by positivity)]
        exact hp
      have h3 : (0 : ℝ) ≤ 1 / Real.sqrt ((q + 1 : ℕ) : ℝ) := by positivity
      linarith
  have hsum_w : (∑ c : Fin m → Fin 3, ∏ i : Fin m, w₃ i (c i)) = 1 := by
    rw [← Fintype.prod_sum (fun (i : Fin m) (x : Fin 3) => w₃ i x)]
    exact Finset.prod_eq_one fun i _ => hw_sum i
  have hsum_exp : (∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) * (1 / 2 : ℝ) ^ Rfn c) =
      (15 / 16 : ℝ) ^ m := by
    have hrw : ∀ c : Fin m → Fin 3,
        (∏ i : Fin m, w₃ i (c i)) * (1 / 2 : ℝ) ^ Rfn c =
        ∏ i : Fin m, w₃ i (c i) * (if c i = 2 then (1 / 2 : ℝ) else 1) := by
      intro c
      have hpow : (1 / 2 : ℝ) ^ Rfn c = ∏ i : Fin m, (if c i = 2 then (1 / 2 : ℝ) else 1) := by
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
      rw [hpow, Finset.prod_mul_distrib]
    simp_rw [hrw]
    rw [← Fintype.prod_sum (fun (i : Fin m) (x : Fin 3) => w₃ i x * (if x = 2 then (1 / 2 : ℝ) else 1))]
    calc ∏ i : Fin m, ∑ c : Fin 3, w₃ i c * (if c = 2 then (1 / 2 : ℝ) else 1)
        = ∏ _ : Fin m, (15 / 16 : ℝ) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          simp [Fin.sum_univ_three, w₃]
          ring
      _ = (15 / 16 : ℝ) ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hterm1 : 1 / Real.sqrt ((q + 1 : ℕ) : ℝ) ≤ 4 / Real.sqrt (m : ℝ) := by
    have hm_lt : m < 16 * (q + 1) := by omega
    have hsqrt_le : Real.sqrt (m : ℝ) ≤ 4 * Real.sqrt ((q + 1 : ℕ) : ℝ) := by
      have h1 : (m : ℝ) ≤ 16 * ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hm_lt.le
      calc Real.sqrt (m : ℝ)
          ≤ Real.sqrt (16 * ((q + 1 : ℕ) : ℝ)) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt 16 * Real.sqrt ((q + 1 : ℕ) : ℝ) := Real.sqrt_mul (by norm_num) _
        _ = 4 * Real.sqrt ((q + 1 : ℕ) : ℝ) := by
            have : Real.sqrt 16 = 4 := by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
            rw [this]
    rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr (by exact_mod_cast hm))]
    linarith
  have hterm2 : (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m ≤ 8 / Real.sqrt (m : ℝ) := by
    have h16q : 16 * q ≤ m := by omega
    have hpow : (15 / 16 : ℝ) ^ m ≤ (15 / 16 : ℝ) ^ (16 * q) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h16q
    have h215 : (2 : ℝ) * (15 / 16 : ℝ) ^ 16 ≤ 3 / 4 := by norm_num
    have hq_pow : (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m ≤ (3 / 4 : ℝ) ^ q := by
      calc (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m
          ≤ (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ (16 * q) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((2 : ℝ) * (15 / 16 : ℝ) ^ 16) ^ q := by rw [pow_mul, ← mul_pow]
        _ ≤ (3 / 4 : ℝ) ^ q := pow_le_pow_left₀ (by positivity) h215 q
    have hsqrt_le : Real.sqrt (m : ℝ) ≤ 4 * ((q + 1 : ℕ) : ℝ) := by
      have hm_lt : m < 16 * (q + 1) := by omega
      have h1 : (m : ℝ) ≤ 16 * ((q + 1 : ℕ) : ℝ) := by exact_mod_cast hm_lt.le
      have hq1 : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos q
      calc Real.sqrt (m : ℝ)
          ≤ Real.sqrt (16 * ((q + 1 : ℕ) : ℝ)) := Real.sqrt_le_sqrt h1
        _ = 4 * Real.sqrt ((q + 1 : ℕ) : ℝ) := by
            rw [Real.sqrt_mul (by norm_num), show Real.sqrt 16 = 4 by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        _ ≤ 4 * ((q + 1 : ℕ) : ℝ) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            rw [Real.sqrt_le_left (by positivity)]
            nlinarith
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast hm))]
    calc ((2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m) * Real.sqrt (m : ℝ)
        ≤ (3 / 4 : ℝ) ^ q * (4 * ((q + 1 : ℕ) : ℝ)) :=
          mul_le_mul hq_pow hsqrt_le (Real.sqrt_nonneg _) (by positivity)
      _ = 4 * (((q + 1 : ℕ) : ℝ) * (3 / 4 : ℝ) ^ q) := by ring
      _ ≤ 4 * 2 := mul_le_mul_of_nonneg_left (nat_succ_mul_three_quarters_le q) (by norm_num)
      _ = 8 := by norm_num
  calc ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) *
        (∑ f : Fin m → Bool,
          (if (Finset.univ.filter (fun i => f i = true)).card = t then (1 : ℝ) else 0) *
          (∏ i : Fin m, q₃ i (c i) (f i)))
      ≤ ∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) *
          ((1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) + (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ Rfn c) := by
        refine Finset.sum_le_sum fun c _ => ?_
        refine mul_le_mul_of_nonneg_left ((hinner c).trans (hpoint c)) ?_
        exact Finset.prod_nonneg fun i _ => hw_nonneg i (c i)
    _ = (∑ c : Fin m → Fin 3, ∏ i : Fin m, w₃ i (c i)) * (1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) +
          (2 : ℝ) ^ q * (∑ c : Fin m → Fin 3, (∏ i : Fin m, w₃ i (c i)) * (1 / 2 : ℝ) ^ Rfn c) := by
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => by ring
    _ = (1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) + (2 : ℝ) ^ q * (15 / 16 : ℝ) ^ m := by
        rw [hsum_w, one_mul, hsum_exp]
    _ ≤ 4 / Real.sqrt (m : ℝ) + 8 / Real.sqrt (m : ℝ) := add_le_add hterm1 hterm2
    _ = 12 / Real.sqrt (m : ℝ) := by ring

private lemma sum_graph_weight_eq_one (k : ℕ) (q : Fin k → Fin k → ℝ) :
    (∑ G : SimpleGraph (Fin k),
      ∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
        if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) = 1 := by
  let E := Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)
  let eGraph : SimpleGraph (Fin k) ≃ ({p : Fin k × Fin k // p ∈ E} → Bool) :=
    { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv
              simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu
              simpa [hvu, hn] using h⟩
          loopless := ⟨by intro u h; simp at h⟩ }
      left_inv := fun G => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu
          simp [hn, hvu, G.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp [huv] }
  let q' : {p : Fin k × Fin k // p ∈ E} → ℝ := fun e => q e.1.1 e.1.2
  have h1 :
      (∑ G : SimpleGraph (Fin k),
        ∏ e ∈ E, if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) =
      ∑ f : ({p : Fin k × Fin k // p ∈ E} → Bool),
        ∏ e : {p : Fin k × Fin k // p ∈ E}, if f e = true then q' e else 1 - q' e := by
    refine Fintype.sum_equiv eGraph _ _ fun G => ?_
    rw [← Finset.prod_coe_sort E]
    refine Finset.prod_congr rfl fun ⟨e, he⟩ _ => ?_
    simp [eGraph, q']
  rw [h1, ← Fintype.prod_sum (fun (e : {p : Fin k × Fin k // p ∈ E}) (b : Bool) =>
    if b = true then q' e else 1 - q' e)]
  refine Finset.prod_eq_one fun e _ => ?_
  simp

private lemma graph_target_le : ∀ (k : ℕ), 1 ≤ k → ∀ (q : Fin k → Fin k → ℝ),
    (∀ i j, 1 / 16 ≤ q i j ∧ q i j ≤ 9 / 16) → ∀ (target : Fin k → ℕ),
    (∑ G : SimpleGraph (Fin k),
      (if ∀ u : Fin k, (Finset.univ.filter (fun v => G.Adj u v)).card = target u then (1 : ℝ) else 0) *
      (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
        if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2))
    ≤ (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)
  | 0, hk, _, _, _ => by omega
  | 1, _, q, hq, target => by
    rw [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, Real.sqrt_one, div_one]
    calc (∑ G : SimpleGraph (Fin 1),
          (if ∀ u : Fin 1, (Finset.univ.filter (fun v => G.Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin 1 × Fin 1 => p.1 < p.2),
            if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2))
        ≤ ∑ G : SimpleGraph (Fin 1),
          (∏ e ∈ Finset.univ.filter (fun p : Fin 1 × Fin 1 => p.1 < p.2),
            if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := by
          refine Finset.sum_le_sum fun G _ => ?_
          have hw : 0 ≤ ∏ e ∈ Finset.univ.filter (fun p : Fin 1 × Fin 1 => p.1 < p.2),
              if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2 := by
            refine Finset.prod_nonneg fun e _ => ?_
            have := hq e.1 e.2
            split_ifs <;> linarith
          by_cases hcond : ∀ u : Fin 1, (Finset.univ.filter (fun v => G.Adj u v)).card = target u
          · rw [if_pos hcond, one_mul]
          · rw [if_neg hcond, zero_mul]
            exact hw
      _ = 1 := sum_graph_weight_eq_one 1 q
  | m + 2, _, q, hq, target => by
    let k := m + 1
    have hk1 : 1 ≤ k := by omega
    let eSplit : SimpleGraph (Fin (k + 1)) ≃ (Fin k → Bool) × SimpleGraph (Fin k) :=
      { toFun := fun G =>
          (fun i => decide (G.Adj 0 i.succ),
           { Adj := fun i j => G.Adj i.succ j.succ
             symm := ⟨fun _ _ h => (G.adj_comm _ _).mp h⟩
             loopless := ⟨fun _ h => G.loopless.irrefl _ h⟩ })
        invFun := fun p =>
          { Adj := fun u v =>
              if hu : u = 0 then
                if hv : v = 0 then False else p.1 (v.pred hv) = true
              else
                if hv : v = 0 then p.1 (u.pred hu) = true
                else p.2.Adj (u.pred hu) (v.pred hv)
            symm := ⟨by
              intro u v h
              by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp only [hu, hv, ↓reduceDIte] at h ⊢
              all_goals first | exact h | exact (p.2.adj_comm _ _).mp h⟩
            loopless := ⟨by
              intro u h
              by_cases hu : u = 0 <;> simp only [hu, ↓reduceDIte] at h
              · exact p.2.loopless.irrefl _ h⟩ }
        left_inv := fun G => by
          ext u v
          by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp only [hu, hv, ↓reduceDIte]
          · subst hu; simp
          · subst hu; simp [Fin.succ_pred]
          · subst hv; simp [Fin.succ_pred, G.adj_comm]
          · simp [Fin.succ_pred]
        right_inv := fun ⟨s, G'⟩ => by
          refine Prod.ext ?_ ?_
          · ext i; simp [Fin.succ_ne_zero]
          · ext i j; simp [Fin.succ_ne_zero] }
    let q_top : Fin k → ℝ := fun i => q 0 i.succ
    let q_sub : Fin k → Fin k → ℝ := fun i j => q i.succ j.succ
    have hq_top : ∀ i, 1 / 16 ≤ q_top i ∧ q_top i ≤ 9 / 16 := fun i => hq 0 i.succ
    have hq_sub : ∀ i j, 1 / 16 ≤ q_sub i j ∧ q_sub i j ≤ 9 / 16 := fun i j => hq i.succ j.succ
    have hprod_split : ∀ (s : Fin k → Bool) (G' : SimpleGraph (Fin k)),
        (∏ e ∈ Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2),
          if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) =
        (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i) *
        (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
          if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2) := by
      intro s G'
      let E := Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2)
      let E0 := E.filter (fun p => p.1 = 0)
      let E1 := E.filter (fun p => p.1 ≠ 0)
      have hpart : E = E0 ∪ E1 := by
        ext p; simp only [E0, E1, Finset.mem_union, Finset.mem_filter]; tauto
      have hdisj : Disjoint E0 E1 := by
        rw [Finset.disjoint_left]
        intro p hp0 hp1
        simp only [E0, E1, Finset.mem_filter] at hp0 hp1
        exact hp1.2 hp0.2
      change (∏ e ∈ E, if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) = _
      rw [hpart, Finset.prod_union hdisj]
      have hE0 : (∏ e ∈ E0, if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) =
          ∏ i : Fin k, if s i = true then q_top i else 1 - q_top i := by
        refine Finset.prod_bij (fun p hp => p.2.pred (by
          simp only [E0, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          intro h0
          rw [hp.2, h0] at hp
          exact lt_irrefl 0 hp.1)) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro p1 hp1 p2 hp2 h
          simp only [E0, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
          refine Prod.ext ?_ (Fin.pred_inj.mp h)
          rw [hp1.2, hp2.2]
        · intro i _
          refine ⟨(0, i.succ), ?_, by simp⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_pos i⟩, rfl⟩
        · intro p hp
          simp only [E0, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hp2 : p.2 ≠ 0 := by intro h0; rw [hp.2, h0] at hp; exact lt_irrefl 0 hp.1
          have hp1 : p.1 = 0 := hp.2
          simp only [eSplit, Equiv.coe_fn_symm_mk, hp1, hp2, ↓reduceDIte, q_top, Fin.succ_pred]
      have hE1 : (∏ e ∈ E1, if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) =
          ∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
            if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2 := by
        refine Finset.prod_bij (fun p hp => (p.1.pred (Finset.mem_filter.mp hp).2, p.2.pred (by
          simp only [E1, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          intro h0
          have : p.1 < 0 := h0 ▸ hp.1
          exact absurd this (Fin.not_lt_zero p.1)))) ?_ ?_ ?_ ?_
        · intro p hp
          simp only [E1, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          rw [← Fin.succ_lt_succ_iff, Fin.succ_pred, Fin.succ_pred]
          exact hp.1
        · intro p1 hp1 p2 hp2 h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (Fin.pred_inj.mp h.1) (Fin.pred_inj.mp h.2)
        · intro e he
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
          refine ⟨(e.1.succ, e.2.succ), ?_, by simp⟩
          simp only [E1, E, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨Fin.succ_lt_succ_iff.mpr he, Fin.succ_ne_zero e.1⟩
        · intro p hp
          simp only [E1, E, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          have hp2 : p.2 ≠ 0 := by intro h0; have : p.1 < 0 := h0 ▸ hp.1; exact absurd this (Fin.not_lt_zero p.1)
          simp only [eSplit, Equiv.coe_fn_symm_mk, hp.2, hp2, ↓reduceDIte, q_sub, Fin.succ_pred]
      rw [hE0, hE1]
    have hdeg_split : ∀ (s : Fin k → Bool) (G' : SimpleGraph (Fin k)),
        (∀ u : Fin (k + 1), (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u) →
        ((Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 ∧
         ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card =
           target i.succ - (if s i = true then 1 else 0)) := by
      intro s G' hG
      have heSplit_zero : ∀ v : Fin (k + 1),
          (eSplit.symm (s, G')).Adj 0 v = (if hv : v = 0 then False else s (v.pred hv) = true) := by
        intro v
        simp only [eSplit, Equiv.coe_fn_symm_mk, ↓reduceDIte]
      have heSplit_succ : ∀ (i : Fin k) (v : Fin (k + 1)),
          (eSplit.symm (s, G')).Adj i.succ v = (if hv : v = 0 then s i = true else G'.Adj i (v.pred hv)) := by
        intro i v
        simp only [eSplit, Equiv.coe_fn_symm_mk, Fin.succ_ne_zero, ↓reduceDIte, Fin.pred_succ]
      constructor
      · have h0 := hG 0
        have heq : (Finset.univ.filter (fun v : Fin (k + 1) => (eSplit.symm (s, G')).Adj 0 v)).card =
            (Finset.univ.filter (fun i : Fin k => s i = true)).card := by
          refine Finset.card_bij (fun v hv => v.pred (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, heSplit_zero] at hv
            intro h0'; simp [h0'] at hv)) ?_ ?_ ?_
          · intro v hv
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, heSplit_zero] at hv ⊢
            by_cases hv0 : v = 0
            · rw [dif_pos hv0] at hv; exact hv.elim
            · rw [dif_neg hv0] at hv; exact hv
          · intro v1 _ v2 _ h; exact Fin.pred_inj.mp h
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            refine ⟨i.succ, ?_, by simp⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, heSplit_zero,
              Fin.succ_ne_zero, ↓reduceDIte, Fin.pred_succ]
            exact hi
        omega
      · intro i
        have hi := hG i.succ
        let F := Finset.univ.filter (fun v : Fin (k + 1) => (eSplit.symm (s, G')).Adj i.succ v)
        let F' := Finset.univ.filter (fun j : Fin k => G'.Adj i j)
        have hF_split : F.card = F'.card + (if s i = true then 1 else 0) := by
          have hsub : (F.erase 0).card = F'.card := by
            refine Finset.card_bij (fun v hv => v.pred (Finset.mem_erase.mp hv).1) ?_ ?_ ?_
            · intro v hv
              have hv0 : v ≠ 0 := (Finset.mem_erase.mp hv).1
              have hvF := (Finset.mem_erase.mp hv).2
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, heSplit_succ,
                hv0, ↓reduceDIte] at hvF
              simp only [F', Finset.mem_filter, Finset.mem_univ, true_and]
              exact hvF
            · intro v1 _ v2 _ h; exact Fin.pred_inj.mp h
            · intro j hj
              simp only [F', Finset.mem_filter, Finset.mem_univ, true_and] at hj
              refine ⟨j.succ, ?_, by simp⟩
              rw [Finset.mem_erase]
              refine ⟨Fin.succ_ne_zero j, ?_⟩
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, heSplit_succ,
                Fin.succ_ne_zero, ↓reduceDIte, Fin.pred_succ]
              exact hj
          by_cases hsi : s i = true
          · have h0mem : (0 : Fin (k + 1)) ∈ F := by
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, heSplit_succ, ↓reduceDIte]
              exact hsi
            rw [← Finset.card_erase_add_one h0mem, hsub, if_pos hsi]
          · have h0not : (0 : Fin (k + 1)) ∉ F := by
              simp only [F, Finset.mem_filter, Finset.mem_univ, true_and, heSplit_succ, ↓reduceDIte]
              exact hsi
            rw [← Finset.erase_eq_of_notMem h0not, hsub, if_neg hsi, add_zero]
        have hF_eq : F.card = target i.succ := hi
        have hF'_eq : F'.card = (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card := rfl
        rw [hF_eq, hF'_eq] at hF_split
        omega
    have hw_nonneg_s : ∀ s : Fin k → Bool,
        0 ≤ ∏ i : Fin k, if s i = true then q_top i else 1 - q_top i := by
      intro s
      refine Finset.prod_nonneg fun i _ => ?_
      have := hq_top i
      split_ifs <;> linarith
    have hw_nonneg_G' : ∀ G' : SimpleGraph (Fin k),
        0 ≤ ∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
          if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2 := by
      intro G'
      refine Finset.prod_nonneg fun e _ => ?_
      have := hq_sub e.1 e.2
      split_ifs <;> linarith
    have hsplit_sum :
        (∑ G : SimpleGraph (Fin (m + 2)),
          (if ∀ u : Fin (m + 2), (Finset.univ.filter (fun v => G.Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin (m + 2) × Fin (m + 2) => p.1 < p.2),
            if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2)) =
        ∑ s : Fin k → Bool, ∑ G' : SimpleGraph (Fin k),
          (if ∀ u : Fin (k + 1), (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2),
            if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := by
      rw [← Fintype.sum_equiv eSplit.symm _ _ (fun _ => rfl), Fintype.sum_prod_type]
    have hstep1 :
        (∑ s : Fin k → Bool, ∑ G' : SimpleGraph (Fin k),
          (if ∀ u : Fin (k + 1), (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2),
            if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2)) ≤
        ∑ s : Fin k → Bool,
          (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
          (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i) *
          (∑ G' : SimpleGraph (Fin k),
            (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card =
                target i.succ - (if s i = true then 1 else 0) then (1 : ℝ) else 0) *
            (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
              if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2)) := by
      refine Finset.sum_le_sum fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun G' _ => ?_
      rw [hprod_split s G']
      have hwG' := hw_nonneg_G' G'
      have hws := hw_nonneg_s s
      by_cases hcond : ∀ u : Fin (k + 1),
          (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u
      · obtain ⟨hs0, hGi⟩ := hdeg_split s G' hcond
        rw [if_pos hcond, if_pos hs0, if_pos hGi]
        ring_nf
        exact le_rfl
      · rw [if_neg hcond, zero_mul]
        positivity
    have hIH : ∀ s : Fin k → Bool,
        (∑ G' : SimpleGraph (Fin k),
          (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card =
              target i.succ - (if s i = true then 1 else 0) then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
            if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2)) ≤
        (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ) :=
      fun s => graph_target_le k hk1 q_sub hq_sub (fun i => target i.succ - (if s i = true then 1 else 0))
    have houter : (∑ s : Fin k → Bool,
          (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
          (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i)) ≤
        12 / Real.sqrt (k : ℝ) :=
      bernoulli_point_le hk1 q_top hq_top (target 0)
    have hmul_eq : (12 / Real.sqrt (k : ℝ)) * ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) =
        (12 : ℝ) ^ (m + 2 - 1) / Real.sqrt (((m + 2 - 1).factorial : ℕ) : ℝ) := by
      have hk_eq : m + 2 - 1 = k := rfl
      have hkm : k = (k - 1) + 1 := by omega
      have hfact : (k.factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by
        have hnat : k.factorial = k * (k - 1).factorial := by
          conv_lhs => rw [hkm, Nat.factorial_succ, ← hkm]
        exact_mod_cast hnat
      have hsqrt_mul : Real.sqrt (k : ℝ) * Real.sqrt (((k - 1).factorial : ℕ) : ℝ) =
          Real.sqrt ((k.factorial : ℕ) : ℝ) := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg k), ← hfact]
      have hpow : (12 : ℝ) * (12 : ℝ) ^ (k - 1) = (12 : ℝ) ^ k := by
        conv_rhs => rw [hkm, pow_succ']
      rw [hk_eq, div_mul_div_comm, hpow, hsqrt_mul]
    calc (∑ G : SimpleGraph (Fin (m + 2)),
          (if ∀ u : Fin (m + 2), (Finset.univ.filter (fun v => G.Adj u v)).card = target u then (1 : ℝ) else 0) *
          (∏ e ∈ Finset.univ.filter (fun p : Fin (m + 2) × Fin (m + 2) => p.1 < p.2),
            if G.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2))
        = ∑ s : Fin k → Bool, ∑ G' : SimpleGraph (Fin k),
            (if ∀ u : Fin (k + 1), (Finset.univ.filter (fun v => (eSplit.symm (s, G')).Adj u v)).card = target u then (1 : ℝ) else 0) *
            (∏ e ∈ Finset.univ.filter (fun p : Fin (k + 1) × Fin (k + 1) => p.1 < p.2),
              if (eSplit.symm (s, G')).Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := hsplit_sum
      _ ≤ ∑ s : Fin k → Bool,
            (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
            (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i) *
            (∑ G' : SimpleGraph (Fin k),
              (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => G'.Adj i j)).card =
                  target i.succ - (if s i = true then 1 else 0) then (1 : ℝ) else 0) *
              (∏ e ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2),
                if G'.Adj e.1 e.2 then q_sub e.1 e.2 else 1 - q_sub e.1 e.2)) := hstep1
      _ ≤ ∑ s : Fin k → Bool,
            (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
            (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i) *
            ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun s _ => ?_
          refine mul_le_mul_of_nonneg_left (hIH s) ?_
          exact mul_nonneg (by split_ifs <;> norm_num) (hw_nonneg_s s)
      _ = (∑ s : Fin k → Bool,
            (if (Finset.univ.filter (fun i : Fin k => s i = true)).card = target 0 then (1 : ℝ) else 0) *
            (∏ i : Fin k, if s i = true then q_top i else 1 - q_top i)) *
            ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) := (Finset.sum_mul _ _ _).symm
      _ ≤ (12 / Real.sqrt (k : ℝ)) * ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right houter (by positivity)
      _ = (12 : ℝ) ^ (m + 2 - 1) / Real.sqrt (((m + 2 - 1).factorial : ℕ) : ℝ) := hmul_eq

end Helpers

theorem proof : OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1.H1 := by
  refine ⟨1000, by norm_num, fun n hn U hU => ?_⟩
  set k : ℕ := U.card
  have hk2 : 2 ≤ k := hU
  have hk1 : 1 ≤ k := by omega
  have hkn : k ≤ n := by
    simpa [k] using (U.card_le_univ.trans_eq (Fintype.card_fin n))
  let emb : Fin k ↪o Fin n := U.orderEmbOfFin rfl
  let p_edge : Fin n → Fin n → ℝ := fun u v =>
    (1 / 4 + (u : ℝ) / (2 * n)) * (1 / 4 + (v : ℝ) / (2 * n))
  have hp_bound : ∀ u v : Fin n, 1 / 16 ≤ p_edge u v ∧ p_edge u v ≤ 9 / 16 := by
    intro u v
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 (w : Fin n) : 1 / 4 ≤ 1 / 4 + (w : ℝ) / (2 * n) ∧ 1 / 4 + (w : ℝ) / (2 * n) ≤ 3 / 4 := by
      have hw0 : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
      have hw1 : (w : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr w.isLt.le
      constructor
      · have : 0 ≤ (w : ℝ) / (2 * (n : ℝ)) := by positivity
        linarith
      · have : (w : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
        linarith
    obtain ⟨hu0, hu1⟩ := h1 u
    obtain ⟨hv0, hv1⟩ := h1 v
    dsimp only [p_edge]
    exact ⟨by nlinarith, by nlinarith⟩
  let q : Fin k → Fin k → ℝ := fun i j => p_edge (emb i) (emb j)
  have hq_bound : ∀ i j, 1 / 16 ≤ q i j ∧ q i j ≤ 9 / 16 := fun i j => hp_bound (emb i) (emb j)
  let E_n := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let E_U := E_n.filter (fun p => p.1 ∈ U ∧ p.2 ∈ U)
  let E_out := E_n \ E_U
  let E_k := Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2)
  let eEdge : {p : Fin k × Fin k // p ∈ E_k} ≃ {p : Fin n × Fin n // p ∈ E_U} :=
    { toFun := fun p => ⟨(emb p.1.1, emb p.1.2), by
        have hp := (Finset.mem_filter.mp p.2).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, emb.lt_iff_lt.mpr hp⟩, ?_, ?_⟩
        · have : emb p.1.1 ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · have : emb p.1.2 ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this⟩
      invFun := fun p =>
        let hmem1 : p.1.1 ∈ Set.range emb := by
          rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp p.2).2.1
        let hmem2 : p.1.2 ∈ Set.range emb := by
          rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp p.2).2.2
        ⟨(Classical.choose hmem1, Classical.choose hmem2), by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [← emb.lt_iff_lt, Classical.choose_spec hmem1, Classical.choose_spec hmem2]
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp p.2).1).2⟩
      left_inv := fun ⟨⟨i, j⟩, _⟩ => by
        refine Subtype.ext (Prod.ext ?_ ?_) <;> dsimp only
        · exact emb.injective (Classical.choose_spec (show emb i ∈ Set.range emb from ⟨i, rfl⟩))
        · exact emb.injective (Classical.choose_spec (show emb j ∈ Set.range emb from ⟨j, rfl⟩))
      right_inv := fun ⟨⟨u, v⟩, hp⟩ => by
        refine Subtype.ext (Prod.ext ?_ ?_) <;> dsimp only
        · exact Classical.choose_spec (show u ∈ Set.range emb by
            rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hp).2.1)
        · exact Classical.choose_spec (show v ∈ Set.range emb by
            rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hp).2.2) }
  let eGraph_n : SimpleGraph (Fin n) ≃ ({p : Fin n × Fin n // p ∈ E_n} → Bool) :=
    { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv; simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu; simpa [hvu, hn] using h⟩
          loopless := ⟨by intro u h; simp at h⟩ }
      left_inv := fun G => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu; simp [hn, hvu, G.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp only [dif_pos huv]
        cases f ⟨(u, v), he⟩ <;> simp }
  let eGraph_k : SimpleGraph (Fin k) ≃ ({p : Fin k × Fin k // p ∈ E_k} → Bool) :=
    { toFun := fun H e => decide (H.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv; simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu; simpa [hvu, hn] using h⟩
          loopless := ⟨by intro u h; simp at h⟩ }
      left_inv := fun H => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu; simp [hn, hvu, H.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp only [dif_pos huv]
        cases f ⟨(u, v), he⟩ <;> simp }
  let eFnSplit : ({p : Fin n × Fin n // p ∈ E_n} → Bool) ≃
      ({p : Fin n × Fin n // p ∈ E_U} → Bool) × ({p : Fin n × Fin n // p ∈ E_out} → Bool) :=
    { toFun := fun f => (fun p => f ⟨p.1, (Finset.mem_filter.mp p.2).1⟩,
        fun p => f ⟨p.1, (Finset.mem_sdiff.mp p.2).1⟩)
      invFun := fun pr p =>
        if h : p.1 ∈ E_U then pr.1 ⟨p.1, h⟩
        else pr.2 ⟨p.1, Finset.mem_sdiff.mpr ⟨p.2, h⟩⟩
      left_inv := fun f => by ext p; by_cases h : p.1 ∈ E_U <;> simp [h]
      right_inv := fun pr => by
        ext p
        · simp [p.2]
        · have hn : p.1 ∉ E_U := (Finset.mem_sdiff.mp p.2).2
          simp [hn] }
  let eSplit : SimpleGraph (Fin n) ≃ SimpleGraph (Fin k) × ({p : Fin n × Fin n // p ∈ E_out} → Bool) :=
    eGraph_n.trans (eFnSplit.trans (Equiv.prodCongr (Equiv.arrowCongr eEdge.symm (Equiv.refl Bool) |>.trans eGraph_k.symm) (Equiv.refl _)))
  have heSplit_adj : ∀ (H : SimpleGraph (Fin k)) (f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool) (u v : Fin n),
      (eSplit.symm (H, f_out)).Adj u v =
        (if h : u < v then
          (if hu : (u, v) ∈ E_U then decide (H.Adj (eEdge.symm ⟨(u, v), hu⟩).1.1 (eEdge.symm ⟨(u, v), hu⟩).1.2)
           else f_out ⟨(u, v), Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hu⟩⟩) = true
         else if h' : v < u then
          (if hv : (v, u) ∈ E_U then decide (H.Adj (eEdge.symm ⟨(v, u), hv⟩).1.1 (eEdge.symm ⟨(v, u), hv⟩).1.2)
           else f_out ⟨(v, u), Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩, hv⟩⟩) = true
         else False) :=
    fun _ _ _ _ => rfl
  have hadj_eq : ∀ (H : SimpleGraph (Fin k)) (f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool)
      (i j : Fin k), (eSplit.symm (H, f_out)).Adj (emb i) (emb j) ↔ H.Adj i j := by
    intro H f_out i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hij' : emb i < emb j := emb.lt_iff_lt.mpr hij
      have hmem : (emb i, emb j) ∈ E_U := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij'⟩, ?_, ?_⟩
        · have : emb i ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · have : emb j ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
      have he1 : eEdge.symm ⟨(emb i, emb j), hmem⟩ = ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩ := by
        rw [Equiv.symm_apply_eq]; ext <;> rfl
      rw [heSplit_adj]
      simp [hij', hmem, he1]
    · simp
    · have hji' : emb j < emb i := emb.lt_iff_lt.mpr hji
      have hij' : ¬ emb i < emb j := lt_asymm hji'
      have hmem : (emb j, emb i) ∈ E_U := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji'⟩, ?_, ?_⟩
        · have : emb j ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
        · have : emb i ∈ Set.range emb := Set.mem_range_self _
          rwa [Finset.range_orderEmbOfFin] at this
      have he1 : eEdge.symm ⟨(emb j, emb i), hmem⟩ = ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩⟩ := by
        rw [Equiv.symm_apply_eq]; ext <;> rfl
      rw [heSplit_adj]
      simp [hij', hji', hmem, he1, H.adj_comm]
  have hdeg_iff : ∀ (H : SimpleGraph (Fin k)) (f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool),
      (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => (eSplit.symm (H, f_out)).Adj u v)).card = d) ↔
      (∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d) := by
    intro H f_out
    have hcard : ∀ i : Fin k,
        (U.filter (fun v => (eSplit.symm (H, f_out)).Adj (emb i) v)).card =
        (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card := by
      intro i
      refine Finset.card_bij (fun v hv =>
        let hmem : v ∈ Set.range emb := by
          rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hv).1
        Classical.choose hmem) ?_ ?_ ?_
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        have hmem : v ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hv.1
        have heq : emb (Classical.choose hmem) = v := Classical.choose_spec hmem
        rw [← heq] at hv
        exact (hadj_eq H f_out i _).mp hv.2
      · intro v1 hv1 v2 hv2 h
        have h1 : v1 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hv1).1
        have h2 : v2 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact (Finset.mem_filter.mp hv2).1
        have := congrArg emb h
        rwa [Classical.choose_spec h1, Classical.choose_spec h2] at this
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hU : emb j ∈ U := by
          have : emb j ∈ Set.range emb := Set.mem_range_self _; rwa [Finset.range_orderEmbOfFin] at this
        refine ⟨emb j, Finset.mem_filter.mpr ⟨hU, (hadj_eq H f_out i j).mpr hj⟩, ?_⟩
        exact emb.injective (Classical.choose_spec (show emb j ∈ Set.range emb by
          rw [Finset.range_orderEmbOfFin]; exact hU))
    constructor
    · rintro ⟨d, hd⟩
      have hd' : ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d := by
        intro i
        have hU : emb i ∈ U := by
          have : emb i ∈ Set.range emb := Set.mem_range_self _; rwa [Finset.range_orderEmbOfFin] at this
        rw [← hcard i]
        exact hd (emb i) hU
      have hdlt : d < k := by
        let i0 : Fin k := ⟨0, hk1⟩
        rw [← hd' i0]
        have hnot : i0 ∉ Finset.univ.filter (fun j : Fin k => H.Adj i0 j) := by
          simp
        have hss : Finset.univ.filter (fun j : Fin k => H.Adj i0 j) ⊂ Finset.univ :=
          Finset.ssubset_univ_iff.mpr (fun h => by rw [h] at hnot; exact hnot (Finset.mem_univ _))
        simpa using Finset.card_lt_card hss
      exact ⟨d, Finset.mem_range.mpr hdlt, hd'⟩
    · rintro ⟨d, _, hd⟩
      refine ⟨d, fun u hu => ?_⟩
      have hmem : u ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hu
      obtain ⟨i, rfl⟩ := hmem
      rw [hcard i]
      exact hd i
  have hw_split : ∀ (H : SimpleGraph (Fin k)) (f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool),
      (∏ e ∈ E_n,
        if (eSplit.symm (H, f_out)).Adj e.1 e.2
        then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
        else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))) =
      (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) *
      (∏ e : {p : Fin n × Fin n // p ∈ E_out},
        if f_out e = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2) := by
    intro H f_out
    have hpart : E_n = E_U ∪ E_out := (Finset.union_sdiff_of_subset (Finset.filter_subset _ _)).symm
    have hdisj : Disjoint E_U E_out :=
      Finset.disjoint_left.mpr fun _ hx1 hx2 => (Finset.mem_sdiff.mp hx2).2 hx1
    rw [hpart, Finset.prod_union hdisj]
    have hEU : (∏ e ∈ E_U, if (eSplit.symm (H, f_out)).Adj e.1 e.2 then p_edge e.1 e.2 else 1 - p_edge e.1 e.2) =
        ∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2 := by
      rw [← Finset.prod_coe_sort E_U, ← Finset.prod_coe_sort E_k]
      refine Fintype.prod_equiv eEdge.symm _ _ fun ⟨⟨u, v⟩, huv⟩ => ?_
      have huU : u ∈ U := (Finset.mem_filter.mp huv).2.1
      have hvU : v ∈ U := (Finset.mem_filter.mp huv).2.2
      have hmu : u ∈ Set.range emb := by rwa [Finset.range_orderEmbOfFin]
      have hmv : v ∈ Set.range emb := by rwa [Finset.range_orderEmbOfFin]
      obtain ⟨i, rfl⟩ := hmu
      obtain ⟨j, rfl⟩ := hmv
      have hadj : (eSplit.symm (H, f_out)).Adj (emb i) (emb j) ↔ H.Adj i j := hadj_eq H f_out i j
      have heij : (eEdge.symm ⟨(emb i, emb j), huv⟩).1 = (i, j) := by
        have : eEdge.symm ⟨(emb i, emb j), huv⟩ = ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            emb.lt_iff_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp huv).1).2⟩⟩ := by
          rw [Equiv.symm_apply_eq]; ext <;> rfl
        rw [this]
      have heij1 : (eEdge.symm ⟨(emb i, emb j), huv⟩).1.1 = i := congrArg Prod.fst heij
      have heij2 : (eEdge.symm ⟨(emb i, emb j), huv⟩).1.2 = j := congrArg Prod.snd heij
      rw [heij1, heij2]
      dsimp only [q]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (hadj.mp h1) h2
      · exact absurd (hadj.mpr h2) h1
      · rfl
    have hEout : (∏ e ∈ E_out, if (eSplit.symm (H, f_out)).Adj e.1 e.2 then p_edge e.1 e.2 else 1 - p_edge e.1 e.2) =
        ∏ e : {p : Fin n × Fin n // p ∈ E_out},
          if f_out e = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2 := by
      rw [← Finset.prod_coe_sort E_out]
      refine Finset.prod_congr rfl fun ⟨⟨u, v⟩, huv⟩ _ => ?_
      have huv_n : (u, v) ∈ E_n := (Finset.mem_sdiff.mp huv).1
      have hlt : u < v := (Finset.mem_filter.mp huv_n).2
      have hnotU : (u, v) ∉ E_U := (Finset.mem_sdiff.mp huv).2
      rw [heSplit_adj]
      simp [hlt, hnotU]
    rw [hEU, hEout]
  have hsum_out : (∑ f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool,
      ∏ e : {p : Fin n × Fin n // p ∈ E_out},
        if f_out e = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2) = 1 := by
    rw [← Fintype.prod_sum (fun (e : {p : Fin n × Fin n // p ∈ E_out}) (b : Bool) =>
      if b = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2)]
    refine Finset.prod_eq_one fun e _ => ?_
    rw [Fintype.sum_bool]
    simp
  have hreduce :
      (∑ G : SimpleGraph (Fin n),
        (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) *
        (∏ e ∈ E_n,
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n)))) =
      ∑ H : SimpleGraph (Fin k),
        (if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
          then (1 : ℝ) else 0) *
        (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := by
    rw [← Fintype.sum_equiv eSplit.symm _ _ (fun p => by rfl)]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun H _ => ?_
    have hrw : ∀ f_out : {p : Fin n × Fin n // p ∈ E_out} → Bool,
        (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => (eSplit.symm (H, f_out)).Adj u v)).card = d then (1 : ℝ) else 0) *
        (∏ e ∈ E_n,
          if (eSplit.symm (H, f_out)).Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))) =
        ((if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
            then (1 : ℝ) else 0) *
          (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2)) *
        (∏ e : {p : Fin n × Fin n // p ∈ E_out},
          if f_out e = true then p_edge e.1.1 e.1.2 else 1 - p_edge e.1.1 e.1.2) := by
      intro f_out
      have hite : (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => (eSplit.symm (H, f_out)).Adj u v)).card = d
            then (1 : ℝ) else 0) =
          if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
            then (1 : ℝ) else 0 := by
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd ((hdeg_iff H f_out).mp h1) h2
        · exact absurd ((hdeg_iff H f_out).mpr h2) h1
        · rfl
      rw [hite]
      change _ * (∏ e ∈ E_n, if (eSplit.symm (H, f_out)).Adj e.1 e.2 then p_edge e.1 e.2 else 1 - p_edge e.1 e.2) = _
      rw [hw_split H f_out]
      ring
    simp_rw [hrw, ← Finset.mul_sum, hsum_out, mul_one]
  have hw_k_nonneg : ∀ H : SimpleGraph (Fin k),
      0 ≤ ∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2 := by
    intro H
    refine Finset.prod_nonneg fun e _ => ?_
    have := hq_bound e.1 e.2
    split_ifs <;> linarith
  have hsum_d :
      (∑ H : SimpleGraph (Fin k),
        (if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
          then (1 : ℝ) else 0) *
        (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2)) ≤
      ∑ d ∈ Finset.range k, ∑ H : SimpleGraph (Fin k),
        (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d then (1 : ℝ) else 0) *
        (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun H _ => ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (hw_k_nonneg H)
    by_cases hH : ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
    · obtain ⟨d, hd, hdi⟩ := hH
      rw [if_pos ⟨d, hd, hdi⟩]
      refine le_trans ?_ (Finset.single_le_sum (fun d' _ => by split_ifs <;> norm_num) hd)
      rw [if_pos hdi]
    · rw [if_neg hH]
      exact Finset.sum_nonneg fun d' _ => by split_ifs <;> norm_num
  have hbound_k : (k : ℝ) * ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) ≤
      (n : ℝ) * (1000 / (k : ℝ)) ^ ((k : ℝ) / 2) := by
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hkn_real : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hfact_eq : Real.sqrt (((k - 1).factorial : ℕ) : ℝ) * Real.sqrt (k : ℝ) =
        Real.sqrt ((k.factorial : ℕ) : ℝ) := by
      have hkm : k = (k - 1) + 1 := by omega
      have hf : (k.factorial : ℝ) = ((k - 1).factorial : ℝ) * (k : ℝ) := by
        have hf_nat : k.factorial = (k - 1).factorial * k := by
          calc k.factorial = ((k - 1) + 1).factorial := by rw [← hkm]
            _ = (k - 1 + 1) * (k - 1).factorial := Nat.factorial_succ (k - 1)
            _ = (k - 1).factorial * k := by rw [← hkm, mul_comm]
        exact_mod_cast hf_nat
      rw [← Real.sqrt_mul (by positivity), ← hf]
    have hfact_lb := factorial_mul_exp_ge_pow k
    have hsqrt_fact : (k : ℝ) ^ ((k : ℝ) / 2) ≤ (Real.exp 1) ^ ((k : ℝ) / 2) * Real.sqrt ((k.factorial : ℕ) : ℝ) := by
      have hsq : ((k : ℝ) ^ ((k : ℝ) / 2)) ^ 2 ≤ ((Real.exp 1) ^ ((k : ℝ) / 2) * Real.sqrt ((k.factorial : ℕ) : ℝ)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
        have hp1 : ((k : ℝ) ^ ((k : ℝ) / 2)) ^ 2 = (k : ℝ) ^ k := by
          rw [← Real.rpow_natCast ((k : ℝ) ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul (Nat.cast_nonneg k),
            show ((k : ℝ) / 2) * ((2 : ℕ) : ℝ) = (k : ℝ) by push_cast; ring, Real.rpow_natCast]
        have hp2 : ((Real.exp 1) ^ ((k : ℝ) / 2)) ^ 2 = (Real.exp 1) ^ k := by
          rw [← Real.rpow_natCast ((Real.exp 1) ^ ((k : ℝ) / 2)) 2, ← Real.rpow_mul (Real.exp_pos 1).le,
            show ((k : ℝ) / 2) * ((2 : ℕ) : ℝ) = (k : ℝ) by push_cast; ring, Real.rpow_natCast]
        rw [hp1, hp2]
        exact hfact_lb
      by_contra! hgt
      have := mul_self_lt_mul_self (by positivity) hgt
      rw [← sq, ← sq] at this
      linarith
    have hsqrt_k_le : Real.sqrt (k : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) / 2) := by
      have hk_2k : k ≤ 2 ^ k := Nat.lt_pow_self (by decide : 1 < 2) |>.le
      have hk_2k_r : (k : ℝ) ≤ (2 : ℝ) ^ (k : ℝ) := by
        rw [Real.rpow_natCast]
        exact_mod_cast hk_2k
      have h1 : Real.sqrt (k : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ (k : ℝ)) := Real.sqrt_le_sqrt hk_2k_r
      have h2 : Real.sqrt ((2 : ℝ) ^ (k : ℝ)) = (2 : ℝ) ^ ((k : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
        congr 1; ring
      exact h1.trans_eq h2
    have h12_le : (12 : ℝ) ^ (k - 1) ≤ (144 : ℝ) ^ ((k : ℝ) / 2) := by
      have h1 : (12 : ℝ) ^ (k - 1) ≤ (12 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le k 1)
      have h2 : (12 : ℝ) ^ k = (144 : ℝ) ^ ((k : ℝ) / 2) := by
        rw [← Real.rpow_natCast 12 k]
        have : (12 : ℝ) ^ (k : ℝ) = ((12 : ℝ) ^ (2 : ℝ)) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
        rw [this]; norm_num
      exact h1.trans_eq h2
    have hmain_frac : (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ) ≤
        (1000 / (k : ℝ)) ^ ((k : ℝ) / 2) := by
      have hnum : (12 : ℝ) ^ (k - 1) * Real.sqrt (k : ℝ) ≤
          (144 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((k : ℝ) / 2) :=
        mul_le_mul h12_le hsqrt_k_le (by positivity) (by positivity)
      have hexp3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
      have h288 : 144 * 2 * Real.exp 1 ≤ 1000 := by linarith
      have hrpow_comb : (144 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((k : ℝ) / 2) * (Real.exp 1) ^ ((k : ℝ) / 2) ≤
          (1000 : ℝ) ^ ((k : ℝ) / 2) := by
        rw [← Real.mul_rpow (by positivity) (by positivity), ← Real.mul_rpow (by positivity) (Real.exp_pos 1).le]
        exact Real.rpow_le_rpow (by positivity) h288 (by positivity)
      have hlhs_eq : (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ) =
          ((12 : ℝ) ^ (k - 1) * Real.sqrt (k : ℝ)) / Real.sqrt ((k.factorial : ℕ) : ℝ) := by
        rw [← hfact_eq]
        have : Real.sqrt (k : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hk_pos).ne'
        field_simp [this]
      rw [hlhs_eq, Real.div_rpow (by norm_num) (Nat.cast_nonneg k)]
      rw [div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.rpow_pos_of_pos hk_pos _)]
      calc ((12 : ℝ) ^ (k - 1) * Real.sqrt (k : ℝ)) * (k : ℝ) ^ ((k : ℝ) / 2)
          ≤ ((144 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((k : ℝ) / 2)) *
              ((Real.exp 1) ^ ((k : ℝ) / 2) * Real.sqrt ((k.factorial : ℕ) : ℝ)) :=
            mul_le_mul hnum hsqrt_fact (by positivity) (by positivity)
        _ = ((144 : ℝ) ^ ((k : ℝ) / 2) * (2 : ℝ) ^ ((k : ℝ) / 2) * (Real.exp 1) ^ ((k : ℝ) / 2)) *
              Real.sqrt ((k.factorial : ℕ) : ℝ) := by ring
        _ ≤ (1000 : ℝ) ^ ((k : ℝ) / 2) * Real.sqrt ((k.factorial : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hrpow_comb (Real.sqrt_nonneg _)
    exact mul_le_mul hkn_real hmain_frac (by positivity) (Nat.cast_nonneg n)
  calc (∑ G : SimpleGraph (Fin n),
        (if ∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d then (1 : ℝ) else 0) *
        (∏ e ∈ E_n,
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))))
      = ∑ H : SimpleGraph (Fin k),
          (if ∃ d ∈ Finset.range k, ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d
            then (1 : ℝ) else 0) *
          (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := hreduce
    _ ≤ ∑ d ∈ Finset.range k, ∑ H : SimpleGraph (Fin k),
          (if ∀ i : Fin k, (Finset.univ.filter (fun j : Fin k => H.Adj i j)).card = d then (1 : ℝ) else 0) *
          (∏ e ∈ E_k, if H.Adj e.1 e.2 then q e.1 e.2 else 1 - q e.1 e.2) := hsum_d
    _ ≤ ∑ _ ∈ Finset.range k, (12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ) :=
        Finset.sum_le_sum fun d _ => graph_target_le k hk1 q hq_bound (fun _ => d)
    _ = (k : ℝ) * ((12 : ℝ) ^ (k - 1) / Real.sqrt (((k - 1).factorial : ℕ) : ℝ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ℝ) * (1000 / (k : ℝ)) ^ ((k : ℝ) / 2) := hbound_k

end E82H1

namespace E82H2
section Helpers

open scoped Classical

private lemma factorial_mul_exp_ge_pow (j : ℕ) :
    (j : ℝ) ^ j ≤ (Real.exp 1) ^ j * (j.factorial : ℝ) := by
  have hj_pos : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hsum : (j : ℝ) ^ j / (j.factorial : ℝ) ≤ Real.exp (j : ℝ) := by
    have h1 : (j : ℝ) ^ j / (j.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (j + 1), (j : ℝ) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => (j : ℝ) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self j))
    exact h1.trans (Real.sum_le_exp_of_nonneg (Nat.cast_nonneg j) (j + 1))
  have hexp : Real.exp (j : ℝ) = (Real.exp 1) ^ j := by
    rw [← mul_one (j : ℝ), Real.exp_nat_mul]
  rw [hexp, div_le_iff₀ hj_pos] at hsum
  exact hsum

private lemma choose_real_le {W j : ℕ} (hj : 1 ≤ j) :
    (Nat.choose W j : ℝ) ≤ (Real.exp 1 * (W : ℝ) / (j : ℝ)) ^ j := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have h1 : (Nat.choose W j : ℝ) * (j.factorial : ℝ) ≤ (W : ℝ) ^ j := by
    have hnat : Nat.choose W j * j.factorial ≤ W ^ j := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow W j
    exact_mod_cast hnat
  have h2 := factorial_mul_exp_ge_pow j
  have h3 : (Nat.choose W j : ℝ) * (j : ℝ) ^ j ≤ (Real.exp 1 * (W : ℝ)) ^ j := by
    calc (Nat.choose W j : ℝ) * (j : ℝ) ^ j
        ≤ (Nat.choose W j : ℝ) * ((Real.exp 1) ^ j * (j.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      _ = (Real.exp 1) ^ j * ((Nat.choose W j : ℝ) * (j.factorial : ℝ)) := by ring
      _ ≤ (Real.exp 1) ^ j * (W : ℝ) ^ j :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (Real.exp 1 * (W : ℝ)) ^ j := by rw [mul_pow]
  rw [div_pow, le_div_iff₀ (pow_pos hjpos j)]
  exact h3

private lemma card_leCard_le (n m : ℕ) (hn : 1 ≤ n) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun L => L.card ≤ m)).card ≤
      (m + 1) * n ^ m := by
  let S := (Finset.univ : Finset (Finset (Fin n))).filter (fun L => L.card ≤ m)
  let T := (Finset.range (m + 1)).biUnion (fun i => (Finset.univ : Finset (Fin n)).powersetCard i)
  have hsub : S ⊆ T := by
    intro L hL
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hL
    simp only [T, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨L.card, Nat.lt_succ_of_le hL, Finset.subset_univ _, rfl⟩
  have hcard : S.card ≤ T.card := Finset.card_le_card hsub
  have hT : T.card ≤ ∑ i ∈ Finset.range (m + 1), Nat.choose n i := by
    refine (Finset.card_biUnion_le).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hsum : ∑ i ∈ Finset.range (m + 1), Nat.choose n i ≤ (m + 1) * n ^ m := by
    calc ∑ i ∈ Finset.range (m + 1), Nat.choose n i
        ≤ ∑ _ ∈ Finset.range (m + 1), n ^ m := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          have hch : Nat.choose n i ≤ n ^ i := by
            have hf : 1 ≤ i.factorial := Nat.factorial_pos i
            calc Nat.choose n i
                ≤ Nat.choose n i * i.factorial := Nat.le_mul_of_pos_right _ hf
              _ = n.descFactorial i := by rw [mul_comm, Nat.descFactorial_eq_factorial_mul_choose]
              _ ≤ n ^ i := Nat.descFactorial_le_pow n i
          exact hch.trans (Nat.pow_le_pow_right hn (Nat.le_of_lt_succ hi))
      _ = (m + 1) * n ^ m := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  exact hcard.trans (hT.trans hsum)

private lemma pow_div_log_le_four_pow {n k : ℕ} (_hk : 1 ≤ k)
    (hsqrt : Real.sqrt (n : ℝ) ≤ (k : ℝ)) :
    n ^ (k / (Nat.log 2 k + 1)) ≤ 4 ^ k := by
  have hn_le_k2 : n ≤ k ^ 2 := by
    have hr : (n : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hsq := mul_self_le_mul_self (Real.sqrt_nonneg n) hsqrt
      rw [Real.mul_self_sqrt (Nat.cast_nonneg n), ← sq] at hsq
      exact hsq
    exact_mod_cast hr
  have hk_lt : k ≤ 2 ^ (Nat.log 2 k + 1) :=
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) k).le
  have hn_le_4 : n ≤ 4 ^ (Nat.log 2 k + 1) := by
    calc n ≤ k ^ 2 := hn_le_k2
      _ ≤ (2 ^ (Nat.log 2 k + 1)) ^ 2 := Nat.pow_le_pow_left hk_lt 2
      _ = (2 ^ 2) ^ (Nat.log 2 k + 1) := by rw [← pow_mul, mul_comm, pow_mul]
      _ = 4 ^ (Nat.log 2 k + 1) := by norm_num
  have hmul : (Nat.log 2 k + 1) * (k / (Nat.log 2 k + 1)) ≤ k :=
    Nat.mul_div_le k (Nat.log 2 k + 1)
  calc n ^ (k / (Nat.log 2 k + 1))
      ≤ (4 ^ (Nat.log 2 k + 1)) ^ (k / (Nat.log 2 k + 1)) :=
        Nat.pow_le_pow_left hn_le_4 _
    _ = 4 ^ ((Nat.log 2 k + 1) * (k / (Nat.log 2 k + 1))) := by rw [← pow_mul]
    _ ≤ 4 ^ k := Nat.pow_le_pow_right (by decide) hmul

private lemma card_mid_le (n : ℕ) (a : Fin n) (W : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun x => a ≤ x ∧ (x : ℕ) ≤ (a : ℕ) + W)).card ≤
      W + 1 := by
  let M := (Finset.univ : Finset (Fin n)).filter (fun x => a ≤ x ∧ (x : ℕ) ≤ (a : ℕ) + W)
  change M.card ≤ W + 1
  have h1 : M.card ≤ (Finset.range (W + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun x => (x : ℕ) - (a : ℕ)) ?_ ?_
    · intro x hx
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have ha : (a : ℕ) ≤ (x : ℕ) := hx'.1
      have hle : (x : ℕ) ≤ (a : ℕ) + W := hx'.2
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (by dsimp only; omega))
    · intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
      have hy' := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
      have ha1 : (a : ℕ) ≤ (x : ℕ) := hx'.1
      have ha2 : (a : ℕ) ≤ (y : ℕ) := hy'.1
      dsimp only at hxy
      exact Fin.ext (by omega)
  exact h1.trans (by simp [Finset.card_range])

end Helpers

theorem proof : OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1.H2 := by
  intro C₁ hC₁
  refine ⟨1 / (4096 * (C₁ + 1)), by positivity, ?_⟩
  set c₂ : ℝ := 1 / (4096 * (C₁ + 1))
  set α : ℝ := (1 / 2 : ℝ) * Real.log (4 / 3)
  have hα : 0 < α := by
    have : 0 < Real.log (4 / 3) := Real.log_pos (by norm_num)
    positivity
  set M_decay : ℝ := 16 * (Nat.factorial 15 : ℝ) / α ^ 15
  set B_req : ℝ := max (max (16 : ℝ) (1 / c₂)) M_decay
  have hB_pos : 0 < B_req := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (B_req ^ 2)
  refine ⟨max N₁ 2, fun n hn k hk_sqrt hk_le => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : 1 ≤ n := by omega
  have hnN₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hsqrt_gt_B : B_req < Real.sqrt (n : ℝ) := by
    have hn_gt_B2 : B_req ^ 2 < (n : ℝ) := lt_of_lt_of_le hN₁ (by exact_mod_cast hnN₁)
    have hsq := Real.sqrt_lt_sqrt (sq_nonneg B_req) hn_gt_B2
    rwa [Real.sqrt_sq hB_pos.le] at hsq
  have hk_gt_16 : (16 : ℝ) < (k : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) (lt_of_lt_of_le hsqrt_gt_B hk_sqrt)
  have hk16 : 16 ≤ k := by
    have : (16 : ℝ) ≤ (k : ℝ) := hk_gt_16.le
    exact_mod_cast this
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hk_gt_inv_c2 : 1 / c₂ < (k : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) (lt_of_lt_of_le hsqrt_gt_B hk_sqrt)
  have hc2_k32 : 1 ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) := by
    have hk_le_k32 : (k : ℝ) ≤ (k : ℝ) ^ (3 / 2 : ℝ) := by
      have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      calc (k : ℝ) = (k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (k : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk_ge1 (by norm_num)
    have h1 : 1 < c₂ * (k : ℝ) := by rwa [div_lt_iff₀ (by positivity : 0 < c₂), mul_comm] at hk_gt_inv_c2
    have h2 : c₂ * (k : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hk_le_k32 (by positivity)
    linarith
  set m : ℕ := k / (Nat.log 2 k + 1)
  have hm5 : 5 * m ≤ k := by
    have hlog : 4 ≤ Nat.log 2 k := by
      have h16 : Nat.log 2 16 = 4 := by decide
      exact h16 ▸ Nat.log_mono_right hk16
    have hmul : (Nat.log 2 k + 1) * m ≤ k := Nat.mul_div_le k (Nat.log 2 k + 1)
    have hle : 5 * m ≤ (Nat.log 2 k + 1) * m := Nat.mul_le_mul_right m (by omega)
    omega
  have hm_le_n : m ≤ n := by omega
  set W : ℕ := Nat.floor (c₂ * (k : ℝ) ^ (3 / 2 : ℝ))
  let LeCard := (Finset.univ : Finset (Finset (Fin n))).filter (fun L => L.card ≤ m)
  let Mid (a : Fin n) :=
    (Finset.univ : Finset (Fin n)).filter (fun x => a ≤ x ∧ (x : ℕ) ≤ (a : ℕ) + W)
  let Small := (Finset.univ : Finset (Finset (Fin n))).filter (fun U =>
    U.card = k ∧ ∃ a b : Fin n, a ≤ b ∧ (b : ℝ) - (a : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ∧
      (U.filter (· < a)).card ≤ m ∧ (U.filter (b < ·)).card ≤ m)
  let Pool := Finset.univ.sigma (fun a : Fin n =>
    LeCard ×ˢ LeCard ×ˢ ((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)))
  have hSmall_sub : Small ⊆ Pool.image (fun p => p.2.1 ∪ p.2.2.2 ∪ p.2.2.1) := by
    intro U hU
    simp only [Small, Finset.mem_filter, Finset.mem_univ, true_and] at hU
    rcases hU with ⟨hUk, a, b, hab, hspan, hLa, hRb⟩
    let L := U.filter (· < a)
    let R := U.filter (b < ·)
    let M := U.filter (fun x => a ≤ x ∧ x ≤ b)
    have hUeq : L ∪ M ∪ R = U := by
      ext x
      simp only [L, M, R, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
      · intro hx
        rcases lt_or_ge x a with hxa | hax
        · exact Or.inl (Or.inl ⟨hx, hxa⟩)
        · rcases le_or_gt x b with hxb | hbx
          · exact Or.inl (Or.inr ⟨hx, hax, hxb⟩)
          · exact Or.inr ⟨hx, hbx⟩
    have hdisjLM : Disjoint L M := by
      rw [Finset.disjoint_left]
      intro x hxL hxM
      simp only [L, M, Finset.mem_filter] at hxL hxM
      exact absurd hxL.2 (not_lt.mpr hxM.2.1)
    have hdisjLR : Disjoint L R := by
      rw [Finset.disjoint_left]
      intro x hxL hxR
      simp only [L, R, Finset.mem_filter] at hxL hxR
      have : x < b := lt_of_lt_of_le hxL.2 hab
      exact absurd hxR.2 (not_lt.mpr this.le)
    have hdisjMR : Disjoint M R := by
      rw [Finset.disjoint_left]
      intro x hxM hxR
      simp only [M, R, Finset.mem_filter] at hxM hxR
      exact absurd hxR.2 (not_lt.mpr hxM.2.2)
    have hdisjLMR : Disjoint (L ∪ M) R := Finset.disjoint_union_left.mpr ⟨hdisjLR, hdisjMR⟩
    have hcard_eq : L.card + M.card + R.card = k := by
      rw [← Finset.card_union_of_disjoint hdisjLM, ← Finset.card_union_of_disjoint hdisjLMR, hUeq, hUk]
    have hL_le : L.card ≤ m := hLa
    have hR_le : R.card ≤ m := hRb
    have hMcard : k - 2 * m ≤ M.card ∧ M.card ≤ k := by omega
    have hb_le_W : (b : ℕ) ≤ (a : ℕ) + W := by
      have hab_nat : (a : ℕ) ≤ (b : ℕ) := hab
      have hba_real : (((b : ℕ) - (a : ℕ) : ℕ) : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) := by
        rw [Nat.cast_sub hab_nat]
        exact hspan
      have hba_nat : (b : ℕ) - (a : ℕ) ≤ W := Nat.le_floor hba_real
      omega
    have hMsub : M ⊆ Mid a := by
      intro x hx
      simp only [M, Finset.mem_filter] at hx
      simp only [Mid, Finset.mem_filter, Finset.mem_univ, true_and]
      have hxb_nat : (x : ℕ) ≤ (b : ℕ) := hx.2.2
      exact ⟨hx.2.1, hxb_nat.trans hb_le_W⟩
    simp only [Finset.mem_image, Pool, Finset.mem_sigma, Finset.mem_univ, Finset.mem_product,
      Finset.mem_powerset, Finset.mem_filter, true_and]
    refine ⟨⟨a, L, R, M⟩, ⟨?_, ?_, hMsub, hMcard⟩, hUeq⟩
    · simp only [LeCard, Finset.mem_filter, Finset.mem_univ, true_and]; exact hLa
    · simp only [LeCard, Finset.mem_filter, Finset.mem_univ, true_and]; exact hRb
  have hLeCard : (LeCard.card : ℝ) ≤ ((n : ℝ) + 1) * (4 : ℝ) ^ k := by
    have h1 : LeCard.card ≤ (m + 1) * n ^ m := card_leCard_le n m hn1
    have h2 : n ^ m ≤ 4 ^ k := pow_div_log_le_four_pow hk1 hk_sqrt
    have h3 : (m + 1) * n ^ m ≤ (n + 1) * 4 ^ k :=
      Nat.mul_le_mul (Nat.add_le_add_right hm_le_n 1) h2
    exact_mod_cast h1.trans h3
  have hW_bound : ((W + 1 : ℕ) : ℝ) ≤ 2 * c₂ * (k : ℝ) ^ (3 / 2 : ℝ) := by
    have hf : (W : ℝ) ≤ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) := Nat.floor_le (by positivity)
    push_cast
    linarith
  have hexp3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hbase_le : 4 * Real.exp 1 * c₂ ≤ 1 := by
    have h1 : 4 * Real.exp 1 * c₂ = Real.exp 1 / (1024 * (C₁ + 1)) := by
      dsimp only [c₂]; field_simp; ring
    rw [h1, div_le_one (by positivity)]
    nlinarith
  have hchoose_bound : ∀ j ∈ Finset.Icc (k - 2 * m) k,
      (Nat.choose (W + 1) j : ℝ) ≤
        (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj_ge_half : (k : ℝ) / 2 ≤ (j : ℝ) := by
      have hnat : k ≤ 2 * j := by omega
      have : (k : ℝ) ≤ 2 * (j : ℝ) := by exact_mod_cast hnat
      linarith
    have hj1 : 1 ≤ j := by omega
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have h1 := choose_real_le (W := W + 1) hj1
    have hk32 : (k : ℝ) ^ (3 / 2 : ℝ) = (k : ℝ) * Real.sqrt (k : ℝ) := by
      have hsplit : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
      rw [hsplit, Real.rpow_add hkpos, Real.rpow_one, Real.sqrt_eq_rpow]
    have h2 : Real.exp 1 * ((W + 1 : ℕ) : ℝ) / (j : ℝ) ≤
        4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ) := by
      calc Real.exp 1 * ((W + 1 : ℕ) : ℝ) / (j : ℝ)
          ≤ Real.exp 1 * (2 * c₂ * (k : ℝ) ^ (3 / 2 : ℝ)) / ((k : ℝ) / 2) := by
            refine div_le_div₀ (by positivity) ?_ (by positivity) hj_ge_half
            exact mul_le_mul_of_nonneg_left hW_bound (Real.exp_pos 1).le
        _ = 4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ) := by
            rw [hk32]
            field_simp; ring
    have h3 : (Real.exp 1 * ((W + 1 : ℕ) : ℝ) / (j : ℝ)) ^ j ≤
        (4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ)) ^ j := by
      exact pow_le_pow_left₀ (by positivity) h2 j
    have h4 : (4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ)) ^ j =
        (4 * Real.exp 1 * c₂) ^ (j : ℝ) * (Real.sqrt (k : ℝ)) ^ (j : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (4 * Real.exp 1 * c₂) j, ← Real.rpow_natCast (Real.sqrt (k : ℝ)) j]
    have h5 : (4 * Real.exp 1 * c₂) ^ (j : ℝ) ≤ (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_ge (by positivity) hbase_le hj_ge_half
    have h6 : (Real.sqrt (k : ℝ)) ^ (j : ℝ) ≤ (k : ℝ) ^ ((k : ℝ) / 2) := by
      have hsq_ge1 : 1 ≤ Real.sqrt (k : ℝ) := by
        rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg k)]
        norm_num
        exact_mod_cast hk1
      have hj_le_k : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj.2
      calc (Real.sqrt (k : ℝ)) ^ (j : ℝ)
          ≤ (Real.sqrt (k : ℝ)) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hsq_ge1 hj_le_k
        _ = ((k : ℝ) ^ (1 / 2 : ℝ)) ^ (k : ℝ) := by rw [Real.sqrt_eq_rpow]
        _ = (k : ℝ) ^ ((k : ℝ) / 2) := by
            rw [← Real.rpow_mul (Nat.cast_nonneg k)]
            congr 1
            ring
    calc (Nat.choose (W + 1) j : ℝ)
        ≤ (Real.exp 1 * ((W + 1 : ℕ) : ℝ) / (j : ℝ)) ^ j := h1
      _ ≤ (4 * Real.exp 1 * c₂ * Real.sqrt (k : ℝ)) ^ j := h3
      _ = (4 * Real.exp 1 * c₂) ^ (j : ℝ) * (Real.sqrt (k : ℝ)) ^ (j : ℝ) := h4
      _ ≤ (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) :=
          mul_le_mul h5 h6 (by positivity) (by positivity)
  have hMid_bound : ∀ a : Fin n,
      (((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card : ℝ) ≤
        ((n : ℝ) + 1) * ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) := by
    intro a
    let F := (Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)
    let G := (Finset.Icc (k - 2 * m) k).biUnion (fun j => (Mid a).powersetCard j)
    have hFG : F ⊆ G := by
      intro M hM
      simp only [F, Finset.mem_filter, Finset.mem_powerset] at hM
      simp only [G, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard]
      exact ⟨M.card, hM.2, hM.1, rfl⟩
    have hcard_le : F.card ≤ ∑ j ∈ Finset.Icc (k - 2 * m) k, Nat.choose (W + 1) j := by
      refine (Finset.card_le_card hFG).trans ((Finset.card_biUnion_le).trans ?_)
      refine Finset.sum_le_sum fun j _ => ?_
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_choose j (card_mid_le n a W)
    have hIcc_le : ((Finset.Icc (k - 2 * m) k).card : ℝ) ≤ (n : ℝ) + 1 := by
      have : (Finset.Icc (k - 2 * m) k).card ≤ n + 1 := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast this
    calc (F.card : ℝ)
        ≤ ∑ j ∈ Finset.Icc (k - 2 * m) k, (Nat.choose (W + 1) j : ℝ) := by exact_mod_cast hcard_le
      _ ≤ ∑ _ ∈ Finset.Icc (k - 2 * m) k,
            ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) :=
          Finset.sum_le_sum hchoose_bound
      _ = ((Finset.Icc (k - 2 * m) k).card : ℝ) *
            ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) + 1) * ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hIcc_le (by positivity)
  have hPool_card : (Small.card : ℝ) ≤
      (n : ℝ) * ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
        (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
    have hc1 : Small.card ≤ Pool.card := (Finset.card_le_card hSmall_sub).trans Finset.card_image_le
    have hc2 : Pool.card = ∑ a : Fin n,
        LeCard.card * (LeCard.card * ((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card) := by
      simp only [Pool, Finset.card_sigma, Finset.card_product]
    have h16 : (16 : ℝ) ^ k = (256 : ℝ) ^ ((k : ℝ) / 2) := by
      calc (16 : ℝ) ^ k
          = (16 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast 16 k).symm
        _ = (16 : ℝ) ^ ((2 : ℝ) * ((k : ℝ) / 2)) := by congr 1; ring
        _ = ((16 : ℝ) ^ (2 : ℝ)) ^ ((k : ℝ) / 2) := Real.rpow_mul (by norm_num) 2 ((k : ℝ) / 2)
        _ = (256 : ℝ) ^ ((k : ℝ) / 2) := by norm_num
    have hterm : ∀ a : Fin n,
        (LeCard.card : ℝ) * ((LeCard.card : ℝ) *
          (((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card : ℝ)) ≤
        ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
          (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
      intro a
      calc (LeCard.card : ℝ) * ((LeCard.card : ℝ) *
            (((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card : ℝ))
          ≤ (((n : ℝ) + 1) * (4 : ℝ) ^ k) * ((((n : ℝ) + 1) * (4 : ℝ) ^ k) *
              (((n : ℝ) + 1) * ((4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)))) := by
            refine mul_le_mul hLeCard (mul_le_mul hLeCard (hMid_bound a) (by positivity) (by positivity))
              (by positivity) (by positivity)
        _ = ((n : ℝ) + 1) ^ 3 * ((4 : ℝ) ^ k * (4 : ℝ) ^ k) *
              (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by ring
        _ = ((n : ℝ) + 1) ^ 3 * (16 : ℝ) ^ k *
              (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
            have h44 : (4 : ℝ) ^ k * (4 : ℝ) ^ k = (16 : ℝ) ^ k := by
              rw [← mul_pow]; norm_num
            rw [h44]
        _ = ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
              (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by rw [h16]
    calc (Small.card : ℝ)
        ≤ (Pool.card : ℝ) := by exact_mod_cast hc1
      _ = ∑ a : Fin n, (LeCard.card : ℝ) * ((LeCard.card : ℝ) *
            (((Mid a).powerset.filter (fun M => k - 2 * m ≤ M.card ∧ M.card ≤ k)).card : ℝ)) := by
          rw [hc2]; push_cast; rfl
      _ ≤ ∑ _ : Fin n, (((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
            (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) :=
          Finset.sum_le_sum fun a _ => hterm a
      _ = (n : ℝ) * ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
            (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hprod_le : (Small.card : ℝ) * ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2)) ≤
      (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) := by
    have hdiv_rpow : (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2) =
        C₁ ^ ((k : ℝ) / 2) / (k : ℝ) ^ ((k : ℝ) / 2) :=
      Real.div_rpow hC₁.le (Nat.cast_nonneg k) _
    have hk_rpow_ne : (k : ℝ) ^ ((k : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hkpos _).ne'
    have hbase_34 : 256 * (4 * Real.exp 1 * c₂) * C₁ ≤ 3 / 4 := by
      have h1 : 256 * (4 * Real.exp 1 * c₂) * C₁ = Real.exp 1 / 4 * (C₁ / (C₁ + 1)) := by
        dsimp only [c₂]; field_simp; ring
      have h2 : C₁ / (C₁ + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
      rw [h1]
      calc Real.exp 1 / 4 * (C₁ / (C₁ + 1))
          ≤ Real.exp 1 / 4 * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ 3 / 4 := by linarith
    have hrpow_le : (256 : ℝ) ^ ((k : ℝ) / 2) * (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) *
        C₁ ^ ((k : ℝ) / 2) ≤ (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) := by
      have hmul1 : (256 : ℝ) ^ ((k : ℝ) / 2) * (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) *
          C₁ ^ ((k : ℝ) / 2) = (256 * (4 * Real.exp 1 * c₂) * C₁) ^ ((k : ℝ) / 2) := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          ← Real.mul_rpow (by positivity) hC₁.le]
      rw [hmul1]
      calc (256 * (4 * Real.exp 1 * c₂) * C₁) ^ ((k : ℝ) / 2)
          ≤ (3 / 4 : ℝ) ^ ((k : ℝ) / 2) :=
            Real.rpow_le_rpow (by positivity) hbase_34 (by positivity)
        _ ≤ (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    calc (Small.card : ℝ) * ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2))
        ≤ ((n : ℝ) * ((n : ℝ) + 1) ^ 3 * (256 : ℝ) ^ ((k : ℝ) / 2) *
            (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) * (k : ℝ) ^ ((k : ℝ) / 2)) *
            ((n : ℝ) * (C₁ / (k : ℝ)) ^ ((k : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hPool_card (by positivity)
      _ = (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 3 *
            ((256 : ℝ) ^ ((k : ℝ) / 2) * (4 * Real.exp 1 * c₂) ^ ((k : ℝ) / 2) *
              C₁ ^ ((k : ℝ) / 2)) := by
          rw [hdiv_rpow]
          field_simp [hk_rpow_ne]
      _ ≤ (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hrpow_le (by positivity)
  have hfinal : 2 * (n : ℝ) ^ 4 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2) < 1 := by
    set t : ℝ := Real.sqrt (n : ℝ)
    have ht_pos : 0 < t := lt_trans hB_pos hsqrt_gt_B
    have hM_lt_t : M_decay < t :=
      lt_of_le_of_lt (le_max_right _ _) hsqrt_gt_B
    have hn_eq : (n : ℝ) = t ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
    have hpoly : 2 * (n : ℝ) ^ 4 * ((n : ℝ) + 1) ^ 3 ≤ 16 * t ^ 14 := by
      have hn1_le : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        linarith
      calc 2 * (n : ℝ) ^ 4 * ((n : ℝ) + 1) ^ 3
          ≤ 2 * (n : ℝ) ^ 4 * (2 * (n : ℝ)) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hn1_le 3) (by positivity)
        _ = 16 * (n : ℝ) ^ 7 := by ring
        _ = 16 * t ^ 14 := by rw [hn_eq]; ring
    have hexp_inv : (3 / 4 : ℝ) ^ (t / 2) = (Real.exp (α * t))⁻¹ := by
      have h43 : (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ := by norm_num
      rw [h43, Real.inv_rpow (by norm_num), Real.rpow_def_of_pos (by norm_num)]
      congr 1
      dsimp only [α]
      ring
    have hexp_ge : (α * t) ^ 15 / (Nat.factorial 15 : ℝ) ≤ Real.exp (α * t) := by
      have h1 : (α * t) ^ 15 / (Nat.factorial 15 : ℝ) ≤
          ∑ i ∈ Finset.range 16, (α * t) ^ i / (i.factorial : ℝ) :=
        Finset.single_le_sum (f := fun i => (α * t) ^ i / (i.factorial : ℝ))
          (fun i _ => by positivity) (Finset.mem_range.mpr (by decide))
      exact h1.trans (Real.sum_le_exp_of_nonneg (by positivity) 16)
    have hdecay : (3 / 4 : ℝ) ^ (t / 2) ≤ (Nat.factorial 15 : ℝ) / (α * t) ^ 15 := by
      rw [hexp_inv, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
      have h := mul_le_mul_of_nonneg_left hexp_ge (by positivity : (0 : ℝ) ≤ (Nat.factorial 15 : ℝ))
      have hfact : (Nat.factorial 15 : ℝ) ≠ 0 := by positivity
      calc 1 * (α * t) ^ 15
          = (Nat.factorial 15 : ℝ) * ((α * t) ^ 15 / (Nat.factorial 15 : ℝ)) := by
            field_simp [hfact]
        _ ≤ (Nat.factorial 15 : ℝ) * Real.exp (α * t) := h
    calc 2 * (n : ℝ) ^ 4 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (t / 2)
        ≤ (16 * t ^ 14) * ((Nat.factorial 15 : ℝ) / (α * t) ^ 15) :=
          mul_le_mul hpoly hdecay (by positivity) (by positivity)
      _ = M_decay / t := by
          dsimp only [M_decay]
          field_simp [ht_pos.ne', hα.ne']
      _ < 1 := (div_lt_one ht_pos).mpr hM_lt_t
  have hgoal : ((n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 3 * (3 / 4 : ℝ) ^ (Real.sqrt (n : ℝ) / 2)) <
      1 / (2 * (n : ℝ) ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  exact lt_of_le_of_lt hprod_le hgoal

end E82H2

namespace E82H3
open scoped Classical

section Helpers

private lemma sum_pair_lt_eq_double (n : ℕ) (F : Fin n → Fin n → ℝ)
    (hdiag : ∀ u : Fin n, F u u = 0) :
    (∑ u : Fin n, ∑ v : Fin n, F u v) =
    ∑ e ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), (F e.1 e.2 + F e.2 e.1) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let Egt := Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)
  let Ediag := Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)
  have hpart : (Finset.univ : Finset (Fin n × Fin n)) = E ∪ Egt ∪ Ediag := by
    ext p
    simp only [E, Egt, Ediag, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases lt_trichotomy p.1 p.2 with h | h | h <;> tauto
  have hdisj1 : Disjoint E Egt := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [E, Egt, Finset.mem_filter] at h1 h2
    exact lt_asymm h1.2 h2.2
  have hdisj2 : Disjoint (E ∪ Egt) Ediag := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [E, Egt, Ediag, Finset.mem_union, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1
    · exact h1.2.ne h2.2
    · exact h1.2.ne h2.2.symm
  have hdouble : (∑ u : Fin n, ∑ v : Fin n, F u v) =
      ∑ p : Fin n × Fin n, F p.1 p.2 := (Fintype.sum_prod_type (fun p : Fin n × Fin n => F p.1 p.2)).symm
  rw [hdouble]
  calc ∑ p ∈ (Finset.univ : Finset (Fin n × Fin n)), F p.1 p.2
      = (∑ p ∈ E, F p.1 p.2) + (∑ p ∈ Egt, F p.1 p.2) + (∑ p ∈ Ediag, F p.1 p.2) := by
        rw [hpart, Finset.sum_union hdisj2, Finset.sum_union hdisj1]
    _ = (∑ p ∈ E, F p.1 p.2) + (∑ p ∈ E, F p.2 p.1) + 0 := by
        have hgt : ∑ p ∈ Egt, F p.1 p.2 = ∑ p ∈ E, F p.2 p.1 := by
          refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
          · intro p hp; simp only [E, Egt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
          · intro p1 _ p2 _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
          · intro p hp; refine ⟨(p.2, p.1), ?_, by ext <;> rfl⟩
            simp only [E, Egt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
          · intro _ _; rfl
        have hdg : ∑ p ∈ Ediag, F p.1 p.2 = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have heq : p.1 = p.2 := (Finset.mem_filter.mp hp).2
          rw [heq, hdiag]
        rw [hgt, hdg]
    _ = ∑ e ∈ E, (F e.1 e.2 + F e.2 e.1) := by rw [add_zero, Finset.sum_add_distrib]

private lemma chernoff_edge_sum (n : ℕ)
    (q : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)} → ℝ)
    (hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (coef : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)} → ℝ)
    (hcoef : ∀ e, |coef e| ≤ 2)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) (L : ℝ) :
    (∑ G : SimpleGraph (Fin n),
      (if (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
            coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤ L
        then (1 : ℝ) else 0) *
      (∏ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) ≤
    Real.exp (t * (L - ∑ e, coef e * q e) + t ^ 2 * ∑ e, (coef e) ^ 2) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let eGraph : SimpleGraph (Fin n) ≃ ({p : Fin n × Fin n // p ∈ E} → Bool) :=
    { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
      invFun := fun f =>
        { Adj := fun u v =>
            if h : u < v then f ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ = true
            else if h' : v < u then f ⟨(v, u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h'⟩⟩ = true
            else False
          symm := ⟨by
            intro u v h
            rcases lt_trichotomy u v with huv | rfl | hvu
            · have hn : ¬ v < u := lt_asymm huv; simpa [huv, hn] using h
            · simp at h
            · have hn : ¬ u < v := lt_asymm hvu; simpa [hvu, hn] using h⟩
          loopless := ⟨by intro u h; simp at h⟩ }
      left_inv := fun G => by
        ext u v
        rcases lt_trichotomy u v with huv | rfl | hvu
        · simp [huv]
        · simp
        · have hn : ¬ u < v := lt_asymm hvu; simp [hn, hvu, G.adj_comm]
      right_inv := fun f => by
        ext ⟨⟨u, v⟩, he⟩
        have huv : u < v := (Finset.mem_filter.mp he).2
        simp [huv] }
  have hw_nonneg : ∀ G : SimpleGraph (Fin n),
      0 ≤ ∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e := by
    intro G
    refine Finset.prod_nonneg fun e _ => ?_
    have := hq e
    split_ifs <;> linarith
  have hmarkov :
      (∑ G : SimpleGraph (Fin n),
        (if (∑ e : {p : Fin n × Fin n // p ∈ E}, coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤ L
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) ≤
      ∑ G : SimpleGraph (Fin n),
        Real.exp (t * (L - ∑ e : {p : Fin n × Fin n // p ∈ E},
          coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0))) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
    refine Finset.sum_le_sum fun G _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (hw_nonneg G)
    split_ifs with hle
    · exact Real.one_le_exp (mul_nonneg ht0 (sub_nonneg.mpr hle))
    · exact (Real.exp_pos _).le
  have hexp_prod :
      (∑ G : SimpleGraph (Fin n),
        Real.exp (t * (L - ∑ e : {p : Fin n × Fin n // p ∈ E},
          coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0))) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) =
      Real.exp (t * L) * ∏ e : {p : Fin n × Fin n // p ∈ E},
        ((1 - q e) + q e * Real.exp (-t * coef e)) := by
    have hrew : ∀ G : SimpleGraph (Fin n),
        Real.exp (t * (L - ∑ e : {p : Fin n × Fin n // p ∈ E},
          coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0))) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) =
        Real.exp (t * L) * ∏ e : {p : Fin n × Fin n // p ∈ E},
          (if G.Adj e.1.1 e.1.2 then q e * Real.exp (-t * coef e) else 1 - q e) := by
      intro G
      have harg : t * (L - ∑ e : {p : Fin n × Fin n // p ∈ E},
            coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) =
          t * L + ∑ e : {p : Fin n × Fin n // p ∈ E},
            (if G.Adj e.1.1 e.1.2 then -t * coef e else 0) := by
        rw [mul_sub, sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> ring
      rw [harg, Real.exp_add, Real.exp_sum, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun e _ => ?_
      split_ifs <;> simp [mul_comm]
    simp_rw [hrew, ← Finset.mul_sum]
    congr 1
    have hequiv :
        (∑ G : SimpleGraph (Fin n), ∏ e : {p : Fin n × Fin n // p ∈ E},
          if G.Adj e.1.1 e.1.2 then q e * Real.exp (-t * coef e) else 1 - q e) =
        ∑ f : ({p : Fin n × Fin n // p ∈ E} → Bool), ∏ e : {p : Fin n × Fin n // p ∈ E},
          if f e = true then q e * Real.exp (-t * coef e) else 1 - q e := by
      refine Fintype.sum_equiv eGraph _ _ fun G => ?_
      refine Finset.prod_congr rfl fun e _ => by simp [eGraph]
    rw [hequiv, ← Fintype.prod_sum (fun (e : {p : Fin n × Fin n // p ∈ E}) (b : Bool) =>
      if b = true then q e * Real.exp (-t * coef e) else 1 - q e)]
    refine Finset.prod_congr rfl fun e _ => ?_
    simp [add_comm]
  have hmgf : ∀ e : {p : Fin n × Fin n // p ∈ E},
      (1 - q e) + q e * Real.exp (-t * coef e) ≤
      Real.exp (q e * (-t * coef e) + (t * coef e) ^ 2) := by
    intro e
    set x : ℝ := -t * coef e
    have hx : |x| ≤ 1 := by
      rw [abs_mul, abs_neg, abs_of_nonneg ht0]
      nlinarith [hcoef e]
    have hexp : Real.exp x ≤ 1 + x + x ^ 2 := by
      have h := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
      linarith
    have hq0 : 0 ≤ q e := (hq e).1
    have hq1 : q e ≤ 1 := (hq e).2
    have hx2 : x ^ 2 = (t * coef e) ^ 2 := by dsimp only [x]; ring
    calc (1 - q e) + q e * Real.exp x
        ≤ (1 - q e) + q e * (1 + x + x ^ 2) := by gcongr
      _ = 1 + q e * x + q e * x ^ 2 := by ring
      _ ≤ 1 + q e * x + x ^ 2 := by gcongr; exact mul_le_of_le_one_left (sq_nonneg x) hq1
      _ = 1 + (q e * x + (t * coef e) ^ 2) := by rw [hx2]; ring
      _ ≤ Real.exp (q e * x + (t * coef e) ^ 2) := by
          linarith [Real.add_one_le_exp (q e * x + (t * coef e) ^ 2)]
  have hprod_le :
      (∏ e : {p : Fin n × Fin n // p ∈ E}, ((1 - q e) + q e * Real.exp (-t * coef e))) ≤
      Real.exp (-t * ∑ e, coef e * q e + t ^ 2 * ∑ e, (coef e) ^ 2) := by
    have hnonneg : ∀ e : {p : Fin n × Fin n // p ∈ E},
        0 ≤ (1 - q e) + q e * Real.exp (-t * coef e) := by
      intro e
      have := hq e
      have := Real.exp_pos (-t * coef e)
      nlinarith
    calc (∏ e : {p : Fin n × Fin n // p ∈ E}, ((1 - q e) + q e * Real.exp (-t * coef e)))
        ≤ ∏ e : {p : Fin n × Fin n // p ∈ E}, Real.exp (q e * (-t * coef e) + (t * coef e) ^ 2) :=
          Finset.prod_le_prod (fun e _ => hnonneg e) (fun e _ => hmgf e)
      _ = Real.exp (∑ e : {p : Fin n × Fin n // p ∈ E}, (q e * (-t * coef e) + (t * coef e) ^ 2)) :=
          (Real.exp_sum _ _).symm
      _ = Real.exp (-t * ∑ e, coef e * q e + t ^ 2 * ∑ e, (coef e) ^ 2) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> refine Finset.sum_congr rfl fun e _ => by ring
  calc (∑ G : SimpleGraph (Fin n),
        (if (∑ e : {p : Fin n × Fin n // p ∈ E}, coef e * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤ L
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e))
      ≤ Real.exp (t * L) * ∏ e : {p : Fin n × Fin n // p ∈ E},
          ((1 - q e) + q e * Real.exp (-t * coef e)) := hmarkov.trans_eq hexp_prod
    _ ≤ Real.exp (t * L) * Real.exp (-t * ∑ e, coef e * q e + t ^ 2 * ∑ e, (coef e) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod_le (Real.exp_pos _).le
    _ = Real.exp (t * (L - ∑ e, coef e * q e) + t ^ 2 * ∑ e, (coef e) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring

private lemma card_powersetCard_le_pow (n m : ℕ) (_hn : 1 ≤ n) :
    ((Finset.univ : Finset (Fin n)).powersetCard m).card ≤ n ^ m := by
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hf : 1 ≤ m.factorial := Nat.factorial_pos m
  calc Nat.choose n m
      ≤ Nat.choose n m * m.factorial := Nat.le_mul_of_pos_right _ hf
    _ = n.descFactorial m := by rw [mul_comm, Nat.descFactorial_eq_factorial_mul_choose]
    _ ≤ n ^ m := Nat.descFactorial_le_pow n m

private lemma log_div_log_two_le {n : ℕ} (hn : 3 ≤ n) :
    (Nat.log 2 n + 1 : ℝ) ≤ 3 * Real.log (n : ℝ) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by
    have hexp3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have : Real.exp 1 ≤ (n : ℝ) := le_trans hexp3.le (by exact_mod_cast hn)
    exact (Real.le_log_iff_exp_le (by positivity)).mpr this
  have hpow : (2 : ℝ) ^ (Nat.log 2 n : ℕ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog_pow : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h := Real.log_le_log (by positivity) hpow
    rwa [Real.log_pow] at h
  have hlog2 : 1 / 2 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have hexp4 : Real.exp 1 < 4 := Real.exp_one_lt_d9.trans (by norm_num)
    have hsq : (Real.exp (1 / 2)) ^ 2 < 2 ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
      exact hexp4
    by_contra! hle
    have := mul_self_le_mul_self (by norm_num) hle
    rw [← sq, ← sq] at this
    linarith
  have hnat_le : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    nlinarith
  linarith

private lemma log_cubed_le_n_twelfth (n : ℕ) (hn : 1 ≤ n) :
    (Real.log (n : ℝ)) ^ 3 ≤ 10368 * (n : ℝ) ^ (1 / 12 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hsum : ((1 / 12 : ℝ) * Real.log (n : ℝ)) ^ 3 / (Nat.factorial 3 : ℝ) ≤
      Real.exp ((1 / 12 : ℝ) * Real.log (n : ℝ)) := by
    have h1 : ((1 / 12 : ℝ) * Real.log (n : ℝ)) ^ 3 / (Nat.factorial 3 : ℝ) ≤
        ∑ i ∈ Finset.range 4, ((1 / 12 : ℝ) * Real.log (n : ℝ)) ^ i / (i.factorial : ℝ) :=
      Finset.single_le_sum (f := fun i => ((1 / 12 : ℝ) * Real.log (n : ℝ)) ^ i / (i.factorial : ℝ))
        (fun i _ => by positivity) (Finset.mem_range.mpr (by decide))
    exact h1.trans (Real.sum_le_exp_of_nonneg (by positivity) 4)
  have hexp : Real.exp ((1 / 12 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ (1 / 12 : ℝ) := by
    rw [Real.rpow_def_of_pos (by positivity), mul_comm]
  rw [hexp] at hsum
  have hfact3 : (Nat.factorial 3 : ℝ) = 6 := by norm_num
  rw [hfact3] at hsum
  linarith

private lemma ind_and (P Q : Prop) [Decidable (P ∧ Q)] [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1 : ℝ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  by_cases hP : P
  · by_cases hQ : Q
    · rw [if_pos ⟨hP, hQ⟩, if_pos hP, if_pos hQ, one_mul]
    · rw [if_neg (fun h => hQ h.2), if_pos hP, if_neg hQ, mul_zero]
  · rw [if_neg (fun h => hP h.1), if_neg hP, zero_mul]

private lemma ind_or_disj (P Q : Prop) [Decidable (P ∨ Q)] [Decidable P] [Decidable Q]
    (hPQ : ¬ (P ∧ Q)) :
    (if P ∨ Q then (1 : ℝ) else 0) = (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hP : P
  · have hQ : ¬ Q := fun h => hPQ ⟨hP, h⟩
    rw [if_pos (Or.inl hP), if_pos hP, if_neg hQ, add_zero]
  · by_cases hQ : Q
    · rw [if_pos (Or.inr hQ), if_neg hP, if_pos hQ, zero_add]
    · rw [if_neg (fun h => h.elim hP hQ), if_neg hP, if_neg hQ, add_zero]

private lemma sum_ite_mem_fin {n : ℕ} (X : Finset (Fin n))
    [DecidablePred (fun v : Fin n => v ∈ X)] :
    (∑ v : Fin n, if v ∈ X then (1 : ℝ) else 0) = (X.card : ℝ) := by
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun v : Fin n => v ∈ X) = X := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hf, Finset.sum_const, nsmul_eq_mul, mul_one]

private lemma sum_orderEmb {n m : ℕ} (X : Finset (Fin n)) (hX : X.card = m) (g : Fin n → ℝ) :
    ∑ x ∈ X, g x = ∑ i : Fin m, g (X.orderEmbOfFin hX i) := by
  let emb := X.orderEmbOfFin hX
  refine Finset.sum_bij (fun x hx =>
    let h : x ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx
    Classical.choose h) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro x1 hx1 x2 hx2 h
    have h1 : x1 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx1
    have h2 : x2 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx2
    have := congrArg emb h
    rwa [Classical.choose_spec h1, Classical.choose_spec h2] at this
  · intro i _
    have hi : emb i ∈ X := by
      have : emb i ∈ Set.range emb := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    refine ⟨emb i, hi, ?_⟩
    exact emb.injective (Classical.choose_spec (show emb i ∈ Set.range emb by
      rw [Finset.range_orderEmbOfFin]; exact hi))
  · intro x hx
    have h1 : x ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx
    rw [Classical.choose_spec h1]

private lemma sum_pairs_orderEmb {n m : ℕ} (X : Finset (Fin n)) (hX : X.card = m)
    (g : Fin n → ℝ) :
    (∑ x₁ ∈ X, ∑ x₂ ∈ X, if x₁ ≠ x₂ then g x₁ * g x₂ else 0) =
    ∑ i : Fin m, ∑ j : Fin m,
      if i ≠ j then g (X.orderEmbOfFin hX i) * g (X.orderEmbOfFin hX j) else 0 := by
  let emb := X.orderEmbOfFin hX
  refine Finset.sum_bij (fun x₁ hx₁ =>
    let h : x₁ ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx₁
    Classical.choose h) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro x1 hx1 x2 hx2 h
    have h1 : x1 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx1
    have h2 : x2 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx2
    have := congrArg emb h
    rwa [Classical.choose_spec h1, Classical.choose_spec h2] at this
  · intro i _
    have hi : emb i ∈ X := by
      have : emb i ∈ Set.range emb := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    refine ⟨emb i, hi, ?_⟩
    exact emb.injective (Classical.choose_spec (show emb i ∈ Set.range emb by
      rw [Finset.range_orderEmbOfFin]; exact hi))
  · intro x₁ hx₁
    have h1 : x₁ ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx₁
    have heq1 : emb (Classical.choose h1) = x₁ := Classical.choose_spec h1
    refine Finset.sum_bij (fun x₂ hx₂ =>
      let h : x₂ ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx₂
      Classical.choose h) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro y1 hy1 y2 hy2 h
      have h1' : y1 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hy1
      have h2' : y2 ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hy2
      have := congrArg emb h
      rwa [Classical.choose_spec h1', Classical.choose_spec h2'] at this
    · intro j _
      have hj : emb j ∈ X := by
        have : emb j ∈ Set.range emb := Set.mem_range_self _
        rwa [Finset.range_orderEmbOfFin] at this
      refine ⟨emb j, hj, ?_⟩
      exact emb.injective (Classical.choose_spec (show emb j ∈ Set.range emb by
        rw [Finset.range_orderEmbOfFin]; exact hj))
    · intro x₂ hx₂
      have h2 : x₂ ∈ Set.range emb := by rw [Finset.range_orderEmbOfFin]; exact hx₂
      have heq2 : emb (Classical.choose h2) = x₂ := Classical.choose_spec h2
      have hne : x₁ ≠ x₂ ↔ Classical.choose h1 ≠ Classical.choose h2 := by
        conv_lhs => rw [← heq1, ← heq2]
        exact emb.injective.ne_iff
      by_cases hc : Classical.choose h1 ≠ Classical.choose h2
      · have hx : x₁ ≠ x₂ := hne.mpr hc
        rw [if_pos hx, if_pos hc, heq1, heq2]
      · have hx : ¬ (x₁ ≠ x₂) := fun h => hc (hne.mp h)
        rw [if_neg hx, if_neg hc]

private lemma H3_coef1_sq_le {n m : ℕ} {A B S : Finset (Fin n)}
    (hAcard : A.card = m) (hBcard : B.card = m)
    (hSA : ∀ x, x ∈ S → x ∉ A) (hSB : ∀ x, x ∈ S → x ∉ B) (hAB : ∀ x, x ∈ A → x ∉ B) :
    ∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
      (((if (e.1.1 ∈ S ∧ e.1.2 ∈ B) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ B) then (1 : ℝ) else 0) -
        (if (e.1.1 ∈ S ∧ e.1.2 ∈ A) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ A) then 1 else 0)) ^ 2) ≤
    2 * (S.card : ℝ) * (m : ℝ) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let F_c : Fin n → Fin n → ℝ := fun u v => if u ∈ S ∧ (v ∈ A ∨ v ∈ B) then 1 else 0
  have hFc_nn : ∀ x y : Fin n, 0 ≤ F_c x y := fun x y => by
    dsimp only [F_c]
    by_cases h : x ∈ S ∧ (y ∈ A ∨ y ∈ B)
    · rw [if_pos h]; norm_num
    · rw [if_neg h]
  have h1 : ∑ e : {p : Fin n × Fin n // p ∈ E},
      (((if (e.1.1 ∈ S ∧ e.1.2 ∈ B) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ B) then (1 : ℝ) else 0) -
        (if (e.1.1 ∈ S ∧ e.1.2 ∈ A) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ A) then 1 else 0)) ^ 2) ≤
      ∑ e ∈ E, (F_c e.1 e.2 + F_c e.2 e.1) := by
    rw [Finset.sum_coe_sort E (fun p : Fin n × Fin n =>
      ((if (p.1 ∈ S ∧ p.2 ∈ B) ∨ (p.2 ∈ S ∧ p.1 ∈ B) then (1 : ℝ) else 0) -
        (if (p.1 ∈ S ∧ p.2 ∈ A) ∨ (p.2 ∈ S ∧ p.1 ∈ A) then 1 else 0)) ^ 2)]
    refine Finset.sum_le_sum fun ⟨u, v⟩ _ => ?_
    have hnn_uv := hFc_nn u v
    have hnn_vu := hFc_nn v u
    by_cases huS : u ∈ S
    · have huA : u ∉ A := hSA u huS
      have huB : u ∉ B := hSB u huS
      by_cases hvB : v ∈ B
      · have hvA : v ∉ A := fun h => hAB v h hvB
        have hB1 : (u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B) := Or.inl ⟨huS, hvB⟩
        have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
          fun h => h.elim (fun h1 => hvA h1.2) (fun h1 => huA h1.2)
        have hF1 : F_c u v = 1 := by dsimp only [F_c]; rw [if_pos ⟨huS, Or.inr hvB⟩]
        rw [if_pos hB1, if_neg hA0, hF1]; linarith
      · by_cases hvA : v ∈ A
        · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
            fun h => h.elim (fun h1 => hvB h1.2) (fun h1 => huB h1.2)
          have hA1 : (u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A) := Or.inl ⟨huS, hvA⟩
          have hF1 : F_c u v = 1 := by dsimp only [F_c]; rw [if_pos ⟨huS, Or.inl hvA⟩]
          rw [if_neg hB0, if_pos hA1, hF1]; norm_num at *; linarith
        · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
            fun h => h.elim (fun h1 => hvB h1.2) (fun h1 => huB h1.2)
          have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
            fun h => h.elim (fun h1 => hvA h1.2) (fun h1 => huA h1.2)
          rw [if_neg hB0, if_neg hA0]; linarith
    · by_cases hvS : v ∈ S
      · have hvA : v ∉ A := hSA v hvS
        have hvB : v ∉ B := hSB v hvS
        by_cases huB : u ∈ B
        · have huA : u ∉ A := fun h => hAB u h huB
          have hB1 : (u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B) := Or.inr ⟨hvS, huB⟩
          have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
            fun h => h.elim (fun h1 => hvA h1.2) (fun h1 => huA h1.2)
          have hF1 : F_c v u = 1 := by dsimp only [F_c]; rw [if_pos ⟨hvS, Or.inr huB⟩]
          rw [if_pos hB1, if_neg hA0, hF1]; linarith
        · by_cases huA : u ∈ A
          · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
              fun h => h.elim (fun h1 => hvB h1.2) (fun h1 => huB h1.2)
            have hA1 : (u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A) := Or.inr ⟨hvS, huA⟩
            have hF1 : F_c v u = 1 := by dsimp only [F_c]; rw [if_pos ⟨hvS, Or.inl huA⟩]
            rw [if_neg hB0, if_pos hA1, hF1]; norm_num at *; linarith
          · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
              fun h => h.elim (fun h1 => hvB h1.2) (fun h1 => huB h1.2)
            have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
              fun h => h.elim (fun h1 => hvA h1.2) (fun h1 => huA h1.2)
            rw [if_neg hB0, if_neg hA0]; linarith
      · have hB0 : ¬ ((u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B)) :=
          fun h => h.elim (fun h1 => huS h1.1) (fun h1 => hvS h1.1)
        have hA0 : ¬ ((u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A)) :=
          fun h => h.elim (fun h1 => huS h1.1) (fun h1 => hvS h1.1)
        rw [if_neg hB0, if_neg hA0]; linarith
  rw [← sum_pair_lt_eq_double n F_c (fun u => by
    dsimp only [F_c]
    rw [if_neg (fun ⟨hS, hABu⟩ => hABu.elim (fun hA => hSA u hS hA) (fun hB => hSB u hS hB))])] at h1
  have h2 : (∑ u : Fin n, ∑ v : Fin n, F_c u v) ≤ 2 * (S.card : ℝ) * (m : ℝ) := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun u _ hu =>
      Finset.sum_eq_zero fun v _ => by dsimp only [F_c]; rw [if_neg (fun h => hu h.1)])]
    calc ∑ u ∈ S, ∑ v : Fin n, F_c u v
        ≤ ∑ _ ∈ S, ((A.card : ℝ) + (B.card : ℝ)) := by
          refine Finset.sum_le_sum fun u _ => ?_
          calc ∑ v : Fin n, F_c u v
              ≤ ∑ v : Fin n, ((if v ∈ A then (1 : ℝ) else 0) + (if v ∈ B then (1 : ℝ) else 0)) := by
                refine Finset.sum_le_sum fun v _ => ?_
                dsimp only [F_c]
                by_cases hvA : v ∈ A
                · rw [if_pos hvA]
                  have ha : (if u ∈ S ∧ (v ∈ A ∨ v ∈ B) then (1 : ℝ) else 0) ≤ 1 := by
                    by_cases h : u ∈ S ∧ (v ∈ A ∨ v ∈ B)
                    · rw [if_pos h]
                    · rw [if_neg h]; norm_num
                  have hb : (0 : ℝ) ≤ if v ∈ B then 1 else 0 := by
                    by_cases h : v ∈ B
                    · rw [if_pos h]; norm_num
                    · rw [if_neg h]
                  linarith
                · rw [if_neg hvA, zero_add]
                  by_cases hvB : v ∈ B
                  · rw [if_pos hvB]
                    by_cases h : u ∈ S ∧ (v ∈ A ∨ v ∈ B)
                    · rw [if_pos h]
                    · rw [if_neg h]; norm_num
                  · have hnot : ¬ (u ∈ S ∧ (v ∈ A ∨ v ∈ B)) := fun ⟨_, h⟩ => h.elim hvA hvB
                    rw [if_neg hnot, if_neg hvB]
            _ = (∑ v : Fin n, if v ∈ A then (1 : ℝ) else 0) +
                  (∑ v : Fin n, if v ∈ B then (1 : ℝ) else 0) := Finset.sum_add_distrib
            _ = (A.card : ℝ) + (B.card : ℝ) := by
                rw [sum_ite_mem_fin A, sum_ite_mem_fin B]
      _ = (S.card : ℝ) * ((m : ℝ) + (m : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hAcard, hBcard]
      _ = 2 * (S.card : ℝ) * (m : ℝ) := by ring
  exact h1.trans h2

private lemma H3_coef2_sq_le {n m : ℕ} {A B : Finset (Fin n)}
    (hAcard : A.card = m) (hBcard : B.card = m) (hAB : ∀ x, x ∈ A → x ∉ B) :
    ∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
      (((if e.1.1 ∈ B ∧ e.1.2 ∈ B then (2 : ℝ) else 0) -
        (if e.1.1 ∈ A ∧ e.1.2 ∈ A then (2 : ℝ) else 0)) ^ 2) ≤
    4 * (m : ℝ) ^ 2 := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let F_c : Fin n → Fin n → ℝ := fun u v =>
    if (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) then 2 else 0
  have hFc_nn : ∀ x y : Fin n, 0 ≤ F_c x y := fun x y => by
    dsimp only [F_c]
    by_cases h : (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B)
    · rw [if_pos h]; norm_num
    · rw [if_neg h]
  have h1 : ∑ e : {p : Fin n × Fin n // p ∈ E},
      (((if e.1.1 ∈ B ∧ e.1.2 ∈ B then (2 : ℝ) else 0) -
        (if e.1.1 ∈ A ∧ e.1.2 ∈ A then (2 : ℝ) else 0)) ^ 2) ≤
      ∑ e ∈ E, (F_c e.1 e.2 + F_c e.2 e.1) := by
    rw [Finset.sum_coe_sort E (fun p : Fin n × Fin n =>
      ((if p.1 ∈ B ∧ p.2 ∈ B then (2 : ℝ) else 0) -
        (if p.1 ∈ A ∧ p.2 ∈ A then (2 : ℝ) else 0)) ^ 2)]
    refine Finset.sum_le_sum fun ⟨u, v⟩ _ => ?_
    by_cases hA : u ∈ A ∧ v ∈ A
    · have hB : ¬ (u ∈ B ∧ v ∈ B) := fun h => hAB u hA.1 h.1
      have hF1 : F_c u v = 2 := by dsimp only [F_c]; rw [if_pos (Or.inl hA)]
      have hF2 : F_c v u = 2 := by dsimp only [F_c]; rw [if_pos (Or.inl ⟨hA.2, hA.1⟩)]
      rw [if_neg hB, if_pos hA, hF1, hF2]; norm_num
    · by_cases hB : u ∈ B ∧ v ∈ B
      · have hF1 : F_c u v = 2 := by dsimp only [F_c]; rw [if_pos (Or.inr hB)]
        have hF2 : F_c v u = 2 := by dsimp only [F_c]; rw [if_pos (Or.inr ⟨hB.2, hB.1⟩)]
        rw [if_pos hB, if_neg hA, hF1, hF2]; norm_num
      · have h1 := hFc_nn u v
        have h2 := hFc_nn v u
        rw [if_neg hB, if_neg hA]; linarith
  have h2 : ∑ e ∈ E, (F_c e.1 e.2 + F_c e.2 e.1) ≤ ∑ u : Fin n, ∑ v : Fin n, F_c u v := by
    let F0 : Fin n → Fin n → ℝ := fun u v => if u = v then 0 else F_c u v
    have hlt : ∑ e ∈ E, (F_c e.1 e.2 + F_c e.2 e.1) = ∑ u : Fin n, ∑ v : Fin n, F0 u v := by
      rw [sum_pair_lt_eq_double n F0 (fun u => by dsimp only [F0]; rw [if_pos rfl])]
      refine Finset.sum_congr rfl fun e he => ?_
      have hne : e.1 ≠ e.2 := ((Finset.mem_filter.mp he).2).ne
      dsimp only [F0]
      rw [if_neg hne, if_neg hne.symm]
    rw [hlt]
    refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
    dsimp only [F0]
    by_cases huv : u = v
    · rw [if_pos huv]; exact hFc_nn u v
    · rw [if_neg huv]
  have h3 : (∑ u : Fin n, ∑ v : Fin n, F_c u v) = 4 * (m : ℝ) ^ 2 := by
    have hsplit : ∀ u v : Fin n, F_c u v =
        (if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0) + (if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0) := by
      intro u v
      dsimp only [F_c]
      by_cases hA : u ∈ A ∧ v ∈ A
      · have hB : ¬ (u ∈ B ∧ v ∈ B) := fun h => hAB u hA.1 h.1
        rw [if_pos (Or.inl hA), if_pos hA, if_neg hB, add_zero]
      · by_cases hB : u ∈ B ∧ v ∈ B
        · rw [if_pos (Or.inr hB), if_neg hA, if_pos hB, zero_add]
        · rw [if_neg (fun h => h.elim hA hB), if_neg hA, if_neg hB, add_zero]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hsA : (∑ u : Fin n, ∑ v : Fin n, if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0) =
        2 * (m : ℝ) ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ A) (fun u _ hu =>
        Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1)])]
      calc ∑ u ∈ A, ∑ v : Fin n, (if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0)
          = ∑ u ∈ A, ∑ _ ∈ A, (2 : ℝ) := by
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [← Finset.sum_subset (Finset.subset_univ A) (fun v _ hv => by rw [if_neg (fun h => hv h.2)])]
            refine Finset.sum_congr rfl fun v hv => by rw [if_pos ⟨hu, hv⟩]
        _ = 2 * (m : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hAcard]; ring
    have hsB : (∑ u : Fin n, ∑ v : Fin n, if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0) =
        2 * (m : ℝ) ^ 2 := by
      rw [← Finset.sum_subset (Finset.subset_univ B) (fun u _ hu =>
        Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1)])]
      calc ∑ u ∈ B, ∑ v : Fin n, (if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0)
          = ∑ u ∈ B, ∑ _ ∈ B, (2 : ℝ) := by
            refine Finset.sum_congr rfl fun u hu => ?_
            rw [← Finset.sum_subset (Finset.subset_univ B) (fun v _ hv => by rw [if_neg (fun h => hv h.2)])]
            refine Finset.sum_congr rfl fun v hv => by rw [if_pos ⟨hu, hv⟩]
        _ = 2 * (m : ℝ) ^ 2 := by
            rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hBcard]; ring
    rw [hsA, hsB]; ring
  exact h1.trans (h2.trans_eq h3)

private lemma H3_struct_pt {n k m : ℕ} {c₂ : ℝ} (hc₂ : 0 < c₂) (hn_pos : (0 : ℝ) < (n : ℝ))
    (hm5 : 5 * m ≤ k) (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) (hUk : U.card = k)
    (d : ℕ) (hd : ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d)
    (a b : Fin n) (hab : a < b) (hspan : c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ))
    (hUa : m ≤ (U.filter (· ≤ a)).card) (hUb : m ≤ (U.filter (b ≤ ·)).card) :
    (∃ p ∈ ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).filter
        (fun p : Finset (Fin n) × Finset (Fin n) × Finset (Fin n) =>
          Disjoint p.1 p.2.1 ∧ Disjoint p.2.2 (p.1 ∪ p.2.1) ∧
          ∀ u ∈ p.1, ∀ v ∈ p.2.1, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)),
      (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        ((if (e.1.1 ∈ p.2.2 ∧ e.1.2 ∈ p.2.1) ∨ (e.1.2 ∈ p.2.2 ∧ e.1.1 ∈ p.2.1) then (1 : ℝ) else 0) -
          (if (e.1.1 ∈ p.2.2 ∧ e.1.2 ∈ p.1) ∨ (e.1.2 ∈ p.2.2 ∧ e.1.1 ∈ p.1) then 1 else 0)) *
        (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤
        c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))) ∨
    (∃ p ∈ ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard m).filter
        (fun p : Finset (Fin n) × Finset (Fin n) => Disjoint p.1 p.2 ∧
          ∀ u ∈ p.1, ∀ v ∈ p.2, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)),
      (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        ((if e.1.1 ∈ p.2 ∧ e.1.2 ∈ p.2 then (2 : ℝ) else 0) -
          (if e.1.1 ∈ p.1 ∧ e.1.2 ∈ p.1 then (2 : ℝ) else 0)) *
        (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤
        -(c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ)))) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let coef₁ (A B S : Finset (Fin n)) (e : Fin n × Fin n) : ℝ :=
    (if (e.1 ∈ S ∧ e.2 ∈ B) ∨ (e.2 ∈ S ∧ e.1 ∈ B) then 1 else 0) -
    (if (e.1 ∈ S ∧ e.2 ∈ A) ∨ (e.2 ∈ S ∧ e.1 ∈ A) then 1 else 0)
  let coef₂ (A B : Finset (Fin n)) (e : Fin n × Fin n) : ℝ :=
    (if e.1 ∈ B ∧ e.2 ∈ B then (2 : ℝ) else 0) -
    (if e.1 ∈ A ∧ e.2 ∈ A then (2 : ℝ) else 0)
  let T₀ : ℝ := c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ))
  let BadTriples := ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).filter
      (fun p : Finset (Fin n) × Finset (Fin n) × Finset (Fin n) =>
        Disjoint p.1 p.2.1 ∧ Disjoint p.2.2 (p.1 ∪ p.2.1) ∧
        ∀ u ∈ p.1, ∀ v ∈ p.2.1, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ))
  let BadPairs := ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun p : Finset (Fin n) × Finset (Fin n) => Disjoint p.1 p.2 ∧
        ∀ u ∈ p.1, ∀ v ∈ p.2, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ))
  let Z1 (A B S : Finset (Fin n)) : ℝ :=
    ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ A B S e.1 * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)
  let Z2 (A B : Finset (Fin n)) : ℝ :=
    ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ A B e.1 * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hUa
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hUb
  let S := U \ (A ∪ B)
  have hAU : A ⊆ U := hAsub.trans (Finset.filter_subset _ _)
  have hBU : B ⊆ U := hBsub.trans (Finset.filter_subset _ _)
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hxa : x ≤ a := (Finset.mem_filter.mp (hAsub hxA)).2
    have hbx : b ≤ x := (Finset.mem_filter.mp (hBsub hxB)).2
    exact absurd (le_trans hbx hxa) (not_le_of_gt hab)
  have hdisjS : Disjoint S (A ∪ B) := Finset.sdiff_disjoint
  have hABU : A ∪ B ⊆ U := Finset.union_subset hAU hBU
  have hScard : S.card = k - 2 * m := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hABU, Finset.card_union_of_disjoint hdisjAB, hUk, hAcard, hBcard]
    omega
  have hgap : ∀ u ∈ A, ∀ v ∈ B, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ) := by
    intro u hu v hv
    have hua : ((u : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_filter.mp (hAsub hu)).2
    have hbv : ((b : ℕ) : ℝ) ≤ ((v : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_filter.mp (hBsub hv)).2
    linarith
  have hsum_zero : Z1 A B S + Z2 A B = 0 := by
    have hdeg_diff :
        (∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ)) -
        (∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ)) = 0 := by
      have hB_eq : ∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ) = (m : ℝ) * (d : ℝ) := by
        calc ∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ)
            = ∑ _ ∈ B, (d : ℝ) := Finset.sum_congr rfl fun v hv => by exact_mod_cast hd v (hBU hv)
          _ = (B.card : ℝ) * (d : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = (m : ℝ) * (d : ℝ) := by rw [hBcard]
      have hA_eq : ∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ) = (m : ℝ) * (d : ℝ) := by
        calc ∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ)
            = ∑ _ ∈ A, (d : ℝ) := Finset.sum_congr rfl fun u hu => by exact_mod_cast hd u (hAU hu)
          _ = (A.card : ℝ) * (d : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ = (m : ℝ) * (d : ℝ) := by rw [hAcard]
      linarith
    let F : Fin n → Fin n → ℝ := fun u v =>
      ((if u ∈ B ∧ v ∈ U then (1 : ℝ) else 0) - (if u ∈ A ∧ v ∈ U then 1 else 0)) *
      (if G.Adj u v then 1 else 0)
    have hF_sum : (∑ u : Fin n, ∑ v : Fin n, F u v) =
        (∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ)) -
        (∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ)) := by
      have h1 : (∑ u : Fin n, ∑ v : Fin n,
          (if u ∈ B ∧ v ∈ U then (1 : ℝ) else 0) * (if G.Adj u v then 1 else 0)) =
          ∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ) := by
        calc (∑ u : Fin n, ∑ v : Fin n,
              (if u ∈ B ∧ v ∈ U then (1 : ℝ) else 0) * (if G.Adj u v then 1 else 0))
            = ∑ v ∈ B, ∑ w ∈ U, (if G.Adj v w then (1 : ℝ) else 0) := by
              rw [← Finset.sum_subset (Finset.subset_univ B) (fun u _ hu =>
                Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1), zero_mul])]
              refine Finset.sum_congr rfl fun v hv => ?_
              rw [← Finset.sum_subset (Finset.subset_univ U) (fun w _ hw => by
                rw [if_neg (fun h => hw h.2), zero_mul])]
              refine Finset.sum_congr rfl fun w hw => by rw [if_pos ⟨hv, hw⟩, one_mul]
          _ = ∑ v ∈ B, ((U.filter (fun w => G.Adj v w)).card : ℝ) := by
              refine Finset.sum_congr rfl fun v _ => ?_
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have h2 : (∑ u : Fin n, ∑ v : Fin n,
          (if u ∈ A ∧ v ∈ U then (1 : ℝ) else 0) * (if G.Adj u v then 1 else 0)) =
          ∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ) := by
        calc (∑ u : Fin n, ∑ v : Fin n,
              (if u ∈ A ∧ v ∈ U then (1 : ℝ) else 0) * (if G.Adj u v then 1 else 0))
            = ∑ u ∈ A, ∑ w ∈ U, (if G.Adj u w then (1 : ℝ) else 0) := by
              rw [← Finset.sum_subset (Finset.subset_univ A) (fun u _ hu =>
                Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1), zero_mul])]
              refine Finset.sum_congr rfl fun u hu => ?_
              rw [← Finset.sum_subset (Finset.subset_univ U) (fun w _ hw => by
                rw [if_neg (fun h => hw h.2), zero_mul])]
              refine Finset.sum_congr rfl fun w hw => by rw [if_pos ⟨hu, hw⟩, one_mul]
          _ = ∑ u ∈ A, ((U.filter (fun w => G.Adj u w)).card : ℝ) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      simp_rw [F, sub_mul, Finset.sum_sub_distrib]
      rw [h1, h2]
    have hF_diag : ∀ u : Fin n, F u u = 0 := fun u => by
      dsimp only [F]; rw [if_neg (G.loopless.irrefl u), mul_zero]
    have hpair := sum_pair_lt_eq_double n F hF_diag
    have hZ_eq : (∑ e ∈ E, (F e.1 e.2 + F e.2 e.1)) = Z1 A B S + Z2 A B := by
      dsimp only [Z1, Z2]
      rw [← Finset.sum_coe_sort E, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ⟨⟨u, v⟩, _⟩ _ => ?_
      have hSA : ∀ x, ¬ (x ∈ S ∧ x ∈ A) := fun x ⟨hxS, hxA⟩ =>
        (Finset.disjoint_left.mp hdisjS hxS) (Finset.mem_union_left B hxA)
      have hSB : ∀ x, ¬ (x ∈ S ∧ x ∈ B) := fun x ⟨hxS, hxB⟩ =>
        (Finset.disjoint_left.mp hdisjS hxS) (Finset.mem_union_right A hxB)
      have hAB_n : ∀ x, ¬ (x ∈ A ∧ x ∈ B) := fun x ⟨hxA, hxB⟩ =>
        Finset.disjoint_left.mp hdisjAB hxA hxB
      have hU_ind : ∀ x : Fin n,
          (if x ∈ U then (1 : ℝ) else 0) =
            (if x ∈ A then 1 else 0) + (if x ∈ B then 1 else 0) + (if x ∈ S then 1 else 0) := by
        intro x
        by_cases hxA : x ∈ A
        · have hxU : x ∈ U := hAU hxA
          have hxB : x ∉ B := fun h => hAB_n x ⟨hxA, h⟩
          have hxS : x ∉ S := fun h => hSA x ⟨h, hxA⟩
          rw [if_pos hxU, if_pos hxA, if_neg hxB, if_neg hxS]; ring
        · by_cases hxB : x ∈ B
          · have hxU : x ∈ U := hBU hxB
            have hxS : x ∉ S := fun h => hSB x ⟨h, hxB⟩
            rw [if_pos hxU, if_neg hxA, if_pos hxB, if_neg hxS]; ring
          · by_cases hxU : x ∈ U
            · have hxS : x ∈ S := Finset.mem_sdiff.mpr ⟨hxU, Finset.notMem_union.mpr ⟨hxA, hxB⟩⟩
              rw [if_pos hxU, if_neg hxA, if_neg hxB, if_pos hxS]; ring
            · have hxS : x ∉ S := fun h => hxU (Finset.sdiff_subset h)
              rw [if_neg hxU, if_neg hxA, if_neg hxB, if_neg hxS]; ring
      dsimp only [F, coef₁, coef₂]
      by_cases hadj_uv : G.Adj u v
      · have hadj_vu : G.Adj v u := (G.adj_comm u v).mp hadj_uv
        rw [if_pos hadj_uv, if_pos hadj_vu, mul_one, mul_one, mul_one, mul_one]
        have h1B : (if (u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B) then (1 : ℝ) else 0) =
            (if u ∈ S then 1 else 0) * (if v ∈ B then 1 else 0) +
            (if v ∈ S then 1 else 0) * (if u ∈ B then 1 else 0) := by
          rw [ind_or_disj _ _ (fun ⟨h1, h2⟩ => hSB u ⟨h1.1, h2.2⟩), ind_and, ind_and]
        have h1A : (if (u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A) then (1 : ℝ) else 0) =
            (if u ∈ S then 1 else 0) * (if v ∈ A then 1 else 0) +
            (if v ∈ S then 1 else 0) * (if u ∈ A then 1 else 0) := by
          rw [ind_or_disj _ _ (fun ⟨h1, h2⟩ => hSA u ⟨h1.1, h2.2⟩), ind_and, ind_and]
        have h2B : (if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0) =
            2 * ((if u ∈ B then (1 : ℝ) else 0) * (if v ∈ B then 1 else 0)) := by
          by_cases hu : u ∈ B <;> by_cases hv : v ∈ B
          · rw [if_pos ⟨hu, hv⟩, if_pos hu, if_pos hv]; norm_num
          · rw [if_neg (fun h => hv h.2), if_pos hu, if_neg hv]; norm_num
          · rw [if_neg (fun h => hu h.1), if_neg hu, if_pos hv]; norm_num
          · rw [if_neg (fun h => hu h.1), if_neg hu, if_neg hv]; norm_num
        have h2A : (if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0) =
            2 * ((if u ∈ A then (1 : ℝ) else 0) * (if v ∈ A then 1 else 0)) := by
          by_cases hu : u ∈ A <;> by_cases hv : v ∈ A
          · rw [if_pos ⟨hu, hv⟩, if_pos hu, if_pos hv]; norm_num
          · rw [if_neg (fun h => hv h.2), if_pos hu, if_neg hv]; norm_num
          · rw [if_neg (fun h => hu h.1), if_neg hu, if_pos hv]; norm_num
          · rw [if_neg (fun h => hu h.1), if_neg hu, if_neg hv]; norm_num
        rw [ind_and (u ∈ B) (v ∈ U), ind_and (u ∈ A) (v ∈ U),
          ind_and (v ∈ B) (u ∈ U), ind_and (v ∈ A) (u ∈ U),
          hU_ind v, hU_ind u, h1B, h1A, h2B, h2A]
        ring
      · have hadj_vu : ¬ G.Adj v u := fun h => hadj_uv ((G.adj_comm u v).mpr h)
        rw [if_neg hadj_uv, if_neg hadj_vu]; ring
    linarith
  have hS_ge_half : (k : ℝ) / 2 ≤ (S.card : ℝ) := by
    have : k ≤ 2 * S.card := by omega
    have : (k : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast this
    linarith
  set T := c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
  have hT0_le_T : T₀ ≤ T := by
    dsimp only [T₀, T]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) * (16 * (n : ℝ))
        = c₂ * ((k : ℝ) / 2) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) * (32 * (n : ℝ)) := by ring
      _ ≤ c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) * (32 * (n : ℝ)) := by
          gcongr
  by_cases hZ1 : Z1 A B S ≤ T
  · left
    refine ⟨(A, B, S), ?_, hZ1⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard]
    exact ⟨⟨⟨Finset.subset_univ _, hAcard⟩, ⟨Finset.subset_univ _, hBcard⟩,
      ⟨Finset.subset_univ _, hScard⟩⟩, hdisjAB, hdisjS, hgap⟩
  · right
    have hZ2 : Z2 A B ≤ -T₀ := by linarith
    refine ⟨(A, B), ?_, hZ2⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard]
    exact ⟨⟨⟨Finset.subset_univ _, hAcard⟩, ⟨Finset.subset_univ _, hBcard⟩⟩, hdisjAB, hgap⟩

private lemma H3_bound1_pt {n k m : ℕ} {c₂ C : ℝ}
    (hc₂ : 0 < c₂) (hC : 0 < C) (hc2C4 : 4 ≤ c₂ ^ 2 * C ^ 4 / 24576)
    (hn_pos : (0 : ℝ) < (n : ℝ)) (hk_pos : (0 : ℝ) < (k : ℝ))
    (hm1 : 1 ≤ m) (hm5 : 5 * m ≤ k) (hm_pos : (0 : ℝ) < (m : ℝ))
    (hlogn_ge1 : 1 ≤ Real.log (n : ℝ)) (hlogn_pos : 0 < Real.log (n : ℝ))
    (hk_lb : C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) ≤ (k : ℝ))
    (hm_lb : (k : ℝ) / (6 * Real.log (n : ℝ)) ≤ (m : ℝ))
    {A B S : Finset (Fin n)} (hAcard : A.card = m) (hBcard : B.card = m) (hScard : S.card = k - 2 * m)
    (hdisjAB : Disjoint A B) (hdisjS : Disjoint S (A ∪ B))
    (hgap : ∀ u ∈ A, ∀ v ∈ B, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)) :
    (∑ G : SimpleGraph (Fin n),
      (if (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
            ((if (e.1.1 ∈ S ∧ e.1.2 ∈ B) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ B) then (1 : ℝ) else 0) -
              (if (e.1.1 ∈ S ∧ e.1.2 ∈ A) ∨ (e.1.2 ∈ S ∧ e.1.1 ∈ A) then 1 else 0)) *
            (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤
          c₂ * ((S.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
        then (1 : ℝ) else 0) *
      (∏ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        if G.Adj e.1.1 e.1.2
        then (1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ)))
        else 1 - (1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ))))) ≤
    Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let p_vert : Fin n → ℝ := fun u => 1 / 4 + (u : ℝ) / (2 * (n : ℝ))
  have hp_vert : ∀ u : Fin n, 1 / 4 ≤ p_vert u ∧ p_vert u ≤ 3 / 4 := by
    intro u
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hu1 : (u : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr u.isLt.le
    constructor
    · have : 0 ≤ (u : ℝ) / (2 * (n : ℝ)) := by positivity
      dsimp only [p_vert]; linarith
    · have : (u : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      dsimp only [p_vert]; linarith
  let q : {p : Fin n × Fin n // p ∈ E} → ℝ := fun e => p_vert e.1.1 * p_vert e.1.2
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := by
    intro e
    obtain ⟨_, _⟩ := hp_vert e.1.1
    obtain ⟨_, _⟩ := hp_vert e.1.2
    exact ⟨by positivity, by nlinarith⟩
  let coef₁ : Fin n × Fin n → ℝ := fun e =>
    (if (e.1 ∈ S ∧ e.2 ∈ B) ∨ (e.2 ∈ S ∧ e.1 ∈ B) then 1 else 0) -
    (if (e.1 ∈ S ∧ e.2 ∈ A) ∨ (e.2 ∈ S ∧ e.1 ∈ A) then 1 else 0)
  have hSA : ∀ x, x ∈ S → x ∉ A := fun x hx => by
    have := Finset.disjoint_left.mp hdisjS hx
    exact fun h => this (Finset.mem_union_left B h)
  have hSB : ∀ x, x ∈ S → x ∉ B := fun x hx => by
    have := Finset.disjoint_left.mp hdisjS hx
    exact fun h => this (Finset.mem_union_right A h)
  have hAB : ∀ x, x ∈ A → x ∉ B := fun x hx => Finset.disjoint_left.mp hdisjAB hx
  let F_mu : Fin n → Fin n → ℝ := fun u v =>
    ((if u ∈ S ∧ v ∈ B then (1 : ℝ) else 0) - (if u ∈ S ∧ v ∈ A then 1 else 0)) * (p_vert u * p_vert v)
  have hmu_eq : (∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e) =
      ∑ w ∈ S, p_vert w * ((∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u)) := by
    have h1 : (∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e) =
        ∑ e ∈ E, (F_mu e.1 e.2 + F_mu e.2 e.1) := by
      rw [Finset.sum_coe_sort E (fun p : Fin n × Fin n => coef₁ p * (p_vert p.1 * p_vert p.2))]
      refine Finset.sum_congr rfl fun ⟨u, v⟩ _ => ?_
      dsimp only [F_mu, coef₁, q]
      have h1B : (if (u ∈ S ∧ v ∈ B) ∨ (v ∈ S ∧ u ∈ B) then (1 : ℝ) else 0) =
          (if u ∈ S then 1 else 0) * (if v ∈ B then 1 else 0) +
          (if v ∈ S then 1 else 0) * (if u ∈ B then 1 else 0) := by
        rw [ind_or_disj _ _ (fun ⟨h1, h2⟩ => hSB u h1.1 h2.2), ind_and, ind_and]
      have h1A : (if (u ∈ S ∧ v ∈ A) ∨ (v ∈ S ∧ u ∈ A) then (1 : ℝ) else 0) =
          (if u ∈ S then 1 else 0) * (if v ∈ A then 1 else 0) +
          (if v ∈ S then 1 else 0) * (if u ∈ A then 1 else 0) := by
        rw [ind_or_disj _ _ (fun ⟨h1, h2⟩ => hSA u h1.1 h2.2), ind_and, ind_and]
      rw [h1B, h1A, ind_and (u ∈ S) (v ∈ B), ind_and (u ∈ S) (v ∈ A),
        ind_and (v ∈ S) (u ∈ B), ind_and (v ∈ S) (u ∈ A)]
      ring
    rw [h1, ← sum_pair_lt_eq_double n F_mu (fun u => by
      dsimp only [F_mu]
      rw [if_neg (fun ⟨h1, h2⟩ => hSB u h1 h2), if_neg (fun ⟨h1, h2⟩ => hSA u h1 h2)]
      ring)]
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun w _ hw =>
      Finset.sum_eq_zero fun v _ => by
        dsimp only [F_mu]; rw [if_neg (fun h => hw h.1), if_neg (fun h => hw h.1), sub_self, zero_mul])]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hsB : ∑ v : Fin n, (if w ∈ S ∧ v ∈ B then (1 : ℝ) else 0) * (p_vert w * p_vert v) =
        p_vert w * ∑ v ∈ B, p_vert v := by
      rw [← Finset.sum_subset (Finset.subset_univ B) (fun v _ hv => by
        rw [if_neg (fun h => hv h.2), zero_mul])]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => by rw [if_pos ⟨hw, hv⟩, one_mul]
    have hsA : ∑ v : Fin n, (if w ∈ S ∧ v ∈ A then (1 : ℝ) else 0) * (p_vert w * p_vert v) =
        p_vert w * ∑ v ∈ A, p_vert v := by
      rw [← Finset.sum_subset (Finset.subset_univ A) (fun v _ hv => by
        rw [if_neg (fun h => hv h.2), zero_mul])]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => by rw [if_pos ⟨hw, hv⟩, one_mul]
    simp_rw [F_mu, sub_mul, Finset.sum_sub_distrib, hsB, hsA, mul_sub]
  have hBA_diff : (m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ))) ≤
      (∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u) := by
    let embA := A.orderEmbOfFin hAcard
    let embB := B.orderEmbOfFin hBcard
    rw [sum_orderEmb A hAcard p_vert, sum_orderEmb B hBcard p_vert, ← Finset.sum_sub_distrib]
    calc (m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ)))
        = ∑ _ : Fin m, (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i : Fin m, (p_vert (embB i) - p_vert (embA i)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hiA : embA i ∈ A := by
            have : embA i ∈ Set.range embA := Set.mem_range_self _
            rwa [Finset.range_orderEmbOfFin] at this
          have hiB : embB i ∈ B := by
            have : embB i ∈ Set.range embB := Set.mem_range_self _
            rwa [Finset.range_orderEmbOfFin] at this
          have hdiff : p_vert (embB i) - p_vert (embA i) =
              (((embB i : ℕ) : ℝ) - ((embA i : ℕ) : ℝ)) / (2 * (n : ℝ)) := by
            dsimp only [p_vert]; ring
          rw [hdiff]
          exact div_le_div_of_nonneg_right (hgap (embA i) hiA (embB i) hiB) (by positivity)
  have hmu_lb : 2 * (c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))) ≤
      ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e := by
    rw [hmu_eq]
    have hS_term : ∀ w ∈ S,
        (1 / 4 : ℝ) * ((m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ)))) ≤
        p_vert w * ((∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u)) :=
      fun w _ => mul_le_mul (hp_vert w).1 hBA_diff (by positivity) (by positivity)
    calc 2 * (c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ)))
        = (S.card : ℝ) * ((1 / 4 : ℝ) * ((m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ))))) := by ring
      _ = ∑ _ ∈ S, ((1 / 4 : ℝ) * ((m : ℝ) * (c₂ * (k : ℝ) ^ (3 / 2 : ℝ) / (2 * (n : ℝ))))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ S, p_vert w * ((∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u)) :=
          Finset.sum_le_sum hS_term
  have hmu_ub : ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e ≤
      2 * (S.card : ℝ) * (m : ℝ) := by
    rw [hmu_eq]
    have hB_ub : ∑ v ∈ B, p_vert v ≤ (m : ℝ) := by
      calc ∑ v ∈ B, p_vert v ≤ ∑ _ ∈ B, (1 : ℝ) :=
            Finset.sum_le_sum fun v _ => (hp_vert v).2.trans (by norm_num)
        _ = (m : ℝ) := by rw [Finset.sum_const, hBcard, nsmul_eq_mul, mul_one]
    have hA_lb : 0 ≤ ∑ u ∈ A, p_vert u :=
      Finset.sum_nonneg fun u _ => by linarith [(hp_vert u).1]
    calc ∑ w ∈ S, p_vert w * ((∑ v ∈ B, p_vert v) - (∑ u ∈ A, p_vert u))
        ≤ ∑ _ ∈ S, (1 : ℝ) * (m : ℝ) := by
          refine Finset.sum_le_sum fun w _ => ?_
          refine mul_le_mul ((hp_vert w).2.trans (by norm_num)) (by linarith) ?_ (by norm_num)
          exact le_trans (by positivity) hBA_diff
      _ ≤ 2 * (S.card : ℝ) * (m : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          nlinarith
  have hC2_ub : ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₁ e.1) ^ 2 ≤
      2 * (S.card : ℝ) * (m : ℝ) :=
    H3_coef1_sq_le hAcard hBcard hSA hSB hAB
  have hcoef1 : ∀ e : {p : Fin n × Fin n // p ∈ E}, |coef₁ e.1| ≤ 2 := by
    intro e; dsimp only [coef₁]; split_ifs <;> norm_num
  set T := c₂ * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
  have hS1 : 1 ≤ S.card := by omega
  have hS_pos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS1
  have hT_pos : 0 < T := by positivity
  have hT_le_Sm : T ≤ (S.card : ℝ) * (m : ℝ) := by
    have : 2 * T ≤ 2 * (S.card : ℝ) * (m : ℝ) := hmu_lb.trans hmu_ub
    linarith
  set t : ℝ := T / (4 * (S.card : ℝ) * (m : ℝ))
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 / 2 := by
    dsimp only [t]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hch := chernoff_edge_sum n q hq (fun e => coef₁ e.1) hcoef1 ht0 ht1 T
  have hexp_le : t * (T - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e) +
      t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₁ e.1) ^ 2 ≤
      -4 * (k : ℝ) * Real.log (n : ℝ) := by
    have h1 : t * (T - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ e.1 * q e) +
        t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₁ e.1) ^ 2 ≤
        t * (-T) + t ^ 2 * (2 * (S.card : ℝ) * (m : ℝ)) := by
      refine add_le_add ?_ (mul_le_mul_of_nonneg_left hC2_ub (sq_nonneg t))
      refine mul_le_mul_of_nonneg_left (by linarith) ht0
    have h2 : t * (-T) + t ^ 2 * (2 * (S.card : ℝ) * (m : ℝ)) =
        -(T ^ 2 / (8 * (S.card : ℝ) * (m : ℝ))) := by
      dsimp only [t]; field_simp [hS_pos.ne', hm_pos.ne']; ring
    have hS_half : (k : ℝ) / 2 ≤ (S.card : ℝ) := by
      have : k ≤ 2 * S.card := by omega
      have : (k : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast this
      linarith
    have h3 : 4 * (k : ℝ) * Real.log (n : ℝ) ≤ T ^ 2 / (8 * (S.card : ℝ) * (m : ℝ)) := by
      have hT2 : T ^ 2 / (8 * (S.card : ℝ) * (m : ℝ)) =
          c₂ ^ 2 * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ 3 / (2048 * (n : ℝ) ^ 2) := by
        dsimp only [T]
        have hk3 : ((k : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (k : ℝ) ^ 3 := by
          rw [← Real.rpow_natCast ((k : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hk_pos.le,
            show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp [hn_pos.ne', hS_pos.ne', hm_pos.ne']
        rw [hk3]
        ring
      have hk4 : C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3 ≤ (k : ℝ) ^ 4 := by
        have h1' : (C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 ≤ (k : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by positivity) hk_lb 4
        have h2' : (C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 =
            C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3 := by
          have hsq4 : (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 := by
            calc (Real.sqrt (n : ℝ)) ^ 4 = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
              _ = (n : ℝ) ^ 2 := by rw [Real.sq_sqrt hn_pos.le]
          have hlog4 : ((Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 = (Real.log (n : ℝ)) ^ 3 := by
            rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hlogn_pos.le,
              show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rw [mul_pow, mul_pow, hsq4, hlog4]
        exact h2' ▸ h1'
      rw [hT2]
      calc 4 * (k : ℝ) * Real.log (n : ℝ)
          ≤ (c₂ ^ 2 * C ^ 4 / 24576) * (k : ℝ) * Real.log (n : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hlogn_pos.le
            exact mul_le_mul_of_nonneg_right hc2C4 hk_pos.le
        _ ≤ (c₂ ^ 2 * C ^ 4 / 24576) * (k : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            nlinarith
        _ = c₂ ^ 2 * (k : ℝ) * (C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3) /
              (24576 * (n : ℝ) ^ 2 * Real.log (n : ℝ)) := by
            field_simp [hn_pos.ne', hlogn_pos.ne']
        _ ≤ c₂ ^ 2 * (k : ℝ) * (k : ℝ) ^ 4 / (24576 * (n : ℝ) ^ 2 * Real.log (n : ℝ)) := by
            gcongr
        _ = c₂ ^ 2 * ((k : ℝ) / 2) * ((k : ℝ) / (6 * Real.log (n : ℝ))) * (k : ℝ) ^ 3 /
              (2048 * (n : ℝ) ^ 2) := by
            field_simp [hn_pos.ne', hlogn_pos.ne']
            ring
        _ ≤ c₂ ^ 2 * (S.card : ℝ) * (m : ℝ) * (k : ℝ) ^ 3 / (2048 * (n : ℝ) ^ 2) := by
            gcongr
    linarith
  exact hch.trans (Real.exp_le_exp.mpr hexp_le)

private lemma H3_Mreq_eq {c₂ C M_req : ℝ} (hc₂ : 0 < c₂) (hC : 0 < C)
    (hM_eq : M_req = 10368 * 768 * 4 / (c₂ * C ^ (5 / 2 : ℝ))) :
    4 * 10368 = c₂ * C ^ (5 / 2 : ℝ) / 768 * M_req := by
  have hC52 : C ^ (5 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hC (5 / 2)).ne'
  rw [hM_eq]
  field_simp [hc₂.ne', hC52]

private lemma H3_bound2_mu_nonneg {n m k : ℕ} {c₂ : ℝ} (hc₂ : 0 < c₂) (hn_pos : (0 : ℝ) < (n : ℝ))
    {A B : Finset (Fin n)} (hAcard : A.card = m) (hBcard : B.card = m)
    (hgap : ∀ u ∈ A, ∀ v ∈ B, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)) :
    0 ≤ ∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
      ((if e.1.1 ∈ B ∧ e.1.2 ∈ B then (2 : ℝ) else 0) -
        (if e.1.1 ∈ A ∧ e.1.2 ∈ A then (2 : ℝ) else 0)) *
      ((1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ)))) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let p_vert : Fin n → ℝ := fun u => 1 / 4 + (u : ℝ) / (2 * (n : ℝ))
  have hp_vert : ∀ u : Fin n, 1 / 4 ≤ p_vert u ∧ p_vert u ≤ 3 / 4 := by
    intro u
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hu1 : (u : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr u.isLt.le
    constructor
    · have : 0 ≤ (u : ℝ) / (2 * (n : ℝ)) := by positivity
      dsimp only [p_vert]; linarith
    · have : (u : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      dsimp only [p_vert]; linarith
  let coef₂ : Fin n × Fin n → ℝ := fun e =>
    (if e.1 ∈ B ∧ e.2 ∈ B then (2 : ℝ) else 0) -
    (if e.1 ∈ A ∧ e.2 ∈ A then (2 : ℝ) else 0)
  let F_mu : Fin n → Fin n → ℝ := fun u v =>
    ((if u ∈ B ∧ v ∈ B ∧ u ≠ v then (1 : ℝ) else 0) -
     (if u ∈ A ∧ v ∈ A ∧ u ≠ v then 1 else 0)) * (p_vert u * p_vert v)
  have hmu_eq : (∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * (p_vert e.1.1 * p_vert e.1.2)) =
      (∑ v₁ ∈ B, ∑ v₂ ∈ B, if v₁ ≠ v₂ then p_vert v₁ * p_vert v₂ else 0) -
      (∑ u₁ ∈ A, ∑ u₂ ∈ A, if u₁ ≠ u₂ then p_vert u₁ * p_vert u₂ else 0) := by
    have h1 : (∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * (p_vert e.1.1 * p_vert e.1.2)) =
        ∑ e ∈ E, (F_mu e.1 e.2 + F_mu e.2 e.1) := by
      rw [Finset.sum_coe_sort E (fun p : Fin n × Fin n => coef₂ p * (p_vert p.1 * p_vert p.2))]
      refine Finset.sum_congr rfl fun ⟨u, v⟩ huv => ?_
      have hne : u ≠ v := ((Finset.mem_filter.mp huv).2).ne
      dsimp only [F_mu, coef₂]
      have hB1 : (if v ∈ B ∧ u ∈ B ∧ v ≠ u then (1 : ℝ) else 0) = if u ∈ B ∧ v ∈ B then 1 else 0 := by
        by_cases h : u ∈ B ∧ v ∈ B
        · rw [if_pos ⟨h.2, h.1, hne.symm⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨h'.2.1, h'.1⟩), if_neg h]
      have hB2 : (if u ∈ B ∧ v ∈ B ∧ u ≠ v then (1 : ℝ) else 0) = if u ∈ B ∧ v ∈ B then 1 else 0 := by
        by_cases h : u ∈ B ∧ v ∈ B
        · rw [if_pos ⟨h.1, h.2, hne⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), if_neg h]
      have hA1 : (if v ∈ A ∧ u ∈ A ∧ v ≠ u then (1 : ℝ) else 0) = if u ∈ A ∧ v ∈ A then 1 else 0 := by
        by_cases h : u ∈ A ∧ v ∈ A
        · rw [if_pos ⟨h.2, h.1, hne.symm⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨h'.2.1, h'.1⟩), if_neg h]
      have hA2 : (if u ∈ A ∧ v ∈ A ∧ u ≠ v then (1 : ℝ) else 0) = if u ∈ A ∧ v ∈ A then 1 else 0 := by
        by_cases h : u ∈ A ∧ v ∈ A
        · rw [if_pos ⟨h.1, h.2, hne⟩, if_pos h]
        · rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩), if_neg h]
      have h2B : (if u ∈ B ∧ v ∈ B then (2 : ℝ) else 0) = 2 * (if u ∈ B ∧ v ∈ B then (1 : ℝ) else 0) := by
        by_cases h : u ∈ B ∧ v ∈ B
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      have h2A : (if u ∈ A ∧ v ∈ A then (2 : ℝ) else 0) = 2 * (if u ∈ A ∧ v ∈ A then (1 : ℝ) else 0) := by
        by_cases h : u ∈ A ∧ v ∈ A
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h]; ring
      rw [hB1, hB2, hA1, hA2, h2B, h2A]
      ring
    rw [h1, ← sum_pair_lt_eq_double n F_mu (fun u => by
      dsimp only [F_mu]
      rw [if_neg (fun h => h.2.2 rfl), if_neg (fun h => h.2.2 rfl), sub_self, zero_mul])]
    have hB_eq : (∑ u : Fin n, ∑ v : Fin n,
        (if u ∈ B ∧ v ∈ B ∧ u ≠ v then (1 : ℝ) else 0) * (p_vert u * p_vert v)) =
        ∑ v₁ ∈ B, ∑ v₂ ∈ B, if v₁ ≠ v₂ then p_vert v₁ * p_vert v₂ else 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ B) (fun u _ hu =>
        Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1), zero_mul])]
      refine Finset.sum_congr rfl fun v₁ hv₁ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ B) (fun v₂ _ hv₂ => by
        rw [if_neg (fun h => hv₂ h.2.1), zero_mul])]
      refine Finset.sum_congr rfl fun v₂ hv₂ => by
        by_cases hne : v₁ ≠ v₂
        · rw [if_pos ⟨hv₁, hv₂, hne⟩, if_pos hne, one_mul]
        · rw [if_neg (fun h => hne h.2.2), if_neg hne, zero_mul]
    have hA_eq : (∑ u : Fin n, ∑ v : Fin n,
        (if u ∈ A ∧ v ∈ A ∧ u ≠ v then (1 : ℝ) else 0) * (p_vert u * p_vert v)) =
        ∑ u₁ ∈ A, ∑ u₂ ∈ A, if u₁ ≠ u₂ then p_vert u₁ * p_vert u₂ else 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ A) (fun u _ hu =>
        Finset.sum_eq_zero fun v _ => by rw [if_neg (fun h => hu h.1), zero_mul])]
      refine Finset.sum_congr rfl fun u₁ hu₁ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ A) (fun u₂ _ hu₂ => by
        rw [if_neg (fun h => hu₂ h.2.1), zero_mul])]
      refine Finset.sum_congr rfl fun u₂ hu₂ => by
        by_cases hne : u₁ ≠ u₂
        · rw [if_pos ⟨hu₁, hu₂, hne⟩, if_pos hne, one_mul]
        · rw [if_neg (fun h => hne h.2.2), if_neg hne, zero_mul]
    simp_rw [F_mu, sub_mul, Finset.sum_sub_distrib, hB_eq, hA_eq]
  change 0 ≤ ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * (p_vert e.1.1 * p_vert e.1.2)
  rw [hmu_eq, sum_pairs_orderEmb A hAcard p_vert, sum_pairs_orderEmb B hBcard p_vert, sub_nonneg]
  let embA := A.orderEmbOfFin hAcard
  let embB := B.orderEmbOfFin hBcard
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hij : i ≠ j
  · rw [if_pos hij, if_pos hij]
    have hiA : embA i ∈ A := by
      have : embA i ∈ Set.range embA := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    have hjA : embA j ∈ A := by
      have : embA j ∈ Set.range embA := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    have hiB : embB i ∈ B := by
      have : embB i ∈ Set.range embB := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    have hjB : embB j ∈ B := by
      have : embB j ∈ Set.range embB := Set.mem_range_self _
      rwa [Finset.range_orderEmbOfFin] at this
    have hi_le : p_vert (embA i) ≤ p_vert (embB i) := by
      have h1 : 0 ≤ ((embB i : ℕ) : ℝ) - ((embA i : ℕ) : ℝ) := le_trans (by positivity) (hgap _ hiA _ hiB)
      have h2 : ((embA i : ℕ) : ℝ) ≤ ((embB i : ℕ) : ℝ) := by linarith
      dsimp only [p_vert]
      gcongr
    have hj_le : p_vert (embA j) ≤ p_vert (embB j) := by
      have h1 : 0 ≤ ((embB j : ℕ) : ℝ) - ((embA j : ℕ) : ℝ) := le_trans (by positivity) (hgap _ hjA _ hjB)
      have h2 : ((embA j : ℕ) : ℝ) ≤ ((embB j : ℕ) : ℝ) := by linarith
      dsimp only [p_vert]
      gcongr
    exact mul_le_mul hi_le hj_le (by linarith [(hp_vert (embA j)).1]) (by linarith [(hp_vert (embB i)).1])
  · rw [if_neg hij, if_neg hij]

private lemma H3_bound2_case2 {n k m : ℕ} {c₂ C M_req T₀ : ℝ}
    (hc₂ : 0 < c₂) (hC : 0 < C)
    (hM_eq : M_req = 10368 * 768 * 4 / (c₂ * C ^ (5 / 2 : ℝ))) (hn_gt_M6 : M_req ^ 6 < (n : ℝ))
    (hT0_eq : T₀ = c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ)))
    (hn1 : 1 ≤ n) (hn_pos : (0 : ℝ) < (n : ℝ)) (hk_pos : (0 : ℝ) < (k : ℝ))
    (hlogn_ge1 : 1 ≤ Real.log (n : ℝ)) (hlogn_pos : 0 < Real.log (n : ℝ))
    (hk_lb : C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) ≤ (k : ℝ))
    (hm_lb : (k : ℝ) / (6 * Real.log (n : ℝ)) ≤ (m : ℝ)) :
    4 * (k : ℝ) * Real.log (n : ℝ) ≤ T₀ / 4 := by
  have hk_lb2 : C * Real.sqrt (n : ℝ) ≤ (k : ℝ) := by
    have hlog34 : 1 ≤ (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := Real.one_le_rpow hlogn_ge1 (by norm_num)
    calc C * Real.sqrt (n : ℝ) = C * Real.sqrt (n : ℝ) * 1 := by ring
      _ ≤ C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by gcongr
      _ ≤ (k : ℝ) := hk_lb
  have hk52 : C ^ (5 / 2 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ) ≤ (k : ℝ) ^ (5 / 2 : ℝ) := by
    have h1 : (C * Real.sqrt (n : ℝ)) ^ (5 / 2 : ℝ) ≤ (k : ℝ) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hk_lb2 (by norm_num)
    have h2 : (C * Real.sqrt (n : ℝ)) ^ (5 / 2 : ℝ) = C ^ (5 / 2 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ) := by
      rw [Real.mul_rpow hC.le (Real.sqrt_nonneg n), Real.sqrt_eq_rpow, ← Real.rpow_mul hn_pos.le,
        show (1 / 2 : ℝ) * (5 / 2 : ℝ) = 5 / 4 by norm_num]
    exact h2 ▸ h1
  have hM_lt : M_req < (n : ℝ) ^ (1 / 6 : ℝ) := by
    have hM0 : 0 ≤ M_req := by rw [hM_eq]; positivity
    have h1 := Real.rpow_lt_rpow (by positivity) hn_gt_M6 (by norm_num : (0 : ℝ) < 1 / 6)
    rw [← Real.rpow_natCast M_req 6, ← Real.rpow_mul hM0,
      show ((6 : ℕ) : ℝ) * (1 / 6 : ℝ) = 1 by norm_num, Real.rpow_one] at h1
    exact h1
  have hlog_pow : 4 * (Real.log (n : ℝ)) ^ 2 ≤ c₂ * C ^ (5 / 2 : ℝ) / 768 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    have h3 := log_cubed_le_n_twelfth n hn1
    have hlog2 : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 3 := by nlinarith
    have hn14 : (n : ℝ) ^ (1 / 6 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hn_pos, show (1 / 6 : ℝ) + (1 / 12 : ℝ) = 1 / 4 by norm_num]
    calc 4 * (Real.log (n : ℝ)) ^ 2
        ≤ 4 * (Real.log (n : ℝ)) ^ 3 := by linarith
      _ ≤ 4 * (10368 * (n : ℝ) ^ (1 / 12 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ = c₂ * C ^ (5 / 2 : ℝ) / 768 * (M_req * (n : ℝ) ^ (1 / 12 : ℝ)) := by
          rw [← mul_assoc, H3_Mreq_eq hc₂ hC hM_eq, mul_assoc]
      _ ≤ c₂ * C ^ (5 / 2 : ℝ) / 768 * ((n : ℝ) ^ (1 / 6 : ℝ) * (n : ℝ) ^ (1 / 12 : ℝ)) := by
          gcongr
      _ = c₂ * C ^ (5 / 2 : ℝ) / 768 * (n : ℝ) ^ (1 / 4 : ℝ) := by rw [hn14]
  have hn54 : (n : ℝ) ^ (5 / 4 : ℝ) / (n : ℝ) = (n : ℝ) ^ (1 / 4 : ℝ) := by
    rw [div_eq_mul_inv]
    conv_lhs => arg 2; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_neg hn_pos.le, ← Real.rpow_add hn_pos,
      show (5 / 4 : ℝ) + -(1 : ℝ) = 1 / 4 by norm_num]
  have hT0_div : T₀ / 4 = c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (128 * (n : ℝ)) := by
    rw [hT0_eq]; ring
  have hk52_split : (k : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) = (k : ℝ) ^ (5 / 2 : ℝ) := by
    conv_lhs => arg 1; rw [← Real.rpow_one (k : ℝ)]
    rw [← Real.rpow_add hk_pos, show (1 : ℝ) + 3 / 2 = 5 / 2 by norm_num]
  rw [hT0_div]
  calc 4 * (k : ℝ) * Real.log (n : ℝ)
      = (4 * (Real.log (n : ℝ)) ^ 2) * (k : ℝ) / Real.log (n : ℝ) := by
        field_simp [hlogn_pos.ne']; try ring
    _ ≤ (c₂ * C ^ (5 / 2 : ℝ) / 768 * (n : ℝ) ^ (1 / 4 : ℝ)) * (k : ℝ) / Real.log (n : ℝ) := by
        gcongr
    _ = c₂ * (k : ℝ) * (C ^ (5 / 2 : ℝ) * (n : ℝ) ^ (5 / 4 : ℝ)) / (768 * (n : ℝ) * Real.log (n : ℝ)) := by
        rw [← hn54]; field_simp [hn_pos.ne', hlogn_pos.ne']; try ring
    _ ≤ c₂ * (k : ℝ) * (k : ℝ) ^ (5 / 2 : ℝ) / (768 * (n : ℝ) * Real.log (n : ℝ)) := by
        gcongr
    _ = c₂ * (k : ℝ) * ((k : ℝ) / (6 * Real.log (n : ℝ))) * (k : ℝ) ^ (3 / 2 : ℝ) / (128 * (n : ℝ)) := by
        rw [← hk52_split]; field_simp [hn_pos.ne', hlogn_pos.ne']; try ring
    _ ≤ c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (128 * (n : ℝ)) := by
        gcongr

private lemma H3_bound2_pt {n k m : ℕ} {c₂ C M_req : ℝ}
    (hc₂ : 0 < c₂) (hC : 0 < C) (hc2C4 : 4 ≤ c₂ ^ 2 * C ^ 4 / 24576)
    (hM_eq : M_req = 10368 * 768 * 4 / (c₂ * C ^ (5 / 2 : ℝ))) (hn_gt_M6 : M_req ^ 6 < (n : ℝ))
    (hn1 : 1 ≤ n) (hn_pos : (0 : ℝ) < (n : ℝ)) (hk_pos : (0 : ℝ) < (k : ℝ))
    (hm_pos : (0 : ℝ) < (m : ℝ)) (hlogn_ge1 : 1 ≤ Real.log (n : ℝ)) (hlogn_pos : 0 < Real.log (n : ℝ))
    (hk_lb : C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) ≤ (k : ℝ))
    (hm_lb : (k : ℝ) / (6 * Real.log (n : ℝ)) ≤ (m : ℝ))
    {A B : Finset (Fin n)} (hAcard : A.card = m) (hBcard : B.card = m)
    (hdisjAB : Disjoint A B)
    (hgap : ∀ u ∈ A, ∀ v ∈ B, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)) :
    (∑ G : SimpleGraph (Fin n),
      (if (∑ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
            ((if e.1.1 ∈ B ∧ e.1.2 ∈ B then (2 : ℝ) else 0) -
              (if e.1.1 ∈ A ∧ e.1.2 ∈ A then (2 : ℝ) else 0)) *
            (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)) ≤
          -(c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ)))
        then (1 : ℝ) else 0) *
      (∏ e : {p : Fin n × Fin n // p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)},
        if G.Adj e.1.1 e.1.2
        then (1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ)))
        else 1 - (1 / 4 + (e.1.1 : ℝ) / (2 * (n : ℝ))) * (1 / 4 + (e.1.2 : ℝ) / (2 * (n : ℝ))))) ≤
    Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let p_vert : Fin n → ℝ := fun u => 1 / 4 + (u : ℝ) / (2 * (n : ℝ))
  have hp_vert : ∀ u : Fin n, 1 / 4 ≤ p_vert u ∧ p_vert u ≤ 3 / 4 := by
    intro u
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hu1 : (u : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr u.isLt.le
    constructor
    · have : 0 ≤ (u : ℝ) / (2 * (n : ℝ)) := by positivity
      dsimp only [p_vert]; linarith
    · have : (u : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      dsimp only [p_vert]; linarith
  let q : {p : Fin n × Fin n // p ∈ E} → ℝ := fun e => p_vert e.1.1 * p_vert e.1.2
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := by
    intro e
    obtain ⟨_, _⟩ := hp_vert e.1.1
    obtain ⟨_, _⟩ := hp_vert e.1.2
    exact ⟨by positivity, by nlinarith⟩
  let coef₂ : Fin n × Fin n → ℝ := fun e =>
    (if e.1 ∈ B ∧ e.2 ∈ B then (2 : ℝ) else 0) -
    (if e.1 ∈ A ∧ e.2 ∈ A then (2 : ℝ) else 0)
  set T₀ : ℝ := c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ))
  have hAB : ∀ x, x ∈ A → x ∉ B := fun x hx => Finset.disjoint_left.mp hdisjAB hx
  have hmu_nonneg : 0 ≤ ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * q e := by
    dsimp only [coef₂, q, p_vert]
    exact H3_bound2_mu_nonneg hc₂ hn_pos hAcard hBcard hgap
  have hC2_ub : ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₂ e.1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 :=
    H3_coef2_sq_le hAcard hBcard hAB
  have hcoef2 : ∀ e : {p : Fin n × Fin n // p ∈ E}, |coef₂ e.1| ≤ 2 := by
    intro e; dsimp only [coef₂]; split_ifs <;> norm_num
  set t : ℝ := min (1 / 2) (T₀ / (8 * (m : ℝ) ^ 2))
  have hT0_pos : 0 < T₀ := by positivity
  have ht0 : 0 ≤ t := le_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have hch := chernoff_edge_sum n q hq (fun e => coef₂ e.1) hcoef2 ht0 ht1 (-T₀)
  have hexp_le : t * (-T₀ - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * q e) +
      t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₂ e.1) ^ 2 ≤
      -4 * (k : ℝ) * Real.log (n : ℝ) := by
    have h1 : t * (-T₀ - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * q e) +
        t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₂ e.1) ^ 2 ≤
        -t * T₀ + 4 * (m : ℝ) ^ 2 * t ^ 2 := by
      refine add_le_add ?_ ?_
      · calc t * (-T₀ - ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ e.1 * q e)
            ≤ t * (-T₀) := mul_le_mul_of_nonneg_left (by linarith) ht0
          _ = -t * T₀ := by ring
      · calc t ^ 2 * ∑ e : {p : Fin n × Fin n // p ∈ E}, (coef₂ e.1) ^ 2
            ≤ t ^ 2 * (4 * (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hC2_ub (sq_nonneg t)
          _ = 4 * (m : ℝ) ^ 2 * t ^ 2 := by ring
    have h2 : -t * T₀ + 4 * (m : ℝ) ^ 2 * t ^ 2 ≤ -4 * (k : ℝ) * Real.log (n : ℝ) := by
      by_cases hcase : T₀ ≤ 4 * (m : ℝ) ^ 2
      · have ht_eq : t = T₀ / (8 * (m : ℝ) ^ 2) := by
          dsimp only [t]; refine min_eq_right ?_
          rw [div_le_iff₀ (by positivity)]; linarith
        rw [ht_eq]
        have hval : -(T₀ / (8 * (m : ℝ) ^ 2)) * T₀ + 4 * (m : ℝ) ^ 2 * (T₀ / (8 * (m : ℝ) ^ 2)) ^ 2 =
            -(T₀ ^ 2 / (16 * (m : ℝ) ^ 2)) := by
          field_simp [hm_pos.ne']; ring
        rw [hval]
        have hT02 : T₀ ^ 2 / (16 * (m : ℝ) ^ 2) =
            c₂ ^ 2 * (k : ℝ) ^ 5 / (16384 * (n : ℝ) ^ 2) := by
          dsimp only [T₀]
          have hk3 : ((k : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = (k : ℝ) ^ 3 := by
            rw [← Real.rpow_natCast ((k : ℝ) ^ (3 / 2 : ℝ)) 2, ← Real.rpow_mul hk_pos.le,
              show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          field_simp [hn_pos.ne', hm_pos.ne']
          rw [hk3]
          ring
        have hk4 : C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3 ≤ (k : ℝ) ^ 4 := by
          have h1' : (C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 ≤ (k : ℝ) ^ 4 :=
            pow_le_pow_left₀ (by positivity) hk_lb 4
          have h2' : (C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 =
              C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3 := by
            have hsq4 : (Real.sqrt (n : ℝ)) ^ 4 = (n : ℝ) ^ 2 := by
              calc (Real.sqrt (n : ℝ)) ^ 4 = ((Real.sqrt (n : ℝ)) ^ 2) ^ 2 := by ring
                _ = (n : ℝ) ^ 2 := by rw [Real.sq_sqrt hn_pos.le]
            have hlog4 : ((Real.log (n : ℝ)) ^ (3 / 4 : ℝ)) ^ 4 = (Real.log (n : ℝ)) ^ 3 := by
              rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hlogn_pos.le,
                show (3 / 4 : ℝ) * ((4 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            rw [mul_pow, mul_pow, hsq4, hlog4]
          exact h2' ▸ h1'
        have hbound : 4 * (k : ℝ) * Real.log (n : ℝ) ≤ T₀ ^ 2 / (16 * (m : ℝ) ^ 2) := by
          rw [hT02]
          calc 4 * (k : ℝ) * Real.log (n : ℝ)
              ≤ (c₂ ^ 2 * C ^ 4 / 24576) * (k : ℝ) * Real.log (n : ℝ) := by
                refine mul_le_mul_of_nonneg_right ?_ hlogn_pos.le
                exact mul_le_mul_of_nonneg_right hc2C4 hk_pos.le
            _ ≤ (c₂ ^ 2 * C ^ 4 / 16384) * (k : ℝ) * (Real.log (n : ℝ)) ^ 3 := by
                have h16 : (c₂ ^ 2 * C ^ 4 / 24576) ≤ c₂ ^ 2 * C ^ 4 / 16384 := by
                  gcongr; norm_num
                have hlog3 : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 3 := by
                  calc Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith
                    _ ≤ (Real.log (n : ℝ)) ^ 3 := by nlinarith
                refine mul_le_mul (mul_le_mul_of_nonneg_right h16 hk_pos.le) hlog3 hlogn_pos.le (by positivity)
            _ = c₂ ^ 2 * (k : ℝ) * (C ^ 4 * (n : ℝ) ^ 2 * (Real.log (n : ℝ)) ^ 3) / (16384 * (n : ℝ) ^ 2) := by
                field_simp [hn_pos.ne']
            _ ≤ c₂ ^ 2 * (k : ℝ) * (k : ℝ) ^ 4 / (16384 * (n : ℝ) ^ 2) := by gcongr
            _ = c₂ ^ 2 * (k : ℝ) ^ 5 / (16384 * (n : ℝ) ^ 2) := by ring
        linarith
      · have ht_eq : t = 1 / 2 := by
          dsimp only [t]; refine min_eq_left ?_
          rw [le_div_iff₀ (by positivity)]
          linarith
        rw [ht_eq]
        have hval : -(1 / 2 : ℝ) * T₀ + 4 * (m : ℝ) ^ 2 * (1 / 2 : ℝ) ^ 2 ≤ -(T₀ / 4) := by
          linarith
        have hbound : 4 * (k : ℝ) * Real.log (n : ℝ) ≤ T₀ / 4 :=
          H3_bound2_case2 hc₂ hC hM_eq hn_gt_M6 rfl hn1 hn_pos hk_pos hlogn_ge1 hlogn_pos hk_lb hm_lb
        linarith
    exact h1.trans h2
  exact hch.trans (Real.exp_le_exp.mpr hexp_le)

end Helpers

set_option maxHeartbeats 800000 in
theorem proof : OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1.H3 := by
  intro c₂ hc₂
  set C : ℝ := max 1 (max (20 / Real.sqrt c₂) ((4000 / c₂) ^ (2 / 5 : ℝ)))
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hc2C4 : 4 ≤ c₂ ^ 2 * C ^ 4 / 24576 := by
    have h20 : 20 / Real.sqrt c₂ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
    have hsq : 400 / c₂ ≤ C ^ 2 := by
      have h1 : (20 / Real.sqrt c₂) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (by positivity) h20 2
      rwa [div_pow, Real.sq_sqrt hc₂.le, show (20 : ℝ) ^ 2 = 400 by norm_num] at h1
    have h4 : 160000 / c₂ ^ 2 ≤ C ^ 4 := by
      have h1 : (400 / c₂) ^ 2 ≤ (C ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hsq 2
      have h2 : (C ^ 2) ^ 2 = C ^ 4 := by ring
      have h3 : (400 / c₂) ^ 2 = 160000 / c₂ ^ 2 := by ring
      linarith
    have hmul : 160000 ≤ c₂ ^ 2 * C ^ 4 := by
      linarith [(div_le_iff₀ (sq_pos_of_pos hc₂)).mp h4]
    linarith
  have hc2C52 : 4000 ≤ c₂ * C ^ (5 / 2 : ℝ) := by
    have h52 : (4000 / c₂) ^ (2 / 5 : ℝ) ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
    have hr : 4000 / c₂ ≤ C ^ (5 / 2 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) h52 (by norm_num : (0 : ℝ) ≤ 5 / 2)
      rw [← Real.rpow_mul (by positivity)] at h
      norm_num at h
      exact h
    linarith [(div_le_iff₀ hc₂).mp hr]
  set M_req : ℝ := 10368 * 768 * 4 / (c₂ * C ^ (5 / 2 : ℝ))
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (max (max (256 : ℝ) (M_req ^ 6)) (3 : ℝ))
  refine ⟨C, hC, N₁, fun n hn k hk_lb hk_le => ?_⟩
  have hn3 : 3 ≤ n := by
    have : (3 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hN₁ (by exact_mod_cast hn))
    exact_mod_cast this.le
  have hn256 : 256 ≤ n := by
    have : (256 : ℝ) < (n : ℝ) :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _))
        (lt_of_lt_of_le hN₁ (by exact_mod_cast hn))
    exact_mod_cast this.le
  have hn1 : 1 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hlogn_ge1 : 1 ≤ Real.log (n : ℝ) := by
    have hexp3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have : Real.exp 1 ≤ (n : ℝ) := le_trans hexp3.le (by exact_mod_cast hn3)
    exact (Real.le_log_iff_exp_le hn_pos).mpr this
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hk_ge_sqrt : Real.sqrt (n : ℝ) ≤ (k : ℝ) := by
    have hC1 : 1 ≤ C := le_max_left _ _
    have hlog34 : 1 ≤ (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := Real.one_le_rpow hlogn_ge1 (by norm_num)
    calc Real.sqrt (n : ℝ)
        = 1 * Real.sqrt (n : ℝ) * 1 := by ring
      _ ≤ C * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by gcongr
      _ ≤ (k : ℝ) := hk_lb
  have hk16 : 16 ≤ k := by
    have h16_le_sqrt : (16 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      norm_num
      exact_mod_cast hn256
    exact_mod_cast h16_le_sqrt.trans hk_ge_sqrt
  have hk1 : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  set m : ℕ := k / (Nat.log 2 k + 1)
  have hlogk_ge4 : 4 ≤ Nat.log 2 k := by
    have h16 : Nat.log 2 16 = 4 := by decide
    exact h16 ▸ Nat.log_mono_right hk16
  have hm5 : 5 * m ≤ k := by
    have hmul : (Nat.log 2 k + 1) * m ≤ k := Nat.mul_div_le k (Nat.log 2 k + 1)
    have hle : 5 * m ≤ (Nat.log 2 k + 1) * m := Nat.mul_le_mul_right m (by omega)
    omega
  have hm1 : 1 ≤ m := by
    have hpow_le : Nat.log 2 k + 1 ≤ k := by
      have hpow : 2 ^ (Nat.log 2 k) ≤ k := Nat.pow_log_le_self 2 (by omega)
      have hlin : ∀ r : ℕ, 4 ≤ r → r + 1 ≤ 2 ^ r := by
        intro r hr
        induction r, hr using Nat.le_induction with
        | base => decide
        | succ r hr ih =>
          rw [pow_succ']
          omega
      exact (hlin _ hlogk_ge4).trans hpow
    exact Nat.div_pos hpow_le (by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hlogk_le_logn : (Nat.log 2 k + 1 : ℝ) ≤ 3 * Real.log (n : ℝ) := by
    have hle : Nat.log 2 k ≤ Nat.log 2 n := Nat.log_mono_right hk_le
    have h1 : (Nat.log 2 k + 1 : ℝ) ≤ (Nat.log 2 n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hle 1
    exact h1.trans (log_div_log_two_le hn3)
  have hm_lb : (k : ℝ) / (6 * Real.log (n : ℝ)) ≤ (m : ℝ) := by
    have hlt : k < (m + 1) * (Nat.log 2 k + 1) := Nat.lt_mul_of_div_lt (Nat.lt_succ_self m) (by positivity)
    have hlt_r : (k : ℝ) < ((m : ℝ) + 1) * (Nat.log 2 k + 1 : ℝ) := by exact_mod_cast hlt
    have hm_2 : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by exact_mod_cast (by omega : m + 1 ≤ 2 * m)
    have h1 : (k : ℝ) ≤ (2 * (m : ℝ)) * (3 * Real.log (n : ℝ)) := by
      calc (k : ℝ) ≤ ((m : ℝ) + 1) * (Nat.log 2 k + 1 : ℝ) := hlt_r.le
        _ ≤ (2 * (m : ℝ)) * (3 * Real.log (n : ℝ)) :=
            mul_le_mul hm_2 hlogk_le_logn (by positivity) (by positivity)
    rw [div_le_iff₀ (by positivity)]
    linarith
  let E := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let p_vert : Fin n → ℝ := fun u => 1 / 4 + (u : ℝ) / (2 * (n : ℝ))
  have hp_vert : ∀ u : Fin n, 1 / 4 ≤ p_vert u ∧ p_vert u ≤ 3 / 4 := by
    intro u
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hu1 : (u : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr u.isLt.le
    constructor
    · have : 0 ≤ (u : ℝ) / (2 * (n : ℝ)) := by positivity
      dsimp only [p_vert]; linarith
    · have : (u : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
      dsimp only [p_vert]; linarith
  let q : {p : Fin n × Fin n // p ∈ E} → ℝ := fun e => p_vert e.1.1 * p_vert e.1.2
  have hq : ∀ e, 0 ≤ q e ∧ q e ≤ 1 := by
    intro e
    obtain ⟨h1, h2⟩ := hp_vert e.1.1
    obtain ⟨h3, h4⟩ := hp_vert e.1.2
    exact ⟨by positivity, by nlinarith⟩
  let coef₁ (A B S : Finset (Fin n)) (e : Fin n × Fin n) : ℝ :=
    (if (e.1 ∈ S ∧ e.2 ∈ B) ∨ (e.2 ∈ S ∧ e.1 ∈ B) then 1 else 0) -
    (if (e.1 ∈ S ∧ e.2 ∈ A) ∨ (e.2 ∈ S ∧ e.1 ∈ A) then 1 else 0)
  let coef₂ (A B : Finset (Fin n)) (e : Fin n × Fin n) : ℝ :=
    (if e.1 ∈ B ∧ e.2 ∈ B then (2 : ℝ) else 0) -
    (if e.1 ∈ A ∧ e.2 ∈ A then (2 : ℝ) else 0)
  let T₀ : ℝ := c₂ * (k : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (32 * (n : ℝ))
  let BadTriples := ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).filter
      (fun p : Finset (Fin n) × Finset (Fin n) × Finset (Fin n) =>
        Disjoint p.1 p.2.1 ∧ Disjoint p.2.2 (p.1 ∪ p.2.1) ∧
        ∀ u ∈ p.1, ∀ v ∈ p.2.1, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ))
  let BadPairs := ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun p : Finset (Fin n) × Finset (Fin n) => Disjoint p.1 p.2 ∧
        ∀ u ∈ p.1, ∀ v ∈ p.2, c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ ((v : ℕ) : ℝ) - ((u : ℕ) : ℝ))
  let Z1 (A B S : Finset (Fin n)) (G : SimpleGraph (Fin n)) : ℝ :=
    ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₁ A B S e.1 * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)
  let Z2 (A B : Finset (Fin n)) (G : SimpleGraph (Fin n)) : ℝ :=
    ∑ e : {p : Fin n × Fin n // p ∈ E}, coef₂ A B e.1 * (if G.Adj e.1.1 e.1.2 then (1 : ℝ) else 0)
  have hn_gt_M6 : M_req ^ 6 < (n : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _))
      (lt_of_lt_of_le hN₁ (by exact_mod_cast hn))
  have hstruct : ∀ G : SimpleGraph (Fin n),
      (∃ U : Finset (Fin n), U.card = k ∧
        (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
        (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
          m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)) →
      (∃ p ∈ BadTriples, Z1 p.1 p.2.1 p.2.2 G ≤
          c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))) ∨
      (∃ p ∈ BadPairs, Z2 p.1 p.2 G ≤ -T₀) := by
    rintro G ⟨U, hUk, ⟨d, hd⟩, ⟨a, b, hab, hspan, hUa, hUb⟩⟩
    dsimp only [BadTriples, BadPairs, Z1, Z2, coef₁, coef₂, T₀]
    exact H3_struct_pt hc₂ hn_pos hm5 G U hUk d hd a b hab hspan hUa hUb
  have hw_nonneg : ∀ G : SimpleGraph (Fin n),
      0 ≤ ∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e := by
    intro G
    refine Finset.prod_nonneg fun e _ => ?_
    have := hq e
    split_ifs <;> linarith
  have h1_bound : ∀ p ∈ BadTriples,
      (∑ G : SimpleGraph (Fin n),
        (if Z1 p.1 p.2.1 p.2.2 G ≤
            c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) ≤
      Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
    rintro ⟨A, B, S⟩ hp
    simp only [BadTriples, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard] at hp
    rcases hp with ⟨⟨⟨_, hAcard⟩, ⟨_, hBcard⟩, ⟨_, hScard⟩⟩, hdisjAB, hdisjS, hgap⟩
    dsimp only [Z1, coef₁, q, p_vert]
    exact H3_bound1_pt hc₂ hC hc2C4 hn_pos hk_pos hm1 hm5 hm_pos hlogn_ge1 hlogn_pos
      hk_lb hm_lb hAcard hBcard hScard hdisjAB hdisjS hgap
  have h2_bound : ∀ p ∈ BadPairs,
      (∑ G : SimpleGraph (Fin n),
        (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) ≤
      Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
    rintro ⟨A, B⟩ hp
    simp only [BadPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_powersetCard] at hp
    rcases hp with ⟨⟨⟨_, hAcard⟩, ⟨_, hBcard⟩⟩, hdisjAB, hgap⟩
    dsimp only [Z2, coef₂, T₀, q, p_vert]
    exact H3_bound2_pt hc₂ hC hc2C4 rfl hn_gt_M6 hn1 hn_pos hk_pos hm_pos hlogn_ge1 hlogn_pos
      hk_lb hm_lb hAcard hBcard hdisjAB hgap
  have hBad_pt : ∀ G : SimpleGraph (Fin n),
      (if ∃ U : Finset (Fin n), U.card = k ∧
          (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
          (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
            m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)
        then (1 : ℝ) else 0) *
      (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) ≤
      (∑ p ∈ BadTriples,
        (if Z1 p.1 p.2.1 p.2.2 G ≤
            c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) +
      (∑ p ∈ BadPairs,
        (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) := by
    intro G
    have hwG := hw_nonneg G
    by_cases hG : ∃ U : Finset (Fin n), U.card = k ∧
        (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
        (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
          m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)
    · rw [if_pos hG, one_mul]
      have hnn1 : ∀ p' ∈ BadTriples, 0 ≤
          (if Z1 p'.1 p'.2.1 p'.2.2 G ≤
              c₂ * ((p'.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
            then (1 : ℝ) else 0) *
          (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
        fun p' _ => mul_nonneg (ite_nonneg zero_le_one le_rfl) hwG
      have hnn2 : ∀ p' ∈ BadPairs, 0 ≤
          (if Z2 p'.1 p'.2 G ≤ -T₀ then (1 : ℝ) else 0) *
          (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
        fun p' _ => mul_nonneg (ite_nonneg zero_le_one le_rfl) hwG
      rcases hstruct G hG with ⟨p, hp, hZ1⟩ | ⟨p, hp, hZ2⟩
      · have hle1 : (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) ≤
            ∑ p' ∈ BadTriples,
              (if Z1 p'.1 p'.2.1 p'.2.2 G ≤
                  c₂ * ((p'.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
                then (1 : ℝ) else 0) *
              (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
          calc (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)
              = (if Z1 p.1 p.2.1 p.2.2 G ≤
                    c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
                  then (1 : ℝ) else 0) *
                (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
                rw [if_pos hZ1, one_mul]
            _ ≤ ∑ p' ∈ BadTriples,
                  (if Z1 p'.1 p'.2.1 p'.2.2 G ≤
                      c₂ * ((p'.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
                    then (1 : ℝ) else 0) *
                  (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
                Finset.single_le_sum hnn1 hp
        have hle2 : 0 ≤ ∑ p' ∈ BadPairs,
            (if Z2 p'.1 p'.2 G ≤ -T₀ then (1 : ℝ) else 0) *
            (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
          Finset.sum_nonneg hnn2
        linarith
      · have hle1 : 0 ≤ ∑ p' ∈ BadTriples,
            (if Z1 p'.1 p'.2.1 p'.2.2 G ≤
                c₂ * ((p'.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
              then (1 : ℝ) else 0) *
            (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
          Finset.sum_nonneg hnn1
        have hle2 : (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) ≤
            ∑ p' ∈ BadPairs,
              (if Z2 p'.1 p'.2 G ≤ -T₀ then (1 : ℝ) else 0) *
              (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
          calc (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)
              = (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
                (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) := by
                rw [if_pos hZ2, one_mul]
            _ ≤ ∑ p' ∈ BadPairs,
                  (if Z2 p'.1 p'.2 G ≤ -T₀ then (1 : ℝ) else 0) *
                  (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e) :=
                Finset.single_le_sum hnn2 hp
        linarith
    · rw [if_neg hG, zero_mul]
      refine add_nonneg ?_ ?_
      · exact Finset.sum_nonneg fun p' _ => mul_nonneg (ite_nonneg (zero_le_one : (0 : ℝ) ≤ 1) le_rfl) hwG
      · exact Finset.sum_nonneg fun p' _ => mul_nonneg (ite_nonneg (zero_le_one : (0 : ℝ) ≤ 1) le_rfl) hwG
  have hTriples_card : (BadTriples.card : ℝ) ≤ (n : ℝ) ^ k := by
    have hsub : BadTriples.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_product, Finset.card_product] at hsub
    have hmul : ((Finset.univ : Finset (Fin n)).powersetCard m).card *
        (((Finset.univ : Finset (Fin n)).powersetCard m).card *
        ((Finset.univ : Finset (Fin n)).powersetCard (k - 2 * m)).card) ≤ n ^ k := by
      have h1 := card_powersetCard_le_pow n m hn1
      have h2 := card_powersetCard_le_pow n (k - 2 * m) hn1
      calc _ ≤ n ^ m * (n ^ m * n ^ (k - 2 * m)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h1 h2)
        _ = n ^ (m + (m + (k - 2 * m))) := by rw [← pow_add, ← pow_add]
        _ = n ^ k := by congr 1; omega
    exact_mod_cast hsub.trans hmul
  have hPairs_card : (BadPairs.card : ℝ) ≤ (n : ℝ) ^ k := by
    have hsub : BadPairs.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard m ×ˢ
        (Finset.univ : Finset (Fin n)).powersetCard m).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_product] at hsub
    have hmul : ((Finset.univ : Finset (Fin n)).powersetCard m).card *
        ((Finset.univ : Finset (Fin n)).powersetCard m).card ≤ n ^ k := by
      have h1 := card_powersetCard_le_pow n m hn1
      calc _ ≤ n ^ m * n ^ m := Nat.mul_le_mul h1 h1
        _ = n ^ (m + m) := by rw [← pow_add]
        _ ≤ n ^ k := Nat.pow_le_pow_right hn1 (by omega)
    exact_mod_cast hsub.trans hmul
  have hnk_exp : (n : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (n : ℝ)) := by
    rw [← Real.rpow_natCast (n : ℝ) k, Real.rpow_def_of_pos hn_pos, mul_comm]
  have hsum_eq :
      (∑ G : SimpleGraph (Fin n),
        (if ∃ U : Finset (Fin n), U.card = k ∧
            (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
            (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
              k / (Nat.log 2 k + 1) ≤ (U.filter (· ≤ a)).card ∧
              k / (Nat.log 2 k + 1) ≤ (U.filter (b ≤ ·)).card)
          then (1 : ℝ) else 0) *
        (∏ e ∈ E,
          if G.Adj e.1 e.2
          then (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n))
          else 1 - (1 / 4 + (e.1 : ℝ) / (2 * n)) * (1 / 4 + (e.2 : ℝ) / (2 * n)))) =
      (∑ G : SimpleGraph (Fin n),
        (if ∃ U : Finset (Fin n), U.card = k ∧
            (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
            (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
              m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) := by
    refine Finset.sum_congr rfl fun G _ => ?_
    congr 1
    rw [← Finset.prod_coe_sort E]
  rw [hsum_eq]
  calc (∑ G : SimpleGraph (Fin n),
        (if ∃ U : Finset (Fin n), U.card = k ∧
            (∃ d : ℕ, ∀ u ∈ U, (U.filter (fun v => G.Adj u v)).card = d) ∧
            (∃ a b : Fin n, a < b ∧ c₂ * (k : ℝ) ^ (3 / 2 : ℝ) ≤ (b : ℝ) - (a : ℝ) ∧
              m ≤ (U.filter (· ≤ a)).card ∧ m ≤ (U.filter (b ≤ ·)).card)
          then (1 : ℝ) else 0) *
        (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e))
      ≤ (∑ p ∈ BadTriples, ∑ G : SimpleGraph (Fin n),
          (if Z1 p.1 p.2.1 p.2.2 G ≤
              c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
            then (1 : ℝ) else 0) *
          (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) +
        (∑ p ∈ BadPairs, ∑ G : SimpleGraph (Fin n),
          (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
          (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) := by
        calc _ ≤ ∑ G : SimpleGraph (Fin n),
              ((∑ p ∈ BadTriples,
                  (if Z1 p.1 p.2.1 p.2.2 G ≤
                      c₂ * ((p.2.2.card : ℕ) : ℝ) * (m : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / (16 * (n : ℝ))
                    then (1 : ℝ) else 0) *
                  (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e)) +
                (∑ p ∈ BadPairs,
                  (if Z2 p.1 p.2 G ≤ -T₀ then (1 : ℝ) else 0) *
                  (∏ e : {p : Fin n × Fin n // p ∈ E}, if G.Adj e.1.1 e.1.2 then q e else 1 - q e))) :=
                Finset.sum_le_sum fun G _ => hBad_pt G
          _ = _ := by
                rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := BadPairs)]
    _ ≤ (∑ _ ∈ BadTriples, Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ))) +
          (∑ _ ∈ BadPairs, Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ))) :=
        add_le_add (Finset.sum_le_sum h1_bound) (Finset.sum_le_sum h2_bound)
    _ = ((BadTriples.card : ℝ) + (BadPairs.card : ℝ)) * Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
    _ ≤ (2 * (n : ℝ) ^ k) * Real.exp (-4 * (k : ℝ) * Real.log (n : ℝ)) := by gcongr; linarith
    _ = 2 * Real.exp (-3 * (k : ℝ) * Real.log (n : ℝ)) := by
        rw [hnk_exp, mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 2 * Real.exp (-3 * Real.log (n : ℝ)) := by
        gcongr
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        nlinarith
    _ = 2 / (n : ℝ) ^ 3 := by
        have h3 : -3 * Real.log (n : ℝ) = -(((3 : ℕ) : ℝ) * Real.log (n : ℝ)) := by push_cast; ring
        rw [h3, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn_pos, ← div_eq_mul_inv]
    _ < 1 / (2 * (n : ℝ) ^ 2) := by
        rw [div_lt_div_iff₀ (by positivity) (by positivity)]
        have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 5 ≤ n)
        have hmul : 4 * (n : ℝ) ^ 2 < (n : ℝ) * (n : ℝ) ^ 2 :=
          mul_lt_mul_of_pos_right (by linarith) (by positivity)
        linarith [show (n : ℝ) * (n : ℝ) ^ 2 = (n : ℝ) ^ 3 by ring]

end E82H3

theorem OMA.solution : type_of% @Erdos82.erdos_82.variants.F_upper_bound :=
  OMA.R_Erdos82_erdos_82_variants_F_upper_bound_R1.main E82H1.proof E82H2.proof E82H3.proof
