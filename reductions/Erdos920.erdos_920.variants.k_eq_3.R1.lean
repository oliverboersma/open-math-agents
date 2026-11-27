import FormalConjectures.ErdosProblems.«920»

-- Reduction Erdos920.erdos_920.variants.k_eq_3.R1 of Erdős Problem 920 — k eq 3
-- Credit: @ptc-prover-bot
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# f₃(n) ≍ √(n / log n): the two classical inputs

`f 3 n` is the largest chromatic number of a triangle-free graph on `n` vertices.
* `H1` (Kim 1995, *The Ramsey number R(3,t) has order of magnitude t²/log t*, Random Structures
  Algorithms 7): for large `n` there is a triangle-free graph on `n` vertices with independence
  number `≤ C √(n log n)`. Its colour classes are independent, so it needs `≥ √(n / log n) / C`
  colours. This is the deep (probabilistic) input.
* `H2` (Ajtai–Komlós–Szemerédi 1980, Shearer 1983): every triangle-free graph on `m` vertices has an
  independent set of size `≥ c √(m log m)`.

`main` proves the upper bound from `H2` by greedy colouring: while more than `√n` vertices remain,
remove an independent set of size `≥ (c/2) √(log n) √|S|`; on at most `√n` vertices use
`α ≥ b √|S|`. A potential argument (`√(m - i) ≤ √m - a/2` when `i ≥ a √m`) bounds the number of
colours by `2√n / a + 2 n^{1/4} / b ≪ √(n / log n)`. The lower bound is `χ(G) ≥ n / α(G)` for the
graph of `H1`.
-/

namespace OMA.R_Erdos920_erdos_920_variants_k_eq_3_R1

open Real Filter Finset

/-- Kim (1995): triangle-free graphs on `n` vertices with independence number `O(√(n log n))`. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧
    ∀ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) → (s.card : ℝ) ≤ C * √((n : ℝ) * log n)

/-- Every triangle-free graph on `m` vertices has an independent set of size `≫ √(m log m)`. -/
def H2 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
      c * √((Fintype.card V : ℝ) * log (Fintype.card V)) ≤ s.card

/-- `H2` inside any vertex set `S`. -/
lemma H2_finset (c : ℝ) (hH : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
      ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧
        c * √((Fintype.card V : ℝ) * log (Fintype.card V)) ≤ s.card)
    {V : Type} (G : SimpleGraph V) (hG : G.CliqueFree 3) (S : Finset V) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ c * √((S.card : ℝ) * log S.card) ≤ I.card := by
  classical
  have hG' : (G.induce (S : Set V)).CliqueFree 3 := hG.comap (SimpleGraph.Embedding.induce _).isContained
  obtain ⟨s, hs, hcard⟩ := hH (S : Set V) (G.induce (S : Set V)) hG'
  refine ⟨s.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  · intro x hx y hy hxy
    simp only [coe_map, Function.Embedding.coe_subtype, Set.mem_image, mem_coe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hs hx' hy' (fun h => hxy (congrArg Subtype.val h))
  · rw [card_map]
    have : Fintype.card (S : Set V) = S.card := by simp
    rw [this] at hcard
    exact hcard

/-- `√(m - i) ≤ √m - a/2` once `a √m ≤ i ≤ m`. -/
lemma sqrt_step {a m i : ℝ} (ha : 0 < a) (hm0 : 0 < m) (hi : i ≤ m) (hai : a * √m ≤ i) :
    2 * √(m - i) / a + 1 ≤ 2 * √m / a := by
  have hm : 0 ≤ m := le_trans (le_trans (mul_nonneg ha.le (sqrt_nonneg m)) hai) hi
  have hsm : √m * √m = m := mul_self_sqrt hm
  have hle : a ≤ √m := by
    have h := sqrt_pos.mpr hm0
    nlinarith
  have hkey : √(m - i) ≤ √m - a / 2 := by
    rw [show m - i = (m - i) by ring]
    calc √(m - i) ≤ √((√m - a / 2) ^ 2) := by
          apply sqrt_le_sqrt; nlinarith
      _ = √m - a / 2 := sqrt_sq (by linarith)
  rw [div_add_one ha.ne', div_le_div_iff_of_pos_right ha]
  linarith

/-- Greedy colouring by repeatedly removing a large independent set. -/
lemma color {V : Type} [DecidableEq V] (G : SimpleGraph V) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (M : ℕ)
    (hA : ∀ S : Finset V, M < S.card → ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ a * √(S.card : ℝ) ≤ I.card)
    (hB : ∀ S : Finset V, S.Nonempty → ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧ b * √(S.card : ℝ) ≤ I.card) :
    ∀ S : Finset V, ∃ (c : V → ℕ) (t : ℕ), (∀ v ∈ S, c v < t) ∧
      (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) ∧
      (t : ℝ) ≤ 2 * √(S.card : ℝ) / a + 2 * √(min (S.card : ℝ) M) / b := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, 0, by simp, by simp, by simp⟩
  have hm : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
  -- one step: colour an independent `I` with a fresh colour
  have step : ∀ I ⊆ S, I.Nonempty → G.IsIndepSet (I : Set V) →
      ∃ (c : V → ℕ) (t : ℕ), (∀ v ∈ S, c v < t) ∧ (∀ u ∈ S, ∀ v ∈ S, G.Adj u v → c u ≠ c v) ∧
      (t : ℝ) ≤ 2 * √((S.card : ℝ) - I.card) / a + 2 * √(min ((S.card : ℝ) - I.card) M) / b + 1 := by
    intro I hIS hIne hI
    obtain ⟨c, t, h1, h2, h3⟩ := ih (S \ I) (sdiff_ssubset hIS hIne)
    have hcard : ((S \ I).card : ℝ) = (S.card : ℝ) - I.card := by
      rw [card_sdiff_of_subset hIS, Nat.cast_sub (card_le_card hIS)]
    refine ⟨fun v => if v ∈ I then t else c v, t + 1, ?_, ?_, ?_⟩
    · intro v hv
      by_cases hvI : v ∈ I
      · simp [hvI]
      · simp only [hvI, if_false]; exact Nat.lt_succ_of_lt (h1 v (mem_sdiff.mpr ⟨hv, hvI⟩))
    · intro u hu v hv huv
      by_cases huI : u ∈ I <;> by_cases hvI : v ∈ I
      · exact absurd huv (hI (mem_coe.mpr huI) (mem_coe.mpr hvI) (G.ne_of_adj huv))
      · simp only [huI, hvI, if_true, if_false]; exact (h1 v (mem_sdiff.mpr ⟨hv, hvI⟩)).ne'
      · simp only [huI, hvI, if_true, if_false]; exact (h1 u (mem_sdiff.mpr ⟨hu, huI⟩)).ne
      · simp only [huI, hvI, if_false]
        exact h2 u (mem_sdiff.mpr ⟨hu, huI⟩) v (mem_sdiff.mpr ⟨hv, hvI⟩) huv
    · rw [hcard] at h3; push_cast; linarith
  have hpos : ∀ e : ℝ, 0 < e → e * √(S.card : ℝ) ≤ 0 → False := fun e he h =>
    by nlinarith [mul_pos he (sqrt_pos.mpr hm)]
  rcases Nat.lt_or_ge M S.card with hbig | hsmall
  · obtain ⟨I, hIS, hI, hai⟩ := hA S hbig
    have hIne : I.Nonempty := by
      rw [← card_pos]; by_contra h0; push Not at h0
      exact hpos a ha (by have : (I.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp h0
                          linarith)
    obtain ⟨c, t, h1, h2, h3⟩ := step I hIS hIne hI
    refine ⟨c, t, h1, h2, ?_⟩
    have him : (I.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hIS
    have hs := sqrt_step ha hm him hai
    have hmin : min ((S.card : ℝ) - I.card) M ≤ min (S.card : ℝ) M :=
      min_le_min_right _ (by linarith [(Nat.cast_nonneg I.card : (0 : ℝ) ≤ I.card)])
    have hsq : 2 * √(min ((S.card : ℝ) - I.card) M) / b ≤ 2 * √(min (S.card : ℝ) M) / b := by
      apply div_le_div_of_nonneg_right _ hb.le
      exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt hmin) (by norm_num)
    linarith
  · obtain ⟨I, hIS, hI, hbi⟩ := hB S hne
    have hIne : I.Nonempty := by
      rw [← card_pos]; by_contra h0; push Not at h0
      exact hpos b hb (by have : (I.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.mp h0
                          linarith)
    obtain ⟨c, t, h1, h2, h3⟩ := step I hIS hIne hI
    refine ⟨c, t, h1, h2, ?_⟩
    have him : (I.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hIS
    have hMR : (S.card : ℝ) ≤ M := by exact_mod_cast hsmall
    have hI0 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
    rw [min_eq_left hMR, min_eq_left (by linarith)] at *
    have hs := sqrt_step hb hm him hbi
    have hfirst : 2 * √((S.card : ℝ) - I.card) / a ≤ 2 * √(S.card : ℝ) / a := by
      apply div_le_div_of_nonneg_right _ ha.le
      exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by linarith)) (by norm_num)
    linarith

lemma chrom_le {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) (h : G.Colorable t) (hG : G.CliqueFree 3)
    (x : ℕ) (hx : G.chromaticNumber = (x : ℕ∞)) : x ≤ t := by
  have h1 : G.chromaticNumber ≤ t := h.chromaticNumber_le
  rw [hx] at h1
  exact_mod_cast h1

/-- Upper bound: `f 3 n ≤ K √(n / log n)` for large `n`, from `H2`. -/
lemma upper (h2 : H2) : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
    (Erdos920.f 3 n : ℝ) ≤ K * √((n : ℝ) / log n) := by
  classical
  obtain ⟨c, hc, hH⟩ := h2
  set b : ℝ := min c (1 / 2) with hbdef
  have hb : 0 < b := lt_min hc (by norm_num)
  refine ⟨4 / c + 2 * √2 / b, by positivity, ?_⟩
  rw [eventually_atTop]
  refine ⟨16, fun n hn => ?_⟩
  set s := Nat.sqrt n with hsdef
  have hs2 : 2 ≤ s := by rw [hsdef, Nat.le_sqrt]; omega
  have hs4 : n ≤ s ^ 4 := by
    have := Nat.lt_succ_sqrt n
    rw [← hsdef] at this
    have h4 : 4 ≤ s ^ 2 := by nlinarith
    have : (s + 1) * (s + 1) ≤ s ^ 4 := by nlinarith
    rw [Nat.succ_eq_add_one] at *
    omega
  have hnR : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 < log (n : ℝ) := log_pos (by linarith)
  -- log of anything above `s` is at least `log n / 4`
  have hlogS : ∀ m : ℕ, s < m → log (n : ℝ) / 4 ≤ log (m : ℝ) := by
    intro m hm
    have h1 : (n : ℝ) ≤ (m : ℝ) ^ 4 := by
      have : n ≤ m ^ 4 := le_trans hs4 (Nat.pow_le_pow_left hm.le 4)
      exact_mod_cast this
    have h2 := log_le_log hnpos h1
    rw [log_pow] at h2
    push_cast at h2
    linarith
  set a : ℝ := c / 2 * √(log (n : ℝ)) with hadef
  have ha : 0 < a := by positivity
  have hfn : Erdos920.f 3 n ≤ ⌊(4 / c + 2 * √2 / b) * √((n : ℝ) / log n)⌋₊ := by
    unfold Erdos920.f
    apply csSup_le
    · have hne : (⊥ : SimpleGraph (Fin n)).chromaticNumber ≠ ⊤ :=
        SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨_, SimpleGraph.colorable_of_fintype _⟩
      exact ⟨_, ⊥, SimpleGraph.cliqueFree_bot (by omega), (ENat.natCast_toNat hne).symm⟩
    rintro x ⟨G, hG, hx⟩
    have hA : ∀ S : Finset (Fin n), s < S.card →
        ∃ I ⊆ S, G.IsIndepSet (I : Set (Fin n)) ∧ a * √(S.card : ℝ) ≤ I.card := by
      intro S hS
      obtain ⟨I, hIS, hI, hc'⟩ := H2_finset c hH G hG S
      refine ⟨I, hIS, hI, le_trans ?_ hc'⟩
      have hl := hlogS S.card hS
      have hSpos : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      rw [hadef, sqrt_mul' _ (by linarith [hlogn] : (0 : ℝ) ≤ log S.card)]
      have : √(log (n : ℝ)) / 2 ≤ √(log (S.card : ℝ)) := by
        rw [show √(log (n : ℝ)) / 2 = √(log (n : ℝ) / 4) by
          rw [sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
        exact sqrt_le_sqrt hl
      have hsS := sqrt_nonneg (S.card : ℝ)
      calc c / 2 * √(log (n : ℝ)) * √(S.card : ℝ) = c * (√(log (n : ℝ)) / 2) * √(S.card : ℝ) := by
            ring
        _ ≤ c * √(log (S.card : ℝ)) * √(S.card : ℝ) := by gcongr
        _ = c * (√(S.card : ℝ) * √(log (S.card : ℝ))) := by ring
    have hB : ∀ S : Finset (Fin n), S.Nonempty →
        ∃ I ⊆ S, G.IsIndepSet (I : Set (Fin n)) ∧ b * √(S.card : ℝ) ≤ I.card := by
      intro S hS
      rcases Nat.lt_or_ge S.card 3 with hlt | hge
      · obtain ⟨v, hv⟩ := hS
        refine ⟨{v}, singleton_subset_iff.mpr hv, by simp, ?_⟩
        have hle : (S.card : ℝ) ≤ 2 := by exact_mod_cast (by omega : S.card ≤ 2)
        have h1 : √(S.card : ℝ) ≤ 2 := by
          rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
          exact sqrt_le_sqrt (by linarith)
        have hb2 : b ≤ 1 / 2 := min_le_right _ _
        simp only [card_singleton, Nat.cast_one]
        nlinarith [sqrt_nonneg (S.card : ℝ)]
      · obtain ⟨I, hIS, hI, hc'⟩ := H2_finset c hH G hG S
        refine ⟨I, hIS, hI, le_trans ?_ hc'⟩
        have h3 : (3 : ℝ) ≤ S.card := by exact_mod_cast hge
        have hl1 : 1 ≤ log (S.card : ℝ) := by
          rw [le_log_iff_exp_le (by linarith)]
          have := Real.exp_one_lt_d9
          linarith
        have hbc : b ≤ c := min_le_left _ _
        have : √(S.card : ℝ) ≤ √((S.card : ℝ) * log S.card) :=
          sqrt_le_sqrt (by nlinarith)
        nlinarith [sqrt_nonneg (S.card : ℝ)]
    obtain ⟨col, t, h1, h2, h3⟩ := color G a b ha hb s hA hB univ
    have hcol : G.Colorable t :=
      ⟨SimpleGraph.Coloring.mk (fun v => ⟨col v, h1 v (mem_univ v)⟩)
        (fun {u v} huv h => h2 u (mem_univ u) v (mem_univ v) huv (congrArg Fin.val h))⟩
    have hxt := chrom_le G t hcol hG x hx
    refine hxt.trans (Nat.le_floor (h3.trans ?_))
    -- numerics
    rw [card_univ, Fintype.card_fin]
    have hmin : min (n : ℝ) (s : ℝ) ≤ s := min_le_right _ _
    have hsR : (s : ℝ) ≤ √(n : ℝ) := by
      rw [le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast Nat.sqrt_le' n
    have hsqrt_n : 0 < √(n : ℝ) := sqrt_pos.mpr hnpos
    have hsl : 0 < √(log (n : ℝ)) := sqrt_pos.mpr hlogn
    have hQ : √((n : ℝ) / log n) = √(n : ℝ) / √(log (n : ℝ)) := sqrt_div' _ hlogn.le
    -- first term
    have e1 : 2 * √(n : ℝ) / a = 4 / c * √((n : ℝ) / log n) := by
      rw [hQ, hadef]; field_simp; ring
    -- second term: √s ≤ √2 √(n / log n), since log n ≤ 2 √n
    have hlog2 : log (n : ℝ) ≤ 2 * √(n : ℝ) := by
      have := log_le_sub_one_of_pos hsqrt_n
      rw [log_sqrt hnpos.le] at this
      linarith
    have hss : √(min (n : ℝ) (s : ℝ)) ≤ √2 * √((n : ℝ) / log n) := by
      have hA1 : √(min (n : ℝ) (s : ℝ)) ≤ √(√(n : ℝ)) := sqrt_le_sqrt (hmin.trans hsR)
      have hA2 : √(√(n : ℝ)) ≤ √2 * √((n : ℝ) / log n) := by
        rw [← sqrt_mul (by norm_num)]
        apply sqrt_le_sqrt
        rw [mul_div_assoc', le_div_iff₀ hlogn]
        have hsq : √(n : ℝ) * √(n : ℝ) = n := mul_self_sqrt hnpos.le
        nlinarith
      exact hA1.trans hA2
    have e2 : 2 * √(min (n : ℝ) (s : ℝ)) / b ≤ 2 * √2 / b * √((n : ℝ) / log n) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hb]
      nlinarith
    rw [e1, add_mul]
    linarith
  calc (Erdos920.f 3 n : ℝ) ≤ (⌊(4 / c + 2 * √2 / b) * √((n : ℝ) / log n)⌋₊ : ℝ) := by
        exact_mod_cast hfn
    _ ≤ _ := Nat.floor_le (by positivity)

/-- Lower bound: `√(n / log n) ≤ C f 3 n` for large `n`, from `H1`. -/
lemma lower (h1 : H1) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
    √((n : ℝ) / log n) ≤ C * Erdos920.f 3 n := by
  classical
  obtain ⟨C, hC, hev⟩ := h1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 2] with n ⟨G, hG, hα⟩ hn2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 < log (n : ℝ) := log_pos (by linarith)
  set t := G.chromaticNumber.toNat with htdef
  have hne : G.chromaticNumber ≠ ⊤ :=
    SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨_, SimpleGraph.colorable_of_fintype _⟩
  have hcol : G.Colorable t := by
    rw [htdef]; exact SimpleGraph.colorable_chromaticNumber_of_fintype G
  -- t ≤ f 3 n
  have htf : t ≤ Erdos920.f 3 n := by
    unfold Erdos920.f
    apply le_csSup
    · refine ⟨n, ?_⟩
      rintro x ⟨H, -, hx⟩
      have : H.chromaticNumber ≤ Fintype.card (Fin n) := SimpleGraph.chromaticNumber_le_card
      rw [hx, Fintype.card_fin] at this
      exact_mod_cast this
    · exact ⟨G, hG, (ENat.natCast_toNat hne).symm⟩
  -- n ≤ t · C √(n log n): colour classes are independent
  obtain ⟨col⟩ := hcol
  have hsum : (n : ℝ) ≤ t * (C * √((n : ℝ) * log n)) := by
    have hcard := card_eq_sum_card_fiberwise (f := fun v : Fin n => col v) (s := univ)
      (t := (univ : Finset (Fin t))) (fun _ _ => mem_univ _)
    rw [card_univ, Fintype.card_fin] at hcard
    have hb : ∀ i ∈ (univ : Finset (Fin t)),
        (((univ : Finset (Fin n)).filter (fun v => col v = i)).card : ℝ) ≤ C * √((n : ℝ) * log n) := by
      intro i _
      apply hα
      intro u hu v hv huv hadj
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hu hv
      exact col.valid hadj (hu.trans hv.symm)
    have := sum_le_sum hb
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc (n : ℝ) = ∑ i : Fin t, (((univ : Finset (Fin n)).filter (fun v => col v = i)).card : ℝ) := by
          exact_mod_cast hcard
      _ ≤ _ := this
  have hR : 0 < √((n : ℝ) * log n) := sqrt_pos.mpr (mul_pos hnpos hlogn)
  have hprod : √((n : ℝ) / log n) * √((n : ℝ) * log n) = n := by
    rw [← sqrt_mul (div_nonneg hnpos.le hlogn.le)]
    rw [show (n : ℝ) / log n * (n * log n) = n ^ 2 by field_simp]
    exact sqrt_sq hnpos.le
  have htR : (t : ℝ) ≤ Erdos920.f 3 n := by exact_mod_cast htf
  have key : √((n : ℝ) / log n) ≤ C * t := by
    by_contra hcon
    push Not at hcon
    have : C * t * √((n : ℝ) * log n) < √((n : ℝ) / log n) * √((n : ℝ) * log n) :=
      mul_lt_mul_of_pos_right hcon hR
    rw [hprod] at this
    nlinarith
  calc √((n : ℝ) / log n) ≤ C * t := key
    _ ≤ C * Erdos920.f 3 n := mul_le_mul_of_nonneg_left htR hC.le

theorem main : H1 → H2 → type_of% @Erdos920.erdos_920.variants.k_eq_3 := by
  intro h1 h2
  obtain ⟨K, hK, hup⟩ := upper h2
  obtain ⟨C, hC, hlo⟩ := lower h1
  have e : ∀ n : ℕ, ((n : ℝ) / log n) ^ (1 / 2 : ℝ) = √((n : ℝ) / log n) := fun n =>
    (sqrt_eq_rpow _).symm
  simp_rw [e]
  refine ⟨Asymptotics.IsBigO.of_bound K ?_, Asymptotics.IsBigO.of_bound C ?_⟩
  · filter_upwards [hup] with n hn
    rw [Real.norm_natCast, Real.norm_of_nonneg (sqrt_nonneg _)]
    exact hn
  · filter_upwards [hlo] with n hn
    rw [Real.norm_natCast, Real.norm_of_nonneg (sqrt_nonneg _)]
    exact hn

end OMA.R_Erdos920_erdos_920_variants_k_eq_3_R1
