import OMAReductions.R_Erdos920_erdos_920_variants_k_eq_3_R1

-- Problem: Erdos920.erdos_920.variants.k_eq_3.R1.H2
-- Credit: @ptc-prover-bot (the owner of the agent is credited as the solver)

/-! Every triangle-free graph on `m` vertices has an independent set of size `≥ √(m log m) / 15`.
Shearer (1983): in every vertex set `S` some independent set has size `≥ |S| f(d) + g(d)(P(S) - |S| d)`
for every `d > 0` (`P` = ordered adjacent pairs, `f(x) = ∫₀¹ (1-t)/(1+(x-1)t) dt`, `g = f'`), with
`f(D) ≥ (log D - 1)/D`. Take `s = √(m log m)`: if the average degree is `≥ s`, a neighbourhood of a
vertex of degree `≥ s` is independent; otherwise Shearer at `d = s` gives `≥ m (log s - 1)/s ≥ s/4`
once `log m ≥ 4`; for `log m < 4`, `m log m < 225` and one vertex suffices. -/


namespace OMA.Erdos920H2.Shearer

open Real intervalIntegral MeasureTheory Set

noncomputable def f (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (1 - t) / (1 + (x - 1) * t)
noncomputable def g (x : ℝ) : ℝ := -∫ t in (0 : ℝ)..1, t * (1 - t) / (1 + (x - 1) * t) ^ 2

lemma den_pos {x t : ℝ} (hx : 0 < x) (ht : t ∈ uIcc (0 : ℝ) 1) : 0 < 1 + (x - 1) * t := by
  rw [uIcc_of_le zero_le_one] at ht
  obtain ⟨h0, h1⟩ := ht
  rcases eq_or_lt_of_le h0 with rfl | h
  · norm_num
  · nlinarith [mul_pos hx h]

lemma int_A {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => (1 - t) / (1 + (x - 1) * t)) volume 0 1 :=
  ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
    (fun t ht => (den_pos hx ht).ne'))

lemma int_B {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => t * (1 - t) / (1 + (x - 1) * t) ^ 2) volume 0 1 :=
  ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
    (fun t ht => (pow_pos (den_pos hx ht) 2).ne'))

/-- `g ≤ 0`. -/
lemma g_nonpos {x : ℝ} (hx : 0 < x) : g x ≤ 0 := by
  unfold g
  rw [neg_nonpos]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro t ht
  have := den_pos hx (by rwa [uIcc_of_le zero_le_one])
  apply div_nonneg _ (by positivity)
  exact mul_nonneg ht.1 (by linarith [ht.2])

/-- Tangent-line inequality (convexity of `f`). -/
lemma tangent {x d : ℝ} (hx : 0 < x) (hd : 0 < d) : f d + g d * (x - d) ≤ f x := by
  have e : f d + g d * (x - d) = ∫ t in (0 : ℝ)..1,
      ((1 - t) / (1 + (d - 1) * t) - (x - d) * (t * (1 - t) / (1 + (d - 1) * t) ^ 2)) := by
    rw [intervalIntegral.integral_sub (int_A hd) ((int_B hd).const_mul _),
      intervalIntegral.integral_const_mul]
    unfold f g; ring
  rw [e]
  apply intervalIntegral.integral_mono_on zero_le_one
    ((int_A hd).sub ((int_B hd).const_mul _)) (int_A hx)
  intro t ht
  have ha := den_pos hd (by rwa [uIcc_of_le zero_le_one])
  have hb := den_pos hx (by rwa [uIcc_of_le zero_le_one])
  set a := 1 + (d - 1) * t
  set b := 1 + (x - 1) * t
  have hc : 0 ≤ 1 - t := by linarith [ht.2]
  have hba : (x - d) * t = b - a := by simp only [a, b]; ring
  have key : (1 - t) / b - ((1 - t) / a - (x - d) * (t * (1 - t) / a ^ 2)) =
      (1 - t) * (b - a) ^ 2 / (a ^ 2 * b) := by
    rw [← hba]; field_simp; simp only [a, b]; ring
  have : 0 ≤ (1 - t) * (b - a) ^ 2 / (a ^ 2 * b) := by positivity
  linarith

/-- Shearer's differential equation: `(1 + d) f(d) - g(d) (d - d²) = 1`. -/
lemma ode {d : ℝ} (hd : 0 < d) : (1 + d) * f d - g d * (d - d ^ 2) = 1 := by
  have e : (1 + d) * f d - g d * (d - d ^ 2) = ∫ t in (0 : ℝ)..1,
      ((1 + d) * ((1 - t) / (1 + (d - 1) * t)) +
        (d - d ^ 2) * (t * (1 - t) / (1 + (d - 1) * t) ^ 2)) := by
    rw [intervalIntegral.integral_add ((int_A hd).const_mul _) ((int_B hd).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    unfold f g; ring
  rw [e]
  have hF : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => t * (d + 1 - t) / (1 + (d - 1) * t))
      ((1 + d) * ((1 - t) / (1 + (d - 1) * t)) +
        (d - d ^ 2) * (t * (1 - t) / (1 + (d - 1) * t) ^ 2)) t := by
    intro t ht
    have hv := den_pos hd ht
    have h1 : HasDerivAt (fun t : ℝ => t * (d + 1 - t)) (1 * (d + 1 - t) + t * (0 - 1)) t :=
      (hasDerivAt_id t).mul ((hasDerivAt_const t (d + 1)).sub (hasDerivAt_id t))
    have h2 : HasDerivAt (fun t : ℝ => 1 + (d - 1) * t) (0 + (d - 1) * 1) t :=
      (hasDerivAt_const t 1).add ((hasDerivAt_id t).const_mul (d - 1))
    have hv' := hv.ne'
    refine (h1.div h2 hv').congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (((int_A hd).const_mul _).add ((int_B hd).const_mul _))]
  have : (1 : ℝ) + (d - 1) * 1 = d := by ring
  rw [this]; field_simp; ring

/-- The tangent line at `d` takes a value at most `1` at `x = 0`. -/
lemma at_zero {d : ℝ} (hd : 0 < d) : f d - d * g d ≤ 1 := by
  have e : f d - d * g d = ∫ t in (0 : ℝ)..1,
      ((1 - t) / (1 + (d - 1) * t) + d * (t * (1 - t) / (1 + (d - 1) * t) ^ 2)) := by
    rw [intervalIntegral.integral_add (int_A hd) ((int_B hd).const_mul _),
      intervalIntegral.integral_const_mul]
    unfold f g; ring
  rw [e]
  refine le_trans (intervalIntegral.integral_mono_on (g := fun _ => (1 : ℝ)) zero_le_one
    ((int_A hd).add ((int_B hd).const_mul _)) intervalIntegrable_const ?_) (by simp)
  intro t ht
  have hy := den_pos hd (by rwa [uIcc_of_le zero_le_one])
  set y := 1 + (d - 1) * t with hydef
  have : (1 - t) / y + d * (t * (1 - t) / y ^ 2) = ((1 - t) * y + d * t * (1 - t)) / y ^ 2 := by
    field_simp
  rw [this, div_le_one (by positivity)]
  have : y ^ 2 - ((1 - t) * y + d * t * (1 - t)) = (d * t) ^ 2 := by rw [hydef]; ring
  nlinarith [sq_nonneg (d * t)]

/-- Lower bound: `f(D) ≥ (log D - 1) / D` for `D ≥ 1`. -/
lemma lower {D : ℝ} (hD : 1 ≤ D) : (Real.log D - 1) / D ≤ f D := by
  have hD0 : 0 < D := by linarith
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) / (1 + D * t)) volume 0 1 :=
    ContinuousOn.intervalIntegrable (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun t ht => by
        rw [uIcc_of_le zero_le_one] at ht
        nlinarith [ht.1]))
  have hmono : ∫ t in (0 : ℝ)..1, (1 - t) / (1 + D * t) ≤ f D := by
    apply intervalIntegral.integral_mono_on zero_le_one hint (int_A hD0)
    intro t ht
    have h1 := den_pos hD0 (by rwa [uIcc_of_le zero_le_one])
    apply div_le_div_of_nonneg_left (by linarith [ht.2]) h1
    linarith [ht.1]
  have hG : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun t => (1 + D) / D ^ 2 * Real.log (1 + D * t) - t / D) ((1 - t) / (1 + D * t)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hp : 0 < 1 + D * t := by nlinarith [ht.1]
    have h1 : HasDerivAt (fun t : ℝ => 1 + D * t) (0 + D * 1) t :=
      (hasDerivAt_const t 1).add ((hasDerivAt_id t).const_mul D)
    have h2 := ((h1.log hp.ne').const_mul ((1 + D) / D ^ 2)).sub ((hasDerivAt_id t).div_const D)
    have hp' := hp.ne'
    have hD' := hD0.ne'
    refine h2.congr_deriv ?_
    field_simp
    ring
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint
  simp only [mul_one, mul_zero, add_zero, Real.log_one, zero_div, sub_zero] at hval
  have hlog : Real.log D ≤ Real.log (1 + D) := Real.log_le_log hD0 (by linarith)
  have hl0 : 0 ≤ Real.log D := Real.log_nonneg hD
  have hcoef : 1 / D ≤ (1 + D) / D ^ 2 := by
    rw [div_le_div_iff₀ hD0 (by positivity)]; nlinarith
  have : (Real.log D - 1) / D ≤ (1 + D) / D ^ 2 * Real.log (1 + D) - 1 / D := by
    have h3 : Real.log D / D ≤ (1 + D) / D ^ 2 * Real.log (1 + D) := by
      calc Real.log D / D = 1 / D * Real.log D := by ring
        _ ≤ (1 + D) / D ^ 2 * Real.log D := mul_le_mul_of_nonneg_right hcoef hl0
        _ ≤ (1 + D) / D ^ 2 * Real.log (1 + D) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
    have : (Real.log D - 1) / D = Real.log D / D - 1 / D := by ring
    linarith
  linarith


end OMA.Erdos920H2.Shearer

open Finset

namespace OMA.Erdos920H2.Shearer

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ordered adjacent pairs inside `S`. -/
def P (S : Finset V) : ℕ := ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card

/-- Degree inside `S`. -/
def deg (S : Finset V) (u : V) : ℕ := (S.filter (G.Adj u)).card

lemma P_eq_sum (S : Finset V) : P G S = ∑ u ∈ S, deg G S u := by
  unfold P deg
  rw [card_filter, sum_product]
  apply sum_congr rfl; intro u _
  rw [card_filter]

lemma no_tri (hG : G.CliqueFree 3) {v a b : V} (ha : G.Adj v a) (hb : G.Adj v b) : ¬ G.Adj a b := by
  intro hab
  exact hG {v, a, b} (SimpleGraph.is3Clique_triple_iff.mpr ⟨ha, hb, hab⟩)

/-- Removing `v` and its neighbourhood removes at least `2 Σ_{u ~ v} deg u` ordered pairs. -/
lemma pairs_drop (hG : G.CliqueFree 3) (S : Finset V) (v : V) :
    P G (S \ insert v (S.filter (G.Adj v))) + 2 * ∑ u ∈ S.filter (G.Adj v), deg G S u ≤ P G S := by
  set N := S.filter (G.Adj v) with hN
  set S' := S \ insert v N with hS'
  set A := (S' ×ˢ S').filter (fun p => G.Adj p.1 p.2)
  set B1 := (N ×ˢ S).filter (fun p => G.Adj p.1 p.2)
  set B2 := (S ×ˢ N).filter (fun p => G.Adj p.1 p.2)
  have hB1 : B1.card = ∑ u ∈ N, deg G S u := by
    simp only [B1, deg]; rw [card_filter, sum_product]
    apply sum_congr rfl; intro u _; rw [card_filter]
  have hB2 : B2.card = B1.card := by
    apply card_bij (fun p _ => (p.2, p.1))
    · intro p hp; simp only [B1, B2, mem_filter, mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
    · intro p _ q _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · intro q hq; refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [B1, B2, mem_filter, mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2.symm⟩
  have hNS : N ⊆ S := filter_subset _ _
  have hS'S : S' ⊆ S := sdiff_subset
  have notN : ∀ x ∈ S', x ∉ N := fun x hx hxN => (mem_sdiff.mp hx).2 (mem_insert_of_mem hxN)
  have d1 : Disjoint A B1 := by
    rw [disjoint_left]; intro p hpA hpB
    simp only [A, B1, mem_filter, mem_product] at hpA hpB
    exact notN _ hpA.1.1 hpB.1.1
  have d2 : Disjoint (A ∪ B1) B2 := by
    rw [disjoint_left]; intro p hp hpB
    simp only [B2, mem_filter, mem_product] at hpB
    rcases mem_union.mp hp with hpA | hpB1
    · simp only [A, mem_filter, mem_product] at hpA
      exact notN _ hpA.1.2 hpB.1.2
    · simp only [B1, mem_filter, mem_product] at hpB1
      have h1 := (mem_filter.mp hpB1.1.1).2
      have h2 := (mem_filter.mp hpB.1.2).2
      exact no_tri G hG h1 h2 hpB1.2
  have hsub : A ∪ B1 ∪ B2 ⊆ (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) := by
    intro p hp
    simp only [A, B1, B2, mem_union, mem_filter, mem_product] at hp ⊢
    rcases hp with (h | h) | h
    · exact ⟨⟨hS'S h.1.1, hS'S h.1.2⟩, h.2⟩
    · exact ⟨⟨hNS h.1.1, h.1.2⟩, h.2⟩
    · exact ⟨⟨h.1.1, hNS h.1.2⟩, h.2⟩
  have := card_le_card hsub
  rw [card_union_of_disjoint d2, card_union_of_disjoint d1, hB2, hB1] at this
  unfold P
  linarith

/-- `Σ_v Σ_{u ~ v} deg u = Σ_u deg u ²`. -/
lemma sum_nbr_deg (S : Finset V) :
    ∑ v ∈ S, ∑ u ∈ S.filter (G.Adj v), (deg G S u : ℝ) = ∑ u ∈ S, (deg G S u : ℝ) ^ 2 := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl; intro u _
  rw [← sum_filter, sum_const, nsmul_eq_mul, sq]
  congr 1
  unfold deg
  congr 2
  ext w; simp only [mem_filter]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

variable (f g : ℝ → ℝ)

theorem shearer (hT : ∀ x d : ℝ, 0 < x → 0 < d → f d + g d * (x - d) ≤ f x)
    (hN : ∀ d : ℝ, 0 < d → g d ≤ 0)
    (hO : ∀ d : ℝ, 0 < d → (1 + d) * f d - g d * (d - d ^ 2) = 1)
    (hZ : ∀ d : ℝ, 0 < d → f d - d * g d ≤ 1)
    (hG : G.CliqueFree 3) (S : Finset V) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧
      ∀ d : ℝ, 0 < d → (S.card : ℝ) * f d + g d * (P G S - S.card * d) ≤ I.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
  by_cases hP : P G S = 0
  · -- no edges: S itself is independent
    refine ⟨S, subset_rfl, ?_, ?_⟩
    · intro a ha b hb _ hab
      have : (a, b) ∈ (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) :=
        mem_filter.mpr ⟨mem_product.mpr ⟨ha, hb⟩, hab⟩
      unfold P at hP
      rw [card_eq_zero] at hP
      rw [hP] at this; simp at this
    · intro d hd
      rw [hP]; push_cast
      have := hZ d hd
      have hn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      nlinarith
  · -- pick the vertex given by averaging
    have hSne : S.Nonempty := by
      rw [nonempty_iff_ne_empty]; rintro rfl; exact hP (by simp [P])
    set n : ℝ := (S.card : ℝ) with hn
    have hn0 : 0 < n := by rw [hn]; exact_mod_cast hSne.card_pos
    set Pr : ℝ := (P G S : ℝ) with hPr
    have hP0 : 0 < Pr := by rw [hPr]; exact_mod_cast Nat.pos_of_ne_zero hP
    set d0 : ℝ := Pr / n with hd0
    have hd0pos : 0 < d0 := div_pos hP0 hn0
    have hnd : n * d0 = Pr := by rw [hd0]; field_simp
    set F := f d0
    set Gs := g d0
    have hGs : Gs ≤ 0 := hN d0 hd0pos
    have hode := hO d0 hd0pos
    -- the averaged quantity
    set term : V → ℝ := fun v => 1 - (1 + (deg G S v : ℝ)) * F +
      Gs * (d0 + d0 * deg G S v - 2 * ∑ u ∈ S.filter (G.Adj v), (deg G S u : ℝ)) with hterm
    have hsumdeg : ∑ v ∈ S, (deg G S v : ℝ) = Pr := by rw [hPr, P_eq_sum]; push_cast; rfl
    have hCS : Pr ^ 2 ≤ n * ∑ u ∈ S, (deg G S u : ℝ) ^ 2 := by
      rw [← hsumdeg, hn]; exact sq_sum_le_card_mul_sum_sq
    have hsum : 0 ≤ ∑ v ∈ S, term v := by
      have e : ∑ v ∈ S, term v = n - (n + Pr) * F + Gs * (n * d0 + d0 * Pr -
          2 * ∑ u ∈ S, (deg G S u : ℝ) ^ 2) := by
        simp only [hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, sum_const,
          nsmul_eq_mul, mul_one, ← hn, hsumdeg, sum_nbr_deg]
      rw [e]
      have hsq : d0 * Pr ≤ ∑ u ∈ S, (deg G S u : ℝ) ^ 2 := by
        have : d0 * Pr * n = Pr ^ 2 := by rw [← hnd]; ring
        nlinarith
      have h1 : Gs * (n * d0 + d0 * Pr - 2 * ∑ u ∈ S, (deg G S u : ℝ) ^ 2) ≥
          Gs * (n * d0 + d0 * Pr - 2 * (d0 * Pr)) :=
        mul_le_mul_of_nonpos_left (by linarith) hGs
      have h2 : n - (n + Pr) * F + Gs * (n * d0 + d0 * Pr - 2 * (d0 * Pr)) =
          n * ((1 + d0) * F - Gs * (d0 - d0 ^ 2) - 1) * (-1) := by
        rw [← hnd]; ring
      rw [hode] at h2
      linarith
    obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, 0 ≤ term v := by
      by_contra hcon
      push Not at hcon
      have := sum_lt_sum_of_nonempty hSne (g := fun _ => (0 : ℝ)) hcon
      simp at this; linarith
    -- remove v and its neighbourhood
    set Nv := S.filter (G.Adj v) with hNv
    set S' := S \ insert v Nv with hS'
    have hvN : v ∉ Nv := fun h => G.irrefl (mem_filter.mp h).2
    have hins : insert v Nv ⊆ S := insert_subset hvS (filter_subset _ _)
    have hcard : S'.card + (1 + deg G S v) = S.card := by
      rw [hS', card_sdiff, inter_eq_left.mpr hins, card_insert_of_notMem hvN]
      have := card_le_card hins
      rw [card_insert_of_notMem hvN] at this
      unfold deg; rw [← hNv]; omega
    have hlt : S'.card < S.card := by omega
    obtain ⟨I', hI'S, hI'ind, hI'⟩ := ih S' (by rw [hS']; exact sdiff_ssubset hins ⟨v, mem_insert_self _ _⟩)
    have hdrop := pairs_drop G hG S v
    rw [← hNv, ← hS'] at hdrop
    have hvI' : v ∉ I' := fun h => (mem_sdiff.mp (hI'S h)).2 (mem_insert_self _ _)
    refine ⟨insert v I', insert_subset hvS (hI'S.trans sdiff_subset), ?_, ?_⟩
    · -- independence
      rw [coe_insert]
      refine Set.Pairwise.insert hI'ind (fun u hu _ => ?_)
      have huS' := hI'S (mem_coe.mp hu)
      have hnot : ¬ G.Adj v u := fun h =>
        (mem_sdiff.mp huS').2 (mem_insert_of_mem (mem_filter.mpr ⟨(mem_sdiff.mp huS').1, h⟩))
      exact ⟨hnot, fun h => hnot h.symm⟩
    · -- the bound, first at d0, then at any d through the tangent line
      have hId0 := hI' d0 hd0pos
      rw [card_insert_of_notMem hvI']
      have hcardR : (S'.card : ℝ) + (1 + deg G S v) = n := by rw [hn]; exact_mod_cast hcard
      have hdropR : (P G S' : ℝ) + 2 * ∑ u ∈ Nv, (deg G S u : ℝ) ≤ Pr := by
        rw [hPr]; exact_mod_cast hdrop
      have hstep : n * F ≤ (I'.card : ℝ) + 1 := by
        have hA : Gs * ((P G S' : ℝ) - S'.card * d0) ≥
            Gs * (Pr - 2 * ∑ u ∈ Nv, (deg G S u : ℝ) - S'.card * d0) :=
          mul_le_mul_of_nonpos_left (by linarith) hGs
        have hv' : 0 ≤ term v := hv
        simp only [hterm] at hv'
        rw [← hNv] at hv'
        have e : n = S'.card + 1 + deg G S v := by linarith
        have e2 : Pr = n * d0 := hnd.symm
        rw [e2] at hA
        rw [e] at hA ⊢
        nlinarith
      intro d hd
      have htan := hT d0 d hd0pos hd
      have : n * f d + g d * (Pr - n * d) = n * (f d + g d * (d0 - d)) := by rw [← hnd]; ring
      rw [this]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left htan hn0.le]

end OMA.Erdos920H2.Shearer


namespace OMA.Erdos920H2

open Real Finset OMA.Erdos920H2.Shearer

lemma exp4_lt : exp (4 : ℝ) < 55 := by
  have h := Real.exp_one_lt_d9
  have e : exp (4 : ℝ) = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h0 : 0 < exp (1 : ℝ) := exp_pos 1
  calc exp (1 : ℝ) ^ 4 < (2.7182818286 : ℝ) ^ 4 := by gcongr
    _ < 55 := by norm_num

theorem H2_proof : OMA.R_Erdos920_erdos_920_variants_k_eq_3_R1.H2 := by
  refine ⟨1 / 15, by norm_num, ?_⟩
  intro V _ G hG
  classical
  set m : ℕ := Fintype.card V with hmdef
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · refine ⟨∅, by simp, ?_⟩
    rw [hm0]; simp
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hlog0 : 0 ≤ log (m : ℝ) := log_nonneg hm1
  by_cases hsmall : log (m : ℝ) < 4
  · -- few vertices: a single vertex suffices
    have hV : Nonempty V := Fintype.card_pos_iff.mp hmpos
    obtain ⟨v⟩ := hV
    refine ⟨{v}, by simp, ?_⟩
    have hm55 : (m : ℝ) < 55 := by
      have := (log_lt_iff_lt_exp (by linarith)).mp hsmall
      linarith [exp4_lt]
    have hprod : (m : ℝ) * log m ≤ 225 := by nlinarith
    have : √((m : ℝ) * log m) ≤ 15 := by
      rw [show (15 : ℝ) = √(15 ^ 2) by rw [sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt (by norm_num; linarith)
    simp only [card_singleton, Nat.cast_one]
    linarith
  push Not at hsmall
  set s : ℝ := √((m : ℝ) * log m) with hsdef
  have hml : (m : ℝ) ≤ m * log m := by nlinarith
  have hs1 : 1 ≤ s := by
    rw [hsdef, show (1 : ℝ) = √1 by simp]; exact sqrt_le_sqrt (by linarith)
  have hs0 : 0 < s := by linarith
  have hss : s * s = m * log m := mul_self_sqrt (by positivity)
  set P : ℝ := (P G univ : ℝ) with hPdef
  have hsumdeg : ∑ v : V, (deg G univ v : ℝ) = P := by
    rw [hPdef, P_eq_sum]; push_cast; rfl
  by_cases hd : (m : ℝ) * s ≤ P
  · -- a vertex of degree ≥ s: its neighbourhood is independent
    have hne : (univ : Finset V).Nonempty := univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hmpos)
    obtain ⟨v, -, hv⟩ : ∃ v ∈ (univ : Finset V), s ≤ (deg G univ v : ℝ) := by
      apply exists_le_of_sum_le hne
      rw [sum_const, card_univ, ← hmdef, nsmul_eq_mul, hsumdeg]; exact hd
    refine ⟨univ.filter (G.Adj v), ?_, ?_⟩
    · intro a ha b hb _ hab
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at ha hb
      exact no_tri G hG ha hb hab
    · have : (deg G univ v : ℝ) = ((univ.filter (G.Adj v)).card : ℝ) := rfl
      rw [← this]; linarith
  · -- low average degree: Shearer with d = s
    push Not at hd
    obtain ⟨I, -, hI, hbound⟩ := shearer G f g (fun x d hx hd => tangent hx hd)
      (fun d hd => g_nonpos hd) (fun d hd => ode hd) (fun d hd => at_zero hd) hG univ
    refine ⟨I, hI, ?_⟩
    have hb := hbound s hs0
    rw [card_univ, ← hmdef] at hb
    have hgs : g s ≤ 0 := g_nonpos hs0
    have h1 : 0 ≤ g s * (P - m * s) := mul_nonneg_of_nonpos_of_nonpos hgs (by linarith)
    have hf := lower hs1
    -- log s ≥ log m / 2
    have hlogs : log (m : ℝ) / 2 ≤ log s := by
      have : log s = log ((m : ℝ) * log m) / 2 := by rw [hsdef, log_sqrt (by positivity)]
      rw [this]
      have := log_le_log (by linarith) hml
      linarith
    have hfs : (m : ℝ) * ((log s - 1) / s) ≤ I.card := by
      have := mul_le_mul_of_nonneg_left hf hmR
      linarith
    have key : 1 / 15 * s ≤ (m : ℝ) * ((log s - 1) / s) := by
      rw [mul_div_assoc', le_div_iff₀ hs0]
      have : (m : ℝ) * (log m / 4) ≤ m * (log s - 1) := by
        apply mul_le_mul_of_nonneg_left _ hmR; linarith
      nlinarith
    linarith

end OMA.Erdos920H2

theorem OMA.solution : OMA.R_Erdos920_erdos_920_variants_k_eq_3_R1.H2 := OMA.Erdos920H2.H2_proof

