import FormalConjectures.ErdosProblems.«713»
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Analysis.Subadditive
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
Reduction R2 of Erdős Problem 713 (i).

Proved here: removing isolated vertices does not change ex(n;G) eventually; a star or a
consecutive matching gives ex(n;G) ≥ n/2, so any limiting exponent is at least 1;
double counting injective neighbour tuples plus Jensen gives ex(n;G) ≤ q n^(2-1/q) for every
bipartite G on q vertices (Kővári–Sós–Turán), so any limiting exponent is below 2; for a
connected forbidden graph ex is superadditive, so by Fekete ex(n;G)/n either tends to a
positive constant or diverges; a greedy tree embedding shows forests are linear.

What remains: a limiting power law (some exponent and positive constant, no range required)
for isolate-free bipartite G which is either connected, cyclic and superlinear (H1), or
disconnected and without a positive linear limit (H2).
-/

-- Credit: @mucoucah

namespace OMA.R_Erdos713_erdos_713_parts_i_R2

open Filter SimpleGraph Finset
open scoped Classical Topology Sym2

/-- Connected cyclic bipartite graphs with superlinear extremal numbers have a power-law
limit ex(n;G)/n^α → c > 0. -/
def H1 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
  (∀ v, ¬ G.IsIsolated v) → G.Connected → ¬ G.IsAcyclic →
  Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop atTop →
  ∃ α c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α) atTop (𝓝 c)

/-- Disconnected isolate-free bipartite graphs with no positive linear limit have a power-law
limit ex(n;G)/n^α → c > 0. -/
def H2 : Prop := ∀ (q : ℕ) (G : SimpleGraph (Fin q)), G.IsBipartite → 2 ≤ G.edgeFinset.card →
  (∀ v, ¬ G.IsIsolated v) → ¬ G.Connected →
  (¬ ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop (𝓝 c)) →
  ∃ α c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α) atTop (𝓝 c)

theorem contained_in_balanced_bipartite {q : ℕ} (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) : G ⊑ completeBipartiteGraph (Fin q) (Fin q) := by
  obtain ⟨c⟩ := bip
  let f : Fin q → Fin q ⊕ Fin q := fun v => if c v = 0 then .inl v else .inr v
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro v w h
    have hc := c.valid h
    by_cases hv : c v = 0 <;> by_cases hw : c w = 0
    · exact (hc (hv.trans hw.symm)).elim
    · simp [f, hv, hw]
    · simp [f, hv, hw]
    · have hv' : c v = 1 := by exact Fin.eq_one_of_ne_zero _ hv
      have hw' : c w = 1 := by exact Fin.eq_one_of_ne_zero _ hw
      exact (hc (hv'.trans hw'.symm)).elim
  · intro v w h
    change f v = f w at h
    have hf (u) : Sum.elim id id (f u) = u := by
      by_cases hu : c u = 0 <;> simp [f, hu]
    simpa only [hf] using congrArg (Sum.elim id id) h

-- Count pairs of a vertex and an ordered tuple of distinct neighbors.
theorem balanced_degree_count {q n : ℕ} (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin q) (Fin q)).Free X) :
    (∑ v : Fin n, (X.degree v).descFactorial q) ≤ n ^ q * (q - 1) := by
  let R (v : Fin n) (f : Fin q ↪ Fin n) : Prop := ∀ i, X.Adj v (f i)
  have hrow (v : Fin n) :
      (univ.bipartiteAbove R v).card = (X.degree v).descFactorial q := by
    let e : (univ.bipartiteAbove R v) ≃ (Fin q ↪ X.neighborFinset v) :=
      { toFun := fun f =>
          ⟨fun i => ⟨f.val i, (mem_neighborFinset X v _).mpr (((mem_bipartiteAbove R).mp f.property).2 i)⟩,
            fun _ _ h => f.val.injective (congrArg Subtype.val h)⟩
        invFun := fun f =>
          ⟨f.trans (Function.Embedding.subtype _),
            (mem_bipartiteAbove R).mpr ⟨mem_univ _, fun i => (mem_neighborFinset X v _).mp (f i).property⟩⟩
        left_inv := fun f => Subtype.ext (Function.Embedding.ext fun _ => rfl)
        right_inv := fun f => Function.Embedding.ext fun _ => rfl }
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq, Fintype.card_fin]
    rw [Fintype.card_coe, card_neighborFinset_eq_degree]
  have hcol (f : Fin q ↪ Fin n) : (univ.bipartiteBelow R f).card ≤ q - 1 := by
    have hlt : (univ.bipartiteBelow R f).card < q := by
      by_contra! hlarge
      obtain ⟨s, hs, hq⟩ := exists_subset_card_eq hlarge
      apply free
      apply completeBipartiteGraph_isContained_iff.mpr
      refine ⟨univ.map f, s, by simp, by simpa using hq, ?_⟩
      intro a ha b hb
      obtain ⟨i, -, rfl⟩ := mem_map.mp (mem_coe.mp ha)
      exact (((mem_bipartiteBelow R).mp (hs (mem_coe.mp hb))).2 i).symm
    omega
  calc
    _ = ∑ v : Fin n, (univ.bipartiteAbove R v).card := by simp only [hrow]
    _ = ∑ f : Fin q ↪ Fin n, (univ.bipartiteBelow R f).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ ≤ ∑ _ : Fin q ↪ Fin n, (q - 1) := sum_le_sum (fun f _ => hcol f)
    _ = n.descFactorial q * (q - 1) := by
      simp [Fintype.card_embedding_eq]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow n q)

theorem balanced_edge_bound {q n : ℕ} (hq : 0 < q) (hn : 0 < n)
    (X : SimpleGraph (Fin n)) [DecidableRel X.Adj]
    (free : (completeBipartiteGraph (Fin q) (Fin q)).Free X) :
    (X.edgeFinset.card : ℝ) ≤ q * (n : ℝ) ^ (2 - 1 / (q : ℝ)) := by
  have npos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have qpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  -- The shifted degrees have q-th powers bounded by the falling factorials.
  let d (v : Fin n) := (X.degree v + 1 - q : ℕ)
  have hcount : (∑ v : Fin n, (d v : ℝ) ^ q) ≤ (n : ℝ) ^ q * (q - 1 : ℕ) := by
    have hnat : (∑ v : Fin n, (d v) ^ q) ≤ n ^ q * (q - 1) :=
      (sum_le_sum fun v _ => Nat.pow_sub_le_descFactorial (X.degree v) q).trans
        (balanced_degree_count X free)
    exact_mod_cast hnat
  let m : ℝ := (∑ v : Fin n, (d v : ℝ)) / n
  have hjensen : m ^ q ≤ (∑ v : Fin n, (d v : ℝ) ^ q) / n := by
    have hw : (∑ _ : Fin n, (1 / (n : ℝ))) = 1 := by
      simp [npos.ne']
    have hmean : m = (n : ℝ)⁻¹ * ∑ v : Fin n, (d v : ℝ) := by
      dsimp only [m]
      rw [div_eq_inv_mul]
    rw [hmean, div_eq_inv_mul]
    simpa only [one_div, ← Finset.mul_sum] using
      Real.pow_arith_mean_le_arith_mean_pow univ (fun _ : Fin n => 1 / (n : ℝ))
        (fun v => (d v : ℝ)) (fun _ _ => by positivity) hw (fun _ _ => by positivity) q
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let β : ℝ := 1 - 1 / (q : ℝ)
  have hβ : 0 ≤ β := sub_nonneg.mpr ((div_le_one qpos).mpr hq1)
  have hpowers : ((n : ℝ) ^ β) ^ q = (n : ℝ) ^ q / n := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ β) q, ← Real.rpow_mul npos.le]
    dsimp only [β]
    rw [sub_mul, one_mul,
      div_mul_cancel₀ _ qpos.ne', Real.rpow_sub npos, Real.rpow_natCast, Real.rpow_one]
  have hqpow : (((q - 1 : ℕ) : ℝ)) ≤ (q : ℝ) ^ q := by
    push_cast [Nat.cast_sub (show 1 ≤ q by omega)]
    exact (sub_le_self _ zero_le_one).trans (le_self_pow₀ hq1 (by omega))
  have havg : m ≤ q * (n : ℝ) ^ β := by
    apply le_of_pow_le_pow_left₀ hq.ne' (by positivity : 0 ≤ (q : ℝ) * (n : ℝ) ^ β)
    calc
      m ^ q ≤ ((n : ℝ) ^ q * (q - 1 : ℕ)) / n :=
        hjensen.trans (div_le_div_of_nonneg_right hcount npos.le)
      _ = (q - 1 : ℕ) * ((n : ℝ) ^ q / n) := by ring
      _ ≤ ((q : ℝ) * (n : ℝ) ^ β) ^ q := by
        rw [mul_pow, hpowers]
        exact mul_le_mul_of_nonneg_right hqpow (by positivity)
  have hdeg : (∑ v : Fin n, (X.degree v : ℝ)) ≤ n * m + n * q := by
    calc
      _ ≤ ∑ v : Fin n, ((d v : ℝ) + q) := by
        apply sum_le_sum
        intro v _
        exact_mod_cast (show X.degree v ≤ d v + q by dsimp [d]; omega)
      _ = _ := by
        simp only [m, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hhand : (∑ v : Fin n, (X.degree v : ℝ)) = 2 * X.edgeFinset.card := by
    exact_mod_cast X.sum_degrees_eq_twice_card_edges
  have hbase : (1 : ℝ) ≤ (n : ℝ) ^ β := Real.one_le_rpow hn1 hβ
  have hsingle : (n : ℝ) * q ≤ n * (q * (n : ℝ) ^ β) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_right qpos.le hbase) npos.le
  have hdouble : 2 * (X.edgeFinset.card : ℝ) ≤ 2 * (n * (q * (n : ℝ) ^ β)) := by
    rw [← hhand, two_mul]
    exact hdeg.trans <| add_le_add (mul_le_mul_of_nonneg_left havg npos.le) hsingle
  have hpow : (n : ℝ) * (q * (n : ℝ) ^ β) = q * (n : ℝ) ^ (2 - 1 / (q : ℝ)) := by
    rw [show (2 : ℝ) - 1 / q = 1 + β by dsimp [β]; ring, Real.rpow_add npos, Real.rpow_one]
    ring
  rw [hpow] at hdouble
  linarith

theorem bipartite_extremal_upper {q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) {n : ℕ} (hn : 0 < n) :
    (extremalNumber n G : ℝ) ≤ (q : ℝ) * (n : ℝ) ^ (2 - 1 / (q : ℝ)) := by
  have hcard := contained_in_balanced_bipartite G bip
  have hmono : extremalNumber n G ≤ extremalNumber n (completeBipartiteGraph (Fin q) (Fin q)) :=
    hcard.extremalNumber_le
  apply (Nat.cast_le.mpr hmono).trans
  rw [← Fintype.card_fin n, extremalNumber_le_iff_of_nonneg _ (by positivity)]
  intro X _ hfree
  rw [Fintype.card_fin]
  exact balanced_edge_bound hq hn X hfree

theorem exponent_le_bipartite_bound {q : ℕ} (hq : 0 < q) (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) {α c : ℝ} (hc : 0 < c)
    (hlim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α)
      atTop (𝓝 c)) :
    α ≤ 2 - 1 / (q : ℝ) := by
  by_contra! hα
  let β : ℝ := 2 - 1 / (q : ℝ)
  have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ (β - α)) atTop (𝓝 0) := by
    rw [← neg_sub]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => (q : ℝ) * (n : ℝ) ^ (β - α)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpower.const_mul (q : ℝ)
  have hle : c ≤ 0 := le_of_tendsto_of_tendsto hlim hzero (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [Real.rpow_sub hnpos, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (bipartite_extremal_upper hq G bip (by omega)) (by positivity))
  exact hc.not_ge hle

theorem consecutive_matching_degree (n : ℕ) (M : SimpleGraph (Fin n)) [DecidableRel M.Adj]
    (hM : ∀ v w, M.Adj v w ↔ v.val / 2 = w.val / 2 ∧ v ≠ w) (v : Fin n) :
    M.degree v ≤ 1 := by
  rw [← card_neighborFinset_eq_degree, Finset.card_le_one]
  intro a ha b hb
  have ha' : v.val / 2 = a.val / 2 ∧ v ≠ a := (hM _ _).mp ((mem_neighborFinset _ _ _).mp ha)
  have hb' : v.val / 2 = b.val / 2 ∧ v ≠ b := (hM _ _).mp ((mem_neighborFinset _ _ _).mp hb)
  have hna : v.val ≠ a.val := fun h => ha'.2 (Fin.ext h)
  have hnb : v.val ≠ b.val := fun h => hb'.2 (Fin.ext h)
  apply Fin.ext
  omega

theorem consecutive_matching_edges (n : ℕ) (M : SimpleGraph (Fin n)) [DecidableRel M.Adj]
    (hM : ∀ v w, M.Adj v w ↔ v.val / 2 = w.val / 2 ∧ v ≠ w) :
    n / 2 ≤ M.edgeFinset.card := by
  let a (i : Fin (n / 2)) : Fin n := ⟨2 * i.val, by have hi := i.isLt; omega⟩
  let b (i : Fin (n / 2)) : Fin n := ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩
  have h (i) : s(a i, b i) ∈ M.edgeFinset := by
    rw [mem_edgeFinset, mem_edgeSet, hM]
    change (2 * i.val) / 2 = (2 * i.val + 1) / 2 ∧ a i ≠ b i
    refine ⟨by omega, ?_⟩
    intro heq
    have eq := congrArg Fin.val heq
    change 2 * i.val = 2 * i.val + 1 at eq
    omega
  let f (i : Fin (n / 2)) : M.edgeFinset := ⟨_, h i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have eq : s(a i, b i) = s(a j, b j) := congrArg Subtype.val hij
    rcases Sym2.eq_iff.mp eq with ⟨heq, _⟩ | ⟨heq, _⟩
    · have hval := congrArg Fin.val heq
      change 2 * i.val = 2 * j.val at hval
      exact Fin.ext (by omega)
    · have hval := congrArg Fin.val heq
      change 2 * i.val = 2 * j.val + 1 at hval
      omega
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem star_free_of_degree_le_one {q n : ℕ} (G : SimpleGraph (Fin q))
    (edges : 2 ≤ G.edgeFinset.card) (degree : ∀ v, G.degree v ≤ 1) (r : Fin n) :
    G.Free (starGraph r) := by
  rintro ⟨f⟩
  have hcenter (v w : Fin q) (h : G.Adj v w) : f v = r ∨ f w = r :=
    (starGraph_adj.mp (f.toHom.map_adj h)).2
  obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < G.edgeFinset.card)
  obtain ⟨u, hu⟩ : ∃ u, f u = r := by
    induction e using Sym2.inductionOn with
    | _ v w =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      exact (hcenter v w he).elim (fun h => ⟨v, h⟩) (fun h => ⟨w, h⟩)
  have hsub : G.edgeFinset ⊆ G.incidenceFinset u := by
    intro e he
    rw [incidenceFinset_eq_filter, mem_filter]
    refine ⟨he, ?_⟩
    induction e using Sym2.inductionOn with
    | _ v w =>
      rw [mem_edgeFinset, mem_edgeSet] at he
      rcases hcenter v w he with hv | hw
      · have hv' : v = u := f.injective (hv.trans hu.symm)
        simp [hv']
      · have hw' : w = u := f.injective (hw.trans hu.symm)
        simp [hw']
  have hle := Finset.card_le_card hsub
  rw [card_incidenceFinset_eq_degree] at hle
  have hdegree := degree u
  omega

theorem extremal_linear_lower {q n : ℕ} (G : SimpleGraph (Fin q))
    (edges : 2 ≤ G.edgeFinset.card) (hn : 0 < n) : n / 2 ≤ extremalNumber n G := by
  by_cases h : ∀ v, G.degree v ≤ 1
  · let r : Fin n := ⟨0, hn⟩
    have hfree := star_free_of_degree_le_one G edges h r
    have hdegree := (starGraph r).card_incidenceFinset_eq_degree r
    have hcard : n - 1 ≤ (starGraph r).edgeFinset.card := by
      rw [degree_starGraph_center, Fintype.card_fin] at hdegree
      rw [← hdegree]
      exact Finset.card_le_card (by
        rw [incidenceFinset_eq_filter]
        exact filter_subset _ _)
    have hex := card_edgeFinset_le_extremalNumber hfree
    rw [Fintype.card_fin] at hex
    exact (by omega : n / 2 ≤ n - 1).trans (hcard.trans hex)
  · obtain ⟨v, hv⟩ := not_forall.mp h
    let M : SimpleGraph (Fin n) :=
      { Adj := fun v w => v.val / 2 = w.val / 2 ∧ v ≠ w
        symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
        loopless := ⟨fun _ h => h.2 rfl⟩ }
    have hM : ∀ v w, M.Adj v w ↔ v.val / 2 = w.val / 2 ∧ v ≠ w := fun _ _ => Iff.rfl
    have hfree : G.Free M := by
      rintro ⟨f⟩
      exact hv ((f.degree_le v).trans (consecutive_matching_degree n M hM (f v)))
    have hex := card_edgeFinset_le_extremalNumber hfree
    rw [Fintype.card_fin] at hex
    exact (consecutive_matching_edges n M hM).trans hex

theorem exponent_ge_one {q : ℕ} (G : SimpleGraph (Fin q))
    (edges : 2 ≤ G.edgeFinset.card) {α c : ℝ}
    (hlim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α)
      atTop (𝓝 c)) : 1 ≤ α := by
  by_contra! hα
  have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    rw [← neg_sub]
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop (𝓝 0) := by
    have hmul := hlim.mul hpower
    rw [mul_zero] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [Real.rpow_sub hnpos, Real.rpow_one, div_mul_div_comm,
      div_eq_div_iff (by positivity) hnpos.ne']
    ring
  have hle : (1 / 3 : ℝ) ≤ 0 := ge_of_tendsto hzero (by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [le_div_iff₀ hnpos]
    have hnat : n ≤ 3 * extremalNumber n G :=
      (show n ≤ 3 * (n / 2) by omega).trans
        (Nat.mul_le_mul_left 3 (extremal_linear_lower G edges (by omega)))
    have hreal : (n : ℝ) ≤ 3 * (extremalNumber n G : ℝ) := by exact_mod_cast hnat
    linarith)
  norm_num at hle

theorem connected_copy_from_left {V W Z : Type*} {G : SimpleGraph V}
    {A : SimpleGraph W} {B : SimpleGraph Z} (conn : G.Connected)
    (f : Copy G (A ⊕g B)) {u : V} {a : W} (hu : f u = Sum.inl a) : G ⊑ A := by
  let g (v : V) : W := Sum.elim id (fun _ => a) (f v)
  have hg (v : V) : f v = Sum.inl (g v) := by
    cases hv : f v with
    | inl w => simp [g, hv]
    | inr z =>
      have hpath := (conn u v).map f.toHom
      change (A ⊕g B).Reachable (f u) (f v) at hpath
      rw [hu, hv] at hpath
      exact (not_reachable_sum_inl_inr a z hpath).elim
  refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
  · intro v w adj
    have h := f.toHom.map_adj adj
    change (A ⊕g B).Adj (f v) (f w) at h
    rw [hg v, hg w] at h
    exact sum_adj_inl.mp h
  · intro v w eq
    change g v = g w at eq
    apply f.injective
    change f v = f w
    rw [hg v, hg w, eq]

theorem connected_free_sum {V W Z : Type*} {G : SimpleGraph V}
    {A : SimpleGraph W} {B : SimpleGraph Z} (conn : G.Connected)
    (freeA : G.Free A) (freeB : G.Free B) : G.Free (A ⊕g B) := by
  rintro ⟨f⟩
  obtain ⟨u⟩ := conn.nonempty
  cases hu : f u with
  | inl a => exact freeA (connected_copy_from_left conn f hu)
  | inr b =>
    apply freeB (connected_copy_from_left conn (Iso.sumComm.toCopy.comp f) (u := u) (a := b) ?_)
    change Sum.swap (f u) = Sum.inl b
    rw [hu]
    rfl

theorem connected_extremal_superadditive {q : ℕ} (G : SimpleGraph (Fin q))
    (conn : G.Connected) (edges : 2 ≤ G.edgeFinset.card) (m n : ℕ) :
    extremalNumber m G + extremalNumber n G ≤ extremalNumber (m + n) G := by
  have hG : G ≠ ⊥ := by
    intro heq
    rw [edgeFinset_eq_empty.mpr heq] at edges
    simp at edges
  obtain ⟨A, hAd, hA⟩ := exists_isExtremal_free (V := Fin m) hG
  obtain ⟨B, hBd, hB⟩ := exists_isExtremal_free (V := Fin n) hG
  let _ := hAd
  let _ := hBd
  calc
    extremalNumber m G + extremalNumber n G = A.edgeFinset.card + B.edgeFinset.card := by
      rw [card_edgeFinset_of_isExtremal_free hA, card_edgeFinset_of_isExtremal_free hB,
        Fintype.card_fin, Fintype.card_fin]
    _ = (A ⊕g B).edgeFinset.card := by
      rw [edgeFinset_card, edgeFinset_card, edgeFinset_card,
        Fintype.card_congr (edgeSetSumEquiv (G := A) (H := B)), Fintype.card_sum]
    _ ≤ _ := by
      simpa only [Fintype.card_sum, Fintype.card_fin] using
        card_edgeFinset_le_extremalNumber (connected_free_sum conn hA.prop hB.prop)

theorem connected_density_alternative {q : ℕ} (G : SimpleGraph (Fin q))
    (conn : G.Connected) (edges : 2 ≤ G.edgeFinset.card) :
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop (𝓝 c)) ∨
      Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / n) atTop atTop := by
  let u (n : ℕ) : ℝ := -(extremalNumber n G : ℝ)
  have hadd : Subadditive u := by
    intro m n
    have h : (extremalNumber m G : ℝ) + extremalNumber n G ≤ extremalNumber (m + n) G :=
      by exact_mod_cast connected_extremal_superadditive G conn edges m n
    dsimp [u]
    linarith
  by_cases hb : BddBelow (Set.range fun n : ℕ => u n / n)
  · left
    have h2 := hadd.lim_le_div hb (by decide : (2 : ℕ) ≠ 0)
    have hlo := extremal_linear_lower G edges (by decide : 0 < (2 : ℕ))
    have hlo' : (1 : ℝ) ≤ extremalNumber 2 G := by exact_mod_cast hlo
    norm_num [u] at h2
    refine ⟨-hadd.lim, by linarith, ?_⟩
    simpa only [u, neg_div, neg_neg] using (hadd.tendsto_lim hb).neg
  · right
    apply tendsto_atTop.mpr
    intro M
    obtain ⟨_, ⟨k, rfl⟩, hk⟩ := not_bddBelow_iff.mp hb (min 0 (-M) - 1)
    have ht : min 0 (-M) - 1 < 0 := by linarith [min_le_left (0 : ℝ) (-M)]
    have hne : k ≠ 0 := by
      rintro rfl
      simp only [Nat.cast_zero, div_zero] at hk
      linarith
    filter_upwards [hadd.eventually_div_lt_of_div_lt hne hk] with n hn
    simp only [u, neg_div] at hn
    linarith [min_le_right (0 : ℝ) (-M)]

theorem tree_copies_into_high_degree {V W : Type} [Fintype V] [Fintype W]
    (T : SimpleGraph V) (tree : T.IsTree) (X : SimpleGraph W) [DecidableRel X.Adj]
    (w : W) (degree : ∀ x, Fintype.card V ≤ X.degree x) : T ⊑ X := by
  have aux (k : ℕ) : ∀ (U : Type) [Fintype U], Fintype.card U = k →
      ∀ (S : SimpleGraph U), S.IsTree → (∀ x, k ≤ X.degree x) → S ⊑ X := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro U _ hU S hS hdeg
      rcases subsingleton_or_nontrivial U with hs | hs
      · exact ⟨⟨⟨fun _ => w, fun h => (h.ne (Subsingleton.elim _ _)).elim⟩,
          fun _ _ _ => Subsingleton.elim _ _⟩⟩
      let _ := hs
      obtain ⟨leaf, hleaf⟩ := hS.exists_vert_degree_one_of_nontrivial
      obtain ⟨parent, hparent, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hleaf
      let V' := ({leaf}ᶜ : Set U)
      let S' := S.induce V'
      have htree' : S'.IsTree := ⟨hS.connected.induce_compl_singleton_of_degree_eq_one hleaf,
        hS.isAcyclic.induce V'⟩
      have hcard : Fintype.card V' < k := by
        rw [← hU]
        exact Fintype.card_lt_of_injective_of_notMem (f := fun x : V' => x.val)
          Subtype.val_injective (b := leaf) (by simp [V'])
      obtain ⟨f⟩ := ih (Fintype.card V') hcard V' rfl S' htree'
        (fun x => hcard.le.trans (hdeg x))
      let p : V' := ⟨parent, hparent.ne.symm⟩
      let used := (univ : Finset V').map f.toEmbedding
      have hfresh : ∃ y ∈ X.neighborFinset (f p), y ∉ used := by
        by_contra! h
        have hc := Finset.card_le_card (show X.neighborFinset (f p) ⊆ used from h)
        rw [card_neighborFinset_eq_degree] at hc
        have hused : used.card = Fintype.card V' := by simp [used]
        exact hcard.not_ge ((hdeg (f p)).trans (hc.trans_eq hused))
      obtain ⟨y, hy, hynew⟩ := hfresh
      have hy' := (mem_neighborFinset X (f p) y).mp hy
      let g (v : U) : W := if h : v = leaf then y else f ⟨v, h⟩
      have g_eq (v : U) (hv : v ≠ leaf) : g v = f ⟨v, hv⟩ := by
        simp [g, hv]
      have g_leaf : g leaf = y := by simp [g]
      have g_used (v : U) (hv : v ≠ leaf) : g v ∈ used := by
        rw [g_eq v hv]
        exact mem_map.mpr ⟨⟨v, hv⟩, mem_univ _, rfl⟩
      have hleaf_adj (v : U) (hv : S.Adj leaf v) : X.Adj (g leaf) (g v) := by
        have hv' : v = parent := hu v hv
        subst v
        rw [g_leaf, g_eq parent hparent.ne.symm]
        exact hy'.symm
      refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
      · intro v u adj
        rcases eq_or_ne v leaf with rfl | hv
        · exact hleaf_adj u adj
        rcases eq_or_ne u leaf with rfl | hu'
        · exact (hleaf_adj v adj.symm).symm
        rw [g_eq v hv, g_eq u hu']
        exact f.toHom.map_adj (show S'.Adj ⟨v, hv⟩ ⟨u, hu'⟩ from adj)
      · intro v u eq
        change g v = g u at eq
        rcases eq_or_ne v leaf with rfl | hv
        · by_contra hu'
          rw [g_leaf] at eq
          exact hynew (eq ▸ g_used u (fun h => hu' h.symm))
        rcases eq_or_ne u leaf with rfl | hu'
        · rw [g_leaf] at eq
          exact (hynew (eq ▸ g_used v hv)).elim
        rw [g_eq v hv, g_eq u hu'] at eq
        exact congrArg Subtype.val (f.injective eq)
  exact aux (Fintype.card V) V rfl T tree degree

theorem forest_extremal_upper {q : ℕ} (G : SimpleGraph (Fin q))
    (forest : G.IsAcyclic) (n : ℕ) : extremalNumber n G ≤ q * n := by
  induction n with
  | zero =>
    rw [← Fintype.card_fin 0, extremalNumber_le_iff (V := Fin 0)]
    intro X _ _
    have bound := X.card_edgeFinset_le_card_choose_two
    simpa using bound
  | succ n ih =>
    rw [← Fintype.card_fin (n+1), extremalNumber_le_iff (V := Fin (n+1))]
    intro X _ free
    by_cases h : ∃ x, X.degree x < q
    · obtain ⟨x, hx⟩ := h
      have hdel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber free x
      rw [card_edgeFinset_deleteIncidenceSet, Fintype.card_fin, Nat.add_sub_cancel] at hdel
      rw [Fintype.card_fin, Nat.mul_succ]
      omega
    · have hdeg (x) : q ≤ X.degree x := Nat.le_of_not_gt (fun hx => h ⟨x, hx⟩)
      have nonempty : Nonempty (Fin q) := by
        by_contra! hempty
        have hbot : G = ⊥ := by ext v; exact (hempty.false v).elim
        exact free (by rw [hbot, bot_isContained_iff_card_le]; simp)
      obtain ⟨T, hGT, _, ht⟩ := (connected_top (V := Fin q)).exists_isTree_le_of_le_of_isAcyclic
        (show G ≤ ⊤ from le_top) forest
      have hc := tree_copies_into_high_degree T ht X (0 : Fin (n+1)) (by simpa using hdeg)
      exact (free ((IsContained.of_le hGT).trans hc)).elim

theorem contained_iff_contained_support {q n : ℕ} (G : SimpleGraph (Fin q))
    (X : SimpleGraph (Fin n)) (hn : q ≤ n) :
    G ⊑ X ↔ (G.induce G.support) ⊑ X := by
  constructor
  · exact fun h => (Copy.induce G G.support).isContained.trans h
  · rintro ⟨f⟩
    let image : Set (Fin n) := Set.range f.toEmbedding
    have himage : Fintype.card image = Fintype.card G.support :=
      Fintype.card_range f.toEmbedding
    have hcard : Fintype.card (↑G.supportᶜ : Type) ≤ Fintype.card (↑imageᶜ : Type) := by
      simpa only [Fintype.card_compl_set, Fintype.card_fin, himage] using
        Nat.sub_le_sub_right hn (Fintype.card G.support)
    let e : (↑G.supportᶜ : Type) ↪ (↑imageᶜ : Type) :=
      (Function.Embedding.nonempty_of_card_le hcard).some
    let g (v : Fin q) : Fin n :=
      if h : v ∈ G.support then f ⟨v, h⟩ else (e ⟨v, h⟩).val
    have hg (v) (hv : v ∈ G.support) : g v = f ⟨v, hv⟩ := dif_pos hv
    have hn' (v) (hv : v ∉ G.support) : g v = (e ⟨v, hv⟩).val := dif_neg hv
    refine ⟨⟨⟨g, ?_⟩, ?_⟩⟩
    · intro v w h
      rw [hg v h.mem_support_left, hg w h.mem_support_right]
      exact f.toHom.map_adj (show (G.induce G.support).Adj
        ⟨v, h.mem_support_left⟩ ⟨w, h.mem_support_right⟩ from h)
    · intro v w heq
      change g v = g w at heq
      by_cases hv : v ∈ G.support <;> by_cases hw : w ∈ G.support
      · rw [hg v hv, hg w hw] at heq
        exact congrArg Subtype.val (f.injective heq)
      · rw [hg v hv, hn' w hw] at heq
        exact ((e ⟨w, hw⟩).property ⟨⟨v, hv⟩, heq⟩).elim
      · rw [hn' v hv, hg w hw] at heq
        exact ((e ⟨v, hv⟩).property ⟨⟨w, hw⟩, heq.symm⟩).elim
      · rw [hn' v hv, hn' w hw] at heq
        exact congrArg Subtype.val (e.injective (Subtype.ext heq))

theorem extremal_eq_on_support {q n : ℕ} (G : SimpleGraph (Fin q)) (hn : q ≤ n) :
    extremalNumber n G = extremalNumber n (G.induce G.support) := by
  have hfree (X : SimpleGraph (Fin n)) : G.Free X ↔ (G.induce G.support).Free X :=
    not_congr (contained_iff_contained_support G X hn)
  have hx : (univ : Finset (SimpleGraph (Fin n))).filter (fun X => G.Free X) =
      univ.filter (fun X => (G.induce G.support).Free X) := by
    ext X
    simpa only [mem_filter, mem_univ, true_and] using hfree X
  unfold extremalNumber
  rw [hx]

theorem remove_isolated_vertices {q : ℕ} (G : SimpleGraph (Fin q))
    (bip : G.IsBipartite) :
    ∃ (k : ℕ) (H : SimpleGraph (Fin k)), H.IsBipartite ∧
      H.edgeFinset.card = G.edgeFinset.card ∧ (∀ v, ¬ H.IsIsolated v) ∧
      ∀ n ≥ q, extremalNumber n G = extremalNumber n H := by
  let k := Fintype.card G.support
  let e : G.support ≃ Fin k := Fintype.equivFin _
  let H := (G.induce G.support).comap e.symm
  let iso : H ≃g G.induce G.support := ⟨e.symm, Iff.rfl⟩
  have hBip : H.IsBipartite :=
    bip.of_hom ((Embedding.induce G.support).toHom.comp iso.toHom)
  refine ⟨k, H, hBip, iso.card_edgeFinset_eq.trans card_edgeFinset_induce_support, ?_, ?_⟩
  · intro v
    rw [← mem_support_iff_not_isIsolated]
    let u := e.symm v
    obtain ⟨w, hw⟩ := (show ∃ w, G.Adj u.val w from u.property)
    let w' : G.support := ⟨w, hw.mem_support_right⟩
    change ∃ w, H.Adj v w
    refine ⟨e w', ?_⟩
    change (G.induce G.support).Adj (e.symm v) (e.symm (e w'))
    rw [e.symm_apply_apply]
    exact hw
  · intro n hn
    rw [extremal_eq_on_support G hn, extremalNumber_congr_right iso]

theorem main : H1 → H2 → type_of% @Erdos713.erdos_713.parts.i := by
  intro connectedCase disconnectedCase q G bip edges
  have hq : 0 < q := by
    by_contra! hz
    have heq : q = 0 := by omega
    subst q
    have hbot : G = ⊥ := by
      ext v
      exact Fin.elim0 v
    rw [edgeFinset_eq_empty.mpr hbot] at edges
    simp at edges
  obtain ⟨k, H, hbip, hcard, hactive, hstable⟩ := remove_isolated_vertices G bip
  have hedges : 2 ≤ H.edgeFinset.card := hcard.symm ▸ edges
  have hlimit : ∃ α c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n : ℝ) ^ α) atTop (𝓝 c) := by
    by_cases linear : ∃ c : ℝ, 0 < c ∧
        Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / n) atTop (𝓝 c)
    · obtain ⟨c, hc, fit⟩ := linear
      exact ⟨1, c, hc, by simpa only [Real.rpow_one] using fit⟩
    have hdiv (conn : H.Connected) :=
      (connected_density_alternative H conn hedges).resolve_left linear
    have hcyclic (conn : H.Connected) : ¬ H.IsAcyclic := by
      intro forest
      have hev := (tendsto_atTop.mp (hdiv conn) ((k : ℝ) + 1)).and
        (eventually_ge_atTop (1 : ℕ))
      obtain ⟨n, hlarge, hn⟩ := hev.exists
      have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hbound : (extremalNumber n H : ℝ) / n ≤ k :=
        (div_le_iff₀ hnpos).mpr (by exact_mod_cast forest_extremal_upper H forest n)
      linarith
    by_cases conn : H.Connected
    · exact connectedCase k H hbip hedges hactive conn (hcyclic conn) (hdiv conn)
    · exact disconnectedCase k H hbip hedges hactive conn linear
  obtain ⟨α, c, hc, hlimH⟩ := hlimit
  have hlim : Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (n : ℝ) ^ α)
      atTop (𝓝 c) := by
    apply hlimH.congr'
    filter_upwards [eventually_ge_atTop q] with n hn
    simp only [hstable n hn]
  have hα := exponent_ge_one G edges hlim
  have hup := exponent_le_bipartite_bound hq G bip hc hlim
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  refine ⟨α, c, ⟨hα, hup.trans_lt (sub_lt_self _ (one_div_pos.mpr hqpos))⟩, hc, ?_⟩
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mpr
  · change Tendsto (fun n : ℕ => (extremalNumber n G : ℝ) / (c * (n : ℝ) ^ α))
      atTop (𝓝 1)
    simpa only [div_div, mul_comm, div_self hc.ne'] using hlim.div_const c
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    positivity

end OMA.R_Erdos713_erdos_713_parts_i_R2
