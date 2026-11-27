import OMAReductions.R_Erdos551_erdos_551_variants_sufficiently_large_R1

-- Step Erdos551.erdos_551.variants.sufficiently_large.R1.H1: hypothesis H1 of reduction Erdos551.erdos_551.variants.sufficiently_large.R1
-- Credit: @Need17Bread

/-!
# Proof of `Erdos551.erdos_551.variants.sufficiently_large.R1.H1` (Bondy–Erdős 1973)

We prove that for all `n ≥ 3` and `k > n ^ 2 - 2`, every graph `G` on `(k - 1) * (n - 1) + 1`
vertices contains `cycleGraph k` or an independent set of size `n` (a copy of `K_n` in `Gᶜ`).

The proof proceeds by induction on `n ≥ 1` (with `k ≥ 3` fixed and `k > n ^ 2 - 2`):
1. If `G` has neither `C_k` nor an independent set of size `n`, every vertex has degree at least
   `k - 1` (otherwise its non-neighbourhood has at least `(k - 1) * (n - 2) + 1` vertices,
   contradicting the induction hypothesis).
2. A longest simple path therefore yields a cycle of length at least `k`.
3. `G` contains no cycle of length `m` with `m₀ = (n - 1) * (n - 2) + 1 ≤ m < k`: taking a
   longest such cycle `C`, `G` has no `C_{m + 1}`, so every vertex `x ∉ C` has at most `n - 2`
   neighbours on `C` (otherwise `{x} ∪ N_C^+(x)` is an independent set of size `n`). The induction
   hypothesis on `V \ C` gives an independent set `I` of size `n - 1` outside `C`, whose
   neighbourhood in `C` has size at most `(n - 1) * (n - 2) < m`, leaving a vertex in `C`
   non-adjacent to `I`.
4. Taking a shortest cycle `C` of length `s ≥ m₀`, we have `s ≥ k + 1 ≥ n ^ 2`, and `C` has no
   chord of span `d ∈ [2, s - m₀ + 1]`. Hence `{f(0), f(2), ..., f(2 * (n - 1))}` is an
   independent set of size `n`.
-/

namespace OMA.P_Erdos551_erdos_551_variants_sufficiently_large_R1_H1

open SimpleGraph Finset
open scoped Classical

section Helpers

variable {V : Type} {G : SimpleGraph V}

/-- Independent set of size `n` in `G`. -/
private def HasIndep (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ S : Finset V, S.card = n ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v

/-- An independent set of size `n` gives a copy of `K_n` in `Gᶜ`. -/
private lemma hasIndep_imp_contained {n : ℕ} (h : HasIndep G n) :
    (completeGraph (Fin n)).IsContained Gᶜ := by
  obtain ⟨S, hcard, hind⟩ := h
  let e : Fin n ≃ S := (S.equivFinOfCardEq hcard).symm
  refine ⟨⟨⟨fun i => (e i).val, ?_⟩, ?_⟩⟩
  · intro i j hij
    have hne : i ≠ j := (SimpleGraph.top_adj i j).1 hij
    have hval : (e i).val ≠ (e j).val := fun hv => hne (e.injective (Subtype.ext hv))
    exact ⟨hval, hind (e i).val (e i).property (e j).val (e j).property hval⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)

/-- In `Fin m` with `m ≥ 3`, `(u - v).val = 1` iff `u = v + 1`. -/
private lemma fin_sub_val_eq_one_iff {m : ℕ} [NeZero m] (hm : 3 ≤ m) {u v : Fin m} :
    (u - v).val = 1 ↔ u = v + 1 := by
  have h1 : (1 : Fin m).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · intro h
    have hsub : u - v = 1 := Fin.ext (h.trans h1.symm)
    rw [sub_eq_iff_eq_add] at hsub
    rw [hsub, add_comm]
  · intro h
    rw [h, add_sub_cancel_left, h1]

/-- Adjacency in `cycleGraph m` for `m ≥ 3`. -/
private lemma cycleGraph_adj_iff {m : ℕ} [NeZero m] (hm : 3 ≤ m) {u v : Fin m} :
    (cycleGraph m).Adj u v ↔ u = v + 1 ∨ v = u + 1 := by
  rw [cycleGraph_adj', fin_sub_val_eq_one_iff hm, fin_sub_val_eq_one_iff hm]

/-- Consecutive vertices in `cycleGraph m` (`m ≥ 3`) are adjacent. -/
private lemma cycle_adj_succ {m : ℕ} [NeZero m] (hm : 3 ≤ m) (f : Copy (cycleGraph m) G) (i : Fin m) :
    G.Adj (f i) (f (i + 1)) := by
  apply f.toHom.map_adj
  rw [cycleGraph_adj_iff hm]
  exact Or.inr rfl

/-- Construct a copy of `cycleGraph m` (`m ≥ 3`) from consecutive edges and wrap-around edge. -/
private lemma hasCycle_of_fn {m : ℕ} (hm : 3 ≤ m) (f : Fin m → V) (hinj : Function.Injective f)
    (hstep : ∀ i : Fin m, (h : i.val + 1 < m) → G.Adj (f i) (f ⟨i.val + 1, h⟩))
    (hwrap : G.Adj (f ⟨m - 1, by omega⟩) (f ⟨0, by omega⟩)) :
    (cycleGraph m).IsContained G := by
  have : NeZero m := ⟨by omega⟩
  have hsucc : ∀ x : Fin m, G.Adj (f x) (f (x + 1)) := by
    intro x
    have h1 : (1 : Fin m).val = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hx : x.val + 1 < m
    · have heq : x + 1 = ⟨x.val + 1, hx⟩ := by
        apply Fin.ext
        rw [Fin.val_add, h1]
        exact Nat.mod_eq_of_lt hx
      rw [heq]
      exact hstep x hx
    · have hxv : x.val = m - 1 := by omega
      have hxm : x = ⟨m - 1, by omega⟩ := Fin.ext hxv
      have hx1 : x + 1 = ⟨0, by omega⟩ := by
        apply Fin.ext
        rw [Fin.val_add, h1, hxv]
        dsimp
        have : m - 1 + 1 = m := by omega
        rw [this, Nat.mod_self]
      have hfx : f x = f ⟨m - 1, by omega⟩ := congrArg f hxm
      have hfx1 : f (x + 1) = f ⟨0, by omega⟩ := congrArg f hx1
      rw [hfx, hfx1]
      exact hwrap
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro u v huv
  rw [cycleGraph_adj_iff hm] at huv
  rcases huv with rfl | rfl
  · exact (hsucc v).symm
  · exact hsucc u

/-- Rotate a copy of `cycleGraph m` by a shift `s : Fin m`. -/
private def rotateCycle {m : ℕ} [NeZero m] (hm : 3 ≤ m) (f : Copy (cycleGraph m) G) (s : Fin m) :
    Copy (cycleGraph m) G where
  toHom := {
    toFun := fun t => f (s + t)
    map_rel' := by
      intro u v huv
      apply f.toHom.map_adj
      rw [cycleGraph_adj_iff hm] at huv ⊢
      rcases huv with rfl | rfl
      · exact Or.inl (add_assoc s v 1).symm
      · exact Or.inr (add_assoc s u 1).symm
  }
  injective' := fun u v huv => add_left_cancel (f.injective huv)

/-- Lift a copy of `cycleGraph k` from an induced subgraph to `G`. -/
private lemma cycle_of_induce {k : ℕ} {U : Set V}
    (h : (cycleGraph k).IsContained (G.induce U)) : (cycleGraph k).IsContained G := by
  obtain ⟨f⟩ := h
  exact ⟨⟨⟨fun i => (f i).val, fun huv => f.toHom.map_adj huv⟩,
    fun i j hij => f.injective (Subtype.ext hij)⟩⟩

/-- Lift an independent set from an induced subgraph to `G`. -/
private lemma indep_of_induce [DecidableEq V] {n : ℕ} {U : Finset V}
    (h : HasIndep (G.induce (U : Set V)) n) :
    ∃ I : Finset V, I ⊆ U ∧ I.card = n ∧ ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v := by
  obtain ⟨S, hcard, hind⟩ := h
  refine ⟨S.image Subtype.val, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  · rw [Finset.card_image_of_injective _ Subtype.val_injective, hcard]
  · intro u hu v hv huv
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
    exact hind u' hu' v' hv' (fun heq => huv (congrArg Subtype.val heq))

/-- Natural number modulo `m` as an element of `Fin m` (`m ≥ 3`). -/
private def finOfNat {m : ℕ} (hm : 3 ≤ m) (r : ℕ) : Fin m :=
  ⟨r % m, Nat.mod_lt r (by omega)⟩

/-- `finOfNat hm (r + 1) = finOfNat hm r + 1`. -/
private lemma finOfNat_succ {m : ℕ} [NeZero m] (hm : 3 ≤ m) (r : ℕ) :
    finOfNat hm (r + 1) = finOfNat hm r + 1 := by
  apply Fin.ext
  rw [Fin.val_add, show (1 : Fin m).val = 1 from by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)]
  dsimp [finOfNat]
  rw [Nat.mod_add_mod]

/-- Value of `finOfNat hm r` when `r < m`. -/
private lemma finOfNat_val_lt {m : ℕ} (hm : 3 ≤ m) {r : ℕ} (hr : r < m) :
    (finOfNat hm r).val = r :=
  Nat.mod_eq_of_lt hr

/-- Value of `finOfNat hm m` is `0`. -/
private lemma finOfNat_self {m : ℕ} (hm : 3 ≤ m) :
    finOfNat hm m = ⟨0, by omega⟩ :=
  Fin.ext (Nat.mod_self m)

/-- If `x ∉ range f` is adjacent to two consecutive vertices `f i` and `f (i + 1)` on `C_m`,
then `G` contains `C_{m + 1}`. -/
private lemma cycle_extend_of_adj_succ {m : ℕ} [NeZero m] (hm : 3 ≤ m) (f : Copy (cycleGraph m) G)
    {x : V} (hx : ∀ i, f i ≠ x) {i : Fin m}
    (h1 : G.Adj x (f i)) (h2 : G.Adj x (f (i + 1))) :
    (cycleGraph (m + 1)).IsContained G := by
  let f' := rotateCycle hm f i
  have hf'0 : f' ⟨0, by omega⟩ = f i := by
    change f (i + ⟨0, by omega⟩) = f i
    have : (⟨0, by omega⟩ : Fin m) = 0 := Fin.ext (by simp)
    rw [this, add_zero]
  have hf'1 : f' ⟨1, by omega⟩ = f (i + 1) := by
    change f (i + ⟨1, by omega⟩) = f (i + 1)
    have : (⟨1, by omega⟩ : Fin m) = 1 :=
      Fin.ext (by rw [Fin.val_one']; exact (Nat.mod_eq_of_lt (by omega)).symm)
    rw [this]
  have hx' : ∀ t, f' t ≠ x := fun t => hx (i + t)
  let g : Fin (m + 1) → V := fun r =>
    if r.val = 0 then x else f' (finOfNat hm r.val)
  apply hasCycle_of_fn (by omega) g
  · intro r₁ r₂ heq
    by_cases h01 : r₁.val = 0 <;> by_cases h02 : r₂.val = 0
    · exact Fin.ext (by omega)
    · simp only [g, if_pos h01, if_neg h02] at heq
      exact absurd heq.symm (hx' _)
    · simp only [g, if_neg h01, if_pos h02] at heq
      exact absurd heq (hx' _)
    · simp only [g, if_neg h01, if_neg h02] at heq
      have hfin := f'.injective heq
      have hval := congrArg Fin.val hfin
      by_cases hr1 : r₁.val < m <;> by_cases hr2 : r₂.val < m
      · rw [finOfNat_val_lt hm hr1, finOfNat_val_lt hm hr2] at hval
        exact Fin.ext hval
      · have h2m : r₂.val = m := by omega
        rw [finOfNat_val_lt hm hr1, h2m, finOfNat_self hm] at hval
        dsimp at hval
        omega
      · have h1m : r₁.val = m := by omega
        rw [h1m, finOfNat_self hm, finOfNat_val_lt hm hr2] at hval
        dsimp at hval
        omega
      · exact Fin.ext (by omega)
  · intro r hr
    by_cases hr0 : r.val = 0
    · have hcast1 : finOfNat hm (r.val + 1) = ⟨1, by omega⟩ := by
        apply Fin.ext
        rw [hr0]
        exact finOfNat_val_lt hm (by omega)
      simp only [g, if_pos hr0, if_neg (by omega : ¬ r.val + 1 = 0), hcast1, hf'1]
      exact h2
    · simp only [g, if_neg hr0, if_neg (by omega : ¬ r.val + 1 = 0)]
      rw [finOfNat_succ hm r.val]
      exact cycle_adj_succ hm f' (finOfNat hm r.val)
  · have hm0 : ¬ (m + 1 - 1 = 0) := by omega
    have hcm : finOfNat hm (m + 1 - 1) = ⟨0, by omega⟩ := by
      have : m + 1 - 1 = m := by omega
      rw [this]
      exact finOfNat_self hm
    simp only [g, if_neg hm0, if_pos rfl, hcm, hf'0]
    exact h1.symm

/-- Crossover lemma: if `x ∉ range f` is adjacent to distinct `f i, f j` on `C_m` and
`f (i + 1)` is adjacent to `f (j + 1)`, then `G` contains `C_{m + 1}`. -/
private lemma cycle_extend_of_crossover {m : ℕ} [NeZero m] (hm : 3 ≤ m) (f : Copy (cycleGraph m) G)
    {x : V} (hx : ∀ i, f i ≠ x) {i j : Fin m} (hij : i ≠ j)
    (hi : G.Adj x (f i)) (hj : G.Adj x (f j)) (hcross : G.Adj (f (i + 1)) (f (j + 1))) :
    (cycleGraph (m + 1)).IsContained G := by
  let f' := rotateCycle hm f i
  let d : ℕ := (j - i).val
  have hd_pos : 1 ≤ d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hji : j - i = 0 := Fin.ext (by simpa [d] using hd0)
    exact hij (sub_eq_zero.mp hji).symm
  have hd_lt : d < m := (j - i).isLt
  have hf'0 : f' ⟨0, by omega⟩ = f i := by
    change f (i + ⟨0, by omega⟩) = f i
    have : (⟨0, by omega⟩ : Fin m) = 0 := Fin.ext (by simp)
    rw [this, add_zero]
  have hf'd : f' ⟨d, hd_lt⟩ = f j := by
    have hdeq : (⟨d, hd_lt⟩ : Fin m) = j - i := Fin.ext rfl
    rw [hdeq]
    change f (i + (j - i)) = f j
    rw [add_sub_cancel]
  have hf'1 : f' ⟨1, by omega⟩ = f (i + 1) := by
    change f (i + ⟨1, by omega⟩) = f (i + 1)
    have : (⟨1, by omega⟩ : Fin m) = 1 :=
      Fin.ext (by rw [Fin.val_one']; exact (Nat.mod_eq_of_lt (by omega)).symm)
    rw [this]
  have hf'd1 : f' (finOfNat hm (d + 1)) = f (j + 1) := by
    change f (i + finOfNat hm (d + 1)) = f (j + 1)
    have hcast : finOfNat hm (d + 1) = (j - i) + 1 := by
      rw [finOfNat_succ hm d]
      congr 1
      apply Fin.ext
      exact finOfNat_val_lt hm hd_lt
    rw [hcast, ← add_assoc, add_sub_cancel]
  have hx' : ∀ t, f' t ≠ x := fun t => hx (i + t)
  let idx : Fin (m + 1) → Fin m := fun r =>
    if h : 1 ≤ r.val ∧ r.val ≤ d then ⟨d + 1 - r.val, by omega⟩ else finOfNat hm r.val
  let g : Fin (m + 1) → V := fun r =>
    if r.val = 0 then x else f' (idx r)
  have hidx_val : ∀ r : Fin (m + 1), r.val ≠ 0 →
      (r.val ≤ d → (idx r).val = d + 1 - r.val) ∧
      (d < r.val → r.val < m → (idx r).val = r.val) ∧
      (r.val = m → (idx r).val = 0) := by
    intro r hr0
    refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩
    · simp only [idx, dif_pos (show 1 ≤ r.val ∧ r.val ≤ d by omega)]
    · simp only [idx, dif_neg (by omega : ¬ (1 ≤ r.val ∧ r.val ≤ d))]
      exact finOfNat_val_lt hm h2
    · simp only [idx, dif_neg (by omega : ¬ (1 ≤ r.val ∧ r.val ≤ d))]
      rw [h, finOfNat_self hm]
  apply hasCycle_of_fn (by omega) g
  · intro r₁ r₂ heq
    by_cases h01 : r₁.val = 0 <;> by_cases h02 : r₂.val = 0
    · exact Fin.ext (by omega)
    · simp only [g, if_pos h01, if_neg h02] at heq
      exact absurd heq.symm (hx' _)
    · simp only [g, if_neg h01, if_pos h02] at heq
      exact absurd heq (hx' _)
    · simp only [g, if_neg h01, if_neg h02] at heq
      have hval := congrArg Fin.val (f'.injective heq)
      have hv1 := hidx_val r₁ h01
      have hv2 := hidx_val r₂ h02
      by_cases a1 : r₁.val ≤ d
      · have e1 := hv1.1 a1
        by_cases a2 : r₂.val ≤ d
        · have e2 := hv2.1 a2
          exact Fin.ext (by omega)
        · by_cases b2 : r₂.val < m
          · have e2 := hv2.2.1 (by omega) b2
            omega
          · have e2 := hv2.2.2 (by omega)
            omega
      · by_cases b1 : r₁.val < m
        · have e1 := hv1.2.1 (by omega) b1
          by_cases a2 : r₂.val ≤ d
          · have e2 := hv2.1 a2
            omega
          · by_cases b2 : r₂.val < m
            · have e2 := hv2.2.1 (by omega) b2
              exact Fin.ext (by omega)
            · have e2 := hv2.2.2 (by omega)
              omega
        · have e1 := hv1.2.2 (by omega)
          by_cases a2 : r₂.val ≤ d
          · have e2 := hv2.1 a2
            omega
          · by_cases b2 : r₂.val < m
            · have e2 := hv2.2.1 (by omega) b2
              omega
            · exact Fin.ext (by omega)
  · intro r hr
    by_cases hr0 : r.val = 0
    · have h1le : 1 ≤ r.val + 1 ∧ r.val + 1 ≤ d := by omega
      have hidx1 : idx ⟨r.val + 1, hr⟩ = ⟨d, hd_lt⟩ := by
        simp only [idx, dif_pos h1le]
        exact Fin.ext (by dsimp; omega)
      simp only [g, if_pos hr0, if_neg (by omega : ¬ r.val + 1 = 0), hidx1, hf'd]
      exact hj
    · simp only [g, if_neg hr0, if_neg (by omega : ¬ r.val + 1 = 0)]
      by_cases hlt : r.val < d
      · have h1 : 1 ≤ r.val ∧ r.val ≤ d := by omega
        have h2 : 1 ≤ r.val + 1 ∧ r.val + 1 ≤ d := by omega
        simp only [idx, dif_pos h1, dif_pos h2]
        have hsucc : (⟨d + 1 - r.val, by omega⟩ : Fin m) = ⟨d + 1 - (r.val + 1), by omega⟩ + 1 := by
          apply Fin.ext
          rw [Fin.val_add, show (1 : Fin m).val = 1 from by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)]
          dsimp
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hsucc]
        exact (cycle_adj_succ hm f' _).symm
      · by_cases heqd : r.val = d
        · have h1 : 1 ≤ r.val ∧ r.val ≤ d := by omega
          have h2 : ¬ (1 ≤ r.val + 1 ∧ r.val + 1 ≤ d) := by omega
          simp only [idx, dif_pos h1, dif_neg h2]
          have ha : (⟨d + 1 - r.val, by omega⟩ : Fin m) = ⟨1, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [ha, heqd, hf'1, hf'd1]
          exact hcross
        · have h1 : ¬ (1 ≤ r.val ∧ r.val ≤ d) := by omega
          have h2 : ¬ (1 ≤ r.val + 1 ∧ r.val + 1 ≤ d) := by omega
          simp only [idx, dif_neg h1, dif_neg h2]
          rw [finOfNat_succ hm r.val]
          exact cycle_adj_succ hm f' (finOfNat hm r.val)
  · have hm0 : ¬ (m + 1 - 1 = 0) := by omega
    have hmd : ¬ (1 ≤ m + 1 - 1 ∧ m + 1 - 1 ≤ d) := by omega
    have hidxm : idx ⟨m + 1 - 1, by omega⟩ = ⟨0, by omega⟩ := by
      simp only [idx, dif_neg hmd]
      have : m + 1 - 1 = m := by omega
      rw [this]
      exact finOfNat_self hm
    simp only [g, if_neg hm0, if_pos rfl, hidxm, hf'0]
    exact hi.symm

/-- A longest simple path in a graph of minimum degree at least `d` (`2 ≤ d`) yields a cycle
of length at least `d + 1`. -/
private lemma exists_cycle_of_min_deg [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {d : ℕ} (hd : 2 ≤ d) (hne : Nonempty V)
    (hmindeg : ∀ v : V, d ≤ (Finset.univ.filter (G.Adj v)).card) :
    ∃ s : ℕ, d + 1 ≤ s ∧ (cycleGraph s).IsContained G := by
  classical
  let IsPath (ℓ : ℕ) (p : Fin ℓ → V) : Prop :=
    Function.Injective p ∧ ∀ i : Fin ℓ, (h : i.val + 1 < ℓ) → G.Adj (p i) (p ⟨i.val + 1, h⟩)
  let HasPath (ℓ : ℕ) : Prop := ∃ p : Fin ℓ → V, IsPath ℓ p
  have h1 : HasPath 1 := by
    obtain ⟨v0⟩ := hne
    exact ⟨fun _ => v0, fun a b _ => Subsingleton.elim a b, fun i hi => by omega⟩
  have hcard_pos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr hne
  let S : Finset ℕ := (Finset.Icc 1 (Fintype.card V)).filter HasPath
  have h1S : 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hcard_pos⟩, h1⟩
  let ℓ := S.max' ⟨1, h1S⟩
  have hℓS : ℓ ∈ S := Finset.max'_mem S ⟨1, h1S⟩
  have hℓ_ge : 1 ≤ ℓ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hℓS).1).1
  obtain ⟨p, hp_inj, hp_adj⟩ := (Finset.mem_filter.mp hℓS).2
  have hmax : ¬ HasPath (ℓ + 1) := by
    rintro ⟨q, hq_inj, hq_adj⟩
    have hle : ℓ + 1 ≤ Fintype.card V := by
      simpa using Fintype.card_le_of_injective q hq_inj
    have hmem : ℓ + 1 ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, ⟨q, hq_inj, hq_adj⟩⟩
    have := Finset.le_max' S (ℓ + 1) hmem
    omega
  let u := p ⟨0, by omega⟩
  have hnbr_on_path : ∀ w : V, G.Adj u w → ∃ j : Fin ℓ, p j = w := by
    intro w hw
    by_contra hnot
    push Not at hnot
    apply hmax
    let q : Fin (ℓ + 1) → V := fun i =>
      if h : i.val = 0 then w else p ⟨i.val - 1, by omega⟩
    refine ⟨q, ?_, ?_⟩
    · intro a b hab
      by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
      · exact Fin.ext (by omega)
      · simp only [q, dif_pos ha, dif_neg hb] at hab
        exact absurd hab.symm (hnot _)
      · simp only [q, dif_neg ha, dif_pos hb] at hab
        exact absurd hab (hnot _)
      · simp only [q, dif_neg ha, dif_neg hb] at hab
        have hval : a.val - 1 = b.val - 1 := congrArg Fin.val (hp_inj hab)
        exact Fin.ext (by omega)
    · intro i hi
      by_cases hi0 : i.val = 0
      · simp only [q, dif_pos hi0, dif_neg (by omega : ¬ i.val + 1 = 0)]
        have hz : (⟨i.val + 1 - 1, by omega⟩ : Fin ℓ) = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hz]
        exact hw.symm
      · simp only [q, dif_neg hi0, dif_neg (by omega : ¬ i.val + 1 = 0)]
        have hstep : (⟨i.val + 1 - 1, by omega⟩ : Fin ℓ) = ⟨(i.val - 1) + 1, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        rw [hstep]
        exact hp_adj ⟨i.val - 1, by omega⟩ (by dsimp; omega)
  let J : Finset (Fin ℓ) := Finset.univ.filter (fun j => G.Adj u (p j))
  have hNsub : Finset.univ.filter (G.Adj u) ⊆ J.image p := by
    intro w hw
    have hadj : G.Adj u w := (Finset.mem_filter.mp hw).2
    obtain ⟨j, rfl⟩ := hnbr_on_path w hadj
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hadj⟩, rfl⟩
  have hJcard : d ≤ J.card := by
    calc d ≤ (Finset.univ.filter (G.Adj u)).card := hmindeg u
      _ ≤ (J.image p).card := Finset.card_le_card hNsub
      _ ≤ J.card := Finset.card_image_le
  let Jval : Finset ℕ := J.image Fin.val
  have hJval_card : Jval.card = J.card :=
    Finset.card_image_of_injective J Fin.val_injective
  have hJval_ne : Jval.Nonempty := Finset.card_pos.mp (by omega)
  let jmax := Jval.max' hJval_ne
  have hjmax_mem : jmax ∈ Jval := Finset.max'_mem Jval hJval_ne
  obtain ⟨jm, hjmJ, hjm_eq⟩ := Finset.mem_image.mp hjmax_mem
  have hJval_sub : Jval ⊆ Finset.Icc 1 jmax := by
    intro t ht
    obtain ⟨j, hjJ, rfl⟩ := Finset.mem_image.mp ht
    have hadj : G.Adj u (p j) := (Finset.mem_filter.mp hjJ).2
    have hj_pos : 1 ≤ j.val := by
      by_contra h0
      have hj0 : j = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [hj0] at hadj
      exact G.loopless.irrefl u hadj
    exact Finset.mem_Icc.mpr ⟨hj_pos, Finset.le_max' Jval j.val ht⟩
  have hjmax_ge : d ≤ jmax := by
    have := Finset.card_le_card hJval_sub
    rw [Nat.card_Icc, hJval_card] at this
    omega
  have hjmax_lt : jmax < ℓ := hjm_eq ▸ jm.isLt
  have hwrap : G.Adj (p ⟨jmax, hjmax_lt⟩) (p ⟨0, by omega⟩) := by
    have hadj : G.Adj u (p jm) := (Finset.mem_filter.mp hjmJ).2
    have hjeq : (⟨jmax, hjmax_lt⟩ : Fin ℓ) = jm := Fin.ext hjm_eq.symm
    rw [hjeq]
    exact hadj.symm
  refine ⟨jmax + 1, by omega, ?_⟩
  apply hasCycle_of_fn (by omega) (fun i : Fin (jmax + 1) => p ⟨i.val, by omega⟩)
  · intro a b hab
    have hval : (⟨a.val, by omega⟩ : Fin ℓ).val = (⟨b.val, by omega⟩ : Fin ℓ).val :=
      congrArg Fin.val (hp_inj hab)
    exact Fin.ext hval
  · intro i hi
    exact hp_adj ⟨i.val, by omega⟩ (by dsimp; omega)
  · have hlast : (⟨jmax + 1 - 1, by omega⟩ : Fin ℓ) = ⟨jmax, hjmax_lt⟩ := Fin.ext rfl
    simpa [hlast] using hwrap

/-- Shortcut lemma: a chord of span `d ∈ [2, s - 2]` on `C_s` creates a cycle of length `s - d + 1`. -/
private lemma cycle_shortcut {s : ℕ} (hs : 3 ≤ s) (f : Copy (cycleGraph s) G)
    {a b : Fin s} (hab : a.val < b.val) (hd2 : 2 ≤ b.val - a.val)
    (hL3 : 3 ≤ s - (b.val - a.val) + 1) (hadj : G.Adj (f a) (f b)) :
    (cycleGraph (s - (b.val - a.val) + 1)).IsContained G := by
  have : NeZero s := ⟨by omega⟩
  have h1s : (1 : Fin s).val = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  let d := b.val - a.val
  let L := s - d + 1
  have hds : d ≤ s - 2 := by omega
  let h : Fin L → V := fun r =>
    if r.val ≤ a.val then f ⟨r.val, by omega⟩ else f ⟨r.val + d - 1, by omega⟩
  apply hasCycle_of_fn hL3 h
  · intro r₁ r₂ heq
    by_cases h1 : r₁.val ≤ a.val <;> by_cases h2 : r₂.val ≤ a.val
    · simp only [h, if_pos h1, if_pos h2] at heq
      have hval : (⟨r₁.val, by omega⟩ : Fin s).val = (⟨r₂.val, by omega⟩ : Fin s).val :=
        congrArg Fin.val (f.injective heq)
      exact Fin.ext hval
    · simp only [h, if_pos h1, if_neg h2] at heq
      have hval : r₁.val = r₂.val + d - 1 := congrArg Fin.val (f.injective heq)
      omega
    · simp only [h, if_neg h1, if_pos h2] at heq
      have hval : r₁.val + d - 1 = r₂.val := congrArg Fin.val (f.injective heq)
      omega
    · simp only [h, if_neg h1, if_neg h2] at heq
      have hval : r₁.val + d - 1 = r₂.val + d - 1 := congrArg Fin.val (f.injective heq)
      exact Fin.ext (by omega)
  · intro r hr
    by_cases h1 : r.val + 1 ≤ a.val
    · simp only [h, if_pos (by omega : r.val ≤ a.val), if_pos h1]
      have hsucc : (⟨r.val + 1, by omega⟩ : Fin s) = ⟨r.val, by omega⟩ + 1 := by
        apply Fin.ext
        rw [Fin.val_add, h1s]
        dsimp
        exact (Nat.mod_eq_of_lt (by omega)).symm
      rw [hsucc]
      exact cycle_adj_succ hs f _
    · by_cases h2 : r.val = a.val
      · simp only [h, if_pos (by omega : r.val ≤ a.val), if_neg (by omega : ¬ r.val + 1 ≤ a.val)]
        have ha : (⟨r.val, by omega⟩ : Fin s) = a := Fin.ext h2
        have hb : (⟨r.val + 1 + d - 1, by omega⟩ : Fin s) = b := Fin.ext (by dsimp [d]; omega)
        rw [ha, hb]
        exact hadj
      · simp only [h, if_neg (by omega : ¬ r.val ≤ a.val), if_neg (by omega : ¬ r.val + 1 ≤ a.val)]
        have hsucc : (⟨r.val + 1 + d - 1, by omega⟩ : Fin s) = ⟨r.val + d - 1, by omega⟩ + 1 := by
          apply Fin.ext
          rw [Fin.val_add, h1s]
          dsimp
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hsucc]
        exact cycle_adj_succ hs f _
  · change G.Adj (h ⟨L - 1, by dsimp [L, d]; omega⟩) (h ⟨0, by dsimp [L, d]; omega⟩)
    dsimp only [h]
    rw [if_neg (by dsimp [L, d]; omega), if_pos (Nat.zero_le _)]
    have hsm : (⟨L - 1 + d - 1, by dsimp [L, d]; omega⟩ : Fin s) = ⟨s - 1, by omega⟩ :=
      Fin.ext (by dsimp [L, d]; omega)
    have h0succ : (⟨0, by omega⟩ : Fin s) = ⟨s - 1, by omega⟩ + 1 := by
      apply Fin.ext
      rw [Fin.val_add, h1s]
      dsimp
      have : s - 1 + 1 = s := by omega
      rw [this, Nat.mod_self]
    rw [hsm, h0succ]
    exact cycle_adj_succ hs f _

/-- Main Bondy–Erdős theorem: for `n ≥ 1`, `k ≥ 3`, `k > n ^ 2 - 2`, any graph on at least
`(k - 1) * (n - 1) + 1` vertices contains `C_k` or an independent set of size `n`. -/
private theorem bondy_erdos_aux :
    ∀ (n : ℕ), 1 ≤ n →
      ∀ (k : ℕ), 3 ≤ k → n ^ 2 - 2 < k →
        ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
          (k - 1) * (n - 1) + 1 ≤ Fintype.card V →
          (cycleGraph k).IsContained G ∨ HasIndep G n := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ m ih =>
    intro _ k hk hkn V _ _ G hcard
    by_cases hm0 : m = 0
    · subst hm0
      right
      have hpos : 0 < Fintype.card V := by omega
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
      exact ⟨{v}, Finset.card_singleton v, fun u hu w hw huw => by
        simp only [Finset.mem_singleton] at hu hw
        exact absurd (hu.trans hw.symm) huw⟩
    by_cases hm1 : m = 1
    · subst hm1
      by_cases hex : ∃ u v : V, u ≠ v ∧ ¬ G.Adj u v
      · right
        obtain ⟨u, v, huv, hnadj⟩ := hex
        refine ⟨{u, v}, Finset.card_pair huv, fun x hx y hy hxy => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · exact hnadj
        · exact fun h => hnadj h.symm
        · exact absurd rfl hxy
      · left
        push Not at hex
        have hle : k ≤ Fintype.card V := by omega
        let e : Fin k ↪ V :=
          (Fin.castLEEmb hle).trans (Fintype.equivFin V).symm.toEmbedding
        refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
        intro a b hab
        exact hex (e a) (e b) (fun h => (cycleGraph k).ne_of_adj hab (e.injective h))
    -- Inductive case: n = m + 1 ≥ 3
    have hn3 : 3 ≤ m + 1 := by omega
    have hsq9 : 9 ≤ (m + 1) ^ 2 := by nlinarith
    have hk8 : 8 ≤ k := by omega
    have hsq_lt : m ^ 2 < (m + 1) ^ 2 := by nlinarith
    have hkn_prev : m ^ 2 - 2 < k := by omega
    have ih_prev : ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W),
        (k - 1) * (m - 1) + 1 ≤ Fintype.card W →
        (cycleGraph k).IsContained H ∨ HasIndep H m :=
      fun H hW => ih (by omega) k hk hkn_prev H hW
    have hcard' : (k - 1) * m + 1 ≤ Fintype.card V := by simpa using hcard
    by_contra hcontra
    have hNoCyc : ¬ (cycleGraph k).IsContained G := fun h => hcontra (Or.inl h)
    have hNoInd : ¬ HasIndep G (m + 1) := fun h => hcontra (Or.inr h)
    -- Step 1: Every vertex has degree at least k - 1
    have hmindeg : ∀ v : V, k - 1 ≤ (Finset.univ.filter (G.Adj v)).card := by
      intro v
      by_contra hlt
      push Not at hlt
      let N : Finset V := Finset.univ.filter (G.Adj v)
      have hNlt : N.card < k - 1 := hlt
      let U : Finset V := Finset.univ.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)
      have hcov : (Finset.univ : Finset V) ⊆ insert v (N ∪ U) := by
        intro w _
        by_cases hwv : w = v
        · exact Finset.mem_insert.mpr (Or.inl hwv)
        · apply Finset.mem_insert_of_mem
          by_cases hadj : G.Adj v w
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hadj⟩)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hwv, hadj⟩)
      have hUle : Fintype.card V ≤ 1 + N.card + U.card := by
        calc Fintype.card V = (Finset.univ : Finset V).card := rfl
          _ ≤ (insert v (N ∪ U)).card := Finset.card_le_card hcov
          _ ≤ (N ∪ U).card + 1 := Finset.card_insert_le _ _
          _ ≤ N.card + U.card + 1 := by linarith [Finset.card_union_le N U]
          _ = 1 + N.card + U.card := by omega
      have hUcard : (k - 1) * (m - 1) + 1 ≤ Fintype.card U := by
        rw [Fintype.card_coe]
        have : (k - 1) * m = (k - 1) * (m - 1) + (k - 1) := by
          have hm1' : m = (m - 1) + 1 := by omega
          conv_lhs => rw [hm1', mul_add, mul_one]
        omega
      rcases ih_prev (G.induce (U : Set V)) hUcard with hcyc | hind
      · exact hNoCyc (cycle_of_induce hcyc)
      · obtain ⟨I, hIU, hIcard, hIind⟩ := indep_of_induce hind
        have hvI : v ∉ I := fun hv => (Finset.mem_filter.mp (hIU hv)).2.1 rfl
        apply hNoInd
        refine ⟨insert v I, by rw [Finset.card_insert_of_notMem hvI, hIcard], ?_⟩
        intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hxI <;>
        rcases Finset.mem_insert.mp hy with rfl | hyI
        · exact absurd rfl hxy
        · exact (Finset.mem_filter.mp (hIU hyI)).2.2
        · exact fun h => (Finset.mem_filter.mp (hIU hxI)).2.2 h.symm
        · exact hIind x hxI y hyI hxy
    -- Step 2: G has a cycle of length ≥ k
    have hVne : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨s0, hs0_ge, hs0_cyc⟩ := exists_cycle_of_min_deg G (d := k - 1) (by omega) hVne hmindeg
    -- Step 3: G has no cycle of length r with m₀ ≤ r < k, where m₀ = m * (m - 1) + 1
    let m0 : ℕ := m * (m - 1) + 1
    have hm_mul : m * (m - 1) + m = m * m := by
      calc m * (m - 1) + m = m * (m - 1) + m * 1 := by rw [mul_one]
        _ = m * (m - 1 + 1) := (mul_add m (m - 1) 1).symm
        _ = m * m := by rw [show m - 1 + 1 = m by omega]
    have hm0_ge3 : 3 ≤ m0 := by
      have : 2 ≤ m * (m - 1) := by
        have h2 : 2 ≤ m := by omega
        have h1 : 1 ≤ m - 1 := by omega
        nlinarith
      dsimp [m0]
      omega
    have hm0_lt_k : m0 < k := by
      have hsq : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
      have : m0 ≤ (m + 1) ^ 2 - 2 := by
        dsimp [m0]
        omega
      omega
    have hNoMid : ∀ r : ℕ, m0 ≤ r → r < k → ¬ (cycleGraph r).IsContained G := by
      classical
      by_contra hmid
      push Not at hmid
      let M : Finset ℕ := (Finset.Icc m0 (k - 1)).filter (fun r => (cycleGraph r).IsContained G)
      obtain ⟨r0, hr0_ge, hr0_lt, hr0_cyc⟩ := hmid
      have hMne : M.Nonempty :=
        ⟨r0, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr0_ge, by omega⟩, hr0_cyc⟩⟩
      let r := M.max' hMne
      have hrM : r ∈ M := Finset.max'_mem M hMne
      have hr_ge : m0 ≤ r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hrM).1).1
      have hr_le : r ≤ k - 1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hrM).1).2
      have hr_ge3 : 3 ≤ r := by omega
      have : NeZero r := ⟨by omega⟩
      obtain ⟨f⟩ := (Finset.mem_filter.mp hrM).2
      have hNoR1 : ¬ (cycleGraph (r + 1)).IsContained G := by
        intro hr1
        by_cases hlt : r < k - 1
        · have hmem : r + 1 ∈ M :=
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hr1⟩
          have := Finset.le_max' M (r + 1) hmem
          omega
        · have heqk : r + 1 = k := by omega
          rw [heqk] at hr1
          exact hNoCyc hr1
      let C : Finset V := Finset.univ.image f
      have hCcard : C.card = r := by
        dsimp only [C]
        have hfinj : Function.Injective (⇑f : Fin r → V) := fun a b h => f.injective h
        rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
      let W : Finset V := Finset.univ \ C
      have hWcard : (k - 1) * (m - 1) + 1 ≤ Fintype.card W := by
        rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ C),
          Finset.card_univ, hCcard]
        have : (k - 1) * m = (k - 1) * (m - 1) + (k - 1) := by
          have hm1' : m = (m - 1) + 1 := by omega
          conv_lhs => rw [hm1', mul_add, mul_one]
        omega
      rcases ih_prev (G.induce (W : Set V)) hWcard with hcyc | hind
      · exact hNoCyc (cycle_of_induce hcyc)
      · obtain ⟨I, hIW, hIcard, hIind⟩ := indep_of_induce hind
        let A : V → Finset (Fin r) := fun x => Finset.univ.filter (fun i => G.Adj x (f i))
        have hAbound : ∀ x ∈ I, (A x).card ≤ m - 1 := by
          intro x hxI
          have hxW : x ∈ W := hIW hxI
          have hxC : ∀ i : Fin r, f i ≠ x := by
            intro i heq
            have : x ∈ C := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq⟩
            exact (Finset.mem_sdiff.mp hxW).2 this
          let B : Finset V := (A x).image (fun i => f (i + 1))
          have hBcard : B.card = (A x).card := by
            apply Finset.card_image_of_injective
            intro i j hij
            exact add_right_cancel (f.injective hij)
          have hxB : x ∉ B := by
            intro hmem
            obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
            exact hxC (i + 1) hi
          have hBind : ∀ u ∈ insert x B, ∀ v ∈ insert x B, u ≠ v → ¬ G.Adj u v := by
            intro u hu v hv huv hadj
            rcases Finset.mem_insert.mp hu with rfl | huB <;>
            rcases Finset.mem_insert.mp hv with rfl | hvB
            · exact huv rfl
            · obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.mp hvB
              exact hNoR1 (cycle_extend_of_adj_succ hr_ge3 f hxC
                (Finset.mem_filter.mp hiA).2 hadj)
            · obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.mp huB
              exact hNoR1 (cycle_extend_of_adj_succ hr_ge3 f hxC
                (Finset.mem_filter.mp hiA).2 hadj.symm)
            · obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.mp huB
              obtain ⟨j, hjA, rfl⟩ := Finset.mem_image.mp hvB
              have hij : i ≠ j := fun h => huv (by rw [h])
              exact hNoR1 (cycle_extend_of_crossover hr_ge3 f hxC hij
                (Finset.mem_filter.mp hiA).2 (Finset.mem_filter.mp hjA).2 hadj)
          by_contra hgt
          push Not at hgt
          have hle : m + 1 ≤ (insert x B).card := by
            rw [Finset.card_insert_of_notMem hxB, hBcard]
            omega
          obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hle
          exact hNoInd ⟨S, hScard, fun u hu v hv huv => hBind u (hSsub hu) v (hSsub hv) huv⟩
        have hUcard : (I.biUnion A).card < r := by
          calc (I.biUnion A).card
              ≤ ∑ x ∈ I, (A x).card := Finset.card_biUnion_le
            _ ≤ ∑ _x ∈ I, (m - 1) := Finset.sum_le_sum hAbound
            _ = I.card * (m - 1) := by rw [Finset.sum_const, smul_eq_mul]
            _ = m * (m - 1) := by rw [hIcard]
            _ < r := by omega
        have hcompl_ne : ((Finset.univ : Finset (Fin r)) \ I.biUnion A).Nonempty := by
          apply Finset.card_pos.mp
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
          omega
        obtain ⟨j, hj⟩ := hcompl_ne
        have hj_not : j ∉ I.biUnion A := (Finset.mem_sdiff.mp hj).2
        have hfj_not_I : f j ∉ I := by
          intro hmem
          have : f j ∈ C := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
          exact (Finset.mem_sdiff.mp (hIW hmem)).2 this
        apply hNoInd
        refine ⟨insert (f j) I, by rw [Finset.card_insert_of_notMem hfj_not_I, hIcard], ?_⟩
        intro u hu v hv huv
        rcases Finset.mem_insert.mp hu with rfl | huI <;>
        rcases Finset.mem_insert.mp hv with rfl | hvI
        · exact absurd rfl huv
        · intro hadj
          exact hj_not (Finset.mem_biUnion.mpr ⟨v, hvI, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hadj.symm⟩⟩)
        · intro hadj
          exact hj_not (Finset.mem_biUnion.mpr ⟨u, huI, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hadj⟩⟩)
        · exact hIind u huI v hvI huv
    -- Step 4: Take a shortest cycle of length ≥ m₀; its even indices form an independent set of size m + 1
    classical
    have hex_s : ∃ s : ℕ, m0 ≤ s ∧ (cycleGraph s).IsContained G := ⟨s0, by omega, hs0_cyc⟩
    let s := Nat.find hex_s
    have hs_spec : m0 ≤ s ∧ (cycleGraph s).IsContained G := Nat.find_spec hex_s
    have hs_gt_k : k < s := by
      by_contra hle
      push Not at hle
      by_cases heq : s = k
      · exact hNoCyc (heq ▸ hs_spec.2)
      · exact hNoMid s hs_spec.1 (by omega) hs_spec.2
    have hs_ge_sq : (m + 1) ^ 2 ≤ s := by omega
    have hspan_bound : 2 * m ≤ s - m0 + 1 := by
      have hsq : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
      have hm0_eq : m0 + m = m * m + 1 := by dsimp [m0]; omega
      omega
    obtain ⟨f⟩ := hs_spec.2
    have hno_chord : ∀ a b : Fin s, a.val < b.val → 2 ≤ b.val - a.val →
        b.val - a.val ≤ s - m0 + 1 → ¬ G.Adj (f a) (f b) := by
      intro a b hab hd2 hdu hadj
      have hL_ge : m0 ≤ s - (b.val - a.val) + 1 := by omega
      have hL_lt : s - (b.val - a.val) + 1 < s := by omega
      have hcyc := cycle_shortcut (by omega) f hab hd2 (by omega) hadj
      exact Nat.find_min hex_s hL_lt ⟨hL_ge, hcyc⟩
    have h2lt : ∀ t : Fin (m + 1), 2 * t.val < s :=
      fun t => lt_of_lt_of_le (by nlinarith [t.isLt]) hs_ge_sq
    let emb : Fin (m + 1) → V := fun i => f ⟨2 * i.val, h2lt i⟩
    have hemb_inj : Function.Injective emb := by
      intro i j hij
      have hval : 2 * i.val = 2 * j.val := congrArg Fin.val (f.injective hij)
      exact Fin.ext (by omega)
    let S : Finset V := Finset.univ.image emb
    apply hNoInd
    refine ⟨S, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fin]
    · intro u hu v hv huv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      have hij : i.val ≠ j.val := fun h => huv (by rw [Fin.ext h])
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact hno_chord ⟨2 * i.val, h2lt i⟩ ⟨2 * j.val, h2lt j⟩
          (by dsimp; omega) (by dsimp; omega) (by dsimp; have := i.isLt; have := j.isLt; omega)
      · intro hadj
        exact hno_chord ⟨2 * j.val, h2lt j⟩ ⟨2 * i.val, h2lt i⟩
          (by dsimp; omega) (by dsimp; omega) (by dsimp; have := i.isLt; have := j.isLt; omega) hadj.symm

end Helpers

end OMA.P_Erdos551_erdos_551_variants_sufficiently_large_R1_H1

theorem OMA.solution : OMA.R_Erdos551_erdos_551_variants_sufficiently_large_R1.H1 := by
  intro n k hn hk C
  have h9 : 9 ≤ n ^ 2 := by nlinarith
  have hk3 : 3 ≤ k := by omega
  have hcard : (k - 1) * (n - 1) + 1 ≤ Fintype.card (Fin ((k - 1) * (n - 1) + 1)) := by
    rw [Fintype.card_fin]
  rcases OMA.P_Erdos551_erdos_551_variants_sufficiently_large_R1_H1.bondy_erdos_aux
      n (by omega) k hk3 hk C hcard with hcyc | hind
  · exact Or.inl hcyc
  · exact Or.inr (OMA.P_Erdos551_erdos_551_variants_sufficiently_large_R1_H1.hasIndep_imp_contained hind)
