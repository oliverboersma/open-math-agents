import FormalConjectures.ErdosProblems.«61»

/-!
The Erdős–Hajnal bound for the five-cycle.

The critical-graph argument and the use of combs follow Chudnovsky, Scott,
Seymour, and Spirkl, [Erdős–Hajnal for graphs with no 5-hole](https://arxiv.org/abs/2102.04994),
Sections 2–4. The sparse-side argument follows Fox and Sudakov,
[Induced Ramsey-type theorems](https://arxiv.org/abs/0706.4112), Section 2.
-/

open SimpleGraph
open scoped BigOperators

namespace FiveHole

def Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ Nonempty (cycleGraph 5 ↪g G)

private def selfComplementary : cycleGraph 5 ≃g (cycleGraph 5)ᶜ where
  toFun := ![0, 2, 4, 1, 3]
  invFun := ![0, 3, 1, 4, 2]
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

theorem free_compl {V : Type*} {G : SimpleGraph V} (h : Free G) : Free Gᶜ := by
  rintro ⟨f⟩
  apply h
  have θ : (cycleGraph 5)ᶜ ↪g Gᶜ := f.comp selfComplementary.symm.toEmbedding
  exact ⟨Embedding.complEquiv.symm θ⟩

theorem free_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Free G) (f : H ↪g G) : Free H := by
  rintro ⟨e⟩
  exact h ⟨f.comp e⟩

theorem free_iff_comap {V : Type*} {G : SimpleGraph V} :
    Free G ↔ ¬ ∃ f : Fin 5 ↪ V, cycleGraph 5 = G.comap f := by
  constructor
  · rintro h ⟨f, hf⟩
    apply h
    refine ⟨⟨f, ?_⟩⟩
    intro x y
    rw [hf]
    rfl
  · rintro h ⟨e⟩
    apply h
    refine ⟨e.toEmbedding, ?_⟩
    ext x y
    exact e.map_adj_iff.symm

structure RootedComb {V : Type*} (G : SimpleGraph V) (t : ℕ) where
  root : V
  tooth : Fin t ↪ V
  block : Fin t → Finset V
  disjoint : Pairwise (Function.onFun Disjoint block)
  rise : ∀ i, G.Adj root (tooth i)
  stable : ∀ {i j}, i ≠ j → ¬ G.Adj (tooth i) (tooth j)
  root_not_mem : ∀ i, root ∉ block i
  tooth_not_mem : ∀ i j, tooth i ∉ block j
  cross : ∀ i j b, b ∈ block j → (G.Adj (tooth i) b ↔ i = j)
  root_miss : ∀ i b, b ∈ block i → ¬ G.Adj root b

private theorem reverse_not_adj {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : ¬ G.Adj u v) : ¬ G.Adj v u :=
  fun he => h he.symm

theorem RootedComb.anticomplete {V : Type*} {G : SimpleGraph V} {t : ℕ}
    (C : RootedComb G t) (hG : Free G) {i j : Fin t} (hij : i ≠ j)
    {b c : V} (hb : b ∈ C.block i) (hc : c ∈ C.block j) : ¬ G.Adj b c := by
  intro hbc
  apply hG
  let f : Fin 5 → V := ![C.root, C.tooth i, b, c, C.tooth j]
  have hri : C.root ≠ C.tooth i := (C.rise i).ne
  have hrj : C.root ≠ C.tooth j := (C.rise j).ne
  have hbi : C.tooth i ≠ b := ((C.cross i i b hb).mpr rfl).ne
  have hcj : C.tooth j ≠ c := ((C.cross j j c hc).mpr rfl).ne
  have hrc : C.root ≠ c := fun he => C.root_not_mem j (he ▸ hc)
  have hrb : C.root ≠ b := fun he => C.root_not_mem i (he ▸ hb)
  have hic : C.tooth i ≠ c := fun he => C.tooth_not_mem i j (he ▸ hc)
  have hjb : C.tooth j ≠ b := fun he => C.tooth_not_mem j i (he ▸ hb)
  have hteeth : C.tooth i ≠ C.tooth j := fun he => hij (C.tooth.injective he)
  have hfi : Function.Injective f := by
    intro u v e
    fin_cases u <;> fin_cases v <;>
      simp only [f] at e <;>
      first | rfl | exact False.elim (by solve_by_elim [Ne.symm, SimpleGraph.Adj.ne])
  refine ⟨⟨⟨f, hfi⟩, ?_⟩⟩
  have hib : G.Adj (C.tooth i) b := (C.cross i i b hb).mpr rfl
  have hjc : G.Adj (C.tooth j) c := (C.cross j j c hc).mpr rfl
  have hnic : ¬ G.Adj (C.tooth i) c := fun h => hij ((C.cross i j c hc).mp h)
  have hnjb : ¬ G.Adj (C.tooth j) b := fun h => hij.symm ((C.cross j i b hb).mp h)
  have hnij : ¬ G.Adj (C.tooth i) (C.tooth j) := C.stable hij
  have hnrb := C.root_miss i b hb
  have hnrc := C.root_miss j c hc
  intro u v
  change G.Adj (f u) (f v) ↔ (cycleGraph 5).Adj u v
  fin_cases u <;> fin_cases v <;>
    simp only [f] <;>
    first
      | exact iff_of_true (by solve_by_elim [C.rise, SimpleGraph.Adj.symm]) (by decide)
      | exact iff_of_false (by solve_by_elim [SimpleGraph.irrefl, reverse_not_adj]) (by decide)

noncomputable def independenceIn {V : Type*} (G : SimpleGraph V) (A : Finset V) : ℕ :=
  (G.induce (A : Set V)).indepNum

theorem exists_independent_in {V : Type*} (G : SimpleGraph V) (A : Finset V) :
    ∃ S : Finset V, S ⊆ A ∧ G.IsIndepSet (S : Set V) ∧ S.card = independenceIn G A := by
  classical
  obtain ⟨S, hS⟩ := (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  let val : (A : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨S.map val, ?_, ?_, by simpa [independenceIn] using hS.card_eq⟩
  · intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hx
    exact u.property
  · intro x hx y hy hxy hxyAdj
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact hS.isIndepSet hu hv (fun eq => hxy (congrArg val eq)) hxyAdj

theorem sum_independence_le {V : Type*} [Finite V] {I : Type*} [Fintype I]
    {G : SimpleGraph V} {A : I → Finset V}
    (hD : Pairwise (Function.onFun Disjoint A))
    (hA : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, ¬ G.Adj x y) :
    ∑ i, independenceIn G (A i) ≤ G.indepNum := by
  classical
  choose S hsub hS hcard using fun i => exists_independent_in G (A i)
  let U := Finset.univ.biUnion S
  have hdS : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint S := by
    intro i _ j _ hij
    exact Disjoint.mono (hsub i) (hsub j) (hD hij)
  have hU : G.IsIndepSet (U : Set V) := by
    intro x hx y hy hxy
    obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, _, hy⟩ := Finset.mem_biUnion.mp hy
    by_cases hij : i = j
    · subst j
      exact hS i hx hy hxy
    · exact hA i j hij x (hsub i hx) y (hsub j hy)
  have hu := hU.card_le_indepNum
  change (Finset.univ.biUnion S).card ≤ G.indepNum at hu
  simpa only [Finset.card_biUnion hdS, hcard] using hu

noncomputable def profile {V : Type*} (G : SimpleGraph V) : ℝ :=
  (G.indepNum : ℝ) * G.cliqueNum

@[simp] theorem profile_compl {V : Type*} (G : SimpleGraph V) :
    profile Gᶜ = profile G := by
  simp [profile, mul_comm]

def Critical {V : Type*} [Fintype V] (G : SimpleGraph V) (τ : ℝ) : Prop :=
  profile G < (Fintype.card V : ℝ) ^ τ ∧
    ∀ A : Finset V, A.card < Fintype.card V →
      (A.card : ℝ) ^ τ ≤ profile (G.induce (A : Set V))

theorem critical_compl {V : Type*} [Fintype V] {G : SimpleGraph V} {τ : ℝ}
    (hG : Critical G τ) : Critical Gᶜ τ := by
  refine ⟨by simpa using hG.1, fun A hA => ?_⟩
  have h : Gᶜ.induce (A : Set V) = (G.induce (A : Set V))ᶜ := by
    ext x y
    change ((x : V) ≠ (y : V) ∧ ¬ G.Adj x y) ↔ x ≠ y ∧ ¬ G.Adj x y
    exact and_congr_left' (not_congr Subtype.val_injective.eq_iff)
  simpa only [h, profile_compl] using hG.2 A hA

theorem RootedComb.excludes_critical {V : Type*} [Fintype V]
    {G : SimpleGraph V} {τ δ : ℝ} {t : ℕ}
    (C : RootedComb G t) (hG : Free G) (hcrit : Critical G τ)
    (hτ : 0 < τ) (hδ : 0 < δ) (ht : 2 ≤ t)
    (hfactor : 1 ≤ δ ^ τ * (2 : ℝ) ^ (1 - 2 * τ))
    (hτsmall : 2 * τ ≤ 1)
    (hsize : ∀ i, δ * (Fintype.card V : ℝ) / (t : ℝ) ^ 2 ≤ (C.block i).card) :
    False := by
  classical
  have hsum := sum_independence_le C.disjoint
    (fun _ _ hij _ hb _ hc => C.anticomplete hG hij hb hc)
  have hsumR : (∑ i, (independenceIn G (C.block i) : ℝ)) ≤ G.indepNum := by
    exact_mod_cast hsum
  have hω : 0 ≤ (G.cliqueNum : ℝ) := Nat.cast_nonneg _
  have hblock : ∀ i, (δ * (Fintype.card V : ℝ) / (t : ℝ) ^ 2) ^ τ ≤
      (independenceIn G (C.block i) : ℝ) * G.cliqueNum := by
    intro i
    have hproper : (C.block i).card < Fintype.card V := by
      rw [← Finset.card_univ]
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, fun eq =>
        C.root_not_mem i (eq ▸ Finset.mem_univ _)⟩
    calc
      _ ≤ ((C.block i).card : ℝ) ^ τ :=
        Real.rpow_le_rpow (by positivity) (hsize i) hτ.le
      _ ≤ profile (G.induce (C.block i : Set V)) := hcrit.2 _ hproper
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by exact_mod_cast G.cliqueNum_induce_le (C.block i : Set V))
        (Nat.cast_nonneg _)
  have hcount : (t : ℝ) * (δ * (Fintype.card V : ℝ) / (t : ℝ) ^ 2) ^ τ ≤ profile G := by
    have hs := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin t))) => hblock i
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right hsumR hω)
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have hfactor' : 1 ≤ δ ^ τ * (t : ℝ) ^ (1 - 2 * τ) :=
    hfactor.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by norm_num) ht' (sub_nonneg.mpr hτsmall)) (by positivity))
  have hpower :
      (t : ℝ) * (δ * (Fintype.card V : ℝ) / (t : ℝ) ^ 2) ^ τ =
        (δ ^ τ * (t : ℝ) ^ (1 - 2 * τ)) * (Fintype.card V : ℝ) ^ τ := by
    rw [Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow hδ.le (by positivity), ← Real.rpow_natCast_mul ht0.le,
      Real.rpow_sub ht0, Real.rpow_one]
    field_simp
    ring_nf
  rw [hpower] at hcount
  exact hcrit.1.not_ge ((le_mul_of_one_le_left (by positivity) hfactor').trans hcount)

theorem finish {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hτsmall : 2 * τ ≤ 1) (hfactor : 1 ≤ δ ^ τ * (2 : ℝ) ^ (1 - 2 * τ))
    (hcomb : ∀ {V : Type} [Fintype V] (G : SimpleGraph V), Free G → Critical G τ →
      ∃ t ≥ (2 : ℕ),
        (∃ C : RootedComb G t, ∀ i, δ * (Fintype.card V : ℝ) / (t : ℝ) ^ 2 ≤
          (C.block i).card) ∨
        (∃ C : RootedComb Gᶜ t, ∀ i, δ * (Fintype.card V : ℝ) / (t : ℝ) ^ 2 ≤
          (C.block i).card)) :
    ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound (cycleGraph 5)
      (fun n : ℕ => (n : ℝ) ^ c) := by
  classical
  have hprofile (n : ℕ) : ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n → Free G → (n : ℝ) ^ τ ≤ profile G := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V inst G hn hfree
      by_contra! hlt
      have hcrit : Critical G τ := by
        refine ⟨by simpa [hn] using hlt, fun A hA => ?_⟩
        exact ih A.card (by simpa [hn] using hA) (G.induce (A : Set V))
          (Fintype.card_coe A) (free_of_embedding hfree (Embedding.induce (A : Set V)))
      obtain ⟨t, ht, hC | hC⟩ := hcomb G hfree hcrit
      · obtain ⟨C, hsize⟩ := hC
        exact C.excludes_critical hfree hcrit hτ hδ ht hfactor hτsmall hsize
      · obtain ⟨C, hsize⟩ := hC
        exact C.excludes_critical (free_compl hfree) (critical_compl hcrit)
          hτ hδ ht hfactor hτsmall hsize
  refine ⟨τ / 2, by positivity, Filter.Eventually.of_forall fun n G hG => ?_⟩
  have hp := hprofile n G (Fintype.card_fin n) (free_iff_comap.mpr hG)
  have hsquare : ((n : ℝ) ^ (τ / 2)) ^ (2 : ℕ) = (n : ℝ) ^ τ := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg n)]
    congr 1
    push_cast
    ring
  by_contra! h
  rw [← hsquare, sq, profile] at hp
  have hstrict := mul_lt_mul'' h.1 h.2
    (Nat.cast_nonneg G.indepNum) (Nat.cast_nonneg G.cliqueNum)
  exact hp.not_gt hstrict

end FiveHole

namespace FiveHole

noncomputable def neighborsIn {V : Type*} (G : SimpleGraph V) (x : V) (U : Finset V) :
    Finset V := by
  classical
  exact U.filter (G.Adj x)

@[simp] theorem mem_neighborsIn {V : Type*} {G : SimpleGraph V} {x y : V} {U : Finset V} :
    y ∈ neighborsIn G x U ↔ y ∈ U ∧ G.Adj x y := by
  classical
  simp [neighborsIn]

theorem neighborsIn_mono {V : Type*} {G : SimpleGraph V} {x : V} {U W : Finset V}
    (h : U ⊆ W) : neighborsIn G x U ⊆ neighborsIn G x W := by
  intro y hy
  exact mem_neighborsIn.mpr ⟨h (mem_neighborsIn.mp hy).1, (mem_neighborsIn.mp hy).2⟩

structure BipartiteComb {V : Type*} (G : SimpleGraph V) (A B : Finset V) (t : ℕ) where
  tooth : Fin t ↪ V
  tooth_mem : ∀ i, tooth i ∈ A
  block : Fin t → Finset V
  block_sub : ∀ i, block i ⊆ B
  disjoint : Pairwise (Function.onFun Disjoint block)
  cross : ∀ i j x, x ∈ block j → (G.Adj (tooth i) x ↔ i = j)

def BipartiteComb.toRooted {V : Type*} {G : SimpleGraph V} {A B : Finset V} {t : ℕ}
    (C : BipartiteComb G A B t) (r : V) (hAB : Disjoint A B) (hA : G.IsIndepSet (A : Set V))
    (hrA : ∀ a ∈ A, G.Adj r a) (hrB : ∀ b ∈ B, r ≠ b ∧ ¬ G.Adj r b) : RootedComb G t where
  root := r
  tooth := C.tooth
  block := C.block
  disjoint := C.disjoint
  rise i := hrA _ (C.tooth_mem i)
  stable hij := hA (C.tooth_mem _) (C.tooth_mem _) (fun he => hij (C.tooth.injective he))
  root_not_mem i hr := (hrB r (C.block_sub i hr)).1 rfl
  tooth_not_mem i j hz := Finset.disjoint_left.mp hAB (C.tooth_mem i) (C.block_sub j hz)
  cross := C.cross
  root_miss i b hb := (hrB b (C.block_sub i hb)).2

def BipartiteBound {V : Type*} (G : SimpleGraph V) (K : ℝ) : Prop :=
  ∀ (A B : Finset V) (Γ Δ : ℝ), 0 < Γ → 0 ≤ Δ → Disjoint A B →
    (∀ b ∈ B, ∃ a ∈ A, G.Adj a b) →
    (∀ a ∈ A, (neighborsIn G a B).card ≤ Δ) →
    (∃ t > (0 : ℕ), ∃ C : BipartiteComb G A B t,
      ∀ i, Γ / (t : ℝ)^2 ≤ (C.block i).card) ∨ (B.card : ℝ) ≤ K * Real.sqrt (Γ * Δ)

theorem independent_in_critical {V : Type*} [Fintype V] {G : SimpleGraph V} {τ : ℝ}
    (hcrit : Critical G τ) {A : Finset V} (hA : A.card < Fintype.card V) :
    ∃ C : Finset V, C ⊆ A ∧ G.IsIndepSet (C : Set V) ∧
      (A.card : ℝ) ^ τ ≤ (C.card : ℝ) * G.cliqueNum := by
  obtain ⟨C, hCA, hC, hcard⟩ := exists_independent_in G A
  refine ⟨C, hCA, hC, (hcrit.2 A hA).trans ?_⟩
  rw [hcard]
  apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact_mod_cast G.cliqueNum_induce_le (A : Set V)

private theorem neighborhood_budget {W a d ε τ K : ℝ} (hW : 0 < W)
    (ha : 0 ≤ a) (hε : 0 < ε) (hε1 : ε ≤ 1) (ha' : a ≤ ε * W)
    (hτ : 0 < τ) (hτ' : τ ≤ 1/4) (hK : 0 ≤ K)
    (hd : d ≤ K * Real.sqrt ((2 * W) * a))
    (hnum : ε ^ (3/4 : ℝ) + (K * Real.sqrt 2) * ε ^ (1/4 : ℝ) ≤ 1/4) :
    a + d ≤ (1/4 : ℝ) * a ^ τ * W ^ (1 - τ) := by
  let x := a / W
  have hx0 : 0 ≤ x := div_nonneg ha hW.le
  have hxε : x ≤ ε := (div_le_iff₀ hW).mpr ha'
  have hxa : x * W = a := div_mul_cancel₀ _ hW.ne'
  have hf₁ : x ^ (1 - τ) ≤ ε ^ (3/4 : ℝ) :=
    (Real.rpow_le_rpow hx0 hxε (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith))
  have hf₂ : x ^ (1/2 - τ) ≤ ε ^ (1/4 : ℝ) :=
    (Real.rpow_le_rpow hx0 hxε (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith))
  have heq₁ : x ^ τ * x ^ (1 - τ) = x := by
    rw [← Real.rpow_add' hx0 (by norm_num), show τ + (1 - τ) = 1 by ring, Real.rpow_one]
  have heq₂ : x ^ τ * x ^ (1/2 - τ) = Real.sqrt x := by
    rw [← Real.rpow_add' hx0 (by norm_num), show τ + (1/2 - τ) = 1/2 by ring,
      Real.sqrt_eq_rpow]
  have heq₃ : Real.sqrt ((2 * W) * a) = Real.sqrt 2 * W * Real.sqrt x := by
    rw [← hxa, show (2 * W) * (x * W) = (2 * x) * (W * W) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_mul_self hW.le]
    ring
  have heq₄ : x ^ τ * W = a ^ τ * W ^ (1 - τ) := by
    dsimp [x]
    rw [Real.div_rpow ha hW.le, Real.rpow_sub hW, Real.rpow_one]
    ring
  have hest : x + (K * Real.sqrt 2) * Real.sqrt x ≤ (1/4 : ℝ) * x ^ τ := by
    calc
      _ = (x ^ (1 - τ) + (K * Real.sqrt 2) * x ^ (1/2 - τ)) * x ^ τ := by
        linear_combination (norm := ring_nf) -heq₁ - (K * Real.sqrt 2) * heq₂
      _ ≤ (ε ^ (3/4 : ℝ) + (K * Real.sqrt 2) * ε ^ (1/4 : ℝ)) * x ^ τ :=
        mul_le_mul_of_nonneg_right
          (add_le_add hf₁ (mul_le_mul_of_nonneg_left hf₂ (by positivity))) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hnum (by positivity)
  calc
    a + d ≤ a + K * Real.sqrt ((2 * W) * a) := add_le_add_right hd _
    _ = (x + (K * Real.sqrt 2) * Real.sqrt x) * W := by rw [heq₃, ← hxa]; ring
    _ ≤ ((1/4 : ℝ) * x ^ τ) * W := mul_le_mul_of_nonneg_right hest hW.le
    _ = _ := by rw [mul_assoc, heq₄]; ring

/-- Without a large rooted comb, each greedy deletion charges its size to two independent sets. -/
private theorem comb_or_budget {V : Type*} [Fintype V] {G : SimpleGraph V}
    {X : Finset V} {ε τ K : ℝ} (hX : X.Nonempty)
    (hcrit : Critical G τ) (hbi : BipartiteBound G K)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) (hτ' : τ ≤ 1/4) (hK : 0 ≤ K)
    (hnum : ε ^ (3/4 : ℝ) + (K * Real.sqrt 2) * ε ^ (1/4 : ℝ) ≤ 1/4)
    (hdeg : ∀ x ∈ X, (neighborsIn G x X).card ≤ ε * (X.card : ℝ)) :
    (∃ t ≥ (2 : ℕ), ∃ C : RootedComb G t, ∀ i, (2 * (X.card : ℝ)) / (t : ℝ)^2 ≤
      (C.block i).card) ∨
    (X.card : ℝ) ≤ profile G * (1/4 : ℝ) * (X.card : ℝ) ^ (1 - τ) + G.indepNum := by
  classical
  let W : ℝ := X.card
  have hW : 0 < W := by dsimp [W]; exact_mod_cast Finset.card_pos.mpr hX
  by_cases he : ∃ t ≥ (2 : ℕ), ∃ C : RootedComb G t, ∀ i, (2 * (X.card : ℝ)) /
      (t : ℝ)^2 ≤ (C.block i).card
  · exact Or.inl he
  apply Or.inr
  let L : ℝ := (1/4 : ℝ) * G.cliqueNum * W ^ (1 - τ)
  have hL : 0 ≤ L := by unfold L; positivity
  have recBudget (n : ℕ) : ∀ U : Finset V, U ⊆ X → U.card = n →
      ∃ R S : Finset V, R ⊆ U ∧ S ⊆ U ∧ G.IsIndepSet (R : Set V) ∧
        G.IsIndepSet (S : Set V) ∧ (U.card : ℝ) ≤ R.card + L * S.card := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hUX hUn
      by_cases hU : U.Nonempty
      swap
      · have hu := Finset.not_nonempty_iff_eq_empty.mp hU
        subst U
        exact ⟨∅, ∅, by simp⟩
      obtain ⟨r, hr, hmax⟩ := Finset.exists_max_image U
        (fun v => (neighborsIn G v U).card) hU
      let A := neighborsIn G r U
      have hA : A ⊆ U := fun _ hx => (mem_neighborsIn.mp hx).1
      have hrA : r ∉ A := by simp [A]
      have hAsc : A.card < Fintype.card V := by
        rw [← Finset.card_univ]
        apply Finset.card_lt_card
        exact ⟨Finset.subset_univ _, fun h => hrA (h (Finset.mem_univ _))⟩
      obtain ⟨C, hCA, hC, hCa⟩ := independent_in_critical hcrit hAsc
      let B := U \ insert r A
      let D := B.filter (fun b => ∃ a ∈ C, G.Adj a b)
      let E := B \ D
      have hDB : D ⊆ B := Finset.filter_subset _ _
      have hBU : B ⊆ U := Finset.sdiff_subset
      have hEU : E ⊆ U := Finset.sdiff_subset.trans hBU
      have hins : insert r A ⊆ U := Finset.insert_subset_iff.mpr ⟨hr, hA⟩
      have hBA : Disjoint B (insert r A) := Finset.disjoint_left.mpr
        (fun _ hx hy => (Finset.mem_sdiff.mp hx).2 hy)
      have hCD : Disjoint C D := by
        apply Finset.disjoint_left.mpr
        intro x hxC hxD
        exact Finset.disjoint_left.mp hBA (hDB hxD) (Finset.mem_insert_of_mem (hCA hxC))
      have hRD : ∀ b ∈ D, r ≠ b ∧ ¬ G.Adj r b := by
        intro b hb
        have hn := (Finset.mem_sdiff.mp (hDB hb)).2
        exact ⟨fun h => hn (Finset.mem_insert.mpr (Or.inl h.symm)),
          fun h => hn (Finset.mem_insert_of_mem (mem_neighborsIn.mpr ⟨hBU (hDB hb), h⟩))⟩
      have hDcover : ∀ b ∈ D, ∃ a ∈ C, G.Adj a b := fun b hb => (Finset.mem_filter.mp hb).2
      have hDdeg : ∀ a ∈ C, (neighborsIn G a D).card ≤ (A.card : ℝ) := by
        intro a ha
        exact_mod_cast (Finset.card_le_card (neighborsIn_mono (hDB.trans hBU))).trans
          (hmax a (hA (hCA ha)))
      have hAbound : (A.card : ℝ) ≤ ε * W := by
        have hm : (A.card : ℝ) ≤ (neighborsIn G r X).card := by
          exact_mod_cast Finset.card_le_card (neighborsIn_mono (G := G) (x := r) hUX)
        exact hm.trans (hdeg r (hUX hr))
      have hDbound : (D.card : ℝ) ≤ K * Real.sqrt ((2 * W) * (A.card : ℝ)) := by
        rcases hbi C D (2 * W) A.card (by positivity) (Nat.cast_nonneg _) hCD hDcover hDdeg with
          ⟨t, ht, Q, hwidth⟩ | hbound
        · exfalso
          have hp : t ≠ 1 := by
            intro ht'
            subst t
            have hb : (Q.block 0).card ≤ X.card :=
              Finset.card_le_card ((Q.block_sub 0).trans (hDB.trans (hBU.trans hUX)))
            have hbR : ((Q.block 0).card : ℝ) ≤ W := by dsimp [W]; exact_mod_cast hb
            have hwidth' : 2 * W ≤ (Q.block 0).card := by simpa using hwidth 0
            linarith
          have htr : ∀ a ∈ C, G.Adj r a := fun _ ha => (mem_neighborsIn.mp (hCA ha)).2
          exact he ⟨t, by omega, Q.toRooted r hCD hC htr hRD, hwidth⟩
        · exact hbound
      have hlocal : (A.card : ℝ) + D.card ≤ L * C.card := by
        calc
          _ ≤ (1/4 : ℝ) * (A.card : ℝ)^τ * W^(1-τ) :=
            neighborhood_budget hW (Nat.cast_nonneg _) hε hε1 hAbound hτ hτ' hK hDbound hnum
          _ ≤ (1/4 : ℝ) * ((C.card : ℝ) * G.cliqueNum) * W^(1-τ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCa (by norm_num))
              (by positivity)
          _ = _ := by dsimp [L]; ring
      have hsplit : E.card + D.card + (A.card + 1) = U.card := by
        have h₁ := Finset.card_sdiff_add_card_eq_card hDB
        have h₂ := Finset.card_sdiff_add_card_eq_card hins
        rw [Finset.card_insert_of_notMem hrA] at h₂
        exact (congrArg (fun k : ℕ => k + (A.card + 1)) h₁).trans h₂
      have hecard : E.card < n := by omega
      obtain ⟨R, S, hRE, hSE, hRI, hSI, hrec⟩ := ih E.card hecard E (hEU.trans hUX) rfl
      have no_root {x : V} (hx : x ∈ E) : r ≠ x ∧ ¬ G.Adj r x := by
        have hn := (Finset.mem_sdiff.mp (Finset.sdiff_subset hx : x ∈ B)).2
        exact ⟨fun h => hn (Finset.mem_insert.mpr (Or.inl h.symm)),
          fun h => hn (Finset.mem_insert_of_mem (mem_neighborsIn.mpr ⟨hEU hx, h⟩))⟩
      have no_cross {a x : V} (ha : a ∈ C) (hx : x ∈ E) : ¬ G.Adj a x := by
        intro h
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr
          ⟨Finset.sdiff_subset hx, a, ha, h⟩)
      have hrR : r ∉ R := fun h => (no_root (hRE h)).1 rfl
      have hCS : Disjoint C S := by
        apply Finset.disjoint_left.mpr
        intro x hxC hxS
        exact Finset.disjoint_left.mp hBA (Finset.sdiff_subset (hSE hxS))
          (Finset.mem_insert_of_mem (hCA hxC))
      refine ⟨insert r R, C ∪ S, Finset.insert_subset_iff.mpr ⟨hr, hRE.trans hEU⟩,
        Finset.union_subset (hCA.trans hA) (hSE.trans hEU), ?_, ?_, ?_⟩
      · intro x hx y hy hxy
        change x ∈ insert r R at hx
        change y ∈ insert r R at hy
        rcases Finset.mem_insert.mp hx with hxr | hxR
        · subst x
          rcases Finset.mem_insert.mp hy with hyr | hyR
          · exact (hxy hyr.symm).elim
          · exact (no_root (hRE hyR)).2
        · rcases Finset.mem_insert.mp hy with hyr | hyR
          · subst y
            exact reverse_not_adj (no_root (hRE hxR)).2
          · exact hRI hxR hyR hxy
      · intro x hx y hy hxy
        rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
        · exact hC hx hy hxy
        · exact no_cross hx (hSE hy)
        · exact reverse_not_adj (no_cross hy (hSE hx))
        · exact hSI hx hy hxy
      · rw [Finset.card_insert_of_notMem hrR, Finset.card_union_of_disjoint hCS]
        push_cast
        have hsplitR : (E.card : ℝ) + D.card + ((A.card : ℝ) + 1) = U.card := by
          exact_mod_cast hsplit
        linarith
  obtain ⟨R, S, _, _, hR, hS, hRS⟩ := recBudget X.card X (Finset.Subset.refl _) rfl
  have hR' : (R.card : ℝ) ≤ G.indepNum := by exact_mod_cast hR.card_le_indepNum
  have hS' : (S.card : ℝ) ≤ G.indepNum := by exact_mod_cast hS.card_le_indepNum
  calc
    _ ≤ (R.card : ℝ) + L * S.card := hRS
    _ ≤ (G.indepNum : ℝ) + L * G.indepNum :=
      add_le_add hR' (mul_le_mul_of_nonneg_left hS' hL)
    _ = _ := by dsimp [L, profile, W]; ring

end FiveHole

namespace FiveHole

theorem neighborsIn_card_sdiff_add {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a : V}
    {P B : Finset V} (h : P ⊆ B) :
    (neighborsIn G a (B \ P)).card + (neighborsIn G a P).card =
      (neighborsIn G a B).card := by
  classical
  have heq : neighborsIn G a (B \ P) = neighborsIn G a B \ neighborsIn G a P := by
    ext b
    simp only [mem_neighborsIn, Finset.mem_sdiff]
    tauto
  rw [heq, Finset.card_sdiff_add_card_eq_card (neighborsIn_mono h)]

private noncomputable def touched {V : Type*} (G : SimpleGraph V) (S P : Finset V) :
    Finset V := by
  classical
  exact S.biUnion (fun x => neighborsIn G x P)

private theorem mem_touched {V : Type*} {G : SimpleGraph V} {S P : Finset V} {b : V} :
    b ∈ touched G S P ↔ b ∈ P ∧ ∃ a ∈ S, G.Adj a b := by
  classical
  simp only [touched, Finset.mem_biUnion, mem_neighborsIn]
  tauto

private theorem touched_card_le {V : Type*} {G : SimpleGraph V} {S P : Finset V} :
    (touched G S P).card ≤ ∑ a ∈ S, (neighborsIn G a P).card := by
  classical
  exact Finset.card_biUnion_le

private structure CombRound {V : Type*} [DecidableEq V] (G : SimpleGraph V) (A B : Finset V) (d : ℝ) where
  remainder : Finset V
  remainder_sub : remainder ⊆ B
  remainder_bound : ∀ a ∈ A, (neighborsIn G a remainder).card ≤ d / 2
  teeth : Finset V
  teeth_sub : teeth ⊆ A
  high : ∀ a ∈ teeth, d / 2 ≤ (neighborsIn G a B).card
  part : V → Finset V
  part_sub : ∀ a ∈ teeth, part a ⊆ B \ remainder
  width : ∀ a ∈ teeth, d / 4 ≤ (part a).card
  cross : ∀ a ∈ teeth, ∀ b ∈ teeth, ∀ z ∈ part b, G.Adj a z ↔ a = b
  budget : ((B \ remainder).card : ℝ) ≤
    d * teeth.card + 4 * ∑ a ∈ teeth, ((neighborsIn G a B).card - d / 2 : ℝ)

/-- Select large teeth in a degree range, rejecting a tooth only when its lost vertices pay for its removal. -/
private theorem comb_round {V : Type*} [DecidableEq V] (G : SimpleGraph V) (A B : Finset V)
    {d : ℝ} (hd : 0 < d) (hcap : ∀ a ∈ A, (neighborsIn G a B).card ≤ d) :
    Nonempty (CombRound G A B d) := by
  classical
  have recRound (n : ℕ) : ∀ U : Finset V, U ⊆ B → U.card = n →
      Nonempty (CombRound G A U d) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U hUB hn
      by_cases hex : ∃ a ∈ A, d / 2 < (neighborsIn G a U).card
      swap
      · have hbound : ∀ a ∈ A, (neighborsIn G a U).card ≤ d / 2 := by
          simpa [not_lt] using hex
        exact ⟨⟨U, fun _ h => h, hbound, ∅, by simp, by simp, fun _ => ∅,
          by simp, by simp, by simp, by simp⟩⟩
      obtain ⟨a, haA, ha⟩ := hex
      let P := neighborsIn G a U
      let U' := U \ P
      have hPU : P ⊆ U := fun _ hz => (mem_neighborsIn.mp hz).1
      have hU'U : U' ⊆ U := Finset.sdiff_subset
      have hp : d / 2 < (P.card : ℝ) := ha
      have hPn : 0 < P.card := by
        have hp' : (0 : ℝ) < P.card := by linarith
        exact_mod_cast hp'
      have hparts := Finset.card_sdiff_add_card_eq_card hPU
      change U'.card + P.card = U.card at hparts
      have hlt : U'.card < n := by omega
      obtain ⟨R⟩ := ih U'.card hlt U' (hU'U.trans hUB) rfl
      have hRsub := R.remainder_sub.trans hU'U
      let T := touched G R.teeth P
      let P' := P \ T
      have hTP : T ⊆ P := fun _ hz => (mem_touched.mp hz).1
      have haS : a ∉ R.teeth := by
        intro h
        have ha0 : neighborsIn G a U' = ∅ := by
          ext z
          simp only [U', Finset.mem_sdiff, mem_neighborsIn, Finset.notMem_empty, iff_false]
          intro hz
          exact hz.1.2 (mem_neighborsIn.mpr ⟨hz.1.1, hz.2⟩)
        have hz := R.high a h
        rw [ha0, Finset.card_empty, Nat.cast_zero] at hz
        linarith
      have hsplit : ((U \ R.remainder).card : ℝ) =
          (P.card : ℝ) + ((U' \ R.remainder).card : ℝ) := by
        have h₁ := Finset.card_sdiff_add_card_eq_card hRsub
        have h₂ := Finset.card_sdiff_add_card_eq_card R.remainder_sub
        exact_mod_cast (show (U \ R.remainder).card = P.card + (U' \ R.remainder).card by omega)
      have hcharge (x : V) :
          ((neighborsIn G x U').card - d / 2 : ℝ) + (neighborsIn G x P).card =
          ((neighborsIn G x U).card - d / 2 : ℝ) := by
        have hh : ((neighborsIn G x U').card : ℝ) + (neighborsIn G x P).card =
            (neighborsIn G x U).card := by exact_mod_cast neighborsIn_card_sdiff_add (G := G) (a := x) hPU
        linarith
      have hpay :
          (∑ x ∈ R.teeth, ((neighborsIn G x U').card - d / 2 : ℝ)) + T.card ≤
          ∑ x ∈ R.teeth, ((neighborsIn G x U).card - d / 2 : ℝ) := by
        have hT : (T.card : ℝ) ≤ ∑ x ∈ R.teeth, ((neighborsIn G x P).card : ℝ) := by
          exact_mod_cast touched_card_le (G := G) (S := R.teeth) (P := P)
        calc
          _ ≤ _ + ∑ x ∈ R.teeth, ((neighborsIn G x P).card : ℝ) := add_le_add_right hT _
          _ = _ := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => hcharge x
      have hhigh : ∀ b ∈ R.teeth, d / 2 ≤ (neighborsIn G b U).card := by
        intro b hb
        exact (R.high b hb).trans (by exact_mod_cast Finset.card_le_card (neighborsIn_mono hU'U))
      have hpartsub : ∀ b ∈ R.teeth, R.part b ⊆ U \ R.remainder := by
        intro b hb z hz
        obtain ⟨hZU, hZR⟩ := Finset.mem_sdiff.mp (R.part_sub b hb hz)
        exact Finset.mem_sdiff.mpr ⟨hU'U hZU, hZR⟩
      by_cases hw : d / 4 ≤ (P'.card : ℝ)
      · let F := fun b => if b = a then P' else R.part b
        refine ⟨⟨R.remainder, hRsub, R.remainder_bound, insert a R.teeth,
          Finset.insert_subset_iff.mpr ⟨haA, R.teeth_sub⟩, ?_, F, ?_, ?_, ?_, ?_⟩⟩
        · intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · exact ha.le
          · exact hhigh b hb
        · intro b hb z hz
          rcases Finset.mem_insert.mp hb with rfl | hb
          · have hzP' : z ∈ P' := by simpa [F] using hz
            have hzP : z ∈ P := Finset.sdiff_subset hzP'
            apply Finset.mem_sdiff.mpr ⟨hPU hzP, fun h => ?_⟩
            exact (Finset.mem_sdiff.mp (R.remainder_sub h)).2 hzP
          · have hba : b ≠ a := fun h => haS (h ▸ hb)
            exact hpartsub b hb (by simpa [F, hba] using hz)
        · intro b hb
          rcases Finset.mem_insert.mp hb with rfl | hb
          · simpa [F] using hw
          · have hba : b ≠ a := fun h => haS (h ▸ hb)
            simpa [F, hba] using R.width b hb
        · intro b hb c hc z hz
          rcases Finset.mem_insert.mp hb with hba | hb <;>
            rcases Finset.mem_insert.mp hc with hca | hc
          · subst b c
            have hzP' : z ∈ P' := by simpa [F] using hz
            exact iff_of_true (mem_neighborsIn.mp
              (Finset.sdiff_subset hzP' : z ∈ P)).2 rfl
          · subst b
            have hca : c ≠ a := fun h => haS (h ▸ hc)
            have hzR : z ∈ R.part c := by simpa [F, hca] using hz
            have hzU := (Finset.mem_sdiff.mp (R.part_sub c hc hzR)).1
            exact iff_of_false (fun he => (Finset.mem_sdiff.mp hzU).2
              (mem_neighborsIn.mpr ⟨hU'U hzU, he⟩)) hca.symm
          · subst c
            have hba : b ≠ a := fun h => haS (h ▸ hb)
            have hzP : z ∈ P' := by simpa [F] using hz
            exact iff_of_false (fun he => (Finset.mem_sdiff.mp hzP).2
              (mem_touched.mpr ⟨Finset.sdiff_subset hzP, b, hb, he⟩)) hba
          · have hca : c ≠ a := fun h => haS (h ▸ hc)
            apply R.cross b hb c hc z
            simpa [F, hca] using hz
        · rw [hsplit, Finset.card_insert_of_notMem haS, Finset.sum_insert haS]
          push_cast
          have hPcap : (P.card : ℝ) ≤ d := (by
            exact_mod_cast Finset.card_le_card (neighborsIn_mono (G := G) (x := a) hUB) :
              (P.card : ℝ) ≤ (neighborsIn G a B).card).trans (hcap a haA)
          have h0 : (0 : ℝ) ≤ T.card := by positivity
          linarith [R.budget]
      · refine ⟨⟨R.remainder, hRsub, R.remainder_bound, R.teeth, R.teeth_sub,
          hhigh, R.part, hpartsub, R.width, R.cross, ?_⟩⟩
        rw [hsplit]
        have hpt : (P'.card : ℝ) + T.card = P.card := by
          exact_mod_cast Finset.card_sdiff_add_card_eq_card hTP
        have hw' : (P'.card : ℝ) < d / 4 := lt_of_not_ge hw
        have hP : (P.card : ℝ) ≤ 4 * T.card := by linarith
        linarith [R.budget]
  exact recRound B.card B (Finset.Subset.refl _) rfl

private def bipartite_comb_transfer {V : Type*} {G : SimpleGraph V} {A B E : Finset V}
    {t : ℕ} (C : BipartiteComb G A E t) (hEB : E ⊆ B) : BipartiteComb G A B t where
  tooth := C.tooth
  tooth_mem := C.tooth_mem
  block := C.block
  block_sub i := (C.block_sub i).trans hEB
  disjoint := C.disjoint
  cross := C.cross

private noncomputable def CombRound.toComb {V : Type*} [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    {d : ℝ} (R : CombRound G A B d) : BipartiteComb G A B R.teeth.card := by
  classical
  let e : (R.teeth : Set V) ≃ Fin R.teeth.card := Fintype.equivFinOfCardEq (Fintype.card_coe _)
  let a : Fin R.teeth.card ↪ V :=
    ⟨fun i => (e.symm i).val, Subtype.val_injective.comp e.symm.injective⟩
  have ha : ∀ i, a i ∈ R.teeth := fun i => (e.symm i).property
  refine ⟨a, fun i => R.teeth_sub (ha i), fun i => R.part (a i),
    fun i => (R.part_sub _ (ha i)).trans Finset.sdiff_subset, ?_, ?_⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have adj := (R.cross _ (ha i) _ (ha i) _ hx).mpr rfl
    exact hij (a.injective ((R.cross _ (ha i) _ (ha j) _ hy).mp adj))
  · intro i j x hx
    exact (R.cross _ (ha i) _ (ha j) _ hx).trans a.injective.eq_iff

theorem bipartite_bound {V : Type*} (G : SimpleGraph V) : BipartiteBound G 24 := by
  classical
  intro A B Γ Δ hΓ hΔ hAB hcover hcap
  by_cases hcomb : ∃ t > (0 : ℕ), ∃ C : BipartiteComb G A B t,
      ∀ i, Γ / (t : ℝ)^2 ≤ (C.block i).card
  · exact Or.inl hcomb
  apply Or.inr
  have recBound (n : ℕ) : ∀ (U : Finset V) (D : ℝ), U ⊆ B → U.card = n → 0 ≤ D →
      (∀ a ∈ A, (neighborsIn G a U).card ≤ D) →
      (U.card : ℝ) ≤ 24 * Real.sqrt (Γ * D) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U D hUB hn hD hcap
      by_cases hU : U.Nonempty
      swap
      · have hu := Finset.not_nonempty_iff_eq_empty.mp hU
        subst U
        simp
      obtain ⟨b, hbU⟩ := hU
      obtain ⟨a, haA, hab⟩ := hcover b (hUB hbU)
      obtain ⟨x, hxA, hxmax⟩ := Finset.exists_max_image A
        (fun y => (neighborsIn G y U).card) ⟨a, haA⟩
      let d : ℝ := (neighborsIn G x U).card
      have hcap' : ∀ y ∈ A, (neighborsIn G y U).card ≤ d := by
        intro y hy
        dsimp [d]
        exact_mod_cast hxmax y hy
      have hdD : d ≤ D := hcap x hxA
      have hd : 0 < d := by
        dsimp [d]
        exact_mod_cast (Finset.card_pos.mpr ⟨b, mem_neighborsIn.mpr ⟨hbU, hab⟩⟩).trans_le
          (hxmax a haA)
      obtain ⟨R⟩ := comb_round G A U hd hcap'
      have hRproper : R.remainder.card < U.card := by
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨R.remainder_sub, fun eq => ?_⟩
        have he : d ≤ d / 2 := by simpa only [eq] using R.remainder_bound x hxA
        linarith
      have hRbd := ih R.remainder.card (by omega) R.remainder (d/2) (R.remainder_sub.trans hUB)
        rfl (by positivity : 0 ≤ d/2) R.remainder_bound
      let t : ℕ := R.teeth.card
      have hdrop : ((U \ R.remainder).card : ℝ) ≤ 3 * d * t := by
        have hsum : (∑ a ∈ R.teeth, ((neighborsIn G a U).card - d / 2 : ℝ)) ≤
            (t : ℝ) * (d/2) := by
          calc
            _ ≤ ∑ a ∈ R.teeth, (d/2 : ℝ) := Finset.sum_le_sum fun a ha => by
              linarith [hcap' a (R.teeth_sub ha)]
            _ = _ := by simp [t, nsmul_eq_mul]
        dsimp [t] at hsum ⊢
        linarith [R.budget]
      have ht : 0 < t := by
        by_contra! h
        have hte : t = 0 := by omega
        have hcard := Finset.card_sdiff_add_card_eq_card R.remainder_sub
        have hdrop' : ((U \ R.remainder).card : ℝ) ≤ 0 := by simpa [hte] using hdrop
        norm_cast at hdrop'
        omega
      let C := bipartite_comb_transfer R.toComb hUB
      have hw : d/4 < Γ / (t : ℝ)^2 := by
        by_contra! h
        apply hcomb
        refine ⟨t, ht, C, fun i => h.trans (R.width (R.toComb.tooth i) ?_)⟩
        exact (Fintype.equivFinOfCardEq (Fintype.card_coe R.teeth)).symm i |>.property
      have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht
      have hsq : (d * (t : ℝ))^2 ≤ (2 * Real.sqrt (Γ * d))^2 := by
        have h := (lt_div_iff₀ (sq_pos_of_pos ht0)).mp hw
        rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        nlinarith [mul_lt_mul_of_pos_left h hd]
      have hdt : d * t ≤ 2 * Real.sqrt (Γ * d) := by
        exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
      have hsqrt : Real.sqrt (Γ * (d/2)) ≤ (3/4) * Real.sqrt (Γ*d) := by
        have h := Real.sq_sqrt (show 0 ≤ Γ * (d/2) by positivity)
        have hh := Real.sq_sqrt (show 0 ≤ Γ * d by positivity)
        apply (sq_le_sq₀ (by positivity) (by positivity)).mp
        rw [mul_pow, h, hh]
        nlinarith
      have hu : ((U \ R.remainder).card : ℝ) + R.remainder.card = U.card := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card R.remainder_sub
      calc
        (U.card : ℝ) ≤ 24 * Real.sqrt (Γ * d) := by linarith
        _ ≤ 24 * Real.sqrt (Γ * D) := by gcongr
  exact recBound B.card B Δ (Finset.Subset.refl _) rfl hΔ hcap

end FiveHole

namespace FiveHole

private noncomputable def edgeCountBetween {V : Type*}
    (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  ∑ x ∈ A, ((neighborsIn G x B).card : ℝ)

private def Sparse {V : Type*} (G : SimpleGraph V) (A : Finset V) (c : ℝ) : Prop :=
  edgeCountBetween G A A ≤ c * (A.card : ℝ)^2

private theorem edgeCount_comm {V : Type*} (G : SimpleGraph V) (A B : Finset V) :
    edgeCountBetween G A B = edgeCountBetween G B A := by
  classical
  unfold edgeCountBetween
  simp only [neighborsIn, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]
  rw [Finset.sum_comm]
  simp only [SimpleGraph.adj_comm]

private theorem edgeCount_le_mul {V : Type*} (G : SimpleGraph V) (A B : Finset V)
    (c : ℝ) (h : ∀ x ∈ A, ((neighborsIn G x B).card : ℝ) ≤ c * B.card) :
    edgeCountBetween G A B ≤ c * A.card * B.card := by
  unfold edgeCountBetween
  calc
    _ ≤ ∑ _ ∈ A, c * (B.card : ℝ) := Finset.sum_le_sum h
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private theorem edgeCount_union_left {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {A B : Finset V} (C : Finset V) (h : Disjoint A B) :
    edgeCountBetween G (A ∪ B) C = edgeCountBetween G A C + edgeCountBetween G B C := by
  unfold edgeCountBetween
  exact Finset.sum_union h

private theorem edgeCount_union {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {A B : Finset V} (h : Disjoint A B) :
    edgeCountBetween G (A ∪ B) (A ∪ B) =
      edgeCountBetween G A A + edgeCountBetween G B B + 2 * edgeCountBetween G B A := by
  rw [edgeCount_union_left G _ h, edgeCount_comm G A (A ∪ B), edgeCount_comm G B (A ∪ B),
    edgeCount_union_left G A h, edgeCount_union_left G B h, edgeCount_comm G A B]
  ring

private theorem edgeCount_compl_le {V : Type*} (G : SimpleGraph V) (A : Finset V) :
    edgeCountBetween G A A + edgeCountBetween Gᶜ A A ≤ (A.card : ℝ)^2 := by
  classical
  have hrow (x : V) : ((neighborsIn G x A).card : ℝ) + (neighborsIn Gᶜ x A).card ≤ A.card := by
    have hd : Disjoint (neighborsIn G x A) (neighborsIn Gᶜ x A) := by
      apply Finset.disjoint_left.mpr
      intro y hy hz
      exact ((G.compl_adj _ _).mp (mem_neighborsIn.mp hz).2).2 (mem_neighborsIn.mp hy).2
    have hs : neighborsIn G x A ∪ neighborsIn Gᶜ x A ⊆ A := by
      apply Finset.union_subset <;> intro _ h <;> exact (mem_neighborsIn.mp h).1
    have h := Finset.card_le_card hs
    rw [Finset.card_union_of_disjoint hd] at h
    exact_mod_cast h
  unfold edgeCountBetween
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _ ∈ A, (A.card : ℝ) := Finset.sum_le_sum fun x _ => hrow x
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, sq]

/-- Deleting a vertex of maximum degree does not increase ordered edge count divided by squared order. -/
private theorem sparse_pick_card {V : Type*} (G : SimpleGraph V) (A : Finset V)
    {m : ℕ} (hm : m ≤ A.card) {c : ℝ} (hc : 0 ≤ c) (hA : Sparse G A c) :
    ∃ B : Finset V, B ⊆ A ∧ B.card = m ∧ Sparse G B c := by
  classical
  by_cases hm0 : m = 0
  · subst m
    exact ⟨∅, Finset.empty_subset _, rfl, by simp [Sparse, edgeCountBetween]⟩
  have recPick (n : ℕ) : ∀ A : Finset V, A.card = n → m ≤ n → Sparse G A c →
      ∃ B : Finset V, B ⊆ A ∧ B.card = m ∧ Sparse G B c := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A hn hm hA
      by_cases he : m = n
      · exact ⟨A, Finset.Subset.refl _, hn.trans he.symm, hA⟩
      have ha : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image A
        (fun v => (neighborsIn G v A).card) ha
      let E := A.erase x
      have hE : E ⊆ A := Finset.erase_subset _ _
      have heq : E ∪ {x} = A := by dsimp [E]; simp [hx]
      have hdis : Disjoint E {x} := by simp [E]
      have hEc : E.card + 1 = A.card := by
        have h := Finset.card_union_of_disjoint hdis
        rw [heq, Finset.card_singleton] at h
        exact h.symm
      have hEcR : (E.card : ℝ) + 1 = A.card := by exact_mod_cast hEc
      have hac : (2 : ℝ) ≤ A.card := by
        have h : 2 ≤ A.card := by omega
        exact_mod_cast h
      let d : ℝ := (neighborsIn G x A).card
      have hdecomp : edgeCountBetween G A A = edgeCountBetween G E E + 2 * d := by
        have hs : neighborsIn G x ({x} : Finset V) = ∅ := by
          ext y
          simp only [mem_neighborsIn, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨rfl, h⟩
          exact G.irrefl h
        have hdeq : neighborsIn G x E = neighborsIn G x A := by
          ext y
          simp only [mem_neighborsIn, E, Finset.mem_erase]
          constructor
          · tauto
          · rintro ⟨hy, hadj⟩
            exact ⟨⟨hadj.ne.symm, hy⟩, hadj⟩
        rw [← heq, edgeCount_union G hdis]
        simp [edgeCountBetween, hs, hdeq, d]
      have hdeg : edgeCountBetween G A A ≤ d * A.card := by
        unfold edgeCountBetween
        calc
          _ ≤ ∑ _ ∈ A, d := Finset.sum_le_sum fun y hy => by
            dsimp [d]
            exact_mod_cast hxmax y hy
          _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      have hprior : edgeCountBetween G A A ≤ c * (A.card : ℝ)^2 := hA
      have hpos : (0 : ℝ) < A.card := by linarith
      have hnew : Sparse G E c := by
        change edgeCountBetween G E E ≤ c * (E.card : ℝ)^2
        apply (le_of_mul_le_mul_right ?_ hpos)
        have hmul := mul_le_mul_of_nonneg_right hprior (show 0 ≤ (A.card : ℝ) - 2 by linarith)
        have hsq : ((A.card : ℝ) - 2) * (A.card : ℝ)^2 ≤ (E.card : ℝ)^2 * A.card := by
          rw [← hEcR]
          nlinarith [Nat.cast_nonneg (α := ℝ) E.card]
        have hmul' := mul_le_mul_of_nonneg_left hsq hc
        have hstart : edgeCountBetween G E E * (A.card : ℝ) ≤
            edgeCountBetween G A A * ((A.card : ℝ) - 2) := by
          rw [hdecomp] at hdeg ⊢
          nlinarith
        nlinarith
      obtain ⟨B, hBE, hBc, hB⟩ := ih E.card (by omega) E rfl (by omega) hnew
      exact ⟨B, hBE.trans hE, hBc, hB⟩
  exact recPick A.card A rfl hm hA

private theorem good_row_subset {V : Type*} (G : SimpleGraph V) (A B : Finset V)
    {γ : ℝ} (hγ : 0 < γ) (hA : A.Nonempty)
    (h : edgeCountBetween G A B ≤ γ * A.card * B.card) :
    ∃ B' : Finset V, B' ⊆ B ∧ (B.card : ℝ)/2 ≤ B'.card ∧
      ∀ x ∈ B', (neighborsIn G x A).card ≤ (2*γ) * (A.card : ℝ) := by
  classical
  let c : ℝ := (2*γ) * (A.card : ℝ)
  let D := B.filter fun x => c < ((neighborsIn G x A).card : ℝ)
  let B' := B \ D
  have hd : D ⊆ B := Finset.filter_subset _ _
  have hdc : (B'.card : ℝ) + D.card = B.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hd
  have hcount : (D.card : ℝ) * c ≤ edgeCountBetween G B A := by
    unfold edgeCountBetween
    calc
      _ = ∑ _ ∈ D, c := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ D, ((neighborsIn G x A).card : ℝ) :=
        Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2.le
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hd (fun _ _ _ => by positivity)
  have hc : 0 < c := by dsimp [c]; have := Finset.card_pos.mpr hA; positivity
  have hsize : (B.card : ℝ)/2 ≤ B'.card := by
    rw [edgeCount_comm] at hcount
    have he : γ * (A.card : ℝ) * B.card = ((B.card : ℝ)/2) * c := by dsimp [c]; ring
    have hdc' := le_of_mul_le_mul_right (hcount.trans (h.trans_eq he)) hc
    linarith
  refine ⟨B', Finset.sdiff_subset, hsize, fun x hx => ?_⟩
  exact le_of_not_gt fun ht => (Finset.mem_sdiff.mp hx).2
    (Finset.mem_filter.mpr ⟨Finset.sdiff_subset hx, ht⟩)

end FiveHole

namespace FiveHole

private def correct {V : Type*} (G : SimpleGraph V) (i j : Fin 5) (x y : V) : Prop :=
  G.Adj x y ↔ (cycleGraph 5).Adj i j

private noncomputable def candidates {V : Type*} (G : SimpleGraph V) (i j : Fin 5) (x : V)
    (S : Finset V) : Finset V := by
  classical
  exact S.filter (correct G i j x)

private theorem mem_candidates {V : Type*} {G : SimpleGraph V} {i j : Fin 5} {x y : V}
    {S : Finset V} : y ∈ candidates G i j x S ↔ y ∈ S ∧ correct G i j x y := by
  classical
  simp [candidates]

private theorem embedding_of_five_parts {V : Type*} {G : SimpleGraph V}
    {S : Fin 5 → Finset V} (hS : ∀ i, (S i).Nonempty)
    (hd : Pairwise (Function.onFun Disjoint S))
    (hc : ∀ i j, i < j → ∀ x ∈ S i, ∀ y ∈ S j, correct G i j x y) :
    Nonempty (cycleGraph 5 ↪g G) := by
  classical
  choose f hf using hS
  have hinj : Function.Injective f := by
    intro i j h
    by_contra hne
    exact Finset.disjoint_left.mp (hd hne) (hf i) (h ▸ hf j)
  refine ⟨⟨⟨f, hinj⟩, ?_⟩⟩
  intro i j
  change correct G i j (f i) (f j)
  rcases lt_trichotomy i j with hij | heq | hji
  · exact hc i j hij _ (hf i) _ (hf j)
  · subst j
    simp [correct]
  · have h := hc j i hji _ (hf j) _ (hf i)
    unfold correct at h ⊢
    exact ⟨fun h' => (h.mp h'.symm).symm, fun h' => (h.mpr h'.symm).symm⟩

/-- A failed step of greedy induced embedding yields a one-sided sparse pair. -/
private theorem sparse_pair_from_parts {V : Type*} {G : SimpleGraph V} (hfree : Free G)
    {U : Finset V} {P : Fin 5 → Finset V}
    (hPU : ∀ i, P i ⊆ U) (hP : Pairwise (Function.onFun Disjoint P))
    {γ M : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hM : 0 < M)
    (hPsize : ∀ i, M ≤ (P i).card) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧
      γ^5 * M / 5 ≤ (A.card : ℝ) ∧ γ^5 * M / 5 ≤ (B.card : ℝ) ∧
      ((∀ x ∈ A, (neighborsIn G x B).card ≤ γ * (B.card : ℝ)) ∨
       (∀ x ∈ A, (neighborsIn Gᶜ x B).card ≤ γ * (B.card : ℝ))) := by
  classical
  by_contra! hnone
  have recParts (k : ℕ) (hk : k ≤ 5) :
      ∃ S : Fin 5 → Finset V, (∀ i, S i ⊆ P i) ∧ (∀ i, (S i).Nonempty) ∧
        (∀ j : Fin 5, k ≤ (j : ℕ) → γ^k * M ≤ ((S j).card : ℝ)) ∧
        (∀ i j : Fin 5, (i : ℕ) < k → i < j → ∀ x ∈ S i, ∀ y ∈ S j, correct G i j x y) := by
    induction k with
    | zero =>
      refine ⟨P, fun _ => Finset.Subset.refl _, ?_, ?_, by simp⟩
      · intro i
        have hs : (0 : ℝ) < (P i).card := hM.trans_le (hPsize i)
        exact Finset.card_pos.mp (by exact_mod_cast hs)
      · intro j _
        simpa using hPsize j
    | succ k ih =>
      obtain ⟨S, hSP, hS, hsz, hc⟩ := ih (by omega)
      let i : Fin 5 := ⟨k, by omega⟩
      let bad (j : Fin 5) := if i < j then (S i).filter fun x =>
        ((candidates G i j x (S j)).card : ℝ) < γ * ((S j).card : ℝ) else ∅
      have hbase (j : Fin 5) (hj : k ≤ (j : ℕ)) :
          γ^5 * M ≤ ((S j).card : ℝ) :=
        (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hγ.le hγ1 (by omega)) hM.le).trans
          (hsz j hj)
      have hbd : ∀ j, ((bad j).card : ℝ) < ((S i).card : ℝ) / 5 := by
        intro j
        by_cases hij : i < j
        swap
        · simp only [bad, if_neg hij, Finset.card_empty, Nat.cast_zero]
          have hp : (0 : ℝ) < (S i).card := Nat.cast_pos.mpr (Finset.card_pos.mpr (hS i))
          positivity
        by_contra! hbad
        have hbadSub : bad j ⊆ S i := by
          simpa only [bad, if_pos hij] using Finset.filter_subset
            (fun x => ((candidates G i j x (S j)).card : ℝ) < γ * ((S j).card : ℝ)) (S i)
        have hdis : Disjoint (bad j) (S j) :=
          Disjoint.mono (hbadSub.trans (hSP i)) (hSP j) (hP hij.ne)
        have hbadSize : γ^5 * M / 5 ≤ ((bad j).card : ℝ) := by
          exact (div_le_div_of_nonneg_right (hbase i (by rfl)) (by norm_num)).trans hbad
        have hSsize : γ^5 * M / 5 ≤ ((S j).card : ℝ) := by
          have hh := hbase j (Nat.le_of_lt hij)
          have hp : 0 ≤ γ^5 * M := by positivity
          linarith
        obtain ⟨he, hn⟩ := hnone (bad j) (S j) (hbadSub.trans ((hSP i).trans (hPU i)))
          ((hSP j).trans (hPU j)) hdis hbadSize hSsize
        have hh (x : V) (hx : x ∈ bad j) :
            ((candidates G i j x (S j)).card : ℝ) < γ * ((S j).card : ℝ) := by
          have hx' : x ∈ (S i).filter (fun x =>
              ((candidates G i j x (S j)).card : ℝ) < γ * ((S j).card : ℝ)) := by
            simpa only [bad, if_pos hij] using hx
          exact (Finset.mem_filter.mp hx').2
        by_cases hcy : (cycleGraph 5).Adj i j
        · obtain ⟨x, hx, hxd⟩ := he
          apply hxd.not_gt
          have eq : neighborsIn G x (S j) = candidates G i j x (S j) := by
            ext y
            simp [mem_candidates, correct, hcy]
          simpa [eq] using hh x hx
        · obtain ⟨x, hx, hxd⟩ := hn
          apply hxd.not_gt
          have eq : neighborsIn Gᶜ x (S j) = candidates G i j x (S j) := by
            ext y
            rw [mem_neighborsIn, mem_candidates]
            refine and_congr_right fun hy => ?_
            have hxy : x ≠ y := fun heq => Finset.disjoint_left.mp hdis hx (heq ▸ hy)
            simp [compl_adj, hxy, correct, hcy]
          simpa [eq] using hh x hx
      let T := Finset.univ.biUnion bad
      have htlt : (T.card : ℝ) < ((S i).card : ℝ) := by
        have ht : (T.card : ℝ) ≤ ∑ j : Fin 5, ((bad j).card : ℝ) := by
          exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := bad))
        have hs : (∑ j : Fin 5, ((bad j).card : ℝ)) < ∑ _j : Fin 5, ((S i).card : ℝ) / 5 := by
          exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hbd j)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
        norm_num at hs
        linarith
      obtain ⟨x, hx, hxT⟩ := Finset.exists_mem_notMem_of_card_lt_card
        (by exact_mod_cast htlt : T.card < (S i).card)
      let F (j : Fin 5) :=
        if j = i then {x} else if i < j then candidates G i j x (S j) else S j
      have hf : ∀ j, F j ⊆ S j := by
        intro j y hy
        by_cases hj : j = i
        · subst j
          have hyx : y = x := by simpa [F] using hy
          exact hyx.symm ▸ hx
        · by_cases hij : i < j
          · exact (mem_candidates.mp (by simpa [F, hj, hij] using hy)).1
          · simpa [F, hj, hij] using hy
      have hnext (j : Fin 5) (hij : i < j) :
          γ * ((S j).card : ℝ) ≤ ((F j).card : ℝ) := by
        simp only [F, if_neg hij.ne.symm, if_pos hij]
        apply le_of_not_gt
        intro h
        apply hxT
        apply Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
        simp [bad, hij, hx, h]
      have hFsize (j : Fin 5) (hkj : k + 1 ≤ (j : ℕ)) : γ^(k+1)*M ≤ ((F j).card : ℝ) := by
        have hij : i < j := hkj
        calc
          _ = γ * (γ ^ k * M) := by rw [pow_succ]; ring
          _ ≤ γ * ((S j).card : ℝ) := mul_le_mul_of_nonneg_left (hsz j (Nat.le_of_lt hij)) hγ.le
          _ ≤ _ := hnext j hij
      refine ⟨F, fun j => (hf j).trans (hSP j), ?_, hFsize, ?_⟩
      · intro j
        rcases lt_trichotomy j i with hj | rfl | hij
        · simpa [F, hj.ne, not_lt_of_gt hj] using hS j
        · simp [F]
        · have hp : (0 : ℝ) < γ ^ (k+1) * M := by positivity
          have hh := hp.trans_le (hFsize j hij)
          exact Finset.card_pos.mp (by exact_mod_cast hh)
      · intro j l hj hjl y hy z hz
        by_cases hjk : (j : ℕ) < k
        · exact hc j l hjk hjl y (hf j hy) z (hf l hz)
        · have heq : j = i := Fin.ext (by change (j : ℕ) = k; omega)
          subst j
          have hyx : y = x := by simpa [F] using hy
          subst y
          have hzc : z ∈ candidates G i l x (S l) := by simpa [F, hjl.ne.symm, hjl] using hz
          exact (mem_candidates.mp hzc).2
  obtain ⟨S, hSP, hS, _, hc⟩ := recParts 5 le_rfl
  exact hfree (embedding_of_five_parts hS
    (fun i j hij => Disjoint.mono (hSP i) (hSP j) (hP hij))
    (fun i j hij => hc i j i.isLt hij))

theorem sparse_pair {V : Type*} {G : SimpleGraph V} (hfree : Free G)
    (U : Finset V) (hU : 10 ≤ U.card) {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ A B : Finset V, A ⊆ U ∧ B ⊆ U ∧ Disjoint A B ∧
      (γ^5 / 50) * U.card ≤ (A.card : ℝ) ∧ (γ^5 / 50) * U.card ≤ (B.card : ℝ) ∧
      ((∀ x ∈ A, (neighborsIn G x B).card ≤ γ * (B.card : ℝ)) ∨
       (∀ x ∈ A, (neighborsIn Gᶜ x B).card ≤ γ * (B.card : ℝ))) := by
  classical
  let m := U.card / 5
  have hm : 0 < m := by dsimp [m]; omega
  have hmU : 5*m ≤ U.card := by dsimp [m]; omega
  have hcard : U.card ≤ 10*m := by dsimp [m]; omega
  let e : (U : Set V) ≃ Fin U.card := Fintype.equivFinOfCardEq (Fintype.card_coe U)
  let block (i : Fin 5) (j : Fin m) : Fin U.card :=
    ⟨(i : ℕ) * m + j, by
      calc
        (i : ℕ) * m + j < ((i : ℕ)+1) * m := by
          rw [Nat.add_mul, one_mul]
          exact Nat.add_lt_add_left j.isLt _
        _ ≤ 5*m := Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := hmU⟩
  have hinj (i j : Fin 5) (u v : Fin m) (h : block i u = block j v) : i = j ∧ u = v := by
    have hh : (i : ℕ)*m + u = (j : ℕ)*m + v := congrArg Fin.val h
    have hi : i = j := by
      apply Fin.ext
      have hx (i : Fin 5) (v : Fin m) : (((i : ℕ)*m + v) / m) = i := by
        rw [Nat.mul_comm (i : ℕ) m, Nat.mul_add_div hm, Nat.div_eq_of_lt v.isLt, add_zero]
      rw [← hx i u, ← hx j v, hh]
    subst j
    exact ⟨rfl, Fin.ext (by omega)⟩
  let part (i : Fin 5) : Fin m ↪ V :=
    ⟨fun j => e.symm (block i j), fun u v h => (hinj i i u v
      (e.symm.injective (Subtype.ext h))).2⟩
  let P (i : Fin 5) : Finset V := Finset.univ.map (part i)
  have hPU : ∀ i, P i ⊆ U := by
    intro i x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    exact (e.symm (block i j)).property
  have hP : Pairwise (Function.onFun Disjoint P) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hxi
    obtain ⟨v, _, he⟩ := Finset.mem_map.mp hxj
    exact hij (hinj i j u v (e.symm.injective (Subtype.ext he.symm))).1
  have hM : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hPsize : ∀ i, (m : ℝ) ≤ ((P i).card : ℝ) := by
    intro i
    simp [P]
  obtain ⟨A, B, hAU, hBU, hAB, hA, hB, hchoice⟩ :=
    sparse_pair_from_parts hfree hPU hP hγ hγ1 hM hPsize
  have hle : (γ^5 / 50) * (U.card : ℝ) ≤ γ^5 * m / 5 := by
    have hcard' : (U.card : ℝ) ≤ (10 : ℝ) * m := by exact_mod_cast hcard
    nlinarith [mul_le_mul_of_nonneg_left hcard' (pow_nonneg hγ.le 5)]
  exact ⟨A, B, hAU, hBU, hAB, hle.trans hA, hle.trans hB, hchoice⟩

end FiveHole

namespace FiveHole

def SparseSide : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ > (0 : ℝ), ∀ {V : Type} [Fintype V] (G : SimpleGraph V),
    Free G → ∃ X : Finset V, δ * (Fintype.card V : ℝ) ≤ X.card ∧
      ((∀ x ∈ X, (neighborsIn G x X).card ≤ ε * (X.card : ℝ)) ∨
       (∀ x ∈ X, (neighborsIn Gᶜ x X).card ≤ ε * (X.card : ℝ)))

private theorem cliqueNum_one_le {V : Type*} [Finite V] (G : SimpleGraph V) (x : V) :
    1 ≤ G.cliqueNum := by
  classical
  have h : G.IsClique (({x} : Finset V) : Set V) := by simp
  simpa using h.card_le_cliqueNum

private theorem profile_one_le {V : Type*} [Finite V] (G : SimpleGraph V) (x : V) :
    1 ≤ profile G := by
  classical
  have hc := cliqueNum_one_le G x
  have hi := cliqueNum_one_le Gᶜ x
  rw [cliqueNum_compl] at hi
  unfold profile
  have hc' : (1 : ℝ) ≤ G.cliqueNum := by exact_mod_cast hc
  have hi' : (1 : ℝ) ≤ G.indepNum := by exact_mod_cast hi
  simpa using mul_le_mul hi' hc' (by norm_num : (0 : ℝ) ≤ 1) (by positivity)

private theorem profile_two_le {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hV : 1 < Fintype.card V) : 2 ≤ profile G := by
  classical
  obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hV
  have bound {H : SimpleGraph V} (h : H.Adj x y) : 2 ≤ profile H := by
    have hs : H.IsClique (({x, y} : Finset V) : Set V) := by
      simpa only [Finset.coe_insert, Finset.coe_singleton] using isClique_pair.mpr (fun _ => h)
    have hc := hs.card_le_cliqueNum
    have hi := cliqueNum_one_le Hᶜ x
    rw [cliqueNum_compl] at hi
    simp only [Finset.card_pair hxy] at hc
    unfold profile
    have hc' : (2 : ℝ) ≤ H.cliqueNum := by exact_mod_cast hc
    have hi' : (1 : ℝ) ≤ H.indepNum := by exact_mod_cast hi
    simpa using mul_le_mul hi' hc' (by norm_num : (0 : ℝ) ≤ 2) (by positivity)
  by_cases h : G.Adj x y
  · exact bound h
  · simpa using bound (G.compl_adj x y |>.mpr ⟨hxy, h⟩)

private theorem exponent_choice {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/4 ∧ 1/2 < δ ^ τ ∧
      1 < (2 * δ) ^ τ * (2 : ℝ) ^ (1 - 2 * τ) ∧ (N : ℝ) ^ τ < 2 := by
  have h₁ : ContinuousAt (fun τ : ℝ => δ ^ τ) 0 :=
    (Real.continuous_const_rpow hδ.ne').continuousAt
  have h₂ : ContinuousAt (fun τ : ℝ => (2 * δ) ^ τ * (2 : ℝ) ^ (1 - 2 * τ)) 0 := by
    apply ((Real.continuous_const_rpow (show 2 * δ ≠ 0 by positivity)).mul ?_).continuousAt
    exact (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp (by fun_prop)
  have h₃ : ContinuousAt (fun τ : ℝ => (N : ℝ) ^ τ) 0 :=
    (Real.continuous_const_rpow (by positivity : (N : ℝ) ≠ 0)).continuousAt
  have h₁' : ∀ᶠ τ in nhds (0 : ℝ), 1/2 < δ ^ τ :=
    continuousAt_const.eventually_lt h₁ (by norm_num)
  have h₂' : ∀ᶠ τ in nhds (0 : ℝ), 1 < (2 * δ) ^ τ * (2 : ℝ) ^ (1 - 2 * τ) :=
    continuousAt_const.eventually_lt h₂ (by norm_num)
  have h₃' : ∀ᶠ τ in nhds (0 : ℝ), (N : ℝ) ^ τ < 2 :=
    h₃.eventually_lt continuousAt_const (by norm_num)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (h₁'.and (h₂'.and h₃'))
  let τ : ℝ := min (r / 2) (1 / 4)
  have hτ : 0 < τ := lt_min (by linarith) (by norm_num)
  have htauDist : dist τ 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hτ]
    exact (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨ha, hb, hc⟩ := hball htauDist
  exact ⟨τ, hτ, min_le_right _ _, ha, hb, hc⟩

theorem from_sparse_side (hsparse : SparseSide) :
    ∃ c > (0 : ℝ), Erdos61.IsErdosHajnalLowerBound (cycleGraph 5)
      (fun n : ℕ => (n : ℝ) ^ c) := by
  classical
  let b : ℝ := 1/256
  let ε := b ^ (4 : ℕ)
  have hb : 0 < b := by norm_num [b]
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by norm_num [ε, b]
  have hnum : ε ^ (3/4 : ℝ) + ((24 : ℝ) * Real.sqrt 2) * ε ^ (1/4 : ℝ) ≤ 1/4 := by
    have h₁ : ε ^ (1/4 : ℝ) = b := by
      rw [show ε = b ^ (4 : ℕ) from rfl, ← Real.rpow_natCast_mul hb.le]
      norm_num
    have h₃ : ε ^ (3/4 : ℝ) = b ^ (3 : ℕ) := by
      rw [show ε = b ^ (4 : ℕ) from rfl, ← Real.rpow_natCast_mul hb.le]
      norm_num [Real.rpow_natCast]
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      norm_num [Real.sqrt_le_iff]
    rw [h₁, h₃]
    norm_num [b]
    linarith
  obtain ⟨δ, hδ, hδg⟩ := hsparse ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 + (2 / δ) ^ (2 : ℕ))
  have hN0 : 0 < N := by
    have hp : (0 : ℝ) < N := by nlinarith [sq_nonneg (2/δ)]
    exact_mod_cast hp
  obtain ⟨τ, hτ, hτ', hhalf, hfactor, hNpow⟩ := exponent_choice hδ hN0
  refine finish hτ (by positivity : 0 < 2 * δ) (by linarith) hfactor.le ?_
  intro V _ G hfree hcrit
  let n := Fintype.card V
  have hlarge : N < n := by
    by_contra! hs
    by_cases hn0 : n = 0
    · have hf : 0 ≤ profile G := by unfold profile; positivity
      have hh := hcrit.1
      change profile G < (n : ℝ) ^ τ at hh
      rw [hn0, Nat.cast_zero, Real.zero_rpow hτ.ne'] at hh
      exact hh.not_ge hf
    by_cases hn1 : n = 1
    · have hnpos : 0 < Fintype.card V := by omega
      have ⟨x⟩ := Fintype.card_pos_iff.mp hnpos
      have hh := hcrit.1
      change profile G < (n : ℝ) ^ τ at hh
      rw [hn1, Nat.cast_one, Real.one_rpow] at hh
      exact hh.not_ge (profile_one_le G x)
    have ht : 1 < Fintype.card V := by change 1 < n; omega
    have hle : (n : ℝ) ≤ N := by exact_mod_cast hs
    exact (hcrit.1.trans_le (Real.rpow_le_rpow (by positivity) hle hτ.le)).not_ge
      (hNpow.le.trans (profile_two_le G ht))
  have hn : (0 : ℝ) < n := by exact_mod_cast hN0.trans hlarge
  have hbig : (2/δ)^2 ≤ (n : ℝ) := by
    have hle : (N : ℝ) ≤ n := by exact_mod_cast hlarge.le
    linarith
  obtain ⟨X, hX, hXside⟩ := hδg G hfree
  have hXpos : 0 < (X.card : ℝ) := lt_of_lt_of_le (mul_pos hδ hn) hX
  have hXne := Finset.card_pos.mp (by exact_mod_cast hXpos)
  have rootComb (H : SimpleGraph V) (hcritH : Critical H τ)
      (hdeg : ∀ x ∈ X, (neighborsIn H x X).card ≤ ε * (X.card : ℝ)) :
      ∃ t ≥ (2 : ℕ), ∃ C : RootedComb H t, ∀ i,
        (2 * δ) * (Fintype.card V : ℝ) / (t : ℝ)^2 ≤ (C.block i).card := by
    rcases comb_or_budget hXne hcritH (bipartite_bound H) hε hε1 hτ hτ' (by norm_num) hnum hdeg
      with ⟨t, ht, C, hw⟩ | hBudget
    · refine ⟨t, ht, C, fun i => ?_⟩
      apply le_trans ?_ (hw i)
      apply div_le_div_of_nonneg_right ?_ (sq_nonneg _)
      nlinarith
    exfalso
    have hn1 : (1 : ℝ) ≤ n := by
      have hnn : 1 ≤ n := by omega
      exact_mod_cast hnn
    have hsqrt : (n : ℝ)^τ ≤ Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      apply Real.rpow_le_rpow_of_exponent_le hn1
      linarith
    have hsquare : (2/δ) ≤ Real.sqrt (n : ℝ) := (Real.le_sqrt (by positivity) hn.le).mpr hbig
    have hsmall : Real.sqrt (n : ℝ) ≤ δ * (n : ℝ) / 2 := by
      have h := mul_le_mul_of_nonneg_right hsquare (Real.sqrt_nonneg (n : ℝ))
      have he : (2 / δ) * Real.sqrt (n : ℝ) = (2 * Real.sqrt (n : ℝ)) / δ := by ring
      rw [he, ← sq, Real.sq_sqrt hn.le, div_le_iff₀ hδ] at h
      linarith
    have hα : (H.indepNum : ℝ) ≤ profile H := by
      have hnV : 0 < Fintype.card V := by
        change 0 < n
        exact_mod_cast hn
      obtain ⟨x⟩ := Fintype.card_pos_iff.mp hnV
      have hc' : (1 : ℝ) ≤ H.cliqueNum := by exact_mod_cast cliqueNum_one_le H x
      exact le_mul_of_one_le_right (by positivity) hc'
    have hαlt : (H.indepNum : ℝ) < (X.card : ℝ) / 2 := by
      have hc := hcritH.1
      change profile H < (n : ℝ)^τ at hc
      linarith [hα.trans_lt (hc.trans_le (hsqrt.trans hsmall))]
    have hpow : (n : ℝ)^τ ≤ 2 * (X.card : ℝ)^τ := by
      have hx := Real.rpow_le_rpow (mul_nonneg hδ.le hn.le) hX hτ.le
      rw [Real.mul_rpow hδ.le hn.le] at hx
      have hh := mul_le_mul_of_nonneg_right hhalf.le (Real.rpow_nonneg hn.le τ)
      linarith
    have hmain : profile H * (1/4 : ℝ) * (X.card : ℝ) ^ (1 - τ) ≤ (X.card : ℝ) / 2 := by
      have h := hcritH.1.le.trans hpow
      calc
        _ ≤ (2 * (X.card : ℝ)^τ) * (1/4 : ℝ) * (X.card : ℝ) ^ (1 - τ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by norm_num)) (by positivity)
        _ = _ := by
          rw [show (2 * (X.card : ℝ)^τ) * (1/4 : ℝ) * (X.card : ℝ) ^ (1 - τ) =
            (1/2 : ℝ) * ((X.card : ℝ)^τ * (X.card : ℝ) ^ (1 - τ)) by ring,
            ← Real.rpow_add hXpos, show τ + (1 - τ) = 1 by ring, Real.rpow_one]
          ring
    linarith
  rcases hXside with hG | hGc
  · obtain ⟨t, ht, C, hw⟩ := rootComb G hcrit hG
    exact ⟨t, ht, Or.inl ⟨C, hw⟩⟩
  · obtain ⟨t, ht, C, hw⟩ := rootComb Gᶜ (critical_compl hcrit) hGc
    exact ⟨t, ht, Or.inr ⟨C, hw⟩⟩

end FiveHole

namespace FiveHole

private theorem sparse_merge_step {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {A B : Finset V} {m : ℕ} {α β γ K : ℝ}
    (hm : 0 < m) (hγ : 0 < γ) (hαγ : 4*γ ≤ α)
    (hAB : Disjoint A B) (hA : K * (m : ℝ) ≤ A.card) (hB : 2 * K * (m : ℝ) ≤ B.card)
    (hpoint : ∀ a ∈ A, (neighborsIn G a B).card ≤ γ * (B.card : ℝ))
    (rec : ∀ U : Finset V, K * (m : ℝ) ≤ U.card →
      ∃ X : Finset V, X ⊆ U ∧ X.card = m ∧ (Sparse G X (3*α/2) ∨ Sparse Gᶜ X β)) :
    ∃ X : Finset V, X ⊆ A ∪ B ∧ X.card = m ∧ (Sparse G X α ∨ Sparse Gᶜ X β) := by
  classical
  obtain ⟨A', hAA', hAc, hSparse | hDense⟩ := rec A hA
  swap
  · exact ⟨A', hAA'.trans Finset.subset_union_left, hAc, Or.inr hDense⟩
  have hA'ne : A'.Nonempty := Finset.card_pos.mp (hAc.symm ▸ hm)
  have hcount := edgeCount_le_mul G A' B γ (fun a ha => hpoint a (hAA' ha))
  obtain ⟨B₁, hBB₁, hBsize, hB₁⟩ := good_row_subset G A' B hγ hA'ne hcount
  have hB₁size : K * (m : ℝ) ≤ B₁.card := by linarith
  obtain ⟨B', hBB', hBc, hSparseB | hDense⟩ := rec B₁ hB₁size
  swap
  · exact ⟨B', (hBB'.trans hBB₁).trans Finset.subset_union_right, hBc, Or.inr hDense⟩
  have hd : Disjoint A' B' := Disjoint.mono hAA' (hBB'.trans hBB₁) hAB
  have hUB : A' ∪ B' ⊆ A ∪ B := Finset.union_subset_union hAA' (hBB'.trans hBB₁)
  have hcount' := edgeCount_le_mul G B' A' (2*γ) (fun b hb => hB₁ b (hBB' hb))
  have hcard : (A' ∪ B').card = m + m := by rw [Finset.card_union_of_disjoint hd, hAc, hBc]
  have hmerge : Sparse G (A' ∪ B') α := by
    unfold Sparse at *
    rw [edgeCount_union G hd, hcard, Nat.cast_add]
    rw [hAc] at hSparse
    rw [hBc] at hSparseB
    rw [hAc, hBc] at hcount'
    have hα := mul_le_mul_of_nonneg_right hαγ (sq_nonneg (m : ℝ))
    nlinarith
  obtain ⟨X, hX, hXm, hXS⟩ := sparse_pick_card G (A' ∪ B') (m := m)
    (by rw [hcard]; omega) (by linarith) hmerge
  exact ⟨X, hX.trans hUB, hXm, Or.inl hXS⟩

/-- Iteratively reduce one density threshold by combining pieces of equal size. -/
private theorem sparse_find_card {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (k : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ {V : Type} (G : SimpleGraph V), Free G → ∀ (U : Finset V) (m : ℕ),
      0 < m → K * (m : ℝ) ≤ U.card → ∀ α β : ℝ,
      4*γ ≤ α → 4*γ ≤ β → (1/4 : ℝ) ≤ (3/2 : ℝ)^k * α * β →
      ∃ X : Finset V, X ⊆ U ∧ X.card = m ∧ (Sparse G X α ∨ Sparse Gᶜ X β) := by
  classical
  induction k with
  | zero =>
    refine ⟨1, le_rfl, ?_⟩
    intro V G _ U m _ hKm α β hα hβ hprod
    have hmc : (m : ℝ) ≤ U.card := by simpa using hKm
    have hmU : m ≤ U.card := by exact_mod_cast hmc
    have hsum : 1 ≤ α + β := by
      simp only [pow_zero, one_mul] at hprod
      have hsq : (1 : ℝ)^2 ≤ (α + β)^2 := by nlinarith [sq_nonneg (α - β)]
      exact (sq_le_sq₀ (by norm_num) (by linarith)).mp hsq
    have hchoice : Sparse G U α ∨ Sparse Gᶜ U β := by
      by_contra! h
      simp only [Sparse, not_le] at h
      have hc := edgeCount_compl_le G U
      have hs := mul_le_mul_of_nonneg_right hsum (sq_nonneg (U.card : ℝ))
      nlinarith [h.1, h.2]
    rcases hchoice with h | h
    · obtain ⟨X, hX, hXm, hXS⟩ := sparse_pick_card G U hmU (by linarith) h
      exact ⟨X, hX, hXm, Or.inl hXS⟩
    · obtain ⟨X, hX, hXm, hXS⟩ := sparse_pick_card Gᶜ U hmU (by linarith) h
      exact ⟨X, hX, hXm, Or.inr hXS⟩
  | succ k ih =>
    obtain ⟨K, hK, ih⟩ := ih
    let ρ := γ^5 / 50
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    let L := max (2*K/ρ) 10
    have hL : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 10).trans (le_max_right _ _)
    refine ⟨L, hL, ?_⟩
    intro V G hfree U m hm hLm α β hα hβ hprod
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hU10 : 10 ≤ U.card := by
      have hL10 : (10 : ℝ) ≤ L := le_max_right _ _
      have h : (10 : ℝ) ≤ U.card := calc
        _ ≤ L := hL10
        _ ≤ L * (m : ℝ) := le_mul_of_one_le_right (by linarith) hmR
        _ ≤ _ := hLm
      exact_mod_cast h
    have hlow : 2 * K * (m : ℝ) ≤ ρ * (U.card : ℝ) := by
      have hhead : (2*K/ρ) * (m : ℝ) ≤ U.card :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hLm
      rw [div_mul_eq_mul_div, div_le_iff₀ hρ] at hhead
      simpa [mul_comm] using hhead
    obtain ⟨A, B, hAU, hBU, hAB, hcardA, hcardB, hside⟩ := sparse_pair hfree U hU10 hγ hγ1
    have hcapA : K * (m : ℝ) ≤ A.card := by
      have h := hlow.trans hcardA
      nlinarith [mul_nonneg (show 0 ≤ K by linarith) (Nat.cast_nonneg (α := ℝ) m)]
    have hcapB := hlow.trans hcardB
    have recProd {a b : ℝ} (h : (1/4 : ℝ) ≤ (3/2 : ℝ)^(k+1)*a*b) :
        (1/4 : ℝ) ≤ (3/2 : ℝ)^k*(3*a/2)*b := by
      convert h using 1
      rw [pow_succ]
      ring
    rcases hside with hG | hGc
    · obtain ⟨X, hX, hmX, hs⟩ := sparse_merge_step G hm hγ hα hAB hcapA hcapB hG
        (fun U' hU' => ih G hfree U' m hm hU' (3*α/2) β (by linarith) hβ (recProd hprod))
      exact ⟨X, hX.trans (Finset.union_subset hAU hBU), hmX, hs⟩
    · have hprod' : (1/4 : ℝ) ≤ (3/2 : ℝ)^(k+1)*β*α := by
        convert hprod using 1
        ring
      obtain ⟨X, hX, hmX, hs⟩ := sparse_merge_step Gᶜ hm hγ hβ hAB hcapA hcapB hGc
        (fun U' hU' => ih Gᶜ (free_compl hfree) U' m hm hU' (3*β/2) α
          (by linarith) hα (recProd hprod'))
      exact ⟨X, hX.trans (Finset.union_subset hAU hBU), hmX, by simpa [or_comm] using hs⟩

theorem sparse_side : SparseSide := by
  classical
  intro ε hε
  let η : ℝ := min (ε/4) 1
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : 4*η ≤ ε := by linarith [min_le_left (ε/4) (1 : ℝ)]
  have hη2 : 0 < η^2 := by positivity
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1/4 : ℝ)/η^2)
    (by norm_num : (1 : ℝ) < 3/2)
  have hprod : (1/4 : ℝ) ≤ (3/2 : ℝ)^k * η * η := by
    have hh := (div_lt_iff₀ hη2).mp hk
    nlinarith
  obtain ⟨K, hK, hd⟩ := sparse_find_card (γ := η/4)
    (by positivity) (by linarith : η/4 ≤ 1) k
  have hK0 : 0 < K := by linarith
  refine ⟨1/(4*K), by positivity, ?_⟩
  intro V _ G hfree
  let n := Fintype.card V
  by_cases hn : 0 < n
  swap
  · have hn0 : n = 0 := by omega
    exact ⟨∅, by simp [show Fintype.card V = 0 from hn0], Or.inl (by simp)⟩
  by_cases hub : (n : ℝ) < 2*K
  · have hnV : 0 < Fintype.card V := hn
    obtain ⟨x⟩ := Fintype.card_pos_iff.mp hnV
    refine ⟨{x}, ?_, Or.inl ?_⟩
    · rw [Finset.card_singleton, Nat.cast_one]
      have hh : (n : ℝ)/(4*K) ≤ 1 := by
        apply (div_le_iff₀ (by positivity : 0 < 4*K)).mpr
        linarith
      simpa [div_eq_mul_inv, mul_comm] using hh
    · intro y hy
      have hye : y = x := Finset.mem_singleton.mp hy
      subst y
      have he : neighborsIn G x ({x} : Finset V) = ∅ := by
        ext y
        simp only [mem_neighborsIn, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨rfl, h⟩
        exact G.irrefl h
      rw [he, Finset.card_empty, Nat.cast_zero]
      positivity
  let m := ⌊(n : ℝ)/K⌋₊
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmK : K * (m : ℝ) ≤ n := by
    have h := Nat.floor_le (show 0 ≤ (n : ℝ)/K by positivity)
    have hh := (le_div_iff₀ hK0).mp h
    simpa [mul_comm] using hh
  have hdiv2 : (2 : ℝ) ≤ (n : ℝ)/K := (le_div_iff₀ hK0).mpr (le_of_not_gt hub)
  have hmL : (n : ℝ)/(2*K) ≤ (m : ℝ) := by
    have hh := Nat.lt_floor_add_one ((n : ℝ)/K)
    change (n : ℝ)/K < (m : ℝ) + 1 at hh
    have he : (n : ℝ)/(2*K) = ((n : ℝ)/K)/2 := by ring
    rw [he]
    linarith
  have hm : 0 < m := by
    have h : (0 : ℝ) < m := (by positivity : 0 < (n : ℝ)/(2*K)).trans_le hmL
    exact_mod_cast h
  obtain ⟨X, _, hXm, hside⟩ := hd G hfree Finset.univ m hm
    (by simpa using hmK) η η (by linarith) (by linarith) hprod
  have finish {H : SimpleGraph V} (hH : Sparse H X η) :
      ∃ Y : Finset V, (1/(4*K)) * (Fintype.card V : ℝ) ≤ Y.card ∧
        ∀ y ∈ Y, (neighborsIn H y Y).card ≤ ε * (Y.card : ℝ) := by
    have hXne : X.Nonempty := Finset.card_pos.mp (hXm.symm ▸ hm)
    have hX := hH
    unfold Sparse at hX
    rw [sq, ← mul_assoc] at hX
    obtain ⟨Y, hYX, hYsz, hdt⟩ := good_row_subset H X X hη hXne hX
    refine ⟨Y, ?_, fun y hy => ?_⟩
    · have he : (1/(4*K)) * (n : ℝ) = ((n : ℝ)/(2*K))/2 := by ring
      change (1/(4*K)) * (n : ℝ) ≤ Y.card
      rw [he]
      rw [hXm] at hYsz
      linarith
    · have hm' : ((neighborsIn H y Y).card : ℝ) ≤ (neighborsIn H y X).card := by
        exact_mod_cast Finset.card_le_card (neighborsIn_mono hYX)
      refine hm'.trans ((hdt y hy).trans ?_)
      have hh := mul_le_mul_of_nonneg_left (show (X.card : ℝ) ≤ 2 * Y.card by linarith)
        (by positivity : 0 ≤ 2*η)
      have hε' := mul_le_mul_of_nonneg_right hηε (Nat.cast_nonneg (α := ℝ) Y.card)
      nlinarith
  rcases hside with hG | hGc
  · obtain ⟨Y, hY, hD⟩ := finish hG
    exact ⟨Y, hY, Or.inl hD⟩
  · obtain ⟨Y, hY, hD⟩ := finish hGc
    exact ⟨Y, hY, Or.inr hD⟩

end FiveHole

theorem OMA.solution : type_of% @Erdos61.erdos_61.variants.c5 :=
  FiveHole.from_sparse_side FiveHole.sparse_side