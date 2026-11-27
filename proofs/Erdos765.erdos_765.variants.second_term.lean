import FormalConjectures.ErdosProblems.«765»
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem 765 — Disproof of the `n/4 + O(n^(1/2))` Second Term (Ma–Yang 2023)

Direct formalization of Section 5 (Eq. 14) of Ma–Yang (2023, arXiv:2107.11601), showing that for
`n_m = 400 * m^2 + 26 * m + 1` (`q = 20 * m`, `r = 6 * m`, `m ≥ 10`),
`ex(n_m; C_4) ≤ n_m * (20 * m + 1) / 2`, which lies at least `30 * m^2 - O(m)` below
`n_m^(3/2) / 2 + n_m / 4`, refuting `ex(n; C_4) - n^(3/2)/2 - n/4 = O(n^(1/2))`.
-/

-- Problem: Erdős Problem 765 — second term
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/765.lean:75 (declaration Erdos765.erdos_765.variants.second_term)
-- Credit: @kDylanHayes

namespace Erdos765MY

open Finset Filter Real SimpleGraph Asymptotics

-- ### Part 1: Basic consequences of C4-freeness

private lemma no_c4_of_free {n : ℕ} {G : SimpleGraph (Fin n)}
    (hfree : (SimpleGraph.cycleGraph 4).Free G)
    {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c d) (h4 : G.Adj d a) : False := by
  let f : Fin 4 → Fin n := fun i =>
    match i with
    | ⟨0, _⟩ => a
    | ⟨1, _⟩ => b
    | ⟨2, _⟩ => c
    | ⟨3, _⟩ => d
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [f] at hij <;>
      first | rfl | exact absurd hij hab | exact absurd hij hac | exact absurd hij had | exact absurd hij.symm hab | exact absurd hij hbc | exact absurd hij hbd | exact absurd hij.symm hac | exact absurd hij.symm hbc | exact absurd hij hcd | exact absurd hij.symm had | exact absurd hij.symm hbd | exact absurd hij.symm hcd
  have hcopy : (SimpleGraph.cycleGraph 4) ⊑ G := by
    refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [SimpleGraph.cycleGraph_adj, f] at hij ⊢ <;>
      first | exact absurd hij (by decide) | exact h1 | exact h1.symm | exact h2 | exact h2.symm | exact h3 | exact h3.symm | exact h4 | exact h4.symm
  exact hfree hcopy

private lemma card_inter_neighborFinset_le_one {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hfree : (SimpleGraph.cycleGraph 4).Free G)
    {u v : Fin n} (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hgt
  obtain ⟨hxu, hxv⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyu, hyv⟩ := Finset.mem_inter.mp hy
  rw [SimpleGraph.mem_neighborFinset] at hxu hxv hyu hyv
  exact no_c4_of_free hfree hxu.ne huv hyu.ne hxv.ne.symm hxy hyv.ne hxu hxv.symm hyv hyu.symm

private lemma disjoint_neighborFinset_erase {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (hfree : (SimpleGraph.cycleGraph 4).Free G)
    {v u₁ u₂ : Fin n} (hu₁ : u₁ ∈ G.neighborFinset v) (hu₂ : u₂ ∈ G.neighborFinset v)
    (hne : u₁ ≠ u₂) :
    Disjoint ((G.neighborFinset u₁).erase v) ((G.neighborFinset u₂).erase v) := by
  rw [Finset.disjoint_left]
  intro w hw₁ hw₂
  have hwv : w ≠ v := (Finset.mem_erase.mp hw₁).1
  have h1 : G.Adj u₁ w := (SimpleGraph.mem_neighborFinset G u₁ w).mp (Finset.mem_erase.mp hw₁).2
  have h2 : G.Adj u₂ w := (SimpleGraph.mem_neighborFinset G u₂ w).mp (Finset.mem_erase.mp hw₂).2
  have hv1 : G.Adj v u₁ := (SimpleGraph.mem_neighborFinset G v u₁).mp hu₁
  have hv2 : G.Adj v u₂ := (SimpleGraph.mem_neighborFinset G v u₂).mp hu₂
  exact no_c4_of_free hfree hv1.ne hwv.symm hv2.ne h1.ne hne h2.ne.symm hv1 h1 h2.symm hv2.symm

-- ### Part 2: Deficiency and Ma-Yang Lemmas 3.2 and 3.3

private def defic {n : ℕ} (q : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) : ℤ :=
  (q + 1 : ℤ) - (G.degree v : ℤ)

private lemma lemma_3_2 {n : ℕ} (q : ℕ) {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hfree : (SimpleGraph.cycleGraph 4).Free G) (v : Fin n) :
    (q : ℤ) * (G.degree v : ℤ) - (n : ℤ) + 1 ≤ ∑ u ∈ G.neighborFinset v, defic q G u := by
  have hdisj : Set.PairwiseDisjoint (G.neighborFinset v : Set (Fin n))
      (fun u => (G.neighborFinset u).erase v) := by
    intro u₁ hu₁ u₂ hu₂ hne
    exact disjoint_neighborFinset_erase hfree hu₁ hu₂ hne
  have hsub : (G.neighborFinset v).biUnion (fun u => (G.neighborFinset u).erase v) ⊆
      (Finset.univ : Finset (Fin n)).erase v := by
    intro w hw
    obtain ⟨u, _, hwu⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hwu).1, Finset.mem_univ w⟩
  have hcard : ∑ u ∈ G.neighborFinset v, (G.degree u - 1) ≤ n - 1 := by
    have h1 : ∑ u ∈ G.neighborFinset v, ((G.neighborFinset u).erase v).card ≤ n - 1 := by
      calc ∑ u ∈ G.neighborFinset v, ((G.neighborFinset u).erase v).card
          = ((G.neighborFinset v).biUnion (fun u => (G.neighborFinset u).erase v)).card :=
            (Finset.card_biUnion hdisj).symm
        _ ≤ ((Finset.univ : Finset (Fin n)).erase v).card := Finset.card_le_card hsub
        _ = n - 1 := by simp [Finset.card_erase_of_mem (Finset.mem_univ v)]
    have h2 : ∀ u ∈ G.neighborFinset v, ((G.neighborFinset u).erase v).card = G.degree u - 1 := by
      intro u hu
      have hvu : v ∈ G.neighborFinset u := by
        rw [SimpleGraph.mem_neighborFinset] at hu ⊢; exact hu.symm
      rw [Finset.card_erase_of_mem hvu, SimpleGraph.card_neighborFinset_eq_degree]
    rwa [Finset.sum_congr rfl h2] at h1
  have hsum_cast : (∑ u ∈ G.neighborFinset v, ((G.degree u : ℤ) - 1)) ≤ (n : ℤ) - 1 := by
    have hge1 : ∀ u ∈ G.neighborFinset v, 1 ≤ G.degree u := by
      intro u hu
      have hvu : v ∈ G.neighborFinset u := by
        rw [SimpleGraph.mem_neighborFinset] at hu ⊢; exact hu.symm
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨v, hvu⟩
    have hcast : ∑ u ∈ G.neighborFinset v, ((G.degree u : ℤ) - 1) =
        ((∑ u ∈ G.neighborFinset v, (G.degree u - 1) : ℕ) : ℤ) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Nat.cast_sub (hge1 u hu), Nat.cast_one]
    rw [hcast]
    have hn1 : 1 ≤ n := by
      have : 0 < Fintype.card (Fin n) := Fintype.card_pos_iff.mpr ⟨v⟩
      rw [Fintype.card_fin] at this; omega
    have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
    rw [← this]
    exact_mod_cast hcard
  have heq : ∑ u ∈ G.neighborFinset v, defic q G u =
      (q : ℤ) * (G.degree v : ℤ) - ∑ u ∈ G.neighborFinset v, ((G.degree u : ℤ) - 1) := by
    unfold defic
    have h1 : ∀ u ∈ G.neighborFinset v,
        (q + 1 : ℤ) - (G.degree u : ℤ) = (q : ℤ) - ((G.degree u : ℤ) - 1) := fun _ _ => by ring
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const,
      SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_comm]
  linarith

private lemma sq_sum_le_card_mul_sum_sq {α : Type*} (S : Finset α) (g : α → ℤ) :
    (∑ x ∈ S, g x) ^ 2 ≤ (S.card : ℤ) * ∑ x ∈ S, (g x) ^ 2 := by
  have h0 : 0 ≤ ∑ x ∈ S, ∑ y ∈ S, (g x - g y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hexp : ∑ x ∈ S, ∑ y ∈ S, (g x - g y) ^ 2 =
      2 * ((S.card : ℤ) * ∑ x ∈ S, (g x) ^ 2 - (∑ x ∈ S, g x) ^ 2) := by
    have h1 : ∀ x ∈ S, ∑ y ∈ S, (g x - g y) ^ 2 =
        (S.card : ℤ) * (g x) ^ 2 - 2 * g x * (∑ y ∈ S, g y) + ∑ y ∈ S, (g y) ^ 2 := by
      intro x _
      have : ∀ y ∈ S, (g x - g y) ^ 2 = (g x) ^ 2 - 2 * g x * g y + (g y) ^ 2 := fun _ _ => by ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
    have h2 : ∑ x ∈ S, 2 * g x = 2 * ∑ x ∈ S, g x := (Finset.mul_sum S g 2).symm
    rw [h2]; ring
  linarith

private lemma lemma_3_3 {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hfree : (SimpleGraph.cycleGraph 4).Free G)
    (v : Fin n) (I : Finset (Fin n)) (hI : I ⊆ G.neighborFinset v) (hIne : I.Nonempty)
    (hL_ge : (n : ℤ) - (I.card : ℤ) ≤
      2 * (G.edgeFinset.card : ℤ) - (∑ u ∈ I, (G.degree u : ℤ)) +
        ((I.card : ℤ) - 1) * (G.degree v : ℤ) - (n : ℤ) * (I.card : ℤ) + (I.card : ℤ)) :
    let k : ℤ := (I.card : ℤ)
    let s : ℤ := ∑ u ∈ I, (G.degree u : ℤ)
    let L : ℤ := 2 * (G.edgeFinset.card : ℤ) - s + (k - 1) * (G.degree v : ℤ) - (n : ℤ) * k + k
    L * (L - ((n : ℤ) - k)) ≤
      ((n : ℤ) - s + k - 1) * ((n : ℤ) - s + k - 2) * ((n : ℤ) - k) := by
  classical
  intro k s L
  let X : Finset (Fin n) := I.biUnion (fun u => G.neighborFinset u)
  -- |X| = s - k + 1
  have hXcard : (X.card : ℤ) = s - k + 1 := by
    have hvX : v ∈ X := by
      obtain ⟨u₀, hu₀⟩ := hIne
      refine Finset.mem_biUnion.mpr ⟨u₀, hu₀, ?_⟩
      rw [SimpleGraph.mem_neighborFinset]
      exact ((SimpleGraph.mem_neighborFinset G v u₀).mp (hI hu₀)).symm
    have hXeq : X = insert v (I.biUnion (fun u => (G.neighborFinset u).erase v)) := by
      ext w
      simp only [X, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨u, huI, hwu⟩
        by_cases hwv : w = v
        · exact Or.inl hwv
        · exact Or.inr ⟨u, huI, hwv, hwu⟩
      · rintro (rfl | ⟨u, huI, _, hwu⟩)
        · obtain ⟨u₀, hu₀⟩ := hIne
          exact ⟨u₀, hu₀, (SimpleGraph.mem_neighborFinset G u₀ w).mpr
            ((SimpleGraph.mem_neighborFinset G w u₀).mp (hI hu₀)).symm⟩
        · exact ⟨u, huI, hwu⟩
    have hv_not : v ∉ I.biUnion (fun u => (G.neighborFinset u).erase v) := by
      simp only [Finset.mem_biUnion, Finset.mem_erase, not_exists, not_and]
      intro u _ hne _; exact hne rfl
    have hdisj : Set.PairwiseDisjoint (I : Set (Fin n)) (fun u => (G.neighborFinset u).erase v) := by
      intro u₁ hu₁ u₂ hu₂ hne
      exact disjoint_neighborFinset_erase hfree (hI hu₁) (hI hu₂) hne
    have hcard_nat : X.card = 1 + ∑ u ∈ I, (G.degree u - 1) := by
      rw [hXeq, Finset.card_insert_of_notMem hv_not, Finset.card_biUnion hdisj, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun u hu => ?_
      have hvu : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u v).mpr
        ((SimpleGraph.mem_neighborFinset G v u).mp (hI hu)).symm
      rw [Finset.card_erase_of_mem hvu, SimpleGraph.card_neighborFinset_eq_degree]
    have hge1 : ∀ u ∈ I, 1 ≤ G.degree u := by
      intro u hu
      have hvu : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u v).mpr
        ((SimpleGraph.mem_neighborFinset G v u).mp (hI hu)).symm
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨v, hvu⟩
    rw [hcard_nat, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
    have hsum : ∑ u ∈ I, ((G.degree u - 1 : ℕ) : ℤ) = s - k := by
      have h1 : ∀ u ∈ I, ((G.degree u - 1 : ℕ) : ℤ) = (G.degree u : ℤ) - 1 := fun u hu => by
        rw [Nat.cast_sub (hge1 u hu), Nat.cast_one]
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum]; ring
  let Y : Finset (Fin n) := Finset.univ \ X
  have hYcard : (Y.card : ℤ) = (n : ℤ) - s + k - 1 := by
    have h1 : Y.card + X.card = n := by
      simpa [Y] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ X)
    have h2 : (Y.card : ℤ) + (X.card : ℤ) = (n : ℤ) := by exact_mod_cast h1
    linarith
  -- Count ordered 2-paths (a, w, b) with w ∉ I, a ≠ b ∈ Y, w ~ a, w ~ b
  let dY (w : Fin n) : ℕ := (G.neighborFinset w ∩ Y).card
  -- Upper bound: each ordered pair (a, b) ∈ Y.offDiag has at most 1 common neighbor w
  have hub : ∑ w ∈ Finset.univ \ I, dY w * (dY w - 1) ≤ Y.card * (Y.card - 1) := by
    let P : Finset ((Fin n × Fin n) × Fin n) :=
      (Finset.univ \ I).biUnion (fun w => ((G.neighborFinset w ∩ Y).offDiag).image (fun ab => (ab, w)))
    have hPcard : P.card = ∑ w ∈ Finset.univ \ I, dY w * (dY w - 1) := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
          Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
      · intro w₁ _ w₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro x hx₁ hx₂
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx₁
        obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hx₂
        exact hne (Prod.mk.inj heq).2.symm
    have hPinj : Set.InjOn Prod.fst (P : Set ((Fin n × Fin n) × Fin n)) := by
      rintro ⟨⟨a, b⟩, w₁⟩ h₁ ⟨⟨a', b'⟩, w₂⟩ h₂ hfst
      simp only at hfst
      rcases Prod.mk.inj hfst with ⟨rfl, rfl⟩
      obtain ⟨u₁, _, h₁'⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp h₁)
      obtain ⟨_, h₁od, h₁eq⟩ := Finset.mem_image.mp h₁'
      rcases Prod.mk.inj h₁eq with ⟨h1ab, hu₁eq⟩
      rw [h1ab, hu₁eq] at h₁od
      obtain ⟨u₂, _, h₂'⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp h₂)
      obtain ⟨_, h₂od, h₂eq⟩ := Finset.mem_image.mp h₂'
      rcases Prod.mk.inj h₂eq with ⟨h2ab, hu₂eq⟩
      rw [h2ab, hu₂eq] at h₂od
      obtain ⟨ha1, hb1, hab⟩ := Finset.mem_offDiag.mp h₁od
      obtain ⟨ha2, hb2, _⟩ := Finset.mem_offDiag.mp h₂od
      have hwa1 : G.Adj a w₁ := ((SimpleGraph.mem_neighborFinset G w₁ a).mp (Finset.mem_inter.mp ha1).1).symm
      have hwb1 : G.Adj b w₁ := ((SimpleGraph.mem_neighborFinset G w₁ b).mp (Finset.mem_inter.mp hb1).1).symm
      have hwa2 : G.Adj a w₂ := ((SimpleGraph.mem_neighborFinset G w₂ a).mp (Finset.mem_inter.mp ha2).1).symm
      have hwb2 : G.Adj b w₂ := ((SimpleGraph.mem_neighborFinset G w₂ b).mp (Finset.mem_inter.mp hb2).1).symm
      have hw12 : w₁ = w₂ := by
        by_contra hne
        have h1 : w₁ ∈ G.neighborFinset a ∩ G.neighborFinset b :=
          Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset G a w₁).mpr hwa1,
            (SimpleGraph.mem_neighborFinset G b w₁).mpr hwb1⟩
        have h2 : w₂ ∈ G.neighborFinset a ∩ G.neighborFinset b :=
          Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset G a w₂).mpr hwa2,
            (SimpleGraph.mem_neighborFinset G b w₂).mpr hwb2⟩
        have hle := card_inter_neighborFinset_le_one hfree hab
        dsimp only at hle
        have hlt : 1 < (G.neighborFinset a ∩ G.neighborFinset b).card :=
          Finset.one_lt_card.mpr ⟨w₁, h1, w₂, h2, hne⟩
        omega
      subst hw12; rfl
    have hPsub : P.image Prod.fst ⊆ Y.offDiag := by
      intro ⟨a, b⟩ hab
      obtain ⟨⟨⟨a', b'⟩, w⟩, hmem, hfst⟩ := Finset.mem_image.mp hab
      simp only at hfst
      rcases Prod.mk.inj hfst with ⟨rfl, rfl⟩
      obtain ⟨u, _, h'⟩ := Finset.mem_biUnion.mp hmem
      obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h'
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
      exact Finset.mem_offDiag.mpr ⟨(Finset.mem_inter.mp ha).2, (Finset.mem_inter.mp hb).2, hne⟩
    calc ∑ w ∈ Finset.univ \ I, dY w * (dY w - 1)
        = P.card := hPcard.symm
      _ = (P.image Prod.fst).card := (Finset.card_image_of_injOn hPinj).symm
      _ ≤ Y.offDiag.card := Finset.card_le_card hPsub
      _ = Y.card * (Y.card - 1) := by rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
  -- Lower bound on ∑_{w ∉ I} dY w ≥ L
  have hdY_nv : ∀ w ∈ G.neighborFinset v \ I, (G.degree w : ℤ) - 1 ≤ (dY w : ℤ) := by
    intro w hw
    have hwN : w ∈ G.neighborFinset v := (Finset.mem_sdiff.mp hw).1
    have hwI : w ∉ I := (Finset.mem_sdiff.mp hw).2
    have hinter : G.neighborFinset w ∩ X ⊆ {v} := by
      intro x hx
      obtain ⟨hxw, hxX⟩ := Finset.mem_inter.mp hx
      obtain ⟨u, huI, hxu⟩ := Finset.mem_biUnion.mp hxX
      by_contra hxv
      simp only [Finset.mem_singleton] at hxv
      have hwu : w ≠ u := fun h => hwI (h ▸ huI)
      have hdisj := disjoint_neighborFinset_erase hfree hwN (hI huI) hwu
      exact Finset.disjoint_left.mp hdisj
        (Finset.mem_erase.mpr ⟨hxv, hxw⟩) (Finset.mem_erase.mpr ⟨hxv, hxu⟩)
    have hsplit : (G.neighborFinset w ∩ Y).card + (G.neighborFinset w ∩ X).card = G.degree w := by
      have hunion : (G.neighborFinset w ∩ Y) ∪ (G.neighborFinset w ∩ X) = G.neighborFinset w := by
        ext x; simp only [Finset.mem_union, Finset.mem_inter, Y, Finset.mem_sdiff, Finset.mem_univ, true_and]
        tauto
      have hdisj : Disjoint (G.neighborFinset w ∩ Y) (G.neighborFinset w ∩ X) := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h1).2).2 (Finset.mem_inter.mp h2).2
      rw [← Finset.card_union_of_disjoint hdisj, hunion, SimpleGraph.card_neighborFinset_eq_degree]
    have hle1 : (G.neighborFinset w ∩ X).card ≤ 1 := le_trans (Finset.card_le_card hinter) (by simp)
    have : dY w + (G.neighborFinset w ∩ X).card = G.degree w := hsplit
    omega
  have hdY_gen : ∀ w ∈ Finset.univ \ I, (G.degree w : ℤ) - k ≤ (dY w : ℤ) := by
    intro w hw
    have hwI : w ∉ I := (Finset.mem_sdiff.mp hw).2
    have hsub : G.neighborFinset w ∩ X ⊆ I.biUnion (fun u => G.neighborFinset w ∩ G.neighborFinset u) := by
      intro x hx
      obtain ⟨hxw, hxX⟩ := Finset.mem_inter.mp hx
      obtain ⟨u, huI, hxu⟩ := Finset.mem_biUnion.mp hxX
      exact Finset.mem_biUnion.mpr ⟨u, huI, Finset.mem_inter.mpr ⟨hxw, hxu⟩⟩
    have hle_k : (G.neighborFinset w ∩ X).card ≤ I.card := by
      calc (G.neighborFinset w ∩ X).card
          ≤ (I.biUnion (fun u => G.neighborFinset w ∩ G.neighborFinset u)).card := Finset.card_le_card hsub
        _ ≤ ∑ u ∈ I, (G.neighborFinset w ∩ G.neighborFinset u).card := Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ I, 1 := Finset.sum_le_sum fun u hu =>
            card_inter_neighborFinset_le_one hfree (fun h => hwI (h ▸ hu))
        _ = I.card := by simp
    have hsplit : dY w + (G.neighborFinset w ∩ X).card = G.degree w := by
      have hunion : (G.neighborFinset w ∩ Y) ∪ (G.neighborFinset w ∩ X) = G.neighborFinset w := by
        ext x; simp only [Finset.mem_union, Finset.mem_inter, Y, Finset.mem_sdiff, Finset.mem_univ, true_and]
        tauto
      have hdisj : Disjoint (G.neighborFinset w ∩ Y) (G.neighborFinset w ∩ X) := by
        rw [Finset.disjoint_left]
        intro x h1 h2
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp h1).2).2 (Finset.mem_inter.mp h2).2
      rw [← Finset.card_union_of_disjoint hdisj, hunion, SimpleGraph.card_neighborFinset_eq_degree]
    omega
  have hL_le : L ≤ ∑ w ∈ Finset.univ \ I, (dY w : ℤ) := by
    have hpart : Finset.univ \ I = (G.neighborFinset v \ I) ∪ (Finset.univ \ G.neighborFinset v) := by
      ext w
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]
      constructor
      · intro hwI
        by_cases hwN : w ∈ G.neighborFinset v
        · exact Or.inl ⟨hwN, hwI⟩
        · exact Or.inr hwN
      · rintro (⟨_, hwI⟩ | hwN)
        · exact hwI
        · exact fun h => hwN (hI h)
    have hdisj_p : Disjoint (G.neighborFinset v \ I) (Finset.univ \ G.neighborFinset v) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact (Finset.mem_sdiff.mp h2).2 (Finset.mem_sdiff.mp h1).1
    have hsum1 : ∑ w ∈ G.neighborFinset v \ I, ((G.degree w : ℤ) - 1) ≤
        ∑ w ∈ G.neighborFinset v \ I, (dY w : ℤ) := Finset.sum_le_sum hdY_nv
    have hsum2 : ∑ w ∈ Finset.univ \ G.neighborFinset v, ((G.degree w : ℤ) - k) ≤
        ∑ w ∈ Finset.univ \ G.neighborFinset v, (dY w : ℤ) :=
      Finset.sum_le_sum fun w hw => hdY_gen w (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h =>
        (Finset.mem_sdiff.mp hw).2 (hI h)⟩)
    have hhandshake : ∑ w : Fin n, (G.degree w : ℤ) = 2 * (G.edgeFinset.card : ℤ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have hsum_deg : ∑ w ∈ Finset.univ \ I, (G.degree w : ℤ) = 2 * (G.edgeFinset.card : ℤ) - s := by
      have h1 := Finset.sum_sdiff (Finset.subset_univ I) (f := fun w : Fin n => (G.degree w : ℤ))
      linarith
    have hcard1 : ((G.neighborFinset v \ I).card : ℤ) = (G.degree v : ℤ) - k := by
      have h1 := Finset.card_sdiff_add_card_eq_card hI
      rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
      have h2 : ((G.neighborFinset v \ I).card : ℤ) + (I.card : ℤ) = (G.degree v : ℤ) := by exact_mod_cast h1
      linarith
    have hcard2 : ((Finset.univ \ G.neighborFinset v).card : ℤ) = (n : ℤ) - (G.degree v : ℤ) := by
      have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (G.neighborFinset v))
      rw [SimpleGraph.card_neighborFinset_eq_degree, Finset.card_univ, Fintype.card_fin] at h1
      have h2 : ((Finset.univ \ G.neighborFinset v).card : ℤ) + (G.degree v : ℤ) = (n : ℤ) := by exact_mod_cast h1
      linarith
    have hsum_split : ∑ w ∈ Finset.univ \ I, (G.degree w : ℤ) =
        ∑ w ∈ G.neighborFinset v \ I, (G.degree w : ℤ) +
        ∑ w ∈ Finset.univ \ G.neighborFinset v, (G.degree w : ℤ) := by
      rw [hpart, Finset.sum_union hdisj_p]
    have hsum_dY : ∑ w ∈ Finset.univ \ I, (dY w : ℤ) =
        ∑ w ∈ G.neighborFinset v \ I, (dY w : ℤ) +
        ∑ w ∈ Finset.univ \ G.neighborFinset v, (dY w : ℤ) := by
      rw [hpart, Finset.sum_union hdisj_p]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcard1] at hsum1
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard2] at hsum2
    have hL_eq : L = (2 * (G.edgeFinset.card : ℤ) - s) - ((G.degree v : ℤ) - k) -
        ((n : ℤ) - (G.degree v : ℤ)) * k := by
      dsimp only [L]; ring
    linarith
  -- Apply Cauchy-Schwarz to ∑_{w ∉ I} dY w
  have hcard_c : ((Finset.univ \ I).card : ℤ) = (n : ℤ) - k := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ((Finset.univ \ I).card : ℤ) + (I.card : ℤ) = (n : ℤ) := by exact_mod_cast h1
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (Finset.univ \ I) (fun w => (dY w : ℤ))
  rw [hcard_c] at hcs
  have hub_z : ∑ w ∈ Finset.univ \ I, ((dY w : ℤ) ^ 2 - (dY w : ℤ)) ≤
      (Y.card : ℤ) * ((Y.card : ℤ) - 1) := by
    have h1 : ∀ w ∈ Finset.univ \ I, ((dY w * (dY w - 1) : ℕ) : ℤ) = (dY w : ℤ) ^ 2 - (dY w : ℤ) := by
      intro w _
      rcases Nat.eq_zero_or_pos (dY w) with h0 | hpos
      · simp [h0]
      · rw [Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one]; ring
    have h2 : ((Y.card * (Y.card - 1) : ℕ) : ℤ) = (Y.card : ℤ) * ((Y.card : ℤ) - 1) := by
      rcases Nat.eq_zero_or_pos Y.card with h0 | hpos
      · simp [h0]
      · rw [Nat.cast_mul, Nat.cast_sub hpos, Nat.cast_one]
    have h3 : ((∑ w ∈ Finset.univ \ I, dY w * (dY w - 1) : ℕ) : ℤ) ≤ ((Y.card * (Y.card - 1) : ℕ) : ℤ) := by
      exact_mod_cast hub
    rw [Nat.cast_sum, Finset.sum_congr rfl h1, h2] at h3
    exact h3
  rw [Finset.sum_sub_distrib] at hub_z
  set S1 : ℤ := ∑ w ∈ Finset.univ \ I, (dY w : ℤ)
  set S2 : ℤ := ∑ w ∈ Finset.univ \ I, (dY w : ℤ) ^ 2
  have hnk_nn : 0 ≤ (n : ℤ) - k := by rw [← hcard_c]; exact Nat.cast_nonneg _
  have hS1_nn : 0 ≤ S1 := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hstep1 : S1 * (S1 - ((n : ℤ) - k)) ≤ (Y.card : ℤ) * ((Y.card : ℤ) - 1) * ((n : ℤ) - k) := by
    have h1 : ((n : ℤ) - k) * (S2 - S1) ≤ ((n : ℤ) - k) * ((Y.card : ℤ) * ((Y.card : ℤ) - 1)) :=
      mul_le_mul_of_nonneg_left hub_z hnk_nn
    nlinarith only [hcs, h1]
  have hL_vs_S1 : L * (L - ((n : ℤ) - k)) ≤ S1 * (S1 - ((n : ℤ) - k)) := by
    have hL_ge' : (n : ℤ) - k ≤ L := hL_ge
    nlinarith only [hL_le, hL_ge', hnk_nn]
  rw [hYcard] at hstep1
  linarith

-- ### Part 3: Ma-Yang Section 5 (Eq. 14) at q = 20*m, r = 6*m, k = 11*m

private lemma appendix_B_poly (m s : ℤ) (hm : 10 ≤ m)
    (hs1 : 11 * m * (20 * m + 2) ≤ s)
    (hs2 : s ≤ 400 * m ^ 2 + 37 * m) :
    let q : ℤ := 20 * m
    let k : ℤ := 11 * m
    let n : ℤ := 400 * m ^ 2 + 26 * m + 1
    let L0 : ℤ := n * (q + 1) - s + (k - 1) * (14 * m) - n * k + k
    (n - s + k - 1) * (n - s + k - 2) * (n - k) < L0 * (L0 - (n - k)) := by
  intro q k n L0
  set Gval : ℤ → ℤ := fun x =>
    (n - x + k - 1) * (n - x + k - 2) * (n - k) -
      (n * (q + 1) - x + (k - 1) * (14 * m) - n * k + k) *
      (n * (q + 1) - x + (k - 1) * (14 * m) - n * k + k - (n - k))
  set s1 : ℤ := 11 * m * (20 * m + 2)
  set s2 : ℤ := 400 * m ^ 2 + 37 * m
  have hs12 : 0 < s2 - s1 := by nlinarith only [hm]
  -- Exact quadratic decomposition: (s2 - s1) * Gval s = (s2 - s1) * (n - k - 1) * (s - s1) * (s - s2) + (s2 - s) * Gval s1 + (s - s1) * Gval s2
  have hquad : (s2 - s1) * Gval s =
      (s2 - s1) * (n - k - 1) * (s - s1) * (s - s2) +
        (s2 - s) * Gval s1 + (s - s1) * Gval s2 := by
    simp only [Gval, s1, s2, n, q, k]
    ring
  have hG1 : Gval s1 < 0 := by
    have h1 : Gval s1 = -3600 * m ^ 5 + 17976 * m ^ 4 - 2365 * m ^ 3 - 298 * m ^ 2 - 10 * m := by
      simp only [Gval, s1, n, q, k]; ring
    rw [h1]
    have hm2 : 100 ≤ m ^ 2 := by nlinarith only [hm]
    have hm3 : 1000 ≤ m ^ 3 := by nlinarith only [hm, hm2]
    have hm4 : 10000 ≤ m ^ 4 := by nlinarith only [hm, hm3]
    have hlead : -3600 * m ^ 5 + 17976 * m ^ 4 ≤ -18024 * m ^ 4 := by nlinarith only [hm, hm4]
    nlinarith only [hm, hm2, hm3, hm4, hlead]
  have hG2 : Gval s2 < 0 := by
    have h2 : Gval s2 = -12960000 * m ^ 6 - 1353600 * m ^ 5 + 94656 * m ^ 4 + 4100 * m ^ 3 - 88 * m ^ 2 + 20 * m := by
      simp only [Gval, s2, n, q, k]; ring
    rw [h2]
    have hm2 : 100 ≤ m ^ 2 := by nlinarith only [hm]
    have hm3 : 1000 ≤ m ^ 3 := by nlinarith only [hm, hm2]
    have hm4 : 10000 ≤ m ^ 4 := by nlinarith only [hm, hm3]
    have hm5 : 100000 ≤ m ^ 5 := by nlinarith only [hm, hm4]
    have hlead : -12960000 * m ^ 6 - 1353600 * m ^ 5 + 94656 * m ^ 4 + 4100 * m ^ 3 ≤ -12960000 * m ^ 6 := by
      nlinarith only [hm, hm3, hm4, hm5]
    nlinarith only [hm, hm2, hm5, hlead]
  have hnk1 : 0 < n - k - 1 := by nlinarith only [hm]
  have hprod_le : (s2 - s1) * (n - k - 1) * (s - s1) * (s - s2) ≤ 0 := by
    have h1 : 0 < (s2 - s1) * (n - k - 1) := mul_pos hs12 hnk1
    have h2 : (s - s1) * (s - s2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith only [h1, h2]
  have hlin_lt : (s2 - s) * Gval s1 + (s - s1) * Gval s2 < 0 := by
    have h1 : (s2 - s) * Gval s1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hG1.le
    have h2 : (s - s1) * Gval s2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hG2.le
    rcases eq_or_lt_of_le hs1 with rfl | hlt
    · have : 0 < s2 - s1 := hs12
      nlinarith only [this, hG1]
    · have : (s - s1) * Gval s2 < 0 := mul_neg_of_pos_of_neg (by linarith) hG2
      linarith
  have hGneg : Gval s < 0 := by
    have : (s2 - s1) * Gval s < 0 := by linarith
    nlinarith only [hs12, this]
  simpa only [Gval, L0, sub_lt_zero] using hGneg

private lemma ma_yang_eq14 (m n : ℕ) (hm : 10 ≤ m) (hn : n = 400 * m ^ 2 + 26 * m + 1)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hfree : (SimpleGraph.cycleGraph 4).Free G) :
    2 * G.edgeFinset.card ≤ n * (20 * m + 1) := by
  classical
  set q : ℕ := 20 * m
  set r : ℕ := 6 * m
  by_contra hgt
  push Not at hgt
  let S : Finset (Fin n) := Finset.univ.filter (fun v => G.degree v ≤ q)
  let Splus : Finset (Fin n) := Finset.univ.filter (fun v => q + 2 ≤ G.degree v)
  -- Claim: every vertex v with d(v) ≥ 14*m has |N(v) ∩ Splus| < 11*m
  have hclaim : ∀ v : Fin n, 14 * m ≤ G.degree v → (G.neighborFinset v ∩ Splus).card < 11 * m := by
    intro v hdv
    by_contra hbig
    push Not at hbig
    obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hbig
    have hIN : I ⊆ G.neighborFinset v := hIsub.trans Finset.inter_subset_left
    have hISp : I ⊆ Splus := hIsub.trans Finset.inter_subset_right
    have hIne : I.Nonempty := Finset.card_pos.mp (by omega)
    set s : ℤ := ∑ u ∈ I, (G.degree u : ℤ)
    -- Lower bound on s: each u ∈ I has degree ≥ q + 2 = 20*m + 2
    have hs1 : 11 * (m : ℤ) * (20 * (m : ℤ) + 2) ≤ s := by
      have h1 : ∀ u ∈ I, (20 * (m : ℤ) + 2) ≤ (G.degree u : ℤ) := fun u hu => by
        have := (Finset.mem_filter.mp (hISp hu)).2
        exact_mod_cast this
      calc 11 * (m : ℤ) * (20 * (m : ℤ) + 2)
          = (I.card : ℤ) * (20 * (m : ℤ) + 2) := by rw [hIcard]; push_cast; ring
        _ = ∑ _u ∈ I, (20 * (m : ℤ) + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ u ∈ I, (G.degree u : ℤ) := Finset.sum_le_sum h1
    -- Upper bound on s: s - k = ∑_{u ∈ I} (d(u) - 1) ≤ n - 1, so s ≤ n - 1 + k = 400*m^2 + 37*m
    have hs2 : s ≤ 400 * (m : ℤ) ^ 2 + 37 * (m : ℤ) := by
      have hdisj : Set.PairwiseDisjoint (I : Set (Fin n)) (fun u => (G.neighborFinset u).erase v) := by
        intro u₁ hu₁ u₂ hu₂ hne
        exact disjoint_neighborFinset_erase hfree (hIN hu₁) (hIN hu₂) hne
      have hsub : I.biUnion (fun u => (G.neighborFinset u).erase v) ⊆
          (Finset.univ : Finset (Fin n)).erase v := by
        intro w hw
        obtain ⟨u, _, hwu⟩ := Finset.mem_biUnion.mp hw
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hwu).1, Finset.mem_univ w⟩
      have hge1 : ∀ u ∈ I, 1 ≤ G.degree u := fun u hu => by
        have hvu : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u v).mpr
          ((SimpleGraph.mem_neighborFinset G v u).mp (hIN hu)).symm
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨v, hvu⟩
      have hcard_nat : ∑ u ∈ I, (G.degree u - 1) ≤ n - 1 := by
        have h1 : ∑ u ∈ I, ((G.neighborFinset u).erase v).card ≤ n - 1 := by
          calc ∑ u ∈ I, ((G.neighborFinset u).erase v).card
              = (I.biUnion (fun u => (G.neighborFinset u).erase v)).card := (Finset.card_biUnion hdisj).symm
            _ ≤ ((Finset.univ : Finset (Fin n)).erase v).card := Finset.card_le_card hsub
            _ = n - 1 := by simp [Finset.card_erase_of_mem (Finset.mem_univ v)]
        have h2 : ∀ u ∈ I, ((G.neighborFinset u).erase v).card = G.degree u - 1 := fun u hu => by
          have hvu : v ∈ G.neighborFinset u := (SimpleGraph.mem_neighborFinset G u v).mpr
            ((SimpleGraph.mem_neighborFinset G v u).mp (hIN hu)).symm
          rw [Finset.card_erase_of_mem hvu, SimpleGraph.card_neighborFinset_eq_degree]
        rwa [Finset.sum_congr rfl h2] at h1
      have hcast : s - (I.card : ℤ) = ((∑ u ∈ I, (G.degree u - 1) : ℕ) : ℤ) := by
        rw [Nat.cast_sum]
        have h1 : ∀ u ∈ I, ((G.degree u - 1 : ℕ) : ℤ) = (G.degree u : ℤ) - 1 := fun u hu => by
          rw [Nat.cast_sub (hge1 u hu), Nat.cast_one]
        rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hle_z : s - (I.card : ℤ) ≤ (n : ℤ) - 1 := by
        rw [hcast]
        have hn1 : 1 ≤ n := by omega
        have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by rw [Nat.cast_sub hn1, Nat.cast_one]
        rw [← this]; exact_mod_cast hcard_nat
      have hk_eq : (I.card : ℤ) = 11 * (m : ℤ) := by exact_mod_cast hIcard
      have hn_eq : (n : ℤ) = 400 * (m : ℤ) ^ 2 + 26 * (m : ℤ) + 1 := by rw [hn]; push_cast; ring
      linarith
    -- Check L ≥ L0 ≥ n - k
    set kZ : ℤ := 11 * (m : ℤ)
    set nZ : ℤ := 400 * (m : ℤ) ^ 2 + 26 * (m : ℤ) + 1
    set L0 : ℤ := nZ * (20 * (m : ℤ) + 1) - s + (kZ - 1) * (14 * (m : ℤ)) - nZ * kZ + kZ
    set L : ℤ := 2 * (G.edgeFinset.card : ℤ) - s + ((I.card : ℤ) - 1) * (G.degree v : ℤ) - (n : ℤ) * (I.card : ℤ) + (I.card : ℤ)
    have hIcard_z : (I.card : ℤ) = kZ := by simp only [kZ]; exact_mod_cast hIcard
    have hn_z : (n : ℤ) = nZ := by rw [hn]; push_cast [nZ]; ring
    have hL0_le_L : L0 ≤ L := by
      have he : nZ * (20 * (m : ℤ) + 1) ≤ 2 * (G.edgeFinset.card : ℤ) := by
        have h1 : (n : ℤ) * (20 * (m : ℤ) + 1) < 2 * (G.edgeFinset.card : ℤ) := by exact_mod_cast hgt
        rw [hn_z] at h1
        linarith
      have hdv_z : 14 * (m : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast hdv
      have hk1 : 0 ≤ kZ - 1 := by
        have : (10 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
        simp only [kZ]; linarith
      have hmul : (kZ - 1) * (14 * (m : ℤ)) ≤ (kZ - 1) * (G.degree v : ℤ) :=
        mul_le_mul_of_nonneg_left hdv_z hk1
      simp only [L, L0, hIcard_z, hn_z]
      linarith
    have hL0_ge_nk : nZ - kZ ≤ L0 := by
      have hm_z : (10 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      have hm2 : 100 ≤ (m : ℤ) ^ 2 := by nlinarith only [hm_z]
      have hm3 : 1000 ≤ (m : ℤ) ^ 3 := by nlinarith only [hm_z, hm2]
      have h1 : L0 - (nZ - kZ) = 3600 * (m : ℤ) ^ 3 + 388 * (m : ℤ) ^ 2 + 17 * (m : ℤ) - s := by
        simp only [L0, nZ, kZ]; ring
      nlinarith only [h1, hs2, hm_z, hm2, hm3]
    have hL_ge_nk : (n : ℤ) - (I.card : ℤ) ≤ L := by
      rw [hIcard_z, hn_z]; exact le_trans hL0_ge_nk hL0_le_L
    have h33 := lemma_3_3 hfree v I hIN hIne hL_ge_nk
    have hpoly := appendix_B_poly (m : ℤ) s (by exact_mod_cast hm) hs1 hs2
    have hnk_nn : 0 ≤ nZ - kZ := by
      have hm_z : (10 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      nlinarith only [hm_z]
    have hmono : L0 * (L0 - (nZ - kZ)) ≤ L * (L - (nZ - kZ)) := by
      nlinarith only [hL0_le_L, hL0_ge_nk, hnk_nn]
    have h33' : L * (L - (nZ - kZ)) ≤ (nZ - s + kZ - 1) * (nZ - s + kZ - 2) * (nZ - kZ) := by
      simpa only [hIcard_z, hn_z, s, L] using h33
    linarith
  -- Every v ∈ S has |N(v) ∩ Splus| ≤ 14*m - 1
  have hS_deg : ∀ v ∈ S, ((G.neighborFinset v ∩ Splus).card : ℤ) ≤ 14 * (m : ℤ) - 1 := by
    intro v _
    by_cases hdv : 14 * m ≤ G.degree v
    · have hlt := hclaim v hdv
      have : (G.neighborFinset v ∩ Splus).card ≤ 14 * m - 1 := by omega
      have h14 : 1 ≤ 14 * m := by omega
      have hcast : ((14 * m - 1 : ℕ) : ℤ) = 14 * (m : ℤ) - 1 := by rw [Nat.cast_sub h14]; push_cast; ring
      rw [← hcast]; exact_mod_cast this
    · have hle : (G.neighborFinset v ∩ Splus).card ≤ G.degree v := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_le_card Finset.inter_subset_left
      have : (G.neighborFinset v ∩ Splus).card ≤ 14 * m - 1 := by omega
      have h14 : 1 ≤ 14 * m := by omega
      have hcast : ((14 * m - 1 : ℕ) : ℤ) = 14 * (m : ℤ) - 1 := by rw [Nat.cast_sub h14]; push_cast; ring
      rw [← hcast]; exact_mod_cast this
  -- Double count W = ∑_{u ∈ Splus} ∑_{v ∈ N(u) ∩ S} defic q G v
  let W : ℤ := ∑ u ∈ Splus, ∑ v ∈ G.neighborFinset u ∩ S, defic q G v
  have hW_lb : 14 * (m : ℤ) * (- ∑ u ∈ Splus, defic q G u) ≤ W := by
    have hterm : ∀ u ∈ Splus, 14 * (m : ℤ) * (- defic q G u) ≤ ∑ v ∈ G.neighborFinset u ∩ S, defic q G v := by
      intro u hu
      have hdu : q + 2 ≤ G.degree u := (Finset.mem_filter.mp hu).2
      have hdef_neg : defic q G u ≤ -1 := by unfold defic; omega
      have h32 := lemma_3_2 q hfree u
      -- ∑_{v ∈ N(u)} defic v ≤ ∑_{v ∈ N(u) ∩ S} defic v (since v ∉ S implies defic v ≤ 0)
      have hsub_sum : ∑ v ∈ G.neighborFinset u, defic q G v ≤
          ∑ v ∈ G.neighborFinset u ∩ S, defic q G v := by
        have hsplit := Finset.sum_sdiff (Finset.inter_subset_left (s₁ := G.neighborFinset u) (s₂ := S))
          (f := defic q G)
        have hnonpos : ∑ v ∈ G.neighborFinset u \ (G.neighborFinset u ∩ S), defic q G v ≤ 0 := by
          apply Finset.sum_nonpos
          intro v hv
          have hvnotS : v ∉ S := fun hS =>
            (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv).1, hS⟩)
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hvnotS
          unfold defic; omega
        linarith
      have halg : (q : ℤ) * (G.degree u : ℤ) - (n : ℤ) + 1 =
          -(defic q G u) * (q : ℤ) - (r : ℤ) := by
        have hn_z : (n : ℤ) = 400 * (m : ℤ) ^ 2 + 26 * (m : ℤ) + 1 := by
          have : (n : ℤ) = ((400 * m ^ 2 + 26 * m + 1 : ℕ) : ℤ) := congrArg Nat.cast hn
          rw [this]; push_cast; ring
        unfold defic; rw [hn_z]; simp only [q, r]; push_cast; ring
      have h14_le : 14 * (m : ℤ) * (- defic q G u) ≤ -(defic q G u) * (q : ℤ) - (r : ℤ) := by
        have hqr : (q : ℤ) - (r : ℤ) = 14 * (m : ℤ) := by simp only [q, r]; push_cast; ring
        have hr_nn : 0 ≤ (r : ℤ) := Nat.cast_nonneg r
        nlinarith only [hdef_neg, hqr, hr_nn]
      linarith
    calc 14 * (m : ℤ) * (- ∑ u ∈ Splus, defic q G u)
        = ∑ u ∈ Splus, 14 * (m : ℤ) * (- defic q G u) := by
          rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      _ ≤ W := Finset.sum_le_sum hterm
  have hW_ub : W ≤ (14 * (m : ℤ) - 1) * (∑ v ∈ S, defic q G v) := by
    -- Swap sums
    have hswap : W = ∑ v ∈ S, ((G.neighborFinset v ∩ Splus).card : ℤ) * defic q G v := by
      have h1 : W = ∑ u ∈ Splus, ∑ v ∈ S, if G.Adj u v then defic q G v else 0 := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [← Finset.sum_filter]
        congr 1
        ext v; simp [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        tauto
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      have h2 : ∑ u ∈ Splus, (if G.Adj u v then defic q G v else 0) =
          ∑ _u ∈ G.neighborFinset v ∩ Splus, defic q G v := by
        rw [← Finset.sum_filter]
        congr 1
        ext u; simp [Finset.mem_inter, SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
        tauto
      rw [h2, Finset.sum_const, nsmul_eq_mul]
    rw [hswap, Finset.mul_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    have hdef_pos : 0 ≤ defic q G v := by
      have := (Finset.mem_filter.mp hv).2
      unfold defic; omega
    exact mul_le_mul_of_nonneg_right (hS_deg v hv) hdef_pos
  -- Sum of all deficiencies is negative: f(S) + f(Splus) = n(q+1) - 2e(G) < 0
  have hsum_all : (∑ v ∈ S, defic q G v) + (∑ u ∈ Splus, defic q G u) < 0 := by
    have hhandshake : ∑ v : Fin n, (G.degree v : ℤ) = 2 * (G.edgeFinset.card : ℤ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    have htot : ∑ v : Fin n, defic q G v = (n : ℤ) * ((q : ℤ) + 1) - 2 * (G.edgeFinset.card : ℤ) := by
      unfold defic
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hhandshake]
    have hdisj : Disjoint S Splus := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      have h1 := (Finset.mem_filter.mp hv1).2
      have h2 := (Finset.mem_filter.mp hv2).2
      omega
    have hzero : ∑ v ∈ Finset.univ \ (S ∪ Splus), defic q G v = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      have hnot := (Finset.mem_sdiff.mp hv).2
      simp only [Finset.mem_union, S, Splus, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_le] at hnot
      unfold defic; omega
    have hsplit : ∑ v : Fin n, defic q G v = (∑ v ∈ S, defic q G v) + (∑ u ∈ Splus, defic q G u) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ (S ∪ Splus)), hzero, zero_add, Finset.sum_union hdisj]
    have hgt_z : (n : ℤ) * ((q : ℤ) + 1) < 2 * (G.edgeFinset.card : ℤ) := by exact_mod_cast hgt
    linarith
  have hfS_nn : 0 ≤ ∑ v ∈ S, defic q G v := Finset.sum_nonneg fun v hv => by
    have := (Finset.mem_filter.mp hv).2; unfold defic; omega
  have hm_pos : (0 : ℤ) < 14 * (m : ℤ) := by omega
  nlinarith only [hW_lb, hW_ub, hsum_all, hfS_nn, hm_pos]

private lemma extremalNumber_c4_subseq (m : ℕ) (hm : 10 ≤ m) :
    (SimpleGraph.extremalNumber (400 * m ^ 2 + 26 * m + 1) (SimpleGraph.cycleGraph 4) : ℝ) ≤
      ((400 * m ^ 2 + 26 * m + 1 : ℕ) : ℝ) * ((20 * m + 1 : ℕ) : ℝ) / 2 := by
  have hle : SimpleGraph.extremalNumber (400 * m ^ 2 + 26 * m + 1) (SimpleGraph.cycleGraph 4) ≤
      (400 * m ^ 2 + 26 * m + 1) * (20 * m + 1) / 2 := by
    have hcard : Fintype.card (Fin (400 * m ^ 2 + 26 * m + 1)) = 400 * m ^ 2 + 26 * m + 1 :=
      Fintype.card_fin _
    have hiff := SimpleGraph.extremalNumber_le_iff (V := Fin (400 * m ^ 2 + 26 * m + 1))
      (SimpleGraph.cycleGraph 4) ((400 * m ^ 2 + 26 * m + 1) * (20 * m + 1) / 2)
    rw [hcard] at hiff
    rw [hiff]
    intro G _ hfree
    have h2 := ma_yang_eq14 m (400 * m ^ 2 + 26 * m + 1) hm rfl hfree
    omega
  have hcast : ((SimpleGraph.extremalNumber (400 * m ^ 2 + 26 * m + 1) (SimpleGraph.cycleGraph 4) : ℕ) : ℝ) ≤
      (((400 * m ^ 2 + 26 * m + 1) * (20 * m + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hle
  have hdiv : (((400 * m ^ 2 + 26 * m + 1) * (20 * m + 1) / 2 : ℕ) : ℝ) ≤
      ((400 * m ^ 2 + 26 * m + 1 : ℕ) : ℝ) * ((20 * m + 1 : ℕ) : ℝ) / 2 := by
    have hmul : ((400 * m ^ 2 + 26 * m + 1) * (20 * m + 1) / 2) * 2 ≤
        (400 * m ^ 2 + 26 * m + 1) * (20 * m + 1) := Nat.div_mul_le_self _ 2
    have hmul_r : (((400 * m ^ 2 + 26 * m + 1) * (20 * m + 1) / 2 : ℕ) : ℝ) * 2 ≤
        ((400 * m ^ 2 + 26 * m + 1 : ℕ) : ℝ) * ((20 * m + 1 : ℕ) : ℝ) := by exact_mod_cast hmul
    linarith
  linarith

end Erdos765MY

theorem OMA.solution : type_of% @Erdos765.erdos_765.variants.second_term := by
  open Filter Real Asymptotics Erdos765MY in
  intro hO
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N0, hN0⟩ := hC
  -- Pick m large enough that n_m ≥ N0, m ≥ 10, and 29 * m^2 > (|C| + 1) * (21 * m) + 100 * m
  set m : ℕ := max (max N0 10) (2 * Nat.ceil (|C| + 1) + 100)
  have hm10 : 10 ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmN0 : N0 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hmC : 2 * (|C| + 1) + 100 ≤ (m : ℝ) := by
    have h1 : 2 * Nat.ceil (|C| + 1) + 100 ≤ m := le_max_right _ _
    have h2 : |C| + 1 ≤ (Nat.ceil (|C| + 1) : ℝ) := Nat.le_ceil _
    have h3 : 2 * (Nat.ceil (|C| + 1) : ℝ) + 100 ≤ (m : ℝ) := by exact_mod_cast h1
    linarith
  set n : ℕ := 400 * m ^ 2 + 26 * m + 1
  have hn_ge_N0 : N0 ≤ n := by
    have : m ≤ n := by
      have : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
      omega
    omega
  have hbound := hN0 n hn_ge_N0
  have hmr : (10 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm10
  have hnr : (n : ℝ) = 400 * (m : ℝ) ^ 2 + 26 * (m : ℝ) + 1 := by push_cast [n]; ring
  -- Lower bound on n^(1/2): 20*m + 13/20 - 1/(20*m) ≤ √n, simpler: 20*m + 3/5 ≤ √n ≤ 21*m
  have hsqrt_lb : 20 * (m : ℝ) + 3 / 5 ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by linarith) (by positivity)]
    rw [hnr]; nlinarith only [hmr]
  have hsqrt_ub : Real.sqrt (n : ℝ) ≤ 21 * (m : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    rw [hnr]; nlinarith only [hmr]
  have hrpow_half : (n : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt (n : ℝ) := (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hrpow_three_halves : (n : ℝ) ^ ((3 : ℝ) / 2) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  -- Lower bound on n^(3/2)/2 + n/4 - ex(n, C_4)
  have hex := extremalNumber_c4_subseq m hm10
  have hex_eq : ((400 * m ^ 2 + 26 * m + 1 : ℕ) : ℝ) * ((20 * m + 1 : ℕ) : ℝ) / 2 =
      (n : ℝ) * (20 * (m : ℝ) + 1) / 2 := by
    push_cast [n]; ring
  rw [hex_eq] at hex
  have hgap : 20 * (m : ℝ) ^ 2 ≤
      (n : ℝ) ^ ((3 : ℝ) / 2) / 2 + (n : ℝ) / 4 -
        (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ) := by
    rw [hrpow_three_halves]
    have h1 : (n : ℝ) * (20 * (m : ℝ) + 3 / 5) ≤ (n : ℝ) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt_lb (Nat.cast_nonneg n)
    have h2 : (n : ℝ) * (20 * (m : ℝ) + 3 / 5) / 2 + (n : ℝ) / 4 - (n : ℝ) * (20 * (m : ℝ) + 1) / 2 =
        (n : ℝ) / 20 := by ring
    have h3 : 20 * (m : ℝ) ^ 2 ≤ (n : ℝ) / 20 := by rw [hnr]; linarith
    linarith
  -- Upper bound from Big-O: |ex - n^(3/2)/2 - n/4| ≤ C * √n ≤ |C| * 21 * m
  have hnorm_ub : (n : ℝ) ^ ((3 : ℝ) / 2) / 2 + (n : ℝ) / 4 -
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ) ≤ |C| * (21 * (m : ℝ)) := by
    rw [hrpow_half, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs] at hbound
    have h1 : (n : ℝ) ^ ((3 : ℝ) / 2) / 2 + (n : ℝ) / 4 -
        (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ) ≤
        |(SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ) -
          (n : ℝ) ^ ((3 : ℝ) / 2) / 2 - (n : ℝ) / 4| := by
      have : -((SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ) -
          (n : ℝ) ^ ((3 : ℝ) / 2) / 2 - (n : ℝ) / 4) =
          (n : ℝ) ^ ((3 : ℝ) / 2) / 2 + (n : ℝ) / 4 -
          (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 4) : ℝ) := by ring
      rw [← this]; exact neg_le_abs _
    have h2 : C * Real.sqrt (n : ℝ) ≤ |C| * (21 * (m : ℝ)) := by
      calc C * Real.sqrt (n : ℝ) ≤ |C| * Real.sqrt (n : ℝ) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
        _ ≤ |C| * (21 * (m : ℝ)) := mul_le_mul_of_nonneg_left hsqrt_ub (abs_nonneg C)
    linarith
  -- Contradiction: 20 * m^2 ≤ |C| * 21 * m, impossible since |C| + 101 ≤ m
  nlinarith only [hgap, hnorm_ub, hmC, hmr]

