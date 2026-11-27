import OMAReductions.R_Erdos22_erdos_22_variants_bollobas_erdos_lower_R1
import Mathlib

/-!
Elementary self-contained proof of `Erdos22.erdos_22.variants.bollobas_erdos_lower.R1.H1`
via weighted twin blowup, Bollobás–Erdős graph on `A ⊕ A`, discrete `d`-dimensional
Prékopa–Leindler on `[-d, d]^d`, Chebyshev norm shell, and Fejér-kernel anti-concentration.
-/

open Filter SimpleGraph BigOperators
open scoped Classical

namespace BollobasErdosTryC

noncomputable section

/- ### Module 1: Weighted-to-unweighted finite twin blowup -/

private lemma floor_mul_ge (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b - a - b ≤ (Nat.floor a : ℝ) * (Nat.floor b : ℝ) := by
  by_cases ha1 : a ≤ 1
  · have h1 : a * b - a - b ≤ 0 := by nlinarith
    have h2 : (0 : ℝ) ≤ (Nat.floor a : ℝ) * (Nat.floor b : ℝ) := by positivity
    linarith
  · by_cases hb1 : b ≤ 1
    · have h1 : a * b - a - b ≤ 0 := by nlinarith
      have h2 : (0 : ℝ) ≤ (Nat.floor a : ℝ) * (Nat.floor b : ℝ) := by positivity
      linarith
    · push Not at ha1 hb1
      have hfa : a - 1 ≤ (Nat.floor a : ℝ) := le_of_lt (Nat.sub_one_lt_floor a)
      have hfb : b - 1 ≤ (Nat.floor b : ℝ) := le_of_lt (Nat.sub_one_lt_floor b)
      have ha' : 0 ≤ a - 1 := by linarith
      have hb' : 0 ≤ b - 1 := by linarith
      nlinarith

private lemma exists_unweighted_of_weighted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : V → ℝ)
    (η δ : ℝ) (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hδ : 0 < δ)
    (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∑ v, w v = 1)
    (hcf : G.CliqueFree 4)
    (hind : ∀ I : Finset V, G.IsIndepSet (I : Set V) → ∑ v ∈ I, w v ≤ δ / 2)
    (hedge : 1 / 4 - η / 2 ≤ ∑ u : V, ∑ v : V, if G.Adj u v then w u * w v else 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ H : SimpleGraph (Fin m),
      H.CliqueFree 4 ∧ (H.indepNum : ℝ) ≤ δ * m ∧
      (1 / 8 - η) * (m : ℝ) ^ 2 ≤ H.edgeFinset.card := by
  let Vcard : ℕ := Fintype.card V
  have hVpos : 0 < Vcard := by
    by_contra h0
    have hcard0 : Fintype.card V = 0 := Nat.eq_zero_of_not_pos h0
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp hcard0
    simp at hw1
  obtain ⟨N, hN⟩ := exists_nat_ge (4 * (Vcard : ℝ) / η + 2 * (Vcard : ℝ) + 2)
  have hN_ge_2V : 2 * (Vcard : ℝ) ≤ (N : ℝ) := by
    have : 0 ≤ 4 * (Vcard : ℝ) / η := by positivity
    linarith
  have hN_eta : 2 * (Vcard : ℝ) ≤ (η / 2) * (N : ℝ) := by
    have h1 : 4 * (Vcard : ℝ) / η ≤ (N : ℝ) := by
      have : 0 ≤ 2 * (Vcard : ℝ) + 2 := by positivity
      linarith
    have h2 : 4 * (Vcard : ℝ) ≤ (N : ℝ) * η := (div_le_iff₀ hη).mp h1
    linarith
  let c : V → ℕ := fun v => Nat.floor ((N : ℝ) * w v)
  let m : ℕ := ∑ v : V, c v
  have hc_le : ∀ v, (c v : ℝ) ≤ (N : ℝ) * w v := fun v =>
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (hw0 v))
  have hc_ge : ∀ v, (N : ℝ) * w v - 1 ≤ (c v : ℝ) := fun v =>
    le_of_lt (Nat.sub_one_lt_floor ((N : ℝ) * w v))
  have hm_le_N : (m : ℝ) ≤ (N : ℝ) := by
    have h1 : (m : ℝ) = ∑ v : V, (c v : ℝ) := by simp [m]
    rw [h1]
    calc ∑ v : V, (c v : ℝ)
        ≤ ∑ v : V, (N : ℝ) * w v := Finset.sum_le_sum (fun v _ => hc_le v)
      _ = (N : ℝ) * ∑ v : V, w v := by rw [← Finset.mul_sum]
      _ = (N : ℝ) := by rw [hw1, mul_one]
  have hm_ge : (N : ℝ) - (Vcard : ℝ) ≤ (m : ℝ) := by
    have h1 : (m : ℝ) = ∑ v : V, (c v : ℝ) := by simp [m]
    rw [h1]
    calc (N : ℝ) - (Vcard : ℝ)
        = (N : ℝ) * (∑ v : V, w v) - ∑ _v : V, (1 : ℝ) := by
          simp [hw1, Vcard]
      _ = ∑ v : V, ((N : ℝ) * w v - 1) := by
          rw [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ ∑ v : V, (c v : ℝ) := Finset.sum_le_sum (fun v _ => hc_ge v)
  have hm_ge_half : (N : ℝ) / 2 ≤ (m : ℝ) := by linarith
  have hm_pos : 0 < m := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (0 : ℝ) < (Vcard : ℝ) := Nat.cast_pos.mpr hVpos
      linarith
    have hmposR : (0 : ℝ) < (m : ℝ) := by linarith
    exact Nat.cast_pos.mp hmposR
  let W := Σ v : V, Fin (c v)
  have hWcard : Fintype.card W = m := by
    simp [W, m, Fintype.card_sigma, Fintype.card_fin]
  let HW : SimpleGraph W := G.comap Sigma.fst
  let e : W ≃ Fin m := Fintype.equivFinOfCardEq hWcard
  let H : SimpleGraph (Fin m) := HW.comap e.symm
  let iso : HW ≃g H :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        simp [H] }
  refine ⟨m, hm_pos, H, ?_, ?_, ?_⟩
  · -- K_4-free
    intro s hs
    let t : Finset W := s.map e.symm.toEmbedding
    have ht_card : t.card = 4 := by
      simpa [t] using hs.card_eq
    have ht_cliq : HW.IsClique (t : Set W) := by
      intro a ha b hb hab
      simp only [t, Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk,
        Finset.mem_coe] at ha hb
      rcases ha with ⟨x, hx, rfl⟩
      rcases hb with ⟨y, hy, rfl⟩
      have hxy : x ≠ y := fun h => hab (by rw [h])
      exact hs.1 hx hy hxy
    have hinj : Set.InjOn Sigma.fst (t : Set W) := by
      intro a ha b hb hfst
      by_contra hne
      have hadj : G.Adj a.1 b.1 := ht_cliq ha hb hne
      exact G.ne_of_adj hadj hfst
    let u : Finset V := t.image Sigma.fst
    have hu_card : u.card = 4 := by
      rw [Finset.card_image_of_injOn hinj, ht_card]
    have hu_cliq : G.IsClique (u : Set V) := by
      intro x hx y hy hxy
      simp only [u, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun h => hxy (congrArg Sigma.fst h)
      exact ht_cliq ha hb hab
    exact hcf u ⟨hu_cliq, hu_card⟩
  · -- indepNum ≤ δ * m
    obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
    let t : Finset W := s.map e.symm.toEmbedding
    have ht_card : t.card = H.indepNum := by
      simpa [t] using hs.card_eq
    have ht_ind : HW.IsIndepSet (t : Set W) := by
      intro a ha b hb hab
      simp only [t, Finset.coe_map, Set.mem_image, Function.Embedding.coeFn_mk,
        Finset.mem_coe] at ha hb
      rcases ha with ⟨x, hx, rfl⟩
      rcases hb with ⟨y, hy, rfl⟩
      have hxy : x ≠ y := fun h => hab (by rw [h])
      exact hs.1 hx hy hxy
    let I : Finset V := t.image Sigma.fst
    have hI_ind : G.IsIndepSet (I : Set V) := by
      intro x hx y hy hxy
      simp only [I, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      rcases hx with ⟨a, ha, rfl⟩
      rcases hy with ⟨b, hb, rfl⟩
      have hab : a ≠ b := fun h => hxy (congrArg Sigma.fst h)
      exact ht_ind ha hb hab
    have ht_sub : t ⊆ I.sigma (fun v => (Finset.univ : Finset (Fin (c v)))) := by
      intro a ha
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_image_of_mem Sigma.fst ha, Finset.mem_univ a.2⟩
    have ht_le : t.card ≤ ∑ v ∈ I, c v := by
      calc t.card
          ≤ (I.sigma (fun v => (Finset.univ : Finset (Fin (c v))))).card :=
            Finset.card_le_card ht_sub
        _ = ∑ v ∈ I, c v := by simp [Finset.card_sigma]
    have hcardR : (H.indepNum : ℝ) ≤ ∑ v ∈ I, (c v : ℝ) := by
      rw [← ht_card]
      exact_mod_cast ht_le
    have hsum_w : ∑ v ∈ I, w v ≤ δ / 2 := hind I hI_ind
    calc (H.indepNum : ℝ)
        ≤ ∑ v ∈ I, (c v : ℝ) := hcardR
      _ ≤ ∑ v ∈ I, (N : ℝ) * w v := Finset.sum_le_sum (fun v _ => hc_le v)
      _ = (N : ℝ) * ∑ v ∈ I, w v := by rw [← Finset.mul_sum]
      _ ≤ (N : ℝ) * (δ / 2) := mul_le_mul_of_nonneg_left hsum_w (Nat.cast_nonneg N)
      _ = δ * ((N : ℝ) / 2) := by ring
      _ ≤ δ * (m : ℝ) := mul_le_mul_of_nonneg_left hm_ge_half hδ.le
  · -- edge count ≥ (1/8 - η) * m^2
    let Ecard : ℕ := H.edgeFinset.card
    change (1 / 8 - η) * (m : ℝ) ^ 2 ≤ (Ecard : ℝ)
    have hedge_eq : HW.edgeFinset.card = Ecard := by
      convert SimpleGraph.Iso.card_edgeFinset_eq iso
    have htwice : 2 * HW.edgeFinset.card =
        ∑ u : V, ∑ v : V, if G.Adj u v then c u * c v else 0 := by
      rw [← HW.sum_degrees_eq_twice_card_edges]
      have hdeg : ∀ a : W, HW.degree a = ∑ b : W, if G.Adj a.1 b.1 then 1 else 0 := by
        intro a
        rw [← HW.card_neighborFinset_eq_degree]
        rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
        congr 1
        ext b
        simp [HW, SimpleGraph.mem_neighborFinset]
      simp_rw [hdeg]
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hinner :
          (∑ b : W, if G.Adj u b.1 then (1 : ℕ) else 0) =
            ∑ v : V, if G.Adj u v then c v else 0 := by
        rw [Fintype.sum_sigma]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases h : G.Adj u v <;> simp [h]
      trans ∑ _ : Fin (c u), (∑ v : V, if G.Adj u v then c v else 0)
      · refine Finset.sum_congr rfl fun _ _ => hinner
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases h : G.Adj u v <;> simp [h]
    have htwiceR : 2 * (Ecard : ℝ) =
        ∑ u : V, ∑ v : V, if G.Adj u v then (c u : ℝ) * (c v : ℝ) else 0 := by
      rw [← hedge_eq]
      have hcastR : ((2 * HW.edgeFinset.card : ℕ) : ℝ) =
          ((∑ u : V, ∑ v : V, if G.Adj u v then c u * c v else 0 : ℕ) : ℝ) :=
        congrArg Nat.cast htwice
      have hL : ((2 * HW.edgeFinset.card : ℕ) : ℝ) = 2 * (HW.edgeFinset.card : ℝ) := by
        push_cast; rfl
      have hR : ((∑ u : V, ∑ v : V, if G.Adj u v then c u * c v else 0 : ℕ) : ℝ) =
          ∑ u : V, ∑ v : V, if G.Adj u v then (c u : ℝ) * (c v : ℝ) else 0 := by
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Nat.cast_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases h : G.Adj u v <;> simp [h]
      linarith
    have hpt : ∀ u v : V,
        (if G.Adj u v then ((N : ℝ) * w u) * ((N : ℝ) * w v) else 0) -
          (N : ℝ) * w u - (N : ℝ) * w v ≤
        (if G.Adj u v then (c u : ℝ) * (c v : ℝ) else 0) := by
      intro u v
      by_cases h : G.Adj u v
      · simp only [h, ↓reduceIte]
        exact floor_mul_ge ((N : ℝ) * w u) ((N : ℝ) * w v)
          (mul_nonneg (Nat.cast_nonneg N) (hw0 u))
          (mul_nonneg (Nat.cast_nonneg N) (hw0 v))
      · simp only [h, ↓reduceIte]
        have h1 : 0 ≤ (N : ℝ) * w u := mul_nonneg (Nat.cast_nonneg N) (hw0 u)
        have h2 : 0 ≤ (N : ℝ) * w v := mul_nonneg (Nat.cast_nonneg N) (hw0 v)
        linarith
    have hsum_lower :
        (N : ℝ) ^ 2 * (∑ u : V, ∑ v : V, if G.Adj u v then w u * w v else 0) -
          2 * (Vcard : ℝ) * (N : ℝ) ≤
        2 * (Ecard : ℝ) := by
      rw [htwiceR]
      have h1 : ∑ u : V, ∑ v : V,
          ((if G.Adj u v then ((N : ℝ) * w u) * ((N : ℝ) * w v) else 0) -
            (N : ℝ) * w u - (N : ℝ) * w v) ≤
          ∑ u : V, ∑ v : V, if G.Adj u v then (c u : ℝ) * (c v : ℝ) else 0 :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hpt u v
      have h2 : ∑ u : V, ∑ v : V,
          ((if G.Adj u v then ((N : ℝ) * w u) * ((N : ℝ) * w v) else 0) -
            (N : ℝ) * w u - (N : ℝ) * w v) =
          (N : ℝ) ^ 2 * (∑ u : V, ∑ v : V, if G.Adj u v then w u * w v else 0) -
            2 * (Vcard : ℝ) * (N : ℝ) := by
        simp_rw [Finset.sum_sub_distrib]
        have hA : ∑ u : V, ∑ v : V,
            (if G.Adj u v then ((N : ℝ) * w u) * ((N : ℝ) * w v) else 0) =
            (N : ℝ) ^ 2 * (∑ u : V, ∑ v : V, if G.Adj u v then w u * w v else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          by_cases h : G.Adj u v <;> simp [h] <;> ring
        have hB : ∑ u : V, ∑ _v : V, (N : ℝ) * w u = (Vcard : ℝ) * (N : ℝ) := by
          simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.mul_sum, ← Finset.mul_sum, hw1, mul_one]
        have hC : ∑ _u : V, ∑ v : V, (N : ℝ) * w v = (Vcard : ℝ) * (N : ℝ) := by
          have hin : ∑ v : V, (N : ℝ) * w v = (N : ℝ) := by rw [← Finset.mul_sum, hw1, mul_one]
          simp [hin, Vcard]
        rw [hA, hB, hC]
        ring
      linarith
    have hmain : (1 / 4 - η) * (N : ℝ) ^ 2 ≤ 2 * (Ecard : ℝ) := by
      have h3 : (N : ℝ) ^ 2 * (1 / 4 - η / 2) ≤
          (N : ℝ) ^ 2 * (∑ u : V, ∑ v : V, if G.Adj u v then w u * w v else 0) :=
        mul_le_mul_of_nonneg_left hedge (sq_nonneg (N : ℝ))
      have h4 : 2 * (Vcard : ℝ) * (N : ℝ) ≤ (η / 2) * (N : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hN_eta (Nat.cast_nonneg N)
        linarith
      linarith
    have hmsq : (m : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hcoeff : 0 ≤ 1 / 4 - η := by linarith
    have h5 : (1 / 4 - η) * (m : ℝ) ^ 2 ≤ (1 / 4 - η) * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hmsq hcoeff
    have h6 : (1 / 8 - η) * (m : ℝ) ^ 2 ≤ (1 / 8 - η / 2) * (m : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg (m : ℝ))
    have h7 : 2 * ((1 / 8 - η / 2) * (m : ℝ) ^ 2) = (1 / 4 - η) * (m : ℝ) ^ 2 := by ring
    linarith

/- ### Module 2: Algebraic Bollobás–Erdős weighted graph on `A ⊕ A` -/

private def ip {d : ℕ} (x y : Fin d → ℤ) : ℝ :=
  ∑ r : Fin d, (x r : ℝ) * (y r : ℝ)

private def normSq {d : ℕ} (x : Fin d → ℤ) : ℝ :=
  ∑ r : Fin d, (x r : ℝ) ^ 2

private lemma normSq_eq_ip {d : ℕ} (x : Fin d → ℤ) : normSq x = ip x x := by
  simp only [normSq, ip, sq]

private lemma normSq_nonneg {d : ℕ} (x : Fin d → ℤ) : 0 ≤ normSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma normSq_neg {d : ℕ} (x : Fin d → ℤ) : normSq (-x) = normSq x := by
  simp [normSq]

private lemma ip_comm {d : ℕ} (x y : Fin d → ℤ) : ip x y = ip y x := by
  simp only [ip]
  refine Finset.sum_congr rfl fun r _ => mul_comm _ _

private lemma ip_neg_right {d : ℕ} (x y : Fin d → ℤ) : ip x (-y) = -ip x y := by
  simp only [ip, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

private lemma ip_add_left {d : ℕ} (x₁ x₂ y : Fin d → ℤ) :
    ip (x₁ + x₂) y = ip x₁ y + ip x₂ y := by
  simp only [ip, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

private lemma ip_add_right {d : ℕ} (x y₁ y₂ : Fin d → ℤ) :
    ip x (y₁ + y₂) = ip x y₁ + ip x y₂ := by
  simp only [ip, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

private lemma ip_sq_le_normSq_mul {d : ℕ} (x y : Fin d → ℤ) :
    (ip x y) ^ 2 ≤ normSq x * normSq y := by
  simpa [ip, normSq] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun r : Fin d => (x r : ℝ))
      (fun r : Fin d => (y r : ℝ)))

private lemma normSq_triangle_bound {d : ℕ} (x y z : Fin d → ℤ) (C : ℝ)
    (hxy : normSq (x + y) ≤ 4 * C ^ 2)
    (hyz : normSq (y + z) ≤ 4 * C ^ 2)
    (hzx : normSq (z + x) ≤ 4 * C ^ 2) :
    normSq x ≤ 9 * C ^ 2 := by
  have hcoord : ∀ r : Fin d,
      4 * (x r : ℝ) ^ 2 ≤
        3 * ((x r + y r : ℝ) ^ 2 + (y r + z r : ℝ) ^ 2 + (z r + x r : ℝ) ^ 2) := by
    intro r
    nlinarith [sq_nonneg ((x r : ℝ) - (z r : ℝ)),
               sq_nonneg ((x r : ℝ) + (y r : ℝ) + (y r : ℝ) + (z r : ℝ)),
               sq_nonneg ((x r : ℝ) - (y r : ℝ)),
               sq_nonneg ((y r : ℝ) + (z r : ℝ) + (z r : ℝ) + (x r : ℝ)),
               sq_nonneg (2 * (y r : ℝ) + (x r : ℝ) + (z r : ℝ))]
  have hsum : 4 * normSq x ≤ 3 * (normSq (x + y) + normSq (y + z) + normSq (z + x)) := by
    simp only [normSq, Pi.add_apply, Int.cast_add, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun r _ => hcoord r
  linarith

private lemma bollobas_erdos_weighted
    {d : ℕ} (A : Finset (Fin d → ℤ)) (w : (Fin d → ℤ) → ℝ)
    (C E η δ : ℝ)
    (_hC : 0 ≤ C) (hE : 0 < E) (hCE : C ^ 2 ≤ E)
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hδ : 0 < δ)
    (hw0 : ∀ x ∈ A, 0 ≤ w x)
    (hw1 : ∑ x ∈ A, w x = 1)
    (hnorm : ∀ x ∈ A, 9 * C ^ 2 < normSq x)
    (hind : ∀ I ⊆ A, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → 4 * C ^ 2 < normSq (x + y)) →
      ∑ x ∈ I, w x ≤ δ / 2)
    (hcross : 1 / 2 - η ≤ ∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ H : SimpleGraph (Fin m),
      H.CliqueFree 4 ∧ (H.indepNum : ℝ) ≤ δ * m ∧
      (1 / 8 - η) * (m : ℝ) ^ 2 ≤ H.edgeFinset.card := by
  let V := {x // x ∈ A} ⊕ {x // x ∈ A}
  let G : SimpleGraph V :=
    { Adj := fun u v =>
        match u, v with
        | Sum.inl x, Sum.inl y => x ≠ y ∧ normSq (x.1 + y.1) ≤ 4 * C ^ 2
        | Sum.inr x, Sum.inr y => x ≠ y ∧ normSq (x.1 + y.1) ≤ 4 * C ^ 2
        | Sum.inl x, Sum.inr y => E < ip x.1 y.1
        | Sum.inr x, Sum.inl y => E < ip y.1 x.1
      symm := ⟨by
        intro u v h
        cases u <;> cases v
        · dsimp at h ⊢; exact ⟨Ne.symm h.1, by rw [add_comm]; exact h.2⟩
        · exact h
        · exact h
        · dsimp at h ⊢; exact ⟨Ne.symm h.1, by rw [add_comm]; exact h.2⟩⟩
      loopless := ⟨by
        intro u h
        cases u with
        | inl x => exact h.1 rfl
        | inr x => exact h.1 rfl⟩ }
  let wG : V → ℝ := fun u =>
    match u with
    | Sum.inl x => w x.1 / 2
    | Sum.inr x => w x.1 / 2
  have hwG0 : ∀ u : V, 0 ≤ wG u := by
    intro u
    cases u with
    | inl x => exact div_nonneg (hw0 x.1 x.2) (by norm_num)
    | inr x => exact div_nonneg (hw0 x.1 x.2) (by norm_num)
  have hsum_sub : ∑ x : {x // x ∈ A}, w x.1 = 1 := by
    rw [Finset.univ_eq_attach, Finset.sum_attach A w, hw1]
  have hwG1 : ∑ u : V, wG u = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [wG, ← Finset.sum_div, hsum_sub]
    norm_num
  have hno_tri_A : ∀ x y z : {x // x ∈ A},
      normSq (x.1 + y.1) ≤ 4 * C ^ 2 →
      normSq (y.1 + z.1) ≤ 4 * C ^ 2 →
      normSq (z.1 + x.1) ≤ 4 * C ^ 2 → False := by
    intro x y z h1 h2 h3
    have hb := normSq_triangle_bound x.1 y.1 z.1 C h1 h2 h3
    linarith [hnorm x.1 x.2]
  have hcf : G.CliqueFree 4 := by
    intro s hs
    let sL := s.filter (fun u : V => u.isLeft)
    let sR := s.filter (fun u : V => ¬ u.isLeft)
    have hsplit : sL.card + sR.card = 4 := by
      have h1 : sL.card + sR.card = s.card := by
        simp only [sL, sR, Finset.card_eq_sum_ones]
        exact Finset.sum_filter_add_sum_filter_not s (fun u : V => u.isLeft) (fun _ => 1)
      rw [h1, hs.card_eq]
    by_cases hL3 : 3 ≤ sL.card
    · obtain ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, h12, h13, h23⟩ :=
        Finset.two_lt_card_iff.mp (by omega : 2 < sL.card)
      have hu₁s : u₁ ∈ s := (Finset.mem_filter.mp hu₁).1
      have hu₂s : u₂ ∈ s := (Finset.mem_filter.mp hu₂).1
      have hu₃s : u₃ ∈ s := (Finset.mem_filter.mp hu₃).1
      have hu₁L : u₁.isLeft := (Finset.mem_filter.mp hu₁).2
      have hu₂L : u₂.isLeft := (Finset.mem_filter.mp hu₂).2
      have hu₃L : u₃.isLeft := (Finset.mem_filter.mp hu₃).2
      cases u₁ with
      | inr _ => simp at hu₁L
      | inl x =>
        cases u₂ with
        | inr _ => simp at hu₂L
        | inl y =>
          cases u₃ with
          | inr _ => simp at hu₃L
          | inl z =>
            have hxy := (hs.1 hu₁s hu₂s h12).2
            have hyz := (hs.1 hu₂s hu₃s h23).2
            have hzx := (hs.1 hu₃s hu₁s h13.symm).2
            exact hno_tri_A x y z hxy hyz hzx
    · by_cases hR3 : 3 ≤ sR.card
      · obtain ⟨u₁, u₂, u₃, hu₁, hu₂, hu₃, h12, h13, h23⟩ :=
          Finset.two_lt_card_iff.mp (by omega : 2 < sR.card)
        have hu₁s : u₁ ∈ s := (Finset.mem_filter.mp hu₁).1
        have hu₂s : u₂ ∈ s := (Finset.mem_filter.mp hu₂).1
        have hu₃s : u₃ ∈ s := (Finset.mem_filter.mp hu₃).1
        have hu₁R : ¬ u₁.isLeft := (Finset.mem_filter.mp hu₁).2
        have hu₂R : ¬ u₂.isLeft := (Finset.mem_filter.mp hu₂).2
        have hu₃R : ¬ u₃.isLeft := (Finset.mem_filter.mp hu₃).2
        cases u₁ with
        | inl _ => simp at hu₁R
        | inr x =>
          cases u₂ with
          | inl _ => simp at hu₂R
          | inr y =>
            cases u₃ with
            | inl _ => simp at hu₃R
            | inr z =>
              have hxy := (hs.1 hu₁s hu₂s h12).2
              have hyz := (hs.1 hu₂s hu₃s h23).2
              have hzx := (hs.1 hu₃s hu₁s h13.symm).2
              exact hno_tri_A x y z hxy hyz hzx
      · have hL2 : 1 < sL.card := by omega
        have hR2 : 1 < sR.card := by omega
        obtain ⟨u₁, hu₁, u₂, hu₂, hu12⟩ := Finset.one_lt_card.mp hL2
        obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := Finset.one_lt_card.mp hR2
        have hu₁s : u₁ ∈ s := (Finset.mem_filter.mp hu₁).1
        have hu₂s : u₂ ∈ s := (Finset.mem_filter.mp hu₂).1
        have hv₁s : v₁ ∈ s := (Finset.mem_filter.mp hv₁).1
        have hv₂s : v₂ ∈ s := (Finset.mem_filter.mp hv₂).1
        have hu₁L : u₁.isLeft := (Finset.mem_filter.mp hu₁).2
        have hu₂L : u₂.isLeft := (Finset.mem_filter.mp hu₂).2
        have hv₁R : ¬ v₁.isLeft := (Finset.mem_filter.mp hv₁).2
        have hv₂R : ¬ v₂.isLeft := (Finset.mem_filter.mp hv₂).2
        cases u₁ with
        | inr _ => simp at hu₁L
        | inl a₁ =>
          cases u₂ with
          | inr _ => simp at hu₂L
          | inl a₂ =>
            cases v₁ with
            | inl _ => simp at hv₁R
            | inr b₁ =>
              cases v₂ with
              | inl _ => simp at hv₂R
              | inr b₂ =>
                have ha : normSq (a₁.1 + a₂.1) ≤ 4 * C ^ 2 := (hs.1 hu₁s hu₂s hu12).2
                have hb : normSq (b₁.1 + b₂.1) ≤ 4 * C ^ 2 := (hs.1 hv₁s hv₂s hv12).2
                have h11 : E < ip a₁.1 b₁.1 := hs.1 hu₁s hv₁s (by simp)
                have h12 : E < ip a₁.1 b₂.1 := hs.1 hu₁s hv₂s (by simp)
                have h21 : E < ip a₂.1 b₁.1 := hs.1 hu₂s hv₁s (by simp)
                have h22 : E < ip a₂.1 b₂.1 := hs.1 hu₂s hv₂s (by simp)
                have hsum4 : 4 * E < ip (a₁.1 + a₂.1) (b₁.1 + b₂.1) := by
                  rw [ip_add_left, ip_add_right, ip_add_right]
                  linarith
                have hcs := ip_sq_le_normSq_mul (a₁.1 + a₂.1) (b₁.1 + b₂.1)
                have hsq_lt : (4 * E) ^ 2 < (ip (a₁.1 + a₂.1) (b₁.1 + b₂.1)) ^ 2 := by
                  nlinarith
                have hmul_le : normSq (a₁.1 + a₂.1) * normSq (b₁.1 + b₂.1) ≤
                    (4 * C ^ 2) * (4 * C ^ 2) :=
                  mul_le_mul ha hb (normSq_nonneg _) (by positivity)
                have hC4 : (4 * C ^ 2) * (4 * C ^ 2) ≤ (4 * E) ^ 2 := by
                  nlinarith [sq_nonneg C]
                linarith
  have hindG : ∀ J : Finset V, G.IsIndepSet (J : Set V) → ∑ u ∈ J, wG u ≤ δ / 2 := by
    intro J hJ
    let JL : Finset (Fin d → ℤ) := A.filter (fun x => ∃ hx : x ∈ A, Sum.inl ⟨x, hx⟩ ∈ J)
    let JR : Finset (Fin d → ℤ) := A.filter (fun x => ∃ hx : x ∈ A, Sum.inr ⟨x, hx⟩ ∈ J)
    have hJL_sub : JL ⊆ A := Finset.filter_subset _ A
    have hJR_sub : JR ⊆ A := Finset.filter_subset _ A
    have hJL_ind : ∀ x ∈ JL, ∀ y ∈ JL, x ≠ y → 4 * C ^ 2 < normSq (x + y) := by
      intro x hx y hy hxy
      obtain ⟨hxA, hxin⟩ := (Finset.mem_filter.mp hx).2
      obtain ⟨hyA, hyin⟩ := (Finset.mem_filter.mp hy).2
      have hne : (Sum.inl ⟨x, hxA⟩ : V) ≠ Sum.inl ⟨y, hyA⟩ := by
        intro h
        exact hxy (congrArg Subtype.val (Sum.inl.inj h))
      have hna := hJ hxin hyin hne
      have hne' : (⟨x, hxA⟩ : {x // x ∈ A}) ≠ ⟨y, hyA⟩ := fun h =>
        hxy (congrArg Subtype.val h)
      by_contra hle
      push Not at hle
      exact hna ⟨hne', hle⟩
    have hJR_ind : ∀ x ∈ JR, ∀ y ∈ JR, x ≠ y → 4 * C ^ 2 < normSq (x + y) := by
      intro x hx y hy hxy
      obtain ⟨hxA, hxin⟩ := (Finset.mem_filter.mp hx).2
      obtain ⟨hyA, hyin⟩ := (Finset.mem_filter.mp hy).2
      have hne : (Sum.inr ⟨x, hxA⟩ : V) ≠ Sum.inr ⟨y, hyA⟩ := by
        intro h
        exact hxy (congrArg Subtype.val (Sum.inr.inj h))
      have hna := hJ hxin hyin hne
      have hne' : (⟨x, hxA⟩ : {x // x ∈ A}) ≠ ⟨y, hyA⟩ := fun h =>
        hxy (congrArg Subtype.val h)
      by_contra hle
      push Not at hle
      exact hna ⟨hne', hle⟩
    have hsumJ : ∑ u ∈ J, wG u = (∑ x ∈ JL, w x) / 2 + (∑ x ∈ JR, w x) / 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not J (fun u : V => u.isLeft)]
      congr 1
      · rw [Finset.sum_div]
        refine Finset.sum_bij (fun u hu => match u with | Sum.inl x => x.1 | Sum.inr x => x.1)
          ?_ ?_ ?_ ?_
        · intro u hu
          have huJ := (Finset.mem_filter.mp hu).1
          have huL := (Finset.mem_filter.mp hu).2
          cases u with
          | inr _ => simp at huL
          | inl x =>
            rw [Finset.mem_filter]
            exact ⟨x.2, x.2, huJ⟩
        · intro u₁ hu₁ u₂ hu₂ heq
          have hu₁L := (Finset.mem_filter.mp hu₁).2
          have hu₂L := (Finset.mem_filter.mp hu₂).2
          cases u₁ with
          | inr _ => simp at hu₁L
          | inl x₁ =>
            cases u₂ with
            | inr _ => simp at hu₂L
            | inl x₂ =>
              exact congrArg Sum.inl (Subtype.ext heq)
        · intro x hx
          obtain ⟨hxA, hxin⟩ := (Finset.mem_filter.mp hx).2
          exact ⟨Sum.inl ⟨x, hxA⟩, Finset.mem_filter.mpr ⟨hxin, by simp⟩, rfl⟩
        · intro u hu
          have huL := (Finset.mem_filter.mp hu).2
          cases u with
          | inr _ => simp at huL
          | inl x => rfl
      · rw [Finset.sum_div]
        refine Finset.sum_bij (fun u hu => match u with | Sum.inl x => x.1 | Sum.inr x => x.1)
          ?_ ?_ ?_ ?_
        · intro u hu
          have huJ := (Finset.mem_filter.mp hu).1
          have huR := (Finset.mem_filter.mp hu).2
          cases u with
          | inl _ => simp at huR
          | inr x =>
            rw [Finset.mem_filter]
            exact ⟨x.2, x.2, huJ⟩
        · intro u₁ hu₁ u₂ hu₂ heq
          have hu₁R := (Finset.mem_filter.mp hu₁).2
          have hu₂R := (Finset.mem_filter.mp hu₂).2
          cases u₁ with
          | inl _ => simp at hu₁R
          | inr x₁ =>
            cases u₂ with
            | inl _ => simp at hu₂R
            | inr x₂ =>
              exact congrArg Sum.inr (Subtype.ext heq)
        · intro x hx
          obtain ⟨hxA, hxin⟩ := (Finset.mem_filter.mp hx).2
          exact ⟨Sum.inr ⟨x, hxA⟩, Finset.mem_filter.mpr ⟨hxin, by simp⟩, rfl⟩
        · intro u hu
          have huR := (Finset.mem_filter.mp hu).2
          cases u with
          | inl _ => simp at huR
          | inr x => rfl
    rw [hsumJ]
    linarith [hind JL hJL_sub hJL_ind, hind JR hJR_sub hJR_ind]
  have hedgeG : 1 / 4 - η / 2 ≤ ∑ u : V, ∑ v : V, if G.Adj u v then wG u * wG v else 0 := by
    rw [Fintype.sum_sum_type]
    have hL : (∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A}, if E < ip x.1 y.1 then w x.1 * w y.1 else 0) / 4 ≤
        ∑ x : {x // x ∈ A}, ∑ v : V, if G.Adj (Sum.inl x) v then wG (Sum.inl x) * wG v else 0 := by
      have hsplit : ∑ x : {x // x ∈ A}, ∑ v : V,
            (if G.Adj (Sum.inl x) v then wG (Sum.inl x) * wG v else 0) =
          (∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
            if G.Adj (Sum.inl x) (Sum.inl y) then wG (Sum.inl x) * wG (Sum.inl y) else 0) +
          (∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
            if G.Adj (Sum.inl x) (Sum.inr y) then wG (Sum.inl x) * wG (Sum.inr y) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_sum_type]
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> rfl
      rw [hsplit]
      have hnn : 0 ≤ ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
          if G.Adj (Sum.inl x) (Sum.inl y) then wG (Sum.inl x) * wG (Sum.inl y) else 0 :=
        Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
          split_ifs
          · exact mul_nonneg (hwG0 (Sum.inl x)) (hwG0 (Sum.inl y))
          · exact le_rfl
      have hcr : ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
          (if G.Adj (Sum.inl x) (Sum.inr y) then wG (Sum.inl x) * wG (Sum.inr y) else 0) =
          (∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A}, if E < ip x.1 y.1 then w x.1 * w y.1 else 0) / 4 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h : E < ip x.1 y.1
        · simp [G, wG, h]; ring
        · simp [G, h]
      rw [hcr]
      linarith
    have hR : (∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A}, if E < ip x.1 y.1 then w x.1 * w y.1 else 0) / 4 ≤
        ∑ x : {x // x ∈ A}, ∑ v : V, if G.Adj (Sum.inr x) v then wG (Sum.inr x) * wG v else 0 := by
      have hsplit : ∑ x : {x // x ∈ A}, ∑ v : V,
            (if G.Adj (Sum.inr x) v then wG (Sum.inr x) * wG v else 0) =
          (∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
            if G.Adj (Sum.inr x) (Sum.inl y) then wG (Sum.inr x) * wG (Sum.inl y) else 0) +
          (∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
            if G.Adj (Sum.inr x) (Sum.inr y) then wG (Sum.inr x) * wG (Sum.inr y) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_sum_type]
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> rfl
      rw [hsplit]
      have hnn : 0 ≤ ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
          if G.Adj (Sum.inr x) (Sum.inr y) then wG (Sum.inr x) * wG (Sum.inr y) else 0 :=
        Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
          split_ifs
          · exact mul_nonneg (hwG0 (Sum.inr x)) (hwG0 (Sum.inr y))
          · exact le_rfl
      have hcr : ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A},
          (if G.Adj (Sum.inr x) (Sum.inl y) then wG (Sum.inr x) * wG (Sum.inl y) else 0) =
          (∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A}, if E < ip x.1 y.1 then w x.1 * w y.1 else 0) / 4 := by
        rw [Finset.sum_comm, Finset.sum_div]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h : E < ip y.1 x.1
        · simp [G, wG, h]; ring
        · simp [G, h]
      rw [hcr]
      linarith
    have hcross_sub :
        ∑ x : {x // x ∈ A}, ∑ y : {x // x ∈ A}, (if E < ip x.1 y.1 then w x.1 * w y.1 else 0) =
        ∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0 := by
      simp_rw [Finset.univ_eq_attach]
      rw [Finset.sum_attach A (fun x => ∑ y ∈ A.attach, if E < ip x y.1 then w x * w y.1 else 0)]
      refine Finset.sum_congr rfl fun x _ => ?_
      exact Finset.sum_attach A (fun y => if E < ip x y then w x * w y else 0)
    linarith
  exact exists_unweighted_of_weighted G wG η δ hη hη4 hδ hwG0 hwG1 hcf hindG hedgeG

/- ### Module 3A: Elementary 1D and d-D Discrete Prékopa–Leindler on `[-M, M]^d` -/

private def segLen (p q : ℝ) (k : ℤ) : ℝ :=
  min q (max p ((k : ℝ) + 1)) - min q (max p (k : ℝ))

private lemma segLen_nonneg (p q : ℝ) (k : ℤ) : 0 ≤ segLen p q k := by
  unfold segLen
  have h1 : max p (k : ℝ) ≤ max p ((k : ℝ) + 1) := max_le_max_left p (by linarith)
  linarith [min_le_min_left q h1]

private lemma clamp_add (p r q t : ℝ) (hpr : p ≤ r) (hrq : r ≤ q) :
    min q (max p t) = min r (max p t) + min q (max r t) - r := by
  by_cases ht1 : t ≤ p
  · rw [max_eq_left ht1, max_eq_left (ht1.trans hpr), min_eq_right (hpr.trans hrq),
        min_eq_right hpr, min_eq_right hrq]
    ring
  · push Not at ht1
    by_cases ht2 : t ≤ r
    · rw [max_eq_right ht1.le, max_eq_left ht2, min_eq_right (ht2.trans hrq),
          min_eq_right ht2, min_eq_right hrq]
      ring
    · push Not at ht2
      by_cases ht3 : t ≤ q
      · rw [max_eq_right ht1.le, max_eq_right ht2.le, min_eq_right ht3, min_eq_left ht2.le]
        ring
      · push Not at ht3
        rw [max_eq_right ht1.le, max_eq_right ht2.le, min_eq_left ht3.le, min_eq_left ht2.le]
        ring

private lemma segLen_add (p r q : ℝ) (hpr : p ≤ r) (hrq : r ≤ q) (k : ℤ) :
    segLen p r k + segLen r q k = segLen p q k := by
  unfold segLen
  have h1 := clamp_add p r q ((k : ℝ) + 1) hpr hrq
  have h2 := clamp_add p r q (k : ℝ) hpr hrq
  linarith

private lemma segLen_le_one (p q : ℝ) (_hpq : p ≤ q) (k : ℤ) : segLen p q k ≤ 1 := by
  unfold segLen
  have h1 : min q (max p ((k : ℝ) + 1)) ≤ min q (max p (k : ℝ) + 1) := by
    apply min_le_min_left
    exact max_le (by linarith [le_max_left p (k : ℝ)]) (by linarith [le_max_right p (k : ℝ)])
  have h2 : min q (max p (k : ℝ) + 1) ≤ min q (max p (k : ℝ)) + 1 := by
    rcases le_total q (max p (k : ℝ)) with h | h
    · rw [min_eq_left (by linarith : q ≤ max p (k : ℝ) + 1), min_eq_left h]
      linarith
    · rw [min_eq_right h]
      exact min_le_right _ _
  linarith

private lemma segLen_pos_imp {p q : ℝ} {k : ℤ} (h : 0 < segLen p q k) :
    p < (k : ℝ) + 1 ∧ (k : ℝ) < q := by
  unfold segLen at h
  constructor
  · by_contra hle
    push Not at hle
    have h1 : max p ((k : ℝ) + 1) = p := max_eq_left hle
    have h2 : max p (k : ℝ) = p := max_eq_left (by linarith)
    rw [h1, h2] at h
    linarith
  · by_contra hle
    push Not at hle
    have h1 : min q (max p (k : ℝ)) = q := min_eq_left (hle.trans (le_max_right p (k : ℝ)))
    have h2 : min q (max p ((k : ℝ) + 1)) = q :=
      min_eq_left (by linarith [le_max_right p ((k : ℝ) + 1)])
    rw [h1, h2] at h
    linarith

private lemma sum_Icc_segLen (p q : ℝ) (a b : ℤ) (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, segLen p q k =
      min q (max p ((b : ℝ) + 1)) - min q (max p (a : ℝ)) := by
  obtain ⟨n, hn⟩ := Int.exists_add_of_le hab
  subst hn
  induction n with
  | zero =>
    simp [segLen]
  | succ n ih =>
    have hle : a ≤ a + (n : ℤ) := by omega
    have hIcc : Finset.Icc a (a + ((n + 1 : ℕ) : ℤ)) =
        insert (a + ((n + 1 : ℕ) : ℤ)) (Finset.Icc a (a + (n : ℤ))) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : a + ((n + 1 : ℕ) : ℤ) ∉ Finset.Icc a (a + (n : ℤ)) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnot, ih hle]
    unfold segLen
    push_cast
    simp only [add_assoc]
    ring

private def stepInt (S : Finset ℤ) (c : ℤ → ℝ) (p q : ℝ) : ℝ :=
  ∑ k ∈ S, c k * segLen p q k

private lemma stepInt_nonneg (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k) (p q : ℝ) :
    0 ≤ stepInt S c p q :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (segLen_nonneg p q k)

private lemma stepInt_add (S : Finset ℤ) (c : ℤ → ℝ) (p r q : ℝ)
    (hpr : p ≤ r) (hrq : r ≤ q) :
    stepInt S c p r + stepInt S c r q = stepInt S c p q := by
  unfold stepInt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_add, segLen_add p r q hpr hrq k]

private lemma stepInt_mono (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (p₁ p₂ q₂ q₁ : ℝ) (hp : p₁ ≤ p₂) (h2 : p₂ ≤ q₂) (hq : q₂ ≤ q₁) :
    stepInt S c p₂ q₂ ≤ stepInt S c p₁ q₁ := by
  have h1 := stepInt_add S c p₁ p₂ q₁ hp (h2.trans hq)
  have h2' := stepInt_add S c p₂ q₂ q₁ h2 hq
  have hn1 := stepInt_nonneg S c hc p₁ p₂
  have hn2 := stepInt_nonneg S c hc q₂ q₁
  linarith

private lemma stepInt_le_sum (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (p q : ℝ) (hpq : p ≤ q) :
    stepInt S c p q ≤ ∑ k ∈ S, c k := by
  unfold stepInt
  refine Finset.sum_le_sum fun k _ => ?_
  have := mul_le_mul_of_nonneg_left (segLen_le_one p q hpq k) (hc k)
  linarith

private lemma stepInt_ge_mul_sub (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (p q M : ℝ) (hpq : p ≤ q) (_hM : 0 ≤ M)
    (hbound : ∀ k : ℤ, p < (k : ℝ) + 1 → (k : ℝ) < q → k ∈ S ∧ M ≤ c k) :
    M * (q - p) ≤ stepInt S c p q := by
  let a : ℤ := Int.floor p
  let b : ℤ := Int.floor q
  have hab : a ≤ b := Int.floor_mono hpq
  have ha_le : (a : ℝ) ≤ p := Int.floor_le p
  have hq_lt : q < (b : ℝ) + 1 := Int.lt_floor_add_one q
  have hsum_len : ∑ k ∈ Finset.Icc a b, segLen p q k = q - p := by
    rw [sum_Icc_segLen p q a b hab]
    have h1 : max p (a : ℝ) = p := max_eq_left ha_le
    have h2 : min q p = p := min_eq_right hpq
    have h3 : max p ((b : ℝ) + 1) = (b : ℝ) + 1 := max_eq_right (hpq.trans hq_lt.le)
    have h4 : min q ((b : ℝ) + 1) = q := min_eq_left hq_lt.le
    rw [h1, h2, h3, h4]
  have hterm : ∀ k ∈ Finset.Icc a b,
      M * segLen p q k ≤ if k ∈ S then c k * segLen p q k else 0 := by
    intro k _
    by_cases hpos : 0 < segLen p q k
    · obtain ⟨h1, h2⟩ := segLen_pos_imp hpos
      obtain ⟨hkS, hMc⟩ := hbound k h1 h2
      simp only [hkS, ↓reduceIte]
      exact mul_le_mul_of_nonneg_right hMc hpos.le
    · have hzero : segLen p q k = 0 := le_antisymm (not_lt.mp hpos) (segLen_nonneg p q k)
      simp [hzero]
  have hstep1 : M * (q - p) ≤ ∑ k ∈ Finset.Icc a b, if k ∈ S then c k * segLen p q k else 0 := by
    rw [← hsum_len, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hstep2 : (∑ k ∈ Finset.Icc a b, if k ∈ S then c k * segLen p q k else 0) ≤
      ∑ k ∈ S, c k * segLen p q k := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.mp hk).2) ?_
    intro k _ _
    exact mul_nonneg (hc k) (segLen_nonneg p q k)
  exact hstep1.trans hstep2

private inductive ValidSegs : ℝ → ℝ → List (ℝ × ℝ × ℝ) → Prop
  | nil {p q : ℝ} (hpq : p ≤ q) : ValidSegs p q []
  | cons {p q x y a : ℝ} {rest : List (ℝ × ℝ × ℝ)}
      (hpx : p ≤ x) (hxy : x < y) (ha : 0 < a) (hrest : ValidSegs y q rest) :
      ValidSegs p q ((x, y, a) :: rest)

private lemma ValidSegs.le {p q : ℝ} {L : List (ℝ × ℝ × ℝ)} (h : ValidSegs p q L) : p ≤ q := by
  induction h with
  | nil hpq => exact hpq
  | cons hpx hxy _ _ ih => linarith

private def segMass : List (ℝ × ℝ × ℝ) → ℝ
  | [] => 0
  | (x, y, a) :: rest => a * (y - x) + segMass rest

private lemma am_gm_step (m a b : ℝ) (hm : 0 ≤ m) (ha : 0 < a) (hb : 0 < b) :
    m ≤ Real.sqrt (a * b) * ((m / a + m / b) / 2) := by
  have hsq : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have hab : 2 * Real.sqrt (a * b) ≤ a + b := by
    rw [Real.sqrt_mul ha.le]
    nlinarith [Real.mul_self_sqrt ha.le, Real.mul_self_sqrt hb.le]
  have hpos : 0 < a * b := mul_pos ha hb
  have hmul : 2 * (a * b) ≤ Real.sqrt (a * b) * (a + b) := by
    have h1 := mul_le_mul_of_nonneg_left hab (Real.sqrt_nonneg (a * b))
    have h2 : Real.sqrt (a * b) * (2 * Real.sqrt (a * b)) = 2 * (a * b) := by
      have := Real.mul_self_sqrt hpos.le
      linarith
    linarith
  have hdiv : (1 : ℝ) ≤ Real.sqrt (a * b) * ((1 / a + 1 / b) / 2) := by
    have hrew : (1 / a + 1 / b) / 2 = (a + b) / (2 * (a * b)) := by field_simp; ring
    rw [hrew, ← mul_div_assoc, one_le_div (by positivity)]
    exact hmul
  have := mul_le_mul_of_nonneg_left hdiv hm
  have hrew2 : m * (Real.sqrt (a * b) * ((1 / a + 1 / b) / 2)) =
      Real.sqrt (a * b) * ((m / a + m / b) / 2) := by ring
  linarith

private lemma step_pl_aux (S : Finset ℤ) (c : ℤ → ℝ) (hc : ∀ k, 0 ≤ c k) :
    ∀ (n : ℕ) (pF qF pG qG : ℝ) (F G : List (ℝ × ℝ × ℝ)),
      F.length + G.length ≤ n →
      ValidSegs pF qF F → ValidSegs pG qG G →
      segMass F = segMass G →
      (∀ sF ∈ F, ∀ sG ∈ G, ∀ k : ℤ,
        (sF.1 + sG.1) / 2 < (k : ℝ) + 1 → (k : ℝ) < (sF.2.1 + sG.2.1) / 2 →
        k ∈ S ∧ Real.sqrt (sF.2.2 * sG.2.2) ≤ c k) →
      segMass F ≤ stepInt S c ((pF + pG) / 2) ((qF + qG) / 2) := by
  intro n
  induction n with
  | zero =>
    intro pF qF pG qG F G hlen _ _ _ _
    have hF : F = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hF, segMass]
    exact stepInt_nonneg S c hc _ _
  | succ n ih =>
    intro pF qF pG qG F G hlen hVF hVG hmass hpt
    cases F with
    | nil =>
      rw [segMass]
      exact stepInt_nonneg S c hc _ _
    | cons sF F' =>
      cases G with
      | nil =>
        rw [hmass, segMass]
        exact stepInt_nonneg S c hc _ _
      | cons sG G' =>
        rcases sF with ⟨x, y, a⟩
        rcases sG with ⟨u, v, b⟩
        cases hVF with
        | cons hpx hxy ha hVF' =>
          cases hVG with
          | cons hpu huv hb hVG' =>
            let mF := a * (y - x)
            let mG := b * (v - u)
            have hmF_pos : 0 < mF := mul_pos ha (sub_pos.mpr hxy)
            have hmG_pos : 0 < mG := mul_pos hb (sub_pos.mpr huv)
            have hyq : y ≤ qF := hVF'.le
            have hvq : v ≤ qG := hVG'.le
            by_cases hle : mF ≤ mG
            · -- Peel off sF completely, split sG at u' = u + mF / b
              let u' := u + mF / b
              have hu_lt : u < u' := by
                have : 0 < mF / b := div_pos hmF_pos hb
                linarith
              have hu'_le : u' ≤ v := by
                have h1 : mF / b ≤ v - u := (div_le_iff₀ hb).mpr (by dsimp [mG] at hle; linarith)
                linarith
              let mid := (y + u') / 2
              have hp_le : (pF + pG) / 2 ≤ (x + u) / 2 := by linarith
              have hstart_le : (x + u) / 2 ≤ mid := by dsimp only [mid]; linarith
              have hmid_le : mid ≤ (qF + qG) / 2 := by dsimp only [mid]; linarith
              have hseg1 : mF ≤ stepInt S c ((x + u) / 2) mid := by
                have hbound : ∀ k : ℤ, (x + u) / 2 < (k : ℝ) + 1 → (k : ℝ) < mid →
                    k ∈ S ∧ Real.sqrt (a * b) ≤ c k := by
                  intro k h1 h2
                  have h2' : (k : ℝ) < (y + v) / 2 := by dsimp only [mid] at h2; linarith
                  exact hpt (x, y, a) (List.mem_cons.mpr (Or.inl rfl)) (u, v, b) (List.mem_cons.mpr (Or.inl rfl))
                    k h1 h2'
                have hst := stepInt_ge_mul_sub S c hc ((x + u) / 2) mid (Real.sqrt (a * b))
                  hstart_le (Real.sqrt_nonneg _) hbound
                have ham := am_gm_step mF a b hmF_pos.le ha hb
                have hlen_eq : mid - (x + u) / 2 = (mF / a + mF / b) / 2 := by
                  have hya : y - x = mF / a := by
                    dsimp [mF]; field_simp
                  have hub : u' - u = mF / b := by dsimp [u']; ring
                  dsimp [mid]; linarith
                rw [hlen_eq] at hst
                linarith
              have hseg2 : segMass F' ≤ stepInt S c mid ((qF + qG) / 2) := by
                by_cases huv' : u' = v
                · have hVG'' : ValidSegs u' qG G' := by rwa [huv']
                  have hm' : segMass F' = segMass G' := by
                    have hmeq : mF = mG := by
                      have : mF / b = v - u := by dsimp [u'] at huv'; linarith
                      have : mF = b * (v - u) := by
                        have := (div_eq_iff hb.ne').mp this
                        linarith
                      exact this
                    simp only [segMass] at hmass
                    linarith
                  have hlen' : F'.length + G'.length ≤ n := by
                    simp only [List.length_cons] at hlen; omega
                  exact ih y qF u' qG F' G' hlen' hVF' hVG'' hm' fun tF htF tG htG k h1 h2 =>
                    hpt tF (List.mem_cons_of_mem _ htF) tG (List.mem_cons_of_mem _ htG) k h1 h2
                · have hu'_lt_v : u' < v := lt_of_le_of_ne hu'_le huv'
                  have hVG'' : ValidSegs u' qG ((u', v, b) :: G') :=
                    ValidSegs.cons le_rfl hu'_lt_v hb hVG'
                  have hm' : segMass F' = segMass ((u', v, b) :: G') := by
                    simp only [segMass] at hmass ⊢
                    have hb_mul : b * (v - u') = mG - mF := by
                      dsimp [u', mG]; field_simp; ring
                    linarith
                  have hlen' : F'.length + ((u', v, b) :: G').length ≤ n := by
                    simp only [List.length_cons] at hlen ⊢; omega
                  refine ih y qF u' qG F' ((u', v, b) :: G') hlen' hVF' hVG'' hm' ?_
                  intro tF htF tG htG k h1 h2
                  rcases List.mem_cons.mp htG with rfl | htG'
                  · have h1' : (tF.1 + u) / 2 < (k : ℝ) + 1 := by linarith
                    exact hpt tF (List.mem_cons_of_mem _ htF) (u, v, b) (List.mem_cons.mpr (Or.inl rfl))
                      k h1' h2
                  · exact hpt tF (List.mem_cons_of_mem _ htF) tG (List.mem_cons_of_mem _ htG')
                      k h1 h2
              have hcomb : segMass ((x, y, a) :: F') ≤ stepInt S c ((x + u) / 2) ((qF + qG) / 2) := by
                rw [← stepInt_add S c ((x + u) / 2) mid ((qF + qG) / 2) hstart_le hmid_le]
                simp only [segMass]
                linarith
              exact hcomb.trans (stepInt_mono S c hc _ _ _ _ hp_le (hstart_le.trans hmid_le) le_rfl)
            · -- Symmetric: mG < mF, peel off sG completely, split sF at x' = x + mG / a
              push Not at hle
              let x' := x + mG / a
              have hx_lt : x < x' := by
                have : 0 < mG / a := div_pos hmG_pos ha
                linarith
              have hx'_lt : x' < y := by
                have h1 : mG / a < y - x := (div_lt_iff₀ ha).mpr (by dsimp [mF] at hle; linarith)
                linarith
              let mid := (x' + v) / 2
              have hp_le : (pF + pG) / 2 ≤ (x + u) / 2 := by linarith
              have hstart_le : (x + u) / 2 ≤ mid := by dsimp only [mid]; linarith
              have hmid_le : mid ≤ (qF + qG) / 2 := by dsimp only [mid]; linarith
              have hseg1 : mG ≤ stepInt S c ((x + u) / 2) mid := by
                have hbound : ∀ k : ℤ, (x + u) / 2 < (k : ℝ) + 1 → (k : ℝ) < mid →
                    k ∈ S ∧ Real.sqrt (a * b) ≤ c k := by
                  intro k h1 h2
                  have h2' : (k : ℝ) < (y + v) / 2 := by dsimp only [mid] at h2; linarith
                  exact hpt (x, y, a) (List.mem_cons.mpr (Or.inl rfl)) (u, v, b) (List.mem_cons.mpr (Or.inl rfl))
                    k h1 h2'
                have hst := stepInt_ge_mul_sub S c hc ((x + u) / 2) mid (Real.sqrt (a * b))
                  hstart_le (Real.sqrt_nonneg _) hbound
                have ham := am_gm_step mG a b hmG_pos.le ha hb
                have hlen_eq : mid - (x + u) / 2 = (mG / a + mG / b) / 2 := by
                  have hxa : x' - x = mG / a := by dsimp [x']; ring
                  have hvb : v - u = mG / b := by dsimp [mG]; field_simp
                  dsimp [mid]; linarith
                rw [hlen_eq] at hst
                linarith
              have hVF'' : ValidSegs x' qF ((x', y, a) :: F') :=
                ValidSegs.cons le_rfl hx'_lt ha hVF'
              have hm' : segMass ((x', y, a) :: F') = segMass G' := by
                simp only [segMass] at hmass ⊢
                have ha_mul : a * (y - x') = mF - mG := by
                  dsimp [x', mF]; field_simp; ring
                linarith
              have hlen' : ((x', y, a) :: F').length + G'.length ≤ n := by
                simp only [List.length_cons] at hlen ⊢; omega
              have hseg2 : segMass ((x', y, a) :: F') ≤ stepInt S c mid ((qF + qG) / 2) := by
                refine ih x' qF v qG ((x', y, a) :: F') G' hlen' hVF'' hVG' hm' ?_
                intro tF htF tG htG k h1 h2
                rcases List.mem_cons.mp htF with rfl | htF'
                · have h1' : (x + tG.1) / 2 < (k : ℝ) + 1 := by linarith
                  exact hpt (x, y, a) (List.mem_cons.mpr (Or.inl rfl)) tG (List.mem_cons_of_mem _ htG)
                    k h1' h2
                · exact hpt tF (List.mem_cons_of_mem _ htF') tG (List.mem_cons_of_mem _ htG)
                    k h1 h2
              have hcomb : segMass ((x, y, a) :: F') ≤ stepInt S c ((x + u) / 2) ((qF + qG) / 2) := by
                rw [← stepInt_add S c ((x + u) / 2) mid ((qF + qG) / 2) hstart_le hmid_le]
                simp only [segMass] at hseg2 ⊢
                have ha_mul : a * (y - x') = mF - mG := by
                  dsimp [x', mF]; field_simp; ring
                linarith
              exact hcomb.trans (stepInt_mono S c hc _ _ _ _ hp_le (hstart_le.trans hmid_le) le_rfl)

private def buildSegs (f : ℤ → ℝ) : List ℤ → List (ℝ × ℝ × ℝ)
  | [] => []
  | i :: rest =>
    if 0 < f i then ((i : ℝ), (i : ℝ) + 1, f i) :: buildSegs f rest
    else buildSegs f rest

private lemma buildSegs_valid (f : ℤ → ℝ) :
    ∀ (L : List ℤ) (p q : ℝ),
      L.Pairwise (· < ·) →
      (∀ i ∈ L, p ≤ (i : ℝ) ∧ (i : ℝ) + 1 ≤ q) →
      p ≤ q →
      ValidSegs p q (buildSegs f L) := by
  intro L
  induction L with
  | nil =>
    intro p q _ _ hpq
    exact ValidSegs.nil hpq
  | cons i rest ih =>
    intro p q hpw hbd hpq
    rw [List.pairwise_cons] at hpw
    have hi := hbd i (List.mem_cons.mpr (Or.inl rfl))
    unfold buildSegs
    split_ifs with hf
    · refine ValidSegs.cons hi.1 (by linarith) hf ?_
      refine ih ((i : ℝ) + 1) q hpw.2 ?_ hi.2
      intro j hj
      have hij : i < j := hpw.1 j hj
      have hjbd := hbd j (List.mem_cons_of_mem _ hj)
      have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hij)
      exact ⟨hij', hjbd.2⟩
    · exact ih p q hpw.2 (fun j hj => hbd j (List.mem_cons_of_mem _ hj)) hpq

private lemma buildSegs_mass (f : ℤ → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∀ L : List ℤ, segMass (buildSegs f L) = (L.map f).sum := by
  intro L
  induction L with
  | nil => simp [buildSegs, segMass]
  | cons i rest ih =>
    unfold buildSegs
    split_ifs with hpos
    · simp only [segMass, List.map_cons, List.sum_cons, ih]
      ring
    · have h0 : f i = 0 := le_antisymm (not_lt.mp hpos) (hf i)
      simp [ih, h0]

private lemma buildSegs_mem (f : ℤ → ℝ) :
    ∀ (L : List ℤ) (s : ℝ × ℝ × ℝ),
      s ∈ buildSegs f L → ∃ i ∈ L, s = ((i : ℝ), (i : ℝ) + 1, f i) := by
  intro L
  induction L with
  | nil => simp [buildSegs]
  | cons i rest ih =>
    intro s hs
    unfold buildSegs at hs
    split_ifs at hs with hpos
    · rcases List.mem_cons.mp hs with rfl | hs'
      · exact ⟨i, List.mem_cons.mpr (Or.inl rfl), rfl⟩
      · obtain ⟨j, hj, rfl⟩ := ih s hs'
        exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := ih s hs
      exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩

private lemma int_mem_Icc_of_mid_close {M : ℕ} {i j k : ℤ}
    (hi : i ∈ Finset.Icc (-(M : ℤ)) M) (hj : j ∈ Finset.Icc (-(M : ℤ)) M)
    (hk : |i + j - 2 * k| ≤ 1) :
    k ∈ Finset.Icc (-(M : ℤ)) M := by
  rw [Finset.mem_Icc] at hi hj ⊢
  rw [abs_le] at hk
  omega

private lemma discrete_PL_1d (M : ℕ) (f g h : ℤ → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ j, 0 ≤ g j) (hh : ∀ k, 0 ≤ h k)
    (hpl : ∀ i ∈ Finset.Icc (-(M : ℤ)) M, ∀ j ∈ Finset.Icc (-(M : ℤ)) M,
      ∀ k : ℤ, |i + j - 2 * k| ≤ 1 → Real.sqrt (f i * g j) ≤ h k) :
    Real.sqrt ((∑ i ∈ Finset.Icc (-(M : ℤ)) M, f i) *
               (∑ j ∈ Finset.Icc (-(M : ℤ)) M, g j)) ≤
      ∑ k ∈ Finset.Icc (-(M : ℤ)) M, h k := by
  let I := Finset.Icc (-(M : ℤ)) M
  let A := ∑ i ∈ I, f i
  let B := ∑ j ∈ I, g j
  change Real.sqrt (A * B) ≤ ∑ k ∈ I, h k
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => hf i
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => hg j
  by_cases hA : A = 0
  · rw [hA, zero_mul, Real.sqrt_zero]
    exact Finset.sum_nonneg fun k _ => hh k
  by_cases hB : B = 0
  · rw [hB, mul_zero, Real.sqrt_zero]
    exact Finset.sum_nonneg fun k _ => hh k
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA)
  have hBpos : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
  let f' : ℤ → ℝ := fun i => f i / A
  let g' : ℤ → ℝ := fun j => g j / B
  let h' : ℤ → ℝ := fun k => h k / Real.sqrt (A * B)
  have hf' : ∀ i, 0 ≤ f' i := fun i => div_nonneg (hf i) hApos.le
  have hg' : ∀ j, 0 ≤ g' j := fun j => div_nonneg (hg j) hBpos.le
  have hh' : ∀ k, 0 ≤ h' k := fun k => div_nonneg (hh k) (Real.sqrt_nonneg _)
  let L : List ℤ := (List.range (2 * M + 1)).map (fun (n : ℕ) => (n : ℤ) - (M : ℤ))
  have hL_pw : L.Pairwise (· < ·) := by
    dsimp [L]
    rw [List.pairwise_map]
    refine List.Pairwise.imp (fun {a b : ℕ} (hab : a < b) => by omega) List.pairwise_lt_range
  have hL_nodup : L.Nodup := hL_pw.imp ne_of_lt
  have hL_mem : ∀ i : ℤ, i ∈ L ↔ i ∈ I := by
    intro i
    simp only [L, I, List.mem_map, List.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨n, hn, rfl⟩; omega
    · intro ⟨h1, h2⟩
      exact ⟨(i + M).toNat, by omega, by omega⟩
  have hL_toFinset : L.toFinset = I := by
    ext i; rw [List.mem_toFinset, hL_mem]
  have hlist_sum : ∀ (K : List ℤ) (φ : ℤ → ℝ), K.Nodup → (K.map φ).sum = ∑ i ∈ K.toFinset, φ i := by
    intro K φ
    induction K with
    | nil => intro _; simp
    | cons a t ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.sum_cons, List.toFinset_cons,
          Finset.sum_insert (by rw [List.mem_toFinset]; exact hnd.1), ih hnd.2]
  have hL_sum : ∀ φ : ℤ → ℝ, (L.map φ).sum = ∑ i ∈ I, φ i := by
    intro φ
    rw [← hL_toFinset, hlist_sum L φ hL_nodup]
  have hL_bd : ∀ i ∈ L, (-(M : ℝ)) ≤ (i : ℝ) ∧ (i : ℝ) + 1 ≤ (M : ℝ) + 1 := by
    intro i hi
    have hI := (hL_mem i).mp hi
    rw [Finset.mem_Icc] at hI
    constructor <;> [exact_mod_cast hI.1; exact_mod_cast (by omega : i + 1 ≤ (M : ℤ) + 1)]
  have hpq : (-(M : ℝ)) ≤ (M : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  let F := buildSegs f' L
  let G := buildSegs g' L
  have hVF : ValidSegs (-(M : ℝ)) ((M : ℝ) + 1) F := buildSegs_valid f' L _ _ hL_pw hL_bd hpq
  have hVG : ValidSegs (-(M : ℝ)) ((M : ℝ) + 1) G := buildSegs_valid g' L _ _ hL_pw hL_bd hpq
  have hmassF : segMass F = 1 := by
    rw [buildSegs_mass f' hf' L, hL_sum]
    simp [f', ← Finset.sum_div, A, div_self hApos.ne']
  have hmassG : segMass G = 1 := by
    rw [buildSegs_mass g' hg' L, hL_sum]
    simp [g', ← Finset.sum_div, B, div_self hBpos.ne']
  have hpt : ∀ sF ∈ F, ∀ sG ∈ G, ∀ k : ℤ,
      (sF.1 + sG.1) / 2 < (k : ℝ) + 1 → (k : ℝ) < (sF.2.1 + sG.2.1) / 2 →
      k ∈ I ∧ Real.sqrt (sF.2.2 * sG.2.2) ≤ h' k := by
    intro sF hsF sG hsG k h1 h2
    obtain ⟨i, hiL, rfl⟩ := buildSegs_mem f' L sF hsF
    obtain ⟨j, hjL, rfl⟩ := buildSegs_mem g' L sG hsG
    have hiI : i ∈ I := (hL_mem i).mp hiL
    have hjI : j ∈ I := (hL_mem j).mp hjL
    have h1Z : i + j < 2 * k + 2 := by
      have : ((i + j : ℤ) : ℝ) < ((2 * k + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp this
    have h2Z : 2 * k < i + j + 2 := by
      have : ((2 * k : ℤ) : ℝ) < ((i + j + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp this
    have habs : |i + j - 2 * k| ≤ 1 := by
      rw [abs_le]; omega
    refine ⟨int_mem_Icc_of_mid_close hiI hjI habs, ?_⟩
    have hplk := hpl i hiI j hjI k habs
    dsimp only [f', g', h']
    have hdiv : f i / A * (g j / B) = (f i * g j) / (A * B) := by ring
    rw [hdiv, Real.sqrt_div (mul_nonneg (hf i) (hg j))]
    exact div_le_div_of_nonneg_right hplk (Real.sqrt_nonneg _)
  have hstep := step_pl_aux I h' hh' (F.length + G.length) _ _ _ _ F G le_rfl hVF hVG
    (hmassF.trans hmassG.symm) hpt
  rw [hmassF] at hstep
  have hle_sum : stepInt I h' ((-(M : ℝ) + -(M : ℝ)) / 2) (((M : ℝ) + 1 + ((M : ℝ) + 1)) / 2) ≤
      ∑ k ∈ I, h' k :=
    stepInt_le_sum I h' hh' _ _ (by linarith)
  have h1 : 1 ≤ (∑ k ∈ I, h k) / Real.sqrt (A * B) := by
    have : ∑ k ∈ I, h' k = (∑ k ∈ I, h k) / Real.sqrt (A * B) := by
      simp [h', ← Finset.sum_div]
    linarith
  exact (one_le_div (Real.sqrt_pos.mpr (mul_pos hApos hBpos))).mp h1

private def box (d M : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M : ℤ)) M)

private lemma mem_box_iff {d M : ℕ} {x : Fin d → ℤ} :
    x ∈ box d M ↔ ∀ r : Fin d, -(M : ℤ) ≤ x r ∧ x r ≤ (M : ℤ) := by
  simp [box, Fintype.mem_piFinset, Finset.mem_Icc]

private lemma sum_box_succ {d M : ℕ} (φ : (Fin (d + 1) → ℤ) → ℝ) :
    ∑ x ∈ box (d + 1) M, φ x =
      ∑ a ∈ Finset.Icc (-(M : ℤ)) M, ∑ x' ∈ box d M, φ (Fin.cons a x') := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun x _ => (x 0, Fin.tail x)) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_product, Finset.mem_Icc, mem_box_iff]
    rw [mem_box_iff] at hx
    exact ⟨hx 0, fun r => hx r.succ⟩
  · intro x₁ _ x₂ _ h
    have h0 : x₁ 0 = x₂ 0 := congrArg Prod.fst h
    have ht : Fin.tail x₁ = Fin.tail x₂ := congrArg Prod.snd h
    ext r
    refine Fin.cases h0 (fun i => congrFun ht i) r
  · intro p hp
    rw [Finset.mem_product, Finset.mem_Icc, mem_box_iff] at hp
    refine ⟨Fin.cons p.1 p.2, ?_, ?_⟩
    · rw [mem_box_iff]
      intro r
      exact Fin.cases hp.1 hp.2 r
    · ext
      · simp
      · simp
  · intro x _
    congr 1
    exact (Fin.cons_self_tail x).symm

private lemma discrete_PL_nd (d M : ℕ) :
    ∀ (f g h : (Fin d → ℤ) → ℝ),
      (∀ x, 0 ≤ f x) → (∀ y, 0 ≤ g y) → (∀ z, 0 ≤ h z) →
      (∀ x ∈ box d M, ∀ y ∈ box d M, ∀ z ∈ box d M,
        (∀ r : Fin d, |x r + y r - 2 * z r| ≤ 1) → Real.sqrt (f x * g y) ≤ h z) →
      Real.sqrt ((∑ x ∈ box d M, f x) * (∑ y ∈ box d M, g y)) ≤ ∑ z ∈ box d M, h z := by
  induction d with
  | zero =>
    intro f g h _ _ _ hpl
    have hbox0 : box 0 M = {Fin.elim0} := by
      ext x
      simp only [mem_box_iff, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ r => Fin.elim0 r⟩
    rw [hbox0, Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton]
    have hmem : Fin.elim0 ∈ box 0 M := by rw [hbox0]; simp
    exact hpl Fin.elim0 hmem Fin.elim0 hmem Fin.elim0 hmem (fun r => Fin.elim0 r)
  | succ d ih =>
    intro f g h hf hg hh hpl
    let F : ℤ → ℝ := fun a => ∑ x' ∈ box d M, f (Fin.cons a x')
    let G : ℤ → ℝ := fun b => ∑ y' ∈ box d M, g (Fin.cons b y')
    let H : ℤ → ℝ := fun c => ∑ z' ∈ box d M, h (Fin.cons c z')
    have hF : ∀ a, 0 ≤ F a := fun a => Finset.sum_nonneg fun x' _ => hf _
    have hG : ∀ b, 0 ≤ G b := fun b => Finset.sum_nonneg fun y' _ => hg _
    have hH : ∀ c, 0 ≤ H c := fun c => Finset.sum_nonneg fun z' _ => hh _
    have hpl1 : ∀ a ∈ Finset.Icc (-(M : ℤ)) M, ∀ b ∈ Finset.Icc (-(M : ℤ)) M,
        ∀ c : ℤ, |a + b - 2 * c| ≤ 1 → Real.sqrt (F a * G b) ≤ H c := by
      intro a ha b hb c habc
      have hc : c ∈ Finset.Icc (-(M : ℤ)) M := int_mem_Icc_of_mid_close ha hb habc
      refine ih (fun x' => f (Fin.cons a x')) (fun y' => g (Fin.cons b y'))
        (fun z' => h (Fin.cons c z')) (fun _ => hf _) (fun _ => hg _) (fun _ => hh _) ?_
      intro x' hx' y' hy' z' hz' hclose
      have hx : Fin.cons a x' ∈ box (d + 1) M := by
        rw [mem_box_iff]; intro r
        exact Fin.cases (Finset.mem_Icc.mp ha) (mem_box_iff.mp hx') r
      have hy : Fin.cons b y' ∈ box (d + 1) M := by
        rw [mem_box_iff]; intro r
        exact Fin.cases (Finset.mem_Icc.mp hb) (mem_box_iff.mp hy') r
      have hz : Fin.cons c z' ∈ box (d + 1) M := by
        rw [mem_box_iff]; intro r
        exact Fin.cases (Finset.mem_Icc.mp hc) (mem_box_iff.mp hz') r
      refine hpl _ hx _ hy _ hz fun r => ?_
      exact Fin.cases habc hclose r
    rw [sum_box_succ f, sum_box_succ g, sum_box_succ h]
    exact discrete_PL_1d M F G H hF hG hH hpl1

/- ### Module 3B: Truncated discrete Gaussian, moments, Chebyshev, Fejér anti-concentration -/

private lemma cos_bounds {a : ℝ} (ha : |a| ≤ 1) :
    1 / 2 ≤ Real.cos a ∧ Real.cos a ≤ 1 - a ^ 2 / 3 := by
  constructor
  · have h1 := Real.one_sub_sq_div_two_le_cos (x := a)
    have h2 : a ^ 2 ≤ 1 := by nlinarith [abs_le.mp ha]
    linarith
  · have hcos_abs : Real.cos a = Real.cos |a| := by
      rcases le_total 0 a with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, Real.cos_neg]
    rw [hcos_abs]
    have ha0 : 0 ≤ |a| := abs_nonneg a
    by_cases h0 : |a| = 0
    · rw [h0, Real.cos_zero]
      have : a = 0 := abs_eq_zero.mp h0
      rw [this]; norm_num
    · have hpos : 0 < |a| / 2 := by positivity
      have hsin := Real.sin_gt_sub_cube hpos
      have hsin_ge : (5 / 6) * (|a| / 2) ≤ Real.sin (|a| / 2) := by
        have hle1 : |a| ^ 2 ≤ 1 := by nlinarith [abs_nonneg a]
        nlinarith
      have hdouble : Real.cos |a| = 1 - 2 * Real.sin (|a| / 2) ^ 2 := by
        have h2 : Real.cos (2 * (|a| / 2)) = 1 - 2 * Real.sin (|a| / 2) ^ 2 := by
          rw [Real.cos_two_mul]
          nlinarith [Real.sin_sq_add_cos_sq (|a| / 2)]
        have h3 : 2 * (|a| / 2) = |a| := by ring
        rwa [h3] at h2
      rw [hdouble]
      have hsq : ((5 / 6) * (|a| / 2)) ^ 2 ≤ Real.sin (|a| / 2) ^ 2 := by
        nlinarith [Real.sin_gt_sub_cube hpos]
      have habs_sq : |a| ^ 2 = a ^ 2 := sq_abs a
      nlinarith

private lemma exp_neg_half_ge : (1 / 2 : ℝ) ≤ Real.exp (-1 / 2) := by
  have h1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h3 : Real.exp (1 / 2) < 2 := by
    nlinarith [Real.exp_pos (1 / 2)]
  calc (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    _ ≤ (Real.exp (1 / 2))⁻¹ := inv_anti₀ (Real.exp_pos (1 / 2)) h3.le
    _ = Real.exp (-1 / 2) := by rw [← Real.exp_neg]; congr 1; ring

private lemma sum_sq_Icc_ge (n : ℕ) :
    (n : ℝ) ^ 3 / 3 ≤ ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k : ℝ) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hIcc : Finset.Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ) =
        insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (1 : ℤ) (n : ℤ)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : ((n + 1 : ℕ) : ℤ) ∉ Finset.Icc (1 : ℤ) (n : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnot]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

private def w1 (σ : ℕ) (k : ℤ) : ℝ :=
  Real.exp (-((k : ℝ) ^ 2) / (2 * (σ : ℝ) ^ 2))

private def Z1 (σ : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(σ : ℤ)) σ, w1 σ k

private def p1 (σ : ℕ) (k : ℤ) : ℝ :=
  w1 σ k / Z1 σ

private def v1 (σ : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ k * (k : ℝ) ^ 2

private lemma w1_pos (σ : ℕ) (k : ℤ) : 0 < w1 σ k := Real.exp_pos _

private lemma w1_neg (σ : ℕ) (k : ℤ) : w1 σ (-k) = w1 σ k := by
  simp [w1]

private lemma Z1_pos (σ : ℕ) : 0 < Z1 σ := by
  unfold Z1
  refine Finset.sum_pos (fun k _ => w1_pos σ k) ?_
  exact ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

private lemma p1_nonneg (σ : ℕ) (k : ℤ) : 0 ≤ p1 σ k :=
  div_nonneg (w1_pos σ k).le (Z1_pos σ).le

private lemma p1_neg (σ : ℕ) (k : ℤ) : p1 σ (-k) = p1 σ k := by
  simp [p1, w1_neg]

private lemma sum_p1 (σ : ℕ) : ∑ k ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ k = 1 := by
  simp only [p1, ← Finset.sum_div]
  exact div_self (Z1_pos σ).ne'

private lemma v1_bounds (σ : ℕ) (hσ : 1 ≤ σ) :
    (σ : ℝ) ^ 2 / 9 ≤ v1 σ ∧ v1 σ ≤ (σ : ℝ) ^ 2 ∧
    ∑ k ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ k * (k : ℝ) ^ 4 ≤ (σ : ℝ) ^ 4 := by
  let I := Finset.Icc (-(σ : ℤ)) σ
  have hσR : (1 : ℝ) ≤ (σ : ℝ) := Nat.one_le_cast.mpr hσ
  have hσpos : (0 : ℝ) < (σ : ℝ) := by linarith
  have hw1_ge : ∀ k ∈ I, (1 / 2 : ℝ) ≤ w1 σ k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk2 : (k : ℝ) ^ 2 ≤ (σ : ℝ) ^ 2 := by
      have h1 : -(σ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
      have h2 : (k : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hk.2
      nlinarith
    have hexp : (-1 / 2 : ℝ) ≤ -((k : ℝ) ^ 2) / (2 * (σ : ℝ) ^ 2) := by
      have hden : (0 : ℝ) < 2 * (σ : ℝ) ^ 2 := by positivity
      rw [div_le_div_iff₀ (by norm_num) hden]
      nlinarith
    exact exp_neg_half_ge.trans (Real.exp_le_exp.mpr hexp)
  have hw1_le : ∀ k ∈ I, w1 σ k ≤ 1 := by
    intro k _
    unfold w1
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  have hZ1_le : Z1 σ ≤ 3 * (σ : ℝ) := by
    have hcard : (I.card : ℝ) = 2 * (σ : ℝ) + 1 := by
      have hc : I.card = 2 * σ + 1 := by
        dsimp [I]
        rw [Int.card_Icc]
        omega
      exact_mod_cast hc
    calc Z1 σ = ∑ k ∈ I, w1 σ k := rfl
      _ ≤ ∑ _k ∈ I, (1 : ℝ) := Finset.sum_le_sum hw1_le
      _ = (I.card : ℝ) := by simp
      _ = 2 * (σ : ℝ) + 1 := hcard
      _ ≤ 3 * (σ : ℝ) := by linarith
  have hnum_ge : (σ : ℝ) ^ 3 / 3 ≤ ∑ k ∈ I, w1 σ k * (k : ℝ) ^ 2 := by
    have h1 : (1 / 2 : ℝ) * (∑ k ∈ I, (k : ℝ) ^ 2) ≤ ∑ k ∈ I, w1 σ k * (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right (hw1_ge k hk) (sq_nonneg _)
    let Ipos := Finset.Icc (1 : ℤ) (σ : ℤ)
    let Ineg := Finset.Icc (-(σ : ℤ)) (-1 : ℤ)
    have hdisj : Disjoint Ipos Ineg := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      rw [Finset.mem_Icc] at hk1 hk2; omega
    have hsub : Ipos ∪ Ineg ⊆ I := by
      intro k hk
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc] at hk
      rw [Finset.mem_Icc]; omega
    have hneg_eq : ∑ k ∈ Ineg, (k : ℝ) ^ 2 = ∑ k ∈ Ipos, (k : ℝ) ^ 2 := by
      refine Finset.sum_bij (fun k _ => -k) ?_ ?_ ?_ ?_
      · intro k hk; rw [Finset.mem_Icc] at hk ⊢; omega
      · intro a _ b _ h; omega
      · intro k hk; exact ⟨-k, by rw [Finset.mem_Icc] at hk ⊢; omega, neg_neg k⟩
      · intro k _; simp
    have hsum2 : (2 / 3 : ℝ) * (σ : ℝ) ^ 3 ≤ ∑ k ∈ I, (k : ℝ) ^ 2 := by
      calc (2 / 3 : ℝ) * (σ : ℝ) ^ 3
          = (σ : ℝ) ^ 3 / 3 + (σ : ℝ) ^ 3 / 3 := by ring
        _ ≤ (∑ k ∈ Ipos, (k : ℝ) ^ 2) + (∑ k ∈ Ipos, (k : ℝ) ^ 2) :=
            add_le_add (sum_sq_Icc_ge σ) (sum_sq_Icc_ge σ)
        _ = (∑ k ∈ Ipos, (k : ℝ) ^ 2) + (∑ k ∈ Ineg, (k : ℝ) ^ 2) := by rw [hneg_eq]
        _ = ∑ k ∈ Ipos ∪ Ineg, (k : ℝ) ^ 2 := (Finset.sum_union hdisj).symm
        _ ≤ ∑ k ∈ I, (k : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · have hv1_eq : v1 σ = (∑ k ∈ I, w1 σ k * (k : ℝ) ^ 2) / Z1 σ := by
      simp only [v1, p1, div_mul_eq_mul_div, ← Finset.sum_div]; rfl
    rw [hv1_eq, le_div_iff₀ (Z1_pos σ)]
    calc (σ : ℝ) ^ 2 / 9 * Z1 σ
        ≤ (σ : ℝ) ^ 2 / 9 * (3 * (σ : ℝ)) :=
          mul_le_mul_of_nonneg_left hZ1_le (by positivity)
      _ = (σ : ℝ) ^ 3 / 3 := by ring
      _ ≤ ∑ k ∈ I, w1 σ k * (k : ℝ) ^ 2 := hnum_ge
  · calc v1 σ = ∑ k ∈ I, p1 σ k * (k : ℝ) ^ 2 := rfl
      _ ≤ ∑ k ∈ I, p1 σ k * (σ : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (p1_nonneg σ k)
          rw [Finset.mem_Icc] at hk
          have h1 : -(σ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
          have h2 : (k : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hk.2
          nlinarith
      _ = (∑ k ∈ I, p1 σ k) * (σ : ℝ) ^ 2 := by rw [← Finset.sum_mul]
      _ = (σ : ℝ) ^ 2 := by rw [sum_p1 σ, one_mul]
  · calc ∑ k ∈ I, p1 σ k * (k : ℝ) ^ 4
        ≤ ∑ k ∈ I, p1 σ k * (σ : ℝ) ^ 4 := by
          refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (p1_nonneg σ k)
          rw [Finset.mem_Icc] at hk
          have h1 : -(σ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
          have h2 : (k : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hk.2
          have hsq : (k : ℝ) ^ 2 ≤ (σ : ℝ) ^ 2 := by nlinarith
          nlinarith [sq_nonneg (k : ℝ)]
      _ = (∑ k ∈ I, p1 σ k) * (σ : ℝ) ^ 4 := by rw [← Finset.sum_mul]
      _ = (σ : ℝ) ^ 4 := by rw [sum_p1 σ, one_mul]

private def pd (d σ : ℕ) (x : Fin d → ℤ) : ℝ :=
  ∏ r : Fin d, p1 σ (x r)

private lemma pd_nonneg (d σ : ℕ) (x : Fin d → ℤ) : 0 ≤ pd d σ x :=
  Finset.prod_nonneg fun _ _ => p1_nonneg σ _

private lemma pd_neg (d σ : ℕ) (x : Fin d → ℤ) : pd d σ (-x) = pd d σ x := by
  simp [pd, p1_neg]

private lemma pd_eq_exp_div (d σ : ℕ) (x : Fin d → ℤ) :
    pd d σ x = Real.exp (-normSq x / (2 * (σ : ℝ) ^ 2)) / (Z1 σ) ^ d := by
  unfold pd p1 w1 normSq
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

-- Direct elementary proof of product factorization over `box d σ` by induction on `d`
private lemma sum_box_prod (d σ : ℕ) (f : Fin d → ℤ → ℝ) :
    ∑ x ∈ box d σ, (∏ r : Fin d, f r (x r)) =
      ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, f r a := by
  induction d with
  | zero =>
    have hbox0 : box 0 σ = {Fin.elim0} := by
      ext x
      simp only [mem_box_iff, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ r => Fin.elim0 r⟩
    simp [hbox0]
  | succ d ih =>
    rw [sum_box_succ]
    simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ih (fun r => f r.succ)]

private lemma sum_box_pd (d σ : ℕ) : ∑ x ∈ box d σ, pd d σ x = 1 := by
  unfold pd
  rw [sum_box_prod]
  simp [sum_p1]

private lemma sum_box_single (d σ : ℕ) (r : Fin d) (g : ℤ → ℝ) :
    ∑ x ∈ box d σ, pd d σ x * g (x r) = ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * g a := by
  have hrew : ∀ x : Fin d → ℤ,
      pd d σ x * g (x r) = ∏ i : Fin d, (p1 σ (x i) * if i = r then g (x i) else 1) := by
    intro x
    unfold pd
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  simp_rw [hrew]
  rw [sum_box_prod d σ (fun i a => p1 σ a * if i = r then g a else 1)]
  have h1 : ∀ i : Fin d,
      (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * if i = r then g a else 1) =
        if i = r then ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * g a else 1 := by
    intro i
    by_cases h : i = r
    · simp [h]
    · simp [h, sum_p1]
  simp_rw [h1]
  rw [Finset.prod_ite_eq']
  simp

private lemma sum_box_pair (d σ : ℕ) (r s : Fin d) (hrs : r ≠ s) (g₁ g₂ : ℤ → ℝ) :
    ∑ x ∈ box d σ, pd d σ x * (g₁ (x r) * g₂ (x s)) =
      (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * g₁ a) *
      (∑ b ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ b * g₂ b) := by
  have hrew : ∀ x : Fin d → ℤ,
      pd d σ x * (g₁ (x r) * g₂ (x s)) =
        ∏ i : Fin d, (p1 σ (x i) * (if i = r then g₁ (x i) else 1) *
          (if i = s then g₂ (x i) else 1)) := by
    intro x
    unfold pd
    simp_rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp [mul_assoc]
  simp_rw [hrew]
  rw [sum_box_prod d σ (fun i a => p1 σ a * (if i = r then g₁ a else 1) * (if i = s then g₂ a else 1))]
  have h1 : ∀ i : Fin d,
      (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
        p1 σ a * (if i = r then g₁ a else 1) * (if i = s then g₂ a else 1)) =
      (if i = r then ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * g₁ a else 1) *
      (if i = s then ∑ b ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ b * g₂ b else 1) := by
    intro i
    by_cases hr : i = r
    · subst hr
      simp [hrs]
    · by_cases hs : i = s
      · subst hs
        simp [hrs.symm]
      · simp [hr, hs, sum_p1]
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp

private lemma chebyshev_shell (d σ : ℕ) (hd : 1 ≤ d) (hσ : 1 ≤ σ) :
    1 - 324 / (d : ℝ) ≤
      ∑ x ∈ (box d σ).filter (fun x => (d : ℝ) / 2 * v1 σ ≤ normSq x), pd d σ x := by
  let B := box d σ
  let A := B.filter (fun x => (d : ℝ) / 2 * v1 σ ≤ normSq x)
  let Ac := B.filter (fun x => ¬ ((d : ℝ) / 2 * v1 σ ≤ normSq x))
  have hsplit : ∑ x ∈ A, pd d σ x + ∑ x ∈ Ac, pd d σ x = 1 := by
    rw [Finset.sum_filter_add_sum_filter_not, sum_box_pd]
  obtain ⟨hv1_lo, _, hm4_hi⟩ := v1_bounds σ hσ
  have hvar : ∑ x ∈ B, pd d σ x * (normSq x - (d : ℝ) * v1 σ) ^ 2 ≤ (d : ℝ) * (σ : ℝ) ^ 4 := by
    let f : ℤ → ℝ := fun a => (a : ℝ) ^ 2 - v1 σ
    have hmean0 : ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * f a = 0 := by
      simp only [f, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_p1, one_mul]
      unfold v1; ring
    have hsq_mean : ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (f a) ^ 2 ≤ (σ : ℝ) ^ 4 := by
      have h1 : ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (f a) ^ 2 =
          (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (a : ℝ) ^ 4) - (v1 σ) ^ 2 := by
        have hterm : ∀ a : ℤ, p1 σ a * (f a) ^ 2 =
            p1 σ a * (a : ℝ) ^ 4 - 2 * v1 σ * (p1 σ a * (a : ℝ) ^ 2) +
            p1 σ a * (v1 σ) ^ 2 := by
          intro a; dsimp [f]; ring
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.sum_mul, sum_p1, one_mul]
        unfold v1; ring
      rw [h1]
      linarith [sq_nonneg (v1 σ)]
    have hexpand : ∀ x : Fin d → ℤ,
        (normSq x - (d : ℝ) * v1 σ) ^ 2 =
          ∑ r : Fin d, ∑ s : Fin d, f (x r) * f (x s) := by
      intro x
      have h1 : normSq x - (d : ℝ) * v1 σ = ∑ r : Fin d, f (x r) := by
        simp only [normSq, f, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      rw [h1, sq, Finset.sum_mul_sum]
    simp_rw [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hswap : ∑ r : Fin d, ∑ x ∈ B, ∑ s : Fin d, pd d σ x * (f (x r) * f (x s)) =
        ∑ r : Fin d, ∑ s : Fin d, ∑ x ∈ B, pd d σ x * (f (x r) * f (x s)) :=
      Finset.sum_congr rfl fun r _ => Finset.sum_comm
    rw [hswap]
    have hdiag : ∀ r : Fin d,
        (∑ s : Fin d, ∑ x ∈ B, pd d σ x * (f (x r) * f (x s))) ≤ (σ : ℝ) ^ 4 := by
      intro r
      have hoff : ∀ s : Fin d, s ≠ r →
          ∑ x ∈ B, pd d σ x * (f (x r) * f (x s)) = 0 := by
        intro s hsr
        rw [sum_box_pair d σ r s hsr.symm f f, hmean0, zero_mul]
      rw [Finset.sum_eq_single r (fun s _ hsr => hoff s hsr) (by simp)]
      have hsq : ∀ x : Fin d → ℤ, pd d σ x * (f (x r) * f (x r)) = pd d σ x * (f (x r)) ^ 2 := by
        intro x; ring
      simp_rw [hsq]
      rw [sum_box_single d σ r (fun a => (f a) ^ 2)]
      exact hsq_mean
    calc ∑ r : Fin d, ∑ s : Fin d, ∑ x ∈ B, pd d σ x * (f (x r) * f (x s))
        ≤ ∑ _r : Fin d, (σ : ℝ) ^ 4 := Finset.sum_le_sum fun r _ => hdiag r
      _ = (d : ℝ) * (σ : ℝ) ^ 4 := by simp
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hσpos : (0 : ℝ) < (σ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hv1_nn : 0 ≤ v1 σ := by nlinarith
  have hAc_bound : ((d : ℝ) / 2 * v1 σ) ^ 2 * (∑ x ∈ Ac, pd d σ x) ≤
      ∑ x ∈ B, pd d σ x * (normSq x - (d : ℝ) * v1 σ) ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ x ∈ Ac, ((d : ℝ) / 2 * v1 σ) ^ 2 * pd d σ x
        ≤ ∑ x ∈ Ac, pd d σ x * (normSq x - (d : ℝ) * v1 σ) ^ 2 := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hlt : normSq x < (d : ℝ) / 2 * v1 σ := not_le.mp (Finset.mem_filter.mp hx).2
          have hpos : 0 ≤ (d : ℝ) / 2 * v1 σ := mul_nonneg (by positivity) hv1_nn
          have hsq : ((d : ℝ) / 2 * v1 σ) ^ 2 ≤ (normSq x - (d : ℝ) * v1 σ) ^ 2 := by nlinarith
          nlinarith [pd_nonneg d σ x]
      _ ≤ ∑ x ∈ B, pd d σ x * (normSq x - (d : ℝ) * v1 σ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ B)
            (fun x _ _ => mul_nonneg (pd_nonneg d σ x) (sq_nonneg _))
  have hden_ge : (d : ℝ) ^ 2 * (σ : ℝ) ^ 4 / 324 ≤ ((d : ℝ) / 2 * v1 σ) ^ 2 := by
    have h1 : (d : ℝ) * (σ : ℝ) ^ 2 / 18 ≤ (d : ℝ) / 2 * v1 σ := by nlinarith
    have h2 : 0 ≤ (d : ℝ) * (σ : ℝ) ^ 2 / 18 := by positivity
    nlinarith
  have hAc_le : ∑ x ∈ Ac, pd d σ x ≤ 324 / (d : ℝ) := by
    have hnn : 0 ≤ ∑ x ∈ Ac, pd d σ x := Finset.sum_nonneg fun x _ => pd_nonneg d σ x
    have h1 : (d : ℝ) ^ 2 * (σ : ℝ) ^ 4 / 324 * (∑ x ∈ Ac, pd d σ x) ≤ (d : ℝ) * (σ : ℝ) ^ 4 := by
      calc (d : ℝ) ^ 2 * (σ : ℝ) ^ 4 / 324 * (∑ x ∈ Ac, pd d σ x)
          ≤ ((d : ℝ) / 2 * v1 σ) ^ 2 * (∑ x ∈ Ac, pd d σ x) :=
            mul_le_mul_of_nonneg_right hden_ge hnn
        _ ≤ (d : ℝ) * (σ : ℝ) ^ 4 := hAc_bound.trans hvar
    have hpos4 : (0 : ℝ) < (d : ℝ) * (σ : ℝ) ^ 4 := by positivity
    have h2 : (d : ℝ) / 324 * (∑ x ∈ Ac, pd d σ x) ≤ 1 := by
      have : (d : ℝ) * (σ : ℝ) ^ 4 * ((d : ℝ) / 324 * (∑ x ∈ Ac, pd d σ x)) ≤
          (d : ℝ) * (σ : ℝ) ^ 4 * 1 := by linarith
      exact le_of_mul_le_mul_left this hpos4
    rw [le_div_iff₀ hdpos]
    linarith
  linarith

private lemma sum_Icc_sin_eq_zero (σ : ℕ) (θ : ℝ) :
    ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * Real.sin (θ * (a : ℝ)) = 0 := by
  let I := Finset.Icc (-(σ : ℤ)) σ
  have hneg : ∑ a ∈ I, p1 σ a * Real.sin (θ * (a : ℝ)) =
      -(∑ a ∈ I, p1 σ a * Real.sin (θ * (a : ℝ))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun a _ => -a) ?_ ?_ ?_ ?_
    · intro a ha; rw [Finset.mem_Icc] at ha ⊢; omega
    · intro a _ b _ h; omega
    · intro a ha; exact ⟨-a, by rw [Finset.mem_Icc] at ha ⊢; omega, neg_neg a⟩
    · intro a _
      rw [p1_neg]
      simp [Real.sin_neg]
  linarith

private lemma sum_box_cos (d σ : ℕ) (α : ℝ) :
    ∀ x : Fin d → ℤ,
      ∑ y ∈ box d σ, pd d σ y * Real.cos (α * ip x y) =
        ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (α * (x r : ℝ) * (a : ℝ)) := by
  induction d with
  | zero =>
    intro x
    have hbox0 : box 0 σ = {Fin.elim0} := by
      ext y
      simp only [mem_box_iff, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ r => Fin.elim0 r⟩
    simp [hbox0, pd, ip]
  | succ d ih =>
    intro x
    rw [sum_box_succ]
    have hstep : ∀ (a : ℤ) (y' : Fin d → ℤ),
        pd (d + 1) σ (Fin.cons a y') * Real.cos (α * ip x (Fin.cons a y')) =
          p1 σ a * Real.cos (α * (x 0 : ℝ) * (a : ℝ)) *
            (pd d σ y' * Real.cos (α * ip (Fin.tail x) y')) -
          p1 σ a * Real.sin (α * (x 0 : ℝ) * (a : ℝ)) *
            (pd d σ y' * Real.sin (α * ip (Fin.tail x) y')) := by
      intro a y'
      have hpd : pd (d + 1) σ (Fin.cons a y') = p1 σ a * pd d σ y' := by
        simp [pd, Fin.prod_univ_succ]
      have hip : ip x (Fin.cons a y') = (x 0 : ℝ) * (a : ℝ) + ip (Fin.tail x) y' := by
        simp [ip, Fin.sum_univ_succ, Fin.tail]
      rw [hpd, hip, mul_add, Real.cos_add]
      ring
    simp_rw [hstep, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    rw [sum_Icc_sin_eq_zero σ (α * (x 0 : ℝ)), zero_mul, sub_zero]
    rw [ih (Fin.tail x), Fin.prod_univ_succ]
    rfl

private def fejer (N : ℕ) (h s : ℝ) : ℝ :=
  (∑ j ∈ Finset.range N, Real.cos ((j : ℝ) * h * s)) ^ 2 +
  (∑ j ∈ Finset.range N, Real.sin ((j : ℝ) * h * s)) ^ 2

private lemma fejer_nonneg (N : ℕ) (h s : ℝ) : 0 ≤ fejer N h s :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

private lemma fejer_expand (N : ℕ) (h s : ℝ) :
    fejer N h s = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      Real.cos (((j : ℝ) - (k : ℝ)) * h * s) := by
  unfold fejer
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ((j : ℝ) - (k : ℝ)) * h * s = (j : ℝ) * h * s - (k : ℝ) * h * s := by ring
  rw [h1, Real.cos_sub]

private lemma fejer_ge_of_small (N : ℕ) (h E s : ℝ) (hN : 1 ≤ N) (hE : 0 < E)
    (hh : h = 1 / ((N : ℝ) * E)) (hs : |s| ≤ E) :
    (N : ℝ) ^ 2 / 4 ≤ fejer N h s := by
  have hcos_sum : (N : ℝ) / 2 ≤ ∑ j ∈ Finset.range N, Real.cos ((j : ℝ) * h * s) := by
    calc (N : ℝ) / 2 = ∑ _j ∈ Finset.range N, (1 / 2 : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ j ∈ Finset.range N, Real.cos ((j : ℝ) * h * s) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjlt : (j : ℝ) < (N : ℝ) := Nat.cast_lt.mpr (Finset.mem_range.mp hj)
        have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
        have habs : |(j : ℝ) * h * s| ≤ 1 := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg j), hh,
            abs_of_pos (by positivity : (0 : ℝ) < 1 / ((N : ℝ) * E))]
          have h1 : (j : ℝ) * (1 / ((N : ℝ) * E)) * |s| ≤
              (N : ℝ) * (1 / ((N : ℝ) * E)) * E := by
            have hstep1 : (j : ℝ) * (1 / ((N : ℝ) * E)) ≤ (N : ℝ) * (1 / ((N : ℝ) * E)) :=
              mul_le_mul_of_nonneg_right hjlt.le (by positivity)
            exact mul_le_mul hstep1 hs (abs_nonneg s) (by positivity)
          have h2 : (N : ℝ) * (1 / ((N : ℝ) * E)) * E = 1 := by field_simp
          linarith
        exact (cos_bounds habs).1
  unfold fejer
  have hsq : ((N : ℝ) / 2) ^ 2 ≤ (∑ j ∈ Finset.range N, Real.cos ((j : ℝ) * h * s)) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  nlinarith [sq_nonneg (∑ j ∈ Finset.range N, Real.sin ((j : ℝ) * h * s))]

private lemma card_close_pairs (N T : ℕ) :
    ((Finset.range N ×ˢ Finset.range N).filter
      (fun (p : ℕ × ℕ) => |(p.1 : ℤ) - (p.2 : ℤ)| ≤ (T : ℤ))).card ≤ N * (2 * T + 1) := by
  have h1 : ∀ j ∈ Finset.range N,
      ((Finset.range N).filter (fun (k : ℕ) => |(j : ℤ) - (k : ℤ)| ≤ (T : ℤ))).card ≤ 2 * T + 1 := by
    intro j _
    have hsub : (Finset.range N).filter (fun (k : ℕ) => |(j : ℤ) - (k : ℤ)| ≤ (T : ℤ)) ⊆
        Finset.Icc (j - T) (j + T) := by
      intro k hk
      have h2 := (Finset.mem_filter.mp hk).2
      rw [abs_le] at h2
      rw [Finset.mem_Icc]
      omega
    calc ((Finset.range N).filter (fun (k : ℕ) => |(j : ℤ) - (k : ℤ)| ≤ (T : ℤ))).card
        ≤ (Finset.Icc (j - T) (j + T)).card := Finset.card_le_card hsub
      _ = j + T + 1 - (j - T) := Nat.card_Icc (j - T) (j + T)
      _ ≤ 2 * T + 1 := by omega
  have hcard : ((Finset.range N ×ˢ Finset.range N).filter
      (fun (p : ℕ × ℕ) => |(p.1 : ℤ) - (p.2 : ℤ)| ≤ (T : ℤ))).card =
      ∑ j ∈ Finset.range N,
        ((Finset.range N).filter (fun (k : ℕ) => |(j : ℤ) - (k : ℤ)| ≤ (T : ℤ))).card := by
    simp only [Finset.card_filter, Finset.sum_product]
  rw [hcard]
  calc ∑ j ∈ Finset.range N,
        ((Finset.range N).filter (fun (k : ℕ) => |(j : ℤ) - (k : ℤ)| ≤ (T : ℤ))).card
      ≤ ∑ _j ∈ Finset.range N, (2 * T + 1) := Finset.sum_le_sum h1
    _ = N * (2 * T + 1) := by simp

private lemma fejer_anticoncentration
    (d σ N : ℕ) (ε C0 η : ℝ)
    (hd : 1 ≤ d) (hσ : 1 ≤ σ) (hN : 1 ≤ N)
    (hε : 0 < ε) (hC0 : 0 < C0) (hη : 0 < η)
    (hsmall : 9 ≤ ε * Real.sqrt (d : ℝ))
    (hC0_bd : 4 * Real.exp (-(C0 ^ 2) / 6) ≤ η / 4)
    (hε_bd : 8 * C0 * ε ≤ η / 4)
    (hN_bd : 12 / (N : ℝ) ≤ η / 4)
    (x : Fin d → ℤ) (hx_box : x ∈ box d σ)
    (hx_norm : (d : ℝ) / 2 * v1 σ ≤ normSq x) :
    let E := ε * v1 σ * Real.sqrt (d : ℝ)
    ∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y ≤ η := by
  intro E
  obtain ⟨hv1_lo, _, _⟩ := v1_bounds σ hσ
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hσpos : (0 : ℝ) < (σ : ℝ) := Nat.cast_pos.mpr (by omega)
  have hv1_pos : 0 < v1 σ := by nlinarith
  have hE_pos : 0 < E := by positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  let h : ℝ := 1 / ((N : ℝ) * E)
  have hh_pos : 0 < h := by dsimp [h]; positivity
  have hmarkov : (N : ℝ) ^ 2 / 4 *
      (∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y) ≤
      ∑ y ∈ box d σ, pd d σ y * fejer N h (ip x y) := by
    rw [Finset.mul_sum]
    calc ∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), (N : ℝ) ^ 2 / 4 * pd d σ y
        ≤ ∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y * fejer N h (ip x y) := by
          refine Finset.sum_le_sum fun y hy => ?_
          have hfe := fejer_ge_of_small N h E (ip x y) hN hE_pos rfl (Finset.mem_filter.mp hy).2
          nlinarith [pd_nonneg d σ y]
      _ ≤ ∑ y ∈ box d σ, pd d σ y * fejer N h (ip x y) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun y _ _ => mul_nonneg (pd_nonneg d σ y) (fejer_nonneg N h (ip x y)))
  have hexp_fejer : ∑ y ∈ box d σ, pd d σ y * fejer N h (ip x y) =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ)) := by
    simp_rw [fejer_expand, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact sum_box_cos d σ (((j : ℝ) - (k : ℝ)) * h) x
  have hterm_le : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range N,
      (∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
        p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ))) ≤
      Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) := by
    intro j hj k hk
    have hjk_lt : |(j : ℝ) - (k : ℝ)| ≤ (N : ℝ) := by
      have hj' : (j : ℝ) < (N : ℝ) := Nat.cast_lt.mpr (Finset.mem_range.mp hj)
      have hk' : (k : ℝ) < (N : ℝ) := Nat.cast_lt.mpr (Finset.mem_range.mp hk)
      rw [abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j, Nat.cast_nonneg (α := ℝ) k]
    have hcoord : ∀ r : Fin d,
        0 ≤ ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ)) ∧
        (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ))) ≤
        Real.exp (-(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)) ^ 2) := by
      intro r
      have hxr : |(x r : ℝ)| ≤ (σ : ℝ) := by
        have h1 := mem_box_iff.mp hx_box r
        rw [abs_le]
        exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
      have hang_le : ∀ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          |((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ)| ≤ 1 := by
        intro a ha
        have ha_le : |(a : ℝ)| ≤ (σ : ℝ) := by
          rw [Finset.mem_Icc] at ha
          rw [abs_le]
          exact ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hh_pos]
        have hstep1 : |(j : ℝ) - (k : ℝ)| * h * |(x r : ℝ)| * |(a : ℝ)| ≤
            (N : ℝ) * h * (σ : ℝ) * (σ : ℝ) := by
          have hA : |(j : ℝ) - (k : ℝ)| * h ≤ (N : ℝ) * h :=
            mul_le_mul_of_nonneg_right hjk_lt hh_pos.le
          have hB : |(j : ℝ) - (k : ℝ)| * h * |(x r : ℝ)| ≤ (N : ℝ) * h * (σ : ℝ) :=
            mul_le_mul hA hxr (abs_nonneg _) (mul_nonneg hNpos.le hh_pos.le)
          exact mul_le_mul hB ha_le (abs_nonneg _) (mul_nonneg (mul_nonneg hNpos.le hh_pos.le) hσpos.le)
        have hstep2 : (N : ℝ) * h * (σ : ℝ) * (σ : ℝ) = (σ : ℝ) ^ 2 / E := by
          dsimp [h]; field_simp
        have hstep3 : (σ : ℝ) ^ 2 / E ≤ 1 := by
          rw [div_le_one hE_pos]
          dsimp [E]
          have h9 : (σ : ℝ) ^ 2 ≤ 9 * v1 σ := by linarith
          calc (σ : ℝ) ^ 2 ≤ 9 * v1 σ := h9
            _ ≤ (ε * Real.sqrt (d : ℝ)) * v1 σ := mul_le_mul_of_nonneg_right hsmall hv1_pos.le
            _ = ε * v1 σ * Real.sqrt (d : ℝ) := by ring
        linarith
      constructor
      · refine Finset.sum_nonneg fun a ha => mul_nonneg (p1_nonneg σ a) ?_
        linarith [(cos_bounds (hang_le a ha)).1]
      · let θ := ((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)
        have hsum_le : ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * Real.cos (θ * (a : ℝ)) ≤
            1 - (v1 σ / 3) * θ ^ 2 := by
          calc ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * Real.cos (θ * (a : ℝ))
              ≤ ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (1 - (θ * (a : ℝ)) ^ 2 / 3) :=
                Finset.sum_le_sum fun a ha =>
                  mul_le_mul_of_nonneg_left (cos_bounds (hang_le a ha)).2 (p1_nonneg σ a)
            _ = (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a) -
                (θ ^ 2 / 3) * (∑ a ∈ Finset.Icc (-(σ : ℤ)) σ, p1 σ a * (a : ℝ) ^ 2) := by
                have hrew : ∀ a : ℤ,
                    p1 σ a * (1 - (θ * (a : ℝ)) ^ 2 / 3) =
                      p1 σ a - (θ ^ 2 / 3) * (p1 σ a * (a : ℝ) ^ 2) := by intro a; ring
                simp_rw [hrew, Finset.sum_sub_distrib, ← Finset.mul_sum]
            _ = 1 - (v1 σ / 3) * θ ^ 2 := by
                rw [sum_p1 σ]; unfold v1; ring
        have hexp_le : 1 - (v1 σ / 3) * θ ^ 2 ≤ Real.exp (-(v1 σ / 3) * θ ^ 2) := by
          linarith [Real.add_one_le_exp (-(v1 σ / 3) * θ ^ 2)]
        exact hsum_le.trans hexp_le
    calc ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
          p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ))
        ≤ ∏ r : Fin d, Real.exp (-(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)) ^ 2) :=
          Finset.prod_le_prod (fun r _ => (hcoord r).1) (fun r _ => (hcoord r).2)
      _ = Real.exp (∑ r : Fin d, -(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)) ^ 2) :=
          (Real.exp_sum _ _).symm
      _ ≤ Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) := by
          apply Real.exp_le_exp.mpr
          have hsum_eq : ∑ r : Fin d, -(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ)) ^ 2 =
              -(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * normSq x := by
            unfold normSq
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => by ring
          rw [hsum_eq]
          have hcoeff : 0 ≤ (v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) := by positivity
          have h1 : (v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * ((d : ℝ) / 2 * v1 σ) ≤
              (v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * normSq x :=
            mul_le_mul_of_nonneg_left hx_norm hcoeff
          have h2 : (v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * ((d : ℝ) / 2 * v1 σ) =
              ((j : ℝ) - (k : ℝ)) ^ 2 / (6 * (N : ℝ) ^ 2 * ε ^ 2) := by
            have hEsq : E ^ 2 = ε ^ 2 * (v1 σ) ^ 2 * (d : ℝ) := by
              dsimp [E]
              rw [mul_pow, mul_pow, Real.sq_sqrt hdpos.le]
            have hhsq : h ^ 2 = 1 / ((N : ℝ) ^ 2 * E ^ 2) := by
              dsimp [h]; field_simp
            rw [hhsq, hEsq]
            field_simp [hNpos.ne', hε.ne', hv1_pos.ne', hdpos.ne']
            ring
          have hneg1 : -(v1 σ / 3) * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * normSq x =
              -(v1 σ / 3 * (((j : ℝ) - (k : ℝ)) ^ 2 * h ^ 2) * normSq x) := by ring
          have hneg2 : -(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2) =
              -(((j : ℝ) - (k : ℝ)) ^ 2 / (6 * (N : ℝ) ^ 2 * ε ^ 2)) := by ring
          linarith
  let T : ℕ := Nat.ceil (C0 * (N : ℝ) * ε)
  have hT_ge : C0 * (N : ℝ) * ε ≤ (T : ℝ) := Nat.le_ceil _
  have hT_lt : (T : ℝ) < C0 * (N : ℝ) * ε + 1 := Nat.ceil_lt_add_one (by positivity)
  let P := Finset.range N ×ˢ Finset.range N
  let Pclose := P.filter (fun (p : ℕ × ℕ) => |(p.1 : ℤ) - (p.2 : ℤ)| ≤ (T : ℤ))
  let Pfar := P.filter (fun (p : ℕ × ℕ) => ¬ (|(p.1 : ℤ) - (p.2 : ℤ)| ≤ (T : ℤ)))
  have hdouble_le : ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) ≤
      (N : ℝ) * (2 * (T : ℝ) + 1) + (N : ℝ) ^ 2 * Real.exp (-(C0 ^ 2) / 6) := by
    rw [← Finset.sum_product']
    rw [← Finset.sum_filter_add_sum_filter_not P (fun (p : ℕ × ℕ) => |(p.1 : ℤ) - (p.2 : ℤ)| ≤ (T : ℤ))]
    have hclose_sum : ∑ p ∈ Pclose,
        Real.exp (-(((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) ≤
        (N : ℝ) * (2 * (T : ℝ) + 1) := by
      calc ∑ p ∈ Pclose,
            Real.exp (-(((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2))
          ≤ ∑ _p ∈ Pclose, (1 : ℝ) := by
            refine Finset.sum_le_sum fun p _ => ?_
            rw [Real.exp_le_one_iff]
            exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
        _ = (Pclose.card : ℝ) := by simp
        _ ≤ (N : ℝ) * (2 * (T : ℝ) + 1) := by
            have hcard_le : Pclose.card ≤ N * (2 * T + 1) := card_close_pairs N T
            exact_mod_cast hcard_le
    have hfar_sum : ∑ p ∈ Pfar,
        Real.exp (-(((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) ≤
        (N : ℝ) ^ 2 * Real.exp (-(C0 ^ 2) / 6) := by
      calc ∑ p ∈ Pfar,
            Real.exp (-(((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2))
          ≤ ∑ _p ∈ Pfar, Real.exp (-(C0 ^ 2) / 6) := by
            refine Finset.sum_le_sum fun p hp => ?_
            apply Real.exp_le_exp.mpr
            have hgt : (T : ℤ) < |(p.1 : ℤ) - (p.2 : ℤ)| := not_le.mp (Finset.mem_filter.mp hp).2
            have hgtR : (T : ℝ) < |(p.1 : ℝ) - (p.2 : ℝ)| := by
              rcases lt_abs.mp hgt with hlt | hlt
              · exact lt_abs.mpr (Or.inl (by exact_mod_cast hlt))
              · exact lt_abs.mpr (Or.inr (by exact_mod_cast hlt))
            have hsq : (C0 * (N : ℝ) * ε) ^ 2 ≤ ((p.1 : ℝ) - (p.2 : ℝ)) ^ 2 := by
              have h1 : C0 * (N : ℝ) * ε ≤ |(p.1 : ℝ) - (p.2 : ℝ)| := hT_ge.trans hgtR.le
              have h2 : (C0 * (N : ℝ) * ε) ^ 2 ≤ |(p.1 : ℝ) - (p.2 : ℝ)| ^ 2 := by
                nlinarith [mul_nonneg (mul_nonneg hC0.le hNpos.le) hε.le]
              rwa [sq_abs] at h2
            have hden : 0 < 6 * (N : ℝ) ^ 2 * ε ^ 2 := by positivity
            have hrew : -(C0 ^ 2) / 6 = -((C0 * (N : ℝ) * ε) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2) := by
              field_simp [hNpos.ne', hε.ne']
            rw [hrew]
            exact div_le_div_of_nonneg_right (neg_le_neg hsq) hden.le
        _ = (Pfar.card : ℝ) * Real.exp (-(C0 ^ 2) / 6) := by simp
        _ ≤ (P.card : ℝ) * Real.exp (-(C0 ^ 2) / 6) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            exact_mod_cast Finset.card_le_card (Finset.filter_subset _ P)
        _ = (N : ℝ) ^ 2 * Real.exp (-(C0 ^ 2) / 6) := by
            simp [P, sq]
    linarith
  have htotal : (N : ℝ) ^ 2 / 4 *
      (∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y) ≤
      (N : ℝ) * (2 * (T : ℝ) + 1) + (N : ℝ) ^ 2 * Real.exp (-(C0 ^ 2) / 6) := by
    calc (N : ℝ) ^ 2 / 4 * (∑ y ∈ (box d σ).filter (fun y => |ip x y| ≤ E), pd d σ y)
        ≤ ∑ y ∈ box d σ, pd d σ y * fejer N h (ip x y) := hmarkov
      _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
            ∏ r : Fin d, ∑ a ∈ Finset.Icc (-(σ : ℤ)) σ,
              p1 σ a * Real.cos (((j : ℝ) - (k : ℝ)) * h * (x r : ℝ) * (a : ℝ)) := hexp_fejer
      _ ≤ ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
            Real.exp (-(((j : ℝ) - (k : ℝ)) ^ 2) / (6 * (N : ℝ) ^ 2 * ε ^ 2)) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hterm_le j hj k hk
      _ ≤ (N : ℝ) * (2 * (T : ℝ) + 1) + (N : ℝ) ^ 2 * Real.exp (-(C0 ^ 2) / 6) := hdouble_le
  have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 / 4 := by positivity
  have hrhs_le : (N : ℝ) * (2 * (T : ℝ) + 1) + (N : ℝ) ^ 2 * Real.exp (-(C0 ^ 2) / 6) ≤
      ((N : ℝ) ^ 2 / 4) * η := by
    have h1 : 4 * (N : ℝ) * (2 * (T : ℝ) + 1) ≤ (N : ℝ) ^ 2 * (8 * C0 * ε + 12 / (N : ℝ)) := by
      have hT1 : 2 * (T : ℝ) + 1 ≤ 2 * C0 * (N : ℝ) * ε + 3 := by linarith
      have h2 := mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ 4 * (N : ℝ))
      have h3 : (N : ℝ) ^ 2 * (8 * C0 * ε + 12 / (N : ℝ)) =
          4 * (N : ℝ) * (2 * C0 * (N : ℝ) * ε + 3) := by
        field_simp [hNpos.ne']; ring
      linarith
    have h2 : 4 * (N : ℝ) ^ 2 * Real.exp (-(C0 ^ 2) / 6) ≤ (N : ℝ) ^ 2 * (η / 4) := by
      have := mul_le_mul_of_nonneg_left hC0_bd (sq_nonneg (N : ℝ))
      linarith
    have h3 : (N : ℝ) ^ 2 * (8 * C0 * ε + 12 / (N : ℝ)) ≤ (N : ℝ) ^ 2 * (η / 2) := by
      refine mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg (N : ℝ))
    nlinarith [sq_nonneg (N : ℝ), hη]
  nlinarith

private lemma discrete_gaussian_indep_bound (d : ℕ) (hd : 1 ≤ d) (C : ℝ) (_hC : 0 ≤ C)
    (I : Finset (Fin d → ℤ)) (hI_sub : I ⊆ box d d)
    (hI_sep : ∀ x ∈ I, ∀ y ∈ I, 4 * C ^ 2 < normSq (x + y)) :
    ∑ x ∈ I, pd d d x ≤ Real.exp (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) := by
  let f : (Fin d → ℤ) → ℝ := fun x =>
    if x ∈ I then Real.exp (-normSq x / (2 * (d : ℝ) ^ 2)) else 0
  let g : (Fin d → ℤ) → ℝ := fun y =>
    if -y ∈ I then Real.exp (-normSq y / (2 * (d : ℝ) ^ 2)) else 0
  let h : (Fin d → ℤ) → ℝ := fun z =>
    Real.exp (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) *
      Real.exp (-normSq z / (2 * (d : ℝ) ^ 2))
  have hf : ∀ x, 0 ≤ f x := fun x => by dsimp [f]; split_ifs <;> positivity
  have hg : ∀ y, 0 ≤ g y := fun y => by dsimp [g]; split_ifs <;> positivity
  have hh : ∀ z, 0 ≤ h z := fun z => by dsimp [h]; positivity
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hpl : ∀ x ∈ box d d, ∀ y ∈ box d d, ∀ z ∈ box d d,
      (∀ r : Fin d, |x r + y r - 2 * z r| ≤ 1) → Real.sqrt (f x * g y) ≤ h z := by
    intro x _ y _ z hz hclose
    by_cases hxin : x ∈ I
    · by_cases hyin : -y ∈ I
      · simp only [f, g, h, hxin, hyin, ↓reduceIte]
        rw [← Real.exp_add, ← Real.exp_half, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hsep : 4 * C ^ 2 < normSq (x + (-y)) := hI_sep x hxin (-y) hyin
        have hcoord : ∀ r : Fin d,
            (x r : ℝ) ^ 2 + (y r : ℝ) ^ 2 ≥
              2 * (z r : ℝ) ^ 2 + ((x r : ℝ) - (y r : ℝ)) ^ 2 / 2 - 2 * (d : ℝ) := by
          intro r
          let e : ℝ := (x r : ℝ) + (y r : ℝ) - 2 * (z r : ℝ)
          have he : |e| ≤ 1 := by
            have h1 := abs_le.mp (hclose r)
            rw [abs_le]
            exact ⟨by dsimp [e]; exact_mod_cast h1.1, by dsimp [e]; exact_mod_cast h1.2⟩
          have hzr : |(z r : ℝ)| ≤ (d : ℝ) := by
            have h1 := mem_box_iff.mp hz r
            rw [abs_le]
            exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
          have hcross : -(d : ℝ) ≤ (z r : ℝ) * e := by
            have h1 : |(z r : ℝ) * e| ≤ (d : ℝ) := by
              rw [abs_mul]
              calc |(z r : ℝ)| * |e| ≤ (d : ℝ) * 1 :=
                mul_le_mul hzr he (abs_nonneg _) hdpos.le
                _ = (d : ℝ) := mul_one _
            exact (abs_le.mp h1).1
          have hid : (x r : ℝ) ^ 2 + (y r : ℝ) ^ 2 =
              2 * (z r : ℝ) ^ 2 + ((x r : ℝ) - (y r : ℝ)) ^ 2 / 2 +
              2 * ((z r : ℝ) * e) + e ^ 2 / 2 := by
            dsimp [e]; ring
          nlinarith [sq_nonneg e]
        have hsum_norm : normSq x + normSq y ≥
            2 * normSq z + normSq (x + (-y)) / 2 - 2 * (d : ℝ) ^ 2 := by
          have h1 : ∑ r : Fin d, ((x r : ℝ) ^ 2 + (y r : ℝ) ^ 2) ≥
              ∑ r : Fin d, (2 * (z r : ℝ) ^ 2 + ((x r : ℝ) - (y r : ℝ)) ^ 2 / 2 - 2 * (d : ℝ)) :=
            Finset.sum_le_sum fun r _ => hcoord r
          have hL : ∑ r : Fin d, ((x r : ℝ) ^ 2 + (y r : ℝ) ^ 2) = normSq x + normSq y := by
            simp only [normSq, Finset.sum_add_distrib]
          have hR : ∑ r : Fin d,
              (2 * (z r : ℝ) ^ 2 + ((x r : ℝ) - (y r : ℝ)) ^ 2 / 2 - 2 * (d : ℝ)) =
              2 * normSq z + normSq (x + (-y)) / 2 - 2 * (d : ℝ) ^ 2 := by
            simp only [normSq, Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg,
              Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have hsub : ∀ r : Fin d, ((x r : ℝ) + -(y r : ℝ)) ^ 2 = ((x r : ℝ) - (y r : ℝ)) ^ 2 := by
              intro r; ring
            simp_rw [hsub]; ring
          linarith
        have hden : 0 < 4 * (d : ℝ) ^ 2 := by positivity
        have hmain : -(normSq x + normSq y) / (4 * (d : ℝ) ^ 2) ≤
            (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) + (-normSq z / (2 * (d : ℝ) ^ 2)) := by
          have h1 : 2 * normSq z + 2 * C ^ 2 - 2 * (d : ℝ) ^ 2 ≤ normSq x + normSq y := by linarith
          have h2 : -(normSq x + normSq y) / (4 * (d : ℝ) ^ 2) ≤
              -(2 * normSq z + 2 * C ^ 2 - 2 * (d : ℝ) ^ 2) / (4 * (d : ℝ) ^ 2) :=
            div_le_div_of_nonneg_right (by linarith) hden.le
          have h3 : -(2 * normSq z + 2 * C ^ 2 - 2 * (d : ℝ) ^ 2) / (4 * (d : ℝ) ^ 2) =
              (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) + (-normSq z / (2 * (d : ℝ) ^ 2)) := by
            field_simp [hdpos.ne']; ring
          linarith
        have hrew : (-normSq x / (2 * (d : ℝ) ^ 2) + -normSq y / (2 * (d : ℝ) ^ 2)) / 2 =
            -(normSq x + normSq y) / (4 * (d : ℝ) ^ 2) := by ring
        linarith
      · simp [g, hyin]; exact hh z
    · simp [f, hxin]; exact hh z
  have hpl_res := discrete_PL_nd d d f g h hf hg hh hpl
  have hf_sum : ∑ x ∈ box d d, f x = ∑ x ∈ I, Real.exp (-normSq x / (2 * (d : ℝ) ^ 2)) := by
    simp only [f, ← Finset.sum_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun hx => hx.2, fun hx => ⟨hI_sub hx, hx⟩⟩
  have hg_sum : ∑ y ∈ box d d, g y = ∑ x ∈ I, Real.exp (-normSq x / (2 * (d : ℝ) ^ 2)) := by
    rw [← hf_sum]
    refine Finset.sum_bij (fun y _ => -y) ?_ ?_ ?_ ?_
    · intro y hy
      rw [mem_box_iff] at hy ⊢
      intro r; have := hy r; simp only [Pi.neg_apply]; omega
    · intro a _ b _ hab; exact neg_inj.mp hab
    · intro x hx
      refine ⟨-x, ?_, neg_neg x⟩
      rw [mem_box_iff] at hx ⊢
      intro r; have := hx r; simp only [Pi.neg_apply]; omega
    · intro y _
      simp [f, g, normSq_neg]
  have hh_sum : ∑ z ∈ box d d, h z =
      Real.exp (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) *
        ∑ z ∈ box d d, Real.exp (-normSq z / (2 * (d : ℝ) ^ 2)) := by
    simp only [h, ← Finset.mul_sum]
  rw [hf_sum, hg_sum, hh_sum, Real.sqrt_mul_self (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)]
    at hpl_res
  have hZd_pos : 0 < (Z1 d) ^ d := pow_pos (Z1_pos d) d
  have hZd_eq : ∑ z ∈ box d d, Real.exp (-normSq z / (2 * (d : ℝ) ^ 2)) = (Z1 d) ^ d := by
    have h1 := sum_box_pd d d
    simp_rw [pd_eq_exp_div, ← Finset.sum_div] at h1
    exact (div_eq_one_iff_eq hZd_pos.ne').mp h1
  rw [hZd_eq] at hpl_res
  have hI_pd : ∑ x ∈ I, pd d d x =
      (∑ x ∈ I, Real.exp (-normSq x / (2 * (d : ℝ) ^ 2))) / (Z1 d) ^ d := by
    simp_rw [pd_eq_exp_div, ← Finset.sum_div]
  rw [hI_pd, div_le_iff₀ hZd_pos]
  exact hpl_res

/- ### Module 4: Final assembly proving `H1` -/

private lemma exists_graph_H1 :
    OMA.R_Erdos22_erdos_22_variants_bollobas_erdos_lower_R1.H1 := by
  intro η_raw δ_raw hη_raw hδ_raw
  let η := min η_raw (1 / 4)
  let δ := min δ_raw 1
  have hη : 0 < η := lt_min hη_raw (by norm_num)
  have hη4 : η ≤ 1 / 4 := min_le_right _ _
  have hη_le : η ≤ η_raw := min_le_left _ _
  have hδ : 0 < δ := lt_min hδ_raw (by norm_num)
  have hδ_le : δ ≤ δ_raw := min_le_left _ _
  -- Step 1: Choose C0 > 0 so 4 * exp(-C0^2 / 6) ≤ (η/2) / 4 = η / 8
  obtain ⟨C0_nat, hC0_nat⟩ := exists_nat_ge (Real.sqrt (6 * Real.log (32 / η)) + 1)
  let C0 : ℝ := (C0_nat : ℝ)
  have hC0_pos : 0 < C0 := by
    have : 0 ≤ Real.sqrt (6 * Real.log (32 / η)) := Real.sqrt_nonneg _
    dsimp [C0]; linarith
  have hC0_bd : 4 * Real.exp (-(C0 ^ 2) / 6) ≤ (η / 2) / 4 := by
    have h32 : 1 ≤ 32 / η := by rw [one_le_div hη]; linarith
    have hlog_nn : 0 ≤ 6 * Real.log (32 / η) := mul_nonneg (by norm_num) (Real.log_nonneg h32)
    have hsq : 6 * Real.log (32 / η) ≤ C0 ^ 2 := by
      have h1 : Real.sqrt (6 * Real.log (32 / η)) ≤ C0 := by dsimp [C0]; linarith
      calc 6 * Real.log (32 / η)
          = (Real.sqrt (6 * Real.log (32 / η))) ^ 2 := (Real.sq_sqrt hlog_nn).symm
        _ ≤ C0 ^ 2 := by nlinarith [Real.sqrt_nonneg (6 * Real.log (32 / η))]
    have hexp : Real.exp (-(C0 ^ 2) / 6) ≤ η / 32 := by
      have h1 : Real.exp (-(C0 ^ 2) / 6) ≤ Real.exp (-Real.log (32 / η)) := by
        apply Real.exp_le_exp.mpr; linarith
      have h2 : Real.exp (-Real.log (32 / η)) = η / 32 := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 32 / η)]
        field_simp
      linarith
    linarith
  -- Step 2: Choose ε > 0 so 8 * C0 * ε ≤ (η / 2) / 4 = η / 8
  let ε : ℝ := η / (64 * C0)
  have hε_pos : 0 < ε := by positivity
  have hε_bd : 8 * C0 * ε ≤ (η / 2) / 4 := by
    dsimp [ε]; field_simp [hC0_pos.ne']; linarith
  -- Step 3: Choose N ≥ 1 so 12 / N ≤ (η / 2) / 4 = η / 8
  obtain ⟨N, hN⟩ := exists_nat_ge (96 / η + 1)
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := by
      have : 0 ≤ 96 / η := by positivity
      linarith
    exact Nat.one_le_cast.mp this
  have hN_bd : 12 / (N : ℝ) ≤ (η / 2) / 4 := by
    have h1 : 96 / η ≤ (N : ℝ) := by linarith
    have h2 : 96 ≤ (N : ℝ) * η := (div_le_iff₀ hη).mp h1
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [div_le_iff₀ hNpos]
    linarith
  -- Step 4: Choose d ≥ 1 large enough for all 4 constraints
  let L_ind := max 0 (1 / 2 + Real.log (4 / δ))
  let D_req := max (max 650 ((18 * ε + 1) ^ 2))
    (max ((9 / ε + 1) ^ 2) ((18 / ε * L_ind + 1) ^ 2))
  obtain ⟨d, hd_ge⟩ := exists_nat_ge (D_req + 1)
  have hd_ge_650 : (650 : ℝ) ≤ (d : ℝ) := by
    have : (650 : ℝ) ≤ D_req := le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  have hd1 : 1 ≤ d := by
    have : (1 : ℝ) ≤ (d : ℝ) := by linarith
    exact Nat.one_le_cast.mp this
  have hdpos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsqrt_d_1 : 18 * ε < Real.sqrt (d : ℝ) := by
    have h1 : (18 * ε + 1) ^ 2 < (d : ℝ) := by
      have : (18 * ε + 1) ^ 2 ≤ D_req := le_trans (le_max_right _ _) (le_max_left _ _)
      linarith
    have h2 : 18 * ε + 1 < Real.sqrt (d : ℝ) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 18 * ε + 1)]
      exact Real.sqrt_lt_sqrt (by positivity) h1
    linarith
  have hsqrt_d_2 : 9 ≤ ε * Real.sqrt (d : ℝ) := by
    have h1 : (9 / ε + 1) ^ 2 ≤ (d : ℝ) := by
      have : (9 / ε + 1) ^ 2 ≤ D_req := le_trans (le_max_left _ _) (le_max_right _ _)
      linarith
    have h2 : 9 / ε + 1 ≤ Real.sqrt (d : ℝ) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 9 / ε + 1)]
      exact Real.sqrt_le_sqrt h1
    have h3 : 9 / ε ≤ Real.sqrt (d : ℝ) := by linarith
    have h4 : 9 ≤ Real.sqrt (d : ℝ) * ε := (div_le_iff₀ hε_pos).mp h3
    linarith
  have hsqrt_d_3 : 18 / ε * L_ind ≤ Real.sqrt (d : ℝ) := by
    have h1 : (18 / ε * L_ind + 1) ^ 2 ≤ (d : ℝ) := by
      have : (18 / ε * L_ind + 1) ^ 2 ≤ D_req := le_trans (le_max_right _ _) (le_max_right _ _)
      linarith
    have h2 : 18 / ε * L_ind + 1 ≤ Real.sqrt (d : ℝ) := by
      have hLnn : 0 ≤ L_ind := le_max_left _ _
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 18 / ε * L_ind + 1)]
      exact Real.sqrt_le_sqrt h1
    linarith
  -- Step 5: Define shell A, weights w, thresholds E, C
  obtain ⟨hv1_lo, hv1_hi, _⟩ := v1_bounds d hd1
  have hv1_pos : 0 < v1 d := by nlinarith
  let E : ℝ := ε * v1 d * Real.sqrt (d : ℝ)
  have hE_pos : 0 < E := by positivity
  let C : ℝ := Real.sqrt E
  have hC_nn : 0 ≤ C := Real.sqrt_nonneg E
  have hC_sq : C ^ 2 = E := Real.sq_sqrt hE_pos.le
  let A : Finset (Fin d → ℤ) := (box d d).filter (fun x => (d : ℝ) / 2 * v1 d ≤ normSq x)
  let pA : ℝ := ∑ x ∈ A, pd d d x
  have hpA_ge : 1 / 2 ≤ pA := by
    have hcheb := chebyshev_shell d d hd1 hd1
    have h324 : 324 / (d : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hdpos]; linarith
    linarith
  have hpA_pos : 0 < pA := by linarith
  let w : (Fin d → ℤ) → ℝ := fun x => pd d d x / pA
  have hw0 : ∀ x ∈ A, 0 ≤ w x := fun x _ => div_nonneg (pd_nonneg d d x) hpA_pos.le
  have hw1 : ∑ x ∈ A, w x = 1 := by
    simp only [w, ← Finset.sum_div]
    exact div_self hpA_pos.ne'
  have hnorm : ∀ x ∈ A, 9 * C ^ 2 < normSq x := by
    intro x hx
    have hx_n : (d : ℝ) / 2 * v1 d ≤ normSq x := (Finset.mem_filter.mp hx).2
    rw [hC_sq]
    dsimp [E]
    have h1 : 9 * (ε * v1 d * Real.sqrt (d : ℝ)) < (d : ℝ) / 2 * v1 d := by
      have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hdpos.le
      have h2 : 18 * ε * Real.sqrt (d : ℝ) < (d : ℝ) := by
        have := mul_lt_mul_of_pos_right hsqrt_d_1 (Real.sqrt_pos.mpr hdpos)
        linarith
      nlinarith
    linarith
  have hind : ∀ I ⊆ A, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → 4 * C ^ 2 < normSq (x + y)) →
      ∑ x ∈ I, w x ≤ δ / 2 := by
    intro I hIA hIsep
    have hI_all : ∀ x ∈ I, ∀ y ∈ I, 4 * C ^ 2 < normSq (x + y) := by
      intro x hx y hy
      by_cases hxy : x = y
      · subst hxy
        have hnx : 9 * C ^ 2 < normSq x := hnorm x (hIA hx)
        have h2x : normSq (x + x) = 4 * normSq x := by
          simp only [normSq, Pi.add_apply, Int.cast_add, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => by ring
        rw [h2x]
        linarith [sq_nonneg C]
      · exact hIsep x hx y hy hxy
    have hI_box : I ⊆ box d d := hIA.trans (Finset.filter_subset _ _)
    have hpl := discrete_gaussian_indep_bound d hd1 C hC_nn I hI_box hI_all
    have hexp_le : Real.exp (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) ≤ δ / 4 := by
      have h1 : (ε / 18) * Real.sqrt (d : ℝ) ≤ C ^ 2 / (2 * (d : ℝ) ^ 2) := by
        rw [hC_sq]
        dsimp [E]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (d : ℝ) ^ 2)]
        have h2 : (ε / 18) * (2 * (d : ℝ) ^ 2) ≤ ε * v1 d := by nlinarith
        have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (d : ℝ))
        linarith
      have h2 : L_ind ≤ (ε / 18) * Real.sqrt (d : ℝ) := by
        have := mul_le_mul_of_nonneg_left hsqrt_d_3 (by positivity : 0 ≤ ε / 18)
        have hrew : (ε / 18) * (18 / ε * L_ind) = L_ind := by field_simp [hε_pos.ne']
        linarith
      have h3 : 1 / 2 + Real.log (4 / δ) ≤ L_ind := le_max_right _ _
      have h4 : 1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2) ≤ -Real.log (4 / δ) := by linarith
      calc Real.exp (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2))
          ≤ Real.exp (-Real.log (4 / δ)) := Real.exp_le_exp.mpr h4
        _ = δ / 4 := by
          rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 4 / δ)]
          field_simp
    have hsum_w : ∑ x ∈ I, w x = (∑ x ∈ I, pd d d x) / pA := by
      simp only [w, ← Finset.sum_div]
    rw [hsum_w, div_le_iff₀ hpA_pos]
    calc ∑ x ∈ I, pd d d x ≤ Real.exp (1 / 2 - C ^ 2 / (2 * (d : ℝ) ^ 2)) := hpl
      _ ≤ δ / 4 := hexp_le
      _ = (δ / 2) * (1 / 2) := by ring
      _ ≤ (δ / 2) * pA := mul_le_mul_of_nonneg_left hpA_ge (by positivity)
  have hcross : 1 / 2 - η ≤ ∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0 := by
    have hper_x : ∀ x ∈ A, 1 / 2 - η ≤ ∑ y ∈ A, if E < ip x y then w y else 0 := by
      intro x hx
      have hx_box : x ∈ box d d := (Finset.mem_filter.mp hx).1
      have hx_norm : (d : ℝ) / 2 * v1 d ≤ normSq x := (Finset.mem_filter.mp hx).2
      have hfejer := fejer_anticoncentration d d N ε C0 (η / 2) hd1 hd1 hN1 hε_pos hC0_pos
        (by positivity) hsqrt_d_2 hC0_bd hε_bd hN_bd x hx_box hx_norm
      have hmid_le : ∑ y ∈ A.filter (fun y => |ip x y| ≤ E), w y ≤ η := by
        have hsub : A.filter (fun y => |ip x y| ≤ E) ⊆ (box d d).filter (fun y => |ip x y| ≤ E) :=
          Finset.filter_subset_filter _ (Finset.filter_subset _ _)
        have h1 : ∑ y ∈ A.filter (fun y => |ip x y| ≤ E), pd d d y ≤ η / 2 :=
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => pd_nonneg d d y)).trans hfejer
        simp only [w, ← Finset.sum_div]
        rw [div_le_iff₀ hpA_pos]
        calc ∑ y ∈ A.filter (fun y => |ip x y| ≤ E), pd d d y
            ≤ η / 2 := h1
          _ = η * (1 / 2) := by ring
          _ ≤ η * pA := mul_le_mul_of_nonneg_left hpA_ge hη.le
      have hsym : ∑ y ∈ A.filter (fun y => E < ip x y), w y =
          ∑ y ∈ A.filter (fun y => ip x y < -E), w y := by
        refine Finset.sum_bij (fun y _ => -y) ?_ ?_ ?_ ?_
        · intro y hy
          rw [Finset.mem_filter] at hy ⊢
          rcases hy with ⟨hyA, hyip⟩
          rw [Finset.mem_filter] at hyA ⊢
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [mem_box_iff]; intro r; have := mem_box_iff.mp hyA.1 r
            simp only [Pi.neg_apply]; omega
          · rw [normSq_neg]; exact hyA.2
          · rw [ip_neg_right]; linarith
        · intro a _ b _ hab; exact neg_inj.mp hab
        · intro y hy
          rw [Finset.mem_filter] at hy
          rcases hy with ⟨hyA, hyip⟩
          rw [Finset.mem_filter] at hyA
          refine ⟨-y, ?_, neg_neg y⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
          · rw [mem_box_iff]; intro r; have := mem_box_iff.mp hyA.1 r
            simp only [Pi.neg_apply]; omega
          · rw [normSq_neg]; exact hyA.2
          · rw [ip_neg_right]; linarith
        · intro y _; simp [w, pd_neg]
      have hpart : (∑ y ∈ A.filter (fun y => E < ip x y), w y) +
          (∑ y ∈ A.filter (fun y => ip x y < -E), w y) +
          (∑ y ∈ A.filter (fun y => |ip x y| ≤ E), w y) = 1 := by
        rw [← hw1]
        have hrew : ∀ y ∈ A, w y =
            (if E < ip x y then w y else 0) +
            (if ip x y < -E then w y else 0) +
            (if |ip x y| ≤ E then w y else 0) := by
          intro y _
          by_cases h1 : E < ip x y
          · have h2 : ¬ (ip x y < -E) := by linarith
            have h3 : ¬ (|ip x y| ≤ E) := by intro hab; linarith [(abs_le.mp hab).2]
            simp [h1, h2, h3]
          · by_cases h2 : ip x y < -E
            · have h3 : ¬ (|ip x y| ≤ E) := by intro hab; linarith [(abs_le.mp hab).1]
              simp [h1, h2, h3]
            · have h3 : |ip x y| ≤ E := by rw [abs_le]; constructor <;> linarith
              simp [h1, h2, h3]
        simp_rw [Finset.sum_filter]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact (Finset.sum_congr rfl hrew).symm
      rw [← Finset.sum_filter]
      linarith
    calc 1 / 2 - η = (∑ x ∈ A, w x) * (1 / 2 - η) := by rw [hw1, one_mul]
      _ = ∑ x ∈ A, w x * (1 / 2 - η) := by rw [Finset.sum_mul]
      _ ≤ ∑ x ∈ A, w x * (∑ y ∈ A, if E < ip x y then w y else 0) :=
          Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (hper_x x hx) (hw0 x hx)
      _ = ∑ x ∈ A, ∑ y ∈ A, if E < ip x y then w x * w y else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          by_cases h : E < ip x y <;> simp [h]
  obtain ⟨m, hm, H, hcf, hindH, hedgeH⟩ :=
    bollobas_erdos_weighted A w C E η δ hC_nn hE_pos hC_sq.le hη hη4 hδ hw0 hw1 hnorm hind hcross
  refine ⟨m, hm, H, hcf, ?_, ?_⟩
  · calc (H.indepNum : ℝ) ≤ δ * (m : ℝ) := hindH
      _ ≤ δ_raw * (m : ℝ) := mul_le_mul_of_nonneg_right hδ_le (Nat.cast_nonneg m)
  · calc (1 / 8 - η_raw) * (m : ℝ) ^ 2 ≤ (1 / 8 - η) * (m : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg (m : ℝ))
      _ ≤ H.edgeFinset.card := hedgeH

end

end BollobasErdosTryC

theorem OMA.solution : OMA.R_Erdos22_erdos_22_variants_bollobas_erdos_lower_R1.H1 :=
  BollobasErdosTryC.exists_graph_H1
