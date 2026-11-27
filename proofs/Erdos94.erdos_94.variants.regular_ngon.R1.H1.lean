import OMAReductions.R_Erdos94_erdos_94_variants_regular_ngon_R1
import Mathlib

-- Step Erdos94.erdos_94.variants.regular_ngon.R1.H1: hypothesis H1 of reduction Erdos94.erdos_94.variants.regular_ngon.R1
-- Credit: @ivillar
-- H1 := the regular n-gon has sum of squared distance multiplicities at least
--   n^2 (n-1) / 2 (n odd), n^3 / 2 - 3 n^2 / 4 (n even).
-- Proof (double counting): index the vertices by ZMod n. The distance between vertices a and b
-- depends only on a - b up to sign, so for every ordered pair (a, b) with t = a - b there are
-- at least n * card {t, -t} ordered pairs at the same distance. Writing N_u for the number of
-- ordered pairs at distance u (so the multiplicity is N_u / 2), the sum of N_u^2 equals the sum
-- over ordered pairs q of N at the distance of q, which is at least n * (2 n (n-1) - n a), where
-- a <= 1 counts the nonzero t with t = -t (and a = 0 for odd n).

open Filter EuclideanGeometry Erdos94

namespace OMA.E94H1
noncomputable def c (n : ℕ) (x : ℤ) : ℝ := Real.cos (2 * Real.pi * x / n)

lemma c_eq (n : ℕ) (hn : n ≠ 0) {x y : ℤ} (h : (x : ZMod n) = (y : ZMod n)) : c n x = c n y := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨m, hm⟩ := h
  have hy : y = x + n * m := by linarith
  unfold c
  rw [hy]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have : 2 * Real.pi * ((x + n * m : ℤ) : ℝ) / n = 2 * Real.pi * x / n + (m : ℝ) * (2 * Real.pi) := by
    push_cast
    field_simp
  rw [this, Real.cos_add_int_mul_two_pi]

lemma c_neg (n : ℕ) (x : ℤ) : c n (-x) = c n x := by
  unfold c
  push_cast
  rw [show 2 * Real.pi * -(x : ℝ) / n = -(2 * Real.pi * x / n) by ring, Real.cos_neg]

noncomputable def g (n : ℕ) (k : ℕ) : ℝ² :=
  !₂[Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

lemma dist_g (n : ℕ) (a b : ℕ) : dist (g n a) (g n b) = Real.sqrt (2 - 2 * c n ((a : ℤ) - b)) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  simp [g, Fin.sum_univ_two, c, Real.dist_eq, sq_abs]
  have h1 := Real.sin_sq_add_cos_sq (2 * Real.pi * a / n)
  have h2 := Real.sin_sq_add_cos_sq (2 * Real.pi * b / n)
  rw [show 2 * Real.pi * ((a : ℝ) - b) / n = 2 * Real.pi * a / n - 2 * Real.pi * b / n by ring,
    Real.cos_sub]
  nlinarith [h1, h2]

section counting

variable {n : ℕ} [NeZero n]

lemma dist_eq_of (a b a' b' : ZMod n) (h : a' - b' = a - b ∨ a' - b' = -(a - b)) :
    dist (g n a'.val) (g n b'.val) = dist (g n a.val) (g n b.val) := by
  rw [dist_g, dist_g]
  congr 3
  rcases h with h | h
  · apply c_eq n (NeZero.ne n)
    push_cast
    simp only [ZMod.natCast_zmod_val]
    exact h
  · rw [← c_neg n ((a.val : ℤ) - b.val)]
    apply c_eq n (NeZero.ne n)
    push_cast
    simp only [ZMod.natCast_zmod_val]
    rw [h]

lemma g_inj (a b : ZMod n) (h : g n a.val = g n b.val) : a = b := by
  have hd : dist (g n a.val) (g n b.val) = 0 := by rw [h, dist_self]
  rw [dist_g, Real.sqrt_eq_zero'] at hd
  have hc : c n ((a.val : ℤ) - b.val) = 1 := by
    have := Real.cos_le_one (2 * Real.pi * (((a.val : ℤ) - b.val : ℤ) : ℝ) / n)
    unfold c at *
    linarith
  unfold c at hc
  rw [Real.cos_eq_one_iff] at hc
  obtain ⟨m, hm⟩ := hc
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [eq_div_iff hn] at hm
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hmul : (2 * Real.pi) * ((m : ℝ) * n - ((a.val : ℝ) - b.val)) = 0 := by
    push_cast at hm
    linear_combination hm
  have hm' : (m : ℝ) * n = (a.val : ℝ) - b.val := by
    rcases mul_eq_zero.mp hmul with h1 | h1
    · exact absurd h1 h2pi
    · linarith
  have hm'' : m * (n : ℤ) = (a.val : ℤ) - b.val := by exact_mod_cast hm'
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with h1 | h1 | h1
    · nlinarith
    · exact h1
    · nlinarith
  apply ZMod.val_injective
  subst hm0
  omega

lemma card_diff_mem (A : Finset (ZMod n)) :
    (Finset.univ.filter (fun p : ZMod n × ZMod n => p.1 - p.2 ∈ A)).card = n * A.card := by
  let e : ZMod n × ZMod n ≃ ZMod n × ZMod n :=
    { toFun := fun p => (p.1, p.1 - p.2), invFun := fun p => (p.1, p.1 - p.2),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  have h : Finset.univ.filter (fun p : ZMod n × ZMod n => p.1 - p.2 ∈ A) =
      (Finset.univ ×ˢ A).map e.toEmbedding := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_product,
      Equiv.coe_toEmbedding, Prod.exists]
    constructor
    · intro hxy
      exact ⟨x, x - y, hxy, by simp [e]⟩
    · rintro ⟨a, b, hb, hab⟩
      simp only [e, Equiv.coe_fn_mk, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      simpa using hb
  rw [h, Finset.card_map, Finset.card_product, Finset.card_univ, ZMod.card]

lemma two_val (s : ZMod n) (h0 : s ≠ 0) (h : s = -s) : 2 * s.val = n := by
  have h2 : ((2 * s.val : ℕ) : ZMod n) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hlt := ZMod.val_lt s
  have hpos : 0 < s.val := by
    rcases Nat.eq_zero_or_pos s.val with h' | h'
    · exact absurd ((ZMod.val_eq_zero s).mp h') h0
    · exact h'
  obtain ⟨k, hk⟩ := h2
  have hk1 : k = 1 := by
    rcases k with _ | _ | k
    · omega
    · rfl
    · nlinarith
  subst hk1
  omega

lemma card_selfneg_le :
    (Finset.univ.filter (fun s : ZMod n => s ≠ 0 ∧ s = -s)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have h1 := two_val a ha.1 ha.2
  have h2 := two_val b hb.1 hb.2
  apply ZMod.val_injective
  omega

lemma card_selfneg_odd (hodd : n % 2 = 1) :
    (Finset.univ.filter (fun s : ZMod n => s ≠ 0 ∧ s = -s)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _ hs
  have := two_val s hs.1 hs.2
  omega

lemma regularNGon_eq : regularNGon n = Finset.univ.image (fun t : ZMod n => g n t.val) := by
  unfold regularNGon
  have h : (Finset.range n) = Finset.univ.image (fun t : ZMod n => t.val) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hk
      exact ⟨k, ZMod.val_cast_of_lt hk⟩
    · rintro ⟨t, rfl⟩
      exact ZMod.val_lt t
  rw [h, Finset.image_image]
  rfl

end counting

theorem bound (n : ℕ) [NeZero n] :
    (if n % 2 = 1 then (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 2
      else (n : ℝ) ^ 3 / 2 - 3 * (n : ℝ) ^ 2 / 4) ≤
      ∑ u ∈ distanceSet (regularNGon n), (distanceMultiplicity (regularNGon n) u : ℝ) ^ 2 := by
  set P := regularNGon n with hP
  set S := P.offDiag with hS
  set f : ℝ² × ℝ² → ℝ := fun q => dist q.1 q.2 with hf
  set N : ℝ → ℕ := fun u => (S.filter (fun q => f q = u)).card with hN
  have hD : distanceSet P = S.image f := rfl
  have hm : ∀ u, (distanceMultiplicity P u : ℝ) = (N u : ℝ) / 2 := by
    intro u
    have he := even_card_offDiag_filter_dist_eq P u
    unfold distanceMultiplicity
    rw [Nat.cast_div (even_iff_two_dvd.mp he) (by norm_num)]
    norm_num
    rfl
  have hsum : ∑ u ∈ distanceSet P, (distanceMultiplicity P u : ℝ) ^ 2 =
      ((∑ u ∈ S.image f, N u ^ 2 : ℕ) : ℝ) / 4 := by
    rw [hD, Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    rw [hm u]
    push_cast
    ring
  have h2 : ∑ u ∈ S.image f, N u ^ 2 = ∑ q ∈ S, N (f q) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image f) (g := f)
      (fun q hq => Finset.mem_image_of_mem f hq) (fun q => N (f q))]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_congr rfl (fun q hq => by rw [(Finset.mem_filter.mp hq).2]),
      Finset.sum_const, smul_eq_mul, sq]
  set T := (Finset.univ : Finset (ZMod n)).offDiag with hT
  set G : ZMod n × ZMod n → ℝ² × ℝ² := fun p => (g n p.1.val, g n p.2.val) with hG
  have hGinj : Function.Injective G := by
    intro p p' h
    simp only [G, Prod.mk.injEq] at h
    exact Prod.ext (g_inj _ _ h.1) (g_inj _ _ h.2)
  have hSimg : S = T.image G := by
    ext ⟨x, y⟩
    rw [hS, Finset.mem_offDiag, hP, regularNGon_eq, Finset.mem_image, Finset.mem_image,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨a, -, rfl⟩, ⟨b, -, rfl⟩, hab⟩
      refine ⟨(a, b), ?_, rfl⟩
      rw [hT, Finset.mem_offDiag]
      refine ⟨Finset.mem_univ _, Finset.mem_univ _, fun h => hab ?_⟩
      simp only at h ⊢
      rw [h]
    · rintro ⟨⟨a, b⟩, hab, he⟩
      simp only [G, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [hT, Finset.mem_offDiag] at hab
      exact ⟨⟨a, Finset.mem_univ _, rfl⟩, ⟨b, Finset.mem_univ _, rfl⟩,
        fun h => hab.2.2 (g_inj _ _ h)⟩
  have h3 : ∑ q ∈ S, N (f q) = ∑ p ∈ T, N (f (G p)) := by
    rw [hSimg, Finset.sum_image (fun p _ p' _ h => hGinj h)]
  have h4 : ∀ p ∈ T, n * ({p.1 - p.2, -(p.1 - p.2)} : Finset (ZMod n)).card ≤ N (f (G p)) := by
    intro p hp
    have hne : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr (Finset.mem_offDiag.mp hp).2.2
    rw [← card_diff_mem, ← Finset.card_image_of_injective _ hGinj]
    apply Finset.card_le_card
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p', hp', rfl⟩ := hq
    rw [Finset.mem_filter] at hp'
    have hp'2 := hp'.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp'2
    rw [Finset.mem_filter]
    constructor
    · rw [hSimg]
      apply Finset.mem_image_of_mem
      rw [hT, Finset.mem_offDiag]
      refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
      intro h
      rw [h, sub_self] at hp'2
      rcases hp'2 with h' | h'
      · exact hne h'.symm
      · exact hne (neg_eq_zero.mp h'.symm)
    · exact dist_eq_of _ _ _ _ hp'2
  have h5 : ∑ p ∈ T, ({p.1 - p.2, -(p.1 - p.2)} : Finset (ZMod n)).card +
      (T.filter (fun p => p.1 - p.2 = -(p.1 - p.2))).card = 2 * T.card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : p.1 - p.2 = -(p.1 - p.2)
    · rw [if_pos h, ← h]
      simp
    · rw [if_neg h, Finset.card_pair h]
      norm_num
  have hTc : T.card = n * n - n := by
    rw [hT, Finset.offDiag_card, Finset.card_univ, ZMod.card]
  have h6 : (T.filter (fun p => p.1 - p.2 = -(p.1 - p.2))).card =
      n * (Finset.univ.filter (fun s : ZMod n => s ≠ 0 ∧ s = -s)).card := by
    rw [← card_diff_mem]
    congr 1
    ext p
    simp only [hT, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨sub_ne_zero.mpr h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨sub_ne_zero.mp h1, h2⟩
  set X := ∑ p ∈ T, ({p.1 - p.2, -(p.1 - p.2)} : Finset (ZMod n)).card with hX
  set a := (Finset.univ.filter (fun s : ZMod n => s ≠ 0 ∧ s = -s)).card with ha
  have hge : n * X ≤ ∑ u ∈ S.image f, N u ^ 2 := by
    rw [h2, h3, hX, Finset.mul_sum]
    exact Finset.sum_le_sum h4
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hXr : (X : ℝ) + n * a = 2 * ((n : ℝ) * n - n) := by
    have := h5
    rw [h6, hTc] at this
    have hc : ((X + n * a : ℕ) : ℝ) = ((2 * (n * n - n) : ℕ) : ℝ) := by rw [this]
    push_cast [Nat.cast_sub hnn] at hc
    linarith
  have hger : (n : ℝ) * X ≤ ((∑ u ∈ S.image f, N u ^ 2 : ℕ) : ℝ) := by exact_mod_cast hge
  rw [hsum]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  split_ifs with hodd
  · have ha0 : a = 0 := card_selfneg_odd hodd
    rw [ha0] at hXr
    push_cast at hXr
    nlinarith
  · have ha1 : (a : ℝ) ≤ 1 := by exact_mod_cast card_selfneg_le
    nlinarith [mul_le_mul_of_nonneg_left ha1 hn0]

end OMA.E94H1

theorem OMA.solution : OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H1 := by
  unfold OMA.R_Erdos94_erdos_94_variants_regular_ngon_R1.H1
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [regularNGon, distanceSet]
  haveI : NeZero n := ⟨hn.ne'⟩
  exact OMA.E94H1.bound n
