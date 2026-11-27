import OMAReductions.R_Erdos128_erdos_128_R1_H2_R1

-- Reduction Erdos128.erdos_128.R1.H2.R1.H2.R1 of step Erdos128.erdos_128.R1.H2.R1.H2
-- Credit: @ashnewmanjones
--
-- Step Erdos128.erdos_128.R1.H2.R1.H2 is the upper middle range of Erdős 128: every triangle-free
-- graph G on n vertices with 3 n^2 / 20 < e < n^2 / 5 has a sparse half (a set V' with
-- 2 |V'| + 1 ≥ n and 50 e(G[V']) ≤ n^2).
--
-- Here two substantial structural regimes are PROVED from scratch:
--   1. Large minimum degree: δ(G) > 3 n / 8 (min_deg_gt_three_eighths). We prove Häggkvist's
--      theorem (every triangle-free graph with δ > 3n/8 is bipartite or homomorphic to C_5) and
--      that every graph homomorphic to C_5 has a sparse half.
--   2. Large independent set: α(G) ≥ 5 n / 12 (indep_ge_five_twelfths), which in particular
--      resolves Δ(G) ≥ 5 n / 12. Given an independent set I of size s ≥ 5n/12, we split V \ I
--      at d_I(u) > s/2 into an independent set X_+ and X_- and combine exact averaging on
--      I ∪ Y_1 and X_+ ∪ Y_2.
--
-- The remaining open step is split into three clean, literature-aligned pieces:
--   H1: δ(G) ≤ 3n/8 and α(G) ∈ [2n/5, 5n/12)  (known: Razborov 2021, Theorem on α ≥ 2n/5)
--   H2: δ(G) ∈ [5n/14, 3n/8] and α(G) < 2n/5  (known: Norin and Yepremyan 2015, JCTB)
--   H3: δ(G) < 5n/14 and α(G) < 2n/5          (open core; in particular Δ(G) < 2n/5).

namespace OMA.R_Erdos128_erdos_128_R1_H2_R1_H2_R1

open Finset OMA.R_Erdos128_erdos_128_R1 OMA.R_Erdos128_erdos_128_R1_H2_R1

-- Known (Razborov 2021): upper middle range with δ ≤ 3n/8 and 2n/5 ≤ α(G) < 5n/12.
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    3 * Fintype.card V ^ 2 < 20 * G.edgeSet.ncard →
    5 * G.edgeSet.ncard < Fintype.card V ^ 2 →
    (∃ v, 8 * (G.neighborSet v).ncard ≤ 3 * Fintype.card V) →
    (∃ I : Set V, G.IsIndepSet I ∧ 2 * Fintype.card V ≤ 5 * I.ncard) →
    (∀ I : Set V, G.IsIndepSet I → 12 * I.ncard < 5 * Fintype.card V) →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

-- Known (Norin and Yepremyan 2015): upper middle range with 5n/14 ≤ δ(G) ≤ 3n/8 and α(G) < 2n/5.
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    3 * Fintype.card V ^ 2 < 20 * G.edgeSet.ncard →
    5 * G.edgeSet.ncard < Fintype.card V ^ 2 →
    (∃ v, 8 * (G.neighborSet v).ncard ≤ 3 * Fintype.card V) →
    (∀ v, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard) →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

-- Open core of the upper middle range: δ(G) < 5n/14 and α(G) < 2n/5.
def H3 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    3 * Fintype.card V ^ 2 < 20 * G.edgeSet.ncard →
    5 * G.edgeSet.ncard < Fintype.card V ^ 2 →
    (∃ v, 14 * (G.neighborSet v).ncard < 5 * Fintype.card V) →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
      ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
        50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2

/-! ## Common helpers -/

lemma sparse_of_finset {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : S.card = Fintype.card V / 2)
    (hD : 25 * ∑ u ∈ S, (S.filter (G.Adj u)).card ≤ Fintype.card V ^ 2) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  refine ⟨(S : Set V), by rw [Set.ncard_coe_finset, hS]; omega, ?_⟩
  have := two_mul_induce G S
  omega

lemma sparse_of_indep_ge_half {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (I : Finset V) (hI : ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w)
    (hcard : Fintype.card V / 2 ≤ I.card) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  obtain ⟨S, hSI, hS⟩ := Finset.exists_subset_card_eq hcard
  refine sparse_of_finset G S hS ?_
  rw [D_indep G S fun u hu w hw => hI u (hSI hu) w (hSI hw)]
  simp

lemma ncard_neighborSet_eq_card_filter {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (G.neighborSet v).ncard = ((univ : Finset V).filter (G.Adj v)).card := by
  have : G.neighborSet v = (((univ : Finset V).filter (G.Adj v)) : Set V) := by
    ext u; simp [SimpleGraph.mem_neighborSet]
  rw [this, Set.ncard_coe_finset]

lemma two_fifths_prod (n k s : ℕ) (hk : 2 * k ≤ n) (hsk : s ≤ k) (h5 : 2 * n ≤ 5 * s) :
    25 * ((k - s) * s) ≤ n ^ 2 := by
  have h1 : (2 : ℤ) * (k : ℤ) ≤ n := by exact_mod_cast hk
  have h2 : (s : ℤ) ≤ k := by exact_mod_cast hsk
  have h3 : 2 * (n : ℤ) ≤ 5 * s := by exact_mod_cast h5
  have h4 : 0 ≤ (5 * (s : ℤ) - 2 * n) * (10 * s - n) :=
    mul_nonneg (by linarith) (by linarith)
  have h5' : 25 * (((k : ℤ) - s) * s) ≤ (n : ℤ) ^ 2 := by nlinarith
  have : ((25 * ((k - s) * s) : ℕ) : ℤ) ≤ ((n ^ 2 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hsk]; exact h5'
  exact_mod_cast this

/-! ## Part 1: Large independent set (α(G) ≥ 5n/12) -/

lemma hys_bound_int (n y s : ℤ) (hs0 : 0 ≤ s) (h12 : 5 * n ≤ 12 * s) (h2ys : 2 * (y + s) ≤ n) :
    144 * y * s ≤ 5 * n ^ 2 := by
  have hA : 0 ≤ 12 * s - 5 * n := by linarith
  have hB : 0 ≤ 12 * s - n := by linarith
  have hprod : 0 ≤ (12 * s - 5 * n) * (12 * s - n) := mul_nonneg hA hB
  have hys2 : 2 * y * s ≤ (n - 2 * s) * s := by nlinarith
  nlinarith

lemma five_twelfths_int (n y z s p m e aIP D1 D2 : ℤ)
    (hy1 : 1 ≤ y) (hz1 : 1 ≤ z) (hs0 : 0 ≤ s) (hp0 : 0 ≤ p) (hm0 : 0 < m)
    (hn12 : 12 ≤ n) (hy12 : 12 * y ≤ n) (h12 : 5 * n ≤ 12 * s)
    (h2ys : 2 * (y + s) ≤ n) (h2pz : n ≤ 2 * p + 2 * z + 1) (hyzm : y + z ≤ m)
    (he : 5 * e ≤ n ^ 2) (haIP : p * (s + 1) ≤ 2 * aIP)
    (hD1 : D1 * m ≤ y * m * s + y ^ 3)
    (hcombo : (z * D1 + y * D2) * m + y * z * (2 * aIP) ≤ y * z * (2 * e))
    (h1 : n ^ 2 < 25 * D1) (h2 : n ^ 2 < 25 * D2) : False := by
  have hcand1_fail : (n ^ 2 - 25 * y * s) * m < 25 * y ^ 3 := by
    have hm1 : n ^ 2 * m < 25 * D1 * m := mul_lt_mul_of_pos_right h1 hm0
    have hid : (n ^ 2 - 25 * y * s) * m = n ^ 2 * m - 25 * (y * m * s) := by ring
    have hassoc : 25 * D1 * m = 25 * (D1 * m) := by ring
    linarith only [hm1, hid, hassoc, hD1]
  have hys : 144 * y * s ≤ 5 * n ^ 2 := hys_bound_int n y s hs0 h12 h2ys
  have hgap : 19 * n ^ 2 ≤ 144 * (n ^ 2 - 25 * y * s) := by linarith only [hys]
  have hzy : 19 * z < 6 * y := by
    have hmy : (n ^ 2 - 25 * y * s) * (m - y) < y * (25 * y * (y + s) - n ^ 2) := by
      have hid : (n ^ 2 - 25 * y * s) * (m - y) - y * (25 * y * (y + s) - n ^ 2) =
          (n ^ 2 - 25 * y * s) * m - 25 * y ^ 3 := by ring
      linarith only [hcand1_fail, hid]
    have hnonneg : 0 ≤ n ^ 2 - 25 * y * s := by linarith only [hgap, sq_nonneg n]
    have hstep1 : (n ^ 2 - 25 * y * s) * z < y * (25 * y * (y + s) - n ^ 2) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linarith only [hyzm]) hnonneg) hmy
    have hstep2 : 24 * (25 * y * (y + s) - n ^ 2) ≤ n ^ 2 := by
      have hmul : (12 * y) * (2 * (y + s)) ≤ n * n :=
        mul_le_mul hy12 h2ys (by linarith only [hy1, hs0]) (by linarith only [hn12])
      have hid1 : (12 * y) * (2 * (y + s)) = 24 * (y * (y + s)) := by ring
      have hid2 : n * n = n ^ 2 := by ring
      linarith only [hmul, hid1, hid2]
    have hstep3 : n ^ 2 * (19 * z) < n ^ 2 * (6 * y) := by
      have hL : 19 * n ^ 2 * z ≤ 144 * (n ^ 2 - 25 * y * s) * z :=
        mul_le_mul_of_nonneg_right hgap (by linarith only [hz1])
      have hM : 144 * ((n ^ 2 - 25 * y * s) * z) < 144 * (y * (25 * y * (y + s) - n ^ 2)) :=
        mul_lt_mul_of_pos_left hstep1 (by norm_num)
      have hR : 24 * (y * (25 * y * (y + s) - n ^ 2)) ≤ y * n ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hstep2 (by linarith only [hy1])
        have hid : 24 * (y * (25 * y * (y + s) - n ^ 2)) = y * (24 * (25 * y * (y + s) - n ^ 2)) := by ring
        linarith only [h, hid]
      have hidL : 144 * (n ^ 2 - 25 * y * s) * z = 144 * ((n ^ 2 - 25 * y * s) * z) := by ring
      have hid1 : n ^ 2 * (19 * z) = 19 * n ^ 2 * z := by ring
      have hid2 : n ^ 2 * (6 * y) = 6 * (y * n ^ 2) := by ring
      linarith only [hL, hM, hR, hidL, hid1, hid2]
    exact lt_of_mul_lt_mul_left hstep3 (sq_nonneg n)
  have haIP_lb : 15 * n ^ 2 ≤ 76 * (2 * aIP) := by
    have h2p : 18 * n - 19 ≤ 19 * (2 * p) := by linarith only [hzy, hy12, h2pz]
    have hs1 : 5 * n + 12 ≤ 12 * (s + 1) := by linarith only [h12]
    have hprod : (18 * n - 19) * (5 * n + 12) ≤ (19 * (2 * p)) * (12 * (s + 1)) :=
      mul_le_mul h2p hs1 (by linarith only [hn12]) (by linarith only [hp0])
    have hidL : (18 * n - 19) * (5 * n + 12) = 90 * n ^ 2 + 121 * n - 228 := by ring
    have hidR : (19 * (2 * p)) * (12 * (s + 1)) = 456 * (p * (s + 1)) := by ring
    linarith only [hprod, hidL, hidR, haIP, hn12]
  have hLHS : (y + z) * m * n ^ 2 < 25 * ((z * D1 + y * D2) * m) := by
    have h1' : z * n ^ 2 < z * (25 * D1) := mul_lt_mul_of_pos_left h1 (by linarith only [hz1])
    have h2' : y * n ^ 2 < y * (25 * D2) := mul_lt_mul_of_pos_left h2 (by linarith only [hy1])
    have h3' : (y + z) * n ^ 2 < 25 * (z * D1 + y * D2) := by
      have hid1 : (y + z) * n ^ 2 = z * n ^ 2 + y * n ^ 2 := by ring
      have hid2 : 25 * (z * D1 + y * D2) = z * (25 * D1) + y * (25 * D2) := by ring
      linarith only [h1', h2', hid1, hid2]
    have h4' := mul_lt_mul_of_pos_right h3' hm0
    have hid1 : (y + z) * n ^ 2 * m = (y + z) * m * n ^ 2 := by ring
    have hid2 : 25 * (z * D1 + y * D2) * m = 25 * ((z * D1 + y * D2) * m) := by ring
    linarith only [h4', hid1, hid2]
  have hRHS : 76 * (25 * ((z * D1 + y * D2) * m)) ≤ 385 * y * z * n ^ 2 := by
    have hB : 25 * (2 * e) ≤ 10 * n ^ 2 := by linarith only [he]
    have hyz_nn : 0 ≤ y * z := mul_nonneg (by linarith only [hy1]) (by linarith only [hz1])
    have hC : 76 * (25 * (y * z * (2 * e))) ≤ 760 * (y * z * n ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hB hyz_nn
      have hid1 : 25 * (y * z * (2 * e)) = y * z * (25 * (2 * e)) := by ring
      have hid2 : y * z * (10 * n ^ 2) = 10 * (y * z * n ^ 2) := by ring
      linarith only [h, hid1, hid2]
    have hD : 375 * (y * z * n ^ 2) ≤ 76 * (25 * (y * z * (2 * aIP))) := by
      have h := mul_le_mul_of_nonneg_left haIP_lb hyz_nn
      have hid1 : y * z * (15 * n ^ 2) = 15 * (y * z * n ^ 2) := by ring
      have hid2 : y * z * (76 * (2 * aIP)) = 76 * (y * z * (2 * aIP)) := by ring
      linarith only [h, hid1, hid2]
    have hidF : 385 * y * z * n ^ 2 = 385 * (y * z * n ^ 2) := by ring
    linarith only [hcombo, hC, hD, hidF]
  have hpoly : 385 * y * z ≤ 76 * ((y + z) * m) := by
    have h2 : 76 * (y + z) ^ 2 - 385 * y * z =
        (6 * y - 19 * z) * (12 * y - 4 * z) + 4 * y ^ 2 + 19 * (y * z) := by ring
    have h3 : 0 ≤ (6 * y - 19 * z) * (12 * y - 4 * z) :=
      mul_nonneg (by linarith only [hzy]) (by linarith only [hzy, hz1])
    have h4 : (y + z) ^ 2 ≤ (y + z) * m := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hyzm (by linarith only [hy1, hz1])
    have h5 : 0 ≤ y * z := mul_nonneg (by linarith only [hy1]) (by linarith only [hz1])
    linarith only [h2, h3, h4, h5, sq_nonneg y]
  have hpoly_n : 385 * y * z * n ^ 2 ≤ 76 * ((y + z) * m * n ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hpoly (sq_nonneg n)
    have hid1 : 76 * ((y + z) * m) * n ^ 2 = 76 * ((y + z) * m * n ^ 2) := by ring
    linarith only [h, hid1]
  linarith only [hLHS, hRHS, hpoly_n]

lemma five_twelfths_endgame (n k s p m e aIP aIM aPM DM D1 D2 : ℕ)
    (hk1 : 2 * k ≤ n) (hk2 : n ≤ 2 * k + 1)
    (h12 : 5 * n ≤ 12 * s) (hsk : s + 1 ≤ k) (hpk : p + 1 ≤ k)
    (hm : m + s + p = n)
    (he : 5 * e < n ^ 2)
    (hdecomp : 2 * e = 2 * aIP + 2 * aIM + 2 * aPM + DM)
    (haIP : p * (s + 1) ≤ 2 * aIP)
    (haIM : 2 * aIM ≤ m * s)
    (hDM : DM ≤ m * (k - s - 1))
    (hD1 : D1 * (m * (m - 1)) ≤ 2 * (k - s) * (m - 1) * aIM + (k - s) * (k - s - 1) * DM)
    (hD2 : D2 * (m * (m - 1)) ≤ 2 * (k - p) * (m - 1) * aPM + (k - p) * (k - p - 1) * DM) :
    25 * D1 ≤ n ^ 2 ∨ 25 * D2 ≤ n ^ 2 := by
  set y := k - s with hy_def
  set z := k - p with hz_def
  have hy1 : 1 ≤ y := by omega
  have hz1 : 1 ≤ z := by omega
  have hyzm : y + z ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hy12 : 12 * y ≤ n := by omega
  have hn12 : 12 ≤ n := by omega
  -- Scale-free bound for Candidate 1: D1 * m ≤ y * m * s + y ^ 3
  have hD1_bound : D1 * m ≤ y * m * s + y ^ 3 := by
    have hstep1 : D1 * (m * (m - 1)) ≤ m * (y * (m - 1) * s + y * (y - 1) ^ 2) := by
      calc D1 * (m * (m - 1))
          ≤ 2 * y * (m - 1) * aIM + y * (y - 1) * DM := hD1
        _ = y * (m - 1) * (2 * aIM) + y * (y - 1) * DM := by ring
        _ ≤ y * (m - 1) * (m * s) + y * (y - 1) * (m * (y - 1)) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ haIM) (Nat.mul_le_mul_left _ hDM)
        _ = m * (y * (m - 1) * s + y * (y - 1) ^ 2) := by ring
    have hstep2 : D1 * (m - 1) ≤ y * (m - 1) * s + y * (y - 1) ^ 2 := by
      have : m * (D1 * (m - 1)) ≤ m * (y * (m - 1) * s + y * (y - 1) ^ 2) := by
        linarith
      exact Nat.le_of_mul_le_mul_left this (by omega)
    have hmy : m * (y - 1) ^ 2 ≤ (m - 1) * y ^ 2 := by
      have hm' : (m : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) := by omega
      have hy' : (y : ℤ) - 1 = ((y - 1 : ℕ) : ℤ) := by omega
      have : (m : ℤ) * ((y : ℤ) - 1) ^ 2 ≤ ((m : ℤ) - 1) * (y : ℤ) ^ 2 := by
        have h1 : 0 ≤ (y : ℤ) * ((m : ℤ) - y) := mul_nonneg (by omega) (by omega)
        have h2 : 0 ≤ (m : ℤ) * ((y : ℤ) - 1) := mul_nonneg (by omega) (by omega)
        nlinarith
      rw [hm', hy'] at this
      exact_mod_cast this
    have hstep3 : (m - 1) * (D1 * m) ≤ (m - 1) * (y * m * s + y ^ 3) := by
      calc (m - 1) * (D1 * m) = m * (D1 * (m - 1)) := by ring
        _ ≤ m * (y * (m - 1) * s + y * (y - 1) ^ 2) := Nat.mul_le_mul_left _ hstep2
        _ = (m - 1) * (y * m * s) + y * (m * (y - 1) ^ 2) := by ring
        _ ≤ (m - 1) * (y * m * s) + y * ((m - 1) * y ^ 2) :=
            Nat.add_le_add_left (Nat.mul_le_mul_left _ hmy) _
        _ = (m - 1) * (y * m * s + y ^ 3) := by ring
    exact Nat.le_of_mul_le_mul_left hstep3 (by omega)
  -- Linear combination of Candidate 1 and Candidate 2
  have hcombo : (z * D1 + y * D2) * m + y * z * (2 * aIP) ≤ y * z * (2 * e) := by
    have hyz_sub : y - 1 + (z - 1) ≤ m - 1 := by omega
    have hsum : (m - 1) * ((z * D1 + y * D2) * m) ≤
        (m - 1) * (y * z * (2 * aIM + 2 * aPM + DM)) := by
      calc (m - 1) * ((z * D1 + y * D2) * m)
          = z * (D1 * (m * (m - 1))) + y * (D2 * (m * (m - 1))) := by ring
        _ ≤ z * (2 * y * (m - 1) * aIM + y * (y - 1) * DM) +
            y * (2 * z * (m - 1) * aPM + z * (z - 1) * DM) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ hD1) (Nat.mul_le_mul_left _ hD2)
        _ = (m - 1) * (y * z * (2 * aIM + 2 * aPM)) + y * z * (y - 1 + (z - 1)) * DM := by ring
        _ ≤ (m - 1) * (y * z * (2 * aIM + 2 * aPM)) + y * z * (m - 1) * DM :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hyz_sub)) _
        _ = (m - 1) * (y * z * (2 * aIM + 2 * aPM + DM)) := by ring
    have hcancel := Nat.le_of_mul_le_mul_left hsum (by omega : 0 < m - 1)
    have hdec : y * z * (2 * e) = y * z * (2 * aIM + 2 * aPM + DM) + y * z * (2 * aIP) := by
      rw [hdecomp]; ring
    omega
  -- Now finish by contradiction in ℤ
  by_contra hboth
  push Not at hboth
  obtain ⟨h1, h2⟩ := hboth
  exact five_twelfths_int n y z s p m e aIP D1 D2
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by exact_mod_cast le_of_lt he) (by exact_mod_cast haIP) (by exact_mod_cast hD1_bound)
    (by exact_mod_cast hcombo) (by exact_mod_cast h1) (by exact_mod_cast h2)

lemma indep_ge_five_twelfths {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcf : G.CliqueFree 3)
    (he : 5 * G.edgeSet.ncard < Fintype.card V ^ 2)
    (I : Finset V) (hI : ∀ u ∈ I, ∀ w ∈ I, ¬ G.Adj u w)
    (hIcard : 5 * Fintype.card V ≤ 12 * I.card) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  set n := Fintype.card V with hn
  set k := n / 2 with hk
  set s := I.card with hs
  rcases le_or_gt k s with hks | hks
  · exact sparse_of_indep_ge_half G I hI hks
  · set X := (univ : Finset V) \ I with hX
    set Xp := X.filter (fun u => s < 2 * (I.filter (G.Adj u)).card) with hXp
    set Xm := X.filter (fun u => 2 * (I.filter (G.Adj u)).card ≤ s) with hXm
    -- Xp is an independent set
    have hXp_ind : ∀ u ∈ Xp, ∀ w ∈ Xp, ¬ G.Adj u w := by
      intro u hu w hw huw
      have hu' := (Finset.mem_filter.mp hu).2
      have hw' := (Finset.mem_filter.mp hw).2
      have hdisj : Disjoint (I.filter (G.Adj u)) (I.filter (G.Adj w)) := by
        rw [Finset.disjoint_left]
        intro t htu htw
        have h1 := (Finset.mem_filter.mp htu).2
        have h2 := (Finset.mem_filter.mp htw).2
        exact hcf {u, w, t} (SimpleGraph.is3Clique_triple_iff.mpr ⟨huw, h1, h2⟩)
      have hsub : (I.filter (G.Adj u)) ∪ (I.filter (G.Adj w)) ⊆ I :=
        Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at hcard
      omega
    rcases le_or_gt k Xp.card with hkp | hkp
    · exact sparse_of_indep_ge_half G Xp hXp_ind hkp
    · set p := Xp.card with hp
      set m := Xm.card with hm
      have hdisj_IX : Disjoint I X := Finset.disjoint_sdiff
      have hunion_IX : I ∪ X = univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
      have hdisj_pm : Disjoint Xp Xm := by
        rw [Finset.disjoint_left]
        intro u hu1 hu2
        have a := (Finset.mem_filter.mp hu1).2
        have b := (Finset.mem_filter.mp hu2).2
        omega
      have hunion_pm : Xp ∪ Xm = X := by
        ext u
        simp only [Xp, Xm, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          rcases lt_or_ge s (2 * (I.filter (G.Adj u)).card) with hlt | hge
          · left; exact ⟨h, hlt⟩
          · right; exact ⟨h, hge⟩
      have hm_sum : m + s + p = n := by
        have h1 : I.card + X.card = n := by
          rw [← Finset.card_union_of_disjoint hdisj_IX, hunion_IX, Finset.card_univ]
        have h2 : Xp.card + Xm.card = X.card := by
          rw [← Finset.card_union_of_disjoint hdisj_pm, hunion_pm]
        omega
      -- Check if some vertex in Xm has ≥ k - s neighbors in Xm
      by_cases hdeg : ∃ w ∈ Xm, k - s ≤ (Xm.filter (G.Adj w)).card
      · obtain ⟨w, -, hw⟩ := hdeg
        obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq hw
        have hYXm : Y ⊆ Xm := hYsub.trans (Finset.filter_subset _ _)
        have hYind : ∀ u ∈ Y, ∀ t ∈ Y, ¬ G.Adj u t := by
          intro u hu t ht hut
          have huw := (Finset.mem_filter.mp (hYsub hu)).2
          have htw := (Finset.mem_filter.mp (hYsub ht)).2
          exact hcf {w, u, t} (SimpleGraph.is3Clique_triple_iff.mpr ⟨huw, htw, hut⟩)
        have hdisj_IY : Disjoint I Y :=
          Finset.disjoint_of_subset_right (hYXm.trans (Finset.filter_subset _ _)) hdisj_IX
        have hcard_IY : (I ∪ Y).card = k := by
          rw [Finset.card_union_of_disjoint hdisj_IY, hYcard]; omega
        refine sparse_of_finset G (I ∪ Y) hcard_IY ?_
        rw [D_union G I Y hdisj_IY hI, D_indep G Y hYind, zero_add]
        have hsum : 2 * ∑ u ∈ Y, (I.filter (G.Adj u)).card ≤ (k - s) * s := by
          calc 2 * ∑ u ∈ Y, (I.filter (G.Adj u)).card
              = ∑ u ∈ Y, 2 * (I.filter (G.Adj u)).card := by rw [Finset.mul_sum]
            _ ≤ ∑ _u ∈ Y, s := Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp (hYXm hu)).2
            _ = (k - s) * s := by rw [Finset.sum_const, hYcard, smul_eq_mul]
        have h25 := two_fifths_prod n k s (by omega) (by omega) (by omega)
        nlinarith
      · push_neg at hdeg
        -- Every vertex in Xm has degree ≤ k - s - 1 inside Xm
        set aIP := ∑ u ∈ Xp, (I.filter (G.Adj u)).card
        set aIM := ∑ u ∈ Xm, (I.filter (G.Adj u)).card
        set aPM := ∑ u ∈ Xm, (Xp.filter (G.Adj u)).card
        set DM := ∑ u ∈ Xm, (Xm.filter (G.Adj u)).card
        have haIP : p * (s + 1) ≤ 2 * aIP := by
          calc p * (s + 1) = ∑ _u ∈ Xp, (s + 1) := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ ∑ u ∈ Xp, 2 * (I.filter (G.Adj u)).card :=
                Finset.sum_le_sum fun u hu => by have := (Finset.mem_filter.mp hu).2; omega
            _ = 2 * aIP := by rw [Finset.mul_sum]
        have haIM : 2 * aIM ≤ m * s := by
          calc 2 * aIM = ∑ u ∈ Xm, 2 * (I.filter (G.Adj u)).card := by rw [Finset.mul_sum]
            _ ≤ ∑ _u ∈ Xm, s := Finset.sum_le_sum fun u hu => (Finset.mem_filter.mp hu).2
            _ = m * s := by rw [Finset.sum_const, smul_eq_mul]
        have hDM : DM ≤ m * (k - s - 1) := by
          calc DM ≤ ∑ _u ∈ Xm, (k - s - 1) :=
                Finset.sum_le_sum fun u hu => by have := hdeg u hu; omega
            _ = m * (k - s - 1) := by rw [Finset.sum_const, smul_eq_mul]
        have hdecomp : 2 * G.edgeSet.ncard = 2 * aIP + 2 * aIM + 2 * aPM + DM := by
          have h1 := deg_sum_univ G
          have h2 := D_union G I X hdisj_IX hI
          rw [hunion_IX] at h2
          have h3 := D_union G Xp Xm hdisj_pm hXp_ind
          rw [hunion_pm] at h3
          have h4 : ∑ u ∈ X, (I.filter (G.Adj u)).card = aIP + aIM := by
            rw [← hunion_pm, Finset.sum_union hdisj_pm]
          omega
        -- Apply avg_two for Candidate 1 (I ∪ Y1) and Candidate 2 (Xp ∪ Y2)
        obtain ⟨Y1, hY1sub, hY1card, hY1⟩ := avg_two G Xm I (k - s) (by omega) (by omega)
        obtain ⟨Y2, hY2sub, hY2card, hY2⟩ := avg_two G Xm Xp (k - p) (by omega) (by omega)
        have hdisj_IY1 : Disjoint I Y1 :=
          Finset.disjoint_of_subset_right (hY1sub.trans (Finset.filter_subset _ _)) hdisj_IX
        have hdisj_XpY2 : Disjoint Xp Y2 := Finset.disjoint_of_subset_right hY2sub hdisj_pm
        have hcard1 : (I ∪ Y1).card = k := by
          rw [Finset.card_union_of_disjoint hdisj_IY1, hY1card]; omega
        have hcard2 : (Xp ∪ Y2).card = k := by
          rw [Finset.card_union_of_disjoint hdisj_XpY2, hY2card]; omega
        set D1 := ∑ u ∈ I ∪ Y1, ((I ∪ Y1).filter (G.Adj u)).card
        set D2 := ∑ u ∈ Xp ∪ Y2, ((Xp ∪ Y2).filter (G.Adj u)).card
        have hD1_eq : D1 = 2 * ∑ u ∈ Y1, (I.filter (G.Adj u)).card +
            ∑ u ∈ Y1, (Y1.filter (G.Adj u)).card := by
          dsimp only [D1]; rw [D_union G I Y1 hdisj_IY1 hI]; ring
        have hD2_eq : D2 = 2 * ∑ u ∈ Y2, (Xp.filter (G.Adj u)).card +
            ∑ u ∈ Y2, (Y2.filter (G.Adj u)).card := by
          dsimp only [D2]; rw [D_union G Xp Y2 hdisj_XpY2 hXp_ind]; ring
        rw [← hD1_eq] at hY1
        rw [← hD2_eq] at hY2
        rcases five_twelfths_endgame n k s p m G.edgeSet.ncard aIP aIM aPM DM D1 D2
            (by omega) (by omega) hIcard (by omega) (by omega) hm_sum he hdecomp
            haIP haIM hDM hY1 hY2 with hfin | hfin
        · exact sparse_of_finset G (I ∪ Y1) hcard1 hfin
        · exact sparse_of_finset G (Xp ∪ Y2) hcard2 hfin

/-! ## Part 2: Graphs homomorphic to C_5 have a sparse half -/

lemma hom_C5_sparse_half {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (c : V → Fin 5)
    (hc : ∀ u v, G.Adj u v → c u + 1 = c v ∨ c v + 1 = c u) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  set n := Fintype.card V with hn
  set k := n / 2 with hk
  let P : Fin 5 → Finset V := fun i => (univ : Finset V).filter (fun v => c v = i)
  have hP_disj : ∀ i j : Fin 5, i ≠ j → Disjoint (P i) (P j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    exact hij ((Finset.mem_filter.mp hv1).2.symm.trans (Finset.mem_filter.mp hv2).2)
  have hP_sum : ∑ i : Fin 5, (P i).card = n := by
    have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset V)) (t := (univ : Finset (Fin 5)))
      (f := c) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ] at this
    exact this.symm
  have hP_ind : ∀ i : Fin 5, ∀ u ∈ P i ∪ P (i + 2), ∀ w ∈ P i ∪ P (i + 2), ¬ G.Adj u w := by
    intro i u hu w hw huw
    have hadj := hc u w huw
    have hu' : c u = i ∨ c u = i + 2 := by
      rcases Finset.mem_union.mp hu with h | h
      · left; exact (Finset.mem_filter.mp h).2
      · right; exact (Finset.mem_filter.mp h).2
    have hw' : c w = i ∨ c w = i + 2 := by
      rcases Finset.mem_union.mp hw with h | h
      · left; exact (Finset.mem_filter.mp h).2
      · right; exact (Finset.mem_filter.mp h).2
    rcases hu' with h1 | h1 <;> rcases hw' with h2 | h2 <;> rw [h1, h2] at hadj <;>
      (fin_cases i <;> simp at hadj)
  by_cases hbig : ∃ j : Fin 5, k ≤ (P j ∪ P (j + 2)).card
  · obtain ⟨j, hj⟩ := hbig
    exact sparse_of_indep_ge_half G (P j ∪ P (j + 2)) (hP_ind j) hj
  · push_neg at hbig
    -- Every non-adjacent pair has size < k; pick i maximizing |P i| + |P (i + 2)| ≥ 2n/5
    have hsum2 : ∑ i : Fin 5, ((P i).card + (P (i + 2)).card) = 2 * n := by
      rw [Finset.sum_add_distrib, hP_sum]
      have hshift : ∑ i : Fin 5, (P (i + 2)).card = ∑ i : Fin 5, (P i).card := by
        refine Fintype.sum_equiv (Equiv.addRight (2 : Fin 5)) _ _ fun _ => rfl
      rw [hshift, hP_sum]; ring
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le (s := (univ : Finset (Fin 5)))
      Finset.univ_nonempty (f := fun _ => 2 * n)
      (g := fun j => 5 * ((P j).card + (P (j + 2)).card))
      (by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          ← Finset.mul_sum, hsum2])
    have h5part : (P i).card + (P (i + 1)).card + (P (i + 2)).card + (P (i + 3)).card +
        (P (i + 4)).card = n := by
      have h5 : ∑ j : Fin 5, (P (i + j)).card = n := by
        have hshift : ∑ j : Fin 5, (P (i + j)).card = ∑ j : Fin 5, (P j).card :=
          Fintype.sum_equiv (Equiv.addLeft i) _ _ fun _ => rfl
        rw [hshift, hP_sum]
      rw [Fin.sum_univ_five] at h5
      simpa [add_assoc] using h5
    have hcard_pair : ∀ j : Fin 5, (P j ∪ P (j + 2)).card = (P j).card + (P (j + 2)).card := by
      intro j
      exact Finset.card_union_of_disjoint (hP_disj j (j + 2) (by fin_cases j <;> decide))
    have hs_lt : (P i).card + (P (i + 2)).card < k := by rw [← hcard_pair i]; exact hbig i
    have h14_lt : (P (i + 1)).card + (P (i + 4)).card < k := by
      have h := hbig (i + 4)
      rw [hcard_pair] at h
      have e : i + 4 + 2 = i + 1 := by fin_cases i <;> decide
      rw [e] at h; omega
    have h13_lt : (P (i + 1)).card + (P (i + 3)).card < k := by
      have h := hbig (i + 1)
      rw [hcard_pair] at h
      have e : i + 1 + 2 = i + 3 := by fin_cases i <;> decide
      rw [e] at h; omega
    set s := (P i).card + (P (i + 2)).card with hs_def
    rcases le_or_gt (P (i + 2)).card (P i).card with hle | hgt
    · -- Add k - s vertices from P (i + 3); they only touch P (i + 2) inside P i ∪ P (i + 2)
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
        (show k - s ≤ (P (i + 3)).card by omega)
      have hdisj : Disjoint (P i ∪ P (i + 2)) S := by
        refine Finset.disjoint_of_subset_right hSsub ?_
        rw [Finset.disjoint_union_left]
        exact ⟨hP_disj i (i + 3) (by fin_cases i <;> decide),
               hP_disj (i + 2) (i + 3) (by fin_cases i <;> decide)⟩
      have hSind : ∀ u ∈ S, ∀ w ∈ S, ¬ G.Adj u w := by
        intro u hu w hw huw
        have hadj := hc u w huw
        rw [(Finset.mem_filter.mp (hSsub hu)).2, (Finset.mem_filter.mp (hSsub hw)).2] at hadj
        fin_cases i <;> simp at hadj
      have hcardV : ((P i ∪ P (i + 2)) ∪ S).card = k := by
        rw [Finset.card_union_of_disjoint hdisj, hcard_pair, hScard]; omega
      refine sparse_of_finset G ((P i ∪ P (i + 2)) ∪ S) hcardV ?_
      rw [D_union G (P i ∪ P (i + 2)) S hdisj (hP_ind i), D_indep G S hSind, zero_add]
      have hbound : ∑ u ∈ S, ((P i ∪ P (i + 2)).filter (G.Adj u)).card ≤ (k - s) * (P (i + 2)).card := by
        calc ∑ u ∈ S, ((P i ∪ P (i + 2)).filter (G.Adj u)).card
            ≤ ∑ _u ∈ S, (P (i + 2)).card := by
              refine Finset.sum_le_sum fun u hu => Finset.card_le_card ?_
              intro w hw
              obtain ⟨hwU, huw⟩ := Finset.mem_filter.mp hw
              rcases Finset.mem_union.mp hwU with hwi | hwi2
              · exfalso
                have hadj := hc u w huw
                rw [(Finset.mem_filter.mp (hSsub hu)).2, (Finset.mem_filter.mp hwi).2] at hadj
                fin_cases i <;> simp at hadj
              · exact hwi2
          _ = (k - s) * (P (i + 2)).card := by rw [Finset.sum_const, hScard, smul_eq_mul]
      have h25 := two_fifths_prod n k s (by omega) (by omega) hi
      have h2p : 2 * (P (i + 2)).card ≤ s := by omega
      have hmul : 2 * ((k - s) * (P (i + 2)).card) ≤ (k - s) * s := by
        calc 2 * ((k - s) * (P (i + 2)).card) = (k - s) * (2 * (P (i + 2)).card) := by ring
          _ ≤ (k - s) * s := Nat.mul_le_mul_left _ h2p
      exact (Nat.mul_le_mul_left 25 (by omega)).trans h25
    · -- Symmetrically add k - s vertices from P (i + 4); they only touch P i inside P i ∪ P (i + 2)
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
        (show k - s ≤ (P (i + 4)).card by omega)
      have hdisj : Disjoint (P i ∪ P (i + 2)) S := by
        refine Finset.disjoint_of_subset_right hSsub ?_
        rw [Finset.disjoint_union_left]
        exact ⟨hP_disj i (i + 4) (by fin_cases i <;> decide),
               hP_disj (i + 2) (i + 4) (by fin_cases i <;> decide)⟩
      have hSind : ∀ u ∈ S, ∀ w ∈ S, ¬ G.Adj u w := by
        intro u hu w hw huw
        have hadj := hc u w huw
        rw [(Finset.mem_filter.mp (hSsub hu)).2, (Finset.mem_filter.mp (hSsub hw)).2] at hadj
        fin_cases i <;> simp at hadj
      have hcardV : ((P i ∪ P (i + 2)) ∪ S).card = k := by
        rw [Finset.card_union_of_disjoint hdisj, hcard_pair, hScard]; omega
      refine sparse_of_finset G ((P i ∪ P (i + 2)) ∪ S) hcardV ?_
      rw [D_union G (P i ∪ P (i + 2)) S hdisj (hP_ind i), D_indep G S hSind, zero_add]
      have hbound : ∑ u ∈ S, ((P i ∪ P (i + 2)).filter (G.Adj u)).card ≤ (k - s) * (P i).card := by
        calc ∑ u ∈ S, ((P i ∪ P (i + 2)).filter (G.Adj u)).card
            ≤ ∑ _u ∈ S, (P i).card := by
              refine Finset.sum_le_sum fun u hu => Finset.card_le_card ?_
              intro w hw
              obtain ⟨hwU, huw⟩ := Finset.mem_filter.mp hw
              rcases Finset.mem_union.mp hwU with hwi | hwi2
              · exact hwi
              · exfalso
                have hadj := hc u w huw
                rw [(Finset.mem_filter.mp (hSsub hu)).2, (Finset.mem_filter.mp hwi2).2] at hadj
                fin_cases i <;> simp at hadj
          _ = (k - s) * (P i).card := by rw [Finset.sum_const, hScard, smul_eq_mul]
      have h25 := two_fifths_prod n k s (by omega) (by omega) hi
      have h2p : 2 * (P i).card ≤ s := by omega
      have hmul : 2 * ((k - s) * (P i).card) ≤ (k - s) * s := by
        calc 2 * ((k - s) * (P i).card) = (k - s) * (2 * (P i).card) := by ring
          _ ≤ (k - s) * s := Nat.mul_le_mul_left _ h2p
      exact (Nat.mul_le_mul_left 25 (by omega)).trans h25

/-! ## Part 3: Häggkvist's theorem (δ(G) > 3n/8 → bipartite or homomorphic to C_5) -/

-- A closed walk of length L ≥ 1 yields a cyclic sequence of adjacent vertices.
lemma cyclic_of_walk {V : Type} {G : SimpleGraph V} {u : V} (p : G.Walk u u) (hpos : 0 < p.length) :
    ∃ f : ℕ → V, ∀ i < p.length, G.Adj (f i) (f ((i + 1) % p.length)) := by
  refine ⟨fun i => p.getVert i, fun i hi => ?_⟩
  by_cases hlast : i + 1 = p.length
  · rw [hlast, Nat.mod_self]
    have h1 := p.adj_getVert_succ hi
    rw [hlast, SimpleGraph.Walk.getVert_length] at h1
    simpa [SimpleGraph.Walk.getVert_zero] using h1
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact p.adj_getVert_succ hi

-- Absence of odd cyclic walks implies bipartiteness (hence a homomorphism to C_5).
lemma bipartite_of_no_odd_cycle {V : Type} (G : SimpleGraph V)
    (hno : ∀ L, Odd L → ¬ ∃ f : ℕ → V, ∀ i < L, G.Adj (f i) (f ((i + 1) % L))) :
    ∃ c : V → Fin 5, ∀ u v, G.Adj u v → c u + 1 = c v ∨ c v + 1 = c u := by
  classical
  have hno_walk : ∀ (u : V) (p : G.Walk u u), ¬ Odd p.length := by
    intro u p hodd
    have hpos : 0 < p.length := by rcases hodd with ⟨m, hm⟩; omega
    exact hno p.length hodd (cyclic_of_walk p hpos)
  -- For each connected component, pick a canonical representative and walk to every vertex in it.
  let rep : G.ConnectedComponent → V := fun comp => Quot.out comp
  have hreach : ∀ v : V, G.Reachable (rep (G.connectedComponentMk v)) v := by
    intro v
    have heq : G.connectedComponentMk (rep (G.connectedComponentMk v)) = G.connectedComponentMk v :=
      Quot.out_eq (G.connectedComponentMk v)
    exact SimpleGraph.ConnectedComponent.exact heq
  let distParity : V → Bool := fun v =>
    decide (Even (Classical.choice (hreach v)).length)
  refine ⟨fun v => if distParity v then 0 else 1, fun u v huv => ?_⟩
  have hcomp : G.connectedComponentMk u = G.connectedComponentMk v :=
    SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable huv)
  have hsame : rep (G.connectedComponentMk u) = rep (G.connectedComponentMk v) := by rw [hcomp]
  set p := Classical.choice (hreach u) with hp_def
  set q := Classical.choice (hreach v) with hq_def
  let q' : G.Walk (rep (G.connectedComponentMk u)) v := q.copy hsame.symm rfl
  have hqlen : q'.length = q.length := SimpleGraph.Walk.length_copy q hsame.symm rfl
  let w : G.Walk (rep (G.connectedComponentMk u)) (rep (G.connectedComponentMk u)) :=
    p.append (SimpleGraph.Walk.cons huv q'.reverse)
  have hw_len : w.length = p.length + 1 + q.length := by
    simp only [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_reverse, hqlen]
    omega
  have hnotodd := hno_walk _ w
  rw [hw_len] at hnotodd
  have hdiff : distParity u ≠ distParity v := by
    intro heq
    dsimp only [distParity] at heq
    rw [decide_eq_decide, ← hp_def, ← hq_def] at heq
    apply hnotodd
    rcases Nat.even_or_odd p.length with hp | hp
    · have hq := heq.mp hp
      rcases hp with ⟨a, ha⟩; rcases hq with ⟨b, hb⟩
      exact ⟨a + b, by omega⟩
    · have hq : Odd q.length := by
        rcases Nat.even_or_odd q.length with hqe | hqo
        · exfalso; exact (Nat.not_even_iff_odd.mpr hp) (heq.mpr hqe)
        · exact hqo
      rcases hp with ⟨a, ha⟩; rcases hq with ⟨b, hb⟩
      exact ⟨a + b + 1, by omega⟩
  cases hu : distParity u <;> cases hv : distParity v <;> simp_all

-- Helper: a vertex x adjacent to two vertices at arc distance d along a cyclic walk creates a
-- cyclic walk of length d + 2.
lemma arc_cycle {V : Type} {G : SimpleGraph V} {L : ℕ} (hL : 0 < L) (f : ℕ → V)
    (hf : ∀ i < L, G.Adj (f i) (f ((i + 1) % L))) (x : V) (s d : ℕ) (hd : 0 < d)
    (hs : G.Adj x (f (s % L))) (he : G.Adj x (f ((s + d) % L))) :
    ∃ g : ℕ → V, ∀ t < d + 2, G.Adj (g t) (g ((t + 1) % (d + 2))) := by
  refine ⟨fun t => if t = 0 then x else f ((s + t - 1) % L), fun t ht => ?_⟩
  by_cases ht0 : t = 0
  · subst ht0
    have h1 : (0 + 1) % (d + 2) = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    simpa using hs
  · by_cases htlast : t = d + 1
    · subst htlast
      have h1 : (d + 1 + 1) % (d + 2) = 0 := Nat.mod_self _
      rw [h1]
      have h2 : s + (d + 1) - 1 = s + d := by omega
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, h2]
      exact he.symm
    · have h1 : (t + 1) % (d + 2) = t + 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1]
      simp only [ht0, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      have hmod := hf ((s + t - 1) % L) (Nat.mod_lt _ hL)
      have hstep : ((s + t - 1) % L + 1) % L = (s + (t + 1) - 1) % L := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1; omega
      rw [hstep] at hmod
      exact hmod

-- Any triangle-free graph with δ > 3n/8 is either homomorphic to C_5 (via bipartiteness) or
-- contains a 5-cycle.
lemma bipartite_or_C5 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcf : G.CliqueFree 3)
    (hdeg : ∀ v : V, 3 * Fintype.card V < 8 * ((univ : Finset V).filter (G.Adj v)).card) :
    (∃ c : V → Fin 5, ∀ u v, G.Adj u v → c u + 1 = c v ∨ c v + 1 = c u) ∨
      ∃ v : Fin 5 → V, ∀ i : Fin 5, G.Adj (v i) (v (i + 1)) := by
  classical
  by_cases hodd : ∃ L, Odd L ∧ ∃ f : ℕ → V, ∀ i < L, G.Adj (f i) (f ((i + 1) % L))
  · right
    set L := Nat.find hodd with hL_def
    have hL_spec : Odd L ∧ ∃ f : ℕ → V, ∀ i < L, G.Adj (f i) (f ((i + 1) % L)) :=
      Nat.find_spec hodd
    have hL_min : ∀ L' < L, Odd L' → ¬ ∃ f : ℕ → V, ∀ i < L', G.Adj (f i) (f ((i + 1) % L')) :=
      fun L' hlt ho => fun hex => Nat.find_min hodd hlt ⟨ho, hex⟩
    obtain ⟨hL_odd, f, hf⟩ := hL_spec
    have hL_ne1 : L ≠ 1 := by
      intro h1
      have h0 := hf 0 (by omega)
      rw [h1] at h0; norm_num at h0
    have hL_ne3 : L ≠ 3 := by
      intro h3
      have e0 := hf 0 (by omega)
      have e1 := hf 1 (by omega)
      have e2 := hf 2 (by omega)
      rw [h3] at e0 e1 e2; norm_num at e0 e1 e2
      exact hcf {f 0, f 1, f 2} (SimpleGraph.is3Clique_triple_iff.mpr ⟨e0, e2.symm, e1⟩)
    have hL_ge5 : 5 ≤ L := by rcases hL_odd with ⟨m, hm⟩; omega
    by_cases hL5 : L = 5
    · refine ⟨fun i => f i.1, fun i => ?_⟩
      have h := hf i.1 (by omega)
      rw [hL5] at h
      have hval : (i + 1 : Fin 5).1 = (i.1 + 1) % 5 := rfl
      rw [← hval] at h
      exact h
    · exfalso
      have hL7 : 7 ≤ L := by rcases hL_odd with ⟨m, hm⟩; omega
      -- Step 1: f is injective on Fin L
      have hinj : ∀ a b : Fin L, f a.1 = f b.1 → a = b := by
        have hlt_ne : ∀ i j, i < j → j < L → f i ≠ f j := by
          intro i j hij hjL heq
          set L1 := j - i
          set L2 := L - (j - i)
          have h12 : L1 + L2 = L := by omega
          have hex1 : ∃ g : ℕ → V, ∀ t < L1, G.Adj (g t) (g ((t + 1) % L1)) := by
            refine ⟨fun t => f (i + t), fun t ht => ?_⟩
            by_cases hlast : t + 1 = L1
            · dsimp only; rw [hlast, Nat.mod_self, add_zero]
              have h := hf (i + t) (by omega)
              have e1 : (i + t + 1) % L = j := by rw [Nat.mod_eq_of_lt (by omega)]; omega
              rw [e1, ← heq] at h; exact h
            · dsimp only; rw [Nat.mod_eq_of_lt (by omega)]
              have h := hf (i + t) (by omega)
              have e1 : (i + t + 1) % L = i + (t + 1) := by rw [Nat.mod_eq_of_lt (by omega)]; omega
              rw [e1] at h; exact h
          have hex2 : ∃ g : ℕ → V, ∀ t < L2, G.Adj (g t) (g ((t + 1) % L2)) := by
            refine ⟨fun t => if t < i then f t else f (t + L1), fun t ht => ?_⟩
            by_cases hlast : t + 1 = L2
            · rw [hlast, Nat.mod_self]
              have hge : ¬ t < i := by omega
              simp only [hge, ↓reduceIte]
              have h := hf (L - 1) (by omega)
              have e1 : (L - 1 + 1) % L = 0 := by
                have : L - 1 + 1 = L := by omega
                rw [this, Nat.mod_self]
              rw [e1] at h
              have e2 : t + L1 = L - 1 := by omega
              rw [e2]
              by_cases hi0 : 0 < i
              · simp [hi0, h]
              · have hi0' : i = 0 := by omega
                simp only [hi0, ↓reduceIte, zero_add]
                have e3 : L1 = j := by omega
                rw [e3, ← heq, hi0']; exact h
            · rw [Nat.mod_eq_of_lt (by omega)]
              by_cases ht1 : t + 1 < i
              · have ht0 : t < i := by omega
                simp only [ht0, ht1, ↓reduceIte]
                have h := hf t (by omega)
                rw [Nat.mod_eq_of_lt (by omega)] at h; exact h
              · by_cases ht0 : t < i
                · simp only [ht0, ht1, ↓reduceIte]
                  have hti : t + 1 = i := by omega
                  have h := hf t (by omega)
                  rw [Nat.mod_eq_of_lt (by omega), hti, heq] at h
                  have e1 : t + 1 + L1 = j := by omega
                  rw [e1]; exact h
                · simp only [ht0, ht1, ↓reduceIte]
                  have h := hf (t + L1) (by omega)
                  have e1 : (t + L1 + 1) % L = t + 1 + L1 := by
                    rw [Nat.mod_eq_of_lt (by omega)]; omega
                  rw [e1] at h; exact h
          rcases Nat.even_or_odd L1 with h1e | h1o
          · have h2o : Odd L2 := by
              rcases h1e with ⟨a, ha⟩; rcases hL_odd with ⟨b, hb⟩; exact ⟨b - a, by omega⟩
            exact hL_min L2 (by omega) h2o hex2
          · exact hL_min L1 (by omega) h1o hex1
        intro a b hab
        rcases lt_trichotomy a.1 b.1 with hlt | heq | hgt
        · exact absurd hab (hlt_ne a.1 b.1 hlt b.2)
        · exact Fin.ext heq
        · exact absurd hab.symm (hlt_ne b.1 a.1 hgt a.2)
      -- Step 2: Every vertex x has at most 2 neighbors among {f i | i : Fin L}
      have hnb_le2 : ∀ x : V, ((univ : Finset (Fin L)).filter (fun i => G.Adj x (f i.1))).card ≤ 2 := by
        intro x
        by_contra hgt
        push_neg at hgt
        have h3 : 3 ≤ ((univ : Finset (Fin L)).filter (fun i => G.Adj x (f i.1))).card := hgt
        obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq h3
        -- Extract three distinct elements of T, sorted by value
        obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :
            ∃ a ∈ T, ∃ b ∈ T, ∃ c ∈ T, a.1 < b.1 ∧ b.1 < c.1 ∧ c.1 < L := by
          obtain ⟨u, hu, hT1⟩ : ∃ u ∈ T, (T.erase u).card = 2 := by
            obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
            exact ⟨u, hu, by rw [Finset.card_erase_of_mem hu, hTcard]⟩
          obtain ⟨v, hv, hT2⟩ : ∃ v ∈ T.erase u, ((T.erase u).erase v).card = 1 := by
            obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (T.erase u).card)
            exact ⟨v, hv, by rw [Finset.card_erase_of_mem hv, hT1]⟩
          obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hT2
          have hw' : w ∈ (T.erase u).erase v := by rw [hw]; simp
          have hvT : v ∈ T := Finset.mem_of_mem_erase hv
          have hwT : w ∈ T := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw')
          have huv : u ≠ v := (Finset.mem_erase.mp hv).1.symm
          have hvw : v ≠ w := (Finset.mem_erase.mp hw').1.symm
          have huw : u ≠ w := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hw')).1.symm
          have ne1 : u.1 ≠ v.1 := fun e => huv (Fin.ext e)
          have ne2 : v.1 ≠ w.1 := fun e => hvw (Fin.ext e)
          have ne3 : u.1 ≠ w.1 := fun e => huw (Fin.ext e)
          rcases lt_or_gt_of_ne ne1 with h1 | h1 <;>
          rcases lt_or_gt_of_ne ne2 with h2 | h2 <;>
          rcases lt_or_gt_of_ne ne3 with h3' | h3'
          · exact ⟨u, hu, v, hvT, w, hwT, h1, h2, w.2⟩
          · omega
          · exact ⟨u, hu, w, hwT, v, hvT, h3', h2, v.2⟩
          · exact ⟨w, hwT, u, hu, v, hvT, h3', h1, v.2⟩
          · exact ⟨v, hvT, u, hu, w, hwT, h1, h3', w.2⟩
          · exact ⟨v, hvT, w, hwT, u, hu, h2, h3', u.2⟩
          · omega
          · exact ⟨w, hwT, v, hvT, u, hu, h2, h1, u.2⟩
        have hxa : G.Adj x (f a.1) := (Finset.mem_filter.mp (hTsub ha)).2
        have hxb : G.Adj x (f b.1) := (Finset.mem_filter.mp (hTsub hb)).2
        have hxc : G.Adj x (f c.1) := (Finset.mem_filter.mp (hTsub hc)).2
        set d1 := b.1 - a.1
        set d2 := c.1 - b.1
        set d3 := L - (c.1 - a.1)
        have hd1_ge2 : 2 ≤ d1 := by
          by_contra h1
          have : b.1 = a.1 + 1 := by omega
          have hadj := hf a.1 a.2
          rw [Nat.mod_eq_of_lt (by omega), ← this] at hadj
          exact hcf {x, f a.1, f b.1} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxa, hxb, hadj⟩)
        have hd2_ge2 : 2 ≤ d2 := by
          by_contra h1
          have : c.1 = b.1 + 1 := by omega
          have hadj := hf b.1 b.2
          rw [Nat.mod_eq_of_lt (by omega), ← this] at hadj
          exact hcf {x, f b.1, f c.1} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxb, hxc, hadj⟩)
        have hd3_ge2 : 2 ≤ d3 := by
          by_contra h1
          have hcL : c.1 = L - 1 := by omega
          have ha0 : a.1 = 0 := by omega
          have hadj := hf c.1 c.2
          have e1 : (c.1 + 1) % L = a.1 := by rw [hcL, ha0, show L - 1 + 1 = L by omega, Nat.mod_self]
          rw [e1] at hadj
          exact hcf {x, f c.1, f a.1} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxc, hxa, hadj⟩)
        have hsumd : d1 + d2 + d3 = L := by omega
        -- One of d1, d2, d3 is odd, giving a shorter odd cyclic walk!
        rcases Nat.even_or_odd d1 with h1e | h1o
        · rcases Nat.even_or_odd d2 with h2e | h2o
          · have h3o : Odd d3 := by
              rcases h1e with ⟨p, hp⟩; rcases h2e with ⟨q, hq⟩; rcases hL_odd with ⟨r, hr⟩
              exact ⟨r - p - q, by omega⟩
            have h3o2 : Odd (d3 + 2) := by rcases h3o with ⟨p, hp⟩; exact ⟨p + 1, by omega⟩
            have e1 : c.1 % L = c.1 := Nat.mod_eq_of_lt c.2
            have e2 : (c.1 + d3) % L = a.1 := by
              have : c.1 + d3 = L + a.1 := by omega
              rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt a.2]
            exact hL_min (d3 + 2) (by omega) h3o2
              (arc_cycle (by omega) f hf x c.1 d3 (by omega) (by rw [e1]; exact hxc) (by rw [e2]; exact hxa))
          · have h2o2 : Odd (d2 + 2) := by rcases h2o with ⟨p, hp⟩; exact ⟨p + 1, by omega⟩
            have e1 : b.1 % L = b.1 := Nat.mod_eq_of_lt b.2
            have e2 : (b.1 + d2) % L = c.1 := by
              have : b.1 + d2 = c.1 := by omega
              rw [this, Nat.mod_eq_of_lt c.2]
            exact hL_min (d2 + 2) (by omega) h2o2
              (arc_cycle (by omega) f hf x b.1 d2 (by omega) (by rw [e1]; exact hxb) (by rw [e2]; exact hxc))
        · have h1o2 : Odd (d1 + 2) := by rcases h1o with ⟨p, hp⟩; exact ⟨p + 1, by omega⟩
          have e1 : a.1 % L = a.1 := Nat.mod_eq_of_lt a.2
          have e2 : (a.1 + d1) % L = b.1 := by
            have : a.1 + d1 = b.1 := by omega
            rw [this, Nat.mod_eq_of_lt b.2]
          exact hL_min (d1 + 2) (by omega) h1o2
            (arc_cycle (by omega) f hf x a.1 d1 (by omega) (by rw [e1]; exact hxa) (by rw [e2]; exact hxb))
      -- Step 3: Double-count edges between C and V: L * (3n/8) < ∑ deg ≤ 2n, contradicting L ≥ 7
      have hdouble : ∑ i : Fin L, ((univ : Finset V).filter (G.Adj (f i.1))).card =
          ∑ x : V, ((univ : Finset (Fin L)).filter (fun i => G.Adj x (f i.1))).card := by
        simp only [Finset.card_filter]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [G.adj_comm]
      have hupper : ∑ i : Fin L, ((univ : Finset V).filter (G.Adj (f i.1))).card ≤ 2 * Fintype.card V := by
        rw [hdouble]
        calc ∑ x : V, ((univ : Finset (Fin L)).filter (fun i => G.Adj x (f i.1))).card
            ≤ ∑ _x : V, 2 := Finset.sum_le_sum fun x _ => hnb_le2 x
          _ = 2 * Fintype.card V := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      have hlower : L * (3 * Fintype.card V + 1) ≤
          8 * ∑ i : Fin L, ((univ : Finset V).filter (G.Adj (f i.1))).card := by
        calc L * (3 * Fintype.card V + 1)
            = ∑ _i : Fin L, (3 * Fintype.card V + 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          _ ≤ ∑ i : Fin L, 8 * ((univ : Finset V).filter (G.Adj (f i.1))).card :=
              Finset.sum_le_sum fun i _ => hdeg (f i.1)
          _ = 8 * ∑ i : Fin L, ((univ : Finset V).filter (G.Adj (f i.1))).card := by
              rw [Finset.mul_sum]
      nlinarith
  · left
    exact bipartite_of_no_odd_cycle G (fun L hL hex => hodd ⟨L, hL, hex⟩)

-- Finite Fin 5 check for Häggkvist's homomorphism on edges.
lemma fin5_haggkvist_check : ∀ (S1 S2 : Finset (Fin 5)),
    (∀ j : Fin 5, j + 4 ∈ S1 ∪ S2 ∨ j + 1 ∈ S1 ∪ S2) →
    ∀ c1 c2 : Fin 5,
      (S1 = {c1 + 4, c1 + 1} ∨ S1 = {c1 + 4}) →
      (S2 = {c2 + 4, c2 + 1} ∨ S2 = {c2 + 4}) →
      c1 + 1 = c2 ∨ c2 + 1 = c1 := by
  intro S1 S2 hhit c1 c2 h1 h2
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
    (simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hhit;
     revert hhit c1 c2; decide)

lemma fin5_indep_classify : ∀ (S : Finset (Fin 5)), S.Nonempty →
    (∀ a ∈ S, ∀ b ∈ S, a + 1 ≠ b) →
    ∃ c : Fin 5, S = {c + 4, c + 1} ∨ S = {c + 4} := by
  intro S hne hind
  obtain ⟨x, hx⟩ := hne
  have h1 : x + 1 ∉ S := fun h => hind x hx (x + 1) h rfl
  have h4 : x + 4 ∉ S := fun h => hind (x + 4) h x hx (by fin_cases x <;> decide)
  have hmem : ∀ y : Fin 5, y = x ∨ y = x + 1 ∨ y = x + 2 ∨ y = x + 3 ∨ y = x + 4 := by
    intro y; fin_cases x <;> fin_cases y <;> decide
  by_cases h2 : x + 2 ∈ S
  · have h3 : x + 3 ∉ S := fun h => hind (x + 2) h2 (x + 3) h (by fin_cases x <;> decide)
    refine ⟨x + 1, Or.inl ?_⟩
    ext y
    have e1 : x + 1 + 4 = x := by fin_cases x <;> decide
    have e2 : x + 1 + 1 = x + 2 := by fin_cases x <;> decide
    rw [e1, e2, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hy
      rcases hmem y with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hy h1
      · exact Or.inr rfl
      · exact absurd hy h3
      · exact absurd hy h4
    · rintro (rfl | rfl) <;> assumption
  · by_cases h3 : x + 3 ∈ S
    · refine ⟨x + 4, Or.inl ?_⟩
      ext y
      have e1 : x + 4 + 4 = x + 3 := by fin_cases x <;> decide
      have e2 : x + 4 + 1 = x := by fin_cases x <;> decide
      rw [e1, e2, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hy
        rcases hmem y with rfl | rfl | rfl | rfl | rfl
        · exact Or.inr rfl
        · exact absurd hy h1
        · exact absurd hy h2
        · exact Or.inl rfl
        · exact absurd hy h4
      · rintro (rfl | rfl) <;> assumption
    · refine ⟨x + 1, Or.inr ?_⟩
      ext y
      have e1 : x + 1 + 4 = x := by fin_cases x <;> decide
      rw [e1, Finset.mem_singleton]
      constructor
      · intro hy
        rcases hmem y with rfl | rfl | rfl | rfl | rfl
        · rfl
        · exact absurd hy h1
        · exact absurd hy h2
        · exact absurd hy h3
        · exact absurd hy h4
      · rintro rfl; exact hx

-- Häggkvist's theorem: a triangle-free graph with δ > 3n/8 containing a C_5 is homomorphic to C_5.
lemma haggkvist_of_C5 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcf : G.CliqueFree 3)
    (hdeg : ∀ v : V, 3 * Fintype.card V < 8 * ((univ : Finset V).filter (G.Adj v)).card)
    (v : Fin 5 → V) (hv : ∀ i : Fin 5, G.Adj (v i) (v (i + 1))) :
    ∃ c : V → Fin 5, ∀ u w, G.Adj u w → c u + 1 = c w ∨ c w + 1 = c u := by
  classical
  set n := Fintype.card V with hn
  let A : Fin 5 → Finset V := fun i =>
    (univ : Finset V).filter (fun x => G.Adj x (v (i + 4)) ∧ G.Adj x (v (i + 1)))
  have hv_adj_prev : ∀ i : Fin 5, G.Adj (v i) (v (i + 4)) := by
    intro i
    have h := hv (i + 4)
    have e : i + 4 + 1 = i := by fin_cases i <;> decide
    rw [e] at h; exact h.symm
  have hv_mem : ∀ i : Fin 5, v i ∈ A i := by
    intro i
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv_adj_prev i, hv i⟩
  -- No vertex is adjacent to two consecutive vertices of the C_5
  have hno_consec : ∀ (x : V) (i : Fin 5), ¬ (G.Adj x (v i) ∧ G.Adj x (v (i + 1))) := by
    intro x i ⟨h1, h2⟩
    exact hcf {x, v i, v (i + 1)} (SimpleGraph.is3Clique_triple_iff.mpr ⟨h1, h2, hv i⟩)
  -- The 5 sets A i are pairwise disjoint
  have hA_disj : ∀ i j : Fin 5, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hxi).2
    obtain ⟨h3, h4⟩ := (Finset.mem_filter.mp hxj).2
    have hcases : j = i + 1 ∨ j = i + 2 ∨ j = i + 3 ∨ j = i + 4 := by
      fin_cases i <;> fin_cases j <;> simp_all
    rcases hcases with rfl | rfl | rfl | rfl
    · have e : i + 1 + 4 = i := by fin_cases i <;> decide
      have e2 : i + 4 + 1 = i := by fin_cases i <;> decide
      rw [e] at h3
      exact hno_consec x (i + 4) ⟨h1, by rw [e2]; exact h3⟩
    · have e2 : i + 2 + 1 = i + 3 := by fin_cases i <;> decide
      have e3 : i + 3 + 1 = i + 4 := by fin_cases i <;> decide
      rw [e2] at h4
      exact hno_consec x (i + 3) ⟨h4, by rw [e3]; exact h1⟩
    · have e : i + 3 + 4 = i + 2 := by fin_cases i <;> decide
      rw [e] at h3
      exact hno_consec x (i + 1) ⟨h2, by
        have e2 : i + 1 + 1 = i + 2 := by fin_cases i <;> decide
        rw [e2]; exact h3⟩
    · have e : i + 4 + 1 = i := by fin_cases i <;> decide
      rw [e] at h4
      exact hno_consec x i ⟨h4, h2⟩
  -- Adjacency inside A is restricted to consecutive indices
  have hA_adj : ∀ (i j : Fin 5) (x : V), x ∈ A i → ∀ y ∈ A j, G.Adj x y →
      i + 1 = j ∨ j + 1 = i := by
    intro i j x hxi y hyj hxy
    obtain ⟨hx1, hx2⟩ := (Finset.mem_filter.mp hxi).2
    obtain ⟨hy1, hy2⟩ := (Finset.mem_filter.mp hyj).2
    by_contra hnot
    have hcases : j = i ∨ j = i + 2 ∨ j = i + 3 := by
      fin_cases i <;> fin_cases j <;> simp_all
    rcases hcases with rfl | rfl | rfl
    · exact hcf {x, y, v (j + 1)} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hx2, hy2⟩)
    · have e : i + 2 + 4 = i + 1 := by fin_cases i <;> decide
      rw [e] at hy1
      exact hcf {x, y, v (i + 1)} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hx2, hy1⟩)
    · have e : i + 3 + 1 = i + 4 := by fin_cases i <;> decide
      rw [e] at hy2
      exact hcf {x, y, v (i + 4)} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy, hx1, hy2⟩)
  -- Union Aall and remainder R
  set Aall := (univ : Finset (Fin 5)).biUnion A with hAall
  set R := (univ : Finset V) \ Aall with hR
  have hdisj_AR : Disjoint Aall R := Finset.disjoint_sdiff
  have hunion_AR : Aall ∪ R = univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hAR_card : Aall.card + R.card = n := by
    rw [← Finset.card_union_of_disjoint hdisj_AR, hunion_AR, Finset.card_univ]
  -- Count edges between C_5 and V to prove 8 * R.card + 5 ≤ n
  have hR_small : 8 * R.card + 5 ≤ n := by
    have hcnt_x : ∀ x : V, ((univ : Finset (Fin 5)).filter (fun i => G.Adj x (v i))).card ≤
        if x ∈ Aall then 2 else 1 := by
      intro x
      set T := (univ : Finset (Fin 5)).filter (fun i => G.Adj x (v i))
      have hTind : ∀ a ∈ T, ∀ b ∈ T, a + 1 ≠ b := by
        intro a ha b hb hab
        have h1 := (Finset.mem_filter.mp ha).2
        have h2 := (Finset.mem_filter.mp hb).2
        rw [← hab] at h2
        exact hno_consec x a ⟨h1, h2⟩
      have hT_le2 : T.card ≤ 2 := by
        rcases T.eq_empty_or_nonempty with hTe | hTne
        · simp [hTe]
        · obtain ⟨i, hi | hi⟩ := fin5_indep_classify T hTne hTind
          · rw [hi]; exact Finset.card_le_two
          · rw [hi, Finset.card_singleton]; omega
      split_ifs with hxA
      · exact hT_le2
      · by_contra hgt
        have hT2 : T.card = 2 := by omega
        have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨i, hi | hi⟩ := fin5_indep_classify T hTne hTind
        · have hxAi : x ∈ A i := by
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
            have m1 : i + 4 ∈ T := by rw [hi]; simp
            have m2 : i + 1 ∈ T := by rw [hi]; simp
            exact ⟨(Finset.mem_filter.mp m1).2, (Finset.mem_filter.mp m2).2⟩
          exact hxA (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxAi⟩)
        · rw [hi, Finset.card_singleton] at hT2; omega
    have hdouble : ∑ i : Fin 5, ((univ : Finset V).filter (G.Adj (v i))).card =
        ∑ x : V, ((univ : Finset (Fin 5)).filter (fun i => G.Adj x (v i))).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
      simp only [G.adj_comm]
    have hupper : ∑ i : Fin 5, ((univ : Finset V).filter (G.Adj (v i))).card ≤ 2 * Aall.card + R.card := by
      rw [hdouble]
      calc ∑ x : V, ((univ : Finset (Fin 5)).filter (fun i => G.Adj x (v i))).card
          ≤ ∑ x : V, (if x ∈ Aall then 2 else 1) := Finset.sum_le_sum fun x _ => hcnt_x x
        _ = ∑ x ∈ Aall, 2 + ∑ x ∈ R, 1 := by
            rw [← hunion_AR, Finset.sum_union hdisj_AR]
            congr 1
            · refine Finset.sum_congr rfl fun x hx => by simp [hx]
            · refine Finset.sum_congr rfl fun x hx => ?_
              have hx' : x ∉ Aall := Finset.disjoint_right.mp hdisj_AR hx
              simp [hx']
        _ = 2 * Aall.card + R.card := by
            rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]; ring
    have hlower : 5 * (3 * n + 1) ≤ 8 * ∑ i : Fin 5, ((univ : Finset V).filter (G.Adj (v i))).card := by
      calc 5 * (3 * n + 1) = ∑ _i : Fin 5, (3 * n + 1) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        _ ≤ ∑ i : Fin 5, 8 * ((univ : Finset V).filter (G.Adj (v i))).card :=
            Finset.sum_le_sum fun i _ => hdeg (v i)
        _ = 8 * ∑ i : Fin 5, ((univ : Finset V).filter (G.Adj (v i))).card := by rw [Finset.mul_sum]
    omega
  -- Key triple-disjointness contradiction lemma
  have htriple : ∀ x y z : V, G.Adj x y →
      Disjoint (Aall.filter (G.Adj x)) (Aall.filter (G.Adj y)) →
      Disjoint (Aall.filter (G.Adj x)) (Aall.filter (G.Adj z)) →
      Disjoint (Aall.filter (G.Adj y)) (Aall.filter (G.Adj z)) → False := by
    intro x y z hxy hdxy hdxz hdyz
    have hdeg_split : ∀ w : V, ((univ : Finset V).filter (G.Adj w)).card =
        (Aall.filter (G.Adj w)).card + (R.filter (G.Adj w)).card := by
      intro w
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj_AR),
        ← Finset.filter_union, hunion_AR]
    have hA3 : (Aall.filter (G.Adj x)).card + (Aall.filter (G.Adj y)).card +
        (Aall.filter (G.Adj z)).card ≤ Aall.card := by
      have hd12 : Disjoint (Aall.filter (G.Adj x) ∪ Aall.filter (G.Adj y)) (Aall.filter (G.Adj z)) :=
        Finset.disjoint_union_left.mpr ⟨hdxz, hdyz⟩
      have hsub : Aall.filter (G.Adj x) ∪ Aall.filter (G.Adj y) ∪ Aall.filter (G.Adj z) ⊆ Aall :=
        Finset.union_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
          (Finset.filter_subset _ _)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hd12, Finset.card_union_of_disjoint hdxy] at hc
      exact hc
    have hRxy : (R.filter (G.Adj x)).card + (R.filter (G.Adj y)).card ≤ R.card := by
      have hd : Disjoint (R.filter (G.Adj x)) (R.filter (G.Adj y)) := by
        rw [Finset.disjoint_left]
        intro t ht1 ht2
        exact hcf {x, y, t} (SimpleGraph.is3Clique_triple_iff.mpr
          ⟨hxy, (Finset.mem_filter.mp ht1).2, (Finset.mem_filter.mp ht2).2⟩)
      have hsub : R.filter (G.Adj x) ∪ R.filter (G.Adj y) ⊆ R :=
        Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hd] at hc
      exact hc
    have hRz : (R.filter (G.Adj z)).card ≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hdx := hdeg x
    have hdy := hdeg y
    have hdz := hdeg z
    rw [hdeg_split x] at hdx
    rw [hdeg_split y] at hdy
    rw [hdeg_split z] at hdz
    omega
  -- Helper: adjacent vertices have disjoint Aall-neighborhoods
  have hdisj_of_adj : ∀ x y : V, G.Adj x y →
      Disjoint (Aall.filter (G.Adj x)) (Aall.filter (G.Adj y)) := by
    intro x y hxy
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    exact hcf {x, y, t} (SimpleGraph.is3Clique_triple_iff.mpr
      ⟨hxy, (Finset.mem_filter.mp ht1).2, (Finset.mem_filter.mp ht2).2⟩)
  -- For each x : V, define S(x) = {i : Fin 5 | ∃ u ∈ A i, G.Adj x u}
  let S : V → Finset (Fin 5) := fun x =>
    (univ : Finset (Fin 5)).filter (fun i => ∃ u ∈ A i, G.Adj x u)
  -- Every vertex x has S(x) nonempty
  have hS_ne : ∀ x : V, (S x).Nonempty := by
    intro x
    have hdeg_split : ((univ : Finset V).filter (G.Adj x)).card =
        (Aall.filter (G.Adj x)).card + (R.filter (G.Adj x)).card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj_AR),
        ← Finset.filter_union, hunion_AR]
    have hdx := hdeg x
    rw [hdeg_split] at hdx
    have hRx : (R.filter (G.Adj x)).card ≤ R.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hpos : 0 < (Aall.filter (G.Adj x)).card := by omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
    obtain ⟨huA, hxu⟩ := Finset.mem_filter.mp hu
    obtain ⟨i, -, hui⟩ := Finset.mem_biUnion.mp huA
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hui, hxu⟩⟩
  -- For every x, S(x) is independent in C_5 (no i and i + 1 both in S(x))
  have hS_ind : ∀ x : V, ∀ a ∈ S x, ∀ b ∈ S x, a + 1 ≠ b := by
    intro x a ha b hb hab
    subst hab
    obtain ⟨u, hua, hxu⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨w, hwb, hxw⟩ := (Finset.mem_filter.mp hb).2
    have hdisj_uw : Disjoint (Aall.filter (G.Adj u)) (Aall.filter (G.Adj w)) := by
      rw [Finset.disjoint_left]
      intro t htu htw
      obtain ⟨htA, hut⟩ := Finset.mem_filter.mp htu
      obtain ⟨-, hwt⟩ := Finset.mem_filter.mp htw
      obtain ⟨k, -, htk⟩ := Finset.mem_biUnion.mp htA
      have h1 := hA_adj a k u hua t htk hut
      have h2 := hA_adj (a + 1) k w hwb t htk hwt
      have hcontra : ∀ a k : Fin 5, (a + 1 = k ∨ k + 1 = a) →
          (a + 1 + 1 = k ∨ k + 1 = a + 1) → False := by decide
      exact hcontra a k h1 h2
    exact htriple x u w hxu (hdisj_of_adj x u hxu) (hdisj_of_adj x w hxw) hdisj_uw
  -- For any adjacent x, y, S(x) ∪ S(y) hits {j + 4, j + 1} for every j : Fin 5
  have hS_hit : ∀ x y : V, G.Adj x y → ∀ j : Fin 5, j + 4 ∈ S x ∪ S y ∨ j + 1 ∈ S x ∪ S y := by
    intro x y hxy j
    by_contra hmiss
    push_neg at hmiss
    obtain ⟨hm1, hm2⟩ := hmiss
    have hdj : ∀ w : V, j + 4 ∉ S w → j + 1 ∉ S w →
        Disjoint (Aall.filter (G.Adj w)) (Aall.filter (G.Adj (v j))) := by
      intro w h1 h2
      rw [Finset.disjoint_left]
      intro t htw htv
      obtain ⟨htA, hwt⟩ := Finset.mem_filter.mp htw
      obtain ⟨-, hvt⟩ := Finset.mem_filter.mp htv
      obtain ⟨k, -, htk⟩ := Finset.mem_biUnion.mp htA
      have hk := hA_adj j k (v j) (hv_mem j) t htk hvt
      rcases hk with rfl | hk2
      · exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htk, hwt⟩)
      · have hprev : ∀ j k : Fin 5, k + 1 = j → k = j + 4 := by decide
        have ek : k = j + 4 := hprev j k hk2
        subst ek
        exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htk, hwt⟩)
    have hx1 : j + 4 ∉ S x := fun h => hm1 (Finset.mem_union_left _ h)
    have hx2 : j + 1 ∉ S x := fun h => hm2 (Finset.mem_union_left _ h)
    have hy1 : j + 4 ∉ S y := fun h => hm1 (Finset.mem_union_right _ h)
    have hy2 : j + 1 ∉ S y := fun h => hm2 (Finset.mem_union_right _ h)
    exact htriple x y (v j) hxy (hdisj_of_adj x y hxy) (hdj x hx1 hx2) (hdj y hy1 hy2)
  -- Assign every vertex x a color c(x) : Fin 5 directly from S(x)!
  -- Notice that for x ∈ A i, S(x) ⊆ {i + 4, i + 1} (and in fact v (i+4) ∈ A (i+4), v (i+1) ∈ A (i+1),
  -- so S(x) = {i + 4, i + 1} automatically!). So ONE uniform formula handles ALL vertices x : V!
  let c : V → Fin 5 := fun x =>
    Classical.choose (fin5_indep_classify (S x) (hS_ne x) (hS_ind x))
  have hc_spec : ∀ x : V, S x = {c x + 4, c x + 1} ∨ S x = {c x + 4} :=
    fun x => Classical.choose_spec (fin5_indep_classify (S x) (hS_ne x) (hS_ind x))
  refine ⟨c, fun x y hxy => ?_⟩
  exact fin5_haggkvist_check (S x) (S y) (hS_hit x y hxy) (c x) (c y) (hc_spec x) (hc_spec y)

lemma min_deg_gt_three_eighths {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hcf : G.CliqueFree 3)
    (hdeg : ∀ v : V, 3 * Fintype.card V < 8 * (G.neighborSet v).ncard) :
    ∃ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V ∧
      50 * (G.induce V').edgeSet.ncard ≤ Fintype.card V ^ 2 := by
  have hdeg' : ∀ v : V, 3 * Fintype.card V < 8 * ((univ : Finset V).filter (G.Adj v)).card := by
    intro v
    rw [← ncard_neighborSet_eq_card_filter]
    exact hdeg v
  rcases bipartite_or_C5 G hcf hdeg' with ⟨c, hc⟩ | ⟨v, hv⟩
  · exact hom_C5_sparse_half G c hc
  · obtain ⟨c, hc⟩ := haggkvist_of_C5 G hcf hdeg' v hv
    exact hom_C5_sparse_half G c hc

/-! ## Main reduction -/

theorem main : H1 → H2 → H3 → OMA.R_Erdos128_erdos_128_R1_H2_R1.H2 := by
  intro h1 h2 h3 V _ G hcf hlow hhigh
  classical
  by_cases hmindeg : ∀ v : V, 3 * Fintype.card V < 8 * (G.neighborSet v).ncard
  · exact min_deg_gt_three_eighths G hcf hmindeg
  · push_neg at hmindeg
    by_cases hbigI : ∃ I : Set V, G.IsIndepSet I ∧ 5 * Fintype.card V ≤ 12 * I.ncard
    · obtain ⟨I, hIind, hIcard⟩ := hbigI
      set Ifin := I.toFinset with hIfin
      have hIfin_ind : ∀ u ∈ Ifin, ∀ w ∈ Ifin, ¬ G.Adj u w := by
        intro u hu w hw huv
        have hu' : u ∈ I := Set.mem_toFinset.mp hu
        have hw' : w ∈ I := Set.mem_toFinset.mp hw
        exact hIind hu' hw' (G.ne_of_adj huv) huv
      have hIfin_card : 5 * Fintype.card V ≤ 12 * Ifin.card := by
        rwa [Set.ncard_eq_toFinset_card' I] at hIcard
      exact indep_ge_five_twelfths G hcf hhigh Ifin hIfin_ind hIfin_card
    · push_neg at hbigI
      by_cases hmedI : ∃ I : Set V, G.IsIndepSet I ∧ 2 * Fintype.card V ≤ 5 * I.ncard
      · exact h1 V G hcf hlow hhigh hmindeg hmedI hbigI
      · push_neg at hmedI
        by_cases hmd514 : ∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard
        · exact h2 V G hcf hlow hhigh hmindeg hmd514 hmedI
        · push_neg at hmd514
          exact h3 V G hcf hlow hhigh hmd514 hmedI

end OMA.R_Erdos128_erdos_128_R1_H2_R1_H2_R1
