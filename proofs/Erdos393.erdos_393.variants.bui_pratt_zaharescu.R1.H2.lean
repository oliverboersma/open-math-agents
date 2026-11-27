import OMAReductions.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1
import Mathlib

/-! Cut `[N, 2N)` into blocks of length `M` and split each block by residue mod `r`.
In every cell, all elements of `S` after the two smallest ones are tops of a triple
`(n - v, n - u, n)` with `0 < u < v ≤ M` and `r ∣ u, v`, so they are counted by the hypothesis;
the two smallest elements of all cells give at most `2r(N/M + 2)`. -/

open Finset

namespace E393H2

lemma close_of_same_div {M n x : ℕ} (hxn : x ≤ n) (h : n / M = x / M) (hM : 0 < M) :
    n - x < M := by
  have h1 := Nat.div_add_mod n M
  have h2 := Nat.div_add_mod x M
  have h3 := Nat.mod_lt n hM
  rw [h] at h1
  generalize M * (x / M) = A at h1 h2
  omega

lemma dvd_sub_of_mod_eq {r n x : ℕ} (hxn : x ≤ n) (h : n % r = x % r) : r ∣ n - x :=
  (Nat.modEq_iff_dvd' hxn).mp h.symm

end E393H2

open E393H2 in
theorem OMA.solution : OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1.H2 := by
  intro r N M hr hM S hS K hK hcount
  classical
  set key : ℕ → ℕ × ℕ := fun n => (n / M, n % r) with hkey
  set p : ℕ → Prop := fun n => ∃ x ∈ S, ∃ y ∈ S, x < y ∧ y < n ∧ key x = key n ∧ key y = key n
    with hp
  set E := S.filter p with hE
  set G := S.filter (fun n => ¬ p n) with hG
  set P := ((Icc 1 M) ×ˢ (Icc 1 M)).filter
    (fun uv : ℕ × ℕ => uv.1 < uv.2 ∧ r ∣ uv.1 ∧ r ∣ uv.2) with hP
  set F : ℕ × ℕ → Finset ℕ := fun uv => S.filter (fun n => uv.2 ≤ n ∧ n - uv.1 ∈ S ∧ n - uv.2 ∈ S)
    with hF
  -- the excess elements are counted by the hypothesis
  have hEsub : E ⊆ P.biUnion F := by
    intro n hn
    rw [hE, mem_filter] at hn
    obtain ⟨hnS, x, hx, y, hy, hxy, hyn, hkx, hky⟩ := hn
    simp only [hkey, Prod.mk.injEq] at hkx hky
    rw [mem_biUnion]
    refine ⟨(n - y, n - x), ?_, ?_⟩
    · rw [hP, mem_filter, mem_product, mem_Icc, mem_Icc]
      have hlt := close_of_same_div (by omega : x ≤ n) hkx.1.symm hM
      exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega,
        dvd_sub_of_mod_eq (by omega) hky.2.symm, dvd_sub_of_mod_eq (by omega) hkx.2.symm⟩
    · rw [hF, mem_filter]
      refine ⟨hnS, by omega, ?_, ?_⟩
      · rwa [show n - (n - y) = y by omega]
      · rwa [show n - (n - x) = x by omega]
  have hEcard : (E.card : ℝ) ≤ (M : ℝ) ^ 2 * K := by
    have h1 : E.card ≤ ∑ uv ∈ P, (F uv).card := (card_le_card hEsub).trans card_biUnion_le
    have h2 : (∑ uv ∈ P, ((F uv).card : ℝ)) ≤ ∑ _uv ∈ P, K := by
      apply sum_le_sum
      intro uv huv
      rw [hP, mem_filter, mem_product, mem_Icc, mem_Icc] at huv
      exact hcount uv.1 uv.2 (by omega) huv.2.1 huv.1.2.2 huv.2.2.1 huv.2.2.2
    have h3 : (P.card : ℝ) ≤ (M : ℝ) ^ 2 := by
      have hc : P.card ≤ M * M := by
        calc P.card ≤ ((Icc 1 M) ×ˢ (Icc 1 M)).card := card_filter_le _ _
          _ = M * M := by rw [card_product, Nat.card_Icc]; simp
      have : (P.card : ℝ) ≤ (M : ℝ) * M := by exact_mod_cast hc
      nlinarith
    rw [sum_const, nsmul_eq_mul] at h2
    have h4 : (E.card : ℝ) ≤ ∑ uv ∈ P, ((F uv).card : ℝ) := by exact_mod_cast h1
    nlinarith
  -- every cell keeps at most two non-excess elements
  have hGcard : G.card ≤ 2 * (G.image key).card := by
    apply card_le_mul_card_image
    intro b _
    by_contra hcon
    push_neg at hcon
    set T := G.filter (fun n => key n = b) with hT
    have hTne : T.Nonempty := card_pos.mp (by omega)
    set m := T.max' hTne with hmdef
    have hm : m ∈ T := max'_mem T hTne
    have h2 : 1 < (T.erase m).card := by rw [card_erase_of_mem hm]; omega
    obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp h2
    have hxT := mem_of_mem_erase hx
    have hyT := mem_of_mem_erase hy
    have hxm : x < m := lt_of_le_of_ne (le_max' T x hxT) (ne_of_mem_erase hx)
    have hym : y < m := lt_of_le_of_ne (le_max' T y hyT) (ne_of_mem_erase hy)
    rw [hT, mem_filter, hG, mem_filter] at hm hxT hyT
    apply hm.1.2
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨x, hxT.1.1, y, hyT.1.1, h, hym, hxT.2.trans hm.2.symm, hyT.2.trans hm.2.symm⟩
    · exact ⟨y, hyT.1.1, x, hxT.1.1, h, hxm, hyT.2.trans hm.2.symm, hxT.2.trans hm.2.symm⟩
  -- the number of cells
  have hcells : ((G.image key).card : ℝ) ≤ r * ((N : ℝ) / M + 2) := by
    have hsub : G.image key ⊆ (Icc (N / M) ((2 * N) / M)) ×ˢ (range r) := by
      intro c hc
      rw [mem_image] at hc
      obtain ⟨n, hn, rfl⟩ := hc
      have hnS : n ∈ S := (mem_filter.mp hn).1
      have hn2 := mem_Ico.mp (hS hnS)
      rw [mem_product, mem_Icc, mem_range]
      exact ⟨⟨Nat.div_le_div_right hn2.1, Nat.div_le_div_right hn2.2.le⟩,
        Nat.mod_lt _ (by omega)⟩
    have hc1 : (G.image key).card ≤ ((2 * N) / M + 1 - N / M) * r := by
      calc (G.image key).card ≤ ((Icc (N / M) ((2 * N) / M)) ×ˢ (range r)).card := card_le_card hsub
        _ = ((2 * N) / M + 1 - N / M) * r := by rw [card_product, Nat.card_Icc, card_range]
    have hab : N / M ≤ (2 * N) / M := Nat.div_le_div_right (by omega)
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hb : (((2 * N) / M : ℕ) : ℝ) ≤ (2 * N : ℕ) / (M : ℝ) := Nat.cast_div_le
    have ha : (N : ℝ) / M < ((N / M : ℕ) : ℝ) + 1 := by
      have h1 := Nat.div_add_mod N M
      have h2 := Nat.mod_lt N hM
      rw [div_lt_iff₀ hMr]
      have : (N : ℝ) = M * ((N / M : ℕ) : ℝ) + ((N % M : ℕ) : ℝ) := by exact_mod_cast h1.symm
      have : ((N % M : ℕ) : ℝ) < M := by exact_mod_cast h2
      nlinarith
    have hcast : ((((2 * N) / M + 1 - N / M) * r : ℕ) : ℝ) =
        ((((2 * N) / M : ℕ) : ℝ) + 1 - ((N / M : ℕ) : ℝ)) * r := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      push_cast
      ring
    have hc2 : ((G.image key).card : ℝ) ≤ ((((2 * N) / M : ℕ) : ℝ) + 1 - ((N / M : ℕ) : ℝ)) * r := by
      rw [← hcast]; exact_mod_cast hc1
    have h2N : ((2 * N : ℕ) : ℝ) / M = 2 * ((N : ℝ) / M) := by push_cast; ring
    rw [h2N] at hb
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    nlinarith
  -- conclusion
  have hsplit : E.card + G.card = S.card := card_filter_add_card_filter_not p
  have hS' : (S.card : ℝ) = E.card + G.card := by exact_mod_cast hsplit.symm
  have hG' : (G.card : ℝ) ≤ 2 * (r * ((N : ℝ) / M + 2)) := by
    have : (G.card : ℝ) ≤ 2 * ((G.image key).card : ℝ) := by exact_mod_cast hGcard
    linarith
  have hNM : (0 : ℝ) ≤ (N : ℝ) / M := by positivity
  have hMK : (0 : ℝ) ≤ (M : ℝ) ^ 2 * K := by positivity
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rw [hS']
  nlinarith
