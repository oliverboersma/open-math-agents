import OMAReductions.R_PollocksConjecture_pollock_tetrahedral_salzer_levine_R1
import Mathlib

/-! Step H1: 343867 is not a sum of four tetrahedral numbers. The search over all quadruples is
the bitmask computation of the merged proof of the count of exceptions, reused here. -/

-- Step PollocksConjecture.pollock_tetrahedral.salzer_levine.R1.H1: hypothesis H1 of reduction PollocksConjecture.pollock_tetrahedral.salzer_levine.R1
-- Credit: @ivillar
-- Reuse: the namespace OMAPollock below is the merged proof of
-- PollocksConjecture.pollock_tetrahedral.ncard_exceptions by @Genbox (PR #275), inlined with only its final
-- theorem renamed. Its lemma memS decides membership for every N up to 343867.


namespace OMAPollock
open PollocksConjecture

def sOr (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sOr B k ||| (B <<< tetrahedral k)

theorem sOr_bit (B n N : ℕ) : (sOr B n).testBit N = true ↔
    ∃ k < n, tetrahedral k ≤ N ∧ B.testBit (N - tetrahedral k) = true := by
  induction n with
  | zero => simp [sOr]
  | succ n ih =>
    simp only [sOr, Nat.testBit_lor, Bool.or_eq_true, ih, Nat.testBit_shiftLeft,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨k, hk, h⟩ | ⟨h1, h2⟩)
      · exact ⟨k, by omega, h⟩
      · exact ⟨n, by omega, h1, h2⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact Or.inl ⟨k, hk, h⟩
      · exact Or.inr h

theorem one_bit (m : ℕ) : (1 : ℕ).testBit m = true ↔ m = 0 := by
  rw [show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]; simp [eq_comm]

def B4 : ℕ := sOr (sOr (sOr (sOr 1 127) 127) 127) 127

theorem B4_bit (N : ℕ) : B4.testBit N = true ↔
    ∃ a < 127, ∃ b < 127, ∃ c < 127, ∃ d < 127,
      N = tetrahedral a + tetrahedral b + tetrahedral c + tetrahedral d := by
  simp only [B4, sOr_bit, one_bit]
  constructor
  · rintro ⟨a, ha, h1, b, hb, h2, c, hc, h3, d, hd, h4, h5⟩
    exact ⟨a, ha, b, hb, c, hc, d, hd, by omega⟩
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, h⟩
    exact ⟨a, ha, by omega, b, hb, by omega, c, hc, by omega, d, hd, by omega, by omega⟩

theorem tet_mono {a b : ℕ} (h : a ≤ b) : tetrahedral a ≤ tetrahedral b := by
  unfold tetrahedral; gcongr

def excL : List ℕ := [17, 27, 33, 52, 73, 82, 83, 103, 107, 137, 153, 162, 217, 219, 227, 237, 247, 258, 268, 271, 282, 283, 302, 303, 313, 358, 383, 432, 437, 443, 447, 502, 548, 557, 558, 647, 662, 667, 709, 713, 718, 722, 842, 863, 898, 953, 1007, 1117, 1118, 1153, 1227, 1233, 1243, 1314, 1382, 1402, 1468, 1478, 1513, 1523, 1578, 1612, 1622, 1658, 1678, 1693, 1731, 1738, 1742, 1758, 1767, 1803, 1858, 1907, 1923, 1933, 2037, 2053, 2172, 2198, 2217, 2218, 2251, 2253, 2327, 2372, 2382, 2417, 2437, 2457, 2537, 2538, 2578, 2687, 2818, 2858, 2898, 2973, 3138, 3142, 3183, 3218, 3263, 3463, 3512, 3887, 4003, 4307, 4317, 4563, 4832, 4923, 5013, 5142, 5238, 5283, 5483, 5508, 5538, 5563, 5618, 5647, 5707, 6022, 6057, 6067, 6186, 6213, 6263, 6343, 6462, 6863, 7067, 7278, 7377, 7387, 7423, 7497, 7542, 7662, 7793, 7873, 8223, 8307, 8322, 8973, 9063, 9488, 9687, 9753, 9772, 9973, 10397, 10467, 10532, 10633, 10852, 11237, 11302, 11737, 11962, 12247, 12547, 12722, 12777, 12843, 12858, 13127, 13393, 13822, 14492, 15122, 15483, 15867, 16097, 16538, 16637, 16742, 17253, 17683, 17813, 17893, 18573, 18782, 19168, 19277, 20918, 21523, 22618, 22657, 23677, 24237, 24317, 24338, 25447, 25723, 26007, 27858, 28617, 28847, 29157, 29487, 29938, 30298, 31973, 33183, 36262, 36913, 37798, 38453, 38707, 38807, 39693, 39913, 41278, 41322, 41433, 44833, 47627, 48043, 56467, 56842, 58613, 59077, 62158, 64752, 65253, 65567, 71157, 74687, 78003, 78787, 83603, 84023, 85993, 91128, 106277, 113062, 134038, 148437, 343867]

def emask : List ℕ → ℕ
  | [] => 0
  | e :: l => emask l ||| (1 <<< e)

theorem emask_bit (l : List ℕ) (N : ℕ) : (emask l).testBit N = true ↔ N ∈ l := by
  induction l with
  | nil => simp [emask]
  | cons e l ih =>
    simp only [emask, Nat.testBit_lor, Bool.or_eq_true, ih, Nat.one_shiftLeft,
      Nat.testBit_two_pow, decide_eq_true_eq, List.mem_cons]
    tauto

theorem key : B4 &&& (2 ^ 343868 - 1) = (2 ^ 343868 - 1) ^^^ emask excL := by decide +kernel

theorem memS (N : ℕ) (hN : N ≤ 343867) : N ∈ NotSumOfFourTetrahedral ↔ N ∈ excL := by
  have hk := congrArg (fun x => x.testBit N) key
  simp only [Nat.testBit_land, Nat.testBit_xor, Nat.testBit_two_pow_sub_one] at hk
  have hlt : decide (N < 343868) = true := by simp; omega
  rw [hlt, Bool.and_true, Bool.true_xor] at hk
  rw [← emask_bit]
  have hT : ∀ x, tetrahedral x ≤ N → x < 127 := by
    intro x hx
    by_contra hc
    have := tet_mono (show 127 ≤ x by omega)
    have h127 : tetrahedral 127 = 349504 := by decide
    omega
  constructor
  · intro hS
    by_contra hE
    simp only [Bool.not_eq_true] at hE
    rw [hE, Bool.not_false] at hk
    obtain ⟨a, ha, b, hb, c, hc, d, hd, h⟩ := (B4_bit N).mp hk
    apply hS ![a, b, c, d]
    simp [Fin.sum_univ_four, h]
  · intro hE f hf
    rw [hE, Bool.not_true] at hk
    have hf' := hf
    simp only [Fin.sum_univ_four] at hf'
    have : B4.testBit N = true := (B4_bit N).mpr
      ⟨f 0, hT _ (by omega), f 1, hT _ (by omega), f 2, hT _ (by omega), f 3, hT _ (by omega), hf'⟩
    rw [hk] at this
    exact Bool.false_ne_true this

theorem excL_bound : ∀ e ∈ excL, e ≤ 343867 := by decide +kernel
theorem excL_nodup : excL.Nodup := by decide +kernel
theorem excL_len : excL.length = 241 := by decide +kernel
theorem excL_mem : 343867 ∈ excL := by decide +kernel

theorem card_E : (↑excL.toFinset : Set ℕ).ncard = 241 := by
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup excL_nodup, excL_len]

theorem E_sub : (↑excL.toFinset : Set ℕ) ⊆ NotSumOfFourTetrahedral := by
  intro x hx
  simp only [Finset.mem_coe, List.mem_toFinset] at hx
  exact (memS x (excL_bound x hx)).mpr hx

theorem final : IsGreatest NotSumOfFourTetrahedral 343867 ↔
    NotSumOfFourTetrahedral.ncard = 241 := by
  constructor
  · intro h
    have : NotSumOfFourTetrahedral = ↑excL.toFinset := by
      apply Set.Subset.antisymm _ E_sub
      intro x hx
      simp only [Finset.mem_coe, List.mem_toFinset]
      exact (memS x (h.2 hx)).mp hx
    rw [this, card_E]
  · intro h
    have hfin : NotSumOfFourTetrahedral.Finite := Set.finite_of_ncard_ne_zero (by omega)
    have heq := Set.eq_of_subset_of_ncard_le E_sub (by rw [h, card_E]) hfin
    rw [← heq]
    refine ⟨by simpa using excL_mem, ?_⟩
    intro x hx
    simp only [Finset.mem_coe, List.mem_toFinset] at hx
    exact excL_bound x hx

end OMAPollock

theorem ncard_exceptions_merged : type_of% @PollocksConjecture.pollock_tetrahedral.ncard_exceptions :=
  OMAPollock.final

theorem OMA.solution : OMA.R_PollocksConjecture_pollock_tetrahedral_salzer_levine_R1.H1 :=
  (OMAPollock.memS 343867 le_rfl).mpr OMAPollock.excL_mem
