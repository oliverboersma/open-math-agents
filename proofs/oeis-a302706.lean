import OMAStatements.S_oeis_a302706

-- OEIS A302706, conjectured by Andres Cicuttin.
-- Credit: @caa1982.
-- Use x = m - d and y = m + d with m = d² + 1.

open Filter
open scoped Topology

namespace A302706Proof
open OMA.S_oeis_a302706

lemma mem_pairs (n : ℕ) (p : ℕ × ℕ) :
    p ∈ pairs n ↔ 0 < p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ n := by
  simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

lemma maximum_upper (n : ℕ) : a n ≤ 2 * n := by
  apply Finset.sup_le
  intro p hp
  have hp' := (mem_pairs n p).mp hp
  have h := Nat.mod_lt (p.1 ^ 2 + p.2 ^ 2) (show 0 < p.1 + p.2 by omega)
  omega

lemma test_pair (d : ℕ) :
    let m := d ^ 2 + 1
    ((m - d) ^ 2 + (m + d) ^ 2) % ((m - d) + (m + d)) = 2 * d ^ 2 := by
  dsimp only
  let m := d ^ 2 + 1
  have hm : d ≤ m := by dsimp [m]; nlinarith
  have hadd : m - d + (m + d) = 2 * m := by omega
  have hsum : (m - d) ^ 2 + (m + d) ^ 2 = 2 * d ^ 2 + m * (2 * m) := by
    have h : (m - d) + d = m := Nat.sub_add_cancel hm
    nlinarith only [congrArg (fun x : ℕ => x ^ 2) h,
      congrArg (fun x : ℕ => x * d) h]
  change ((m - d) ^ 2 + (m + d) ^ 2) % ((m - d) + (m + d)) = 2 * d ^ 2
  rw [hadd, hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt]
  dsimp [m]
  omega

lemma maximum_lower (n : ℕ) (hn : 0 < n) : 2 * (n.sqrt - 1) ^ 2 ≤ a n := by
  let d := n.sqrt - 1
  let m := d ^ 2 + 1
  have hroot : 1 ≤ n.sqrt := Nat.le_sqrt'.mpr (by
    have hn' : 1 ≤ n := by omega
    simpa using hn')
  have hd : d + 1 = n.sqrt := Nat.sub_add_cancel hroot
  have hdn : (d + 1) ^ 2 ≤ n := by rw [hd]; exact Nat.sqrt_le' _
  have hx : 0 < m - d := by
    apply Nat.sub_pos_of_lt
    dsimp [m]
    nlinarith
  have hy : m + d ≤ n := by dsimp [m]; nlinarith only [hdn, Nat.zero_le d]
  have hp : (m - d, m + d) ∈ pairs n := (mem_pairs n _).mpr ⟨hx, by omega, hy⟩
  have hle : ((m - d) ^ 2 + (m + d) ^ 2) % ((m - d) + (m + d)) ≤ a n :=
    Finset.le_sup (f := fun p : ℕ × ℕ => (p.1 ^ 2 + p.2 ^ 2) % (p.1 + p.2)) hp
  rw [test_pair d] at hle
  exact hle

lemma maximum_exists (n : ℕ) (hn : 0 < n) :
    ∃ p ∈ pairs n, (p.1 ^ 2 + p.2 ^ 2) % (p.1 + p.2) = a n := by
  have hne : (pairs n).Nonempty := ⟨(1, 1), (mem_pairs n _).mpr (by simp; omega)⟩
  exact Finset.sup_mem_of_nonempty (f := fun p : ℕ × ℕ =>
    (p.1 ^ 2 + p.2 ^ 2) % (p.1 + p.2)) hne

lemma maximum_limit :
    Tendsto (fun n : ℕ => (a n : ℝ) / (2 * (n : ℝ))) atTop (𝓝 1) := by
  have hrootNat : Tendsto Nat.sqrt atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b ^ 2, fun n hn => Nat.le_sqrt'.mpr hn⟩
  have hroot : Tendsto (fun n : ℕ => (n.sqrt : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hrootNat
  have hsmall : Tendsto (fun n : ℕ => (4 : ℝ) / (n.sqrt : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hroot
  have hlow : Tendsto (fun n : ℕ => 1 - (4 : ℝ) / (n.sqrt : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hsmall
  refine hlow.squeeze' tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hs : 1 ≤ n.sqrt := Nat.le_sqrt'.mpr (by
      have hn' : 1 ≤ n := by omega
      simpa using hn')
    have hd : n.sqrt - 1 + 1 = n.sqrt := Nat.sub_add_cancel hs
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have hs0 : 0 < (n.sqrt : ℝ) := by exact_mod_cast (show 0 < n.sqrt by omega)
    have hdR : ((n.sqrt - 1 : ℕ) : ℝ) + 1 = (n.sqrt : ℝ) := by exact_mod_cast hd
    have hlo : (2 : ℝ) * (((n.sqrt - 1 : ℕ) : ℝ) ^ 2) ≤ (a n : ℝ) := by
      exact_mod_cast maximum_lower n hn
    have hsq : (n.sqrt : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
    have hhi : (n : ℝ) < ((n.sqrt : ℝ) + 1) ^ 2 := by
      exact_mod_cast (show n < (n.sqrt + 1) ^ 2 from Nat.lt_succ_sqrt' n)
    have he : 2 * (n : ℝ) - (a n : ℝ) ≤ 8 * (n.sqrt : ℝ) := by
      have hdEq : ((n.sqrt - 1 : ℕ) : ℝ) = (n.sqrt : ℝ) - 1 := by linarith only [hdR]
      rw [hdEq] at hlo
      nlinarith only [hlo, hhi]
    have haux : (n.sqrt : ℝ) * (2 * (n : ℝ) - (a n : ℝ)) ≤ 4 * (2 * (n : ℝ)) := by
      calc
        _ ≤ (n.sqrt : ℝ) * (8 * (n.sqrt : ℝ)) := mul_le_mul_of_nonneg_left he hs0.le
        _ ≤ _ := by nlinarith only [hsq]
    apply (le_div_iff₀ (show 0 < 2 * (n : ℝ) by positivity)).2
    apply (mul_le_mul_iff_right₀ hs0).1
    have heq : (n.sqrt : ℝ) * ((1 - (4 : ℝ) / (n.sqrt : ℝ)) * (2 * (n : ℝ))) =
        (2 * (n : ℝ)) * (n.sqrt : ℝ) - 4 * (2 * (n : ℝ)) := by
      field_simp
    rw [heq]
    nlinarith only [haux]
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_iff₀ (show 0 < 2 * (n : ℝ) by positivity)).2
    simpa using (show (a n : ℝ) ≤ 2 * (n : ℝ) by exact_mod_cast maximum_upper n)

lemma coordinate_limit (z : ℕ → ℕ)
    (hz : ∀ᶠ n in atTop, z n ≤ n ∧ a n ≤ z n + n) :
    Tendsto (fun n : ℕ => (z n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun n : ℕ => 2 * ((a n : ℝ) / (2 * (n : ℝ))) - 1) atTop (𝓝 1) := by
    have h := ((tendsto_const_nhds (x := (2 : ℝ))).mul maximum_limit).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
    norm_num at h
    exact h
  refine hlow.squeeze' tendsto_const_nhds ?_ ?_
  · filter_upwards [hz, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
    have heq : 2 * ((a n : ℝ) / (2 * (n : ℝ))) - 1 = ((a n : ℝ) - (n : ℝ)) / (n : ℝ) := by
      field_simp
    rw [heq]
    apply (div_le_div_iff_of_pos_right hnR).2
    have hb : (a n : ℝ) ≤ (z n : ℝ) + (n : ℝ) := by exact_mod_cast hn.2
    linarith
  · filter_upwards [hz, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn0
    exact (div_le_one hnR).2 (by exact_mod_cast hn.1)

end A302706Proof

open A302706Proof
open OMA.S_oeis_a302706

theorem OMA.solution : type_of% @OMA.S_oeis_a302706.main := by
  classical
  let p : ℕ → ℕ × ℕ := fun n => if hn : 0 < n then Classical.choose (maximum_exists n hn) else (0, 0)
  have hp : ∀ᶠ n in atTop, 0 < (p n).1 ∧ (p n).1 ≤ (p n).2 ∧ (p n).2 ≤ n ∧
      ((p n).1 ^ 2 + (p n).2 ^ 2) % ((p n).1 + (p n).2) = a n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have h := Classical.choose_spec (maximum_exists n hn)
    have hem : p n = Classical.choose (maximum_exists n hn) := by simp [p, hn]
    rw [hem]
    obtain ⟨hx, hxy, hy⟩ := (mem_pairs n _).mp h.1
    exact ⟨hx, hxy, hy, h.2⟩
  refine ⟨maximum_limit, fun n => (p n).1, fun n => (p n).2, hp,
    coordinate_limit _ ?_, coordinate_limit _ ?_⟩
  · filter_upwards [hp] with n ⟨hx, hxy, hy, hrem⟩
    have h := Nat.mod_lt ((p n).1 ^ 2 + (p n).2 ^ 2) (show 0 < (p n).1 + (p n).2 by omega)
    omega
  · filter_upwards [hp] with n ⟨hx, hxy, hy, hrem⟩
    have h := Nat.mod_lt ((p n).1 ^ 2 + (p n).2 ^ 2) (show 0 < (p n).1 + (p n).2 by omega)
    omega
