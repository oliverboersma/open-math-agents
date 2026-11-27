import OMAStatements.S_arxiv_2008_08020

open Filter OMA.S_arxiv_2008_08020
open scoped Topology

/- The two one-pair tails give distinct right secant limits after any finite prefix. -/

namespace Vielhaber

private theorem rational_prefix (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    ∃ ds : List (ℕ × ℕ), cf ds 0 = (p : ℝ) / q := by
  induction q using Nat.strong_induction_on generalizing p with
  | h q ih =>
    let a := q / p
    let r := q % p
    have haq : 1 ≤ a := Nat.div_pos (le_of_lt hpq) hp
    have hrp : r < p := Nat.mod_lt _ hp
    have hq : q = a * p + r := by
      simpa [a, r, Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div q p).symm
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hq' : (q : ℝ) = (a : ℝ) * p + r := by exact_mod_cast hq
    by_cases hr : r = 0
    · have ha2 : 2 ≤ a := by
        by_contra! h
        have ha : a = 1 := by omega
        rw [ha, hr] at hq
        simp at hq
        omega
      refine ⟨[(a - 2, 0)], ?_⟩
      simp only [cf, Nat.cast_sub ha2, Nat.cast_ofNat, Nat.cast_zero, zero_add, add_zero,
        div_one]
      have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
      have hz : (r : ℝ) = 0 := by exact_mod_cast hr
      rw [show (a : ℝ) - 2 + 1 + 1 = a by ring]
      field_simp
      linarith
    · let b := p / r
      let s := p % r
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hb : 1 ≤ b := Nat.div_pos (le_of_lt hrp) hrpos
      have hsr : s < r := Nat.mod_lt _ hrpos
      have hp' : p = b * r + s := by
        simpa [b, s, Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div p r).symm
      have hp'' : (p : ℝ) = (b : ℝ) * r + s := by exact_mod_cast hp'
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
      obtain ⟨ds, hds⟩ : ∃ ds : List (ℕ × ℕ), cf ds 0 = (s : ℝ) / r := by
        by_cases hs : s = 0
        · exact ⟨[], by simp [cf, hs]⟩
        · exact ih r (hrp.trans hpq) s (Nat.pos_of_ne_zero hs) hsr
      refine ⟨(a - 1, b - 1) :: ds, ?_⟩
      have hinner : (b : ℝ) + (s : ℝ) / r = (p : ℝ) / r := by
        field_simp
        linarith
      simp only [cf, Nat.cast_sub haq, Nat.cast_sub hb, Nat.cast_one, sub_add_cancel, hds,
        hinner, one_div_div]
      field_simp
      linarith

private theorem prefix_differentiable (ds : List (ℕ × ℕ)) :
    DifferentiableAt ℝ (cf ds) 0 ∧ 0 ≤ cf ds 0 := by
  induction ds with
  | nil =>
    exact ⟨differentiableAt_id, le_rfl⟩
  | cons pair ds ih =>
    rcases pair with ⟨a, b⟩
    have hb : 0 < (b : ℝ) + 1 + cf ds 0 :=
      add_pos_of_pos_of_nonneg (by positivity) ih.2
    have ha : 0 < (a : ℝ) + 1 + 1 / ((b : ℝ) + 1 + cf ds 0) := by positivity
    have hinner : DifferentiableAt ℝ (fun x => (b : ℝ) + 1 + cf ds x) 0 :=
      (differentiableAt_const ((b : ℝ) + 1)).add ih.1
    have hone : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) 0 :=
      differentiableAt_const 1
    have houter : DifferentiableAt ℝ
        (fun x => (a : ℝ) + 1 + 1 / ((b : ℝ) + 1 + cf ds x)) 0 :=
      (differentiableAt_const ((a : ℝ) + 1)).add (hone.div hinner hb.ne')
    exact ⟨hone.div houter ha.ne', one_div_nonneg.mpr ha.le⟩

private theorem cf_append (ds es : List (ℕ × ℕ)) (x : ℝ) :
    cf (ds ++ es) x = cf ds (cf es x) := by
  induction ds with
  | nil => rfl
  | cons pair ds ih =>
    rcases pair with ⟨a, b⟩
    simp only [List.cons_append, cf, ih]

private theorem code_append (ds es : List (ℕ × ℕ)) (x : ℝ) :
    code (ds ++ es) x = code ds (code es x) := by
  induction ds with
  | nil => rfl
  | cons pair ds ih =>
    rcases pair with ⟨a, b⟩
    simp only [List.cons_append, code, ih]

private theorem code_linear (ds : List (ℕ × ℕ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ y, code ds y - code ds 0 = c * y := by
  induction ds with
  | nil =>
    exact ⟨1, one_pos, by intro y; simp [code]⟩
  | cons pair ds ih =>
    obtain ⟨c, hc, h⟩ := ih
    rcases pair with ⟨a, b⟩
    refine ⟨c / (denom (b+1) : ℝ) / (denom (a+1) : ℝ), ?_, ?_⟩
    · unfold denom
      positivity
    · intro y
      simp only [code]
      rw [← sub_div, add_sub_add_left_eq_sub, ← sub_div, add_sub_add_left_eq_sub, h]
      ring

private theorem one_pair_cf {d : ℕ} (hd : 1 ≤ d) :
    cf [(d - 1, 0)] 0 = 1 / ((d : ℝ) + 1) := by
  simp [cf, Nat.cast_sub hd]

private theorem one_pair_code {d : ℕ} (hd : 1 ≤ d) :
    code [(d - 1, 0)] 0 = (bitsI d : ℝ) / denom d := by
  have h : bitsII 1 = 0 := by decide
  simp [code, Nat.sub_add_cancel hd, h]

private theorem log_digit (u k : ℕ) (hu : u = 2 ∨ u = 3) :
    Nat.log 2 (u * 2 ^ k) = k + 1 := by
  have hpos : 0 < (2 : ℕ) ^ k := by positivity
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · rw [pow_succ']
    exact Nat.mul_le_mul_right _ (by omega)
  · rw [pow_succ', pow_succ']
    have h : 2 * (2 * 2 ^ k) = 4 * (2 : ℕ) ^ k := by ring
    rw [h]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hpos

private theorem tail_formula (u k : ℕ) (hu : u = 2 ∨ u = 3) :
    ((u * 2 ^ k : ℕ) + 1 : ℝ) *
      ((bitsI (u * 2 ^ k) : ℝ) / (denom (u * 2 ^ k) : ℝ)) =
    (((u : ℝ) + ((2 : ℝ) ^ k)⁻¹) *
      ((6 - (u : ℝ)) - ((2 : ℝ) ^ k)⁻¹)) / 8 := by
  have hpos : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hsub : u * 2 ^ k ≤ 3 * 2 ^ (k + 1) - 1 := by
    rw [pow_succ']
    have hpow : 0 < (2 : ℕ) ^ k := by positivity
    rcases hu with rfl | rfl <;> omega
  have hh : 1 ≤ 3 * (2 : ℕ) ^ (k + 1) := Nat.succ_le_of_lt (by positivity)
  unfold bitsI denom
  rw [log_digit u k hu, Nat.cast_sub hsub, Nat.cast_sub hh]
  push_cast
  have hden : (2 : ℝ) ^ (2 * (k + 1) + 1) = (2 ^ k) ^ 2 * 8 := by
    rw [show 2 * (k + 1) + 1 = k * 2 + 3 by omega, pow_add, pow_mul]
    norm_num
  rw [hden, pow_succ']
  field_simp
  ring

private theorem slope_limits (F : ℝ → ℝ) (henc : Encodes F) (ds : List (ℕ × ℕ))
    {c : ℝ} (hc : ∀ y, code ds y - code ds 0 = c * y)
    (u : ℕ) (hu : u = 2 ∨ u = 3) :
    Tendsto (fun k : ℕ => slope (F ∘ cf ds) 0 (1 / ((u : ℝ) * 2 ^ k + 1)))
      atTop (𝓝 (c * (((u : ℝ) * (6 - (u : ℝ))) / 8))) := by
  have hp : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hi : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
    hp.inv_tendsto_atTop
  have hlim : Tendsto
      (fun k : ℕ => c * (((u : ℝ) + ((2 : ℝ) ^ k)⁻¹) *
        ((6 - (u : ℝ)) - ((2 : ℝ) ^ k)⁻¹) / 8))
      atTop (𝓝 (c * (((u : ℝ) * (6 - (u : ℝ))) / 8))) := by
    simpa only [add_zero, sub_zero] using
      (((tendsto_const_nhds.add hi).mul (tendsto_const_nhds.sub hi)).div_const (8 : ℝ)).const_mul c
  apply hlim.congr
  intro k
  let d := u * 2 ^ k
  have hd : 1 ≤ d := by
    apply Nat.succ_le_of_lt
    rcases hu with rfl | rfl <;> dsimp [d] <;> positivity
  have hcast : ((d : ℕ) : ℝ) = (u : ℝ) * 2 ^ k := by simp [d]
  rw [slope_def_field, Function.comp_apply, Function.comp_apply, sub_zero,
    ← hcast, ← one_pair_cf hd, ← cf_append, henc, henc, code_append, hc,
    one_pair_code hd, one_pair_cf hd]
  simp only [one_div, div_inv_eq_mul]
  convert congrArg (c * ·) (tail_formula u k hu).symm using 1
  ring

private theorem tail_tendsto (u : ℕ) (hu : 0 < u) :
    Tendsto (fun k : ℕ => 1 / ((u : ℝ) * 2 ^ k + 1)) atTop (𝓝[≠] (0 : ℝ)) := by
  have hp : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have huR : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [one_div, Function.comp_def] using
      (tendsto_mul_add_inv_atTop_nhds_zero (u : ℝ) 1 huR).comp hp
  · exact Eventually.of_forall (fun k => by simp; positivity)

theorem proof : type_of% @OMA.S_arxiv_2008_08020.main := by
  intro F henc p q hp hpq hdiff
  obtain ⟨ds, hds⟩ := rational_prefix p q hp hpq
  rw [← hds] at hdiff
  have hcomp : DifferentiableAt ℝ (F ∘ cf ds) 0 :=
    hdiff.comp 0 (prefix_differentiable ds).1
  obtain ⟨c, hc, hlin⟩ := code_linear ds
  have h2 := tendsto_nhds_unique (hcomp.hasDerivAt.tendsto_slope.comp (tail_tendsto 2 (by decide)))
    (slope_limits F henc ds hlin 2 (Or.inl rfl))
  have h3 := tendsto_nhds_unique (hcomp.hasDerivAt.tendsto_slope.comp (tail_tendsto 3 (by decide)))
    (slope_limits F henc ds hlin 3 (Or.inr rfl))
  norm_num at h2 h3
  linarith

end Vielhaber

theorem OMA.solution : type_of% @OMA.S_arxiv_2008_08020.main := Vielhaber.proof
