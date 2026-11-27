import OMAStatements.S_arxiv_2611_14718

namespace Arxiv261114718

open OMA.S_arxiv_2611_14718

private def adjNat (u v : ℕ) : Bool :=
  (u == 0 && (v == 1 || v == 2 || v == 3)) ||
  (u == 1 && (v == 0 || v == 2 || v == 7)) ||
  (u == 2 && (v == 0 || v == 1 || v == 11)) ||
  (u == 3 && (v == 0 || v == 4 || v == 5)) ||
  (u == 4 && v == 3) ||
  (u == 5 && (v == 3 || v == 6)) ||
  (u == 6 && v == 5) ||
  (u == 7 && (v == 1 || v == 8 || v == 9)) ||
  (u == 8 && v == 7) ||
  (u == 9 && (v == 7 || v == 10)) ||
  (u == 10 && v == 9) ||
  (u == 11 && (v == 2 || v == 12 || v == 13)) ||
  (u == 12 && v == 11) ||
  (u == 13 && (v == 11 || v == 14)) ||
  (u == 14 && v == 13)

private def G : SimpleGraph (Fin 15) where
  Adj u v := adjNat u.val v.val = true
  symm := ⟨by
    intro u v h
    fin_cases u <;> fin_cases v <;> simp_all [adjNat]⟩
  loopless := ⟨by
    intro v
    fin_cases v <;> simp [adjNat]⟩

private instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable (adjNat u.val v.val = true))

private theorem G_deg_le_three : ∀ v : Fin 15, G.degree v ≤ 3 := by
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  fin_cases v <;> decide

private def N_tbl : Fin 15 → ℕ
  | ⟨0, _⟩ => 15
  | ⟨1, _⟩ => 135
  | ⟨2, _⟩ => 2055
  | ⟨3, _⟩ => 57
  | ⟨4, _⟩ => 24
  | ⟨5, _⟩ => 104
  | ⟨6, _⟩ => 96
  | ⟨7, _⟩ => 898
  | ⟨8, _⟩ => 384
  | ⟨9, _⟩ => 1664
  | ⟨10, _⟩ => 1536
  | ⟨11, _⟩ => 14340
  | ⟨12, _⟩ => 6144
  | ⟨13, _⟩ => 26624
  | ⟨14, _⟩ => 24576

private theorem closedMask_G_eq : closedMask G = N_tbl := by
  funext v
  fin_cases v <;> decide

private theorem jammed_count_le_six :
    (jammedSizes N_tbl (List.finRange 15) 0 0).countP (fun j => j ≤ 6) = 1 := by
  decide

private theorem jammed_length :
    (jammedSizes N_tbl (List.finRange 15) 0 0).length = 55 := by
  decide

private theorem staticCDF_val : staticCDF N_tbl 6 = (1 : ℚ) / 55 := by
  simp only [staticCDF, jammed_count_le_six, jammed_length]
  norm_num

private inductive BState
  | F
  | B
  | H
  | E
  deriving DecidableEq

private instance : Fintype BState where
  elems := {.F, .B, .H, .E}
  complete x := by cases x <;> simp

private def bMask (j : Fin 3) (st : BState) : ℕ :=
  let c := j.val
  let h := 3 + 4 * j.val
  let l := 4 + 4 * j.val
  let a := 5 + 4 * j.val
  let b := 6 + 4 * j.val
  match st with
  | .F => (1 <<< c) ||| (1 <<< h) ||| (1 <<< l) ||| (1 <<< a) ||| (1 <<< b)
  | .B => (1 <<< c) ||| (1 <<< h) ||| (1 <<< l)
  | .H => 1 <<< b
  | .E => 0

private def bNeed : BState → ℕ
  | .F => 2
  | .B => 1
  | .H => 1
  | .E => 0

private def bW : BState → ℕ
  | .F => 4
  | .B => 5
  | .H => 15
  | .E => 15

private def tripleMask (s0 s1 s2 : BState) : ℕ :=
  bMask 0 s0 ||| bMask 1 s1 ||| bMask 2 s2

private def stepNext (s0 s1 s2 : BState) (i : Fin 15) : Option (BState × BState × BState) :=
  match i.val with
  | 3 =>
    match s0 with
    | .F => some (.H, s1, s2)
    | .B => some (.E, s1, s2)
    | _ => none
  | 6 =>
    match s0 with
    | .F => some (.B, s1, s2)
    | .H => some (.E, s1, s2)
    | _ => none
  | 7 =>
    match s1 with
    | .F => some (s0, .H, s2)
    | .B => some (s0, .E, s2)
    | _ => none
  | 10 =>
    match s1 with
    | .F => some (s0, .B, s2)
    | .H => some (s0, .E, s2)
    | _ => none
  | 11 =>
    match s2 with
    | .F => some (s0, s1, .H)
    | .B => some (s0, s1, .E)
    | _ => none
  | 14 =>
    match s2 with
    | .F => some (s0, s1, .B)
    | .H => some (s0, s1, .E)
    | _ => none
  | _ => none

private def stepWeightNat (s0 s1 s2 : BState) (i : Fin 15) : ℕ :=
  match stepNext s0 s1 s2 i with
  | some (t0, t1, t2) => bW t0 * bW t1 * bW t2
  | none => 0

private def stepNextCheck (s0 s1 s2 : BState) (i : Fin 15) : Bool :=
  match stepNext s0 s1 s2 i with
  | none => true
  | some (t0, t1, t2) =>
    (tripleMask s0 s1 s2 ^^^ (tripleMask s0 s1 s2 &&& N_tbl i) == tripleMask t0 t1 t2) &&
    (bNeed t0 + bNeed t1 + bNeed t2 + 1 == bNeed s0 + bNeed s1 + bNeed s2)

private theorem stepNextCheck_all :
    ∀ (s0 s1 s2 : BState) (i : Fin 15), stepNextCheck s0 s1 s2 i = true := by
  decide

private theorem stepNext_spec (s0 s1 s2 : BState) (i : Fin 15) (t0 t1 t2 : BState)
    (h : stepNext s0 s1 s2 i = some (t0, t1, t2)) :
    tripleMask s0 s1 s2 ^^^ (tripleMask s0 s1 s2 &&& N_tbl i) = tripleMask t0 t1 t2 ∧
    bNeed t0 + bNeed t1 + bNeed t2 + 1 = bNeed s0 + bNeed s1 + bNeed s2 := by
  have hc := stepNextCheck_all s0 s1 s2 i
  simp only [stepNextCheck, h, Bool.and_eq_true, beq_iff_eq] at hc
  exact hc

private theorem stepWeight_sum :
    ∀ (s0 s1 s2 : BState), 0 < bNeed s0 + bNeed s1 + bNeed s2 →
      ((seats 15 (tripleMask s0 s1 s2)).map (stepWeightNat s0 s1 s2)).sum =
      (seats 15 (tripleMask s0 s1 s2)).length * (bW s0 * bW s1 * bW s2) := by
  decide

private theorem tripleMask_pos_props :
    ∀ (s0 s1 s2 : BState), 0 < bNeed s0 + bNeed s1 + bNeed s2 →
      tripleMask s0 s1 s2 ≠ 0 ∧ 0 < (seats 15 (tripleMask s0 s1 s2)).length := by
  decide

private theorem tripleMask_zero_props :
    ∀ (s0 s1 s2 : BState), bNeed s0 + bNeed s1 + bNeed s2 = 0 →
      tripleMask s0 s1 s2 = 0 ∧ bW s0 * bW s1 * bW s2 = 3375 := by
  decide

private theorem seqCDF_nonneg {n : ℕ} (N : Fin n → ℕ) :
    ∀ (k s : ℕ), 0 ≤ seqCDF N k s
  | 0, s => by
    unfold seqCDF
    split_ifs <;> norm_num
  | k + 1, s => by
    unfold seqCDF
    split_ifs
    · norm_num
    · apply div_nonneg
      · exact List.sum_nonneg (fun q hq => by
          rcases List.mem_map.mp hq with ⟨i, _, rfl⟩
          exact seqCDF_nonneg N k _)
      · exact Nat.cast_nonneg _

private theorem list_map_nat_div_sum {α : Type*} (l : List α) (f : α → ℕ) (d : ℚ) :
    (l.map (fun x => (f x : ℚ) / d)).sum = ((l.map f).sum : ℚ) / d := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih, add_div]

private theorem list_sum_map_le {α : Type*} (l : List α) (f g : α → ℚ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

private theorem seqCDF_lb :
    ∀ (k : ℕ) (s0 s1 s2 : BState),
      bNeed s0 + bNeed s1 + bNeed s2 = k →
      ((bW s0 * bW s1 * bW s2 : ℕ) : ℚ) / 3375 ≤ seqCDF N_tbl k (tripleMask s0 s1 s2)
  | 0, s0, s1, s2, hk => by
    obtain ⟨hm, hw⟩ := tripleMask_zero_props s0 s1 s2 hk
    rw [hm, hw]
    simp [seqCDF]
  | k + 1, s0, s1, s2, hk => by
    have hpos : 0 < bNeed s0 + bNeed s1 + bNeed s2 := by omega
    obtain ⟨hmne, hlen⟩ := tripleMask_pos_props s0 s1 s2 hpos
    unfold seqCDF
    rw [if_neg hmne]
    set m := tripleMask s0 s1 s2
    set xs := seats 15 m
    have hpoint : ∀ i ∈ xs,
        ((stepWeightNat s0 s1 s2 i : ℕ) : ℚ) / 3375 ≤
          seqCDF N_tbl k (m ^^^ (m &&& N_tbl i)) := by
      intro i _
      cases hnext : stepNext s0 s1 s2 i with
      | none =>
        simp only [stepWeightNat, hnext, Nat.cast_zero, zero_div]
        exact seqCDF_nonneg N_tbl k _
      | some t =>
        rcases t with ⟨t0, t1, t2⟩
        have hspec := stepNext_spec s0 s1 s2 i t0 t1 t2 hnext
        simp only [stepWeightNat, hnext]
        rw [hspec.1]
        exact seqCDF_lb k t0 t1 t2 (by omega)
    have hsum :
        (xs.map (fun i => ((stepWeightNat s0 s1 s2 i : ℕ) : ℚ) / 3375)).sum ≤
        (xs.map (fun i => seqCDF N_tbl k (m ^^^ (m &&& N_tbl i)))).sum :=
      list_sum_map_le xs _ _ hpoint
    have hsum_eq :
        (xs.map (fun i => ((stepWeightNat s0 s1 s2 i : ℕ) : ℚ) / 3375)).sum =
        (xs.length : ℚ) * (((bW s0 * bW s1 * bW s2 : ℕ) : ℚ) / 3375) := by
      rw [list_map_nat_div_sum, stepWeight_sum s0 s1 s2 hpos, Nat.cast_mul, mul_div_assoc]
    have hlen_pos : (0 : ℚ) < (xs.length : ℚ) := Nat.cast_pos.mpr hlen
    have hdiv := div_le_div_of_nonneg_right hsum hlen_pos.le
    rw [hsum_eq, mul_div_cancel_left₀ _ hlen_pos.ne'] at hdiv
    exact hdiv

private theorem seqCDF_counterexample :
    (64 : ℚ) / 3375 ≤ seqCDF N_tbl 6 (2 ^ 15 - 1) := by
  have h := seqCDF_lb 6 .F .F .F rfl
  have hm : tripleMask .F .F .F = 2 ^ 15 - 1 := by decide
  have hw : bW .F * bW .F * bW .F = 64 := by decide
  rw [hm, hw] at h
  simpa using h

end Arxiv261114718

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2611_14718.main) := by
  intro h
  have hle := h Arxiv261114718.G Arxiv261114718.G_deg_le_three 6
  rw [Arxiv261114718.closedMask_G_eq] at hle
  rw [Arxiv261114718.staticCDF_val] at hle
  have hlb := Arxiv261114718.seqCDF_counterexample
  linarith
