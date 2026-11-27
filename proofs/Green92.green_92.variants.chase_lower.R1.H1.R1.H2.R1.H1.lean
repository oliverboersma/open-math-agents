import OMAReductions.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1

/-! Count the deletion masks S with trace w by the number emb u w of embeddings of w as a
subsequence of u = ofFn x (removal of the first letter gives the recursion). Embeddings into a
concatenation split at a cut point of w. The word W b is (01)^b 1 (01)^(2k+1-b), and embeddings
of w into the alternating word (01)^a number C(a + r, |w|) with r the number of 01 factors of w
(Pascal's rule, by induction on a). Splitting on whether the extra 1 is used gives B w + D b w. -/

namespace OMA.Green92Trace

open Finset

/-- Number of embeddings of the second list as a subsequence of the first. -/
def emb : List Bool → List Bool → ℕ
  | [], w => if w = [] then 1 else 0
  | _ :: u, [] => emb u []
  | x :: u, y :: w => emb u (y :: w) + if x = y then emb u w else 0

/-- Number of 01 factors. -/
def asc (v : List Bool) : ℕ := (v.zip v.tail).count (false, true)

/-- The alternating word (01)^a. -/
def alt : ℕ → List Bool
  | 0 => []
  | a + 1 => false :: true :: alt a

lemma emb_nil_right (u : List Bool) : emb u [] = 1 := by
  induction u with
  | nil => simp [emb]
  | cons x u ih => simp [emb, ih]

lemma emb_nil_left (w : List Bool) : emb [] w = if w = [] then 1 else 0 := by
  simp [emb]

lemma emb_cons_cons (x y : Bool) (u w : List Bool) :
    emb (x :: u) (y :: w) = emb u (y :: w) + if x = y then emb u w else 0 := by
  simp [emb]

lemma emb_true_cons (u v : List Bool) :
    emb (true :: u) v = emb u v + if v.head? = some true then emb u v.tail else 0 := by
  cases v with
  | nil => simp [emb]
  | cons y v => cases y <;> simp [emb]

lemma asc_nil : asc [] = 0 := by simp [asc]

lemma asc_single (x : Bool) : asc [x] = 0 := by simp [asc]

lemma asc_cons_cons (x y : Bool) (v : List Bool) :
    asc (x :: y :: v) = (if x = false ∧ y = true then 1 else 0) + asc (y :: v) := by
  simp only [asc, List.tail_cons, List.zip_cons_cons, List.count_cons]
  by_cases h : x = false ∧ y = true
  · obtain ⟨rfl, rfl⟩ := h
    simp
    ring
  · rw [if_neg h]
    have : ((x, y) == (false, true)) = false := by
      cases x <;> cases y <;> simp_all
    simp [this]

lemma asc_true_cons (v : List Bool) : asc (true :: v) = asc v := by
  cases v with
  | nil => simp [asc]
  | cons y v => rw [asc_cons_cons]; simp

lemma asc_lt (v : List Bool) (hv : v ≠ []) : asc v < v.length := by
  have h1 : asc v ≤ (v.zip v.tail).length := List.count_le_length
  have h2 : (v.zip v.tail).length = v.length - 1 := by
    simp [List.length_zip, List.length_tail]
  have h3 : 0 < v.length := List.length_pos_iff.mpr hv
  omega

lemma emb_append (u v w : List Bool) :
    emb (u ++ v) w = ∑ j ∈ range (w.length + 1), emb u (w.take j) * emb v (w.drop j) := by
  induction u generalizing w with
  | nil =>
    cases w with
    | nil => simp [emb]
    | cons y w =>
      rw [List.length_cons, sum_range_succ']
      simp [emb]
  | cons x u ih =>
    cases w with
    | nil => simp [emb, ih]
    | cons y w =>
      have e1 : emb ((x :: u) ++ v) (y :: w) =
          emb (u ++ v) (y :: w) + if x = y then emb (u ++ v) w else 0 := by
        rw [List.cons_append, emb_cons_cons]
      rw [e1, ih (y :: w), ih w, List.length_cons, sum_range_succ', sum_range_succ' _ (w.length + 1)]
      simp only [List.take_succ_cons, List.drop_succ_cons, List.take_zero, List.drop_zero,
        emb_cons_cons]
      have e2 : emb (x :: u) [] = emb u [] := by rw [emb_nil_right, emb_nil_right]
      rw [e2]
      by_cases hxy : x = y
      · simp only [hxy, if_true, add_mul, sum_add_distrib]
        ring
      · simp only [hxy, if_false, add_zero]

lemma alt_append (b c : ℕ) : alt b ++ alt c = alt (b + c) := by
  induction b with
  | zero => simp [alt]
  | succ b ih =>
    rw [Nat.succ_add]
    simp [alt, ih]

lemma choose_pascal (m l : ℕ) : (m + 1).choose (l + 1) = m.choose (l + 1) + m.choose l := by
  rw [Nat.choose_succ_succ]
  ring

lemma emb_alt (a : ℕ) (w : List Bool) :
    emb (alt a) w = (a + asc w).choose w.length := by
  induction a generalizing w with
  | zero =>
    rw [alt, emb_nil_left]
    by_cases hw : w = []
    · subst hw
      simp [asc]
    · rw [if_neg hw, zero_add, Nat.choose_eq_zero_of_lt (asc_lt w hw)]
  | succ a ih =>
    cases w with
    | nil => simp [alt, emb_nil_right]
    | cons y w =>
      cases y with
      | true =>
        -- emb (f :: t :: alt a) (t :: w) = emb (alt a) (t :: w) + emb (alt a) w
        have e : emb (alt (a + 1)) (true :: w) = emb (alt a) (true :: w) + emb (alt a) w := by
          simp only [alt, emb_cons_cons]
          simp
        rw [e, ih, ih, asc_true_cons, List.length_cons,
          show a + 1 + asc w = (a + asc w) + 1 by ring, choose_pascal]
      | false =>
        have e : emb (alt (a + 1)) (false :: w) =
            emb (alt a) (false :: w) + emb (true :: alt a) w := by
          simp only [alt, emb_cons_cons]
          simp
        rw [e, emb_true_cons]
        cases w with
        | nil =>
          simp only [ih, List.head?_nil, reduceCtorEq, if_false, add_zero, asc_single, asc_nil,
            List.length_cons, List.length_nil]
          rw [show a + 1 + 0 = (a + 0) + 1 by ring, choose_pascal]
        | cons z w =>
          cases z with
          | true =>
            have hA : asc (false :: true :: w) = asc w + 1 := by
              rw [asc_cons_cons, asc_true_cons]; simp [Nat.add_comm]
            simp only [ih, List.head?_cons, Option.some.injEq, if_true, List.tail_cons,
              List.length_cons, hA, asc_true_cons]
            have p1 : (a + asc w + 1 + 1).choose (w.length + 1 + 1) =
                (a + asc w + 1).choose (w.length + 1) + (a + asc w + 1).choose (w.length + 1 + 1) :=
              Nat.choose_succ_succ _ _
            have p2 : (a + asc w + 1).choose (w.length + 1) =
                (a + asc w).choose w.length + (a + asc w).choose (w.length + 1) :=
              Nat.choose_succ_succ _ _
            have q1 : a + 1 + (asc w + 1) = a + asc w + 1 + 1 := by ring
            have q2 : a + (asc w + 1) = a + asc w + 1 := by ring
            rw [q1, q2]
            omega
          | false =>
            simp only [ih, List.head?_cons, Option.some.injEq, Bool.false_eq_true, if_false,
              add_zero, List.length_cons]
            rw [asc_cons_cons]
            simp only [Bool.false_eq_true, and_false, if_false, zero_add]
            rw [show a + 1 + asc (false :: w) = (a + asc (false :: w)) + 1 by ring, choose_pascal]

lemma length_alt (a : ℕ) : (alt a).length = 2 * a := by
  induction a with
  | zero => simp [alt]
  | succ a ih => simp [alt, ih]; ring

lemma getElem_alt (a i : ℕ) (h : i < (alt a).length) : (alt a)[i] = decide (i % 2 = 1) := by
  induction a generalizing i with
  | zero => simp [alt] at h
  | succ a ih =>
    match i with
    | 0 => simp [alt]
    | 1 => simp [alt]
    | i + 2 =>
      have h' : i < (alt a).length := by simp [alt] at h; omega
      simp only [alt, List.getElem_cons_succ]
      rw [ih i h']
      simp [Nat.add_mod]

/-- Deletion masks of a word and embeddings of the trace. -/
lemma card_trace (n : ℕ) (x : Fin n → Bool) (w : List Bool) :
    (univ.filter (fun S : Finset (Fin n) => Green92.trace x S = w)).card =
      emb (List.ofFn x) w := by
  classical
  induction n generalizing w with
  | zero =>
    have hu : (univ : Finset (Finset (Fin 0))) = {∅} := by
      ext S
      simp only [mem_univ, mem_singleton, true_iff]
      exact Finset.eq_empty_of_isEmpty S
    rw [hu, filter_singleton]
    have ht : Green92.trace x ∅ = [] := by simp [Green92.trace]
    rw [ht]
    by_cases hw : w = []
    · subst hw; simp [emb]
    · rw [if_neg (Ne.symm hw)]; simp [emb, hw]
  | succ n ih =>
    have tr0 (T : Finset (Fin n)) :
        Green92.trace x (T.image Fin.succ) = Green92.trace (Fin.tail x) T := by
      simp only [Green92.trace, List.finRange_succ, List.filter_cons, List.filter_map]
      have h0 : (0 : Fin (n + 1)) ∉ T.image Fin.succ := by simp [Fin.succ_ne_zero]
      simp [h0, Function.comp_def, Fin.tail, Finset.mem_image, Fin.succ_inj]
    have tr1 (T : Finset (Fin n)) :
        Green92.trace x (insert 0 (T.image Fin.succ)) = x 0 :: Green92.trace (Fin.tail x) T := by
      simp only [Green92.trace, List.finRange_succ, List.filter_cons, List.filter_map]
      simp [Function.comp_def, Fin.tail, Finset.mem_image, Fin.succ_inj, Fin.succ_ne_zero]
    have huniv : (univ : Finset (Fin (n + 1))) = insert 0 (univ.image Fin.succ) := by
      ext i; cases i using Fin.cases <;> simp
    have h0 : (0 : Fin (n + 1)) ∉ (univ : Finset (Fin n)).image Fin.succ := by
      simp [Fin.succ_ne_zero]
    have hinj : Set.InjOn (fun T : Finset (Fin n) => T.image Fin.succ)
        ((univ : Finset (Fin n)).powerset : Set (Finset (Fin n))) :=
      fun _ _ _ _ h => Finset.image_injective (Fin.succ_injective n) h
    rw [card_filter, ← powerset_univ, huniv, sum_powerset_insert h0, powerset_image,
      sum_image hinj, sum_image hinj]
    simp only [tr0, tr1]
    have ihs (v : List Bool) : (∑ T ∈ (univ : Finset (Fin n)).powerset,
        if Green92.trace (Fin.tail x) T = v then 1 else 0) = emb (List.ofFn (Fin.tail x)) v := by
      rw [powerset_univ, ← card_filter]
      exact ih (Fin.tail x) v
    rw [ihs, List.ofFn_succ]
    have hofn : List.ofFn (fun i : Fin n => x i.succ) = List.ofFn (Fin.tail x) := rfl
    rw [hofn]
    cases w with
    | nil => simp [emb]
    | cons y w =>
      rw [emb_cons_cons]
      simp only [List.cons.injEq]
      by_cases hxy : x 0 = y
      · simp only [hxy, true_and, if_true]
        rw [ihs]
      · simp [hxy]

end OMA.Green92Trace

open Finset OMA.Green92Trace in
theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1.H1 := by
  intro n hn k W F B D b hb w
  classical
  have hn' : n = 4 * k + 3 := by omega
  set c := 2 * k + 1 - b with hc
  have hbc : b + c = 2 * k + 1 := by omega
  have hF (a : ℕ) (v : List Bool) : F a v = emb (alt a) v := by
    rw [emb_alt]; rfl
  -- the word
  have hword : List.ofFn (W b) = alt b ++ true :: alt c := by
    apply List.ext_getElem
    · simp [length_alt]; omega
    · intro i h1 h2
      rw [List.getElem_ofFn]
      simp only [W]
      have hl : (alt b).length = 2 * b := length_alt b
      by_cases hi : i < 2 * b
      · rw [List.getElem_append_left (by omega), getElem_alt]
        simp [hi]
      · rw [List.getElem_append_right (by omega)]
        simp only [hl]
        by_cases hi2 : i = 2 * b
        · subst hi2; simp
        · have : i - 2 * b = (i - 2 * b - 1) + 1 := by omega
          rw [List.getElem_cons, dif_neg (by omega), getElem_alt]
          simp only [hi, if_false]
          apply decide_eq_decide.mpr
          omega
  rw [card_trace, hword, emb_append]
  simp only [emb_true_cons, mul_add, sum_add_distrib]
  have hfirst : (∑ j ∈ range (w.length + 1), emb (alt b) (w.take j) * emb (alt c) (w.drop j)) =
      B w := by
    rw [← emb_append, alt_append, hbc]
    exact (hF _ _).symm
  rw [hfirst]
  congr 1
  simp only [D]
  rw [sum_range_succ]
  have hlast : (w.drop w.length).head? = none := by simp
  rw [hlast]
  simp only [reduceCtorEq, if_false, mul_zero, add_zero]
  apply sum_congr rfl
  intro j hj
  rw [List.head?_drop, List.tail_drop, hF, hF]
  split_ifs <;> simp [hc]
