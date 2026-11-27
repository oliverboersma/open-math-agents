import FormalConjectures.OEIS.«109074»

/-! Proof of OeisA109074.conjecture via the 6-vertex transfer matrix over ℚ[q]/(q^2 - q + 1),
Sklyanin reflection equation, Chebyshev unitriangularity, and direct polynomial interpolation. -/

namespace OMA.R_OeisA109074_conjecture_R1

open Finset OeisA109074

private theorem factor_eq (n : ℕ) : frac (n+1) = ((6*n+4).factorial : ℚ) * (2*n+1).factorial /
    (2 * (4*n+3).factorial * (4*n+2).factorial) := by
  unfold frac
  rw [show 6*(n+1)-2 = 6*n+4 by omega, show 4*(n+1)-1 = 4*n+3 by omega]
  push_cast
  rw [Nat.cast_choose ℚ (show 2*(n+1) ≤ 6*n+4 by omega),
      Nat.cast_choose ℚ (show 2*(n+1) ≤ 4*n+3 by omega),
      show 6*n+4-2*(n+1) = 4*n+2 by omega,
      show 4*n+3-2*(n+1) = 2*n+1 by omega]
  have pos (k : ℕ) : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  field_simp [fun k => (pos k).ne']

-- The symbols 0, 1, 2 encode the matrix entries -1, 0, 1.
def H1 : Prop := ∀ n : ℕ,
  let I := Fin (2*n+1)
  let lineOK (v : I → Fin 3) :=
    let partialSum (k : ℕ) := ∑ j : I, if j.val < k then ((v j).val : ℤ) - 1 else 0
    partialSum (2*n+1) = 1 ∧ ∀ k : Fin (2*n+2), partialSum k.val = 0 ∨ partialSum k.val = 1
  let matrices : Set (I → I → Fin 3) := {M | (∀ i, lineOK (M i)) ∧
    (∀ j, lineOK fun i => M i j) ∧ ∀ i j, M i j = M i (Fin.rev j)}
  b n = matrices.ncard

def H2 : Prop := ∀ n : ℕ,
  let I := Fin (2*n+1)
  let lineOK (v : I → Fin 3) :=
    let partialSum (k : ℕ) := ∑ j : I, if j.val < k then ((v j).val : ℤ) - 1 else 0
    partialSum (2*n+1) = 1 ∧ ∀ k : Fin (2*n+2), partialSum k.val = 0 ∨ partialSum k.val = 1
  let matrices : Set (I → I → Fin 3) := {M | (∀ i, lineOK (M i)) ∧
    (∀ j, lineOK fun i => M i j) ∧ ∀ i j, M i j = M i (Fin.rev j)}
  (matrices.ncard : ℚ) = ∏ k ∈ range n, ((6*k+4).factorial : ℚ) * (2*k+1).factorial /
    (2 * (4*k+3).factorial * (4*k+2).factorial)

theorem main : H1 → H2 → type_of% @OeisA109074.conjecture := by
  intro hcount hformula n
  let F (k : ℕ) : ℚ := ((6*k+4).factorial : ℚ) * (2*k+1).factorial /
    (2 * (4*k+3).factorial * (4*k+2).factorial)
  have eqn (j : ℕ) : (b j : ℚ) = ∏ k ∈ range j, F k := by
    rw [hcount j]
    exact hformula j
  have pos (k : ℕ) : 0 < F k := by dsimp [F]; positivity
  have hp : (∏ k ∈ range n, F k) ≠ 0 := (Finset.prod_pos (fun i _ => pos i)).ne'
  rw [eqn, eqn, prod_range_succ]
  change frac (n+1) = (∏ k ∈ range n, F k) * F n / (∏ k ∈ range n, F k)
  rw [mul_div_cancel_left₀ _ hp]
  exact factor_eq n

end OMA.R_OeisA109074_conjecture_R1


section InlinedR1H1

open OeisA109074

namespace OMAA109074H1

theorem take_ofFn_sum : ∀ (m : ℕ) (g : Fin m → ℤ) (k : ℕ),
    ((List.ofFn g).take k).sum = ∑ j : Fin m, if j.val < k then g j else 0
  | 0, g, k => by simp
  | m+1, g, 0 => by simp
  | m+1, g, k+1 => by
    rw [List.ofFn_succ, List.take_succ_cons, List.sum_cons, take_ofFn_sum m _ k, Fin.sum_univ_succ]
    simp [Fin.val_succ]

theorem aux_iff : ∀ (xs : List ℤ) (acc : ℤ), isAsmLineAux acc xs = true ↔
    (∀ i, i < xs.length → (acc + (xs.take (i+1)).sum = 0 ∨ acc + (xs.take (i+1)).sum = 1)) ∧
      acc + xs.sum = 1
  | [], acc => by simp [isAsmLineAux]
  | x :: xs, acc => by
    simp only [isAsmLineAux, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, aux_iff xs (acc + x)]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun i hi => ?_, by simp; linarith⟩
      cases i with
      | zero => simpa using h0
      | succ i =>
        have := h1 i (by simpa using hi)
        simp only [List.take_succ_cons, List.sum_cons]
        rw [← add_assoc]; exact this
    · rintro ⟨h1, h2⟩
      refine ⟨by simpa using h1 0 (by simp), fun i hi => ?_, by simp at h2; linarith⟩
      have := h1 (i+1) (by simp; omega)
      simp only [List.take_succ_cons, List.sum_cons] at this
      rw [add_assoc]; exact this

def rowList {m : ℕ} (v : Fin m → Fin 3) : List ℤ := List.ofFn fun j => ((v j).val : ℤ) - 1

def LineOK (m : ℕ) (v : Fin m → Fin 3) : Prop :=
  let partialSum (k : ℕ) := ∑ j : Fin m, if j.val < k then ((v j).val : ℤ) - 1 else 0
  partialSum m = 1 ∧ ∀ k : Fin (m+1), partialSum k.val = 0 ∨ partialSum k.val = 1

theorem isAsmLine_rowList (m : ℕ) (v : Fin m → Fin 3) :
    isAsmLine (rowList v) = true ↔ LineOK m v := by
  unfold isAsmLine LineOK
  rw [aux_iff]
  simp only [zero_add, ← take_ofFn_sum]
  have hl : (rowList v).length = m := by simp [rowList]
  have hs : ((rowList v).take m).sum = (rowList v).sum := by
    rw [List.take_of_length_le (by omega)]
  rw [hl]
  unfold rowList at hs ⊢
  rw [hs]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun k => ?_⟩
    rcases k with ⟨k, hk⟩
    cases k with
    | zero => simp
    | succ k => exact h1 k (by omega)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h2 ⟨i+1, by omega⟩, h1⟩


def Tri (x : ℤ) : Prop := x = -1 ∨ x = 0 ∨ x = 1

theorem mem_trinaryLists : ∀ (k : ℕ) (xs : List ℤ),
    xs ∈ trinaryLists k ↔ xs.length = k ∧ ∀ x ∈ xs, Tri x
  | 0, xs => by
    simp only [trinaryLists, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.mp h
  | k+1, xs => by
    simp only [trinaryLists, List.mem_flatMap, mem_trinaryLists k, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨ys, ⟨hl, hy⟩, h | h | h⟩ <;> subst h <;>
        refine ⟨by simp [hl], fun x hx => ?_⟩ <;>
        simp only [List.mem_cons] at hx <;> rcases hx with rfl | hx <;>
        first | exact hy x hx | (unfold Tri; norm_num)
    · rintro ⟨hl, hx⟩
      cases xs with
      | nil => simp at hl
      | cons x ys =>
        refine ⟨ys, ⟨by simpa using hl, fun y hy => hx y (by simp [hy])⟩, ?_⟩
        rcases hx x (by simp) with rfl | rfl | rfl <;> simp

theorem nodup_trinaryLists : ∀ k, (trinaryLists k).Nodup
  | 0 => by simp [trinaryLists]
  | k+1 => by
    rw [trinaryLists, List.nodup_flatMap]
    refine ⟨fun xs _ => by simp, ?_⟩
    refine (nodup_trinaryLists k).imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro l (rfl | rfl | rfl) (h | h | h) <;> simp at h <;> exact hab h

theorem row_decomp (n : ℕ) (r : List ℤ) (hl : r.length = 2*n+1) (hr : r.reverse = r) :
    r = r.take n ++ [r[n]'(by omega)] ++ (r.take n).reverse := by
  have h1 : (r.take n).reverse = r.drop (n+1) := by
    rw [List.reverse_take, hr, hl]; congr 1; omega
  rw [h1, List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons,
    List.take_append_drop]

theorem mem_symAsmRows (n : ℕ) (r : List ℤ) :
    r ∈ symAsmRows n ↔ r.length = 2*n+1 ∧ (∀ x ∈ r, Tri x) ∧ r.reverse = r ∧
      isAsmLine r = true := by
  unfold symAsmRows
  simp only [List.mem_flatMap, List.mem_filterMap, mem_trinaryLists]
  constructor
  · rintro ⟨half, ⟨hl, hh⟩, mid, hmid, h⟩
    split_ifs at h with ha
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨by simp [hl]; omega, fun x hx => ?_, by simp, ha⟩
    simp only [List.mem_append, List.mem_reverse, List.mem_singleton] at hx
    rcases hx with (hx | rfl) | hx
    · exact hh x hx
    · simp at hmid; unfold Tri; omega
    · exact hh x hx
  · rintro ⟨hl, hx, hr, ha⟩
    have hd := row_decomp n r hl hr
    refine ⟨r.take n, ⟨by simp; omega, fun x h => hx x (List.mem_of_mem_take h)⟩,
      r[n]'(by omega), ?_, ?_⟩
    · have := hx (r[n]'(by omega)) (List.getElem_mem _)
      unfold Tri at this; simp; omega
    · rw [← hd, if_pos ha]

theorem nodup_symAsmRows (n : ℕ) : (symAsmRows n).Nodup := by
  unfold symAsmRows
  rw [List.nodup_flatMap]
  constructor
  · intro half _
    apply List.Nodup.filterMap _ (by simp)
    intro a a' b ha ha'
    simp only [Option.mem_def] at ha ha'
    split_ifs at ha ha' <;> simp at ha ha'
    subst ha
    simp at ha'
    exact ha'.symm
  · refine (nodup_trinaryLists n).imp_of_mem ?_
    intro a b ha hb hab
    simp only [Function.onFun, List.disjoint_left, List.mem_filterMap]
    rintro l ⟨x, -, hx⟩ ⟨y, -, hy⟩
    split_ifs at hx hy <;> simp at hx hy
    rw [mem_trinaryLists] at ha hb
    have := congrArg (List.take n) (hx.trans hy.symm)
    simp [ha.1, hb.1] at this
    exact hab this


theorem rowList_injective {m : ℕ} : Function.Injective (@rowList m) := by
  intro v w h
  have := List.ofFn_injective h
  funext j
  have hj := congrFun this j
  apply Fin.ext
  omega

theorem rowList_reverse {m : ℕ} (v : Fin m → Fin 3) :
    (rowList v).reverse = rowList (fun j => v j.rev) := by
  apply List.ext_getElem (by simp [rowList])
  intro i h1 h2
  simp only [rowList, List.getElem_reverse, List.getElem_ofFn, List.length_ofFn]
  have hi : i < m := by simpa [rowList] using h2
  have : (Fin.rev ⟨i, hi⟩ : Fin m) = ⟨m - 1 - i, by omega⟩ := Fin.ext (by simp [Fin.val_rev]; omega)
  rw [this]

theorem rowList_mem (n : ℕ) (v : Fin (2*n+1) → Fin 3) :
    rowList v ∈ symAsmRows n ↔ LineOK (2*n+1) v ∧ ∀ j, v j = v j.rev := by
  rw [mem_symAsmRows, isAsmLine_rowList, rowList_reverse]
  have htri : ∀ x ∈ rowList v, Tri x := by
    intro x hx
    simp only [rowList, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    have := (v j).isLt
    unfold Tri; omega
  have hsym : rowList (fun j => v j.rev) = rowList v ↔ ∀ j, v j = v j.rev := by
    constructor
    · intro h j; exact (congrFun (rowList_injective h) j).symm
    · intro h; congr 1; funext j; exact (h j).symm
  rw [hsym]
  simp [rowList, htri]
  tauto

def toF3 (x : ℤ) : Fin 3 := if x = -1 then 0 else if x = 0 then 1 else 2

theorem exists_rowList {m : ℕ} (r : List ℤ) (hl : r.length = m) (ht : ∀ x ∈ r, Tri x) :
    ∃ v : Fin m → Fin 3, rowList v = r := by
  refine ⟨fun j => toF3 (r[j.val]'(by omega)), ?_⟩
  apply List.ext_getElem (by simp [rowList, hl])
  intro i h1 h2
  simp only [rowList, List.getElem_ofFn]
  have := ht _ (List.getElem_mem h2)
  unfold Tri at this
  unfold toF3
  rcases this with h | h | h <;> simp [h]

theorem foldl_eq_sum (rows : List (List ℤ)) (p : List ℤ → Bool) (g : List ℤ → ℕ) :
    ∀ a : ℕ, rows.foldl (fun acc r => if p r then acc + g r else acc) a =
      a + (rows.map fun r => if p r then g r else 0).sum := by
  induction rows with
  | nil => intro a; simp
  | cons r rs ih =>
    intro a
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]
    split_ifs <;> omega

def lists (rows : List (List ℤ)) : ℕ → List (List (List ℤ))
  | 0 => [[]]
  | k+1 => rows.flatMap fun r => (lists rows k).map (r :: ·)

def good : List ℤ → List (List ℤ) → Bool
  | c, [] => c.all (· == 1)
  | c, r :: L => (List.zipWith (· + ·) c r).all (fun s => s == 0 || s == 1) &&
      good (List.zipWith (· + ·) c r) L

theorem count_eq (rows : List (List ℤ)) : ∀ (k : ℕ) (c : List ℤ),
    countVsasmRows rows k c = ((lists rows k).filter (good c)).length
  | 0, c => by
    simp only [countVsasmRows, lists]
    by_cases h : (c.all fun x => x == 1) = true
    · rw [if_pos h, List.filter_cons_of_pos (by simpa [good] using h)]; rfl
    · rw [if_neg h, List.filter_cons_of_neg (by simpa [good] using h)]; rfl
  | k+1, c => by
    simp only [countVsasmRows]
    rw [foldl_eq_sum rows (fun r => (List.zipWith (· + ·) c r).all (fun s => s == 0 || s == 1))
      (fun r => countVsasmRows rows k (List.zipWith (· + ·) c r)) 0]
    simp only [lists, List.filter_flatMap, List.length_flatMap, zero_add]
    congr 1
    apply List.map_congr_left
    intro r _
    rw [List.filter_map, List.length_map, count_eq rows k]
    split_ifs with h
    · congr 2
      funext L
      simp [good, h]
    · have : (good c ∘ (r :: ·)) = fun _ => false := by
        funext L; simp [good, h]
      rw [this]; simp

theorem mem_lists (rows : List (List ℤ)) : ∀ (k : ℕ) (L : List (List ℤ)),
    L ∈ lists rows k ↔ L.length = k ∧ ∀ r ∈ L, r ∈ rows
  | 0, L => by
    simp only [lists, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.mp h
  | k+1, L => by
    simp only [lists, List.mem_flatMap, List.mem_map, mem_lists rows k]
    constructor
    · rintro ⟨r, hr, L', ⟨hl, hL⟩, rfl⟩
      refine ⟨by simp [hl], fun x hx => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hr
      · exact hL x hx
    · rintro ⟨hl, hL⟩
      cases L with
      | nil => simp at hl
      | cons r L' =>
        exact ⟨r, hL r (by simp), L', ⟨by simpa using hl, fun x hx => hL x (by simp [hx])⟩, rfl⟩

theorem nodup_lists (rows : List (List ℤ)) (hr : rows.Nodup) : ∀ k, (lists rows k).Nodup
  | 0 => by simp [lists]
  | k+1 => by
    rw [lists, List.nodup_flatMap]
    refine ⟨fun r _ => (nodup_lists rows hr k).map (fun a b h => by simpa using h), ?_⟩
    refine hr.imp ?_
    intro a b hab
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro l ⟨x, -, rfl⟩ ⟨y, -, hy⟩
    simp at hy
    exact hab hy.1.symm


theorem zipWith_ofFn {m : ℕ} (f g : Fin m → ℤ) :
    List.zipWith (· + ·) (List.ofFn f) (List.ofFn g) = List.ofFn (fun j => f j + g j) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2; simp

theorem all_ofFn_iff {m : ℕ} (f : Fin m → ℤ) (p : ℤ → Bool) :
    (List.ofFn f).all p = true ↔ ∀ j, p (f j) = true := by
  simp [List.all_eq_true, List.mem_ofFn]

def ColGood (k m : ℕ) (cf : Fin m → ℤ) (A : Fin k → Fin m → ℤ) : Prop :=
  (∀ t, 1 ≤ t → t ≤ k → ∀ j, cf j + (∑ i : Fin k, if i.val < t then A i j else 0) = 0 ∨
      cf j + (∑ i : Fin k, if i.val < t then A i j else 0) = 1) ∧
  ∀ j, cf j + ∑ i, A i j = 1

theorem good_iff {m : ℕ} : ∀ (k : ℕ) (cf : Fin m → ℤ) (A : Fin k → Fin m → ℤ),
    good (List.ofFn cf) (List.ofFn fun i => List.ofFn (A i)) = true ↔ ColGood k m cf A
  | 0, cf, A => by
    rw [List.ofFn_zero, good, all_ofFn_iff]
    unfold ColGood
    simp only [beq_iff_eq, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    constructor
    · intro h; exact ⟨fun t h1 h2 => by omega, h⟩
    · intro h; exact h.2
  | k+1, cf, A => by
    rw [List.ofFn_succ, good, zipWith_ofFn, Bool.and_eq_true, good_iff k, all_ofFn_iff]
    unfold ColGood
    simp only [Bool.or_eq_true, beq_iff_eq, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    constructor
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun t ht1 htk j => ?_, fun j => by rw [← h2 j]; ring⟩
      rcases (show t = 1 ∨ 2 ≤ t by omega) with rfl | ht
      · have : ∀ i : Fin k, ¬ (i.val + 1 < 1) := fun i => by omega
        simp only [this, if_false, Finset.sum_const_zero, add_zero, zero_lt_one, if_true]
        exact h0 j
      · obtain ⟨t', rfl⟩ : ∃ t', t = t'+1 := ⟨t-1, by omega⟩
        have := h1 t' (by omega) (by omega) j
        have e : ∀ i : Fin k, (i.val + 1 < t' + 1) ↔ i.val < t' := fun i => by omega
        simp only [e, Nat.zero_lt_succ, if_true]
        rw [← add_assoc]; exact this
    · rintro ⟨h1, h2⟩
      refine ⟨fun j => ?_, fun t ht1 htk j => ?_, fun j => by rw [← h2 j]; ring⟩
      · have := h1 1 le_rfl (by omega) j
        have : ∀ i : Fin k, ¬ (i.val + 1 < 1) := fun i => by omega
        simpa [this] using h1 1 le_rfl (by omega) j
      · have := h1 (t+1) (by omega) (by omega) j
        have e : ∀ i : Fin k, (i.val + 1 < t + 1) ↔ i.val < t := fun i => by omega
        simp only [e, Nat.zero_lt_succ, if_true] at this
        rw [add_assoc]; exact this

theorem colGood_iff (m : ℕ) (A : Fin m → Fin m → Fin 3) :
    ColGood m m (fun _ => 0) (fun i j => ((A i j).val : ℤ) - 1) ↔
      ∀ j, LineOK m (fun i => A i j) := by
  unfold ColGood LineOK
  simp only [zero_add]
  have htot : ∀ j, (∑ i : Fin m, if i.val < m then ((A i j).val : ℤ) - 1 else 0) =
      ∑ i : Fin m, (((A i j).val : ℤ) - 1) :=
    fun j => Finset.sum_congr rfl fun i _ => if_pos i.isLt
  constructor
  · rintro ⟨h1, h2⟩ j
    refine ⟨by rw [htot]; exact h2 j, fun k => ?_⟩
    rcases k with ⟨k, hk⟩
    cases k with
    | zero => simp
    | succ k => exact h1 (k+1) (by omega) (by omega) j
  · intro h
    exact ⟨fun t h1 h2 j => (h j).2 ⟨t, by omega⟩, fun j => by rw [← htot]; exact (h j).1⟩

def Mat (n : ℕ) : Set (Fin (2*n+1) → Fin (2*n+1) → Fin 3) :=
  {M | (∀ i, LineOK (2*n+1) (M i)) ∧ (∀ j, LineOK (2*n+1) fun i => M i j) ∧
    ∀ i j, M i j = M i (Fin.rev j)}

def fM {m : ℕ} (M : Fin m → Fin m → Fin 3) : List (List ℤ) := List.ofFn fun i => rowList (M i)

theorem fM_injective {m : ℕ} : Function.Injective (@fM m) := by
  intro M M' h
  have := List.ofFn_injective h
  funext i
  exact rowList_injective (congrFun this i)

theorem fM_mem (n : ℕ) (M : Fin (2*n+1) → Fin (2*n+1) → Fin 3) :
    (fM M ∈ lists (symAsmRows n) (2*n+1) ∧
      good (List.replicate (2*n+1) 0) (fM M) = true) ↔ M ∈ Mat n := by
  have hc : List.replicate (2*n+1) (0:ℤ) = List.ofFn (fun _ : Fin (2*n+1) => (0:ℤ)) := by
    rw [List.ofFn_const]
  rw [mem_lists, hc, show fM M = List.ofFn fun i => List.ofFn fun j => ((M i j).val : ℤ) - 1
    from rfl, good_iff, colGood_iff]
  have hrows : (∀ r ∈ List.ofFn (fun i => List.ofFn fun j => ((M i j).val : ℤ) - 1),
      r ∈ symAsmRows n) ↔ ∀ i, LineOK (2*n+1) (M i) ∧ ∀ j, M i j = M i j.rev := by
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
    exact forall_congr' fun i => rowList_mem n (M i)
  rw [hrows]
  simp only [List.length_ofFn, true_and, Mat, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i => (h1 i).1, h2, fun i => (h1 i).2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨fun i => ⟨h1 i, h3 i⟩, h2⟩

theorem surj (n : ℕ) (L : List (List ℤ)) (hL : L ∈ lists (symAsmRows n) (2*n+1)) :
    ∃ M : Fin (2*n+1) → Fin (2*n+1) → Fin 3, fM M = L := by
  rw [mem_lists] at hL
  obtain ⟨hl, hr⟩ := hL
  have : ∀ i : Fin (2*n+1), ∃ v : Fin (2*n+1) → Fin 3, rowList v = L[i.val]'(by omega) := by
    intro i
    have h := (mem_symAsmRows n (L[i.val]'(by omega))).1 (hr _ (List.getElem_mem _))
    exact exists_rowList _ h.1 h.2.1
  choose M hM using this
  refine ⟨M, List.ext_getElem (by simp [fM, hl]) fun i h1 h2 => ?_⟩
  simp only [fM, List.getElem_ofFn]
  exact hM ⟨i, by simpa [fM] using h1⟩

theorem main_eq (n : ℕ) : b n = (Mat n).ncard := by
  have hb : b n = ((lists (symAsmRows n) (2*n+1)).filter
      (good (List.replicate (2*n+1) 0))).length := count_eq _ _ _
  have hnd := ((nodup_lists _ (nodup_symAsmRows n) (2*n+1)).filter
    (good (List.replicate (2*n+1) 0)))
  have himg : fM '' Mat n = ↑((lists (symAsmRows n) (2*n+1)).filter
      (good (List.replicate (2*n+1) 0))).toFinset := by
    ext L
    simp only [Set.mem_image, Finset.mem_coe, List.mem_toFinset, List.mem_filter]
    constructor
    · rintro ⟨M, hM, rfl⟩; exact (fM_mem n M).2 hM
    · rintro hL
      obtain ⟨M, rfl⟩ := surj n L hL.1
      exact ⟨M, (fM_mem n M).1 hL, rfl⟩
  rw [hb, ← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset, ← himg,
    Set.ncard_image_of_injective _ fM_injective]

end OMAA109074H1

end InlinedR1H1


namespace OMA.R_OeisA109074_conjecture_R1_H2_R1

open Finset

private theorem denominator_row (j : ℕ) :
    (j+1) * (∏ i ∈ range j, ((j+1)-(i+1)) * ((j+1)+(i+1))) = (2*j+1).factorial := by
  calc
    _ = (j+1) * (∏ i ∈ range j, (j-i) * ((j+1+1)+i)) := by
      apply congrArg ((j+1) * ·)
      apply prod_congr rfl
      intro i _
      exact congrArg₂ Nat.mul (by omega) (by omega)
    _ = _ := by
      rw [prod_mul_distrib, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self,
        ← Nat.ascFactorial_eq_prod_range, ← mul_assoc, ← Nat.factorial_succ,
        Nat.factorial_mul_ascFactorial]
      congr 1
      omega

def H1 : Prop := ∀ n : ℕ,
  let I := Fin (2*n+1)
  let lineOK (v : I → Fin 3) :=
    let partialSum (k : ℕ) := ∑ j : I, if j.val < k then ((v j).val : ℤ) - 1 else 0
    partialSum (2*n+1) = 1 ∧ ∀ k : Fin (2*n+2), partialSum k.val = 0 ∨ partialSum k.val = 1
  let matrices : Set (I → I → Fin 3) := {M | (∀ i, lineOK (M i)) ∧
    (∀ j, lineOK fun i => M i j) ∧ ∀ i j, M i j = M i (Fin.rev j)}
  let alt (a : ℕ → ℕ) := ∏ j ∈ range (2*n),
    a j * ∏ i ∈ range j, (a j - a i) * (a j + a i)
  3^(n*(n-1)) * matrices.ncard * alt (fun j => j+1) = alt (fun j => j+1+j/2)

def H2 : Prop := ∀ n : ℕ,
  let a (j : ℕ) := j+1+j/2
  let row (j : ℕ) := a j * ∏ i ∈ range j, (a j - a i) * (a j + a i)
  2*(4*n+2) * (row (2*n) * row (2*n+1)) =
    3^(2*n) * (6*n+4).factorial * (2*n+1).factorial

theorem main : H1 → H2 → OMA.R_OeisA109074_conjecture_R1.H2 := by
  intro hs hr
  let a (j : ℕ) := j+1+j/2
  let row (j : ℕ) := a j * ∏ i ∈ range j, (a j - a i) * (a j + a i)
  let numer (n : ℕ) : ℚ := ∏ j ∈ range (2*n), (row j : ℚ)
  let denom (n : ℕ) : ℚ := ∏ j ∈ range (2*n), ((2*j+1).factorial : ℚ)
  let factor (k : ℕ) : ℚ := ((6*k+4).factorial : ℚ) * (2*k+1).factorial /
    (2 * (4*k+3).factorial * (4*k+2).factorial)
  have pos (k : ℕ) : (0 : ℚ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have step (n : ℕ) : (row (2*n) : ℚ) * row (2*n+1) =
      (3:ℚ)^(2*n) * factor n * (4*n+1).factorial * (4*n+3).factorial := by
    have h := hr n
    change 2*(4*n+2) * (row (2*n) * row (2*n+1)) = _ at h
    have hc : (2:ℚ)*(4*n+2) * ((row (2*n) : ℚ) * row (2*n+1)) =
        (3:ℚ)^(2*n) * (6*n+4).factorial * (2*n+1).factorial := by exact_mod_cast h
    have fac : ((4*n+2).factorial : ℚ) = (4*(n:ℚ)+2) * (4*n+1).factorial := by
      exact_mod_cast Nat.factorial_succ (4*n+1)
    calc
      _ = (3:ℚ)^(2*n) * (6*n+4).factorial * (2*n+1).factorial / (2*(4*n+2)) := by
        apply (eq_div_iff (by positivity)).mpr
        rwa [mul_comm]
      _ = _ := by
        dsimp only [factor]
        rw [fac]
        field_simp [fun k => (pos k).ne']
  have eval (n : ℕ) : numer n = (3:ℚ)^(n*(n-1)) *
      (∏ k ∈ range n, factor k) * denom n := by
    induction n with
    | zero => simp [numer, denom]
    | succ n ih =>
      have e : (n+1)*((n+1)-1) = n*(n-1)+2*n := by
        cases n <;> simp
        ring
      have index : 2*(n+1) = 2*n+1+1 := by omega
      have hn : numer (n+1) = numer n * ((row (2*n) : ℚ) * row (2*n+1)) := by
        simp only [numer, index, prod_range_succ, mul_assoc]
      have hd : denom (n+1) = denom n * ((4*n+1).factorial : ℚ) * (4*n+3).factorial := by
        simp only [denom, index, prod_range_succ, show 2*(2*n)+1 = 4*n+1 by omega,
          show 2*(2*n+1)+1 = 4*n+3 by omega]
      rw [hn, step, ih, hd, e, pow_add, prod_range_succ]
      ring
  intro n
  have h := hs n
  dsimp only at h ⊢
  simp_rw [denominator_row] at h
  have hd : 0 < denom n := Finset.prod_pos (fun j _ => pos (2*j+1))
  apply mul_left_cancel₀ (by positivity : (3:ℚ)^(n*(n-1)) ≠ 0)
  apply mul_right_cancel₀ hd.ne'
  change _ = (3:ℚ)^(n*(n-1)) * (∏ k ∈ range n, factor k) * denom n
  rw [← eval]
  dsimp only [denom, numer]
  exact_mod_cast h

end OMA.R_OeisA109074_conjecture_R1_H2_R1


namespace OMA109074

open Finset

def aa (j : ℕ) : ℕ := j + 1 + j / 2

def rowf (j : ℕ) : ℕ := aa j * ∏ i ∈ range j, (aa j - aa i) * (aa j + aa i)

lemma aa_even (m : ℕ) : aa (2 * m) = 3 * m + 1 := by
  unfold aa
  omega

lemma aa_odd (m : ℕ) : aa (2 * m + 1) = 3 * m + 2 := by
  unfold aa
  omega

lemma prod_pair (g : ℕ → ℕ) (n : ℕ) :
    ∏ i ∈ range (2 * n), g i = ∏ m ∈ range n, g (2 * m) * g (2 * m + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ]
    ring

lemma split_prod (f : ℕ → ℕ) (n : ℕ) :
    (∏ m ∈ range n, f (n - 1 - m)) * (∏ m ∈ range n, f (n + m)) = ∏ k ∈ range (2 * n), f k := by
  have h : ∏ k ∈ Ico n (2 * n), f k = ∏ m ∈ range n, f (n + m) := by
    rw [Finset.prod_Ico_eq_prod_range, show 2 * n - n = n from by omega]
  rw [Finset.prod_range_reflect, ← h]
  exact Finset.prod_range_mul_prod_Ico f (by omega)

lemma rowA (n : ℕ) :
    ∏ i ∈ range (2 * n), (aa (2 * n) - aa i) * (aa (2 * n) + aa i) =
      ∏ k ∈ range (2 * n), (3 * k + 2) * (3 * k + 3) := by
  rw [prod_pair, ← split_prod (fun k => (3 * k + 2) * (3 * k + 3)) n, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  have hm' : m < n := Finset.mem_range.1 hm
  rw [aa_even, aa_even, aa_odd]
  obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - m - 1, by omega⟩
  have e1 : 3 * (m + 1 + d) + 1 - (3 * m + 1) = 3 * d + 3 := by omega
  have e2 : 3 * (m + 1 + d) + 1 - (3 * m + 2) = 3 * d + 2 := by omega
  have e3 : m + 1 + d - 1 - m = d := by omega
  simp only [e1, e2, e3]
  ring

lemma rowB (n : ℕ) :
    ∏ i ∈ range (2 * n + 1), (aa (2 * n + 1) - aa i) * (aa (2 * n + 1) + aa i) =
      (∏ k ∈ range (2 * n), (3 * k + 3) * (3 * k + 4)) * (6 * n + 3) := by
  rw [prod_range_succ]
  have hlast : (aa (2 * n + 1) - aa (2 * n)) * (aa (2 * n + 1) + aa (2 * n)) = 6 * n + 3 := by
    rw [aa_even, aa_odd]
    have : 3 * n + 2 - (3 * n + 1) = 1 := by omega
    rw [this]
    ring
  rw [hlast]
  congr 1
  rw [prod_pair, ← split_prod (fun k => (3 * k + 3) * (3 * k + 4)) n, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro m hm
  have hm' : m < n := Finset.mem_range.1 hm
  rw [aa_odd, aa_even, aa_odd]
  obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - m - 1, by omega⟩
  have e1 : 3 * (m + 1 + d) + 2 - (3 * m + 1) = 3 * d + 4 := by omega
  have e2 : 3 * (m + 1 + d) + 2 - (3 * m + 2) = 3 * d + 3 := by omega
  have e3 : m + 1 + d - 1 - m = d := by omega
  simp only [e1, e2, e3]
  ring

lemma fact1 (m : ℕ) :
    (∏ k ∈ range m, (3 * k + 1)) * (∏ k ∈ range m, (3 * k + 2) * (3 * k + 3)) =
      (3 * m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ, show 3 * (m + 1) = 3 * m + 1 + 1 + 1 from by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, ← ih]
    ring

lemma fact2 (m : ℕ) :
    (∏ k ∈ range (m + 1), (3 * k + 2)) * (∏ k ∈ range m, (3 * k + 3) * (3 * k + 4)) *
      (3 * m + 3) = (3 * m + 3).factorial := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [prod_range_succ (fun k => 3 * k + 2) (m + 1), prod_range_succ (fun k => (3 * k + 3) * (3 * k + 4)) m,
      show 3 * (m + 1) + 3 = 3 * m + 3 + 1 + 1 + 1 from by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, ← ih]
    ring

lemma fact3 (m : ℕ) :
    (∏ k ∈ range m, (3 * k + 1)) * (∏ k ∈ range m, (3 * k + 2)) * 3 ^ m * m.factorial =
      (3 * m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, prod_range_succ, show 3 * (m + 1) = 3 * m + 1 + 1 + 1 from by ring,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, ← ih, pow_succ]
    ring

theorem main (n : ℕ) :
    2 * (4 * n + 2) * (rowf (2 * n) * rowf (2 * n + 1)) =
      3 ^ (2 * n) * (6 * n + 4).factorial * (2 * n + 1).factorial := by
  set U := ∏ k ∈ range (2 * n), (3 * k + 1) with hU
  set V := ∏ k ∈ range (2 * n), (3 * k + 2) with hV
  set PA := ∏ k ∈ range (2 * n), (3 * k + 2) * (3 * k + 3) with hPA
  set PB := ∏ k ∈ range (2 * n), (3 * k + 3) * (3 * k + 4) with hPB
  have hX : rowf (2 * n) = (3 * n + 1) * PA := by
    unfold rowf
    rw [rowA, aa_even]
  have hY : rowf (2 * n + 1) = (3 * n + 2) * (PB * (6 * n + 3)) := by
    unfold rowf
    rw [rowB, aa_odd]
  have h1 : U * PA = (6 * n).factorial := by
    have := fact1 (2 * n)
    rw [show 3 * (2 * n) = 6 * n from by ring] at this
    exact this
  have h2 : V * (6 * n + 2) * PB * (6 * n + 3) = (6 * n + 3).factorial := by
    have := fact2 (2 * n)
    rw [prod_range_succ, show 3 * (2 * n) + 3 = 6 * n + 3 from by ring,
      show 3 * (2 * n) + 2 = 6 * n + 2 from by ring] at this
    exact this
  have h3 : U * V * 3 ^ (2 * n) * (2 * n).factorial = (6 * n).factorial := by
    have := fact3 (2 * n)
    rw [show 3 * (2 * n) = 6 * n from by ring] at this
    exact this
  have hUpos : 0 < U := Finset.prod_pos fun k _ => by omega
  have hVpos : 0 < V := Finset.prod_pos fun k _ => by omega
  have hTpos : 0 < U * V * (6 * n + 2) * (2 * n).factorial :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hUpos hVpos) (by omega)) (Nat.factorial_pos _)
  have f1 : (6 * n + 4).factorial = (6 * n + 4) * (6 * n + 3).factorial :=
    Nat.factorial_succ (6 * n + 3)
  have f2 : (2 * n + 1).factorial = (2 * n + 1) * (2 * n).factorial := Nat.factorial_succ (2 * n)
  apply Nat.eq_of_mul_eq_mul_right hTpos
  rw [hX, hY]
  calc 2 * (4 * n + 2) * ((3 * n + 1) * PA * ((3 * n + 2) * (PB * (6 * n + 3)))) *
        (U * V * (6 * n + 2) * (2 * n).factorial)
      = 2 * (4 * n + 2) * (3 * n + 1) * (3 * n + 2) * (2 * n).factorial * (U * PA) *
          (V * (6 * n + 2) * PB * (6 * n + 3)) := by ring
    _ = 2 * (4 * n + 2) * (3 * n + 1) * (3 * n + 2) * (2 * n).factorial * (6 * n).factorial *
          (6 * n + 3).factorial := by rw [h1, h2]
    _ = (6 * n).factorial * ((6 * n + 4) * (6 * n + 3).factorial) *
          ((2 * n + 1) * (2 * n).factorial) * (6 * n + 2) := by ring
    _ = (U * V * 3 ^ (2 * n) * (2 * n).factorial) * (6 * n + 4).factorial *
          (2 * n + 1).factorial * (6 * n + 2) := by rw [h3, f1, f2]
    _ = 3 ^ (2 * n) * (6 * n + 4).factorial * (2 * n + 1).factorial *
          (U * V * (6 * n + 2) * (2 * n).factorial) := by ring

end OMA109074


noncomputable section

namespace OMAC

structure E6 where
  re : ℚ
  im : ℚ
deriving DecidableEq

namespace E6

lemma mk_ext {x y : E6} (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x; cases y; simp_all

def zero : E6 := ⟨0, 0⟩
def one : E6 := ⟨1, 0⟩
def q : E6 := ⟨0, 1⟩
def add (x y : E6) : E6 := ⟨x.re + y.re, x.im + y.im⟩
def neg (x : E6) : E6 := ⟨-x.re, -x.im⟩
def sub (x y : E6) : E6 := ⟨x.re - y.re, x.im - y.im⟩
def mul (x y : E6) : E6 := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩
def norm (x : E6) : ℚ := x.re * x.re + x.re * x.im + x.im * x.im
def inv (x : E6) : E6 := let d := x.norm; ⟨(x.re + x.im) / d, -x.im / d⟩

instance : Zero E6 := ⟨zero⟩
instance : One E6 := ⟨one⟩
instance : Add E6 := ⟨add⟩
instance : Neg E6 := ⟨neg⟩
instance : Sub E6 := ⟨sub⟩
instance : Mul E6 := ⟨mul⟩
instance : Inv E6 := ⟨inv⟩

@[simp] lemma zero_re : (0 : E6).re = 0 := rfl
@[simp] lemma zero_im : (0 : E6).im = 0 := rfl
@[simp] lemma one_re : (1 : E6).re = 1 := rfl
@[simp] lemma one_im : (1 : E6).im = 0 := rfl
@[simp] lemma q_re : q.re = 0 := rfl
@[simp] lemma q_im : q.im = 1 := rfl
@[simp] lemma add_re (x y : E6) : (x + y).re = x.re + y.re := rfl
@[simp] lemma add_im (x y : E6) : (x + y).im = x.im + y.im := rfl
@[simp] lemma neg_re (x : E6) : (-x).re = -x.re := rfl
@[simp] lemma neg_im (x : E6) : (-x).im = -x.im := rfl
@[simp] lemma sub_re (x y : E6) : (x - y).re = x.re - y.re := rfl
@[simp] lemma sub_im (x y : E6) : (x - y).im = x.im - y.im := rfl
@[simp] lemma mul_re (x y : E6) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] lemma mul_im (x y : E6) : (x * y).im = x.re * y.im + x.im * y.re + x.im * y.im := rfl
@[simp] lemma inv_re (x : E6) : x⁻¹.re = (x.re + x.im) / x.norm := rfl
@[simp] lemma inv_im (x : E6) : x⁻¹.im = -x.im / x.norm := rfl

lemma norm_eq_zero_iff (x : E6) : x.norm = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h1 : 4 * x.norm = (2 * x.re + x.im) ^ 2 + 3 * x.im ^ 2 := by unfold norm; ring
    have h2 : (2 * x.re + x.im) ^ 2 + 3 * x.im ^ 2 = 0 := by linarith
    have him : x.im = 0 := by nlinarith
    have hre : x.re = 0 := by nlinarith
    exact mk_ext hre him
  · rintro rfl; simp [norm]

instance : CommRing E6 where
  add_assoc a b c := by apply mk_ext <;> simp <;> ring
  zero_add a := by apply mk_ext <;> simp
  add_zero a := by apply mk_ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := by apply mk_ext <;> simp
  add_comm a b := by apply mk_ext <;> simp <;> ring
  sub_eq_add_neg a b := by apply mk_ext <;> simp [sub_eq_add_neg]
  mul_assoc a b c := by apply mk_ext <;> simp <;> ring
  one_mul a := by apply mk_ext <;> simp
  mul_one a := by apply mk_ext <;> simp
  left_distrib a b c := by apply mk_ext <;> simp <;> ring
  right_distrib a b c := by apply mk_ext <;> simp <;> ring
  zero_mul a := by apply mk_ext <;> simp
  mul_zero a := by apply mk_ext <;> simp
  mul_comm a b := by apply mk_ext <;> simp <;> ring

instance : Field E6 where
  exists_pair_ne := ⟨0, 1, by intro h; have := congrArg E6.re h; norm_num at this⟩
  mul_inv_cancel a ha := by
    have hd : a.norm ≠ 0 := by intro h; exact ha ((norm_eq_zero_iff a).1 h)
    apply mk_ext
    · simp only [mul_re, inv_re, inv_im, one_re]
      unfold norm at hd ⊢
      have hd' : a.re * a.re + a.re * a.im + a.im * a.im ≠ 0 := hd
      rw [mul_div_assoc', mul_div_assoc', ← sub_div, div_eq_one_iff_eq hd']
      ring
    · simp only [mul_im, inv_re, inv_im, one_im]
      unfold norm at hd ⊢
      rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', ← add_div, ← add_div]
      have hnum : a.re * -a.im + a.im * (a.re + a.im) + a.im * -a.im = 0 := by ring
      rw [hnum, zero_div]
  inv_zero := by apply mk_ext <;> simp [norm]
  nnqsmul := _
  qsmul := _

def ofRatHom : ℚ →+* E6 where
  toFun r := ⟨r, 0⟩
  map_one' := rfl
  map_mul' _ _ := by apply mk_ext <;> simp
  map_zero' := rfl
  map_add' _ _ := by apply mk_ext <;> simp

@[simp] lemma ofRatHom_eq (r : ℚ) : ofRatHom r = (r : E6) := map_ratCast ofRatHom r
@[simp] lemma ratCast_re (r : ℚ) : (r : E6).re = r := by rw [← ofRatHom_eq]; rfl
@[simp] lemma ratCast_im (r : ℚ) : (r : E6).im = 0 := by rw [← ofRatHom_eq]; rfl

lemma ratCast_inj : Function.Injective (Rat.cast : ℚ → E6) := fun r s h => by
  have := congrArg E6.re h; simpa using this

instance : CharZero E6 where
  cast_injective m n h := by
    have hq : (((m : ℚ) : E6)) = (((n : ℚ) : E6)) := by simpa only [Rat.cast_natCast] using h
    exact Nat.cast_injective (ratCast_inj hq)

lemma q_sq : q ^ 2 = q - 1 := by apply mk_ext <;> simp [sq]
lemma q_cube : q ^ 3 = -1 := by apply mk_ext <;> simp [pow_succ]
lemma q_ne_zero : q ≠ 0 := by intro h; have := congrArg E6.im h; norm_num at this
lemma q_inv : q⁻¹ = 1 - q := by apply inv_eq_of_mul_eq_one_right; apply mk_ext <;> simp

lemma q_sq_eq_neg_inv : q ^ 2 = -q⁻¹ := by rw [q_sq, q_inv]; ring
lemma q_four : q ^ 4 = -q := by rw [show (4 : ℕ) = 3 + 1 by rfl, pow_succ, q_cube]; ring
lemma q_sq_inv : (q ^ 2)⁻¹ = -q := by
  apply inv_eq_of_mul_eq_one_right
  calc q ^ 2 * (-q) = -(q ^ 3) := by ring
    _ = 1 := by rw [q_cube]; ring

def sig (z : E6) : E6 := z - z⁻¹
def c : E6 := sig q

lemma c_eq : c = 2 * q - 1 := by unfold c sig; rw [q_inv]; ring
lemma c_sq : c ^ 2 = -3 := by
  have h2 : (2 : E6) = 1 + 1 := by ring
  have h3 : (3 : E6) = 1 + 1 + 1 := by ring
  rw [c_eq, h2, h3]; apply mk_ext <;> simp [sq] <;> ring
lemma c_ne_zero : c ≠ 0 := by
  intro h; have h3 : (3 : E6) = 1 + 1 + 1 := by ring
  have h1 := congrArg E6.re c_sq; rw [h, h3] at h1; simp at h1; norm_num at h1
lemma sig_q_sq : sig (q ^ 2) = c := by
  unfold sig; rw [q_sq_inv, q_sq, c_eq]; ring

lemma sig_one : sig 1 = 0 := by simp [sig]

end E6


section Mod1
open Finset

/- Module 3: VSASM Structural Bijection (`Mat n` ≃ `HalfMat n`) -/

def val3 (x : Fin 3) : ℤ := (x.val : ℤ) - 1

def psum {m : ℕ} (v : Fin m → Fin 3) (k : ℕ) : ℤ :=
  ∑ j : Fin m, if j.val < k then val3 (v j) else 0

lemma psum_zero {m : ℕ} (v : Fin m → Fin 3) : psum v 0 = 0 := by
  simp [psum]

lemma psum_succ {m : ℕ} (v : Fin m → Fin 3) (k : ℕ) (hk : k < m) :
    psum v (k + 1) = psum v k + val3 (v ⟨k, hk⟩) := by
  unfold psum
  have h : (∑ j : Fin m, if j.val < k + 1 then val3 (v j) else 0) =
      ∑ j : Fin m, ((if j.val < k then val3 (v j) else 0) +
        if j = ⟨k, hk⟩ then val3 (v j) else 0) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : j.val < k
    · have h2 : j.val < k + 1 := by omega
      have h3 : j ≠ ⟨k, hk⟩ := fun he => by have := congrArg Fin.val he; dsimp at this; omega
      simp [h1, h2, h3]
    · by_cases h2 : j.val = k
      · have h3 : j = ⟨k, hk⟩ := Fin.ext h2
        simp [h3]
      · have h3 : ¬ j.val < k + 1 := by omega
        have h4 : j ≠ ⟨k, hk⟩ := fun he => h2 (congrArg Fin.val he)
        simp [h1, h3, h4]
  rw [h, Finset.sum_add_distrib]
  simp

lemma psum_full {m : ℕ} (v : Fin m → Fin 3) : psum v m = ∑ j : Fin m, val3 (v j) := by
  unfold psum
  apply Finset.sum_congr rfl
  intro j _
  simp [j.isLt]

def LineOK (m : ℕ) (v : Fin m → Fin 3) : Prop :=
  psum v m = 1 ∧ ∀ k : Fin (m + 1), psum v k.val = 0 ∨ psum v k.val = 1

def LineOKSum (m : ℕ) (target : ℤ) (v : Fin m → Fin 3) : Prop :=
  psum v m = target ∧ ∀ k : Fin (m + 1), psum v k.val = 0 ∨ psum v k.val = 1

def Mat (n : ℕ) : Set (Fin (2 * n + 1) → Fin (2 * n + 1) → Fin 3) :=
  {M | (∀ i, LineOK (2 * n + 1) (M i)) ∧
       (∀ j, LineOK (2 * n + 1) (fun i => M i j)) ∧
       (∀ i j, M i j = M i (Fin.rev j))}

def HalfMat (n : ℕ) : Set (Fin (2 * n) → Fin n → Fin 3) :=
  {A | (∀ r, LineOKSum n (if r.val % 2 = 0 then 1 else 0) (A r)) ∧
       (∀ c, LineOK (2 * n) (fun r => A r c))}

lemma sym_row_sum (n : ℕ) (v : Fin (2 * n + 1) → Fin 3)
    (hsym : ∀ j, v j = v j.rev) :
    psum v (2 * n + 1) = 2 * psum v n + val3 (v ⟨n, by omega⟩) := by
  rw [psum_full]
  have hsplit : (∑ j : Fin (2 * n + 1), val3 (v j)) =
      (∑ j : Fin (2 * n + 1), if j.val < n then val3 (v j) else 0) +
      (∑ j : Fin (2 * n + 1), if j.val = n then val3 (v j) else 0) +
      (∑ j : Fin (2 * n + 1), if n < j.val then val3 (v j) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy j.val n with h | h | h
    · simp [h, ne_of_lt h, not_lt.mpr (le_of_lt h)]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt.mpr (le_of_lt h)]
  rw [hsplit]
  have hmid : (∑ j : Fin (2 * n + 1), if j.val = n then val3 (v j) else 0) =
      val3 (v ⟨n, by omega⟩) := by
    rw [Finset.sum_eq_single ⟨n, by omega⟩]
    · simp
    · intro j _ hj; simp [show j.val ≠ n from fun h => hj (Fin.ext h)]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hright : (∑ j : Fin (2 * n + 1), if n < j.val then val3 (v j) else 0) =
      ∑ j : Fin (2 * n + 1), if j.val < n then val3 (v j) else 0 := by
    refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
    simp only [Fin.revPerm_apply]
    have hv : v j = v j.rev := hsym j
    have hlt : n < j.val ↔ j.rev.val < n := by simp [Fin.val_rev]; omega
    simp [hv, hlt]
  rw [hmid, hright]
  unfold psum
  ring

lemma mat_mid_col {n : ℕ} {M : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin 3} (hM : M ∈ Mat n) :
    ∀ i : Fin (2 * n + 1),
      val3 (M i ⟨n, by omega⟩) = if i.val % 2 = 0 then 1 else -1 := by
  have hpm : ∀ i : Fin (2 * n + 1),
      val3 (M i ⟨n, by omega⟩) = 1 ∨ val3 (M i ⟨n, by omega⟩) = -1 := by
    intro i
    have h1 := sym_row_sum n (M i) (hM.2.2 i)
    have htot := (hM.1 i).1
    have hpn := (hM.1 i).2 ⟨n, by omega⟩
    dsimp only at hpn
    rcases hpn with h0 | h1' <;> omega
  have hcol := hM.2.1 ⟨n, by omega⟩
  have hind : ∀ k : ℕ, k ≤ 2 * n + 1 →
      psum (fun i => M i ⟨n, by omega⟩) k = if k % 2 = 0 then 0 else 1 := by
    intro k
    induction k with
    | zero => intro _; simp [psum_zero]
    | succ k ih =>
      intro hk
      rw [psum_succ _ k (by omega), ih (by omega)]
      have h01 := hcol.2 ⟨k + 1, by omega⟩
      dsimp only at h01
      rw [psum_succ _ k (by omega), ih (by omega)] at h01
      rcases hpm ⟨k, by omega⟩ with h | h <;> rw [h] at h01 ⊢
      · by_cases he : k % 2 = 0
        · simp [he] at h01 ⊢; omega
        · simp [he] at h01
      · by_cases he : k % 2 = 0
        · simp [he] at h01
        · simp [he] at h01 ⊢; omega
  intro i
  have h1 := hind i.val (by omega)
  have h2 := hind (i.val + 1) (by omega)
  rw [psum_succ _ i.val i.isLt, h1] at h2
  by_cases he : i.val % 2 = 0
  · have he' : (i.val + 1) % 2 ≠ 0 := by omega
    simp [he, he'] at h2 ⊢; omega
  · have he' : (i.val + 1) % 2 = 0 := by omega
    simp [he, he'] at h2 ⊢; omega

lemma mat_top_row {n : ℕ} {M : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin 3} (hM : M ∈ Mat n) :
    ∀ j : Fin (2 * n + 1), M 0 j = if j.val = n then 2 else 1 := by
  have hge : ∀ j : Fin (2 * n + 1), 0 ≤ val3 (M 0 j) := by
    intro j
    have h1 := (hM.2.1 j).2 ⟨1, by omega⟩
    dsimp only at h1
    rw [psum_succ _ 0 (by omega), psum_zero, zero_add] at h1
    change val3 (M 0 j) = 0 ∨ val3 (M 0 j) = 1 at h1
    rcases h1 with h | h <;> omega
  have hmid : val3 (M 0 ⟨n, by omega⟩) = 1 := by
    have := mat_mid_col hM 0
    simpa using this
  have hsum : ∑ j : Fin (2 * n + 1), val3 (M 0 j) = 1 := by
    rw [← psum_full]; exact (hM.1 0).1
  have hrest : ∑ j ∈ Finset.univ.erase (⟨n, by omega⟩ : Fin (2 * n + 1)), val3 (M 0 j) = 0 := by
    have := Finset.add_sum_erase Finset.univ (fun j => val3 (M 0 j))
      (Finset.mem_univ (⟨n, by omega⟩ : Fin (2 * n + 1)))
    linarith
  have hall0 : ∀ j ∈ Finset.univ.erase (⟨n, by omega⟩ : Fin (2 * n + 1)), val3 (M 0 j) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hge j)).1 hrest
  intro j
  by_cases hj : j.val = n
  · have heq : j = ⟨n, by omega⟩ := Fin.ext hj
    rw [heq, if_pos rfl]
    unfold val3 at hmid
    apply Fin.ext; omega
  · rw [if_neg hj]
    have hmem : j ∈ Finset.univ.erase (⟨n, by omega⟩ : Fin (2 * n + 1)) :=
      Finset.mem_erase.2 ⟨fun he => hj (congrArg Fin.val he), Finset.mem_univ j⟩
    have h0 := hall0 j hmem
    unfold val3 at h0
    apply Fin.ext; omega

def toHalf {n : ℕ} (M : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin 3) :
    Fin (2 * n) → Fin n → Fin 3 :=
  fun r c => M ⟨r.val + 1, by omega⟩ ⟨c.val, by omega⟩

def fromHalf {n : ℕ} (A : Fin (2 * n) → Fin n → Fin 3) :
    Fin (2 * n + 1) → Fin (2 * n + 1) → Fin 3 :=
  fun i j =>
    if hi : i.val = 0 then
      if j.val = n then 2 else 1
    else if hj1 : j.val < n then
      A ⟨i.val - 1, by omega⟩ ⟨j.val, hj1⟩
    else if hj2 : j.val = n then
      if i.val % 2 = 0 then 2 else 0
    else
      A ⟨i.val - 1, by omega⟩ ⟨2 * n - j.val, by omega⟩

lemma psum_toHalf_row {n : ℕ} (M : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin 3)
    (r : Fin (2 * n)) (k : ℕ) (hk : k ≤ n) :
    psum (toHalf M r) k = psum (M ⟨r.val + 1, by omega⟩) k := by
  induction k with
  | zero => simp [psum_zero]
  | succ k ih =>
    rw [psum_succ _ k (by omega), psum_succ _ k (by omega), ih (by omega)]
    rfl

lemma psum_toHalf_col {n : ℕ} {M : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin 3} (hM : M ∈ Mat n)
    (c : Fin n) (k : ℕ) (hk : k ≤ 2 * n) :
    psum (fun r => toHalf M r c) k = psum (fun i => M i ⟨c.val, by omega⟩) (k + 1) := by
  induction k with
  | zero =>
    rw [psum_zero, psum_succ _ 0 (by omega), psum_zero, zero_add]
    have h0 := mat_top_row hM ⟨c.val, by omega⟩
    have hc : c.val ≠ n := by omega
    rw [show (⟨0, by omega⟩ : Fin (2 * n + 1)) = 0 from rfl, h0, if_neg hc]
    rfl
  | succ k ih =>
    rw [psum_succ _ k (by omega), psum_succ _ (k + 1) (by omega), ih (by omega)]
    rfl

lemma toHalf_mem {n : ℕ} {M : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin 3} (hM : M ∈ Mat n) :
    toHalf M ∈ HalfMat n := by
  constructor
  · intro r
    constructor
    · rw [psum_toHalf_row M r n le_rfl]
      have hsym := sym_row_sum n (M ⟨r.val + 1, by omega⟩) (hM.2.2 _)
      have htot := (hM.1 ⟨r.val + 1, by omega⟩).1
      have hmid := mat_mid_col hM ⟨r.val + 1, by omega⟩
      dsimp only at hmid
      by_cases he : r.val % 2 = 0
      · have he' : (r.val + 1) % 2 ≠ 0 := by omega
        simp [he, he'] at hmid ⊢
        omega
      · have he' : (r.val + 1) % 2 = 0 := by omega
        simp [he, he'] at hmid ⊢
        omega
    · intro k
      rw [psum_toHalf_row M r k.val (by omega)]
      exact (hM.1 ⟨r.val + 1, by omega⟩).2 ⟨k.val, by omega⟩
  · intro c
    constructor
    · rw [psum_toHalf_col hM c (2 * n) le_rfl]
      exact (hM.2.1 ⟨c.val, by omega⟩).1
    · intro k
      rw [psum_toHalf_col hM c k.val (by omega)]
      exact (hM.2.1 ⟨c.val, by omega⟩).2 ⟨k.val + 1, by omega⟩

lemma toHalf_fromHalf {n : ℕ} (A : Fin (2 * n) → Fin n → Fin 3) :
    toHalf (fromHalf A) = A := by
  funext r c
  unfold toHalf fromHalf
  simp [c.isLt]

lemma fromHalf_toHalf {n : ℕ} {M : Fin (2 * n + 1) → Fin (2 * n + 1) → Fin 3} (hM : M ∈ Mat n) :
    fromHalf (toHalf M) = M := by
  funext i j
  unfold fromHalf toHalf
  by_cases hi : i.val = 0
  · simp only [hi, dite_true]
    have hi0 : i = 0 := Fin.ext hi
    rw [hi0, mat_top_row hM j]
  · simp only [hi, dite_false]
    by_cases hj1 : j.val < n
    · simp only [hj1, dite_true]
      congr 1
      exact Fin.ext (by dsimp; omega)
    · simp only [hj1, dite_false]
      by_cases hj2 : j.val = n
      · simp only [hj2, dite_true]
        have hmid := mat_mid_col hM i
        have hjeq : j = ⟨n, by omega⟩ := Fin.ext hj2
        rw [hjeq]
        unfold val3 at hmid
        by_cases he : i.val % 2 = 0
        · simp only [he, ite_true] at hmid ⊢; apply Fin.ext; omega
        · simp only [he, ite_false] at hmid ⊢; apply Fin.ext; omega
      · simp only [hj2, dite_false]
        have hrev : j.rev = ⟨2 * n - j.val, by omega⟩ := Fin.ext (by simp [Fin.val_rev])
        have hsym := (hM.2.2 i j).symm
        rw [hrev] at hsym
        rw [← hsym]
        congr 1
        exact Fin.ext (by dsimp; omega)

lemma psum_fromHalf_row_le {n : ℕ} (A : Fin (2 * n) → Fin n → Fin 3)
    (i : Fin (2 * n + 1)) (hi : i.val ≠ 0) (k : ℕ) (hk : k ≤ n) :
    psum (fromHalf A i) k = psum (A ⟨i.val - 1, by omega⟩) k := by
  induction k with
  | zero => simp [psum_zero]
  | succ k ih =>
    rw [psum_succ _ k (by omega), psum_succ _ k (by omega), ih (by omega)]
    unfold fromHalf
    have hk' : k < n := by omega
    simp [hi, hk']

lemma psum_fromHalf_row_gt {n : ℕ} (A : Fin (2 * n) → Fin n → Fin 3)
    (hA : A ∈ HalfMat n) (i : Fin (2 * n + 1)) (hi : i.val ≠ 0)
    (k : ℕ) (hk1 : n + 1 ≤ k) (hk2 : k ≤ 2 * n + 1) :
    psum (fromHalf A i) k = 1 - psum (A ⟨i.val - 1, by omega⟩) (2 * n + 1 - k) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = n + 1 + d := ⟨k - (n + 1), by omega⟩
  induction d with
  | zero =>
    rw [show n + 1 + 0 = n + 1 by omega, psum_succ _ n (by omega),
        psum_fromHalf_row_le A i hi n le_rfl,
        show 2 * n + 1 - (n + 1) = n by omega]
    have hrow := (hA.1 ⟨i.val - 1, by omega⟩).1
    have hmid : fromHalf A i ⟨n, by omega⟩ = if i.val % 2 = 0 then 2 else 0 := by
      unfold fromHalf; simp [hi]
    rw [hmid]
    by_cases he : i.val % 2 = 0
    · have he' : (i.val - 1) % 2 ≠ 0 := by omega
      simp [he, he', val3] at hrow ⊢; omega
    · have he' : (i.val - 1) % 2 = 0 := by omega
      simp [he, he', val3] at hrow ⊢; omega
  | succ d ih =>
    rw [show n + 1 + (d + 1) = (n + 1 + d) + 1 by omega,
        psum_succ _ (n + 1 + d) (by omega), ih (by omega) (by omega)]
    have hpos : 2 * n + 1 - (n + 1 + d) = (2 * n + 1 - (n + 1 + d + 1)) + 1 := by omega
    rw [hpos, psum_succ _ (2 * n + 1 - (n + 1 + d + 1)) (by omega)]
    have hentry : fromHalf A i ⟨n + 1 + d, by omega⟩ =
        A ⟨i.val - 1, by omega⟩ ⟨2 * n + 1 - (n + 1 + d + 1), by omega⟩ := by
      unfold fromHalf
      have h1 : ¬ (n + 1 + d) < n := by omega
      have h2 : n + 1 + d ≠ n := by omega
      simp only [hi, h1, h2, dite_false]
      congr 1; exact Fin.ext (by dsimp; omega)
    rw [hentry]
    ring

lemma fromHalf_mem {n : ℕ} {A : Fin (2 * n) → Fin n → Fin 3} (hA : A ∈ HalfMat n) :
    fromHalf A ∈ Mat n := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val = 0
    · have hrow : ∀ k : ℕ, k ≤ 2 * n + 1 →
          psum (fromHalf A i) k = if k ≤ n then 0 else 1 := by
        intro k
        induction k with
        | zero => intro _; simp [psum_zero]
        | succ k ih =>
          intro hk
          rw [psum_succ _ k (by omega), ih (by omega)]
          have hent : fromHalf A i ⟨k, by omega⟩ = if k = n then 2 else 1 := by
            unfold fromHalf; simp [hi]
          rw [hent]
          by_cases hkn : k < n
          · have h1 : k ≠ n := by omega
            have h2 : k ≤ n := by omega
            have h3 : k + 1 ≤ n := by omega
            simp [h1, h2, h3, val3]
          · by_cases hke : k = n
            · subst hke
              have h3 : ¬ k + 1 ≤ k := by omega
              simp [h3, val3]
            · have h2 : ¬ k ≤ n := by omega
              have h3 : ¬ k + 1 ≤ n := by omega
              simp [hke, h2, h3, val3]
      refine ⟨by rw [hrow (2 * n + 1) le_rfl]; simp [show ¬ 2 * n + 1 ≤ n by omega], fun k => ?_⟩
      rw [hrow k.val (by omega)]
      split_ifs <;> simp
    · refine ⟨?_, fun k => ?_⟩
      · rw [psum_fromHalf_row_gt A hA i hi (2 * n + 1) (by omega) le_rfl]
        simp [psum_zero]
      · by_cases hk : k.val ≤ n
        · rw [psum_fromHalf_row_le A i hi k.val hk]
          exact (hA.1 ⟨i.val - 1, by omega⟩).2 ⟨k.val, by omega⟩
        · rw [psum_fromHalf_row_gt A hA i hi k.val (by omega) (by omega)]
          have h01 := (hA.1 ⟨i.val - 1, by omega⟩).2 ⟨2 * n + 1 - k.val, by omega⟩
          dsimp only at h01
          rcases h01 with h | h <;> omega
  · intro j
    by_cases hj1 : j.val < n
    · have hcol : ∀ k : ℕ, k ≤ 2 * n →
          psum (fun i => fromHalf A i j) (k + 1) = psum (fun r => A r ⟨j.val, hj1⟩) k := by
        intro k
        induction k with
        | zero =>
          intro _
          rw [psum_zero, psum_succ _ 0 (by omega), psum_zero, zero_add]
          have h0 : fromHalf A ⟨0, by omega⟩ j = 1 := by
            unfold fromHalf; simp [show j.val ≠ n by omega]
          rw [h0]; rfl
        | succ k ih =>
          intro hk
          rw [psum_succ (fun i => fromHalf A i j) (k + 1) (by omega),
              psum_succ (fun r => A r ⟨j.val, hj1⟩) k (by omega), ih (by omega)]
          have h1 : fromHalf A ⟨k + 1, by omega⟩ j = A ⟨k, by omega⟩ ⟨j.val, hj1⟩ := by
            unfold fromHalf; simp [hj1]
          rw [h1]
      refine ⟨by rw [hcol (2 * n) le_rfl]; exact (hA.2 ⟨j.val, hj1⟩).1, fun k => ?_⟩
      rcases k with ⟨k, hk⟩
      cases k with
      | zero => left; exact psum_zero _
      | succ k => rw [hcol k (by omega)]; exact (hA.2 ⟨j.val, hj1⟩).2 ⟨k, by omega⟩
    · by_cases hj2 : j.val = n
      · have hcol : ∀ k : ℕ, k ≤ 2 * n + 1 →
            psum (fun i => fromHalf A i j) k = if k % 2 = 0 then 0 else 1 := by
          intro k
          induction k with
          | zero => intro _; simp [psum_zero]
          | succ k ih =>
            intro hk
            rw [psum_succ _ k (by omega), ih (by omega)]
            have hent : fromHalf A ⟨k, by omega⟩ j = if k % 2 = 0 then 2 else 0 := by
              unfold fromHalf
              cases k with
              | zero => simp [hj2]
              | succ k => simp [hj2]
            rw [hent]
            by_cases he : k % 2 = 0
            · have he' : (k + 1) % 2 ≠ 0 := by omega
              simp [he, he', val3]
            · have he' : (k + 1) % 2 = 0 := by omega
              simp [he, he', val3]
        refine ⟨by rw [hcol (2 * n + 1) le_rfl]; simp, fun k => ?_⟩
        rw [hcol k.val (by omega)]
        split_ifs <;> simp
      · have hj3 : 2 * n - j.val < n := by omega
        have hcol : ∀ k : ℕ, k ≤ 2 * n →
            psum (fun i => fromHalf A i j) (k + 1) = psum (fun r => A r ⟨2 * n - j.val, hj3⟩) k := by
          intro k
          induction k with
          | zero =>
            intro _
            rw [psum_zero, psum_succ _ 0 (by omega), psum_zero, zero_add]
            have h0 : fromHalf A ⟨0, by omega⟩ j = 1 := by
              unfold fromHalf; simp [hj2]
            rw [h0]; rfl
          | succ k ih =>
            intro hk
            rw [psum_succ (fun i => fromHalf A i j) (k + 1) (by omega),
                psum_succ (fun r => A r ⟨2 * n - j.val, hj3⟩) k (by omega), ih (by omega)]
            have h1 : fromHalf A ⟨k + 1, by omega⟩ j = A ⟨k, by omega⟩ ⟨2 * n - j.val, hj3⟩ := by
              unfold fromHalf; simp [hj1, hj2]
            rw [h1]
        refine ⟨by rw [hcol (2 * n) le_rfl]; exact (hA.2 ⟨2 * n - j.val, hj3⟩).1, fun k => ?_⟩
        rcases k with ⟨k, hk⟩
        cases k with
        | zero => left; exact psum_zero _
        | succ k => rw [hcol k (by omega)]; exact (hA.2 ⟨2 * n - j.val, hj3⟩).2 ⟨k, by omega⟩
  · intro i j
    unfold fromHalf
    have hrev : j.rev.val = 2 * n - j.val := by simp [Fin.val_rev]
    by_cases hi : i.val = 0
    · simp only [hi, dite_true, hrev]
      by_cases hjn : j.val = n
      · simp [hjn, show 2 * n - n = n by omega]
      · simp [hjn, show 2 * n - j.val ≠ n by omega]
    · simp only [hi, dite_false]
      by_cases hj1 : j.val < n
      · have hr1 : ¬ j.rev.val < n := by omega
        have hr2 : j.rev.val ≠ n := by omega
        simp only [hj1, hr1, hr2, dite_true, dite_false]
        congr 1; exact Fin.ext (by dsimp; omega)
      · by_cases hj2 : j.val = n
        · rw [dif_neg hj1, dif_pos hj2, dif_neg (show ¬ j.rev.val < n by omega),
              dif_pos (show j.rev.val = n by omega)]
        · have hr1 : j.rev.val < n := by omega
          simp only [hj1, hj2, hr1, dite_true, dite_false]
          congr 1; exact Fin.ext (by dsimp; omega)

theorem mat_ncard_eq_halfMat_ncard (n : ℕ) : (Mat n).ncard = (HalfMat n).ncard := by
  have himg : toHalf '' Mat n = HalfMat n := by
    ext A
    constructor
    · rintro ⟨M, hM, rfl⟩; exact toHalf_mem hM
    · intro hA; exact ⟨fromHalf A, fromHalf_mem hA, toHalf_fromHalf A⟩
  rw [← himg]
  symm
  exact Set.InjOn.ncard_image (fun M1 hM1 M2 hM2 h => by
    rw [← fromHalf_toHalf hM1, ← fromHalf_toHalf hM2, h])


end Mod1


section Mod2
open Finset Polynomial Matrix

section GeneralRing

variable {R : Type*} [CommRing R]

/- 1. Chebyshev polynomials of the second kind -/

def chebU : ℕ → Polynomial R
  | 0 => 1
  | 1 => X
  | n + 2 => X * chebU (n + 1) - chebU n

lemma chebU_zero : (chebU 0 : Polynomial R) = 1 := rfl
lemma chebU_one : (chebU 1 : Polynomial R) = X := rfl
lemma chebU_add_two (n : ℕ) : (chebU (n + 2) : Polynomial R) = X * chebU (n + 1) - chebU n := rfl

lemma eval_chebU_add_inv {K : Type*} [Field K] (z : K) (hz : z ≠ 0) :
    ∀ m : ℕ, (z - z⁻¹) * (chebU m).eval (z + z⁻¹) = z ^ (m + 1) - (z⁻¹) ^ (m + 1)
  | 0 => by simp [chebU_zero]
  | 1 => by simp only [chebU_one, eval_X]; ring
  | m + 2 => by
    rw [chebU_add_two, eval_sub, eval_mul, eval_X]
    have h1 := eval_chebU_add_inv z hz (m + 1)
    have h0 := eval_chebU_add_inv z hz m
    have hzz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
    calc (z - z⁻¹) * ((z + z⁻¹) * (chebU (m + 1)).eval (z + z⁻¹) - (chebU m).eval (z + z⁻¹))
        = (z + z⁻¹) * ((z - z⁻¹) * (chebU (m + 1)).eval (z + z⁻¹)) -
          (z - z⁻¹) * (chebU m).eval (z + z⁻¹) := by ring
      _ = (z + z⁻¹) * (z ^ (m + 2) - (z⁻¹) ^ (m + 2)) - (z ^ (m + 1) - (z⁻¹) ^ (m + 1)) := by
          rw [h1, h0]
      _ = z ^ (m + 3) - (z⁻¹) ^ (m + 3) +
          (z * z⁻¹ - 1) * (z ^ (m + 1) - (z⁻¹) ^ (m + 1)) := by ring
      _ = z ^ (m + 3) - (z⁻¹) ^ (m + 3) := by rw [hzz]; ring

lemma chebU_coeff_self_and_gt :
    ∀ m : ℕ, (chebU m : Polynomial R).coeff m = 1 ∧
      ∀ k, m < k → (chebU m : Polynomial R).coeff k = 0 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    match m with
    | 0 =>
      refine ⟨by simp [chebU_zero], fun k hk => ?_⟩
      simp [chebU_zero, Polynomial.coeff_one, show k ≠ 0 by omega]
    | 1 =>
      refine ⟨by simp [chebU_one], fun k hk => ?_⟩
      simp [chebU_one, Polynomial.coeff_X, show 1 ≠ k by omega]
    | m + 2 =>
      have h1 := ih (m + 1) (by omega)
      have h0 := ih m (by omega)
      rw [chebU_add_two]
      constructor
      · rw [coeff_sub, coeff_X_mul, h1.1, h0.2 (m + 2) (by omega), sub_zero]
      · intro k hk
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [coeff_sub, coeff_X_mul, h1.2 k' (by omega), h0.2 (k' + 1) (by omega), sub_zero]

/- 2. Upper unitriangular determinant preservation -/

lemma det_mul_upperUnitriangular {m : ℕ} (M U : Matrix (Fin m) (Fin m) R)
    (hU_tri : ∀ i j : Fin m, j.val < i.val → U i j = 0)
    (hU_diag : ∀ i : Fin m, U i i = 1) :
    (M * U).det = M.det := by
  rw [Matrix.det_mul]
  have htri : U.BlockTriangular id := fun i j hij => hU_tri i j hij
  rw [Matrix.det_of_isUpperTriangular htri]
  have hprod : ∏ i : Fin m, U i i = 1 := Finset.prod_eq_one (fun i _ => hU_diag i)
  rw [hprod, mul_one]

/- 3. Vandermonde = Chebyshev determinant -/

def Vmat (m : ℕ) (Z : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => Z i ^ j.val

def chebVmat (m : ℕ) (Z : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => (chebU j.val).eval (Z i)

lemma det_chebVmat (m : ℕ) (Z : Fin m → R) :
    (chebVmat m Z).det = (Vmat m Z).det := by
  let U : Matrix (Fin m) (Fin m) R := Matrix.of fun k j => (chebU j.val).coeff k.val
  have hmul : chebVmat m Z = Vmat m Z * U := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [chebVmat, Vmat, U, Matrix.of_apply]
    have hdeg : (chebU j.val : Polynomial R).natDegree < m := by
      have hle : (chebU j.val : Polynomial R).natDegree ≤ j.val :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun k hk =>
          (chebU_coeff_self_and_gt j.val).2 k hk
      omega
    rw [Polynomial.eval_eq_sum_range' hdeg,
        Fin.sum_univ_eq_sum_range (fun k => Z i ^ k * (chebU j.val).coeff k)]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hmul]
  exact det_mul_upperUnitriangular (Vmat m Z) U
    (fun k j hjk => (chebU_coeff_self_and_gt j.val).2 k.val hjk)
    (fun j => (chebU_coeff_self_and_gt j.val).1)

lemma det_Vmat_eq_prod (m : ℕ) (Z : Fin m → R) :
    (Vmat m Z).det = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (Z j - Z i) := by
  have hv : Vmat m Z = Matrix.vandermonde Z := by
    ext i j; simp [Vmat, Matrix.vandermonde]
  rw [hv, Matrix.det_vandermonde]

/- 4. `Dmat` = Chebyshev `U_{s + s/2}` determinant -/

def Tpoly : Polynomial R := X ^ 3 - C 3 * X

def Pbasis (s : ℕ) : Polynomial R := Tpoly ^ (s / 2) * X ^ (s % 2)

lemma Tpoly_mul_Pbasis (s : ℕ) : (Tpoly : Polynomial R) * Pbasis s = Pbasis (s + 2) := by
  unfold Pbasis
  have h1 : (s + 2) / 2 = s / 2 + 1 := by omega
  have h2 : (s + 2) % 2 = s % 2 := by omega
  rw [h1, h2, pow_succ]
  ring

lemma chebU_2 : (chebU 2 : Polynomial R) = X ^ 2 - 1 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, chebU_add_two, chebU_one, chebU_zero]; ring

lemma chebU_3_explicit : (chebU 3 : Polynomial R) = X ^ 3 - 2 * X := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, chebU_add_two, chebU_2, chebU_one]; ring

lemma chebU_4_explicit : (chebU 4 : Polynomial R) = X ^ 4 - 3 * X ^ 2 + 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, chebU_add_two, chebU_3_explicit, chebU_2]; ring

lemma chebU_5_explicit : (chebU 5 : Polynomial R) = X ^ 5 - 4 * X ^ 3 + 3 * X := by
  rw [show (5 : ℕ) = 3 + 2 from rfl, chebU_add_two, chebU_4_explicit, chebU_3_explicit]; ring

lemma chebU_6_explicit : (chebU 6 : Polynomial R) = X ^ 6 - 5 * X ^ 4 + 6 * X ^ 2 - 1 := by
  rw [show (6 : ℕ) = 4 + 2 from rfl, chebU_add_two, chebU_5_explicit, chebU_4_explicit]; ring

lemma chebU_7_explicit : (chebU 7 : Polynomial R) = X ^ 7 - 6 * X ^ 5 + 10 * X ^ 3 - 4 * X := by
  rw [show (7 : ℕ) = 5 + 2 from rfl, chebU_add_two, chebU_6_explicit, chebU_5_explicit]; ring

lemma C_three : (C (3 : R) : Polynomial R) = 3 := by
  have h3 : (3 : R) = 1 + 1 + 1 := by ring
  rw [h3, map_add, map_add, map_one]
  ring

lemma chebU_3 : (chebU 3 : Polynomial R) = Tpoly * chebU 0 + chebU 1 := by
  rw [chebU_3_explicit, chebU_zero, chebU_one, Tpoly, C_three]; ring

lemma chebU_4 : (chebU 4 : Polynomial R) = Tpoly * chebU 1 + chebU 0 := by
  rw [chebU_4_explicit, chebU_zero, chebU_one, Tpoly, C_three]; ring

lemma chebU_triple : ∀ k : ℕ,
    (chebU (k + 6) : Polynomial R) + chebU k = Tpoly * chebU (k + 3) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    match k with
    | 0 =>
      rw [show 0 + 6 = 6 from rfl, show 0 + 3 = 3 from rfl,
          chebU_6_explicit, chebU_zero, chebU_3_explicit, Tpoly, C_three]
      ring
    | 1 =>
      rw [show 1 + 6 = 7 from rfl, show 1 + 3 = 4 from rfl,
          chebU_7_explicit, chebU_one, chebU_4_explicit, Tpoly, C_three]
      ring
    | k + 2 =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have e1 : (chebU (k + 8) : Polynomial R) = X * chebU (k + 7) - chebU (k + 6) :=
        chebU_add_two (k + 6)
      have e2 : (chebU (k + 2) : Polynomial R) = X * chebU (k + 1) - chebU k :=
        chebU_add_two k
      have e3 : (chebU (k + 5) : Polynomial R) = X * chebU (k + 4) - chebU (k + 3) :=
        chebU_add_two (k + 3)
      rw [e1, e2, e3]
      calc (X * chebU (k + 7) - chebU (k + 6)) + (X * chebU (k + 1) - chebU k)
          = X * (chebU (k + 7) + chebU (k + 1)) - (chebU (k + 6) + chebU k) := by ring
        _ = X * (Tpoly * chebU (k + 4)) - Tpoly * chebU (k + 3) := by rw [h1, h0]
        _ = Tpoly * (X * chebU (k + 4) - chebU (k + 3)) := by ring

lemma chebU_a_expansion : ∀ s : ℕ,
    ∃ coeff : ℕ → R, coeff s = 1 ∧
      (chebU (s + s / 2) : Polynomial R) = ∑ k ∈ range (s + 1), C (coeff k) * Pbasis k := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    match s with
    | 0 =>
      refine ⟨fun _ => 1, rfl, ?_⟩
      simp [chebU_zero, Pbasis]
    | 1 =>
      refine ⟨fun k => if k = 1 then 1 else 0, by simp, ?_⟩
      simp [chebU_one, Pbasis]
    | 2 =>
      refine ⟨fun k => if k = 2 ∨ k = 1 then 1 else 0, by simp, ?_⟩
      rw [show 2 + 2 / 2 = 3 from rfl, chebU_3, chebU_zero, chebU_one]
      simp [Finset.sum_range_succ, Pbasis]
      ring
    | 3 =>
      refine ⟨fun k => if k = 3 ∨ k = 0 then 1 else 0, by simp, ?_⟩
      rw [show 3 + 3 / 2 = 4 from rfl, chebU_4, chebU_zero, chebU_one]
      simp [Finset.sum_range_succ, Pbasis]
      ring
    | s + 4 =>
      obtain ⟨c2, hc2_top, hc2⟩ := ih (s + 2) (by omega)
      obtain ⟨c0, hc0_top, hc0⟩ := ih s (by omega)
      let c : ℕ → R := fun k =>
        (if 2 ≤ k then c2 (k - 2) else 0) - (if k ≤ s then c0 k else 0)
      refine ⟨c, ?_, ?_⟩
      · simp [c, hc2_top, show ¬ (s + 4 ≤ s) by omega]
      · have htrip := chebU_triple (R := R) (s + s / 2)
        have e1 : (s + 4) + (s + 4) / 2 = (s + s / 2) + 6 := by omega
        have e2 : (s + 2) + (s + 2) / 2 = (s + s / 2) + 3 := by omega
        rw [e1]
        have hsub : (chebU (s + s / 2 + 6) : Polynomial R) =
            Tpoly * chebU (s + s / 2 + 3) - chebU (s + s / 2) := eq_sub_of_add_eq htrip
        rw [hsub, ← e2, hc2, hc0, Finset.mul_sum]
        have hshift : (∑ k ∈ range (s + 3), Tpoly * (C (c2 k) * Pbasis k)) =
            ∑ k ∈ range (s + 5), C (if 2 ≤ k then c2 (k - 2) else 0) * Pbasis k := by
          have h1 : ∀ k, Tpoly * (C (c2 k) * Pbasis k) = C (c2 k) * Pbasis (k + 2) := by
            intro k; rw [← Tpoly_mul_Pbasis]; ring
          simp_rw [h1]
          conv_rhs => rw [show s + 5 = 2 + (s + 3) by omega, Finset.sum_range_add]
          have h00 : (∑ x ∈ range 2, C (if 2 ≤ x then c2 (x - 2) else 0) * Pbasis x) = 0 := by
            simp [Finset.sum_range_succ]
          rw [h00, zero_add]
          apply Finset.sum_congr rfl
          intro k _
          simp [add_comm 2 k]
        have hpad : (∑ k ∈ range (s + 1), C (c0 k) * Pbasis k) =
            ∑ k ∈ range (s + 5), C (if k ≤ s then c0 k else 0) * Pbasis k := by
          conv_rhs => rw [show s + 5 = (s + 1) + 4 by omega, Finset.sum_range_add]
          have hzero : (∑ x ∈ range 4, C (if s + 1 + x ≤ s then c0 (s + 1 + x) else 0) * Pbasis (s + 1 + x)) = 0 := by
            apply Finset.sum_eq_zero
            intro x _
            simp [show ¬ (s + 1 + x ≤ s) by omega]
          rw [hzero, add_zero]
          apply Finset.sum_congr rfl
          intro k hk
          simp [show k ≤ s by have := Finset.mem_range.1 hk; omega]
        rw [hshift, hpad, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        simp only [c, map_sub, sub_mul]

def Dmat (n : ℕ) (Z : Fin (2 * n) → R) : Matrix (Fin (2 * n)) (Fin (2 * n)) R :=
  Matrix.of fun r s => (Z r ^ 3 - 3 * Z r) ^ (s.val / 2) * Z r ^ (s.val % 2)

def chebAmat (n : ℕ) (Z : Fin (2 * n) → R) : Matrix (Fin (2 * n)) (Fin (2 * n)) R :=
  Matrix.of fun r s => (chebU (s.val + s.val / 2)).eval (Z r)

lemma eval_Pbasis (s : ℕ) (z : R) :
    (Pbasis s : Polynomial R).eval z = (z ^ 3 - 3 * z) ^ (s / 2) * z ^ (s % 2) := by
  simp [Pbasis, Tpoly]

lemma det_chebAmat (n : ℕ) (Z : Fin (2 * n) → R) :
    (chebAmat n Z).det = (Dmat n Z).det := by
  choose coeff htop hexp using (chebU_a_expansion (R := R))
  let U : Matrix (Fin (2 * n)) (Fin (2 * n)) R :=
    Matrix.of fun k s => if k.val ≤ s.val then coeff s.val k.val else 0
  have hmul : chebAmat n Z = Dmat n Z * U := by
    ext r s
    rw [Matrix.mul_apply]
    simp only [chebAmat, Dmat, U, Matrix.of_apply]
    rw [hexp s.val, Polynomial.eval_finsetSum]
    simp_rw [Polynomial.eval_mul, Polynomial.eval_C, eval_Pbasis]
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      ((Z r ^ 3 - 3 * Z r) ^ (k / 2) * Z r ^ (k % 2)) *
        if k ≤ s.val then coeff s.val k else 0)]
    symm
    rw [← Finset.sum_subset (Finset.range_mono (show s.val + 1 ≤ 2 * n by omega))]
    · apply Finset.sum_congr rfl
      intro k hk
      have hks : k ≤ s.val := by have := Finset.mem_range.1 hk; omega
      simp [hks, mul_comm]
    · intro k _ hk
      have hks : ¬ k ≤ s.val := by
        rw [Finset.mem_range] at hk; omega
      simp [hks]
  rw [hmul]
  exact det_mul_upperUnitriangular (Dmat n Z) U
    (fun k s hsk => by simp [U, show ¬ k ≤ s from not_le.mpr hsk])
    (fun s => by simp [U, htop s.val])

/- 5. `Dmat` Reduction Lemma when `Z 0 ^ 3 - 3 * Z 0 = Z 1 ^ 3 - 3 * Z 1` -/

lemma det_Dmat_reduction (n : ℕ) (Z : Fin (2 * (n + 1)) → R)
    (hT : Z ⟨0, by omega⟩ ^ 3 - 3 * Z ⟨0, by omega⟩ =
          Z ⟨1, by omega⟩ ^ 3 - 3 * Z ⟨1, by omega⟩) :
    (Dmat (n + 1) Z).det =
      (Z ⟨1, by omega⟩ - Z ⟨0, by omega⟩) *
      (∏ r : Fin (2 * n),
        ((Z ⟨r.val + 2, by omega⟩ ^ 3 - 3 * Z ⟨r.val + 2, by omega⟩) -
         (Z ⟨0, by omega⟩ ^ 3 - 3 * Z ⟨0, by omega⟩))) *
      (Dmat n (fun r => Z ⟨r.val + 2, by omega⟩)).det := by
  let t0 : R := Z ⟨0, by omega⟩ ^ 3 - 3 * Z ⟨0, by omega⟩
  let U : Matrix (Fin (2 * (n + 1))) (Fin (2 * (n + 1))) R :=
    Matrix.of fun k s => if k.val = s.val then 1 else if k.val + 2 = s.val then -t0 else 0
  have hU_det : (Dmat (n + 1) Z * U).det = (Dmat (n + 1) Z).det :=
    det_mul_upperUnitriangular (Dmat (n + 1) Z) U
      (fun k s hsk => by simp [U, show k.val ≠ s.val by omega, show k.val + 2 ≠ s.val by omega])
      (fun s => by simp [U])
  rw [← hU_det]
  let e : Fin 2 ⊕ Fin (2 * n) ≃ Fin (2 * (n + 1)) :=
    { toFun := Sum.elim (fun i => ⟨i.val, by omega⟩) (fun i => ⟨i.val + 2, by omega⟩)
      invFun := fun i => if h : i.val < 2 then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - 2, by omega⟩
      left_inv := fun x => by
        cases x with
        | inl i => simp [i.isLt]
        | inr i =>
          have h1 : ¬ (i.val + 2 < 2) := by omega
          simp [h1]
      right_inv := fun i => by
        by_cases h : i.val < 2
        · simp [h]
        · simp only [h, dite_false, Sum.elim_inr]
          exact Fin.ext (by dsimp; omega) }
  have hre : (Dmat (n + 1) Z * U).det = ((Dmat (n + 1) Z * U).submatrix e e).det :=
    (Matrix.det_submatrix_equiv_self e (Dmat (n + 1) Z * U)).symm
  rw [hre]
  have hM : ∀ r s : Fin (2 * (n + 1)), (Dmat (n + 1) Z * U) r s =
      if h : s.val < 2 then
        if s.val = 0 then 1 else Z r
      else
        ((Z r ^ 3 - 3 * Z r) - t0) *
          (Z r ^ 3 - 3 * Z r) ^ ((s.val - 2) / 2) * Z r ^ ((s.val - 2) % 2) := by
    intro r s
    rw [Matrix.mul_apply]
    by_cases hs : s.val < 2
    · rw [dif_pos hs]
      rw [Finset.sum_eq_single s]
      · simp only [U, Dmat, Matrix.of_apply, ite_true, mul_one]
        by_cases hs0 : s.val = 0
        · simp [hs0]
        · have hs1 : s.val = 1 := by omega
          simp [hs1]
      · intro k _ hks
        have hk1 : k.val ≠ s.val := fun h => hks (Fin.ext h)
        have hk2 : k.val + 2 ≠ s.val := by omega
        simp [U, hk1, hk2]
      · intro h; exact absurd (Finset.mem_univ s) h
    · rw [dif_neg hs]
      let s2 : Fin (2 * (n + 1)) := ⟨s.val - 2, by omega⟩
      have hs2_ne : s ≠ s2 := fun h => by have := congrArg Fin.val h; dsimp [s2] at this; omega
      have hsum2 : (∑ k : Fin (2 * (n + 1)), Dmat (n + 1) Z r k * U k s) =
          Dmat (n + 1) Z r s * U s s + Dmat (n + 1) Z r s2 * U s2 s := by
        rw [← Finset.sum_subset (Finset.subset_univ {s, s2})]
        · rw [Finset.sum_pair hs2_ne]
        · intro k _ hk
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          have h1 : k.val ≠ s.val := fun h => hk.1 (Fin.ext h)
          have h2 : k.val + 2 ≠ s.val := fun h => hk.2 (Fin.ext (by dsimp [s2]; omega))
          simp [U, h1, h2]
      rw [hsum2]
      have he1 : s.val / 2 = (s.val - 2) / 2 + 1 := by omega
      have he2 : s.val % 2 = (s.val - 2) % 2 := by omega
      simp only [U, Dmat, Matrix.of_apply, s2, ite_true, mul_one,
        show s.val - 2 ≠ s.val by omega, show s.val - 2 + 2 = s.val by omega, ite_false,
        he1, he2, pow_succ]
      ring
  let A : Matrix (Fin 2) (Fin 2) R := Matrix.of fun i j => if j.val = 0 then 1 else Z ⟨i.val, by omega⟩
  let C : Matrix (Fin (2 * n)) (Fin 2) R := Matrix.of fun i j => if j.val = 0 then 1 else Z ⟨i.val + 2, by omega⟩
  let D : Matrix (Fin (2 * n)) (Fin (2 * n)) R :=
    Matrix.of fun r s => ((Z ⟨r.val + 2, by omega⟩ ^ 3 - 3 * Z ⟨r.val + 2, by omega⟩) - t0) *
      Dmat n (fun i => Z ⟨i.val + 2, by omega⟩) r s
  have hblk : (Dmat (n + 1) Z * U).submatrix e e = Matrix.fromBlocks A 0 C D := by
    ext x y
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁]
        simp only [e, Equiv.coe_fn_mk, Sum.elim_inl, hM, j.isLt, dite_true, A, Matrix.of_apply]
      | inr j =>
        rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
        simp only [e, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr, hM,
          show ¬ (j.val + 2 < 2) by omega, dite_false]
        have hi : i.val = 0 ∨ i.val = 1 := by omega
        rcases hi with h0 | h1
        · have heq : (⟨i.val, by omega⟩ : Fin (2 * (n + 1))) = ⟨0, by omega⟩ := Fin.ext h0
          rw [heq]; simp [t0]
        · have heq : (⟨i.val, by omega⟩ : Fin (2 * (n + 1))) = ⟨1, by omega⟩ := Fin.ext h1
          rw [heq, ← hT]; simp [t0]
    | inr i =>
      cases y with
      | inl j =>
        rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁]
        simp only [e, Equiv.coe_fn_mk, Sum.elim_inl, Sum.elim_inr, hM, j.isLt, dite_true, C,
          Matrix.of_apply]
      | inr j =>
        rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂]
        simp only [e, Equiv.coe_fn_mk, Sum.elim_inr]
        rw [hM, dif_neg (show ¬ (j.val + 2 < 2) by omega)]
        simp only [D, Dmat, Matrix.of_apply, Nat.add_sub_cancel]
        ring
  rw [hblk, Matrix.det_fromBlocks_zero₁₂]
  have hdetA : A.det = Z ⟨1, by omega⟩ - Z ⟨0, by omega⟩ := by
    rw [Matrix.det_fin_two]
    simp [A]
  have hdetD : D.det = (∏ r : Fin (2 * n),
      ((Z ⟨r.val + 2, by omega⟩ ^ 3 - 3 * Z ⟨r.val + 2, by omega⟩) - t0)) *
      (Dmat n (fun i => Z ⟨i.val + 2, by omega⟩)).det := by
    have hDmul : D = Matrix.diagonal (fun r : Fin (2 * n) =>
        (Z ⟨r.val + 2, by omega⟩ ^ 3 - 3 * Z ⟨r.val + 2, by omega⟩) - t0) *
        Dmat n (fun i => Z ⟨i.val + 2, by omega⟩) := by
      ext r s
      simp [D, Matrix.diagonal_mul]
    rw [hDmul, Matrix.det_mul, Matrix.det_diagonal]
  rw [hdetA, hdetD]
  ring

end GeneralRing

/- 6. Symplectic Vandermonde Specialization -/

section FieldSpec

variable {K : Type*} [Field K]

def altNat (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∏ j ∈ range (2 * n), a j * ∏ i ∈ range j, (a j - a i) * (a j + a i)

def Qalt (n : ℕ) (a : ℕ → ℕ) : Polynomial K :=
  (∏ j ∈ range (2 * n), ∑ l ∈ range (2 * a j), X ^ l) *
  (∏ j ∈ range (2 * n), ∏ i ∈ range j,
    (∑ l ∈ range (a j - a i), X ^ l) * (∑ l ∈ range (a j + a i), X ^ l))

def Ealt (n : ℕ) (a : ℕ → ℕ) : ℕ :=
  ∑ j ∈ range (2 * n), (j + 1) * a j

lemma eval_geom_sum_one (m : ℕ) :
    (∑ l ∈ range m, (X : Polynomial K) ^ l).eval 1 = (m : K) := by
  simp [Polynomial.eval_finsetSum]

lemma Qalt_eval_one (n : ℕ) (a : ℕ → ℕ) :
    (Qalt (K := K) n a).eval 1 = (2 : K) ^ (2 * n) * (altNat n a : K) := by
  unfold Qalt altNat
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, eval_geom_sum_one, Nat.cast_prod,
    Nat.cast_mul]
  rw [← Finset.prod_mul_distrib]
  have h2 : (2 : K) ^ (2 * n) = ∏ _j ∈ range (2 * n), (2 : K) := by simp
  rw [h2, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  ring

lemma geom_sum_mul_sub_one (s : K) (m : ℕ) :
    (s - 1) * ∑ l ∈ range m, s ^ l = s ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

lemma det_symp_vandermonde (n : ℕ) (a : ℕ → ℕ) (ha : ∀ i j, i < j → a i < a j)
    (s : K) (hs : s ≠ 0) :
    s ^ (Ealt n a) *
      (Matrix.of fun (i j : Fin (2 * n)) =>
        (s ^ (i.val + 1)) ^ (a j.val) - ((s ^ (i.val + 1))⁻¹) ^ (a j.val)).det =
    (s - 1) ^ (4 * n ^ 2) * (Qalt (K := K) n a).eval s := by
  let M : Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
    Matrix.of fun i j => (s ^ (i.val + 1)) ^ (a j.val) - ((s ^ (i.val + 1))⁻¹) ^ (a j.val)
  have htr : M.det = Mᵀ.det := (Matrix.det_transpose M).symm
  let w : Fin (2 * n) → K := fun j => s ^ (a j.val)
  have hw_ne : ∀ j, w j ≠ 0 := fun j => pow_ne_zero _ hs
  have hMtr : Mᵀ = Matrix.diagonal (fun j => w j - (w j)⁻¹) *
      chebVmat (2 * n) (fun j => w j + (w j)⁻¹) := by
    ext j i
    rw [Matrix.transpose_apply, Matrix.diagonal_mul]
    simp only [M, chebVmat, Matrix.of_apply]
    rw [eval_chebU_add_inv (w j) (hw_ne j) i.val]
    simp only [w, ← pow_mul, inv_pow]
    rw [mul_comm (i.val + 1) (a j.val)]
  change s ^ (Ealt n a) * M.det = _
  rw [htr, hMtr, Matrix.det_mul, Matrix.det_diagonal, det_chebVmat, det_Vmat_eq_prod]
  have hprod1 : (∏ j : Fin (2 * n), (w j - (w j)⁻¹)) =
      ∏ j ∈ range (2 * n), (s ^ a j - (s ^ a j)⁻¹) := by
    dsimp only [w]
    exact Fin.prod_univ_eq_prod_range (fun j => s ^ a j - (s ^ a j)⁻¹) (2 * n)
  have hprod2 : (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((w j + (w j)⁻¹) - (w i + (w i)⁻¹))) =
      ∏ j ∈ range (2 * n), ∏ i ∈ range j, ((s ^ a j + (s ^ a j)⁻¹) - (s ^ a i + (s ^ a i)⁻¹)) := by
    have hswap : (∏ i : Fin (2 * n), ∏ j ∈ Finset.Ioi i, ((w j + (w j)⁻¹) - (w i + (w i)⁻¹))) =
        ∏ j : Fin (2 * n), ∏ i ∈ Finset.Iio j, ((w j + (w j)⁻¹) - (w i + (w i)⁻¹)) := by
      rw [Finset.prod_sigma', Finset.prod_sigma']
      refine Finset.prod_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, Finset.mem_Iio, true_and] at hp ⊢
        exact hp
      · intro p1 _ p2 _ h
        cases p1; cases p2
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
      · intro p hp
        refine ⟨⟨p.2, p.1⟩, ?_, rfl⟩
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, Finset.mem_Iio, true_and] at hp ⊢
        exact hp
      · intro p _; rfl
    rw [hswap]
    have hinner : ∀ j : Fin (2 * n),
        (∏ i ∈ Finset.Iio j, ((w j + (w j)⁻¹) - (w i + (w i)⁻¹))) =
        ∏ i ∈ range j.val, ((s ^ a j.val + (s ^ a j.val)⁻¹) - (s ^ a i + (s ^ a i)⁻¹)) := by
      intro j
      refine Finset.prod_bij (fun (i : Fin (2 * n)) _ => i.val) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_Iio, Fin.lt_def] at hi
        exact Finset.mem_range.2 hi
      · intro i1 _ i2 _ h; exact Fin.ext h
      · intro i hi
        have hi' : i < j.val := Finset.mem_range.1 hi
        exact ⟨⟨i, by omega⟩, Finset.mem_Iio.2 hi', rfl⟩
      · intro i _; rfl
    simp_rw [hinner]
    exact Fin.prod_univ_eq_prod_range
      (fun j => ∏ i ∈ range j, ((s ^ a j + (s ^ a j)⁻¹) - (s ^ a i + (s ^ a i)⁻¹))) (2 * n)
  rw [hprod1, hprod2]
  have hE : s ^ (Ealt n a) =
      (∏ j ∈ range (2 * n), s ^ a j) * (∏ j ∈ range (2 * n), ∏ _i ∈ range j, s ^ a j) := by
    unfold Ealt
    rw [Finset.prod_pow_eq_pow_sum]
    simp_rw [Finset.prod_const, Finset.card_range, ← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum, ← pow_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h4n2 : (s - 1) ^ (4 * n ^ 2) =
      (∏ _j ∈ range (2 * n), (s - 1)) * (∏ j ∈ range (2 * n), ∏ _i ∈ range j, (s - 1) ^ 2) := by
    simp only [Finset.prod_const, Finset.card_range, ← pow_mul, Finset.prod_pow_eq_pow_sum,
      ← pow_add]
    congr 1
    have hsum : ∀ m : ℕ, m + ∑ j ∈ range m, 2 * j = m ^ 2 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ]
        linarith [show (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 by ring]
    have h2n := hsum (2 * n)
    linarith [show (2 * n) ^ 2 = 4 * n ^ 2 by ring]
  rw [hE, h4n2]
  unfold Qalt
  simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_finsetSum,
    Polynomial.eval_pow, Polynomial.eval_X]
  calc (∏ j ∈ range (2 * n), s ^ a j) * (∏ j ∈ range (2 * n), ∏ _i ∈ range j, s ^ a j) *
        ((∏ j ∈ range (2 * n), (s ^ a j - (s ^ a j)⁻¹)) *
         (∏ j ∈ range (2 * n), ∏ i ∈ range j, ((s ^ a j + (s ^ a j)⁻¹) - (s ^ a i + (s ^ a i)⁻¹))))
      = (∏ j ∈ range (2 * n), s ^ a j * (s ^ a j - (s ^ a j)⁻¹)) *
        (∏ j ∈ range (2 * n), ∏ i ∈ range j,
          s ^ a j * ((s ^ a j + (s ^ a j)⁻¹) - (s ^ a i + (s ^ a i)⁻¹))) := by
        simp only [Finset.prod_mul_distrib]
        ring
    _ = (∏ j ∈ range (2 * n), (s - 1) * ∑ l ∈ range (2 * a j), s ^ l) *
        (∏ j ∈ range (2 * n), ∏ i ∈ range j,
          (s - 1) ^ 2 * ((∑ l ∈ range (a j - a i), s ^ l) * (∑ l ∈ range (a j + a i), s ^ l))) := by
        congr 1
        · apply Finset.prod_congr rfl
          intro j _
          rw [geom_sum_mul_sub_one, mul_sub, mul_inv_cancel₀ (pow_ne_zero _ hs), ← pow_add,
            two_mul]
        · apply Finset.prod_congr rfl
          intro j _
          apply Finset.prod_congr rfl
          intro i hi
          have hij : a i < a j := ha i j (Finset.mem_range.1 hi)
          have hsub : (s - 1) ^ 2 * ((∑ l ∈ range (a j - a i), s ^ l) * (∑ l ∈ range (a j + a i), s ^ l)) =
              (s ^ (a j - a i) - 1) * (s ^ (a j + a i) - 1) := by
            calc (s - 1) ^ 2 * ((∑ l ∈ range (a j - a i), s ^ l) * (∑ l ∈ range (a j + a i), s ^ l))
                = ((s - 1) * ∑ l ∈ range (a j - a i), s ^ l) *
                  ((s - 1) * ∑ l ∈ range (a j + a i), s ^ l) := by ring
              _ = _ := by rw [geom_sum_mul_sub_one, geom_sum_mul_sub_one]
          rw [hsub]
          have hsaj : s ^ a j ≠ 0 := pow_ne_zero _ hs
          have hsai : s ^ a i ≠ 0 := pow_ne_zero _ hs
          have h1 : s ^ a j * (s ^ a i)⁻¹ = s ^ (a j - a i) := by
            rw [mul_inv_eq_iff_eq_mul₀ hsai, ← pow_add, Nat.sub_add_cancel (le_of_lt hij)]
          have h2 : s ^ a j * s ^ a i = s ^ (a j + a i) := (pow_add s (a j) (a i)).symm
          have h3 : s ^ a j * s ^ a j = s ^ (a j - a i) * s ^ (a j + a i) := by
            rw [← pow_add, ← pow_add]; congr 1; omega
          have h4 : s ^ a j * (s ^ a j)⁻¹ = 1 := mul_inv_cancel₀ hsaj
          calc s ^ a j * (s ^ a j + (s ^ a j)⁻¹ - (s ^ a i + (s ^ a i)⁻¹))
              = s ^ a j * s ^ a j + s ^ a j * (s ^ a j)⁻¹ - s ^ a j * s ^ a i - s ^ a j * (s ^ a i)⁻¹ := by ring
            _ = s ^ (a j - a i) * s ^ (a j + a i) + 1 - s ^ (a j + a i) - s ^ (a j - a i) := by
                rw [h3, h4, h2, h1]
            _ = (s ^ (a j - a i) - 1) * (s ^ (a j + a i) - 1) := by ring
    _ = _ := by
        simp only [Finset.prod_mul_distrib]
        ring

lemma det_Vmat_symp_spec (n : ℕ) (s : K) (hs : s ≠ 0) :
    let w : Fin (2 * n) → K := fun i => s ^ (i.val + 1)
    let Z : Fin (2 * n) → K := fun i => w i + (w i)⁻¹
    s ^ (Ealt n (fun j => j + 1)) * (∏ i : Fin (2 * n), (w i - (w i)⁻¹)) * (Vmat (2 * n) Z).det =
      (s - 1) ^ (4 * n ^ 2) * (Qalt (K := K) n (fun j => j + 1)).eval s := by
  intro w Z
  rw [← det_chebVmat, mul_assoc]
  have hmul : (∏ i : Fin (2 * n), (w i - (w i)⁻¹)) * (chebVmat (2 * n) Z).det =
      (Matrix.of fun (i j : Fin (2 * n)) =>
        (s ^ (i.val + 1)) ^ (j.val + 1) - ((s ^ (i.val + 1))⁻¹) ^ (j.val + 1)).det := by
    rw [← Matrix.det_diagonal, ← Matrix.det_mul]
    congr 1
    ext i j
    simp only [Matrix.diagonal_mul, chebVmat, Matrix.of_apply, Z]
    exact eval_chebU_add_inv (w i) (pow_ne_zero _ hs) j.val
  rw [hmul]
  exact det_symp_vandermonde n (fun j => j + 1) (fun i j h => by omega) s hs

lemma det_Dmat_symp_spec (n : ℕ) (s : K) (hs : s ≠ 0) :
    let w : Fin (2 * n) → K := fun i => s ^ (i.val + 1)
    let Z : Fin (2 * n) → K := fun i => w i + (w i)⁻¹
    s ^ (Ealt n (fun j => j + 1 + j / 2)) * (∏ i : Fin (2 * n), (w i - (w i)⁻¹)) * (Dmat n Z).det =
      (s - 1) ^ (4 * n ^ 2) * (Qalt (K := K) n (fun j => j + 1 + j / 2)).eval s := by
  intro w Z
  rw [← det_chebAmat, mul_assoc]
  have hmul : (∏ i : Fin (2 * n), (w i - (w i)⁻¹)) * (chebAmat n Z).det =
      (Matrix.of fun (i j : Fin (2 * n)) =>
        (s ^ (i.val + 1)) ^ (j.val + 1 + j.val / 2) -
        ((s ^ (i.val + 1))⁻¹) ^ (j.val + 1 + j.val / 2)).det := by
    rw [← Matrix.det_diagonal, ← Matrix.det_mul]
    congr 1
    ext i j
    simp only [Matrix.diagonal_mul, chebAmat, Matrix.of_apply, Z]
    have he := eval_chebU_add_inv (w i) (pow_ne_zero _ hs) (j.val + j.val / 2)
    have hidx : j.val + j.val / 2 + 1 = j.val + 1 + j.val / 2 := by omega
    rw [hidx] at he
    exact he
  rw [hmul]
  exact det_symp_vandermonde n (fun j => j + 1 + j / 2) (fun i j h => by omega) s hs

end FieldSpec


end Mod2


section Mod4
open Finset Matrix E6

/- R-matrix and K-matrix -/

def Rmat (z : E6) (o1 o2 i1 i2 : Bool) : E6 :=
  if o1 = i1 ∧ o2 = i2 then
    if i1 = i2 then sig (q * z) else sig z
  else if o1 = i2 ∧ o2 = i1 then sig q
  else 0

def Kmat (y α β : E6) (o i : Bool) : E6 :=
  if o = i then
    if i = false then α * y + β * y⁻¹ else α * y⁻¹ + β * y
  else 0

lemma Rmat_at_q (o1 o2 i1 i2 : Bool) :
    Rmat q o1 o2 i1 i2 = if o1.toNat + o2.toNat = i1.toNat + i2.toNat then c else 0 := by
  cases o1 <;> cases o2 <;> cases i1 <;> cases i2 <;>
    simp [Rmat, ← sq, sig_q_sq, c]

lemma Kmat_at_q (o i : Bool) :
    Kmat q (-q) q⁻¹ o i = if o = false ∧ i = false then -c else 0 := by
  cases o <;> cases i <;> simp only [Kmat, Bool.false_eq_true, Bool.true_eq_false, and_self,
    and_false, false_and, ite_true, ite_false]
  · rw [← sig_q_sq]; unfold sig; rw [sq, mul_inv]; ring
  · rw [neg_mul, mul_inv_cancel₀ q_ne_zero, inv_mul_cancel₀ q_ne_zero]; ring

/- Small 8x8 and 4x4 matrices for YBE and Reflection Equation -/

abbrev B3 := Bool × Bool × Bool
abbrev B2 := Bool × Bool

def R01s (z : E6) : Matrix B3 B3 E6 :=
  Matrix.of fun a b => if a.2.2 = b.2.2 then Rmat z a.1 a.2.1 b.1 b.2.1 else 0

def R20s (z : E6) : Matrix B3 B3 E6 :=
  Matrix.of fun a b => if a.2.1 = b.2.1 then Rmat z a.2.2 a.1 b.2.2 b.1 else 0

def R21s (z : E6) : Matrix B3 B3 E6 :=
  Matrix.of fun a b => if a.1 = b.1 then Rmat z a.2.2 a.2.1 b.2.2 b.2.1 else 0

lemma ybe_A_small (a b : E6) (ha : a ≠ 0) (hb : b ≠ 0) :
    R01s (a * b⁻¹) * R20s a * R21s b = R21s b * R20s a * R01s (a * b⁻¹) := by
  have hq : q ≠ 0 := q_ne_zero
  ext ⟨o0, o1, o2⟩ ⟨i0, i1, i2⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, R01s, R20s, R21s,
    Matrix.of_apply]
  cases o0 <;> cases o1 <;> cases o2 <;> cases i0 <;> cases i1 <;> cases i2 <;>
    simp only [Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add, sig, mul_inv, inv_inv] <;>
    field_simp [ha, hb, hq] <;>
    ring

lemma ybe_B_small (a b : E6) (ha : a ≠ 0) (hb : b ≠ 0) :
    R20s a * R01s (a * b) * R21s b = R21s b * R01s (a * b) * R20s a := by
  have hq : q ≠ 0 := q_ne_zero
  ext ⟨o0, o1, o2⟩ ⟨i0, i1, i2⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, R01s, R20s, R21s,
    Matrix.of_apply]
  cases o0 <;> cases o1 <;> cases o2 <;> cases i0 <;> cases i1 <;> cases i2 <;>
    simp only [Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add, sig, mul_inv] <;>
    field_simp [ha, hb, hq] <;>
    ring

def R12s (z : E6) : Matrix B2 B2 E6 := Matrix.of fun a b => Rmat z a.1 a.2 b.1 b.2
def K1s (y α β : E6) : Matrix B2 B2 E6 := Matrix.of fun a b => if a.2 = b.2 then Kmat y α β a.1 b.1 else 0
def K2s (y α β : E6) : Matrix B2 B2 E6 := Matrix.of fun a b => if a.1 = b.1 then Kmat y α β a.2 b.2 else 0

lemma re_base_small (y1 y2 α β : E6) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) :
    R12s (y1 * y2⁻¹) * K1s y1 α β * R12s (y1 * y2) * K2s y2 α β =
    K2s y2 α β * R12s (y1 * y2) * K1s y1 α β * R12s (y1 * y2⁻¹) := by
  have hq : q ≠ 0 := q_ne_zero
  ext ⟨o1, o2⟩ ⟨i1, i2⟩
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool, R12s, K1s, K2s,
    Matrix.of_apply]
  cases o1 <;> cases o2 <;> cases i1 <;> cases i2 <;>
    simp only [Rmat, Kmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add, sig, mul_inv, inv_inv] <;>
    field_simp [hy1, hy2, hq] <;>
    ring

/- Recursive transfer matrix `Umat` and `Bmat` -/

abbrev Vec (n : ℕ) := Fin n → Bool

def allF (n : ℕ) : Vec n := fun _ => false
def allT (n : ℕ) : Vec n := fun _ => true

def Umat : (n : ℕ) → (Fin n → E6) → E6 → E6 → E6 →
    Matrix (Bool × Vec n) (Bool × Vec n) E6
  | 0, _, y, α, β => Matrix.of fun p1 p2 => Kmat y α β p1.1 p2.1
  | n + 1, x, y, α, β =>
    let x0 := x 0
    let Ut := Umat n (fun i => x i.succ) y α β
    Matrix.of fun p1 p2 =>
      ∑ v0m : Bool, ∑ h1 : Bool, ∑ h2 : Bool,
        Rmat (y * x0) (p1.2 0) p1.1 v0m h2 *
        Ut (h2, fun i => p1.2 i.succ) (h1, fun i => p2.2 i.succ) *
        Rmat (y * x0⁻¹) v0m h1 (p2.2 0) p2.1

/- Operators on `B2 × Vec n` for Sklyanin's Reflection Equation -/

def R12_op (n : ℕ) (z : E6) : Matrix (B2 × Vec n) (B2 × Vec n) E6 :=
  Matrix.kronecker (R12s z) (1 : Matrix (Vec n) (Vec n) E6)

def U1_op (n : ℕ) (U : Matrix (Bool × Vec n) (Bool × Vec n) E6) :
    Matrix (B2 × Vec n) (B2 × Vec n) E6 :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then U (a.1.1, a.2) (b.1.1, b.2) else 0

def U2_op (n : ℕ) (U : Matrix (Bool × Vec n) (Bool × Vec n) E6) :
    Matrix (B2 × Vec n) (B2 × Vec n) E6 :=
  Matrix.of fun a b => if a.1.1 = b.1.1 then U (a.1.2, a.2) (b.1.2, b.2) else 0

/- Operators on `B3 × Vec n` for the induction step `n -> n + 1` -/

def R01_op (n : ℕ) (z : E6) : Matrix (B3 × Vec n) (B3 × Vec n) E6 :=
  Matrix.kronecker (R01s z) (1 : Matrix (Vec n) (Vec n) E6)

def R20_op (n : ℕ) (z : E6) : Matrix (B3 × Vec n) (B3 × Vec n) E6 :=
  Matrix.kronecker (R20s z) (1 : Matrix (Vec n) (Vec n) E6)

def R21_op (n : ℕ) (z : E6) : Matrix (B3 × Vec n) (B3 × Vec n) E6 :=
  Matrix.kronecker (R21s z) (1 : Matrix (Vec n) (Vec n) E6)

def U1_lift (n : ℕ) (U : Matrix (Bool × Vec n) (Bool × Vec n) E6) :
    Matrix (B3 × Vec n) (B3 × Vec n) E6 :=
  Matrix.of fun a b =>
    if a.1.2.1 = b.1.2.1 ∧ a.1.2.2 = b.1.2.2 then U (a.1.1, a.2) (b.1.1, b.2) else 0

def U2_lift (n : ℕ) (U : Matrix (Bool × Vec n) (Bool × Vec n) E6) :
    Matrix (B3 × Vec n) (B3 × Vec n) E6 :=
  Matrix.of fun a b =>
    if a.1.1 = b.1.1 ∧ a.1.2.2 = b.1.2.2 then U (a.1.2.1, a.2) (b.1.2.1, b.2) else 0

lemma kronecker_one_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A B : Matrix α α E6) :
    Matrix.kronecker A (1 : Matrix β β E6) * Matrix.kronecker B (1 : Matrix β β E6) =
    Matrix.kronecker (A * B) (1 : Matrix β β E6) := by
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, mul_one]

lemma ybe_A_op (n : ℕ) (a b : E6) (ha : a ≠ 0) (hb : b ≠ 0) :
    R01_op n (a * b⁻¹) * R20_op n a * R21_op n b =
    R21_op n b * R20_op n a * R01_op n (a * b⁻¹) := by
  simp only [R01_op, R20_op, R21_op, kronecker_one_mul, ybe_A_small a b ha hb]

lemma ybe_B_op (n : ℕ) (a b : E6) (ha : a ≠ 0) (hb : b ≠ 0) :
    R20_op n a * R01_op n (a * b) * R21_op n b =
    R21_op n b * R01_op n (a * b) * R20_op n a := by
  simp only [R01_op, R20_op, R21_op, kronecker_one_mul, ybe_B_small a b ha hb]

lemma U1_lift_comm_R21 (n : ℕ) (U : Matrix (Bool × Vec n) (Bool × Vec n) E6) (z : E6) :
    U1_lift n U * R21_op n z = R21_op n z * U1_lift n U := by
  ext ⟨⟨o1, o2, ov⟩, ovt⟩ ⟨⟨i1, i2, iv⟩, ivt⟩
  simp only [Matrix.mul_apply, U1_lift, R21_op, Matrix.kronecker, Matrix.kroneckerMap_apply,
    R21s, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ((i1, o2, ov), ivt)]
  · rw [Finset.sum_eq_single ((o1, i2, iv), ovt)]
    · simp [mul_comm]
    · rintro ⟨⟨m1, m2, mv⟩, mvt⟩ _ hm
      by_cases h1 : m1 = o1 ∧ m2 = i2 ∧ mv = iv ∧ mvt = ovt
      · rcases h1 with ⟨rfl, rfl, rfl, rfl⟩; exact absurd rfl hm
      · split_ifs <;> simp_all
    · intro h; exact absurd (Finset.mem_univ _) h
  · rintro ⟨⟨m1, m2, mv⟩, mvt⟩ _ hm
    by_cases h1 : m1 = i1 ∧ m2 = o2 ∧ mv = ov ∧ mvt = ivt
    · rcases h1 with ⟨rfl, rfl, rfl, rfl⟩; exact absurd rfl hm
    · split_ifs <;> simp_all
  · intro h; exact absurd (Finset.mem_univ _) h

lemma U2_lift_comm_R20 (n : ℕ) (U : Matrix (Bool × Vec n) (Bool × Vec n) E6) (z : E6) :
    U2_lift n U * R20_op n z = R20_op n z * U2_lift n U := by
  ext ⟨⟨o1, o2, ov⟩, ovt⟩ ⟨⟨i1, i2, iv⟩, ivt⟩
  simp only [Matrix.mul_apply, U2_lift, R20_op, Matrix.kronecker, Matrix.kroneckerMap_apply,
    R20s, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ((o1, i2, ov), ivt)]
  · rw [Finset.sum_eq_single ((i1, o2, iv), ovt)]
    · simp [mul_comm]
    · rintro ⟨⟨m1, m2, mv⟩, mvt⟩ _ hm
      by_cases h1 : m1 = i1 ∧ m2 = o2 ∧ mv = iv ∧ mvt = ovt
      · rcases h1 with ⟨rfl, rfl, rfl, rfl⟩; exact absurd rfl hm
      · split_ifs <;> simp_all
    · intro h; exact absurd (Finset.mem_univ _) h
  · rintro ⟨⟨m1, m2, mv⟩, mvt⟩ _ hm
    by_cases h1 : m1 = o1 ∧ m2 = i2 ∧ mv = ov ∧ mvt = ivt
    · rcases h1 with ⟨rfl, rfl, rfl, rfl⟩; exact absurd rfl hm
    · split_ifs <;> simp_all
  · intro h; exact absurd (Finset.mem_univ _) h

/- Equivalence `B2 × Vec (n + 1) ≃ B3 × Vec n` -/

def splitEquiv (n : ℕ) : B2 × Vec (n + 1) ≃ B3 × Vec n where
  toFun p := ((p.1.1, p.1.2, p.2 0), fun i => p.2 i.succ)
  invFun p := ((p.1.1, p.1.2.1), Fin.cons p.1.2.2 p.2)
  left_inv p := by
    rcases p with ⟨⟨h1, h2⟩, v⟩
    ext1
    · rfl
    · funext i; refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    rcases p with ⟨⟨h1, h2, v0⟩, vt⟩
    ext1
    · rfl
    · funext i; simp

lemma submatrix_mul_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (A B : Matrix β β E6) :
    (A * B).submatrix e e = A.submatrix e e * B.submatrix e e := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm

lemma R12_op_step (n : ℕ) (z : E6) :
    (R12_op (n + 1) z).submatrix (splitEquiv n).symm (splitEquiv n).symm = R01_op n z := by
  ext ⟨⟨o1, o2, ov⟩, ovt⟩ ⟨⟨i1, i2, iv⟩, ivt⟩
  simp only [Matrix.submatrix_apply, R12_op, R01_op, Matrix.kronecker, Matrix.kroneckerMap_apply,
    R12s, R01s, Matrix.of_apply, Matrix.one_apply, splitEquiv, Equiv.coe_fn_symm_mk]
  have hcons : (Fin.cons ov ovt : Vec (n + 1)) = Fin.cons iv ivt ↔ ov = iv ∧ ovt = ivt := by
    constructor
    · intro h
      refine ⟨by simpa using congrFun h 0, ?_⟩
      funext j; simpa using congrFun h j.succ
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [hcons]
  by_cases h1 : ov = iv <;> by_cases h2 : ovt = ivt <;> simp [h1, h2]

lemma U1_op_step (n : ℕ) (x : Fin (n + 1) → E6) (y α β : E6) :
    (U1_op (n + 1) (Umat (n + 1) x y α β)).submatrix (splitEquiv n).symm (splitEquiv n).symm =
    R20_op n (y * x 0) * U1_lift n (Umat n (fun i => x i.succ) y α β) * R20_op n (y * (x 0)⁻¹) := by
  ext ⟨⟨o1, o2, ov⟩, ovt⟩ ⟨⟨i1, i2, iv⟩, ivt⟩
  simp only [Matrix.submatrix_apply, U1_op, Umat, Matrix.of_apply, splitEquiv,
    Equiv.coe_fn_symm_mk, Fin.cons_zero, Fin.cons_succ]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, R20_op, U1_lift, Matrix.kronecker, Matrix.kroneckerMap_apply,
    R20s, Matrix.of_apply, Matrix.one_apply]
  by_cases ho2 : o2 = i2
  · subst ho2
    rw [if_pos rfl]
    simp only [Fintype.sum_prod_type]
    have hinner : ∀ (m1 m2 mv : Bool) (mvt : Vec n),
        (∑ a1 : Bool, ∑ a2 : Bool, ∑ av : Bool, ∑ avt : Vec n,
          (if o2 = a2 then Rmat (y * x 0) ov o1 av a1 else 0) * (if ovt = avt then 1 else 0) *
          (if a2 = m2 ∧ av = mv then Umat n (fun i => x i.succ) y α β (a1, avt) (m1, mvt) else 0)) *
        ((if m2 = o2 then Rmat (y * (x 0)⁻¹) mv m1 iv i1 else 0) * (if mvt = ivt then 1 else 0)) =
        if m2 = o2 ∧ mvt = ivt then
          (∑ a1 : Bool, Rmat (y * x 0) ov o1 mv a1 *
            Umat n (fun i => x i.succ) y α β (a1, ovt) (m1, ivt)) *
          Rmat (y * (x 0)⁻¹) mv m1 iv i1
        else 0 := by
      intro m1 m2 mv mvt
      by_cases hm : m2 = o2 ∧ mvt = ivt
      · rcases hm with ⟨rfl, rfl⟩
        simp only [ite_true, and_self, mul_one]
        congr 1
        apply Finset.sum_congr rfl; intro a1 _
        rw [Finset.sum_eq_single m2]
        · rw [Finset.sum_eq_single mv]
          · rw [Finset.sum_eq_single ovt]
            · simp
            · intro avt _ havt; simp [Ne.symm havt]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro av _ hav; simp [hav]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro a2 _ ha2; simp [ha2]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg hm]
        by_cases h1 : m2 = o2
        · have h2 : mvt ≠ ivt := fun h => hm ⟨h1, h⟩
          simp [h2]
        · simp [h1]
    simp_rw [hinner]
    trans ∑ mv : Bool, ∑ m1 : Bool, ∑ a1 : Bool,
        Rmat (y * x 0) ov o1 mv a1 * Umat n (fun i => x i.succ) y α β (a1, ovt) (m1, ivt) *
        Rmat (y * (x 0)⁻¹) mv m1 iv i1
    · rfl
    · symm
      have hcollapse : ∀ m1 : Bool,
          (∑ m2 : Bool, ∑ mv : Bool, ∑ mvt : Vec n,
            if m2 = o2 ∧ mvt = ivt then
              (∑ a1 : Bool, Rmat (y * x 0) ov o1 mv a1 *
                Umat n (fun i => x i.succ) y α β (a1, ovt) (m1, ivt)) *
              Rmat (y * (x 0)⁻¹) mv m1 iv i1
            else 0) =
          ∑ mv : Bool, ∑ a1 : Bool,
            Rmat (y * x 0) ov o1 mv a1 * Umat n (fun i => x i.succ) y α β (a1, ovt) (m1, ivt) *
            Rmat (y * (x 0)⁻¹) mv m1 iv i1 := by
        intro m1
        rw [Finset.sum_eq_single o2]
        · apply Finset.sum_congr rfl; intro mv _
          rw [Finset.sum_eq_single ivt]
          · simp only [and_self, ite_true, Finset.sum_mul]
          · intro mvt _ hmvt; simp [hmvt]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro m2 _ hm2
          apply Finset.sum_eq_zero; intro mv _
          apply Finset.sum_eq_zero; intro mvt _
          simp [hm2]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [hcollapse]
      rw [Finset.sum_comm]
  · rw [if_neg ho2]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨⟨m1, m2, mv⟩, mvt⟩ _
    by_cases hm2 : m2 = i2
    · subst hm2
      have hzero : (∑ a : B3 × Vec n,
          (if o2 = a.1.2.1 then Rmat (y * x 0) ov o1 a.1.2.2 a.1.1 else 0) *
          (if ovt = a.2 then 1 else 0) *
          (if a.1.2.1 = m2 ∧ a.1.2.2 = mv then
            Umat n (fun i => x i.succ) y α β (a.1.1, a.2) (m1, mvt) else 0)) = 0 := by
        apply Finset.sum_eq_zero; rintro ⟨⟨a1, a2, av⟩, avt⟩ _
        by_cases ha : o2 = a2
        · subst ha; simp [ho2]
        · simp [ha]
      rw [hzero, zero_mul]
    · simp [hm2]

lemma U2_op_step (n : ℕ) (x : Fin (n + 1) → E6) (y α β : E6) :
    (U2_op (n + 1) (Umat (n + 1) x y α β)).submatrix (splitEquiv n).symm (splitEquiv n).symm =
    R21_op n (y * x 0) * U2_lift n (Umat n (fun i => x i.succ) y α β) * R21_op n (y * (x 0)⁻¹) := by
  ext ⟨⟨o1, o2, ov⟩, ovt⟩ ⟨⟨i1, i2, iv⟩, ivt⟩
  simp only [Matrix.submatrix_apply, U2_op, Umat, Matrix.of_apply, splitEquiv,
    Equiv.coe_fn_symm_mk, Fin.cons_zero, Fin.cons_succ]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, R21_op, U2_lift, Matrix.kronecker, Matrix.kroneckerMap_apply,
    R21s, Matrix.of_apply, Matrix.one_apply]
  by_cases ho1 : o1 = i1
  · subst ho1
    rw [if_pos rfl]
    simp only [Fintype.sum_prod_type]
    have hinner : ∀ (m1 m2 mv : Bool) (mvt : Vec n),
        (∑ a1 : Bool, ∑ a2 : Bool, ∑ av : Bool, ∑ avt : Vec n,
          (if o1 = a1 then Rmat (y * x 0) ov o2 av a2 else 0) * (if ovt = avt then 1 else 0) *
          (if a1 = m1 ∧ av = mv then Umat n (fun i => x i.succ) y α β (a2, avt) (m2, mvt) else 0)) *
        ((if m1 = o1 then Rmat (y * (x 0)⁻¹) mv m2 iv i2 else 0) * (if mvt = ivt then 1 else 0)) =
        if m1 = o1 ∧ mvt = ivt then
          (∑ a2 : Bool, Rmat (y * x 0) ov o2 mv a2 *
            Umat n (fun i => x i.succ) y α β (a2, ovt) (m2, ivt)) *
          Rmat (y * (x 0)⁻¹) mv m2 iv i2
        else 0 := by
      intro m1 m2 mv mvt
      by_cases hm : m1 = o1 ∧ mvt = ivt
      · rcases hm with ⟨rfl, rfl⟩
        simp only [ite_true, and_self, mul_one]
        congr 1
        rw [Finset.sum_eq_single m1]
        · apply Finset.sum_congr rfl; intro a2 _
          rw [Finset.sum_eq_single mv]
          · rw [Finset.sum_eq_single ovt]
            · simp
            · intro avt _ havt; simp [Ne.symm havt]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro av _ hav; simp [hav]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro a1 _ ha1
          apply Finset.sum_eq_zero; intro a2 _
          apply Finset.sum_eq_zero; intro av _
          apply Finset.sum_eq_zero; intro avt _
          simp [ha1]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [if_neg hm]
        by_cases h1 : m1 = o1
        · have h2 : mvt ≠ ivt := fun h => hm ⟨h1, h⟩
          simp [h2]
        · simp [h1]
    simp_rw [hinner]
    symm
    rw [Finset.sum_eq_single o1]
    · have hcollapse : ∀ m2 : Bool,
          (∑ mv : Bool, ∑ mvt : Vec n,
            if o1 = o1 ∧ mvt = ivt then
              (∑ a2 : Bool, Rmat (y * x 0) ov o2 mv a2 *
                Umat n (fun i => x i.succ) y α β (a2, ovt) (m2, ivt)) *
              Rmat (y * (x 0)⁻¹) mv m2 iv i2
            else 0) =
          ∑ mv : Bool, ∑ a2 : Bool,
            Rmat (y * x 0) ov o2 mv a2 * Umat n (fun i => x i.succ) y α β (a2, ovt) (m2, ivt) *
            Rmat (y * (x 0)⁻¹) mv m2 iv i2 := by
        intro m2
        apply Finset.sum_congr rfl; intro mv _
        rw [Finset.sum_eq_single ivt]
        · rw [if_pos ⟨rfl, rfl⟩, Finset.sum_mul]
        · intro mvt _ hmvt; simp [hmvt]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hsum : (∑ m2 : Bool, ∑ mv : Bool, ∑ mvt : Vec n,
          if o1 = o1 ∧ mvt = ivt then
            (∑ a2 : Bool, Rmat (y * x 0) ov o2 mv a2 *
              Umat n (fun i => x i.succ) y α β (a2, ovt) (m2, ivt)) *
            Rmat (y * (x 0)⁻¹) mv m2 iv i2
          else 0) =
          ∑ m2 : Bool, ∑ mv : Bool, ∑ a2 : Bool,
            Rmat (y * x 0) ov o2 mv a2 * Umat n (fun i => x i.succ) y α β (a2, ovt) (m2, ivt) *
            Rmat (y * (x 0)⁻¹) mv m2 iv i2 :=
        Finset.sum_congr rfl fun m2 _ => hcollapse m2
      rw [hsum, Finset.sum_comm]
    · intro m1 _ hm1
      apply Finset.sum_eq_zero; intro m2 _
      apply Finset.sum_eq_zero; intro mv _
      apply Finset.sum_eq_zero; intro mvt _
      simp [hm1]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg ho1]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨⟨m1, m2, mv⟩, mvt⟩ _
    by_cases hm1 : m1 = i1
    · subst hm1
      have hzero : (∑ a : B3 × Vec n,
          (if o1 = a.1.1 then Rmat (y * x 0) ov o2 a.1.2.2 a.1.2.1 else 0) *
          (if ovt = a.2 then 1 else 0) *
          (if a.1.1 = m1 ∧ a.1.2.2 = mv then
            Umat n (fun i => x i.succ) y α β (a.1.2.1, a.2) (m2, mvt) else 0)) = 0 := by
        apply Finset.sum_eq_zero; rintro ⟨⟨a1, a2, av⟩, avt⟩ _
        by_cases ha : o1 = a1
        · subst ha; simp [ho1]
        · simp [ha]
      rw [hzero, zero_mul]
    · simp [hm1]

lemma re_lift_of_re (n : ℕ) (U1 U2 : Matrix (Bool × Vec n) (Bool × Vec n) E6) (z1 z2 : E6)
    (hre : R12_op n z1 * U1_op n U1 * R12_op n z2 * U2_op n U2 =
           U2_op n U2 * R12_op n z2 * U1_op n U1 * R12_op n z1) :
    R01_op n z1 * U1_lift n U1 * R01_op n z2 * U2_lift n U2 =
    U2_lift n U2 * R01_op n z2 * U1_lift n U1 * R01_op n z1 := by
  -- Both sides are diagonal in v0 (the third Bool coordinate), with identical block on B2 × Vec n!
  let e : B3 × Vec n ≃ Bool × (B2 × Vec n) :=
    { toFun := fun p => (p.1.2.2, ((p.1.1, p.1.2.1), p.2))
      invFun := fun p => ((p.2.1.1, p.2.1.2, p.1), p.2.2)
      left_inv := fun ⟨⟨_, _, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, ⟨⟨_, _⟩, _⟩⟩ => rfl }
  have hsub : ∀ M : Matrix (B3 × Vec n) (B3 × Vec n) E6,
      M = (M.submatrix e.symm e.symm).submatrix e e := by
    intro M; ext a b; simp [Matrix.submatrix_apply]
  have hR01 : ∀ z, (R01_op n z).submatrix e.symm e.symm =
      Matrix.kronecker (1 : Matrix Bool Bool E6) (R12_op n z) := by
    intro z; ext ⟨o, ⟨o1, o2⟩, ov⟩ ⟨i, ⟨i1, i2⟩, iv⟩
    simp only [Matrix.submatrix_apply, R01_op, R12_op, Matrix.kronecker, Matrix.kroneckerMap_apply,
      R01s, R12s, Matrix.of_apply, Matrix.one_apply, e, Equiv.coe_fn_symm_mk]
    by_cases h : o = i <;> simp [h]
  have hU1 : (U1_lift n U1).submatrix e.symm e.symm =
      Matrix.kronecker (1 : Matrix Bool Bool E6) (U1_op n U1) := by
    ext ⟨o, ⟨o1, o2⟩, ov⟩ ⟨i, ⟨i1, i2⟩, iv⟩
    simp only [Matrix.submatrix_apply, U1_lift, U1_op, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.of_apply, Matrix.one_apply, e, Equiv.coe_fn_symm_mk]
    by_cases h1 : o = i <;> by_cases h2 : o2 = i2 <;> simp [h1, h2]
  have hU2 : (U2_lift n U2).submatrix e.symm e.symm =
      Matrix.kronecker (1 : Matrix Bool Bool E6) (U2_op n U2) := by
    ext ⟨o, ⟨o1, o2⟩, ov⟩ ⟨i, ⟨i1, i2⟩, iv⟩
    simp only [Matrix.submatrix_apply, U2_lift, U2_op, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Matrix.of_apply, Matrix.one_apply, e, Equiv.coe_fn_symm_mk]
    by_cases h1 : o = i <;> by_cases h2 : o1 = i1 <;> simp [h1, h2]
  have hgoal : (R01_op n z1 * U1_lift n U1 * R01_op n z2 * U2_lift n U2).submatrix e.symm e.symm =
      (U2_lift n U2 * R01_op n z2 * U1_lift n U1 * R01_op n z1).submatrix e.symm e.symm := by
    simp only [submatrix_mul_equiv, hR01, hU1, hU2]
    have hmul : ∀ A B : Matrix (B2 × Vec n) (B2 × Vec n) E6,
        Matrix.kronecker (1 : Matrix Bool Bool E6) A * Matrix.kronecker (1 : Matrix Bool Bool E6) B =
        Matrix.kronecker (1 : Matrix Bool Bool E6) (A * B) := by
      intro A B; unfold Matrix.kronecker; rw [← Matrix.mul_kronecker_mul, mul_one]
    simp only [hmul, hre]
  rw [hsub (R01_op n z1 * U1_lift n U1 * R01_op n z2 * U2_lift n U2),
      hsub (U2_lift n U2 * R01_op n z2 * U1_lift n U1 * R01_op n z1), hgoal]

/- Sklyanin's Reflection Equation for `Umat n`! -/

theorem sklyanin_RE : ∀ (n : ℕ) (x : Fin n → E6) (hx : ∀ j, x j ≠ 0)
    (y1 y2 α β : E6) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0),
    R12_op n (y1 * y2⁻¹) * U1_op n (Umat n x y1 α β) *
      R12_op n (y1 * y2) * U2_op n (Umat n x y2 α β) =
    U2_op n (Umat n x y2 α β) * R12_op n (y1 * y2) *
      U1_op n (Umat n x y1 α β) * R12_op n (y1 * y2⁻¹)
  | 0, x, _, y1, y2, α, β, hy1, hy2 => by
    have hU1 : U1_op 0 (Umat 0 x y1 α β) = Matrix.kronecker (K1s y1 α β) (1 : Matrix (Vec 0) (Vec 0) E6) := by
      ext ⟨⟨o1, o2⟩, ov⟩ ⟨⟨i1, i2⟩, iv⟩
      have hEq : ov = iv := Subsingleton.elim ov iv
      simp [U1_op, Umat, K1s, hEq]
    have hU2 : U2_op 0 (Umat 0 x y2 α β) = Matrix.kronecker (K2s y2 α β) (1 : Matrix (Vec 0) (Vec 0) E6) := by
      ext ⟨⟨o1, o2⟩, ov⟩ ⟨⟨i1, i2⟩, iv⟩
      have hEq : ov = iv := Subsingleton.elim ov iv
      simp [U2_op, Umat, K2s, hEq]
    simp only [R12_op, hU1, hU2, kronecker_one_mul, re_base_small y1 y2 α β hy1 hy2]
  | n + 1, x, hx, y1, y2, α, β, hy1, hy2 => by
    let e := (splitEquiv n).symm
    have hinj : ∀ A B : Matrix (B2 × Vec (n + 1)) (B2 × Vec (n + 1)) E6,
        A.submatrix e e = B.submatrix e e → A = B := by
      intro A B h
      ext a b
      have := congrFun (congrFun h (splitEquiv n a)) (splitEquiv n b)
      simpa [Matrix.submatrix_apply, e] using this
    apply hinj
    simp only [submatrix_mul_equiv, e, R12_op_step, U1_op_step, U2_op_step]
    set x0 := x 0
    have hx0 : x0 ≠ 0 := hx 0
    set U1 := U1_lift n (Umat n (fun i => x i.succ) y1 α β)
    set U2 := U2_lift n (Umat n (fun i => x i.succ) y2 α β)
    have hIH := re_lift_of_re n (Umat n (fun i => x i.succ) y1 α β)
      (Umat n (fun i => x i.succ) y2 α β) (y1 * y2⁻¹) (y1 * y2)
      (sklyanin_RE n (fun i => x i.succ) (fun i => hx i.succ) y1 y2 α β hy1 hy2)
    have hA1 : R01_op n (y1 * y2⁻¹) * R20_op n (y1 * x0) * R21_op n (y2 * x0) =
        R21_op n (y2 * x0) * R20_op n (y1 * x0) * R01_op n (y1 * y2⁻¹) := by
      have h := ybe_A_op n (y1 * x0) (y2 * x0) (mul_ne_zero hy1 hx0) (mul_ne_zero hy2 hx0)
      have heq : (y1 * x0) * (y2 * x0)⁻¹ = y1 * y2⁻¹ := by field_simp [hx0, hy2]
      rwa [heq] at h
    have hA2 : R01_op n (y1 * y2⁻¹) * R20_op n (y1 * x0⁻¹) * R21_op n (y2 * x0⁻¹) =
        R21_op n (y2 * x0⁻¹) * R20_op n (y1 * x0⁻¹) * R01_op n (y1 * y2⁻¹) := by
      have h := ybe_A_op n (y1 * x0⁻¹) (y2 * x0⁻¹)
        (mul_ne_zero hy1 (inv_ne_zero hx0)) (mul_ne_zero hy2 (inv_ne_zero hx0))
      have heq : (y1 * x0⁻¹) * (y2 * x0⁻¹)⁻¹ = y1 * y2⁻¹ := by field_simp [hx0, hy2]
      rwa [heq] at h
    have hB1 : R20_op n (y1 * x0⁻¹) * R01_op n (y1 * y2) * R21_op n (y2 * x0) =
        R21_op n (y2 * x0) * R01_op n (y1 * y2) * R20_op n (y1 * x0⁻¹) := by
      have h := ybe_B_op n (y1 * x0⁻¹) (y2 * x0)
        (mul_ne_zero hy1 (inv_ne_zero hx0)) (mul_ne_zero hy2 hx0)
      have heq : (y1 * x0⁻¹) * (y2 * x0) = y1 * y2 := by field_simp [hx0]
      rwa [heq] at h
    have hB2 : R20_op n (y1 * x0) * R01_op n (y1 * y2) * R21_op n (y2 * x0⁻¹) =
        R21_op n (y2 * x0⁻¹) * R01_op n (y1 * y2) * R20_op n (y1 * x0) := by
      have h := ybe_B_op n (y1 * x0) (y2 * x0⁻¹)
        (mul_ne_zero hy1 hx0) (mul_ne_zero hy2 (inv_ne_zero hx0))
      have heq : (y1 * x0) * (y2 * x0⁻¹) = y1 * y2 := by field_simp [hx0]
      rwa [heq] at h
    have hC1a : U1 * R21_op n (y2 * x0) = R21_op n (y2 * x0) * U1 := U1_lift_comm_R21 n _ _
    have hC1b : U1 * R21_op n (y2 * x0⁻¹) = R21_op n (y2 * x0⁻¹) * U1 := U1_lift_comm_R21 n _ _
    have hC2a : U2 * R20_op n (y1 * x0) = R20_op n (y1 * x0) * U2 := U2_lift_comm_R20 n _ _
    have hC2b : U2 * R20_op n (y1 * x0⁻¹) = R20_op n (y1 * x0⁻¹) * U2 := U2_lift_comm_R20 n _ _
    calc R01_op n (y1 * y2⁻¹) * (R20_op n (y1 * x0) * U1 * R20_op n (y1 * x0⁻¹)) *
          R01_op n (y1 * y2) * (R21_op n (y2 * x0) * U2 * R21_op n (y2 * x0⁻¹))
        = R01_op n (y1 * y2⁻¹) * R20_op n (y1 * x0) * U1 *
          (R20_op n (y1 * x0⁻¹) * R01_op n (y1 * y2) * R21_op n (y2 * x0)) *
          U2 * R21_op n (y2 * x0⁻¹) := by simp only [Matrix.mul_assoc]
      _ = R01_op n (y1 * y2⁻¹) * R20_op n (y1 * x0) * U1 *
          (R21_op n (y2 * x0) * R01_op n (y1 * y2) * R20_op n (y1 * x0⁻¹)) *
          U2 * R21_op n (y2 * x0⁻¹) := by rw [hB1]
      _ = (R01_op n (y1 * y2⁻¹) * R20_op n (y1 * x0)) * (U1 * R21_op n (y2 * x0)) *
          R01_op n (y1 * y2) * (R20_op n (y1 * x0⁻¹) * U2) * R21_op n (y2 * x0⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = (R01_op n (y1 * y2⁻¹) * R20_op n (y1 * x0) * R21_op n (y2 * x0)) * U1 *
          R01_op n (y1 * y2) * U2 * (R20_op n (y1 * x0⁻¹) * R21_op n (y2 * x0⁻¹)) := by
          rw [hC1a, ← hC2b]; simp only [Matrix.mul_assoc]
      _ = R21_op n (y2 * x0) * R20_op n (y1 * x0) *
          (R01_op n (y1 * y2⁻¹) * U1 * R01_op n (y1 * y2) * U2) *
          R20_op n (y1 * x0⁻¹) * R21_op n (y2 * x0⁻¹) := by
          rw [hA1]; simp only [Matrix.mul_assoc]
      _ = R21_op n (y2 * x0) * R20_op n (y1 * x0) *
          (U2 * R01_op n (y1 * y2) * U1 * R01_op n (y1 * y2⁻¹)) *
          R20_op n (y1 * x0⁻¹) * R21_op n (y2 * x0⁻¹) := by rw [hIH]
      _ = R21_op n (y2 * x0) * (R20_op n (y1 * x0) * U2) * R01_op n (y1 * y2) * U1 *
          (R01_op n (y1 * y2⁻¹) * R20_op n (y1 * x0⁻¹) * R21_op n (y2 * x0⁻¹)) := by
          simp only [Matrix.mul_assoc]
      _ = R21_op n (y2 * x0) * U2 * R20_op n (y1 * x0) * R01_op n (y1 * y2) *
          (U1 * R21_op n (y2 * x0⁻¹)) * R20_op n (y1 * x0⁻¹) * R01_op n (y1 * y2⁻¹) := by
          rw [← hC2a, hA2]; simp only [Matrix.mul_assoc]
      _ = R21_op n (y2 * x0) * U2 *
          (R20_op n (y1 * x0) * R01_op n (y1 * y2) * R21_op n (y2 * x0⁻¹)) *
          U1 * R20_op n (y1 * x0⁻¹) * R01_op n (y1 * y2⁻¹) := by
          rw [hC1b]; simp only [Matrix.mul_assoc]
      _ = R21_op n (y2 * x0) * U2 *
          (R21_op n (y2 * x0⁻¹) * R01_op n (y1 * y2) * R20_op n (y1 * x0)) *
          U1 * R20_op n (y1 * x0⁻¹) * R01_op n (y1 * y2⁻¹) := by rw [hB2]
      _ = (R21_op n (y2 * x0) * U2 * R21_op n (y2 * x0⁻¹)) * R01_op n (y1 * y2) *
          (R20_op n (y1 * x0) * U1 * R20_op n (y1 * x0⁻¹)) * R01_op n (y1 * y2⁻¹) := by
          simp only [Matrix.mul_assoc]

/- `Bmat` and its commutativity! -/

def Bmat (n : ℕ) (x : Fin n → E6) (y α β : E6) : Matrix (Vec n) (Vec n) E6 :=
  Matrix.of fun vo vi => Umat n x y α β (false, vo) (true, vi)

theorem Bmat_comm (n : ℕ) (x : Fin n → E6) (hx : ∀ j, x j ≠ 0)
    (y1 y2 α β : E6) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0)
    (h1 : sig (q * (y1 * y2⁻¹)) ≠ 0) (h2 : sig (y1 * y2) ≠ 0) :
    Bmat n x y1 α β * Bmat n x y2 α β = Bmat n x y2 α β * Bmat n x y1 α β := by
  have hRE := sklyanin_RE n x hx y1 y2 α β hy1 hy2
  set U1 := Umat n x y1 α β
  set U2 := Umat n x y2 α β
  ext vo vi
  have hent := congrFun (congrFun hRE ((false, false), vo)) ((true, true), vi)
  have hL : (R12_op n (y1 * y2⁻¹) * U1_op n U1 * R12_op n (y1 * y2) * U2_op n U2)
        ((false, false), vo) ((true, true), vi) =
      sig (q * (y1 * y2⁻¹)) * sig (y1 * y2) * (Bmat n x y1 α β * Bmat n x y2 α β) vo vi := by
    rw [Matrix.mul_assoc (R12_op n (y1 * y2⁻¹)), Matrix.mul_assoc (R12_op n (y1 * y2⁻¹)),
        Matrix.mul_assoc (U1_op n U1)]
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single ((false, false), vo)]
    · have hR0 : R12_op n (y1 * y2⁻¹) ((false, false), vo) ((false, false), vo) =
          sig (q * (y1 * y2⁻¹)) := by
        simp [R12_op, R12s, Rmat]
      rw [hR0, Matrix.mul_apply]
      have hmid : (∑ m : B2 × Vec n,
          U1_op n U1 ((false, false), vo) m *
          (R12_op n (y1 * y2) * U2_op n U2) m ((true, true), vi)) =
          sig (y1 * y2) * (Bmat n x y1 α β * Bmat n x y2 α β) vo vi := by
        have hRU2 : ∀ m : B2 × Vec n,
            U1_op n U1 ((false, false), vo) m *
              (R12_op n (y1 * y2) * U2_op n U2) m ((true, true), vi) =
            if m.1 = (true, false) then
              U1 (false, vo) (true, m.2) * (sig (y1 * y2) * U2 (false, m.2) (true, vi))
            else 0 := by
          rintro ⟨⟨m1, m2⟩, mv⟩
          cases m2 with
          | true => simp [U1_op]
          | false =>
            simp only [U1_op, Matrix.of_apply, ite_true, Matrix.mul_apply, R12_op, U2_op,
              Matrix.kronecker, Matrix.kroneckerMap_apply, R12s, Matrix.one_apply]
            cases m1 with
            | false =>
              have hzero : (∑ k : B2 × Vec n,
                  Rmat (y1 * y2) false false k.1.1 k.1.2 * (if mv = k.2 then 1 else 0) *
                  (if k.1.1 = true then U2 (k.1.2, k.2) (true, vi) else 0)) = 0 := by
                apply Finset.sum_eq_zero; rintro ⟨⟨k1, k2⟩, kv⟩ _
                cases k1 <;> cases k2 <;> simp [Rmat]
              rw [hzero, mul_zero]; rfl
            | true =>
              rw [if_pos rfl]
              congr 1
              rw [Finset.sum_eq_single ((true, false), mv)]
              · simp [Rmat]
              · rintro ⟨⟨k1, k2⟩, kv⟩ _ hk
                cases k1 <;> cases k2 <;> by_cases hv : mv = kv <;> simp_all [Rmat]
              · intro h; exact absurd (Finset.mem_univ _) h
        simp_rw [hRU2]
        rw [Fintype.sum_prod_type, Finset.sum_eq_single (true, false)]
        · simp only [ite_true, Bmat, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro mv _; ring
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hmid]; ring
    · rintro ⟨⟨a1, a2⟩, av⟩ _ ha
      cases a1 <;> cases a2 <;> by_cases hv : vo = av <;> simp_all [R12_op, R12s, Rmat]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : (U2_op n U2 * R12_op n (y1 * y2) * U1_op n U1 * R12_op n (y1 * y2⁻¹))
        ((false, false), vo) ((true, true), vi) =
      sig (q * (y1 * y2⁻¹)) * sig (y1 * y2) * (Bmat n x y2 α β * Bmat n x y1 α β) vo vi := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single ((true, true), vi)]
    · have hR1 : R12_op n (y1 * y2⁻¹) ((true, true), vi) ((true, true), vi) =
          sig (q * (y1 * y2⁻¹)) := by
        simp [R12_op, R12s, Rmat]
      rw [hR1, Matrix.mul_assoc (U2_op n U2), Matrix.mul_apply]
      have hmid : (∑ m : B2 × Vec n,
          U2_op n U2 ((false, false), vo) m *
          (R12_op n (y1 * y2) * U1_op n U1) m ((true, true), vi)) =
          sig (y1 * y2) * (Bmat n x y2 α β * Bmat n x y1 α β) vo vi := by
        have hRU1 : ∀ m : B2 × Vec n,
            U2_op n U2 ((false, false), vo) m *
              (R12_op n (y1 * y2) * U1_op n U1) m ((true, true), vi) =
            if m.1 = (false, true) then
              U2 (false, vo) (true, m.2) * (sig (y1 * y2) * U1 (false, m.2) (true, vi))
            else 0 := by
          rintro ⟨⟨m1, m2⟩, mv⟩
          cases m1 with
          | true => simp [U2_op]
          | false =>
            simp only [U2_op, Matrix.of_apply, ite_true, Matrix.mul_apply, R12_op, U1_op,
              Matrix.kronecker, Matrix.kroneckerMap_apply, R12s, Matrix.one_apply]
            cases m2 with
            | false =>
              have hzero : (∑ k : B2 × Vec n,
                  Rmat (y1 * y2) false false k.1.1 k.1.2 * (if mv = k.2 then 1 else 0) *
                  (if k.1.2 = true then U1 (k.1.1, k.2) (true, vi) else 0)) = 0 := by
                apply Finset.sum_eq_zero; rintro ⟨⟨k1, k2⟩, kv⟩ _
                cases k1 <;> cases k2 <;> simp [Rmat]
              rw [hzero, mul_zero]; rfl
            | true =>
              rw [if_pos rfl]
              congr 1
              rw [Finset.sum_eq_single ((false, true), mv)]
              · simp [Rmat]
              · rintro ⟨⟨k1, k2⟩, kv⟩ _ hk
                cases k1 <;> cases k2 <;> by_cases hv : mv = kv <;> simp_all [Rmat]
              · intro h; exact absurd (Finset.mem_univ _) h
        simp_rw [hRU1]
        rw [Fintype.sum_prod_type, Finset.sum_eq_single (false, true)]
        · simp only [ite_true, Bmat, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro mv _; ring
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hmid]; ring
    · rintro ⟨⟨a1, a2⟩, av⟩ _ ha
      cases a1 <;> cases a2 <;> by_cases hv : av = vi <;> simp_all [R12_op, R12s, Rmat]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR] at hent
  exact mul_left_cancel₀ (mul_ne_zero h1 h2) hent

/- The 4 Freezing Lemmas on `Bmat`! -/

lemma Bmat_head_true (n : ℕ) (x : Fin (n + 1) → E6) (y α β : E6)
    (vo : Vec (n + 1)) (vt : Vec n) :
    Bmat (n + 1) x y α β vo (Fin.cons true vt) =
      if vo 0 = true then
        sig (q * (y * (x 0)⁻¹)) * sig (y * x 0) *
          Bmat n (fun i => x i.succ) y α β (fun i => vo i.succ) vt
      else 0 := by
  simp only [Bmat, Umat, Matrix.of_apply, Fintype.sum_bool, Fin.cons_zero, Fin.cons_succ]
  cases hvo : vo 0 <;>
    simp only [Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add] <;>
    ring

lemma Bmat_head_false (n : ℕ) (x : Fin (n + 1) → E6) (y α β : E6)
    (vt : Vec n) (vi : Vec (n + 1)) :
    Bmat (n + 1) x y α β (Fin.cons false vt) vi =
      if vi 0 = false then
        sig (q * (y * x 0)) * sig (y * (x 0)⁻¹) *
          Bmat n (fun i => x i.succ) y α β vt (fun i => vi i.succ)
      else 0 := by
  simp only [Bmat, Umat, Matrix.of_apply, Fintype.sum_bool, Fin.cons_zero, Fin.cons_succ]
  cases hvi : vi 0 <;>
    simp only [Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add] <;>
    ring

lemma Umat_allF_zero : ∀ (n : ℕ) (x : Fin n → E6) (y α β : E6) (ho : Bool) (vo : Vec n),
    Umat n x y α β (ho, vo) (false, allF n) =
      if ho = false ∧ vo = allF n then
        (α * y + β * y⁻¹) *
          ∏ j : Fin n, sig (q * (y * (x j)⁻¹)) * sig (q * (y * x j))
      else 0
  | 0, _, y, α, β, ho, vo => by
    have hvo : vo = allF 0 := Subsingleton.elim vo (allF 0)
    cases ho <;> simp [Umat, Kmat, hvo]
  | n + 1, x, y, α, β, ho, vo => by
    rw [Umat]
    simp only [Matrix.of_apply, Fintype.sum_bool]
    have hIH : ∀ h2 : Bool,
        Umat n (fun i => x i.succ) y α β (h2, fun i => vo i.succ) (false, fun _ => false) =
        if h2 = false ∧ (fun (i : Fin n) => vo i.succ) = (fun _ => false) then
          (α * y + β * y⁻¹) *
            ∏ j : Fin n, sig (q * (y * (x j.succ)⁻¹)) * sig (q * (y * x j.succ))
        else 0 :=
      fun h2 => Umat_allF_zero n (fun i => x i.succ) y α β h2 (fun i => vo i.succ)
    change _ = if ho = false ∧ vo = (fun _ => false) then _ else 0
    cases ho <;> cases hvo0 : vo 0 <;>
      simp only [allF, Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
        true_and, ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add, hIH]
    · by_cases hvt : (fun i : Fin n => vo i.succ) = (fun _ => false)
      · have hvo_all : vo = (fun _ => false) := by
          funext i; refine Fin.cases hvo0 (fun j => congrFun hvt j) i
        rw [if_pos hvt, if_pos hvo_all, Fin.prod_univ_succ]
        ring
      · have hvo_ne : vo ≠ (fun _ => false) := fun h => hvt (funext fun j => congrFun h j.succ)
        rw [if_neg hvt, if_neg hvo_ne, mul_zero, zero_mul]
    · have hvo_ne : vo ≠ (fun _ => false) := fun h => by
        have := congrFun h 0; simp [hvo0] at this
      rw [if_neg hvo_ne]

lemma Bmat_top_freeze (n : ℕ) (x : Fin (n + 1) → E6) (y α β : E6)
    (hy : y ≠ 0) (hx0 : x 0 = y) (vo : Vec (n + 1)) :
    Bmat (n + 1) x y α β vo (allF (n + 1)) =
      if vo = Fin.cons true (allF n) then
        c * (α * y + β * y⁻¹) * sig (y ^ 2) *
          ∏ j : Fin n, sig (q * (y * (x j.succ)⁻¹)) * sig (q * (y * x j.succ))
      else 0 := by
  rw [Bmat, Matrix.of_apply, Umat]
  simp only [Matrix.of_apply, Fintype.sum_bool, hx0, mul_inv_cancel₀ hy]
  have hIH : ∀ h2 : Bool,
      Umat n (fun i => x i.succ) y α β (h2, fun i => vo i.succ) (false, fun _ => false) =
      if h2 = false ∧ (fun (i : Fin n) => vo i.succ) = (fun _ => false) then
        (α * y + β * y⁻¹) *
          ∏ j : Fin n, sig (q * (y * (x j.succ)⁻¹)) * sig (q * (y * x j.succ))
      else 0 :=
    fun h2 => Umat_allF_zero n (fun i => x i.succ) y α β h2 (fun i => vo i.succ)
  change _ = if vo = Fin.cons true (fun _ => false) then _ else 0
  cases hvo0 : vo 0 <;>
    simp only [allF, Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      true_and, ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add, sig_one, hIH]
  · have hne : vo ≠ Fin.cons true (fun _ => false) := fun h => by
      have := congrFun h 0; simp [hvo0] at this
    rw [if_neg hne]
  · by_cases hvt : (fun i : Fin n => vo i.succ) = (fun _ => false)
    · have heq : vo = Fin.cons true (fun _ => false) := by
        funext i; refine Fin.cases (by simp [hvo0]) (fun j => by simpa using congrFun hvt j) i
      rw [if_pos hvt, if_pos heq, sq, c]
      ring
    · have hne : vo ≠ Fin.cons true (fun _ => false) := fun h =>
        hvt (funext fun j => by simpa using congrFun h j.succ)
      rw [if_neg hvt, if_neg hne, mul_zero, zero_mul]

lemma Umat_allT_one : ∀ (n : ℕ) (x : Fin n → E6) (y α β : E6) (hi : Bool) (vi : Vec n),
    Umat n x y α β (true, allT n) (hi, vi) =
      if hi = true ∧ vi = allT n then
        (α * y⁻¹ + β * y) *
          ∏ j : Fin n, sig (q * (y * (x j)⁻¹)) * sig (q * (y * x j))
      else 0
  | 0, _, y, α, β, hi, vi => by
    have hvi : vi = allT 0 := Subsingleton.elim vi (allT 0)
    cases hi <;> simp [Umat, Kmat, hvi]
  | n + 1, x, y, α, β, hi, vi => by
    rw [Umat]
    simp only [Matrix.of_apply, Fintype.sum_bool]
    have hIH : ∀ h1 : Bool,
        Umat n (fun i => x i.succ) y α β (true, fun _ => true) (h1, fun i => vi i.succ) =
        if h1 = true ∧ (fun (i : Fin n) => vi i.succ) = (fun _ => true) then
          (α * y⁻¹ + β * y) *
            ∏ j : Fin n, sig (q * (y * (x j.succ)⁻¹)) * sig (q * (y * x j.succ))
        else 0 :=
      fun h1 => Umat_allT_one n (fun i => x i.succ) y α β h1 (fun i => vi i.succ)
    change _ = if hi = true ∧ vi = (fun _ => true) then _ else 0
    cases hi <;> cases hvi0 : vi 0 <;>
      simp only [allT, Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
        true_and, ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add, hIH]
    · have hvi_ne : vi ≠ (fun _ => true) := fun h => by
        have := congrFun h 0; simp [hvi0] at this
      rw [if_neg hvi_ne]
    · by_cases hvt : (fun i : Fin n => vi i.succ) = (fun _ => true)
      · have hvi_all : vi = (fun _ => true) := by
          funext i; refine Fin.cases hvi0 (fun j => congrFun hvt j) i
        rw [if_pos hvt, if_pos hvi_all, Fin.prod_univ_succ]
        ring
      · have hvi_ne : vi ≠ (fun _ => true) := fun h => hvt (funext fun j => congrFun h j.succ)
        rw [if_neg hvt, if_neg hvi_ne, mul_zero, zero_mul]

lemma Bmat_bot_freeze (n : ℕ) (x : Fin (n + 1) → E6) (y α β : E6)
    (hy : y ≠ 0) (hx0 : x 0 = y⁻¹) (vi : Vec (n + 1)) :
    Bmat (n + 1) x y α β (allT (n + 1)) vi =
      if vi = Fin.cons false (allT n) then
        c * (α * y⁻¹ + β * y) * sig (y ^ 2) *
          ∏ j : Fin n, sig (q * (y * (x j.succ)⁻¹)) * sig (q * (y * x j.succ))
      else 0 := by
  rw [Bmat, Matrix.of_apply, Umat]
  simp only [Matrix.of_apply, Fintype.sum_bool, hx0, mul_inv_cancel₀ hy, inv_inv]
  have hIH : ∀ h1 : Bool,
      Umat n (fun i => x i.succ) y α β (true, fun _ => true) (h1, fun i => vi i.succ) =
      if h1 = true ∧ (fun (i : Fin n) => vi i.succ) = (fun _ => true) then
        (α * y⁻¹ + β * y) *
          ∏ j : Fin n, sig (q * (y * (x j.succ)⁻¹)) * sig (q * (y * x j.succ))
      else 0 :=
    fun h1 => Umat_allT_one n (fun i => x i.succ) y α β h1 (fun i => vi i.succ)
  change _ = if vi = Fin.cons false (fun _ => true) then _ else 0
  cases hvi0 : vi 0 <;>
    simp only [allT, Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      true_and, ite_true, ite_false, zero_mul, mul_zero, add_zero, zero_add, sig_one, hIH]
  · by_cases hvt : (fun i : Fin n => vi i.succ) = (fun _ => true)
    · have heq : vi = Fin.cons false (fun _ => true) := by
        funext i; refine Fin.cases (by simp [hvi0]) (fun j => by simpa using congrFun hvt j) i
      rw [if_pos hvt, if_pos heq, sq, c]
      ring
    · have hne : vi ≠ Fin.cons false (fun _ => true) := fun h =>
        hvt (funext fun j => by simpa using congrFun h j.succ)
      rw [if_neg hvt, if_neg hne, mul_zero, zero_mul]
  · have hne : vi ≠ Fin.cons false (fun _ => true) := fun h => by
      have := congrFun h 0; simp [hvi0] at this
    rw [if_neg hne]

/- Partition function `Z_n` and its two freezing recursions! -/

def prodB (n : ℕ) (x : Fin n → E6) (α β : E6) : List E6 → Matrix (Vec n) (Vec n) E6
  | [] => 1
  | y :: ys => prodB n x α β ys * Bmat n x y α β

def Z_n (n : ℕ) (x y : Fin n → E6) (α β : E6) : E6 :=
  prodB n x α β (List.ofFn y) (allT n) (allF n)

lemma prodB_head_true (n : ℕ) (x : Fin (n + 1) → E6) (α β : E6) :
    ∀ (ys : List E6) (vo : Vec (n + 1)) (vt : Vec n),
      prodB (n + 1) x α β ys vo (Fin.cons true vt) =
        if vo 0 = true then
          (ys.map fun y => sig (q * (y * (x 0)⁻¹)) * sig (y * x 0)).prod *
            prodB n (fun i => x i.succ) α β ys (fun i => vo i.succ) vt
        else 0
  | [], vo, vt => by
    simp only [prodB, Matrix.one_apply, List.map_nil, List.prod_nil, one_mul]
    by_cases hvo : vo 0 = true
    · rw [if_pos hvo]
      have heq : vo = Fin.cons true vt ↔ (fun i : Fin n => vo i.succ) = vt := by
        constructor
        · intro h; funext i; simpa using congrFun h i.succ
        · intro h; funext i; refine Fin.cases (by simp [hvo]) (fun j => by simpa using congrFun h j) i
      simp [heq]
    · rw [if_neg hvo]
      have hne : vo ≠ Fin.cons true vt := fun h => hvo (by simpa using congrFun h 0)
      simp [hne]
  | y :: ys, vo, vt => by
    simp only [prodB, Matrix.mul_apply, List.map_cons, List.prod_cons]
    have hB := fun vm => Bmat_head_true n x y α β vm vt
    simp_rw [hB]
    have hsplit : (∑ vm : Vec (n + 1),
        prodB (n + 1) x α β ys vo vm *
          if vm 0 = true then
            sig (q * (y * (x 0)⁻¹)) * sig (y * x 0) *
              Bmat n (fun i => x i.succ) y α β (fun i => vm i.succ) vt
          else 0) =
        ∑ vmt : Vec n,
          prodB (n + 1) x α β ys vo (Fin.cons true vmt) *
            (sig (q * (y * (x 0)⁻¹)) * sig (y * x 0) *
              Bmat n (fun i => x i.succ) y α β vmt vt) := by
      let e : Bool × Vec n ≃ Vec (n + 1) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun v => (v 0, fun i => v i.succ)
          left_inv := fun ⟨b, v⟩ => by ext <;> simp
          right_inv := fun v => by funext i; refine Fin.cases ?_ ?_ i <;> simp }
      rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type, Fintype.sum_bool]
      simp [e]
    rw [hsplit]
    simp_rw [prodB_head_true n x α β ys vo]
    by_cases hvo : vo 0 = true
    · simp only [hvo, ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro vmt _; ring
    · simp [hvo]

lemma prodB_head_false (n : ℕ) (x : Fin (n + 1) → E6) (α β : E6) :
    ∀ (ys : List E6) (vt : Vec n) (vi : Vec (n + 1)),
      prodB (n + 1) x α β ys (Fin.cons false vt) vi =
        if vi 0 = false then
          (ys.map fun y => sig (q * (y * x 0)) * sig (y * (x 0)⁻¹)).prod *
            prodB n (fun i => x i.succ) α β ys vt (fun i => vi i.succ)
        else 0
  | [], vt, vi => by
    simp only [prodB, Matrix.one_apply, List.map_nil, List.prod_nil, one_mul]
    by_cases hvi : vi 0 = false
    · rw [if_pos hvi]
      have heq : Fin.cons false vt = vi ↔ vt = (fun i : Fin n => vi i.succ) := by
        constructor
        · intro h; funext i; simpa using congrFun h i.succ
        · intro h; funext i; refine Fin.cases (by simp [hvi]) (fun j => by simpa using congrFun h j) i
      simp [heq]
    · rw [if_neg hvi]
      have hne : Fin.cons false vt ≠ vi := fun h => hvi (by simpa using (congrFun h 0).symm)
      simp [hne]
  | y :: ys, vt, vi => by
    simp only [prodB, Matrix.mul_apply, List.map_cons, List.prod_cons]
    simp_rw [prodB_head_false n x α β ys vt]
    have hsplit : (∑ vm : Vec (n + 1),
        (if vm 0 = false then
          (ys.map fun y => sig (q * (y * x 0)) * sig (y * (x 0)⁻¹)).prod *
            prodB n (fun i => x i.succ) α β ys vt (fun i => vm i.succ)
        else 0) * Bmat (n + 1) x y α β vm vi) =
        ∑ vmt : Vec n,
          ((ys.map fun y => sig (q * (y * x 0)) * sig (y * (x 0)⁻¹)).prod *
            prodB n (fun i => x i.succ) α β ys vt vmt) *
          Bmat (n + 1) x y α β (Fin.cons false vmt) vi := by
      let e : Bool × Vec n ≃ Vec (n + 1) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun v => (v 0, fun i => v i.succ)
          left_inv := fun ⟨b, v⟩ => by ext <;> simp
          right_inv := fun v => by funext i; refine Fin.cases ?_ ?_ i <;> simp }
      rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type, Fintype.sum_bool]
      simp [e]
    rw [hsplit]
    simp_rw [Bmat_head_false n x y α β]
    by_cases hvi : vi 0 = false
    · simp only [hvi, ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro vmt _; ring
    · simp [hvi]

theorem Z_n_freeze_top_0 (n : ℕ) (x y : Fin (n + 1) → E6) (α β : E6)
    (hy0 : y 0 ≠ 0) (hx0 : x 0 = y 0) :
    Z_n (n + 1) x y α β =
      c * (α * y 0 + β * (y 0)⁻¹) * sig ((y 0) ^ 2) *
      (∏ j : Fin n, sig (q * (y 0 * (x j.succ)⁻¹)) * sig (q * (y 0 * x j.succ))) *
      (∏ k : Fin n, sig (q * (y k.succ * (y 0)⁻¹)) * sig (y k.succ * y 0)) *
      Z_n n (fun i => x i.succ) (fun k => y k.succ) α β := by
  unfold Z_n
  rw [List.ofFn_succ, prodB, Matrix.mul_apply]
  simp_rw [Bmat_top_freeze n x (y 0) α β hy0 hx0]
  rw [Finset.sum_eq_single (Fin.cons true (allF n))]
  · rw [if_pos rfl, prodB_head_true]
    have hT0 : allT (n + 1) 0 = true := rfl
    have hTt : (fun i : Fin n => allT (n + 1) i.succ) = allT n := rfl
    rw [if_pos hT0, hTt, hx0]
    have hlist : ((List.ofFn fun i : Fin n => y i.succ).map
        fun yk => sig (q * (yk * (y 0)⁻¹)) * sig (yk * y 0)).prod =
        ∏ k : Fin n, sig (q * (y k.succ * (y 0)⁻¹)) * sig (y k.succ * y 0) := by
      rw [List.map_ofFn, List.prod_ofFn]; rfl
    rw [hlist]; ring
  · intro vm _ hvm; simp [hvm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma prodB_append (n : ℕ) (x : Fin n → E6) (α β : E6) (l1 l2 : List E6) :
    prodB n x α β (l1 ++ l2) = prodB n x α β l2 * prodB n x α β l1 := by
  induction l1 with
  | nil => simp [prodB]
  | cons a l1 ih => simp [prodB, ih, Matrix.mul_assoc]

theorem Z_n_freeze_bot_last (n : ℕ) (x y : Fin (n + 1) → E6) (α β : E6)
    (hyl : y (Fin.last n) ≠ 0) (hx0 : x 0 = (y (Fin.last n))⁻¹) :
    Z_n (n + 1) x y α β =
      c * (α * (y (Fin.last n))⁻¹ + β * y (Fin.last n)) * sig ((y (Fin.last n)) ^ 2) *
      (∏ j : Fin n, sig (q * (y (Fin.last n) * (x j.succ)⁻¹)) * sig (q * (y (Fin.last n) * x j.succ))) *
      (∏ k : Fin n, sig (q * (y k.castSucc * (y (Fin.last n))⁻¹)) * sig (y k.castSucc * y (Fin.last n))) *
      Z_n n (fun i => x i.succ) (fun k => y k.castSucc) α β := by
  unfold Z_n
  rw [List.ofFn_succ', List.concat_eq_append, prodB_append, prodB, prodB, Matrix.one_mul,
      Matrix.mul_apply]
  simp_rw [Bmat_bot_freeze n x (y (Fin.last n)) α β hyl hx0]
  rw [Finset.sum_eq_single (Fin.cons false (allT n))]
  · rw [if_pos rfl, prodB_head_false]
    have hF0 : allF (n + 1) 0 = false := rfl
    have hFt : (fun i : Fin n => allF (n + 1) i.succ) = allF n := rfl
    rw [if_pos hF0, hFt, hx0, inv_inv]
    have hlist : ((List.ofFn fun k : Fin n => y k.castSucc).map
        fun yk => sig (q * (yk * (y (Fin.last n))⁻¹)) * sig (yk * y (Fin.last n))).prod =
        ∏ k : Fin n, sig (q * (y k.castSucc * (y (Fin.last n))⁻¹)) * sig (y k.castSucc * y (Fin.last n)) := by
      rw [List.map_ofFn, List.prod_ofFn]; rfl
    rw [hlist]; ring
  · intro vm _ hvm; simp [hvm]
  · intro h; exact absurd (Finset.mem_univ _) h


end Mod4


section ModA
open Finset E6
open scoped Classical

lemma psum_cons_succ {m : ℕ} (x : Fin 3) (v : Fin m → Fin 3) (k : ℕ) :
    psum (Fin.cons x v) (k + 1) = val3 x + psum v k := by
  unfold psum
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.zero_lt_succ, ite_true, Fin.cons_zero, Fin.val_succ,
    Nat.add_lt_add_iff_right, Fin.cons_succ]

/- Single-row transfer matrices at z = q -/

def Sbot : (n : ℕ) → Bool → Bool → Matrix (Vec n) (Vec n) E6
  | 0, ho, hi => Matrix.of fun _ _ => if ho = hi then 1 else 0
  | n + 1, ho, hi => Matrix.of fun vo vi =>
      ∑ hm : Bool, Rmat q (vo 0) ho (vi 0) hm * Sbot n hm hi (fun i => vo i.succ) (fun i => vi i.succ)

def Stop : (n : ℕ) → Bool → Bool → Matrix (Vec n) (Vec n) E6
  | 0, ho, hi => Matrix.of fun _ _ => if ho = hi then 1 else 0
  | n + 1, ho, hi => Matrix.of fun vo vi =>
      ∑ hm : Bool, Stop n ho hm (fun i => vo i.succ) (fun i => vi i.succ) * Rmat q (vo 0) hm (vi 0) hi

lemma Umat_at_special : ∀ (n : ℕ) (ho hi : Bool) (vo vi : Vec n),
    Umat n (fun _ => 1) q (-q) q⁻¹ (ho, vo) (hi, vi) =
      (-c) * ∑ vm : Vec n, Sbot n ho false vo vm * Stop n false hi vm vi
  | 0, ho, hi, vo, vi => by
    simp only [Umat, Matrix.of_apply, Kmat_at_q, Sbot, Stop, Fintype.sum_unique]
    cases ho <;> cases hi <;> simp
  | n + 1, ho, hi, vo, vi => by
    rw [Umat, Matrix.of_apply]
    simp only [mul_one, inv_one]
    have hIH : ∀ h2 h1 : Bool,
        Umat n (fun _ => 1) q (-q) q⁻¹ (h2, fun i => vo i.succ) (h1, fun i => vi i.succ) =
        (-c) * ∑ vmt : Vec n,
          Sbot n h2 false (fun i => vo i.succ) vmt * Stop n false h1 vmt (fun i => vi i.succ) :=
      fun h2 h1 => Umat_at_special n h2 h1 (fun i => vo i.succ) (fun i => vi i.succ)
    simp_rw [hIH]
    let e : Bool × Vec n ≃ Vec (n + 1) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun v => (v 0, fun i => v i.succ)
        left_inv := fun ⟨_, _⟩ => by ext <;> simp
        right_inv := fun v => by funext i; refine Fin.cases ?_ ?_ i <;> simp }
    symm
    rw [← Fintype.sum_equiv e _ _ (fun _ => rfl), Fintype.sum_prod_type]
    simp only [e, Equiv.coe_fn_mk, Sbot, Stop, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v0m _
    have hL : (-c) * ∑ vmt : Vec n,
        (∑ h2 : Bool, Rmat q (vo 0) ho v0m h2 * Sbot n h2 false (fun i => vo i.succ) vmt) *
        (∑ h1 : Bool, Stop n false h1 vmt (fun i => vi i.succ) * Rmat q v0m h1 (vi 0) hi) =
        ∑ h1 : Bool, ∑ h2 : Bool, ∑ vmt : Vec n,
          Rmat q (vo 0) ho v0m h2 *
            ((-c) * (Sbot n h2 false (fun i => vo i.succ) vmt *
              Stop n false h1 vmt (fun i => vi i.succ))) *
          Rmat q v0m h1 (vi 0) hi := by
      rw [Finset.mul_sum]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      trans ∑ h2 : Bool, ∑ h1 : Bool, ∑ vmt : Vec n,
          Rmat q (vo 0) ho v0m h2 *
            ((-c) * (Sbot n h2 false (fun i => vo i.succ) vmt *
              Stop n false h1 vmt (fun i => vi i.succ))) *
          Rmat q v0m h1 (vi 0) hi
      · apply Finset.sum_congr rfl; intro h2 _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro h1 _
        apply Finset.sum_congr rfl; intro vmt _
        ring
      · exact Finset.sum_comm
    rw [hL]
    apply Finset.sum_congr rfl; intro h1 _
    apply Finset.sum_congr rfl; intro h2 _
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]

/- Evaluation of `Sbot` and `Stop` in terms of `diff3` and `psum` -/

def diff3 {n : ℕ} (vo vi : Vec n) : Fin n → Fin 3 :=
  fun j => ⟨(vo j).toNat + 1 - (vi j).toNat, by cases vo j <;> cases vi j <;> simp⟩

lemma val3_diff3 {n : ℕ} (vo vi : Vec n) (j : Fin n) :
    val3 (diff3 vo vi j) = ((vo j).toNat : ℤ) - ((vi j).toNat : ℤ) := by
  simp only [val3, diff3]
  cases vo j <;> cases vi j <;> simp

lemma Sbot_eval : ∀ (n : ℕ) (ho hi : Bool) (vo vi : Vec n),
    Sbot n ho hi vo vi =
      if ((ho.toNat : ℤ) + psum (diff3 vo vi) n = (hi.toNat : ℤ) ∧
          ∀ k : Fin (n + 1), (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 0 ∨
                             (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 1)
      then c ^ n else 0
  | 0, ho, hi, vo, vi => by
    simp only [Sbot, Matrix.of_apply, pow_zero, psum_zero, add_zero]
    have h01 : ∀ k : Fin 1, (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 0 ∨
        (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 1 := by
      intro k
      have hk : k.val = 0 := by omega
      rw [hk, psum_zero, add_zero]; cases ho <;> simp
    have heq : ((ho.toNat : ℤ) = (hi.toNat : ℤ)) ↔ ho = hi := by
      cases ho <;> cases hi <;> simp
    by_cases h : ho = hi
    · rw [if_pos h, if_pos ⟨heq.2 h, h01⟩]
    · rw [if_neg h, if_neg (fun hp => h (heq.1 hp.1))]
  | n + 1, ho, hi, vo, vi => by
    rw [Sbot, Matrix.of_apply]
    have hIH := fun hm => Sbot_eval n hm hi (fun i => vo i.succ) (fun i => vi i.succ)
    simp_rw [hIH, Rmat_at_q]
    have hdiff : diff3 vo vi = Fin.cons (diff3 vo vi 0) (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) := by
      funext j; refine Fin.cases ?_ ?_ j <;> simp [diff3]
    have hsum_step : ∀ k : ℕ, (ho.toNat : ℤ) + psum (diff3 vo vi) (k + 1) =
        ((ho.toNat : ℤ) + ((vo 0).toNat : ℤ) - ((vi 0).toNat : ℤ)) +
        psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) k := by
      intro k
      rw [hdiff, psum_cons_succ, val3_diff3]
      ring
    rw [Fintype.sum_bool]
    by_cases hcase : (ho.toNat : ℤ) + ((vo 0).toNat : ℤ) - ((vi 0).toNat : ℤ) = 0 ∨
                     (ho.toNat : ℤ) + ((vo 0).toNat : ℤ) - ((vi 0).toNat : ℤ) = 1
    · rcases hcase with h0 | h1
      · have hT : ¬ ((vo 0).toNat + ho.toNat = (vi 0).toNat + true.toNat) := by
          revert h0; cases vo 0 <;> cases ho <;> cases vi 0 <;> simp
        have hF : (vo 0).toNat + ho.toNat = (vi 0).toNat + false.toNat := by
          revert h0; cases vo 0 <;> cases ho <;> cases vi 0 <;> simp
        rw [if_neg hT, zero_mul, zero_add, if_pos hF]
        have hcond : ((false.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) n = (hi.toNat : ℤ) ∧
            ∀ k : Fin (n + 1), (false.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) k.val = 0 ∨
                               (false.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) k.val = 1) ↔
            ((ho.toNat : ℤ) + psum (diff3 vo vi) (n + 1) = (hi.toNat : ℤ) ∧
            ∀ k : Fin (n + 2), (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 0 ∨
                               (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 1) := by
          rw [hsum_step n, h0]; simp only [Bool.toNat_false, Nat.cast_zero]
          constructor
          · rintro ⟨htot, hall⟩
            refine ⟨htot, fun k => ?_⟩
            refine Fin.cases ?_ (fun k' => ?_) k
            · rw [Fin.val_zero, psum_zero, add_zero]; cases ho <;> simp
            · rw [Fin.val_succ, hsum_step k'.val, h0]; exact hall k'
          · rintro ⟨htot, hall⟩
            refine ⟨htot, fun k => ?_⟩
            have := hall k.succ
            rw [Fin.val_succ, hsum_step k.val, h0] at this
            exact this
        by_cases hc : (false.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) n = (hi.toNat : ℤ) ∧
            ∀ k : Fin (n + 1), (false.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) k.val = 0 ∨
                               (false.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) k.val = 1
        · rw [if_pos hc, if_pos (hcond.1 hc), pow_succ']
        · rw [if_neg hc, if_neg (fun h => hc (hcond.2 h)), mul_zero]
      · have hT : (vo 0).toNat + ho.toNat = (vi 0).toNat + true.toNat := by
          revert h1; cases vo 0 <;> cases ho <;> cases vi 0 <;> simp
        have hF : ¬ ((vo 0).toNat + ho.toNat = (vi 0).toNat + false.toNat) := by
          revert h1; cases vo 0 <;> cases ho <;> cases vi 0 <;> simp
        rw [if_pos hT, if_neg hF, zero_mul, add_zero]
        have hcond : ((true.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) n = (hi.toNat : ℤ) ∧
            ∀ k : Fin (n + 1), (true.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) k.val = 0 ∨
                               (true.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) k.val = 1) ↔
            ((ho.toNat : ℤ) + psum (diff3 vo vi) (n + 1) = (hi.toNat : ℤ) ∧
            ∀ k : Fin (n + 2), (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 0 ∨
                               (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 1) := by
          rw [hsum_step n, h1]; simp only [Bool.toNat_true, Nat.cast_one]
          constructor
          · rintro ⟨htot, hall⟩
            refine ⟨htot, fun k => ?_⟩
            refine Fin.cases ?_ (fun k' => ?_) k
            · rw [Fin.val_zero, psum_zero, add_zero]; cases ho <;> simp
            · rw [Fin.val_succ, hsum_step k'.val, h1]; exact hall k'
          · rintro ⟨htot, hall⟩
            refine ⟨htot, fun k => ?_⟩
            have := hall k.succ
            rw [Fin.val_succ, hsum_step k.val, h1] at this
            exact this
        by_cases hc : (true.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) n = (hi.toNat : ℤ) ∧
            ∀ k : Fin (n + 1), (true.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) k.val = 0 ∨
                               (true.toNat : ℤ) + psum (diff3 (fun i => vo i.succ) (fun i => vi i.succ)) k.val = 1
        · rw [if_pos hc, if_pos (hcond.1 hc), pow_succ']
        · rw [if_neg hc, if_neg (fun h => hc (hcond.2 h)), mul_zero]
    · have hT : ¬ ((vo 0).toNat + ho.toNat = (vi 0).toNat + true.toNat) := by
        revert hcase; cases vo 0 <;> cases ho <;> cases vi 0 <;> simp
      have hF : ¬ ((vo 0).toNat + ho.toNat = (vi 0).toNat + false.toNat) := by
        revert hcase; cases vo 0 <;> cases ho <;> cases vi 0 <;> simp
      rw [if_neg hT, if_neg hF, zero_mul, zero_mul, add_zero]
      have hfail : ¬ ((ho.toNat : ℤ) + psum (diff3 vo vi) (n + 1) = (hi.toNat : ℤ) ∧
          ∀ k : Fin (n + 2), (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 0 ∨
                             (ho.toNat : ℤ) + psum (diff3 vo vi) k.val = 1) := by
        rintro ⟨_, hall⟩
        have h1 := hall ⟨1, by omega⟩
        dsimp only at h1
        rw [hsum_step 0, psum_zero, add_zero] at h1
        exact hcase h1
      rw [if_neg hfail]

lemma Stop_eq_Sbot : ∀ (n : ℕ) (ho hi : Bool) (vo vi : Vec n),
    Stop n ho hi vo vi = Sbot n (!hi) (!ho) vo vi
  | 0, ho, hi, vo, vi => by
    simp only [Stop, Sbot, Matrix.of_apply]
    cases ho <;> cases hi <;> simp
  | n + 1, ho, hi, vo, vi => by
    rw [Stop, Sbot, Matrix.of_apply, Matrix.of_apply]
    rw [Fintype.sum_bool, Fintype.sum_bool]
    have hIH_t : Stop n ho true (fun i => vo i.succ) (fun i => vi i.succ) =
        Sbot n false (!ho) (fun i => vo i.succ) (fun i => vi i.succ) :=
      Stop_eq_Sbot n ho true (fun i => vo i.succ) (fun i => vi i.succ)
    have hIH_f : Stop n ho false (fun i => vo i.succ) (fun i => vi i.succ) =
        Sbot n true (!ho) (fun i => vo i.succ) (fun i => vi i.succ) :=
      Stop_eq_Sbot n ho false (fun i => vo i.succ) (fun i => vi i.succ)
    rw [hIH_t, hIH_f, Rmat_at_q, Rmat_at_q, Rmat_at_q, Rmat_at_q]
    have hswap : ∀ b : Bool,
        ((vo 0).toNat + b.toNat = (vi 0).toNat + hi.toNat) ↔
        ((vo 0).toNat + (!hi).toNat = (vi 0).toNat + (!b).toNat) := by
      intro b; cases vo 0 <;> cases vi 0 <;> cases hi <;> cases b <;> simp
    simp only [hswap true, hswap false, Bool.not_true, Bool.not_false]
    ring

lemma Bmat_at_special (n : ℕ) (vo vi : Vec n) :
    Bmat n (fun _ => 1) q (-q) q⁻¹ vo vi =
      ((-c) * c ^ (2 * n)) *
        ∑ vm : Vec n,
          (if LineOKSum n 0 (diff3 vo vm) then (1 : E6) else 0) *
          (if LineOKSum n 1 (diff3 vm vi) then (1 : E6) else 0) := by
  rw [Bmat, Matrix.of_apply, Umat_at_special]
  simp_rw [Stop_eq_Sbot, Sbot_eval]
  simp only [Bool.not_true, Bool.not_false, Bool.toNat_false, Bool.toNat_true, Nat.cast_zero,
    Nat.cast_one, zero_add]
  rw [Finset.mul_sum]
  have hpow : (-c) * c ^ (2 * n) = (-c) * (c ^ n * c ^ n) := by rw [← pow_add, two_mul]
  rw [hpow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro vm _
  have h1 : (if psum (diff3 vo vm) n = 0 ∧ ∀ k : Fin (n + 1), psum (diff3 vo vm) k.val = 0 ∨ psum (diff3 vo vm) k.val = 1 then c ^ n else 0) =
      if LineOKSum n 0 (diff3 vo vm) then c ^ n else 0 := by congr
  have h2 : (if psum (diff3 vm vi) n = 1 ∧ ∀ k : Fin (n + 1), psum (diff3 vm vi) k.val = 0 ∨ psum (diff3 vm vi) k.val = 1 then c ^ n else 0) =
      if LineOKSum n 1 (diff3 vm vi) then c ^ n else 0 := by congr
  rw [h1, h2]
  split_ifs <;> ring

/- Path counting bijection for `prodB` at special values vs `HalfMat n` -/

lemma toNat_of_decide_eq {z : ℤ} {b : Bool} (hz : z = 0 ∨ z = 1) (hd : decide (z = 1) = b) :
    z = (b.toNat : ℤ) := by
  rcases hz with rfl | rfl <;> simp at hd <;> subst hd <;> simp

def ValidBlock (n k : ℕ) (vi vo : Vec n) : Set (Fin (2 * k) → Fin n → Fin 3) :=
  {A | (∀ r, LineOKSum n (if r.val % 2 = 0 then 1 else 0) (A r)) ∧
       ∀ c, ((vi c).toNat : ℤ) + psum (fun r => A r c) (2 * k) = ((vo c).toNat : ℤ) ∧
            ∀ t : Fin (2 * k + 1),
              ((vi c).toNat : ℤ) + psum (fun r => A r c) t.val = 0 ∨
              ((vi c).toNat : ℤ) + psum (fun r => A r c) t.val = 1}

lemma validBlock_eq_halfMat (n : ℕ) : ValidBlock n n (allF n) (allT n) = HalfMat n := by
  ext A
  simp only [ValidBlock, HalfMat, Set.mem_ofPred_eq, allF, allT, Bool.toNat_false, Bool.toNat_true,
    Nat.cast_zero, Nat.cast_one, zero_add, LineOK]

lemma prodB_replicate_special (n : ℕ) : ∀ (k : ℕ) (vo vi : Vec n),
    prodB n (fun _ => 1) (-q) q⁻¹ (List.replicate k q) vo vi =
      ((-c) * c ^ (2 * n)) ^ k * ((ValidBlock n k vi vo).ncard : E6)
  | 0, vo, vi => by
    simp only [List.replicate_zero, prodB, Matrix.one_apply, pow_zero, one_mul]
    by_cases h : vo = vi
    · subst h
      rw [if_pos rfl]
      have hcard : (ValidBlock n 0 vo vo).ncard = 1 := by
        have huniv : ValidBlock n 0 vo vo = Set.univ := by
          ext A; simp only [ValidBlock, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          refine ⟨fun r => Fin.elim0 r, fun c => ⟨by simp [psum_zero], fun t => ?_⟩⟩
          have ht : t.val = 0 := by omega
          rw [ht, psum_zero, add_zero]; cases vo c <;> simp
        rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
            pow_zero]
      rw [hcard]; simp
    · rw [if_neg h]
      have hemp : ValidBlock n 0 vi vo = ∅ := by
        ext A; simp only [ValidBlock, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, hcol⟩
        apply h
        funext c
        have hc := (hcol c).1
        simp only [mul_zero, psum_zero, add_zero] at hc
        revert hc; cases vo c <;> cases vi c <;> simp
      rw [hemp, Set.ncard_empty]; simp
  | k + 1, vo, vi => by
    rw [List.replicate_succ, prodB, Matrix.mul_apply]
    simp_rw [prodB_replicate_special n k, Bmat_at_special n]
    have hfact : (∑ vm : Vec n,
        ((-c) * c ^ (2 * n)) ^ k * ((ValidBlock n k vm vo).ncard : E6) *
        (((-c) * c ^ (2 * n)) *
          ∑ vh : Vec n,
            (if LineOKSum n 0 (diff3 vm vh) then (1 : E6) else 0) *
            (if LineOKSum n 1 (diff3 vh vi) then (1 : E6) else 0))) =
        ((-c) * c ^ (2 * n)) ^ (k + 1) *
        ((∑ vm : Vec n, ∑ vh : Vec n,
          (ValidBlock n k vm vo).ncard *
          ((if LineOKSum n 0 (diff3 vm vh) then 1 else 0) *
           (if LineOKSum n 1 (diff3 vh vi) then 1 else 0)) : ℕ) : E6) := by
      rw [pow_succ, Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro vm _
      rw [Nat.cast_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro vh _
      split_ifs <;> simp <;> ring
    rw [hfact]
    congr 1
    apply congrArg (Nat.cast (R := E6))
    let splitA (A : Fin (2 * (k + 1)) → Fin n → Fin 3) :
        (Vec n × Vec n) × (Fin (2 * k) → Fin n → Fin 3) :=
      ((fun c => decide (((vi c).toNat : ℤ) + val3 (A ⟨0, by omega⟩ c) + val3 (A ⟨1, by omega⟩ c) = 1),
        fun c => decide (((vi c).toNat : ℤ) + val3 (A ⟨0, by omega⟩ c) = 1)),
       fun r c => A ⟨r.val + 2, by omega⟩ c)
    let joinA (vm vh : Vec n) (B : Fin (2 * k) → Fin n → Fin 3) :
        Fin (2 * (k + 1)) → Fin n → Fin 3 :=
      fun r c =>
        if hr0 : r.val = 0 then diff3 vh vi c
        else if hr1 : r.val = 1 then diff3 vm vh c
        else B ⟨r.val - 2, by omega⟩ c
    have hsplit_vals : ∀ (A : Fin (2 * (k + 1)) → Fin n → Fin 3) (vm vh : Vec n),
        A ∈ ValidBlock n (k + 1) vi vo → (splitA A).1 = (vm, vh) →
        (∀ c, ((vi c).toNat : ℤ) + val3 (A ⟨0, by omega⟩ c) = ((vh c).toNat : ℤ)) ∧
        (∀ c, ((vi c).toNat : ℤ) + val3 (A ⟨0, by omega⟩ c) + val3 (A ⟨1, by omega⟩ c) = ((vm c).toNat : ℤ)) := by
      intro A vm vh hA hpair
      constructor
      · intro c
        have h1 := (hA.2 c).2 ⟨1, by omega⟩
        dsimp only at h1
        rw [psum_succ _ 0 (by omega), psum_zero, zero_add] at h1
        exact toNat_of_decide_eq h1 (congrFun (congrArg Prod.snd hpair) c)
      · intro c
        have h2 := (hA.2 c).2 ⟨2, by omega⟩
        dsimp only at h2
        rw [psum_succ _ 1 (by omega), psum_succ _ 0 (by omega), psum_zero, zero_add, ← add_assoc] at h2
        exact toNat_of_decide_eq h2 (congrFun (congrArg Prod.fst hpair) c)
    have hfin : (ValidBlock n (k + 1) vi vo).ncard =
        (Finset.univ.filter (fun A => A ∈ ValidBlock n (k + 1) vi vo)).card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1; ext A; simp
    rw [hfin]
    have hcard_part : ∀ vm vh : Vec n,
        (Finset.univ.filter (fun A => A ∈ ValidBlock n (k + 1) vi vo ∧
          (splitA A).1 = (vm, vh))).card =
        (ValidBlock n k vm vo).ncard *
          ((if LineOKSum n 0 (diff3 vm vh) then 1 else 0) *
           (if LineOKSum n 1 (diff3 vh vi) then 1 else 0)) := by
      intro vm vh
      by_cases hok : LineOKSum n 0 (diff3 vm vh) ∧ LineOKSum n 1 (diff3 vh vi)
      · rw [if_pos hok.1, if_pos hok.2, mul_one, mul_one]
        rw [Set.ncard_eq_toFinset_card']
        refine Finset.card_bij (fun A _ => (splitA A).2) ?_ ?_ ?_
        · intro A hA
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset] at hA ⊢
          have ⟨_, hvm⟩ := hsplit_vals A vm vh hA.1 hA.2
          have hshift : ∀ c (t : ℕ), t ≤ 2 * k →
              ((vm c).toNat : ℤ) + psum (fun (r : Fin (2 * k)) => A ⟨r.val + 2, by omega⟩ c) t =
              ((vi c).toNat : ℤ) + psum (fun r => A r c) (t + 2) := by
            intro c t
            induction t with
            | zero =>
              intro _
              rw [psum_zero, add_zero, psum_succ _ 1 (by omega), psum_succ _ 0 (by omega),
                psum_zero, zero_add, ← hvm c]; ring
            | succ t ih =>
              intro ht
              rw [psum_succ (fun (r : Fin (2 * k)) => A ⟨r.val + 2, by omega⟩ c) t (by omega),
                  psum_succ (fun r => A r c) (t + 2) (by omega), ← add_assoc, ih (by omega)]
              ring
          refine ⟨fun r => ?_, fun c => ⟨?_, fun t => ?_⟩⟩
          · have hr := hA.1.1 ⟨r.val + 2, by omega⟩
            simpa [Nat.add_mod] using hr
          · rw [hshift c (2 * k) le_rfl]; exact (hA.1.2 c).1
          · rw [hshift c t.val (by omega)]; exact (hA.1.2 c).2 ⟨t.val + 2, by omega⟩
        · intro A1 hA1 A2 hA2 htail
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA1 hA2
          have ⟨hvh1, hvm1⟩ := hsplit_vals A1 vm vh hA1.1 hA1.2
          have ⟨hvh2, hvm2⟩ := hsplit_vals A2 vm vh hA2.1 hA2.2
          funext r c
          by_cases hr0 : r.val = 0
          · have hreq : r = ⟨0, by omega⟩ := Fin.ext hr0
            rw [hreq]
            have heq : val3 (A1 ⟨0, by omega⟩ c) = val3 (A2 ⟨0, by omega⟩ c) := by
              linarith [hvh1 c, hvh2 c]
            unfold val3 at heq; exact Fin.ext (by omega)
          · by_cases hr1 : r.val = 1
            · have hreq : r = ⟨1, by omega⟩ := Fin.ext hr1
              rw [hreq]
              have heq : val3 (A1 ⟨1, by omega⟩ c) = val3 (A2 ⟨1, by omega⟩ c) := by
                linarith [hvh1 c, hvh2 c, hvm1 c, hvm2 c]
              unfold val3 at heq; exact Fin.ext (by omega)
            · have ht := congrFun (congrFun htail ⟨r.val - 2, by omega⟩) c
              dsimp [splitA] at ht
              have hreq : (⟨r.val - 2 + 2, by omega⟩ : Fin (2 * (k + 1))) = r := Fin.ext (by dsimp; omega)
              rw [hreq] at ht; exact ht
        · intro B hB
          simp only [Set.mem_toFinset] at hB
          refine ⟨joinA vm vh B, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hcol_shift : ∀ c (t : ℕ), t ≤ 2 * k →
                ((vi c).toNat : ℤ) + psum (fun r => joinA vm vh B r c) (t + 2) =
                ((vm c).toNat : ℤ) + psum (fun r => B r c) t := by
              intro c t
              induction t with
              | zero =>
                intro _
                rw [psum_zero, add_zero, psum_succ _ 1 (by omega), psum_succ _ 0 (by omega),
                  psum_zero, zero_add]
                simp only [joinA, dite_true, show (1 : ℕ) ≠ 0 by omega, dite_false, val3_diff3]
                ring
              | succ t ih =>
                intro ht
                rw [psum_succ (fun r => joinA vm vh B r c) (t + 2) (by omega),
                    psum_succ (fun r => B r c) t (by omega), ← add_assoc, ih (by omega)]
                have h1 : t + 2 ≠ 0 := by omega
                have h2 : t + 2 ≠ 1 := by omega
                simp only [joinA, h1, h2, dite_false, Nat.add_sub_cancel]
                ring
            refine ⟨⟨fun r => ?_, fun c => ⟨?_, fun t => ?_⟩⟩, ?_⟩
            · by_cases hr0 : r.val = 0
              · have heq : joinA vm vh B r = diff3 vh vi := by
                  funext c; unfold joinA; rw [dif_pos hr0]
                rw [heq, hr0]; simpa using hok.2
              · by_cases hr1 : r.val = 1
                · have heq : joinA vm vh B r = diff3 vm vh := by
                    funext c; unfold joinA; rw [dif_neg hr0, dif_pos hr1]
                  rw [heq, hr1]; simpa using hok.1
                · have heq : joinA vm vh B r = B ⟨r.val - 2, by omega⟩ := by
                    funext c; unfold joinA; rw [dif_neg hr0, dif_neg hr1]
                  rw [heq]
                  have hr := hB.1 ⟨r.val - 2, by omega⟩
                  have hmod : (r.val - 2) % 2 = r.val % 2 := by omega
                  simpa [hmod] using hr
            · have h2k : 2 * (k + 1) = 2 * k + 2 := by omega
              conv_lhs => arg 2; arg 2; rw [h2k]
              rw [hcol_shift c (2 * k) le_rfl]
              exact (hB.2 c).1
            · rcases t with ⟨t, ht⟩
              match t with
              | 0 => rw [psum_zero, add_zero]; cases vi c <;> simp
              | 1 =>
                rw [psum_succ _ 0 (by omega), psum_zero, zero_add]
                simp only [joinA, dite_true, val3_diff3]
                cases vh c <;> simp
              | t + 2 =>
                rw [hcol_shift c t (by omega)]
                exact (hB.2 c).2 ⟨t, by omega⟩
            · ext c
              · simp only [splitA, joinA, dite_true, show (1 : ℕ) ≠ 0 by omega, dite_false,
                  val3_diff3]
                cases vm c <;> simp
              · simp only [splitA, joinA, dite_true, val3_diff3]
                cases vh c <;> simp
          · funext r c
            simp [splitA, joinA]
      · have hzero : (if LineOKSum n 0 (diff3 vm vh) then 1 else 0) *
            (if LineOKSum n 1 (diff3 vh vi) then 1 else 0) = 0 := by
          by_cases h1 : LineOKSum n 0 (diff3 vm vh)
          · have h2 : ¬ LineOKSum n 1 (diff3 vh vi) := fun h => hok ⟨h1, h⟩
            simp [h2]
          · simp [h1]
        rw [hzero, mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro A _ hA
        have ⟨hvh, hvm⟩ := hsplit_vals A vm vh hA.1 hA.2
        have hrow0 : A ⟨0, by omega⟩ = diff3 vh vi := by
          funext c
          have heq : val3 (A ⟨0, by omega⟩ c) = val3 (diff3 vh vi c) := by
            rw [val3_diff3]; linarith [hvh c]
          unfold val3 at heq; exact Fin.ext (by omega)
        have hrow1 : A ⟨1, by omega⟩ = diff3 vm vh := by
          funext c
          have heq : val3 (A ⟨1, by omega⟩ c) = val3 (diff3 vm vh c) := by
            rw [val3_diff3]; linarith [hvh c, hvm c]
          unfold val3 at heq; exact Fin.ext (by omega)
        have hr0 := hA.1.1 ⟨0, by omega⟩
        have hr1 := hA.1.1 ⟨1, by omega⟩
        rw [hrow0] at hr0; rw [hrow1] at hr1
        simp only [Nat.zero_mod, ite_true] at hr0
        simp only [show (1 : ℕ) % 2 ≠ 0 by omega, ite_false] at hr1
        exact hok ⟨hr1, hr0⟩
    simp_rw [← hcard_part]
    rw [← Fintype.sum_prod_type', ← Finset.card_biUnion]
    · apply congrArg Finset.card
      ext A; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨(splitA A).1, h, rfl⟩⟩
    · intro p1 _ p2 _ hp
      simp only [Function.onFun, Finset.disjoint_left]
      intro A h1 h2
      simp only [Finset.mem_filter] at h1 h2
      exact hp (h1.2.2.symm.trans h2.2.2)

theorem Z_n_at_special (n : ℕ) :
    Z_n n (fun _ => 1) (fun _ => q) (-q) q⁻¹ =
      (-1 : E6) ^ n * c ^ (2 * n ^ 2 + n) * ((HalfMat n).ncard : E6) := by
  unfold Z_n
  have hrep : List.ofFn (fun _ : Fin n => q) = List.replicate n q := by
    rw [List.ofFn_const]
  rw [hrep, prodB_replicate_special, validBlock_eq_halfMat]
  congr 1
  have h1 : ((-c) * c ^ (2 * n)) ^ n = (-1 : E6) ^ n * (c * c ^ (2 * n)) ^ n := by
    rw [← mul_pow]; congr 1; ring
  rw [h1, ← pow_succ', ← pow_mul]
  congr 2
  ring


end ModA


section Mod5
open Finset Polynomial E6

def Zvec (n : ℕ) (x y : Fin n → E6) : Fin (2 * n) → E6 :=
  fun i =>
    if h : i.val < n then
      x ⟨i.val, h⟩ ^ 2 + (x ⟨i.val, h⟩ ^ 2)⁻¹
    else
      -q * (y ⟨i.val - n, by omega⟩ ^ 2) - q⁻¹ * (y ⟨i.val - n, by omega⟩ ^ 2)⁻¹

def pref (n : ℕ) (x y : Fin n → E6) (α β : E6) : E6 :=
  c ^ n * (∏ k : Fin n, sig (y k ^ 2)) * (∏ j : Fin n, (α * x j + β * (x j)⁻¹))

/- ### 5.1. `IsPolyInSq` and `IsLaurent` calculus -/

def IsPolyInSq (d : ℕ) (f : E6 → E6) : Prop :=
  ∃ P : Polynomial E6, P.natDegree ≤ d ∧ ∀ z : E6, z ≠ 0 → z ^ d * f z = P.eval (z ^ 2)

lemma isPolyInSq_zero (d : ℕ) : IsPolyInSq d (fun _ => 0) :=
  ⟨0, by simp, fun _ _ => by simp⟩

lemma isPolyInSq_const (a : E6) : IsPolyInSq 0 (fun _ => a) :=
  ⟨C a, by simp, fun z _ => by simp⟩

lemma isPolyInSq_add {d : ℕ} {f g : E6 → E6} (hf : IsPolyInSq d f) (hg : IsPolyInSq d g) :
    IsPolyInSq d (fun z => f z + g z) := by
  obtain ⟨P, hPd, hP⟩ := hf
  obtain ⟨Q, hQd, hQ⟩ := hg
  refine ⟨P + Q, le_trans (natDegree_add_le P Q) (max_le hPd hQd), fun z hz => ?_⟩
  rw [mul_add, hP z hz, hQ z hz, eval_add]

lemma isPolyInSq_neg {d : ℕ} {f : E6 → E6} (hf : IsPolyInSq d f) :
    IsPolyInSq d (fun z => -f z) := by
  obtain ⟨P, hPd, hP⟩ := hf
  exact ⟨-P, by simpa using hPd, fun z hz => by simp [← hP z hz]⟩

lemma isPolyInSq_sub {d : ℕ} {f g : E6 → E6} (hf : IsPolyInSq d f) (hg : IsPolyInSq d g) :
    IsPolyInSq d (fun z => f z - g z) := by
  simpa [sub_eq_add_neg] using isPolyInSq_add hf (isPolyInSq_neg hg)

lemma isPolyInSq_sum {ι : Type*} {d : ℕ} (s : Finset ι) (f : ι → E6 → E6)
    (hf : ∀ i ∈ s, IsPolyInSq d (f i)) :
    IsPolyInSq d (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, fun z _ => by simp⟩
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hsum : (fun z => ∑ i ∈ insert a s, f i z) = (fun z => f a z + ∑ i ∈ s, f i z) := by
      funext z; exact Finset.sum_insert ha
    rw [hsum]; exact isPolyInSq_add h1 h2

lemma isPolyInSq_mul {d1 d2 : ℕ} {f g : E6 → E6}
    (hf : IsPolyInSq d1 f) (hg : IsPolyInSq d2 g) :
    IsPolyInSq (d1 + d2) (fun z => f z * g z) := by
  obtain ⟨P, hPd, hP⟩ := hf
  obtain ⟨Q, hQd, hQ⟩ := hg
  refine ⟨P * Q, le_trans natDegree_mul_le (Nat.add_le_add hPd hQd), fun z hz => ?_⟩
  rw [pow_add, eval_mul, ← hP z hz, ← hQ z hz]; ring

lemma isPolyInSq_step2 {d : ℕ} {f : E6 → E6} (hf : IsPolyInSq d f) :
    IsPolyInSq (d + 2) f := by
  obtain ⟨P, hPd, hP⟩ := hf
  refine ⟨P * X, le_trans natDegree_mul_le (by simp; omega), fun z hz => ?_⟩
  rw [eval_mul, eval_X, ← hP z hz, pow_add]; ring

lemma isPolyInSq_raise {d1 d2 : ℕ} {f : E6 → E6} (hle : d1 ≤ d2) (heven : (d2 - d1) % 2 = 0)
    (hf : IsPolyInSq d1 f) : IsPolyInSq d2 f := by
  obtain ⟨k, hk⟩ : ∃ k, d2 = d1 + 2 * k := ⟨(d2 - d1) / 2, by omega⟩
  subst hk
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [show d1 + 2 * (k + 1) = (d1 + 2 * k) + 2 by omega]
    exact isPolyInSq_step2 (ih (by omega) (by omega))

lemma isPolyInSq_lin (a b : E6) : IsPolyInSq 1 (fun z => a * z + b * z⁻¹) := by
  refine ⟨C a * X + C b, ?_, fun z hz => ?_⟩
  · refine le_trans (natDegree_add_le _ _) (max_le ?_ (by simp))
    exact le_trans natDegree_mul_le (by simp)
  · simp only [pow_one, eval_add, eval_mul, eval_C, eval_X]
    have hbz : z * (b * z⁻¹) = b := by
      rw [← mul_assoc, mul_comm z b, mul_assoc, mul_inv_cancel₀ hz, mul_one]
    rw [mul_add, hbz]; ring

lemma isPolyInSq_sig_mul (a : E6) : IsPolyInSq 1 (fun z => sig (a * z)) := by
  have h : (fun z : E6 => sig (a * z)) = fun z => a * z + (-a⁻¹) * z⁻¹ := by
    funext z; simp only [sig, mul_inv]; ring
  rw [h]; exact isPolyInSq_lin a (-a⁻¹)

lemma isPolyInSq_sig_mul_inv (a : E6) : IsPolyInSq 1 (fun z => sig (a * z⁻¹)) := by
  have h : (fun z : E6 => sig (a * z⁻¹)) = fun z => (-a⁻¹) * z + a * z⁻¹ := by
    funext z; simp only [sig, mul_inv, inv_inv]; ring
  rw [h]; exact isPolyInSq_lin (-a⁻¹) a

lemma isPolyInSq_Rmat_mul (y : E6) (o1 o2 i1 i2 : Bool) :
    IsPolyInSq (if o1 = i1 then 1 else 0) (fun z => Rmat (y * z) o1 o2 i1 i2) := by
  cases o1 <;> cases o2 <;> cases i1 <;> cases i2 <;>
    simp only [Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      ite_true, ite_false]
  · simpa [mul_assoc] using isPolyInSq_sig_mul (q * y)
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_sig_mul y
  · exact isPolyInSq_const (sig q)
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_const (sig q)
  · exact isPolyInSq_sig_mul y
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · simpa [mul_assoc] using isPolyInSq_sig_mul (q * y)

lemma isPolyInSq_Rmat_mul_inv (y : E6) (o1 o2 i1 i2 : Bool) :
    IsPolyInSq (if o1 = i1 then 1 else 0) (fun z => Rmat (y * z⁻¹) o1 o2 i1 i2) := by
  cases o1 <;> cases o2 <;> cases i1 <;> cases i2 <;>
    simp only [Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      ite_true, ite_false]
  · simpa [mul_assoc] using isPolyInSq_sig_mul_inv (q * y)
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_sig_mul_inv y
  · exact isPolyInSq_const (sig q)
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_const (sig q)
  · exact isPolyInSq_sig_mul_inv y
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · exact isPolyInSq_zero _
  · simpa [mul_assoc] using isPolyInSq_sig_mul_inv (q * y)

lemma isPolyInSq_Bmat (n : ℕ) (xt : Fin n → E6) (y α β : E6) (vo vi : Vec (n + 1)) :
    IsPolyInSq (if vo 0 = vi 0 then 2 else 1)
      (fun x0 => Bmat (n + 1) (Fin.cons x0 xt) y α β vo vi) := by
  have hdef : (fun x0 => Bmat (n + 1) (Fin.cons x0 xt) y α β vo vi) =
      fun x0 => ∑ v0m : Bool, ∑ h1 : Bool, ∑ h2 : Bool,
        Rmat (y * x0) (vo 0) false v0m h2 *
        Umat n xt y α β (h2, fun i => vo i.succ) (h1, fun i => vi i.succ) *
        Rmat (y * x0⁻¹) v0m h1 (vi 0) true := by
    funext x0
    rw [Bmat, Matrix.of_apply, Umat, Matrix.of_apply]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [hdef]
  apply isPolyInSq_sum; intro v0m _
  apply isPolyInSq_sum; intro h1 _
  apply isPolyInSq_sum; intro h2 _
  have h1' := isPolyInSq_Rmat_mul y (vo 0) false v0m h2
  have h2' := isPolyInSq_const (Umat n xt y α β (h2, fun i => vo i.succ) (h1, fun i => vi i.succ))
  have h3' := isPolyInSq_Rmat_mul_inv y v0m h1 (vi 0) true
  have hm := isPolyInSq_mul (isPolyInSq_mul h1' h2') h3'
  refine isPolyInSq_raise ?_ ?_ hm <;> cases vo 0 <;> cases vi 0 <;> cases v0m <;> simp

lemma isPolyInSq_prodB (n : ℕ) (xt : Fin n → E6) (α β : E6) :
    ∀ (ys : List E6) (vo vi : Vec (n + 1)),
      (vo 0 = vi 0 → IsPolyInSq (2 * ys.length)
        (fun x0 => prodB (n + 1) (Fin.cons x0 xt) α β ys vo vi)) ∧
      (vo 0 ≠ vi 0 → ys ≠ [] → IsPolyInSq (2 * ys.length - 1)
        (fun x0 => prodB (n + 1) (Fin.cons x0 xt) α β ys vo vi))
  | [], vo, vi => by
    refine ⟨fun _ => ?_, fun _ hne => absurd rfl hne⟩
    simp only [List.length_nil, mul_zero, prodB, Matrix.one_apply]
    exact isPolyInSq_const _
  | y :: ys, vo, vi => by
    have hIH := isPolyInSq_prodB n xt α β ys
    have hmul_def : (fun x0 => prodB (n + 1) (Fin.cons x0 xt) α β (y :: ys) vo vi) =
        fun x0 => ∑ vm : Vec (n + 1),
          prodB (n + 1) (Fin.cons x0 xt) α β ys vo vm *
          Bmat (n + 1) (Fin.cons x0 xt) y α β vm vi := by
      funext x0; rw [prodB, Matrix.mul_apply]
    rw [hmul_def]
    constructor
    · intro hEq
      simp only [List.length_cons]
      apply isPolyInSq_sum; intro vm _
      by_cases hvm : vo 0 = vm 0
      · have hB := isPolyInSq_Bmat n xt y α β vm vi
        rw [show vm 0 = vi 0 by rw [← hvm, hEq], if_pos rfl] at hB
        have hP := (hIH vo vm).1 hvm
        exact isPolyInSq_raise (by omega) (by omega) (isPolyInSq_mul hP hB)
      · cases ys with
        | nil =>
          have hzero : (fun x0 => prodB (n + 1) (Fin.cons x0 xt) α β [] vo vm *
              Bmat (n + 1) (Fin.cons x0 xt) y α β vm vi) = fun _ => 0 := by
            funext x0
            have hne : vo ≠ vm := fun h => hvm (congrFun h 0)
            simp [prodB, hne]
          rw [hzero]
          exact isPolyInSq_zero _
        | cons y2 ys2 =>
          have hB := isPolyInSq_Bmat n xt y α β vm vi
          have hvm_ne : vm 0 ≠ vi 0 := fun h => hvm (hEq.trans h.symm)
          rw [if_neg hvm_ne] at hB
          have hP := (hIH vo vm).2 hvm (List.cons_ne_nil y2 ys2)
          exact isPolyInSq_raise (by simp; omega) (by simp; omega) (isPolyInSq_mul hP hB)
    · intro hNe _
      simp only [List.length_cons]
      apply isPolyInSq_sum; intro vm _
      by_cases hvm : vo 0 = vm 0
      · have hB := isPolyInSq_Bmat n xt y α β vm vi
        have hvm_ne : vm 0 ≠ vi 0 := fun h => hNe (hvm.trans h)
        rw [if_neg hvm_ne] at hB
        have hP := (hIH vo vm).1 hvm
        exact isPolyInSq_raise (by omega) (by omega) (isPolyInSq_mul hP hB)
      · cases ys with
        | nil =>
          have hzero : (fun x0 => prodB (n + 1) (Fin.cons x0 xt) α β [] vo vm *
              Bmat (n + 1) (Fin.cons x0 xt) y α β vm vi) = fun _ => 0 := by
            funext x0
            have hne : vo ≠ vm := fun h => hvm (congrFun h 0)
            simp [prodB, hne]
          rw [hzero]
          exact isPolyInSq_zero _
        | cons y2 ys2 =>
          have hB := isPolyInSq_Bmat n xt y α β vm vi
          have hvm_eq : vm 0 = vi 0 := by
            cases h1 : vo 0 <;> cases h2 : vi 0 <;> cases h3 : vm 0 <;> simp_all
          rw [if_pos hvm_eq] at hB
          have hP := (hIH vo vm).2 hvm (List.cons_ne_nil y2 ys2)
          exact isPolyInSq_raise (by simp; omega) (by simp; omega) (isPolyInSq_mul hP hB)

lemma isPolyInSq_Z_n (n : ℕ) (xt : Fin n → E6) (y : Fin (n + 1) → E6) (α β : E6) :
    IsPolyInSq (2 * n + 1) (fun x0 => Z_n (n + 1) (Fin.cons x0 xt) y α β) := by
  have h := (isPolyInSq_prodB n xt α β (List.ofFn y) (allT (n + 1)) (allF (n + 1))).2
    (by simp [allT, allF]) (by simp [List.ofFn_succ])
  rw [List.length_ofFn, show 2 * (n + 1) - 1 = 2 * n + 1 by omega] at h
  exact h

lemma isPolyInSq_sq_add_inv : IsPolyInSq 2 (fun z => z ^ 2 + (z ^ 2)⁻¹) := by
  refine ⟨X ^ 2 + 1, le_trans (natDegree_add_le _ _) (max_le (by simp) (by simp)), fun z hz => ?_⟩
  simp only [eval_add, eval_pow, eval_X, eval_one]
  rw [mul_add, mul_inv_cancel₀ (pow_ne_zero 2 hz)]; ring

lemma isPolyInSq_pow {d : ℕ} {f : E6 → E6} (hf : IsPolyInSq d f) :
    ∀ k : ℕ, IsPolyInSq (k * d) (fun z => (f z) ^ k)
  | 0 => by simpa using isPolyInSq_const 1
  | k + 1 => by
    rw [show (k + 1) * d = k * d + d by ring]
    simpa [pow_succ] using isPolyInSq_mul (isPolyInSq_pow hf k) hf

lemma isPolyInSq_det_row0 {m d : ℕ} (M : E6 → Matrix (Fin (m + 1)) (Fin (m + 1)) E6)
    (hconst : ∀ (i : Fin (m + 1)), i ≠ 0 → ∀ j z, M z i j = M 0 i j)
    (hrow0 : ∀ j, IsPolyInSq d (fun z => M z 0 j)) :
    IsPolyInSq d (fun z => (M z).det) := by
  have hdet : (fun z => (M z).det) =
      fun z => ∑ σ : Equiv.Perm (Fin (m + 1)),
        ((Equiv.Perm.sign σ : E6) * ∏ j ∈ Finset.univ.erase (σ.symm 0), M 0 (σ j) j) *
        M z 0 (σ.symm 0) := by
    funext z
    rw [Matrix.det_apply]
    apply Finset.sum_congr rfl; intro σ _
    have hprod : (∏ j : Fin (m + 1), M z (σ j) j) =
        M z 0 (σ.symm 0) * ∏ j ∈ Finset.univ.erase (σ.symm 0), M z (σ j) j := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => M z (σ j) j) (Finset.mem_univ (σ.symm 0))]
      simp
    have hrest : (∏ j ∈ Finset.univ.erase (σ.symm 0), M z (σ j) j) =
        ∏ j ∈ Finset.univ.erase (σ.symm 0), M 0 (σ j) j := by
      apply Finset.prod_congr rfl; intro j hj
      have hne : σ j ≠ 0 := by
        intro h0; rw [Finset.mem_erase] at hj
        exact hj.1 (by rw [← h0]; simp)
      exact hconst (σ j) hne j z
    rw [hprod, hrest]; simp [Units.smul_def]; ring
  rw [hdet]
  apply isPolyInSq_sum; intro σ _
  simpa [zero_add] using isPolyInSq_mul (isPolyInSq_const _) (hrow0 (σ.symm 0))

lemma isPolyInSq_Vmat (n : ℕ) (xt : Fin n → E6) (y : Fin (n + 1) → E6) :
    IsPolyInSq (4 * n + 2)
      (fun x0 => (Vmat (2 * (n + 1)) (Zvec (n + 1) (Fin.cons x0 xt) y)).det) := by
  have hdim : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  let e : Fin ((2 * n + 1) + 1) ≃ Fin (2 * (n + 1)) := finCongr hdim.symm
  let M : E6 → Matrix (Fin ((2 * n + 1) + 1)) (Fin ((2 * n + 1) + 1)) E6 :=
    fun x0 => (Vmat (2 * (n + 1)) (Zvec (n + 1) (Fin.cons x0 xt) y)).submatrix e e
  have hdet_eq : (fun x0 => (Vmat (2 * (n + 1)) (Zvec (n + 1) (Fin.cons x0 xt) y)).det) =
      fun x0 => (M x0).det := by
    funext x0; exact (Matrix.det_submatrix_equiv_self e _).symm
  rw [hdet_eq]
  apply isPolyInSq_det_row0 M
  · intro i hi j z
    simp only [M, Matrix.submatrix_apply, Vmat, Matrix.of_apply, Zvec, e, finCongr_apply,
      Fin.val_cast]
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    by_cases hlt : i.val < n + 1
    · rw [dif_pos hlt, dif_pos hlt]
      have hidx : (⟨i.val, hlt⟩ : Fin (n + 1)) = (⟨i.val - 1, by omega⟩ : Fin n).succ :=
        Fin.ext (by dsimp; omega)
      rw [hidx]; simp only [Fin.cons_succ]
    · rw [dif_neg hlt, dif_neg hlt]
  · intro j
    have hrow : (fun z => M z 0 j) = fun z => (z ^ 2 + (z ^ 2)⁻¹) ^ j.val := by
      funext z
      simp only [M, Matrix.submatrix_apply, Vmat, Matrix.of_apply, Zvec, e, finCongr_apply,
        Fin.val_cast, Fin.val_zero, Nat.zero_lt_succ]
      rfl
    rw [hrow]
    have hp := isPolyInSq_pow isPolyInSq_sq_add_inv j.val
    exact isPolyInSq_raise (by omega) (by omega) hp

lemma isPolyInSq_Dmat (n : ℕ) (xt : Fin n → E6) (y : Fin (n + 1) → E6) :
    IsPolyInSq (6 * n + 2)
      (fun x0 => (Dmat (n + 1) (Zvec (n + 1) (Fin.cons x0 xt) y)).det) := by
  have hdim : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  let e : Fin ((2 * n + 1) + 1) ≃ Fin (2 * (n + 1)) := finCongr hdim.symm
  let M : E6 → Matrix (Fin ((2 * n + 1) + 1)) (Fin ((2 * n + 1) + 1)) E6 :=
    fun x0 => (Dmat (n + 1) (Zvec (n + 1) (Fin.cons x0 xt) y)).submatrix e e
  have hdet_eq : (fun x0 => (Dmat (n + 1) (Zvec (n + 1) (Fin.cons x0 xt) y)).det) =
      fun x0 => (M x0).det := by
    funext x0; exact (Matrix.det_submatrix_equiv_self e _).symm
  rw [hdet_eq]
  apply isPolyInSq_det_row0 M
  · intro i hi j z
    simp only [M, Matrix.submatrix_apply, Dmat, Matrix.of_apply, Zvec, e, finCongr_apply,
      Fin.val_cast]
    have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    by_cases hlt : i.val < n + 1
    · rw [dif_pos hlt, dif_pos hlt]
      have hidx : (⟨i.val, hlt⟩ : Fin (n + 1)) = (⟨i.val - 1, by omega⟩ : Fin n).succ :=
        Fin.ext (by dsimp; omega)
      rw [hidx]; simp only [Fin.cons_succ]
    · rw [dif_neg hlt, dif_neg hlt]
  · intro j
    have hrow : (fun z => M z 0 j) = fun z =>
        ((z ^ 2 + (z ^ 2)⁻¹) ^ 3 - 3 * (z ^ 2 + (z ^ 2)⁻¹)) ^ (j.val / 2) *
        (z ^ 2 + (z ^ 2)⁻¹) ^ (j.val % 2) := by
      funext z
      simp only [M, Matrix.submatrix_apply, Dmat, Matrix.of_apply, Zvec, e, finCongr_apply,
        Fin.val_cast, Fin.val_zero, Nat.zero_lt_succ]
      rfl
    rw [hrow]
    have hT : IsPolyInSq 6 (fun z => (z ^ 2 + (z ^ 2)⁻¹) ^ 3 - 3 * (z ^ 2 + (z ^ 2)⁻¹)) := by
      have h3 := isPolyInSq_pow isPolyInSq_sq_add_inv 3
      have h1 : IsPolyInSq 6 (fun z => 3 * (z ^ 2 + (z ^ 2)⁻¹)) :=
        isPolyInSq_raise (d2 := 6) (by omega) (by omega)
          (show IsPolyInSq 2 (fun z => 3 * (z ^ 2 + (z ^ 2)⁻¹)) from by
            simpa [zero_add] using isPolyInSq_mul (isPolyInSq_const 3) isPolyInSq_sq_add_inv)
      exact isPolyInSq_sub h3 h1
    have hpart1 := isPolyInSq_pow hT (j.val / 2)
    have hpart2 := isPolyInSq_pow isPolyInSq_sq_add_inv (j.val % 2)
    have hmul := isPolyInSq_mul hpart1 hpart2
    have hle : j.val / 2 * 6 + j.val % 2 * 2 ≤ 6 * n + 2 := by omega
    have hev : (6 * n + 2 - (j.val / 2 * 6 + j.val % 2 * 2)) % 2 = 0 := by omega
    exact isPolyInSq_raise hle hev hmul

/- ### 5.2. `IsLaurent` calculus -/

def IsLaurent (f : E6 → E6) : Prop :=
  ∃ (M : ℕ) (P : Polynomial E6), ∀ z : E6, z ≠ 0 → z ^ M * f z = P.eval z

lemma isLaurent_const (a : E6) : IsLaurent (fun _ => a) :=
  ⟨0, C a, fun z _ => by simp⟩

lemma isLaurent_id : IsLaurent (fun z => z) :=
  ⟨0, X, fun z _ => by simp⟩

lemma isLaurent_inv : IsLaurent (fun z => z⁻¹) :=
  ⟨1, 1, fun z hz => by simp [mul_inv_cancel₀ hz]⟩

lemma isLaurent_add {f g : E6 → E6} (hf : IsLaurent f) (hg : IsLaurent g) :
    IsLaurent (fun z => f z + g z) := by
  obtain ⟨M1, P1, h1⟩ := hf
  obtain ⟨M2, P2, h2⟩ := hg
  refine ⟨M1 + M2, X ^ M2 * P1 + X ^ M1 * P2, fun z hz => ?_⟩
  simp only [eval_add, eval_mul, eval_pow, eval_X, ← h1 z hz, ← h2 z hz, pow_add]
  ring

lemma isLaurent_neg {f : E6 → E6} (hf : IsLaurent f) : IsLaurent (fun z => -f z) := by
  obtain ⟨M, P, h⟩ := hf
  exact ⟨M, -P, fun z hz => by simp [← h z hz]⟩

lemma isLaurent_sub {f g : E6 → E6} (hf : IsLaurent f) (hg : IsLaurent g) :
    IsLaurent (fun z => f z - g z) := by
  simpa [sub_eq_add_neg] using isLaurent_add hf (isLaurent_neg hg)

lemma isLaurent_mul {f g : E6 → E6} (hf : IsLaurent f) (hg : IsLaurent g) :
    IsLaurent (fun z => f z * g z) := by
  obtain ⟨M1, P1, h1⟩ := hf
  obtain ⟨M2, P2, h2⟩ := hg
  refine ⟨M1 + M2, P1 * P2, fun z hz => ?_⟩
  simp only [eval_mul, ← h1 z hz, ← h2 z hz, pow_add]
  ring

lemma isLaurent_pow {f : E6 → E6} (hf : IsLaurent f) : ∀ k : ℕ, IsLaurent (fun z => (f z) ^ k)
  | 0 => by simpa using isLaurent_const 1
  | k + 1 => by simpa [pow_succ] using isLaurent_mul (isLaurent_pow hf k) hf

lemma isLaurent_sum {ι : Type*} (s : Finset ι) (f : ι → E6 → E6)
    (hf : ∀ i ∈ s, IsLaurent (f i)) : IsLaurent (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLaurent_const 0
  | insert a s ha ih =>
    have hsum : (fun z => ∑ i ∈ insert a s, f i z) = fun z => f a z + ∑ i ∈ s, f i z := by
      funext z; exact Finset.sum_insert ha
    rw [hsum]
    exact isLaurent_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma isLaurent_prod {ι : Type*} (s : Finset ι) (f : ι → E6 → E6)
    (hf : ∀ i ∈ s, IsLaurent (f i)) : IsLaurent (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isLaurent_const 1
  | insert a s ha ih =>
    have hprod : (fun z => ∏ i ∈ insert a s, f i z) = fun z => f a z * ∏ i ∈ s, f i z := by
      funext z; exact Finset.prod_insert ha
    rw [hprod]
    exact isLaurent_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma isLaurent_det {m : ℕ} (M : E6 → Matrix (Fin m) (Fin m) E6)
    (hM : ∀ i j, IsLaurent (fun z => M z i j)) : IsLaurent (fun z => (M z).det) := by
  have hdet : (fun z => (M z).det) =
      fun z => ∑ σ : Equiv.Perm (Fin m),
        (Equiv.Perm.sign σ : E6) * ∏ j : Fin m, M z (σ j) j := by
    funext z; simp [Matrix.det_apply, Units.smul_def]
  rw [hdet]
  apply isLaurent_sum; intro σ _
  exact isLaurent_mul (isLaurent_const _) (isLaurent_prod _ _ fun j _ => hM (σ j) j)

lemma isLaurent_of_const_mul_zpow (a : E6) (k : ℤ) :
    IsLaurent (fun z => a * z ^ k) := by
  cases k with
  | ofNat m => simpa using isLaurent_mul (isLaurent_const a) (isLaurent_pow isLaurent_id m)
  | negSucc m =>
    have h : (fun z : E6 => a * z ^ Int.negSucc m) = fun z => a * (z⁻¹) ^ (m + 1) := by
      funext z; simp [zpow_negSucc, inv_pow]
    rw [h]; exact isLaurent_mul (isLaurent_const a) (isLaurent_pow isLaurent_inv (m + 1))

lemma isLaurent_sig_of_laurent {f : E6 → E6} (hf : IsLaurent f) (hfi : IsLaurent (fun z => (f z)⁻¹)) :
    IsLaurent (fun z => sig (f z)) := isLaurent_sub hf hfi

lemma isLaurent_Rmat {f : E6 → E6} (hf : IsLaurent f) (hfi : IsLaurent (fun z => (f z)⁻¹))
    (o1 o2 i1 i2 : Bool) : IsLaurent (fun z => Rmat (f z) o1 o2 i1 i2) := by
  have hqf : IsLaurent (fun z => q * f z) := isLaurent_mul (isLaurent_const q) hf
  have hqfi : IsLaurent (fun z => (q * f z)⁻¹) := by
    have h : (fun z => (q * f z)⁻¹) = fun z => q⁻¹ * (f z)⁻¹ := by funext z; rw [mul_inv]
    rw [h]; exact isLaurent_mul (isLaurent_const q⁻¹) hfi
  cases o1 <;> cases o2 <;> cases i1 <;> cases i2 <;>
    simp only [Rmat, Bool.false_eq_true, Bool.true_eq_false, and_self, and_false, false_and,
      ite_true, ite_false]
  · exact isLaurent_sig_of_laurent hqf hqfi
  · exact isLaurent_const 0
  · exact isLaurent_const 0
  · exact isLaurent_const 0
  · exact isLaurent_const 0
  · exact isLaurent_sig_of_laurent hf hfi
  · exact isLaurent_const (sig q)
  · exact isLaurent_const 0
  · exact isLaurent_const 0
  · exact isLaurent_const (sig q)
  · exact isLaurent_sig_of_laurent hf hfi
  · exact isLaurent_const 0
  · exact isLaurent_const 0
  · exact isLaurent_const 0
  · exact isLaurent_const 0
  · exact isLaurent_sig_of_laurent hqf hqfi

lemma isLaurent_Kmat {f : E6 → E6} (hf : IsLaurent f) (hfi : IsLaurent (fun z => (f z)⁻¹))
    (α β : E6) (o i : Bool) : IsLaurent (fun z => Kmat (f z) α β o i) := by
  cases o <;> cases i <;> simp only [Kmat, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false]
  · exact isLaurent_add (isLaurent_mul (isLaurent_const α) hf) (isLaurent_mul (isLaurent_const β) hfi)
  · exact isLaurent_const 0
  · exact isLaurent_const 0
  · exact isLaurent_add (isLaurent_mul (isLaurent_const α) hfi) (isLaurent_mul (isLaurent_const β) hf)

lemma isLaurent_Umat : ∀ (n : ℕ) (x : E6 → Fin n → E6) (y : E6 → E6) (α β : E6),
    (∀ j, IsLaurent (fun z => x z j) ∧ IsLaurent (fun z => (x z j)⁻¹)) →
    (IsLaurent y ∧ IsLaurent (fun z => (y z)⁻¹)) →
    ∀ p1 p2, IsLaurent (fun z => Umat n (x z) (y z) α β p1 p2)
  | 0, _, y, α, β, _, hy, p1, p2 => isLaurent_Kmat hy.1 hy.2 α β p1.1 p2.1
  | n + 1, x, y, α, β, hx, hy, p1, p2 => by
    have hdef : (fun z => Umat (n + 1) (x z) (y z) α β p1 p2) =
        fun z => ∑ v0m : Bool, ∑ h1 : Bool, ∑ h2 : Bool,
          Rmat (y z * x z 0) (p1.2 0) p1.1 v0m h2 *
          Umat n (fun i => x z i.succ) (y z) α β (h2, fun i => p1.2 i.succ) (h1, fun i => p2.2 i.succ) *
          Rmat (y z * (x z 0)⁻¹) v0m h1 (p2.2 0) p2.1 := by
      funext z; rw [Umat, Matrix.of_apply]
    rw [hdef]
    have h1 : IsLaurent (fun z => y z * x z 0) := isLaurent_mul hy.1 (hx 0).1
    have h1i : IsLaurent (fun z => (y z * x z 0)⁻¹) := by
      have h : (fun z => (y z * x z 0)⁻¹) = fun z => (y z)⁻¹ * (x z 0)⁻¹ := by
        funext z; rw [mul_inv]
      rw [h]; exact isLaurent_mul hy.2 (hx 0).2
    have h2 : IsLaurent (fun z => y z * (x z 0)⁻¹) := isLaurent_mul hy.1 (hx 0).2
    have h2i : IsLaurent (fun z => (y z * (x z 0)⁻¹)⁻¹) := by
      have h : (fun z => (y z * (x z 0)⁻¹)⁻¹) = fun z => (y z)⁻¹ * x z 0 := by
        funext z; rw [mul_inv, inv_inv]
      rw [h]; exact isLaurent_mul hy.2 (hx 0).1
    apply isLaurent_sum; intro v0m _
    apply isLaurent_sum; intro h1' _
    apply isLaurent_sum; intro h2' _
    exact isLaurent_mul (isLaurent_mul (isLaurent_Rmat h1 h1i _ _ _ _)
      (isLaurent_Umat n (fun z i => x z i.succ) y α β (fun i => hx i.succ) hy _ _))
      (isLaurent_Rmat h2 h2i _ _ _ _)

lemma isLaurent_prodB (n : ℕ) (x : E6 → Fin n → E6) (α β : E6)
    (hx : ∀ j, IsLaurent (fun z => x z j) ∧ IsLaurent (fun z => (x z j)⁻¹)) :
    ∀ (ys : List (E6 → E6)), (∀ f ∈ ys, IsLaurent f ∧ IsLaurent (fun z => (f z)⁻¹)) →
      ∀ vo vi, IsLaurent (fun z => prodB n (x z) α β (ys.map fun f => f z) vo vi)
  | [], _, vo, vi => by
    simp only [List.map_nil, prodB, Matrix.one_apply]
    exact isLaurent_const _
  | f :: fs, hfs, vo, vi => by
    have hdef : (fun z => prodB n (x z) α β ((f :: fs).map fun g => g z) vo vi) =
        fun z => ∑ vm : Vec n,
          prodB n (x z) α β (fs.map fun g => g z) vo vm * Bmat n (x z) (f z) α β vm vi := by
      funext z; rw [List.map_cons, prodB, Matrix.mul_apply]
    rw [hdef]
    apply isLaurent_sum; intro vm _
    have hf := hfs f (List.mem_cons_self ..)
    have hfs' := fun g hg => hfs g (List.mem_cons_of_mem f hg)
    exact isLaurent_mul (isLaurent_prodB n x α β hx fs hfs' vo vm)
      (isLaurent_Umat n x f α β hx hf (false, vm) (true, vi))

lemma isLaurent_Z_n (n : ℕ) (x y : E6 → Fin n → E6) (α β : E6)
    (hx : ∀ j, IsLaurent (fun z => x z j) ∧ IsLaurent (fun z => (x z j)⁻¹))
    (hy : ∀ k, IsLaurent (fun z => y z k) ∧ IsLaurent (fun z => (y z k)⁻¹)) :
    IsLaurent (fun z => Z_n n (x z) (y z) α β) := by
  have hmap : ∀ z, List.ofFn (y z) = (List.ofFn fun k : Fin n => fun z => y z k).map (fun f => f z) := by
    intro z; rw [List.map_ofFn]; rfl
  have hdef : (fun z => Z_n n (x z) (y z) α β) =
      fun z => prodB n (x z) α β ((List.ofFn fun k : Fin n => fun z => y z k).map fun f => f z)
        (allT n) (allF n) := by
    funext z; simp only [Z_n, hmap]
  rw [hdef]
  apply isLaurent_prodB n x α β hx
  intro f hf
  rw [List.mem_ofFn] at hf
  obtain ⟨k, rfl⟩ := hf
  exact hy k

lemma isLaurent_Zvec (n : ℕ) (x y : E6 → Fin n → E6)
    (hx : ∀ j, IsLaurent (fun z => x z j) ∧ IsLaurent (fun z => (x z j)⁻¹))
    (hy : ∀ k, IsLaurent (fun z => y z k) ∧ IsLaurent (fun z => (y z k)⁻¹))
    (i : Fin (2 * n)) : IsLaurent (fun z => Zvec n (x z) (y z) i) := by
  unfold Zvec
  by_cases hi : i.val < n
  · simp only [hi, dite_true]
    have h1 := isLaurent_pow (hx ⟨i.val, hi⟩).1 2
    have h2 : IsLaurent (fun z => (x z ⟨i.val, hi⟩ ^ 2)⁻¹) := by
      have h : (fun z => (x z ⟨i.val, hi⟩ ^ 2)⁻¹) = fun z => ((x z ⟨i.val, hi⟩)⁻¹) ^ 2 := by
        funext z; rw [inv_pow]
      rw [h]; exact isLaurent_pow (hx ⟨i.val, hi⟩).2 2
    exact isLaurent_add h1 h2
  · simp only [hi, dite_false]
    have h1 := isLaurent_mul (isLaurent_const (-q)) (isLaurent_pow (hy ⟨i.val - n, by omega⟩).1 2)
    have h2 : IsLaurent (fun z => q⁻¹ * (y z ⟨i.val - n, by omega⟩ ^ 2)⁻¹) := by
      have h : (fun z => q⁻¹ * (y z ⟨i.val - n, by omega⟩ ^ 2)⁻¹) =
          fun z => q⁻¹ * ((y z ⟨i.val - n, by omega⟩)⁻¹) ^ 2 := by
        funext z; rw [inv_pow]
      rw [h]; exact isLaurent_mul (isLaurent_const q⁻¹) (isLaurent_pow (hy ⟨i.val - n, by omega⟩).2 2)
    exact isLaurent_sub h1 h2

lemma isLaurent_pref (n : ℕ) (x y : E6 → Fin n → E6) (α β : E6)
    (hx : ∀ j, IsLaurent (fun z => x z j) ∧ IsLaurent (fun z => (x z j)⁻¹))
    (hy : ∀ k, IsLaurent (fun z => y z k) ∧ IsLaurent (fun z => (y z k)⁻¹)) :
    IsLaurent (fun z => pref n (x z) (y z) α β) := by
  unfold pref
  apply isLaurent_mul
  · apply isLaurent_mul (isLaurent_const _)
    apply isLaurent_prod; intro k _
    have h1 := isLaurent_pow (hy k).1 2
    have h2 : IsLaurent (fun z => (y z k ^ 2)⁻¹) := by
      have h : (fun z => (y z k ^ 2)⁻¹) = fun z => ((y z k)⁻¹) ^ 2 := by funext z; rw [inv_pow]
      rw [h]; exact isLaurent_pow (hy k).2 2
    exact isLaurent_sig_of_laurent h1 h2
  · apply isLaurent_prod; intro j _
    exact isLaurent_add (isLaurent_mul (isLaurent_const α) (hx j).1)
      (isLaurent_mul (isLaurent_const β) (hx j).2)

lemma isLaurent_Vmat_Zvec (n : ℕ) (x y : E6 → Fin n → E6)
    (hx : ∀ j, IsLaurent (fun z => x z j) ∧ IsLaurent (fun z => (x z j)⁻¹))
    (hy : ∀ k, IsLaurent (fun z => y z k) ∧ IsLaurent (fun z => (y z k)⁻¹)) :
    IsLaurent (fun z => (Vmat (2 * n) (Zvec n (x z) (y z))).det) := by
  apply isLaurent_det; intro i j
  exact isLaurent_pow (isLaurent_Zvec n x y hx hy i) j.val

lemma isLaurent_Dmat_Zvec (n : ℕ) (x y : E6 → Fin n → E6)
    (hx : ∀ j, IsLaurent (fun z => x z j) ∧ IsLaurent (fun z => (x z j)⁻¹))
    (hy : ∀ k, IsLaurent (fun z => y z k) ∧ IsLaurent (fun z => (y z k)⁻¹)) :
    IsLaurent (fun z => (Dmat n (Zvec n (x z) (y z))).det) := by
  apply isLaurent_det; intro r s
  have hZ := isLaurent_Zvec n x y hx hy r
  have hT := isLaurent_sub (isLaurent_pow hZ 3) (isLaurent_mul (isLaurent_const 3) hZ)
  exact isLaurent_mul (isLaurent_pow hT (s.val / 2)) (isLaurent_pow hZ (s.val % 2))

lemma poly_eq_of_card_roots {d : ℕ} {P Q : Polynomial E6} (hP : P.natDegree ≤ d)
    (hQ : Q.natDegree ≤ d) (S : Finset E6) (hS : d < S.card)
    (heq : ∀ a ∈ S, P.eval a = Q.eval a) : P = Q := by
  by_contra hne
  have hsub : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (P - Q).natDegree ≤ d := le_trans (natDegree_sub_le P Q) (max_le hP hQ)
  have hmem : S ⊆ (P - Q).roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hsub, Polynomial.IsRoot, eval_sub,
        heq a ha, sub_self]
  have hle1 : S.card ≤ (P - Q).roots.toFinset.card := Finset.card_le_card hmem
  have hle2 : (P - Q).roots.toFinset.card ≤ (P - Q).roots.card := Multiset.toFinset_card_le _
  have hle3 : (P - Q).roots.card ≤ (P - Q).natDegree := Polynomial.card_roots' (P - Q)
  omega

lemma laurent_eq_of_gt_bound {f g : E6 → E6} (hf : IsLaurent f) (hg : IsLaurent g)
    (B : ℚ) (hB : 0 ≤ B) (heq : ∀ r : ℚ, B < r → f (r : E6) = g (r : E6)) :
    ∀ z : E6, z ≠ 0 → f z = g z := by
  obtain ⟨M1, P1, h1⟩ := hf
  obtain ⟨M2, P2, h2⟩ := hg
  let M := M1 + M2
  let Q1 := X ^ M2 * P1
  let Q2 := X ^ M1 * P2
  let d := max Q1.natDegree Q2.natDegree
  let S : Finset E6 := (range (d + 1)).image (fun k : ℕ => ((B + (k : ℚ) + 1 : ℚ) : E6))
  have hcard : S.card = d + 1 := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range (d + 1)
    · intro i j hij
      have hq := E6.ratCast_inj hij
      exact_mod_cast (show (i : ℚ) = (j : ℚ) by linarith)
  have hQeq : Q1 = Q2 := by
    apply poly_eq_of_card_roots (le_max_left _ _) (le_max_right _ _) S (by omega)
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨k, _, rfl⟩ := ha
    have hr_gt : B < B + (k : ℚ) + 1 := by linarith [Nat.cast_nonneg (α := ℚ) k]
    have hr_ne : ((B + (k : ℚ) + 1 : ℚ) : E6) ≠ 0 := by
      intro h0
      have := E6.ratCast_inj (by simpa using h0 : ((B + (k : ℚ) + 1 : ℚ) : E6) = ((0 : ℚ) : E6))
      linarith
    have hfg := heq (B + (k : ℚ) + 1) hr_gt
    simp only [Q1, Q2, eval_mul, eval_pow, eval_X, ← h1 _ hr_ne, ← h2 _ hr_ne, hfg]
    ring
  intro z hz
  have hM : z ^ M * f z = z ^ M * g z := by
    have h1' : Q1.eval z = z ^ M * f z := by
      simp only [Q1, M, eval_mul, eval_pow, eval_X, ← h1 z hz, pow_add]; ring
    have h2' : Q2.eval z = z ^ M * g z := by
      simp only [Q2, M, eval_mul, eval_pow, eval_X, ← h2 z hz, pow_add]; ring
    rw [← h1', ← h2', hQeq]
  exact mul_left_cancel₀ (pow_ne_zero M hz) hM

/- ### 5.3. Permutation symmetry of `Z_n` and `MasterEq` -/

lemma prodB_perm (n : ℕ) (x : Fin n → E6) (α β : E6) {l1 l2 : List E6}
    (hperm : l1.Perm l2)
    (hcomm : ∀ a ∈ l1, ∀ b ∈ l1, Bmat n x a α β * Bmat n x b α β = Bmat n x b α β * Bmat n x a α β) :
    prodB n x α β l1 = prodB n x α β l2 := by
  induction hperm with
  | nil => rfl
  | cons a _ ih =>
    simp only [prodB]
    rw [ih fun u hu v hv => hcomm u (List.mem_cons_of_mem a hu) v (List.mem_cons_of_mem a hv)]
  | swap a b l =>
    simp only [prodB, Matrix.mul_assoc]
    rw [hcomm a (List.mem_cons_of_mem b (List.mem_cons_self ..)) b (List.mem_cons_self ..)]
  | trans hp1 _ ih1 ih2 =>
    rw [ih1 hcomm, ih2 fun u hu v hv => hcomm u (hp1.mem_iff.2 hu) v (hp1.mem_iff.2 hv)]

lemma list_ofFn_comp_perm {m : ℕ} (y : Fin m → E6) (σ : Fin m ≃ Fin m) :
    (List.ofFn (y ∘ σ)).Perm (List.ofFn y) := by
  have hof : ∀ g : Fin m → E6, List.ofFn g = (List.finRange m).map g := fun g =>
    List.ext_getElem (by simp) (fun i h1 h2 => by simp)
  rw [hof, hof, ← List.map_map]
  apply List.Perm.map
  rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange m).map σ.injective) (List.nodup_finRange m)]
  intro i
  simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
  exact ⟨σ.symm i, σ.apply_symm_apply i⟩

lemma Z_n_comp_perm (n : ℕ) (x y : Fin n → E6) (α β : E6) (σ : Fin n ≃ Fin n)
    (hcomm : ∀ j k, Bmat n x (y j) α β * Bmat n x (y k) α β = Bmat n x (y k) α β * Bmat n x (y j) α β) :
    Z_n n x (y ∘ σ) α β = Z_n n x y α β := by
  unfold Z_n
  rw [prodB_perm n x α β (list_ofFn_comp_perm y σ)]
  intro a ha b hb
  rw [List.mem_ofFn] at ha hb
  obtain ⟨j, rfl⟩ := ha
  obtain ⟨k, rfl⟩ := hb
  exact hcomm (σ j) (σ k)

/- ### 5.4. Exact `E6` algebraic identities for freezing + `Dmat`/`Vmat` reduction -/

lemma e6_T_identities (y0 : E6) (hy0 : y0 ≠ 0) :
    let z0 := y0 ^ 2 + (y0 ^ 2)⁻¹
    let z1 := -q * y0 ^ 2 - q⁻¹ * (y0 ^ 2)⁻¹
    let u0 := -(z0 + z1)
    (z0 ^ 3 - 3 * z0 = z1 ^ 3 - 3 * z1) ∧
    (∀ z : E6, (z ^ 3 - 3 * z) - (z0 ^ 3 - 3 * z0) = (z - z0) * (z - z1) * (z - u0)) ∧
    (∀ xj : E6, xj ≠ 0 →
      sig (q * (y0 * xj⁻¹)) * sig (q * (y0 * xj)) = -((xj ^ 2 + (xj ^ 2)⁻¹) - u0)) ∧
    (∀ yk : E6, yk ≠ 0 →
      sig (q * (yk * y0⁻¹)) * sig (yk * y0) = -((-q * yk ^ 2 - q⁻¹ * (yk ^ 2)⁻¹) - u0)) := by
  intro z0 z1 u0
  have hy2 : y0 ^ 2 ≠ 0 := pow_ne_zero 2 hy0
  have hq : q ≠ 0 := q_ne_zero
  have hq2 := q_sq
  have hq3 := q_cube
  have hqi := q_inv
  have hT : z0 ^ 3 - 3 * z0 = z1 ^ 3 - 3 * z1 := by
    dsimp only [z0, z1]
    rw [hqi]
    field_simp [hy2]
    ring_nf; simp only [hq3, hq2]; ring
  have hsum_sq : z0 ^ 2 + z0 * z1 + z1 ^ 2 = 3 := by
    dsimp only [z0, z1]
    rw [hqi]
    field_simp [hy2]
    ring_nf; simp only [hq2]; ring
  refine ⟨hT, ?_, ?_, ?_⟩
  · intro z
    dsimp only [u0]
    linear_combination (z - z0) * hsum_sq
  · intro xj hxj
    dsimp only [u0, z0, z1, sig]
    rw [mul_inv, mul_inv, mul_inv, mul_inv, inv_inv, hqi]
    field_simp [hy0, hxj, hq]
    ring_nf; simp only [hq2]; ring
  · intro yk hyk
    dsimp only [u0, z0, z1, sig]
    rw [mul_inv, mul_inv, mul_inv, inv_inv, hqi]
    field_simp [hy0, hyk, hq]
    ring_nf

/- ### 5.5. Master Theorem + Final Specialization -/


def MasterEq (n : ℕ) (x y : Fin n → E6) (α β : E6) : Prop :=
  (Vmat (2 * n) (Zvec n x y)).det * Z_n n x y α β =
  pref n x y α β * (Dmat n (Zvec n x y)).det

lemma det_Vmat_split (n : ℕ) (Z : Fin (2 * (n + 1)) → E6) :
    (Vmat (2 * (n + 1)) Z).det =
      (Z ⟨1, by omega⟩ - Z ⟨0, by omega⟩) *
      (∏ r : Fin (2 * n), (Z ⟨r.val + 2, by omega⟩ - Z ⟨0, by omega⟩) *
                          (Z ⟨r.val + 2, by omega⟩ - Z ⟨1, by omega⟩)) *
      (Vmat (2 * n) (fun r => Z ⟨r.val + 2, by omega⟩)).det := by
  rw [det_Vmat_eq_prod, det_Vmat_eq_prod]
  let i0 : Fin (2 * (n + 1)) := ⟨0, by omega⟩
  let i1 : Fin (2 * (n + 1)) := ⟨1, by omega⟩
  have hsplit : (∏ i : Fin (2 * (n + 1)), ∏ j ∈ Finset.Ioi i, (Z j - Z i)) =
      (∏ j ∈ Finset.Ioi i0, (Z j - Z i0)) *
      (∏ j ∈ Finset.Ioi i1, (Z j - Z i1)) *
      (∏ r : Fin (2 * n), ∏ j ∈ Finset.Ioi (⟨r.val + 2, by omega⟩ : Fin (2 * (n + 1))),
        (Z j - Z ⟨r.val + 2, by omega⟩)) := by
    let e : Fin 2 ⊕ Fin (2 * n) ≃ Fin (2 * (n + 1)) :=
      { toFun := Sum.elim (fun i => ⟨i.val, by omega⟩) (fun r => ⟨r.val + 2, by omega⟩)
        invFun := fun i => if h : i.val < 2 then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - 2, by omega⟩
        left_inv := fun x => by cases x with | inl i => simp [i.isLt] | inr r => simp [show ¬ r.val + 2 < 2 by omega]
        right_inv := fun i => by
          by_cases h : i.val < 2
          · simp [h]
          · simp only [h, dite_false, Sum.elim_inr]; exact Fin.ext (by dsimp; omega) }
    rw [← Fintype.prod_equiv e _ _ (fun _ => rfl), Fintype.prod_sum_type, Fin.prod_univ_two]
    rfl
  rw [hsplit]
  have hi0 : (∏ j ∈ Finset.Ioi i0, (Z j - Z i0)) =
      (Z i1 - Z i0) * ∏ r : Fin (2 * n), (Z ⟨r.val + 2, by omega⟩ - Z i0) := by
    rw [← Finset.mul_prod_erase (Finset.Ioi i0) (fun j => Z j - Z i0)
      (Finset.mem_Ioi.2 (show i0 < i1 by simp [i0, i1]))]
    congr 1
    refine Finset.prod_bij (fun (j : Fin (2 * (n + 1))) hj => ⟨j.val - 2, by
        simp only [Finset.mem_erase, Finset.mem_Ioi, Fin.lt_def, i0, i1] at hj
        have hne : j.val ≠ 1 := fun h => hj.1 (Fin.ext h)
        omega⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro j1 hj1 j2 hj2 h
      simp only [Finset.mem_erase, Finset.mem_Ioi, Fin.lt_def, i0, i1] at hj1 hj2
      have hne1 : j1.val ≠ 1 := fun h => hj1.1 (Fin.ext h)
      have hne2 : j2.val ≠ 1 := fun h => hj2.1 (Fin.ext h)
      have hv := congrArg Fin.val h; dsimp at hv
      exact Fin.ext (by omega)
    · intro r _
      refine ⟨⟨r.val + 2, by omega⟩, ?_, Fin.ext (by dsimp; omega)⟩
      simp only [Finset.mem_erase, Finset.mem_Ioi, Fin.lt_def, i0, i1]
      exact ⟨fun h => by have := congrArg Fin.val h; simp at this, by omega⟩
    · intro j hj
      simp only [Finset.mem_erase, Finset.mem_Ioi, Fin.lt_def, i0, i1] at hj
      have hne : j.val ≠ 1 := fun h => hj.1 (Fin.ext h)
      have hjeq : (⟨j.val - 2 + 2, by omega⟩ : Fin (2 * (n + 1))) = j := Fin.ext (by dsimp; omega)
      simp only [hjeq]
  have hi1 : (∏ j ∈ Finset.Ioi i1, (Z j - Z i1)) =
      ∏ r : Fin (2 * n), (Z ⟨r.val + 2, by omega⟩ - Z i1) := by
    refine Finset.prod_bij (fun (j : Fin (2 * (n + 1))) hj => ⟨j.val - 2, by
        simp only [Finset.mem_Ioi, Fin.lt_def, i1] at hj; omega⟩) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro j1 hj1 j2 hj2 h
      simp only [Finset.mem_Ioi, Fin.lt_def, i1] at hj1 hj2
      have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega)
    · intro r _
      refine ⟨⟨r.val + 2, by omega⟩, ?_, Fin.ext (by dsimp; omega)⟩
      simp only [Finset.mem_Ioi, Fin.lt_def, i1]; omega
    · intro j hj
      simp only [Finset.mem_Ioi, Fin.lt_def, i1] at hj
      have hjeq : (⟨j.val - 2 + 2, by omega⟩ : Fin (2 * (n + 1))) = j := Fin.ext (by dsimp; omega)
      simp only [hjeq]
  have htail : (∏ r : Fin (2 * n), ∏ j ∈ Finset.Ioi (⟨r.val + 2, by omega⟩ : Fin (2 * (n + 1))),
      (Z j - Z ⟨r.val + 2, by omega⟩)) =
      ∏ r : Fin (2 * n), ∏ s ∈ Finset.Ioi r, (Z ⟨s.val + 2, by omega⟩ - Z ⟨r.val + 2, by omega⟩) := by
    apply Finset.prod_congr rfl; intro r _
    refine Finset.prod_bij (fun (j : Fin (2 * (n + 1))) hj => ⟨j.val - 2, by
        simp only [Finset.mem_Ioi, Fin.lt_def] at hj; omega⟩) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ioi, Fin.lt_def] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 h
      simp only [Finset.mem_Ioi, Fin.lt_def] at hj1 hj2
      have hv := congrArg Fin.val h; dsimp at hv; exact Fin.ext (by omega)
    · intro s hs
      simp only [Finset.mem_Ioi, Fin.lt_def] at hs
      refine ⟨⟨s.val + 2, by omega⟩, ?_, Fin.ext (by dsimp; omega)⟩
      simp only [Finset.mem_Ioi, Fin.lt_def]; omega
    · intro j hj
      simp only [Finset.mem_Ioi, Fin.lt_def] at hj
      have hjeq : (⟨j.val - 2 + 2, by omega⟩ : Fin (2 * (n + 1))) = j := Fin.ext (by dsimp; omega)
      simp only [hjeq]
  rw [hi0, hi1, htail, Finset.prod_mul_distrib]
  ring

lemma masterEq_row_perm (n : ℕ) (Z : Fin (2 * n) → E6) (τ : Equiv.Perm (Fin (2 * n)))
    (A B : E6) :
    ((Vmat (2 * n) (Z ∘ τ)).det * A = B * (Dmat n (Z ∘ τ)).det) ↔
    ((Vmat (2 * n) Z).det * A = B * (Dmat n Z).det) := by
  have hV : (Vmat (2 * n) (Z ∘ τ)).det = (Equiv.Perm.sign τ : E6) * (Vmat (2 * n) Z).det := by
    have hsub : Vmat (2 * n) (Z ∘ τ) = (Vmat (2 * n) Z).submatrix τ id := rfl
    rw [hsub, Matrix.det_permute]
  have hD : (Dmat n (Z ∘ τ)).det = (Equiv.Perm.sign τ : E6) * (Dmat n Z).det := by
    have hsub : Dmat n (Z ∘ τ) = (Dmat n Z).submatrix τ id := rfl
    rw [hsub, Matrix.det_permute]
  have hsign_ne : (Equiv.Perm.sign τ : E6) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simp
  rw [hV, hD]
  constructor
  · intro h
    apply mul_left_cancel₀ hsign_ne
    calc (Equiv.Perm.sign τ : E6) * ((Vmat (2 * n) Z).det * A)
        = (Equiv.Perm.sign τ : E6) * (Vmat (2 * n) Z).det * A := by ring
      _ = B * ((Equiv.Perm.sign τ : E6) * (Dmat n Z).det) := h
      _ = (Equiv.Perm.sign τ : E6) * (B * (Dmat n Z).det) := by ring
  · intro h
    calc (Equiv.Perm.sign τ : E6) * (Vmat (2 * n) Z).det * A
        = (Equiv.Perm.sign τ : E6) * ((Vmat (2 * n) Z).det * A) := by ring
      _ = (Equiv.Perm.sign τ : E6) * (B * (Dmat n Z).det) := by rw [h]
      _ = B * ((Equiv.Perm.sign τ : E6) * (Dmat n Z).det) := by ring

lemma masterEq_perm_y (n : ℕ) (x y : Fin n → E6) (α β : E6) (σ : Fin n ≃ Fin n)
    (hcomm : ∀ j k, Bmat n x (y j) α β * Bmat n x (y k) α β = Bmat n x (y k) α β * Bmat n x (y j) α β) :
    MasterEq n x (y ∘ σ) α β ↔ MasterEq n x y α β := by
  unfold MasterEq
  rw [Z_n_comp_perm n x y α β σ hcomm]
  have hpref : pref n x (y ∘ σ) α β = pref n x y α β := by
    unfold pref; congr 2
    exact Fintype.prod_equiv σ _ _ (fun _ => rfl)
  rw [hpref]
  let τ : Equiv.Perm (Fin (2 * n)) :=
    { toFun := fun i => if h : i.val < n then i else ⟨n + (σ ⟨i.val - n, by omega⟩).val, by omega⟩
      invFun := fun i => if h : i.val < n then i else ⟨n + (σ.symm ⟨i.val - n, by omega⟩).val, by omega⟩
      left_inv := fun i => by
        by_cases h : i.val < n
        · simp [h]
        · have h2 : ¬ (n + (σ ⟨i.val - n, by omega⟩).val < n) := by omega
          simp only [h, h2, dite_false]
          apply Fin.ext; dsimp
          have heq : (⟨n + (σ ⟨i.val - n, by omega⟩).val - n, by omega⟩ : Fin n) = σ ⟨i.val - n, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [heq, σ.symm_apply_apply]; dsimp; omega
      right_inv := fun i => by
        by_cases h : i.val < n
        · simp [h]
        · have h2 : ¬ (n + (σ.symm ⟨i.val - n, by omega⟩).val < n) := by omega
          simp only [h, h2, dite_false]
          apply Fin.ext; dsimp
          have heq : (⟨n + (σ.symm ⟨i.val - n, by omega⟩).val - n, by omega⟩ : Fin n) = σ.symm ⟨i.val - n, by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [heq, σ.apply_symm_apply]; dsimp; omega }
  have hZ : Zvec n x (y ∘ σ) = Zvec n x y ∘ τ := by
    funext i
    simp only [Function.comp_apply, Zvec, τ, Equiv.coe_fn_mk]
    by_cases h : i.val < n
    · simp [h]
    · have h2 : ¬ (n + (σ ⟨i.val - n, by omega⟩).val < n) := by omega
      simp only [h, h2, dite_false]
      have hidx : (⟨n + (σ ⟨i.val - n, by omega⟩).val - n, by omega⟩ : Fin n) = σ ⟨i.val - n, by omega⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hidx]
  rw [hZ]
  exact masterEq_row_perm n (Zvec n x y) τ _ _

/- Permutation moving row `n + 1` to row `1` (bringing `y 0` next to `x 0`) -/
def moveY0Perm (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) where
  toFun i :=
    if i.val = 0 then ⟨0, by omega⟩
    else if i.val = 1 then ⟨n + 1, by omega⟩
    else if i.val < n + 2 then ⟨i.val - 1, by omega⟩
    else i
  invFun i :=
    if i.val = 0 then ⟨0, by omega⟩
    else if h : i.val < n + 1 then ⟨i.val + 1, by omega⟩
    else if i.val = n + 1 then ⟨1, by omega⟩
    else i
  left_inv i := by
    have hi := i.isLt
    apply Fin.ext; dsimp only
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases h1 : i.val = 1
      · simp [h0, h1, show ¬ (n + 1 < n + 1) by omega, Nat.mod_eq_of_lt (show 1 < 2 * (n + 1) by omega)]
      · by_cases h2 : i.val < n + 2
        · have h3 : i.val - 1 ≠ 0 := by omega
          have h4 : i.val - 1 < n + 1 := by omega
          simp [h0, h1, h2, h3, h4]; omega
        · have h3 : ¬ (i.val < n + 1) := by omega
          have h4 : i.val ≠ n + 1 := by omega
          simp [h0, h1, h2, h3, h4]
  right_inv i := by
    have hi := i.isLt
    apply Fin.ext; dsimp only
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases h1 : i.val < n + 1
      · have h2 : i.val + 1 ≠ 0 := by omega
        have h3 : i.val + 1 ≠ 1 := by omega
        have h4 : i.val + 1 < n + 2 := by omega
        simp [h0, h1, h2, h3, h4]
      · by_cases h2 : i.val = n + 1
        · simp [h0, h1, h2, Nat.mod_eq_of_lt (show 1 < 2 * (n + 1) by omega)]
        · have h3 : i.val ≠ 1 := by omega
          have h4 : ¬ (i.val < n + 2) := by omega
          simp [h0, h1, h2, h3, h4]

lemma masterEq_at_y0 (n : ℕ) (x y : Fin (n + 1) → E6) (α β : E6)
    (hx : ∀ j, x j ≠ 0) (hy : ∀ k, y k ≠ 0) (hx0 : x 0 = y 0)
    (hIH : MasterEq n (fun j => x j.succ) (fun k => y k.succ) α β) :
    MasterEq (n + 1) x y α β := by
  unfold MasterEq
  rw [← masterEq_row_perm (n + 1) (Zvec (n + 1) x y) (moveY0Perm n)]
  set Z' := Zvec (n + 1) x y ∘ moveY0Perm n
  have hZ0 : Z' ⟨0, by omega⟩ = y 0 ^ 2 + (y 0 ^ 2)⁻¹ := by
    simp [Z', Zvec, moveY0Perm, hx0]
  have hZ1 : Z' ⟨1, by omega⟩ = -q * y 0 ^ 2 - q⁻¹ * (y 0 ^ 2)⁻¹ := by
    have h1 : ¬ (n + 1 < n + 1) := by omega
    simp only [Z', Function.comp_apply, Zvec, moveY0Perm, Equiv.coe_fn_mk,
      show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true, h1, dite_false]
    have hsub : (⟨n + 1 - (n + 1), by omega⟩ : Fin (n + 1)) = 0 := Fin.ext (by dsimp; omega)
    rw [hsub]
  have hZtail : (fun r : Fin (2 * n) => Z' ⟨r.val + 2, by omega⟩) =
      Zvec n (fun j => x j.succ) (fun k => y k.succ) := by
    funext r
    simp only [Z', Function.comp_apply, Zvec, moveY0Perm, Equiv.coe_fn_mk,
      show r.val + 2 ≠ 0 by omega, show r.val + 2 ≠ 1 by omega, ite_false]
    by_cases hr : r.val < n
    · have h1 : r.val + 2 < n + 2 := by omega
      have h2 : r.val + 2 - 1 < n + 1 := by omega
      simp only [h1, ite_true, h2, dite_true, hr]
      congr 2 <;> congr 1 <;> exact Fin.ext (by dsimp; omega)
    · have h1 : ¬ (r.val + 2 < n + 2) := by omega
      have h2 : ¬ (r.val + 2 < n + 1) := by omega
      simp only [h1, ite_false, h2, dite_false, hr]
      have heq : (⟨r.val + 2 - (n + 1), by omega⟩ : Fin (n + 1)) =
          (⟨r.val - n, by omega⟩ : Fin n).succ := Fin.ext (by dsimp; omega)
      rw [heq]
  obtain ⟨hT, hfac, hfx, hfy⟩ := e6_T_identities (y 0) (hy 0)
  rw [← hZ0, ← hZ1] at hT hfac
  rw [det_Vmat_split n Z', det_Dmat_reduction n Z' hT, hZtail]
  simp_rw [hfac, Finset.prod_mul_distrib]
  rw [Z_n_freeze_top_0 n x y α β (hy 0) hx0]
  have hpref_split : pref (n + 1) x y α β =
      c * sig (y 0 ^ 2) * (α * y 0 + β * (y 0)⁻¹) *
      pref n (fun j => x j.succ) (fun k => y k.succ) α β := by
    unfold pref
    rw [pow_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, hx0]
    ring
  rw [hpref_split]
  set u0 := -(Z' ⟨0, by omega⟩ + Z' ⟨1, by omega⟩)
  have hu0_eq : u0 = -((y 0 ^ 2 + (y 0 ^ 2)⁻¹) + (-q * y 0 ^ 2 - q⁻¹ * (y 0 ^ 2)⁻¹)) := by
    simp only [u0, hZ0, hZ1]
  have hprod_match :
      (∏ j : Fin n, sig (q * (y 0 * (x j.succ)⁻¹)) * sig (q * (y 0 * x j.succ))) *
      (∏ k : Fin n, sig (q * (y k.succ * (y 0)⁻¹)) * sig (y k.succ * y 0)) =
      ∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - u0) := by
    let he : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
      { toFun := Sum.elim (fun j => ⟨j.val, by omega⟩) (fun k => ⟨n + k.val, by omega⟩)
        invFun := fun r => if h : r.val < n then Sum.inl ⟨r.val, h⟩ else Sum.inr ⟨r.val - n, by omega⟩
        left_inv := fun s => by cases s with | inl j => simp [j.isLt] | inr k => simp [show ¬ n + k.val < n by omega]
        right_inv := fun r => by
          by_cases h : r.val < n
          · simp [h]
          · simp only [h, dite_false, Sum.elim_inr]; exact Fin.ext (by dsimp; omega) }
    rw [← Fintype.prod_equiv he _ _ (fun _ => rfl), Fintype.prod_sum_type]
    have hL1 : (∏ j : Fin n, sig (q * (y 0 * (x j.succ)⁻¹)) * sig (q * (y 0 * x j.succ))) =
        (-1 : E6) ^ n * ∏ j : Fin n, (Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ - u0) := by
      have hterm : ∀ j : Fin n,
          sig (q * (y 0 * (x j.succ)⁻¹)) * sig (q * (y 0 * x j.succ)) =
          (-1 : E6) * (Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ - u0) := by
        intro j
        have hZj : Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ = x j.succ ^ 2 + (x j.succ ^ 2)⁻¹ := by
          have := congrFun hZtail (he (Sum.inl j))
          rw [this]; simp [Zvec, he, j.isLt]
        rw [hZj, hu0_eq, hfx (x j.succ) (hx j.succ)]; ring
      simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hL2 : (∏ k : Fin n, sig (q * (y k.succ * (y 0)⁻¹)) * sig (y k.succ * y 0)) =
        (-1 : E6) ^ n * ∏ k : Fin n, (Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ - u0) := by
      have hterm : ∀ k : Fin n,
          sig (q * (y k.succ * (y 0)⁻¹)) * sig (y k.succ * y 0) =
          (-1 : E6) * (Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ - u0) := by
        intro k
        have hZk : Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ =
            -q * y k.succ ^ 2 - q⁻¹ * (y k.succ ^ 2)⁻¹ := by
          have := congrFun hZtail (he (Sum.inr k))
          rw [this]; dsimp only [Zvec, he, Equiv.coe_fn_mk, Sum.elim_inr]
          rw [dif_neg (show ¬ (n + k.val < n) by omega)]
          have hsub : (⟨n + k.val - n, by omega⟩ : Fin n) = k := Fin.ext (by dsimp; omega)
          rw [hsub]
        rw [hZk, hu0_eq, hfy (y k.succ) (hy k.succ)]; ring
      simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hL1, hL2]
    have hsign : (-1 : E6) ^ n * (-1 : E6) ^ n = 1 := by
      rw [← mul_pow]; simp
    calc (-1 : E6) ^ n * (∏ j, (Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ - u0)) *
          ((-1 : E6) ^ n * (∏ k, (Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ - u0)))
        = ((-1 : E6) ^ n * (-1 : E6) ^ n) *
          ((∏ j, (Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ - u0)) *
           (∏ k, (Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ - u0))) := by ring
      _ = _ := by rw [hsign, one_mul]
  have hIH' : (Vmat (2 * n) (Zvec n (fun j => x j.succ) (fun k => y k.succ))).det *
      Z_n n (fun j => x j.succ) (fun k => y k.succ) α β =
      pref n (fun j => x j.succ) (fun k => y k.succ) α β *
      (Dmat n (Zvec n (fun j => x j.succ) (fun k => y k.succ))).det := hIH
  have hprod_match' :
      (∏ j : Fin n, sig (q * (y 0 * (x j.succ)⁻¹)) * sig (q * (y 0 * x j.succ))) *
      (∏ k : Fin n, sig (q * (y k.succ * (y 0)⁻¹)) * sig (y k.succ * y 0)) =
      ∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - -(Z' ⟨0, by omega⟩ + Z' ⟨1, by omega⟩)) :=
    hprod_match
  calc (Z' ⟨1, by omega⟩ - Z' ⟨0, by omega⟩) *
        ((∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨0, by omega⟩)) *
         (∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨1, by omega⟩))) *
        (Vmat (2 * n) (Zvec n (fun j => x j.succ) (fun k => y k.succ))).det *
        (c * (α * y 0 + β * (y 0)⁻¹) * sig (y 0 ^ 2) *
          (∏ j : Fin n, sig (q * (y 0 * (x j.succ)⁻¹)) * sig (q * (y 0 * x j.succ))) *
          (∏ k : Fin n, sig (q * (y k.succ * (y 0)⁻¹)) * sig (y k.succ * y 0)) *
          Z_n n (fun j => x j.succ) (fun k => y k.succ) α β)
      = (Z' ⟨1, by omega⟩ - Z' ⟨0, by omega⟩) *
        ((∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨0, by omega⟩)) *
         (∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨1, by omega⟩))) *
        ((∏ j : Fin n, sig (q * (y 0 * (x j.succ)⁻¹)) * sig (q * (y 0 * x j.succ))) *
         (∏ k : Fin n, sig (q * (y k.succ * (y 0)⁻¹)) * sig (y k.succ * y 0))) *
        (c * sig (y 0 ^ 2) * (α * y 0 + β * (y 0)⁻¹)) *
        ((Vmat (2 * n) (Zvec n (fun j => x j.succ) (fun k => y k.succ))).det *
          Z_n n (fun j => x j.succ) (fun k => y k.succ) α β) := by ring
    _ = (Z' ⟨1, by omega⟩ - Z' ⟨0, by omega⟩) *
        ((∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨0, by omega⟩)) *
         (∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨1, by omega⟩))) *
        (∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - -(Z' ⟨0, by omega⟩ + Z' ⟨1, by omega⟩))) *
        (c * sig (y 0 ^ 2) * (α * y 0 + β * (y 0)⁻¹)) *
        (pref n (fun j => x j.succ) (fun k => y k.succ) α β *
          (Dmat n (Zvec n (fun j => x j.succ) (fun k => y k.succ))).det) := by
        rw [hprod_match', hIH']
    _ = _ := by ring

/- Permutation moving row `2 * n + 1` to row `1` (bringing `y (Fin.last n)` next to `x 0`) -/
def moveYLastPerm (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) where
  toFun i :=
    if i.val = 0 then ⟨0, by omega⟩
    else if i.val = 1 then ⟨2 * n + 1, by omega⟩
    else ⟨i.val - 1, by omega⟩
  invFun i :=
    if i.val = 0 then ⟨0, by omega⟩
    else if h : i.val = 2 * n + 1 then ⟨1, by omega⟩
    else ⟨i.val + 1, by omega⟩
  left_inv i := by
    have hi := i.isLt
    apply Fin.ext; dsimp only
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases h1 : i.val = 1
      · simp [h0, h1, Nat.mod_eq_of_lt (show 1 < 2 * (n + 1) by omega)]
      · have h2 : i.val - 1 ≠ 0 := by omega
        have h3 : i.val - 1 ≠ 2 * n + 1 := by omega
        simp [h0, h1, h2, h3]; omega
  right_inv i := by
    have hi := i.isLt
    apply Fin.ext; dsimp only
    by_cases h0 : i.val = 0
    · simp [h0]
    · by_cases h1 : i.val = 2 * n + 1
      · simp [h0, h1, Nat.mod_eq_of_lt (show 1 < 2 * (n + 1) by omega)]
      · have h2 : i.val + 1 ≠ 0 := by omega
        have h3 : i.val + 1 ≠ 1 := by omega
        simp [h0, h1, h2, h3]

lemma masterEq_at_ylast_inv (n : ℕ) (x y : Fin (n + 1) → E6) (α β : E6)
    (hx : ∀ j, x j ≠ 0) (hy : ∀ k, y k ≠ 0) (hx0 : x 0 = (y (Fin.last n))⁻¹)
    (hIH : MasterEq n (fun j => x j.succ) (fun k => y k.castSucc) α β) :
    MasterEq (n + 1) x y α β := by
  unfold MasterEq
  rw [← masterEq_row_perm (n + 1) (Zvec (n + 1) x y) (moveYLastPerm n)]
  set Z' := Zvec (n + 1) x y ∘ moveYLastPerm n
  set yl := y (Fin.last n)
  have hyl : yl ≠ 0 := hy (Fin.last n)
  have hZ0 : Z' ⟨0, by omega⟩ = yl ^ 2 + (yl ^ 2)⁻¹ := by
    simp only [Z', Function.comp_apply, Zvec, moveYLastPerm, Equiv.coe_fn_mk, ite_true,
      Nat.zero_lt_succ, dite_true]
    change x 0 ^ 2 + (x 0 ^ 2)⁻¹ = yl ^ 2 + (yl ^ 2)⁻¹
    rw [hx0, inv_pow, inv_inv, add_comm]
  have hZ1 : Z' ⟨1, by omega⟩ = -q * yl ^ 2 - q⁻¹ * (yl ^ 2)⁻¹ := by
    have h1 : ¬ (2 * n + 1 < n + 1) := by omega
    simp only [Z', Function.comp_apply, Zvec, moveYLastPerm, Equiv.coe_fn_mk,
      show (1 : ℕ) ≠ 0 by omega, ite_false, ite_true, h1, dite_false]
    have hsub : (⟨2 * n + 1 - (n + 1), by omega⟩ : Fin (n + 1)) = Fin.last n :=
      Fin.ext (by dsimp [Fin.last]; omega)
    rw [hsub]
  have hZtail : (fun r : Fin (2 * n) => Z' ⟨r.val + 2, by omega⟩) =
      Zvec n (fun j => x j.succ) (fun k => y k.castSucc) := by
    funext r
    simp only [Z', Function.comp_apply, Zvec, moveYLastPerm, Equiv.coe_fn_mk,
      show r.val + 2 ≠ 0 by omega, show r.val + 2 ≠ 1 by omega, ite_false]
    by_cases hr : r.val < n
    · have h1 : r.val + 2 - 1 < n + 1 := by omega
      simp only [h1, dite_true, hr]
      congr 2 <;> congr 1 <;> exact Fin.ext (by dsimp; omega)
    · have h1 : ¬ (r.val + 2 - 1 < n + 1) := by omega
      simp only [h1, dite_false, hr]
      have heq : (⟨r.val + 2 - 1 - (n + 1), by omega⟩ : Fin (n + 1)) =
          (⟨r.val - n, by omega⟩ : Fin n).castSucc := Fin.ext (by dsimp; omega)
      rw [heq]
  obtain ⟨hT, hfac, hfx, hfy⟩ := e6_T_identities yl hyl
  rw [← hZ0, ← hZ1] at hT hfac
  rw [det_Vmat_split n Z', det_Dmat_reduction n Z' hT, hZtail]
  simp_rw [hfac, Finset.prod_mul_distrib]
  rw [Z_n_freeze_bot_last n x y α β hyl hx0]
  have hpref_split : pref (n + 1) x y α β =
      c * sig (yl ^ 2) * (α * yl⁻¹ + β * yl) *
      pref n (fun j => x j.succ) (fun k => y k.castSucc) α β := by
    unfold pref
    rw [pow_succ, Fin.prod_univ_castSucc, Fin.prod_univ_succ, hx0, inv_inv]
    ring
  rw [hpref_split]
  set u0 := -(Z' ⟨0, by omega⟩ + Z' ⟨1, by omega⟩)
  have hu0_eq : u0 = -((yl ^ 2 + (yl ^ 2)⁻¹) + (-q * yl ^ 2 - q⁻¹ * (yl ^ 2)⁻¹)) := by
    simp only [u0, hZ0, hZ1]
  have hprod_match :
      (∏ j : Fin n, sig (q * (yl * (x j.succ)⁻¹)) * sig (q * (yl * x j.succ))) *
      (∏ k : Fin n, sig (q * (y k.castSucc * yl⁻¹)) * sig (y k.castSucc * yl)) =
      ∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - u0) := by
    let he : Fin n ⊕ Fin n ≃ Fin (2 * n) :=
      { toFun := Sum.elim (fun j => ⟨j.val, by omega⟩) (fun k => ⟨n + k.val, by omega⟩)
        invFun := fun r => if h : r.val < n then Sum.inl ⟨r.val, h⟩ else Sum.inr ⟨r.val - n, by omega⟩
        left_inv := fun s => by cases s with | inl j => simp [j.isLt] | inr k => simp [show ¬ n + k.val < n by omega]
        right_inv := fun r => by
          by_cases h : r.val < n
          · simp [h]
          · simp only [h, dite_false, Sum.elim_inr]; exact Fin.ext (by dsimp; omega) }
    rw [← Fintype.prod_equiv he _ _ (fun _ => rfl), Fintype.prod_sum_type]
    have hL1 : (∏ j : Fin n, sig (q * (yl * (x j.succ)⁻¹)) * sig (q * (yl * x j.succ))) =
        (-1 : E6) ^ n * ∏ j : Fin n, (Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ - u0) := by
      have hterm : ∀ j : Fin n,
          sig (q * (yl * (x j.succ)⁻¹)) * sig (q * (yl * x j.succ)) =
          (-1 : E6) * (Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ - u0) := by
        intro j
        have hZj : Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ = x j.succ ^ 2 + (x j.succ ^ 2)⁻¹ := by
          have := congrFun hZtail (he (Sum.inl j))
          rw [this]; simp [Zvec, he, j.isLt]
        rw [hZj, hu0_eq, hfx (x j.succ) (hx j.succ)]; ring
      simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hL2 : (∏ k : Fin n, sig (q * (y k.castSucc * yl⁻¹)) * sig (y k.castSucc * yl)) =
        (-1 : E6) ^ n * ∏ k : Fin n, (Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ - u0) := by
      have hterm : ∀ k : Fin n,
          sig (q * (y k.castSucc * yl⁻¹)) * sig (y k.castSucc * yl) =
          (-1 : E6) * (Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ - u0) := by
        intro k
        have hZk : Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ =
            -q * y k.castSucc ^ 2 - q⁻¹ * (y k.castSucc ^ 2)⁻¹ := by
          have := congrFun hZtail (he (Sum.inr k))
          rw [this]; dsimp only [Zvec, he, Equiv.coe_fn_mk, Sum.elim_inr]
          rw [dif_neg (show ¬ (n + k.val < n) by omega)]
          have hsub : (⟨n + k.val - n, by omega⟩ : Fin n) = k := Fin.ext (by dsimp; omega)
          rw [hsub]
        rw [hZk, hu0_eq, hfy (y k.castSucc) (hy k.castSucc)]; ring
      simp_rw [hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hL1, hL2]
    have hsign : (-1 : E6) ^ n * (-1 : E6) ^ n = 1 := by rw [← mul_pow]; simp
    calc (-1 : E6) ^ n * (∏ j, (Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ - u0)) *
          ((-1 : E6) ^ n * (∏ k, (Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ - u0)))
        = ((-1 : E6) ^ n * (-1 : E6) ^ n) *
          ((∏ j, (Z' ⟨(he (Sum.inl j)).val + 2, by omega⟩ - u0)) *
           (∏ k, (Z' ⟨(he (Sum.inr k)).val + 2, by omega⟩ - u0))) := by ring
      _ = _ := by rw [hsign, one_mul]
  have hIH' : (Vmat (2 * n) (Zvec n (fun j => x j.succ) (fun k => y k.castSucc))).det *
      Z_n n (fun j => x j.succ) (fun k => y k.castSucc) α β =
      pref n (fun j => x j.succ) (fun k => y k.castSucc) α β *
      (Dmat n (Zvec n (fun j => x j.succ) (fun k => y k.castSucc))).det := hIH
  have hprod_match' :
      (∏ j : Fin n, sig (q * (yl * (x j.succ)⁻¹)) * sig (q * (yl * x j.succ))) *
      (∏ k : Fin n, sig (q * (y k.castSucc * yl⁻¹)) * sig (y k.castSucc * yl)) =
      ∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - -(Z' ⟨0, by omega⟩ + Z' ⟨1, by omega⟩)) :=
    hprod_match
  calc (Z' ⟨1, by omega⟩ - Z' ⟨0, by omega⟩) *
        ((∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨0, by omega⟩)) *
         (∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨1, by omega⟩))) *
        (Vmat (2 * n) (Zvec n (fun j => x j.succ) (fun k => y k.castSucc))).det *
        (c * (α * yl⁻¹ + β * yl) * sig (yl ^ 2) *
          (∏ j : Fin n, sig (q * (yl * (x j.succ)⁻¹)) * sig (q * (yl * x j.succ))) *
          (∏ k : Fin n, sig (q * (y k.castSucc * yl⁻¹)) * sig (y k.castSucc * yl)) *
          Z_n n (fun j => x j.succ) (fun k => y k.castSucc) α β)
      = (Z' ⟨1, by omega⟩ - Z' ⟨0, by omega⟩) *
        ((∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨0, by omega⟩)) *
         (∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨1, by omega⟩))) *
        ((∏ j : Fin n, sig (q * (yl * (x j.succ)⁻¹)) * sig (q * (yl * x j.succ))) *
         (∏ k : Fin n, sig (q * (y k.castSucc * yl⁻¹)) * sig (y k.castSucc * yl))) *
        (c * sig (yl ^ 2) * (α * yl⁻¹ + β * yl)) *
        ((Vmat (2 * n) (Zvec n (fun j => x j.succ) (fun k => y k.castSucc))).det *
          Z_n n (fun j => x j.succ) (fun k => y k.castSucc) α β) := by ring
    _ = (Z' ⟨1, by omega⟩ - Z' ⟨0, by omega⟩) *
        ((∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨0, by omega⟩)) *
         (∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - Z' ⟨1, by omega⟩))) *
        (∏ r : Fin (2 * n), (Z' ⟨r.val + 2, by omega⟩ - -(Z' ⟨0, by omega⟩ + Z' ⟨1, by omega⟩))) *
        (c * sig (yl ^ 2) * (α * yl⁻¹ + β * yl)) *
        (pref n (fun j => x j.succ) (fun k => y k.castSucc) α β *
          (Dmat n (Zvec n (fun j => x j.succ) (fun k => y k.castSucc))).det) := by
        rw [hprod_match', hIH']
    _ = _ := by ring

/- ### 5.6. Interpolation step (6n+4 distinct points vs degree ≤ 6n+3) + Density lift + Master Theorem -/

lemma masterEq_of_Zvec_eq {n : ℕ} {x y : Fin n → E6} {α β : E6}
    {i j : Fin (2 * n)} (hij : i ≠ j) (hZ : Zvec n x y i = Zvec n x y j) :
    MasterEq n x y α β := by
  unfold MasterEq
  have hV : (Vmat (2 * n) (Zvec n x y)).det = 0 :=
    Matrix.det_zero_of_row_eq hij (funext fun s => by simp [Vmat, hZ])
  have hD : (Dmat n (Zvec n x y)).det = 0 :=
    Matrix.det_zero_of_row_eq hij (funext fun s => by simp [Dmat, hZ])
  rw [hV, hD, zero_mul, mul_zero]

lemma rat_gt_one_ne_zero (r : ℚ) (hr : 1 < r) : (r : E6) ≠ 0 := by
  intro h
  have := E6.ratCast_inj (by simpa using h : (r : E6) = ((0 : ℚ) : E6))
  linarith

lemma sig_rat_gt_one_ne_zero (r1 r2 : ℚ) (h1 : 1 < r1) (h2 : 1 < r2) :
    sig ((r1 : E6) * (r2 : E6)) ≠ 0 := by
  intro h
  have hprod : (r1 : E6) * (r2 : E6) = ((r1 * r2 : ℚ) : E6) := (Rat.cast_mul r1 r2).symm
  have hinv : (((r1 * r2 : ℚ) : E6))⁻¹ = (((r1 * r2)⁻¹ : ℚ) : E6) := (Rat.cast_inv (r1 * r2)).symm
  rw [sig, hprod, hinv] at h
  have hre := congrArg E6.re h
  simp only [E6.sub_re, E6.ratCast_re, E6.zero_re] at hre
  have hgt : 1 < r1 * r2 := by nlinarith
  have hlt : (r1 * r2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hgt
  linarith

lemma sig_q_rat_div_ne_zero (r1 r2 : ℚ) (h1 : 0 < r1) (h2 : 0 < r2) :
    sig (q * ((r1 : E6) * (r2 : E6)⁻¹)) ≠ 0 := by
  intro h
  set t : ℚ := r1 / r2
  have ht : 0 < t := div_pos h1 h2
  have hrat : (r1 : E6) * (r2 : E6)⁻¹ = (t : E6) := by
    rw [← div_eq_mul_inv, ← Rat.cast_div]
  have hinv : (t : E6)⁻¹ = ((t⁻¹ : ℚ) : E6) := (Rat.cast_inv t).symm
  rw [sig, hrat, mul_inv, q_inv, hinv] at h
  have him := congrArg E6.im h
  simp only [E6.sub_im, E6.mul_im, E6.ratCast_re, E6.ratCast_im, E6.q_re, E6.q_im,
    E6.one_im, E6.zero_im] at him
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  linarith

lemma masterEq_step_generic (n : ℕ) (a : Fin n → ℚ) (b : Fin (n + 1) → ℚ) (α β : E6)
    (ha1 : ∀ j, 1 < a j) (hb1 : ∀ k, 1 < b k)
    (ha_inj : Function.Injective a) (hb_inj : Function.Injective b)
    (hab : ∀ j k, a j ≠ b k)
    (hIH : ∀ (x' y' : Fin n → E6), (∀ j, x' j ≠ 0) → (∀ k, y' k ≠ 0) → MasterEq n x' y' α β) :
    ∀ x0 : E6, x0 ≠ 0 →
      MasterEq (n + 1) (Fin.cons x0 (fun j => (a j : E6))) (fun k => (b k : E6)) α β := by
  let xt : Fin n → E6 := fun j => (a j : E6)
  let y : Fin (n + 1) → E6 := fun k => (b k : E6)
  have hxt_ne : ∀ j, xt j ≠ 0 := fun j => rat_gt_one_ne_zero (a j) (ha1 j)
  have hy_ne : ∀ k, y k ≠ 0 := fun k => rat_gt_one_ne_zero (b k) (hb1 k)
  -- Both sides satisfy `IsPolyInSq (6 * n + 3)` in `x0`
  have hLHS : IsPolyInSq (6 * n + 3)
      (fun x0 => (Vmat (2 * (n + 1)) (Zvec (n + 1) (Fin.cons x0 xt) y)).det *
                 Z_n (n + 1) (Fin.cons x0 xt) y α β) := by
    have h := isPolyInSq_mul (isPolyInSq_Vmat n xt y) (isPolyInSq_Z_n n xt y α β)
    rwa [show 4 * n + 2 + (2 * n + 1) = 6 * n + 3 by omega] at h
  have hRHS : IsPolyInSq (6 * n + 3)
      (fun x0 => pref (n + 1) (Fin.cons x0 xt) y α β *
                 (Dmat (n + 1) (Zvec (n + 1) (Fin.cons x0 xt) y)).det) := by
    have hpref : IsPolyInSq 1 (fun x0 => pref (n + 1) (Fin.cons x0 xt) y α β) := by
      have hrewrite : (fun x0 => pref (n + 1) (Fin.cons x0 xt) y α β) =
          fun x0 => (c ^ (n + 1) * (∏ k : Fin (n + 1), sig (y k ^ 2)) *
                     (∏ j : Fin n, (α * xt j + β * (xt j)⁻¹))) * (α * x0 + β * x0⁻¹) := by
        funext x0; unfold pref
        let x' : Fin (n + 1) → E6 := Fin.cons x0 xt
        have hpx : (∏ j : Fin (n + 1), (α * x' j + β * (x' j)⁻¹)) =
            (α * x0 + β * x0⁻¹) * ∏ j : Fin n, (α * xt j + β * (xt j)⁻¹) := by
          rw [Fin.prod_univ_succ]; simp only [x', Fin.cons_zero, Fin.cons_succ]
        change c ^ (n + 1) * (∏ k : Fin (n + 1), sig (y k ^ 2)) *
            (∏ j : Fin (n + 1), (α * x' j + β * (x' j)⁻¹)) = _
        rw [hpx]; ring
      rw [hrewrite]
      have hm := isPolyInSq_mul (isPolyInSq_const (c ^ (n + 1) * (∏ k : Fin (n + 1), sig (y k ^ 2)) *
                     (∏ j : Fin n, (α * xt j + β * (xt j)⁻¹)))) (isPolyInSq_lin α β)
      rwa [zero_add] at hm
    have h := isPolyInSq_mul hpref (isPolyInSq_Dmat n xt y)
    rwa [show 1 + (6 * n + 2) = 6 * n + 3 by omega] at h
  obtain ⟨P, hPd, hP⟩ := hLHS
  obtain ⟨Q, hQd, hQ⟩ := hRHS
  -- Build the 6n + 4 distinct interpolation points `w = z^2` via an explicit sum type
  let Idx := Fin n ⊕ Fin n ⊕ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin (n + 1) ⊕ Fin (n + 1)
  let rootZ : Idx → E6
    | Sum.inl j => (a j : E6)
    | Sum.inr (Sum.inl j) => ((a j)⁻¹ : ℚ)
    | Sum.inr (Sum.inr (Sum.inl k)) => (b k : E6)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl k))) => ((b k)⁻¹ : ℚ)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k)))) => q ^ 2 * (b k : E6)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr k)))) => q * (((b k)⁻¹ : ℚ) : E6)
  let rootW : Idx → E6 := fun u => (rootZ u) ^ 2
  -- Helper lemmas for `rootW`'s `(re, im)` coordinates
  have hW_rat : ∀ r : ℚ, ((r : E6) ^ 2).re = r ^ 2 ∧ ((r : E6) ^ 2).im = 0 := by
    intro r
    have hsq : (r : E6) ^ 2 = ((r ^ 2 : ℚ) : E6) := (Rat.cast_pow r 2).symm
    rw [hsq]; exact ⟨E6.ratCast_re _, E6.ratCast_im _⟩
  have hW_fam5 : ∀ k : Fin (n + 1),
      ((q ^ 2 * (b k : E6)) ^ 2).re = 0 ∧ ((q ^ 2 * (b k : E6)) ^ 2).im = -(b k) ^ 2 := by
    intro k
    have hq4 : (q ^ 2) ^ 2 = -q := by
      calc (q ^ 2) ^ 2 = q ^ 3 * q := by ring
        _ = -q := by rw [q_cube]; ring
    have hsq : (q ^ 2 * (b k : E6)) ^ 2 = -q * (((b k) ^ 2 : ℚ) : E6) := by
      rw [mul_pow, hq4, ← Rat.cast_pow]
    rw [hsq]
    simp only [E6.mul_re, E6.mul_im, E6.neg_re, E6.neg_im, E6.q_re, E6.q_im, E6.ratCast_re, E6.ratCast_im]
    constructor <;> ring
  have hW_fam6 : ∀ k : Fin (n + 1),
      ((q * (((b k)⁻¹ : ℚ) : E6)) ^ 2).re = -((b k)⁻¹) ^ 2 ∧
      ((q * (((b k)⁻¹ : ℚ) : E6)) ^ 2).im = ((b k)⁻¹) ^ 2 := by
    intro k
    have hsq : (q * (((b k)⁻¹ : ℚ) : E6)) ^ 2 = (q - 1) * ((((b k)⁻¹) ^ 2 : ℚ) : E6) := by
      rw [mul_pow, q_sq, ← Rat.cast_pow]
    rw [hsq]
    simp only [E6.mul_re, E6.mul_im, E6.sub_re, E6.sub_im, E6.q_re, E6.q_im, E6.one_re, E6.one_im,
      E6.ratCast_re, E6.ratCast_im]
    constructor <;> ring
  have hsq_inj_pos : ∀ r1 r2 : ℚ, 0 < r1 → 0 < r2 → r1 ^ 2 = r2 ^ 2 → r1 = r2 := by
    intro r1 r2 h1 h2 h
    have : (r1 - r2) * (r1 + r2) = 0 := by linarith
    rcases mul_eq_zero.mp this with hsub | hadd <;> linarith
  have hW_inj : Function.Injective rootW := by
    intro u1 u2 hEq
    have hre := congrArg E6.re hEq
    have him := congrArg E6.im hEq
    rcases u1 with j1 | j1 | k1 | k1 | k1 | k1 <;>
    rcases u2 with j2 | j2 | k2 | k2 | k2 | k2
    · -- 1 vs 1
      have h1 := (hW_rat (a j1)).1; have h2 := (hW_rat (a j2)).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      exact congrArg Sum.inl (ha_inj (hsq_inj_pos _ _ (by linarith [ha1 j1]) (by linarith [ha1 j2]) hre))
    · -- 1 vs 2
      have h1 := (hW_rat (a j1)).1; have h2 := (hW_rat (a j2)⁻¹).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have : 1 < (a j1) ^ 2 := by nlinarith [ha1 j1]
      have : ((a j2)⁻¹) ^ 2 < 1 := by
        have hlt : (a j2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (ha1 j2)
        have hpos : 0 < (a j2)⁻¹ := inv_pos.mpr (by linarith [ha1 j2])
        nlinarith
      linarith
    · -- 1 vs 3
      have h1 := (hW_rat (a j1)).1; have h2 := (hW_rat (b k2)).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      exact absurd (hsq_inj_pos _ _ (by linarith [ha1 j1]) (by linarith [hb1 k2]) hre) (hab j1 k2)
    · -- 1 vs 4
      have h1 := (hW_rat (a j1)).1; have h2 := (hW_rat (b k2)⁻¹).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have : 1 < (a j1) ^ 2 := by nlinarith [ha1 j1]
      have : ((b k2)⁻¹) ^ 2 < 1 := by
        have hlt : (b k2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (hb1 k2)
        have hpos : 0 < (b k2)⁻¹ := inv_pos.mpr (by linarith [hb1 k2])
        nlinarith
      linarith
    · -- 1 vs 5
      dsimp only [rootW, rootZ] at him
      rw [(hW_rat (a j1)).2, (hW_fam5 k2).2] at him
      nlinarith [hb1 k2]
    · -- 1 vs 6
      dsimp only [rootW, rootZ] at him
      rw [(hW_rat (a j1)).2, (hW_fam6 k2).2] at him
      have : 0 < (b k2)⁻¹ := inv_pos.mpr (by linarith [hb1 k2]); nlinarith
    · -- 2 vs 1
      have h1 := (hW_rat (a j1)⁻¹).1; have h2 := (hW_rat (a j2)).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have : 1 < (a j2) ^ 2 := by nlinarith [ha1 j2]
      have : ((a j1)⁻¹) ^ 2 < 1 := by
        have hlt : (a j1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (ha1 j1)
        have hpos : 0 < (a j1)⁻¹ := inv_pos.mpr (by linarith [ha1 j1])
        nlinarith
      linarith
    · -- 2 vs 2
      have h1 := (hW_rat (a j1)⁻¹).1; have h2 := (hW_rat (a j2)⁻¹).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have hinv_eq := hsq_inj_pos _ _ (inv_pos.mpr (by linarith [ha1 j1]))
        (inv_pos.mpr (by linarith [ha1 j2])) hre
      exact congrArg (fun x => Sum.inr (Sum.inl x)) (ha_inj (inv_injective hinv_eq))
    · -- 2 vs 3
      have h1 := (hW_rat (a j1)⁻¹).1; have h2 := (hW_rat (b k2)).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have : 1 < (b k2) ^ 2 := by nlinarith [hb1 k2]
      have : ((a j1)⁻¹) ^ 2 < 1 := by
        have hlt : (a j1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (ha1 j1)
        have hpos : 0 < (a j1)⁻¹ := inv_pos.mpr (by linarith [ha1 j1])
        nlinarith
      linarith
    · -- 2 vs 4
      have h1 := (hW_rat (a j1)⁻¹).1; have h2 := (hW_rat (b k2)⁻¹).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have hinv_eq := hsq_inj_pos _ _ (inv_pos.mpr (by linarith [ha1 j1]))
        (inv_pos.mpr (by linarith [hb1 k2])) hre
      exact absurd (inv_injective hinv_eq) (hab j1 k2)
    · -- 2 vs 5
      dsimp only [rootW, rootZ] at him
      rw [(hW_rat (a j1)⁻¹).2, (hW_fam5 k2).2] at him
      nlinarith [hb1 k2]
    · -- 2 vs 6
      dsimp only [rootW, rootZ] at him
      rw [(hW_rat (a j1)⁻¹).2, (hW_fam6 k2).2] at him
      have : 0 < (b k2)⁻¹ := inv_pos.mpr (by linarith [hb1 k2]); nlinarith
    · -- 3 vs 1
      have h1 := (hW_rat (b k1)).1; have h2 := (hW_rat (a j2)).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      exact absurd (hsq_inj_pos _ _ (by linarith [hb1 k1]) (by linarith [ha1 j2]) hre).symm (hab j2 k1)
    · -- 3 vs 2
      have h1 := (hW_rat (b k1)).1; have h2 := (hW_rat (a j2)⁻¹).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have : 1 < (b k1) ^ 2 := by nlinarith [hb1 k1]
      have : ((a j2)⁻¹) ^ 2 < 1 := by
        have hlt : (a j2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (ha1 j2)
        have hpos : 0 < (a j2)⁻¹ := inv_pos.mpr (by linarith [ha1 j2])
        nlinarith
      linarith
    · -- 3 vs 3
      have h1 := (hW_rat (b k1)).1; have h2 := (hW_rat (b k2)).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inl x)))
        (hb_inj (hsq_inj_pos _ _ (by linarith [hb1 k1]) (by linarith [hb1 k2]) hre))
    · -- 3 vs 4
      have h1 := (hW_rat (b k1)).1; have h2 := (hW_rat (b k2)⁻¹).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have : 1 < (b k1) ^ 2 := by nlinarith [hb1 k1]
      have : ((b k2)⁻¹) ^ 2 < 1 := by
        have hlt : (b k2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (hb1 k2)
        have hpos : 0 < (b k2)⁻¹ := inv_pos.mpr (by linarith [hb1 k2])
        nlinarith
      linarith
    · -- 3 vs 5
      dsimp only [rootW, rootZ] at him
      rw [(hW_rat (b k1)).2, (hW_fam5 k2).2] at him
      nlinarith [hb1 k2]
    · -- 3 vs 6
      dsimp only [rootW, rootZ] at him
      rw [(hW_rat (b k1)).2, (hW_fam6 k2).2] at him
      have : 0 < (b k2)⁻¹ := inv_pos.mpr (by linarith [hb1 k2]); nlinarith
    · -- 4 vs 1
      have h1 := (hW_rat (b k1)⁻¹).1; have h2 := (hW_rat (a j2)).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have : 1 < (a j2) ^ 2 := by nlinarith [ha1 j2]
      have : ((b k1)⁻¹) ^ 2 < 1 := by
        have hlt : (b k1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (hb1 k1)
        have hpos : 0 < (b k1)⁻¹ := inv_pos.mpr (by linarith [hb1 k1])
        nlinarith
      linarith
    · -- 4 vs 2
      have h1 := (hW_rat (b k1)⁻¹).1; have h2 := (hW_rat (a j2)⁻¹).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have hinv_eq := hsq_inj_pos _ _ (inv_pos.mpr (by linarith [hb1 k1]))
        (inv_pos.mpr (by linarith [ha1 j2])) hre
      exact absurd (inv_injective hinv_eq).symm (hab j2 k1)
    · -- 4 vs 3
      have h1 := (hW_rat (b k1)⁻¹).1; have h2 := (hW_rat (b k2)).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have : 1 < (b k2) ^ 2 := by nlinarith [hb1 k2]
      have : ((b k1)⁻¹) ^ 2 < 1 := by
        have hlt : (b k1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (hb1 k1)
        have hpos : 0 < (b k1)⁻¹ := inv_pos.mpr (by linarith [hb1 k1])
        nlinarith
      linarith
    · -- 4 vs 4
      have h1 := (hW_rat (b k1)⁻¹).1; have h2 := (hW_rat (b k2)⁻¹).1
      dsimp only [rootW, rootZ] at hre; rw [h1, h2] at hre
      have hinv_eq := hsq_inj_pos _ _ (inv_pos.mpr (by linarith [hb1 k1]))
        (inv_pos.mpr (by linarith [hb1 k2])) hre
      exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inl x))))
        (hb_inj (inv_injective hinv_eq))
    · -- 4 vs 5
      dsimp only [rootW, rootZ] at him
      rw [(hW_rat (b k1)⁻¹).2, (hW_fam5 k2).2] at him
      nlinarith [hb1 k2]
    · -- 4 vs 6
      dsimp only [rootW, rootZ] at him
      rw [(hW_rat (b k1)⁻¹).2, (hW_fam6 k2).2] at him
      have : 0 < (b k2)⁻¹ := inv_pos.mpr (by linarith [hb1 k2]); nlinarith
    · -- 5 vs 1
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam5 k1).2, (hW_rat (a j2)).2] at him
      nlinarith [hb1 k1]
    · -- 5 vs 2
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam5 k1).2, (hW_rat (a j2)⁻¹).2] at him
      nlinarith [hb1 k1]
    · -- 5 vs 3
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam5 k1).2, (hW_rat (b k2)).2] at him
      nlinarith [hb1 k1]
    · -- 5 vs 4
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam5 k1).2, (hW_rat (b k2)⁻¹).2] at him
      nlinarith [hb1 k1]
    · -- 5 vs 5
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam5 k1).2, (hW_fam5 k2).2] at him
      exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl x)))))
        (hb_inj (hsq_inj_pos _ _ (by linarith [hb1 k1]) (by linarith [hb1 k2]) (by linarith)))
    · -- 5 vs 6
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam5 k1).2, (hW_fam6 k2).2] at him
      have : 0 < (b k2)⁻¹ := inv_pos.mpr (by linarith [hb1 k2]); nlinarith [hb1 k1]
    · -- 6 vs 1
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam6 k1).2, (hW_rat (a j2)).2] at him
      have : 0 < (b k1)⁻¹ := inv_pos.mpr (by linarith [hb1 k1]); nlinarith
    · -- 6 vs 2
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam6 k1).2, (hW_rat (a j2)⁻¹).2] at him
      have : 0 < (b k1)⁻¹ := inv_pos.mpr (by linarith [hb1 k1]); nlinarith
    · -- 6 vs 3
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam6 k1).2, (hW_rat (b k2)).2] at him
      have : 0 < (b k1)⁻¹ := inv_pos.mpr (by linarith [hb1 k1]); nlinarith
    · -- 6 vs 4
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam6 k1).2, (hW_rat (b k2)⁻¹).2] at him
      have : 0 < (b k1)⁻¹ := inv_pos.mpr (by linarith [hb1 k1]); nlinarith
    · -- 6 vs 5
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam6 k1).2, (hW_fam5 k2).2] at him
      have : 0 < (b k1)⁻¹ := inv_pos.mpr (by linarith [hb1 k1]); nlinarith [hb1 k2]
    · -- 6 vs 6
      dsimp only [rootW, rootZ] at him
      rw [(hW_fam6 k1).2, (hW_fam6 k2).2] at him
      have hinv_eq := hsq_inj_pos _ _ (inv_pos.mpr (by linarith [hb1 k1]))
        (inv_pos.mpr (by linarith [hb1 k2])) him
      exact congrArg (fun x => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr x)))))
        (hb_inj (inv_injective hinv_eq))
  -- Cardinality of `S = image rootW univ` is `6 * n + 4 > 6 * n + 3`
  let S : Finset E6 := Finset.univ.image rootW
  have hScard : S.card = 6 * n + 4 := by
    rw [Finset.card_image_of_injective _ hW_inj, Finset.card_univ]
    simp only [Idx, Fintype.card_sum, Fintype.card_fin]; omega
  -- Prove `P.eval (rootW u) = Q.eval (rootW u)` for every `u : Idx`
  have hPQ : P = Q := by
    apply poly_eq_of_card_roots hPd hQd S (by omega)
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨u, _, rfl⟩ := hw
    have hrootZ_ne : rootZ u ≠ 0 := by
      rcases u with j | j | k | k | k | k
      · exact hxt_ne j
      · dsimp only [rootZ]; rw [Rat.cast_inv]; exact inv_ne_zero (hxt_ne j)
      · exact hy_ne k
      · dsimp only [rootZ]; rw [Rat.cast_inv]; exact inv_ne_zero (hy_ne k)
      · exact mul_ne_zero (pow_ne_zero 2 q_ne_zero) (hy_ne k)
      · dsimp only [rootZ]; rw [Rat.cast_inv]; exact mul_ne_zero q_ne_zero (inv_ne_zero (hy_ne k))
    have hMaster_u : MasterEq (n + 1) (Fin.cons (rootZ u) xt) y α β := by
      rcases u with j | j | k | k | k | k
      · -- Family 1: `x0 = a j` => row 0 = row `j.val + 1`
        apply masterEq_of_Zvec_eq (i := ⟨0, by omega⟩) (j := ⟨j.val + 1, by omega⟩)
          (fun h => by have := congrArg Fin.val h; dsimp at this; omega)
        simp only [Zvec, Nat.zero_lt_succ, show j.val + 1 < n + 1 by omega, dite_true, rootZ]
        have h1 : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
        have h2 : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = j.succ := rfl
        rw [h1, h2]; simp [xt]
      · -- Family 2: `x0 = (a j)⁻¹` => row 0 = row `j.val + 1`
        apply masterEq_of_Zvec_eq (i := ⟨0, by omega⟩) (j := ⟨j.val + 1, by omega⟩)
          (fun h => by have := congrArg Fin.val h; dsimp at this; omega)
        simp only [Zvec, Nat.zero_lt_succ, show j.val + 1 < n + 1 by omega, dite_true, rootZ]
        have h1 : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
        have h2 : (⟨j.val + 1, by omega⟩ : Fin (n + 1)) = j.succ := rfl
        rw [h1, h2]; simp only [Fin.cons_zero, Fin.cons_succ, xt]
        rw [Rat.cast_inv, inv_pow, inv_inv, add_comm]
      · -- Family 3: `x0 = b k` => permute `y` so `y 0 = b k`, then `masterEq_at_y0`
        let x' : Fin (n + 1) → E6 := Fin.cons (b k : E6) xt
        have hx'_ne : ∀ i, x' i ≠ 0 := fun i => Fin.cases (hy_ne k) hxt_ne i
        have hcomm : ∀ k1 k2, Bmat (n + 1) x' (y k1) α β * Bmat (n + 1) x' (y k2) α β =
            Bmat (n + 1) x' (y k2) α β * Bmat (n + 1) x' (y k1) α β := fun k1 k2 =>
          Bmat_comm (n + 1) x' hx'_ne (y k1) (y k2) α β (hy_ne k1) (hy_ne k2)
            (sig_q_rat_div_ne_zero (b k1) (b k2) (by linarith [hb1 k1]) (by linarith [hb1 k2]))
            (sig_rat_gt_one_ne_zero (b k1) (b k2) (hb1 k1) (hb1 k2))
        rw [← masterEq_perm_y (n + 1) x' y α β (Equiv.swap 0 k) hcomm]
        apply masterEq_at_y0 n x'
          (y ∘ Equiv.swap 0 k) α β hx'_ne (fun i => hy_ne _)
        · simp [x', y]
        · exact hIH _ _ (fun i => hx'_ne _) (fun i => hy_ne _)
      · -- Family 4: `x0 = (b k)⁻¹` => permute `y` so `y (Fin.last n) = b k`, then `masterEq_at_ylast_inv`
        let x' : Fin (n + 1) → E6 := Fin.cons (((b k)⁻¹ : ℚ) : E6) xt
        have hx'_ne : ∀ i, x' i ≠ 0 :=
          fun i => Fin.cases (by dsimp only [x']; rw [Fin.cons_zero, Rat.cast_inv]; exact inv_ne_zero (hy_ne k)) hxt_ne i
        have hcomm : ∀ k1 k2, Bmat (n + 1) x' (y k1) α β * Bmat (n + 1) x' (y k2) α β =
            Bmat (n + 1) x' (y k2) α β * Bmat (n + 1) x' (y k1) α β := fun k1 k2 =>
          Bmat_comm (n + 1) x' hx'_ne (y k1) (y k2) α β (hy_ne k1) (hy_ne k2)
            (sig_q_rat_div_ne_zero (b k1) (b k2) (by linarith [hb1 k1]) (by linarith [hb1 k2]))
            (sig_rat_gt_one_ne_zero (b k1) (b k2) (hb1 k1) (hb1 k2))
        rw [← masterEq_perm_y (n + 1) x' y α β (Equiv.swap (Fin.last n) k) hcomm]
        apply masterEq_at_ylast_inv n x'
          (y ∘ Equiv.swap (Fin.last n) k) α β hx'_ne (fun i => hy_ne _)
        · simp only [x', y, Fin.cons_zero, Function.comp_apply, Equiv.swap_apply_left]
          exact Rat.cast_inv (b k)
        · exact hIH _ _ (fun i => hx'_ne _) (fun i => hy_ne _)
      · -- Family 5: `x0 = q^2 * b k` => `x0^2 = -q * (b k)^2` => row 0 = row `n + 1 + k`
        apply masterEq_of_Zvec_eq (i := ⟨0, by omega⟩) (j := ⟨n + 1 + k.val, by omega⟩)
          (fun h => by have := congrArg Fin.val h; dsimp at this; omega)
        simp only [Zvec, Nat.zero_lt_succ, show ¬ (n + 1 + k.val < n + 1) by omega,
          dite_true, dite_false, Nat.add_sub_cancel_left, rootZ]
        have h1 : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
        rw [h1, Fin.cons_zero]
        have hq4 : (q ^ 2) ^ 2 = -q := by
          calc (q ^ 2) ^ 2 = q ^ 3 * q := by ring
            _ = -q := by rw [q_cube]; ring
        have hsq : (q ^ 2 * (b k : E6)) ^ 2 = -q * (y k) ^ 2 := by
          rw [mul_pow, hq4]
        rw [hsq, mul_inv, inv_neg]; ring
      · -- Family 6: `x0 = q * (b k)⁻¹` => `x0^2 = -q⁻¹ * ((b k)^2)⁻¹` => row 0 = row `n + 1 + k`
        apply masterEq_of_Zvec_eq (i := ⟨0, by omega⟩) (j := ⟨n + 1 + k.val, by omega⟩)
          (fun h => by have := congrArg Fin.val h; dsimp at this; omega)
        simp only [Zvec, Nat.zero_lt_succ, show ¬ (n + 1 + k.val < n + 1) by omega,
          dite_true, dite_false, Nat.add_sub_cancel_left, rootZ]
        have h1 : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := rfl
        rw [h1, Fin.cons_zero]
        have hq2' : q ^ 2 = -q⁻¹ := by rw [q_sq, q_inv]; ring
        have hsq : (q * (((b k)⁻¹ : ℚ) : E6)) ^ 2 = -q⁻¹ * ((y k) ^ 2)⁻¹ := by
          rw [Rat.cast_inv, mul_pow, hq2', inv_pow]
        rw [hsq, mul_inv, inv_neg, inv_inv, inv_inv]; ring
    dsimp only [rootW]
    rw [← hP (rootZ u) hrootZ_ne, ← hQ (rootZ u) hrootZ_ne]
    dsimp only
    rw [hMaster_u]
  -- Conclude for ALL `x0 ≠ 0`!
  intro x0 hx0
  unfold MasterEq
  apply mul_left_cancel₀ (pow_ne_zero (6 * n + 3) hx0)
  rw [hP x0 hx0, hQ x0 hx0, hPQ]

lemma laurent_multivar_lift {N : ℕ} {F G : (Fin N → E6) → E6}
    (hF : ∀ (v : Fin N → E6) (idx : Fin N), IsLaurent (fun z => F (Function.update v idx z)))
    (hG : ∀ (v : Fin N → E6) (idx : Fin N), IsLaurent (fun z => G (Function.update v idx z)))
    (hRat : ∀ r : Fin N → ℚ, (∀ i, 1 < r i) → Function.Injective r →
      F (fun i => (r i : E6)) = G (fun i => (r i : E6))) :
    ∀ v : Fin N → E6, (∀ i, v i ≠ 0) → F v = G v := by
  have hstep : ∀ (k : ℕ), k ≤ N → ∀ (v : Fin N → E6) (r : Fin N → ℚ),
      (∀ i : Fin N, i.val < k → v i ≠ 0) →
      (∀ i : Fin N, k ≤ i.val → 1 < r i) →
      (∀ i j : Fin N, k ≤ i.val → k ≤ j.val → r i = r j → i = j) →
      F (fun i => if i.val < k then v i else (r i : E6)) =
      G (fun i => if i.val < k then v i else (r i : E6)) := by
    intro k
    induction k with
    | zero =>
      intro _ v r _ hr1 hrinj
      have hmix : (fun i : Fin N => if i.val < 0 then v i else (r i : E6)) =
          fun i => (r i : E6) := by funext i; simp
      rw [hmix]
      exact hRat r (fun i => hr1 i (Nat.zero_le _))
        (fun i j hij => hrinj i j (Nat.zero_le _) (Nat.zero_le _) hij)
    | succ k ih =>
      intro hk v r hv hr1 hrinj
      let i0 : Fin N := ⟨k, by omega⟩
      let base : Fin N → E6 := fun i => if i.val < k then v i else (r i : E6)
      have hupd_eq : (fun i : Fin N => if i.val < k + 1 then v i else (r i : E6)) =
          Function.update base i0 (v i0) := by
        funext i
        by_cases hi : i = i0
        · subst hi; simp [i0]
        · have hne : i.val ≠ k := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hi]
          have hiff : i.val < k + 1 ↔ i.val < k := by omega
          simp only [base, hiff]
      rw [hupd_eq]
      let B : ℚ := 1 + ∑ i : Fin N, |r i|
      have hB : 0 ≤ B := by
        have hsum : 0 ≤ ∑ i : Fin N, |r i| := Finset.sum_nonneg fun i _ => abs_nonneg (r i)
        linarith
      apply laurent_eq_of_gt_bound (hF base i0) (hG base i0) B hB
      · intro t ht
        let r' : Fin N → ℚ := Function.update r i0 t
        have hmix' : Function.update base i0 (t : E6) =
            fun i => if i.val < k then v i else (r' i : E6) := by
          funext i
          by_cases hi : i = i0
          · subst hi; simp [r', i0]
          · rw [Function.update_of_ne hi]
            simp only [base, r', Function.update_of_ne hi]
        rw [hmix']
        apply ih (by omega) v r' (fun i hi => hv i (by omega))
        · intro i hi
          by_cases heq : i = i0
          · subst heq; simp only [r', Function.update_self]
            have hsum : 0 ≤ ∑ j : Fin N, |r j| := Finset.sum_nonneg fun j _ => abs_nonneg (r j)
            linarith
          · simp only [r', Function.update_of_ne heq]
            have : k + 1 ≤ i.val := by
              have : i.val ≠ k := fun h => heq (Fin.ext h); omega
            exact hr1 i this
        · intro i j hi hj hreq
          by_cases hi0 : i = i0 <;> by_cases hj0 : j = i0
          · rw [hi0, hj0]
          · exfalso
            simp only [r', hi0, Function.update_self, Function.update_of_ne hj0] at hreq
            have hle : r j ≤ ∑ l : Fin N, |r l| :=
              le_trans (le_abs_self (r j))
                (Finset.single_le_sum (fun l _ => abs_nonneg (r l)) (Finset.mem_univ j))
            linarith
          · exfalso
            simp only [r', hj0, Function.update_self, Function.update_of_ne hi0] at hreq
            have hle : r i ≤ ∑ l : Fin N, |r l| :=
              le_trans (le_abs_self (r i))
                (Finset.single_le_sum (fun l _ => abs_nonneg (r l)) (Finset.mem_univ i))
            linarith
          · simp only [r', Function.update_of_ne hi0, Function.update_of_ne hj0] at hreq
            have hi' : k + 1 ≤ i.val := by have : i.val ≠ k := fun h => hi0 (Fin.ext h); omega
            have hj' : k + 1 ≤ j.val := by have : j.val ≠ k := fun h => hj0 (Fin.ext h); omega
            exact hrinj i j hi' hj' hreq
      · exact hv i0 (by dsimp [i0]; omega)
  intro v hv
  have h := hstep N (le_refl N) v (fun _ => 2) (fun i _ => hv i)
    (fun i hi => absurd hi (not_le.mpr i.isLt))
    (fun i _ hi => absurd hi (not_le.mpr i.isLt))
  have hmix : (fun i : Fin N => if i.val < N then v i else ((2 : ℚ) : E6)) = v := by
    funext i; simp [i.isLt]
  rwa [hmix] at h

theorem master_theorem : ∀ (n : ℕ) (x y : Fin n → E6) (α β : E6),
    (∀ j, x j ≠ 0) → (∀ k, y k ≠ 0) → MasterEq n x y α β
  | 0, x, y, α, β, _, _ => by
    unfold MasterEq Z_n pref
    have : IsEmpty (Fin (2 * 0)) := ⟨fun i => Nat.not_lt_zero i.val i.isLt⟩
    have hV : (Vmat (2 * 0) (Zvec 0 x y)).det = 1 := Matrix.det_isEmpty
    have hD : (Dmat 0 (Zvec 0 x y)).det = 1 := Matrix.det_isEmpty
    have hZ : prodB 0 x α β (List.ofFn y) (allT 0) (allF 0) = 1 := by
      have hnil : List.ofFn y = [] := List.ofFn_zero
      have htf : allT 0 = allF 0 := funext fun i => i.elim0
      rw [hnil, htf]; simp [prodB]
    rw [hV, hD, hZ]; simp
  | n + 1, x, y, α, β, hx, hy => by
    have hIH := master_theorem n
    have hx_cons : x = Fin.cons (x 0) (fun j => x j.succ) := (Fin.cons_self_tail x).symm
    rw [hx_cons]
    let packX : (Fin (n + (n + 1)) → E6) → Fin (n + 1) → E6 :=
      fun v => Fin.cons (x 0) (fun j => v ⟨j.val, by omega⟩)
    let packY : (Fin (n + (n + 1)) → E6) → Fin (n + 1) → E6 :=
      fun v => fun k => v ⟨n + k.val, by omega⟩
    let v0 : Fin (n + (n + 1)) → E6 :=
      fun i => if h : i.val < n then x (⟨i.val, h⟩ : Fin n).succ else y ⟨i.val - n, by omega⟩
    have hv0_ne : ∀ i, v0 i ≠ 0 := by
      intro i; dsimp only [v0]; split_ifs
      · exact hx _
      · exact hy _
    have hpx : packX v0 = Fin.cons (x 0) (fun j => x j.succ) := by
      funext j; refine Fin.cases rfl (fun i => ?_) j
      simp [packX, v0, i.isLt]; rfl
    have hpy : packY v0 = y := by
      funext k
      simp only [packY, v0, show ¬ (n + k.val < n) by omega, dite_false, Nat.add_sub_cancel_left]
    rw [← hpx, ← hpy]
    have hcoord_laur : ∀ (v : Fin (n + (n + 1)) → E6) (idx : Fin (n + (n + 1))) (m : Fin (n + (n + 1))),
        IsLaurent (fun z => Function.update v idx z m) ∧
        IsLaurent (fun z => (Function.update v idx z m)⁻¹) := by
      intro v idx m
      by_cases hm : m = idx
      · subst hm; simp only [Function.update_self]; exact ⟨isLaurent_id, isLaurent_inv⟩
      · simp only [Function.update_of_ne hm]; exact ⟨isLaurent_const _, isLaurent_const _⟩
    have hpackX_laur : ∀ (v : Fin (n + (n + 1)) → E6) (idx : Fin (n + (n + 1))) (j : Fin (n + 1)),
        IsLaurent (fun z => packX (Function.update v idx z) j) ∧
        IsLaurent (fun z => (packX (Function.update v idx z) j)⁻¹) := by
      intro v idx j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [packX, Fin.cons_zero]; exact ⟨isLaurent_const _, isLaurent_const _⟩
      · simp only [packX, Fin.cons_succ]; exact hcoord_laur v idx ⟨i.val, by omega⟩
    have hpackY_laur : ∀ (v : Fin (n + (n + 1)) → E6) (idx : Fin (n + (n + 1))) (k : Fin (n + 1)),
        IsLaurent (fun z => packY (Function.update v idx z) k) ∧
        IsLaurent (fun z => (packY (Function.update v idx z) k)⁻¹) :=
      fun v idx k => hcoord_laur v idx ⟨n + k.val, by omega⟩
    exact laurent_multivar_lift
      (F := fun v => (Vmat (2 * (n + 1)) (Zvec (n + 1) (packX v) (packY v))).det *
                     Z_n (n + 1) (packX v) (packY v) α β)
      (G := fun v => pref (n + 1) (packX v) (packY v) α β *
                     (Dmat (n + 1) (Zvec (n + 1) (packX v) (packY v))).det)
      (fun v idx => isLaurent_mul
        (isLaurent_Vmat_Zvec (n + 1) (fun z => packX (Function.update v idx z))
          (fun z => packY (Function.update v idx z)) (hpackX_laur v idx) (hpackY_laur v idx))
        (isLaurent_Z_n (n + 1) (fun z => packX (Function.update v idx z))
          (fun z => packY (Function.update v idx z)) α β (hpackX_laur v idx) (hpackY_laur v idx)))
      (fun v idx => isLaurent_mul
        (isLaurent_pref (n + 1) (fun z => packX (Function.update v idx z))
          (fun z => packY (Function.update v idx z)) α β (hpackX_laur v idx) (hpackY_laur v idx))
        (isLaurent_Dmat_Zvec (n + 1) (fun z => packX (Function.update v idx z))
          (fun z => packY (Function.update v idx z)) (hpackX_laur v idx) (hpackY_laur v idx)))
      (fun r hr1 hrinj =>
        masterEq_step_generic n
          (fun j => r ⟨j.val, by omega⟩) (fun k => r ⟨n + k.val, by omega⟩) α β
          (fun j => hr1 _) (fun k => hr1 _)
          (fun j1 j2 h => Fin.ext (by have := congrArg Fin.val (hrinj h); dsimp at this; omega))
          (fun k1 k2 h => Fin.ext (by have := congrArg Fin.val (hrinj h); dsimp at this; omega))
          (fun j k h => by have := congrArg Fin.val (hrinj h); dsimp at this; omega)
          (fun x' y' hx' hy' => hIH x' y' α β hx' hy')
          (x 0) (hx 0))
      v0 hv0_ne

/- ### 5.7. Principal Specialization (`master_theorem` + `mod2` + `modA` => `H1`) -/


theorem master_to_H1 (n : ℕ) :
    3 ^ (n * (n - 1)) * (HalfMat n).ncard * altNat n (fun j => j + 1) =
      altNat n (fun j => j + 1 + j / 2) := by
  let a1 : ℕ → ℕ := fun j => j + 1
  let a2 : ℕ → ℕ := fun j => j + 1 + j / 2
  let E1 := Ealt n a1
  let E2 := Ealt n a2
  let xr : E6 → Fin n → E6 := fun r j => r ^ (j.val + 1)
  let yr : E6 → Fin n → E6 := fun r k => q * r ^ (n + k.val + 1)
  have hZ_spec : ∀ r : E6, r ≠ 0 →
      Zvec n (xr r) (yr r) = fun i : Fin (2 * n) => (r ^ 2) ^ (i.val + 1) + ((r ^ 2) ^ (i.val + 1))⁻¹ := by
    intro r hr
    funext i
    simp only [Zvec, xr, yr]
    by_cases hi : i.val < n
    · simp only [hi, dite_true]
      have hpow : (r ^ (i.val + 1)) ^ 2 = (r ^ 2) ^ (i.val + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
      rw [hpow]
    · simp only [hi, dite_false]
      have hidx : n + (i.val - n) + 1 = i.val + 1 := by omega
      rw [hidx]
      have hpow : (r ^ (i.val + 1)) ^ 2 = (r ^ 2) ^ (i.val + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
      have hq_left : -q * (q * r ^ (i.val + 1)) ^ 2 = (r ^ 2) ^ (i.val + 1) := by
        rw [mul_pow, hpow]
        calc -q * (q ^ 2 * (r ^ 2) ^ (i.val + 1)) = -(q ^ 3) * (r ^ 2) ^ (i.val + 1) := by ring
          _ = (r ^ 2) ^ (i.val + 1) := by rw [q_cube]; ring
      have hq_right : -(q⁻¹ * ((q * r ^ (i.val + 1)) ^ 2)⁻¹) = ((r ^ 2) ^ (i.val + 1))⁻¹ := by
        rw [mul_pow, hpow, mul_inv]
        have hqi3 : q⁻¹ * (q ^ 2)⁻¹ = -1 := by
          rw [← mul_inv, show q * q ^ 2 = q ^ 3 by ring, q_cube, inv_neg, inv_one]
        calc -(q⁻¹ * ((q ^ 2)⁻¹ * ((r ^ 2) ^ (i.val + 1))⁻¹))
            = -(q⁻¹ * (q ^ 2)⁻¹) * ((r ^ 2) ^ (i.val + 1))⁻¹ := by ring
          _ = ((r ^ 2) ^ (i.val + 1))⁻¹ := by rw [hqi3]; ring
      rw [sub_eq_add_neg, hq_left, hq_right]
  have hpoly_sq_laur : ∀ P : Polynomial E6, IsLaurent (fun r : E6 => P.eval (r ^ 2)) := fun P =>
    ⟨0, P.comp (X ^ 2), fun r _ => by simp⟩
  have hxr_laur : ∀ j : Fin n, IsLaurent (fun r => xr r j) ∧ IsLaurent (fun r => (xr r j)⁻¹) := by
    intro j; refine ⟨isLaurent_pow isLaurent_id (j.val + 1), ?_⟩
    have : (fun r : E6 => (xr r j)⁻¹) = fun r => (r⁻¹) ^ (j.val + 1) := by
      funext r; simp [xr, inv_pow]
    rw [this]; exact isLaurent_pow isLaurent_inv (j.val + 1)
  have hyr_laur : ∀ k : Fin n, IsLaurent (fun r => yr r k) ∧ IsLaurent (fun r => (yr r k)⁻¹) := by
    intro k
    refine ⟨isLaurent_mul (isLaurent_const q) (isLaurent_pow isLaurent_id (n + k.val + 1)), ?_⟩
    have : (fun r : E6 => (yr r k)⁻¹) = fun r => q⁻¹ * (r⁻¹) ^ (n + k.val + 1) := by
      funext r; simp [yr, inv_pow]; ring
    rw [this]; exact isLaurent_mul (isLaurent_const q⁻¹) (isLaurent_pow isLaurent_inv (n + k.val + 1))
  have hF_laur : IsLaurent (fun r => (r ^ 2) ^ E2 * (Qalt n a1).eval (r ^ 2) *
      Z_n n (xr r) (yr r) (-q) q⁻¹) :=
    isLaurent_mul (isLaurent_mul (isLaurent_pow (isLaurent_pow isLaurent_id 2) E2) (hpoly_sq_laur _))
      (isLaurent_Z_n n xr yr (-q) q⁻¹ hxr_laur hyr_laur)
  have hG_laur : IsLaurent (fun r => (r ^ 2) ^ E1 * pref n (xr r) (yr r) (-q) q⁻¹ *
      (Qalt n a2).eval (r ^ 2)) :=
    isLaurent_mul (isLaurent_mul (isLaurent_pow (isLaurent_pow isLaurent_id 2) E1)
      (isLaurent_pref n xr yr (-q) q⁻¹ hxr_laur hyr_laur)) (hpoly_sq_laur _)
  have hrat_eq : ∀ r : ℚ, 1 < r →
      ((r : E6) ^ 2) ^ E2 * (Qalt n a1).eval ((r : E6) ^ 2) * Z_n n (xr (r : E6)) (yr (r : E6)) (-q) q⁻¹ =
      ((r : E6) ^ 2) ^ E1 * pref n (xr (r : E6)) (yr (r : E6)) (-q) q⁻¹ * (Qalt n a2).eval ((r : E6) ^ 2) := by
    intro r hr
    set z : E6 := (r : E6)
    have hz : z ≠ 0 := rat_gt_one_ne_zero r hr
    set s : E6 := z ^ 2
    have hs : s ≠ 0 := pow_ne_zero 2 hz
    have hs_sub : s - 1 ≠ 0 := by
      intro h0
      have hsq : z ^ 2 = ((r ^ 2 : ℚ) : E6) := by push_cast; rfl
      have hre := congrArg E6.re h0
      simp only [s, hsq, E6.sub_re, E6.ratCast_re, E6.one_re, E6.zero_re] at hre
      nlinarith
    have hM := master_theorem n (xr z) (yr z) (-q) q⁻¹
      (fun j => pow_ne_zero _ hz) (fun k => mul_ne_zero q_ne_zero (pow_ne_zero _ hz))
    unfold MasterEq at hM
    rw [hZ_spec z hz] at hM
    have hVspec := det_Vmat_symp_spec (K := E6) n s hs
    have hDspec := det_Dmat_symp_spec (K := E6) n s hs
    dsimp only at hVspec hDspec
    apply mul_left_cancel₀ (pow_ne_zero (4 * n ^ 2) hs_sub)
    set Pw := ∏ i : Fin (2 * n), (s ^ (i.val + 1) - (s ^ (i.val + 1))⁻¹)
    calc (s - 1) ^ (4 * n ^ 2) * (s ^ E2 * (Qalt n a1).eval s * Z_n n (xr z) (yr z) (-q) q⁻¹)
        = s ^ E2 * ((s - 1) ^ (4 * n ^ 2) * (Qalt n a1).eval s) * Z_n n (xr z) (yr z) (-q) q⁻¹ := by ring
      _ = s ^ E2 * (s ^ E1 * Pw * (Vmat (2 * n) (fun i => s ^ (i.val + 1) + (s ^ (i.val + 1))⁻¹)).det) *
          Z_n n (xr z) (yr z) (-q) q⁻¹ := by rw [← hVspec]
      _ = s ^ E1 * s ^ E2 * Pw *
          ((Vmat (2 * n) (fun i => s ^ (i.val + 1) + (s ^ (i.val + 1))⁻¹)).det *
            Z_n n (xr z) (yr z) (-q) q⁻¹) := by ring
      _ = s ^ E1 * s ^ E2 * Pw *
          (pref n (xr z) (yr z) (-q) q⁻¹ *
            (Dmat n (fun i => s ^ (i.val + 1) + (s ^ (i.val + 1))⁻¹)).det) := by rw [hM]
      _ = s ^ E1 * pref n (xr z) (yr z) (-q) q⁻¹ *
          (s ^ E2 * Pw * (Dmat n (fun i => s ^ (i.val + 1) + (s ^ (i.val + 1))⁻¹)).det) := by ring
      _ = s ^ E1 * pref n (xr z) (yr z) (-q) q⁻¹ *
          ((s - 1) ^ (4 * n ^ 2) * (Qalt n a2).eval s) := by rw [hDspec]
      _ = (s - 1) ^ (4 * n ^ 2) * (s ^ E1 * pref n (xr z) (yr z) (-q) q⁻¹ * (Qalt n a2).eval s) := by ring
  -- Evaluate at `r = 1` via `laurent_eq_of_gt_bound`!
  have h1 := laurent_eq_of_gt_bound hF_laur hG_laur 1 (by norm_num) hrat_eq 1 one_ne_zero
  have hxr1 : xr 1 = fun _ => 1 := by funext j; simp [xr]
  have hyr1 : yr 1 = fun _ => q := by funext k; simp [yr]
  rw [hxr1, hyr1, one_pow, one_pow, one_pow, one_mul, one_mul,
      Qalt_eval_one (K := E6) n a1, Qalt_eval_one (K := E6) n a2, Z_n_at_special n] at h1
  have hpref1 : pref n (fun _ => 1) (fun _ => q) (-q) q⁻¹ = (-1 : E6) ^ n * c ^ (3 * n) := by
    unfold pref
    have hq_term : (-q) * (1 : E6) + q⁻¹ * (1 : E6)⁻¹ = -c := by
      rw [mul_one, inv_one, mul_one, q_inv, c_eq]; ring
    simp only [sig_q_sq, hq_term, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hneg : (-c) ^ n = (-1 : E6) ^ n * c ^ n := by rw [← mul_pow]; simp
    rw [hneg]; ring
  rw [hpref1] at h1
  -- Cancel `(-1)^n * c^(3*n) * 2^(2*n)`
  have h2_ne : (2 : E6) ≠ 0 := by
    intro h0
    have hre := congrArg E6.re h0
    have h2eq : (2 : E6) = ((2 : ℚ) : E6) := by norm_cast
    rw [h2eq, E6.ratCast_re, E6.zero_re] at hre; norm_num at hre
  have hfac_ne : (-1 : E6) ^ n * c ^ (3 * n) * (2 : E6) ^ (2 * n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero n (by norm_num)) (pow_ne_zero (3 * n) c_ne_zero))
      (pow_ne_zero (2 * n) h2_ne)
  have hc_pow : c ^ (2 * n ^ 2 + n) = c ^ (3 * n) * (3 : E6) ^ (n * (n - 1)) := by
    cases n with
    | zero => simp
    | succ m =>
      have hexp : 2 * (m + 1) ^ 2 + (m + 1) = 3 * (m + 1) + 2 * ((m + 1) * m) := by ring
      rw [show m + 1 - 1 = m by omega, hexp, pow_add, pow_mul c 2 ((m + 1) * m), c_sq]
      congr 1
      have hev : Even ((m + 1) * m) := by
        rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
        · exact ⟨(2 * k + 1) * k, by ring⟩
        · exact ⟨(k + 1) * (2 * k + 1), by ring⟩
      obtain ⟨t, ht⟩ := hev
      rw [ht, ← two_mul, pow_mul, pow_mul]
      congr 1; ring
  have hEqE6 : ((3 : E6) ^ (n * (n - 1)) * ((HalfMat n).ncard : E6) * (altNat n a1 : E6)) =
      (altNat n a2 : E6) := by
    apply mul_left_cancel₀ hfac_ne
    rw [hc_pow] at h1
    calc (-1 : E6) ^ n * c ^ (3 * n) * (2 : E6) ^ (2 * n) *
          ((3 : E6) ^ (n * (n - 1)) * ((HalfMat n).ncard : E6) * (altNat n a1 : E6))
        = (2 : E6) ^ (2 * n) * (altNat n a1 : E6) *
          ((-1 : E6) ^ n * (c ^ (3 * n) * (3 : E6) ^ (n * (n - 1))) * ((HalfMat n).ncard : E6)) := by ring
      _ = (-1 : E6) ^ n * c ^ (3 * n) * ((2 : E6) ^ (2 * n) * (altNat n a2 : E6)) := h1
      _ = (-1 : E6) ^ n * c ^ (3 * n) * (2 : E6) ^ (2 * n) * (altNat n a2 : E6) := by ring
  have hEqNat : ((3 ^ (n * (n - 1)) * (HalfMat n).ncard * altNat n a1 : ℕ) : E6) =
      ((altNat n a2 : ℕ) : E6) := by
    push_cast; exact hEqE6
  exact Nat.cast_injective hEqNat


end Mod5


theorem h1_symp_proof : OMA.R_OeisA109074_conjecture_R1_H2_R1.H1 := by
  intro n
  change 3 ^ (n * (n - 1)) * (Mat n).ncard * altNat n (fun j => j + 1) =
    altNat n (fun j => j + 1 + j / 2)
  rw [mat_ncard_eq_halfMat_ncard]
  exact master_to_H1 n

end OMAC

end

theorem OMA.solution : type_of% @OeisA109074.conjecture :=
  OMA.R_OeisA109074_conjecture_R1.main
    (fun n => OMAA109074H1.main_eq n)
    (OMA.R_OeisA109074_conjecture_R1_H2_R1.main
      OMAC.h1_symp_proof
      (fun n => OMA109074.main n))
