import OMAReductions.R_Erdos1070_erdos_1070_parts_ii_R1
import Mathlib

/-!
The integer dual certificate and exact 29-vertex construction of Ágoston Dúcz
and Dániel Varga (arXiv:2606.28157). The source and image masks, coefficients,
and chosen motions encode the paper's public supplementary data.

The kernel checks the exact distances and congruences in a nested quadratic
extension, the signed arithmetic on independent masks, and the coverage of
the branches of a vertex split.
-/

/- Arithmetic of radix-encoded nonnegative mask coefficients. -/

namespace UnitDistancePacked

abbrev Weights := List (ℕ × ℕ)

def encode (base : ℕ) (t : Weights) : ℕ :=
  (t.map (fun r => r.2 * base^r.1)).sum

def mass (t : Weights) : ℕ := (t.map Prod.snd).sum

def low (split : ℕ) (t : Weights) : Weights :=
  t.filter (fun r => r.1 < split)

def high (split : ℕ) (t : Weights) : Weights :=
  t.filterMap (fun r => if split ≤ r.1 then some (r.1 - split, r.2) else none)

theorem encode_append (base : ℕ) (t u : Weights) :
    encode base (t ++ u) = encode base t + encode base u := by
  simp [encode]

theorem mass_partition (h : ℕ) (t : Weights) :
    mass (low h t) + mass (high h t) = mass t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    by_cases hr : r.1 < h
    · have hneg : ¬h ≤ r.1 := by omega
      simp [low, high, hr, hneg, mass] at ih ⊢
      omega
    · have hpos : h ≤ r.1 := by omega
      simp [low, high, hr, hpos, mass] at ih ⊢
      omega

theorem encode_partition (base h : ℕ) (t : Weights) :
    encode base t = encode base (low h t) + base^h * encode base (high h t) := by
  induction t with
  | nil => simp [encode, low, high]
  | cons r t ih =>
    by_cases hr : r.1 < h
    · have hneg : ¬h ≤ r.1 := by omega
      simp [low, high, hr, hneg, encode] at ih ⊢
      omega
    · have hpos : h ≤ r.1 := by omega
      have hf : base^r.1 = base^h * base^(r.1 - h) := by
        rw [← pow_add, Nat.add_sub_of_le hpos]
      simp [low, high, hr, hpos, encode, hf, Nat.mul_add] at ih ⊢
      rw [ih]
      ring

private theorem encode_le_mul (base k : ℕ) (hb : 0 < base) (t : Weights)
    (ht : ∀ r ∈ t, r.1 ≤ k) : encode base t ≤ mass t * base^k := by
  induction t with
  | nil => simp [encode, mass]
  | cons r t ih =>
    simp only [encode, mass, List.map_cons, List.sum_cons, Nat.add_mul]
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (ht r List.mem_cons_self))
    · exact ih (fun x hx => ht x (List.mem_cons_of_mem _ hx))

private theorem encode_low_lt {base : ℕ} (hb : 0 < base) (h : ℕ) (t : Weights)
    (ht : mass t < base) : encode base (low h t) < base^h := by
  cases h with
  | zero => simp [low, encode]
  | succ k =>
    have hm : mass (low (k+1) t) < base := by
      have hp := mass_partition (k+1) t
      omega
    have hw := encode_le_mul base k hb (low (k+1) t) fun r hr => by
      have hh := (List.mem_filter.1 hr).2
      have hlt : r.1 < k+1 := of_decide_eq_true hh
      omega
    apply hw.trans_lt
    rw [pow_succ, Nat.mul_comm (base^k) base]
    exact Nat.mul_lt_mul_of_pos_right hm (Nat.pow_pos hb)

theorem encode_low_eq_mod {base : ℕ} (hb : 0 < base) (h : ℕ) (t : Weights)
    (ht : mass t < base) : encode base t % base^h = encode base (low h t) := by
  rw [encode_partition base h t, Nat.add_comm, Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt (encode_low_lt hb h t ht)

theorem encode_high_eq_div {base : ℕ} (hb : 0 < base) (h : ℕ) (t : Weights)
    (ht : mass t < base) : encode base t / base^h = encode base (high h t) := by
  rw [encode_partition base h t, Nat.add_mul_div_left _ _ (Nat.pow_pos hb),
    Nat.div_eq_of_lt (encode_low_lt hb h t ht), Nat.zero_add]

theorem encode_mod_mass {base : ℕ} (hb : 1 < base - 1) (t : Weights)
    (ht : mass t < base - 1) : encode base t % (base-1) = mass t := by
  have hbase : base ≡ 1 [MOD base-1] := by
    change base % (base - 1) = 1 % (base - 1)
    calc
      _ = ((base-1) + 1) % (base-1) := by congr 1; omega
      _ = _ := Nat.add_mod_left _ _
  have hmod (u : Weights) : encode base u ≡ mass u [MOD base-1] := by
    induction u with
    | nil => rfl
    | cons r u ih =>
      simp only [encode, mass, List.map_cons, List.sum_cons]
      simpa only [encode, mass, one_pow, Nat.mul_one] using ((Nat.ModEq.refl r.2).mul (hbase.pow r.1)).add ih
  exact (show encode base t % (base-1) = mass t % (base-1) from hmod t).trans
    (Nat.mod_eq_of_lt ht)

private theorem encode_low_one (base : ℕ) (t : Weights) :
    encode base (low 1 t) = mass (low 1 t) := by
  unfold encode mass
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  have hlt : r.1 < 1 := of_decide_eq_true (List.mem_filter.1 hr).2
  simp [Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)]

theorem encode_mod_zero {base : ℕ} (hb : 0 < base) (t : Weights)
    (ht : mass t < base) : encode base t % base = mass (low 1 t) := by
  have h := encode_low_eq_mod hb 1 t ht
  simpa only [pow_one, encode_low_one] using h

end UnitDistancePacked



namespace UnitDistancePacked

def lane (base word i : ℕ) : ℕ := (word / base^i) % base

def massAt (i : ℕ) (t : Weights) : ℕ := mass (t.filter (fun r => r.1 = i))

private theorem mass_at_eq (t : Weights) (i : ℕ) :
    mass (low 1 (high i t)) = massAt i t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    by_cases h : i ≤ r.1
    · have he : r.1 - i < 1 ↔ r.1 = i := by omega
      by_cases hr : r.1 = i
      · simpa [high, low, massAt, mass, h, hr] using congrArg (r.2 + ·) ih
      · have hz : r.1 - i ≠ 0 := by omega
        simpa [high, low, massAt, mass, h, he, hr, hz] using ih
    · have hh : r.1 ≠ i := by omega
      simpa [high, low, massAt, mass, h, hh] using ih

theorem lane_encode {base : ℕ} (hb : 0 < base) (t : Weights) (ht : mass t < base) (i : ℕ) :
    lane base (encode base t) i = massAt i t := by
  unfold lane
  rw [encode_high_eq_div hb i t ht, encode_mod_zero hb (high i t), mass_at_eq]
  have hm := mass_partition i t
  omega

theorem testBit_lane {width : ℕ} (hw : 0 < width) (word i : ℕ) :
    word.testBit i = (lane (2^width) word (i/width)).testBit (i%width) := by
  unfold lane
  rw [← pow_mul, ← Nat.shiftRight_eq_div_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  have hm : decide (i % width < width) = true := decide_eq_true (Nat.mod_lt i hw)
  rw [hm]
  simp only [Bool.true_and]
  rw [Nat.div_add_mod]

theorem testBit_encode {width : ℕ} (hw : 0 < width) (t : Weights) (ht : mass t < 2^width) (i : ℕ) :
    (encode (2^width) t).testBit i = (massAt (i/width) t).testBit (i%width) := by
  rw [testBit_lane hw, lane_encode (Nat.two_pow_pos _) t ht]

private theorem mass_filter_le (t : Weights) (p : ℕ × ℕ → Bool) :
    mass (t.filter p) ≤ mass t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    cases e : p r <;>
      simp [mass, e] at ih ⊢ <;> omega

private theorem massAt_filter (t : Weights) (p : ℕ → Bool) (i : ℕ) :
    massAt i (t.filter (fun r => p r.1)) = if p i then massAt i t else 0 := by
  unfold massAt
  rw [List.filter_filter]
  by_cases hi : p i
  · have h : t.filter (fun x => decide (x.1 = i) && p x.1) = t.filter (fun x => decide (x.1 = i)) := by
      apply List.filter_congr
      intro r _
      by_cases hr : r.1 = i <;> simp [hr, hi]
    rw [h, if_pos hi]
  · have h : t.filter (fun x => decide (x.1 = i) && p x.1) = [] := by
      apply List.filter_eq_nil_iff.2
      intro r _
      by_cases hr : r.1 = i <;> simp [hr, hi]
    rw [h, if_neg hi]
    rfl

theorem encode_filter_by_mask {width : ℕ} (hw : 0 < width)
    (t : Weights) (ht : mass t < 2^width) (predicate : ℕ → Bool) (mask : ℕ)
    (hmask : ∀ i, mask.testBit i = predicate (i/width)) :
    encode (2^width) t &&& mask = encode (2^width) (t.filter fun r => predicate r.1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_land, hmask, testBit_encode hw t ht,
    testBit_encode hw _ ((mass_filter_le _ _).trans_lt ht), massAt_filter]
  by_cases h : predicate (i/width) <;> simp [h]

end UnitDistancePacked


namespace UnitDistancePacked

private def repeatWord (word period : ℕ) : ℕ → ℕ
  | 0 => word
  | h+1 =>
    let a := repeatWord word period h
    a ||| (a <<< (period * 2^h))

private def lowStripes (width n j : ℕ) : ℕ :=
  let block := width * 2^j
  repeatWord (2^block-1) (2*block) (n-(j+1))

private def zetaWord (width n : ℕ) (a : ℕ) : ℕ :=
  (List.range n).foldl (fun w j =>
    w + ((w &&& lowStripes width n j) <<< (width * 2^j))) a

private def auditGuards (width : ℕ) (rows : List ℕ) (allowed : ℕ) : ℕ × ℕ :=
  let n := rows.length
  let guards := repeatWord (2^(width-1)) width n
  let mask := (List.range n).foldl (fun acc i =>
    let stripe := lowStripes width n i
    if allowed.testBit i then
      let row := rows[i]?.getD 0
      (List.range i).foldl (fun curr j =>
        if row.testBit j then curr &&& (stripe ||| lowStripes width n j) else curr) acc
    else acc &&& stripe) guards
  (guards, mask)

end UnitDistancePacked

namespace UnitDistancePacked

private theorem repeatWord_bits {word period : ℕ} (hword : word < 2^period)
    (depth i : ℕ) :
    (repeatWord word period depth).testBit i =
      (decide (i < period * 2^depth) && word.testBit (i % period)) := by
  induction depth generalizing i with
  | zero =>
    simp only [repeatWord, pow_zero, Nat.mul_one]
    by_cases hi : i < period
    · simp [hi, Nat.mod_eq_of_lt hi]
    · have hbound : word < 2^i := hword.trans_le
        (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hi))
      simp [hi, Nat.testBit_lt_two_pow hbound]
  | succ depth ih =>
    simp only [repeatWord, Nat.testBit_or, Nat.testBit_shiftLeft, ih]
    let cut := period * 2^depth
    have hsize : period * 2^(depth+1) = 2 * cut := by
      dsimp [cut]
      rw [pow_succ]
      ring
    change (decide (i < cut) && word.testBit (i % period) ||
        (decide (cut ≤ i) &&
          (decide (i-cut < cut) && word.testBit ((i-cut) % period)))) =
      (decide (i < period * 2^(depth+1)) && word.testBit (i % period))
    rw [hsize]
    by_cases hi : i < cut
    · have hlt : i < 2*cut := by omega
      simp [hi, hlt, Nat.not_le_of_lt hi]
    · have hl := Nat.le_of_not_gt hi
      have htail : i - cut < cut ↔ i < 2 * cut := by omega
      have hmod : (i-cut)%period = i%period := by
        conv_rhs => rw [show i = i-cut + period * 2^depth from (Nat.sub_add_cancel hl).symm]
        exact (Nat.add_mul_mod_self_left _ _ _).symm
      simp [hi, hl, htail, hmod]

theorem lowStripes_bits {width n j : ℕ} (hw : 0 < width) (hj : j < n) (i : ℕ) :
    (lowStripes width n j).testBit i = (decide (i/width < 2^n) && !(i/width).testBit j) := by
  let block := width * 2^j
  have hb : 0 < block := Nat.mul_pos hw (Nat.two_pow_pos _)
  have hword : 2^block-1 < 2^(2*block) := by
    have hpow : 2^block ≤ 2^(2*block) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hlt := Nat.two_pow_pos block
    omega
  change (repeatWord (2^block-1) (2*block) (n-(j+1))).testBit i = _
  rw [repeatWord_bits hword, Nat.testBit_two_pow_sub_one]
  have hlen : (2 * block) * 2^(n - (j+1)) = width * 2^n := by
    calc
      _ = width * (2^(j+1) * 2^(n-(j+1))) := by
        rw [pow_succ]
        dsimp [block]
        ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le (Nat.succ_le_of_lt hj)]
  have hsize : i < width * 2^n ↔ i/width < 2^n := by
    rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm width (2^n)]
  have hb' : i % (2*block) < block ↔ i / block % 2 = 0 := by
    have he : (i % (2*block)) / block < 1 ↔ i % (2*block) < block := by
      simpa only [Nat.one_mul] using (Nat.div_lt_iff_lt_mul hb (x := i % (2*block)) (y := 1))
    rw [← he, Nat.mod_mul_left_div_self]
    exact Nat.lt_one_iff
  rw [hlen, Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul]
  change (decide (i < width * 2^n) && decide (i % (2*block) < block)) =
    (decide (i / width < 2^n) && !decide (i / block % 2 = 1))
  rcases Nat.mod_two_eq_zero_or_one (i / block) with h | h <;> simp [hsize, hb', h]

end UnitDistancePacked


namespace UnitDistancePacked

private def zetaTerms (j : ℕ) (t : Weights) : Weights :=
  t ++ (t.filter fun r => !r.1.testBit j).map (fun r => (r.1 + 2^j, r.2))

private theorem encode_shift (width h : ℕ) (t : Weights) :
    encode (2^width) (t.map fun r => (r.1 + h, r.2)) =
      encode (2^width) t <<< (width * h) := by
  rw [Nat.shiftLeft_eq, pow_mul]
  induction t with
  | nil => simp [encode]
  | cons r t ih =>
    simp only [encode, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, pow_add]
    ring

private theorem stripe_filter (width n j : ℕ) (hw : 0 < width) (hj : j < n)
    (t : Weights) (hbound : ∀ r ∈ t, r.1 < 2^n) (ht : mass t < 2^width) :
    encode (2^width) t &&& lowStripes width n j =
      encode (2^width) (t.filter fun r => !r.1.testBit j) := by
  rw [encode_filter_by_mask hw t ht (fun k => decide (k < 2^n) && !k.testBit j)
    (lowStripes width n j) (lowStripes_bits hw hj)]
  congr 1
  apply List.filter_congr
  intro r hr
  simp [hbound r hr]

private theorem encode_zeta_step (width n j : ℕ) (hw : 0 < width) (hj : j < n)
    (t : Weights) (hbound : ∀ r ∈ t, r.1 < 2^n) (ht : mass t < 2^width) :
    encode (2^width) (zetaTerms j t) =
      encode (2^width) t + ((encode (2^width) t &&& lowStripes width n j) <<< (width * 2^j)) := by
  rw [zetaTerms, encode_append, encode_shift, stripe_filter width n j hw hj t hbound ht]

private theorem zetaTerms_mass (j : ℕ) (t : Weights) :
    mass (zetaTerms j t) ≤ 2 * mass t := by
  have h := mass_filter_le t (fun r => !r.1.testBit j)
  simp only [zetaTerms, mass, List.map_append, List.sum_append,
    List.map_map, Function.comp_def] at h ⊢
  change (List.map Prod.snd (List.filter (fun r => !r.1.testBit j) t)).sum ≤ _ at h
  exact (Nat.add_le_add_left h _).trans (by omega)

end UnitDistancePacked


namespace UnitDistancePacked

private theorem setBit_of_clear {x j : ℕ} (hx : x.testBit j = false) :
    x + 2^j = x ||| 2^j := by
  let b := 2^(j+1)
  let r := x % b
  let q := x / b
  have hr : r < 2^j := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    change (x % 2^(j+1)).testBit i = false
    rw [Nat.testBit_mod_two_pow]
    rcases Nat.eq_or_lt_of_le hi with h | h
    · subst i
      simp [hx]
    · simp [show ¬ i < j+1 by omega]
  have hrb : r < b := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hr' : r + 2^j < b := by
    dsimp [b]
    rw [pow_succ]
    omega
  have hqr : x = b * q + r := (Nat.div_add_mod _ _).symm
  have hqr' : x + 2^j = b * q + (r + 2^j) := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hqr', Nat.testBit_or, hqr, Nat.testBit_two_pow_mul_add q hrb,
    Nat.testBit_two_pow_mul_add q hr', Nat.testBit_two_pow]
  by_cases hi : i < j+1
  · simp only [hi, if_true]
    rw [← Nat.or_two_pow_eq_add_of_lt hr, Nat.testBit_or, Nat.testBit_two_pow]
  · have hj : j ≠ i := by omega
    simp [hi, hj]

private theorem zetaTerms_bounded {n j : ℕ} (hj : j < n)
    (t : Weights) (ht : ∀ r ∈ t, r.1 < 2^n) :
    ∀ r ∈ zetaTerms j t, r.1 < 2^n := by
  intro r hr
  rw [zetaTerms, List.mem_append] at hr
  rcases hr with hr | hr
  · exact ht _ hr
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hr
    have hv' := List.mem_filter.1 hv
    have hbit : v.1.testBit j = false := by simpa using hv'.2
    change v.1 + 2^j < 2^n
    rw [setBit_of_clear hbit]
    exact Nat.or_lt_two_pow (ht v hv'.1)
      (Nat.pow_lt_pow_right (by decide : 1 < 2) hj)

end UnitDistancePacked


namespace UnitDistancePacked

private theorem zetaTerms_fold_mass (js : List ℕ) (t : Weights) :
    mass (js.foldl (fun w j => zetaTerms j w) t) ≤ mass t * 2^js.length := by
  induction js generalizing t with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons, List.length_cons, pow_succ]
    calc
      _ ≤ mass (zetaTerms j t) * 2^js.length := ih _
      _ ≤ (2 * mass t) * 2^js.length := Nat.mul_le_mul_right _ (zetaTerms_mass j t)
      _ = _ := by ring

private theorem zetaTerms_fold_bounded (js : List ℕ) (n : ℕ) (t : Weights)
    (hjs : ∀ j ∈ js, j < n) (ht : ∀ r ∈ t, r.1 < 2^n) :
    ∀ r ∈ js.foldl (fun w j => zetaTerms j w) t, r.1 < 2^n := by
  induction js generalizing t with
  | nil => exact ht
  | cons j js ih =>
    exact ih _ (fun k hk => hjs k (List.mem_cons_of_mem _ hk))
      (zetaTerms_bounded (hjs j List.mem_cons_self) t ht)

private theorem encode_zeta_fold (width n : ℕ) (hw : 0 < width)
    (js : List ℕ) (t : Weights) (hjs : ∀ j ∈ js, j < n)
    (hbound : ∀ r ∈ t, r.1 < 2^n) (hmass : mass t * 2^js.length < 2^width) :
    encode (2^width) (js.foldl (fun w j => zetaTerms j w) t) =
      js.foldl (fun w j =>
        w + ((w &&& lowStripes width n j) <<< (width * 2^j))) (encode (2^width) t) := by
  induction js generalizing t with
  | nil => rfl
  | cons j js ih =>
    have hj := hjs j List.mem_cons_self
    have hinit : mass t < 2^width := by
      refine lt_of_le_of_lt ?_ hmass
      exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    have hnext : mass (zetaTerms j t) * 2^js.length < 2^width := by
      apply lt_of_le_of_lt _ hmass
      simpa only [List.length_cons, pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using (Nat.mul_le_mul_right (2^js.length) (zetaTerms_mass j t))
    simp only [List.foldl_cons]
    rw [← encode_zeta_step width n j hw hj t hbound hinit]
    exact ih _ (fun k hk => hjs k (List.mem_cons_of_mem _ hk))
      (zetaTerms_bounded hj t hbound) hnext

private theorem zetaWord_eq (width n : ℕ) (hw : 0 < width) (t : Weights)
    (hbound : ∀ r ∈ t, r.1 < 2^n) (hmass : mass t * 2^n < 2^width) :
    zetaWord width n (encode (2^width) t) =
      encode (2^width) ((List.range n).foldl (fun w j => zetaTerms j w) t) := by
  apply Eq.symm
  apply encode_zeta_fold width n hw
  · exact fun j hj => List.mem_range.1 hj
  · exact hbound
  · simpa only [List.length_range] using hmass

end UnitDistancePacked


namespace UnitDistancePacked

private theorem bit_at_lane {width j : ℕ} (hw : 0 < width) (hj : j < width)
    (word i : ℕ) :
    (lane (2^width) word i).testBit j = word.testBit (j + width*i) := by
  rw [testBit_lane hw word, Nat.add_mul_div_left _ _ hw, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, Nat.zero_add]

private theorem high_guard_lane {width n : ℕ} (hw : 0 < width) (i : ℕ) :
    lane (2^width) (repeatWord (2^(width-1)) width n) i =
      if i < 2^n then 2^(width-1) else 0 := by
  have hx : 2^(width-1) < 2^width := Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < width
  · rw [bit_at_lane hw hj, repeatWord_bits hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    have hindex : j + width*i < width * 2^n ↔ i < 2^n := by
      rw [Nat.mul_comm width (2^n), ← Nat.div_lt_iff_lt_mul hw,
        Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hj, Nat.zero_add]
    by_cases hi : i < 2^n <;> simp [hi, hindex]
  · have hl := Nat.mod_lt ((repeatWord (2^(width-1)) width n) / (2^width)^i) (Nat.two_pow_pos width)
    have hp : 2^width ≤ 2^j := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hj)
    have hleft : lane (2^width) (repeatWord (2^(width-1)) width n) i < 2^j := hl.trans_le hp
    by_cases hi : i < 2^n <;> simp [hi, Nat.testBit_lt_two_pow hleft,
      Nat.testBit_lt_two_pow (hx.trans_le hp)]

private theorem high_bit_iff {width word : ℕ} (hw : 0 < width) (hword : word < 2^width) :
    word.testBit (width-1) = true ↔ 2^(width-1) ≤ word := by
  refine ⟨Nat.ge_two_pow_of_testBit, fun h => Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt h ?_⟩
  rwa [Nat.sub_add_cancel (by omega : 1 ≤ width)]

end UnitDistancePacked


namespace UnitDistancePacked

private def encodeVector (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + base * encodeVector base ds

private theorem lane_vector {base : ℕ} (hb : 0 < base) (ds : List ℕ)
    (hd : ∀ d ∈ ds, d < base) (i : ℕ) :
    lane base (encodeVector base ds) i = ds[i]?.getD 0 := by
  induction ds generalizing i with
  | nil => simp [lane, encodeVector]
  | cons d ds ih =>
    have hlt := hd d List.mem_cons_self
    cases i with
    | zero =>
      simp only [lane, encodeVector, pow_zero, Nat.div_one, List.getElem?_cons_zero, Option.getD_some]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    | succ i =>
      simp only [lane, encodeVector, pow_succ, List.getElem?_cons_succ]
      rw [Nat.mul_comm (base^i) base, ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hlt, Nat.zero_add]
      exact ih (fun x hx => hd x (List.mem_cons_of_mem _ hx)) i

private theorem word_of_vector {width n word : ℕ} (hw : 0 < width)
    (hword : ∀ i ≥ n, lane (2^width) word i = 0) :
    word = encodeVector (2^width) ((List.range n).map (lane (2^width) word)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_lane hw word, testBit_lane hw (encodeVector _ _), lane_vector (Nat.two_pow_pos _)]
  · by_cases hj : j/width < n
    · simp [hj]
    · simp [hj, hword _ (Nat.le_of_not_gt hj)]
  · intro d hd
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hd
    exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem encodeVector_balance (base : ℕ) (d : ℕ → ℕ)
    (p q r : ℕ → ℕ) (n : ℕ)
    (h : ∀ i < n, r i + q i = d i + p i) :
    encodeVector base ((List.range n).map r) + encodeVector base ((List.range n).map q) =
      encodeVector base ((List.range n).map d) + encodeVector base ((List.range n).map p) := by
  induction n generalizing d p q r with
  | zero => simp [encodeVector]
  | succ n ih =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def, encodeVector]
    have h₁ := h 0 (Nat.zero_lt_succ n)
    have h₂ := ih (fun i => d (i+1)) (fun i => p (i+1)) (fun i => q (i+1)) (fun i => r (i+1))
      (fun i hi => h (i+1) (by omega))
    rw [Nat.add_add_add_comm, Nat.add_add_add_comm (d 0), ← Nat.mul_add, ← Nat.mul_add, h₁, h₂]

end UnitDistancePacked


namespace UnitDistancePacked

private theorem guarded_sub_lane {width n p q : ℕ} (hw : 0 < width)
    (hp : ∀ i, lane (2^width) p i < 2^(width-1))
    (hq : ∀ i, lane (2^width) q i < 2^(width-1))
    (hp0 : ∀ i ≥ 2^n, lane (2^width) p i = 0)
    (hq0 : ∀ i ≥ 2^n, lane (2^width) q i = 0) (i : ℕ) (hi : i < 2^n) :
    lane (2^width) (repeatWord (2^(width-1)) width n + p - q) i =
      2^(width-1) + lane (2^width) p i - lane (2^width) q i := by
  let base := 2^width
  let guard := 2^(width-1)
  let g := repeatWord guard width n
  let r (i : ℕ) := guard + lane base p i - lane base q i
  have hbase : base = guard * 2 := by
    dsimp [base, guard]
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ width)]
  have hguard (j : ℕ) := high_guard_lane (n := n) hw j
  have hg0 (j : ℕ) (hj : j ≥ 2^n) : lane base g j = 0 := by
    simpa [base, g, guard, Nat.not_lt_of_ge hj] using hguard j
  have he (j : ℕ) (hj : j < 2^n) :
      r j + lane base q j = lane base g j + lane base p j := by
    have hl : lane base g j = guard := by simpa [base, g, guard, hj] using hguard j
    rw [hl]
    have hqj : lane base q j < guard := hq j
    dsimp [r]
    omega
  have hbal := encodeVector_balance base (lane base g) (lane base p) (lane base q) r (2^n) he
  rw [← word_of_vector hw hg0, ← word_of_vector hw hp0, ← word_of_vector hw hq0] at hbal
  have htotal : g + p - q = encodeVector base ((List.range (2^n)).map r) := by omega
  have hr (j : ℕ) : r j < base := by
    have hpj : lane base p j < guard := hp j
    calc
      r j < guard * 2 := by dsimp [r]; omega
      _ = base := hbase.symm
  change lane base (g+p-q) i = r i
  rw [htotal, lane_vector (Nat.two_pow_pos width)]
  · simp [hi]
  · intro d hd
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hd
    exact hr j

private theorem zeta_lane_zero {width n : ℕ} (t : Weights)
    (ht : ∀ r ∈ t, r.1 < 2^n)
    (hm : mass t * 2^n < 2^width) (hw : 0 < width) (i : ℕ) (hi : i ≥ 2^n) :
    lane (2^width) (zetaWord width n (encode (2^width) t)) i = 0 := by
  let e := (List.range n).foldl (fun w j => zetaTerms j w) t
  have he := zetaTerms_fold_bounded (List.range n) n t (fun _ hj => List.mem_range.1 hj) ht
  have hmass := zetaTerms_fold_mass (List.range n) t
  rw [List.length_range] at hmass
  rw [zetaWord_eq width n hw t ht hm, lane_encode (Nat.two_pow_pos _) e (lt_of_le_of_lt hmass hm)]
  unfold massAt
  have he' : e.filter (fun r => r.1 = i) = [] := by
    apply List.filter_eq_nil_iff.2
    intro r hr
    have hl : r.1 < 2^n := he r hr
    simp [show r.1 ≠ i by omega]
  simp [he', mass]

end UnitDistancePacked


namespace UnitDistancePacked

private theorem setBit_xor_of_clear {x j : ℕ} (hx : x.testBit j = false) :
    x + 2^j = x ^^^ 2^j := by
  rw [setBit_of_clear hx]
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : j = k
  · subst k
    simp [hx]
  · simp [h]

private theorem toggleBit_of {x j : ℕ} :
    (x ^^^ 2^j).testBit j = !x.testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_self]
  cases x.testBit j <;> decide

private theorem massAt_cons (i : ℕ) (r : ℕ × ℕ) (t : Weights) :
    massAt i (r :: t) = (if r.1 = i then r.2 else 0) + massAt i t := by
  by_cases h : r.1 = i <;> simp [massAt, mass, h]

private theorem massAt_append (i : ℕ) (t u : Weights) :
    massAt i (t ++ u) = massAt i t + massAt i u := by
  simp [massAt, mass]

private theorem massAt_copy (j i : ℕ) (t : Weights) :
    massAt i ((t.filter fun r => !r.1.testBit j).map (fun r => (r.1 + 2^j, r.2))) =
      if i.testBit j then massAt (i ^^^ 2^j) t else 0 := by
  induction t with
  | nil => simp [massAt, mass]
  | cons r t ih =>
    have hc : (r.1 ^^^ 2^j = i) ↔ r.1 = (i ^^^ 2^j) := by
      constructor <;> intro h
      · rw [← h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      · rw [h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    cases hr : r.1.testBit j
    · have hadd := setBit_xor_of_clear hr
      have hfalse (hi : i.testBit j = false) : r.1 ^^^ 2^j ≠ i := by
        intro h
        have he := congrArg (fun p : ℕ => p.testBit j) h
        simp [hr, hi] at he
      cases hi : i.testBit j
      · simp [hr, hi, ih, massAt_cons, hadd, hfalse hi]
      · simp [hr, hi, ih, massAt_cons, hadd, hc]
    · have hfalse (hi : i.testBit j = true) : r.1 ≠ i ^^^ 2^j := by
        intro h
        have he := congrArg (fun p : ℕ => p.testBit j) h
        simp [hr, hi] at he
      cases hi : i.testBit j
      · simp [hr, hi, ih]
      · simp [hr, hi, ih, massAt_cons, hfalse hi]

private theorem massAt_zetaTerms (j i : ℕ) (t : Weights) :
    massAt i (zetaTerms j t) =
      massAt i t + if i.testBit j then massAt (i ^^^ 2^j) t else 0 := by
  rw [zetaTerms, massAt_append, massAt_copy]

end UnitDistancePacked


namespace UnitDistancePacked

private def Reachable (k source target : ℕ) : Prop :=
  (∀ j < k, source.testBit j = true → target.testBit j = true) ∧
  ∀ j ≥ k, source.testBit j = target.testBit j

private theorem reachable_zero (source target : ℕ) :
    Reachable 0 source target ↔ source = target := by
  constructor
  · intro h
    exact Nat.eq_of_testBit_eq fun j => h.2 j (Nat.zero_le j)
  · rintro rfl
    exact ⟨fun _ _ h => h, fun _ _ => rfl⟩

private theorem testBit_xor_other {i j : ℕ} (h : i ≠ j) (x : ℕ) :
    (x ^^^ 2^i).testBit j = x.testBit j := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne h]
  cases x.testBit j <;> decide

private theorem reachable_succ (k a b : ℕ) :
    Reachable (k+1) a b ↔
      Reachable k a b ∨ (b.testBit k = true ∧ Reachable k a (b ^^^ 2^k)) := by
  constructor
  · intro h
    by_cases hab : a.testBit k = b.testBit k
    · exact Or.inl ⟨fun j hj => h.1 j (by omega), fun j hj => by
        rcases Nat.eq_or_lt_of_le hj with h₁ | h₁
        · simpa [← h₁] using hab
        · exact h.2 j (by omega)⟩
    · have ha : a.testBit k = false := by
        cases e : a.testBit k
        · rfl
        · exact False.elim (hab (e.trans (h.1 k (by omega) e).symm))
      have hb : b.testBit k = true := by
        cases e : b.testBit k
        · exact False.elim (hab (ha.trans e.symm))
        · rfl
      refine Or.inr ⟨hb, ⟨?_, ?_⟩⟩
      · intro j hj hja
        rw [testBit_xor_other (by omega : k ≠ j)]
        exact h.1 j (by omega) hja
      · intro j hj
        rcases Nat.eq_or_lt_of_le hj with h₁ | h₁
        · subst j
          simp [ha, hb]
        · rw [testBit_xor_other (by omega : k ≠ j)]
          exact h.2 j (by omega)
  · intro h
    rcases h with h | ⟨hb, h⟩
    · refine ⟨?_, fun j hj => h.2 j (by omega)⟩
      intro j hj hja
      by_cases hlt : j < k
      · exact h.1 j hlt hja
      · rwa [← h.2 j (by omega)]
    · refine ⟨?_, ?_⟩
      · intro j hj hja
        by_cases hlt : j < k
        · have ht := h.1 j hlt hja
          rwa [testBit_xor_other (by omega : k ≠ j)] at ht
        · rwa [show j = k by omega]
      · intro j hj
        have ht := h.2 j (by omega)
        rwa [testBit_xor_other (by omega : k ≠ j)] at ht

private theorem reachable_disjoint (k a b : ℕ)
    (h : Reachable k a b) (h' : Reachable k a (b ^^^ 2^k)) : False := by
  have s := (h.2 k le_rfl).symm.trans (h'.2 k le_rfl)
  rw [toggleBit_of] at s
  cases e : b.testBit k <;> simp [e] at s

end UnitDistancePacked


namespace UnitDistancePacked

private noncomputable def massWhere (p : ℕ → Prop) (t : Weights) : ℕ := by
  classical
  exact (t.map fun r => if p r.1 then r.2 else 0).sum

private theorem massWhere_cons (p : ℕ → Prop) (r : ℕ × ℕ) (t : Weights) :
    letI := Classical.propDecidable
    massWhere p (r :: t) = (if p r.1 then r.2 else 0) + massWhere p t := rfl

private theorem massWhere_eq (I : ℕ) (t : Weights) :
    massWhere (· = I) t = massAt I t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    rw [massWhere_cons, massAt_cons, ih]
    by_cases h : r.1 = I <;> simp [h]

private theorem massWhere_reach_succ (k I : ℕ) (t : Weights) :
    massWhere (Reachable (k+1) · I) t =
      massWhere (Reachable k · I) t +
        if I.testBit k then massWhere (Reachable k · (I ^^^ 2^k)) t else 0 := by
  classical
  induction t with
  | nil => cases I.testBit k <;> rfl
  | cons r t ih =>
    simp only [massWhere_cons]
    rw [ih, reachable_succ k r.1 I]
    by_cases h₁ : Reachable k r.1 I
    · have h₂ : ¬Reachable k r.1 (I ^^^ 2^k) :=
        fun h => reachable_disjoint k r.1 I h₁ h
      cases hi : I.testBit k <;> simp [h₁, h₂, Nat.add_assoc]
    · cases hi : I.testBit k
      · simp [h₁]
      · simp [h₁, Nat.add_left_comm]

private theorem massAt_zeta_range (k I : ℕ) (t : Weights) :
    massAt I ((List.range k).foldl (fun w j => zetaTerms j w) t) =
      massWhere (Reachable k · I) t := by
  induction k generalizing I with
  | zero =>
    change massAt I t = _
    rw [show (Reachable 0 · I) = (· = I) from funext (fun a => propext (reachable_zero a I)),
      massWhere_eq]
  | succ k ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [massAt_zetaTerms, ih, ih, massWhere_reach_succ]

private def submask (m I : ℕ) : Prop := m &&& I = m

private theorem submask_iff (m I : ℕ) :
    submask m I ↔ ∀ j, m.testBit j = true → I.testBit j = true := by
  constructor
  · intro h j hj
    have hh := congrArg (fun n => Nat.testBit n j) h
    simpa only [Nat.testBit_land, hj, Bool.true_and] using hh
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_land]
    cases e : m.testBit j
    · simp
    · simp only [Bool.true_and]
      exact h j e

private theorem reachable_full {n a I : ℕ} (ha : a < 2^n) (hI : I < 2^n) :
    Reachable n a I ↔ submask a I := by
  have off {m : ℕ} (hm : m < 2^n) {k : ℕ} (hk : n ≤ k) :
      m.testBit k = false :=
    Nat.testBit_lt_two_pow (hm.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hk))
  rw [submask_iff]
  constructor
  · intro h k hs
    by_cases hk : k < n
    · exact h.1 k hk hs
    · simp [off ha (Nat.le_of_not_gt hk)] at hs
  · intro h
    exact ⟨fun k _ => h k, fun k hk => (off ha hk).trans (off hI hk).symm⟩

private theorem massWhere_congr (p q : ℕ → Prop) (t : Weights)
    (h : ∀ r ∈ t, p r.1 ↔ q r.1) : massWhere p t = massWhere q t := by
  classical
  unfold massWhere
  congr 1
  apply List.map_congr_left
  intro r hr
  simp only [h r hr]

private theorem zeta_submask_lane (width n : ℕ) (hw : 0 < width) (t : Weights)
    (hbound : ∀ r ∈ t, r.1 < 2^n) (hmass : mass t * 2^n < 2^width)
    (I : ℕ) (hI : I < 2^n) :
    lane (2^width) (zetaWord width n (encode (2^width) t)) I = massWhere (submask · I) t := by
  have h := zetaTerms_fold_mass (List.range n) t
  rw [List.length_range] at h
  rw [zetaWord_eq width n hw t hbound hmass,
    lane_encode (Nat.two_pow_pos _) _ (h.trans_lt hmass), massAt_zeta_range]
  apply massWhere_congr
  exact fun r hr => reachable_full (hbound r hr) hI

end UnitDistancePacked


namespace UnitDistancePacked

private theorem foldl_preserves {α β : Type} (p : α → Prop) (f : α → β → α)
    (a : α) (xs : List β) (ha : p a)
    (hf : ∀ b ∈ xs, ∀ curr, p curr → p (f curr b)) :
    p (xs.foldl f a) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons b xs ih =>
    exact ih (f a b) (hf b List.mem_cons_self a ha)
      (fun x hx => hf x (List.mem_cons_of_mem _ hx))

private theorem valid_guard_bit {width : ℕ} (hw : 0 < width) (rows : List ℕ)
    (allowed mask : ℕ) (hmask : mask < 2^rows.length)
    (ha : ∀ i < rows.length, mask.testBit i = true → allowed.testBit i = true)
    (he : ∀ i < rows.length, ∀ j < i, (rows[i]?.getD 0).testBit j = true →
      mask.testBit i = false ∨ mask.testBit j = false) :
    (auditGuards width rows allowed).2.testBit (width-1 + width*mask) = true := by
  let n := rows.length
  let index := width-1 + width*mask
  have hwidth : width-1 < width := by omega
  have hindex : index/width = mask := by
    dsimp [index]
    rw [Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hwidth, Nat.zero_add]
  have guard : (repeatWord (2^(width-1)) width n).testBit index = true := by
    rw [← bit_at_lane hw hwidth, high_guard_lane hw, if_pos hmask, Nat.testBit_two_pow_self]
  have stripe (i : ℕ) (hi : i < n) :
      (lowStripes width n i).testBit index = !mask.testBit i := by
    rw [lowStripes_bits hw hi, hindex]
    simp [hmask, n]
  unfold auditGuards
  refine foldl_preserves (fun (a : ℕ) => a.testBit index = true) _ _ _ guard ?_
  intro i hi current hcurrent
  have hin := List.mem_range.1 hi
  dsimp only
  split
  · refine foldl_preserves (fun (a : ℕ) => a.testBit index = true) _ _ _ hcurrent ?_
    intro j hj curr hcurr
    have hji := List.mem_range.1 hj
    split
    · rename_i hv
      rw [Nat.testBit_and, Nat.testBit_or, stripe i hin, stripe j (hji.trans hin)]
      rcases he i hin j hji hv with hx | hx <;> simp [hcurr, hx]
    · exact hcurr
  · rename_i hv
    have hm : mask.testBit i = false := by
      cases hc : mask.testBit i
      · rfl
      · exact False.elim (hv (ha i hin hc))
    have hstripe : (lowStripes width rows.length i).testBit index = !mask.testBit i := stripe i hin
    simp [Nat.testBit_and, hstripe, hcurrent, hm]

end UnitDistancePacked


namespace UnitDistancePacked

private abbrev Terms := List (ℕ × ℤ)

private def positiveTerms (t : Terms) : Weights :=
  t.filterMap fun r => if 0 ≤ r.2 then some (r.1, r.2.toNat) else none

private def negativeTerms (t : Terms) : Weights :=
  t.filterMap fun r => if 0 ≤ r.2 then none else some (r.1, (-r.2).toNat)

private def packAdd (width : ℕ) (a : ℕ × ℕ) (r : ℕ × ℤ) : ℕ × ℕ :=
  if 0 ≤ r.2 then (a.1 + (r.2.toNat <<< (width*r.1)), a.2)
  else (a.1, a.2 + ((-r.2).toNat <<< (width*r.1)))

private def packWords (width : ℕ) (t : Terms) : ℕ × ℕ :=
  t.foldl (packAdd width) (0, 0)

private theorem packFold_eq (width : ℕ) (t : Terms) (a : ℕ × ℕ) :
    t.foldl (packAdd width) a =
      (a.1 + encode (2^width) (positiveTerms t), a.2 + encode (2^width) (negativeTerms t)) := by
  induction t generalizing a with
  | nil => simp [positiveTerms, negativeTerms, encode]
  | cons r t ih =>
    rw [List.foldl_cons, ih]
    by_cases hr : 0 ≤ r.2 <;>
      simp [packAdd, encode, positiveTerms, negativeTerms, hr, Nat.shiftLeft_eq, pow_mul, Nat.add_assoc]

private theorem packWords_eq (width : ℕ) (t : Terms) :
    packWords width t =
      (encode (2^width) (positiveTerms t), encode (2^width) (negativeTerms t)) := by
  simpa only [packWords, Nat.zero_add] using packFold_eq width t (0,0)

private def totalMass (t : Terms) : ℕ := (t.map (fun r => r.2.natAbs)).sum

private theorem absMass_bound (t : Terms) :
    mass (positiveTerms t) + mass (negativeTerms t) = totalMass t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    by_cases hr : 0 ≤ r.2
    · have hh : r.2.toNat = r.2.natAbs := by omega
      simp [positiveTerms, negativeTerms, mass, totalMass, hr, hh] at ih ⊢
      omega
    · have hh : (-r.2).toNat = r.2.natAbs := by omega
      simp [positiveTerms, negativeTerms, mass, totalMass, hr, hh] at ih ⊢
      omega

private theorem terms_bounded (n : ℕ) (t : Terms)
    (ht : ∀ r ∈ t, r.1 < 2^n) :
    (∀ r ∈ positiveTerms t, r.1 < 2^n) ∧ (∀ r ∈ negativeTerms t, r.1 < 2^n) := by
  constructor <;> intro r hr
  · obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
    by_cases h : 0 ≤ x.2
    · simp [h] at e
      rw [← e]
      exact ht x hx
    · simp [h] at e
  · obtain ⟨x, hx, e⟩ := List.mem_filterMap.1 hr
    by_cases h : 0 ≤ x.2
    · simp [h] at e
    · simp [h] at e
      rw [← e]
      exact ht x hx

private instance (m I : ℕ) : Decidable (submask m I) :=
  inferInstanceAs (Decidable (_ = _))

def score (I : ℕ) (t : Terms) : ℤ :=
  (t.map fun r => if submask r.1 I then r.2 else 0).sum

private theorem score_split (I : ℕ) (t : Terms) :
    score I t = (massWhere (submask · I) (positiveTerms t) : ℤ) -
      (massWhere (submask · I) (negativeTerms t) : ℤ) := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    simp only [score, List.map_cons, List.sum_cons] at ih ⊢
    by_cases hr : 0 ≤ r.2 <;>
      by_cases hm : submask r.1 I <;>
      simp [positiveTerms, negativeTerms, hr, massWhere_cons, hm] at ih ⊢ <;>
      omega

private def auditPacked (width : ℕ) (rows : List ℕ) (allowed : ℕ) (packed : ℕ × ℕ) : Bool :=
  let n := rows.length
  let (p, q) := packed
  let (g, valid) := auditGuards width rows allowed
  let word := g + zetaWord width n p - zetaWord width n q
  word &&& valid == valid

private theorem zeta_lane_lt_guard (width n : ℕ) (hw : 0 < width) (t : Weights)
    (ht : ∀ r ∈ t, r.1 < 2^n)
    (hm : mass t * 2^n < 2^(width-1)) (i : ℕ) :
    lane (2^width) (zetaWord width n (encode (2^width) t)) i < 2^(width-1) := by
  have hg : 2^(width-1) ≤ 2^width := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have h := zetaTerms_fold_mass (List.range n) t
  rw [List.length_range] at h
  rw [zetaWord_eq width n hw t ht (hm.trans_le hg),
    lane_encode (Nat.two_pow_pos _) _ ((h.trans_lt hm).trans_le hg)]
  exact (mass_filter_le _ _).trans_lt (h.trans_lt hm)

private theorem auditPacked_sound {width : ℕ} (hw : 0 < width) (rows : List ℕ)
    (allowed : ℕ) (t : Terms) (hcheck : auditPacked width rows allowed (packWords width t) = true)
    (hterms : ∀ r ∈ t, r.1 < 2^rows.length)
    (hmass : totalMass t * 2^rows.length < 2^(width-1))
    (I : ℕ) (hI : I < 2^rows.length)
    (ha : ∀ i < rows.length, I.testBit i = true → allowed.testBit i = true)
    (he : ∀ i < rows.length, ∀ j < i, (rows[i]?.getD 0).testBit j = true →
      I.testBit i = false ∨ I.testBit j = false) : 0 ≤ score I t := by
  let n := rows.length

  obtain ⟨hp, hq⟩ := terms_bounded n t hterms
  have hgt : 2^(width-1) ≤ 2^width := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hm := absMass_bound t
  have hmp : mass (positiveTerms t) * 2^n < 2^(width-1) :=
    (Nat.mul_le_mul_right _ (show mass (positiveTerms t) ≤ totalMass t by omega)).trans_lt hmass
  have hmq : mass (negativeTerms t) * 2^n < 2^(width-1) :=
    (Nat.mul_le_mul_right _ (show mass (negativeTerms t) ≤ totalMass t by omega)).trans_lt hmass
  let P := zetaWord width n (encode (2^width) (positiveTerms t))
  let Q := zetaWord width n (encode (2^width) (negativeTerms t))
  let G := repeatWord (2^(width-1)) width n
  let V := (auditGuards width rows allowed).2
  simp only [auditPacked, packWords_eq, beq_iff_eq] at hcheck
  change (G + P - Q) &&& V = V at hcheck
  let idx := width-1 + width*I
  have hv : V.testBit idx = true := valid_guard_bit hw rows allowed I hI ha he
  have hb := congrArg (fun w : ℕ => w.testBit idx) hcheck
  simp only [Nat.testBit_and, hv, Bool.and_true] at hb
  have ht : width-1 < width := by omega
  change (G + P - Q).testBit (width-1 + width*I) = true at hb
  rw [← bit_at_lane hw ht] at hb
  have hguard := (high_bit_iff hw (Nat.mod_lt _ (Nat.two_pow_pos width))).1 hb
  change 2^(width-1) ≤ lane (2^width) (G + P - Q) I at hguard
  rw [guarded_sub_lane hw (zeta_lane_lt_guard width n hw _ hp hmp)
    (zeta_lane_lt_guard width n hw _ hq hmq)
    (zeta_lane_zero _ hp (hmp.trans_le hgt) hw)
    (zeta_lane_zero _ hq (hmq.trans_le hgt) hw) I hI] at hguard
  rw [zeta_submask_lane width n hw _ hp (hmp.trans_le hgt) I hI,
      zeta_submask_lane width n hw _ hq (hmq.trans_le hgt) I hI] at hguard
  rw [score_split]
  have hgpos := Nat.two_pow_pos (width-1)
  omega

end UnitDistancePacked


namespace UnitDistancePacked

private def restrictMask (free : List ℕ) (m : ℕ) : ℕ :=
  match free with
  | [] => 0
  | v :: vs => Nat.bit (m.testBit v) (restrictMask vs m)

private theorem restrictMask_lt (free : List ℕ) (m : ℕ) :
    restrictMask free m < 2^free.length := by
  induction free with
  | nil => simp [restrictMask]
  | cons v vs ih => simpa [restrictMask] using ih

private theorem testBit_restrictMask (free : List ℕ) (m i : ℕ) (hi : i < free.length) :
    (restrictMask free m).testBit i = m.testBit (free[i]'hi) := by
  induction free generalizing i with
  | nil => simp at hi
  | cons v vs ih =>
    cases i with
    | zero => simp [restrictMask]
    | succ i =>
      rw [restrictMask, Nat.testBit_bit_succ]
      exact ih i (by simpa using hi)

private def freeMask : List ℕ → ℕ
  | [] => 0
  | v :: vs => 2^v ||| freeMask vs

private theorem testBit_freeMask (free : List ℕ) (j : ℕ) :
    (freeMask free).testBit j = true ↔ j ∈ free := by
  induction free with
  | nil => simp [freeMask]
  | cons v vs ih =>
    simp only [freeMask, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

private def AgreesOutside (free : List ℕ) (fixed I : ℕ) : Prop :=
  ∀ j ∉ free, I.testBit j = fixed.testBit j

private theorem submask_restrict (free : List ℕ) (fixed I m : ℕ)
    (hI : AgreesOutside free fixed I) :
    submask m I ↔ submask m (fixed ||| freeMask free) ∧
      submask (restrictMask free m) (restrictMask free I) := by
  simp only [submask_iff]
  constructor
  · intro h
    constructor
    · intro j hj
      rw [Nat.testBit_or, Bool.or_eq_true]
      by_cases hjf : j ∈ free
      · exact Or.inr ((testBit_freeMask free j).2 hjf)
      · exact Or.inl ((hI j hjf).symm.trans (h j hj))
    · intro i hi
      by_cases hib : i < free.length
      · rw [testBit_restrictMask free m i hib] at hi
        rw [testBit_restrictMask free I i hib]
        exact h _ hi
      · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hib)
        simp [Nat.testBit_lt_two_pow ((restrictMask_lt free m).trans_le hpow)] at hi
  · rintro ⟨hallowed, hproj⟩ j hj
    by_cases hm : j ∈ free
    · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
      have hb : (restrictMask free m).testBit i = true := by
        rw [testBit_restrictMask free m i hi, he, hj]
      have h := hproj i hb
      rwa [testBit_restrictMask free I i hi, he] at h
    · have hbit : (freeMask free).testBit j = false := by
        cases h : (freeMask free).testBit j
        · rfl
        · exact False.elim (hm ((testBit_freeMask free j).1 h))
      have hf := hallowed j hj
      rw [Nat.testBit_or, hbit, Bool.or_false] at hf
      exact (hI j hm).trans hf

private def projectTerms (free : List ℕ) (fixed : ℕ) (t : Terms) : Terms :=
  let allowed := fixed ||| freeMask free
  t.filterMap fun r =>
    if submask r.1 allowed then some (restrictMask free r.1, r.2) else none

private theorem score_projectTerms (free : List ℕ) (fixed I : ℕ) (t : Terms)
    (hi : AgreesOutside free fixed I) :
    score (restrictMask free I) (projectTerms free fixed t) = score I t := by
  induction t with
  | nil => rfl
  | cons r t ih =>
    have hm := submask_restrict free fixed I r.1 hi
    by_cases h : submask r.1 (fixed ||| freeMask free)
    · have he : submask r.1 I ↔ submask (restrictMask free r.1) (restrictMask free I) := by
        rw [hm, and_iff_right h]
      simp [projectTerms, h, score, he] at ih ⊢
      rw [ih]
    · have hn : ¬submask r.1 I := fun e => h (hm.1 e).1
      simpa [projectTerms, score, h, hn] using ih

private def restrictRows (adj : ℕ → ℕ) (free : List ℕ) : List ℕ :=
  free.map fun i => restrictMask free (adj i)

private def Independent (adj : ℕ → ℕ) (I : ℕ) : Prop :=
  ∀ i j, (adj i).testBit j = true → I.testBit i = true → I.testBit j = false

private theorem restriction_independent (adj : ℕ → ℕ) (free : List ℕ) (I : ℕ)
    (hI : Independent adj I) (i : ℕ) (hi : i < (restrictRows adj free).length)
    (j : ℕ) (hj : j < i)
    (he : ((restrictRows adj free)[i]?.getD 0).testBit j = true) :
    (restrictMask free I).testBit i = false ∨ (restrictMask free I).testBit j = false := by
  have hi' : i < free.length := by simpa [restrictRows] using hi
  have hj' : j < free.length := hj.trans hi'
  rw [restrictRows, List.getElem?_map, List.getElem?_eq_getElem hi',
    Option.map_some, Option.getD_some, testBit_restrictMask free _ j hj'] at he
  rw [testBit_restrictMask free I i hi', testBit_restrictMask free I j hj']
  cases hh : I.testBit (free[i]'hi')
  · exact Or.inl rfl
  · exact Or.inr (hI _ _ he hh)

private def omitVertex (free : List ℕ) (v : ℕ) : List ℕ :=
  free.filter fun w => w ≠ v

private def omitNeighbors (adj : ℕ → ℕ) (free : List ℕ) (v : ℕ) : List ℕ :=
  free.filter fun w => (decide (w ≠ v)) && !(adj v).testBit w

private def exclude (fixed v : ℕ) : ℕ := Nat.ldiff fixed (2^v)

private def includeVertex (adj : ℕ → ℕ) (fixed v : ℕ) : ℕ :=
  Nat.ldiff fixed (adj v) ||| 2^v

private def NonnegativeOn (adj : ℕ → ℕ) (free : List ℕ) (fixed : ℕ) (t : Terms) : Prop :=
  ∀ I, Independent adj I → AgreesOutside free fixed I → 0 ≤ score I t

private theorem nonnegative_branch (adj : ℕ → ℕ) (free : List ℕ) (fixed v : ℕ) (t : Terms)
    (hoff : NonnegativeOn adj (omitVertex free v) (exclude fixed v) t)
    (hon : NonnegativeOn adj (omitNeighbors adj free v) (includeVertex adj fixed v) t) :
    NonnegativeOn adj free fixed t := by
  intro I hi hag
  cases hv : I.testBit v
  · apply hoff I hi
    intro j hj
    by_cases e : j = v
    · subst j
      simp [exclude, hv]
    · have hfree : j ∉ free := fun h => hj (List.mem_filter.2 ⟨h, by simp [e]⟩)
      simpa [exclude, Nat.testBit_two_pow_of_ne (Ne.symm e)] using hag j hfree
  · apply hon I hi
    intro j hj
    by_cases e : j = v
    · subst j
      simp [includeVertex, hv]
    · cases hn : (adj v).testBit j
      · have hfree : j ∉ free := fun h => hj (List.mem_filter.2 ⟨h, by simp [e, hn]⟩)
        simpa [includeVertex, hn, Nat.testBit_two_pow_of_ne (Ne.symm e)] using hag j hfree
      · have hj' := hi v j hn hv
        simp [includeVertex, hn, hj', Nat.testBit_two_pow_of_ne (Ne.symm e)]

private theorem nonnegative_unconstrained (adj : ℕ → ℕ) (n : ℕ) (t : Terms)
    (h : NonnegativeOn adj (List.range n) 0 t) (I : ℕ)
    (hi : Independent adj I) (hb : I < 2^n) :
    0 ≤ score I t := by
  apply h I hi
  intro j hj
  have hle : n ≤ j := Nat.le_of_not_gt (fun h => hj (List.mem_range.2 h))
  rw [Nat.zero_testBit]
  exact Nat.testBit_lt_two_pow
    (hb.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hle))

end UnitDistancePacked


namespace UnitDistancePacked

private def addProjection (width : ℕ) (free : List ℕ) (allowed : ℕ)
    (a : ℕ × ℕ) (r : ℕ × ℤ) : ℕ × ℕ :=
  if submask r.1 allowed then packAdd width a (restrictMask free r.1, r.2) else a

private def packProjected (width : ℕ) (free : List ℕ) (fixed : ℕ)
    (blocks : List Terms) : ℕ × ℕ :=
  let add := addProjection width free (fixed ||| freeMask free)
  blocks.foldl (fun a b => b.foldl add a) (0, 0)

private def checkProjected (width : ℕ) (adj : ℕ → ℕ) (free : List ℕ)
    (fixed : ℕ) (blocks : List Terms) : Bool :=
  let n := free.length
  let (p, q) := packProjected width free fixed blocks
  let (g, valid) := auditGuards width (restrictRows adj free) (2^n-1)
  let word := g + zetaWord width n p - zetaWord width n q
  word &&& valid == valid

private theorem packProjected_eq (width : ℕ) (free : List ℕ) (fixed : ℕ)
    (blocks : List Terms) :
    packProjected width free fixed blocks =
      packWords width (projectTerms free fixed blocks.flatten) := by
  let a := addProjection width free (fixed ||| freeMask free)
  have h₁ (t : Terms) (w : ℕ × ℕ) :
      t.foldl a w = (projectTerms free fixed t).foldl (packAdd width) w := by
    induction t generalizing w with
    | nil => rfl
    | cons r t ih =>
      rw [List.foldl_cons, ih]
      by_cases hr : submask r.1 (fixed ||| freeMask free) <;>
        simp [a, addProjection, projectTerms, hr]
  have h₂ (w : ℕ × ℕ) :
      blocks.foldl (fun w b => b.foldl a w) w =
      blocks.flatten.foldl a w := by
    induction blocks generalizing w with
    | nil => rfl
    | cons b bs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.foldl_append]
  exact (h₂ (0,0)).trans (h₁ blocks.flatten (0,0))

private theorem projectTerms_support (free : List ℕ) (fixed : ℕ) (t : Terms) :
    ∀ r ∈ projectTerms free fixed t, r.1 < 2^free.length := by
  intro r hr
  obtain ⟨s, _, hs⟩ := List.mem_filterMap.1 hr
  by_cases ha : submask s.1 (fixed ||| freeMask free)
  · simp [ha] at hs
    rw [← hs]
    exact restrictMask_lt free s.1
  · simp [ha] at hs

private theorem projectTerms_mass (free : List ℕ) (fixed : ℕ) (t : Terms) :
    totalMass (projectTerms free fixed t) ≤ totalMass t := by
  induction t with
  | nil => simp [projectTerms, totalMass]
  | cons r rs ih =>
    by_cases h : submask r.1 (fixed ||| freeMask free) <;>
      simp [projectTerms, totalMass, h] at ih ⊢ <;> omega

private theorem checkProjected_sound {width : ℕ} (hw : 0 < width)
    (adj : ℕ → ℕ) (free : List ℕ) (fixed : ℕ) (blocks : List Terms)
    (hm : totalMass blocks.flatten * 2^free.length < 2^(width-1))
    (hc : checkProjected width adj free fixed blocks = true) :
    NonnegativeOn adj free fixed blocks.flatten := by
  intro I hI hag
  rw [← score_projectTerms free fixed I _ hag]
  let rows := restrictRows adj free
  have hlen : rows.length = free.length := by simp [rows, restrictRows]
  have hcore : auditPacked width rows (2^free.length-1)
      (packWords width (projectTerms free fixed blocks.flatten)) = true := by
    rw [← packProjected_eq]
    unfold auditPacked checkProjected at *
    rwa [hlen]
  apply auditPacked_sound hw rows _ _ hcore
  · intro r hr
    rw [hlen]
    exact projectTerms_support free fixed _ r hr
  · rw [hlen]
    exact (Nat.mul_le_mul_right _ (projectTerms_mass free fixed _)).trans_lt hm
  · rw [hlen]
    exact restrictMask_lt free I
  · intro i hi _
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hi.trans_eq hlen
  · exact fun i hi j hj => restriction_independent adj free I hI i hi j hj

end UnitDistancePacked

/- Exact integer arithmetic for the four radicals in the 29-vertex construction. -/

namespace SnailCoordinates

private def extendAdd {K : Type} (add : K → K → K) (x y : K × K) : K × K :=
  (add x.1 y.1, add x.2 y.2)

private def extendNeg {K : Type} (neg : K → K) (x : K × K) : K × K :=
  (neg x.1, neg x.2)

private def extendMul {K : Type} (add mul : K → K → K) (D : K)
    (x y : K × K) : K × K :=
  (add (mul x.1 y.1) (mul D (mul x.2 y.2)),
    add (mul x.1 y.2) (mul x.2 y.1))

private def extendEval {K : Type} (e : K → ℝ) (r : ℝ) (x : K × K) : ℝ :=
  e x.1 + r * e x.2

private theorem extendEval_add {K : Type} (e : K → ℝ) (r : ℝ) (add : K → K → K)
    (hadd : ∀ x y, e (add x y) = e x + e y) (x y : K × K) :
    extendEval e r (extendAdd add x y) = extendEval e r x + extendEval e r y := by
  simp only [extendEval, extendAdd, hadd]
  ring

private theorem extendEval_neg {K : Type} (e : K → ℝ) (r : ℝ) (neg : K → K)
    (hneg : ∀ x, e (neg x) = - e x) (x : K × K) :
    extendEval e r (extendNeg neg x) = - extendEval e r x := by
  simp only [extendEval, extendNeg, hneg]
  ring

private theorem extendEval_mul {K : Type} (e : K → ℝ) (r : ℝ) (add mul : K → K → K)
    (D : K) (hr : r^2 = e D)
    (hadd : ∀ x y, e (add x y) = e x + e y)
    (hmul : ∀ x y, e (mul x y) = e x * e y) (x y : K × K) :
    extendEval e r (extendMul add mul D x y) = extendEval e r x * extendEval e r y := by
  simp only [extendEval, extendMul, hadd, hmul]
  linear_combination -(e x.2 * e y.2) * hr

private abbrev K0 := ℤ
private def int0 (q : ℤ) : K0 := q
private def add0 (x y : K0) : K0 := x + y
private def mul0 (x y : K0) : K0 := x * y
private def neg0 (x : K0) : K0 := -x
private def eval0 (q : K0) : ℝ := q

private theorem eval0_add (x y : K0) : eval0 (add0 x y) = eval0 x + eval0 y := by
  simp [eval0, add0]

private theorem eval0_neg (x : K0) : eval0 (neg0 x) = -eval0 x := by simp [eval0, neg0]
private theorem eval0_mul (x y : K0) : eval0 (mul0 x y) = eval0 x * eval0 y := by simp [eval0, mul0]
private theorem eval0_int (q : ℤ) : eval0 (int0 q) = q := rfl

private abbrev K1 := K0 × K0
private def int1 (q : ℤ) : K1 := (int0 q, int0 0)
private def add1 := extendAdd (K := K0) add0
private def neg1 := extendNeg (K := K0) neg0
private def square1 : K0 := int0 3
private def mul1 := extendMul (K := K0) add0 mul0 square1
private noncomputable def radical1 : ℝ := Real.sqrt 3
private noncomputable def eval1 := extendEval (K := K0) eval0 radical1

private theorem eval1_int (q : ℤ) : eval1 (int1 q) = q := by
  simp [eval1, int1, extendEval, eval0_int]

private theorem radical1_sq : radical1^2 = eval0 square1 := by
  unfold radical1
  rw [Real.sq_sqrt (by norm_num)]
  unfold square1
  rw [eval0_int]
  norm_num

private theorem eval1_add (x y : K1) : eval1 (add1 x y) = eval1 x + eval1 y :=
  extendEval_add eval0 radical1 add0 eval0_add x y
private theorem eval1_neg (x : K1) : eval1 (neg1 x) = -eval1 x :=
  extendEval_neg eval0 radical1 neg0 eval0_neg x
private theorem eval1_mul (x y : K1) : eval1 (mul1 x y) = eval1 x * eval1 y :=
  extendEval_mul eval0 radical1 add0 mul0 square1 radical1_sq eval0_add eval0_mul x y

private abbrev K2 := K1 × K1
private def int2 (q : ℤ) : K2 := (int1 q, int1 0)
private def add2 := extendAdd (K := K1) add1
private def neg2 := extendNeg (K := K1) neg1
private def square2 : K1 := int1 11
private def mul2 := extendMul (K := K1) add1 mul1 square2
private noncomputable def radical2 : ℝ := Real.sqrt 11
private noncomputable def eval2 := extendEval (K := K1) eval1 radical2

private theorem eval2_int (q : ℤ) : eval2 (int2 q) = q := by
  simp [eval2, int2, extendEval, eval1_int]

private theorem radical2_sq : radical2^2 = eval1 square2 := by
  unfold radical2
  rw [Real.sq_sqrt (by norm_num)]
  unfold square2
  rw [eval1_int]
  norm_num

private theorem eval2_add (x y : K2) : eval2 (add2 x y) = eval2 x + eval2 y :=
  extendEval_add eval1 radical2 add1 eval1_add x y
private theorem eval2_neg (x : K2) : eval2 (neg2 x) = -eval2 x :=
  extendEval_neg eval1 radical2 neg1 eval1_neg x
private theorem eval2_mul (x y : K2) : eval2 (mul2 x y) = eval2 x * eval2 y :=
  extendEval_mul eval1 radical2 add1 mul1 square2 radical2_sq eval1_add eval1_mul x y

private abbrev K3 := K2 × K2
private def int3 (q : ℤ) : K3 := (int2 q, int2 0)
private def add3 := extendAdd (K := K2) add2
private def neg3 := extendNeg (K := K2) neg2
private def square3 : K2 := int2 5
private def mul3 := extendMul (K := K2) add2 mul2 square3
private noncomputable def radical3 : ℝ := Real.sqrt 5
private noncomputable def eval3 := extendEval (K := K2) eval2 radical3

private theorem eval3_int (q : ℤ) : eval3 (int3 q) = q := by
  simp [eval3, int3, extendEval, eval2_int]

private theorem radical3_sq : radical3^2 = eval2 square3 := by
  unfold radical3
  rw [Real.sq_sqrt (by norm_num)]
  unfold square3
  rw [eval2_int]
  norm_num

private theorem eval3_add (x y : K3) : eval3 (add3 x y) = eval3 x + eval3 y :=
  extendEval_add eval2 radical3 add2 eval2_add x y
private theorem eval3_neg (x : K3) : eval3 (neg3 x) = -eval3 x :=
  extendEval_neg eval2 radical3 neg2 eval2_neg x
private theorem eval3_mul (x y : K3) : eval3 (mul3 x y) = eval3 x * eval3 y :=
  extendEval_mul eval2 radical3 add2 mul2 square3 radical3_sq eval2_add eval2_mul x y

private abbrev K4 := K3 × K3
private def int4 (q : ℤ) : K4 := (int3 q, int3 0)
private def add4 := extendAdd (K := K3) add3
private def neg4 := extendNeg (K := K3) neg3
private def square4 : K3 := (((830, 0), (0, 158)), ((0, 0), (0, 0)))
private def mul4 := extendMul (K := K3) add3 mul3 square4
private noncomputable def radical4 : ℝ := Real.sqrt (830 + 158 * radical1 * radical2)
private noncomputable def eval4 := extendEval (K := K3) eval3 radical4

private theorem eval4_int (q : ℤ) : eval4 (int4 q) = q := by
  simp [eval4, int4, extendEval, eval3_int]

private theorem radical4_sq : radical4^2 = eval3 square4 := by
  unfold radical4 square4
  rw [Real.sq_sqrt (by unfold radical1 radical2; positivity)]
  simp only [eval3, eval2, eval1, eval0, extendEval]
  push_cast
  ring

private theorem eval4_add (x y : K4) : eval4 (add4 x y) = eval4 x + eval4 y :=
  extendEval_add eval3 radical4 add3 eval3_add x y
private theorem eval4_neg (x : K4) : eval4 (neg4 x) = -eval4 x :=
  extendEval_neg eval3 radical4 neg3 eval3_neg x
private theorem eval4_mul (x y : K4) : eval4 (mul4 x y) = eval4 x * eval4 y :=
  extendEval_mul eval3 radical4 add3 mul3 square4 radical4_sq eval3_add eval3_mul x y

abbrev Coordinates := K4 × K4

def add (x y : Coordinates) : Coordinates := (add4 x.1 y.1, add4 x.2 y.2)

def neg (x : Coordinates) : Coordinates := (neg4 x.1, neg4 x.2)

def sub (x y : Coordinates) : Coordinates := add x (neg y)

def conj (x : Coordinates) : Coordinates := (x.1, neg4 x.2)

def mul (x y : Coordinates) : Coordinates :=
  (add4 (mul4 x.1 y.1) (neg4 (mul4 x.2 y.2)),
    add4 (mul4 x.1 y.2) (mul4 x.2 y.1))

def squareNorm (x : Coordinates) : K4 := add4 (mul4 x.1 x.1) (mul4 x.2 x.2)

noncomputable def toComplex (x : Coordinates) : ℂ := ⟨eval4 x.1, eval4 x.2⟩

theorem toComplex_sub (x y : Coordinates) : toComplex (sub x y) = toComplex x - toComplex y := by
  apply Complex.ext <;> simp [toComplex, sub, add, neg, eval4_add, eval4_neg, sub_eq_add_neg]

theorem toComplex_conj (x : Coordinates) : toComplex (conj x) = star (toComplex x) := by
  apply Complex.ext <;> simp [toComplex, conj, eval4_neg]

theorem toComplex_mul (x y : Coordinates) : toComplex (mul x y) = toComplex x * toComplex y := by
  apply Complex.ext <;>
    simp [toComplex, mul, eval4_add, eval4_mul, eval4_neg, sub_eq_add_neg]

theorem eval_squareNorm (x : Coordinates) :
    eval4 (squareNorm x) = Complex.normSq (toComplex x) := by
  simp [Complex.normSq_apply, squareNorm, toComplex, eval4_add, eval4_mul]

end SnailCoordinates


namespace UnitDistanceCertificate

private def oriented (reverse : Bool) (z : ℂ) : ℂ :=
  if reverse then star z else z

theorem normSq_orientation (reverse : Bool) (z : ℂ) :
    Complex.normSq (oriented reverse z) = Complex.normSq z := by
  cases reverse <;> simp [oriented, Complex.normSq_apply]

theorem congruence_of_cross_products {V : Type*} [DecidableEq V] (p : V → ℂ)
    (S : Finset V) (σ : V → V) (i j : V) (reverse : Bool)
    (hne : oriented reverse (p j) - oriented reverse (p i) ≠ 0)
    (hnorm :
      Complex.normSq (p (σ j) - p (σ i)) =
      Complex.normSq (oriented reverse (p j) - oriented reverse (p i)))
    (hcross : ∀ k ∈ S,
      (p (σ j) - p (σ i)) * (oriented reverse (p k) - oriented reverse (p i)) =
      (p (σ k) - p (σ i)) * (oriented reverse (p j) - oriented reverse (p i))) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧
      (S.image (fun k => a * p k + b) = (S.image σ).image p ∨
        S.image (fun k => a * star (p k) + b) = (S.image σ).image p) := by
  classical
  let x := fun k => oriented reverse (p k)
  let y := p ∘ σ
  let u := x j - x i
  let v := y j - y i
  let a := v / u
  let b := y i - a * x i
  have hu : u ≠ 0 := hne
  have hnorm' : ‖v‖ = ‖u‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
    change Complex.normSq v = Complex.normSq u at hnorm
    simpa only [Complex.normSq_eq_norm_sq] using hnorm
  have ha : ‖a‖ = 1 := by
    rw [show a = v / u from rfl, norm_div, hnorm', div_self (norm_ne_zero_iff.2 hu)]
  have hmap (k : V) (hk : k ∈ S) : a * x k + b = y k := by
    have h := hcross k hk
    change v * (x k - x i) = (y k - y i) * u at h
    have hh : a * (x k - x i) = y k - y i := by
      calc
        _ = (v * (x k - x i)) / u := by unfold a; ring
        _ = _ := (div_eq_iff hu).2 h
    unfold b
    linear_combination hh
  have himage : S.image (fun k => a * x k + b) = (S.image σ).image p := by
    rw [Finset.image_image]
    exact Finset.image_congr hmap
  refine ⟨a, b, ha, ?_⟩
  cases reverse
  · exact Or.inl (by simpa [x, oriented] using himage)
  · exact Or.inr (by simpa [x, oriented] using himage)

theorem edge_of_normSq_one {x y : ℂ} (h : Complex.normSq (x - y) = 1) : dist x y = 1 := by
  rw [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1
  simpa only [Complex.normSq_eq_norm_sq, one_pow] using h

end UnitDistanceCertificate


namespace SnailCoordinates

private def scaleFactor : ℤ := 384

private def vertices : Fin 29 → Coordinates := ![
  (((((1600, 0), (0, -64)), ((-72, 0), (0, -8))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 728), (8, 0)), ((0, 64), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1648, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 1), (-3, 0)), ((0, 0), (0, 0)))), ((((0, 632), (56, 0)), ((0, 0), (0, 0))), (((9, 0), (0, -1)), ((0, 0), (0, 0))))),
  (((((1792, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 768), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1728, 0), (0, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 768), (192, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1504, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (32, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1824, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (96, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1760, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2144, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1952, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 928), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1888, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 544), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2080, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 736), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1888, 0), (0, -32)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 928), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2048, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (64, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2176, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 704), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1600, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1984, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2112, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 704), (192, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1920, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (192, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1664, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 704), (256, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1856, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 896), (256, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1984, 0), (0, -64)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 704), (320, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1952, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 480), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1760, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 672), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2144, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 672), (160, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1696, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 672), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2080, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 672), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1888, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 864), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((2272, 0), (0, -96)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 864), (224, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0))))),
  (((((1984, 0), (0, -128)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))), ((((0, 832), (128, 0)), ((0, 0), (0, 0))), (((0, 0), (0, 0)), ((0, 0), (0, 0)))))]

private def edges : List (Fin 29 × Fin 29) := [(0, 4), (1, 4), (2, 8), (3, 5), (3, 11), (4, 5), (5, 7), (5, 15), (6, 7), (6, 8), (6, 10), (6, 14), (6, 17), (6, 18), (6, 22), (7, 8), (7, 15), (7, 23), (8, 12), (8, 19), (9, 10), (10, 11), (10, 13), (10, 17), (10, 20), (10, 25), (11, 15), (11, 26), (13, 15), (13, 25), (14, 15), (14, 17), (15, 26), (15, 28), (16, 17), (16, 27), (18, 19), (18, 20), (18, 22), (20, 25), (21, 22), (21, 23), (22, 23), (22, 25), (23, 28), (24, 25), (24, 26), (25, 26), (25, 27), (26, 27), (26, 28)]

end SnailCoordinates


namespace SnailCoordinates

private def Encloses (a : ℚ × ℚ) (x : ℝ) : Prop :=
  (a.1 : ℝ) ≤ x ∧ x ≤ (a.2 : ℝ)

private def extendBounds {K : Type} (bounds : K → ℚ × ℚ) (r : ℚ × ℚ)
    (x : K × K) : ℚ × ℚ :=
  ((bounds x.1).1 + min (r.1 * (bounds x.2).1) (r.2 * (bounds x.2).1),
    (bounds x.1).2 + max (r.1 * (bounds x.2).2) (r.2 * (bounds x.2).2))

private theorem extendBounds_sound {K : Type} (bounds : K → ℚ × ℚ) (e : K → ℝ)
    (H : ∀ a, Encloses (bounds a) (e a)) {r : ℝ} {s : ℚ × ℚ}
    (hr₀ : 0 ≤ r) (hr : Encloses s r) (x : K × K) :
    Encloses (extendBounds bounds s x) (extendEval e r x) := by
  obtain ⟨hl, hu⟩ := hr
  obtain ⟨h₁l, h₁u⟩ := H x.1
  obtain ⟨h₂l, h₂u⟩ := H x.2
  unfold Encloses extendBounds extendEval
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_min, Rat.cast_max]
  refine ⟨add_le_add h₁l ?_, add_le_add h₁u ?_⟩
  · refine le_trans ?_ (mul_le_mul_of_nonneg_left h₂l hr₀)
    by_cases ha : 0 ≤ ((bounds x.2).1 : ℝ)
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl ha)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu (le_of_not_ge ha))
  · refine (mul_le_mul_of_nonneg_left h₂u hr₀).trans ?_
    by_cases ha : 0 ≤ ((bounds x.2).2 : ℝ)
    · exact (mul_le_mul_of_nonneg_right hu ha).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hl (le_of_not_ge ha)).trans (le_max_left _ _)

private theorem sqrt_between {a b v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : a^2 ≤ v) (h₂ : v ≤ b^2) : a ≤ Real.sqrt v ∧ Real.sqrt v ≤ b := by
  have hv : 0 ≤ v := (sq_nonneg a).trans h₁
  refine ⟨(sq_le_sq₀ ha (Real.sqrt_nonneg _)).1 ?_,
    (sq_le_sq₀ (Real.sqrt_nonneg _) hb).1 ?_⟩
  · simpa only [Real.sq_sqrt hv] using h₁
  · simpa only [Real.sq_sqrt hv] using h₂

private def root1Box : ℚ × ℚ := (17320/10000, 17321/10000)
private def root2Box : ℚ × ℚ := (33166/10000, 33167/10000)
private def root3Box : ℚ × ℚ := (22360/10000, 22361/10000)
private def root4Box : ℚ × ℚ := (416848/10000, 416852/10000)

private theorem root1Bound : Encloses root1Box radical1 := by
  norm_num [Encloses, root1Box, radical1]
  exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem root2Bound : Encloses root2Box radical2 := by
  norm_num [Encloses, root2Box, radical2]
  exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem root3Bound : Encloses root3Box radical3 := by
  norm_num [Encloses, root3Box, radical3]
  exact sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem root4Bound : Encloses root4Box radical4 := by
  have hmul : radical1 * radical2 = Real.sqrt 33 := by
    rw [radical1, radical2, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hx : (574456/100000 : ℝ) ≤ Real.sqrt 33 ∧ Real.sqrt 33 ≤ (574457/100000 : ℝ) :=
    sqrt_between (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  unfold Encloses root4Box radical4
  push_cast
  rw [mul_assoc, hmul]
  exact sqrt_between (by norm_num) (by norm_num)
    (by linarith only [hx.1]) (by linarith only [hx.2])

private def bounds0 (r : ℤ) : ℚ × ℚ := (r, r)

private theorem bounds0_sound (r : ℤ) : Encloses (bounds0 r) (eval0 r) := by
  simp [bounds0, Encloses, eval0]

private def bounds1 := extendBounds (K := K0) bounds0 root1Box

private theorem bounds1_sound (v : K1) : Encloses (bounds1 v) (eval1 v) :=
  extendBounds_sound _ _ bounds0_sound (by unfold radical1; positivity) root1Bound v

private def bounds2 := extendBounds (K := K1) bounds1 root2Box

private theorem bounds2_sound (v : K2) : Encloses (bounds2 v) (eval2 v) :=
  extendBounds_sound _ _ bounds1_sound (by unfold radical2; positivity) root2Bound v

private def bounds3 := extendBounds (K := K2) bounds2 root3Box

private theorem bounds3_sound (v : K3) : Encloses (bounds3 v) (eval3 v) :=
  extendBounds_sound _ _ bounds2_sound (by unfold radical3; positivity) root3Bound v

private def bounds4 := extendBounds (K := K3) bounds3 root4Box

private theorem bounds4_sound (v : K4) : Encloses (bounds4 v) (eval4 v) :=
  extendBounds_sound _ _ bounds3_sound (by unfold radical4; positivity) root4Bound v

private def edgeCheck (e : Fin 29 × Fin 29) : Bool :=
  decide (squareNorm (sub (vertices e.1) (vertices e.2)) = int4 (scaleFactor^2))

set_option maxHeartbeats 0 in
private theorem edgeAudit : edges.all edgeCheck = true := by
  decide +kernel

theorem edge_dist {i j : Fin 29} (h : (i,j) ∈ edges) :
    dist (toComplex (vertices i) / 384) (toComplex (vertices j) / 384) = 1 := by
  have hcheck := List.all_eq_true.1 edgeAudit _ h
  have hr := congrArg eval4 (of_decide_eq_true hcheck)
  rw [eval_squareNorm, toComplex_sub, eval4_int, Complex.normSq_eq_norm_sq] at hr
  have hs : ‖toComplex (vertices i) - toComplex (vertices j)‖^2 = (384 : ℝ)^2 := by
    norm_num [scaleFactor] at hr ⊢
    exact hr
  have he := (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 384)).1 hs
  rw [dist_eq_norm, ← sub_div, norm_div, he]
  norm_num

private structure Motion where
  reflect : Bool
  source : Fin 29 × Fin 29
  target : Fin 29 × Fin 29
  pairs : List (Fin 29 × Fin 29)

private def transformed (m : Motion) (i : Fin 29) : Coordinates :=
  if m.reflect then conj (vertices i) else vertices i

private def u (m : Motion) : Coordinates :=
  sub (transformed m m.source.2) (transformed m m.source.1)

private def v (m : Motion) : Coordinates :=
  sub (vertices m.target.2) (vertices m.target.1)

private def motionCheck (m : Motion) : Bool :=
  decide (0 < (bounds4 (squareNorm (u m))).1 ∧ squareNorm (u m) = squareNorm (v m)) &&
    m.pairs.all (fun e =>
      let lhs := mul (v m) (sub (transformed m e.1) (transformed m m.source.1))
      let rhs := mul (sub (vertices e.2) (vertices m.target.1)) (u m)
      decide (lhs.1 = rhs.1) && decide (lhs.2 = rhs.2))

end SnailCoordinates


namespace SnailCoordinates

private def ms0 : List Motion := [
  ⟨false, (2, 7), (20, 19), [(2, 20), (7, 19), (8, 18), (9, 27), (10, 26), (11, 24), (13, 11), (14, 9), (16, 17), (18, 23), (19, 22), (20, 28), (22, 7), (23, 8), (24, 13), (25, 15), (27, 14), (28, 2)]⟩,
  ⟨true, (2, 3), (24, 18), [(2, 24), (3, 18), (4, 21), (5, 22), (8, 26), (11, 19), (12, 28), (14, 16), (16, 14), (17, 17), (18, 3), (19, 11), (21, 4), (22, 5), (24, 2), (26, 8), (28, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg0 : PLift (ms0.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms1 : List Motion := [
  ⟨true, (2, 3), (23, 25), [(2, 23), (3, 25), (5, 13), (6, 16), (9, 9), (11, 26), (12, 12), (13, 5), (15, 15), (16, 6), (17, 17), (19, 19), (23, 2), (25, 3), (26, 11)]⟩,
  ⟨true, (2, 6), (12, 15), [(2, 12), (6, 15), (7, 5), (9, 16), (13, 2), (16, 6), (17, 14), (18, 26), (20, 24), (22, 11), (23, 3), (24, 19)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg1 : PLift (ms1.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms2 : List Motion := [
  ⟨true, (3, 5), (12, 8), [(3, 12), (5, 8), (6, 15), (7, 7), (8, 5), (10, 13), (12, 3), (13, 10), (14, 14), (15, 6), (16, 16), (18, 28), (22, 26), (25, 25), (26, 22), (28, 18)]⟩,
  ⟨true, (2, 3), (11, 8), [(2, 11), (3, 8), (5, 19), (6, 17), (8, 10), (11, 7), (12, 20), (16, 27), (17, 16), (19, 13), (24, 28), (26, 23)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg2 : PLift (ms2.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms3 : List Motion := [
  ⟨true, (2, 4), (14, 4), [(2, 14), (4, 4), (9, 28), (10, 26), (11, 11), (13, 24), (14, 2), (20, 27), (24, 13), (25, 25), (26, 10), (27, 20), (28, 9)]⟩,
  ⟨false, (2, 6), (12, 15), [(2, 12), (6, 15), (7, 13), (9, 6), (10, 7), (13, 23), (16, 16), (18, 11), (21, 24), (22, 26), (23, 25), (24, 19)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg3 : PLift (ms3.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms4 : List Motion := [
  ⟨true, (2, 5), (18, 24), [(2, 18), (5, 24), (7, 26), (9, 14), (10, 17), (11, 10), (15, 25), (17, 16), (18, 5), (19, 7), (23, 28), (26, 13)]⟩,
  ⟨true, (2, 5), (2, 6), [(2, 2), (5, 6), (6, 5), (7, 7), (9, 12), (12, 9), (13, 16), (16, 13), (21, 28), (23, 23), (28, 21)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg4 : PLift (ms4.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms5 : List Motion := [
  ⟨true, (2, 3), (8, 15), [(2, 8), (3, 15), (5, 11), (6, 17), (7, 10), (8, 6), (9, 27), (10, 16), (19, 22), (23, 20), (26, 24)]⟩,
  ⟨true, (2, 3), (2, 5), [(2, 2), (3, 5), (5, 3), (6, 6), (9, 16), (16, 9), (18, 22), (20, 21), (21, 20), (22, 18), (24, 24)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg5 : PLift (ms5.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms6 : List Motion := [
  ⟨true, (2, 9), (9, 2), [(2, 9), (9, 2), (11, 24), (13, 13), (14, 20), (15, 25), (20, 14), (24, 11), (25, 15), (26, 26), (27, 28), (28, 27)]⟩,
  ⟨true, (2, 3), (3, 2), [(2, 3), (3, 2), (6, 6), (7, 10), (9, 15), (10, 7), (15, 9), (16, 16), (22, 22), (23, 25), (25, 23)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg6 : PLift (ms6.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms7 : List Motion := [
  ⟨false, (6, 7), (27, 26), [(6, 27), (7, 26), (8, 25), (11, 23), (12, 20), (13, 19), (16, 17), (17, 16), (19, 13), (20, 12), (23, 11), (25, 8), (26, 7), (27, 6)]⟩,
  ⟨false, (2, 3), (2, 6), [(2, 2), (3, 6), (6, 5), (9, 13), (10, 15), (11, 14), (14, 4), (16, 12), (20, 28)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg7 : PLift (ms7.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms8 : List Motion := [
  ⟨false, (2, 5), (3, 2), [(2, 3), (5, 2), (6, 6), (7, 8), (9, 16), (10, 17), (16, 15), (17, 14), (18, 22), (23, 12)]⟩,
  ⟨false, (2, 7), (9, 16), [(2, 9), (7, 16), (10, 25), (11, 24), (12, 5), (13, 13), (16, 23), (17, 22), (27, 28)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg8 : PLift (ms8.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms9 : List Motion := [
  ⟨false, (2, 8), (4, 5), [(2, 4), (8, 5), (11, 2), (14, 14), (17, 6), (19, 3), (27, 9), (28, 24)]⟩,
  ⟨true, (2, 5), (12, 15), [(2, 12), (5, 15), (7, 13), (12, 6), (13, 16), (16, 23), (23, 25), (27, 21), (28, 24)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg9 : PLift (ms9.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms10 : List Motion := [
  ⟨true, (2, 3), (7, 16), [(2, 7), (3, 16), (6, 10), (8, 6), (10, 9), (14, 11), (15, 3), (18, 20), (19, 18)]⟩,
  ⟨false, (2, 3), (24, 22), [(2, 24), (3, 22), (4, 20), (5, 18), (9, 14), (14, 9), (18, 5), (20, 4), (22, 3), (24, 2)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg10 : PLift (ms10.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms11 : List Motion := [
  ⟨true, (2, 3), (7, 13), [(2, 7), (3, 13), (4, 11), (5, 10), (6, 16), (15, 9), (19, 21)]⟩,
  ⟨false, (2, 4), (24, 9), [(2, 24), (4, 9), (6, 22), (9, 28), (13, 14), (21, 12), (28, 4)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg11 : PLift (ms11.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms12 : List Motion := [
  ⟨true, (2, 4), (9, 20), [(2, 9), (4, 20), (13, 2), (14, 24), (27, 4), (28, 14)]⟩,
  ⟨false, (2, 3), (13, 7), [(2, 13), (3, 7), (4, 28), (5, 23), (6, 16), (9, 9), (14, 27), (24, 20)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg12 : PLift (ms12.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms13 : List Motion := [
  ⟨true, (2, 3), (16, 25), [(2, 16), (3, 25), (5, 10), (7, 9), (11, 24), (12, 3), (14, 19), (17, 18)]⟩,
  ⟨true, (2, 5), (23, 16), [(2, 23), (5, 16), (6, 25), (8, 22), (12, 6), (13, 9), (14, 26), (17, 24), (22, 20)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg13 : PLift (ms13.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms14 : List Motion := [
  ⟨true, (2, 5), (8, 17), [(2, 8), (5, 17), (6, 15), (8, 7), (13, 27), (15, 16), (17, 13), (22, 28)]⟩,
  ⟨true, (3, 5), (20, 25), [(3, 20), (5, 25), (7, 26), (10, 19), (15, 27), (16, 17), (21, 5), (22, 7), (23, 15), (25, 8)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg14 : PLift (ms14.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms15 : List Motion := [
  ⟨false, (3, 8), (5, 13), [(3, 5), (8, 13), (11, 7), (13, 21), (15, 23), (17, 16), (19, 10), (22, 24), (24, 18)]⟩,
  ⟨true, (2, 3), (13, 16), [(2, 13), (3, 16), (6, 7), (7, 5), (8, 15), (10, 6), (11, 17), (16, 2), (17, 8), (19, 11)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg15 : PLift (ms15.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms16 : List Motion := [
  ⟨true, (2, 5), (25, 16), [(2, 25), (5, 16), (8, 26), (10, 18), (12, 15), (13, 6), (15, 17), (17, 19), (23, 3)]⟩,
  ⟨true, (2, 6), (24, 22), [(2, 24), (6, 22), (8, 25), (11, 16), (14, 21), (16, 28), (17, 23), (19, 13), (20, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg16 : PLift (ms16.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms17 : List Motion := [
  ⟨true, (2, 7), (9, 6), [(2, 9), (7, 6), (8, 10), (10, 3), (12, 13), (13, 5), (15, 7), (16, 2)]⟩,
  ⟨false, (2, 8), (14, 17), [(2, 14), (8, 17), (11, 11), (13, 24), (15, 26), (16, 18), (17, 19), (27, 20)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg17 : PLift (ms17.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms18 : List Motion := [
  ⟨false, (2, 8), (13, 10), [(2, 13), (8, 10), (12, 9), (16, 2), (19, 11), (21, 4), (24, 14)]⟩,
  ⟨true, (2, 3), (19, 11), [(2, 19), (3, 11), (4, 24), (5, 26), (6, 17), (14, 16), (15, 27), (24, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg18 : PLift (ms18.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms19 : List Motion := [
  ⟨true, (2, 11), (4, 14), [(2, 4), (11, 14), (14, 2), (26, 15), (27, 28), (28, 13)]⟩,
  ⟨false, (2, 5), (12, 15), [(2, 12), (5, 15), (7, 5), (12, 16), (13, 6), (15, 7), (16, 2), (23, 3)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg19 : PLift (ms19.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms20 : List Motion := [
  ⟨false, (5, 13), (20, 19), [(5, 20), (13, 19), (15, 18), (16, 26), (17, 24), (22, 16), (23, 17), (24, 23), (26, 22), (28, 6)]⟩,
  ⟨false, (2, 9), (9, 23), [(2, 9), (9, 23), (10, 7), (13, 5), (15, 3), (24, 26), (25, 15), (26, 11)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg20 : PLift (ms20.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms21 : List Motion := [
  ⟨true, (2, 3), (22, 24), [(2, 22), (3, 24), (4, 13), (14, 17), (15, 14), (22, 3)]⟩,
  ⟨true, (3, 9), (3, 17), [(3, 3), (9, 17), (10, 10), (13, 20), (17, 9), (20, 13), (22, 24), (24, 22), (25, 25)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg21 : PLift (ms21.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms22 : List Motion := [
  ⟨true, (2, 5), (25, 23), [(2, 25), (5, 23), (6, 16), (8, 27), (9, 6), (10, 17), (16, 15), (23, 12)]⟩,
  ⟨true, (2, 5), (5, 6), [(2, 5), (5, 6), (9, 23), (13, 9), (22, 24)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg22 : PLift (ms22.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms23 : List Motion := [
  ⟨true, (2, 5), (11, 17), [(2, 11), (5, 17), (6, 8), (12, 27), (14, 7), (22, 12)]⟩,
  ⟨false, (3, 6), (2, 5), [(3, 2), (6, 5), (10, 7), (11, 8), (15, 12), (16, 13), (17, 15), (19, 17), (24, 22), (25, 23)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg23 : PLift (ms23.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms24 : List Motion := [
  ⟨true, (5, 6), (23, 25), [(5, 23), (6, 25), (7, 22), (10, 24), (14, 27), (17, 26), (18, 20), (22, 10), (23, 6), (26, 19), (28, 8)]⟩,
  ⟨true, (3, 6), (3, 6), [(3, 3), (6, 6), (7, 17), (8, 10), (10, 8), (12, 25), (15, 16), (16, 15), (17, 7), (25, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg24 : PLift (ms24.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms25 : List Motion := [
  ⟨false, (5, 8), (9, 18), [(5, 9), (8, 18), (12, 6), (13, 16), (16, 25), (17, 24), (22, 21), (23, 23)]⟩,
  ⟨false, (2, 7), (9, 6), [(2, 9), (7, 6), (9, 13), (13, 2), (16, 5), (27, 4)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg25 : PLift (ms25.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms26 : List Motion := [
  ⟨false, (3, 5), (6, 22), [(3, 6), (5, 22), (8, 16), (10, 9), (11, 10), (14, 26), (15, 25), (26, 20)]⟩,
  ⟨false, (3, 10), (28, 22), [(3, 28), (10, 22), (11, 23), (16, 24), (17, 25), (18, 17), (19, 16), (20, 6), (24, 19), (25, 18)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg26 : PLift (ms26.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms27 : List Motion := [
  ⟨false, (2, 5), (25, 16), [(2, 25), (5, 16), (6, 23), (8, 22), (10, 28), (12, 6), (13, 15), (23, 12)]⟩,
  ⟨false, (3, 7), (9, 7), [(3, 9), (7, 7), (8, 6), (10, 16), (15, 5), (16, 13), (18, 21), (19, 22)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg27 : PLift (ms27.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms28 : List Motion := [
  ⟨true, (2, 5), (3, 6), [(2, 3), (5, 6), (6, 2), (7, 8), (12, 16), (13, 15), (15, 7), (23, 12)]⟩,
  ⟨true, (2, 7), (9, 16), [(2, 9), (7, 16), (9, 5), (10, 7), (13, 23), (16, 13)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg28 : PLift (ms28.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms29 : List Motion := [
  ⟨false, (2, 3), (15, 8), [(2, 15), (3, 8), (6, 17), (7, 16), (10, 10), (13, 25), (15, 27), (25, 20)]⟩,
  ⟨false, (3, 5), (25, 20), [(3, 25), (5, 20), (7, 18), (9, 17), (17, 9), (18, 7), (20, 5), (25, 3)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg29 : PLift (ms29.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms30 : List Motion := [
  ⟨false, (2, 3), (3, 6), [(2, 3), (3, 6), (6, 2), (19, 4)]⟩,
  ⟨true, (2, 3), (3, 6), [(2, 3), (3, 6), (10, 9), (18, 24)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg30 : PLift (ms30.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms31 : List Motion := [
  ⟨true, (2, 11), (4, 2), [(2, 4), (11, 2), (20, 13), (27, 9)]⟩,
  ⟨true, (2, 12), (5, 9), [(2, 5), (12, 9), (16, 23), (19, 26)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg31 : PLift (ms31.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms32 : List Motion := [
  ⟨false, (2, 5), (6, 5), [(2, 6), (5, 5), (7, 15), (8, 14), (9, 23), (13, 12)]⟩,
  ⟨true, (3, 6), (18, 24), [(3, 18), (6, 24), (10, 26), (17, 25), (19, 16), (20, 15), (25, 28), (26, 23)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg32 : PLift (ms32.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms33 : List Motion := [
  ⟨false, (6, 8), (10, 11), [(6, 10), (8, 11), (11, 19), (14, 6), (15, 8), (17, 17), (18, 25), (19, 26), (22, 13), (24, 23), (28, 12)]⟩,
  ⟨false, (6, 7), (25, 24), [(6, 25), (7, 24), (10, 22), (11, 21), (13, 18), (18, 13), (21, 11), (22, 10), (24, 7), (25, 6)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg33 : PLift (ms33.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms34 : List Motion := [
  ⟨false, (2, 3), (17, 8), [(2, 17), (3, 8), (5, 19), (6, 11), (8, 10), (10, 3), (12, 20)]⟩,
  ⟨false, (2, 8), (11, 26), [(2, 11), (8, 26), (12, 27), (16, 20), (19, 24), (24, 9)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg34 : PLift (ms34.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms35 : List Motion := [
  ⟨true, (2, 4), (13, 17), [(2, 13), (4, 17), (5, 16), (6, 23), (12, 9), (14, 22), (17, 21)]⟩,
  ⟨false, (5, 6), (2, 3), [(5, 2), (6, 3), (13, 7), (15, 8), (16, 10), (17, 11), (23, 16), (24, 18), (26, 19)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg35 : PLift (ms35.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms36 : List Motion := [
  ⟨false, (9, 13), (20, 11), [(9, 20), (13, 11), (16, 19), (21, 16), (23, 17), (24, 24), (25, 26), (28, 14)]⟩,
  ⟨false, (2, 3), (16, 13), [(2, 16), (3, 13), (5, 10), (6, 7), (7, 6), (10, 5), (13, 3), (16, 2)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg36 : PLift (ms36.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms37 : List Motion := [
  ⟨true, (3, 6), (8, 11), [(3, 8), (6, 11), (8, 3), (10, 10), (11, 6), (18, 26), (20, 25), (25, 20), (26, 18)]⟩,
  ⟨false, (3, 7), (27, 19), [(3, 27), (7, 19), (10, 17), (11, 16), (16, 11), (17, 10), (19, 7), (27, 3)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg37 : PLift (ms37.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms38 : List Motion := [
  ⟨true, (5, 6), (11, 8), [(5, 11), (6, 8), (14, 6), (15, 10), (17, 7), (18, 12), (23, 27), (26, 13), (28, 25)]⟩,
  ⟨false, (2, 9), (14, 18), [(2, 14), (9, 18), (10, 22), (24, 10), (25, 25), (26, 13)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg38 : PLift (ms38.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms39 : List Motion := [
  ⟨false, (3, 10), (12, 13), [(3, 12), (10, 13), (16, 23), (18, 17), (20, 10), (24, 26), (25, 25), (26, 27)]⟩,
  ⟨true, (2, 3), (7, 10), [(2, 7), (3, 10), (7, 2), (8, 8), (10, 3), (11, 11)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg39 : PLift (ms39.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms40 : List Motion := [
  ⟨false, (2, 3), (11, 17), [(2, 11), (3, 17), (6, 8), (11, 14), (14, 2), (18, 12)]⟩,
  ⟨false, (2, 3), (18, 24), [(2, 18), (3, 24), (16, 14), (22, 5)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg40 : PLift (ms40.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms41 : List Motion := [
  ⟨true, (2, 8), (18, 19), [(2, 18), (8, 19), (13, 14), (14, 10), (15, 17), (17, 11), (22, 2)]⟩,
  ⟨false, (2, 4), (26, 10), [(2, 26), (4, 10), (5, 17), (15, 14), (22, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg41 : PLift (ms41.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms42 : List Motion := [
  ⟨false, (2, 5), (26, 19), [(2, 26), (5, 19), (6, 17), (10, 14), (14, 10), (17, 6), (19, 5), (26, 2)]⟩,
  ⟨true, (3, 6), (24, 22), [(3, 24), (6, 22), (11, 26), (14, 23), (15, 28), (18, 6), (19, 17), (24, 5), (26, 15)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg42 : PLift (ms42.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms43 : List Motion := [
  ⟨false, (5, 8), (27, 23), [(5, 27), (8, 23), (13, 17), (15, 16), (16, 15), (17, 13), (23, 8), (27, 5)]⟩,
  ⟨false, (9, 13), (28, 24), [(9, 28), (13, 24), (16, 22), (17, 21), (21, 17), (22, 16), (24, 13), (28, 9)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg43 : PLift (ms43.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms44 : List Motion := [
  ⟨true, (12, 13), (12, 13), [(12, 12), (13, 13), (16, 23), (17, 28), (22, 27), (23, 16), (25, 25), (27, 22), (28, 17)]⟩,
  ⟨true, (2, 10), (2, 15), [(2, 2), (10, 15), (11, 11), (13, 13), (15, 10), (27, 27)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg44 : PLift (ms44.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms45 : List Motion := [
  ⟨true, (2, 8), (3, 5), [(2, 3), (8, 5), (12, 15), (19, 4)]⟩,
  ⟨false, (2, 3), (10, 16), [(2, 10), (3, 16), (6, 7), (7, 8), (8, 6), (10, 15), (15, 2), (17, 5)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg45 : PLift (ms45.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms46 : List Motion := [
  ⟨false, (2, 12), (12, 23), [(2, 12), (12, 23), (16, 6), (27, 18)]⟩,
  ⟨false, (2, 3), (19, 26), [(2, 19), (3, 26), (5, 11), (6, 17), (14, 6), (17, 14), (24, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg46 : PLift (ms46.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms47 : List Motion := [
  ⟨true, (3, 5), (28, 15), [(3, 28), (5, 15), (9, 25), (10, 22), (13, 6), (15, 14), (22, 19), (25, 18)]⟩,
  ⟨true, (4, 5), (8, 7), [(4, 8), (5, 7), (6, 13), (22, 25), (26, 21)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg47 : PLift (ms47.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms48 : List Motion := [
  ⟨true, (6, 7), (27, 16), [(6, 27), (7, 16), (10, 25), (12, 8), (13, 10), (15, 17), (17, 26), (25, 20), (27, 18)]⟩,
  ⟨true, (16, 19), (2, 4), [(16, 2), (19, 4), (21, 11), (23, 3), (24, 14), (25, 6)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg48 : PLift (ms48.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms49 : List Motion := [
  ⟨false, (2, 3), (2, 5), [(2, 2), (3, 5), (11, 4)]⟩,
  ⟨false, (2, 24), (2, 26), [(2, 2), (24, 26)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg49 : PLift (ms49.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms50 : List Motion := [
  ⟨false, (7, 9), (23, 15), [(7, 23), (9, 15), (10, 13), (13, 25), (16, 16), (21, 19), (25, 10)]⟩,
  ⟨false, (2, 25), (3, 23), [(2, 3), (25, 23), (27, 28)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg50 : PLift (ms50.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms51 : List Motion := [
  ⟨true, (2, 13), (6, 12), [(2, 6), (13, 12), (14, 19)]⟩,
  ⟨false, (2, 3), (7, 13), [(2, 7), (3, 13), (8, 5), (10, 12)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg51 : PLift (ms51.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms52 : List Motion := [
  ⟨false, (2, 3), (7, 16), [(2, 7), (3, 16), (6, 13), (8, 15), (15, 12), (19, 28)]⟩,
  ⟨true, (5, 9), (12, 23), [(5, 12), (9, 23), (13, 5), (21, 10), (22, 17), (23, 6), (24, 26)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg52 : PLift (ms52.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms53 : List Motion := [
  ⟨true, (2, 10), (10, 2), [(2, 10), (10, 2), (14, 26), (15, 15), (26, 14)]⟩,
  ⟨true, (2, 4), (13, 28), [(2, 13), (4, 28), (9, 9), (13, 2), (28, 4)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg53 : PLift (ms53.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms54 : List Motion := [
  ⟨false, (2, 11), (13, 17), [(2, 13), (11, 17), (14, 22), (15, 6), (26, 14)]⟩,
  ⟨false, (2, 10), (17, 18), [(2, 17), (10, 18), (11, 22), (13, 20), (14, 13), (15, 25)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg54 : PLift (ms54.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms55 : List Motion := [
  ⟨false, (2, 8), (18, 6), [(2, 18), (8, 6), (19, 7), (27, 12)]⟩,
  ⟨true, (2, 8), (28, 15), [(2, 28), (8, 15), (19, 7), (27, 3)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg55 : PLift (ms55.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms56 : List Motion := [
  ⟨true, (3, 6), (11, 19), [(3, 11), (6, 19), (11, 10), (14, 18), (15, 20), (19, 16), (26, 25)]⟩,
  ⟨false, (4, 7), (1, 25), [(4, 1), (7, 25)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg56 : PLift (ms56.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms57 : List Motion := [
  ⟨true, (4, 9), (12, 21), [(4, 12), (9, 21), (12, 4), (21, 9), (24, 24)]⟩,
  ⟨false, (5, 6), (25, 23), [(5, 25), (6, 23), (7, 22), (8, 21), (21, 8), (22, 7), (23, 6), (25, 5)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg57 : PLift (ms57.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms58 : List Motion := [
  ⟨false, (5, 12), (27, 17), [(5, 27), (12, 17), (14, 23), (17, 28), (28, 12)]⟩,
  ⟨false, (6, 7), (23, 21), [(6, 23), (7, 21), (18, 7), (21, 18), (24, 10), (25, 9)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg58 : PLift (ms58.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms59 : List Motion := [
  ⟨false, (7, 14), (0, 12), [(7, 0), (14, 12)]⟩,
  ⟨true, (7, 15), (21, 23), [(7, 21), (15, 23), (17, 25), (25, 9), (28, 7)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg59 : PLift (ms59.all motionCheck = true) := ⟨by decide +kernel⟩

private def ms60 : List Motion := [
  ⟨true, (8, 12), (15, 11), [(8, 15), (12, 11), (15, 17), (16, 27), (19, 28), (27, 25)]⟩,
  ⟨false, (10, 13), (15, 26), [(10, 15), (13, 26), (15, 27), (16, 17), (23, 19), (25, 11), (27, 10)]⟩]

set_option maxHeartbeats 0 in
set_option maxRecDepth 8192 in
private def mg60 : PLift (ms60.all motionCheck = true) := ⟨by decide +kernel⟩

private theorem allConsChecked {m : List Motion} {ms : List (List Motion)}
    (hm : m.all motionCheck = true) (hms : ms.all (·.all motionCheck) = true) :
    (m :: ms).all (·.all motionCheck) = true := by
  rw [List.all_cons, hm, hms]
  rfl

private theorem mp0 : ms0.all motionCheck = true :=
  mg0.down

private theorem mp1 : ms1.all motionCheck = true :=
  mg1.down

private theorem mp2 : ms2.all motionCheck = true :=
  mg2.down

private theorem mp3 : ms3.all motionCheck = true :=
  mg3.down

private theorem mp4 : ms4.all motionCheck = true :=
  mg4.down

private theorem mp5 : ms5.all motionCheck = true :=
  mg5.down

private theorem mp6 : ms6.all motionCheck = true :=
  mg6.down

private theorem mp7 : ms7.all motionCheck = true :=
  mg7.down

private theorem mp8 : ms8.all motionCheck = true :=
  mg8.down

private theorem mp9 : ms9.all motionCheck = true :=
  mg9.down

private theorem mp10 : ms10.all motionCheck = true :=
  mg10.down

private theorem mp11 : ms11.all motionCheck = true :=
  mg11.down

private theorem mp12 : ms12.all motionCheck = true :=
  mg12.down

private theorem mp13 : ms13.all motionCheck = true :=
  mg13.down

private theorem mp14 : ms14.all motionCheck = true :=
  mg14.down

private theorem mp15 : ms15.all motionCheck = true :=
  mg15.down

private theorem mp16 : ms16.all motionCheck = true :=
  mg16.down

private theorem mp17 : ms17.all motionCheck = true :=
  mg17.down

private theorem mp18 : ms18.all motionCheck = true :=
  mg18.down

private theorem mp19 : ms19.all motionCheck = true :=
  mg19.down

private theorem mp20 : ms20.all motionCheck = true :=
  mg20.down

private theorem mp21 : ms21.all motionCheck = true :=
  mg21.down

private theorem mp22 : ms22.all motionCheck = true :=
  mg22.down

private theorem mp23 : ms23.all motionCheck = true :=
  mg23.down

private theorem mp24 : ms24.all motionCheck = true :=
  mg24.down

private theorem mp25 : ms25.all motionCheck = true :=
  mg25.down

private theorem mp26 : ms26.all motionCheck = true :=
  mg26.down

private theorem mp27 : ms27.all motionCheck = true :=
  mg27.down

private theorem mp28 : ms28.all motionCheck = true :=
  mg28.down

private theorem mp29 : ms29.all motionCheck = true :=
  mg29.down

private theorem mp30 : ms30.all motionCheck = true :=
  mg30.down

private theorem mp31 : ms31.all motionCheck = true :=
  mg31.down

private theorem mp32 : ms32.all motionCheck = true :=
  mg32.down

private theorem mp33 : ms33.all motionCheck = true :=
  mg33.down

private theorem mp34 : ms34.all motionCheck = true :=
  mg34.down

private theorem mp35 : ms35.all motionCheck = true :=
  mg35.down

private theorem mp36 : ms36.all motionCheck = true :=
  mg36.down

private theorem mp37 : ms37.all motionCheck = true :=
  mg37.down

private theorem mp38 : ms38.all motionCheck = true :=
  mg38.down

private theorem mp39 : ms39.all motionCheck = true :=
  mg39.down

private theorem mp40 : ms40.all motionCheck = true :=
  mg40.down

private theorem mp41 : ms41.all motionCheck = true :=
  mg41.down

private theorem mp42 : ms42.all motionCheck = true :=
  mg42.down

private theorem mp43 : ms43.all motionCheck = true :=
  mg43.down

private theorem mp44 : ms44.all motionCheck = true :=
  mg44.down

private theorem mp45 : ms45.all motionCheck = true :=
  mg45.down

private theorem mp46 : ms46.all motionCheck = true :=
  mg46.down

private theorem mp47 : ms47.all motionCheck = true :=
  mg47.down

private theorem mp48 : ms48.all motionCheck = true :=
  mg48.down

private theorem mp49 : ms49.all motionCheck = true :=
  mg49.down

private theorem mp50 : ms50.all motionCheck = true :=
  mg50.down

private theorem mp51 : ms51.all motionCheck = true :=
  mg51.down

private theorem mp52 : ms52.all motionCheck = true :=
  mg52.down

private theorem mp53 : ms53.all motionCheck = true :=
  mg53.down

private theorem mp54 : ms54.all motionCheck = true :=
  mg54.down

private theorem mp55 : ms55.all motionCheck = true :=
  mg55.down

private theorem mp56 : ms56.all motionCheck = true :=
  mg56.down

private theorem mp57 : ms57.all motionCheck = true :=
  mg57.down

private theorem mp58 : ms58.all motionCheck = true :=
  mg58.down

private theorem mp59 : ms59.all motionCheck = true :=
  mg59.down

private theorem mp60 : ms60.all motionCheck = true :=
  mg60.down

private def mb60 : List (List Motion) := ms60 :: []

private theorem mj60 : mb60.all (·.all motionCheck) = true :=
  allConsChecked mp60 rfl

private def mb59 : List (List Motion) := ms59 :: mb60

private theorem mj59 : mb59.all (·.all motionCheck) = true :=
  allConsChecked mp59 mj60

private def mb58 : List (List Motion) := ms58 :: mb59

private theorem mj58 : mb58.all (·.all motionCheck) = true :=
  allConsChecked mp58 mj59

private def mb57 : List (List Motion) := ms57 :: mb58

private theorem mj57 : mb57.all (·.all motionCheck) = true :=
  allConsChecked mp57 mj58

private def mb56 : List (List Motion) := ms56 :: mb57

private theorem mj56 : mb56.all (·.all motionCheck) = true :=
  allConsChecked mp56 mj57

private def mb55 : List (List Motion) := ms55 :: mb56

private theorem mj55 : mb55.all (·.all motionCheck) = true :=
  allConsChecked mp55 mj56

private def mb54 : List (List Motion) := ms54 :: mb55

private theorem mj54 : mb54.all (·.all motionCheck) = true :=
  allConsChecked mp54 mj55

private def mb53 : List (List Motion) := ms53 :: mb54

private theorem mj53 : mb53.all (·.all motionCheck) = true :=
  allConsChecked mp53 mj54

private def mb52 : List (List Motion) := ms52 :: mb53

private theorem mj52 : mb52.all (·.all motionCheck) = true :=
  allConsChecked mp52 mj53

private def mb51 : List (List Motion) := ms51 :: mb52

private theorem mj51 : mb51.all (·.all motionCheck) = true :=
  allConsChecked mp51 mj52

private def mb50 : List (List Motion) := ms50 :: mb51

private theorem mj50 : mb50.all (·.all motionCheck) = true :=
  allConsChecked mp50 mj51

private def mb49 : List (List Motion) := ms49 :: mb50

private theorem mj49 : mb49.all (·.all motionCheck) = true :=
  allConsChecked mp49 mj50

private def mb48 : List (List Motion) := ms48 :: mb49

private theorem mj48 : mb48.all (·.all motionCheck) = true :=
  allConsChecked mp48 mj49

private def mb47 : List (List Motion) := ms47 :: mb48

private theorem mj47 : mb47.all (·.all motionCheck) = true :=
  allConsChecked mp47 mj48

private def mb46 : List (List Motion) := ms46 :: mb47

private theorem mj46 : mb46.all (·.all motionCheck) = true :=
  allConsChecked mp46 mj47

private def mb45 : List (List Motion) := ms45 :: mb46

private theorem mj45 : mb45.all (·.all motionCheck) = true :=
  allConsChecked mp45 mj46

private def mb44 : List (List Motion) := ms44 :: mb45

private theorem mj44 : mb44.all (·.all motionCheck) = true :=
  allConsChecked mp44 mj45

private def mb43 : List (List Motion) := ms43 :: mb44

private theorem mj43 : mb43.all (·.all motionCheck) = true :=
  allConsChecked mp43 mj44

private def mb42 : List (List Motion) := ms42 :: mb43

private theorem mj42 : mb42.all (·.all motionCheck) = true :=
  allConsChecked mp42 mj43

private def mb41 : List (List Motion) := ms41 :: mb42

private theorem mj41 : mb41.all (·.all motionCheck) = true :=
  allConsChecked mp41 mj42

private def mb40 : List (List Motion) := ms40 :: mb41

private theorem mj40 : mb40.all (·.all motionCheck) = true :=
  allConsChecked mp40 mj41

private def mb39 : List (List Motion) := ms39 :: mb40

private theorem mj39 : mb39.all (·.all motionCheck) = true :=
  allConsChecked mp39 mj40

private def mb38 : List (List Motion) := ms38 :: mb39

private theorem mj38 : mb38.all (·.all motionCheck) = true :=
  allConsChecked mp38 mj39

private def mb37 : List (List Motion) := ms37 :: mb38

private theorem mj37 : mb37.all (·.all motionCheck) = true :=
  allConsChecked mp37 mj38

private def mb36 : List (List Motion) := ms36 :: mb37

private theorem mj36 : mb36.all (·.all motionCheck) = true :=
  allConsChecked mp36 mj37

private def mb35 : List (List Motion) := ms35 :: mb36

private theorem mj35 : mb35.all (·.all motionCheck) = true :=
  allConsChecked mp35 mj36

private def mb34 : List (List Motion) := ms34 :: mb35

private theorem mj34 : mb34.all (·.all motionCheck) = true :=
  allConsChecked mp34 mj35

private def mb33 : List (List Motion) := ms33 :: mb34

private theorem mj33 : mb33.all (·.all motionCheck) = true :=
  allConsChecked mp33 mj34

private def mb32 : List (List Motion) := ms32 :: mb33

private theorem mj32 : mb32.all (·.all motionCheck) = true :=
  allConsChecked mp32 mj33

private def mb31 : List (List Motion) := ms31 :: mb32

private theorem mj31 : mb31.all (·.all motionCheck) = true :=
  allConsChecked mp31 mj32

private def mb30 : List (List Motion) := ms30 :: mb31

private theorem mj30 : mb30.all (·.all motionCheck) = true :=
  allConsChecked mp30 mj31

private def mb29 : List (List Motion) := ms29 :: mb30

private theorem mj29 : mb29.all (·.all motionCheck) = true :=
  allConsChecked mp29 mj30

private def mb28 : List (List Motion) := ms28 :: mb29

private theorem mj28 : mb28.all (·.all motionCheck) = true :=
  allConsChecked mp28 mj29

private def mb27 : List (List Motion) := ms27 :: mb28

private theorem mj27 : mb27.all (·.all motionCheck) = true :=
  allConsChecked mp27 mj28

private def mb26 : List (List Motion) := ms26 :: mb27

private theorem mj26 : mb26.all (·.all motionCheck) = true :=
  allConsChecked mp26 mj27

private def mb25 : List (List Motion) := ms25 :: mb26

private theorem mj25 : mb25.all (·.all motionCheck) = true :=
  allConsChecked mp25 mj26

private def mb24 : List (List Motion) := ms24 :: mb25

private theorem mj24 : mb24.all (·.all motionCheck) = true :=
  allConsChecked mp24 mj25

private def mb23 : List (List Motion) := ms23 :: mb24

private theorem mj23 : mb23.all (·.all motionCheck) = true :=
  allConsChecked mp23 mj24

private def mb22 : List (List Motion) := ms22 :: mb23

private theorem mj22 : mb22.all (·.all motionCheck) = true :=
  allConsChecked mp22 mj23

private def mb21 : List (List Motion) := ms21 :: mb22

private theorem mj21 : mb21.all (·.all motionCheck) = true :=
  allConsChecked mp21 mj22

private def mb20 : List (List Motion) := ms20 :: mb21

private theorem mj20 : mb20.all (·.all motionCheck) = true :=
  allConsChecked mp20 mj21

private def mb19 : List (List Motion) := ms19 :: mb20

private theorem mj19 : mb19.all (·.all motionCheck) = true :=
  allConsChecked mp19 mj20

private def mb18 : List (List Motion) := ms18 :: mb19

private theorem mj18 : mb18.all (·.all motionCheck) = true :=
  allConsChecked mp18 mj19

private def mb17 : List (List Motion) := ms17 :: mb18

private theorem mj17 : mb17.all (·.all motionCheck) = true :=
  allConsChecked mp17 mj18

private def mb16 : List (List Motion) := ms16 :: mb17

private theorem mj16 : mb16.all (·.all motionCheck) = true :=
  allConsChecked mp16 mj17

private def mb15 : List (List Motion) := ms15 :: mb16

private theorem mj15 : mb15.all (·.all motionCheck) = true :=
  allConsChecked mp15 mj16

private def mb14 : List (List Motion) := ms14 :: mb15

private theorem mj14 : mb14.all (·.all motionCheck) = true :=
  allConsChecked mp14 mj15

private def mb13 : List (List Motion) := ms13 :: mb14

private theorem mj13 : mb13.all (·.all motionCheck) = true :=
  allConsChecked mp13 mj14

private def mb12 : List (List Motion) := ms12 :: mb13

private theorem mj12 : mb12.all (·.all motionCheck) = true :=
  allConsChecked mp12 mj13

private def mb11 : List (List Motion) := ms11 :: mb12

private theorem mj11 : mb11.all (·.all motionCheck) = true :=
  allConsChecked mp11 mj12

private def mb10 : List (List Motion) := ms10 :: mb11

private theorem mj10 : mb10.all (·.all motionCheck) = true :=
  allConsChecked mp10 mj11

private def mb9 : List (List Motion) := ms9 :: mb10

private theorem mj9 : mb9.all (·.all motionCheck) = true :=
  allConsChecked mp9 mj10

private def mb8 : List (List Motion) := ms8 :: mb9

private theorem mj8 : mb8.all (·.all motionCheck) = true :=
  allConsChecked mp8 mj9

private def mb7 : List (List Motion) := ms7 :: mb8

private theorem mj7 : mb7.all (·.all motionCheck) = true :=
  allConsChecked mp7 mj8

private def mb6 : List (List Motion) := ms6 :: mb7

private theorem mj6 : mb6.all (·.all motionCheck) = true :=
  allConsChecked mp6 mj7

private def mb5 : List (List Motion) := ms5 :: mb6

private theorem mj5 : mb5.all (·.all motionCheck) = true :=
  allConsChecked mp5 mj6

private def mb4 : List (List Motion) := ms4 :: mb5

private theorem mj4 : mb4.all (·.all motionCheck) = true :=
  allConsChecked mp4 mj5

private def mb3 : List (List Motion) := ms3 :: mb4

private theorem mj3 : mb3.all (·.all motionCheck) = true :=
  allConsChecked mp3 mj4

private def mb2 : List (List Motion) := ms2 :: mb3

private theorem mj2 : mb2.all (·.all motionCheck) = true :=
  allConsChecked mp2 mj3

private def mb1 : List (List Motion) := ms1 :: mb2

private theorem mj1 : mb1.all (·.all motionCheck) = true :=
  allConsChecked mp1 mj2

private def mb0 : List (List Motion) := ms0 :: mb1

private theorem mj0 : mb0.all (·.all motionCheck) = true :=
  allConsChecked mp0 mj1

private def chunkedMotions : List Motion := mb0.flatten

private theorem chunkedAudit : chunkedMotions.all motionCheck = true := by
  rw [chunkedMotions, List.all_flatten]
  exact mj0

end SnailCoordinates

namespace SnailCoordinates

private theorem transformed_eval (m : Motion) (i : Fin 29) :
    toComplex (transformed m i) =
      UnitDistanceCertificate.oriented m.reflect (toComplex (vertices i)) := by
  cases h : m.reflect <;> simp [h, transformed, UnitDistanceCertificate.oriented, toComplex_conj]

private theorem motionCheck_sound (m : Motion) (hm : motionCheck m = true) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ e ∈ m.pairs,
      a * UnitDistanceCertificate.oriented m.reflect (toComplex (vertices e.1)) + b =
        toComplex (vertices e.2) := by
  let x (i : Fin 29) := toComplex (transformed m i)
  let y (i : Fin 29) := toComplex (vertices i)
  let c := toComplex (u m)
  let d := toComplex (v m)
  let a := d / c
  let b := y m.target.1 - a * x m.source.1
  simp only [motionCheck, Bool.and_eq_true] at hm
  have han : 0 < (bounds4 (squareNorm (u m))).1 ∧ squareNorm (u m) = squareNorm (v m) :=
    of_decide_eq_true hm.1
  have hcp : 0 < Complex.normSq c := by
    have hlo := (bounds4_sound (squareNorm (u m))).1
    rw [eval_squareNorm] at hlo
    exact (Rat.cast_pos.2 han.1).trans_le hlo
  have hcn : c ≠ 0 := Complex.normSq_pos.1 hcp
  have hnd : ‖d‖ = ‖c‖ := by
    have h := congrArg eval4 han.2.symm
    rw [eval_squareNorm, eval_squareNorm, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h
  have ha : ‖a‖ = 1 := by
    dsimp [a]
    rw [norm_div, hnd, div_self (norm_ne_zero_iff.2 hcn)]
  refine ⟨a,b,ha,?_⟩
  intro e he
  rw [← transformed_eval]
  change a * x e.1 + b = y e.2
  have hraw := List.all_eq_true.1 hm.2 e he
  simp only [Bool.and_eq_true] at hraw
  have heq :
      mul (v m) (sub (transformed m e.1) (transformed m m.source.1)) =
      mul (sub (vertices e.2) (vertices m.target.1)) (u m) :=
    Prod.ext (of_decide_eq_true hraw.1) (of_decide_eq_true hraw.2)
  have heq' := congrArg toComplex heq
  rw [toComplex_mul, toComplex_mul, toComplex_sub, toComplex_sub] at heq'
  change d * (x e.1 - x m.source.1) = (y e.2 - y m.target.1) * c at heq'
  have hs : a * (x e.1 - x m.source.1) = y e.2 - y m.target.1 := by
    calc
      _ = (d * (x e.1 - x m.source.1)) / c := by unfold a; ring
      _ = _ := (div_eq_iff hcn).2 heq'
  unfold b
  linear_combination hs

end SnailCoordinates


namespace SnailCoordinates

private noncomputable def point (i : Fin 29) : ℂ := toComplex (vertices i) / 384

private theorem scaled_orientation (reverse : Bool) (z : ℂ) :
    UnitDistanceCertificate.oriented reverse z / 384 =
      UnitDistanceCertificate.oriented reverse (z / 384) := by
  cases reverse <;> simp [UnitDistanceCertificate.oriented]

private theorem scaledMotion_sound (m : Motion) (hm : motionCheck m = true) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ e ∈ m.pairs,
      a * UnitDistanceCertificate.oriented m.reflect (point e.1) + b = point e.2 := by
  obtain ⟨a, b, ha, hab⟩ := motionCheck_sound m hm
  refine ⟨a, b / 384, ha, ?_⟩
  intro e he
  have h := congrArg (fun z : ℂ => z / 384) (hab e he)
  change (_ * _ + _) / (384 : ℂ) = point e.2 at h
  rwa [add_div, mul_div_assoc, scaled_orientation] at h

private def targetSubset (m : Motion) (s : Finset (Fin 29)) : Finset (Fin 29) :=
  (m.pairs.toFinset.filter fun e => e.1 ∈ s).image Prod.snd

private theorem targetSubset_congr (m : Motion) (hm : motionCheck m = true)
    (s : Finset (Fin 29)) (hs : ∀ i ∈ s, ∃ j, (i, j) ∈ m.pairs) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧
      ((s.image fun i => a * point i + b) = (targetSubset m s).image point ∨
       (s.image fun i => a * star (point i) + b) = (targetSubset m s).image point) := by
  obtain ⟨a, b, ha, hab⟩ := scaledMotion_sound m hm
  have ht : (s.image fun i => a * UnitDistanceCertificate.oriented m.reflect (point i) + b)
        = (targetSubset m s).image point := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi, hiz⟩ := Finset.mem_image.1 hz
      obtain ⟨j, hj⟩ := hs i hi
      have hab' := hab (i,j) hj
      exact Finset.mem_image.2 ⟨j, Finset.mem_image.2
        ⟨(i,j), Finset.mem_filter.2 ⟨List.mem_toFinset.2 hj, hi⟩, rfl⟩,
        hab'.symm.trans hiz⟩
    · intro hz
      obtain ⟨j, hj, hjz⟩ := Finset.mem_image.1 hz
      obtain ⟨e, he, hej⟩ := Finset.mem_image.1 hj
      obtain ⟨he, hei⟩ := Finset.mem_filter.1 he
      exact Finset.mem_image.2 ⟨e.1, hei, (hab e (List.mem_toFinset.1 he)).trans
        ((congrArg point hej).trans hjz)⟩
  refine ⟨a, b, ha, ?_⟩
  cases hr : m.reflect
  · exact Or.inl (by simpa [hr, UnitDistanceCertificate.oriented] using ht)
  · exact Or.inr (by simpa [hr, UnitDistanceCertificate.oriented] using ht)

end SnailCoordinates


namespace SnailCoordinates

private abbrev CertificateRow := ℤ × ℕ × ℕ
private abbrev ProofRow := ℤ × Finset (Fin 29) × Finset (Fin 29)

private def maskSet (mask : ℕ) : Finset (Fin 29) :=
  Finset.univ.filter fun i => mask.testBit i

private theorem mem_maskSet (mask : ℕ) (i : Fin 29) :
    i ∈ maskSet mask ↔ mask.testBit i = true := by
  simp [maskSet]

private def pairMask {α : Type} (use : α → Bool) (index : α → ℕ) : List α → ℕ
  | [] => 0
  | x :: xs => (if use x then 2^(index x) else 0) ||| pairMask use index xs

private theorem testBit_pairMask {α : Type} (use : α → Bool) (index : α → ℕ)
    (xs : List α) (k : ℕ) :
    (pairMask use index xs).testBit k = true ↔ ∃ x ∈ xs, use x = true ∧ index x = k := by
  induction xs with
  | nil => simp [pairMask]
  | cons x xs ih =>
    simp only [pairMask, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
    cases he : use x <;> simp [Nat.testBit_two_pow]

private def sourceMask (m : Motion) : ℕ :=
  pairMask (fun _ => true) (fun e => e.1.val) m.pairs

private def targetMask (m : Motion) (s : ℕ) : ℕ :=
  pairMask (fun e => s.testBit e.1.val) (fun e => e.2.val) m.pairs

private def motionRow (m : Motion) (src : ℕ × ℤ) : CertificateRow :=
  let s := src.1 &&& sourceMask m
  (src.2, s, targetMask m s)

private def proofRow (r : CertificateRow) : ProofRow :=
  (r.1, maskSet r.2.1, maskSet r.2.2)

private def Congruent (r : ProofRow) : Prop :=
  ∃ a b : ℂ, ‖a‖ = 1 ∧
    ((r.2.1.image fun i => a * point i + b) = r.2.2.image point ∨
      (r.2.1.image fun i => a * star (point i) + b) = r.2.2.image point)

private theorem maskSet_targetMask (m : Motion) (s : ℕ) :
    maskSet (targetMask m s) = targetSubset m (maskSet s) := by
  ext j
  rw [mem_maskSet, targetMask, testBit_pairMask]
  constructor
  · rintro ⟨e, he, hs, hj⟩
    refine Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨List.mem_toFinset.2 he, ?_⟩, Fin.ext hj⟩
    exact (mem_maskSet s e.1).2 hs
  · intro hj
    obtain ⟨e, he, h⟩ := Finset.mem_image.1 hj
    obtain ⟨he, hs⟩ := Finset.mem_filter.1 he
    exact ⟨e, List.mem_toFinset.1 he, (mem_maskSet s e.1).1 hs, congrArg Fin.val h⟩

private theorem motionRow_congr (m : Motion) (hm : motionCheck m = true) (r : ℕ × ℤ) :
    Congruent (proofRow (motionRow m r)) := by
  let s := r.1 &&& sourceMask m
  change Congruent (r.2, maskSet s, maskSet (targetMask m s))
  rw [maskSet_targetMask]
  apply targetSubset_congr m hm
  intro i hi
  have hbit : (sourceMask m).testBit i = true := by
    have hv := (mem_maskSet s i).1 hi
    rw [show s = r.1 &&& sourceMask m from rfl, Nat.testBit_and, Bool.and_eq_true] at hv
    exact hv.2
  rw [sourceMask, testBit_pairMask] at hbit
  obtain ⟨e, he, _, hi⟩ := hbit
  have heq : e.1 = i := Fin.ext hi
  exact ⟨e.2, by simpa only [← heq] using he⟩

private def singletonRow (r : ℤ × Fin 29 × Fin 29) : CertificateRow :=
  (r.1, 2^(r.2.1.val), 2^(r.2.2.val))

private theorem maskSet_singleton (i : Fin 29) : maskSet (2^i.val) = {i} := by
  ext j
  rw [mem_maskSet, Nat.testBit_two_pow, decide_eq_true_eq, Finset.mem_singleton]
  constructor
  · intro h
    exact Fin.ext h.symm
  · rintro rfl
    rfl

private theorem singletonRow_congr (r : ℤ × Fin 29 × Fin 29) :
    Congruent (proofRow (singletonRow r)) := by
  refine ⟨1, point r.2.2 - point r.2.1, norm_one, Or.inl ?_⟩
  change (maskSet (2^r.2.1.val)).image _ = (maskSet (2^r.2.2.val)).image _
  rw [maskSet_singleton, maskSet_singleton]
  simp [sub_eq_add_neg, add_comm]

end SnailCoordinates


namespace SnailCoordinates

private theorem pairMask_lt {α : Type} (use : α → Bool) (idx : α → ℕ)
    (xs : List α) (n : ℕ) (h : ∀ x ∈ xs, idx x < n) :
    pairMask use idx xs < 2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  cases hb : (pairMask use idx xs).testBit j
  · rfl
  · obtain ⟨x, hx, _, he⟩ := (testBit_pairMask use idx xs j).1 hb
    exact False.elim (by have hlt := h x hx; omega)

private def BoundedRow (r : CertificateRow) : Prop :=
  r.2.1 < 2^29 ∧ r.2.2 < 2^29

private theorem motionRow_bounded (m : Motion) (r : ℕ × ℤ) : BoundedRow (motionRow m r) := by
  have h : sourceMask m < 2^29 := pairMask_lt _ _ _ _ (fun e _ => e.1.isLt)
  constructor
  · change r.1 &&& sourceMask m < 2^29
    exact Nat.and_le_right.trans_lt h
  · exact pairMask_lt _ _ _ _ (fun e _ => e.2.isLt)

private theorem singletonRow_bounded (r : ℤ × Fin 29 × Fin 29) :
    BoundedRow (singletonRow r) :=
  ⟨Nat.pow_lt_pow_right (by decide : 1 < 2) r.2.1.isLt,
    Nat.pow_lt_pow_right (by decide : 1 < 2) r.2.2.isLt⟩

private def maskOf (I : Finset (Fin 29)) : ℕ :=
  ∑ j ∈ I.image Fin.val, 2^j

private theorem testBit_maskOf (I : Finset (Fin 29)) (i : ℕ) :
    (maskOf I).testBit i = true ↔ ∃ j ∈ I, (j : ℕ) = i := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, maskOf, Finset.toFinset_bitIndices_sum_two_pow]
  exact Finset.mem_image

private theorem testBit_maskOf_fin (I : Finset (Fin 29)) (i : Fin 29) :
    (maskOf I).testBit i = true ↔ i ∈ I := by
  rw [testBit_maskOf]
  constructor
  · rintro ⟨j, hj, he⟩
    rwa [← Fin.ext he]
  · exact fun h => ⟨i, h, rfl⟩

private theorem maskOf_lt (I : Finset (Fin 29)) : maskOf I < 2^29 := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  cases hb : (maskOf I).testBit k
  · rfl
  · obtain ⟨j, _, hj⟩ := (testBit_maskOf I k).1 hb
    exact False.elim (by have hj' := j.isLt; omega)

private theorem submask_iff_subset (I : Finset (Fin 29)) (s : ℕ) (hs : s < 2^29) :
    UnitDistancePacked.submask s (maskOf I) ↔ maskSet s ⊆ I := by
  rw [UnitDistancePacked.submask_iff]
  constructor
  · intro h i hi
    exact (testBit_maskOf_fin I i).1 (h _ ((mem_maskSet s i).1 hi))
  · intro h k hb
    have hk0 := Nat.ge_two_pow_of_testBit hb
    have hk : k < 29 := by
      by_contra hn
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hn)
      omega
    exact (testBit_maskOf_fin I ⟨k,hk⟩).2 (h ((mem_maskSet s ⟨k,hk⟩).2 hb))

private def rowTerms (r : CertificateRow) : UnitDistancePacked.Terms :=
  [(r.2.1, r.1), (r.2.2, -r.1)]

private theorem score_rowTerms (I : Finset (Fin 29)) (r : CertificateRow) (h : BoundedRow r) :
    UnitDistancePacked.score (maskOf I) (rowTerms r) =
      r.1 * ((if (proofRow r).2.1 ⊆ I then 1 else 0) -
             (if (proofRow r).2.2 ⊆ I then 1 else 0)) := by
  unfold UnitDistancePacked.score rowTerms proofRow
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    submask_iff_subset I _ h.1, submask_iff_subset I _ h.2]
  split_ifs <;> ring

private theorem score_rows (I : Finset (Fin 29)) (rows : List CertificateRow)
    (h : ∀ r ∈ rows, BoundedRow r) :
    UnitDistancePacked.score (maskOf I) (rows.flatMap rowTerms) =
      ((rows.map proofRow).map fun r => r.1 *
        ((if r.2.1 ⊆ I then 1 else 0) - (if r.2.2 ⊆ I then 1 else 0))).sum := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have h₁ := score_rowTerms I r (h r List.mem_cons_self)
    have h₂ := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    rw [show UnitDistancePacked.score (maskOf I) (rowTerms r ++ rs.flatMap rowTerms) =
      UnitDistancePacked.score (maskOf I) (rowTerms r) +
      UnitDistancePacked.score (maskOf I) (rs.flatMap rowTerms) by
        simp [UnitDistancePacked.score], h₁, h₂]
    rfl

private def edgeMask (i : ℕ) : ℕ :=
  pairMask (fun e => decide (e.1.val = i)) (fun e => e.2.val) (edges ++ edges.map Prod.swap)

private theorem edgeMask_dist {i j : ℕ} (he : (edgeMask i).testBit j = true) :
    ∃ a b : Fin 29, a.val = i ∧ b.val = j ∧ dist (point a) (point b) = 1 := by
  rw [edgeMask, testBit_pairMask] at he
  obtain ⟨e, he, hai, hbj⟩ := he
  refine ⟨e.1, e.2, of_decide_eq_true hai, hbj, ?_⟩
  rcases List.mem_append.1 he with h | h
  · exact edge_dist h
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
    rw [dist_comm]
    exact edge_dist hr

private theorem maskOf_independent (I : Finset (Fin 29))
    (hI : ∀ i ∈ I, ∀ j ∈ I, dist (point i) (point j) ≠ 1) :
    UnitDistancePacked.Independent edgeMask (maskOf I) := by
  intro i j he hi
  obtain ⟨a, b, rfl, rfl, hab⟩ := edgeMask_dist he
  cases hj : (maskOf I).testBit b
  · rfl
  · exact False.elim
      (hI a ((testBit_maskOf_fin I a).1 hi) b ((testBit_maskOf_fin I b).1 hj) hab)

end SnailCoordinates


namespace SnailCoordinates

private def proofRows (rows : List CertificateRow) : List ProofRow :=
  rows.map proofRow

private def completeTerms (d n : ℤ) (rows : List CertificateRow) : UnitDistancePacked.Terms :=
  (0, d) :: (1, -n) :: rows.flatMap rowTerms

private theorem score_completeTerms (I : Finset (Fin 29)) (d n : ℤ)
    (rows : List CertificateRow) (hb : ∀ r ∈ rows, BoundedRow r) :
    UnitDistancePacked.score (maskOf I) (completeTerms d n rows) =
      d - n * (if (0 : Fin 29) ∈ I then 1 else 0) +
        ((proofRows rows).map fun r => r.1 *
          ((if r.2.1 ⊆ I then 1 else 0) - (if r.2.2 ⊆ I then 1 else 0))).sum := by
  have h₀ : UnitDistancePacked.submask 0 (maskOf I) := by
    exact Nat.zero_and _
  have h₁ : UnitDistancePacked.submask 1 (maskOf I) ↔ (0 : Fin 29) ∈ I := by
    have hs := submask_iff_subset I 1 (by decide)
    have ht : maskSet 1 = {(0 : Fin 29)} := by
      simpa using maskSet_singleton (0 : Fin 29)
    rwa [ht, Finset.singleton_subset_iff] at hs
  unfold completeTerms
  change (if UnitDistancePacked.submask 0 (maskOf I) then d else 0) +
      ((if UnitDistancePacked.submask 1 (maskOf I) then -n else 0) +
      UnitDistancePacked.score (maskOf I) (rows.flatMap rowTerms)) = _
  rw [if_pos h₀, score_rows I rows hb]
  by_cases hi : (0 : Fin 29) ∈ I
  · simp [hi, h₁, proofRows]
    ring
  · simp [hi, h₁, proofRows]

private theorem certificate_sound (d n : ℤ) (rows : List CertificateRow)
    (hb : ∀ r ∈ rows, BoundedRow r)
    (hc : ∀ r ∈ rows, Congruent (proofRow r))
    (hscore : ∀ I < 2^29, UnitDistancePacked.Independent edgeMask I →
      0 ≤ UnitDistancePacked.score I (completeTerms d n rows))
    (hd : 0 < d) (hn : 4*d < n) :
    ∃ p : Fin 29 → ℂ, ∃ C : List ProofRow,
      (∀ r ∈ C, ∃ a b : ℂ, ‖a‖ = 1 ∧
        (r.2.1.image (fun i ↦ a * p i + b) = r.2.2.image p ∨
          r.2.1.image (fun i ↦ a * star (p i) + b) = r.2.2.image p)) ∧
      ∃ D N : ℤ, 0 < D ∧ 4 * D < N ∧
        ∀ I : Finset (Fin 29), (∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1) →
          N * (if 0 ∈ I then 1 else 0) ≤ D +
            (C.map fun r ↦ r.1 * ((if r.2.1 ⊆ I then 1 else 0) -
                                          (if r.2.2 ⊆ I then 1 else 0))).sum := by
  classical
  refine ⟨point, proofRows rows, ?_, d, n, hd, hn, ?_⟩
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    exact hc s hs
  · intro I hI
    have h := hscore (maskOf I) (maskOf_lt I) (maskOf_independent I hI)
    rw [score_completeTerms I d n rows hb] at h
    omega

end SnailCoordinates


namespace SnailCoordinates

private def rowFits (m : Motion) (r : CertificateRow) : Bool :=
  (r.2.1 &&& sourceMask m == r.2.1) && (targetMask m r.2.1 == r.2.2)

private theorem rowFits_congr (m : Motion) (hm : motionCheck m = true)
    (r : CertificateRow) (h : rowFits m r = true) : Congruent (proofRow r) := by
  rcases r with ⟨w, s, t⟩
  simp only [rowFits, Bool.and_eq_true, beq_iff_eq] at h
  have hrow : motionRow m (s, w) = (w, s, t) := by
    change (w, s &&& sourceMask m, targetMask m (s &&& sourceMask m)) = (w, s, t)
    rw [h.1, h.2]
  rw [← hrow]
  exact motionRow_congr m hm _

private theorem rowFits_bounded (m : Motion) (r : CertificateRow) (h : rowFits m r = true) :
    BoundedRow r := by
  rcases r with ⟨w, s, t⟩
  simp only [rowFits, Bool.and_eq_true, beq_iff_eq] at h
  have hrow : motionRow m (s, w) = (w, s, t) := by
    change (w, s &&& sourceMask m, targetMask m (s &&& sourceMask m)) = (w, s, t)
    rw [h.1, h.2]
  rw [← hrow]
  exact motionRow_bounded m _

end SnailCoordinates

namespace SnailCoordinates

private abbrev RowBlock := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

private def decodeCoefficient (u : ℕ) : ℤ :=
  if u % 2 = 0 then Int.ofNat (u / 2) else -Int.ofNat (u / 2 + 1)

private def unpackRows (block : RowBlock) : List CertificateRow :=
  let (count, width, s, sw, t, tw, bits) := block
  (List.range count).map fun i =>
    let cell := (bits >>> (width * i)) % (2^width)
    (decodeCoefficient (cell >>> (sw+tw)), (cell % (2^sw)) <<< s, ((cell >>> sw) % (2^tw)) <<< t)

private def singletonRows : List (ℤ × Fin 29 × Fin 29) := [(-1, 0, 1), (-1242579097, 0, 2), (94697399, 0, 3), (1058199, 0, 4), (-116055208, 0, 5), (729913735, 0, 6), (621115501, 0, 7), (398544897, 0, 8), (-712410074, 0, 9), (998944164, 0, 10), (262434946, 0, 11), (-926345377, 0, 12), (340317927, 0, 13), (845804849, 0, 14), (659917025, 0, 15), (-427797197, 0, 16), (714582776, 0, 17), (365810760, 0, 18), (-685474022, 0, 19), (606649491, 0, 20), (-1026288, 0, 21), (358353054, 0, 22), (179965117, 0, 23), (-530297663, 0, 24), (741211147, 0, 25), (330612660, 0, 26), (97261952, 0, 27), (295505631, 0, 28)]

private def rowBlocks : List (List RowBlock) := [
  [(96, 78, 2, 27, 2, 27, 0xf7136ec8c14031102a87d9bb5c205000c804200f5337420211001004503cbccfa0a0c602661001f1a7784c815001046a07c4eb15320d002410a81eed84004201800844103b99263004540c445880ed6d6180c05400506087afa70c900c402411100e7931f409410020142079d2612284400c464200e682c280c1500110608794e1d1230d502501aa1e3e3220c9410020548077f5c5b220150c141a81df77c680c010001040877a5673034050c1450a1da2d1a4001180180420362e5fb2a0800e060281d6721d8a42440858288346e2e1031000c8000a1cca33202811801884007301f8e20c1600245a40c895a9008344094020071b9ee80b05100520821c082a30c904000052806f830ed00c02002040c0bab7e188221808904902d566e20005600641800b50e76cac21438584a86d306ba2900400061220b12a7e02d14401492086b4c01a290d102560a20ad00d60a9044004928069fe788320d202610a01a4e507824140011820828c1b8520800000002c0a21cc142c40002080286842e2f284100c064a8090942282d050001960864249fc3205200610a018ed7ab8010443051200221ef9b0b084020610a187fb7f089400320108061daabb00854004418c08701bd0c3408028509020ccaca20c500c444a407feacc02904800892005fc803d00404000050807e49bf80c05030106085c5dabe03405001450216f6eabc0405030106281b9c0f881445005051206ddcbb8a105430596801af91b13205000410a8169475808221808804901a1a7102905500521a20660e89ca400030180a818d1f7720c010c1442c0612a76c021580190630181093b210510c540aa05c2ca4445000300502816018c7208900e040ac0566acb2211100109440156529400c12002048405405d00891000101080540ac4d10d0200a140c047e924ca515001196a811dcc93204510c544a80447fbd0811180181480104a73900c51005048c03e1177c8415001106a80e9c6512309502101aa133982724200800840500cb7a60030d10250082132768e08c25438406884c287832a05000460a812e265f08505030016880b43a48209000c80024029216080505030116080a2470a2a45600665a01252da40a00440048280088f673090010c1600a01df7dd22830439480404739b9b2805400461a801c5fc9229104014904045cfd692a0810212028115df2cca415001186a805508a6024410c54400114cd6b0a1144314928004ae744135040081502112a482029400020900042ddd762240600245201060a818a9048009928040d5538294040c025220), (96, 79, 2, 27, 2, 27, 0xf8b1fe05488a00a4a403ea95b304211001044103cbefeb006020602282077f86708a0c50e521101ef8bfa6008080008a101dd75f940240032000303ac0c7e18a080600a510757a328800c202600100e9d29f11410c04442203d13def40401000004283a0cf6e486030010a8a073b46da2941100164a20e46b0c8200ac00c23001c89ff5243108018505038f1fc29906201208940f001e63030140c0418a1df4086410028000c3001bde912421010300942037b542640a00860820906f2069b01081021400a0dcb8c4616820180c9143b7f1bac8031809904a036d21b890a28802825506da2e220080600241040da9b5de018081808a181b475b18251503119608363bd499504207030940eb4e7f8908c002410140d5282012610004020243a7340c4c911801854a073e260790020802a014066a4c54810440c401120cd062de46028000835439460c404305030056103271ba8186820040a920637aa76224400c444201c5f3f26441a404c815038b51fdc8234409502b03140d870500100130000e09a0712b404000252a1bfa8ea64280a0028a5417c27b608831809804806f5d63505a0806032410ddd058c204550c505a00b9782ac448a00088940371d83ac0d15001116286cdb2a2440000001008058349360209202240801aea0c764600a002825435cd513c2514001192282b325c511a08860a2510d5eb36c0a0110c120801a971a8920004004202014ed1f980211401504102994cbc4906001208080d2bc8c60940500165020a568136100a400cc11014aa7e68200180098400293f79b9022b00322d405246af40a09502121801a3a5732408a400c0950147195c0850443041288288e2ec904800640016051140bc3040200214200a18050e4102a182835813f471f081410320148027981569822b0030ad404ee54ea024100c0448019da37d05488400c4840334ac030811500101680268c99488480064080604c0a4a40840100124000977218224008180221032e88010894000201080659770e048080001041049d2d16034040c0450219203ba021108040220811ee07b003148018121023ab0a094a2a86292d50466364e01094020418208cc066a6610804022543172250440050000462022d5bf111228802a2500c547fdd2241600205a818a85188420a80080344113b0fb08d0100001488625cb1e90a280020255043c558a030140004182185eec9810822182490010ada96041018008540021332b2184800040812041196fc224460060520181b29e8448080000a402fed93748515401416a81fbb64591a2a802a2d50be04136204140c045a00), (96, 80, 2, 27, 2, 27, 0xb36f5222241000044a01b354bc5124000c014081b34528111500008140a0b2e64ed2b41500125aa1b18e8501210200a10001b0a54a08200500101101b0795f62084400441240afc594110800000100c0af007c5220550c501a81aef67911245600615881aed26372085000440ac0ae5b86f0a0510c560881ac18a062009602241a00aaaf7b20144400445020aaa788c3240600215201aa999f510802002100c0aa5b5e20b40100164021aa28947280150c161a80a8a9944834050c105121a82180b2a08202260281a7e8f800040600205000a7bc2220300500141021a5698e1081040c821080a446db03210200a10201a420c6e2a41000064a01a4072f82241100104a01a31aa002308502101221a2ea1389008202210100a2b32f48b00500121121a1e36bc2801500121a00a1c43922a00200260201a1453ca0a40200264001a0488962805100560a00a004779320d602611a819ffa0b5305040c8152809e380fa280150c161a009dd1468320500c410a019dc68c1204050c1052809db903c90882022101409d1c26f0a012002608819c9ee64814410c5041209c92dc6008c2026400409c2e320934440c4151219b9ac4d00c41005040c09b8907228440004642009a82165084410c5240809a293b88a0040002110199eafd4311000081022098f28c5230c5025012a1989681a2345000444a2197a372f2241000044a81971dede2b0150c161a21969973500840004000c09628866208d202640a4094d5d2c224500c404a0193c453b280510c560a80938c39e2300400041221938a563290910e160aa09234788820450050110191b4dbc8144100504120917ef362081400041a4090c31d800455005058008feca37214100c044aa08f4e0ec1010200a100008f39bab230140c041aa18ea054100880020000c08de797820005001012008d334f40a010000208018cd75e4224410c5042018c5f9613109402011aa08c524048b4410c5241218a75714004550c50580089731fc034010c104021895460d28005001212808942931094500c4248a0892fbe400806002010408905d222a0000c06020187f382e200d602641a0086daf26230150c141a2186bc40c0085000400840868f8cd309000c8102c0854eb432a05600661a8183bf4000b4450c52502182d3ffc030010c100021829cf1812104008110018244209214410c5042a08228ea32a0510c560a8181bcf65304060021528080fb425220d202600a8180bf2f4130840e0110217f621cc03404000050217f5277c8b081021201217eb803a2b0d002460a217e59861034110c1048a17e58656204540c445a007d1bb672a0040c061281), (96, 80, 2, 27, 2, 27, 0xedbfb0c2a09202220a01ed25b7c2b05100520a21ed246101090400811040ecc42c8894400c424120eb3957b2b4100c064aa1eb2a129094000c0240a0ead4277220d602641a81eab4f700309102100821eab48360080500141040ea6573d120c002410081ea5500820c1100104a40e96809d034400c4040a1e8f4b6d2a4040c025281e8e025d00850004008c0e7691c90845400425880e74cac10a1040c821081e66121c320d002410a01e5a03eb2800200260280e5420e2030000c040021e1dbcc220c040c045240e0feaa5325040c815281df5a5882a44600625201de1ad852309102100aa1ddbbea62b0050c161221dbf778120c100c004ac0da145da20c1500145a40d9ff453008d5025418c0d882c992210600a01281d851710109000c810040d7693748a04000420101d714135234410c5042a1d70065c9080600211140d6f525500d00008040c0d681ea8808000c000140d52fe249304000410121d4ad0ff2244200644281d368cc92b0c1025202a1d1c01f2294450c565220d10ccba2304100540221d0b866a0941100164820d049143214000c0442a0d02012a0944000464020cf625080009602201800cf334350a4040c025081ceb97c300814000418c0cdf5163294450c5652a0cd7a758808400c400140cd2c75c80c0600205140ccaebd1114440c4150a0ccaa3a6094140c065820caa89140b01100120821ca00cb60904000460020c9e75a520840004002c0c9d6a988b04100520121c9382f32a45000464a81c6f4a012a0040c021281c6b244321080020402a0c673d8e0b0d402461821c6083f92b4110c124aa1c605084930c402411121c4c5d98820810e100101c4b94232a0950e161a81c2e563f2b0440c4612a1c26079c8a40400025101c1b8d5080c0200204140c042ab0305000c814200c02f7d120c1000004ac0c020c150a0c002420081c019d950050600a05080bfe7436208d502541a40bf96754800c602601100be67cb43244200614201bd8a35c0309502101821bd0687c8240100104101bbc25a08080200200140bae1a742a10000820201bab7ab20a0050c161001baa2a9121404000052a0ba846e22304000440221ba5de86024140c045801ba242a8830000c000121ba0febc334100c014a21b9becbd31440004142a0b8dc52f220010c140281b8d4ffd224410c504281b8ae317000550c541880b867fdb2208102140281b7d54c51000600211080b710766020d202640801b64992f2301000040aa1b59bced2008202200280b57779533040004102a1b5616542050600a05200b52ef592244200604281b4804748a00600221101b3e6bb13141400015aa0), (96, 81, 2, 27, 2, 27, 0x90080cf80a020002285047f8433c8900030110a063fb67fa0000a002021011e6af4e000d6026418008f092d28088206400850478334400d040300120863ba569642800000885411d5e6e300842006400c08ea1c2689a820040a850c6f94dd0200140048400237ca50c16880008c80431b18563084150c1658808d5d91a9908200408940c6938cb04d1500105608633aca2a012040140018119d1ca900900008000c08c990d6086810050a0204645c550804180280480232003861208218ac0141188ce3f0b0040c0610a18c2b2e31520b00132d00c601bb2080114014048022ead5ea21008000221811738047024100c0448818b3e084086010010a020458462e0c2050000469022ba947a4602018001543153e90b00056006418808a74b8c10a280620251044f53f24a834409482a0624953c6028a81888b14110fd04e000c2026400008829d2e906820640296043df97d48c41032004a861ef8390608ac00c2b4010f09e9e2a4450c565201872e59505008860b0400c376bd34210000009020216def7e5408400cc05030b68fe60208102140001856271f9022a00222d40428773504c25038046086135ad9e0102a002831810934e008104500501120848f4810020300122800420e6ac808114015040061038bc64600a1828254307e9b91224020020428183cf3071120b00122d00c1c86898a9004005908060e4166e1408c00cc210306e3344210010010022083612b71122100322100c182eac08d114314148860bcd298018a00080908105ddcd30b054004618a182c684e8848300508860415f80b80c150311060860ae43ba1408200a40103048f6952b040004202a18219c564904101108080c10606fc8410001100a820792ce24212004001541038bf802001500101a008154d5a806810050206040a05178800540050680204f99001288a00a4a04100c6f2120442006042807feae9f0500006030000bfd441808314031012901fd09dbc56102042c0442fe80e1e2905400461a207f370e980802800a08503f992d10a915801896805f9fc0b40682a0028b042fcf557b0a0150c1618817e1ba9c4906101308080bedfab8c2511001194281f22c9e0568280004b442f80b28430c400c4142407bf184d10a0a06022d103df146440901430414205ef3d2b0408a400c09400f644b5f20c45005452c07a8f88f15020802b0100bd0e47924111001054401e644514068a80088b042f2e1af88b4050c12512179685ab10408860a05203c7259b4ad10001090a85e36156e4208800882540f15ff482a0c10252020178111158422a802b2c403bf282080234409502101ddcf680468880080a442edd1fb48304000400121), (96, 81, 2, 27, 2, 27, 0xad2d5f18484001030050567980e04d00030050086b2579b820a0c0142a00158766e30b0440c4610a1ac34a748186801200450d602b754cc20008040a86ae5cd5e448a80088b503572182510d040c8150c0ab8c11794a020003295055937060ac14031082886a9f98ea0420c0140210354698488084600601140aa29a6240622802828a0550138388815401506806a7538ec4602a00283443529d72120c010c1042c0a8c01ff802220022284054158090cc140310428869d1c67a41020000015814e625fb000150c141880a71c54991800800a0150d35c484424240080822829a5ff5244a00010085034c783888b0400c420121a6146f1006220022282052f2aca88414401502882977ab9052200010404414b9fe1d1009402011880a3820dd806000602206051bb3aa049410020540068d06996448a01888950345ec78d0a0150c121881a2b31e91060a00022d2050ff4738801180190480287a353a2400800022103437d8632804000460280a19e4644504001010080d0cb3f6c8400000100a8285ee29e501021c2c050141c425c0090400801040a0d29f89902100308140d04c362c031080191030281b6fca408a218a0950140bf8dc1090200a10040a03a3a98186a01220c50d0140848821500110690280376b44102a002834813ed83880b040004200219f12b198520100132040cf45f820c141032054802770ae82240ac00c231033aefd392941000024aa09d18b8c9500a86090d40ce7dc7d48811801804a0672745fe448a200a8950338d6d940a091021208019c4fe2f0402a00230c004e0250f48d05000016a866d8c02214028180431033434745124500c41488199b1a84192820640a900ccce5ef40904430412206655c1a6041a404c811033275108930c00241012198dceee9180006000150cc655d6ca914431592a0662eb81814120040410033165e5f000d602641880980ff6f9500a00030d40cbcc56208c410020048865db0dee5000c004c25012e70a5a084400046400096f49c21582080290110cb717e0804114015040825ad82d641800180885812d670f3080560066188095ee6b31120006022100cae0f6604914031052006545bf3c001aa04a8300129d41cc094100002482094ce55840403001008a049faf9d48505000016a824d8da122120819022181269eef91005400411880934ee500980806008410c97cbf90c8350390468064bc7584021a0048810412594b01230c1025002a1928682248061013080804928dc080911031114006477a354108a8188cb00122f3ed8321000081020191523ce84a228629285048a44464050103001428244bff5a4100800002581204d073020550c541881), (96, 81, 2, 27, 2, 27, 0xcdb3aa10522206232800e6ad33904d04030052087340e5c8248881882a00399ba2da234100c044a21cc94fc4984210030816066433d300c354094060872e53a16121081c0c21419603f48880410c520100c9f88dd140230033090064d625248910001010a072658331140801884020392e834d3209402011a81c935f5e086820040a8206459dad080154014068031f19262468a0008095438f006bb280110c160a80c77f7579582006230150e3950390c8040300428071b646c85482a0024b4038d1c49d20880020002c0c65ccf60500806010400e2e763920820408400407164c7de12020180c11418a9dd40120d402411801c48c9784900000008080e226df80ac310090848871031f240418204a80003872bffc8a0810e120101c2134871182a00220d10e0fd65d02041002084003064ba06048081808a103822a7e10005600601880c0dbe6d80600860a2060604c9334041140140428301efb9246080008005438050d7521441005042a0bf8bf709528000412140dfb43934c840802840a06fd1d84a64820000295037e5c3eb00c410c5440c0bef76c00186201200810df601dd88c10031100886fa108f4008881888a0017c8d9ea2a05000460a01be1b1919122006222140df076414a501430494a82f3e39ea410880080258179ab573290010c1602a0bc7b5f844a22002128905e262730c824008042806f0e73fe100a200ac110177a3c488b08002020121bbd000b84a20002320505de0c6748101000014a02ee0c69912088188422417589004230110c100a21b9d39870060a860a2c205cbd4dacac30439580a86e50cc4c128a200ac9041721cac82a50000824201b87cd348908206408840dc301a448d41002014a86df232ec46000180804436f83d96024000c044001b7bd92208882004088105b5f47c22831409484406d972f804088400c084016c4ea062244500545201b5cd54094200800921405ad8af8ca104000192a02d449cd81012804043001698dbaa230840e041221b4c131205a0086092010da41fde4c830009040a06cfea88c508a8008cb40167880d12a0d402421a81b3bf87111068812a0500d9528d3c2830809980206c9fd3c2508a218a4950164823b200c1000044840b24055f1504801030500d8bda200c200000040902c588349140021824020361f0a5e284550c565a00b018c150186801220410d7e359448241032004b02baecafa62208190225415d4a5281210000810001ae7fdfd0500a860b0c00d73b8a54a515001096a82b9c3f76120a218ac11415cd962b2309102140aa1ae39e971180a00020d10d6eb2cdca804000182a06b6288092188c00c2a2815ad845d2b4500c424aa1), (96, 81, 2, 27, 2, 27, 0xe7dccac1906a01208d00f3e7193c2c240081822879eeb5664010c04482501ce41b9c2944100524220e6d13481122800202500f33180ec2804030182207995e518268a018829043cbe946321445005452a0e5e37c81004a81080d0072cfdde4a115431496a0395ebbe02120c01422081cac9c822b0110c160a21e5332224982006208090f27e952c083580990620792124be0012a04283101c88241e214150c145a20e4292f39022800222540721340682d054005960878d0b48a1020c01442101c6545ab0040500145080e327a1b10228062225007187af1800018009040038932e4c148a8188cb003c49881a2901500161a20e21c6070062b00322c20709da68c0811801904207846d3ba2400018020103c18de0c2345400405a21e097b8294a8000412150704b2374a834009082a0781d03d25282a0024b541c09399b2b05400461aa1e0209440500a80090c00efe27ff20c210080044877cceb921082218249101bddfd7e00c0600245040dec378818428002085206f52c5c448050300462077a5d8a6008a80088b101bd068f9104000c014080ddd26aa99a820040a950eec98a622101030094403736da0a20a080102a101b9600f0034400c404021dcaeb099182a00220d50ee1196ec0c110011042877025e204110a04202481b80e15d1250400815081dbff5124986207208890ede4c0ac04110011042836e382d6411ac04c83581b6d29ce0a04000460001db3663d1500800030500ed11a41000158018060036774884408ac00c8b401b301174120100c010801d9327b4186820640a9206c8a7a602914401492007635b5790400c00402203b10c7660901000060820d8442001184287080910ec0c23602d154314960875feb2d21400818042103afcf4340945500525820d7d47c89522880292540eb6868704315001056103583bf4a4180a1820a581abe7683208940e041ac0d5865200122806202400eabd7288080543050600755c8c225082200249501aa507fa2240200244201d476cb840462012008a06a27c408211080199000350c805a5612004041543a7810de20c5100544a40d37dfe28508300510840e9b9b83c28058009862074db8f14420aa00a83441a6743fc2809602221a00d3116e01062a86282d2069857d84a115401496a034c06a7e0100a18282181a4687552208502101281d1209cb0522806232400e83ebb7800218089040033df461e400a400c815019e767e20240600245001cf2959590023003209406777582041058008560033b79b5004820180090039d7c47e2089602241a40ce70ce304200000320006704dc808c14401402887379f50a448a0008095039bc600c235040c805221), (96, 82, 2, 27, 2, 27, 0x84abb7bc043000910028212778da204040c045200843664a20110031010402107fedb010040c0410a083f57024a904800892a060ec34f3290510c560aa083978158a0044305828020e502ad2a4050012528182e2e0d48205000006b020aff8272a4400c464281828e0d302d15401496086086ca701050200a1400081efd71cad15001196a8607bafb92b100008202a181d60da4c810001040a0606df4ed20c44004052c08176b198030403011210205af7848a08102120101816437580d140311120860498c4d224440040528180eb3b64030403001230201d62f8814450c505120806923e8291580199600600e66722b0450c5612218026def8a904030192805fef3cf512104008110817f8270b40101030014201fc1ffc7284140c065a807efa0cf20c21408404485fa5f1530a002002600817e50add08c00430400885f894898304400c4142007e052bf48c14031002a85f7b92ee0b451005648217dece9f24820008040405f7a2b7b230410c5402a17dccf2ac0000430500201f5df7a72b401001642a17d572dc40505400416281f4219f52a09602221a817d02f4a4c824008042a05f395b912801100120a807cc170d02901800894005f2085e0284440c4252007c41b9582811431584005f10131f2a0810e1602817c3e4cb24c21038044485f0da1182a09002020a017c2c21a02d40002090085f08088093444004151217bcea1f08d04430412885ee7b8d513100008100a17b98bc600d41002014085ecf0dd900c150c1058c07af8d5a40801400404205ebcc3c93345000414aa17ad509ac8905000116a05eac843520046006012807ab172700225808806101e7e3e882900400021220796b82844140002050201e5764c0290440042122079576a822010001080401e46e00100c110c1048c078ede9c20821408404405e2f8730095040082502078af67642820808880205e2a40de214110c144a2078a6d0220831809804405e29abc8084450052500078a20f002441002084081e26411510c02002140c07828f6280034409502001df0c19d3050200a1428077a95860a815001086805de57da808015001218007784e9d00c15431406085dd64cc8204110c104a00774f4f688024808902801dd1665d1050200a14080772256f82515001196081d97dfac8b4050012512176536c4c8d01000114a85d923cab0b0c4024610a176144cc82100400590001d7fd83101454004058a075f4daf80d04030112085d6830222801100160a00757a8dd80025808906001d596e4a20c1000044a407557cb622110401490401d55d17c2050400805200748707cc2501430594281d108b3329044004612a0743217b08821408404805d08a3912a0550c521a81), (96, 82, 2, 27, 2, 27, 0x953f2080ad11431494886543f8f08a4050c12510194ef10808d410020148865363861204410c5042809484b9ac280003018020651da3dc2905400421a209465e8ec04340091022825185ab913444004150a194399c98801580190680250d5994214150c105a20943479e42c154314862865014ab1124440c415081937a0674cc30009040a864da4941114040c0150a093585e94c111801854a024d008072b0000c0602a192f4e8d4cc04000042a864b9ee82080d002460800924da17401110310142024796867210c1025402a091d314d0894180281480646c621c0a05500521801918aeba08211001004902455cd983050400815200910caac4a841002084a0642a2c27000d20264088090525db8031440151210240f22e90250000804081903457ec8d01430514a8640872140a100008200018fee70d043010300541023efef2a2345100544a218f56660089410020148063c76c2f2845000464a808ee3877444400320402823b3b0290010600a010808ec4c1c825104315900823b01717290500c460aa08eafc950c8210080448063a36ce920c5200604ac08e70c9c882018009049023927248284500c424a008e04c8a48901000014a0637231a883401001041218da37e242915031096206367d4912a441005242818d7fb670c20400004290235a6418211040c8012208d42cbd02c1400108208634e4cc7020110c1408818d2ca100483000904000633cc8a9094140c0258a08cc93c600005800806002320b993080400c4600808c7909780105800916002319fef833084020112218c03883228110310844062fffe52024050c1450018bf940f4a440002080a822fcbd9d21080020002a08bc15b5228214384844062e86f8709094020618a08b50d750a1154314968022d3ef2f2085400441ac08b4157182c054305860862bffe7b03081021400a18af03d148311431414b022817152280d002460a0089a7c08028158018860062672a572a44200664281899a921c8d01030114a862631181224050c105281897edd7c8115401516a02253897510840004100c08903b7724d0000005048621fbf582900500121220882e6b24c011801844a02209ac39284000002428087f447c028310090840061e738a52a45500525a81878453aca020038180a021d0adf4290410052022086f3bbbc08208089002061b8b91e000910214080086c1bf94c501000054a8217eb5e62041100144a0085a24404a020008080a021672d3480c4400405140858049e24c0000004048615cb6c43210400811201853fa0748315001016b0214cd4840a4160022580184f52e94431000105030213d1b5723444004452a184d871c8890440051280612af0d52b0c4024212a1), (96, 82, 2, 27, 2, 27, 0xa5bebe920d0043041048696dd7ec2084600601240a5ad0d58a811401584806969e7053200400011281a53d96a04820008040006946841511454004158a0a503e8e0c20180084490293e83f60801600261800a4e725fc2d0143059428692b173729440004642a0a4a91134c440002040a829213aca204150c145a00a43d37cc8405030106a8290c26f52b4050c1252a1a40bda50c1018008548028fe810a0b04000460021a3c4314220310090844028db10c72a0d40e461a81a33cb0c4a000400480a028a631c500841005000c0a28c0128a10003019080286c40ba014550c545820a19f6868ac000001808868670f28224100c004a01a191bb74a500430490a8286388f1281000c820280a16505124d0103005448684ed15c8a4410c524101a12d63c8a51100119488282688ec030d402401821a092fdb44941032054206819ee0e0b00000060021a06004204341032054102814ec50894040c025120a035cc1004350090060827f8ce8c094400c4240209fdee6e48d14431412a867e42593084510c5648809f34ec30ac200080808867c6b46900c44004050c09f1288d4c035009046a027bdfdc53001400011a809ee178b445140310522827aea44a034140c0458219e4d49b8281140158400677d6fae00c110c1448409ddb2138890480091280676e8ea920c550c505ac09d797d64a400400480a82758bf40924400c4141019d2acc8c041540150628272e862808046006210009c8d1d348410001000a827183df92201500101a819bf830e405044304122826fe03ec10094020118009baf173042158018461026e4f85423080020002219b8c78dc8301000114b026e136842a0d002420a019b7d0c800d104314100866df38491210200a100819b4ea66228118018844066cc03ec88001001201009b2cb86801050301160026c8277e024450c5450019b124844c841032044a066bf7d8f2b000000602a19ac08f988d044005128866ac785c8a085021211019a8544f0291043149000669223e700c46006450c09a393ab821010001940026816d40224400c40420199ab5fb88101000114802662412c094110012482098ca9fe4041100100428262dbdbc80886022011409865bd1881110311148025fccb29320820221028197eb7ad40c350390062865f1e2c60a44600665001976b0210a5144014928825c4a85f0a0410c5600819703871c20000301802025bd68ed0a45400425881969f93e80315001116102597ae7a030110c140821965b2bfc8410401500a8259644e10a00100120081965016a2001180180440258c197c824410c50410195ab62248100430410a0256a6723208840e0412c0959023d4030103001430256347f0304100c014a00), (96, 82, 2, 27, 2, 27, 0xb71e02800511431414082db41cd53201600211a81b6c37c0c2100800990202da5c02510c00000140c0b68bf3848835809806a06d848d211010000810080b57d4b8c8c00000100a86d5a5b1909004000210a0b562c0380c30009100086d4ca5602a4500c424a01b52ea3488021408504802d4791d4009040c801040b5080c8c0900030110206d369aeb208d502541ac0b48ff4b02900800890006d1e3ec1020d202600881b42315dc8c01030104a86d05f5740b0010c120021b40979508825408406806cfda70b080100c060880b3d5fb208d11401414886ced4ab32240000044281b39abec0c025808846802cde077010c000c014040b30448a40200800800302cb4fe720001600241800b2cfb4d48041802804a02ca6cc5d0850600a25080b28655b44824008042206c9d14182a45000424a01b25b2278a501000194882c7fc69c8844600625100b1d878444241002044302c6d88809088002010140b1abe9f42c31409484286c6807f70845000464880b18799500c14031002086c5edd7a2801500161a00b1272fd80915801916006c2a9d190a0550c521881b0994c28a004800982802c0972f83010600a11200b00939eca430039180a82bf83ab22240400045201afdb38180101030114002bf66ba13241400015a81afd583148941002014a06bf33b760a05100560801afc15ec4a801400484a06be0c3780900400021020aee0a63c0c01400504286bb817849200600211101aedb6f540241032004302bb6a181208d402401ac0ae8da5b88910431510806ba1984b2041000044a80ae7316a20011401404402b8698711250000814081ae0f14040901030014206b666403280d00e460a80ad9434082d01400594086b4b8f350050400805080ad243aa4c110801850a02b2d90342245200604a01ac83af188d10001110886b1fac860341400045821ac50b7900205800806102b0ffaf0334500c414a21ac2418fc8810801900a06b04f2783005000410a00ac1312c88301000114902b034c1010c5000414840abaf653ca000030180a02ae87cef214150c145aa0ab56ea682115431596002ad409f511080020100a0ab3d327c8500430510a82ac2dad60000500141000aafd4a10a825438486806ab01eb920c1400005ac0a8f1e4f88200800900902a339bfd20c40004042c0a8cae3ec0d14031112286a2b9ff7024510c544881a88704500141802814002a1ed754120c602611001a829655005054304160829f7714a224100c044a01a7c5c4748414001002a829cee320214410c504220a6d3e8a4a041002084a029aeae142b44000424221a6b69e3220000300804029a8fb422a04000460201a63e7084c820008040a0698eab992b45000424aa1), (96, 82, 2, 27, 2, 27, 0xc824cba02d100010900872083ade2301000040a21c7eacd602d054004960871f2fcb80088602201040c7c83bd404400320002831e440ac334440c415221c75a180c09044305122071c73c29024100c004881c71493fc8310001110b031a400de224510c544a01c625c0e2490000005040717ff97810c5600615840c5fdc9888814401502807179da74880450c521100c5df308ca404030182a83171bfab090c0024600a0c5b9fa48ad0040059088714583d82a0110c120a01c4b0690c2c200081802871200e78880010c120100c4484798210403019200310b510a024010c144001c42314b808154015060071023e84120d002410801c38e3f7081054304168030c2d7ec2a05500521a01c265f7388d004305108870914cb923001001002a1c23977b80304400512103060dee42344000404221c1590e742901800894207048d73e008d402441840c10f7fc20c20038000487043a0bf2244000444281c0ed30bc283480998220702d1d2d1205400411881c04e6e580c14431502086fff93a4334140c015a21bfe75bfca825808986a06ff2ed9b210100c040aa0bfb46a882c00030180086fe91e453241600215a81bf86f6e8a010031180802fd3e42d1040600215080bf2aeba8a510001190882fc529e10044500505080bec14dd08300800810902fb0094c8a0c002420101bea53d20a941802894806f9f460e2b0d40e461a21be59e8d42440032080282f8d982a2008202240200be30ba988301400514902f86d1842200100100201be0f279cac25438586a86f8215bd320d40e411a81bdec33f88410001100882f796b542341500105a21bd15a1788d11431514886f43900a2041000044a00bd075590a425008086882f3ccbca0a45400465801bce13490c940032050806f33231e0841200264800bcc00078a111801994802f29f206294410c564220bc7d25382020808980002f0a1aa83050000814200bbae735c8100000110a02ed9e9089204400411101baff8f94ac34009082a86ebb5dea20c410c544240bae66b404815031046006e9d4e58920440c411101ba5d1fc4c021808844a02e80b791300c002410280b9df5c822c30409480486e67bdfd3240400015281b931baac0900430510206e3a2060284410c524200b8d903d40415001006282e34db9f210040c0412a0b8cfdbc40d41032014286e2c0e1b00c41005440c0b8ab3d6ca005030186a02e26b2f02810400821200b87813622c11401484486e1c98dc2a0c002420201b86a242c2504030192282e171f902b45500525a21b7fb5a7c0030809900202dddc35323004000412a1b761dc080811431504006dd5021e2140400045220b7328a8c8025808906a02dc7cbca204510c544a00), (96, 82, 2, 27, 2, 27, 0xd8df60c08c25038006887619f7f2210c502541220d8377018030480091210360c46dd120100c010881d803fadc20140311822035ef60e32a0c00e460281d77e84848800400400a075d5587c2345100504a21d724a2e48110401410a035b7133a230110c140a21d6daf874c314031052b035b2a668030d40e401821d6b356502515001096083597936320c44004452c0d6528fcc8000800900a0358c139d3009402011a80d5e862a4ac04030082a8756e756a00c550c545840d5af05d82c3503918608755760a52b405001252a1d5552e0828104015800075528981314400c4142a0d53e2b124900030050407532ef8b03004000410a1d4a51f50c11403105280351de01c20d0400805240d463ee9c03150011163035081a1f20c410c5442c0d3f1eb0ca415031186a834ea7f702204200600201d39eb3c208304094004074be8f7490c400c414140d2cdf2520c004304004874ac902b2a0010c160281d29426ec00244085022034a0e8693004200610280d2552fcca114801992a0347441908a04500521101d17f4d58091403111200745f28de210110c140a20d1322f74a101400494a0344624892301100100aa1d108fde0ad0403009288743bfad4094150c125820d0e475d00015401406003433c36e2080400041240d0a8ff342501000094283425de9c295000c824220cfb6deac21148019922033eb67c82209102100a01cf9d56a025100010900833e444a120d000c8042c0cf80721041150010560033df439f0a44600665081cf0475c228304094804073c0237e210d402441a20cee5a304490103005420739c62c91090200a100c0ce52f6e82c014305840873920f37284500c464a80ce4012c4281103108420738adc36084050c165000ce1a63702820408480007376f5d42305400401a21cd9340e02d04400492087364165e0a09202260801cd79d7ac241403118228334b99d3200950e141a80cce732880d0100011408732303b2208040c041240cc83d654a035009086a0331b98108a0050c121101cc24b9c82015801986003306f8491208202210081cc19a5b425154314962832f68e30020c102500001cbc70e2424050000862832e8aef2204000c044200cb4ddcc02d040000920872d03a6d13104008110a1cb2697348d01000014a872bd836a2300000040221cacf41b48901800814a072b214900340500105021cabace74c911031054a072a210a08b40100124121ca7ca2d4cc40002040a8729dd760824400c404101ca5c5340831440141290328cd454020d502501801ca02da74294100209420727ead708a0c402421101c9dd34d2421080184050325447220841000064800c922c0b405410020142832480dc2014040c045020), (96, 82, 2, 27, 2, 27, 0xe7bbfb28a5004305908839e8fc4c034000c004021e78b1cf8a4210081848839dadc1d224400c404281e760de8c8c11001104a879c9c0f03205000410a01e71fb954c110031050a039c3fea10840600225080e703c7e8a4040301828839bbd364108d402411840e69bec04a041032084a03995fdb7280400c460280e5f3cbe8811043151080397b2d4b23085021412a1e5ad16d0c504000052883967cb722901400061a20e56079948511031014a839474059320040c011281e495c8a0c2108018409039221e2a208010c140240e487e86c8d05000116a8790768589200200210101e3b580e443400020503038e58a270209202240881e2e1191801010001140038b559100350000804021e28ffedc8235009106b038a0f792034150c145821e22576208c2440840288787bd98a200c602641200e1ed09a4c104000052a0387998dc0208502101001e1e2bc88080443050200786d7a9c2309502101a21e1a6b0bc8020808900a038583693210500c440aa0e14dc298a9104015908078505c293009002010a80e13ef32c201080198020384b60783208602211201e0c1e5500105400416003818dbac2041500105a00e03b5ca42c1403108228780bca482304100500221e018594088304094008077fdb1182041100104a00dff2205021410020940037f0f5208a44000424101dfaa4eb203118018145037e151100a40100124001df360f5c24340091822837c3d8a8810c102500120df04dc24c900030050a077b8c4b03140000014220dedf41cc8800400500a0779e26fd124100c014881de686d780115801916003773f7822144400445220dd82193c8d04030112a8775113170245400445881dd36ecc42c304094802877490f1d10c44004150c0dd1ba9c88101400514803741f3e41009602211800dd072fc88c3100910488773aa3ae0940100164020dcca71a0411503105600372ad04e230040c041221dc6f55708414001002883713bea40085600601840dc302de48300030010b03706ea85224010c104281dbeb9f1208004004004076effb5d0b450004248a1dbb7b41c8c14431502a876ecae5400c5500505840db34ef5825040001920836bf2be20a0100c060801dae72c6c2d150011962876b89dd030c5400415a40da9b1d0048050300460076a3aa45310c0024102a0da84fad0482080884000769f8d6d2245400405a81da3f1030200440048200368e83860b40400065021da317a2c8415431506a83680c1422344400445221da01b2d420000000802036796a7c0a05400421801d9e3a1a4241000108028367659110845600625880d9910920cc24008042887659500511414000158a0d91b88fc8305030116b036451362230450c541221), (96, 82, 2, 27, 2, 27, 0xf73ca0000411401404083dbf8b30334540c415a21f656534c2805030186207d92131d0b4110c1248a1f60a3b948300000010b03d7d0ef60845600665800f5d89d740111001014203d75fc86004540c445800f5d0f4188411401504883d737c7b2044500545280f5a6d9aca104430592a03d478db0084010c124000f4e7dab48240002000b03d31ad3a004500c444800f4b9fac24d10031050487d26f3f8008d602601840f490ade00240802800103d21beeb0805500561880f48361022401030084483d0a64180b0d102520821f3e098644101000054203cf57d0a210000c040220f32c711c2505400596283cbe2016094150c165820f2eae51c8510031110a83ca69f84020c602601001f24937a80310431510103c862d708044600605100f2129b482914401592007c8403c220c140c045a40f20c2ee88001430504803c7fe13b0a4510c564881f1fa2bf02940802890007c7242eb034150c1458a1f1bc49a48905000016a07c6d40ba2b4010c164221f1a4f55c0c05000106287c65beec830840e001121f18c0ab02415401486083c625df62005200640a00f1819f688d01030114887c5c50f41209002010801f15f55608411001004883c4ff96d304040c015280f121f30c2c25008186287c417f5f284150c165a80f0f34e344840002040207c3a0f150b4050c1250a1f0dced40c515001056883c310e093201200210a81f0bdfa744c14031042287c29e91d0841600225880f07b1e1c8214431502b03c1ac9e12041200204a80f06945d4c901030054a07c0990c520c110c104ac0f023cf982910401590007be4452100c00000040c0ef82fb440300030010303bdbe1a00140500105020ef6d7f9c0114431512203bd62981234040c0052a1ef0c926c8904030112a07bb4f3dd094400c4240a0ee143e10a901800894807b74739e0344400445021ed9a9bd80301400514103b4673042308102100221ed0886e82405000186083b1b02fd00c54004058c0ec3161b00240032000103b02da44120c402411001ebf964620900030010407af57b6c324540c415a01ebc74174c211801844b03ae65bc120c500c404ac0eb779a68a015001186803ada92981344400415021eb4de6d08810401400807ac3f57f2141000044aa0eadf46c24c21008044487ab1cad5084510c524880eac2a834a835409486a07ab077a1014440c4050a0eaa8f4d04005800846003a85410a094010c164020e9fe054c8310401510b03a6f042000d0200a04040e934c1740940802810207a4cda3703055005418a1e8bb45cc2815431586207a2c6cc92009202200a80e865d2a08114031012803a0d03f40208102100001e80b70acad05000196a879f3e3722340000044221), (96, 83, 2, 27, 2, 27, 0x83e0324a508081804a501074c4044c041802844a020da12d41980806008510c1b28ff51010200a1008083406bca2120001020181067df98209104014104060ce2d28182090010a5004174bd1a200020024020082e1a9c414880008c800305b985e800214085040020b4dc6381868812a0450c15854fd13454004158a18289ec5854a080104a40304c0f628820143050490208e7d9484222002128404118748103504008050a181d089a254024004415030362eaf8891403111280606bafdb1120000022100c0d5069c2b40400025221818e34d2408280000b5010300b092291100109440605fa60e8000a80080c4040be130c0b0550c521821813b50cc521a0048c14410256c2448835409406a060465c8685a2000212050c08a2f28230c50250122180fa8ed40080a0028a0010182dde441400320502020294ce21488200410910403f15da20c5400445a40806e2dc1101020424020100ac475c8d04400512a8601345c60906101308000c01c05be0a40600265001803348d4161a0048c1043005659e0a82040848080600a6b3e1186081280110c012269500800000000c08011483202028000031410018765c0105000116201ffa9ff90022a00222c003ff0f16890c40004141407fd14f42418a218a09580ff845b342404000082281fedfe6f81a0a06022c50bfd297e3080900e0608807f9ec806101001c0c0100fefbc1324020008040401fdaba180520880092400bfb4f128020c5025010017f5e697a40a081900a500fe8986a80225008106101fcd1bb848423003088a03f8d2570908400c4101407ef2d2b10408c00c02202fddec57c0430409500281fb707a418a820040a9103f63ef5a214440c4452207eae2e822200800022140fd591bc00311031014101fa2754241a0200002890bf3f78e1014550c5058a07e64fe44168a0188c9042fc49dc242c14001082285f88cfdf90060812a01403f00c6cc211000c8002207db7f7e1011821ca00280fb6036e22001430484401f6a23049120800002540beb9bc9b034100c0448a17d6643a04180c0040a480fa8e38a48804400402a05f4ede1244060012100803e9819d728446006652807d27a854108a8008cb000fa423a60c914001052805f46e31408a2a0020ac103e88fc3008054004218007d05c8da4680018008542fa09cd044c20008040285f3f53f994a02860b29503e6c2684330c4024112217cbe3c60261a804823042f965f1520511031014481f2190990504101130000be3542bf024050c1450817c424efe508a8008cb500f83c4418a025808986801f03530914a08860b25103dfeff3d030c0024000a17bfd65810608a18a02242f7edd7048305030016b01efa332f9580800030550bdcfc0ba090000c060020), (96, 83, 2, 27, 2, 27, 0x8c9b2a280288218a0804118c5c4208c110010048863115f6e0586a87290c10c61e0cd9308c2026102c08c2e0dfc0100400480081183496bc0005400506202301a5bd906280022256045e6a0e62a440004642018bbb2b422488c00c2a1031770199884210081048822ec4004080830050880045caf04b2a044004612818b903df80120c01402081171ba6c40d140310122862dfc23191200860a2140c5b7053c908000c0101408b547929160880084224315593634c800030040a062a7ef6c91a0000002150c54e221931444004152a08a9b71391688000848243152b09b0c4410020448822a349291406001230100453ede4d08442006240808a5f65f6448a81888b50314b3c08442208088403022936f0011a0a00002d10c508482c2a45400425a0189eff1e0018281800b08113cd1e48ac04030182886276b3a41804a01008d0044d36cd221044004412208970448c0008c00c82001129c5d62090080081040624ceefe9820a0000ad404480e0322b441005642218900f561010021820028111ef1d7c8104800912a0223dc8680042900300420446d69db020060024108188d44fa86482018029403116742c82034809982002229e3838580200030850c452e92a208000c040240889bfb3112080188402411121f832021043140050221fb7801062886282520443c202a08002002600008872c1941682a182cb043109ce52c2115001196202200dcaf0184a07020c10c3ea30ca00c040004504087cfe9100008c00c020010f550c18a9100311908061d848448522806212440c3877d65284110c124a808703f8b81080a1824a0010de5e8dc29104315902061b4e3fa9088206400950432b680f214500c444aa08641bbd92488400c282030c601168a5054005968821755b5a1402a00210d0042e94ae930c400c4142c085c09964168a0008c90430b6ca4a4000180080420216c3275106220022292042d28f25230c4024012a18598f23a52822182495410b1929d4281400108220615d3bc0984630130896042b365e800d000c804040856275aa02200010001410abe74d4430103005430215346b2892830050a840c295efd7224050c145281852666ca21800180281810a2aaae8820480090290214148b21480a00010d1042823d7d2250600a05281850341da640000002050309fe9d4881100311108021370a909846201208960426d4f3130804000112c084d7fde850a081904a4010987d7e2090100001440612ccfe81506301310900c25342112a09102120a8184837044061a80488304308f70f60284180288400611d7d32886230030a86042323c8c13414000158218436611856a00010484430863a890a80500008680610bad2d8020a800a2c4041fe2b902a0c502521201), (96, 83, 2, 27, 2, 27, 0x961da1692408c00c222032b93b930c50003005088256d149e4180286080890cad628188a4450c5251019589af8e448a400c895032ada0dcc001540150620255634d219a0a0000ad10caaa25c000c1600205840955288944082a0028b4012a7da0c48111031014a02548588584069013304404a8887452a09502121a8194f82951060020020024329a57968251400119208252c5f939522b00332d40ca4388ee2244600645201944d5382408081800a50128662a448010801800a024fd6a2f002200622200049f8bf3d094110c1248a093dfa3741602a002c304327bc7a0828010301840064f413ae0506281290800c9e167600a0d502521801939e88704182218209481273cf8204c400320400864dcfb3c04a008009201049ae7ff52840200224280930de4780180c0040a08125e980eca014001182a024b66d4310a2006222110495c90983001400011a00927dce5a542000104050324855344c101000054a0248bcbe48068206402860491570de230d402441a2192237f88548280004b40324009b304305800856102480100d91a0a800a2d50c8fccfc5080560062188091e68cd00420c0140200323c397204c400020400864761e680528200412800c8d9e01f2a0410c56028191af568a4118004800581235a74dc8811801904a06469fa679182000220150c8cd459f280940e061a809182eacc048221828900322d0dfac08104315002064524faf0420a06032c00487f47cf2b081021602a190ec90960418c04c8210321a9265ca821808984a06430fe6691a0800002550c8507a660a4410c564001909ce54a018a0188091812135bb148021808804a0242575fc9180086080150c83076002b05000420a21904982a12408018820203204da2fc8914001112a0640801a494a228629295047fdc3ea01454004458208f8867b921804004282811ee5edac25114315942823d5e2c04900200008880c79a8bda014540c4458208f308ff91288200a482411e3b6ce448350090462063c00f34986230030a960477bb64508446006250808edb871e0182a1828b1811d9627b003158018161023a2020004220862920004734f99f2085500541ac08e67050e508aa18acb5011ca2eb3801114015140023920b6305a08800b2410c71d450f20c450c5452c08de6a99e400aa18a835011bc7072c201443158220237607178104301120840c6e58340810400c4001208dbc2bf2668280002b5431b4d8d120810401400406368b97e842008609204046c8875482002002001018d7db8a860a04014284011accdc54c434009042a8235855440580886090410c68741a82a1000c8202018cd706644400218280403199b578c8305430516b0232cb8f88062086282060465471e01210600a11001), (96, 83, 2, 27, 2, 27, 0x9f16cf0c10024004c10013e2cf0f4c300030050b027c2723184a00860b20504f82c63520c150c105ac09f04ced110880008482013dc50d4800318099040027b28bb480a0a00002c504f55086b2a41000064a819e929f32108881884a1013d0a82580c2000810008679d031e99a000000a150cf318bfc124000c0140019e5d2e2901108040022813ca343580c0403010208678bee5b81a22862a2850cf0f87f40b0d5025218219e170d20120a8008430413c013082241000108048277ff26a9522006212140cefb231d00045005010809dec9e145008200ac04013b9017b82d01430594086771fc6190228802a25404ecc0a4801094020018209d8fb378508081804a4013af886e00941032014006758ebef91228862a2540ceabe0442a402002242019d3acbe81000c004420013a0e2a948d15001016a8674088f990040870a01404e688edf290d00e460aa09ca9d6b066000180204433947d510031003101010272730b385822862b0850ce4cc83c88041005201009c995bda620880082254138ef45b80514031112082718f0c38500300130840ce28132022444004052019c191c9841a040140848137eeec38a9118019948066f839b81060a80082d204deed572234440c4452219baa69b81202a00243041373d16fca914801992a066e450ac1180a80080d10cdaba7c8209040c8012409b17154a268080002a143362a99000c214384040866bf91cc84281005120404d6ffe68215040c8052209ac51efa12a00010481413552eb6403154314163026a86dd315860812b0110cd40d17d1250200a140819a7f1a56028a01888914134f985e0090003001000669bacd884003001108404d339ce80a012002208019a584508261200402104334a861588205030106902687f67e99a220620a950cd015b50324440c41520199e9723e52180048c0541337475c48231009004b026654e200522886292400cc92b1ae280d602661a0099204bfc001a404c8100131de22802d140010920866362a9a1900a00008d00cc6c2b41304140c015a8098c6a3cc120a8008c30413173ec3429100310902066268dd418a280020a5104c36d0903200600211201983668524180400408581305c9b424411001044482608410b10a02860a29104c0cb0488084200600140981014085608000840443300fbfc880218089048025f2329d91a0000022150cbe3868930900008102c097c170e066028000234432e41b75403118018143025c322b10520800032400cb8269da0a4420066400196fb8de04420c014024032d7cc40ca100800990a025a9f2f240820862800904b49e5d010c060021504096852ee2208ac00c2b1012cdca1d8a8158019868065970ed0992820040a940cb1767ca2b4100c064a21), (96, 83, 2, 27, 2, 27, 0xa8aa3e8c4208200a80441513933d00941002014006a23071b05a20802b2010d444a79d3208402011281a859a350410a800803481508680324d00030050486a10c456086830050a82053f00f180840500125000a7bc92be011ac04c831814f614fd448310090442069e121388504081090040d3a0f65e0845500565800a73fec7824a04014280034dae7cd0a504430492882990177c0480a00010c1052fcd8b7230c1025402a1a5f1a1c8128280004b0414bce9d38841500110688297237d81402b00310d0052e43f9c0240600205001a5c28c885688200a484434b6dd0eca015801986a0296ce4a10020a860a2c0052d3304e0809602261800a54c8a7a26a081902a1434a83c5d00d1443141208694cfb169088200400950528135cf09084020610a0a4abcac2128881884a14149532fe4ac10401480a869225430982220620a9405234c51b090400c4600a0a457e4f8122001904004148791474c814031042a0690b3d664186201200890d2113d320804600661000a3dc149c16820000c904347a246648c20408400a868ef30dd14228802b250051dbf93e2000500141200a3a747924408a00a02503471e77cc02044005023028e062cb8480a00030c5051be508c8a04100520101a3637284428220028944146a05ae02d114014940868c3a4021586801210510d177c0e93245200614a81a2e7a1de4012404481501456c55b20c010000044868aa958180423003208605152f63300890020408c0a2995e520082218209101453148a8a0150311868028a38bd91102900320500d14686e92050600a05280a28aebc8661281c02344344cc13c88c0503010688688e68b08002a80280c405111904d210c0024002a0a21a5b62468a81880b54343d1aba08114001012802877871b94228862b254050e4e6b3010540c4418a0a1c05ffa20200190201014374e992211140149440286e2e08004220020082050cf69fa094050c165020a17b60604680a1820a44342b0713000114014040028557a819182206220950d0900e3830c100c014a40a11e1591261001c02024342204850004180280400283dd7f88904901108440d07abac02a09502121a01a0ed1e9e018a81888b18141ac6d28243400918208283391b10062900322420503e79ed2a4010c124281a07b503a50a0c0144a50140e3aebc041003110028281791d24506301310880d012141709404000650a0a01e9a701288218a4804140285c6c8315801916b027ff58be10220062021004ffb4d4520d0200a042c09ff4577446880188884433fbec8704c300090400867f33f9b04828802b04104fd9d05b090540c4618a09f6565fe06122042811433e80e10081050300168027cd1a6f91200800a2140cf946583014400c4440a0), (96, 83, 2, 27, 2, 27, 0xb2ef79ce441221c28150365a32e64a141032094a02cafadb218a200620a110595ae5622000600241200b299bfbc1082a182cb001652cc210c304000052902c9d633114200860b210059392e4d2305000400aa1b25529e850a080104a401642f84144211001044302c82d8ba01a2806202410d9023da7090140c0618a0b1edef94568a8008cb44363da3558a421408584882c76b64295a0000012150d8b1b6cc2801600221a00b14ccd00108aa00a4b00162803ce42420008080282c478d048908006408040d876033c3089402011a40b0e6ae7c448880088a40361c8f7682d15001196086c2f76e49100280080940d8498c688040600205100b072e300108220024900160e086b44314001052302c1575f498a280020a5505823c1508904100520120b025b6fc14822002c9003603e8270cc34009042886c04ebb58080a800a0c5057f6f3ab0841500165880afca30ac52188048c24415ee656588c30409500886bdc1ef01520900112500d7b4a8d000c5400405840af614ba416888008ca0435e6f9fb88c15031106886bcb8f028122806202440d794a0d5130c0024100a1aee6fb2c0218a04a820415d2c61d04821008044006b91de32092030010a800d713a1ee0840600265000ae25496401088008820815c2b8af82425008186082b84f7e911a02860a2910d6f2056d2850200a24280adcc31bc44802182884035b2fd8d24801030044406b59c2769180a86080d50d6866ceb20846006412c0acf508a8428a218a094415973b49ca110801990a02b2dfe6c8022300302840564850c10204600601081ac826ea864a000102840358e27ce40501000014282b19f9789984801008550d63160113245600615a81ac58e07612808180ca1415889beac8c05400506a86b06a24c18a820640a91055f6bdd20a01200260801abd163c101104044002815791cd440215001006302af0ed9c0188006400010d5db8e3d2044600605280ab985c82528220024954156bc2dc88405430506882ac2a7644186207200890d574fa02010d402441820aad73ed9011001c000281559d0438a500030190882aafad270502300330800d5584f7030c0200214240aaa3b9191610804042243552fa6182d15031196086aa5816591a02800a2950d53ab40f0844200664080aa56d538241a404c210035497468c2401000184282a8744ea986080000a56054fec891005040c805080a9a4c8a6548a8008cb503533e6a122021408484402a64133b9080a860a0d5054c799791044400415080a96734f9200801882020152adb8622900000090406a51038a482030010a880549b8214294410c524220a905cf7a608a400c2950151adb0548421408404a82a312ef29802a00208d40545d7c3e0b08102160021), (96, 83, 2, 27, 2, 27, 0xbaea22010180018008281759bbcc82900400590006eb30e3f1484a810b0d105d631e4a030550c541821baac71160418404c8010374d3c6680501000114082e95dc7b94220002321405d25216c8208602201101b9eb859e021080408214173a915f80235409506102e6d937310208060225005cd404c53204400411281b9a0e1510010c0440220173292af4a110001090a02e62b21c0984001008010dca98b780905000420820b950afb11008a00a4220172823f20c341802854902e4fdfaf9502000230140dc9cf87a2945400465a20b93780480412a0420300371dce610a811401484806e3b247c10203001029005c7224483010000810200b8bd584c1282a002cb041716821f42914001092206e27bb578004b01120c405c4ebcb5104500c414880b89025940188c00c8a08170bf0a142d15001096286e1501de192810050a100dc24b1b110d000c8140c0b83f5fb060a0c0142a4017078d9f0c904800852806df5ef5b10808800a05105be413b48204200600101b7b683aa008aa00a0b1016f6a94d0a400000080882dea04649906901308540dbcc9eba2a0050c161201b794d8cc0110c044820816f274b388304400512902de44a188106081280040dbc85c272105500541aa0b74ecf3c568a0008c94436e4cf340ad00000090886dc2a6204186007200090db854abc8044200604100b704874c50820000c94016df499708814801802806dbbdf221986a01208d10db6ef1253209602211a81b6d58ca2068881880a1436d9b7038ad11001194886da852a40984201008810db502b6c2844100524200b69a0b09068081800a2436d1c9f98a804400582806d9f9f6710000860a01005b3212c12045500505a80b651a506148a400cc91036c3e307c8515401516a82d860d8d90848810a05505b0334320100500141020b5def16a248a81882b1036b4ee1f8a411001184882d5a87da8586801210450daac5ccf2b4050c1652a1b51e810261208190225816a0840b88305430516902d3eaae088a820040a8505a60cce22208502141201b4a2a938460a218a0144368f6f3d88100430510802d1e73af05822862b0810da37c6e3024500c444881b44cbc1841028000034816885b4ec8d04000112a86d0a06c208003001088005a10b648284150c125a00b41d2b50461a204a0144367ffb01c2c34009182286cfb147a14a220621291059eab04920904008012c0b3d51934508a8188cb401677dd7140340032010302cedf6810406b01330c0059d3a80c234440c405221b39f4936011a80488318166fd16722500030090482cd54deb8504b01130c40d9a65a09224000c004281b332bbf4060081808204366610a820c20408400486cc8aae394000860b0140598d756d3010000810280), (96, 83, 2, 27, 2, 27, 0xc2b3ee6a20880188281018565d63005150010160830aadee0186220020a920614bc5a6034050c145021c2764842428801880854184e7a73cac34009182a87094ad401128100502100e125f15800d0600a05040c2438a6222a081902a141847cce802c4000208008708c3a939580200030950e0f47cee0085100540840c1e4a2be100a8008c310183c23f248515431416a830783e0511202800a2900e0ed5f0e2144000444220c1d5e2cc568aa18acb4438375a02c8314431512b0306d3a919020a860a2d4060c6423e2940100164220c164935046a0019008443829ff754250540049628305213de81a0806002450e09d7f9a2005500541a00c1379fe24610004000543824e6fc449100310502070413d4f04200860b2000607bce3d220c602601281c0f3085c1000a002c200181e2db282d0503019608703c0f3690220002021406064d39c3101000010a20c0bee12c12020180c10418127bf9403050300163030235a549020300102940603ebdf5294500c424aa0c078ebd20408a00a0210380ce8254a911401494a07016ed1c0506881290400e02a1b440900500121020c048d8890480c0040a2038077a534c341032054b02ffe6c3414a82004129105ffc21f30a0400c460081bfef1584008280008b0017fc0caac8814801902a06ff4bff89106081280140dfe679180a0c602621001bf987e8a0280a0020a1417f3043342040032080202fdb644440463013008a05fae65612009502101a80bf45318a0080a0020a1017e6be4d08114431412802fbad4a905800800b0010df6ba59f2a4100c064a81beb41a9a528a0008495417d4ee1ac8821438504a06fa958d594a22002329505f49a0de2801400061a00be7038cc460a218a814437c9ce5644341802854302f8d28289900806008540df15c8d09088602211140be123c7416800000c80437c13e07c0411031104282f7ee0829904207008940def7077a0089502141840bde887ca548a0188495037bc5be5c8301030114b02f770cea94009001105405ee4112c0b4110c124821bdc3164c46022002814437b81138c2105800996202f66ad6c1904b01108d00dec4e5500141500105820bd2a807e4488200a885037a4a32220d00030010486f2623501980200008910de45993200c400c444040bc869d56168aa18acb14378e563300c20408400086f19195510a00060221105e2bbf8c3310400811221bc3f5312208281802b10178682f488910001110806f0b1de50522800232400de0fa841214000c0042a0bc0f2eb4048280008b003777211a08211401404902ee1611a80622062028605db0f967034540c4458a1bb5383564110c04482581766013744310031050302ebd852290208860825405d786bfe004510c544800), (96, 83, 2, 27, 2, 27, 0xcad243985082200249401959bfbb48914801812a072a8103689a000600a050e54ffbce2081600241a40ca949d5a661a00482154394e5ef2ca024438582a0329677eb11a02800a2910e518471d210d402401aa0ca02f562240880082210393befc00c401000044883277259c1586a81290d10e4e7db440b40500125021c9cf17f6048281808b103934a04c0250443049208325ab549102230032290064b3b7392a5000c824281c92540e454822002c940391f2e092421100104450323c4ce008023003088006476b2ca208c202640240c8e97bc22088c00c2a10191cb0604ac05430486a8722dd1cf9500300130940e453b1ab2044200644280c8a5c6d2600a0008215019143ddec240543058628321f08ad900090012054064343f2c2a05100520a01c86603d6508a8188cb501907b8770283400908200720f65d88586001210050e3f0bd5d01500008040a0c7d94466020aa18a831418f4b16fc01058009162031e5a1e71022a00222d0063bff08d23100008002a1c75a5de2611a0048215818e81bb680d004305100871d01b1848003001088806390de2130c5000414ac0c6ed53e60002c004831018da171e083158018169031abb49b94842870b0950635611b700851005408c0c66440a920180048202018ca9764c8100430510a03191995394202860b2940630d4db42b4400c424221c6103a2a108a0008491018bdef5608900030010807179a4150500a800b0c00e2f1421c3201200210a01c5dddc606112c044234818bae0fb42c34409482287170c0ca806008008206062e147b7014440c4450a0c59704ea50108040425018b1f7cac0c3040950028715d02a09184281080950e2a8ce4b21404000452a0c550e59c10822002c90018a9b6de4c840002040a07153093b91842870a0950e2a5149b2a44000464281c5432c284000c004024018a78c370820180080490314bb59115042810b0900e2832f252850400825280c4e73aca410a000801581897895508c0403000288711f875790002860a0940623aa53a0840500165000c45a5ed652080008c054188a650bca431039184a8310cb2590506101330000e2145364324000c014201c4249aba4612a1c20354387e58770c8058008468070fb009d11a2a06222d10e1f3ad7d2208202200281c3d9bf5a6420019020503878d0180c3010300549030f00375102290032250061d72a16034410c544021c3a0c84a40804004085018681f580c0058008468030cfdf1e4122286282880e19e0cb43204200610201c336df4e411a0048815818667696ca410031180a830c2a7de4500000010080e1795dd301085021410a0c2ecd022648a00082950385c0264c0d010301142870b3c02681a2086282050e16099592301000000aa1), (96, 83, 2, 27, 2, 27, 0xd2b679220488018808103a541d8922d004304904874a26a9e440600721008069420f7701014000418a0d257ba164602200281543a490ce4c8d10031110a874916baa9880a00008d506921f406004550c545800d23b3c404100400400481a47056bc8915431516a0748724bb9522806232540e90de9c49004400411100d1fa87bc5488400cc8403a3c5707c8405400506a834771f3290a080600255068ed03c8334000c014221d1d11b026682000029543a3873340a51003109088346c5e3110008800a050068d873b4114500c414820d19704e0410a000801481a2f6f9640c2400800228745ab3d88184287080850e8af92b8121040c811001d1448cea24a0019028103a21cb7f24900800850407438ab7884a08000124506867da6700c56006458c0d0cd57b6008ac00c8b101a17e93820901430414407429e7148584881090450e850b45b2801200260a80d09df5921008400c40101a08bd2542510431490283409afaf00a28862a241067f9d7cc3001000010a00cfd771111288a00a4a2419f9ef5eca420438580a833e6061191a00860a2150e7bd7e3e00c140c045840cf187cf826188048220439e3057d083054304169033c54c1c4404201010880677eabed324500c414a81cef72f6604102042801039dd7068883114315149033ba4b830122a00222c00e76fda7e0945500565820cedb519852108040424419d73bb6c04310091042833a98aa414a0006012110673950c910884020110c0ce69d7f8408a81880b4019c4d8f144314801852303388ba1b0500200030800e70c830a230440c441221ce168da844124044014039bf1f0a8240100018408337d1e7f80408860a046066f40e442345500505a21cddf6a861408400cc01039b8cbf848505400416a833702a4e982800640a14066dc1b9d2a0c402421281cd931ee80680a1820a0439b1b56e0890180081480735d4ec50082a802a0c1066a3348c030150c101821cd45d080628880082a4419a819a98a50143059488334ec9f79106301320940e63d4748034110c104821cc7450d0041220420100398dee6f2401080184040331b9c5f1004a810a0d00663465a4234040c005221cc65cf54100a0008c100198908890cc4003204088730f7b1d9060000022160661aa2862144500545220cc3285fc0188400c8808198325c00a1400320908032fc9cac0522a80292c00e5ecab43034110c1448a1cbc93fe02182400429081974d252885104015108832e1ec198520900132440e5be0a20335000c814221cb7a28281208800842041966dff9224114014844832cd33d244822002108906599f5ec2004600601200cb2f5e68261a81c82304396401e5085154314168832c75f5504220062320006587b32f2241200244a81), (96, 83, 2, 27, 2, 27, 0xdbad59191010004040201b729eb5220210380844036d6baba80203001028406d8f80740809602221800dae10a56001aa04a83101b5aac02242300390405036b4e7d614228802925006d4eb523210c0024402a0da88cf0a1088000848101b4e6a0148824408402a0769a7bba9902a06208d40ed29e8972841400065a80da325b88061281c003043b459a1c8030580091610368479271504101130100ed08846a2204500541201da0f80fa0120801002181b3c6100c8911001114a07675fb8e99a020600a950ece47671030500c4008a1d9b1472e50824004c9501b2f7d668a901030194807658b9d04522100312080ecb132932905000460aa0d957ce825082400449501b2a5ae440314801812303641a49e80a22862828506c6617a6094500c464820d88cd3c12600800022243b0e72240a80040048080761c295200422802808206c34f8af2309402041aa1d851a5592418c04c22203b0317a9ca421038184a835f4325180802000208506be50e0c2a45500525a01d7bc49144082c0048b401af630844c100030050a035d74eb99022a06222d406b9fd061120c202610081d723aeee4108400c80581ae4475f82d004305900875c6000f1522a06232d00eb5f0817220c202640281d6b8b3a81488200a48003ad5aa89c2c300091802875a9173710a02060229106b4f39012945500525aa0d6943c705618204a40443acdc93bc021540150630359844e640222802828806b27dd90230d40e401a21d63b8ddc560a0188c1443ac6dde12420103004450358bf6bf90a28002225506b124b7320c5400445ac0d5db6dde048a81888b103abb2ea808d00430410887574f840986810050a1606ad73a76034540c445821d59e6a086418004820403ab32f57c2515401596283560c4c59422b00332d406abbb4b22a00400061201d56421481412404441003aa99c264010543041620354e2e5494842810909506a99894e224050c145201d51f121e568a200ac9543aa27c6b40c054304062875427eb304068812b04006a8096ed2b4400c4242a1d4920d5a0410404400103a90eab44ac40032080a8751fc6d484a00000120506a2cc9a20a4140c065801d452db9654124044c1503a892a5c48314401412b03510fd94092800040a000ea1eadf12045000404a80d3f31b410218004800241a7ce866c05050001162834f637b6408220020089069e8d38529401001242a0d39019ce10824004c9101a6c9144420140010822034d6408b1020a00022d0069ab698b294110c164aa0d3535d8260a0001028501a67de4f4ac14001082a874c8b1f215a0286092910e98a7e6d2004100500280d30062fe4212004081541a5f1f42c01018009142034afc4ec9806201208940695f52a0309000c810240), (96, 83, 2, 27, 2, 27, 0xe4202edc52102042c0441c82cda80a9058008968078fd094705222862b2800f1f9c56e280140c061a00e3f05c81041821ca00203c78c83d04d010000540878dc34d41580080090110f1a4fb7b00c04000450c0e33eeb81161801c840243c570cb308c350090068878a8a2400044a81080c207146a4dc810840e001120e27713ac028280008b041c4da677408308098002078989d510080a00020c10711ca3fb2a40600265281e23920d86008c00c22401c45edde202014004045038816f7304a000603201070ff4a2e0104400441020e1fba64826a0001028043c3e3a76ca505400596a8387c24de9104a81080d40f0d5e529214500c404aa0e18677aa6100000020581c307504ca400000180a83858fc8c1822a0620ad0070a304af20c1600245ac0e105a7291000400440201c2048bb4a510431490a838384e461904a01008d00f05aad2f080c202660080e0929c2456880008c8443c120e6fc8434009102a838195f3491a2806202550f00059c4830850e101121dffeaed06420019020403bfdcdbe08d140010128877f46a4b1062a06222d206fdb89ed308d202610ac0dfb5a46e10822182c9101bf3629920c100310004877e48d660900a00008c00efb11b0923440004042a1df54411c12002002c0041be8a2d1884050001068837c7df8e98008000085406f8daab42b0c502521221df0e9a224112004001581be140a8240210080444037c1f1a18484a810b0c506f62cfc2024510c544801dea9d16e421aa04a83541bd1c2c6208114314044077a249929586281290950ef41ed87080d602661880de81ee311008818842201bceb79e8a02400818280379a396b1522800232500ef320709024440c405081de2a4c400412a1c203003bbf315d0051540141608377cc39c1920a0600ad00eef84598230d502501a21dde01cb6008281808b101bb5444e08820408400807768b3101980000008110eeabf6201209402011801dd546560248080002a003ba9a701c020543050630374ba9021100100100100ee94b1aa280c602661200dd1fa5b44412a1c283403ba0f2970c84180284480773f20c314049011305006e77b6f92841000024a80dce82dca141a81c843103b9b201122c0040048048772b45509182a86280d50ee4f793d2085200600ac0dc9b48aa0108800802181b91ec2ec03110311143037236e0115000800b0100ee43f3a7094410c5640a0dc7848391008c00c42201b8e13b2885014005148837162eab04021003300006e2a78f0808c00e400140dc3fa8485282000049441b85687e48815401406a076ff85cb80003001208406dff09fc0a0540c421801dbeba76456022002c1443b7a79b6c8d14001112a876f413f00180006000010ede49fce0a4040c065001), (96, 83, 2, 27, 2, 27, 0xed3d58211018204a40201da58a40c2401430584283b4add8644002060108807673f508294510c524a20ecd996802182000029081d9836d4c2514401592283b2fa1bb9002b00320d407655852c814400c404120ec8a5aa45418204ac0403d88b47f08114401412803b11649e04880004100107620bf1301405001450a0ec1a0fd2428a80080b541d803213ca421008184a83b003f4d1100100120100f5eb90fb2101000040aa0ebcbd02450828180cb401d796f764a510001090a83af2d4869840a00008d6075de11408a40600225101ebad4f010488400c08203d742d7e02d01430494087ae4cd26980400100814075b6b1160240400045001eb66dc625018804842501d6c469c4c001000044a03ad61fe8884230030886075a86de300c02002440c0eb301d920280a1820a141d6469f608c21008004887ac29d4f1022a802a2d00754eef7c2201500101a01ea758dba0480218208103d4c5f334c021008044a03a8f60d41062a06202d20751abfe70845600665880ea3057985288a00a4a441d45e907c8314401512b03a8b505608a020000a810750fd72329004000612a0ea075f904612004001443d40035d48511431414a83a77b8169402a80290d4074eabae7090c4024610a0e9a2fb1a6402000021503d32cc6e80911001114007a5b7f941128206402900f4b175400a0550c521801e95742804002200201401d27d4b020310031010503a4b82ca192830050a900f48324f80844100524000e9056072610a400c21581d1254b0ca005000186a03a1cff729920a0600ad40f425c300134440c415021e838937e420a818883541d06afb8ca515031196a83a01f78b1186801220510f401263b0244600645081e7fec2a05402400441403cfce86bc8901030114a079f7f6a7806200022206073dfc9640089402001840e791bb70610a800823481cee8d8e884140011028839d683329106281280940f3aa0e0d23444004052a1e74b4fce018a000889181ce634a688c040301028879c79f791120a800a2d00f370cdcb210450c5412a0e6c5cf66421a204a81541cd5daecc8d00030110a879a32a5c81a0086082050f3449dbf208540c441ac0e66dd90654000000c0503cc7f6f988d1500111688798d406c1500100110100f30bdbc8024410c504001e5f9dd5c5680a002ca443cbe6cd482c3000918008797b0ba194a220623295072db5988884410c524100e59e892e068881888a143cb18f6f8a900800990807955e078084820640882072a8fc262a0c002460201e5338206400aa00a83501ca48adec09114315142079420ddc88040010080407277ef17030500c4408a1e4ef4ae40288018888041c8c295a402144014023039124fd618082004089007212194a024400c444001), (96, 83, 2, 27, 2, 27, 0xf4fc5df25088218a48501e98bd2e0a001400484803d3055de94a22002129507a5fef900250200a04001f48643b0461aa1ca03443e8e855242800030080207d1654624186001200090fa1bc4ff0a44200664081f4316dce12000180c0141e80e3d480415001106083cfa118385000860b0040f9e78d122b01000060a21f3ca71140480a0028a003e78b31642040002080203cefc65e442210031208079da62fa0045500545800f3982fc85480a0024a403e71fa078a004000182803cddf76d15800860b0110f9b15ab02901500121a20f3611de64200a00282541e67005580901030114007cc6fc381182000200110f97bd8bd30d000c8142c0f2e513a86188c00c2a481e5b58d248105430416a03cb3388e9060206002960796279943044000414200f2bf95fe440ac00c83503e56618a4a111001094a03ca3971a4106281280880f9439052290500c460a20f264f9cc16100040c0043e4c93e200111801814003c936da311a0800022510f91f9e988804200620100f22a1bf24202a00203541e42f75d0c831809844807c84dcad84868812b0450790993300810600a21000f20425ea1420019040103e3df677c8224008102b03c73cb1f8502a06230c40f89c54a20b45500565821f0ddb8cc50000180c0401e165aca4a825008086a07c1fd8440520a00012c00f83790560901500161820f0654fd2208881882a101e0c62a804304030052103c1830ae9500200010940f82098d12909002020aa0f03044b40210804082041e038d9c48310431410b03c00634304848810b041077ee62d22b4140c065a21ef7ed3fe161aa04ac3143dec89b20cc14001042887bd3323301a22862a2810f7968c362a0040c061201ef24010e4082018089501de34c000a811001084807bc53a808128206402840f77f13ab210400c4402a0eefac5720188018808181dde892dc2114401592203bb947b88062b00302c60777189ff294100c064aa0eeda3a56010aa18a83181dd815564c040032040a03baf1c441048000400120775989fe0145500545820eea1c30e028a80088b141dd38744c8110001110a03ba5e9bc1180006000110f7427dbf204410c544280ee772c6652188048c2541dce6bdb4c310001050b03b9b7f120102300300800f726e39d00c510c5048c0ee0414f64080018088501dbefdb188114001112803b7d613714a280023251076eff76c2950000824220edd45d025280a0024a541db97dda42020008080203b7017e818a020600a91076da96d700c14000458c0edb2f81450802002c8401db5d82d4a815031086a07b6069339180806020550f6be64c02305500501a21ed5f7ab414180048c0003dab73c5c0014431502203b5269e0880220020884076a4acab2141500145aa0), (96, 83, 2, 27, 2, 27, 0xfde01f19061821ca00243fb56ef048340002010b03f5ec36b10048810a05007eb8add5134400c4140a1fd4fa8ea2110004020181fa954910a810801880807f4c790b90802860a09507e8c15b43010200a10200fcff31791008018840201f9ebb57c8010431500a03f3abe2b10422802a09207e6d00693000000010280fcadda06448ac00c8b503f93cd3400d11001014087f250afe18a800640a1107e2add2b024440c445081fc238d40608281802b401f842e940c821038044807f07a7340988200408810fdecab6309054004618a0fbd467601088a18a4a001f779dca48111001014a03ee8646498068012085407dc98f552b4450c5252a1fb8a7bda2410004020103f7037974c805030046a07edd5fca0100886080400fdb75be0908c202610140fb32f47824a081902a003f62ae7c8a101430594803eb7c13094200860921407d6a38bd1009602211880fac238f4148a218ac9003f57c0faca030039180a03eab045e1500806010500fd41b41c9208402011101fa81c8aa42a080100a541f4ebe9520901400414407e9d00bb0502a862b0c00fd3306f0024140c005801fa528c601412a1c243003f4a1c1942c14401482287e8ac89d80008860a04407d1367540a0d402421801fa01b3cc4280200288441f3f5b7a04940032050007e7b2fac986290030a5607cf5d9782b0010c120221f9dd4038448881880a403f3b2b7f48805800806a07e75a0af94840010301507ce484993210600a11281f9a7e26c4212a04283441f3446e800211801804103e6823dd90828802a05507cbef0192b4010c1242a1f96a2d7e468a80088b543f2b98750c901030054807e52349b80068812a04407c9add5b0805000460880f92b6e360088018888101f20833f0c800030040807e41034a04283005128007c7c8d492341100104aa1f8ab7e520220801002141f0d752bc8810401500a07e16bca21988000408110fc0f75212005500501a80f80d3f385020019040401efc6739c8034809902a03df8788e08480004080207be7178e20c550c545a40f7cb1a5c0482c0048b003ef6d279c0800430500207debcbb900a08860a24107b9c3c86030450c541021f724cf02228281802b141ee395b840511401414283dc5b25a94048010105407b7a42bd1210600a11081f6e919024408200a00503edbc30122111431494403db3f07a0188200400810fb43026709414000658a0f65db37a061aa04a03143ec224a682c04430582087d83a9869044a01000d607b0554722a0440c461201f5c50c421002c00443101eb23eb4c0d10031110287d5c8c3804842010108107ab0cf0c30c0600215240f55980cc14002002c0003ea794c80c900800850807d4521f010a2a00202d107a7f90cf080110c160880), (96, 84, 2, 27, 2, 27, 0x8380f8b8230500c400a21837702ce0801500161800835e23dd2a10600a21281834ee25b00c44004450c08338c9e529400000242a083368cb32044100544280833164f32109502141aa0832e83f42a4400c424201831707962084200640240830ad8d6220420064020182ff03ea080100c06080082fb00da020820224000182efa24c8b0c40242112182e4d152024460064500182d10b46094110c16482082ca8ffc214450c50522082c0dcb82a45100524a0182b0e461034000c0040a182af83c8924400041410182a8b5a88340500105121828b5e503208002010201828a09a3208500c440ac0828493190a44200624081824ca0e0108540041184082494d932b4140c065aa1823508b82940000024220822e1ab3284010c164280821678e600c440c44504081fbc5f40a0500c42080181f6525a210c40244122081f37faf00c00000440c081f304a6090c10256002081c6ade02a4110c124a0181a0dcb729400000642a081a0d97000d040080504081a0c2c910c04000150c081a070cf00892022408c0819f6a98130500c41082181924dd1334000c0142a18176d6fe20882022402408175d4b103500008040a18172a27c1089602211840815ef288890000c020120815109240945000424820814790c0014400c404020814605e000c0200204040814367680a50600a2500181347c6d2901100120aa08128df7a2a0d002460a0181260023280850e161280811f0fab20c46006452c08107b6c2080450056100080ecfe340b0100002082180df07b430c500c414a4080da7d04124400c41400180c9c7eb2a4540c465a8180b93018094040c02502080a9a3db004440c4450808097683d2a0140c021a818091869c121000c810001808d36cb2b0c0024602a18085de8002092022008018072dd85291000c8202a08069fa6b2a05400461a8180690c78830040c00112180636a0d020950e10188180507bee0940400065020804ee27f2b440004642a1804e27cc00c110c10484080467f5e2001600241a008043adb9231000c8002a1803c6e7b280c20266028080320c172105000440aa0802ada3b21001001402a08018004d304540c415a808007a5260a412002648017fdb906f290940e061aa07fd8dcbe2001200240a007fccfd5a03445005450217fc544c20a000000600017fb3d6642b4010c1242217f9a3876004410c5440007f992859230c0024002a17f9723f933104008112a17f96104433040004102217f93090b2a4410c5642817f92a0de23044004412217f904e7492444004151017f8c932521100008002a07f6b7287000050c1410807f6657492a401001242817f44706b080150c1618807f2c0563290150c161aa07f27cbf623084020412217f16f4bc8b085021211217ef24cf010c400c414040), (96, 84, 2, 27, 2, 27, 0x88165d9c0b44100524021880f1179134100c0148a1880ba556030840e04102187ff3272080010016000087e1938d305040081528087e0e0e6234450054522187ddf58e2081100140a4087dab996084410c56400087c3884c2b1000082022187bf2b05284040002528087b74896090810216002087b5c0b0134140c01582187a9c1c70841400065880878a873e0b0100c06082187887ac4335040081522187858f7121444004052a08782df32210050c1412208781db3d3250600a15281877698a81050400815000876de4c82201100100a01875f6cfb284440046528087531f8f2b4010c1642a1874dcb26280060026120087428efe20445005452008737e5603209202210a0187255f5e2040600245200870f7d6e0801100160800870523732801000060a8086fc95ae214500c444a2086f973770b414000658a186e8c7922245200644a0186a773f7290d402461aa086a3bd372b0c00e4602a18697e2190800400021080868b41f72b404000652a1868320740a10400821001867fa2fa0b0c402461021866d421103104008010a186612e28800c502501100864f5c192050400805280862ba9b111100008100a08623a4b7290d002460aa08619bf3880c410c504140861209772a0110c160a8186100a92220c502541201860e8a052a4510c524a81860c35372a402002642818609513a2905000460a2085f76f2600c140004584085ea5ef3220050c14128185e793c8824010c10410185d647d4884000002410085cab7050a0400042008185b40b7d094050c1250a0859a4020081000c820000859810fc214400c4042208584ccbd30904008112c0857ee8842b01000020a21857e92432b4500c464aa18574079320c1400045ac0856edd493200200210281855d843a2841200264a00855a8ae70a082022600818552ecea0904400461020854b686b2b400000642a1850f0c22210d502541a2085002203004110c14488084e6853e004440044500084e114ed2a0d602621a8184dc136f20c5500545ac084ce4c24124560061580184ca1b34908840201114084c4bb5910850004108c084bccb04220c50250120184b864c50a0540c42188184a8d85e008160024184084a00fa031440004142208494dc852000600201280848723fc024400c4040018468f65d0b090020208a1845fb7df230400c4402a1845c8f3b024550c545881844ce8243041400015a00844b8581008d6026018c08444fc722a0400c4602018419517e2b00100160221840ac2522041200244a0083f6e2d4030110c10082183e6c2ce0a4400c46400183e5b4bf208810e1402c083df263100846006010c083c80e222209102140a0183c35ebb080820226008083c1fa4430804000112408393c0e5024000c0040818385ace00b40100124021), (96, 84, 2, 27, 2, 27, 0x8d7e571a224450c5452018d72b62930c5600615ac08d60a424800010c1001008d5ea03229405001652208d5749d2094100c0648208d269be62b4400c4642218d04083c910c0024101208d023a0f2901000060aa08d000294910400c4101208cf4350322402002442818ceefef509405001250a08cdea12700810000408c08cd7c10e08095021618008cd6b8852045400405a808cd60355024510c5048818cbe65262341500145a218cb54ac220c06002452408c94f94f204400c4442808c91cc54230440c4012218c8a183c2a0c4024212018c8580060a4010c1640018c7550fe0a400000640018c4afbb48a044004211018c46ef8b2145100544aa08c385edd10090020108808c371c7220c010c1442408c2e21b6204110c144a008c00838d3109002010aa08bf2647082446006051018bf00291105040c8150808bde20ae280d202660a008bdcd02d2045100504a808bd4c0e5225000c8042818bd1105e0a042006600018bc0782130440004142808bbefdb20a416002658018bbcdf6509504008250a08ba0c22c130000c0100218b9db47c11094020118208b80e72e08051005608008b6d00012809402021a808b6a72f62085000440a408b4e243109445005250a08b3f4104808c2026001408b353952024540c4458018b2b33cd2250200a042818b24e1f308012002608808b1adc5103404000050a18b0265ef2b0040c0612a18b01b42d32500008142818af76c713085600611ac08ae8ea7c2a4410c5242018ae7837b0b4500c4648a18ad97f05094040c0250a08ad80c848b000000201218ad74a50930440c4111218ac0d8d10a440004240818aa09d85085040c8250808a79cf93030100c0408a18a6ba8b422005001012018a5aadfd280c0024202808a50d61209414000658208a2bd4a322404000452818a29217908414000258808a23d2152a504008252818a21fec83341000014a2189e1046d30d00008142c089d9b3650b410000248a189d8d6f2294550c565a2089cd4ab82a0150c121a0189c83c6f000810214008089b655602150000804220899787183005400411a0089957d8c020d602601801897fd54f024400c444081897684fa010c002440020893995fe220110c140a0189273d0f024140004588189220590820850e101101891f0fd60a4100c064801890e5850830c50e50112188fb04603105400411a2088e24832090900206082088c142a0830810e10012188b917af094000c0640a088a8c4d6290d402461a2088a49a682805000420a00889c0b6b234140c045aa1889375e88a40500125101887b4aa13000600211280886f2d9f214040c0452a08863dbb420c5200604a40885dada3204110c144a80884c7868810010c10012088474c88024440c405001882d04870801600261880), (96, 84, 2, 27, 2, 27, 0x931c6ab82a0500c420a01931886c10244600605081930faec93085400411ac093084b062809102160a0092fce870810c50250112092fc19ca20c5000444a4092e116ac80c420060414092d76e37084110016488092d5812109104008210a092bcadc509000000200a0929eb3fc0b09102120821929c28d701045005410a09286d7800845100524800924f54520b0140c06182192397c9a2141400045a20921c5a782a404000252019201b1da224140c045a0191e865dc8a0450c52110191a1b41f010d4024418a0919ee1e52810000820280919b604200812002408409195357d0b4010c1240a19191d0970a0150016188191854fe4321040c81120191719d110a4110c1248819168053f2840600265280914860ed11404000150a09118471b230d402441aa1910f18b48b404000251219107a91709090020608a090de935703404000450a190dd211309400000640a090cb2bfb2a0910e160a81908153b10205600601881907b5d9e010c102540020906bd9dc90840004101409069d5003000600211200906011d89044000414100905cf1b600415001458009059991f280d202660a8090452f542b1000c820221903f76ca0304400441021901efc3b200450c541280900274a6208d102540a4090024d0a0a4110c1648018ff11f6509054004218a08ff0f68600c500c4448408fcdc98b090110c1608a08fc80332214540c445a208fc625588a084020211018fb41d0a034440c4450218fb1421702091021408818fafaa66010c4024410208f950d7f0b040004600a18f93555300086022410808f8f171d31004000112a08f88288109094020218a08f86f29d2b01100120aa18f80a76f2945000464aa08f7298c30a406002650818f403cd609084020610208f1aa78a08094020618008f008d1c224040c0052018edb47e42a082022202018eda364522081021002818ed5283520801001002c08ecfd77220c100c044a408ecdc93c324500c414a018e826f8e208d602641a408e7de1b10a051005208818e79e59490086022111008e71414b2045200644a808e5a4fbc0a442006240018e56faae0a452006648018e523ad42945400425a208e48bb5910084020110808e4760bc094000c0240208e412b348b040004201218e2f0e3130c100c014ac08e2da5bc31044004112208e28c449214510c504aa08e2276880b090020208218e18aa252101400001aa08e01910600045005410008e018ba322446006452818dff764209085021610208dfee0c500852006008c08de32ee003414000058218de09052294400c4642208dcf094c0b4410c5240218dc392613009602211a808dbd215b084050c1650808da7f3cc13094020118218d934fd42245100504a018d8f65a9310d402411aa08d8cac5800c5100504840), (96, 84, 2, 27, 2, 27, 0x97a3a5ed0a04600621081979bc9c42090400801240979b73ca2a0d602661a01978e6b2c311040c811220977154c62241400045a01976aa8e5104540c415880975f95e32085100540ac0975c04400809502121800974bff19025000c804081973ec8a08300500101121973bce7d0808402021080973a3ab22b4050c16522197209e990b0c4024210a1971806e700c400c4440c0971176122845600665a00970875792000100100280970415a8025000080400196f3abc110852006108c096f099fc080140002180096e8f931080400042008096e1c398335000081422196e19be2214010c14422096d9a271024540c40588196d28df1224040c00528196d10cb32145400445aa096d0f93e2a41500165a0196ce9ad4290d402421a2096ab47f701415001458a096a5b984010840200102096a4a2d10a4160022588196a1f73d120440c4110819699f6002a0d402421a019687c0753045000414a80965a648820c460060524096543c8200c020024404096439c6d294440c4252a09639f43c30c0400015240961d43ee0244500545001961cd0c7290140c061aa0960792792b45100524aa195f04634900460061110095e6a4ff200420064028095da15522081000040a4095cd3e9d2309002000aa195aefdaf010500c4408a095ad8e19130c4024110a195ac2397290050c1612a095a98824284140c025a0095a5b3d600c5000444840957cd3a40a0c102520001957ca9f103100008000a195750fb93305000410aa1956723df2b4150c165aa1955faeb72841500165a80955da5cf23440004442a195575fe2230850214122195516c08284540c425a00954d719f094540c4658a0953ffab4014440c40502095376e282241400005a019534bd5700c050c1450c09530b5de020950e14180195137caa094550c56582094e856a520c46006052c094d825ad23500008042a194d0c5f0120460061100194d00c07004500c44488094ce65b4008540040184094cb83a6208100c040a4094c43956234040004522194c2f30b020150014188194abaddd0b4500c4248a19481f9492a440004242819469c7a0234410050422194422b48095000c8240209439cf33030c4024410a194333b683241600215a019427d03d00c010c1040c0942069662a45400465a01940a1363234110c144aa194077d272085600641ac093f892fa230050014122193f66ddb21045005412a093f6521111090020108a093f261c02201200200a0193f1d170220110c100a0193e9d016290400046022093e2daa7030000c0400a193dc8042280010c16020093cddf90220d602601a0193cc2ab1094150c1258a093a0406d2901000020aa09365a873210440c4412a0936321e92809502121a8093270ecf20806002412c093253c172840400065280), (96, 84, 2, 27, 2, 27, 0x9d6dfd5e20c45005452409d6a431821005001012209d6983d6294540c465a209d62ff0f00804000410c09d5ca658014010c1040209d5608ab2305500541aa19d0cbcb40a404000250019cfa4ab03345400415a219cf7b8a922400000042819cf5df2030c1400015a409ce0b03f2201100140a819cd553c8314500c414a209cc98bec00416002058009cbbbc4022442006042019cbac4cc80006002011009caa5cdc2241600205a019ca0ac4c8a401001241019c9c39582a4000c0242019c7d40dd29104008212a09c5ed9c909100008200a09c47495e2a4110c164a019c0b2d9b03414000458a19bebd36602415001458019bd87d91130840e0110a19bd68c7920c5600605ac09bb5a36489440004241209ba793dc29440004242209b8da6fa2305000440a219b857f0823005001012219b8562292b05100520aa19b841e0100454004058809b79473f000c6026410809b7437fa2a0110c160a019b6b43dd130940e0118a19b68e1a503080020000a19b6795f6020050c1410019b4cfcdc80444004051009b3ce503200010c1402809b37258c130140c0118219b162a2e2a0450c5612019afaa169330d402411aa19af6627c0b080020200219aea17de00055005418009ad84ec40a415001258019aca56012109402001aa09abf83000b095021218219abb5c51134040c0150a19ab2ada93005200610a809ab2144d308c0024102c09a951b3882444004051019a8514dc2a50200a242019a775d8028045005212009a70f02530040004102809a6d41f42305000400a219a4347b80b041005200219a29758502081021000819a2510af294140c065aa09a0b6a252a41100124a819a074f280a0820222000199e023c82901000020a2099d5bd222085100540a4099d4a8b4080450052100099c7fd2e2b0400046022199c7389b2b040004602a199a420d600095021418009993cf6f208800e0402c0998ddcc9335040c8152a1998bc4ed23000000002a1997fce00034040c00502199790839014500c4048a0996b516900c40004040c099590a6b2941000064aa09958b2950801200220880993df819131040c8110a19930095c2804600621200990bf0e5000160020188098dcec34808810e10014098d654bd131000c8100a198c72fc721085021412a098c22850124100c01480198c193a6084140006580098bf64683044600615200988c9986080c6026610009885245b014040c0450a09862162f0800200260080984a6f77034010c1440a198438bc02300100100221982f3a5a280c2026602009825054830c0000014240980229b30a4550056588197e8b4203245600615a0197e4fd80004150c10580097d4b93e2a0c20266020197c72d9d094100c0248a097b9a084335040c81522197b39b2f00816002418c0), (96, 84, 2, 27, 2, 27, 0xa343ec55115000c8140a0a33eb6d5015040c8050a0a30a5f320208502141001a2e7b453224410c544281a2e459680b0d002420821a2c15545284440c425280a2b9fb6c2a09102120a01a2b94578224510c504a01a28487022089502141a40a2822679224450c505281a27bed722089102140a40a26c131f280540c461a80a25b3ab0234100c004a21a239dc7a0808602261000a23265fe0900000060020a220cc8c0244600605001a21a8ae0320c402411201a2084fa10b444004250a1a1f0115f20c42006442c0a1e577d5230110c100aa1a1e4cbe60089102140840a1dccb04334400c414221a1d0175d2241200204a81a1c04d4e2809402061a00a1bbefcd09095021218a0a1b4c9b529040004202a0a1b35752204050c145200a1adc08f2040200244280a17d9c6e20c400c444240a15b8d9c0345400405821a14fca512a09002020a81a12e64c529005001212a0a126a342294150c165a20a11895a0930000c010121a10af384024510c504801a1042cbd0a5040c825081a0f579c303045005410a1a0f0d2d9325000c814281a0caa26c230840e001221a0b27c9420c400c404240a0b17914810c00e400120a08f902500856006018c0a083aea32a0000c060281a077d543234450c5452a1a067bbf08b44400425121a06331493240600215281a0596830330c002410221a049c3d9234010c1042a1a044cc04820410c500101a03113409044600615100a01ad4e50245400405881a019a2cc0940000024020a005e19f2a4450c565281a00014f70a454004658819ffd45a029040004202209fd127ba034550c5458219fd022f600804000410409fcfa27e2941400065a209fccef2e2901100160a209fc691720b054004618219fb88bd4135000c8140219fa5c0f6094400c4640209fa185df020150c1418819f9c9ae0284110c124a009f852eec0b400000240219f6d41ce2a45100564a019f6676bd014010c1040a09f6122db2841100164a809f5df1f910806002110c09f4c6a5f2109402041aa09f374cb9280d002420a809f2ef7612085500501ac09f1f8f612001500101a809f1705cd130100c0108a19f059b9d32440004142819f0193cb20401001442809ef0cefc09094020218209ebb7a24301000c8102009eb342d0114540c4158209e998b6c030100c0008219e807911204400c4042809e7535150a080020200819e6dd709235040c8052a19e366f2d2b0550c521aa19e20abe600854004418409e1b7703008510c5408c09dff1c8200c000c0440409df5060628086022612009de503f033440004142219dc06f6e014150c1458209db965f3220550c541a819db29273034550c5458a19dad380320c050c1452c09d7f80d810894020118409d7cbf01014540c4058a09d6fa88e210c002440220), (96, 84, 2, 27, 2, 27, 0xa8d1fbeb230d002440aa1a8c557de030850e141021a8b9c3b5220150c101a81a8acdf713081000010ac0a8980ace0140500145020a895d84f084010c164080a881c2242145000404a20a865faec2b09502121a21a8569e5b0004600641080a8556782200d502541a00a8549e2f2000600241280a849dc7430c4000414240a83f15fe2145400445a20a829b267210c5025412a0a828b7e08804400421100a8246d9d2941400025aa0a8212dfe210100c040a20a81ac0441244400415001a8088a550a0d602621881a7f0ae230240400045081a7e3b1080a0d602621801a7d94a9d20c5500505ac0a7d5d6fc308d402411a40a7c69ce903081021000a1a7c4547d0041400005880a7b1093e030c402441021a7af6010920c402411101a7ae6b28004540c405800a7ad8b4410d000c814040a7ad2438094440c425020a792f68b000c102540080a7822f750009502101880a77a78911201400011881a750b1053050600a15280a74cc1cd2b0010c1202a1a74c9754234000c004221a747c8172309502141aa1a74323d7224140c045a81a6f6d8ba2080500141240a6d95080110d402411820a6d0f629224500c404a81a6cbf8589340400015121a6babf2e2901000060a20a688f16301091021408a0a687c2081150400815020a67c71c08088502101140a679605e2a09202260a01a64d9d540144500505020a642789901005001010a0a6143f44025000c804001a6094e1a2045100544a00a607dfd300c15001458c0a5fe052f2000100140280a5f5cb2f0b0540c4618a1a5f04b752b0c0024202a1a5df82f200c1500145840a5dbcc392245600605a81a5d739cd030050c1010a1a5cf1bda2145500545a20a5ce25830b404000650a1a5a5ba5e030150c141821a594d80d20842006002c0a58c53452a40000024281a5822b360a00500161001a573b8102045500505a00a563e9c4920000c010101a55eabf50a44400425081a55e483503444004050a1a5581e912b401001242a1a55244881209202210801a50ef818130d002410821a50216282b01500121a21a4e66d3b00c51005448c0a4c90a27220810e140281a4b960942a04100520201a4a8d0448a00500121101a4a021383090400811240a49e1e4e2085200640a40a49658b08a44500525101a49323088840100124100a473ecea024150c145801a46fdaa12845000424a80a461653c320140c011a01a451d2f529080020202a0a43d6e29204540c405a80a41b4b032945100564aa0a4195a670b400000640a1a406cba8880c602621100a4040ac5134500c4148a1a3fc64132b0050c1612a1a3eb39bf09050004608a0a3e7832920c5000404ac0a3c9f86f2a41400065a81a37acd2a2840400065200a366ff2c0a01400021801a364c8df210840e0412a0), (96, 84, 2, 27, 2, 27, 0xaef15a7923405001052a1aeec9b4a2b05000460a21aed7f7c0330840e011221aec0242920846006012c0aea9497b2141100144aa0aea05558030840e001021ae96bf60294450c525220ae7c40281304400411021ae6ea1a0880c40e421100ae530c09130d40e4118a1ae31e7822900100160220ae2971e200c4500545040ae1e5f9e0b04100560021ae17630a084500c464800ade745e82101100100a20add091c8084440c425000adcc3d942a0d502521a01adab4a90035000c804021ada5d3c9220110c100a81ad9d0b90234400c404221ad91dbc80901100120820ad8e5c053009202210a80ad8c54192241500105a81ad82343b214050c1452a0ad7b83a8281040c821200ad7155892a50200a24281ad6e6ff3000450c541080ad5a3cf20b0500c460821ad471cbc0b0950e121821ad4024d10a0c602621081ad2db0a42b09002020a21acff890c0105500501820acf6c4d03305400411a21acf33afe030440c441021acda2e8b2a05200660a81acd49857234150c145aa1aca2219c0a1000c820001aca181e00b4500c424821ac969d548a04200620101ac916d052a1040c821281ac8c847a2040200244200ac85dea60944400465020ac811f75134440c4150a1ac6e30a80a0c002420001ac6c3cc30241600245881ac645a012050200a04280ac64587501455005058a0ac47e7b300c140c0458c0ac4315672101100140aa0ac21ce280900000020020ac1aaed0830c502501121ac1936092810600a21280ac0956b32809202260a80ac063e68291000c820220abc5cb9d091040c8210a0aba9fe1e2a01500161a01ab8f91e70245500545881ab6f48120085000440840ab6cb11e0805200660800ab6beeeb2a44600665281ab47058f004040c045080ab463cd7204140c045a80ab2e524c10c4400415040aafa9c9a2340100144221aad38d6c830c102500121aac9eaff0a0500c460881aac75e98124540c415801aaa9221a0b4110c164821aa7b4fe22a05100560a01aa5910762100500141220aa45cb1d0a5000c824081aa407ab701054004418a0aa36d43e208150c141a40aa348b742b0d402421a21aa1302722a41400065a01aa1208080308502101021aa06d862020550c541801aa0365e92200600201281a9f7ada51010600a11080a9dee78a0809202260800a9d58a3c810c402401120a9cca871211000c8002a0a9b3bae5285000c824280a9af2bbd094540c4258a0a99935853209202210a81a95ab5472040500145280a955e0722b41000064a21a941eabe0201500141801a9310aa9234100c004aa1a92d3aa88004200600100a9209c470004500541080a9170b270a45100564881a9163a2e0081000040840a9104928030c102500021a8e8e43d3200600211281a8e0e438890c102520120), (96, 84, 2, 27, 2, 27, 0xb4fc09ed224100c004a81b4f27a1c0045400405800b4df33a1015000c8040a0b4de969d224440c405281b4d7621a0144500545020b4d297fa0841600265800b4b470cf2b0c4024612a1b4985a420200500141001b49243fc2240500105201b489710f0240600245081b475360909455005258a0b45042c89240600215101b422c7fc3150000814220b412ce99334500c414aa1b40fd23a2101500141a20b4063cee020c202640001b3e3c2ae0b09002060821b3dcdd3d2809602221a80b3c925c909414000258a0b3c5e62931504008152a0b3b2c99c10c1400015840b3a2ffc6080c002460000b39e1b732200600241281b3615559204100c004a80b354b553204500c444a80b33b63ab00896022418c0b339b0da220450c541201b33896502210200a00201b31c79501208602211001b2fd52f20801000060800b2fa485c1200600211001b2f0a36c3045400415a00b2e963e9104100c014880b2e445e4134040c015021b2d135101301400011821b2ceec462b41100164a21b2ccea70334040c015221b2b25dc0204040c005200b2a51b2e034110c144821b2a1c9f121500008042a0b298abc92a4050c125281b287df809208602211101b284411e0909502161820b27608a53205200610a81b25d5b182a01000020a01b250bf75095000c8240a0b246400b01094020418a0b2350365304100c014a80b21efcb80845000424800b21eb704124140c015801b1e386441085000410840b1e1529b0044500545080b1a8bc5e0088402041040b1a4950b2840000064280b1a316bc820c50e501101b19df49a2a4410c564201b1743e0d114540c4158a0b167e266014450c545020b16534808b00400021121b160ce0500c50004048c0b143c8720a4550c565801b13c19802085200600a40b0f9499700c550c5458c0b0f2b28500c45005050c0b0d2706b0b0840e0610a1b0b5905b0b014000618a1b0b511d300882022400c0b0ac0d9d0b404000250a1b0a8cf4f204440c445280b0a3900c00c4500505040b093f78420d0600a05240b07caee800c040c005040b046f5793010200a10280b04477a1020150c101881b03e94a32800400061280b0320b7d0a05400421881b024beb43005600611a00b015ddeb084140c065880b005d5d910812002108c0affca448304000c014200afedcc532b444004652a1afe276ab2041500145a80afd4e86a0b01000060821afcdc7b7210c4024412a0afb357c22a01200260a01afaeac5e0a41400065801afa64f5b0841000064880af8890e20084200640040af6090d00941500125820af5a95410b400000240a1af50178c830440c401121af2478553141000014aa0af185dcd2a09202220a81af113b81120840e011081af0bb3bd30844004112c0af0627432305000440aa1), (96, 84, 2, 27, 2, 27, 0xba5e1f2c2205500501a01ba5d77c62089402041a40ba5892b72b0410c5602a1ba545df52205600601a81ba4a8d53200c202640280ba28eb7d014140c0058a0ba1b351930c1200214ac0ba087b370840600265080b9eb9bb80950000824020b9e7207a0088202240040b9e4ed2500884020010c0b9df397d00814000018c0b9d32e320845100564800b9ac4b013101000010aa0b98b52a08a00100120101b9848f5e2a00000060201b9762c710a0d102520881b972eefa084450c565000b96b0f152841600225a80b96322392b0450c5212a1b94a37160a44400465001b94a19b0034450c505021b9439fe08b0c502521121b914eb60804010c104100b907912a034510c544821b8f8d9212105400401aa0b8eaa55c310d402411a20b8d43c15020c502501081b8d02a8c215000c804220b8a48fc8894450c525120b8996cf4231000c800221b88aabd709410000648a0b87f5f242a04600621201b87a51a90b4410c5240a1b874c002224110c144a01b856c139230510c500aa1b826b9450a0d202620881b80f04112b4440c4252a1b80315742245400405a01b7c0576c304440c415200b7b3e8888008502101100b7b173f7008c2026400c0b796d0802301400001a21b7767aad10d04008150c0b77636e60b01400061821b7605dbc2909502121a20b7552af90090600a010c0b721ffc90b4540c4258a1b721c5a7024410c544081b71cfab30b451005648a1b70e9af22841100164a00b70e2ccd33004000112a1b70131d88a0c40e421101b6ed40d4884010c124100b6e8c3c03244400415201b6cce002094510c564820b6b2382b2a45100564a81b681f72e2305500541a21b66ca1ff2005100540a80b662d53929000000202a0b6618d912240100104281b649cf7d1005600611880b63766383040400015200b6329c7b00850004408c0b62996df030d0024408a1b628fe3f084100c064880b621c86a2100100140220b61d5dc300c55005458c0b61b3b8a280d102560a00b617c00100804000010c0b615c59e2b0c002460221b6147c1d320c602611281b605707900c050c1050c0b5f583f309454004658a0b5ee291a030500c440821b5e6f8092a41000024a81b5e06c472a0d00e460a81b5cfc48c2a05000420a01b5c1e17a2341400045a21b5aaa3f43204000410201b5a29cbc0208602201001b59defe12a00600221281b5955ff92845600625a80b5928182210d002440a20b58fe2ad084550c525880b582bed42a45200624a01b578beda204550c545a00b56b664a0a4050c165001b55f0a4b094110c1648a0b55cf95e084510c564800b556e45c884440c425100b5222731230d40e401aa1b515cbb60a01100160801b51191b909451005248a0b50b80e929404000252a0b50a029e0a0140c061801), (96, 84, 2, 27, 2, 27, 0xbfcc38242105100500a20bfca5a610244400405081bfc7146d31000000102a0bfc06904314140c015a20bfb67cb9034510c5048a1bfadd3e70a05200660881bfa9cd649044200614100bfa56cbb2001600241a80bf9ff94090c4400415140bf96f0052a0000c020281bf72b1730801400061880bf6817ae090d102560820bf5b76bc0310000800021bf5b5608830410c500121bf56d8bc904400c414100bf444db90b0010c1200a1bf09b11e0109102140820bf06eab01150000814020bef7b11e2b05400461a21beeb8c7109055005218a0beea9f082b04500521221bee5a5d9284500c424a80bee20c2b2044400445280bec218492a40200224281beac4178220050c101201bea150b22a0d202660a01be971806034400c444021be90b8912b01000020aa1be84e5c12a4540c425a81be7b5ecc9204000410101be546f1f21441005442a0be4cd7d53205600611a81be21694d2000500101280be1545a62841500165a00be026fe7284440c465280bdf98cd10a04400421081bde652b0090d402421820bddecd7720882022402c0bdd29143030940e0418a1bd9288a8900800e010100bd86fe612b0500c420aa1bd812d4300800000400c0bd7555362800100160200bd6fd64931080020102a0bd64f8372200200240281bd62ba0e2b41400065a21bd606c510b040004200a1bd5d799b2b4410c5642a1bd4ba90620c050c145240bd4b34653041200214a80bd48b0a08a0800e020101bd3822bb210940e041aa0bcfa9f0e014440c445020bce3bfc32a09002060a81bcaffbbb2b405001652a1bc9cc46d2241100104a81bc996d472089602241ac0bc8e13c20a05500561801bc4b4cb5324400c414281bc2e0bf4900440c411100bc2644d42845500525a00bc117a792a08602221281bc116d9d23104008012a1bc04bb432201200240a81bbfe91d32041400045a80bbf1ac9d030000c0000a1bbd905d5284150c125a80bbcdf66620c000c044240bbb58e7720c500c444ac0bba98e560a08502161001bba46ba0130540c411821bb940c45024450c505081bb4c5e040a44500525001bb4c5df81045600615800bb48abef008d0024408c0bb463ded2b09102120aa1bb3ca9ba0b00400061021bb33f79020d0000804240bb2ffc462201200240a01bb255ded2844600625280bb1360132208202240281baf3debb230110c140aa1baf0e7e8120000c010001baf072172a00400061281baeda63a2a04600661201baeaf492000c502541000bad4188a0044600645000bacc816e0a0440c461001babeff352a4000c024281babbff61230d002400aa1bab8fbe220c110c144a40bab7c3262300100140221bab73551204550c505a80ba88c9fa2900000060220ba7d78c521001001002a0ba7399462309002040a21), (96, 84, 2, 27, 2, 27, 0xc65dbd583200200210201c6569fc0301040c811200c6539113030440c4410a1c65195b93040200214280c6317b6513500008140a1c62903c50a0d002420881c6198b320905500561820c6131545030010c1000a1c60561ce2a0150c161a01c5f73a68900c602611100c5ef560b2a0850e161281c5e1b54b2081600241ac0c5bde24a2b04100560221c5bb181b020510c540881c55814882840100124200c552122503091021008a1c53307fe2b4110c164a21c5320195214040c0052a0c531b1e20805500561800c52769fc0b00100120021c51feae13240000014281c500c7a1330100c010aa1c4c72e9b280050c161280c4925419124140c015881c48e30f43044200614200c485bd5323441005442a1c47f5c542a4040c025201c4576c21334140c015aa1c447350a0844100564000c43eb832090d502561820c43e4cd320c02002442c0c42689040a00500121001c41d8c59301040c811280c413560300c16002458c0c412c01a2a40600265201c3ff523a0088502141040c3f840cd204000c004280c3e615bf0a05000460881c3d0da322044400445200c3bdb1960a45500565801c3ba0f17290800e0602a0c3b52a250240400005081c399442830d000c814240c37049602801400021a00c367f59c90c440c415140c357152b0a4010c164081c356b1d42b40500125221c3148c9113090020108a1c3112ee9094510c5248a0c3100a842045600605a00c3084cbe2a0c602661201c2fea6f82005600601a00c2da18088084500501140c2d8fc4c9304400411121c2d5be010840200224080c2c8b65d2005200600a80c2c4be8b09040004600a0c2c11d52008c402441040c29214642350000804221c277f16d014150c1058a0c2723e3a0001500141800c238ce502104000400220c21966e52085600601ac0c209aa8d330000c0102a1c1f582c6090d402461820c1eba2b08304100500121c1c3d8aa0309002040821c1b7d9fd120d602611881c18dd4fd23044004012a1c16bdb583084600611240c161f2fd2085100500ac0c13f1dfb280840e061280c13ce2df000410c540080c13cbc63280100c060a80c12c66c00a04500521001c12ba6300b0450c521021c12afe072b05000460aa1c0e3307020c5400405a40c0d99962290c102560220c0ca2ccd320c202610281c0c6574b208050c1412c0c09ff5d10a0c102520081c0798ee2234500c444a21c05e47c00245400405801c0593f9b0a0440c461081c0373ec60804100560000c0311f01294400c4242a0c02ac4120a4000c064001c02a05cb2a0150c161a81c017e7c52a0110c120a81c01237481205400411801c00a8d040b4150c125821bffc39c42904500521220bfe6562f09044004610a0bfe179d48a0840e021101bfdd3942284510c564a00), (96, 84, 2, 27, 2, 27, 0xcc04e9a9208d002400ac0cbfff78c0a45000424801cbfc5d262900500161220cbbba74f280040c061280cbb93a482145100504a20cbb909a300844004410c0cbabd313210010c1402a0cb9a832b2b41100164aa1cb707461324100c014a81cb68e5b08208202200101cb5a31630b000000600a1cb5317f50841500125880cb18318e2a08102160201cb0210ce0a01000060801caeb602f2a40000064281cae4c2a5031040c8010a1cadca4f82110400801220cadbe7542b0450c521221cad6a9222a40000064201cac7a4f72081400041ac0cab6920d2a04600621281cab25d6c024040c005001caa14fed13044004110a1ca8243b50b0d4024218a1ca7ecd5620c0200244240ca5c41722304500541221ca5b967000c550c505840ca56a7a9330c4024112a1ca41d5512845100524a80ca3abbc323041005402a1ca34b2c303015001418a1c9f93cbb0b4540c4658a1c9dee1942109402001a20c9c0c8de2141500145a20c9bf055e00c5500545840c9b5368d314440c4152a0c9aa711c1305400411821c99cedf7020c102540081c99596ad084500c424880c98ee3c80045600605800c97fc46a0901100160820c97318c40b0c102520021c97156842805500521a00c96955908800500121100c96308d93241200214a81c94b67742a0550c521a01c90a484b080010c160080c8ff08fa004010c144000c8feadc30b0000c0600a1c8fc2af52210200a00281c8fb9fc70a0040c061081c8f193f42b0110c120a21c8e51253030840e0410a1c8c2e9602a05600621a01c8bc8e1a2a44400465201c8bbc25d2b41000024aa1c8a3cfa620c510c544a40c88a50fa080c202660000c875b9372a09402061a81c8682f2100886022010c0c85c8b592b41100124aa1c854b68b0844000464080c85202952805100520a80c84d1b2700880020400c0c83573e70a41600265881c81b84e3084550c565880c7ef87f00b45400425821c7e657583090200a10240c7d0528c2a10600a21201c7a39e840b0c402421021c76f9bf2014050c145020c76f6000894440c425120c76399681250600a15001c760eb343084400411240c75215910a50000824081c734d9cf21081021402a0c734be34294150c125a20c725da8909081021200a0c6f951b72b0500c460aa1c6ea7ad70809202260880c6d98b680309402001821c6c3eb8c8900000020120c6b208222101000040a20c6afa3412808102120280c6a68f7f2209202240a81c6a49727034000c0440a1c6a2f77400d040c805040c69c1e30890050c121120c69aa59e2085500541a40c69145f32909002060aa0c68f38370b4040c0650a1c6825a1929504008252a0c67adc1e0844600665000c66c9b842810600a21200c6672b222b41500165a21c65fee3913004000110a1), (96, 84, 2, 27, 2, 27, 0xd1e923c110c140c0158c0d1e004282245600605a01d1d90438824440c405101d1d8c8550b011001208a1d1d39b77208550c541ac0d18ecf549240400015101d17257ec094010c124020d14538c3090440c4610a0d140240b224440c445281d13e60072b044004612a1d12e9fa09040200214100d116a9bb204040c045280d110aa8810c4000414040d0f6869d1204600611081d0df244c908800e010140d0ce7bff00802002400c0d0c8bb3f094500c4648a0d0c63874035040c805021d0c0fa708304400401121d0b1262a0089002040840d09393f2220150c141a01d0876d0509051005208a0d08755e02900100120220d086afa103454004058a1d07085392a40400025281d060d54e0100400041020d0476201230440c4012a1d03920f9210d002400aa0d02aa4222b40400065221d01b887300c110c1448c0cff3495510c12002148c0cff2ab112801000020a80cfe75f922b0400c460221cfca3d972041600245a80cfc54a3f0801500161880cfbe93a4030950e101821cfbcea6903095021018a1cf9dd8f22b0d402461a21cf9ad6a709000000600a0cf9612a80944100524020cf5b61543204600611201cf52d3a60a08602261001cf36e5fa0b4450c565021cf18512100801001000c0cf180c5d008d4024018c0cf0d3a4e2b4440c465221cf053cfb2b01400061aa1cf034be530884020112c0cece93932a41200264a81cec555c09108002010120ceb75f452841500125a80cea5f400034150c105821ce8b8f7b0008502141080ce88350d004540c405880ce87c5843304400411221ce6fbb548a44600625101ce6215d3020950e141881ce1328222b0410c560221ce0b339d0b0150c1218a1ce05e0c62240100144201ce048be4880c502521100cded0c60234510c504a21cdc9d9048a4010c124101cdc5811d2205100500a81cdc22afd224510c504a81cdb40e3c0841500125800cd6de0592090200a002c0cd59571d208d602601ac0cd3a41b510c06002150c0cd3235f72b41000064aa1cd2f6bcd21440004042a0cd273a95104040c015080cd0a85a42a10200a20201cd04c1dd0a0840e021081cd033c9723401001442a1ccff6e06008d002440840ccfc013b294150c165aa0ccef9f391240400015081ccee932c0308402001021cce9f4b20840200264000ccde52b62b0950e161a21ccbda8c121445005052a0cc9d2a760a09102160801cc9cd95f20c440c4452c0cc8e1ebc120500c410801cc82c85b03094020418a1cc762d2531500008142a0cc75ccf70b010000608a1cc7323340b0c002420021cc56505130840004102c0cc4a1c512a1000c820281cc3a9e800b0d402421821cc3845602208602201201cc1ee1bc8008202200100cc1be79c294500c424a20cc0dac862145100544a20), (96, 84, 2, 27, 2, 27, 0xd86f79e7224450c545281d86af46300812002408c0d860d5c90a0940e021881d85ba579108d4024118c0d85adc8901055005018a0d823a0b309051005608a0d81faa400a44600625001d7ffc0ed20886022012c0d7e3cb45004050c105080d7d274de2b4150c165a21d7c8ec753010400811280d7c070680a45400425801d794625b208910e140ac0d7939157214510c544aa0d774e5e92850000824280d750b10420c5500505a40d72cb65f21444004452a0d728a7108b40000024121d70884ff00c05001450c0d701cc91030940e0018a1d6eac265034540c4058a1d6e362e301444004450a0d6e2c682234150c145a21d6c16e7a294500c464a20d6a227c00009502101800d68f157c2b45400425a21d68da3e0311000c810220d689325d0a10000820081d684e75a0b0c102560021d6783d39320440c411281d6754c67210000c0402a0d66bb08a2084600641240d64f43a22805500561a00d64bf294924440c415101d6397b053040000014280d63921a2284440c465200d62ada04930040c011121d6239dad09454004258a0d615dc53214410c5442a0d60f4968234140c005a21d60e733c3308002010221d60919f92804000420280d5fbfc3a200d202640a00d5f7e4d900885021010c0d5eb64792045600605a80d5e9077c2150400805220d5c8ae9d2804500521280d5beabf40940500125020d59fbc250a09202220881d597b1170044600645080d58df92c30c540c415a40d57e9c8c820c202600101d57d16082a00500121201d57840408a4440c425101d56abeb12804100520280d566f2f88b0440c421121d5537315090d4024218a0d54cdc9d2a0050c121281d53d41f0104500c414800d537724e200150c141a00d51a84d513084020110a1d4ca28762b40000064221d4aefcc6280100c060a00d4821c472a04600661281d474d91c0250600a05001d432169e2840200264200d430dc982844500525200d43011b0820050c101101d427899a034000c044021d3c54dc40a05100520801d3b9d0ed1041600215880d3970bea0845200664800d35d3fc8294550c525a20d35143da2a0100c060a01d34af310214540c405a20d34284490805400421880d33e26830800600261080d33d53fa2b45100564a21d327e85c2241500105a01d323697c030d002400821d2ff63fc0341500105821d2f6c39430c000c014240d2ed7b688900100120120d2d20bc51000400011080d2be5215030c4024010a1d2a9808e2a4140c065a01d28fcf832a00200260281d27d2ce2284410c564200d276bdbd2009602201a80d26759741300400011021d256109d20c540c405ac0d2505112084110c164800d24bb5612004500501280d1f6071a0a41500165801d1edf5730a05100560881d1ec2f7f00c06002450c0), (96, 84, 2, 27, 2, 27, 0xdfc51d48210d402401a20dfaf26b80085500501840dfaacffb094550c5658a0df993dd7024150c145881df7ae6042104500501220df69060c231040c801221df51e3232909502161aa0df284b69114400c4140a0df027ebc0a41000024801defb54f920c04000052c0deceb153210110c140aa0deb60fa90b4400c4240a1dea7b112080140c061800de9c9008024110c104801de8956fd0840400025080de77a42c2901100120a20de7038f62845500565a00de46a45e2a0010c160201de2d7b78030c002400021de200b370a45600665881ddfc80ba2a40500165201ddf58e692800400021280ddd0d8311208402011081ddc4375b00c01001440c0ddc41fc90a4000c024081dda5d2be0200600241001dd96ef19010d4024018a0dd8ef63a2245400445a01dd3e7b352b0050c1212a1dd3933403085600611a40dd2cd1290b0d5025218a1dd1da338884050c125100dd16cfb3208140c041ac0dd10e5822841400065a00dd0b5c44920800e010101dd06fc513090600a112c0dcfd70900805500521800dce88c742b0d50e521a21dccd86ca210040c041220dcc87994120840e011001dcc5987e0b05000460821dcb6ccb60085200640840dca719b72040400045280dca2b4bf2b09502161aa1dc9da8c7014140c0458a0dc93ad1a0a05200660801dc907d7b008010c1400c0dc7ea28500c04000050c0dc76e5c900d04008050c0dc6194760b00500161021dc5304502310000800221dbf8fd61230050c1012a1dbddb12a0808002060000dbd39ebf280500c460a80dbc8fceb030800e0400a1dbaba64d09440004240a0db644fda290c002460220db549f080940400025020db233069130000c0100a1db2322f43045000414a00dafcba690804400421080dafbf27f00891021408c0daebe6dc204410c504200dac5c7d10210200a00081dab780260a08002060001dab3efbc8900500121120dab242f13345400415aa1daa744393004400411280da894b9520c400c4042c0da818c262344100544221da5fc7290041500105880da3c3ec5204140c005a80da31ffe10a01100120881da31ca2721401001442a0da30009c8144400405120da14baed2a08402021281da069c8c3001200210a00da0641608a0410c520101d9faefe53105000410aa0d9f9debe020c602641001d9f77a862805600661a00d9e79f772809602261a80d9c35540031040c801021d98a92993301400011aa1d9598b820841500165800d957c016030010c140021d92793d0014110c104820d90f2861214050c1052a0d90b82e22145000444a20d9046f8e2b0c402461221d8f47ebb220110c140a81d8e7edde214410c544220d8d57287214540c445aa0d8c1f3c4094500c424820d88505462208202240201d87b8ac92801500121a80), (96, 84, 2, 27, 2, 27, 0xe617b260834410c504121e5f82a602041400005a00e5e5145c0844600625000e5d0b57c2b05500521a21e5cb02d42b00000020221e592003510894020118c0e578954b0a04000460081e57471ee2245500545a01e56bb8e500c42006040c0e51d70fb284040c065280e51a2fe12005600601a80e5178b1f004010c144080e500b6bf2845100564a80e4fb76e80a0140c021801e4ec282430d0000814240e4df5fa50b500008240a1e4dc9426234000c044221e49fbe4b010d5025418a0e481b2790841200224880e47e9b9f290410c5602a0e47023472a4040c065281e468581e2201100140a01e4632fde220d202640a01e443088933444004152a1e40ebeb40805600621800e3e399c020c140c005a40e3e16560008d402401840e3d2f4892a0c602621281e3cafe45204500c404a80e3c25da48a0000c020101e3b9d7b80845600625800e3b819c3080d102560880e3a4f474234540c405a21e38fa906004050c145000e3676261094010c1240a0e3635488220d202600a01e35c08d80245600605801e340582700c45005450c0e33b1f382b01100120a21e3355e252105100500aa0e300ea6d3001600211a80e2f90824834400c404121e2edc973220c102540281e2da5a362a08402061201e2ac7be72345100544aa1e28c4378220d502501a01e28380612840600225280e27a3d2d294510c524aa0e27a34e1320940e011a81e26750cd214540c405aa0e25ab75e294440c465220e2521f5b2a0140c061a81e248b32930c1400015ac0e23703d52010200a00280e22289362b09102160a21e20ef6962a4000c064201e20a36c83141400015a20e205ac552a08002020281e1f5b06b200d102540a80e1f10f122200600241201e1e7eb9f214110c144aa0e1c5a124234500c404a21e1c44d888a0040c021101e1b78879084150c125880e1a5b5ab210d402441aa0e19d8c80890c00e420120e1820727010d1025408a0e18093db0a09202260881e17beaf60a0d602661801e1742965024550c505881e155bf8d0a0100c020881e1540e24020550c501801e1465688908440c411140e122b1bb090550c5618a0e11ddfe20208602241001e11b34b6090140c061820e11b1dcc3205400411a01e1068fd5034040c0050a1e0dbd95530d0600a152c0e0bf69c20a05000460801e0bb10481081600211840e0ba6f032841600265a80e0b6eb720081100140840e06b557d1209402011881e05781b83201000010a01e0510f73200150c141a80e04aba730a0110c160881e042ddbc3041600215a00e03d64612a5040c825281e0390a9c234410c504221e03704a4084150c125800e0346aaf2240600245281e00cc7808840400025100e0043091084050c125080dfe98a510250600a05081dfd986ad29081021202a0), (96, 84, 2, 27, 2, 27, 0xed4320ad33440004142a1ed33c8fc2845000424a00ed2cc95a0081400041840ed1f77b52a44200624281ed10d38d2105500501aa0ed0257172a0940e061a81ecfb4ca60309402041821eccd42250840100124080ecc52e9d0850000824080ecc503d90009602201880ecb173e530c140c015ac0ecaddbe8134400c414021ec9ba50d2905400421aa0ec850bf8004050c105000ec6abd6b20c400c4442c0ec2892180a01100120801ec12a47e2a04400461201ec05879d0b081021200a1ebe9b152008d202640840ebdf2ba32804600661280ebbb304d230850e1012a1eb716a6130880020102c0eafc7a4b230000c0402a1eade940200c540c445840eada211f20c540c445ac0ead4b49a0900500161020eacecee72808202260280eaa225a41084600611040ea9cf5e8094050c125020ea90a49c220950e101a01ea8eb64c3240400015201ea84130a2004200640200ea82152d33404000152a1ea4fc0ae204450c545200ea48bc650a4440c425081ea25105520802002002c0ea09aa848808602221100e9fab9ff0045500545880e9ce4b9911054004118a0e9b7dd111041400015880e9aa9e542b0850e121221e9a133248100400001120e9809f692201200200a81e97361b52a45000424a81e95535290b080020200a1e933b4640a0150c121801e91c748101084020010a0e915fe97210410c5402a0e914d07e0a0c102560001e90358282204500501201e8e1cf312909102120aa0e8ce834c0204500501001e8cb6a200b00000020021e8bd5d3f2a44400465281e8bc01c20a08402061001e89394aa20c5200644a40e88cda6b2b45000464aa1e888ec7c2040400005200e8867b382b41000024a21e86fb4fe2840500165200e86497ea090c402461020e8547f600b40400025021e83638272801600261a80e82aac05311000c8102a0e8291698808c40e401140e81d584a2201500141a01e8072338114440c415020e7fe1c9a084000c064000e7fa62fe2a01400061a01e7f957fa0141500145820e7e302cb008c6026410c0e7c518388b44100524121e7a517512081100100ac0e77b6f432245500545a81e76a947c880c202620100e767bc31024410c504081e75a223b2941400065aa0e755a33d120540c411881e746c883008450c5410c0e745be8b0a45000464881e741f65600c010c144040e723914e2a05500561a01e71c9ee70b411001648a1e704ec1530c02002142c0e6ef576d114100c0148a0e6b4c1122089202240a40e6a67e5c2144100504220e6a119c32209102140a81e68965d30b401001640a1e68799bb214140c045aa0e67e5c6e0101500141820e679a0c2230010c140221e6547d6b0b044004610a1e63a58a5284100c024a80e63831553085000410ac0e625272d2204200600281), (96, 84, 2, 27, 2, 27, 0xf4df353e0808402061000f4d3b190094100c024820f4bbfe57080050c161080f467d7a80241600205801f45a1fec8a0c00e420101f4323d2321084020412a0f412e1330209602241881f3f784802040500105200f3f21984910800e010120f3e0d9332208502141281f3e07b5700801001400c0f3bc88022840600265200f3bc023c220d102500a01f3af1dcb010110c1408a0f3835589214140c005aa0f36bc9bb01455005458a0f359d8f22209502141a01f34bcd9d0b451005248a1f329d2b6230500c440a21f3179fed3089602211ac0f310ee5a2a4010c164201f309a357090040c0610a0f2eb79e32a0900e060a81f2eab47931104008112a0f2ea24670a44000464081f2d4c01c0208202200001f238ae992a0c502521281f22c1c0b2241600245a81f2249f8910856006118c0f21c3b0220c5500545a40f1f42803008d1025408c0f1e774f52008102100280f1e6b0ea0a40400065001f1e5c012210c102540220f1c79bc52044500505280f1a77302090c502561020f19f9af60944100564020f18ceb2c3208202210201f18870e60a4150c165801f183c25e090c002460020f17e62fa030050c141021f178fb6c284010c124200f16a1d600801600221800f14467d10b4450c5250a1f1342ae0810450c501120f10f63fd130d4024118a1f10b428e0a0d202660801f0f9c3fe294140c065a20f0f4a5b4320940e011a01f0ce70088840200224100f0ca6a6f290550c561aa0f0c216402944400425220f0bd3fbf00852006408c0f0a13e87004150c145880f08f12f72805200660a80f08d783a2b00500161221f0816d6909401001240a0f05e6224304040c015200f047898b0b440004640a1f04438f10240600205081f040af888b0c002420121eff4732d0810400821080eff40a9420d000c804240eff1542510892022108c0efc98bf91050600a15080efa59e582a10400821201efa38588204010c104200ef9997210b414000258a1ef8887680841400025800ef86866d00c450c5050c0ef57861510c100c0148c0ef3e95c1294150c125aa0ef3b39642b08102120221ef2c4c58124040c015001ef12b6e62108102140220ef0ea781235000c8042a1ef0742822a04200660201eefdde0d3090200a102c0eef77c003309402011a21eee3aa3300841005400c0ee9333403041000014a00ee674af42a0050c121201ee5df4c02240200204201ee30f8748308002000121ee2d58672a08002060281ee14e55e2a4550c565a01ee12ffb50a0950e121881ee0688c2220050c141201edfd3cad10810000108c0edf46fff0804000460080edee9c8930c00000142c0edb8964d230940e001aa1eda62fbd130d0024108a1ed7029f4120040c011001ed65a4049244600615101ed5f86ca0204600641001), (96, 84, 2, 27, 2, 27, 0xfbc353a9230840e0012a1fbb085910a0c502521081fb9758ca220c102540201fb7ca31a2b08002060221fb797ebb0b0500c4608a1fb715fec2304500501221fb5189e133000000102a1fb490e4121004000012a0fb3d484c2309402001a21fb24107d20c41005042c0fb1366b4820010c100101faf0ef3810d0000814040fae497842a08502121201fadabf503240000014201fad25b89290c0024202a0faacc4b89100400011120faa96ea13201400011a81fa77ef788800600221100fa538b211010400811080fa520c302850600a25200fa51ba6e230c502541221fa489bfc024540c405801fa3bb0c80101500101820fa145e300840600225000fa10546420c4200604240fa09f62a0a00600261001f9c0a1bb030510c5408a1f9b4ce242090200a00240f9ac9234014510c504820f9a024b0230c402401221f9865de00b0c502521021f97c72ee234550c545a21f97711d52090600a012c0f976f6540088502101040f96f44700b0850e121021f963a4302041600205a00f96094eb00895021418c0f93e7f8620c4600645240f9347c1b0b4150c1658a1f91169c1334400c4142a1f907b22e2844400465200f8f60b7133044004112a1f8e9d526210010c140220f8e1368c2840500125200f8b94b0c131040c811021f89e513d10c56006158c0f89ba880208d602601a40f889d1160b44500565021f865fa00314440c415220f857754f030040c0410a1f805e16a0089602241840f7ec88f48244000404101f7e804ff008140c0418c0f7e4e10f0804600661080f7dfd584034140c005821f7cee0432241100144a81f7c092f120881021002c0f7b28d202809402021a00f7a7583d00895021018c0f7a52ff12200200200281f79fec232909402061aa0f79b05d8135040c815021f774758a0085600641840f76f8e6f2800000060280f749d8880904500521020f746da022809502161a00f7448f8c2b4000c024221f72c1bed0801400021880f720ef960209502141801f7151e262800200260200f70e27a70240500145081f6ee9a5e0b08402061021f69fc5103105000410a20f69e2f642a01100120a01f68d6051120c602611081f68046722808202260200f66e93e6224440c445201f66b7a3b0b410000648a1f6623ff82a5040c825201f62b9a3810c0400015040f601d55a2244100544201f5f647f100c540c4058c0f5f0e5d7010450c5410a0f5db505b00c10000448c0f5be758700840004400c0f591a3090a0050c121081f56ab8400205600601801f569d8382a05200620a01f569264d21045005012a0f5670db723081021402a1f541fb30084500c424800f53a5deb0a05500561881f535deb12089502101ac0f51824cd331040c8112a1f51329d88940000024120f4f3616c8b0c40e421121), (96, 85, 2, 27, 2, 27, 0x82506fa900602860a28204124faf5c0c1043150028608fb67f2441a204a015030453984120806002012c08226d9958504807030440c104f555c282003818020607c4dc46501ac04cc350103dcd873008c0024400c081ccac73942000603214040e324188a10403019280206acdfa01220819042041031c70fc2085600601a40818a013015a0a80092d10c0c375cf0420500004610205cf84f2528201804954102c774762b01500161a21814e204a0422a06212c0040a079094250440049228204b32590548881884a4030240dc0b0b0050c1610a1811053f4904420100096040797b6342d1103109428603c1fa1a561aa04a4354301dc5971205000c80428080e0b08180002800a0840406cb588c020180090430202f4b1221480218248103013957f10b0d50e5218a180987df49420006012140404a7af14a500030090a82022fe5d4061080408204300fc2b443345000414a21806f4a3594021003301404035e2a1028004004800060115b2d8102081904200100867c72290050c161220804019938184001020050c01f07960090540041600600e59fc8068881880a04300711384314540c415a20802c970895a0a00012d50c00fc97e20421008004482004296a616802182c81430019a2cf204050c1452808007482618483005089203ff61c6688234009102901ff5c4fdc52080188c0440ff97df2a2a080020602017fc30e1680448010004603fdfbcbac2821808984205fefd1339048081800a202ff5cc125290d002420aa07fae0508086290030a4203fce9f65c2034009182201fe0f5cb854a0019048402fefdfd202009602201a007f73f8988906801208440bfb11969c0221808904301fd6594f05082018049400fea1bcb70b4410c5640a17f4650808508200410840bfa06ddc40c11431404285fcf410f414088008c2002fe4ee59a200110c140a007f2205d790603001229603f8adcee04811031044005fc4c7eb24108200a00580fe2478872b0550c561aa17f09d40244202800928803f7dda4c08511031014881fbc65c42618880082a580fddfbaa429404000252207edf2ed680a20062020503f6f89f7c8021438504a01fb78e410640a818823402fdb8540d2209202200a817ed8e42280683005028603f64ff478a104430592801fb267419011081c002280fd845833094400c4640a07ebefea28588006410050bf54a50d82035009186001fa9b5dc0040aa00a03002fd4d7ea80a041005200017e9a2e8090028802805403f42f39348d10031010a85f9b9942a0618204a00142fccd3d93200d602641a807e607c4c8062a80282c603f281eef02d05000096085f8fe982c4408c00c82402fc27eaf02090600a012407e0573141884a01008d103eff543408814401402805f79e40360412a04283102fbcf0ffd2a04000420281), (96, 85, 2, 27, 2, 27, 0x863507d590002800a0940431a347c088118018048061881e0b044802182084030c2f767b200510c540a80860dfa6215a2a86292d10c305e17448541032014a82180eb38416128040c30430c0277ac094550c52582085f8780d01048810a0400c2fbcf2542d144314922861784ba820680a1820a1430bb2325909444004250a085c8c91a99a2a0620ad50c2e209d222c304394804861703a562468881880a5430b6e6afc2141100104a208599ccd6906088008256042ca3903449110010542061600d4aa42822002095410af67a7d214010c1042a08570c59c888820640885042a670e6c8c34409502a8614c4f5ae4400a002825030a5ca1d48800400021100852dd5569068200402960428cc92c8250000019008214383174140ac00cc300309fc28dc890c00242012084ed64640484a81090c104275e97604825038046006135f1631140040044020309a2897b080940e061880849bfee89906a01208d40c24b6a3f0c405000046882122fc65c400a200a81401090b60cf00c100c0448c0848049251480006030110423f78e62481080184040611f96e504488a18a0a40308f74cb00a050004208018474c92a1042a80280d204236e12c0ac2543848688611b104be028221828914108a3025511014000118a0844f106790a0a00022d50422526720a91443149280610781484418881888a48108341d0121005001012a08410c35d94068012305404208438340201800804302103db47246028180035430806f5f20a0900206080183ef59d88580800010450c1f3c841c02104315003020f8ef942620800082054107c36ac2210040004122083dc1bb64520100112080c1ecf1c0c8200800900b020f6670d2060201800114307ae376100894020018c083d2dfea4986007208090c1e4a9ee044210080440820e6be920608880082a4010725ed5e2a4050c165201838ce3f191822862a0950c1c5263dca004400582a020dfd319a1008200a4010106d3d09d0a50600a2508183693b829046a81280d6041b3faf1825114315940820d4222cc048aa18a8b0030677932b20804000412c08337fd1100a20862a20104196eeda4a414001082a820ca502c6461aa04a83543064c8aee200c202640200830b66ba4122280282880c184522ac20318099842020c0429a81400c0044200305ea4b11030d4024018a182f20bc814a008609211041739d45221018008944020b64631a6188400c2858105958c5110c42006140c082c2d9128522300312840c157311348d00400410a860aaa524654800180c85030541136120d0600a052c0829dd1ae8420006012040414e0e808a8014005848060a5d71e6108a0188c9101050cc0fb2a40100164281826f90d991020862a0140c134469a003110010141020956474e14028000c310304a281262945100564a20), (96, 85, 2, 27, 2, 27, 0x89bb8de24584007010090c4dc7fe54240040048028226ca8e18440ac00c034031356e1c82a01500121a0189a1bfda4520206012880c4c858c548c21008004a862627fe3a1480a1824a103130592ad020c602601081896d5ec841a2206202890c4b5090680314431512102258a00e90088218a0820112be6d790b001001200a1895a5dc780828862a045044aa4bf60c83080984080625113604548a400cc94031282a3fc124160021580189404ebc9120a06002d40c49db61f4240540048628224ec4eae028aa18a8b1411259ad5d224410050428189289380448020001089044897a19424140010822822436a466428881888a541120b44412085400401ac088fe0a2905a20862b2010c47db1a00ad0040049088623a88db00402a1820300311d2bd6e204420064420088e81426942028609294044704479c020003010030223555e7210a080104a101119cac813105400411aa088c1be7c9106101300140c45df5e74211143149420222dee140461a004801443115f367c8a0820222010188ac3dc310442810a0920445573a788231809904902220cf6940612a1c28304310f6a4900b055005218218879898e1580806010510c42d2f59c241143158428221618040648801882840310ac203f0a401001640818853bdff8184a810a0c50c4268cedc8c21008104a862124fd904288000808441104a6216220810214020188208ff78184201020850c405e33548411001004a82200728064118404c805810fe83592220c60264120187e94c8d8502a00230c40c3f43167c8005400506a021f685da20612a1c2031430fa9e53b090940e0618a087cd8698840008009004043e5b3b3c8c15031106a861ef4792446128040834430f71c242200450054120087a9ee2f0584a810b0c10c3d16388c25014005942821e74432e46180048805430f1ca3172a41600265a818788190c40402060008a043c3c00ec8301400514b021dd35d64468aa00a8b4430ed8b83c2a0d202620a018764419590848870a055043b0698d441150010562021d5c3cbe16822182c91430e86a925284540c425a808740d0791182a862a0d10c39bf60cc03114315143021cd32184101aa04ac30010e634ca52845400425a808726babf9102a802a0d40c390542b82c044005820861c730e4e10800000c81010dd08e3d2a4440042528186cecec00504281090800c36675d8c24214085842821b0f10f4401a204a814010d860b652b0000c0202a186c2ccba1906b01308d00c35821be88d104315108861ab6e02e1008218ac01010d402d142001600201a00869fa5cc1068206402920434e9f178a4004305808821a413ce44288a18a8a4410cf3b2242905000420a20864703c490840810801504322bd9c4cc40032040a861910795c02802182880410c7e2a1c8344400405121), (96, 85, 2, 27, 2, 27, 0x8ed0499c9580a00010d50c765c24242c254384862863ac6a6ba0400c004021031d489bd6280050c1612008e895e7a8122b00302c40c7448b8b4284080288020639d953e641122042815811ce71c2e020c5025410018e7255cb94a0206032950472b5cab025110010940823898ddb20180c0040a1811c4afffb080540c4618808e20b2a610a0206002910470e4aa744210801840302380c000e44822182895031bfdbeff0b0400c4600a18dfd727a880820640884046f3b9cd40405400406282378ea90a500a0008415011b7cfb8930082022102808dbd91ae1120886082500c6de4e744a435009086a8236cf90b8010a200a010811b4ccac82941400025a208d9bfdd415a0886092510c6cd313708111401414802361f065e01824004891811af118f12905100520aa08d7031ec9182880280550c6a4571820431039004482349e8ee65610a042c25431a4e7c020a081021600018d128fa89420a00012d404684684f0891140141480633feaf8e14022002c110319de592e094040c0650208cec5e2114828802b05104673b87ac011543151620233958e026082c0042b50119b135e12a0c0024202818cd0995e81a8006402050c657d9aec0c3540950628632b2385e0288a00a8a1411937500f2a0c2026602818c84dec78584a07030c50c6402a7bc2c2003818028631d339e44610a1c28244318c8e3e4084040c0250008c5036bb11802860a0910c62748a00251443149208230b60b085688a00a4a4431820017622041005402018c0471fb91022862a0940c5fa0685009050000160062f7cb8a6461201c08154317ba29b82b09102120a218bb9a03e45a2280292890c5d65a710a1108018908022e74b9be1288a00aca141171cba6b290d102560aa08b5e17811120206022900c5a98c9dc8d10431510a862d1dd6d641124044815811669dc36224540c445a018b2dca828528100512040c59407cc02d144314920862c4f71f2041ac04c03103160eb99528085021212808af25d2844a0086092090455d9b4f8a0140011828022ae37e7254a0c0144a503155fbf1b030850e1410a18aa1aec98184801020450c5493cfec240400018228229f6d656410221828158114e2e6592a41500125a818a70e7fb95a0a800b2d50c52de5aeca834809982a06296ccbae0402c0048310314911c062b004000612218a3b6bf590048870a05404517297048c05400406a8628a84f985280a1824a441144c22252a4140c025a818a172486902228628294045064b0648310801810b0228236e38648280002b40314094e4f0b455005658a18a0084ea8084a01000c5044f98b2948c10401400a8627b759da618080002a58113bb584b080110016088089dd35a38506301330840c4ebe9b12023140940450227584ca8618281802b4811379f5a100c14000058c0), (96, 85, 2, 27, 2, 27, 0x9313c3ab84a2206232850497ec5c48ac150311868864bf53e8e141281c0c310325f6f8110b0d40e4218a192f7d5c88522880292440c97bcd8f4a020808880a024b5e0d64048aa00a8b003257f16d8030140c00182192b892789844301108960495bfcf2248300390404064adf454410808180ca0012566ea1120c01001042c092ab6d441422a00212d0049512f26c20258089862024a60a8221600a18242143251277c60b4550c5658219283ed998040206020860493ca7accac00430580a8649db82e0162001904004324d457eb2b0800e0602a1925da287106090012252049104b84029150310960064840f7d042028000034412411899e00815001418409200dcc68522080292040c900585042914431492206480018e6121001c0c014123fcef65220450c50128191fb078a900090010054048f9a5024283080988020647bf386c448ac00c8b40323c145850a0450052108191c231d015a0a86092d10c8de3e2948901400414a0646bca1d456088008c2443235322a720c01001442c0919a82860902200208800c8c85188c8210001100b024632a1a806088008020432312f2bb008400c4400c0917605fa848488109045048ba7ccbc2811001184206459ac988528201804944122c87faf2901400061aa0914cb6bd104420102092048a38bce4a024808882a02450eb7e05600a182424432262cb488b4400c424121912e8ddf8486a812b0c50488e620a40105800816202445ccd0c4212804083441221e873900842006000c09100c8179104301120940c875c2450291403109200642dcc962418881880a581212e7f013089402011ac09086d79105a0206032810c83fef16c290000019020641de6998628080002a44120a88c84114400c4140209047591784a28862b2450481dd4fb442150010463024054dc6254104044405032021895a230d502541a218ffeaec619a220020a910c7fa09df083140010129023fbb8a3e14820000c91031fdad82081081021001208fed281e942200621214047f5feb948941032014a063fafc4264110a1c2825811fd4185821401001042208fe5dec29846a01208d6047f0bc9548d05030016a863ef9f26e4118c04c825811f7cbe1f00c11001448c08fb90a00992210030a140c7d635ca48005800806a023e730df216a080104a1431ef755a430884020112408f72ddba14a008009211047b0d33f421144014922023d7d32ba54002002405031e9f73322a09102160a018f3a756a0922a0020ac00c79bde81003104314101023c99840066028180234431e41999f080140c0618808f1dfa709922a0620ad40c7894c05225104314904823c3c605641100040805811de9bb7a28005001612008eeff9a585840810b0050c776dce8c21118019942023b86a97c168a218ac90431dc34b2129045005212a0), (96, 85, 2, 27, 2, 27, 0x9908912704000060300004c7fcc1b2451000105048263e324f8540281804340331e32630084550c52580098c4a6ea1422b00312d004c59fa94c2504400592282629e6bf60400a18282103312949b7280c00246028098944fff04048010304004c301e22c0c150311062866179cd960610a04282143309b531930c040c0152c098481a2510842810a09104c0156e0005140310120825fe86a9c10102042c00012f9eb0cd330500c410aa197b350b60182286280810cbd811a0884244085028825ea318e2228880082a1412f4721a80b0150c12182197a2429b14060812b01004bcf78d8824200081800825e4fcdfc16888188ca0432f12f0110a0060022108197695f9204a28802924104bab06d5402258088063025d46c4ba008ac00c0b1012e92c00d2b001001202a1974761b69182286280950cb9f2777c28358099862065ccc122060004004204012e6192902941100124a209719b30b85020802b0040cb8c2383c29140311922065bd562b4010aa00a830812de74aed01444004050a096ef5338886220620a8604b753dcb4ac20008080a865ba672711208218a402412dc9fc90214450050522096d1f86f10448010205204b67bf18c05144315122825b1aa1d80280a1820a0412d52d51529004000212a096a951d910621003221204b4d353d02c140310820865a23d0da241a404c211032d0c462f20446006452809685bb4298a2a0020ad504b36c41a4a405000086a82597193005082a0024b4012bec0ea02b0000c02022195e8a9119400a800b0d404aee905782c25038186086576e66f0541a204a414032bb458132809402061a8095da276d80862812a08504ae969d100d1140141408656e20be654828180cb5032b6f85b90b411001248a195b4ee90982280620a5404ad46aeeca015431586a02559063d6528a0188c95412ac496bb230c4024412a19559a23a1420a00012d004aa83f04228308098804065508b648408881880a4012a4ebbdb2a01100160a81951f5dab9480a800b0d504a8accdb089104014108065452dc8601020180811812a0986d0020060020100194e8e01e00623003028204a6cbe1eca821008184a06531beb22541081c04250329849b0e230950e141a2194b7073c0906b01308c00ca546a4608c150310068865292ab71221880482224128bcc5462b0000c060221945d10198584a870b0c50ca1c7bd588d0503011688650d105d8568881884a443285c0fec020d2026008019415c9760186281280810ca05b958882158019069024fd44a384418404c0040327aeb32121041005002a093cf55a58500800030440c9c7887222c000300804864e2e9e781288a18a4a041271252b32b001001602a1938376da982220020a94049bb24ff224114314844824daa699a141880484210326b851142a0d602621a01), (96, 85, 2, 27, 2, 27, 0x9e1723360982206208810cefae2b2c0c3000910028677b890b22002c004231013ba5d5f208085021610009dc8237785800860b0050cee28aa9ca801430584a06770ccb284100a002024813b237898884400c4241009d8b002395208800b2540cec509460a11003109080275d968700182a1820b0813ae9da7a0a014000618019d69333f95000800b0140ceb1b59e802318099041027577c44102880008082413abae5fe008d6026418409d50d97618401001081204ea7f3b34a431409484a827533edb444002002804033a96fce629080020602209d4b5a8590040810a01404e9f5a6e2250140049448274f340981408a18a420033a74bcec908c6026111409d0f9d4880602800828604e8210a40281103108400673e71b86060801888014339ed1d230a004000610819cf0f2e914040810b01004e5e755c8a50400019288272ea9da054820000494033966d02b208c1025402c09ca5bdbd05a2006232010ce3e3775c021403110230271b1c54654180048c050338c1291b208000c0402c09c5b722780422802a08604e2922a80030043041010271368e50061aa1ca030433857323a230d50e541a219c294ef290280004021404e11350aca815401586a067041d490568a81884b44337e52432208d402441a409bd7f24714228062325004dde5143c2d114315942866eaedb560482a0028b1033745b2e3010050c1410a09b9c3dcc8502a80290c40cdccf4fac28014305842066e1fab60108281804b00136f224a102085021010819b56248c95a8000412150cdab0610ca014401582a026c62851a461a804803543362e9e30880c10e5201009af9ef4785202860b2840cd7bc55b8a4104015808826ba11b78428280000b44135c8f60d2b4540c425aa19ae22cb690603001029604d6f3050402040000023026b2c129226a0019028143358f54b309091021608a09ac19a5e8022a86282c404d56c9c6cad10401590a866a73b8384280218208441351a36e22a09402061a019a48d6360422a00212c004d228675425104014902826911f6ca4282a1820b5413485757012446006150019a3c3bca186290030a5204d197e248a424008182882683d39904410404400403341559fc884000c0241009a0419dc94a80064121504cedb4738211103119400266f52e32440a400c01503336a65d6030450054102199b5318b9506207230940ccda24604201440148220266b35901018881880a28133597127030900e0408a1999fa89d90a20002221504ccfbdba48220808800b0265a37b305088c00c4a40132c095d72a0400c46028199555eea186090010a5204ca743e840824808802206650cdcbc141a0048c1003326f5d5108455005258809933de0d91202800a2940cc9253be44c1500104628664709d841288a00aca041321e809f294010c1642a0), (96, 85, 2, 27, 2, 27, 0xa3478aec9586881290550d1a10ab78a4054305868828d045242448221820950346773c362a09502161a01a321b9a704228002324005183c24e001114014140028bc96d28418280000b48145e1026d2244600605281a2f03cbf95a22862b2950d17523b9c24154015862828ba4a4ce460a200a8154345b5089129044004212a0a2d8c2dd85208800b2440d15e7e4f48100400410a028ada0061101001c0402014537d4b9004140c005880a25fdab49800900108540512bdf74c8811401504a06894cf27610800180c8101449e95ef208040c0412c0a2482edc8520200012840d120ddce80c2040850008688e90a9a4082a0020b5014445d8bd2809102120a80a20ffc958486a01230c5050f57626443140310523028785282e0202a1828314143847deb2b09102160aa1a1b3110e9484a81090d5050cd966c0a8250380868068654e96a268281802b1434328b2e62200500141201a1842b0d81a2200222850d0c1a7f44ac11001084a8685f8cd99120021824024142f10ada0a0540c461801a140cc7b9404801030540509856cd803114315141028488c212068281800b1434234803c1081200210840a1100aad14028062305005072bc3ac8304030112b0283909530141a81c843003418738fe0345500545821a0b453221100300100900d0547533c8d11031114a86822bc362421aa04a0354140eacfc30244500545081a070ad8785a02800b2850d030d02242104030092202812573de048880088a103401f32f12a0100c020a819fed120e00802800808104ff07a1e88c204085008867f6191f25002c004435013fb064d72309002040aa19fd6bfba09a2a0620ac10cfe954afc02250081063027f26593854820180494033f8e83932a404000652819fbe93fc10602000029204fde44874a514401492a827eeb99621208200a401413f70ef6023405001052219fb28c9790608860a25604fd00b93c08214085042067e24919454188048c24033f00a875020110c1008819f78e06795220802b2140cfba7d6b043110310541027d96b4ac418ac00c8b4813ea8a0bb2b4440c4652a19f390d9300423003208204f9b757f021144314920027c418722561a8048435433e1ea66109011001208a09f0d4f1a9180a00000d50cf7f4b1f8a1104015908027be65c900600a182020433de9708830c42006142409eebadcb05202800b2800cf75834d08c010000048867b97b5710080a0020a2013dafe4513045400415a809ed152399080a00020d504f60f40e220208088804027affa816010a8188831813d69aec88b4450c5251219eab23179100b00120d40cf53713882c254385860867a4f3f1a148a400c491033d1a46a0214000c0042209e7637b28500200010840cf34f7e4828344095820067953dd0a0400a182021033c7777a110890020108c0), (96, 85, 2, 27, 2, 27, 0xa8d62ba11422800232500544bc728c8805400506a06a244c8225410a0424250351144c9a0904100560020a872ab64986820040a9605435f85304300000050102a196c4c40612a0428304350b98d4a220c202640201a84b11af91848870a0550d4243bcc88514431512882a0db4c9a2220801022141505e18d30b095021618a1a827757848462012088a0540a91e9c0c014305042869fec229a56a080104a5434fc2418b2001100140a80a7d13ac39584207030950d3db4af9089014304148069ebcd2e60080a1828a1014f4ceb73034410c5440a1a796b464400208628008053c85e33402048008023029df3213a241281c0231034eb1d41a010d102540820a74f0e401922a0020ad00d39cba73c8d15431516a869ce54a0e52088188c25414e64ef1c8940400025120a7253e2800622862828205381967fc20154315862029c007550528a0008494414ddf14df084450c565080a6dcb43581a02800a2850d361ef31025050300960829ad721ac0118a04a820814d5e9d6b004410c544080a67f2c6d11828802a0510d3391bde48311401414b0299ac92de41180048805814cd45e9d215000c8042a0a64f17a390400000201605326faae0a1058008968029920ef425088400c485014c8d97050a01000020881a645216d04048810b0400531b0d992430003005050298c9d0221080a0024a1014c351d230a44100564081a5e2db8f840020003084052eff8520ac15431486886970a77ee14000000c01034b6f9fb72041100144a80a5a3b8fe9180206000950d2d0b42d0890480081280696734b2a1408400c401034b2620a1120500c410881a5910b4e10a2a80282d1052bfe0ee4a021808884a0294d621dc42000000804414a3c618d024140c005881a505dfef1420206032900528181fe4211503109620293d2040e420080008254149d70e24095040c825020a4e564900920a0000ac00d2703cdb48424408402a82935ce3ea1608200a4014349a540ea030d40e441821a4c95e938422200232840525ef4920291143149400692d1855a040aa18a031034941e9d52800600221280a4979a9c9100286080940d24738f78a51443159288291433e92541a404c41503485eb6ff290110c160aa0a420f91c886080000a460520d97150a835039086806902496926410c0442250347f4d1a7020450c541081a3efdb2f0582200230810d1f72ebcc20300091802028f6f17ee018a218a8918147a250ae0b0540c461821a3cb34c6400608728008051e468fdc0c314095042868ef7c54a61120040215814775dd1830c5000414a40a3ad8692184820640892051d5849588c254085068868e6ad4645402c004c3403472d791a2209202240a01a38e6a98992810050a140d1c495c180c304095000868d8204d266a000102854346a701be284450c565200), (96, 85, 2, 27, 2, 27, 0xaeedb2248182a06200c50d7650c4848825808806a06ba5c21d05418404c404035d1677a930c06002152c0ae88a0240508100510000d73de05788515431516882b9e4d631161081c0422435ccdc7812b081021202a1ae64970010428802805205723b9a748915031016a06b90e646e4602a182835435c7b81da2a05400461a01ae2dc9921520086092100d70b861482831409584006b85b0cae10088188c21015c1eafae0b0040c061021ade70b2715068812b0500d6d27ccb24030039040402b5f0c44a068280000b1435aec766323080020402a1ad72872d1522206232900d6b2fa95c2900030190206b51a5b5a2480c0042a1035a7e3ec4920c40e411101ad115c5304222802b28005686767780815801906006b3cfba24440ac00c8340359bd492c2b4140c025a21acd9d2ab81a28862a2450d66c78e54c500030050a82b334735e0118204a801815972d111084400c424080aca1271a40422062008a05642d02b02140032090002b1e4455a1008c00c4210158ce9a89214110c104aa0ac60b8061840b00108d20562f405588031409504802b0ee54e86602000021443586e09f529041005202a0ac3582d19184207020950d618ff1182001030184002b09d0f3e160a218ac1143583a79c20b08502161021ac177d9395200860b2140d6077222c0c11431504286afeca6c20408a18a0210357eaa9a7020d502541881abee53e64182280280890d5f1ae8cc8814401502a06af687c6a50028000435015783ae462a00600261201abae4b2c042820641280055d4f42e42905030096206ae91ceac52800000c8441573277812101100100aa0ab6e3e1c904028008096055b5ecaa22c21438484486ada857f9128020024824156b4e87d230540c401aa1ab4ec1838084a810a0c5055a52d61ca815431586a06abfd521e561a21cac154355e196b5230d102500aa1aae74f3411a0880082510d56005d5ca100400590a02aad2d4f8060a818803043555bee702940500125220aaac09211580a00030d10d555878cc0500430510282aa5ec05e5012a1c2c3501551e8dcb0a4400c464081aa89cc2e8502b00310c40d5430971c8825408506a06a98c0114160aa18ac304354a7ba4c291040c821220aa3854ab84008000304405516f50042140032090202a880d5285012a042434015424191920c1600205ac0aa0c597c9182a00200d50d4fd4f2fc8115431516a02a723c1fa4680a1820a54353550f332b4110c164aa1a9968edc900428108094054c8bccb0c910001050806a5fbb04c4402c0048340352d117932081000040ac0a95f51f091a2080282150d4a42d7cca021808984a02a4f3a81e410201808158152731b520844400465000a9387e7b84840810b00505493005280c15401506086a39fc1fa4410c0440250351c1e1160a0950e161801), (96, 85, 2, 27, 2, 27, 0xb5f037ef10a08000225105af70f9044c25008046286d7875ae6018a0188891816b5aceb40841600225800b56f1dc194848070305505ab504ec20001430404402d5900a06011a404c811816a85af5b2b01500161aa1b52704e31582a862b0d10da83fa96cac14431582a86d3e9c07a4682a0020b54369dca7662a0500c460a01b4c4da529802b00308d405a5fa7368a914031192806d2a9e006041a204a81103691e48f4880c50e521100b46aaf920580a80090c10da31cabbcac04430582a86d179c2a85602a1824344368a31358880850e121100b43ffc900180a80080c10da1fe79e0ad14401492886d09e031e461001c08054368266a3f208010c1402c0b401adc8084080000842059e97d0b24021038044402cf3b99645002c004c34016793c5070a0d402461881b3bd64b00584081090010d9c8c83ec2c14001182286ce39ab3e5600a002c25436719f02c0b0050c121021b369961e05a2006212010d9afef848a515401596882cd789d402188c00c2a0816641689320c550c545ac0b318680819a020000a910d97da3ad48501400414a82cb8615764412c044835036597a3362208602241201b2bb049984220862b20405955864a4a515031096a82ca458fde5280a002ca54165173d550800500121080b283bd791500a06030d00d93b570242541032094282c9a35ad8418201800948164ad94270808602261080b2568ab29020b00102d405922e104ca110031190a02c8eea3a91600a18242243645b275d11044004110a0b200875495a0a06012d50d8fa0ab40c801030044806c7cb15120102c0040318163972d0f230c40e4412a1b19b2ad3004490112042058bbade580435409506082c566edd2648880082a50362aee9930840400065080b14c57508180280080850d8a4910c4c501030054a82c51befba50088008425016285a5d530806002112c0b11de14e9582280290950d881caa240c34409402286c3831a6450108040c240161bb4d7c230550c501a21b0aa8b0d0106b01320c00d8478f8e40835409406206c1bda22e411a404c8158160da82cb0b415001658a1b06d26db15228862b2500d8314d5882825408586006c079a99456108040c2443601f609e2b0140c061a21b00de80615a2800212510d801b22b48c01400404a86bfff59664088a18a8a5015ff3aa572a0d002460a81afeb15720122286282800d7f2a2bb08501400414882befd4f4616028180c31435f669ab0295040c825220afb1b2ba4522006212080d7c84895c2830009180206be3663c6548aa18acb5035f19264c2b04400421221af8278a19186a07220d50d7bc840f82831009184006bdd146e2508281804b5015ee397ef200d502541a80af43e7f80102286280800d79f49d7c2424038182282bcf0c2dc56088188c24435e4aa28c894050c125120), (96, 85, 2, 27, 2, 27, 0xbc9c85a68504881090440de4c86d388405030106882f24ff516411280408358179099a3c0a0940e021801bc77e2bd8504207030840de24f47780c21408504086f123033c4212004081441789147800209602201801bc47ff1f15222802b2900ddfc0a8302104030092002efb310aa548221824950377c673dc220150c101a01bbc930f71504a07030d00dde077b5ca515401596a82ee9b6b7652008180c2541774088e82945500525a20bb98b6241082a80280d105dc1ad6d42c04430482286ee0af4e610802002c810176f561a50a4100c024881bb4ca4848522a86292c40dd93d7f140201400404302ec6a70f8148aa18a4b0037621cb030b4510c5648a1baff8c1894882064109505d79da13c8c34039102a86eb6e54e10110a1c20228175b4c461030110c1008a1bac1e8df84220062320405d52ac50c2834009182206ea7655be4108800882581753134190a0500c420881ba97d3b381808860a0450dd4afed844d05000056286e96b69d6421001c08054174ad3043080d402461880ba53ab519186007220150dd1c53e34ad11001094a86e8a14f4a5288a00a4a541742ffdcc1041400015800ba11e06c9060a80082d605cfdb64d08c30009000886e7bdb36a418240040958173c870872a0100c060a81b9c2819e8584287090850dcc4636ac8210431500b02e59d50b61412a1c2c310372cad70b2a08102160281b94ccbf985000800b0040dc96ee1888500000110882e48329fa160201804114371e6b5a11245400415881b8ea5296192290030a500dc71bc8102d11001094086e38d9dd8668000002844371b1560c1044600615000b8b0b58c8120a00002c40dc3ec4f64a111431494a02e1bc99825600000040543709a8302230940e041a21b847793840a02000028905c224f428a905430596806e10c68340088a18a8a0017080cf4110896022118c0b83ee4db9486a812b0d505c16c9f122c20438480486e0b44b2a1012004041101703b4a20800810e100100b812bf169582206210950dbfca1d704314031052102df80baa610000000c01016f9e3d4500c16002058c0b766bb1d80440810a00605bb2f8838a901000194806dd7b0a805610a042424436e60e0e32845500565a80b6f944820582886290410db7761858a504030192882db712832128a0008491416da34b692844500525280b6c978b240402860808a05b58ee65cac20008180a86dabebe7006088188020436d2d10eb0a4040c065081b6963f3c8580006010050db466a09ca504400592a82d9da79290688a18a0a2436cec54cc230050c101221b67068f784042070308405b281484c8d11401514a86d90d6976160aa18ac31436c4cc2093081600211ac0b611bce59500b00130d40db04fb4dc0501430514282d7ff125e1618204ac01436bfde5290a09002020881), (96, 85, 2, 27, 2, 27, 0xc3f527f41500300110900e1f77d6044c050300462870f535fe266008180225438755532f0200500141081c398f0a39402a802b0d4061c3bd4ec05054305162830dccc5a82412c044230038689544e2804200660200c327106e11a0080082110e17e8678428048008822070be61c6a400220020150185d2f69c208d402401a40c2c5a30a0520886092400e16231e5448218088442070afc1e9066208190224438540b143030010c1400a1c29806a915a22862b2910e143f43fca011001184a0309fc6a82541a81c843503849d6e962b09002060a21c22e3e6390048810a054061030e5ec020140050430307ff5cbc520a8188c344183a406962808502161200c1cdfcc49180200000950e0e6c9b4c0314801912303071b95fc560a200ac14438372f4f92a44600625281c1b46f178422a06232c4060d1ac5a40c15431406287067d4d4a108281804b101833d1e140a4440c425001c190c85f9522a802b2d40e0c2276f40304000012303051dcf061288200ac81418227170c0301400001821c10e1e8c1586001210110e0841ab824901030054407036be286148a8188cb103819ad153294000c0642a0c0b628800106101300000e05b1372ca810401580a0702cb2f58011aa04a03081811c32810a40100124081c07310360122a80282c00e03070b622421038084483012548de4008a00a8250180697b230b0810e1600a1c01ff93295a2086292150e00b4941c8304000112b0300572c02100200004110180073fd22a0550c561a01bff0374395808800b0550dff4b80d24231039044502ff99e7bc568a0188c94437fc1ce2e0108502141020bfe0518e88842010088505fef984d24d10001050486fe96da76160aa00ac31437ee24edb080040c061080bf63850594a20862b21505fa3e226c2c04430582286fc7018082188400c280817e3259872a01200260a81bf13afc794a2a862b2d505f7f5bf14cc21038044a86fbe2e13616022002c11437dbef5b30a09402061881beb141121180880080510df57cb9b40c21038004286faa2665452808180ca4417cbb64062a09602261a01be4d08a29040a80080d605f1f88948a425008186882f8a90508561a204a414437c405c202140400005220be175e6014202860929005f03b24444801800844206f7e290d2548a400c495037bad4c9b2b0100c060aa1bdd0f09b91222802a2940dee28716ca000400580a02f6ef1f1841024004014817b66c517084040c065080bdaf9da890208800825405ed4d0c70a111431494802f6984fa616800180c81437abeb530130040c011021bd5614f68982a06208c50de9b087c0c311031054902f4c7cb9a628281802b5417a4a8c5121401001042a0bd1bb9bc9186a87280d50de8da5e0c2835409586206f44f2f8c468a218a894437a1d17d52844100524280), (96, 85, 2, 27, 2, 27, 0xcbf7bd9710868812a051065fa8762443150010563032fb421c44282018089441979b710e224150c145a01cbbc410a8522086292040e5d894dc224310090844832ec395f0018280000b081970cc9c91209602211881cb8491c90100b00120c00e5a8317208c054304068872d144e4e461281c083543960c9ae08100500101120caf9b45b85a2800232450e578afda028108018800072b9d38304608a18a0244395bf450b0245600645881cad75e481860b0010ad206565327a428044304822072a98dcb8660a81882344395435da8904440c415100ca9f37068060a80082c60653dc9150890503001680729af2a9a0688a18a0a14394b59fff280900e060a80ca4e352e4486207210890652498c02422103804450328fdf45e561021c2c05439468f6c6208c402441240ca1b76c898a000000a1506502bc2c82c2440858208727fa32a9008080000a20193c704612804600621280c9adce9b95028802b0540e4cfc586c2c104315802872653dd72061080400214392a47ce60209602241801c929e0981062280282920649175770c41000104088324473b30610240042148191e3c5870a09502161881c8e92c7e10a2200202910646012c14cd04030052a8722cfd616541a8048c350391439dd01201600211801c89b19208060900102460643696690a90040049080721abe4801412804043003907c7824804440c405100c83bb9761060086082120641d1c4e0820540040690320d06cfe540a8188c35038ff936dd0b4550c5258a1c7da399048a220020a89063ec2f8948d14401412a871f2f0ce8618ac00c2b4818f7d476d2810200a20280c7bdffe89520806012540e3d7952fc8314801912b031e989afe0018a04a821018ef4ff60294140c025a20c76d35f80180200000810e39e0898083104314109031bdd4ad25218204a405418dd0332c2a09402021a01c6b69efa9504a07010d40e35818b2028218088840071a90027261004004205818d3657ef200110c140a80c67f422194822862b0950633ec63fc8c00430500a87192819c210204014401018c6b0c23280410c560280c63274e31184001020110e313b74720401430404483180946491618a1ca422438bae9cbd3000200210280c599b21a8886a01208c5062ca74974c204800842b03164a9330548aa18a4b4038b1b9270810c10e500120c56cbafc9044b01100d60629ee6e9c8d14031112a87143e8c045412a1c2c34038a17a01420c0500105240c4ab1d4795822862b0950e24d34f34a814031082a0712351e240210204280041890bdda5290d102520aa0c4720d781060900102520622a6f6824421038044483113bf7c90180218208281888a2cfc2101500101a20c436e368988420100895062195b16c290403019220710b111f2568a80084b543882bcd1923045005012a1), (96, 85, 2, 27, 2, 27, 0xd512498290448810805606a79fd2744c05000046287539a137a62a081902a541a98174320a44500565001d4a00fbf0186a812a0c10ea4b186904405000046083522305fe16888008ca143a8923a7d09084020210a0d44580a44582286290890e9f148fb08c050300068874ecb84b610120040c1101a6e1117f0b051005608a1d36b71f69482a80290d5069b0615dca510031190a834d5bdeae5210a042c2541a694fb73230550c541aa1d341589085a0280092850e9837255c28114315842074b6fabc04402c00403403a5b752ff0a4550c565881d2c676838520a06032c40e95e0bd14c915001056a074aadbe645288200ac8441a54447b9004450c505080d29c0b1e48842010088906945efdec8515431516a83499b729e1688200ac8143a46b9b1b2040600245280d1f3532e9582a00210d50e8e7786d44c01030044287472731c02200800022041a381496d03085021010a1d1951b3b9506b01330d40e8c0741b4a811031084a0745e64e39101021c240201a2905255030140c0018a1d14627fe0180280080810e89c1a6ec8214801902b0343d5c824500a400cc1401a1e2b5ea208c502541240d0c5d4420902b00308c00e8625836cac31039184a87430b37a2448a200a09503a1509ad70808002060080d093764c0520280092800e83f8c9a8a43540958688341b14a185080c0044a401a0bf6962290110c160a20d05e815385a0a06032c50e82a4035429050000962074138843a5688200a48543a0850ef820c440c405240d040783384000800b00406813c925408254084062073f88529221028000231819f1014eb29005001612a0cf75d3ec1982206208910e7b2e5524a811001084a073cffc9b21088200a481019e019e042a1040c821201cef2b2fa8580000010050e77789fa8a1108019908033b9b37ba2008c00c221019d9c9e710209102100881ce9645691186001220110e745823a420054004862033a29bc926408c00c225039d11b6e90809402021880ce73d6c790420062201606730cfbb08825808806807395083f90280a0020a2419ca084e80305400401821ce3146fe95a0806012550e7175fd3448058008462073893e6440618a04a820439c20105d0241600205881cde600d28184a01000c50e6eed0ea2403103904440336c9695804204014000039b22032e2a05200660a01cd9054f78580806030450e6a726490831100101490333b93d380182a0020b08199cc704b2b084020612a1cce1d1100084281080810667017a5c8814431502a0732c3bbc05000c00442401993fb1772a01500161a81cc9b407410a02860829106636468bc04004305002833158122c50800000c840198abaf5309015001618a0cc53e2fb8182a00220c50e61598054a425008086a8330922a8c441ac04c83403982d9fae0b4000c064021), (96, 85, 2, 27, 2, 27, 0xdfa1308385842810b0850efc26ddd009054304160077d5f617a4102c00403581be6a1ec7210950e141aa0def2064d84222062328406f75f25648911401414a077b9c3bca6218804822541bd7293e30b041005600a1de83ab4014229003125006f412860cac30409580a8779edde461488a18aca103bcf15828024550c505801de49bb004580086090090ef24793d0451100105408377f70a1a6182c0042b581bbabea1c2b10400821221ddceefd68582286290850eee57f4a4ac35439486a877707d8060208218a80141bb580593094140c0658a0dd927d0e1504301110900eebf6405c8905400516a0775cd238e161221c2c1143b9ef67e70b4400c4640a1dcf4a5668500b00110c40ee6a4b348a0010301848037340b06c508a400cc9401b99584db284450c565280dc7d2f92192230030a900ee3a28e00890040041080771d04d94548aa00acb403b8ac7f970840500165080dc54eb8f85208860b2440ee1d054e4283500908620770633de0068a81880b043b81f46282b0d40e421a21dbffa3520180206000810edfa8262444250080462836f9060ca5602a00243543b796f9f50b415001258a1dbb1573800608800824206dbf3abc808354095060076da6747c1618a04ac2043b68ae57d3240200214281db25631400621003020206d8afd78402054004063036c27813610088008c2101b5a451208344500505121da79ef510582206230810ed2b9a5fc2911031194207682013d2268a81882b143b3e65cf320c1200244ac0d9b0a89594022062309406cb4698102d410020940876433bafc461a81c883443b1e958e3090c1025600a0d8f24a641044a01000d206c656499c8204400502b036300ecf21482000049103b152ffdd21084020012a0d88e8c0815a2200212910ec2ff7b24a501030094a8360ce2ffe4010a04282501b008a91810c540c415840d7fbea181502a06210d00ebfa55a84a804400482a075f676e80021aa04a03041af9995de2a0d402461a01d7b6f5689502100310140ebd38d9700d154314160875e35c8506408800822403aee1c41400c510c504840d75cda9e9506081290140eba8ddde028410320840075d331ea21008a00a42101ae8b88e2090040c061020d6eebfd99004a810a0d406b6ec201c8210401500b035b7151165482a002cb503adb7e3440b4540c425821d6cb9e1240840870800906b3c2fa80ad4003209088759c5d3e20288218a08141ac7268002b4500c424a21d620fc3f84a00800b20506b1079c9c2901000194207584801224080a0020a501abd664e02b50400825221d5b237dc9480a80090d506ad8a9de0283480988200756b31d9a6612804023543ab253dc02245500505a01d56508f88186281280850eab0b1f8ca404400582a8354c2e1ac160aa00ac3043aa3a1d222108002040220), (96, 85, 2, 27, 2, 27, 0xec2d899f1420b00132d00760f7495ca400400580a83b06a159e4608a00a82543d80747280a45200624801ec010a050504b01130c00f5cbcba944305000056303ae1d48881610a04242043d6a94eed2b4150c125aa1eb37fda794062072309407588bcc20cc35039046887ac1271b65602a182c3543d5d076d7008440c4410c0eadfb3f11580206030910f56a1b4682825038186007aa51ff6410188048c2001d51c22350b0540c4218a1ea6f035195a2006232150f52cc71dc8424038102a83a963e51c1208a00ac2041d49dca352a01500121a81ea4ce0c485a0a86092c50f5210ab0c0d15401516287a8261e8c540a8188c3403d4047c74084400c424000e9e203591584a07030d10f4e0ae200c815801846807a6a6bd78241a81c823003d2cdab830b4440c4650a1e94d4db584020802b004074743e0f42d05030096287a32b526412888188ca041d176480b290d40e461aa0e8af71409522086292140f446cf3520421408404483a22d1b2a1408a18a42103d0e1b0dd0b401001240a1e829ce9b9060a800a2d6073d0565f4a901800894a079da3e30e1602a002c3143ce83d5e509044004210a0e740580a91a0886082550f393fc87c2c244085822879b97a1e22182c0042b181cdc661890201600201881e6dfc0808046a81280c607364fba1c250543059628399eb5a8650100040c0501cc889b4d2a05400421a81e610ed518504001030040f2e1e1774283540948620795ca822a508a400c49501cac325b0014550c505820e55304c10584207030810f29cc106ca101400594a0394ce1ad4161aa04ac3043c9fa814b0a44400465081e4cd33b70502a00230c00f265242d4020440040230391dd7af654822182c9503c8e85be2224550c545a01e46b614a8180200000850f21e5867c8211431504b0390c998c0560a800843443c8563eb1024150c105881e4209c4584022862b0840720d48b340d014004142878fb3beba5402c00443503c7a05a12280d402461a00e3615a1c1520a06012d00f1a559d1082044004029038c4c1a712208818822241c621be130a41400065881e2f5e4f24486281290890715e6439c2c004005802878a9330fe10128040c3101c48c74dc0305500501821e20d009c8522286292840f0dcd54c4a840802880a07860f942a1012c04443101c2f0a4db294510c564aa0e177c86891a2286282950f0b9e33a42d1040149028785701b2e52122042c1541c2903ca1314100c014aa0e13df3429844101108160709dd471ca414401582a83831fe0c85482a1824b403c16f4c910845200624880e0a9fbae8102a80280c40f0531cca08c01030004887827be7084182c0040b481c12cc2db2a0500c460a81e0676b1384220802b2040701318668ad11401594887801880625288200a48541bf4b4150030510c500821), (96, 85, 2, 27, 2, 27, 0xfb08985d81062812a0840fd6eacda02c11001084087eb2d7f0e1602a182c3143f53f77f03045200614a00fa0e2abb8102b00320c40fcc805ab8a031009184803e56760aa5602818043543f2a86d692b104008212a1f94719368520000012040fc970a3d02905030096007e3b6d6660602a18283143f1c040880b10400821021f8b8d82e0522b00312c00fc3fd5814a830809880a07e14b47c2560a818843543f05a85f12a45400425a81f7f2205c9584a81090d50fbef6cef8a431409584883df6f672a548280004b503efa6cc690208602201081f79eb4549502800210540fbbfce284a810401480a07dbdc8bde161a8048c3143ede2b3bc00c050c105040f69ca40085a0806012450fb1b7a8022420008080483d89666681682018049043ec45651f2081200240ac0f5e5bb179522206232940faf0b1fa42801400484207d6f241f8421aa04a03441eb68d84f2b0140c061aa1f5a56fc81582886290510fad1ac6248204800802b03d660da29228881882a241eae813132b09002060aa1f56f6b2840422862808a07a94370e48024408402a03d41ac0a10688000808243e9b79eac024010c104001f4c8478e4580206010890fa62c4b2c8905430516a07d2edd9924612804003543e960b1622b0d102560a21f47724e59484a870b0d507a0a10f640c11001004287d04add2a528281804b541e7e4aa8e0309102140821f3e9957245a2206212890f9cd44b10a515031096883cc9d98da010aa00a03181e62eea5f20881021402c0f2c35e581122a06202d00f95f609ec8421438504a83ca0d77ca1482400449103e4f8746f284410c564280f2432ad195202860b2940f9171b1040805400406207c8a440ba618a80082b581e445bf942a4540c425a01f202eb129502880290540f8f9a1594a010801880a03c76687f2618a81882b581e398a4160a09402061801f1c45ec00500286090800f8dd99bc88c24408502887c69e89384408a18a02403e3323f5c0a0c202620001f187c6d7904420102096078ad86c388835409506807c4c354a45410c044c2403e219e0a70a09002060881f0e59a221584201010910f8636d77c8825438506a07c2f1b500411aa04a03481e0aed4f80244500505001f0546f00006280620242078261f750a505400496883c10db0de5008200ac0501dfb3bedd020d102500881ef9a6e72106020600292077c8bee302114801892003bd149190068aa00a0b043ddb43167008c4024410c0eeba0ff69500800010540f70286ed42905430496207b7c599a65408a18ac2503dbe0f9c109005001210a0edde4db60582a00210c10f6e111c442900800890207b697cd161012a042c3101db0560ae2b08502161221ecc528cc10a0a80082d10764b24294c514031052a83b23f36e1241081c022203d8f70166030d50e541821), (96, 86, 2, 27, 2, 27, 0x863ebbe740c1103100428618b2f0592805400421a8085f006dc00c11401404086170e08fb2081500141ac085bef629ca430409580a8216ea7a37208950e141ac0857a65bdc283440958220615d90af7214450c5452a0856b6c2a0251503109608215656efb20801001402c08507882aca500400590a8213e89a690a0840202108184f578c242825808886206138d5421314540c415aa084d301154282140848420612fa0cc20b0450056102184a880ba820304095800021228eb2102405001050818483d8f80280580088600611e6c15f280d102560a8084609dd5420148018822021077f5f12b0110c120aa184140503c20244085822021037c34d20c05001052c083fe5eae48431009004a820fa9f104010950210182083e0c1d7003150310161020f5b78d40a0960222180183a4b195424114014842820d9e707489084020211208351216b42c250380862860c7fbf050a0860222108182d8755b4cc05030046a860abdef2a2b4000c06422182a94b8042c214084842860a55de8e2b045005612218275590542c2540848628609a28014800450c501100825b9b16c2831009184206094d4c64014540c40582081f84d6402910031090006077af3e92b4000c0242a181b69260c2815801986206064a33fc2b41100124a218185c29a8042540850608205aa0f6c8344100504121816a762fc08154015062060538ebb1315000c8142a0814841f2421044004922020413796b00884020410c081036be4ca024408582a0203ad8ed4020160020180180e74cc18280580098600603871ba12b5040c8252a180a477ab42d410320942860266d99c320440c411201807fd12e4030440041230201fdebc13089202210ac08039122bc0d0540051628600d6aa4d10c540c4158c0803508a0c290140059420600625aad30c440c4152c080121d898ac25008186886001b9d6b20845005412c07fff5ff0c8d15031116a85fff839fd335000c8142a17ff6e67a20421438404481ffb6f784204050c1052007fc927694ad01030094a85feb384db014450c5450a07f8f82e30ac01400484885fdf7fd952305500501aa17f7d1e92c8c20438500a85fdc2885d08445005250807f593bcd42025408486201fd13058e020d1025408017ed09d2d08225408406901f9b37cec0b0000c0200217e57ed238a511401594881f94eca850b4000c0240a17e4c4a6240d15431416285f91ead692a0950e121a817e4717a4cad01030194a85f8541d140a4000c0240017e06c4c488825808906805f80ac2b90a014000218817dfb64f1c0510431510281f7a81acf080d5025618807de154b748211401404b01f77578712a05500521a817dca56630ac05000086885f70809870a415001658817db1d7b244835039046205f6a53c8489081021201207d95b161ca021008184a01f61cf5f53305400411aa1), (96, 86, 2, 27, 2, 27, 0x914916348a111401594802451eedf00b0100c020821913b7a34c283040958020644882f052a45600625a81910db53c48825438406a06439e90cf2b041005602a1906eaacb4a915431496a0641a38d312a01400021a819061c65a045050000560824179e1930808402061080902d1bac08815431406806409baacb0b0d1025608a19025cb4642d01030094286409022cb2b0540c461aa19001217802c050000860863f44ec272a09102160a818fbba8678a8314095848063e8154f72a0c4024612818f915988c21114015942023dc31afd03054004018a18f659dd3c8834409502a063d57c6700b084020210218f36f131c28014005842063cbf9999330940e011aa18f2e59c7405144314122823c90573501085021010a08f1a91a0c2c014005842863c69ba2d08011001208808ee380840a8258088868063a66d7ed0a405001250818e9557d20ad104314908863a1d8c03208c4024412c08e80e1842410003005040238f2e6b4808c50e5011408e2c09f48283500918600638876bc8914400c4141208e15d8d300801430404006381511f309001001600a08dcf836e02d0503009608637250b3d2a045005212818dc74fe1c2401400584282362075e80a5000c8240018d6f0303c2821008184206356a97ac2a0440c4212018d472279244310390444823515b0362905500561a208d45401388c344095028863246deb0910c00e4101208c74adcb4290440049220631c0b337208c5025412c08c5f533b02c3503908608631592e9c800850e1011008bb380284ac21008084a862d8387502a441005242018b526ac1449050000562062d45a14b2b45500565aa18b10e07cc8d14431512a862b1f3283008c5025410c08aa76a538283540958600629f36a310b054004218a18a78b696c200140058420229e0d2632b0d402461aa18a63bba90cc0103004488629892fa62b0840e0612218a3f0c8f4cc11031044a86281256a70a0810216008189f9c0bc4ac15401486a8627e37e0f090c5025610a089f0c669c240440058228226bbe120234550c505a21898dc7faca410401580a8224dcb115080550052188089201a022290003009040623cfc2c510816002118c088ebb37b8ad010301948862335bb630a4150c16588188b3146d4a015801886a02229aa0d90a0520062088188a15d6f40c0540040628622479d332b0d00e460aa1886d2638c2c2403818228620c20800210840200122087fab6e142c210080842861f6b20950b104008210a187d9ebd040c010300042861f4caa6c234150c105a2187cd612b8a0200081808021edec8fa2b4540c465a21878e3e8c44c110310442861dccfb7c0a5040c8250018762cc5c029004304900061d8263840b04500521021873e2d47c01114315142021c05908b284410056428086b17c7b4ac41032084a8619c1600d2b085021212a1), (96, 86, 2, 27, 2, 27, 0xa24b0f6bc0d1140151428688fdb3c900845005010c0a2089bc84a421008084a82880ce61c004450c505000a1b5ebbe0820580080690285fccc86290040c061220a175ce048a41103118488285c756300144400405020a142223b4ac25438486a8683508d672a0c102560281a0c7128c0ac1103108488680cb4a180b005001210219fada9c04a905800896a067d83dfbf09041005600a09f4e1ed5408258088062067cfe7a7d2a05200620a819f0c33b748221408404b027befd25b0a091021608819eb925ac4a911031094a067ab26c8c0b5000c8240219ea1fc5148224808802b0278b927082b4040c0252219e2cc93082c1440158208676ecb2f0804450c5051009d5435c1203114314145027547f1c80a4150c1258019d3398f9ca001400584a02749ad1fa290140c061a209c88dca840c0500000628671c95ebd2b0d40e421aa19c206d3f4a800800880a06707bf1f72b4000c0642a19b8da2354ad40032090a866dbb0f57280d402461a809adf24f4c8304400512b0268a0aa562804500561200999d6cba0ac010000848866578f5b10b094020218a1995d170702c010000840866567d48b29081021602a0991afd304ad14431492a866432b616280d502561a0098d66145c022140850430263372955224150c105a819880073642c14431482286616c0617080c402461080984f8455c0c350391062865d398a090a4560062588197419cf8243000000505025bc09d2729441005642a096df280548425408406a825b15efa0890850212112096b7d2610a8058008868065a6ae3892a4150c125a8196300a1e205014304144825830924b20885021412c095d2b44348d11401414a86570ae75d010d5025018a0959b566d028148018820065620271720805001412c095598e6e42825408486206552824692b005001212a1952fdb2aca415401586a8254bcf5cb0a0450056108195118d9540d054304162865422bf58800c50e5011009500c6638881543150680653ef25bd2b09402021aa194e34e9dca031809984a02538c47d80b4440c42502194cdb4d94210400009220251f6a34d0a015001218819476ee86ca811031184a0651186196280440c461200944183e70a91143149480650f407248b0410c52012194184919c8420438500a82501b68d82a0450c52120193ea16fb4a541032094a824ec1fdcb200c5025412809384dd3c449058008562064e10c7680b4000c024021933350e6c08114015042064b0ba10a2b09502161a2192a0cc5e0a90143049480649d4db772a40500165281923447d402904030092006489b77eb2a00500161281922576b4c2020408580202473a37252245500505a8191c4e4b702c2500808608646a842842089602201a40919e770008425408406882466782992b4550c525aa19192927fc8225408506b0245aa8053280d40e461a80), (96, 86, 2, 27, 2, 27, 0xc96545128ad14431592887253cbf932a44500565281c9438630ca834409582a07221a37af030550c5418a1c7a26a34c2c314095842871cae91c12345500505aa1c68f3a8502c2103808408718775aac0b4040c025021c60d9562009014304140071566ba400b0940e021821c472c86cc2c350391862871002aaf880c0400005140c364ebaf428250080862070bd540b02b0840e021221c14f84f942c0500008628703f2165d0b005001210a1c0f3398940c144314022870273f64103055005018a1c023ce1a4ac01030084a86fa1bc8a42b0940e021a21be6d6081c2021408584202f7287e500b0540c421821bdb1a16524301000054502f50ccfe72844500565280bd315f8bc8831409504a06f39e5bff29045005612a0bcc59b50ca831809984a06ef9239350244500505081bb978fe008905430416806ee35db24890850e121120bb72430502c11031084086ed297aec804050c105100bac0da42ca030409580a02e32f16c52b0840e0212a1b7f3554bca811401584a06dfb37fc503045005010a1b75ac9aecad15431596a86dad848c52b0510c520aa1b6aa2ea908311431414902da5f622d0b445005250a1b5c456fe4ac25038086a86d6a365088b4040c025121b582d2d8cac24438582a86d4437e1103415001058a1b334ac0bc2030409580202c3028a2f030950e1418a1b09f52464ac21438484a86c18f5363208440c4412c0afffee9b82c34409582086bff161810b0840e0210a1afdde7d724501000054482bd7da32f2b0d102560aa1af4666fec8835409506a06bae41b6c8b4000c024121aea835e722430439480482ba3c541d0b044004210a1ae376edc08111431414802b809a76309045005610a0adb1d0f5c2011401584202b6c470672b09402061aa1ad8d4a1c24101000054402b356db890b0440c4210a1acc9f0f6c8c31409504a86b1f0f8a90a44500525081abf9955fca821408584a06af94ef390b5000c8240a1ab6265a042905400496206aca3988a030d102540821aad3744ac8c25438506a86a5b81ef5290c4024212a0a947f647ca020408580a02a4e30fbf0a44500565081a921849c48915431416a06a4532c692a05600621a81a8a0ee908a411401584882a0d628cf2809502161a80a82776f38ad10431590886a077b7043108402011220a81c8e28083014304149029f95c2650b055005218a1a7b7a839204314394044829bf8051a2b05500561a21a6a4b5a40ac25008086886982bc3050a45500525881a5f3720c42c01000084286974e56472a4150c165a81a58f64c34ac01000084a86913589562b45500565a21a40c4a1442c410320842868fb7d92c914000c014120a3c973fa42d154014962868d7e81c329445005652a0a353624242c050300862868c2a0d232b05100560aa1a2bfc3944a014801882a028a44cf100a4040c025001), (72, 87, 2, 27, 2, 27, 0xbfdbf0bee5018a04ac250171bcd22aca831409584a06c1d6efb39506a812b0d40d0fa8659880c050c1051409658ab38e5618a04ac25432c85aa0ac0c354395062864b9c30b184062812b08404713f2b472b0d40e461aa1893e5bcba068aa00a0b1430eec46f6ca035409586a021dc3afb895a2280292950c1f4c4fef0a0c50256108181a6197065608a00ac2543014e676222431439484481fa6dfbf295a2a80292d50bf482518b28045005612807dfe903ae568a8188cb542f3f81201c8c35439506a85e561738f1586a812b0d10bc904e8b80b0040c021021778efdb81228081802a240eefcf62c40d11401414285dda71e519584a07030d50ba87b8f3c2b5040c825221749dafb3e568a218ac9542e889b0b00ac05030086885d0f805820520286092800b9872f8632b0d502561aa1730c02bce5688a00aca542e5f0121b0ac01030084885cbaf141a0580a06010c10b96474333280850216128071e044a924682a1820b542e3871c0e40915401416205c648d3be482020600a88038a2930992a0450c521281712b92ff1218081802a280e062abb520301030014501bd9c76b915862812b0910b7acf4d372b05500561aa16f1ed1a6a061aa1ca03142de20d2f242c05400486285bb67e4741588206410910b72e0cf31330540c411aa16e518fd165618a1cac2542dc0c561a22420438480481b5c04b0a9986a07208d50b6870b5bd0b0040c0210a16cd9f54020212a04203140d974283cc2d11401594285b29dafe69522286292940b5c4f680a2a0d502561a016b1e7852a468aa18a0b542d639116802d41032094085ab3f5d521582a06210d10b517f56890b045005210a1694a949e90180a0020a280d1e98aebcac24038182a85a3c91b6a0588206410810b4731109a280c50256120068d73a0cc1018a04ac2000d02e6854ca431409584a819fbf2cf6108428108091033ac10f37280450c561280674b56568448aa18a0b402ce687bffc2c114015842859b6fe4c19406201230940334a10acb2a09502161a81668d2af561410a042c2102cb652e514090540041620596a4a58a448400701009032ce267dc2b4510c524a21)],
  [(96, 74, 2, 27, 2, 27, 0xb923621400100400912e484e0540020088604b89aa20100080220102e17ea0840020088408b5a0681400080201812d5ea20400000000404b515401080040044012d1b320400010010404af16d02004080280022a5a340480010010006a84620820008020000ea110c04c0000008006a82cb011000400600129f35004000100100049e263890040000810166ea2a04010200a040498520890041004810165dd088140020088240973e4804800802058025921a04012010204049627d22500080220922582680940020088208960688040004004180257b2804410000280049598b21080844044112468be0400201000404908d0811000000210123e8ae04400200884048e58381008010001012382a205420040086048ddc08130004006101a3156a24000100104058a2d882008090201022173c404c10000280068022c01500080220811fc4c085000300902447eccd82408090201821ef55e00c0020088402728c680404080281801bc1ce04400401084046c9da8920400008101d8c754054001001820461284811041004a101179af885400100182445dd1e804000802018016694608002210804085701a212800400441195bb2004c00100180065429a203000c02601094148084a00200810464ed7e814080902018113511209000200806084cc6c810208c4251011315200540030098204497008900480408101517ce88420020081044429330840008020080508f56040100842040441c76811040000a101102b8405200300912043d4d581024904491010dc36c88280300950483655381300080221018d9226048904012440635dc280280080205008d5dfc89200200812482c05e813000000210188e0ba0400221080404214ef8100c01008101083dde04800100104062074b81000100401010815e008400200880081dbe08100410048101070574854003009824418419224000802009205dfc8090002008020816c6b810040000810105945881000200802401324c21200884200118459f204012210a04040d3de811080500610103358005000100102040c324090000400400142779c85000100102440908d8100490448101022c68842001001104407ace804080100018001d1de080002008040806a590148008020481002ad2040002008040400a8f01400080200810026ee05000000006040064c8920410048101c003440480020080006000c8013000802200180015c8100028480240), (96, 75, 2, 27, 2, 27, 0xdd3dec0880442110809ba392810201004110134ecdb026002008420369c3960488010014406d23420091002002800da3d4b2130004006011b46cea024400000200368d6400408000004004d1661808100200280099c9d28000088420100333327020400000220265e7720481000020406c82a8c10440681228118f8f08120010040101b1930f004001424020162a21084a0211011046c53299094006012208d8284c8150000002181301001020401804a2025f37ca0408010014404bd546400820401508017a21f88080040045006e9d2e02808000101025d28520501000020604b97b6c0a84048110c097076a22000080200122db54642000200800225b0d008440040108044b528890a800401104896a2ab01480040044812d090d02048000122025907660488221084406afe891090008020008d5fd1202480080204822bf5e440440100420215784160480221080406aea619098008021008d5b6f98128008020501ab6d69020012088020255953480c0020088042aaed94004006012280154483024000c0240822a4a2442a0000004122547e3605010200a0604a856c90a0000000048950153015000000208129f472000081005000053312c8120020081240a584e0490002002000f4675d201000c0260102761c502449108522034e721200012210a04009cbf74098042203080d277ad8110004006101232c40041001004080446020c082003009100888730c090208024080cfe77e802800c0245009fa1c304018020102043ee20c04810000200067db9f0091004010800cfb52c01080080204011f11b842000180480223decea04402010084047b5ff90880060130088f478101280080204019e465102209008142023bdec6008802008440277ba610a40020022488ee8c080200080201009d694e42400180480233aafca050004010060474c9510a00040100488e97bc21200080200119d179e42000100400223a0e5884c003009804673e019098004011008ce6f4e21100080220111c462b0290010040b023803ce08280300954086f36ac0840060122808d5039024800c0244821a062302a000800c30233b0d204800200804066633cc0a04008000c08cace5814000400418118e17402a080001410231b41c09010200a0208627e1c0100442100804c4b0d810240802910118794a028001804810230980004890000240066116b9098044211008cc0bcb010240000900118041500a00100443002e86060480000000406), (96, 76, 2, 27, 2, 27, 0xcab6d609010200a0608ca7b488480201000046c9c5c02140030098201c77d4e0488020084406c57ccc04a0010011006c3890e04c0201008406c19e8a0480030090406c1388624c2014018407c03e3c8408000004044c02b608408010014044bfa93a04812210a0406bf37e88840030098048be85702520018411205bd378884a0231091046bd07bc8488010014046bcdf588488000004046ba3ce208010200a0408b905e424c0000008007b8cf2620a92210a5403b7842480a0020081042b7298a0408201004404b6f4d08008030094040b5742c2440018418005b50e7c2500040100205b1aa2a00810200a0402b0e2a60400008400404b0aab601410200a8600afa8e48540038498244af66e48420201001044ac536a0480201000406aac2582401000020005aa95f62400000000405a9e8808420000001044a9bcea0920020081608a8bb860842024088408a669c60409201024404a4f37c2401040120005a38c920040020088400a0867e05420140186049c09d604802110104069b60ca05410200a86049b533605410000286049b365484a022108104699c1e6044124112840499ba80840804010404499a6e48088030094042992fa20400231090404982b7e05010401206049600a484880401040469560f880a003009104294e65a048800000440694173e04810200a040693dc94882002008104893a07a040802008440493285a040021101040492c0e20442004008404917114802003009104090d51e0402014010404905ea880200200810408fa02604402411084048f8b0205020140106048d826600080300944008cfb1604890000244068ca5be00000184104008a95c488400200880488a1c94848822108404688c182040904012440486dd14084003009800885838a00a10200a140285244a040001841040485203a240004010040582a0bc84a00401010468167a884000000000448165b48400010010044810c4084400100180448109b48440000008044810670808002008004280c89480800300900427e537884800100100467e044484800000000467df98604082210844047dac3084c00000080467d04a080000300900407bc93484002010000447b6a6c84080300940447b48e604402110184047ad33c88000300900487a23f604880300944067945fc8488020084046791230840802008404478724e044300402840475db2604410200a840474cec604c100002840674971e048804010440670af5884202210810446fc9e48428020085044), (96, 78, 2, 27, 2, 27, 0x9569b78120c01008101a55613a24c10000284078b7989814080d02418122a2a0200200200814008a33860900010040001623e87205090200a460486d687810040a128101218d83c24a10200a1007850f10202000e124010a0817d0802802008504080f60e014a0080214811f486d425000200802057bfcc0810a0080215011ee2d8624890200a44077b55ff81080080205011e65dc2048200400040678fa0d804000c0241801d9cc040528010015204762b66010a0000014011c5969a24090200a4405709c2e881000c0261005bf02ac80800284800426f87ca813048040a1019bc1ca884880300940466e40b8800000c0241001b07be805080100142046aa74d81204804081019a5589a04892010244066796f7812200e12510199c3c04810003009024066902081204904481019973356004022108840061c6d5210a0000014111831d588428201005044605b5e012800c02440197f96ee04a00300914065fc490814240210918117edcae00002310904005f775f212a00c02541197d737020a80200850035d711981208090201019748cb004280100150045c6f51811041214a10116dcf5e00c10200a84025b0e00202a00802141096b0e8e048000840040659aa92224000c0240921644e9824c002848800754c689811048842a10114fba9208030240a040850d9c381020844051011426f86010a00400460050490b210208440501114031e884082010040444f9341802000c02410093a497024000300900054e137c8130090442101936c2e6242a00c4054054d29188030088422100933c60e04820140104064cd135012a00400540192e9c3081200300912404a2c1a89480021005815278094290004850020949d5ac894280b1211815181e76248001001040745fdf6813040802a10191608f4890001841024845448f21220804010119131140248104012000743e99f892200c025101d0be45024c003009800741efa58920010040101d04a40604210200a140440dfe7804200802118010227b081400300982403f4e2580204884281008f298a084882110140463c0e28814000c0241810ef336608012210a04083b9d7a820a0100415020ed1fd604000300904043affab81200904401018eae1c084a82110150463ab7f981020904411010e8a132048821101440639ab9581220804011018e44a2a04c022108840638e89b210800c0244110db948e242004850140536b3e322020080210120d79fe6248801841440735053221000844040110d2e8fa2480000000407346ed6802808c4245008cf20dc8480211010046), (96, 79, 2, 27, 2, 27, 0xaab761c0802090a4080954fb4589020080211016a818250050110840a015451b1424c0020088007a70785852800200304134c4e53800808c4245002957afd028480001230252a793204c0030098406a4f1b840810010808809478ea180004904481002880847004011884820150c918a0488048504406a12d0b40a80060130c0940bf6c220800400441227cdd1204840100421044e999b604400300984049bafdf40042040142801359c1a214200e1250912684ca61244010042003c983faa294201401860992123f4484200004280b2169fd8200412148102242bab51251002000a03c81a0fc84a80401050468f848e910404621220911d15d98a020844051026338e6b104401c24a201c65314604c20240884068bfcd74481046212880b17aca1800000e1241002294b3d024411884a20344ddbda24c12210a840786dbc44098201085080d0d579d8030006106100a1203ea4260100804023420183420210200a10018081b5c1206048140c10fe130b812a00c0255019fbbcb8424000c2080233ec0176244200c4084057d49c0c0112040148804f9dca2220a0080214121f2559a40840100421203d5f87e09200384916087aa9368480201084000aefc9fd81024884291011ddf590426010880c0233aed0f028010284a000975719141010462128810e6bb23804800c0245801cafb1b0284010042302382568805080200842046f11009091003082808cdd626f802800e1245009b6db2b1004110842200b62ba5e04c02310984066a5c18c0a10070928c08d3fc77881040802a100597a8a10250020080a0332e88aa24c000000840763d512c0a84068130c08c67acf812008c42410198c598d028400c20a302316ba12248201c410407629f6c4095600804a80cc5019a01084000084011867716025400000280330af5b605030040206046141ca1085042202a088c17660214800802049117f17e902a18020143022efe51600412210a84005d302b8495006012a00eb94e5b81224080291019708fb7126000800c203adf9e7604880084044065ae29ec4a06008040c0ab3a2c1801008440610015e94b0405401804a8212bc3e4c24010200a000557877e8490004010000eaf04e80900008020001558c3b90290018048b022af91d20500018410604555314c0a00050900c08a8581f814000210018114bf5771280008008302a9555cc28210284a1009527d2a4085046212a808a375ec212a00400541194577341240810050003a899e7e20082310944015010334480204014080a9fffc6094000c024081539217a421400800a82226d133c2820038491009), (96, 80, 2, 27, 2, 27, 0x8400eee052104012160483d06ce24ab04412540783c75fc2440008408005824dce60128020085600816e1c825080000042058124e5608402210884088062b24248004010000780208d229290284a56097fe021c85080100142447fa13ac89000284802487f95ff024410000280057eb512029400384982097e93d4229280200856097e831ae20c10200a84037dc132821000300902017d2bc1e00880384944027cfcfd028200200810097bd4e6604a02411014067947782084124112840877b5fd82088020084003779ab8a24a20140114077723af488402310980487630326290b02c4a4609760bd6e082802008540875920222441000028405746e4862000030090401744a47c248002848000773d9768248803009400773a7e8a20aa00c40540372dcc0601290200a56007244b5c80280300950407168f5825400300982057139e7c0508030094204711636084280284850446f2d18a04880184144066ec8aaa08000384904086e25a9a20c20140184036e1b98e01210284a16006e101dc84880084040466dd582625200000016056c2b98e00280284854006c127b209080200846086b02232050a0140146046ae9b0620230040214016a1f5f4852003849124469e1b18852001841124469ccf7e210200c40060169b89cc24a900002500769a854624820340904076927466248002008040768eba0805210200a12046885b2a0028030095400683e10224aa04410540766d83c600c023109840266c28f62409000024405663796024090000240056523c86242304412140564e1536240002008040564dca548940010018248640f966208304412040363e6dd4248900002400763e2d5601210200a160063d879c80a00284810426374dc6040904852440462d7d9a004001841840062229e0052900002520461ecce20400048500404609f2da24200200814055fe43a224890000244075ee32d408280300950085de3ad424090401240055dbb00484c00184180465d9a4e024880184140075d7d76020880300940035d61cd605080000046045d3a4c805080000042045d3193224290000254055d2719600092411244005c2e25204402310984045c03df084402010080445b6d91e25200300916055b64e0620a82210854035ad10ea05080084046045aac8e42540000008205597a03a08210200a14085950f748440211018044590e7ac24890200a400758c00ba2409040124405586ceda282803009540957f27ca24210200a14055762c94050900002420456c288e24a8020085407567adb4052803009520455f9dfe00a90284a540255a83f02440020088005559b2002480030090007), (96, 80, 2, 27, 2, 27, 0xc91bb2e2020221081401c9024ba0489241124406c8c18aa24a0000001407c8c0a3c24a8020085007c781ae62481241120407c6e24602408008404005c63c22224410284a8405c4d1b422429040125405c48b8702820030091009c478d262400221080405c45b83a04c2014018406c440a608420028481044c43ec8a2480221080407c42d7c204290200a5404c3481f60040030098400c2f83b224292210a5405c2c04ea00a8020085402c24c54c8508020084244c10be5024c10200a8007bf9655424410200a8005be29e542040020088001be061e60041241128400bddb7ea0140030098600bd821cc25210200a1205bb3b9e22082034090403baf5742212b0240a5601bac0bec2440010018005ba670588920030091248b9e272e20a8030095403b9b87b48408028484044b8dd5720021040121400b829c1a00c0030098402b66924e2489040124407b51a62e20c0030098403b430dd224a0030091407b303f302489040124007afbdd9820c0020088003af68cac8508018414244af3267e248b0240a4407adf90b22000048500401adab9508408008404044ab1918e2123044121601ab13b8620c2034098403aa80ac424c0008408007a93582c2800038490009a92d4542400018410005a8f6ea08500038490244a85f8a22042034098401a827c320408028484404a748d6c8040028488040a6ae54c24c0010018007a66d32a0808221084408a57c2220428030095404a4c65d20102014010600a4aeab600c12210a8402a41a6d80828020085008a3d420a00c2004008402a317dc60028221085400a2b82b22080048500403a29b36e04280000054049ecab0600280200854009e8b73e280201c4104099e2f3be20292210a54019d89eb884880384940469c47002248802848440797bd96624810200a0407973e3a0254001841820596e017485200300912449631b86240800000440595ba3ea240804010440595a55fe0840211018408940a8f2240801001440593d36ba240824110440592f145e248804010440792d3f9e214003009860192a35a62008038494401928d1088840221088048926b93200a10284a140290d5192248800000440790748ca292302c4a16098f3c97a282a0340954098e44dd604290084254048dd0e4620020040004018d9284e28020240804098cc9ff424400300980058c3b7de25020441006058be1e70240802008400589fa2f88000038490040899ca0028410284a800988238de048802848440687b2166292202408160987891f6254200c40860586deb0a2500040100605869a4e22540010018605848c6ec2408010014005847c4922428008405405), (96, 81, 2, 27, 2, 27, 0x86297f21494014242904c2cfda8800200e125100211f52890a5006012a48906983b0890803849424882d1a8842a001424412241643712110002102011209ff8bc090201084080d04b79ea24ab0240a540781f7b3b1200824290202c09969689008110401016043ec48491001080800f01f544a208001001040380c6b8a12a0010044102c009bd80a0a00c0254025fe4d0240a5406812ac08ff1458884400184180447f0d5bd02400142402033f0496e8800c010081005f6a28890040070922080faf6f8a052a0040056047d4a8cd129000c208b02bea1c2389100804021015f4323bc0142442142804f9aa01c29000300902097caac421054820092801be41e9c80420061051801f177eac4a02040140c0af8335c224880084044077c0c1a0102001804c000bde89b889400121401815ed5bc1c481401880880af61aade24a80000054077ac1a9c1280008008102bd42d75210000a1200111e64d99c494200004280ef2b70b8850000840024479485c41050010040801bc81dce210000e1240111dd47e240080070930800ec31d58242104012100575675411045006202201baaba99092800c024401dd52bbfc0a5200004ac08e802006248804850440773c7cb7020481425220239c444d8148c090285811cd28b2c4000070920802e6836ae214001841860172518570200014240202385a1450928008020401dc2bc6c40a80070930c08e15868a24a8038495407704746f1061002004201b81e16f814a0061055811bdf5514491004010880ede88ace24012411204056e795e91290010040b02b733d41815041214a1811b8033a44800090a0080adbfa00a24882411044076d3e4d2421002008082236973c1083000c026000db343c540a40000002c08d97c526200a0040044016ca63751481012040304b63a0b289008010001015af18ad4098600805080cd75b7e224400100184056b9c3f644100180488243587c2e81024021091011ac3c0810a40000002488d5cf83e05080284846046a90d890014120882a003544461204800a1204901a9a406c1080060130810d3bc46204810284a04066902e0d002011884c200345ccb48928004004501da2a7204488046213080ad0c14602500028480205684d6aa04900200809043405a9c884880d02458059f529f4094204014280ccf911d6242b04412540567b030d1040010040201b3d336f891000000210159e36b0c094400800280cced579e282a004005409674f78702610020042033398803892000c024101d9b64bdc5040442102812cd104ee0802004000408663f5bd006000800c20132a4726214a0000014911930cb74495401880a80ec95246a05090284a4604), (96, 81, 2, 27, 2, 27, 0x9fa22491401816250204cfce51a214a00802149127dec6c40a42040142c093ee8d3424a00284810079ee1a9914a000800c304cf68bd8814a010041581277d1e50481204014800b3b9ed3889080284842489dbdedf1244100802203ce900850902010041001671ef7c0498003083000f388296604400485084049c353cc1210804210802ce09f438942c010091816701e1f0481000000800b37dd3b824880401040079ad45f81480008008104cd6693f0922000001001e68d85385200070920413340ac6220a802008540399cbc2f1060010044201cccd2fd0848008020480663d1da40a02010840c0931b90108480028480046988a14402540100428034bfaafa8022090441100a5f2444c125006012ac112ef527200a02411014029772ccd04009208902044bb84b0890a00000150165cfb310494007092200f2e5f0e4852801001524497183690291002000b024b89ea1804880100058025c3e68c40000200208032df8668848802848404696fab611085006202300cb71bdd804a80500558025aaebf4480003082080b2d32ede240000840040596449a242540100428234b04bfa881008c4261006576d66c00800200308012a297f820810200a000395056bb1401802010204ca51b78890008c424101651f830c098244215080d28d940820290200a5001944241444101108408244a0914a802000e124100a502f7d00a5000000a409275a4c88808221084048939bac3108400800a300c98015a894880b12058164aff8f1100005090009123767f224a0201001407918410c120400c20a002c891779094040802808164422d34410006012080721bb0fc880022108004890904c84400118848024482bd1b220000e1240122408101c488400801080b203abd62480008400407901c4901410810050804c796723890808842050163c2934c0284028030c011e0cbd809000100102088f014c24480008008124475e7400248408028482238f286841120401480071b4f4f224c200c4084078d769a1049501a04ab0446b40318948408028581634fb25c405006012a8031a1003e20420240884018ce7768401001424082046687e121000061040112333f4210800010800089195257c85000184102448c74a331261802014203c622b38820800802050222ff8e7c490005090080f17f5fbc85400084082448b0c8b31085022082300c543df0895000000218162904278414204014200713d33d080c001001804289b20b3105100a008a01c4bbc02891008440610162300df4411208024880711558188800040100048887be031411802010a04c429bf08910c1104a10161ca138410004621208110e29ae224c10284a8407), (96, 81, 2, 27, 2, 27, 0xc601961006010880c20162f3c3a094a010041481715063804a4002002240b894bf1e2480201000407c4a278700441108422016241b378942000001181711d2319094000000208d88d56ce00c10284a8402c44d667025411884aa0361a709e8822088421100f0c23d504202040140403859020e04a3004021406c21cf550004120882200610a9ca2128080400411b05938c40212040148c018265c360041040128400bff4a7c12a0810054102dff776a01484000084812fcdfccc00104421088017a059860488241104406bc62fd91200100800202ddda54589000844041016eb38bd40880070930809742b28e24c0030098407b9e11d51061012044201dcd5c128a088090205026e12294c00400709228016f9e50e24a8241105407b7a2f5c449000c2089245bc0ae7821080d0261022dd4940c485600804a80b6e469182440000008005b68571f04218120542045ae206d080800c0244006d2eef740a02090a40c09691e5ca0420221081404b48338e1040018048001da234a8210a0100414112d09b03c418005091080767ec1820943004028608b3d7b361410014240804d93ca828a1080b1221026c987514100048220081162ebe702481000020007b16fa130490810050b0458754438122c01009101ac2083d400424421428015db04b620c10284a8403ae6f4c91204100802202d6f8537802a408029500ab5e7461124005090249159dadec8520008401244acdb2d61250008008803d6419ed2120002100011aafff050424204014240357cff9880c0028488042abe34550050014240a0155e9f5a820800e1245022ae1c270494200004200f56f8c162408211014405aa87599122100a00c202d52a93889004021081016a86bcd1014007092208553924922482014010407a92cfc9020401c24a20254795d0082800c024400ea3981e4425208024ac0351ac0dc8480038490046a8d4e7f126100e20c203d3fd8518922803101101e9f5c6c042800401104034f374162089241124403a753ff504a001004430453860d88130012142101a9bc8f044a14078928c0b4ddb92a2842024088409a679259042011884c20452eaa148902412149101696c1b51085006012a08949693b020410200a8001a4ade14425411084282352201cd8a4041004818268f2ed5c0240080202c014754aa22408008404405a36f8110014910852a00514d28f210800e12441128a5386c400003082080344cc3a82520020081205a2203371044010042201d0f93298930809022101e8604c78485204014a00b425905a2428211015405a0b381e1060810054001d04980d812a008021501a807d2140282080250c013fbc2d084c0008408046), (96, 81, 2, 27, 2, 27, 0xe95b9410204024282202747ee7682428090211823a12114c1000050900811cb642ee2822014011409e57dcba12a000800c102f2ad68c803000a122100b938ee944082482250803c9ba2482528000005205e48e162441401c24a8247227fc2800800a12050038fb7a605000060120013c6f5e888540018418244e356e63009100a008b00710710e8050801002180385f63e40240020022c01c2277a40940030098208e086a331285822092302f025b71084a00c02548077eb400c4a12040148c0bbf3c8182808030094009deda95244900200809246f5df34880800802050077a31d441284088210c11bcb718a0923004021608ddd60e01290804210902eede18b09080080204017769db6c098208025080dbb06c7a240200c400405dcbb09b1204900812202edf42fa8a1008842210276f4abc04a0200004040bb7665b48108028484240db1d157121100e208a02ed8807b894200610518176b32bc90910090a0808db5939e48440038498044dabaa471241822090203ed419f4824801214058236919fd11280060130491b33fc2c2481008420007d90a5851405006202204ec7ed3e211000a122011361ed5b44200060120c03b0977422040010018401d830665102001c24c200ebd9574814801004058135ec5989105044210a091ab872620040241108400d56f51c1010010040800eaac591220800a120412354efd7c5002050940813aa660662809040124409d50aea902609208942036a69b56210a00610541135335e1c095204014a80da96b0708508030094244d4af4281254810052803ea448a32028084404410b501a1c4490042202080fa6a224a2102034090601d31965502a082009430269137af8208004004502343737445050090a0a813a129f322040020088401d068f1b1051802010a01e80471f880008842010073e80a6c01820802508059ddf74e2902014010609ce92c48441411884a8246746c158142809021181339bea7c494048220280f9cd70188908020084248ce314b11210018048a02e715fd6094840a12848173718f9012820401504119b2fe3a2440221088405cd4265f1490008008b04e671403095040000a0817329fd9852400401024139856cb024a1040121007cbf24010014024282a0065c6e0d810a08842150132e0b62c418002003080796c500884a8000005046cb54cc70255002002a036599113892a805005501f2ae395c481608824880b94104808508000004244c947a8c425001c248823649fd44884a0040055807249fd80095200004a00d92147be2501000020605c852feb148401c24a304e412612810280500510131aec384091400800880d8cf1e6e2409008424405), (96, 82, 2, 27, 2, 27, 0x8b812f4810800e12450122dd048624400184184058b4d2ea090840802840162d01ed824200300910058b2e600824840a12858222c1336604400084084048acb1a2824880902058222a7eb2224a80300954078a9c904820200c025102229120ac25090000242058a2b10d8908c010085016285491a24a004850140789f1f342142012141091225fff36248a01401440788d6ace814a4121495812232a3a204a8000005406880e00889100021021016201249a04292210a540487537448922084405101e1cf5c5a20410284a8401873482f824a00802158221c90d7e010104012060086bb6ee8a0a088421502619aa6ca2428020085405863ed23085040802a080616c2ef084c0038498046846a6138930010042101e0f4db32050a00400460482e91ee8920809020101e0aad3062080221080403823c7c58a0008c424102607fa2ba242124112140581b4fe42200004004012206964ea2808038494409816371c800840a128500205346048840010018048813a1688920402108101e041b60e24a900002540780e63e5201000e1260102034d61624c022108840780bfd680a48408028482602e3f9e200803009440180525240908400008401600d2dc600c00384984028012e7a810a0804015011ff83d8c88400485080487fa11f181420040051811fbd6786290204c5006097e9e750891040210a1015fa364fa00a92210a54027e28bad88500080221805f86aa3624080284844057df51f4203000e1260109f6f92ae08210485214087db92778928c01008501df6ad27824200401010057c4275a82100040061021efc7f5884080184140447b4d9888a0808c4245025ec9b49209200401016087afcf9381200061041019ebbd4f224a12010214077aab9ee82108050061021eaa950a24a02210814077a80a67010a4000094011e987bf889000384902487a57d808a420080211825e95c48604210000214047a3fcb1812240a1291019e6ebe762828020085409799ee288922088421101de66531484c0028488046797f6cc880808c4245005e56f82a00092210a440079247d1814040a1281811e40bd5e090904012460878e7a77881000a1221005e0258b4840803849404477ea54b20200121400109de8589a01280100156007796c7f8922004005101dddba37c24c1000028007771e80c8810c0902a1005dc656fe29030240a060976efe7e8a0200a1211025dbae27e250002008060576a429f893040802a101dd9fb15024880100140077675b878a4880b1205825d89139e20a00300914037602a9489100121421015d8009fa050803009460475e79f1824000e1241821d78a84484a820100504675473640928006104401dd2db3182808018414009), (96, 82, 2, 27, 2, 27, 0xa4d4a82090800a120401692d73960128030095600a477c7f8a08408028502690fa5f20120028481600a31e73e0a1000610600268b714602429000025005a2d27f8825000c02618228a87b6a0820231091408a28d3fd8908480408501688b823408210200a1008a2299b08940803100181687bbc4620030240a0401a09bee2890000a1201016814c9920420028481404a032377801000a1221002804afaa2541000028605a00cdd3090800400440167e01e1625090084246059f39340810a00610550127cd40b621010284a06019efc523090200c025001678c6a46040a0040044049df7424892a490449501e77d505a21280184156019dd2693800001214010027654972212a0140156019d85a10810a4904495012758e15200c12411284029ce87f089080021005016727906a04c10284a84069c91feb212a00e125411a7240ff888200384910489b2a4d7882040a128100e6c558be20002310904019a80021024a008021482269c3b7204230040214049a4e7f48a1041004a1026692dc76240b00c42440599ea07f885080d026180666957ce000904012440099815f28800090440100664bf8d6240822108440598fbdd78830c0902a100e637b492042800840540498dd3b28000410048100260ae73e240003849040597dc0fb8922490449101e5f4ecc624c0008408407977d4958a1080310210265c9405229230240a16099685cbc821041004a102259d7cee24c1048528407962d1ff82508090221822573383c84a0008401046958768c220200c025012256158ee280300c4204099543706882a012141500e524c8662800018410409944b5e1800009044010025126152040801841440494458df824200a121182250ced9409080401042089410ced882240a129100e503043e082003009140893eadc28830088422100e4e32a12210002008060193383318120012140101a4ab456a240300c4204059236233814a00c025581248990c4292002848120991bb2cd09404021080816458ea322420231091405914f59a8122402109101a4419ee2008104012040291059c58820490448100e44018f20522024081604903c0488102c0100910123ee0e0425000384902058fb56478828410048500e3e9fed809080100142088f96244811000610610123d0db3820c00100180038eed314800808842050023bb285a20a200c4014038ed4ddc884001214018063967d3e248a0441044078e335c2092200a121001e38b3df200010485204008df8ed08920488428101e369137209230441216088d29275214000a1200912348779200800184104028d205c2224a008021492231c71b224030040204058c51309820200802110222f6f31a24a0040101407), (96, 82, 2, 27, 2, 27, 0xc13424e094a0080214817049d98a0440028488404c0f554381500061061813011e2ea2528010015605c022b9c81500021021812ff3347c2480018410007bfa33a102500100420822fe6d6c20421241121404bf82a9a814000e1241812fd265ea248a004004407bf1854c882200c025100efa7f37204a0201001406be9fc208920006104101ef6dd3f08408048504044bd5f5c788024904491006f52ccee0840028488408bcb3c9509400061040816ef5c0c88480048500046bb0b0c7882800a120500eec22d7a0140010018600bac7906814280d0251812eadf82e20a12210a1403baa5254883041004a100ee9aaaba212a01c415601ba3364c8a42c031091826e888d960529040125604b9c904889084100485016e586aca01010284a0600b92373b204a0080214902e419c522043004028401b8894cb825040802a1822e0c293e24830240a0407b7ea25681084804085012dc354560088030094402b6399128a400040041826d8af5520429000025404b5ee9200a400080200826d73f0702420018411005b5b9ee389400000001816d59da8228230240a1409b49c475800208c4251002d1f83062081040120403b4204c20a1041004a0026cfeb86a2020030091401b3e3fcc820a00e1255022ce9a4682120030091201b39d04622020061050122ce5e49c84a8048505046b33fd4108424080290806cb8f5cc2800020080009b27642988508031021806c89039e0088028484402b1e1449880a00a1215006c65de0e04aa024085406b18c7a28a0a08c4255026c524d942428020085005b0c3e3488004100481006c22d08e0422024081404b075279814880d0245812c15d3a22480048500407afebbeb824000c0241822bdd24be24c0241108407af6f5a4204a00c0254902bb676622443004028405ae960fd894a4000095816b98e25484a0028481046ae07b2c8202c010091022b7b9a962481201020407ad44780812000e124101ab4d6dfa2028221085401ad26492814800a1205812b41a6162101040120601acc58c5220208c4250122b2b192e2028038495401ac7d9008a508110421826aed75d200290200a5400ab72a3f204000e1240902aa506f60421040121404a96e9f38a408010001826a5414f60509040124604a9373f80a4200a1210826a29ea1624290284a5405a7f4390890249044910169f1796e0900018410608a7b5f2d824081104018229cc9e420080241100402a713ce0894240000918169a865be24c2004008407a68bd5d0a4800c02448269997af224c0018418407a64b5af88480080205806989ac42250b00c424605a549c19805040a12a180294f45ae04a8040105406a517b498922807105101e942754e04a0038491406), (96, 82, 2, 27, 2, 27, 0xe1a185a0250004006082385cfe46048a014014406e0e5d82811040210a1013815c3e60420010011404e0126b9814201004118137fa27982800028480009df4273f890880b12050177cf9e788120038491240df2c91b810a09044150137c57e9208410200a8408de1ec988930008022101f77612022408038494405ddaad66820800a120502375488822480241100407dc743f7821048842a10236dce16e2408048504405db19dde8a0001214010276c14ef224410200a8405daeb2db8a408071041827696d7d62400241100405da01d7e094200c025081763767202529040125205d89b87e8208c0902850236264ad2240a044104405d8572ac881080500610076011f0e2020038491401d7cdefd890280710510175e38f0c2520030091205d780ebc804241004918035aa5e7604a0000001406d6a65228208c01008502359b6d5a00a8221085402d62f3e989088031005017588274e0903004020608d61890a8240801000182357a3f1e0420231091404d5e47f5892a488429501f556f5242520028481205d4c984788400040041807530e4122508008404605d4adf9d8840c110481807529574209430240a8608d40bdc78208088420502350012be2900030090609d3ca31f801041214a10034efcea204a0008401406d3b9259811040a12a10134dc769a240b004024405d29f69a09500021020817494fbc20840040108408d167e29894080100018174446d008520028481244d0d8f3d804200c025180342103ae00a8028485402cfcb0ab882ac01009500f3ea770a2128030095601cf75a2a824800c02458233b6314e0529008425604cea2b65880880310050073a320f224810284a0407ce3cf0f880840802850073831b902028030095001cdef2be890800400450173705c6a20230240a1401cd74b18812a088421501b330c70e2540018418605cc1539d802040a128100b2fdb0c624a0008401407cb88ed4020000c02400232dfbc562080241100403cb729db8a1080500610272c112ba292b044125609cafd8598922488429101f2bc47de200a034094401cac981c814800400458132adc2b20123004021600ca4b78d82088090205023281bdda2520010011605c9cb228802a00c025500b2692cbc29010200a0209c96e364885080500618072588c022508010014605c9195378940c0310818171b1e9462482004000407c699ae28240004004182319e29ee2022004001401c675b6c8822090441100f19a92542900028480209c5c316f814a000001581314a0a0e048a024084406c45600e8828801000500f10860c220a0038491403c2f9a3f894000210018170775d108420018411044c1cd94d824a004005582305372822108030094601), (96, 83, 2, 27, 2, 27, 0x83bbf08912400709224910705d39880800610450060d5f32304a100200430441a2498e04a001841140683297824485604814a80b05f1e978822805005100e0b2e5c7009001c248b00410835022483004020407820c08bc5284068130c13037a2a88a10c0310a102606ad1cb1220010044202c0ab286a210b044124601810c6cbc105046212a8110174a92221000a122012202d2a50148000c208104c011f4ee21080384946017fdb3d94484040200280aff65f17895040802a1815fea87d900400242802013fd18e1a24802310904077f6d187c0040030822800feba0cd22420040050921fb342651201822090202bf5430fc25280100152057e96ae98415204014a006fce42ac210a0021014111f9825ca42000242800223f2814f224c02110184077e4912645012442148812fc6d66482000061041021f8478951220910854202befe821c89200000012487d84ee24495046212a80efafbce8884280d0251805f4cb8eb1240824290203be664d7a24a00200814077c6c9cbc4a5008020ac0af8d65f18902c090291015f175a4f120400c20a202be2cc03a24820441004077c3ce8ac0842442142808f7f9563812a4884295019efb7d291280820090302bde40ec620810200a04037ba4e51c1280080210c10f729e2f8830803102100dec880691210108808a02bd69a90e24000300904057ab04a744a02010840c0af4cd89081204121481019e98698f000410880a2003cfb469e29010200a060979d61c0c0214028028c00f38353f884a00e1255805e6fca2b04008200902043cde69920828221085408795fe5bc5086008050812f2a7c368822408029100de54d40900208142542003c89ba9e244002848840578eee2f91280080210490f0e789d80300904421009e057aeb00800142403003c091346280b04412440977edcf390a40080202488ef45ca382400121401821dbf2bc312a0024284302bb66b9b2052000840160476c1c87c0800070920808ec66d47883041214a100dd7624ad1201812050202badca0ea202b0240a540175b0e4784a1002002840aea126d888484080285805d396f7f02a00142443023a549c54894001841824874a631d05012080248012e8e37cc08420080210805d14dce51404810052204b9eeae0e292300c42160973db0f805202050940412e7a654909404100480815ce214531205002002202b99aad6e080003009040872f58b94480402802080ae49da768a10c0902a1025c8d28d700449108522013900f47e054004010860471e733d84a1004010840ae3bb11a814ac010095811c6407cd124001c248203b8c32c148088010014042713e26881082040150010e26ede121500100420911c4a5187141410880aa04b89059aa2500030090605), (96, 83, 2, 27, 2, 27, 0x95f2cf24095005090a80d2bad7438940412148181656c4a55121000c208a02caca91502088010014003958df5110a5008020a489299f06009424080290816522b9d81220020084002ca162fa6080804010440893e157e11240020022491279891e8a4000e12418264e3dcf1108100a008300c99656ca010004010060092b96e64481404810880b256499f8930080402101e4a95123001400800aa00492af58e24a801001540792496a944110090a0880724437508040012140180248778791400110840204c8c9443a280a02c484409915f4b9c495404810a80f22a081c094200a1210816450fedf1415006202a04c89cafaa052100002160490d740e4488007093080b21aa724812808c424501a431d0970495802012b04485dbdc628030240a040990b188ec095201084a80d21063488a0a80f1255026420b65f025101a048a0348395a460520038491604904fe69c4280020030c03206fa32880080d02410063f5a8b3026000c20c20347e96ac624012210a04058fb6f53c085007092a8091f51c90090a01004140163e9c91d1214110842a02c7d1a70a08090200a44088f9ddbb90a100802084891f3834f805000e12618023e325491211002000a02c79f2da624400401084058f207d9410020509408111dca32c813000e126101a3b41b4b124501a04a203c75a4c7488080100140488eb4662c5204068120c131d635fb8a4080310018263993505142000800c204c72bf10e04a80485054068dc506ac505007092a8131b271222208010040412236349f71491802010b04c6c13ee221080184146018d00218c410402802080719b75228922480409101e32c5eb71414910852a04c6350b1e090a0040046088c47889c094005090280d183bf798a0000e12410262f1671a1220804214002c5d1313220200485014018b8ff07c4110020028807171cf42212a002101411a2b7cab300409208902014550548e04a02210814068a5b05d9085007092a089143e6278840809020180627d2a2e049481005290444abf4a620a20340914038943cd24504601884281310d7c77092a410049401e2129439026000420420343f9943884a001841104687a33dec4050090a0a8030ea35f18828008020500e1d2b941040482429220443a41bda0843004028408872ed14c0a44028022c090df0b950202408029002219dde924284004202122430ac5da20402210884018602a484498604815080f0b6c797810a4100495012161c50b1261016244203c27edf7a208104852040384fc7e3c1210020028c1109363888128809020501a125f8bf108001c248300c2385af205290284a56048449979c498046213080f083f6500a4a40a129482610486871250910850a03c2025dca04a0010011406), (96, 83, 2, 27, 2, 27, 0xade2f8fc0a5005090ac095bb19c18122412149101ab603ba50294010042b0256be6de22521008421605ad5446ec4a14088208c0b5a48ae88a028050051026b443a43120100e208202d657d5fc0928040105208ac3bb8985200080200413582a79789500021021816af23d71000402428220055c6821a20ab0240a5403ab835c3c41824822508075650c3e8202c090291022ac89b171211806210a02d570520e0900040100608aa7057240210020028c01549152d210a0121414112a90fc991254820092a03d50e126821290200a5201aa01bac4484008020280b53fa84688408010001806a72b30b1215002002a02d4dee1420028038495400a9b722144a80040110c0b5306f4f8a4080f1241826a579a75008401424230054a5cb720821040121408a8ceaa08481201084800b50b2dfd81080100405012a11170f004482009220153cee3002028020085001a76470d44a00070920c0b4e199c2804000e124180299ea1f90250910850a0353235f802808020084009a5d176f052800401104134b9aa388802004005100695c98c91290800010b02d2b6f49224ab00c425407a541d0ec4284008010c034a4e1e1884a01214158069286bcc142001c24c004d2126f6e2802034090409a4195f0c491201084880f481fddb892240a129101e8ff341e1214820092802d1de72ae2922034091609a3532590485006012a00b467c198214a00210149128cead211284020082302d197673a242a014015405a30d1f84491601884880f460c09c880080902010068c03d10405410080282151694ef6282a02c485409a2772e744980090a1080f443ed14880800a120500688452570095002002b0050fd2b1e0921040121608a1ea9b8c484604814280b43d3ff60948410048481687317ff1040910850201d0d9e0562120030091601a1a2768c4210050908c0343109218900809020101685c31f8442002008402450a38f3c8820018411048a131431c00400200228014261a67884040802818067de71751284010042302cfb5f41425080384942059f116c9110400108020913e0f0218a50809022182679ab283121400800aa02cec0c13a25020140106059d5b002c1082090a508113a93ce1884a809021580674dc31300440242822014e933972042a0040054049cfbaaec405046212a80339e87d1094a00c025481671ea9d91281012040302ce33c5ca29410200a86099c561474491404810880f360dc16805001004218026bcc7211050110840a01cd3d1be620400184184019a6d07445200040100c1332315008802c01009100663af3d304808142503044c53de46250304412060597c74ef40a42050942c092e5886b21080021004112596c0f70254800012a034b2546208508028484244), (96, 83, 2, 27, 2, 27, 0xca6ed2e0125006012a4119422cca8842c010091807276a7111080014240300e4b937062920020081609c96a93d4084402802280991f86748a50801002182722588570291802010b0264498f842508008404205c87c07f4481006012880b8fac6ee0a4240802908271efc4df1084010042300e375db062521040121605c6e345184a5200004a40b8d61233214a01214149131ab86541284820092102e31f27b6290a044104609c613fa484a1008020840b8b4d142802240a129100b15ccf89021400800aa026251b90e2541008428605c404db0c5206008040c1388092b30a5041004a08270efdad5106000c20c201e1d4e8f62002014010401c38fcfac5244098a02c1386c47ab895000c02618170d117a30420120884204613eb6b604a0211011406c0cd5cec411400800880780409c78a0200c025102700685570094824292b006004c5402920010011209bffdc62110000308200917fc240d225000e1260922feabdf51420020084204df6e47962808221084409be884c3c484406812280b7d0d60c8a4040a1281826f9a8bef0211002000a025f0e4abe2022034091401bdf22d44085008020a8097b9d1d6890a80d0255016f53a45304040142422045e8266ae0088018414402bce7a784418600805080779419ad814a8090215812edf9aca42600242840235d4e6c4e248202c480407ba4d438c0012090a4880174638a0800a08c4255002e8a6b950250814250a035cdef32a0928028485608b9ad2e6c015048220a80573200bf0a420100410826e60294d1491022080b04dcb9c6f604c0028488406b94a8074500204014081371e93400a0240a1290026e38a71b1214100802a02dc6fc79c80a0048501042b8718bdc4a12080248c0b70445e8812a090441501ae000703104000c208201dbf2b6bc8540048508244b79b3a1c491007092880f6e7b187095000a1220816dcb6eff0290024280b025b075c3e0942034098608b588ee51125002002a491693164e09420061050816d061b011254024282a03da08ba7a24a8008405407b40c0cfc095040200a80d675446881080844045012cce0358141000c208804d9863e3608212210a1408b2d0aa89120008020049164e6c0c891000c0261016c8ff0430285802012302590a192e042b004025404b13489244a5401880ac0b622521d82480040045822c335fdd101100a008a00d84a563a2900018410609afd179f4488404811080b5eb9d8a891041004a1016bd4297504850220823045781cd7600c0048508402aec4bf04480406812080b5d1cfe182020061051022ba34ebd125410880aa03d737bfc224a202c481407ae56838401440280228055c9169c8820c09028100eb907c85121411884aa02d7186786248a02c484407), (96, 83, 2, 27, 2, 27, 0xe3d882944a10050908c0bc765a2c893080d026101f8ea3b6b1210120880a02f1bdc2f62041040128401e319dab44100462120807c5f9df70a5040802a082787cb4f112a101e24c302f0cdf2ac04a1000021006e190cefc5014008008813c2fddc62110012142011385daebc44a0014244124706540f620a0010011403e022cb0c4a84088210c0bbff4e0f8948c0b12858177e4ae0e1404014242004efc0f0288420048501044df80628c105406812a811be675988a0080f12410277c8c61e1060820094001ef7b0ad62800211010409dee1c0f8525204014a413bd48718891009044210177a2cec31214824292a02ef397b462921048521609de1affe9125006012a491bc2e839815040210a181377124d70491002000b046e7613ae284302c4a8409dcd999bc5082040150813b9176408a1048842a102771ce4a0406000c20c0216df3383e2120018411601dbe0eee41004068120811b74d10c804201004118036b17963008401c24a3006d5e729a090b004024608dab355dc5000020020813b3ab961824800a1205823674e94e1484010042104ec89af5e0428028485404d8eab5010a00090a00489b08ce3d8928408028501f60a3c6900a00142443006bf3b1282509008424205d7c3c6241010482208811af420e4802a012141500b5d10af7000400800a2006b58d8e62542024088605d68696a41210080208c11ac16a30212a00a121411b57f1c12105401804a801eadaba82210a024084601d567db744a00030820c0baa8dda2020a408029402353b3ed9040501a04a2046a4ed2d20828028485408d49718dc491046212880fa907168894a0021015817516df8502a08142543026a0ed85e282200c401409d40da8344016048148803a7b8b5c812a00e125501b4ceabeb1220824294202e96e30ba20c0048508403d2979118488208025000ba4eb7cb8840c01008180748adfc312a0820094302e8f8c41a2428038495405d1d638c4425008020ac03a3a82a6883048842a100f4711acf028482429230268cdb3208080010010042d1870dc902100601284819fed56e202a004005410b3fbe9c71410024280a04e7a4b1122028010015401cf3ac66450800401108139e3456d812a004005501b3c3fbdd10a1022084300e77e9f7e2028020085401cedaa99c480205094080b9c7d3b1884ac11049580738636ed1204910852202e6bfad962422014011405cd60ba64085205094a80999fe89d8948809020581732d5d3d00449208922016650fb2200a0048501402cc84a1844244048102c0398f4a540a4a0121414827318de1d1041022080201e62effd6080a024084408cbad42cc494046212280f970de99814800610458132b75f41125101a048a03e53e96e62842034098409), (96, 83, 2, 27, 2, 27, 0xfb956c8c5206058940c13f68465789480100405817eb27cfd04000242802047d5700188140038498240fa2817505082040150013f3334ec81084021085013e4c50f9141101a048a04fc92b1de210a004004601f916ab2c5244018802c13f227fe18a420100411827e2f2f6f128401804a302fc492ace2840231098409f7ba4e244282040150c03ef1287c882000e124100fdd54f6f04848100523047b9a0ba6092a024085608f7289ec44204088200c03ee4bfd489088090205017dc4b3e714a1822094304fb50f4522540040108605f67a7efc505605894a813ec1fb5d82088010005023d78dac0408401c24a1207acd978a2441241128405f591f4a0485201084a00beb11d69883008c426100fd40022b1055002002a01fa770c22254300c428605f4579c690a5003082a489e86ca7e80020061051003cde90e4441400000282479ac227620aa024085403f309b2bc5004008000813e4df6c6802a00e125500bc982b651260014244203f928f34c28290200a5009f1f56bac0842050942809e3d78b2824080d0241823c7ab1591010820090a00f8e4a55a0121040121600f184e1ac494042202280fe20de59084a0080214807c37b2230414810052a0478456e808128028485240f0738fb44280070930c03e0c8371882000a120100fbf20920425002428082377e2db6a2808010014409efa08e241044028022811df3ab378020412148100bbe3e17c442000c20c02477c5727e280b02c4a4409ef849afc498201085080fdea5713810a4804095013bba703b105100e208a01f7711c2e092a014015608ee9eadf44a5000000ac0bdcd1a63894000a1201817b8002931050118848a01f6e5f42604a1008421406ed2446f45002090a40813d9fd2bc220200a1210123b06dbc51414014242a04f5d0126e20c0038498403eb8933cc0a00090a00c09d6ec4c122000844040123ad854e6449400000292475af928e28012210a0409eb12eabc0210090a08c01d56b14a894a40a1295817a6663fb1494820092b04f48cbc682540038498205e81b22f40840030822809cfe82368a0808440450279f730aa429002428092273d5a8860940010018608e759d2541244088202c11cea48b6820280500510239ba22b60490008008904736db13c2828020085009e68be2740080090a10801ccc854a0a4840a128482799778f11091022080b00f32bc0060020048501400e649a56c4a86008050c0bcc2e7498820809020100f975d5d8048481005210472c4aa262940020088609e54393fc4044048102803c9e527a893041004a101f928dbcf1004820092200f235a2502520038491205e45c0ad45044008002813c85b5468a0080500410278ff152e1410008008804f1f10bd22542004008605), (96, 84, 2, 27, 2, 27, 0x8f50a12209290401256088e708e7c29400401082098e6b95ba21000184106018e635af6282201c4114098e5c80bc28280100150098db421ae208b0240a44038d9d2e0e28400300984098d978f4a24280485054058d7b60ba29210200a16098d6ee71484a80184150468d569d7228200100114098d23d41889080300942488d1358be248b0441244078cf7308e01290401256008cbb69fa24c300c4284078cb693ba04a10000214068c79dbae04280485054048c6dfa9c80a00084010428c57804428080401040098beade3628082411044098bafe076280a0340944098b8d8c6e04282110154048b886d56252203c4916058abe93a824890084240078a92335609230240a160889c1cfcc884003849804889864cea28410284a840989414b748128038495240893c0102208b044124403893a6db60028018415400891eef02090801841460889030c8c254004010820588f53eae242a02408540588f48d9e20a30240a140388bf212a20290200a5401886521208840211018048885b181a04a80084054068832edc22088028484403882192d60901040120608880b0fa4242801001500587ea15f20420241101404874dea4624c12411284078701793e208823109440386e2d202284200400840986b0c66624430240a840586ac79ca0908030094608866f289e24a804010540786189dd6280202c48040986059d3e212001001160185f44322292804010560985ee32e2280002848040985b872e2202821101540185b2ed12090002848060885727d0228080200844098569d15c21080300942018567723080c004850804285535fe628290200a5409851ad64a2489048524407851293d60842004008408850a3e5a21410284a86018494a0008528038495244847e0fa4092801001520884735a5c080803009400883ff3212240a01401440583f83aa424c104012800783ba952209290200a5608836c5dc6212a034095601835fed2e0922034091608829fc6ca21030240a0601825d573a214202408860182582fa224aa0040054078210a59a010904852460082107b5a282002008140981f66fe220a90284a540381da3e3e08092210a440881d295ba242003849140581cf31f4880803849404881c489422943004028609812087fa0942014018608811332ce2042004008401810c87aa282a0140154097fd3b86e208a0340944037fc5725428080384940097f7e4ed624a203c4914077f6c5dce04c10485284067f5e4bbe04202010014047f47206609280401056087f2338a620082411044017f0a80d6090b0240a46087ec4585e24a10401214077e974b6425290200a52057e73279e08080384944087e22c85020810401200037dfdd48e20092210a44017dec738809000401002087dd1fc4e2421008421405), (96, 84, 2, 27, 2, 27, 0xa212cbda29430240a8609a1cba39e24a8221085407a1a7121024a8040105007a19dfc782928020085209a19ac282200a014014401a18e9d5a0420048501404a18475642940018418209a050634e28000200804099f60559200212411214009f5397e200882310944029edaf2d429400300982099e67c33a252a02c4856059dd88a6e24c00384984079dc7c91629280100156099dbaa9be25080384946059d96123605210084216049d7bbf8425210000212059d760226250201c4106059d32b92601000184106009cedb6ee00802110104029c79a89c29400485082099c4fc1a428010200a00099c35d59621430441286019b94896e09020140106089b94671a09410401286089b93fdd828090200a40099b8f96e025410084282059b7fdc3e01400485086009ad82fb624a92010254079a90bc2629000485006099a125162092b0240a560899cf8a04252900842520599b6b17e24a202408140799ab5180808804850404298ff000a208a02408440398ceb67e2429241125405988e0b702520040101205988dc00e012801841560098317bf624a00184114079818fbfa24a3044121407980ec3da20a304412140397d2d8ce282203c4914099766eb8a20a8241105403975d459429090284a420997595c02280200c400409975505be240a03409440597414ec22082004000403971d961e20290284a540196fabbb2284124112840996f1f3ae250a00c40460596b88ab6294200c408609966f77d224212210a14059656c092052a01401560496296fcc89200084012489620cc9a04a920102540695e36ed48908018414248957cc37a212802008560195544ae609400284886089551189e05290200a560495502656210804010460195319de8242800840500594df2ece242803009540594ce7fd024c100842800794b3a2ba248200c40040794a1a4c888202411010489496d41e25030240a0605948ee95a250202c480605948d1d742528038495205940436b82840028488009939dfa9e21230240a1601933a079a2808231094409930d026c800803849404093015bec808001841004292da2854882801001504892d2f262050804850460492c4082224ab004025407929676a82920038491209922f450229290200a560991d452e220892210a440391a808e200c1048528402915a4bbe20212210a140191508536208200c400403913186d42089040124003912ea4d220012210a04019125847a0540048508604910c18fa24a300c4214079106a6f2052803849560490f6f0c6012804010560090f1b682290300c42060990e9ccde00a001841140290ce73c8254104012820590a4806e008200400040290a0cab888082110140489099fce625280200856058f7d5e0428400200880098f782b1620aa034095403), (96, 84, 2, 27, 2, 27, 0xbe0de77a290202c480609bcfeb2da0080010010402bce28b7e292b00c425609bcdb625e08210284a1408bc2751ce00a8231095402bb167f9a210a01c414601baf8069a04a8211015406baef9bca0140018418600baeabe4620412210a8401ba8a67f62001048520401ba545a3e2020211011401ba2619c62428018415405ba0e2c8a2088018414403b9751aaa20a9040125403b938759620a0241101403b8fe428e2502034090605b86d52a20420000001404b81ea222242a044105405b7fd110a2800241100409b7e270162441201028405b7c368122908028484609b6e8265e250203c490605b69f2d1a280b004024409b587813a2940030098609b523585e0809241124408b4c41c22250a004004605b4780c160840018418408b46bcba60800211010408b4208b3e2540038498605b407e1ea0822044101408b3d4774e244201c418405b3d2e3962008018414401b3374ad22908010014609b2d1c0f82909040124209b2640dde252a01c415605b23e2d7e24a9008425407b1edab688828028485048b1b5dad6248300c420407b188f02a25010284a0605b11f39f88808040104048b0fe96f2202a004005401b0e50ace0101048520600b0ce05448820201001048b0c8b3808828018415048b0bce36604a1201021406b047c2c2208b004024403aec8cbf208292210a5408ae54c5842940028488209ae2998be20a0048501403ada031a40908030094208ad888ca624a0038491407ad20779220a1241121403ad0e1d662021048521401ace7642880a8008405042acc6e38a24a8201005407acc0bc622429201025405ac5ab966042a014015404ac23233a0120048501600ac11c7fe0528010015604abe1532a24a1241121407abd41b188820211011048abc069aa0809040124408abafc93e2542014018605ab5c07422920030091609ab3300ce20210284a1401aac83c76214201c418601aa8ba46e20a90200a5403aa4d88442840040108009aa4cf08a20a10200a1403aa00012a0922014011608a974cf82202a024085401a8deaa7e290a03c494609a7ecddb220a8010015403a7d510e824c0040108007a75f0a7c8140028488240a74545762508048504605a6e87d6c8528028485244a6b56abe2420000001405a6009eda0820211011408a5a9506e248b004024407a5a0003a2940038498609a557d8ee28290284a5409a5133c2629090284a4609a4cebb7480a0201001042a4b6b68c2920018411209a4393afa080a004004408a3f04aaa20a8231095403a370bb1a24a30240a1407a348f95a2003044120401a2b88f0604a2014011406a2a1ddee24a2044101407a26bb5ea21090200a4601a25b55b604a90284a5406a256d0ca2143004028601a25392902840030098009a2286c720088211014402), (96, 84, 2, 27, 2, 27, 0xdf2ebdd60928038495608def622b22922004001609de721d0609290284a5608de27f1720800010010408de1dbeb08940048508248dddf882c2428000005005dd75f23820a0018411003dd3a9bda09410284a8608dd033c602928040105209dcb58c7e082b004025408dc69a54a250b0240a4605dc2982062840028488409dbf66da2082a024085408db53b9fe280a03c494409da8bee962520038491605da65c9782920040101209da1700922903044120609da11040c80a8028485042d9969d362902044100609d886d32228212210a1409d745a41e212300c421601d6f9fe422543044128605d6d29e1e0128028485600d67ce33a24aa02c485407d61fe1b6090a034094608d5c9df120429048525404d56bbe76200b044124401d311a5ae2040048508401d2aac68e29090200a4609d269098824a8000005007d18075ba2028018415401d12d4b7a2522034091605d0fa6ad2280b00c424409d0f19f360941048528608d0b31c3420a8010015003d06b88ca0840038498408d04bd40e2100040100601cfcfe4a6200a024084401ceefd7e62529048525605ceb57ac42801040120009ceb46aae0820048501408ce8eefd620a2044101403ce84bc862828010015409cdc0a32a2428028485405cd76560e282302c4a1409cd56090a20c0211018403cd262bb20000211010400cce64df22000211010401ccd6f76a202a034095401cca6b6b62422044101405cc80e20a0829048525408cc205b982901040120209cbbf35c824a8028485007ca7ea61604a9241125406ca645076210b0240a4601c9e2439e250a014014605c98392262820030091409c8d3313c80a0010011042c8c497d00921040121208c8816f362522044101605c836a2108928038495248c7f589ea092a004005608c7b39d42282204c501409c7111a762002044100401c677028224090284a4405c631f9260121048521600c6276b7e210201c410601c5f628b6250a024084605c5ea17e22840241108409c59b4e2a24aa034095407c58355322001241120401c4bc31c6290a014014609c460f7762442034098405c411c8e22522004001605c3b7a1e225230240a1605c3a4653624a200c401407c3a1e8d604a0048501406c3773dfe04a8018415406c37137622528030095605c3595f1624290200a5405c3235376082a004005408c295952a20a2024081403c23acb5a20a10284a1403c1eaf8360420008401404c1a047fa0528008405604c168860a04a9040125406c11b7f2a2801040120409c0b49c22252a024085605c019e35a20aa014015403bfed6112290a02c484609bf624d9a2120038491601bf532cbe2442044108405bf52548a0128048505600bec591462803044120409be6f393a24c1201028407be25c4ca2800030090409), (96, 85, 2, 27, 2, 27, 0x893e1eff14a1016244304c4867e7a8a4ac0100958262236586c5210060128c1310eb6af024a801001500787d0397d048500a00a30443d98dbb8822412149100e1d6339340112090a488050e974db625280485056058735c0b51294820092b02c38a93a4825000610618221aa5889c125408820ac110d34293424a8008405007869210101410024280804c2cdf926892a40a129501e13836509005005090a0810997e97c20a10401210038425c523042081425420441d02b068128490448501a0e6f3c6c505404810a813060df940802803849504082f7f009142010880c204c15f4923884a4080295806078cd8e41210070928c1103149af224a0028481407817647ad0010824290a004048a570894280d02518160226190c10424822428110047726c89280284852487fe2e2fb1090024280b00bfdecd628a100121421025fef281bc5280090a10c12fe70aa52280a0240844097f0a665f0010120880a003f34e7258830811042100df70d7ef40282090a50c00fb325a2224a90200a54077d876a971295812052b02beb7f124884840a1285805f54521a41280090a10c10fa49e5be24200284814057cde41a7142001c24c204be594e9e802a0061055009f0783dc44a40090a02c0af822280a09200184116087bf766071090014240b00bddf835c88028110411005ee8d6e144a12090a48c0af74107a600290284a54007b7998cb1495016242b04bdaf154382484121485821ec54f4004a5003082a40af61135ae29200184116097af595a512a101a04c302bd60759288420121411805e82ce29c0a50090a0ac08f3cb389e200821101440179cd486a148400800a104bcb6a16e094a00a1214815e58f2fe44052090a4a802f28f6b4880a0018411042791034a91415802012a04bc5f844a88080904405005e0c00e7c4244038822c02f00f092a002904012540077d7d62914a0020084304bbc9fd728928807104501dddcd3cd44a86048150c0aeeaf37a624280401054057737879444940200829243b78e0bd0928010040401ddb7700744280090a10c02ece330ea2528038495605766fa3f5149401804ab04bb2642650a0a00e1254025d8cb90bc5242050942c12ec37587a04aa01401540675c18a0b149001c248b04ba9f92c7880a0904415005d4dbadfc4a82050950c0aea40213a292b02c4a5609745eb001009000c208b003a13723a890a8071055015cd0d25d45010080208812e5fa048a282202c48140972e474f2449400c20a9243960431f8a48c110485825caba0d5c4080422030802e4cc881a280924112440972641c1b1405022082204b9111480890a0904415015c5d9633c1004028020810e1925a0a252a014015605707801711054014242a01b83817e2804a00e1255801c060a65c105604814a810df7031fe280a01c414409), (96, 85, 2, 27, 2, 27, 0xad887a831485006202304d6bbb3f1802a410049500ab295020c500248224081358039fb2282a01c415409abe9c7810094814252b0055e980c8884a4121495806af1adb144202090a40c035703bce88920048501248aac1d1f11021022084200d5112c0e0a5040a12a0826a6c267ec425408820ac0351896b062820028481409a8c42742404401c24a021545eca5e894a8110415816a2341e1c4214028028c0350aa9906294300c428609a69170a3105401c24aa01d2c7bbd78948803100581695dab16c5216008048c134ae6bff221090284a4601a53f4de41414020082804d24ef37e8a50813142182691c957dc5284078930c1348558a5228090284a4409a35eb6271295002002b02d1a44e68820208440510228b5ec3740152090a4a805453dcb8a0828048505408a264e8191290014240b02d12bec7a894ac010095816865a43a45286058950c1342ce55ce2522014011605a090ae3f149101e248b04d01e5a7e0a4a00e125482680193f3c425600804ac033fdbafa6244300c4284059eccb2970010108808a004ef5e1258948c0100858167580909410404822028113a7d0b0e28290485254099d3b6bcd0050820090a014e8e2b248242012141182273e9a57c4a5003082ac0b39ac08ba09010485206089cbc016d0051002000a014e27faf2090a00610540166f0f1f345042050942813357840d828280284850099aaf0d251215806212a02cd4ba312220001214001226823fa8912100802084913348ee52212004010160198f670091261022084203cc0e98d18a1080710610265ee8edf45250090a0ac132f0295722540028488605977c1e831054824292a01cb5d58a5890a402109501659bcb8c91040090a020912ca84d9e202b00402540195f5f0d3004400800a2014af57063094a00210148165745c9844142090a428072b309c3e00290485254009432f60c148401804a104c9f404318a4880500458264f264d690150090a0a085278840b620430441284019368252b10a1812054300c95f22088a02006105102648af876c1010090a0881120799d3e290002848060990290a77042002428420447ddbedc8a4a81104158263d3e00f44a14038828c0b1e21f66a254201c4186058e833a0e149401804a904c73cae268a080061045026395b20c450800308308131c0da08221210485216018db92df9105000c208a01c6c984ec8a0800e124502634ae2aac415608824a807190fb22e09400384986088c5210c51485822092304c61a3c57894240a129181630abbe244a82090a50c0b1826fa86082a0140154088b5dab2b0250820090a0345a3782e8a4280710518262c42551c4242080242c03157a203621400401086018a968faf1041802010201c540c3e98802012141100628a3ad940140422022805139147f88088028484042), (96, 85, 2, 27, 2, 27, 0xe43aef891485026282304f15006b98a40412148182784279d14495003082a80fc1daa9fa2920028481609df8be5ab1421022084204ee7a8aa7820a41004950236daaab28494201084200fb4aeb4d60928018415608d8a112bf149501a04ab04ebe3ed6d8a4280902118275601f8c45280050910c13a6d89b8a212200c401601d36985fd1495012042b04e9b155400a4200610508274777922c4a84058910c0ba39fd8be01090284a4600d03d612f1091002000b00e7921ccd894ac1104958173c70aea8505208024a0139a64fa1220c3044128403cc8559ac1410820090804e63c1a228948807104581731b6bcec50420802428139459ef022088211014403ca1b64bd1091802010b00e50209198a0ac03109502726cae9744244028022c03932895ee00a8211015402c9563046405400c20a821647b7c2e220a01214141231ecc7dfc4a5005090ac0b8e26e5c6280b0240a4409c70e47d11411822090a04e3748822824240a12918231b7bbd045246098a42c138c24dc5e0820018411408c55d3bec1484024282104e2ade35d89484121485817136cb474005042202a80188c9ce4a2529008425605c358a61f1020120884200e1ac468c814841214858130cb3f5c91200090a00491854a17fe202a014015401c15880cc141400c20a804e0a97333884a80310158070131ae79105042202a09180478a0a2421048521405c021c7311490820090b04df9d064e8a428010011826fb9c7224015248224a8057cd4caa60808010014408be3e088c1254804212803debddb7f220a0021014122f5833f944a46018842c0b7a246b422808048504409bcaa50c5149401c24ab04ddba9ad18808c110485006ed8b7b4c005248224a8017664042a2900040100609bb0422df1295806212b02dd40df238a5040a12a1826e7dcb2dc4a5406812ac0b704322d62140028488601b7db8ebe1490024280904dbaf47a488088110405006d989554c5280030830c136af843ae24a8028485407b5767d170050008008a015a601e72894a4080295816d2673780525002002a413693330c22523044121605b46f70cd1410824290a04da18bed581084121485012cfd3b0544012090a4880367d9f54e20a9241125403b3d068fb0050824290a0159b6487b812a412149501acca35e0c41004220208076625a2a620a8018415403b2e267091401022080204d951a1eb8a1041214a1026ca0f0df40114008008805637cda1a2843044128409b1889d85129501e24ab02d8a2f918202a00e125410ac3f280fc425205094ac0361b29f1e00a1241121402b08cb2f4404400c20a02158342b148a1080f1261026bd9044b1105040200a0915e7bdbbc2928018415209aeb75ed11250804210a03d732a19b82424121491822b7d8a2644282080250c035bd3d0ca2041048528401), (79, 87, 2, 27, 2, 27, 0x192e80d828a424121491826740fb25f1494824292b04c8e74c3ae2829241125409841adb6711210090a08490f9519c2b88424121491805b2f04a3a449402428292436201bdd228212411214096908ac464405248224a802cd72a3b88a4a80f1255825913eb95d14a0824294304b1ee7a1ee2141048528601625ca0b04505208024a812bddbbe168a4a803101582574aa5fb11485812052304ae8dae7b220aa0441054035cb56d7bc505008020a812b84354198a4a807105582568eed20914a100e20c304ab936538e2909040124609568f6320c105042202a810a9fe5af2824a412149582152b5d2141490824290904a9c7b0f90892800840524852652e064525003082ac12a43374558a4a81314158253ec679f51084820092300a6be44e76292a0040056094d2f5295c5012090a48812991d9ebf8a4a00a121582531717e87148400c20a304a59c11fea202b0441254014a60427845214068128c1293abb4ff8822811041100d1e6a5d061490820090904a3c0885ae082824110540846429e344105205094a8108c3b0fad8a4ac090295825180b34a31010920890a00a2d6c1ec62828018415409454c3415c415042202a8068a48f553802a8010015009136a94eb1484024282304a22e3d5fc28290284a5009442877664105003082a81088405b70892a412149501d0b564df90250824290a03213a6420a282824110540941bd2369c505608824a81282a072ea820a490449502103b16a911415812052a04a04d7985624a10284a14073fafb50cc4942090a4280e7ea73700890840a1285014fc659d45005400800aa011f5b0af9c29080384942093e939afc4425400800ac027cc858278a080904405024f9126217125500e20aa039f0da56a488280401050483dc04ad5441404220228067b01b67d22020121410120f39be3911094014242b009e70bac1229200485016093c9680a6c1012050948810784f87c68a488071045824ef9c7f9014948200929049d9fdb67609280485056083b22504cc405208024a80275d2c5ad8a480100405824eb701a931015022082a009d5642cfe29410401286093a87d6f2c4a42050942c0a74db49328830090442100ce93b0f2f1411022080a049d11d6652292a01401560939f6ebfc4105002002a810730c443a8a0a8110415024e59e0db6125400c20a8039c98d7ae624c3044128407)],
  [(96, 76, 2, 24, 2, 25, 0x8478474a0a08120a0838445d5082400922081283dadf0a22481222483819f845224012824211813763f000c800006887f55e4e8024812024827d7f698a2a40282a4037c58fad020c19224e087ab0005004498004e907931501004c02800618784938282a40122a4027804664a0009800488377d4017204c8000069975fd7fe824008020812758508aa2a00002a00371f83b5008883a082887098a5d220483a2068170898f5028c812286887059f00a04409200c136ec189c804498004c926af0ab3224409220e1169f7dd282200122200269f339a20a48000a48169b09af204088000a9166d55a8800009200802667d3dca04408000c1364ed79600608000209064d1c3c220c18024c0961c4824a08482808483616a304a02081202083605774c200498004c815e4ef94a064028024135cde644a080880088835bc96e42064812024915963abd0004912046805805442a06483a0249356d015d0048812002985564280800480000482540f6f90004800006805389e03220498024e81512de4022409002409150d04e48064828024925095245208083a082814ee7e2a8064800024924e4380ca240028200134d9b3ef0084028086004c6eaf9008c812086884bf2df7224889220a994be28168000992048824b7226c820409220c024b1d988a224900264834a70f5b224408020e1149f9d27028808028a084720faea0241120640345b723f004c012006184140e18004c800004983ff115d008c03a086083f3a98d0084828086803d98b27000c13a046083d975a90044812006903d62885008488008e803d5d875008889208a883c2ce9320848000868137736f1020c03a2060836793b0a200128240033470984800488000c82340c0ba224489220c91330f80f220499224e81325638a224c18024c193182a02a20409220c032ca2fdea0a48000a4832a04d88824409220c12296fd34a04402800413293c1a8a0048120048327e1cf302848002868026fa05d224491224691269af58808488008c822668523000499204e802545e4b220c18024e0924260322248092208191d86863024c900246981aa42b3004488000e9017fad83204c91204699168e487028883a28288157f331000488000e80155e1f8a08000008003122b7d480a48120a48211d16c6800018004802119112ea024128064030e81c8aa0a40000a4030b2d55222401802481105199ff024082820290030edf522081282420902389b50004828006800061782804009200812002661d204002800211), (96, 77, 2, 24, 2, 25, 0x901ed5590244140014cc6da49ca08024009020a3389382000930009d0116ac8a2a220928260838b40fc2512249412249c5954bfa09104489104a2a25c9a0410124414110e4c6df220c03a20609863aa9941220c912609431455dc803004801826180f0d5004802404804fdee173024c88020e987e014b74150009150013e3d7ea40a120e8a1a01f11b359014800014804f77c38ea084800084837a89c23503040001049bd012d7a88024a09020de616226009907400d30f0d933300488000029878410cf904041404140bbe8ef0488124a091a05dd43ce144c002444026ec8a70e824019224812763b60f912601d1030cbb14b49408300a081821d69905c011900010910e8a8ec4808080008082740057b902240000348b940046409124a091a41c73211e049812441c30e20cf8ea26002822013706ab67910244010740b7931d54882224882a25bc855e1000902400904daf58470008912042886ca4f01112004910408b51ac1f2020204820209a54031a049125048530d294f308084800084826900f06900249402340b39faf84093244891a619be9191410005010006caccef4800098004882645692c910240910340b21276928a100a0a100d8eb282e009027408430c66f9c922488002029963354ed515240015241b12cb87c0020448108218808062001920008d10c3771b482241122640261908fe8004480021442fd793a4091240091a417cff13e040900040d00bd5c32d204008000a115e277cd8146400143442ea1c354092240090a617264e91444802444806b8c1a7d000c828006885c452358146014143042dc221140120448108616c3404e011805010c10b2cd1e9020488020e8058cf2dd514200914201ac4d7d0c08304e8918216027a9e001107400510afbda98a08082808083578cf8b510001410001ab249b8400300480182154e934e400912401d02a8ec1e0020c800204885256bfc113048013048a8f75b4c823224823a25475e011414005014006a397086a2a08122a0835189617912009d12108a87e8cda81824001824d43811720510074504109e475e88024800024824ee31c7104240004240a6cf8b548a12000a1a05323221d41081241180698d87768260812220924b4d89040024c002641252d743c0930200838612837996409825008c3292b3ea9228483a286814946895514044914441a4947794021200021a0123eac590088050008249059c81000493a04680462c28d810248912340221142b48220200228250b98d1a450005050402856d385224082820291), (96, 77, 2, 24, 2, 25, 0xe16ab8f80060140030470a5455a88106489300f8033dc2009825008c31be0fe5d004c90004698de16d678122400103486efa88da01900a00904b7784b3a400920008d03bb06413024813a24218dd6aaa4900609402304ee75344c80200a0008277086d3e401900000d13b68d779020808020a08db374da91244891214ced890e3800320000122357f91b1040802440805abbf560a06490006493d4da73780400140410069f279008910200830474ef11ca041120048511a688166804488000c92d2768e380240140010c6889907a02920002920b3abbb9444c92004c9239aa1816a00412804403cbfbd41511040911041e5ea60008230048210272b5ef41414100014107944a524a28008028803ca09162503008903009e4d147d482120a021a072372aba009905000d318e133b5020888020a88c6e057f80464140434463045fa4001224803a03142775901000241000589c775c826001222012c4a19ae114240014240e169703a09026009224af5f0476001925008d117ae883480a08120a082bc2be2f500240000241de0d488a09900a08904ae8ffa5e011800010c1173597a0802490006482b9823eb8022480023485c6dec50893260093266e20af32401912401d1370264cea26012826013b7f7319511001411001dbde96da82120482120edd2037e0091100015316b167b4a24089220893b3d767741204401044959d7fef0891220083246c97a3d9048805040825642627a808008008802b1286d8414004914401586cc29281122000324ec26610e4481000405236027284a24491224493af09450503249403249d74c7e1c81020e800a46b162ad940c002404027582d09ea02402802403a81da98914441d14144d3780cdc09304e8918629918a3140080500080749560a4a06480002493a41bfcd81460091430451e5b7aa81120000124e8997506400907400d0344c3d2f208802808209a0e665d80244800214c501f8814090220082a4280b88a94101000101073ff8012a024928064839f2743c810241d103404f3c9d2a80124481120e756e3e100880240082539fcc5d204488000e919cdd830513001d11009ce64290482320e821a266f843754488074408273763725024c028206189b8d60f914241414340cd81b04889322008326667ad6554481324491272f2bce8a00488000c8396c137e510244910641cb0637c889204489006653e2ae10109024109052846b3f024c98024e98932efdd80264000034c4975e79a88920008920e4adc46940080240080724c1f76a24401220413), (96, 78, 2, 24, 2, 25, 0x988ce4e288124a09120e5fdcfaaa20480020483975e46ca81104a01104e5cf4f0d204409200e1197166fda02820002820a57d78caa080080088039446a97c090240090a425101865008c83a0868893e6064c81004e8108464ee0d5282648282249293a9fa888812600932064da9577208408008e019326137281900e80904e4c607b5200c13a046099315c5788810200830064ab5164a02401202403927172d280920000920e45c96d3004c98004e989148cd1c01324a011a6244d51aaa2401122401390bc4c1201120000124a4204caa80a00120a00290521534083200081a2240b5054a264828224938f88921402220a020a223d4fd04a024900064838ef9913c801260013a063957ef08260028220128e44ce2482000a02080637771888244900244928db9cd6a00100480100a35fbd44a084012084038d1d3c4401020a000a423318953200809200a098be3558400124a011a022ce1f2aa260812220938ae3017289804489804e25c68e4a2800122800388f5cc2c8810248838062385a8b0208128242088855ac3a09804489804a204ac3120081280420987eeded4023200021a221f3526e8204912244828648d36a89120a08124e1825b9b000c03a00608855dc470881240091206145bed8a0208000208384c04a7880924001920612cd152a20499224c838476ad24092260092a620e623c1000802800208836423a282920a02920e0c901c5000c1280460882f9bdac08220a080a220bb281480640120241282e6b43c01120e801a420a089300244800204908256c91a89004a09004e095325b008083a082808198c80c801204801a0603d5c2d02081122420880a3d304093060093861fe5c9f1204c18004e197f3603e8818204808245fb91c6c8080880088827ecfabca089004889009fafd0baa0a08280a0837e51e2fc812220002a65f685835200c93a046897ce7220a020024822009f1d8e6a820419224c027c1f2e940a30000a1821ec6eee08044900044927b06f47c802044810825e89d0ad0244812206907a22226a021020023009e77514c82401122401279c2e9028a90048a900de6b9dc3000c91204688795b2b9c811004801845e3389d280448280049278aa1988801220003205dfca6af024098024a90778df75c0a22200a2a21dd231b2a2a00282a00376f767020a10048a1009da7ad722060900060917675e69281106481304dd5a8f7d220c83a20689749d44aa09000a080049d032c97004c99204e9873e5cbb489224e890a65cf67f4b224093a2429173a4f414811060013845c7802fe824082820092), (96, 78, 2, 24, 2, 25, 0xc7b6cdb288020a08020f1ca5833204092804291c589f3f400204e81082315b4bd1000c19204e08c53a00240a300e8a18230e94da6804099204892c23309ac08304a0918230856e9e224480020491c1da67ac083244891a23031f6dc024c88020c98bfd31d6a0a02248a220afc655ab200c03a00609be8a51628a92048a920ef82cc17000490004680bcff32d4883020083826f372c6d204403a00611bc884860808240018206eed06eea02001202003bae66fac09320e881a62e901052208888008889b991bc7c09220e880a62e609bb2824090024092b7b78270893004881066dd13387028488028e80b6f2d1e8093020083062daa1c5ca0a48120a483b6954eca81106001304ed9ab310826401222412b5c34f8a80102480300ece928ef008809208a08b2df8194011200001a42caf7778822080022082b2bd326408320e881a22caa0c5f208c09208e09b209c4c4813044811866c3cffdf020c88020e88b0e86dac81000e800846c35f625004090004290b0b4052a89924009924ec0830c2824401220412b0202fe4081240091a02bfe5acc804018004812af84393201104481104abcb5cdd004882800298af08c3c8893204881266b9eadbd024483a20690adb926bc88224a090a26b59f23b204408000e11acdf0f7c010260012a42ae3a3c3224002820211aa977cca08820488820aa7fca4ea22082822083a95a6844882240090a26a18e5a3200c02800609a84a007481300a001866a0d8a71000888000a88a7b466ec89204e8908669cdd88b024092824290a71ab40c01304e8118629c60f7d200c83a00689a64a6b3c8010248038069871555000c93a04688a58deb84092204880a629615748a04482800493a5557b4089304489106694160ee800490004482a4dd49b88980048880468dec190a00482800483a3757d2c022220022a228ae4456820489220c82a2443ad288100a08100e82faeb8a0a00000a003a0a43684010220002a42821633a826490026492a07c310888206009202681802808244828204929ff5867a80804481800e7e1d504a04083a000939f465d54090200080a427bb671d024c800206989edb733a81000e80004e797507b0044828006909dc0477c02200e820822768d74b2288828282899d5b40e48230200238267482a46028c800284889d16ec0289900488904e735038d0080828082809c9c89ac80306001382671ef462804419204c129a596238809200009206694ee0ca004928044839a000a0280126001320e676ece022400802081199a2026400302480382262d9d69204c99204e99), (96, 78, 2, 24, 2, 25, 0xf55f800c88120a081a07ca011d1004c19204e18f1ee2c8c8a020a0a0a07c6473f7024482820690f16bf10a81920a00924fc4c409c228488028c81f0f13c7400224a010a23bfc5bb2800411204402ef5a6cc0801200001207b7d3f71028082828280ede40eb8893244891267b376b08224088020891ec065d50881060093007ac8bd12a02090006083eae7c6288a92000a9207a7df057024091224290e9f6e72c81320a001a67a6fd81f204493a04691e9bb0fbc083240091a23a34a759028882828288e89e443a80920480920fa24985aa00408000c03e84e448c891264893a47a09cbb0820498024c82e786b89289924a09924f9cd5666024c80020498e6c6737c0830048818239a9d1e0820019224802e6943ea289006009204f9331985004c81200698e217c874810204800a4787e9eb5004092804290e1f3a40402120e821a0386d9e9e220c08020c09e1838fa28a02048a020f856efd6024488020c90e12b3030881220083207840c364820408020c02e0ef61aa80920a00920f82d4e55004c91204698e076c05c8830248838277fd8593024c11224618dfd017d48910048818477bcf8e7224c89220e99dec013c88132000012677783204224889220899ddc7541489124e891a4770c97c4822011226002dc00b4b4813220003a676dcc8f6820411224402db63821c88320a081a276cb475b204009200a11dae574448a12248a3a076afb2eb004883a00298da49a5ba81104481104f68afc1d024488020e90d9e4e8f00132200032636558fad220c80020689d9015f648900248828475ffaa15004812804218d74fb6e288106009300f5b09f4b200493a04681d5f30bc209904489904b55eb62a22a40002a401d4ef69100192000092435304ac9204001200211d41ceec4003220003a234e5f386820418024c02d37c83f48a020e8a0a074d98e59004c03a00618d338640a8a02200a220f48c4a85000889200a88d1a9f2b200102000300b455468d220882820289d0857ab28a10248a300f3e9ddf9024491224690cf7dc55c891224883a473c8e801224483a20691cf03fcf00a30000a10233787591004492804690cd93ad54092060092863355df75200491204681cc88c5e4811244811a473063caf008c88008e88cbf5abac812264812a672fb65e1208889208a89cbe45d8c09124e891a432ecc364a24090024093cb3b9dac893244891a672ce8b95200402800601cb1bd15288800488800f2bd82e1200c88000e89ca5858dc012264812a63238384b224899224a99c8c8a4d08930248830671fca1d5220818024a09), (96, 79, 2, 24, 2, 25, 0x920770f945090505090722d3788a82900482900e44eebe3810401d10104486db8c5000c1120460890be1c344119024109132159cb1200106481300a41c3543104404004404c8229c092004828006818fe25282050810051c011f944d248120200028663cac5d2413041411049477414dd2288028282098eb1e6c60011050005111cdc0b5a08002488200a365440f4142040146014683129b228409228e018d02be1e45100745041319e75f2281120e80124e3293eae512004910409c63c421820a40000a4018c65860104890244092518cac6ba82102002300e306c66a904441d04144c6019832a2a00122a0038ba5166e009910001d31162ef7c400320e801a222c454d4910204010700c57cf06c8080892088828ab7bf0d40893000992714bd4c9c093204881a6228fcb08900640900344c4fc185e80649000649289cec15d408932409927114162aa88904489900e2257cdf504244904641c43e05aaa20008020803886a7f7140c82500c82710b2e81c02200a0208221f8551d910248012340c3ef52f7020c09220e088789bdb6001912401d110eff4a9409320a081a621d01b3d4100089120014342909b004c09200e1886336ace450902450d030ae3b56288120488120e15719d4513041d11049c29fb44520401280421185233316400825008c0309ea114809324009126213b73e9900441400144c2612cd522081122420984bd97654008224088070972b5828a12248a320e12a63f7504040904041c2463cdd208809208a09847663f904492004c90506f05fba88100488100e0d2c64c80064c0027444198a49c82209002608283224fa644902504843305d792bc02000e8208020aa47f1514004914401c11f91d0804481200492821b856100c00240402503e6880c081260093a02063c93b510209412201c0c2835ca24091224093815c03c6010810011c01026d04a28a000a0a000e04aa35c4100489120414080924f00489280429880d755564091250085330188c8aa89904a09904dffc509e912044010548bfe251a60264800224907f3c3b0e009927408d30fe7701dc093264893a61fc79fca4142440146413f380501020883a202887e510478449810041832fc181f4c803024803825f5784cb81260941230c3e99326a228c812284897d29c9e6049807440c30fa4f1a84821024823805f3ec7fb912641d1034cbe79905482a00002a0027c4a051a448900040d22f837dfc40a12048a1a01efd1e2c900641400344bde8680f2240928242917bb6c5d2001030009410f769c48288122008320dedec0a491200c012508bd706677224403a20611), (96, 79, 2, 24, 2, 25, 0xac3f621e010902410d0157f620d400200e800822af65bf111224c012648d5ddf497208489208e81ab30bc0a008927408d2155ed776288124009120eabacd1d111248013240d53878d4226480022491aa1e8c2104c12004c12552f133e408120a081a02a5255e3810244910740549b4410a20491224483a901f6b2011802410c1151d34fac890264892a46a39a25281064c012744541aeb85220403a20601a7c34d154448050448074f044b2488104a0918069a16f5a41200c012409533261e9200401200601a64cfa9d4489200489274c53846c092200080a6298a6a3e502244900649d2bfd662220c01220409a553ecd50548000548054a77955282122002320e9171f1541504001504152115c2ca28480028483a40b7a5844892004892347eca5dc081204881a028f6c5ba40220490060951446262806411206412a27abda9014802414805431807fc88200a08082685dde3a11204c012448d079c17aa04492804493a0ef09b2040932449d0141875dc289104a09104e82dc5e4110640910244d055659d0048012002189fc8882a4411324495133ef1fefa00022480220a7cf2ab751024c012641cf9e4445020c08020e089e8ca6a24500074504033c1d651a8a12048a120e77fbce4810249d123404ef63cf8a264112264139d7ed18940c82240c8273ac10fc20a12248a320a73c7612511040011041ce70a2172204028206019c4fb2aa041902440d1137e5fe100982000882426deb1ac103040001048cdbd54f8a26403a224139b2f3c7e410907410d03364a92e40230200238226b7509990224c902748cd6d73bea04403a004139a8123c2408905000d233493448280106481300e6902268914444914544ccc639e2a24499224c939960616544c90004492732ae6e2c88304e8918266458aee8146440147444c498497204819204a19982c2ca60410324494113005f33209106009304a5efada9511008913001cbc50547004c11204618973be362409927408d332e0351388212200232065a227bb51004c012441cb351f1622489122409996453ee544c12004c1272b6f5e2c89120a081a4656d8be7514000014001cad4141e82049002448295a4e9dd0008300098052b13efa488200e88082655b08f881040c0125044a710f16a0049000448394c16f12449812441c3327e12b1c091260093a424f76169800241d0034049ede12a80840120840293d1f5fa440912441d03274cfdd4813204801a664e81784904441404144c9c6a3ae220c800204899352fcec44090004090325c4cb3a82000482000e4b0cb22902041400148c94fbce7224481220691), (96, 79, 2, 24, 2, 25, 0xd36af3f2009810001c31a53973348020600128274a16dcd80244890214c68f68791208400008601d0eef839440030049007a13514a209122488324b40c5f8c81420141430066edbd2f204419204e11cdb9a49940412240c1079b3b77520a12048a120b33e8792512044010449e619d397008489208e80cc2afc8a050802450c01982879f88132600132672fc470d902240900348e5dfe0c0820480020482cbb399b640802240842395e1029a82100a02100f2ba7df3810448912144653b133f224890024299c9fb09ce451907450d139393a92c023024823823263d1b0910248912340e4641407004491204690c8b3e7d140880240082790e87ee4812244810a671c1f1f6904244004740e3773bff028003a28200c6c28e004488024408238d1ef87c88224e890a2715accc1912048912148e2a9d4ef204498004e91c51da0f944810504012789871a0a08122008320b0dfac96412248912249613ce9d5024882820298c2658e0940091240190784abeabc891060093847091e09c01240401040c61216821000481200680c11562c2041932449d1181c221fa00102480300b031435380064c9027445ff9176d224c11224619bfc1b87a4490050404337f6485cc813064813866f97fbd881244401054c5f0775d0822491226482bd589a3a448805040c2379080b2c801264813a06ef1b4f8904444004544dd91de12a24019224813bb1cb79c04911004113175e833d4083224883a22eaf765a8106089123045d5aa729008403a08600ba0c364100482240c80573ecb3f281820e80824ee4564a2900608902304dc87ac39200893a04289b8c71382441927448d136fda1ed4093004881862df955418144014141045bedaac6a20019224803b7bb7bf60500050504016f0b33cc881060093806dc16360511009413001db81ec79200488000e81b6a3c77e0090074004316c8319bc0a120a0a1a02d678caa111240011240da255d3d200c08000e09b4427492448827448c23680a787c80100e801806cfc4307900441d00144d9ecf60d220809220a09b3ade2a640903000943366f541ca88120a08120eccedf6b40204c0024495987fc3e824408020c12b30ce51e449927448d33639f6878899004889046c634cc181264941234c588b0728224418024c11b10c229944c90244492761e153c4003060013822c27cc5c114600914204d82c8dff004809200a18b00dcca94480074400275f25b4ea09920488924abe1447c50020c002601d6cc51f4a0a40280a403acdf25960490324494315978872c802224802a26b2174fc40000c9024015626eefaa20408020c03), (96, 79, 2, 24, 2, 25, 0xff2a24c6449802440c33fbe39fa0883240091227f4412874022040006097e796cc7004081200290fca7c95a001012401411f94e2c98891024883047f281f3750000c002401fe29f26aa00499204c83fb2f723e441825048c13f6432f6a8a82000a820fea4b6a3514041414041fd42c2b8a04011204013fa0a0ea6411007410413f30eb150819240019247e4cd26940024c9026417bff81eca20088020883f727a1e944c805044827ee32f12489320a081a67db551c781044c0125447b55157ea22492826483f697b8a6051810051c11ecaddc4c810244810a47d56dcb78006409003447aad4c3c828080028082f559ff8d050900050905ea9098d4821204821a07d353e0191244141014cfa5c4e7d204c98004e99f35b4ac2441802440c13e6682e5c003020003823cbde25081240891210c795c7cdf204881200299f1ebb376440802440c03e354d98c08224a090a23c5c849981060c0127047898aa4ca22412826403f12bea51040112441105e20d825a89104489104fc165d6d910448912144f81037cd204802800219f01dce8a048127448521df46ff50891204881247be5a6f481204c91254877a6fb4aa06401202413ee727942008932409d21dcc79b0c801200001a07b710cbf410044010441768b909f004c18004e18ecb69550441010041013d8c9370a82002482200fadda852502044900449f5979ae1204080000291eadc9a0d044900044905d588bc8c81304e811867a75445c104204004600f4bab51f004489200e90e971ec41050110051105d2bb778c813020003867a4d8de7512004010409f44f3702828008028802e8058019050002450005cfc488f4883244891a279e946134102409102417385f4e4224c80020499e66e42fa440900040d03cba306ca89102488304f963493b91264001034cf2bcff02824091224092e42111aa049927448d31c58c29d4812240010a67869f0a6400244900641704b0ae3024c89220e98dfd3223a408030009423bced53cc802220002a2779c36054142049146016f2e6ad8a2a40002a403dcca1ee140492240c907b70299ac82000e8208076d197e28146414143446d981c62a00011204003dacf902e450800050c03b370816481120e801a47663965f900648902344ec7b4c6a806481202492d89693d1450100050107b1096d9a09924489924b5f96d5e81260c91270c6bc30cb2226080022091d75ae826411902410d13ac88849201024481024b55209b0502248002249ea8c326ca24408020c13d472f810401900000913a82c4db289122488324f4f32952505000905001e9d51f90806081202092), (96, 81, 2, 25, 2, 25, 0x9909b64020481800240ccc37b8bc413240008924a5f372c840920490484312f76f44940c90220249397ab425b200c19102704cbc98f9c9026492011a665dd3d70088824004c1032ec0f15a408824804611975642c920488000014ccb90b0839106480091a265ba21b4c88220d4405132c65db1c401130004889960ad7eea04481100249cab4d4e7404200002100a540adca401226000953129b768e504003002480294b8748aa00089100441ca5ae0bf910249a891a06525ab5f4893220041d3329242832408822204611947e3c0e82449801264949d377ce9022480011a464dc77f4c081249048d0126b12a8e4098022006199305179d020802410104497b8d4b10460400230264b5235da08824444c105257dacb94101122088839293ee08828400014201493fbeec9004492010a2649898c4280026440910723d04ece01080220860091038c1c820098012441486686af1132408889246425e20cc89200d44043320fd203c449912220c999071a4f4a00009100401c824c2cd9042012021806409c1d6c091264449d211f0a7daa4499022206998f45516b024089110548478df30b51424400a320e3c44f61c8820644494131e09d7694080300048138ede3c03204402400308c76a490b90420088218063a6718e20a92000549051ce736da450810028e018e084b0aa06081101049c6ee739d9122088891846377076c28800444480071b54e5c44481122208918d9de330a2a082415041c6bb110c110644008322635942b2c083209040d111a6febc2409106a002998bce586282800001400145c4ab3e404204882300a2dc108388822400481131600050a4019200046898ac6608ca24480010249c55fece381440488a28222a403a4c89002004142314d83d204019022004898a4ba408a22482411241c4fafcea410004008200a2707ce2c002049008411138242ba050106a2828089b53fb9224090012148c4d36df591020c889380622fa1c5089206004903310cb96c6448910020e9186735d43000893502144430f20bd902209a8118461664db020a82044541050a684976441010020a09851e5614822481111241427cbff8912008889084611eab1fc08204d44841108e8899a010812208e0083ef485b204c8350034cc1e79f54812401a8808620eaf898401024440852105ff83c9440822224403828dd402a24402410209c12adca6400248881120a0887cb22081264449905038781dc40c90000249181ac40c8a20009110401c082a71a910601208182603e8845c812024401433018b42ec450810028c0180b32395204093502148c03e434580044c0012a2200f93c40000822001000fff0b026051906a28688), (96, 80, 2, 24, 2, 25, 0xbc2c3e50a08400008403bbcc0245224c13a24619bb6b85a1208c02808609baede7a0204c88000c99ba5c98f1204099204a91b9dfe968a04098004893b94af9f7024802820218b926d845228c82828689b8ccc951200418004e01b8b4a96d208403a08601b89fd726a20089220883b8220899200803a00209b671a4a1000899204a88b5dd7592a22090026083b54be95e802491206482b4e13f6d224c18024e19b3b031ca204c81200499b3afb6c4a26080022093b35db3cb224001220211b3317939208c01208609b2600222a24488020c93b23e7592828081228082b1ddc1ba826080022092b1cfa625228401228601b128f419024891224298b06eae76208c80008489b04662f9220c89220e89b01679c2a26082822093afde347aa26091226093af0f3643224811224219ae8c8d41004c89200e98adb32683004889200a98ada41a4f208c00008609aca949d3024801220218ab5f1902820099224882aa98a2cd204c03a00619a9ed6deea24092824093a9b42ead204098004a91a8fcb1f3004080000290a8f98ca3200408000e01a89daa1b020c93a24688a889a1af004093a04290a7676b3d200419204e01a6dd4224a24483a20493a6bfbc07024808020a18a679ab9e82a48122a482a6239795008c89208e88a6095d99224892824299a5febbd5220813a24209a4e5b53aa00019204803a451a5fb220413a24601a44c45d7028403a28600a447c6dd224492824691a440a7d5224003a20211a40671e7028c89228e88a3bdc6ff228809228a09a31f32b2024890024098a2e184e3204c90004699a2e1002d024489220e90a297290a224c90024499a1f2ad11208c80008689a1e59215004083a00290a1d5921c228400028401a14f34b5004819204a18a1325aab208c82808689a0f8bda7224490024691a0dd2a0f208c03a086099fc57a608040892008929f7034b28244800204929f66d4be8240892208929f66b53aa2a48282a4839f2e966ca000912040839e99039d2048012002199e0e7f7b228488028e819e0845622248080208199d9377fe8040192048129d4773af200808000a099d233377220c812206899d11688d028489228e809cb0e5b8804418004c129c4d57930240812202909c40d3ff2044928046919bbbd32ca044912044939bb59ed5024809220a189b9ba162220c98024c899b995944a24498024c939b94c71d220c928246899b5e758b200c928046899ac2d0320240880208909aa1c4cf004099204a909a65813c204898004899999ce37920089120428999986484a2649122649399859a48a0609120609399628d01024083a20290995605f7204811204219), (96, 81, 2, 24, 2, 25, 0x8b91721990044c902544c5af16a808a22200a222622746d524491074405330f6a94f0228c08028c098774d8c7114404014404c2f936a84882220082a2617aa855e451900050d130b3104962084000084018540708f812449d1214c420f2fd788032200032260f0e1e4644113004951306906fa3204893a0429982e3b354802449d0214c4150c615289106489304e0544834640913000953300268acf224c928246997f14c0c1114600014204beede37a2090264892249f75787b2041127448510f9ea6bb8a220912260837ced58d0912044910548be721a7540a30248a3821f16034b540c92240c926f7f3ba7d224c900246997bda12e391244091014cbdb9b513c893064893865ecd210e2401130009512f642f495220c98024e897ae8ff9c91264c91274cbcf29dbb2019244819249e176bc06401027408412efe5baa0a04019204813776d9ad58142049147003b5affba289824a09824dd82edc9c409112401132e9760b68224888020899736663ac91260941230cb98f9184c89020e880a45c8a69a2a451812451c12e39b6e97200c98004e8971c91f3491060c912704b8b8624f408324a091a21c4ceab66448032449422e2267107220c88020e8970fb08da81044c9125443854ceecc002064812821bbfc029a451800050c12dd3dca7aa24418024c136e844584914201414300b70cc3ae4891260093a45b7efb356408120008522db8ed9faa26483a224936d44137d514200014201b688e8da4092224882a61b13d120e409007400432d7a98942a040912040936bc7b0ad114644014644b5c21be1a88924489920da967e406049132449530d2f8c47c208c88008c8969590ada41224401064934a510a84892004880865a22f5186009030009430cf809238a2009922488366f44caa40224c9026493347f8f1c89300a0818659934f12e449810041c32cc91cedc228c8002848966385d0a514204014601b2beb1c0c80104481180595a2e296411910011d12ca71c3fe824499224c9264fef96d914201d14300b27572f0a89120488124d92c9cf56441822448c12c8fdab972008900042896415b0d2900209d02300b1c35020a89026009224d8d356151440120048106c695ffeea040092008136322a5c391264c01274cb190f53ca89020e88024d8bf6155a440822448c02c4eb04bf224098024a9161fba41290200c902508b0f5bd8fa02122482320986107004408910001922c2f90655204489200e9160edd93f912209412308b02d1556c81204a0108657f8f519d008922408924bf54b4a48260912260925ec835d2113040911048af46eda7089224009026579d0b7c5408132409126bc7a330a804489200c92), (35, 81, 2, 24, 2, 25, 0x66fb15fb4812224802a671dfb2cfe441932449d1389d0dbaf228c01228609c0975cc3914601414304dc7bf566c813224803a66e2ee81b24490100414336c65518b228c89228e89b58b6ffe10264490064cd9456647c810224802a46c65aea824491300495335a18edb9228c81228689ab850ff3914604014704d556dce2481204e81086697b580ca451910051d134a69be0d224819224a19a50b080c90064c902744d1eece6ec8920600928667db3678a0081124015213e971991228808028a099e8ed973914444014544ceda44ea082300002102674fdfc1a4010324094133977008622489802489999b38109510048912041cb7f1f86c892220082a665a7e6dfa451807450c132c68ad77224809220a199336a1cf810444910544497145270803260013226465ef56a448832449c231e15c96c2208980248898ebc398f110444010444c65553704890204880a46306dffa2409812401c33175c5c2d028889228a88)],
  [(96, 76, 2, 23, 2, 25, 0x9fa931c2012008408119f3506d2102096440019eeab292010092440109eb30f3211208c448119e9de142020012400809c8adaf20020c0440219c8acdc010a004080019a01cbd2112004400119626bd181200961408094c7280200100940800949c1c3200001a4080090f2e5b21100964401090540ba2028012480808fe927100030c1040218d42833010300d008018d18a7820010894480089de5fc012a00408081896e94b21210854408088f8a9021080044800088b03d3012209604081882c478010304d0082187f0dd12101045400208602cd9213200440091855e5ad200201a408018558c978028048188a0848fe7f2030088448908332f4a21300844409081dd6ba80020c01402181473e92030008408907871975802a0001808176c141d202801a488807626792810a01618001748c00e20020c84482173a193a20300124009071994fc800009214000716643f212208c448816f2679201320960409169e1b6c210a00c488016850764812a0161808166b08d581280041808063a3eb5211201e40811638a2028028008188806107ad88100044100205f0ce4c01120040001158bf69b01200840408057547cc2122044400a154d5acb2012012400115468251800a0121800152ee199011209604011525853c211000c40810517f57c000308104001505e826810204410021500b9e1013201e008914d2eaf88120004100804bfa683201009a448104bbc03e80200c8148a0476303c800a0081880144e628921030c544021443d91900280000808040a6f79200208844801408c52b213000c4089040501cb210201e408013c95e2d011208404011356607b202900148080347eb6e800209a148013234934013008c0489030d9c802002048408212f40eb50130096040902f0452f2003081440012c6a829012a01e08881296f3402029009488802767297212008c4488026ff550213009e448902554984800801218000252dee1012b00508081241e61e20030894480122a679e8102096140011d04a76210a004480011ce00c7010a044080211995f7e200304140021181aa69212b00548081173888220210c1440a0161ae3a01320160009114c261e810004c1082014bf45481020cc1482112ac686800204010021124a265010a04c0882112165278028000180800f206938028012180800dc518421200cc448a00b6dcaa810000c108000971d97210204c4082107ede8e80080401802007bd59d21020444002105f3a9220090094880001aedf30028048088a0), (96, 77, 2, 23, 2, 25, 0xb0d7fb0900904d22408d84ff5dc840423512002b6d5d8c0224118090235b40b53000b04108021ad1d0d090880462240855b1ec76048823052206a8a1be040640248012351bf9ef20210c9448a0a8a604b00980420204854434e100084324122829ee871c4014034910034f1883b212804c488a0a6b8d2f00148008404051900da4000c104000868bdc82d00041242800345ce94d0021049008a0a2df932809502204050d16d380c800824910006896e84a401401091003428bbfb810801618000a10817b0004024044104f7ad4ec8408059000067b6a414024210a081013b857e4200009a448009d6f24b1004820a40104e703a5a002006862002718575240640108112337d2aa181200c4140a09b2a1c18098002000484bf0c68e000032052082572722c422003c8102128bb0eb211001640010912c44c1094802a4040460ca93a0088300502862d7aad2404200280101152967b013200c0089184b3a031011840a2040c23c4e2800ac104202860a6df1100440802014305262a7010304500021820a82400908468244040e4d414044805800045fd9a45e402003481020fd641d32000092440007e1f18d0014820840503ecb1bd800a002022201f05bd75000400020002f80367b212a004480817bc19329004800a40003d4e03e4804822112045e5dff1c420219a89040f14891220320884489176aaa021000044224003b113c82008030050281d3ddeee424409881142e9e769b81220cc148a173fbb2510080442240839f0a77a04a005860201cdfca58026413c09122e5444d42010012400106f2076a1014020240503718e588840c21510005b73e5b4420011889000da26aaf210a01e488016bd1545008500b04000b5abdd38840031110081aafa852026400800122d37e452210b0054800169b9084809000f00440344337060088200502059f27ca4400402480002ce8b8bd20100084081065cca3a008400b04000321b46ee0080200502018d8796a400618288042c2bd0872112084440115fcc25c108106222010af86a8460408010400057879b64020403c01002bab878b203201a408915c95bca108900b20008ae40e9be00a81206228570d0290021001811000b74802b8122016100815b47707808104b02000ace8a6488424015200016367988402412488022ad59dfd010900d0880056824de8098006004482b28c82480c02691224154cd800025002c10100a9d79d3210009e44800545c1c0908900620408aa0830d204a80786220546bd9f4401400090002a35d55f200b00148001), (96, 78, 2, 23, 2, 25, 0x911ab3bc808826912206402e06b010801e088008fef28c804a0110202823d472912110084440108f1a8cf484c0079022423be2e1020200c8448a08ed7f7a084c02311224237581b30108044080208b3cc5800428078220062aac59301010c5040208aa02d0c0408310100862a50816200a048488218a6428448400259100022625a878002012100018964348c80081010008620aee33210004c4082085f770b484082111000615d36f02022088448818513b55204082105000610c68e221080164800082484c58800c12502086070fb5d210b00d48801811eb23c80a806922206047621e2000048408208098382884082791200600d9f432020088448807f73cd2004c005800241f81cd9820220c0440a17d8c2a90840823112005f40a7cd012a016080817ced4ec6000822052005f146242010308d048017b6f30e080c024910241eae4ed22112096440117ab7df1e048827852205ead65b52132016400917aacef74048811000285eab09792130096440907a9bd82e040805840005e91ace92021041400a079e4d15484ac03522205e3c3b0e212108d44880781d1808048c21410205def194981000c41402077ae9e40840021110001dda613401280040808076e2193484a005920201d85098c010104d008207601a940048827812205d48a2e9002a048088a17521967c04a003022201cfbb80d210a04c4882173bcbba0042411420081cec336c200209a4480173a8ab1e000812042085ca5fe36810801e188007277a31c848003102201c9bb866012104d008a07269254484a411520281c89586f200a012480016f9964e0808422512201bb969ec800001a108006d87e370800c02502005af4f4338000008108006b977b52008824850205ace2890210200c408016a060950002412422081a5eef96201201a40811686f549c0408110000859ff0d66210100d4080067b2d5a880a0021222019dd4a6520000c84482067157e6604a0030622019c2ec0520090494882067085990800c325120859384a4c203209a4489164d2bad48004325120818e85d4c0029049088a06281f1f484c001100241896b54d000904108020619b9a4084a813122285842858c00030490082160eca56404843341228180aea6a802a012180815fa6ad440408058000057df5619812200c108815f20b76c840c015000057a89c6c010b045080215cc2a82c84003311208172b565c0101045000205c660f4c04a4114202816f2a3322130016400905a82e33880200692200163d0724210a016480015895b1a0048431410281624daa5200200840801), (96, 78, 2, 23, 2, 25, 0xdd28bb6884a007922203707ed3c212100540080db9320fa0408130420876b07a5a01020cc04821d9ca683a04880784220762b365c210304540021d87e626404a0130222835f4d27c810001610000d72947720028068620075ada5e120220c8448a1d3cc074a0488110402874b1e19281020c414021d2791b44002806822007490c78180220c8148a1d1ecdf1e04281106008745e1101010b04d08821d09be86c0484114002834197757810800418000cee149d8844027912043385fc35212800448080cda5721e04802305220335d41ec802a00818881c9f23f4004480780204723f8d7b00010c104020c6761c34800c00500007194ba47200804048020c4cb6a2c002c02422007118ea7a200104940820c3e4c166042807862006fe948fd812209614081bed09728048031010282f72a03b012b00d08881bdc09f2c848027912202e91ab28002a040080a1b9a29ecc808402502202de554b9812001610080b779af06040823052006ddc2ae8012b04d088a1b6bc954800a806822206da02ebd202800048080b5e472d084a403522202d59a78e010804c08820b512c870802c02522006cdc2d22210001640000b1ca5840008c10400286c4aeb45202a00048081b032c968048805800206bd31d09212300540081af390a86042803062006bacdd45213208c44891ae4a827e048013042282b7d71fe212100d40880addefda0840c03502006b6cca40800200810801ada4bcec802c12522086b4d07d1013208c04891acd56ee4048c01400206b2ec6cf202308944881aac48cfa008000040202a3c87032128044480a0a7f695b004a4034222029f6d514202300940881a7d108dc04a4014202029d70564210108544000a3ec0a3880c0069022428eac89e210800c48800a37f92848424035220028b918b3812001e10880a2b7a24c84083311208689f66a6810201e10801a1b98c8080201212208286dd129212001640080a145f58604881304228684d88ea0023049008a1a0a0fce40408130020867f07a9e8022012100819f54604e008800040206796e687010208c048019dffafac04ac1142028676b0cd3810200c108019c7352da0480278522026a150bd002a0000808199bd1c4480a412522282666da0e802009214080998e28ec8400079020025f875e28120084140809705fc9c84a4135222825bfd21b21210cd448a0965351c400ac004202065723f25812a0041808195bca38404480300204656bbf55210104d408209423f9d48404315100824defe4000210c1040a091fcfc6004801100028246fc2a7212800c48880), (96, 79, 2, 23, 2, 25, 0xae50694a40440108110359808754808012102282ae9bc2a101102420450d547c42f002a00808881a9fb5acb00001102900151c73efa0020020620029ed12c180140200405053914748810804418020a5e7ee664240088801414622b0048424115200828b5c1c49081846a2400d10cd9c221220cc448a1a106c6020200088000414207a80004c0078022427f0b23d1090862a20504f0b07a8000801a088009d9239b700140003000339a99c5e04003305208272a80a19090826a04504e276027200a0404802199f95012024403c01103338c9f6c84a805920206635dde01090822a00504b296ad70122084040819633ab4d0050034311012c301d14048c1340228656ed5d7008184282000caa67ef2802009a1488093a4b99102540883014326fe87420400078420024b78289001186082050c8d66474012904d088a09119d519005008030141219123e8042c0142000640e5752108502224010c7e4640501000c4040208fbf2e1f0250088301411f62a0a88088249102063e97bae008580684400c7c293cc812000c108808ee6a29a4210098910411d7d3c1880841250228238a8065009904202048c6f2c8c78122004100818d62193a024201a011011a7d1388840011100082341a8e70090026004504664db0a8100096140008c9847da40560129110318825a860008068420062f75bfd008904f02408c5cffdd50029009088808b83325200560921114316316578040c3141008627840e3908904f22408c4accd11810a0041800186354c900244098011430c02ec2c80c824910246156fcfa400004d0a400427b58fd010904d0882083fc96a3004008020141074867ec000c224120060e2cd18109100b20040c1b9c9640123045000a182a5144b024008820141033c852880802691220205f2fa910840222401040b2af31212300d40881801263e2404210288100fdbccbce008004840201f62ee639000820a00103eade8db80020c8148217bec9544001600210002f6ed7c5e008022052201e6d6820101100d20440bcd17cf9010a00c088017937a76d001408030042f16d8cf2042003062001e0d963e4000024084103bc34ca6210100540000775e3868405208290140eeb3521e002812062085d52389a101500424440ba8e5491802a040180a174c1cba4024011809100e8a46d2c808804900205cfc9174009180680440b9784dbd00030c904821721edf38400218288040e183c85c048027812201c2fa15c1015800a4040b85a14d101200960408070ac4732404618288142e1479d68000432412081be2cee5108800220008375050bf012a00c08881), (96, 81, 2, 23, 2, 25, 0x964201099095826a4450c98769028048c334122862716401a00140901104312a3f3dc002308904881847c41901091826a0450bca70e61484c807902245db7528fa424619a89142dfb6e9e7812a04c188a16b8c131f1095822a4050b560e036880ac12522285a69f1382024611a09102cd1276ed810009e1480064897ffc9015820a4050af0bbc68084c80310224572628110426413c89122b15534b52023049408a157cb11b5809186282050aadd5c464008c32412285526113d5024019829140a69a9c1d212200c4088151c0b89a909104f22440a8a1638920488210502053fe8a0e04054080901429d81122c2122084440814e65bfba408104f0a400a652c7d68842413522081315572d70040034211009682cd1c212201e408814b40369f808186682410a5864dfda04a8030622052541732f02100983104091a1ab0d212a01e4888147c45bef001580484440a3da516fe0488310502851db4566e420609a8104287e50c2f802a01a1888142f066ef1085826a4410a1315660600882685220507091cb8424618a88142830e2d8a212004c408a0415dd4f2401100d08440a09d5464480a8121222850369873c4046192891427b92989b2120084440803d7d2e8240940260c4501eb1efd5c802004920000f50f0aa0424012c881007a8253e7202001a408803cec1eeb0080066024101e6ab14a6000820050004f2f7fe9a020413c090027852df07210b045480213a6f6d768011840820409d0fce98804a813022284e82d8ae5004411029102728975dc21030cd44821389b15951011820a00509be5a198a008812042284df1aab210214098310426ecbb835013009e04890372c09081091846a24409b3c1ed4c048033012280d5ee1a0f025003c311006aaa97e1212308544081354fb541109000f204401a7457b82040023052000d19dc8da42000188100067ceb0d8012801e0888033c7790890110202005099d5e3004848825910204cadf29c700440102110264f3ba26212a00c488813210bb8a90950222405098b41f690048823012204c3ec8b1700400902114061a539392123045400a130bb0e791011800a004098277bf2080a012122280c0ce0f40426412c881225ede1cc401220c4040a12f3d349f40040240c410178a389c484c821110244bb02cf020050034111005cdcaa0b0021041000a02e4087798091066024509715c81cc848031110280b7046950020219a090405b09daaf21220c4440a12d6858b940100040844016a2ec1fc040013002080b44f8c244016082900425a1bcc46000b049088212cb0b94890100492204016293b5a4842007922000b0374d88405402490102578f7109000104900820)],
  [(96, 80, 3, 26, 3, 26, 0xcd4d82a900882440b201ca8ab13200a044082a10ca6a88d8002844008a11c7b964c900a04440aa10c54ea0f8202a40808c11c051ca72008a44082611bc3175b8001804008281b876c938203044808a90b86ce03000b800002881b7b36862208840882011b79852f2201804880281aee0c15900a00440aa00ae9dd2c800802400b200a64d6292009024083280a4a142e820981080a0a1a12ac9b22028408808119d3e19722010408800909c7124d20082900824249c6a9c622018448802919b9439690008444082119a341f92002244080e109a19334000201000082094935eb8002a40008c11939cb469000824409201932f6e9000b8400028918fd33852003044080a9089fec988000090008024885ea69800b04400aa9086cf4bd100a81040282184b233d220100488028083d0d4a80030900088a483240182000a10080421815308b2203084880a8480e9d15800804400a2107f220bb800882400b2017d067b22000a440806117c3314e220b8408828917ae604e20028400808117954fbe000b044002a90785fe52220980488228177df4c3800902400b28074b59c920090840822847480f598000a4400861172372f610028404008116ee5e1920010840802846d950e38202084808a0468f76b380010900080a4689774e8000a0400860165c2d1b220900488228064a5e54800824400a61061241e9220904488229060f5bfa2000a400804116080f2782008448082115fbd6bc2002a10080c215adaa698200a048086015a7e1258002084008a0457d15d120090900820a453d56f50003044000a90534e2d1802909200a0a44e44173820b00480aa804d2f5c98208a0480a6014b31202800980400a28149f7d63800828400a60449c8cbb9000804408201420888720018440802913f63a67820184480829139b2cda820984480a291351023a2000a040806013077adc0003084000a842fd0f0022010848802842b9b45a800904400a2902a1e7d6000984400229123623622002a40080c112211278800b80400aa8121f6f6420038400808911f15f3622010448802901b91b01802984600a29118bbab69002844408a1118b8bd9900a09040a82417cf5799000090408024165a70c200809008202415885fd820828480a604153f7d290000304090201381cf300038400008910d990f022018408800910cc8b13200904408229009c876e800029000842408d3a22802b80600aa8108c695020008440802110806acd9002804408a01053c8c92003084080a84049056c000908400228404385852203004880a8001c6d802209040882090018d2c8220b8008828810016d2b80210920080a4), (96, 81, 3, 26, 3, 26, 0xd50edf941001484042126a27eadc8824212208a1350dab950007008011503a73500b220b804882a81d385bdb8000c02000140e6d5b76e080284202108734e546b001210801450997228bb800b00400aa80c80bbbac800418204810e3dac18208029120218471ce0ad104154010158038d048ca820884480a211c54f4b04800420204008e2a78bc600228100298070c2c31800170880055238220e99800a08400aa04bf1d8fbc000402004100df7b0e4a002824002a092f9556770410409014c017bb4f33000a840002811bd066d59005c22041548dd5df8e4800e010202a06e7918164017000105103738d1438203804808a81b92685f8805400201400dc4b3bde00a6018028a06e22dac4440708110112369e042a9002084408a04b3ebee30000c22000148d9be8fec802a81020b806c69cc650004508011c095bcfdff820b04480aa90ab764ba400184200454255684166080a802023006a6c6c0504144210158414f59b158202284808e04a6b95b3c10010840421052dd75e48020a0020901292f09530000508010c094292aaf2003004080a80a123bf941041484052124fe8c0520086018020a067dfbef70001088010423377d361900808440a2049a7f7f3c8040222051084c6ab056082280202900661716c100130480165032efd5a922030108808a095a624c4004c22005148c9f80b5c802881020b8024cd4b2320100488164012039a28820a81080a8218e6e0bd910084844005246cf3526080c212022a1234f8b9e4014488105c2117ed8eb90000844082048be8a558801400200400c4418e9a080824202209221031f244010811000230e686538000a000084018687f279004422041108c31c900608060020202060dc03cf000104801240305ae4912002044080a107f8b3344000c12004940bf79b602402a04102a085fa64fbf0406021011140fcea83e802b84600aa917e29ef9c101408404410beab69d0882c01220aa01f1dd4e90410489014c20f4fe536800a04400aa107a5d2c84100500404200bc70ae9a008c248022291dc47dac0009408000c12ed29d2b200b004082a80763edc30801408200410bac8c788800a110202845ce697c30404489011c20e72f50f22090908820a4732793e4000c22004148b980b9de0008240022091cacbb470002108010508e3bfb94800900400a280712b59010008120409403820837c8824042208281bf939f80013008004502dcad068820a80480aa016d7565cc805402205500b68be6188826002208205b3932550015408015c02d4d4cb1900880440a20169cd0fc480104820441234bb42808804202200211a4e8fe24007088101522cf74d55200b840082891), (96, 82, 3, 26, 3, 26, 0xb20a14348004110200a42c416e1c820804480a210b0a276920800a12021812bd032992008a10082421ade10e4a082a10202a046b5d787d2008a40082411ad5c139c002e01000aa06b4a14619000024409200acefd2b4880e002202206b3359f49000004408200ac9dee5e400a041022086b1a3b2682038108088a1ac035bbe4082049020086af933cf9002840408811abaf54e0802a80020b006ad9eaf920098100820a1ab5d5670002c21000aa12ab7719a820b80480aa81a8fb1c20000e010002a06a28ebab9002004408a00a88bee7a0008a400230929f6d6ac2001804080281a7391dc6082a11202a8469b37a2f8002204008e00a3f43aca0804212020a128a1f867800884400a211a0d7d94e000a81002380682f5b8d900881040a021a03968ea080a8120238067dd3dd0900800440a2009efb84748006090204a0674393ca20080440822109c66ccf0800c2002022126d9658d82028408088119a0a9c8a00000900248026384bd48202844808a1198a040888004010200a025dd3f8e800a84400aa11973de8b8002c01000aa025cc58ab2008a0408260196a78c920804042020282577a721900803040b02095bae6320802042020086552e4ba80002040086009503eefa000290002104651a826620010900800a4944b1a408024010208a02504d34f820aa4080ac11934c9c64800e0402022864a77099820904480a2909298d0f0880e012202a0649cf9a2820384080889192643452000c110022a42474dc15820184080809191abd728882610220824644dcfe98003004008a808d41ce7400328100098263308a99820909080a0a48a522d4e4020241028092281fc07820809080a024899ae762000a80002300623a3909200824408261088222924000e110002a462012b628003844008a9187bc9e38880c112202a421caa51382038008088818717518200089100238420e12f2690008104080218317222a080a842023085ff2e7648203004808a807e81a1b2002c24002a291f8c04c1820880480a2017bbc8fa8800a810203805e9bc02a22098108820a17937a326000e100022245e28a9148000a100084217818f2c2082c24202a291dfda2768023846008a9177c9789a0822842029085dbfb5e7800008400820476364498802c11020aa41d655aa182018108080a175515c260800242020091d3d77168202210808c20720137e60086118020a45c6193bf800829000a4247168df808806002200205c42f11f22010108800a0709149ac880e112202a45c0419d920010800800846fe0330a000a100022045bf51e7a20080840822046f203a920802012020805bae22e720082840826046d5ee04a0806012020a05b14b8718200a40808411), (96, 83, 3, 26, 3, 26, 0xa21a559100430040101034263380e0004110020a427e1b32bc104420405008cf78e929900a84440aa119ec3997044121011041093a6d230a008c018022a026e75a50c005408005410cdc16e4c220b04088289099d365de40030601021433030ba28802e01020aa065cf611c4004402005100ca3038b38202290808c2493ca5b56441508110502324c24b3e008604802028647d9ca11004c18041850c8fb0a03802100600828090532c8d00101080144091f09af8e002c21002aa123b622a7110180044044046efc6af220b0808828848c59c2e90004008011401135d4dba002291002984623625c89105822441548441d9f9f82010048082808736535b04070890115230d35ef30802609020ca0615d9bf0c01584900545242aaad85200b084082a84834cac99201508081502300e8304a000a9100238460028b881000c08040050bfd71062200a8400828117e0e35692011060816042fc161d224082009020005f68072f9104c22441148be11dcbf900a80040a8017b7ce6b04013088104522f274f8ec002c24000a291e3bdcacc1041084052103b70a4189002044408a10767c8ffe4006120101148ece963120082108020045d9757d191018204404483b28e9dd820980480a281753f65f90404409011c00e93937c64000111020841cf8ab7c1101848440452394a16ca820a24480ae1071338119004210c010508e23ac4ae40aa04902a085c3cb20ec814401205000b85f6497820004480821070b6704e4416001105100df3dd1f6080c242022291be015b7410504840541237411c41200a844082a116e23783f0405009011402d99e3ad60800812021801b0c8b544814409205010b5c951f3820908480a2846b1419870004088011420d5c3de4e000a840023085a8b2d54910480044104035129748900280040880169f66d0d0014408015c00d17d84620800912021841a079b06c01182300454833d4a6ee820aa0480ae016690062a4005488101c22cb295eaa0020240028091939853e9005520041608b2479f05200a290082c2464221ba30414089015420c709a7e488060422002858d58bbfc805042205502317f9108820900480a28062c330104015420105842c454c47a008e04802228584d262e4100848404052308acdad8023806008a8160d2fa344007000101102c12aaa38402a10100a0458162f23c0008120049402ff35cec80010040082805e4eacd64406101101108badb9328880e0422022856d5d129c0001220043082da0985b800909000a0a45b3b2b870415421015842b611bd6a00208100298016b995724104c00405040ad2ddf708202044808a105a0c5f570412021014140b33df6ca408a0490220856552ffe1004500041200ac90ccd48200840808011), (80, 85, 3, 26, 3, 26, 0x88e1bf8ec015c21005448ba67f5ede00ae04802a285cab142710057004015102d1525530220b0108828a05de079c84014c21005048adb0c49e2082a91202b8456d14a4ed005610c015508ad1cb0b6800b84000a891514c99ed4015421005408a81ee35ba0828a1202b8113e4ca644401450010580895f57a79800b80000a8814a32831d9105c08441450a4da962a2002e04002a2852066346b00510840140228eca25d9820b84080a89147609418c004520005208a2c949378802e04020a28510b3e0df0014508015c0885f289a2820a29080ac2442200b8cc815421205408a0b9dce7608229120298450407c4fd0053024014142809137f2220b084882a843fbd271c10041020413001f65da79a0826102028244f9de1f730405489011c227c410ca6802b04600aa903e131b18c014c010050409eca29a72082c04202a280f589f7e400100200040407a678948820b84480aa913cc52ef190050400414021e27a634a408a109022044f121d55f005208c014520776d7854800aa4000ac113b0f3a5d10055220417089d4600faa40a2109028044e2064c4704170210151426f7debf3200a284082e04360a048310050480414121ac025e88802821020a810d3deb4ae0017020005142697955648208a4080a41133252682c1051024057001980ab524882c24220a290c8d67131001542001584262c3eb42200b0900828a430fe4725c011843004542183d94a4e00ac01802aa00c108b93b005210c0145086041570e8021046008290300f517bc00450800521097b7e963a0022800029004bd856d9f00150800150225e9b51e380228420088112f2e7f994105842405542177f84c6c8026010208a04bb579f1b00150080154025d5b00fc802900600a2802ea409b5c010c21004048971e323b6408a009022004b6f52c9f0015488015c225ad75f18200b0800828842c7cad744011c210044489614afa9a002a00002a004aee5601b0014488015c20573dfc24220b844882a912b8323a44105c0040544095bd01d3a4022111028844ac7f6cdf001540001580255a1713d900884040a0112ab8481f9004840041042153804f5e008e008022204a86324f1205500481500253ae2a1c8002804008a0129c449ecc81042120400894e011076002e11002aa44a4aaac05040208901052051f690ef800a29000ac24)],
  [(96, 75, 2, 25, 7, 22, 0xbf98e0fc08144848c037cb3eb7000201080002f57fd8b01051212104dce0977002002000208b5c697ec091488488276abd744092284081046b6ff20e0304121030456a2183204884024412aaf8be7c0c040808813535993080029009000e9a29a651040080200853391bc824425008403a4ee2bc80110484042146aaeb481220809184287bb23f02450212208ce336bec040a04204018b7cb8480c144840c1312da5b680028009000624f853000441010108442fd0d0028020002188772d9d808104840c010e4c44781201101104a1857bfd12412802209c2cd668e040224046018553a5e804840810013049b17d012281081046001c63302412202209bf7cb5a8204810280007e4d232c08108848804fc04cfe08a204080061f2c9ece024012003083e266530248850204127ace944c0c044808c12f1a064981009101100de0d775c132408142043b735fce0001240424075dd8fac05140848032e7373ce810208091801cd2109c03041010304390cda6c008224002117180962c05044808432dfd8039012211081049b689a5101050012004b59739f6048824246106a5c9bc048102040800d2258ed8182890918259e967d002451010308b2fff14a048a40244136587706c0c000808810c6a01f00912040a100174afb5200210204000ad199b2a008820242105904644c09108848824b175f270100110010095e41f0f00051212100ab80d2fa0202200420956cf34ac09004808c20ac9b9570110010210014b89fd300450212008a8e6962c048a242061147662abc0110484842089399d2808040010121118493302411202308a10fb6ea20005004002411982a8090088008247e14d03810011011008f71f560104108000089e96f228240250004033c516ce00c0000008107493e030192810a1024e826d3b0340020220c1ab92734024124082482d7f01204c802010810592d993000049000900aeea2c70041120210893d3a96c0680240061825ca6de4400020080004618f7401900802182088ebf601020a80402110991a0a2200100400820c0c978041048404103e6907c00a0880008646121952000112001008bf9ab24008a042001113f00e0809044800c22244122e8180080118203c3254a00051210100874e2228068220006190b51f96440102048000137a97b81a08901186422eaaaa0204221020103fd1ec82088102001006e16028050448004320ce072408009400000c139cdf20220220420100d9741826821000419), (96, 76, 2, 25, 7, 22, 0xc0e3cd9a20885024012bfb00d6224001004400beafdf7604880424410bd5b1f2c00484428002bd3b770820405008002bbe7205c00410408040b977d6ce060a0424409b7f44f9a22801004018b584341c060a0420409b553960a06022004609b499dbfa02882024218b3f5266202822004219b0e4a898068a2020619ad205b8024881020410ac8fa000068a0020419aadf974e04800404410a939e61e040a4424403a802d81020411008040a7d5375c008a2420211a3c5df0406022400609a2b6b34c00412408240a1bd9a7824825000413a088b94c028804200189ff8b098024a20282099e9f37e8240850204029e8d1670240a50204039e513250268810204189dd25024048244004139b5fa74e0000240420099542ff40688242061897b17d84068204004199488b54020401008000938e33b4044a44284039380121822411008048925b88360002240420191c41d9c044024086009146628c060204004098ed91abe048204044118e4d22ec044244084038d4526a4064824286088c8f0c22260810244088c40f098240010004008c1533b0068200004198b15fc1826001000408898754b2000a2024201887b19de068024046188788a0a804884020412873b100c06800400418872752ea2408502440281b12ee8060a0020409806cd4c4040804204007eec3b62020a20242097e3d767c048824206107ce7b248044820286007b199d40248050004127b0692ba208250040137a1843580600200060879abc634068804204187913de9e0688042441878c61b9e06080424408780d09920402200460177ea6b520200200420877dfaf40000a40200037790969226001004408770c87502200100000876f141e60600240460876d8a18c0040440800276822c780480200061075d9c68c068a042041975932aa8024200080097582f5ba2408102440072a8ee7c048a4420413720fa078208050000126f99e2ae068204044196e6865f0204a50280036c410fe0068000004186b8bdba0020a00200096b3c1788248210004116b1ea904000144000426ae60d54040004004006a5a19440042240820169b8dbae020224042096926b5bc0482040041167d145fc020a242020967b52e3a20025004003679babb0008a402001366f4df640448442840266e737340402440040366e0b64e0200240420865e736c40442040840165d55810024100080486542b0d404422408601644db9b22680100441862d8ff702440500840261d7714a2008502400261b8982c004a0428001), (96, 77, 2, 25, 7, 22, 0x9eab0714010410101044ef0aa7d80021109000a751400a04500200003139852ea4000a04200019c9331390145101210ccde8e96800a2080808626c03e43c08104848c01344750e80440200860099f21fae02052210201cc847cd60112800a10066299cce008844010c032d6a0a7024485028402963d9eba030402102044b1bc1aa0082000800224d3b24e80c004800c1124d71e7c028824202189214beec11050810004c90a25f10112090a18024076dfa8040248004911d1d3070220110000488e8432bd0140100210c4721e85c09820408102235ea1124490420088231a30c354068224006198d0c629c10050810000c671436b0000410001023135e4e80900080082118475e7c048804204108c0724c000252014001c5f32f3f0112010a10022b468f804d00200083114eb60a2240050044028a27be7110010802000c49a7f560192000a10222050b8a8051448404330dd36c8220881024010846b8fb112050812200c22eb9a601820008102210cd04940814004880307b34f52248a502441382b47513004422120093fe2cbdd800041010101fd6bf8044100a008024fe970758024120082487eac3a700145001000cbf3d1651008089000825f90235880c840810812fc76c158048a00204117ddeac78022400142003e9b698c008048000921f2a1bb0800944850402f7c47974040224006017bca12e4032410143043d66dcce091084021005e9f7aa3449002008820f2c1d2b4028024002187937c36c102428140013c68db2c0012100a0009dd8de45c0c104848c10ebe921c2220a102400974ba2a341345081020cb9f33600892014011049cdcbc50001144040422e65fb47222011004048722fa3850244001220839117f3201a200081061c86bdde045142040032e30b31fa208210040116f46592e002002040003799774100229108004db3c8dbc008104040c00d946b660008a00200116c503a7602250214200b61eaab70012910a000db08f8db804020800090d820cf96068a04244196b208b8a03211204304b5725c78800210090009a970292401100048020d3a9e11e048a242461169d044cc0204201020134b694f2890084011005a58dd86c04104848410d0b502502440100840067bfb4cd12012802201b38564b00082880808259b0ed8e44002a008084cd59ef18040a002040164e7221b0344121230c322c18da0092800a00258ebf90d04800a000804c63986640648042840862b2dd8c01211004104b1512b2009229408104d8984340c05004808430c34e9f7c000a4420003), (96, 78, 2, 25, 7, 22, 0x8aefed320080880008262b5a2180024020082088a5f935c08005400010a252cfd82068a20246198946ff8d01900102102224fe4c24004024082008865a12e89221409104a1d2ed832060a002440986a1bf1181a289091866149e290a06800004418849b759080a20009006211981bd22282100401983eef89a80221009004a0c2c92fa0208202420881f083b881820809182206b79180224010080087fd096eb008281080025fbf2ea5a048a20246117eb2ec5280a280090065f97d4c86040a04244017df6d8a889a284091065f18690ba260a10244097bea5498810008011801ed7e5b4a208a10240117a86501a090284081005e688cb5826021000409798ee314081084020005e61c6e380642200860978673d7b00109102000de06fb72e000a04240017801ee42818200091021db645920064a0028409756e2fea800048010901d3ecb162228a10240197396e0e7810081011005cc170ffc06402408608717a6e05802289090845c37bb81c020024002087027ab9780229109004dbf537e8a008a20242116fa4b398880284090005bc155c1e020804240086eec31f4808048010921bae15a60068820206186dc1b3b5808281090025b472f16c024104080486c3c1020808200090021b066e086020104040486bfa1fe8010288081805ab22c4ea200110040406a5cb550012208081841a5f6e90802480028008690a1c71008201080021a1f36a4c0240040800867232c5e0112100a10099af7978a248a10244116672de500112900a100d99b817ba040a202460165b7e13c08001400000995cc20640080240021064b9e8cd80029109000d8a60eb50028a2020219621d961689a084011065836a39e0024820282086053970009008400100581117a4e028804240186022d514012200081041783bf688204a10280015d5f41d208109402000d745a090e000144040425ce257300190000210216f97109e000804240005a968e8489029409100d67b78224024224082095926d18089220409104162f16a1c00414408042580c20df0090090208215e8e474020825000013574ab0d201a0080018615c1fdccc0400240060056c884b40990840210255ab4ec9a2288102401856a121168880840100255813c8d80482200061155694fe301028908180553efa8be0400040440054f7c43301a28908186553337aa0260a102040954c30f4c8102100910094d6fa6d806020000409532a953b8102010910014b216df8048a40204135134d6cd00a281080065428d28b02008502000250728a110100810010053e29f062008a0024011), (64, 79, 2, 25, 7, 22, 0xddaa1ed54010440084238190096e08229408004eff9cf45d03010002204cd1584a02208a50240138f84e4e1804944850413192b10a688029409000e26d41097010092021244473fbba4024a042800981be7e85045042000033009ad4b2019080021025ef195a1c124008002083c58365fa068220046197841bf74409044008c22e3f38ff6089084020025c6c5ae8803251014304b72899b90008220002116b6a3eb840d004008c30d48634f10112890a1805a2e3cfe412252814201b44f1de5c008844200126861816340d104048c30d060d9298100090118019d5887f90341000220cb3994671200022004201663db21340d140048832c9e04ed481a20009106188ef3b8700440212008303ee25de028a24242195fd39f69804900850010bb7986270192890a182575391d69030000022042de4dcb78044a20286015a2bab2c044042000012b439312281029009100d65c0f7c5110408120042c6921bb2060a20246095802cd7c00c044000c12adbe07360100880018055670a20811250814004aa76ef2ae0080240421054a2e00380c000800810a87af2dd00021108000950242bda0004121010029560c694004804280005277cdad44d102048830a345188c0912840a1005421429dc0144001000c28364bba0208a10200114f7ddc5504c9420508129d705ebc01029008100d356353a01124081400425cc9ca28220810200084ae6de7f40114804802695abd6258002090908012acd30b30144121210c24dbe927400880420010498221b044c04200881290e5566d0092090a082121ac9ade0024121410023ea9eba0200a502000347b5fdc300c144040c128f0ef79c08221408004917c98f8102450012208a2c9d043a04802004610)],
  [(96, 81, 2, 27, 2, 27, 0xf524c47010080500094078e3ffb200000a0004413a52992e4400054083109c33e2b62200022000884de79c579002004220c406dc5a0f88025090002a173cf2dd100080108022019b13e9b0004424440084cac4d989006014220c02e35cb52c00010b01042130cd3ca24418004881003827fcf62201022000a84bfde8cb11028112005425be70e248030021106006d5df9b6041204408050b59b27660008821000085a8d08538000814020942518f285c80000801022128c73698400204000140944163cc80088210001059d7e2ed1100815000d424b9eea1800140a1004a124bac56e040804488010922cc7452005008441a008dcbad31006800200540c4ebbbf880050b0006a11fb30fda4008010883000ed5b39d220800204080174c7bc31000010000442383b80280830089000215bce84ae001204008050abfb840f200042c0418845b97c3f9000404820c402bf4578480140811028115f35d76041804488010a9b50834200c0204008054c6bef59004010020442a3a9c68c0014081100a11089dca0401204000140a7b776a5220902a041a05383a1ef11048110005429b9af1a40820088100014da19c52401a010883402670561b220c02a4418852fe65eb9104015020c4294c942848010081102010958c206440801488310049eedb7020802204008524667fb1000212000442105bed44880002810600081ac6d480120110025023c6f639220002a0418041dd9ef710028102005420eeccde8002109000021468bbcbe04000140821003250fcf000c0204400851451f9491000110204020a0d0df488040881028104c5ef5604020440805082461a7e20008210008840ec5826900401002040287629d140014081100810364a6fc041004400010a1b0b08d20008290418040c2ebc89000014020c020413963808100890002101f6c1f240020400814080ed1fff220000a041880058862a800281422090202aef052002008000041415517ca40000400810080854989000082904100403f2e54900041082040201bdd69880340a1006a140d2fecc000a04080050805cdb042001028001a0402d2a5f80002120200420167ae2c00000801002100af7b9c0402044000508057a977020002204008402bb55101000110000420153c67880200a00062140833ecc801004100010a03fd0ab000082104008401c7ba3900421202044280d92a980814089000a1005a8d19000004000020802b6c8d0001020040204015aeca800041082000200ac798200100810004100561939001804080020a029590a000082100008400ad6eb20000104000420043eb290004082000a1001c4cec00020400005080001a244008020800005), (96, 83, 2, 27, 2, 27, 0x9dc3883e44120040815033b521fec8034021106a06762d1f91000216000c424d030086020102a001284996737ee0002858082509312bd6b888200a80062165e764750104015000842ca733aae000902000028594e082b4801204100050b2608b45480340011028064a9413b91000110204424950577a2001028001a84927a5a96000a010882501217fa14c00210b01042163e1cff89000404820c0047ad3643200140c041a808f22b0be040a0548825091c70b034002008010001637a7e3a9004404820c00c6d2c03620000280018848b777c74001284800050b16aac9cc8830089102216233bc6f1006004200c40c3fbbb9b2201022040a848703453640000500831090b986044802200410200616c248d9002a12220542423186ea200080900188082ef23d8401a00080140305009bbc80020a4106212076a8198006810220142c082f11f200042404088481028d54401084800110b0106ecd808100a9004211f51440f81008150209423e6a559f220d426440a857bfdd2890008050802208f765a7340034081100815ee0515f0006814200942bdafa45d22080220408057a7c1d124002010083400f1ea33cc8830029106205d6fb1671004410800442ba519917200442444088474820004441004400110ae6177d8c00340a1104a15c579ffd1006010200442b8910f03200540c441a807115996e0408054882108e1e9f00480340a1106815b9daf2f8004404820840b6202e93220940e041a81676db68e441a014883502cc290a8800040a0004a1197ae2219104207020c40b17f65362005028401a84628057da441a04488140ac12f34ac00110b110421181f1cf9900041082044230125f9f02090020402815e5910ae400a010883500b92e7d3880100810022116fd9ce08006814220902ac88c5d2220402240088458fff038801204100040ab018a1348830089102015600025c9004014020c02ab585401200c02044080553c4248a401205008340aa2f1fd4c883109910221545be4b98006212220042a86c0d47200402844188450b90434041a04480050aa07f15dc08200a8104215407bf1c9004804020d00a7c8abeb020002a0410844f764b12001204008040a9b45dd94082408810081536223851000414800c42263f9488800c0084011014bb4b5ee040a044880508958a758c00220841002152a7fdc89004810020502a5241b8a00008290010844898ac1c801005100210a8d22015080240a00068151897a359004206020c40a2d4c896020902200028542f2fe564002040081508819cf8fc00140a1104a1100d00a48004014020802a00c1b5a20088290018853ffadc32001205008240a7e13630c0005090100a10fbd259680008140209021eff48df0001020040284), (96, 84, 2, 27, 2, 27, 0x97bb3977020900a041281974554232005028441a8496851ab32001424040a84965ec00b200c00844188193e580de220000a001880933c6efb200940c041a81930eb8fd2209002040a0192dff5bf200080104088092c53ac6400102880128492043cf12209022040a0591acab6500008090410008fc43a9d20040284418048e0ade83220d002440a818c08cd7f22040224408848be3690a020c02a4010858a69c980200d020400a058994c743220900a041a818924c4f3200c0284418858793791f2008809041881871932ce200d424400a8586c57e2a200c4244008858600c21b020100a041280832791b6200842c0018857feda1f700084240400857ecfcaa320080080418817e0402c3000940c0412817ce650322005000400a807a39828f200c0204408857a0e7507000c42c44108579f2baab200142c041a84799492bf000942c04128579048202200400840188078dc7ccb020842604008576a96ffb220402a4418847692ec6d000882104000575728d6e2209002000a8174d7e8bf020800204008174b5169e220c02a40188574aa7eab2004020440884746ea0cd2000008041800736d76ef220d02a441a8572c2463702094260402857109d11a220100a001a806f793eab000542c4412846f74fe9f00094240402856f3bb532020c00a4010816d793916020500a4012806bbca99a20080200008856b9bc71a220402a40188469f54bb24008008801081694123cb2205022440a8468b601ef220502a441a8467cb101a400842480008567a38e9f2005020440a846624c26e020002a001084654614e52009000040a01649545c7020400a441080642a2a2a020900a00128163d6ff8900088090410016344bbab220802204088562e654f92005028441a0462e36ff6020d00240028161f852d2200880900188161a4d0290008801040001617e8b3f2009020040a856107f54a000d0204002856107d4fd200800804180160825733020c02a4410855f9c5c27000540c4412805f9427af00008290410845f373926020c0024000815ea63e292001028041a045d21ce9e2001424000a845cceeecb2005000440a805ac6a537000802804108559c8e3df220c00244088159ab31f3020c002440081599ab0ed220800a04180158b9fcf7020d00244028157db8503220142e041a8457ace0dd220102a041a04573e6fd0000902000020556df58be2009020000a8555e3de82200402840188454ed0b622001020000a84547ee9ab2209426040a85540a376e000d0004002815382eee24000028801084524e6b79220802a041805523abb68800c028401105521a7582220002a001884514854bb220042e04188450e51663220d022440a8550d5d89b0008020040085500f460b2009028041a854ee2c289000d000440201), (96, 85, 2, 27, 2, 27, 0xb125df628006804220900d62bc0ab808340a9004a16acecf7ac0410014002103544322cb200442c441884a72f48018104005020840cf6e129c480220a41060167b6e3eb1001800080020337f8137b020d00a4412819a1c5ddd9006212220442ccce8c2880834029004a06569ca77444180048011032a55e4f7220800a0418819480aac39100805020d40498c61c5c80340a1106a1647e70f5e0010818082103235e527640000088010808bf32e931004400800440c5cde4efc8035091102a1623a0e9024402014083401109b75ab200842c041885872f8eae9004410820402c35cfd99c80040a0106a121394c874001100200010309b6155a020800200008183eab5be4004014000882c1ec132e90004022004a020d308f2e040a01488250104ed3ceb20088210408857ce342259004400820440be0b2009c80150b1106a11e94d5d364012000081502ef0e11ab200c40c44188175fb5f7b9004414820c42bacd7607400220a4104015ca1277bc4418014803102e275f693220500a441a80712a6a4b1002804200d4037bafac9c8004000102a01bcf1d3de0011002080102dd8e215f22084260408856e21733f1102815200d4236854164800240a0004a15adc18d6a000a010882400d6519c8b220902a041a856abccc510004404800840b547bca1c0005030104a01a748a704040a054802508cc2179262009028001a8565d48fe59000004020c4031de1498c00010301042018eec0b2e0418014882102c6ad72e6220800200088162a360398006800220140b144dad390025092000a15898ab8ac401805080310ac34141b3220102a041a84612dae418006a12220142b032044d488240281068057f5b39448012809000502bf7c76b7000440c4410805f3d3a7f1106011200442af9b525188824028006a057c92e656401a04088150abe0ea4bb020902a0412855db934cf9006800220540ae7ee1a1888240a8006a1573ac3456401284808150ab48cfb4b000d0084412815a2953b10104801000140ac894022c08340a9104a1563f07a544001002001100b1cc7386400840480008157a1b54900028042009402b6e824dc0834089100a1558e58446440084c081108abb8989b000c40c44108155afec2b9104811020542aab2f876c8024020106a054fdc2474441a04480150aa7131427000d40c441281534a36b59104001020440a9596f97c0015091100a1149fa91e60001012082100a453dcfe200d020400a8552187d470104815000942a8c81e8d80002024004201441454f2441a004881402a1ae97cf2001008041a804ec1618b1106801200540a74ce950c00240a0104a1539d3928e401005008310a9b4bbe0d200d020440a054da345bb9104217020c42a6cddd57c88250b8106a153514fabc801205100250a9812ebba200942c001a85), (13, 86, 2, 27, 2, 27, 0x3e5e28833200d42c441a85bc1fa365c80310b1106216585dad7e000d00840128188276f7e88034021006a061623e9af200942c041a857d96ce4f800220a4004215f619f097000d42c44128575e7c4d2888340a9006a15b645151300088290410856b5574ac88820028006205a2632107200d40c441a815f7b282788834029006a056eeafd7f2201426040a84)],
  [(96, 72, 2, 23, 6, 21, 0xca2a56d31050c908a0c8fa12421051490120bd4e04220270094021b92152651200e04880b85504600231014101b557dec11220404801b37141a30010890880b30a4f610230814881b2f683931010490800b2da10511300c04890addb62b10250014820a92753140211214100a89f5e851230e14881a82cef511030c10881a61830e31050490820a0a0d1740031210101a049d05310704908219e092ee202710941219886bde40010a100809367ce8212214841019306e8b002700140218d3c93b11220c0488189c005a40221204101840742951320604811826b2a3802609040a1805e79d31250c948a07fa6d34002710141217ecb76c110604008217e18120102100148007de457850210a148807d44b0d412106140007d3ae15113204048117a1d748312504948207558c0d012114141007343e5a31040480820704cf43210414801206862ccc31010c90880648fd3101060c000a16137bde300508908a05e21c1b91020d0088159d237f11230c14881593d39f30210094800589d49840030210001560ae5d210114901004f4fc3341210e140804e7f65a31100c808904c3384711050c108a048f74b44021021400048ddc0a81040500020482616821031490101445900c21240c840a0440dd792126148412143b08a521040c800a04053520311204808113fdb36e810615001213f640a8510006008003acde00010614001213530b419102050080134d828251120e0089133c94bf30210894880339e58321050490020323a48c310304908012a49e6411320c048912a32492800609000a129f118941100600010288a1195112060081126a398c2007109012126048683027009482125dcdeb2007009002125117d52104048002022e9612300700908212002355313204848111eeb9ec312204848011d3f64a802401040201c40bdc21050c900a01a3e6e331060480821186d15451220e048811728ad3111204008110fd314840210a140800ec6780202110941000adc62a11120c0089107c06ea40201204100065885a2006108012104a042d20021080101044f2b43003009080103ec0382003109010103bc688200708900a102a23cb21001480100015992a200508900a0014c7ce3102048080101474112001109010001185a72102148010100166132005109012000006322005009002000002843001009080000001d830050090820), (96, 73, 2, 23, 6, 21, 0xe2bb70000830200010f0bd4a39040438402037fd2f3b00481208141bee4d61002508140a0df4fcc7989002424006f59c5214440380224378e512022041801103bb824ec90200904880dc186b190130842090ec74ec2cc49012120835765470424a0928041aa7ca5411300404810d52adeda011810a000ea0386c044941052083431e20322080a01041a136e0d31270494821ce29e001013844a050e6fc47c4841812000872b89cce60460129003949a33641230614001c830c4c00930602050e40f0da4809402500831df61e8220608210038e94f3590020900881c5574c240930a82090e1c2645504403800242ffd3c86224018091017f5a5fb10010810880bf5bfe0a88083084005f8e84c8c00c2242206f2f0efd224c1a0914378a865740030a10081ba06662880280084105cdfc19084845250402e2fb139200c12011436b7989a91060500821b4ed9644880068044059c3120d008c4850406c9a816f000c220024360c264b11020400801b0591361890864a440581e2eb884185200486a9221d4024a082804152e616801070410021a92eabec0930282010d215e660041c50404868e3bc0e2006002100342bee2a21060c800a1a121e88c88206804504f6378c0400c20422067ae7aa3000c02000433b7034a302708948a19c247c6c81000824004d7657e204085400406630aad8404a21282412e6093a51300e04890969b6c3a0910b02080cb449af00488501040659410f882640c080232c86bb4410116101009518ebd80038408050c9c77d34c448320224646bfb64200e00210431d9073741230e140818e7c84aa0890700048c71d81bd448018120021edfe7c620009010010e079865003021080186b11a4a0010900080c1ac07aa44881412006091df52a0061421103032207b91220d04881810a322288803004083f1493d8449c3052285f5005d882240c00022f99ac543025009482079b31e800818a08080bcd07c7a04183400285e5ffc72a2440c09002f0850118120150410077ea908808206000503adfe06e40980412085d5d06b0000e2020242e9603230102140010173e5d761811844a440b991bdda40982412285ca06f88424e1928142e35f4de80201104100714fa719898064244837fbc53084943250281b2bb1b2624c0909042d60112c012714141216af221a90838648050b4b9d86c84805210401a15a43222201801120d068d5391060d008a1), (96, 74, 2, 23, 6, 21, 0xdb7c75e8448c1052007664224201240404020d91244e8c4083202207625d65710230014801d848117c849c125008760d52d541000e00080d5ddcc12008844104075695bef41020600001d14f45f5048c585040744b312901261404121cf682f58c4c832122473d8f18201011410100cdccab95440c18420072fc4e7e51010e10880c95875da4480141200323b552881040d000a0c7637871440818020071d31bf880001100100c660f2e0409420522830c02eb831230c94881c14470dd40840852002fc1d2c241030610001befb8ee4409c2052286fa64ad281221504101be3af23080942250282f66d5c301051410120b90b35a904083800206df28d9500070010021b54f411e00104400482d0e507590060100821b12b9271008c2850206c0f126390000900880af9b0e8104803810202bae119640200204000ae7893f104883810206b93150311260c048a1ad812b58449c1052086b4734bd40001200100abad3715040c3840206a909df241021600101a709118cc4c012120429943055900409008a0a452f22d04c03810242908831401231414101a1556f390484585040283034fd21240484020a06cb47d448c185200679b14a6202210841019d95686904c01810042709c7c7513006048109c05be55040c584040669e5bcb31210494800992e0195408c285220663974374120060400096f40721440c38422065a7cb0b21231494101951dc9748494525048253f204b11250c148a0941a0971048058104024cb1dce31070c908a191820f5cc01c22422863e0defd410016001008dcf0210041430402822dae549202310941018a8c30b44480101200227e5bbc3123049480188ed279c441830022861f68cf0212604840218477a6f2049054104820eed82f10210814880826ed234009c20502860631d46800409000a0805cd838849c5250485fb139bc11240c048a07ea0fb9cc0942252281f98573981260d040a17deb292544843852201f195d3551000e008807bcc41bc049c1050085e117f5f31030c90881783d0acc401c2042285ddb6ef080260104021760ce32a00084400405d5a9c96112104148007551e20004981010085d40997651320e04891742f201904881810005d086c1f1110040081073e7b278c4401202041cf808e9210714901217360ef1240080402005c9e657f500102108007222676604181400085c84161a21070490021718c096100044840401c5c66ce21241484120), (50, 76, 2, 23, 6, 21, 0xea65ea3a31260c848a1c118726411040400820a2f063831124040482099bd779531220c848818139449291240d048a07f7b876781240d040a0753e0f4f11010c10880661d648801270c140a161cde5129126050482160f0618a012514141206072f1ce102700148215ff3ff3211070c108a15eb8228721260c840a15eb24d5d01241404120576ebac0100508108a0528ef63b912405048205175e9d131270c948a151306e22410006000004fc26f63902209048814ef7e22b31000c808804e0d32c2902201048014e04ab10902409048a04caefa80502302148014c87329341320e040914c467f6a31040c808a04c283ca9110704108214bfed866802411041204baa1d9331240c848a04b3390fa010414001204b1562a0400202000014ab1f1bd01201404100497fe01b11040c008a04950125a900401008204903130601240c040a048b7952111260404821479a6b1101250c140a046db662c31200c8488043b0608b90240104820429fd441802611041214223844b31060c808a14152550a000508100a03dab1c2411210c148803cad1db0812405040203c957822512106148003c8ea1a050010a108803bcceb7591200d048803aac129f8104150012038c52a9901070c100a13794126b51020e008813753537f41010610000)],
  [(96, 77, 2, 25, 5, 24, 0xd98bbaf080a200041446be7d330011108040a0757b781e00c000400203a63b9a1000402210080cf2b6b6802204110040e710b34081002008800737ac59e202406430011983ffba105609028089c9422c0802804114000e485ee1400102088020314a77f800a880010503895332c100042010208c22cfca902004111000e0a98348810008048006fb9ea282044060202117622567106201200109b7f3c4c102201009040da28ad90011120080a06bec0bf08044060202415d20d96405203018021ad48c268810011080845646a8680051200a0a02a7f0b520088044201034f1121b20140822a080a4acc59202804014010d1f8706c01500082020680efece4040104442013df93312060082221019d7b2e8202204010050ce818ab840580402022266a28f600a810450103321180900500020800196d9d77202220000150ca09fe448180088484063d64e4480a8000101431dc976d20500020a00189d47b7800021108100441fad3c8080088484021b4136a0028104501010c5432110504020820980bbd34803100900080bf9420784151200a0a25f65a00e408000404002f5f969d0042092200017a6b4fa802300900040bd1e6110401108040a21e7f4c1880a004030042f3418bb0012092280007998deb100201009040397f1db8814008068005ba5b7cc402010054000dc0fc8c4014000080a06b39534082221008144b57f00d4411020880225a3ee11e000884420500d06b09900520120800167b1157882004110004b3218810401120080a21978e11a00a004430002c6bac0e1044080200896281253082b0180c044b035e1540108048000055005caa208c02400112a4793f51044402002894f2d7d2902001109000a76220f000182408020139cf8a2008c124401029aa829a4014400082a0465e882882a20104144a2f2537440010884082109fbe5400a88403050282a93650052032180013fcdbba2021008000109dbb8ae44148248a0024e33ed024020004140006e3bb2b00404221020136188aa8020011080009a31f584008008840400cd706d24088104441026064c711062032101092bc8e43882221108144943f8a448010088482009613a0420288403051046fdbf310044221028823747a8200101808010119878c8001108040a007cbe30c8024120500403c916112000082220001df4d558022201001408d46409c41010884082469cc1f6008890440502250bf832044022120810cc5cfa08230481004484d59c21011120080a8418dde28402004034000078720d006203210101), (96, 79, 2, 25, 5, 24, 0xa3553b2620a01045001345a9fd6440580c860222899b9662011008000904ff28ed50012012080009d8d34c0808c0200014337c75b10415100020a26678e30c202024010110cc8f03cd10104020820894c3e92020a0840304132443ea1040180c0402224851b88103001009080c8532019100203210008908a7fb62028004101111d4df5990148240a00863a51148102a00005040c71fe6ea0016010080808b7867a000089004050116e3a57c0110008002062a8bf3f202304810050c512ec02405042018221877f25262020844304110369fc5100180c04028202e5ddb902804115000bf89edeb0050422182017d91de7480a080010442f7e3665c800008848001ee33538902a04115040bd1cdee710560120808978d5abf000a804030102ef5e13ac410008840025dc117d1882200100044bb37d8fb006209220101759ac57c808004020042eaebd5f4401008840221d18a8e9080b0180c04439d7954310600020010973a70b4a208c12440112e5305dc08140200a8005c518a46802024110100b896ba4700400822000170e0071420a810050112da010d7c818000808405af0c8ee102a04015040b59097fb1042012000096af99e14408810044102d338fadc40180c840221a664803100a0401504034c91ac310044822028868f34db2202890450510d1a6d8840180208804059f875df8003049100403346ab0200544802828165d860a800a084030402cb9a700c418020880425953965708082100c1043224b3e2404008020021620fce8e208412440012c3b94090411120080a2583213a92002240101503044e49300220321010060208aa6008080400402c00fafa40100008000057f822438002241101402fc9d40d0002032100005c13683e20a884430512b4ae0790818020088405635b29d100a000050402c4ab6ee1014480282885806190c20a004030012ae09852441080c8400254a1e96d00290180c000a8f40e7b20540020a08150757328802c020101409a84bf48411100000a2531b365888100411008425f3c5ad1012012080084b98358640a004434002959fd5a4811000808205291865a2008240141102468b6b810404201020947c75b648080800004428ec0406c40880c840421196a59e082300800044a31a1ec840420902002145f4f73c40400402420089e927ac801020888201130bc248030011080809fff5d8c4056010080a13fd375d60084064200027bbc6420808020088400f4a085888282110c1049dfed4924054080280a137b8819c8040100402406f601f1c405804820220dcc918a2003048100501b572a6c4004080200a0), (96, 80, 2, 25, 5, 24, 0xb187c473105402218089b1100291105002218009b0208a72102008020108af67f566104603010089abee899d005040208201a87ed76b105000208009a6e488f9101402218088a5480228101408028088a29cf8ff005209228001a1e6fc6c006203010101a16ee81c1014000080889d86f7cc4056090280a19bdbdae64054020180a19b9441904054400082a19afe74fe00460902008198db77d600540802808194f98dd11046032100899391f44c4014480282a09349a77f10120922800891fea14640104000822091dc819a4052010080218dd08b384042030100218aeae57d0054422182818a111083005440208281899c6edb1056032180898942316e10200201010888760fc3102209220108879636a520100221a00086461110005400008081855caf001056010080898547b5f6105400008089822d2f33104048220209811e27930006032100807f0c22291000482202087dd449290014482282807d5daf7d1054002080897cf985fe4014080280a07bac7a4e4062090201217b67c2584022090201207b5b3cd51016092280887b1f1e3020140201a0807a6ba7011054082280897996830220540201a081798d24c910200020010878cff40f1010482282087867f2cb005601208081781923da4016090280a077e433e000140802808075ba98d100140221808075b02afe10040802008874f14bec4054420182a17346b8764004020100a0704d8bf71000082200087020f0af0014402082806e7452d31056092280896deadc1a0042030100016da31d841054020180896ca528b61054420182896bdbb0851010082280086a5aa4e910400020000968ba4bd44004420102a068535c0520540221a081684ee6c810420301000967b9627c00160902808066c02307105203218009669f73a020040802208066332fd04060020101216560bbcf00140020808064a2b85c4040420102216310e424406201000121631080fc00060301008062dff15410600201010961ca7b7920140020a0806145f43c400209020020610e522300460321008160755401104402210089605aacbb0054022180815ee5751c0050020180015dae26244044020100a15cee3df91004082200885bc7d4e120100822a0005a7e0bd71014402082885a51856a4044420102a15a1b90b04050480282215791bde0405000008021577da59d106209220109570f73720014400082805673922720140221a08055afacdb101408228088555e525710404020020954865b071060022101095408cec810520301800953a0ebdb00444221028152fc917710220120010852f5c58910144221828852a2e081202000202100), (41, 81, 2, 25, 5, 24, 0x19d13f322106209020109cba3a89a802b0190c040df2c5f5a900580c060282e822c6c800c41204020355ba5094001603018080a37c115c202b0180c050d1363e6504180200804265b051e4820c4020002132d3e886700160321808091174264002204010040c5ab53dc10180200804862810346a20a090450413100b042100120321800087c8f0fd002b00804040c190e216801580c060205fc53b8da200412440010fb4a573b0016092280807b60451b083101808084bd159eea4414804820025e66452aa00a890450502eb4fa04300504822820174316449882a24114144ba03841200158240a0205c916e140002884030500e31b2a341022090201086ff0a1c4882224110144b79160f01004108060881b82433f2002c02410100dbb2a8da1016090280886bfb5d18802b04914040b4a6d95cc40182488022193e7adec202804030110c85dec0a4014420182a062d701f1202301808050af1398bf100480c06008174cc08a2002084430400b9dd926e4062030101215bc4f98e002301808040adbb60e3c005108860a016946aa6c80a890050542b1d480e4100609020088)],
  [(96, 83, 2, 27, 2, 27, 0x83698ab80044810001903068d99b8001900021120208b7f0808012401002443f39ff0e042208c0808897b6be4940044990101932f64767581088010202201e9814a808112001006403cfddf2204200cc08081978435cb40844888101920e98404b80099420213285d2a589d0010284040610b9890bb00022440000c906e44621c0044180101130d7aa11481081210203021a7eb9eb021300204244033bbb84a00061080840a166c45eac0008890108822c9af0c88108941020328187d50850010204040600b026ec060024048084811600bde002040010401002bb917788008020020202175cd5b7021126204064c2bc40162002604008489053bc54802044110401112a509edc000982200122253ae943e00132400026442635c1c01020480200c084c4693e40004910100912928b3cc800184002102811fde1390210202040600225fb18604260c4084898423a71e400448901019227f6a91f80081300203060fae5f4808110401004441f0c4a3204220cc0808993c5d455c000090010081076a179581090230212024ed3c65b00022040422009c9aa46200004c008041837cdc8c020400004010006e5bcdf80099220213224d0f10dd0001284040250993c0aa60024040084810306ae064080419810013253f111a800881002022409fb1b45001022004060813ad7c46000448808440926e95b1c00042101001424b8cdde8001942021128493cb8e300102400406041178857e0022088080889219560ac00401101010124134740810800302020047a64a1a001126000064c0e656b6810024882004891bcd2dac0840098101022319f3ea810813102030606123c0300012400402440c083e3e0420504080c2016c498dc00400101010022c7f176800004002000805863c7500100240404088a933d5200024c008049813b99384084099810183226fec4604081300803060384ae470211226040648870074f00022500000ca00d6460cc00049901009321aa03f904081120803044323770300130440424448625e0c40022508000ca108ace12c00408001018000f44994040891208032441da6f85001024404060482e52d0604020c40800980572428c00441901011320ac448a8100821020022011645a50010020040408020bb37e0420044080810034006540000880100820065a6d9800004202000840b5628d001008404041081386132000240808048102484c7c000488010092002c34b6810002302000240426191021000204040000613526000050008042000b7e9cc0000800100800013656680009400201280025c7f30001200040240003447b20402004080080005a424c08049081009100094ee881008110200240003e87702010820400500000117e0400084080008), (96, 84, 2, 27, 2, 27, 0xccd47c620004508084421ca5fcc5400221000008a0c8d1cf4810220c0200898c67187160020100080820c6278fb20024488084c09c46d4dc81000088200009c4556d320020000080800c421c8c60026048084891c41416220022408080c81c11494f20424084084808be8b9aba00260c0084898be1cd6bc10220c8200899b89a63741020048200811b7025f260000508080421b684380a0004500084420b4dabc0a00240c8084819b2b88e5a04260cc084899b14091180024088004809b0383eb2042250c080ca1ad09a21c0026488004c89a9697b1e0022440080c90a7833c3a00044c8084419a7761a3a0022400080c80a38eaf420024508084c21a31d423a0422044080890a128397c00024880004899cd6e0ba00004c80804199a9dc0920000408080401992532f810224c8200c9998c2790a00221080808a1985840e20006480084488950cec7a0026000084880926c87ec10020c0200098915e0a6a00200c00808189112ad8604260840848889067f71600064080844818e9345a600220080808818dd375a6040204c0800918d1146a010224c0200c988c6f7c2c10220082008818c4009ba00240880848098ab70b0a0006440084490870e5694102200020088083ac87660020448080c11839233400022448000c91837f66fe00004880804097fce79ae00241080848217f0a6e2e04201040808207ea6e8880020500000c207d6145f20026008084881769b197c1020088200809769150d60422404080c807598c2d01020400200c00755e793a00065000844a074a01a3010020402000907204614e042044c080c1171b34b86042200c0808817104276604200840808087099664e0022488080c8970763b3600024480804917057633e042240c080c816df0caf810020882000896d9da3ee00200c80808196a3eb38a04221040808a067f1e9e2042210c0808a16725e58204261040848a064e28810102004020081064578bf6000648808448961e46b2a00260c808489960781cbe00004480804115f42d2ea0026408084c815e33f01e0022500080ca05c02d7c60020500080c205b6c24f00022480000c885b1127fa0422484080c8859cbf1ca042008c0808095815fc160420444080c1058042d1200204c8080c195803288a04200c4080818564582dc1002008200081546ac02410020c8200099533bf37c0022400000c8052ff25f000024800004885278f0140024080004808521729ce00064c008449850bedb26040248c0804894b5e74b800261000048a04ac2d7e2042010c080821498d44f2002400808480148c72a4e00041080840214756726a042208408088845dbf47e0024500084c20455f6812002204808089143e7dc56040208c0800894291e93e040210c0800a1424dcd22040200c080081), (96, 86, 2, 27, 2, 27, 0x9ac040db0008812000224658bf87b4002604000489091be464e040803208020663af4b1a600244c8084c198cecdbc70409812081224626e9fe7010260c8204899847c90ed810984302122860c596d8810260082048817b6afaec00088100002241cb02297c10000802000086d27be3404099200813221b419068400224c8000c996c388e4900088300002261ad372ad010020482000916a9db77500080400002081aa5aa492042600c0848816a53d408000981200122459ffb9dae042604c08489166545a4f800104002100819583a65400260c800489964bd9f33800984002122818ee24746042648c084c89632cddde000882000022218a8899e6042050c080c2160efb778000880000022017f8d872400260800048885efe3d35040892008032217a5ed31e042048c080c095e67511504098220812225700dfcf800220c800089959042ed3800903002120616210da481022440200c90579a2349040802008020215e364c0a00244c0084c1856e59c0c8108923020322551fbe4b000021080000a15394028b8009912021324549189eb41020488200c0952254596000984200122853f2e673604224cc080c994f8fb6d2800191202112453cd4daa010240882048094d9f6baf80008400200281305e6ebc10020802000884ae3912c800112002110212a4784e0002600000488049edf6210409830081226121ec77b2042040c080c0147b26866040080008002011c7125b41026000204880469c23f9800990002132011954625600044c008441845394696040982008122211272463e0024480084c0843a2494e800911202130450b24c8580022488000c8942abfdb28008840020228109d456301022408200c81411969448008930020326103f4d5a4002200800088140e4aca180088200202220fd23c47e0022508080ca13ec329be80011100211040fa0b204600044000844003e59c07800098300012260f890877200264c8084c993d99f20580019320211264f49d050010200c02008183d16864e81099210213220f293ca820026440084c903c8b557780088000202200f2188ed60022480080c883bf8d1dc81098110212240ec78c6de00264c0084c983ab3065b80091100213040ea4c5ec20024400084c0039e8d9a900008400000280e71354aa042204c0808913993476b80091020213004e52701901026488204c8938b9984780098200212220dc043cc20026500084ca036e1a24800080420002084db6034120026480084c88369abd1804088120802244d86a999400221080008a135e18c4280090200212020d783fec6042608c084889359b83ed04090200812020d635e96e04220c40808983555cbee04081020803004d4abe5780020508000c2133d2f83504081100803040cf2b2a4410204c8200c19333f332b04089220803224ccf48d7600261080848a1), (6, 81, 2, 22, 2, 27, 0x3ad013bf2002410109041acdfc37e001300404881cf3ffa1d80090004240066d73bfa0204c08812242facbc3d41022044011213b6c8a32001104400889)],
  [(96, 76, 2, 25, 6, 22, 0xb52bfb7401400000092b4fb5bcca9001220090b3decfa8a0041020008b3062f20a8409220003b23c4d64004280000a3aee32f6028800220100ae76353009048200019abb47454a04210200a2a89b0c3080c03000142a854a35080043000048a1cad524000020000c0a0cdb2d880c010001029c55091428408220083993514648100100009092b5e3f8a0409020003925b2d482884822010990eb4758288082201018953b78028c0822010388e001e0a0421020022882a42f4800290000a185e36ab80940820001383190d8829000220010800e73e8880012000007e466638a0c210201227c04c650088082001017a8f6808880032000407a6a27d888c0320014279297418a90092200117465227ca00010200806ef64180888032001406d011a94200200200a06cfbfeb0a10010200106adc4fcc8104100009864fef78c8800920008164c1999ca840122008262fd4f940800820008161755c708840320004260403320008480001095c3f2ca008c0020010259c771d88800920000159741ab8a94012200125807e82c0900820009157cafdf8a88492201095616a0ac804030000c255bd68682002802002152a7c858888012001004f3abda0804290000234f13aff0810410000184dbe2abca80412200884dabf10088c092001034b1f38c88880920010149047a4088c0120010248ec221c884032000c2475ea9580940020001244e6868081409000013447127f0808030001404364d34880003000040435cb05c2004002008843324840a9049220019418df2e0a04010200023f15adfc004200000a23d6bc0a0810010000103bdee268080082000013b746954210000200903a5ff9c8a880922010139fa0bc800842000148378ac09488409200083376d4994800210000a036ad70d0a004902000935756bb40940820009333fb17300884020010833d2c57889409200013312495b889401200012311fb430a800122000030ec1a70090082000112ef44094a04010200822e7288d4204200200a22c9e8b84a94012200922bae0f30a840122000227c4c44c8100900009121aed324800030000c0210b90f0280002200001f94ae10a14010200121b1b88f820428020023184b11e008c022001421815e314084022000c211f767e0a8c092201030d8bd2dc800490000890ca0afa4a00410200880994eac0a8c01220102054cacd8a000902000102d0b7b081401000012025217d00804220004802451424a8409220083005782f008402200042002a3554004020000c2), (96, 77, 2, 25, 6, 22, 0xd199cb4450214810011e862618c200124000027411f7200100044000819b7e464c00400000082cc1b557610204010041e5d349c92041240002672c91405110092400013954c4a0828008220001c9ac23fe44024900044e3f149a408210008042318dfae890001200010388a16d1889009200011c44a952810410010090621e71eb02010880032302b802581081040010780277aa029400220012bd93fdf6400008000405ea383aa02302080040ee7cefa311108640029173d0a170a8801220100b9d7101a140001100405cd570ec2a0104880022e2779b10500804400117066361080021000020b7ff64d650a008100495a5bed6420102400000ece3a08b011000400201656aea6428008220081b1943a3e04a0010004958c68138080100080022bcf6e718520804401315aa6d22428400220082a9313b4c1420011000153cb7b1422100480000a9c0cfed8000500001434985a138a1409020013a1a525a440614800091d061579e022108800522769898c9100824001113a4b5d58294082200139d2558d8404008000804e2ecff928008408028270162ef91200240012131c676382002002002097fada64544209100844b3076aa2000a400008656189c39120824001312a44f67c0140800009392ccfafc4041080009048b69f8e28412408006645090af8528004401252102b1a0a0c290201238f9ded8a040011000604686c215224124800266336a56c812090400133182a79d4210080200918a4dfeae54004910040c4f8e6c622102480000e25f38d810008200001111fb8a9400408000083884776c450410810090440e40a620108400008a198ecd191201240012306e33ba42004802008981beeaf604024100044bf1e1fff22010c800321f5bb2d3101812000206f9d5333c884012000827c57ffb2440019000603e19b6982a4004880041ea15784912802400124f117ad00808290001217832da080482010000c3bf5f83e201004000009d08f919141052040242e3d4c3682840822000371cd337e1020001004138c718f7201084000289bc17898101842000244dd97edd8a00010200006e8a63a21402011004436b2ca1b2010a400028db17bf94150012440002d65850d008848200109699e9d4c5060081008134a7ea592840040802419834060051800440204caa7eec48140100009263cebdcc50400810080314edc7c0a21008804218a0b56b010090400012c2aa0fcc800430000c85e794ab4500108100102e3f008f20502400024d6c6da7b112002400020b5c5921480409000083), (77, 79, 2, 25, 6, 22, 0x5b1ac8ac0a0849020109ab6a84771520824400314fbe9b772a41248802668c11c05a54024910044cf970385c2900822009197be40851410120402031daf70ba2021240004262f32f5521482411004cc1bb8d780808090001017fb98bf0111082400210ff2fd3d32a502488024df90dc49614024110044bd5c447308904920001974f0742c852810440126e082c14f2800a4080285bda032d000414000090b6d0f2b3089041200018691f8485942082040130cd57547d2a40248802459809c9fc0420010000132af7de68208480201095f797cea900802000104be19a5380a41008800617ae97392540009100402dd3b6ad8208280201215b0b42d4042090040032b5eb538a20100c000109696ff30804204100001acf3c1c14a904122009857e6067e140052040042acb7003e0030a000048d53320a2c10024010004a9e9a5cbc09040200098523817b4910002400100a35d1f9728402408024542ab41d250a04810049a7e6aa0e4a00090200814cb888208420800401309803ebdc2840240800452f57999610a04010049a5b16b4ac200080200814b62d08c84005004014295ee9a0d0a400088024120bf19f41482411000ca29fa9c680900020001044c2efe694209204013287d164402841040800610e7ee7da10a0001004921c5654540840020008243586705141082040210863697062040240000450acf0cf650024810044a1036485c21048020099411f9382011004400280818e7e5d024000800241018d422850604810081a0294e938204200200223f7d265d1500924400127e9d75d0202104000420fa9f6dd0140241100049e6e3f328880412000083cb7c22f042080040030796d60a00830a008048cf03a5afa400208000441df923830a94092200133b27fa5a9408520401467403860d22502480024ce6cc77ca502048100419cc8e6eb02900822001138a58b7a041840040244712cb91220210c000520e21a39dc4082480000c9bf8e83dc204280200a337d534be1100864000906ebd60dd000108000320da4c9b48444249000849a661388880009000001)],
  [(96, 74, 2, 23, 2, 23, 0x97f1ab59880233002465c67c16a0041c94009951226380801300020e407a818820018100898bd48339000031000062c79fb0620448c40838ac2ccc10810611022625518e84204004408087ca73018801230020e109f17e40044444002835577610800210020609681b24204cc440937e1675c900101110001d680502a200049008074887a7200004040021cdf0c386204c8c409371395fd800011000009c094500a20048900836d420cfa8801324020d9a5fada40044c44003668e75d00003200004d8ae865a4204c4440925e8aba0a080010402016705854620098c009957c9b1380001300000d3af4a2ca20008900814313c67988031300248f8af5f86204c0c40923d246f4a00005040020e363b5aa2000c90081367a12498801330020cc88a54aa00004900002f8b3c0100022100044be2b97c400008400012f57798908121110240bc58ab680001c1000929fbcb71080061002249dd3180420098400992729ef39000011000008cc0dcc4004084400121026449001031100047edda3a400044400021fb2bad9000311000486ff670c4200c84009312763a328000224000448953d0620018c008911a615d2801002500003f7d9f44004c0440120e4d2c528010225000436ff514420080400900dba0d7200110050008333d2fe6000ccc00130be68759081111102082cefb184004404400208c2964a80005240020229ff244004984401908401ec98001330000c1f50f460200c4000920754c381000201000401cd28006000c8c00130709a999000051000201afa0244000c04001206560529000251000601952ffea000449000206380d71001061100241774098620088c0091055953c100120110040123206040009840019039ce081001001100000b9d92ca200009008002bbe5b1080241002600aee1284200104008802a16fd18001230000c0a3bb74620090c00980156fbe100004100020055a6f46000c0c0012015359218803030024805495126000c4c001200d2403188004300220031efe04004904401800c589410001010000802a16cca000009000000a854710000610002402a047c4000904001800a7cbb980011300008029e650600040c000200a76e4280010240008029d04ca000489000300a2e5d18801030020801574f8a20010900880036e1518800230020400549144004104400800149a3288010240208000d9f8a004409400200007d4188020300240000002c620000c0080), (96, 76, 2, 23, 2, 23, 0x991598ca4200cc4009397647e2682040c1408196869ebe420084400909335a988420048400838a2dc7528200441008289723cf802000800081894dbc740204c00409288ca3f960200cc0009387c7304202001400088854f6f6e02044c0408381fa2642020094000988014056240049c440197f7a7be2420404440807e8daada800444140027cc8d0f2420044400827c87f03e42008c400917a744ce04204484408376008c2e42044c4408373822a0802008000090737be444820418140897281187a0204440408270b084c402004000082703e08dc800040100026dceed1662001cc00896d647e6a42048c440916cfef64aa20014900886bce40a8020440040826bb2a0fa4004844401069646552a204049408068b4d1904004c84401367e3ccb2a004049400067dc346e4000cc4001366e150d64004c44401266d5dcba42041444088665c3924420408440815fcf6d5e40048c440115f65fb1240004c400035e6827d4820010100885a7ea988a0044894003596a4cc60000c4000125950936a620004c008058f2d3ce42040c44081584eefa662000cc008157dbe2ae800004100004f7e5d3c4204c8440934e49f0e4400488440114e249368420488440914dfcbfe8420490440984d449f2e40009c400194cc618c0820410140884c1f343a80041c140094b65f706620044c00824af8786202008c0009148ebb2aea004149400848b909fa8204141408847b3552442049844099465242826200ccc009346011d168204041408045cbf68e8000441000245821f1680041414008433199ca40001c4000942b6263642049444098420cb29080041014008410c751aa0001c900094087f0248000481000340301740a00410940083ffaf8604200c0400923f4b95c4420040400823e72b670800018100093dcc8e3ea20044900823c1e2b2a620084c00903bd01b6ea0000c9000139dbd046a2001c9008938236fd4a204489408337b964fc4200884009136cbe8da40008c400113683dfaca2040894081348d7904a00418940093284d194a0001090008327196dc6200c8c009331c9c1bca00018900092c367ddaa0004c900032bb8e5ca02000c000812b79c8d8820400140802b777d52620014c00882b173a2640041c440092abd05fe4000844001029b4c18ca20440940822852cc6e40049444018284db53282004c1008327c952fe40041444008272946cc620440c408226c7c9cc4204104408826bbe35c40004840003264163784000c840013261117c482004810083), (76, 79, 2, 23, 2, 23, 0x900ee7fa084000080100a9b056662001020500054bee1e4401000c00044a70a2b7c60200040008047ba0e931000800280008c2ec542a0011305000d0eb49e2341020e0a044a09869b44020448040833cf4f578404010800120796b144c20811205020ced017f0e4002240a0019c2ed12740200880009135289bb1d40089928006621dac3f000030000048c32f46a74002020a00018446df8202001c000893074346ad040888281046071932b208000040200b3304a640102640204995995a1a4020010000882a5d309ad00081828002545ae9cf908007100224a5e07f255002064a0009358f2a5aa2044494082259446c850400182010249366ac480813301024c8f6cb53f4102260a04191c35cfaa42009c40099232f0ed4904081028102463eb2538080110002088b1c926b3102626204911277307c0200c00009220c1cd994c40889881043f9fd3262081100502087ce4dda4210220220410ef93ecd0020090000981d5e38104c40139801323a5ff963a8811325020c727e26cf21020e220448e44ab392a00444940021c83d7204840028801103896cfdfa88103250204704deb11000066000098d99407460204c4040921b0b56f81440831281123606f5fea881072502246ba5312521024e2204c8d5cba08a6204ccc409318c5229dd44082928110301390921081201102405fde9808000024000018bfa1077ca204009408017d60746c840098801062f3bacd090013311004c5e72094f310226620418ba5b36ac4004484400316d7b3379000830280122d0cf7d0a0800504022058d98851400006080008b12c0fd64200944009815e0ce619440031201122b9a1079988025300260572c84fd210006200408ae05b1e64200c44009215a370384840008801002b32c38da0001304000c558a3e7a400004080008a7f7c8ec4204c04409214b5c22190400802010428f734ea208002040204503364dc5102084a04409f7653ee82001c1008913e9493600400900010627abdace00803200024c4daf51b401004c0004c89b3b83de02009c00099)],
  [(96, 83, 2, 27, 2, 27, 0xcf90642e000880c0010039cfc9150803100010280737063a3900400302010065584e520209402441001c9fc925c00180040810018deffa68001502900220718368e5900000300010062e0fa5a2000402000201c557eae0801281088410389d3b1390001028008207114a8c61106a00220d00e1fe33f6200c40a040a81bf4bf00080008100041037a91f1ac0811018006006e4f2d720102200000c00dbd0dbfe0208402041001b54b1b24801001408410169848e688805029004a06cea878d9104203020900d8dbe54e0205002401800aff9b64c000280480000352e8ce72081100400600697ea8e51102a05200d40d0c8a3bc4008008042080a050e28444188040834033d170978002102810020666e42764100204800840cc6abcbc820000900108097e7904880000100041012c622808083402910620245a0f0d900600302050046be6f6a020540a4018818d7ac96e400801c001501146170dc0001018000006276e60f2004801221000427ae846200040a00028184b5de46040881c003102fd9ccc680810008006001e76d89110040010201003ca0535e0204402001801762533f90408812003102ebc4aeec0810018006001a837d679000007000140325961a482004010010015fd392144018004081400bab1b158080500900400540923df1000801200100274f2beb220c006041a004e16d6c440028148005029bfed68208310041060052cf0a040106200020c00a572a0c62205402401a014ad35c6440028048004028a37160888010080048050c67a7d110480122090020eff51602010024010003b8549d40418004083000740d89c88805009004804e7dabbb00028012004001aba7f1e020900a441080352e995c000a014801100697e7eec8835019106804d23a2850104a052208409943c5004009008442080301378c044020008024005e0298d80005029000204ba994c3810020300080095eae2f24001402402001291b57dc4018014081500481aef79000402900820087caa6b0006205020440907d79c602004020010011f58874e401081c0805023b1790388835029106a047006edb1006a052205408df5e3b2200500a400a8019f55974400a0048014002f19088c88000180048005a14e421106200020d008aec546e400900a44208014ffa280441801008350027e055308830000106800405198e100220400054087514972000d0024408000e076c38440a80080340217cdefb88010028002a00239ecf91102801200d00046f831622010024012000837029c4408004003400105f2588880000800480020ba481110420102090083f0faec2205000401a00076c523c00100140801000b483d8c8015019002804108cb2120000050010400155bfb22004002000a00), (96, 84, 2, 27, 2, 27, 0xfa2f157e0209002441000f8ef9b77220500e401a80f63579432008406040201f360919e020d402441801efe197ee220d00a441a80efcc4b5f200040e000281edbebeac2005400400a01ed5bcc4a020400a001880ed405ffe0009402440001eb76b8a60005402400801eb67027c2204408001a81eabb43808204001001800e9aa7f0a400840a042081e7358a232204406001a01e30e97a44009400442001e1fef0c7020c406041801dfc75856000c402040801df7d01c2220440a001a81df374b8c4008408042081df1bd3532000406000201df0d3e2a2005402400a01db4fe05f220840e041281dad805d6020d40a441881d89870632201406401201d6407c7c200c000040a00d490a4a04009000442000d3bf85df2200406001201d2d223a20008402040001d0392cb7020400e001880cb3fd48f2208006041200c9d22492020c40a041881c9b00af6000d40a440881c8932d260208002041000c70c2b46220040a001281c5ff19520000402000001c5c3a62e200540a400a81c3046006200000a000280c25c2a92020040a001081c07660042201400401201bc9c7702020100a401080ba121f4e200900a440280b7d3787f220140e401281b6f3df882004000000a00b6371a02020d002441800b510a20e0200002001000b4efd2ff2205406401a01b47eb44e020440a001881b314722c0204000001800b06029cc2205408401a81aed3841a220d402441a01ae3be4484008400042001ae204bca4009402442001ade4150e020000a001080ac1fe0548208401041001ab9d02da2009002440200ab9bd346200940a440281aa6d95448200001001000a99af2da400140a402081a942c1c32004406000a01a921e6aa000100a400080a90717d7200440e000a81a843f9e6220c40a041a81a7c8f9132204006001a00a7970b072004006000a00a567dcbc4001000402000a56144220205402401801a29ad17e200d00a440a809ec19c16400840204200196089ddf2205006401a009570ab402004400000a019125903a000c00a04088091243a0c0204408001881900ef2ba200840a0402818f7cac26200d002440a008ee8353a220840a0412818e8f7b9e000900a440080871c8326020140a4010818557fcae2204402001a01854d19c44001400402001852f287b220540e401a8183cfa26c4010400802001813ef4ce000040a00008180c5432b200c40e040a817fe17e5a40010024020007fc6380840014084020817f9cd242220d002441a007bb047dc200c408040a817b53217f200c00e040a807540e0d3220940644120174878e824008002042000745bd76620000020002007159938a000440a0008816fa965082204400001a016ed0f3b6020500a4018806d96b4c322010064012006907504f200800e040280), (59, 86, 2, 27, 2, 27, 0x29b53574f220440e001a81a1adcd2c2001100400200665ad7f5e220800a0412808e80e97288830028106a01eefc081c2004008000a807889095608825001104805c55e7a4820014004002016c16ac80c8820038104a01a4e67d96200840204020167f71a60800240091000018ab5221c2204000001a0061769f4288800028004a0185a7f4de400940a44208160b67ef5880110080028057a62d557200c406040a015e53270688824029104a017376432a020800a0410805910919f10004021008201636224502204008001a8058b13acac8804039004a015d7437a4220c408041a8155eff4808802500910080553124e1e220100a40128054ad3157888300081068014ee3f0aa200440a000a815323201fc8800038004a014ad698b42205008401a8051b3f11bc8830038106a0144af68b82201408401281505784df808210281042053ca4f93b02084060410014ecc38af88810028006a0131a2c16e220940a4412814c1b640c208100240062012f30ae96020c00a0418804b6414c3888250091048052af5303b220c40e041a814a7b5080c08000180040012882d732000d40244080147ec2de8800250291002051f75ee6a220500a401a8047d436ed880350091028051e956f92000d00a440880478c54d3008100200062011d13853b220400e001a80462cd9ae08030020102a011897d8e440080000420004488a067c800501900080511ff3422020c4020418014445996a08804021004a011078430b220c406041a01438add42c08000380042010cb6f16f020040e001081409fcbb888020028100a01004e62f2200100a4002803ff8e71c88820008104800fd9a64da00044020008013f0f0492c8801038004a04fa86437a200c402040a01)],
  [(96, 78, 2, 24, 2, 24, 0x92fdfca801040401008a48c3c2e80608020608091bd5c7e0182088182063c712558060032040838b55e4c80004080000860d33b9d804023204103812d3fc6010280818401f5fb1f80001010000227c7889fa808046800249ecd4c058020812020827631250a00800c80020dcf1bdc400608200608173ac7708000488000485aec09e280609320609368d72d9a818002810201a2ddde3802012200091685fbdba008008800205a07eb69a02001a0008266df208a80804e80024d8de507ca04012a04011622363de00000c80000d87c77c8802091202092606e29e20000888004057de9891a02010a000905afc5d304080044002096b8c0ab8040902060105a48a40601024881804563995a9806012204091575d5e66000280808401531f7b480001120001254a43d420102008180014ea360d8020932020935354ad084184084102854579cc50021020000a14c450afe010084810409310b54c8040012040024bf591804104004100812f70f8d8060902060904a2e9086010204818009280e2668040a120610247bbbcb40080080002051d7caf71061001040a04748abba01028c81840d1c076b480408320600346fc602441048841048519d0b1f0061010040a245dc0100408208408205163001fa02002a0008143f4a276018004810209096718780209020209041066a7441800c41020cfd557d28020102000903e34b1b2000048800044f6cc6238000022000013aae485e000208808004e91263d80002120010239212d5681800e81020ce418bdb0021010000a23845647e010244818048dc0b4de802011200092365b8972010044810048d3a6c74a04002a0400134600b14018248018244c85b4d71060011040822e0ae7e2010048810044afee9740061030040a32a397a9280804a800244a7d6e96100103100023288c6f9441040c41008c9e48bfd00208200208126fe9f6c01800401020894f1e6700001200001120c5d29a00008c80040c75045778000132000131b9e4af680820a8082046d701dba06013a040931add9daa008248808244647484f8000a220210117a51da04180084102045d5fdc0a00002a00001172a892a0002048080085bf50378000a12021021693c3f60100408100405a0d566100122100121162e230c41040841008457bc8331021011000a213c96ff80082480082444a22166a06002a04081126a02684004044000884424ed50021030000a3098b084e80800280020022d940310200010008007f8062a0002008080001cf8d038020822020810720c55280800e80020c0f42668a00012a00011), (73, 80, 2, 24, 2, 24, 0xffd07212004002004001dd5a5e1d006013004093d749732f002012000091c281bbd0004102004021b37619b000600300408384f0076800201300009370d4ab9e8060132040936d4070ee0060000040806a13c1530020030000836840ec4580401320401367c5784b80200120008265f75e708000012000026321cc2b0060020040815ffe4e860020010000825dedbb330001030000235d0167410040120040115a443f6980600020408057a3621a80009320201356e767b1a06092a0609156dfbdf200601100409253ce3864804022204101536d803f8060832060835205e5a21061011040a24e9648bf0021000000a04dc5a9fe0020100000904d7a61ce8040032040034a79cfb28060022040814a5db7938040a220610148b3de5b806091206092473d379700201100009244073bd71021021000a143c1267500412200412142802b7c1021001000a04246de9fa06011a0409240f2dc7410200210008140bdb16ea06082a06081405635c71020031000833fa1c1638040022040013ce794e90041030040233be6fe1ea06010a0409039965e9710608210608139738de6100102100021391db9550061000040a0385574f11061031040a3383f7a9d800010200010378b030880208020208036b2a6dea06001a0408236363afe8000a3202103362bc8338000832020033564b0d30060100040903511753480608120608234253bec806010204090329710e1800091202012326f6a9fa06012a04091314d5d55806011204092301ab40ea02092a020912ff1d3478020002000802f212c7f1000021000012ee1d6860060120040912d89bc6e8000902020102d5f3bda1001001000202ce48a858020132000932cc5bd2a8040822060012c593b9c8060922060912c470bfb1041011040222bb0083f1060001040802b27307d0041000040202acae7720061020040a12a57da341040021040012a26378580409320601327f027a6802083202083274d8c1e1021031000a32700e4e5800092202011)],
  [(96, 73, 6, 22, 6, 22, 0xf387cb904d0c01227074f3252220081808087a3508b10207004c083b9b645a01a300064c0d890f3d40c08302060eb4962320204241020741a281a130300481c19acc21741110004842cc4615ea089000142163fce89a068c24193071ee182e824200088858cde85480a30006481c397089249080022316169f4c6048624911070aff3350306000c1837e38f0249101080862bcd8aba44c0c312070dd5e5c5826040010382e45849513020c081c36f1052089028622061b6b288ea0c084820615678658d068c001930ab13d7610146120c903503fb5d09130006860a79d04bc0c08002060d3581262228c001928698eb4170246000c8834c21f7041a100044c2a5bb7f480d0800226052be76110640240230a95b553c124200088c13fd1b9e808309060819f7214240818003020ce244a62220c18182865b4a77f13010c401c324bc55e419100048c28d678522408084041143c4bf6e020e249820605a24c21246000c8c0fc29b618081892408175b5c252091800322137e3fd3106842411309a375b7682201201084cfaf33d898206020e166d05d944c18003070b1a9faaa220e009828583aed3f12040c040c2c045769898100040e16008e5020c884824612f994459240c001818965ad61502021208082b2abdd641010004042570b506c4918003230a93cf43d248c001918945de198122200090c0a2047f0481210828224ced6d540c08482060a642947e20860091085313bb7b11420008942986d32a491100048624a6c01a80c880024602417879d240400101890e8c100030200081807a8ed04888180240a13c7e64b208980034211cabe636200e0098084c6d367912010c400c262caecb81030906041303dc8f24d080022711534dfb1060400103089c643cc9226000d0c44bd84a50903000606022288c2c4808302030909aeb9e2684001138480fa753020312480823f79f67888100040a11f79ba48490c0122300d043766040600901046100245034212089822f487f04112090284215b381ba081800302109c969ce228600912843d03e8c120200080c01aa61cb888106040a10c8cd49c0c10301060860de6320408180810422830381346000c9c00e420b789010004061071b4dec4818003030832d4dd50484241110817cdf8d124200088c2058ea23419209028c20143b04c090800222080a1c80a04040010104035648f1003004804200003b101210004440), (60, 76, 6, 22, 6, 22, 0xa8f180dd89a380264e1985eae9c892380264617d2085e081a380264c17b179b30898380260e175102467898180240e173de932489a180244e172a96347890380260616d3ceb838921802446168764a0181a180244c1686c26ff81a389264c15d3029db499300068e259940b6b818380260c150fd2b0a890180240615069695081a189244c1505242a7898306060e14ca2c09981238026441459e44f889030606061457c62f0888086200a144d5f2f2818180240c142afbaa7808300060814291b0da818389260c141a62eb8099300068e03f1c7ee1880306060213e2a76ca89a300064e13d8205c3818189240c13cc95a3388a380264a13a02a6844112108284234b5f392419300068c234a92f054912108286233fc572c8121802444133e7f34581a300064c131dfcd9a498300060e230d47f2480a389264812f6cdd0a812309064412ea57942419200028c22ea2feb241a309064c22d1cc1d9818309060c12d108fae49a300064e22bf53bfd418300060c22bd3379a888206020a12ba973d009a380264e02ae476828123892644128f3d0828823802642128d62b2c499200028e228cfb956499100048e22817ae3f8103892604127f88bed098300060e0256f268f80a380264812497f4f0888300060a123c10236808380260812254c4b1498100040e2223b9b93099100048e0217064b781210904441212b496a81a100044c1210d49f509a100044e020954938099180248e020342e2c898286220e1200b0266491200028621f26caa980a109044811f086cb080a18924481)],
  [(96, 76, 2, 19, 2, 27, 0xbcfbbaa200000cc0013bb6d1a2c000a0285201b4433172000408c0083b35f985e000008c0003b093012e00020844002ac97e0fc000c0400290abf529f800080201200a99b7776000a0044200a2d54494000e0084281a0f0fb88000c02812819af4af6a00060ac50839a70453a000800402009999920a000204c4011986460bc00100080101919581800012008410190204bd6000604c40918dcc4506000602c50818852987c000608040828794daf60006004408083a758960002044401082a92cda00020c4401279b8e7bc0004088008376e78392000202c500175f58a5200020044000746acde6000c00c028173c2bbb80012000410072f70bb2000408400827225e50a000a04442106ec149ee000004c00116e1352a400000a0100267c1fde000100a81103664badd80006040409061e14b62000c04c02915e0f7ed6000e04442905c72f344000204840115b12debe000604440905984251e000802412005852143e00020cc40135707dc0c00100a0110254198f8e000804402105295954e000a02452004f5b0ede00060c440924ecfdfca000400c008143111cc6000802c12014297c99c00040a81083424bdeb8000e028528141887c1800040c000924131c6ac000e02052803fa96758000204040103e0137b6000e00442803b815cb4000c000028034d22266000002c100130c5aaae00020ac50032d6a5f0800040a010822c10d702000208c400325d66a2c00020a850032588e73800120a85103242a23d000020c040122288eb12000a00c420121618f8e00060a450822110cfce000a04c42111eef5ca600060cc40931dda0f1000020c840131be60daa000200c40011bd2784800060c040921b8ddfaa00020a450021b22a32a00000ac10031a7af55600000c4001219a6dc3000060a0508217c7ea7a00040c400921658a8a2000602450801619bf1e000600c408114d68d62000e00c42811450835800060a85083129a260a000608c40830e017b2c00040c800930ddaab260000084000209c1c31a00040a41082082377fe000e04c42910573f20a000c02c1281028b2a900002020500002367b8200060844082021cf4f4000804002100211b95c000e0004280019f526a000a02c520100bdf0b6000804c02110088901200000a41002007e97f400020285001004fdc7c000e0404290003db36c000602850810033ad0400120a0510200243b48001202851010023c6740012020510000107f70000602050800006484000020a05002000144fa00020245000), (50, 79, 2, 19, 2, 27, 0x24ede4ad400050242108c33e43536000400400806d63a243800040108002b05a4c9600008221000d3c6cc8840002010084025f750f1c0012088410349cb57c90001001004028ec843620004008044010923f8950000022000820630cb0c00100880103409f2b9d0001c090852280e305a9000301200a45003a4516000601009401f24cd928000400800813d80a4f8c0008048210075a6bafa800000300004eb06edc7000400601009b45df86400040281081361496b4400180482500684c2b1e000180210204b7910aff00060020140166612fc4000804802112c68db680000c1908126583786d8000281010840aac3d83c00050042100953907a5a000402c108129c458304001808805205304ec2e000482010408a07992a60005000210013d731b36000e02c528125e95acdc000819801264b2549f2000082010008874f62e30002022004810d8b3b1800040480091216bba648000c110810641d0cbbe8001013002447dc7cc64000004400018fb2bb574000408000821f0911ba0000015020063b0bcd18800380914a0075bee81c000501029000eb4ac1e8000802812011c511483400000482000366687ee000400a044046914bffc000600401408cf55563600040ac10831920cbb78000c090812231fd796300010100024062528c44000804000810c29e0fa000060004080)],
  [(96, 73, 2, 22, 2, 21, 0xee48bfea140840a090f6304e2c05003020227ac1810100021000043d26545180500608008e554009a020040c000f29e53f7060400502838ef006f02821010143c6b61a781900e04089e1ed9efc1080700084f0173323040420402877dab43882020020141be9a1de02900e04109dea2e3e40480702004e5611acc044038002270e62bff80a01c3001381e95cf42100e10109bd45314814080020905d6f957308042040486e47595c8302102814369b1731018100040a0b2eab46c1400002080564af27000412800046a7016c7052004082015042d0a40400418008a7b024440a80704044d39d4a6f0a0020504069843e998220142010348dd00a80400808001a2ba97d00200604004d0225fc1010000600027f7d7088520142820336e508240100a100019a56d62c0080500000caddf197084008404022977b8b8420142020300f2782804004080088065bf7c1400602084bf2d1ab50a003050425f8476b705201408202fa7f7d9420008101017c066ef40482502008bd066ce204413800265da57f3d03209c08132eb88e72c0400c18009747d0d3c0208004010361dac1f0a403850425ae1561902201400102d6731a181904a0409168c59ba600803080043442cc100440180022191fab9f80a01430002c8f9270c2000c1010962bda03c1080500080b01d016a040420002857bbda7982800030100af41e7dc2010010120573af3f6048050a000aa88a76806042010285469a98b84000020200a072ecf00500e08009502c06e6140000a08023321f390040384002514976940400100020289af2d10050020800043f1b93e0c8030a04421518ec70240385002506a601302801010102823e94ac09002140003958265014803020841c81e87905400860200df5ee4504000800210661aa8f4050061800832c55274140840209098096d4404412800244ae44ede03200c08110556245340010010020291893de0a0060c04493c59baf0a40185042092ddf9a81200c280103f10e19428100141201d306c5a00801080000e401d330a4008504006b34885050010082022ee31f142100610108176b34f608803080440a8d82c9050020602043dd62eb82a014301021e7767b809006040080dba6cf2040800a01006224090054028202042838ed503208c0813011333ca8090020400008494c1a0c8050a0408355f2f30104006008012aa0b600a0141000201063ef82010800121), (42, 75, 2, 22, 2, 21, 0x354e03b78048270200cea294260001006000089b76356d04200c002112fac3670024118100624ee6e0d8088230004c455c515a02000c001098678ae7a83201c2811308b865a6004118000620fa877e20a8070c044be4d85bd0190020408076de149805000808210ed58785a00413800065d38e93260880708044b8f563f3c1500618088713a5eee82800830110e0ba094b01400860001b62867b01080100080346fca7e014100080a068c57aac00821010042d155ca3a020420100859b4c26240c82102048318aff7e00900a040015f37361c82821030142b4b76a5a064028102056618a874048210200829afde47010100000a04fa399ca85000828210981208d1080010404212ebc08dc088210004825451194811002000804a1ca5248220042010093d57ca00804000048127820c0e040840a010a43cf33cc14100180a044e2edcb83200428100823b349e05001020220f8e5bde80a803040441ef5358500100e000093d9d8b5f010200080407a0e3bdc05400820200f3ed1f3200084080109e457d5dc0410818021)],
  [(96, 80, 2, 26, 5, 24, 0xf100cabe002042000021ecfc88e8280004008600e8ce1c86280006008600db977d68500004004500da1c202a002442000821d6011e0e202442000a21d52d3568280040008201d2d15a9e202006000620cb2f5a1e282402008a20cab52d80082400008820c04b6eb4402004000520ba45bbd0202444000e21ba35dbae282406008e20b79ff1ce282442008a21b619be94500044004501b2df3ffe080446008c01b0c892a6280042008201adf140b6002406000c20ad15cf34280044008601ace38f0a082446008c21ab94c6ac280400008a00aaf947ca202402000a20aadac720200444000e01a645cd70282404008e209f9a66264000020001009ea5b01a280446008e019ea45a422820420082219e989c3e4020060005209d7de14c302440004a219d3bf4220820020080209c30b8d82820440086219acfd47830204000422196af3a74300444004e0190337d64280444008e018f38d9d4202400000a208d1350f6080002008000865c2ba0202440000a217ff79100302404004e207dedf0a8280000008200762a3878282400008a2073adcd8808200400842071c076760820420080217024b30a0804020088006eb5b0c24000060005006d9afa9a2820460086216a6c5e86080442008801626ac7da280402008a00624f8af0080444008c0161ed0a56002446000c215db2621e0000460004015daf0e0a0020460004215b5039b840204400052157fd3a0208244200882156b06608280440008a0154ff6c7c202044000621537056a8300400004a004f150b662000060006004aac8fa42020400002214930410e282446008e2148295e12080006008400478ee5b620004600060141da52440800440084013b77ebe20800460084013b77e64c082444008c213b4108d4500040004101385083d4400044000501376214ca40204600052136e0551e40004200010132c502be202446000e2132768b18302044004621326fa85c3020040046202f9b20462800460086012dfce70e280406008e002bebbb9850200000412029527e64300404004e002792b4ee000446000c0123464b0a0824020088202303c962200406000e0022cf9db0202404000e2022a5e6aa2020460006212022409e0820060084201d69c7e83020000042201959fd945020040045201700d37a20200200022016bdc9ea202406000e20154f103e4000460005011404f54840000400050013a495bc5000000041000ed1886a200446000e010dba5170302400004a200c9952b208004200800108daa7bc28204000822107d1f23608204600842107985008200004000600001a7c68282440008a210016a3e4502044004521), (33, 83, 2, 26, 5, 24, 0x44a5549c43000400042015b3283920504000010440b3d4235a02091000220850a399b051410030043101fb5b051a2800020082003dfd7e43c5040040104407bf6537d8000018001000f7b9663a1410020043101df4033902020040006203894d3b30400088000c025f4eb7070209010023080b732ad1218000200230016b8bdf944020400001212d0977a0c10080c01180057a6ea320201100022004ac22c6f2180220002500940009462082406008c2027ea5de101040000100404ebb73720c001100118049d5928a6041022004210932e513c6402002000120253a5da48504888011c424a01d58e80010180030008f65022428102000209090c170de240204200012121826aaa010080801180042fc3ac5800801800108083218fd1140221004500902a7f3322020420002211f8c29388604888009c423dc23a4702081000200847a61d9761002020007000f1797098280404008e00)],
  [(96, 81, 2, 27, 2, 23, 0xc32a744700401a010800dffe655c8020050084002e6e7e1580108640420034cd9710e00842e0012018b581f0000005c014100c55d5cd580000500800020d0fe648000150010403058a649c00840a0012007e231a1d004002000800399326a480200f0084805c1ca7104000128050000dda8acdc0080380212016c56c6bc00420100080035d3a9bf00002400a00019d17d66c010018002400b4deb2040004a20080015a01c0000040240009202c63edb600013080201016268d35c01081c002400ad613d2400044a000240556c930f00021b010000a9ac032d00011080001014ca7d220000904010000a57e24a00004aa00820150f9f2e3000213000000a7e6c77c80210780848013e0c57dc01082c04200099747f000000c80082404967f1a5000042004000247fe2e68021018004001213882b400085c0004029014c58a0000340200014772ec9600000c01010022bd1f020021108004101127997b400094c010002839128200004ca0082404034b5a70042270009201fe26acf0021068084800fb30fe500009340504007d629e4a00044e0002403dc1a8ad0000160001009e0ef8898001078080800f05359d001004000200275f0f9d400041202000038ac80990042130008009c3eebe10000220020800dc642fec00097c0504026dbbd0040000480002403639aa320002190100009972dcae8001058080000c933babc00088c0000806456c36c00801802120031d9989000021500010098b6c37500012e80a0804c030d07c01004800200259fee8be0004ae0082012cb9ec1800401801080096592c6d8001338020900ae84ae0400093c05040054986ad800043a0202012913503100005200400094429e9600002c00a00049d8807840000380404004711651000841202100022d392f70000260001201160f93f80012580a0000822b241c0100580024023c69400e00003c0202011c9df8c500005a0140008e19fcc280003300209006f44c4b401088c00208036b192820004b60280011a215b3e00001c0101008cfcc4748020110004100649165800001300504003145c12e00008c00820018440a780042250009200a53794c80002b0020804506c36a4000088000080232e183600048e0082001032de5d00006200402007b06445800121802000037d65cc4000138050400163af38c00801002100008d84cc80042110008008462016b80200700848001e3f087400087c0404020bcb554400041a020200056189c8004215000900828c544f00012480a00000ec59cb400017805040205f9ebcc0004b202800101b8fdb500402600092000dc3db7800131802010003dd5bb4000048000002003d26b8000422000001), (9, 82, 2, 27, 2, 23, 0x37e54b30e00040e000200ce2ca5770001228020802f0a52186000406000000882dd30f80210f8084805db58398000040a000200726a493080210d8084005b109059000843a0212016b35e39c0000300020101959e9c3a00000c000200)],
  [(96, 77, 2, 27, 6, 20, 0xefa0320e81904102604f6de4e5100c820803027a73b234a02010408811d0c4be524260e000c21e054103d810060026006ca95c2d4008208110071ef717fa004004080038294f8ea4060e000421beccc8b1818060026045f095142c0c830013026e146f234044180018036dffcf5a0300c000c08a8aaf18e01104100600d39865fec040100100228500df180041040080337a9b1aa4240e000c209088e16981106002600c5acbcf040c8200130262d2b3ee48081c000841162070c503200204809835c05ee80900102004bd3b5d88801830001085d62b030604408009002e8b6028c432022008097380e27a21905100604b854d1b3004820801025c203856600c18008842de7ce425012082044096dd0473900906000204b69de512c09810012085b493291a00010408800cf5cf9730240c004c20601dbcd501306000610af14602b00c80080202568d8df048041c000802b18f930a4200e000c004a6013cc818040026042118cf08901818000085078c78b48241c00081282fb2aa20020c0004014060c11820901000004a0264e12c00830011004ff285c588240440001273a9d19b0100c00440836eeb039218030004041954a6a4900038001000c816baa4048180018405d56fbe2404060000202e823b6580102002000961d6e65104828801024ac4f16d60081800884055fb89d30120c0044092acb21b180302002010951d987a1048280010249589da840240800001243a254d84320200080921aaf119809020020049082fcfe90081800000483a233b48640c001012402c3ad04320a000c091f858422009001000048fad2c4480c83000302462a3e364060080010103108fb2200604000021185ba92d019020004048c1d496110802880300060d256d88601440181030660df04300a000c0817f005f6218011004040ab49625108828803004549a6b56064080090122a1513a303004004808142c44802180100040409e96a5a9090180020804cbfc61a0440040900223a581cc422022008011089d08d01302000410877143fb00880080200430ba6dd48240c00001217188d0a4320e000c090ab8e7cd218070006040536167940882081300428f0b07a0401040980010f0b05a4220e000c0107a9ebae2100110040002b3425a90881800200406dac3c48201c000810035651284100a00040801ab27822080510020400d5938b100028801000040ba3188041440080200a678744000220000000533510208010000040027a74f100808800004009e23648200c000010004f063441002200008), (4, 78, 2, 27, 6, 20, 0x967a2cb28010300010822a42b35b0260c004c218a28db0b40c02081302221694cca42606000821)],
  [(72, 68, 2, 18, 3, 18, 0xb6a9eb79082042012a3d1e3e22824620138537c04a2820200127faddc192824200137b6528332820620127b601f1008244201376654d4728046200374352d3b88101010264839fbe2800620025a0431b888041000358e68c0c08420104253ed55f88842110424b093bef0052011403fec52248052111403edbd32a2804200033dfe736d8050111003d7d7b750012421403c594d878802100423af07adf88521114236470af82854211033431645488501110232b411a308044200331aaa2412814201032e840c3c2840210022d5695a30810421022cd17dd68814101032b64326d8812521422abe1c7228106210229804497880052002293ea7c32014621012918d1b028002000228803b80800210040285ff0a58012101402737ede120106210026a6533820046200123a1d84328442100322cfd9a3885411103228ca5c22014201012250935d2024620111de742448802520421dda6f3a8812101421c24c7fb8840110021ba987e52010201001b453bf80812421421b26db818004100011ae4ed3d80541110119f240b1804211040194fe57680401100017c1743e08520114216a40fa488001000215cb4cce081442103157d786f200420001151f2e1288105210214708b3c8012521401288191e804411001126c72ab281020102115d518a8844110030f3dc3432054211010f1d86d42040210000eeb13d12850211020e6b22488010521000dd472118014521010becc80a8014101010a22311c20242001106d0c20e28146210305cdc4c420502110005975fe8204421001053c3c458002520400484dc4988145210303270850800052000020a0ee9880452003005dd89d800452001)],
  [(60, 78, 2, 23, 2, 23, 0xb2c2c5bd8821130442168f6f908aa0844c110876adea63ca0210b10420d8a65bf8aa0842041087540f9fd1a8210c50421d3cbba1f6a0842c410874cfb87c4a8010c50401d33d0cffea08020400874bbfd315a8010810401d264de1e6a0002c4000745f695dc88211004421517b998daa0803140087455681cea8000810001d14d88336a000314000741771604a8200b10021cc8b834f6a084401108731645f53822104404224b4409662a0042c410072a8ccb22a0210440420ca9491e7220804c100852700a54fa0211304420c975b595e80042c410032477326ba8200740021c913b9a5a800420410032389f26ba0010c50400c7759883e808420410831ac99af8a8210440421c68be6326a0804c1008718b7c26082210c50422458337a3a20841101085143663c688200440021443cec462080420410090f262bf9a8200f50021c3b0ebd0a088440110890e6372f920211004420835e782c6088420410890bf08b87a0211004420c2a6a1e9ea08011000870999b5c782010c5040241ed7521c8084204108206fc3be388200c5002141bc9a8ca8084314108306db309f28210810421818922e16a0804010087061437ee8820100402141703a8dca084110108604f17ca30821100442101388bbc22084314108504368b7988000c500014109a4a5a200431410050386229ba8210740421c07a553a4a08440110860020efdf280108104018007ba06ca0804010086001b086728200810021800662ae020804010084000f7c4d28200c500218002c1768a000204000600081eef28200440021800183a0080042041002)],
  [(58, 66, 2, 18, 7, 15, 0x92979daac20080041dce253a90906001373c8d81cc2458804dabaa2c2f0902001256bebfe90204080414ef6a421091220124796481440458800d120278cf011220023f694f41820508044f8dc9cec0054200537c85585020900064db5415830806001133c8b0bd80410000ca651c8ae01142003279be05f82100005099cfbd5b00162001245939394205880447cb9d5f4084400151bd3bd8382410004c6d40369a0910201219b2ce31805000018636261af010600031895144d4040800085cca87f40900001213ea400f8054080184df79e8a085020140f333fe202540805834142ddf081220100b0160e302450804c2b89913a0954201709e7741800510001c2250b9fa0944001706a0c4cc00550801c1877ad170846001505f8c89682500005815d67589082600190407ca784215880540f2ffd0d0956201702ea79220215080540b7ce9eb0146000701fdd68700440800805fcb9bb09460017016e629c40018000402b59cb1082200180082d2f7c0048800001380d2709420016002ae585425488058003efdf708522014000c22b1405488018002bad1908420014000a7105c00980024002591a30142000600059536c0158801400134ac5005220040000b8b640108001000028bd70156200700007cb4c0088002000001db100460005)],
  [(36, 82, 2, 27, 4, 25, 0xce72b3e6280a4302022560f418170a0290c0808157845293e28024002002552e71108820210c0008943e702992080a430202250b9e7f7a8a0290008089528d2e232200a4302022149e8731f8a0010c00009521eb72a220024302002147c48e220a009000800151cd1b2f4200a4302020146ae183c8a0090c08009518731ca228084300022544595b6b02029000808140e032f64280a4002020542cede1708009000800050b3ada88200a4002020142c68f1082029000808940ae08c66200a4002022142ad93b088009000800850a866bd0080a43020205024bf02b800290c08088400d5688028024302000540213291000290c0808040052fc7c2002430200014011764f820010c0000940042fbde080240020025000b5a43020090c080014002d6008000243020001000615ee820090c080094000997fe0002430200210000321f800290008088400001cda00024002002100000139000090008000400000378080240020005000000ba0002900080804)],
  [(34, 82, 2, 27, 2, 23, 0xf8db4e388001020006006b371eb0220840c0018054b193bd300200b800200123f14a7a2000000010043fbeb8258800020006010fe23ea062084040010053afe28678820010004010bd2142b02004080008051b7e0a1500210b800200468e1940620842e0018051744097b88000a8006010550832e220802e0018041505402100010a800200453c3822a00802e001800129188f780010a80060044697987a20042a00180510e0b4c68001088004004423d74d42084260000050f4e499f80210b80060043a60473a2084260010050de20f4208210b8002014315b33fe2080260010040a29c7bd08010a800201415232b4600002a00180004dd1e0888010200060140ea75de620042200100503a9d594880008800401006cbf80820002a00080401a5ecab08200b800201002454f0e20040000100500302457882003000601000aff45820802600000400214ca00801088000014002b5bd4200022000004)],
  [(30, 77, 2, 23, 7, 22, 0x2f13048470204580210f3766ec2981002c010866cedc3d9c080060080331173d89a0400b004209420e52df0000500210c7baa2a49800228010873b9a6c3dc00104008039dc2d2f420408b00420ceba7a9b60200580010c6f07746701120c000173580aeb2c081060080392b43b1a404003000018918036520220580012c41abe3d101120400015205df254440010008440fe82e1bc0048a00025c7a236a6a0004500010e36bb15b2890024010881afd9891800014000430b5a9acb60000200401850317dd20220080002828079f4d01020c000070e8ab7448088060000b06d0ded44044090002502caa72960224580012e128477328802200108904d364b08081160004382560b4ba2408900422409189cba0224480012a02beec7700102800096)],
  [(29, 70, 2, 16, 3, 23, 0x3f75665b2120811609dafd7f7a808204182710633cc20a0818609a2f5044c040100408284cdbd6c0a001840380414891028002000d44829fda10040122034db505c8002041820d0cb84841004114222e06f213048004500cb2ade48a0808186082a4301b50200061008a340c6841204010232865c4ff040100408895627c5a120801209243af285028102008c8d217c4210041162021457e7a8481045884802d54c21204012211ed1ab35028106108c73a5d0bc100011402172a56fe04810040845247add21008012080818d5a0840204582019b176b8120411421066146d1020106108811b3fd5c08040802201e9e73604010450800648216c120411423)],
  [(29, 74, 2, 21, 6, 21, 0x22af3bf6a4881301c095357db4112204c030254a7e239a0881101808454b1cdd30204823025117ef60e48811018094296753832204c230250081c9562881101848391c790f82200c05020bc0794ee0881301c082ecab13e82200404020ac7ecc24c8803084092863ae6b92004c070049e7258104801300c012099af3e8a200404120745c12fe48801010091c6a939c32000c2100466dffe024800301401190696b520204823020559aaa2cc801308c0112ae09c322200c210203cba50f648803014090bc395a922004c230002afbd8ba080030140009e179b402204c030201236d1362080001048038a128e22204c230200cf04cc20801301c0002b6429188204006120000c903c0801300c00)],
  [(27, 75, 2, 21, 7, 22, 0x10ea88e700012102800565044c930044084404293c643120088408809505b85ac80110a100129ec030d1001214280052a9583c3004018042423078c9ce00883088483ec3dfba4010040109074e86af300021420004c2f301770044284404983cdf59400405020012e4ff14bc0010a1100252d67e1700200c00120924b7071004410442410644b1ba00880088081873e55d400104110802fe0adc500220c2012055d3dc5700041844200a804fa1a00084088011216f70740000401080207f680e0022082012040a85ece004408400407e311446000030084007b505dc400100110000c66a4260022102002415527f340044004004016093ec60008108800)],
  [(27, 75, 3, 23, 5, 23, 0x1a7bd298402013108041833d238414010410421fc1671600804c43000329dde700d00108410263de1ed81a00210c204c6659210240042180098cc91dc0480084200129ae08e40100108600047307140120131080048cf7a73024026218008d24917080804c4200416bcddca090010840222c1a8b241a0021082442b784b0824026210088519ae6a02800843080012455620000988002001eaef4800013104000038f68682002620008805d126004004c40001009b26740400108210000cc9db810013104004015f07082000420008802bbcfa040008410010052d4c1000098800080006c13018002100204000b43c8300042004880015fe206000841081)],
  [(26, 72, 3, 22, 5, 20, 0xc5dd394a4a40684421bcb9b9230208495001aab7d7890a406050218406c4144a406044217f9095464840680421703876d8484060042162116a370a40685021528b3b7f0a086950014cad49764a0869440146e81268420841440141f0bba4404040042137d50f17000849100137886732424048442135b9aa4508406010212a4399144a0861440127803c4a420849440121a1767b08086910011a289c644240404421196ce943080068100118d632cf0a0068500113d7651308406810210ed65a22404048042101175cc2480869040100cfe2d64008490401002af7884008410401000667384808610401)],
  [(25, 66, 2, 18, 2, 16, 0x223efa715286201236bbab93048180048d889b0e89282640234d2d89b24a119040d15053a91282200233f64fa9f0a0990084f0b025c12064412335b01c954a199048cc9aa6f01092280222cd5901b8a0990884b315d2e2282202212761ec2f4209900888f57354e2922822120bc577442119040881d05b9d292280231ebe00c142199048870106404282200211b3ca3290a119040462e152f8286201211225c9560a48a0084465ae1f4286641210dc3e3100219904800bb1cd612120802300f5547b60111050802ec7f0e08220220)],
  [(25, 77, 2, 22, 3, 24, 0x1b99f165402c00600508a9a3a3e081600300284bdd6fad200b000001421b5b5ca0209004c1101280bb65da048006080483660c1fa822003042009af283b200d001809400d5f3b45a06800c04a024fcadde50540000a4012741438081a0000128092c826018040018081008c5437ca05800000a1240588a95024000005011ae5f660818003010808d26cb53404001808004556eecc20a800c14802294ece6a0500060a04013b1e7b8826003042048963075700c0018084003f04342a04800c00a02137686ca03000602140081c7e8a82601304604834c478d812009822120143103a202800c0480207c59bb10500060a001)],
  [(23, 67, 2, 19, 12, 17, 0x12247ba824023109019e775bdc800620202b41e6288909e5201431ebb220413c0420801716c6282790844f9397324500f20089620a6b789092520126207bd90413c84203792f6862407940046b4236b4084f29000d04863d8809e420119ae0a481403c002229743b12080790040513306b48840292009ed9e4f8109252000a8955a30203ca0001165fa6c080780040213ec694400f2000840b726e9108c5240016e72341413c042200dc6396240494004005ab40c8800282000098eb29100c5040)],
  [(22, 60, 2, 15, 2, 12, 0x919f05c5c44cc018228a660044c801625a6216084c84051062e08c48c4213b381caa409052033628cc94440c012ed4c82644ccc21237341234480421221177d7c4c0c2121b185f0449c5211ac6b5a3c01050011ab18eec09c5200ee5291dc4905210e6d4dd544105010e52090cc01c5000b4eac5cc1125000abdd924c41c5010884713f451e501043d7f94c50e40102d7128ec512501020a811784cc82100cdacc1411e500)],
  [(22, 73, 2, 26, 11, 16, 0x3b16684e90600009081d6ea06fc8c26008a01a47ae2cc4611004400c224d8f020c10012901ea9064a41844014002ea5cae600c2600820172027de64483000520365f9cd78340802810185a514910448009402c279f4fa090200204045f280b241020025001f361f8d20880012004df94c6f418040140006a7cb57e02200060012a7b57d646010044001535748123418022900a1018a91180c0114004e054b908d0200884023797ebd01000030000cc9539f00c1001090041d2344c060000c0801ccbeda40c22008001)],
  [(21, 66, 2, 23, 2, 13, 0x36588e04942ca4400c175895220b210102fbcbd20d02ca4001af28d78f50b2910050f5f8f21028a400040962cc450a291000ff25df7d424a04013d33ec6550a291004d0a825b5028a40012ac1cc36409280000a45b5ae5420a04011f02d12f10b21100476aa6d39424a04001d10280b1092010045cf4751d024a000114997ea420a210100504b4195020a00010922106e209200100184ff64902ca40000080f9fc208200100001dd4e1420a0400)],
  [(21, 71, 2, 23, 11, 17, 0x53fa97cf80214020107a99c769214380402e8a51a75e4285008054f5edd54c81040100b1c86a0239081c020073876942d210280400a5238581a428200805c9984017c010e0100911240abe902000201420e7bc23210100400e3e8b383200070080086a54b694050e010098828109480a14020110b84149b210000400a16c4fb9602050080042d515d3c040e0100184e076fe902140201408fc61eb204380402c06a2d55a428000805403e256d4800a0100200712de59001c02006)],
  [(19, 86, 2, 27, 2, 27, 0x370431e8a0004006000000a43e6ac68003001800080257ffc03a000c02e001201887c6a0b80010038004001ec0c346a00040260000017919e57600030030004801b1c3b12e000c02600020149226dcc000400240040011d5656b2000c00e001200405e5e6400030090000804f4d7b848001002900100138b6bb7180000088000004d47a77cc000c02c001201342a9aef00030010000800ca14ed4c0010021000001264db6dd800200a800480491ca9cde00080220002011ef42c7b800100b800400403efbdda000002a001001)],
  [(17, 69, 2, 22, 2, 15, 0x1a812737b800e04408b2475c58c02702604574d4382a4138120260fda068b2014008129d9f3270104e048014893f689480500004a39d017a64100030250f34b98b209c09812877fd107100e0440140a312a5c022026041e435550a41101202491158a7b201c0881246798e8d104e04c01187b91aec822026048a5b7a2cc4238190042f467e28211c0c00211bc9935008e06400)],
  [(15, 76, 5, 24, 6, 21, 0xa350acd7064000209016072ccba660018811014a19247d0640182090147485a0c664018a11013c9eb7364640182110134a663042600188010120155bff264018a09011d967b4e564002211011d11319c264018a01011cca35b116400220901199334df260018809011637b430664000a11010e4962e44600180110109103a4416400220101082b878b264000a0901)],
  [(14, 80, 2, 25, 3, 24, 0xfe91c07e0002a1000101b46b01e70000a04001018630a37500008240200170c28ff62000820020816eb8594a2002810000815ff860592000024020805d17a52020020900088053a1b7ef200088400881385e42062002890008812a9a949e00028900080129aadfdf0000a2402101162d9b9b200082402081149148192000084008800ff250d2200201000080)],
  [(14, 73, 2, 21, 3, 22, 0x25910d9ea110060200ef0590a8c08803010065642237c80c0181002a81f7c0f40400c0800d21265ff2110060200a78730b8d080030100332b8461a004018000310b77d6400600c0801078590292010060000a1b5b85d008803010040d27341280c01810038157ac7b40200c0001c01772558030060400c005b2ea00080300004)],
  [(14, 73, 3, 22, 3, 22, 0x3744b60512200940883a4e74b7a91006a04419d56d5654800340220cad8d18624441291105d9958d502220948082c8bb705801104a40014a4ba9d548083422209df8a75e24001201104cfc727a122008408826730c65881104a440132f76de84808202220849886b2040412101041f83479120209088820001d61881004a0401)],
  [(13, 72, 5, 19, 6, 22, 0xa3a9d5b110420400298cfc0f8b001204080876b158cd10020c0019765375d9005204082872c6f58300020c001866b43a6f1002040009622d8cc900120c081852c06a6300100808184af1bc2310120c0819444873f71000080019434b245110120408093bff1fb51010080819214d08af1052040829)],
  [(12, 74, 2, 21, 5, 20, 0x81784a3460008402200bbfea8f980001000802d6d7352e0008c022048d6d31e18000300081168c400de0001c002243aa0247d00027008090dd1ba44c00094020202d258db700023008010a8634eb600094022202334ccaf8000500088080a29e460009c022241a1e6cb90002100800)],
  [(12, 74, 2, 21, 7, 21, 0x80ba254600018c04005a96f6432008630140961ade1a180010c050017b7b6560000430100047e051cb00210c04020e84e009400863010092d27dce380018c05004b15b2782008430140823f0ee91802184010248f9df08e00041004001f7b244b80018401004118043c20084100408)],
  [(12, 74, 3, 22, 2, 21, 0x8bd5ab6908c2184c205cccbf16823084130816611617d0842084420160c3d33c21086110814fbc53df004208042010dd9b50c0308603081353060b308c2084c200b0daf3b42900615001241b9ddf024018140047535241403082030801305e385004218042040f5d36b02308013080)],
  [(12, 74, 5, 22, 6, 22, 0xb386998e06001908801e04a29e908006402205dc9772e22001900805439ea7f898006422013e79bd7266001908884a1d77e89800044022127d7506e6400110888496c28b79180064222020c87336620019008847fc3a0a890004422010fafb4560200190080030a70a344804221004)],
  [(11, 76, 3, 23, 3, 23, 0xc7cc2ffe01810803281bad5752a010108012815996c35201104c0120945b5a7ce008108022813062594e01100c0120126a426e202100c002111e526d2a020108002911a7a10e202008804211151bf47a02810802291124722ba0001080028102dc00ba02900c02211)],
  [(10, 68, 5, 19, 6, 20, 0xb0d81d3c4a0420909951eba5d0a044090962b42f044204a098141c599ed0804408093d95426442042090106bf2f7c4a002090805b7a6a440042080102575b8c4004a08810126110c48042080900000ecc480020808)],
  [(10, 68, 2, 26, 2, 12, 0xee87fc4e216000881b4491c58252000021ab2af1e4256000821592c467601200008048f726b22560008a141b617fa0160008803e762abe0520000a0263f52d22520000a115641c6621200008106b0fbc60560008a0)],
  [(10, 75, 3, 24, 6, 21, 0x379d1d808a20440045252d875790440180082160241d26088010010409fe1a75c5100200209125f6397882080004921b98d12d104080008a4229c9922088110011401cf04c4c11026002284145ff588800800048200bd056504009800881)],
  [(10, 77, 3, 23, 6, 23, 0x2f3d3f2606200144420151cbd08221000a2200133cecb6a18900519080193477d10848028c8000aaa5714482800418002530b80d450c0040c1002931bed9109005190008f25074f9048028d00046d180bac404010640022e4c2bbe01200a30001)],
  [(9, 76, 2, 22, 6, 23, 0xfa600bc5001106005087fc8b1eb201106005096fea18a520100400509543c82670010040050846856de52001060050143533a38040902008403054b37d0001060050025fff644041902008481046599920000400501)],
  [(9, 65, 3, 16, 5, 17, 0x168aade870911b081ae0e75dc8489d850bb152349c240ec2818b62a7d212036100c4fcdc6b0912a0a157f18c958089d810a53d15044044a8085040cff2202076040460fd23a091330a1)],
  [(8, 67, 2, 22, 2, 15, 0xb68c20e8211404002f5f5c704422809005b7f8b170843010082ac074da108e0201130a8bb582104040005cd4b55c4218090406932fac8841012000a1d7949108e02411)],
  [(8, 65, 2, 15, 5, 19, 0xf2c029830240645075bba0b1012030283ad73d16c01109003045fd68a0088c8817c2231d602446050baa211d88122322859cd4cc2409009040468c945a04884821)],
  [(8, 60, 2, 12, 8, 18, 0xd9ae6a9602008107b91323a0081803432b16d600018023ff2538e02818133805c80a02808113154dd5e0181823119ecc22010182207b3d6f20201812)],
  [(8, 75, 3, 23, 3, 23, 0x94c3c7cc0c0440480a3094a1b78180230201451396aef0301000202896dc1dea0202800c0412c3def2c0c0500180a254ef4858100a00300448806591020110120088748aace06020c04051)],
  [(7, 55, 2, 18, 2, 5, 0x1dd36ef58580041619ef2e6f000999e99be0d200023370177b3400025513e3e55800488203ae6ed00018f1928181e0011)],
  [(7, 70, 2, 17, 3, 22, 0x2faa0ec8400091010288f5dc3b00024c040e148b6d7c0008301017fcbfcb50002040401b7fe6e3c0001300035d4638bd00000c0004f50fc2b4000110002)],
  [(7, 70, 2, 26, 2, 12, 0x26df43d22014040201880125e9804010000580f3e4be206040200493f0d6088581008050f3b92ca2020400000dee9ab480101008000dff79f6212040001)],
  [(7, 71, 2, 18, 5, 22, 0x19ea154da000018000601fc38040002102002148eb98900006400134eb48032000048000683217ca4001091000ad227d348002322009104579c8000460401)],
  [(7, 59, 5, 9, 5, 19, 0x194ee11b40140c25f0f3827002808424acfde7804001817905e4500a06321da569200100824279ac6fc02010c8086455f8050118)],
  [(7, 65, 3, 24, 15, 12, 0x75a836dcc2e0c0026f01e99860706001122f99b290a810081670ff9c085c18000af5e37a882c0c00252d3c8e2a1706800250eb0da509824001)],
  [(7, 73, 6, 23, 8, 19, 0x421081fd50412106810e9a20ae08814880042739e7da90104801a0423303871220522101091461809010290000848398423282010834002d48e68a040a402021)],
  [(7, 65, 6, 19, 7, 19, 0x5b950d1490232028ab83df4a48501214406c24c520280902202abb2110046401080d379d89020202840567c2c40101004202907662408c80a1)],
  [(6, 57, 2, 11, 3, 18, 0x2a827dc64001a0303b50e5a000d09731f2a18008681398f89c4804340d2c268070001a10849847d0000d00)],
  [(6, 74, 2, 23, 9, 19, 0x9256e7471000b080005b52fca364402c244014779b2ea9000b081004d7a5abee0002c0040127db49708100b01100479d79d104402c24001)],
  [(6, 58, 2, 16, 9, 13, 0xee309a5c24610260002a930818408005a04ec44610140165655101840400541c54402001000003b11108005)],
  [(6, 69, 5, 20, 2, 17, 0x235e559ce820781006eec3c6414123c090358d1f8c3a011e0081a75b3ed3d08870440423a4abc202470120608673583002380103)],
  [(6, 66, 9, 20, 11, 16, 0x9d635b608ca2242053389ba8832891081476b0e6c8ca6242443057f6c2228890010bfd096488a62404400af0ad822891001)],
  [(5, 61, 2, 15, 2, 15, 0x13eae8d60411081245b4d2ef20084019ecd7bd79047204cb1e2bafc822102641b9c36a4090823)],
  [(5, 78, 3, 24, 3, 24, 0x22de18be8080a08080813211c3010004800800249b7dfb382000940812026df1f920800050200807ea41af820021408021)],
  [(5, 78, 3, 25, 3, 25, 0x38a30bf2020103004011b11017f808000c00004564b307a0280030000910b6519580a008c0402440000676008003000081)],
  [(5, 74, 5, 22, 6, 22, 0x3f06356a800306422009e1a57160008190080195af1ca800286402013c13063e00061108804cd2596880038642201)],
  [(4, 72, 2, 25, 10, 16, 0xaa9db6d820224001015a55d1ce023100008130a7fc0b02008000800c3c0abd0220800081)],
  [(4, 73, 3, 24, 10, 18, 0xc0a888131046405040cec5efdd4801488800555d1b854401900410200db16122005822001)],
  [(3, 51, 2, 10, 2, 10, 0x1476be6712108d7b133cca80211251f68188201)],
  [(3, 60, 2, 17, 2, 13, 0xad668bf6c010201527fc66280312000848e1c6c031201)],
  [(3, 70, 2, 21, 5, 20, 0x3128274204403040017bffa7a41000c0000d00f58730440304003)],
  [(3, 69, 2, 21, 2, 18, 0x7c40a40e8880c060055d415c58440603080311a46e4220001840)],
  [(3, 67, 2, 21, 10, 17, 0x1295e4f2800ac080153a64ddd000580002a1110764002b02004)],
  [(3, 80, 2, 25, 2, 25, 0xc3772c7e0422100211096c1f0d3204220300110934f2d7de042200001109)],
  [(3, 76, 3, 22, 5, 24, 0x8a963ed430400610801874f9f5a200008090017f76cada20000e09001)],
  [(3, 75, 5, 23, 5, 23, 0x12bb83b6882013100425ddd47db1044060088499c56c3620800c00109)],
  [(3, 67, 9, 20, 9, 20, 0x1614f30e2440604444511307c48880488880ad25d8111009101)],
  [(3, 63, 12, 17, 12, 17, 0x1a793063c011c108ebb2a2a984034211d3a907bf08028421)],
  [(2, 82, 2, 26, 2, 26, 0xcda801e200200080004014f7a1218008006000101)],
  [(2, 62, 2, 18, 3, 13, 0xb885f307002810013ea41c0c00e0401)],
  [(2, 55, 2, 16, 5, 12, 0x2288c98c14c011c4266b88098022)],
  [(2, 68, 2, 26, 12, 12, 0xa49a1c9a1060004013c58ac38106000001)],
  [(2, 70, 2, 23, 11, 16, 0xb1433d49021502000e40fd7288085c08009)],
  [(2, 73, 3, 20, 6, 23, 0x2a48f30180400300802329248348200180441)],
  [(2, 61, 4, 23, 8, 18, 0x2760ee20018800022f6f61010c00005)],
  [(2, 70, 7, 21, 8, 19, 0xc62e295e08809010851f050cf40c0300128)],
  [(2, 49, 16, 10, 2, 10, 0x234f6e750ac52014ed4085228)],
  [(1, 45, 2, 10, 2, 3, 0x1cd3774a7601)],
  [(1, 77, 2, 23, 2, 25, 0x155accc6800000c00001)],
  [(1, 62, 7, 19, 10, 14, 0x388457c7130c4205)],
  [(1, 82, 2, 26, 3, 26, 0x26754d518000006000001)],
  [(1, 56, 2, 13, 6, 14, 0xd9a5bcd4083801)],
  [(1, 45, 3, 8, 5, 9, 0x1cd1d76781a1)],
  [(1, 50, 3, 13, 12, 5, 0x2039c02973021)],
  [(1, 72, 5, 20, 5, 22, 0xd60dbc42400a190111)],
  [(1, 73, 2, 25, 10, 17, 0x11ee47a820023001001)],
  [(1, 77, 2, 27, 4, 25, 0x146b124800110c000085)],
  [(1, 64, 2, 25, 13, 10, 0xc9d42ee407001001)],
  [(1, 52, 2, 14, 17, 9, 0xa64c2ec40e101)],
  [(1, 67, 2, 26, 7, 12, 0x79444e56086020001)],
  [(1, 82, 2, 26, 3, 26, 0x2e84c19c8000046020001)],
  [(1, 69, 3, 24, 11, 15, 0x113a7835c0a1810801)],
  [(1, 50, 4, 4, 1, 25, 0x2bb9910000019)],
  [(1, 64, 4, 21, 9, 16, 0xd26466b201320021)],
  [(1, 66, 5, 21, 5, 21, 0x2d2fac68001310003)],
  [(1, 70, 5, 24, 12, 17, 0x2c4503418021801081)],
  [(1, 54, 7, 19, 7, 15, 0x3ef5ae402c4801)],
  [(1, 45, 7, 8, 0, 13, 0x106551500181)],
  [(1, 65, 7, 22, 7, 19, 0x12469131001640401)],
  [(1, 59, 12, 16, 11, 18, 0x5bc513a40418089)],
  [(1, 65, 10, 18, 10, 18, 0x11a8bda5808862021)]]

end SnailCoordinates

namespace SnailCoordinates

private def rowChunks : List (List CertificateRow) :=
  (singletonRows.map singletonRow) ::
    (chunkedMotions.zip rowBlocks).flatMap (fun (_, blocks) => blocks.map unpackRows)

private def allRows : List CertificateRow := rowChunks.flatten

private def rowCheck : Bool :=
  (chunkedMotions.zip rowBlocks).all fun (m, blocks) =>
    blocks.all fun block => (unpackRows block).all (rowFits m)

private theorem allRows_valid (hrow : rowCheck = true)
    (hmotions : chunkedMotions.all motionCheck = true) (r : CertificateRow) (hr : r ∈ allRows) :
    BoundedRow r ∧ Congruent (proofRow r) := by
  obtain ⟨batch, hb, hr⟩ := List.mem_flatten.1 hr
  rcases List.mem_cons.1 hb with h | h
  · subst batch
    obtain ⟨p, _, rfl⟩ := List.mem_map.1 hr
    exact ⟨singletonRow_bounded p, singletonRow_congr p⟩
  · obtain ⟨⟨m, blocks⟩, hm, hbatch⟩ := List.mem_flatMap.1 h
    obtain ⟨block, hblock, rfl⟩ := List.mem_map.1 hbatch
    have hg := List.all_eq_true.1 hrow (m, blocks) hm
    have hb := List.all_eq_true.1 hg block hblock
    have h := List.all_eq_true.1 hb r hr
    have ha := List.all_eq_true.1 hmotions m (List.of_mem_zip hm).1
    exact ⟨rowFits_bounded m r h, rowFits_congr m ha r h⟩

private def denominator : ℤ := 1000000018

private def numerator : ℤ := 4000716307

private def termBlocks : List UnitDistancePacked.Terms :=
  [(0, denominator), (1, -numerator)] :: rowChunks.map (·.flatMap rowTerms)

private theorem flatten_terms (chunks : List (List CertificateRow)) :
    (chunks.map (·.flatMap rowTerms)).flatten = chunks.flatten.flatMap rowTerms := by
  induction chunks with
  | nil => rfl
  | cons rs chunks ih =>
    simp only [List.map_cons, List.flatten_cons, List.flatMap_append, ih]

private theorem termBlocks_eq :
    termBlocks.flatten = completeTerms denominator numerator allRows := by
  rw [termBlocks, List.flatten_cons, flatten_terms]
  rfl

private def edgeMasks : Array ℕ :=
  #[16, 16, 256, 2080, 35, 32920, 4605312, 8421728, 528580, 1024, 34744896, 67142664,
    256, 33588224, 163904, 335571104, 134348800, 83008, 5767232, 262400, 33817600,
    12582912, 44302400, 274727040, 100663296, 223355904, 453019648, 100728832, 75530240]

private def adj (v : ℕ) : ℕ := edgeMasks[v]?.getD 0

private theorem adj_fin_check :
    (List.range 29).all (fun i => adj i == edgeMask i) = true := by decide +kernel

private theorem adj_eq : adj = edgeMask := by
  funext i
  by_cases hi : i < 29
  · exact beq_iff_eq.1 (List.all_eq_true.1 adj_fin_check i (List.mem_range.2 hi))
  · have hlen : edgeMasks.size ≤ i := Nat.le_of_not_gt hi
    have hz : adj i = 0 := by simp [adj, Array.getElem?_eq_none hlen]
    rw [hz]
    apply Nat.eq_of_testBit_eq
    intro j
    cases e : (edgeMask i).testBit j
    · simp
    · obtain ⟨a, _, hai, _, _⟩ := edgeMask_dist e
      exact False.elim (hi (hai ▸ a.isLt))

private theorem mass_flatten (blocks : List UnitDistancePacked.Terms) :
    UnitDistancePacked.totalMass blocks.flatten =
      (blocks.map UnitDistancePacked.totalMass).sum := by
  induction blocks with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, List.flatten_cons, List.sum_cons]
    have hr : UnitDistancePacked.totalMass (row ++ rows.flatten) =
        UnitDistancePacked.totalMass row + UnitDistancePacked.totalMass rows.flatten := by
      simp [UnitDistancePacked.totalMass]
    rw [hr, ih]

private abbrev MassBound : Prop :=
  (termBlocks.map UnitDistancePacked.totalMass).sum < 2^44

private abbrev Good (free : List ℕ) (fixed : ℕ) : Prop :=
  UnitDistancePacked.NonnegativeOn adj free fixed termBlocks.flatten

private theorem checked_leaf (hm : MassBound) (free : List ℕ) (fixed : ℕ)
    (hlen : free.length ≤ 15)
    (h : UnitDistancePacked.checkProjected 64 adj free fixed termBlocks = true) : Good free fixed := by
  apply UnitDistancePacked.checkProjected_sound (by decide) adj free fixed termBlocks _ h
  rw [mass_flatten]
  calc
    _ < 2^44 * 2^free.length := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)
    _ ≤ 2^44 * 2^15 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 0 < 2) hlen)
    _ < 2^(64-1) := by decide

private theorem checked_branch (free : List ℕ) (fixed v : ℕ) {lf rf : List ℕ} {lk rk : ℕ}
    (left : Good lf lk) (right : Good rf rk)
    (hl : (UnitDistancePacked.omitVertex free v, UnitDistancePacked.exclude fixed v) = (lf, lk))
    (hr : (UnitDistancePacked.omitNeighbors adj free v,
      UnitDistancePacked.includeVertex adj fixed v) = (rf, rk)) : Good free fixed := by
  have hlf : UnitDistancePacked.omitVertex free v = lf := congrArg Prod.fst hl
  have hlk : UnitDistancePacked.exclude fixed v = lk := congrArg Prod.snd hl
  have hrf : UnitDistancePacked.omitNeighbors adj free v = rf := congrArg Prod.fst hr
  have hrk : UnitDistancePacked.includeVertex adj fixed v = rk := congrArg Prod.snd hr
  apply UnitDistancePacked.nonnegative_branch adj free fixed v termBlocks.flatten
  · rw [hlf, hlk]
    exact left
  · rw [hrf, hrk]
    exact right

private theorem finish (hrow : rowCheck = true) (hmotions : chunkedMotions.all motionCheck = true)
    (hroot : Good (List.range 29) 0) : OMA.R_Erdos1070_erdos_1070_parts_ii_R1.H1 := by
  refine certificate_sound denominator numerator allRows
    (fun r hr => (allRows_valid hrow hmotions r hr).1)
    (fun r hr => (allRows_valid hrow hmotions r hr).2) ?_ (by decide) (by decide)
  intro I hb hi
  rw [← termBlocks_eq]
  exact UnitDistancePacked.nonnegative_unconstrained adj 29 termBlocks.flatten hroot I
    (adj_eq.symm ▸ hi) hb

end SnailCoordinates

namespace SnailCoordinates

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def rowAudit : PLift (rowCheck = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def massAudit : PLift MassBound := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a0 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 22, 24, 27, 28] 0 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n0 : Good [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 22, 24, 27, 28] 0 :=
  checked_leaf massAudit.down _ _ (by decide) a0.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a1 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 24, 27, 28] 2097152 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n1 : Good [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 24, 27, 28] 2097152 :=
  checked_leaf massAudit.down _ _ (by decide) a1.down

private theorem j0 : Good [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 7, 9, 11, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 0 21 n0 n1 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a2 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 11, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16384 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n2 : Good [0, 1, 2, 7, 9, 11, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16384 :=
  checked_leaf massAudit.down _ _ (by decide) a2.down

private theorem j1 : Good [0, 1, 2, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 0 14 j0 n2 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a3 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 11, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 32 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n3 : Good [0, 1, 2, 9, 11, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 32 :=
  checked_leaf massAudit.down _ _ (by decide) a3.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a4 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 11, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16416 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n4 : Good [0, 1, 2, 9, 11, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16416 :=
  checked_leaf massAudit.down _ _ (by decide) a4.down

private theorem j2 : Good [0, 1, 2, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 32 :=
  checked_branch [0, 1, 2, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 32 14 n3 n4 (by decide +kernel) (by decide +kernel)

private theorem j3 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 0 5 j1 j2 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a5 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65536 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n5 : Good [0, 1, 2, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65536 :=
  checked_leaf massAudit.down _ _ (by decide) a5.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a6 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65568 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n6 : Good [0, 1, 2, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65568 :=
  checked_leaf massAudit.down _ _ (by decide) a6.down

private theorem j4 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65536 :=
  checked_branch [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65536 5 n5 n6 (by decide +kernel) (by decide +kernel)

private theorem j5 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 0 16 j3 j4 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a7 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 8 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n7 : Good [0, 1, 2, 7, 9, 12, 13, 17, 19, 20, 21, 22, 24, 27, 28] 8 :=
  checked_leaf massAudit.down _ _ (by decide) a7.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a8 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16392 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n8 : Good [0, 1, 2, 7, 9, 12, 13, 19, 20, 21, 22, 24, 27, 28] 16392 :=
  checked_leaf massAudit.down _ _ (by decide) a8.down

private theorem j6 : Good [0, 1, 2, 7, 9, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 8 :=
  checked_branch [0, 1, 2, 7, 9, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 8 14 n7 n8 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a9 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65544 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n9 : Good [0, 1, 2, 7, 9, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65544 :=
  checked_leaf massAudit.down _ _ (by decide) a9.down

private theorem j7 : Good [0, 1, 2, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 8 :=
  checked_branch [0, 1, 2, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 8 16 j6 n9 (by decide +kernel) (by decide +kernel)

private theorem j8 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 0 3 j5 j7 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a10 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 17, 21, 24, 27, 28] 262144 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n10 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 17, 21, 24, 27, 28] 262144 :=
  checked_leaf massAudit.down _ _ (by decide) a10.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a11 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 21, 24, 28] 327680 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n11 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 21, 24, 28] 327680 :=
  checked_leaf massAudit.down _ _ (by decide) a11.down

private theorem j9 : Good [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262144 :=
  checked_branch [0, 1, 2, 5, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262144 16 n10 n11 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a12 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262152 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n12 : Good [0, 1, 2, 7, 9, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262152 :=
  checked_leaf massAudit.down _ _ (by decide) a12.down

private theorem j10 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262144 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262144 3 j9 n12 (by decide +kernel) (by decide +kernel)

private theorem j11 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 0 18 j8 j10 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a13 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 16 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n13 : Good [2, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 16 :=
  checked_leaf massAudit.down _ _ (by decide) a13.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a14 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 7, 9, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 24 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n14 : Good [2, 7, 9, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 24 :=
  checked_leaf massAudit.down _ _ (by decide) a14.down

private theorem j12 : Good [2, 3, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 16 :=
  checked_branch [2, 3, 7, 9, 11, 12, 13, 14, 17, 19, 20, 21, 22, 24, 27, 28] 16 3 n13 n14 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a15 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65552 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n15 : Good [2, 3, 7, 9, 11, 12, 13, 14, 19, 20, 21, 22, 24, 28] 65552 :=
  checked_leaf massAudit.down _ _ (by decide) a15.down

private theorem j13 : Good [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 16 :=
  checked_branch [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 24, 27, 28] 16 16 j12 n15 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a16 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262160 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n16 : Good [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 21, 24, 27, 28] 262160 :=
  checked_leaf massAudit.down _ _ (by decide) a16.down

private theorem j14 : Good [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 16 :=
  checked_branch [2, 3, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 16 18 j13 n16 (by decide +kernel) (by decide +kernel)

private theorem j15 : Good [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 27, 28] 0 4 j11 j14 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a17 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108864 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n17 : Good [0, 1, 2, 3, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108864 :=
  checked_leaf massAudit.down _ _ (by decide) a17.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a18 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108896 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n18 : Good [0, 1, 2, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108896 :=
  checked_leaf massAudit.down _ _ (by decide) a18.down

private theorem j16 : Good [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108864 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 19, 20, 21, 22] 67108864 5 n17 n18 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a19 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 21] 67371008 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n19 : Good [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 21] 67371008 :=
  checked_leaf massAudit.down _ _ (by decide) a19.down

private theorem j17 : Good [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108864 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108864 18 j16 n19 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a20 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108880 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n20 : Good [2, 3, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108880 :=
  checked_leaf massAudit.down _ _ (by decide) a20.down

private theorem j18 : Good [0, 1, 2, 3, 4, 5, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108864 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22] 67108864 4 j17 n20 (by decide +kernel) (by decide +kernel)

private theorem j19 : Good [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 24, 26, 27, 28] 0 26 j15 j18 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a21 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 9, 11, 12, 13, 14, 17, 18, 19, 20, 24, 27] 8388608 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n21 : Good [0, 1, 2, 5, 9, 11, 12, 13, 14, 17, 18, 19, 20, 24, 27] 8388608 :=
  checked_leaf massAudit.down _ _ (by decide) a21.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a22 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 9, 11, 12, 13, 14, 18, 19, 20, 24] 8454144 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n22 : Good [0, 1, 2, 5, 9, 11, 12, 13, 14, 18, 19, 20, 24] 8454144 :=
  checked_leaf massAudit.down _ _ (by decide) a22.down

private theorem j20 : Good [0, 1, 2, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388608 :=
  checked_branch [0, 1, 2, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388608 16 n21 n22 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a23 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388616 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n23 : Good [0, 1, 2, 9, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388616 :=
  checked_leaf massAudit.down _ _ (by decide) a23.down

private theorem j21 : Good [0, 1, 2, 3, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388608 :=
  checked_branch [0, 1, 2, 3, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 27] 8388608 3 j20 n23 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a24 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 5, 9, 12, 13, 14, 16, 17, 18, 19, 20] 75497472 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n24 : Good [0, 1, 2, 3, 5, 9, 12, 13, 14, 16, 17, 18, 19, 20] 75497472 :=
  checked_leaf massAudit.down _ _ (by decide) a24.down

private theorem j22 : Good [0, 1, 2, 3, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388608 :=
  checked_branch [0, 1, 2, 3, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388608 26 j21 n24 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a25 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 3, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388624 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n25 : Good [2, 3, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388624 :=
  checked_leaf massAudit.down _ _ (by decide) a25.down

private theorem j23 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388608 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 24, 26, 27] 8388608 4 j22 n25 (by decide +kernel) (by decide +kernel)

private theorem j24 : Good [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 23 j19 j23 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a26 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 5, 9, 11, 13, 14, 17, 18, 20, 21, 23, 24, 27, 28] 256 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n26 : Good [0, 1, 5, 9, 11, 13, 14, 17, 18, 20, 21, 23, 24, 27, 28] 256 :=
  checked_leaf massAudit.down _ _ (by decide) a26.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a27 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 5, 9, 11, 13, 14, 18, 20, 21, 23, 24, 28] 65792 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n27 : Good [0, 1, 5, 9, 11, 13, 14, 18, 20, 21, 23, 24, 28] 65792 :=
  checked_leaf massAudit.down _ _ (by decide) a27.down

private theorem j25 : Good [0, 1, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 256 :=
  checked_branch [0, 1, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 256 16 n26 n27 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a28 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 9, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 264 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n28 : Good [0, 1, 9, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 264 :=
  checked_leaf massAudit.down _ _ (by decide) a28.down

private theorem j26 : Good [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 256 :=
  checked_branch [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 23, 24, 27, 28] 256 3 j25 n28 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a29 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 20, 24, 27, 28] 4194560 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n29 : Good [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 20, 24, 27, 28] 4194560 :=
  checked_leaf massAudit.down _ _ (by decide) a29.down

private theorem j27 : Good [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 256 :=
  checked_branch [0, 1, 3, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 256 22 j26 n29 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a30 : PLift (UnitDistancePacked.checkProjected 64 adj [3, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 272 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n30 : Good [3, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 272 :=
  checked_leaf massAudit.down _ _ (by decide) a30.down

private theorem j28 : Good [0, 1, 3, 4, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 256 :=
  checked_branch [0, 1, 3, 4, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 27, 28] 256 4 j27 n30 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a31 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 4, 5, 9, 13, 14, 16, 17, 18, 20, 21, 22, 23] 67109120 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n31 : Good [0, 1, 3, 4, 5, 9, 13, 14, 16, 17, 18, 20, 21, 22, 23] 67109120 :=
  checked_leaf massAudit.down _ _ (by decide) a31.down

private theorem j29 : Good [0, 1, 3, 4, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 26, 27, 28] 256 :=
  checked_branch [0, 1, 3, 4, 5, 9, 11, 13, 14, 16, 17, 18, 20, 21, 22, 23, 24, 26, 27, 28] 256 26 j28 n31 (by decide +kernel) (by decide +kernel)

private theorem j30 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 8 j24 j29 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a32 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 7, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1024 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n32 : Good [0, 1, 2, 3, 7, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1024 :=
  checked_leaf massAudit.down _ _ (by decide) a32.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a33 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1056 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n33 : Good [0, 1, 2, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1056 :=
  checked_leaf massAudit.down _ _ (by decide) a33.down

private theorem j31 : Good [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 27, 28] 1024 5 n32 n33 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a34 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22] 67109888 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n34 : Good [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22] 67109888 :=
  checked_leaf massAudit.down _ _ (by decide) a34.down

private theorem j32 : Good [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1024 26 j31 n34 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a35 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1040 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n35 : Good [2, 3, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1040 :=
  checked_leaf massAudit.down _ _ (by decide) a35.down

private theorem j33 : Good [0, 1, 2, 3, 4, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 12, 14, 16, 18, 19, 21, 22, 24, 26, 27, 28] 1024 4 j32 n35 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a36 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 5, 12, 14, 16, 18, 19, 24, 26, 27] 8389632 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n36 : Good [0, 1, 2, 3, 4, 5, 12, 14, 16, 18, 19, 24, 26, 27] 8389632 :=
  checked_leaf massAudit.down _ _ (by decide) a36.down

private theorem j34 : Good [0, 1, 2, 3, 4, 5, 7, 12, 14, 16, 18, 19, 21, 22, 23, 24, 26, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 12, 14, 16, 18, 19, 21, 22, 23, 24, 26, 27, 28] 1024 23 j33 n36 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a37 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 4, 5, 14, 16, 18, 21, 22, 23, 24, 26, 27, 28] 1280 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n37 : Good [0, 1, 3, 4, 5, 14, 16, 18, 21, 22, 23, 24, 26, 27, 28] 1280 :=
  checked_leaf massAudit.down _ _ (by decide) a37.down

private theorem j35 : Good [0, 1, 2, 3, 4, 5, 7, 8, 12, 14, 16, 18, 19, 21, 22, 23, 24, 26, 27, 28] 1024 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 12, 14, 16, 18, 19, 21, 22, 23, 24, 26, 27, 28] 1024 8 j34 n37 (by decide +kernel) (by decide +kernel)

private theorem j36 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28] 0 10 j30 j35 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a38 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 28] 33554432 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n38 : Good [0, 1, 2, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 28] 33554432 :=
  checked_leaf massAudit.down _ _ (by decide) a38.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a39 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 7, 9, 12, 14, 16, 17, 18, 19, 21, 28] 33554440 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n39 : Good [0, 1, 2, 7, 9, 12, 14, 16, 17, 18, 19, 21, 28] 33554440 :=
  checked_leaf massAudit.down _ _ (by decide) a39.down

private theorem j37 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 28] 33554432 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 28] 33554432 3 n38 n39 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a40 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 5, 9, 11, 12, 14, 16, 17, 18, 19] 41943040 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n40 : Good [0, 1, 2, 3, 5, 9, 11, 12, 14, 16, 17, 18, 19] 41943040 :=
  checked_leaf massAudit.down _ _ (by decide) a40.down

private theorem j38 : Good [0, 1, 2, 3, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 :=
  checked_branch [0, 1, 2, 3, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 23 j37 n40 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a41 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 3, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554448 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n41 : Good [2, 3, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554448 :=
  checked_leaf massAudit.down _ _ (by decide) a41.down

private theorem j39 : Good [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 4 j38 n41 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a42 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 4, 5, 9, 11, 14, 16, 17, 18, 21, 23, 28] 33554688 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n42 : Good [0, 1, 3, 4, 5, 9, 11, 14, 16, 17, 18, 21, 23, 28] 33554688 :=
  checked_leaf massAudit.down _ _ (by decide) a42.down

private theorem j40 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 11, 12, 14, 16, 17, 18, 19, 21, 23, 28] 33554432 8 j39 n42 (by decide +kernel) (by decide +kernel)

private theorem j41 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 25 j36 j40 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a43 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32768 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n43 : Good [0, 1, 2, 3, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_leaf massAudit.down _ _ (by decide) a43.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a44 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 3, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32784 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n44 : Good [2, 3, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32784 :=
  checked_leaf massAudit.down _ _ (by decide) a44.down

private theorem j42 : Good [0, 1, 2, 3, 4, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 9, 12, 16, 17, 19, 20, 21, 22, 23, 24, 27] 32768 4 n43 n44 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a45 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 9, 12, 16, 17, 21, 23, 24, 27] 294912 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n45 : Good [0, 1, 2, 3, 4, 9, 12, 16, 17, 21, 23, 24, 27] 294912 :=
  checked_leaf massAudit.down _ _ (by decide) a45.down

private theorem j43 : Good [0, 1, 2, 3, 4, 9, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 9, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 18 j42 n45 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a46 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 12, 16, 18, 19, 21, 22, 23, 24, 27] 33792 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n46 : Good [0, 1, 2, 3, 4, 12, 16, 18, 19, 21, 22, 23, 24, 27] 33792 :=
  checked_leaf massAudit.down _ _ (by decide) a46.down

private theorem j44 : Good [0, 1, 2, 3, 4, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 10 j43 n46 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a47 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 3, 4, 9, 10, 16, 17, 18, 20, 21, 22, 23, 24, 27] 33024 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n47 : Good [0, 1, 3, 4, 9, 10, 16, 17, 18, 20, 21, 22, 23, 24, 27] 33024 :=
  checked_leaf massAudit.down _ _ (by decide) a47.down

private theorem j45 : Good [0, 1, 2, 3, 4, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27] 32768 8 j44 n47 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a48 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 8, 9, 12, 16, 17, 18, 19, 21, 23] 33587200 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n48 : Good [0, 1, 2, 3, 4, 8, 9, 12, 16, 17, 18, 19, 21, 23] 33587200 :=
  checked_leaf massAudit.down _ _ (by decide) a48.down

private theorem j46 : Good [0, 1, 2, 3, 4, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27] 32768 :=
  checked_branch [0, 1, 2, 3, 4, 8, 9, 10, 12, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27] 32768 25 j45 n48 (by decide +kernel) (by decide +kernel)

private theorem j47 : Good [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 15 j41 j46 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a49 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 21, 24, 27, 28] 64 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n49 : Good [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 21, 24, 27, 28] 64 :=
  checked_leaf massAudit.down _ _ (by decide) a49.down

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a50 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 24, 27] 8388672 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n50 : Good [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 24, 27] 8388672 :=
  checked_leaf massAudit.down _ _ (by decide) a50.down

private theorem j48 : Good [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 :=
  checked_branch [0, 1, 2, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 23 n49 n50 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a51 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 9, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 72 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n51 : Good [0, 1, 2, 9, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 72 :=
  checked_leaf massAudit.down _ _ (by decide) a51.down

private theorem j49 : Good [0, 1, 2, 3, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 3 j48 n51 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a52 : PLift (UnitDistancePacked.checkProjected 64 adj [2, 3, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 80 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n52 : Good [2, 3, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 80 :=
  checked_leaf massAudit.down _ _ (by decide) a52.down

private theorem j50 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 27, 28] 64 4 j49 n52 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a53 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 5, 9, 11, 12, 16, 19, 21, 23, 28] 33554496 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n53 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 16, 19, 21, 23, 28] 33554496 :=
  checked_leaf massAudit.down _ _ (by decide) a53.down

private theorem j51 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 25, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 16, 19, 20, 21, 23, 24, 25, 27, 28] 64 25 j50 n53 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a54 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 9, 12, 16, 19, 20, 21, 23, 24, 25, 27] 32832 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n54 : Good [0, 1, 2, 3, 4, 9, 12, 16, 19, 20, 21, 23, 24, 25, 27] 32832 :=
  checked_leaf massAudit.down _ _ (by decide) a54.down

private theorem j52 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 15, 16, 19, 20, 21, 23, 24, 25, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 15, 16, 19, 20, 21, 23, 24, 25, 27, 28] 64 15 j51 n54 (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 180000 in
private def a55 : PLift (UnitDistancePacked.checkProjected 64 adj [0, 1, 2, 3, 4, 5, 9, 12, 13, 16, 19, 20, 21, 23] 67108928 termBlocks = true) :=
  ⟨by decide +kernel⟩

private theorem n55 : Good [0, 1, 2, 3, 4, 5, 9, 12, 13, 16, 19, 20, 21, 23] 67108928 :=
  checked_leaf massAudit.down _ _ (by decide) a55.down

private theorem j53 : Good [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 15, 16, 19, 20, 21, 23, 24, 25, 26, 27, 28] 64 :=
  checked_branch [0, 1, 2, 3, 4, 5, 9, 11, 12, 13, 15, 16, 19, 20, 21, 23, 24, 25, 26, 27, 28] 64 26 j52 n55 (by decide +kernel) (by decide +kernel)

private theorem j54 : Good [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 :=
  checked_branch [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28] 0 6 j47 j53 (by decide +kernel) (by decide +kernel)

private theorem full_certificate : OMA.R_Erdos1070_erdos_1070_parts_ii_R1.H1 :=
  finish rowAudit.down chunkedAudit j54

end SnailCoordinates

theorem OMA.solution : OMA.R_Erdos1070_erdos_1070_parts_ii_R1.H1 :=
  SnailCoordinates.full_certificate