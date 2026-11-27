import FormalConjectures.GreensOpenProblems.«15»
import Mathlib

/-!
# Proof of Ben Green's Open Problem 15

Credit: @AkiRA-COM-FP

Constructs an explicit Lipschitz function `F : ℕ → ℤ` whose graph contains no
nontrivial 3-term arithmetic progression, following the 4-uniform 6-letter substitution
and finite-state descent invariant method of Jensen Kohlmeyer and Liam Kruer (2026).
-/

namespace OMA.Green15Proof

open scoped NNReal

private def H (a : Fin 6) (r : Fin 4) : Fin 6 :=
  (![![0, 2, 0, 1], ![0, 4, 0, 1], ![0, 2, 5, 1],
      ![5, 4, 0, 3], ![5, 2, 5, 3], ![5, 4, 5, 3]] : Fin 6 → Fin 4 → Fin 6) a r

private def w (a : Fin 6) : ℤ := ![0, 1, 2, 4, 5, 6] a

private def q (a : Fin 6) : ℤ := ![0, 1, 3, 4, 9, 10] a

private def B (a : Fin 6) (r : Fin 4) : ℤ :=
  (![![0, -3, -4, -7], ![0, -3, -1, -4], ![0, -3, -4, -1],
      ![0, 3, 5, 2], ![0, 3, 2, 5], ![0, 3, 5, 8]] : Fin 6 → Fin 4 → ℤ) a r

private theorem w_bounds (a : Fin 6) : 0 ≤ w a ∧ w a ≤ 6 := by
  fin_cases a <;> decide

private theorem q_bounds (a : Fin 6) : 0 ≤ q a ∧ q a ≤ 10 := by
  fin_cases a <;> decide

private theorem q_separates (a b c : Fin 6)
    (h : q a - 2 * q b + q c = 0) : a = b ∧ b = c :=
  (by decide : ∀ a b c : Fin 6, q a - 2 * q b + q c = 0 → a = b ∧ b = c) a b c h

private theorem B_bounds (a : Fin 6) (r : Fin 4) : -7 ≤ B a r ∧ B a r ≤ 8 :=
  (by decide : ∀ a : Fin 6, ∀ r : Fin 4, -7 ≤ B a r ∧ B a r ≤ 8) a r

private theorem B_step (a : Fin 6) (r : Fin 3) :
    B a r.succ - B a r.castSucc = w (H a r.castSucc) - 3 :=
  (by decide : ∀ a : Fin 6, ∀ r : Fin 3,
    B a r.succ - B a r.castSucc = w (H a r.castSucc) - 3) a r

private theorem B_zero (a : Fin 6) : B a 0 = 0 :=
  (by decide : ∀ a : Fin 6, B a 0 = 0) a

private theorem B_wrap (a : Fin 6) :
    3 * (w a - 3) - B a 3 = w (H a 3) - 3 :=
  (by decide : ∀ a : Fin 6, 3 * (w a - 3) - B a 3 = w (H a 3) - 3) a

private def digit (n : ℕ) : Fin 4 := ⟨n % 4, Nat.mod_lt _ (by decide)⟩

private def u (n : ℕ) : Fin 6 :=
  if n = 0 then 5 else H (u (n / 4)) (digit n)
termination_by n
decreasing_by omega

private def G (n : ℕ) : ℤ :=
  if n = 0 then 0 else 3 * G (n / 4) + B (u (n / 4)) (digit n)
termination_by n
decreasing_by omega

private theorem u_zero : u 0 = 5 := by rw [u, if_pos rfl]

private theorem G_zero : G 0 = 0 := by rw [G, if_pos rfl]

private theorem u_div (n : ℕ) : u n = H (u (n / 4)) (digit n) := by
  by_cases hn : n = 0
  · subst n
    change u 0 = H (u 0) 0
    rw [u_zero]
    decide
  · conv_lhs => rw [u, if_neg hn]

private theorem G_div (n : ℕ) : G n = 3 * G (n / 4) + B (u (n / 4)) (digit n) := by
  by_cases hn : n = 0
  · subst n
    change G 0 = 3 * G 0 + B (u 0) 0
    rw [G_zero, u_zero]
    decide
  · conv_lhs => rw [G, if_neg hn]

private theorem div_digit (m : ℕ) (r : Fin 4) : (4 * m + r.val) / 4 = m := by
  have := r.isLt
  omega

private theorem digit_digit (m : ℕ) (r : Fin 4) : digit (4 * m + r.val) = r := by
  apply Fin.ext
  change (4 * m + r.val) % 4 = r.val
  have := r.isLt
  omega

private theorem u_digit (m : ℕ) (r : Fin 4) :
    u (4 * m + r.val) = H (u m) r := by
  rw [u_div (4 * m + r.val), div_digit, digit_digit]

private theorem G_digit (m : ℕ) (r : Fin 4) :
    G (4 * m + r.val) = 3 * G m + B (u m) r := by
  rw [G_div (4 * m + r.val), div_digit, digit_digit]

private theorem G_step (n : ℕ) : G (n + 1) - G n = w (u n) - 3 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    let m := n / 4
    by_cases hr : n % 4 < 3
    · let r : Fin 3 := ⟨n % 4, hr⟩
      have hn : n = 4 * m + r.castSucc.val := by
        change n = 4 * (n / 4) + n % 4
        omega
      have hn' : n + 1 = 4 * m + r.succ.val := by
        change n + 1 = 4 * (n / 4) + (n % 4 + 1)
        omega
      rw [hn', hn, G_digit, G_digit, u_digit]
      linarith only [B_step (u m) r]
    · have hn : n = 4 * m + (3 : Fin 4).val := by
        change n = 4 * (n / 4) + 3
        omega
      have hn' : n + 1 = 4 * (m + 1) + (0 : Fin 4).val := by
        change n + 1 = 4 * (n / 4 + 1) + 0
        omega
      have hm : m < n := by
        dsimp [m]
        omega
      rw [hn', hn, G_digit, G_digit, u_digit, B_zero]
      linarith only [ih m hm, B_wrap (u m)]

private def S (n : ℕ) : ℤ := G n + 3 * (n : ℤ)

private def F (n : ℕ) : ℤ := 21 * S n + q (u n) - 10

private theorem F_step (n : ℕ) :
    F (n + 1) - F n = 21 * w (u n) + q (u (n + 1)) - q (u n) := by
  simp only [F, S, Nat.cast_add, Nat.cast_one]
  linarith only [G_step n]

private theorem F_dist_step (n : ℕ) : dist (F n) (F (n + 1)) ≤ 136 := by
  rw [Int.dist_eq, abs_sub_comm, ← Int.cast_sub, F_step]
  have h : |21 * w (u n) + q (u (n + 1)) - q (u n)| ≤ (136 : ℤ) := by
    obtain ⟨hw₁, hw₂⟩ := w_bounds (u n)
    obtain ⟨hq₁, hq₂⟩ := q_bounds (u n)
    obtain ⟨hq₃, hq₄⟩ := q_bounds (u (n + 1))
    exact abs_le.mpr ⟨by omega, by omega⟩
  exact_mod_cast h

private theorem F_dist_add (m d : ℕ) : dist (F m) (F (m + d)) ≤ 136 * (d : ℝ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc
      dist (F m) (F (m + (d + 1))) ≤
          dist (F m) (F (m + d)) + dist (F (m + d)) (F ((m + d) + 1)) := by
        rw [← Nat.add_assoc]
        exact dist_triangle _ _ _
      _ ≤ 136 * (d : ℝ) + 136 := add_le_add ih (F_dist_step _)
      _ = 136 * ((d + 1 : ℕ) : ℝ) := by push_cast; ring

private theorem F_lipschitz : LipschitzWith 136 F := by
  apply LipschitzWith.of_dist_le_mul
  have h (m n : ℕ) (hmn : m ≤ n) : dist (F m) (F n) ≤ (136 : ℝ) * dist m n := by
    have hd : dist m n = ((n - m : ℕ) : ℝ) := by
      rw [Nat.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmn))]
      exact (Nat.cast_sub hmn).symm
    have hh := F_dist_add m (n - m)
    rw [Nat.add_sub_of_le hmn] at hh
    rwa [hd]
  intro m n
  change dist (F m) (F n) ≤ (136 : ℝ) * dist m n
  rcases le_total m n with hmn | hnm
  · exact h m n hmn
  · simpa only [dist_comm] using h n m hnm

private theorem separate (i j k : ℕ) (h : F i - 2 * F j + F k = 0) :
    (u i = u j ∧ u j = u k) ∧ S i - 2 * S j + S k = 0 := by
  obtain ⟨hi₁, hi₂⟩ := q_bounds (u i)
  obtain ⟨hj₁, hj₂⟩ := q_bounds (u j)
  obtain ⟨hk₁, hk₂⟩ := q_bounds (u k)
  unfold F at h
  have hs : S i - 2 * S j + S k = 0 := by omega
  have hq : q (u i) - 2 * q (u j) + q (u k) = 0 := by omega
  exact ⟨q_separates _ _ _ hq, hs⟩

-- Each packed row contains 18 indices into the dictionary of 31-bit masks.
-- A mask records vertical offset D at bit D + 15.
private def packedIndices : ℕ → ℕ
  | 0 => 0x90703603703603080
  | 1 => 0x10102105102105010
  | 2 => 0x20205201205201020
  | 3 => 0x10102105102105010
  | 4 => 0x20205201205201020
  | 5 => 0x90703603703603090
  | 6 => 0x603030000030000603
  | 7 => 0x105000050000040105
  | 8 => 0x201000010000010201
  | 9 => 0x105000050000050105
  | 10 => 0x201000010000010201
  | 11 => 0x603030000030000603
  | 12 => 0x703000030000030703
  | 13 => 0x102020000020000102
  | 14 => 0x205050000040000205
  | 15 => 0x102020000020000102
  | 16 => 0x205050000050000205
  | 17 => 0x703000030000030703
  | 18 => 0x603030000030000603
  | 19 => 0x105000050000050105
  | 20 => 0x201000010000010201
  | 21 => 0x105000040000050105
  | 22 => 0x201000010000010201
  | 23 => 0x603030000030000603
  | 24 => 0x703000030000030703
  | 25 => 0x102020000020000102
  | 26 => 0x205050000050000205
  | 27 => 0x102020000020000102
  | 28 => 0x205040000050000205
  | 29 => 0x703000030000030703
  | 30 => 0x90703603703603090
  | 31 => 0x10102105102105010
  | 32 => 0x20205201205201020
  | 33 => 0x10102105102105010
  | 34 => 0x20205201205201020
  | 35 => 0x80703603703603090
  | _ => 0

private def maskIndex (a b c : Fin 6) (A : ℤ) : Fin 10 :=
  ⟨(packedIndices (6 * a.val + b.val) / 16 ^ (3 * c.val + (A + 1).toNat) % 16) % 10,
    Nat.mod_lt _ (by decide)⟩

private def mask (index : Fin 10) : ℕ :=
  ![0x0, 0x12492492, 0x24924924, 0x36db6db6, 0x49241249, 0x49249249, 0x5b6db6db, 0x6db6db6d, 0x7fff7fff, 0x7fffffff] index

private def insideA (A : ℤ) : Prop := -1 ≤ A ∧ A ≤ 1

private def insideD (D : ℤ) : Prop := -15 ≤ D ∧ D ≤ 15

private def nextA (A : ℤ) (x y z : Fin 4) : ℤ :=
  4 * A + ((x.val : ℤ) - 2 * y.val + z.val)

private def correction (a b c : Fin 6) (x y z : Fin 4) : ℤ :=
  B a x - 2 * B b y + B c z

private def nextD (a b c : Fin 6) (D : ℤ) (x y z : Fin 4) : ℤ :=
  3 * D + correction a b c x y z

private def contains (m : ℕ) (D : ℤ) : Bool :=
  decide (m / 2 ^ (D + 15).toNat % 2 = 1)

private def R (a b c : Fin 6) (A D : ℤ) (e : Bool) : Bool :=
  if e then contains (mask (maskIndex a b c A)) D
  else decide (a = b ∧ b = c ∧ A = 0 ∧ D = 0)

private def allFin {n : ℕ} (f : Fin n → Bool) : Bool := (List.finRange n).all f

private theorem fromAllFin {n : ℕ} {f : Fin n → Bool} (h : allFin f = true)
    (i : Fin n) : f i = true :=
  List.all_eq_true.mp h i (List.mem_finRange i)

-- The source mask, target mask and vertical correction determine whether a
-- transition preserves membership. Each row packs ten sets of corrections.
private def packedCorrections : ℕ → ℕ
  | 0 => 0x0
  | 1 => 0x20a2f866000000000001c31010000000005144100000000a2cb6590080009009249249200000004004100000000025b6db6c92000000492492480000004924924924000000000000000000
  | 2 => 0x1e1ba8820000010070c40000000000105144000000020165b2ca2000000249249248048000000104004000000125b6db6c90000000492492490000004924924924000000000000000000
  | 3 => 0x434db4c100000000020c2000000000000104000000000434d34d30400009249249249248000000800020000000025b6db6c90000000492492480000004924924924000000000000000000
  | 4 => 0x4000000000000010400000000000008200000000000004100000000000000400000000000012492000000000002490000000000000000000000000000000000000
  | 5 => 0x249a48000000000430830400000000001040000000000a69a69a2000000049241249000000004100104000000025b6db6c90000000492492480000004924924924000000000000000000
  | 6 => 0x800020000000000400010000000001040041000000000000000000000000000000000000000000000000000000000000000000012490000492400024924000924900000000000000000
  | 7 => 0x800020000000000400010000000001040041000000000000000000000000000000000000000000000000000000000000000000012490000492400024924000924900000000000000000
  | 8 => 0x4000000000000010400000000000008200000000000004100000000000000400000000000000480000000000000480000000000000000000000000000000000000
  | 9 => 0x201008040200000000000000000000000010400000000201040041008024024924124920120000000000000000012492492492000000492492480000000000000000000000000000000000
  | _ => 0

private def allows (source target : Fin 10) (offset : ℤ) : Bool :=
  let m := packedCorrections source.val / 2305843009213693952 ^ target.val % 2305843009213693952
  decide (m / 2 ^ (offset + 30).toNat % 2 = 1)

private def checkBits (source target : Fin 10) (offset : ℤ) : Bool :=
  let lo := (-13 - offset) / 3
  allFin fun n : Fin 11 =>
    let D : ℤ := lo + n.val
    let E := 3 * D + offset
    if contains (mask source) D then
      if -15 ≤ E ∧ E ≤ 15 then contains (mask target) E else true
    else true

private def checkCorrections (source : Fin 10) : Bool :=
  allFin fun target => allFin fun i : Fin 61 =>
    let offset := (i.val : ℤ) - 30
    if allows source target offset then checkBits source target offset else true

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem correctionsChecked (source : Fin 10) : checkCorrections source = true := by
  fin_cases source <;> exact eagerReduce (Eq.refl true)

private def checkRow (a b c : Fin 6) (A : ℤ) : Bool :=
  let source := maskIndex a b c A
  if source = 0 then true else
    allFin fun x => allFin fun y => allFin fun z =>
      let A' := nextA A x y z
      if -1 ≤ A' ∧ A' ≤ 1 then
        allows source (maskIndex (H a x) (H b y) (H c z) A') (correction a b c x y z)
      else true

private def checkLetter (a : Fin 6) : Bool :=
  allFin fun b => allFin fun c => allFin fun p : Fin 3 =>
    checkRow a b c ((p.val : ℤ) - 1)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem cert (a : Fin 6) : checkLetter a = true := by
  fin_cases a <;> exact eagerReduce (Eq.refl true)

private theorem preservesBits (source target : Fin 10) (offset D : ℤ)
    (hlo : -30 ≤ offset) (hhi : offset ≤ 30)
    (hallow : allows source target offset = true)
    (hmem : contains (mask source) D = true) (hE : insideD (3 * D + offset)) :
    contains (mask target) (3 * D + offset) = true := by
  let i : Fin 61 := ⟨(offset + 30).toNat, by omega⟩
  have hi : (i.val : ℤ) - 30 = offset := by
    change ((offset + 30).toNat : ℤ) - 30 = offset
    omega
  have hcheck := fromAllFin (fromAllFin (correctionsChecked source) target) i
  change (if allows source target ((i.val : ℤ) - 30) then
    checkBits source target ((i.val : ℤ) - 30) else true) = true at hcheck
  have hbits : checkBits source target offset = true := by
    simpa only [hi, hallow, if_true] using hcheck
  have hE' : -15 ≤ 3 * D + offset ∧ 3 * D + offset ≤ 15 := hE
  obtain ⟨hEl, hEu⟩ := hE
  let lo := (-13 - offset) / 3
  have hdelta : 0 ≤ D - lo ∧ D - lo < 11 := by
    dsimp [lo]
    exact ⟨by omega, by omega⟩
  let n : Fin 11 := ⟨(D - lo).toNat, by omega⟩
  have hn : (-13 - offset) / 3 + (n.val : ℤ) = D := by
    change lo + ((D - lo).toNat : ℤ) = D
    omega
  unfold checkBits at hbits
  have hbit := fromAllFin hbits n
  simpa only [hn, hmem, if_true, if_pos hE'] using hbit

private theorem advanceUnequal
    (a b c : Fin 6) (A D : ℤ) (x y z : Fin 4)
    (hA : insideA A) (h : R a b c A D true = true)
    (hA' : insideA (nextA A x y z)) (hD' : insideD (nextD a b c D x y z)) :
    R (H a x) (H b y) (H c z) (nextA A x y z) (nextD a b c D x y z) true = true := by
  obtain ⟨hAl, hAu⟩ := hA
  let p : Fin 3 := ⟨(A + 1).toNat, by omega⟩
  have hp : (p.val : ℤ) - 1 = A := by
    change ((A + 1).toNat : ℤ) - 1 = A
    omega
  have hrow := fromAllFin (fromAllFin (fromAllFin (cert a) b) c) p
  change checkRow a b c ((p.val : ℤ) - 1) = true at hrow
  rw [hp] at hrow
  let source := maskIndex a b c A
  let target := maskIndex (H a x) (H b y) (H c z) (nextA A x y z)
  have hmem : contains (mask source) D = true := h
  by_cases hm : source = 0
  · simp [contains, hm, show mask 0 = 0 by decide] at hmem
  · change (if source = 0 then true else _) = true at hrow
    rw [if_neg hm] at hrow
    have hedge := fromAllFin (fromAllFin (fromAllFin hrow x) y) z
    change (if -1 ≤ nextA A x y z ∧ nextA A x y z ≤ 1 then
      allows source target (correction a b c x y z) else true) = true at hedge
    have hA'' : -1 ≤ nextA A x y z ∧ nextA A x y z ≤ 1 := hA'
    rw [if_pos hA''] at hedge
    obtain ⟨hx₁, hx₂⟩ := B_bounds a x
    obtain ⟨hy₁, hy₂⟩ := B_bounds b y
    obtain ⟨hz₁, hz₂⟩ := B_bounds c z
    exact preservesBits source target (correction a b c x y z) D
      (by unfold correction; omega) (by unfold correction; omega) hedge hmem hD'

private def differentDigits (x y z : Fin 4) : Bool := decide (x ≠ y ∨ y ≠ z)

private theorem advanceEqual (a : Fin 6) (x y z : Fin 4)
    (hA : insideA (nextA 0 x y z)) (hD : insideD (nextD a a a 0 x y z)) :
    R (H a x) (H a y) (H a z) (nextA 0 x y z) (nextD a a a 0 x y z)
      (differentDigits x y z) = true :=
  (by decide : ∀ (a : Fin 6) (x y z : Fin 4),
    (-1 ≤ nextA 0 x y z ∧ nextA 0 x y z ≤ 1) →
    (-15 ≤ nextD a a a 0 x y z ∧ nextD a a a 0 x y z ≤ 15) →
    R (H a x) (H a y) (H a z) (nextA 0 x y z) (nextD a a a 0 x y z)
      (differentDigits x y z) = true) a x y z hA hD

private theorem advance
    (a b c : Fin 6) (A D : ℤ) (e : Bool) (x y z : Fin 4)
    (hA : insideA A) (h : R a b c A D e = true)
    (hA' : insideA (nextA A x y z)) (hD' : insideD (nextD a b c D x y z)) :
    R (H a x) (H b y) (H c z) (nextA A x y z) (nextD a b c D x y z)
      (e || differentDigits x y z) = true := by
  cases e with
  | false =>
    have hh : a = b ∧ b = c ∧ A = 0 ∧ D = 0 := of_decide_eq_true h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hh
    exact advanceEqual _ x y z hA' hD'
  | true =>
    exact advanceUnequal a b c A D x y z hA h hA' hD'

private theorem excludes (a : Fin 6) : R a a a 0 0 true = false :=
  (by decide : ∀ a : Fin 6, R a a a 0 0 true = false) a

private def A (i j k : ℕ) : ℤ := (i : ℤ) - 2 * (j : ℤ) + (k : ℤ)

private def D (i j k : ℕ) : ℤ := G i - 2 * G j + G k

private def distinct (i j k : ℕ) : Bool := decide (i ≠ j ∨ j ≠ k)

private theorem A_split (i j k : ℕ) :
    A i j k = nextA (A (i / 4) (j / 4) (k / 4)) (digit i) (digit j) (digit k) := by
  simp only [A, nextA, digit]
  omega

private theorem D_split (i j k : ℕ) :
    D i j k = nextD (u (i / 4)) (u (j / 4)) (u (k / 4))
      (D (i / 4) (j / 4) (k / 4)) (digit i) (digit j) (digit k) := by
  unfold D nextD correction
  linarith only [G_div i, G_div j, G_div k]

private theorem distinct_split (i j k : ℕ) :
    distinct i j k =
      (distinct (i / 4) (j / 4) (k / 4) || differentDigits (digit i) (digit j) (digit k)) := by
  have eq_parts (m n : ℕ) : m = n ↔ m / 4 = n / 4 ∧ digit m = digit n := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h₁, h₂⟩
      have hm : m % 4 = n % 4 := congrArg Fin.val h₂
      omega
  apply Bool.eq_iff_iff.mpr
  simp only [distinct, differentDigits, Bool.or_eq_true_iff, decide_eq_true_eq]
  simp only [ne_eq, eq_parts i j, eq_parts j k]
  tauto

private theorem reachable (i j k : ℕ)
    (hA : insideA (A i j k)) (hD : insideD (D i j k)) :
    R (u i) (u j) (u k) (A i j k) (D i j k) (distinct i j k) = true := by
  induction hs : i + j + k using Nat.strongRecOn generalizing i j k with
  | ind n ih =>
    by_cases hn : n = 0
    · have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      have hk : k = 0 := by omega
      subst i j k
      rw [u_zero, A, D, G_zero]
      decide
    · let I := i / 4
      let J := j / 4
      let K := k / 4
      have hlt : I + J + K < n := by
        dsimp [I, J, K]
        omega
      have hAs := A_split i j k
      have hDs := D_split i j k
      change A i j k = nextA (A I J K) (digit i) (digit j) (digit k) at hAs
      change D i j k = nextD (u I) (u J) (u K) (D I J K)
        (digit i) (digit j) (digit k) at hDs
      rw [hAs] at hA
      rw [hDs] at hD
      have hAp : insideA (A I J K) := by
        obtain ⟨hl, hu⟩ := hA
        have hx := (digit i).isLt
        have hy := (digit j).isLt
        have hz := (digit k).isLt
        simp only [nextA] at hl hu
        exact ⟨by omega, by omega⟩
      have hDp : insideD (D I J K) := by
        obtain ⟨hl, hu⟩ := hD
        obtain ⟨hx₁, hx₂⟩ := B_bounds (u I) (digit i)
        obtain ⟨hy₁, hy₂⟩ := B_bounds (u J) (digit j)
        obtain ⟨hz₁, hz₂⟩ := B_bounds (u K) (digit k)
        simp only [nextD, correction] at hl hu
        exact ⟨by omega, by omega⟩
      have hp := ih (I + J + K) hlt I J K hAp hDp rfl
      have hn' := advance (u I) (u J) (u K) (A I J K) (D I J K)
        (distinct I J K) (digit i) (digit j) (digit k) hAp hp hA hD
      rw [hAs, hDs, distinct_split, u_div i, u_div j, u_div k]
      exact hn'

private theorem noProgression
    (i j k : ℕ) (hA : A i j k = 0) (hF : F i - 2 * F j + F k = 0) :
    i = j ∧ j = k := by
  obtain ⟨⟨hij, hjk⟩, hS⟩ := separate i j k hF
  have hD : D i j k = 0 := by
    unfold A at hA
    unfold S at hS
    unfold D
    linarith only [hA, hS]
  have h := reachable i j k (by rw [hA]; exact ⟨by decide, by decide⟩)
    (by rw [hD]; exact ⟨by decide, by decide⟩)
  rw [hA, hD, ← hjk, ← hij] at h
  by_cases hh : i ≠ j ∨ j ≠ k
  · have he : distinct i j k = true := decide_eq_true hh
    have hbad : false = true := by simpa only [he, excludes] using h
    contradiction
  · tauto

private theorem free :
    Set.IsAPOfLengthFree {((n, F n) : ℤ × ℤ) | (n : ℕ)} 3 := by
  intro t ht hap
  obtain ⟨a, d, hcard, ht'⟩ := hap
  have mem_graph (n : ℕ) (hn : (n : ℕ∞) < 3) :
      a + n • d ∈ {((m, F m) : ℤ × ℤ) | (m : ℕ)} := by
    apply ht
    rw [ht']
    exact ⟨n, hn, rfl⟩
  obtain ⟨i, hi⟩ := mem_graph 0 (by decide)
  obtain ⟨j, hj⟩ := mem_graph 1 (by decide)
  obtain ⟨k, hk⟩ := mem_graph 2 (by decide)
  have hi' : ((i : ℤ), F i) = a := by simpa only [zero_nsmul, add_zero] using hi
  have hj' : ((j : ℤ), F j) = a + d := by simpa only [one_nsmul] using hj
  have hk' : ((k : ℤ), F k) = a + (d + d) := by simpa only [two_nsmul] using hk
  have hA : A i j k = 0 := by
    have hi₁ := congrArg Prod.fst hi'
    have hj₁ := congrArg Prod.fst hj'
    have hk₁ := congrArg Prod.fst hk'
    simp only [Prod.fst_add] at hi₁ hj₁ hk₁
    unfold A
    omega
  have hF : F i - 2 * F j + F k = 0 := by
    have hi₂ := congrArg Prod.snd hi'
    have hj₂ := congrArg Prod.snd hj'
    have hk₂ := congrArg Prod.snd hk'
    simp only [Prod.snd_add] at hi₂ hj₂ hk₂
    omega
  obtain ⟨rfl, _⟩ := noProgression i j k hA hF
  have hd : d = 0 := by
    have he : a + d = a + 0 := hj'.symm.trans (hi'.trans (add_zero a).symm)
    exact add_left_cancel he
  subst d
  have hs : t = {a} := by
    rw [ht']
    ext p
    constructor
    · rintro ⟨n, _, rfl⟩
      simp
    · intro hp
      have he : p = a := hp
      subst p
      exact ⟨0, by decide, by simp⟩
  rw [hs] at hcard
  simpa using hcard.symm.le

end OMA.Green15Proof

theorem OMA.solution : type_of% @Green15.green_15 := by
  exact ⟨136, OMA.Green15Proof.F, OMA.Green15Proof.F_lipschitz, OMA.Green15Proof.free⟩