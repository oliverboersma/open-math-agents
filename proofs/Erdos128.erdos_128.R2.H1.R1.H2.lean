import OMAReductions.R_Erdos128_erdos_128_R2_H1_R1

/-!
# Proof of `Erdos128.erdos_128.R2.H1.R1.H2`

We eliminate the Band subcase containing a homomorphic image `φ : And(4) → G`
directly from triangle-freeness, `δ(G) ≥ (5 / 14) n`, and the half-vertex edge
lower bound `∀ V', 2 * |V'| + 1 ≥ n → 50 * e(G[V']) > n^2`.

Every vertex `v` is classified by its `φ`-neighborhood `I(v) ⊆ Fin 11`, which
must be one of the 89 independent sets of `And(4)`. For each of the 22 pairs
`(i, d) ∈ Fin 11 × {+1, -1}`, taking `S_i = N_G(φ i)` together with the first
`t_i = n / 2 - |S_i|` vertices from the disjoint independent set
`V'_{i + 2d} ∪ V'_{i + 5d}` yields a half-size set `V'` whose edge count is
bounded by `t_i * |D1_{i,d}| + max(0, t_i - |V'_{i+2d}|) * |DIFF_{i,d}|`.
Relaxing `max(0, U) * y ≤ (U + y)^2 / 4` and summing over all 22 pairs gives a
strictly positive quadratic form in the 89 type counts `x_a`, which is
contradicted by an exact `ℤ/11`-invariant linear multiplier certificate against
the 11 degree inequalities `14 * |S_k| - 5 * n ≥ 0`.
-/

namespace Erdos128_R2_H1_R1_H2

/-- Powers of 2 for `Fin 11`. -/
def pow2 (k : Fin 11) : ℕ :=
  match k.1 with
  | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 8 | 4 => 16 | 5 => 32
  | 6 => 64 | 7 => 128 | 8 => 256 | 9 => 512 | _ => 1024

/-- Bit test using kernel-reduced integer division and mod. -/
def hasBit (m : ℕ) (k : Fin 11) : Bool :=
  (m / pow2 k) % 2 == 1

/-- Test whether an 11-bit mask represents an independent set of `And(4)`. -/
def isIndepMask (m : ℕ) : Bool :=
  (List.finRange 11).all fun i =>
    !hasBit m i || (!hasBit m (i + 1) && !hasBit m (i + 4) && !hasBit m (i + 7) && !hasBit m (i + 10))

/-- The 89 bitmasks of independent sets of `And(4)`. -/
def maskOf (a : Fin 89) : ℕ :=
  match a.1 with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 8 | 5 => 16 | 6 => 32 | 7 => 64 | 8 => 128
  | 9 => 256 | 10 => 512 | 11 => 1024 | 12 => 5 | 13 => 9 | 14 => 33 | 15 => 65 | 16 => 257
  | 17 => 513 | 18 => 10 | 19 => 18 | 20 => 66 | 21 => 130 | 22 => 514 | 23 => 1026 | 24 => 20
  | 25 => 36 | 26 => 132 | 27 => 260 | 28 => 1028 | 29 => 40 | 30 => 72 | 31 => 264 | 32 => 520
  | 33 => 80 | 34 => 144 | 35 => 528 | 36 => 1040 | 37 => 160 | 38 => 288 | 39 => 1056 | 40 => 320
  | 41 => 576 | 42 => 640 | 43 => 1152 | 44 => 1280 | 45 => 37 | 46 => 261 | 47 => 41 | 48 => 73
  | 49 => 265 | 50 => 521 | 51 => 289 | 52 => 321 | 53 => 577 | 54 => 74 | 55 => 522 | 56 => 82
  | 57 => 146 | 58 => 530 | 59 => 1042 | 60 => 578 | 61 => 642 | 62 => 1154 | 63 => 148 | 64 => 1044
  | 65 => 164 | 66 => 292 | 67 => 1060 | 68 => 1156 | 69 => 1284 | 70 => 296 | 71 => 328 | 72 => 584
  | 73 => 592 | 74 => 656 | 75 => 1168 | 76 => 1184 | 77 => 1312 | 78 => 293 | 79 => 297 | 80 => 329
  | 81 => 585 | 82 => 586 | 83 => 594 | 84 => 658 | 85 => 1170 | 86 => 1172 | 87 => 1188 | _ => 1316

/-- Inverse lookup from an independent-set bitmask to `Fin 89`. -/
def idxOfMask (m : ℕ) : Fin 89 :=
  match m with
  | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4 | 16 => 5 | 32 => 6 | 64 => 7 | 128 => 8
  | 256 => 9 | 512 => 10 | 1024 => 11 | 5 => 12 | 9 => 13 | 33 => 14 | 65 => 15 | 257 => 16
  | 513 => 17 | 10 => 18 | 18 => 19 | 66 => 20 | 130 => 21 | 514 => 22 | 1026 => 23 | 20 => 24
  | 36 => 25 | 132 => 26 | 260 => 27 | 1028 => 28 | 40 => 29 | 72 => 30 | 264 => 31 | 520 => 32
  | 80 => 33 | 144 => 34 | 528 => 35 | 1040 => 36 | 160 => 37 | 288 => 38 | 1056 => 39 | 320 => 40
  | 576 => 41 | 640 => 42 | 1152 => 43 | 1280 => 44 | 37 => 45 | 261 => 46 | 41 => 47 | 73 => 48
  | 265 => 49 | 521 => 50 | 289 => 51 | 321 => 52 | 577 => 53 | 74 => 54 | 522 => 55 | 82 => 56
  | 146 => 57 | 530 => 58 | 1042 => 59 | 578 => 60 | 642 => 61 | 1154 => 62 | 148 => 63 | 1044 => 64
  | 164 => 65 | 292 => 66 | 1060 => 67 | 1156 => 68 | 1284 => 69 | 296 => 70 | 328 => 71 | 584 => 72
  | 592 => 73 | 656 => 74 | 1168 => 75 | 1184 => 76 | 1312 => 77 | 293 => 78 | 297 => 79 | 329 => 80
  | 585 => 81 | 586 => 82 | 594 => 83 | 658 => 84 | 1170 => 85 | 1172 => 86 | 1188 => 87 | 1316 => 88
  | _ => 0

/-- `+1` cyclic shift on `Fin 89`. -/
def sh1 (a : Fin 89) : Fin 89 :=
  match a.1 with
  | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8 | 8 => 9
  | 9 => 10 | 10 => 11 | 11 => 1 | 12 => 18 | 13 => 19 | 14 => 20 | 15 => 21 | 16 => 22
  | 17 => 23 | 18 => 24 | 19 => 25 | 20 => 26 | 21 => 27 | 22 => 28 | 23 => 12 | 24 => 29
  | 25 => 30 | 26 => 31 | 27 => 32 | 28 => 13 | 29 => 33 | 30 => 34 | 31 => 35 | 32 => 36
  | 33 => 37 | 34 => 38 | 35 => 39 | 36 => 14 | 37 => 40 | 38 => 41 | 39 => 15 | 40 => 42
  | 41 => 43 | 42 => 44 | 43 => 16 | 44 => 17 | 45 => 54 | 46 => 55 | 47 => 56 | 48 => 57
  | 49 => 58 | 50 => 59 | 51 => 60 | 52 => 61 | 53 => 62 | 54 => 63 | 55 => 64 | 56 => 65
  | 57 => 66 | 58 => 67 | 59 => 45 | 60 => 68 | 61 => 69 | 62 => 46 | 63 => 70 | 64 => 47
  | 65 => 71 | 66 => 72 | 67 => 48 | 68 => 49 | 69 => 50 | 70 => 73 | 71 => 74 | 72 => 75
  | 73 => 76 | 74 => 77 | 75 => 51 | 76 => 52 | 77 => 53 | 78 => 82 | 79 => 83 | 80 => 84
  | 81 => 85 | 82 => 86 | 83 => 87 | 84 => 88 | 85 => 78 | 86 => 79 | 87 => 80 | _ => 81

/-- `-1` cyclic shift on `Fin 89`. -/
def invSh1 (a : Fin 89) : Fin 89 :=
  match a.1 with
  | 0 => 0 | 1 => 11 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7
  | 9 => 8 | 10 => 9 | 11 => 10 | 12 => 23 | 13 => 28 | 14 => 36 | 15 => 39 | 16 => 43
  | 17 => 44 | 18 => 12 | 19 => 13 | 20 => 14 | 21 => 15 | 22 => 16 | 23 => 17 | 24 => 18
  | 25 => 19 | 26 => 20 | 27 => 21 | 28 => 22 | 29 => 24 | 30 => 25 | 31 => 26 | 32 => 27
  | 33 => 29 | 34 => 30 | 35 => 31 | 36 => 32 | 37 => 33 | 38 => 34 | 39 => 35 | 40 => 37
  | 41 => 38 | 42 => 40 | 43 => 41 | 44 => 42 | 45 => 59 | 46 => 62 | 47 => 64 | 48 => 67
  | 49 => 68 | 50 => 69 | 51 => 75 | 52 => 76 | 53 => 77 | 54 => 45 | 55 => 46 | 56 => 47
  | 57 => 48 | 58 => 49 | 59 => 50 | 60 => 51 | 61 => 52 | 62 => 53 | 63 => 54 | 64 => 55
  | 65 => 56 | 66 => 57 | 67 => 58 | 68 => 60 | 69 => 61 | 70 => 63 | 71 => 65 | 72 => 66
  | 73 => 70 | 74 => 71 | 75 => 72 | 76 => 73 | 77 => 74 | 78 => 85 | 79 => 86 | 80 => 87
  | 81 => 88 | 82 => 78 | 83 => 79 | 84 => 80 | 85 => 81 | 86 => 82 | 87 => 83 | _ => 84

def sh (k : Fin 11) (a : Fin 89) : Fin 89 := sh1^[k.1] a
def invSh (k : Fin 11) (a : Fin 89) : Fin 89 := invSh1^[k.1] a

/-- Representatives of the 9 `ℤ/11`-orbits on `Fin 89`. -/
def rep (r : Fin 9) : Fin 89 :=
  match r.1 with
  | 0 => 0 | 1 => 1 | 2 => 12 | 3 => 13 | 4 => 14 | 5 => 45 | 6 => 46 | 7 => 48 | _ => 78

def orbId (a : Fin 89) : Fin 9 :=
  match a.1 with
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1
  | 9 => 1 | 10 => 1 | 11 => 1 | 12 => 2 | 13 => 3 | 14 => 4 | 15 => 4 | 16 => 3 | 17 => 2
  | 18 => 2 | 19 => 3 | 20 => 4 | 21 => 4 | 22 => 3 | 23 => 2 | 24 => 2 | 25 => 3 | 26 => 4
  | 27 => 4 | 28 => 3 | 29 => 2 | 30 => 3 | 31 => 4 | 32 => 4 | 33 => 2 | 34 => 3 | 35 => 4
  | 36 => 4 | 37 => 2 | 38 => 3 | 39 => 4 | 40 => 2 | 41 => 3 | 42 => 2 | 43 => 3 | 44 => 2
  | 45 => 5 | 46 => 6 | 47 => 6 | 48 => 7 | 49 => 7 | 50 => 5 | 51 => 7 | 52 => 5 | 53 => 6
  | 54 => 5 | 55 => 6 | 56 => 6 | 57 => 7 | 58 => 7 | 59 => 5 | 60 => 7 | 61 => 5 | 62 => 6
  | 63 => 5 | 64 => 6 | 65 => 6 | 66 => 7 | 67 => 7 | 68 => 7 | 69 => 5 | 70 => 5 | 71 => 6
  | 72 => 7 | 73 => 5 | 74 => 6 | 75 => 7 | 76 => 5 | 77 => 6 | 78 => 8 | 79 => 8 | 80 => 8
  | 81 => 8 | 82 => 8 | 83 => 8 | 84 => 8 | 85 => 8 | 86 => 8 | 87 => 8 | _ => 8

def orbSh (a : Fin 89) : Fin 11 :=
  match a.1 with
  | 0 => 10 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7
  | 9 => 8 | 10 => 9 | 11 => 10 | 12 => 0 | 13 => 0 | 14 => 0 | 15 => 6 | 16 => 8 | 17 => 9
  | 18 => 1 | 19 => 1 | 20 => 1 | 21 => 7 | 22 => 9 | 23 => 10 | 24 => 2 | 25 => 2 | 26 => 2
  | 27 => 8 | 28 => 10 | 29 => 3 | 30 => 3 | 31 => 3 | 32 => 9 | 33 => 4 | 34 => 4 | 35 => 4
  | 36 => 10 | 37 => 5 | 38 => 5 | 39 => 5 | 40 => 6 | 41 => 6 | 42 => 7 | 43 => 7 | 44 => 8
  | 45 => 0 | 46 => 0 | 47 => 3 | 48 => 0 | 49 => 8 | 50 => 9 | 51 => 5 | 52 => 6 | 53 => 9
  | 54 => 1 | 55 => 1 | 56 => 4 | 57 => 1 | 58 => 9 | 59 => 10 | 60 => 6 | 61 => 7 | 62 => 10
  | 63 => 2 | 64 => 2 | 65 => 5 | 66 => 2 | 67 => 10 | 68 => 7 | 69 => 8 | 70 => 3 | 71 => 6
  | 72 => 3 | 73 => 4 | 74 => 7 | 75 => 4 | 76 => 5 | 77 => 8 | 78 => 0 | 79 => 3 | 80 => 6
  | 81 => 9 | 82 => 1 | 83 => 4 | 84 => 7 | 85 => 10 | 86 => 2 | 87 => 5 | _ => 8

/-- Nonnegative integer multipliers for `k = 0` in the `ℤ/11`-equivariant certificate. -/
def Lval (a : Fin 89) : ℤ :=
  match a.1 with
  | 0 => 4121 | 1 => 3195 | 2 => 2874 | 3 => 2657 | 4 => 2550 | 5 => 2622 | 6 => 2693
  | 7 => 2693 | 8 => 2622 | 9 => 2550 | 10 => 2657 | 11 => 2874 | 12 => 1732 | 13 => 1921
  | 14 => 1791 | 15 => 1791 | 16 => 1921 | 17 => 1732 | 18 => 1322 | 19 => 1672 | 20 => 1470
  | 21 => 1399 | 22 => 1885 | 23 => 1660 | 24 => 1144 | 25 => 1494 | 26 => 1134 | 27 => 1078
  | 28 => 1885 | 29 => 1109 | 30 => 1405 | 31 => 957 | 32 => 1078 | 33 => 1181 | 34 => 1405
  | 35 => 1134 | 36 => 1399 | 37 => 1181 | 38 => 1405 | 39 => 1470 | 40 => 1109 | 41 => 1494
  | 42 => 1144 | 43 => 1672 | 44 => 1322 | 45 => 867 | 46 => 867 | 47 => 1117 | 48 => 918
  | 49 => 732 | 50 => 867 | 51 => 918 | 52 => 1117 | 53 => 867 | 54 => 761 | 55 => 867
  | 56 => 868 | 57 => 670 | 58 => 803 | 59 => 796 | 60 => 883 | 61 => 1081 | 62 => 796
  | 63 => 655 | 64 => 1081 | 65 => 619 | 66 => 421 | 67 => 883 | 68 => 803 | 69 => 867
  | 70 => 477 | 71 => 477 | 72 => 421 | 73 => 619 | 74 => 655 | 75 => 670 | 76 => 868
  | 77 => 761 | 78 => 71 | 79 => 107 | 80 => 107 | 81 => 71 | 82 => 107 | 83 => 179
  | 84 => 250 | 85 => 0 | 86 => 250 | 87 => 179 | _ => 107

def dir (d : Bool) : Fin 11 := if d then 1 else 10

def b2z (b : Bool) : ℤ := if b then 1 else 0

/-- Membership predicate for `V'_j = V_j ∪ Orb1(j) ∪ Orb2(j)`. -/
def inVp (j : Fin 11) (m : ℕ) : Bool :=
  hasBit m (j + 10) && hasBit m (j + 1) && (hasBit m (j + 4) || hasBit m (j + 7))

/-- Necessary condition for a vertex in `S_i` to be adjacent to a vertex in `V'_j`. -/
def canAdjVp (i j : Fin 11) (m : ℕ) : Bool :=
  hasBit m i && !hasBit m (j + 10) && !hasBit m (j + 1) && !(hasBit m (j + 4) && hasBit m (j + 7))

def d1Pred (i : Fin 11) (d : Bool) (a : Fin 89) : Bool :=
  canAdjVp i (i + 2 * dir d) (maskOf a)

def diffPred (i : Fin 11) (d : Bool) (a : Fin 89) : Bool :=
  canAdjVp i (i + 5 * dir d) (maskOf a) && !canAdjVp i (i + 2 * dir d) (maskOf a)

def gCoeff (k : Fin 11) (a : Fin 89) : ℤ :=
  14 * b2z (hasBit (maskOf a) k) - 5

def mTerm (i : Fin 11) (d : Bool) (a b : Fin 89) : ℤ :=
  let u0a := 1 - 2 * b2z (hasBit (maskOf a) i)
  let u0b := 1 - 2 * b2z (hasBit (maskOf b) i)
  let d1a := b2z (d1Pred i d a)
  let d1b := b2z (d1Pred i d b)
  let v2a := u0a - 2 * b2z (inVp (i + 2 * dir d) (maskOf a)) + b2z (diffPred i d a)
  let v2b := u0b - 2 * b2z (inVp (i + 2 * dir d) (maskOf b)) + b2z (diffPred i d b)
  50 * (u0a * d1b + d1a * u0b) + 25 * v2a * v2b - 4

def mInt (a b : Fin 89) : ℤ :=
  ∑ i : Fin 11, (mTerm i true a b + mTerm i false a b)

def symLG (a b : Fin 89) : ℤ :=
  ∑ k : Fin 11, (Lval (invSh k a) * gCoeff k b + gCoeff k a * Lval (invSh k b))

def certMat (a b : Fin 89) : ℤ :=
  20 * mInt a b + symLG a b

/- Finite decidable checks on `Fin 89` and `Fin 2048`. -/

lemma Lval_nonneg (a : Fin 89) : 0 ≤ Lval a := by
  revert a; decide

lemma maskOf_idxOfMask_chunk (q : Fin 32) (r : Fin 64) :
    isIndepMask (64 * q.1 + r.1) = true →
      maskOf (idxOfMask (64 * q.1 + r.1)) = 64 * q.1 + r.1 := by
  fin_cases q <;> (revert r; decide)

lemma maskOf_idxOfMask (m : ℕ) (hm : m < 2048) :
    isIndepMask m = true → maskOf (idxOfMask m) = m := by
  have hdiv : 64 * (m / 64) + m % 64 = m := Nat.div_add_mod m 64
  have hq : m / 64 < 32 := by omega
  have hr : m % 64 < 64 := Nat.mod_lt m (by decide)
  intro h
  have hchk := maskOf_idxOfMask_chunk ⟨m / 64, hq⟩ ⟨m % 64, hr⟩ (by simpa [hdiv] using h)
  simpa [hdiv] using hchk

lemma invSh1_sh1 (a : Fin 89) : invSh1 (sh1 a) = a := by
  revert a; decide

lemma sh1_invSh1 (a : Fin 89) : sh1 (invSh1 a) = a := by
  revert a; decide

lemma sh1_iter_11 (a : Fin 89) : sh1^[11] a = a := by
  revert a; decide

lemma invSh1_iter_11 (a : Fin 89) : invSh1^[11] a = a := by
  revert a; decide

lemma hasBit_sh1 (a : Fin 89) (k : Fin 11) :
    hasBit (maskOf (sh1 a)) (k + 1) = hasBit (maskOf a) k := by
  revert a k; decide

lemma sh_orb (a : Fin 89) : sh (orbSh a) (rep (orbId a)) = a := by
  revert a; decide

lemma size_cert_true (a : Fin 89) :
    (∑ m : Fin 7, gCoeff (Fin.ofNat 11 m.1) a) ≤
    7 * (2 * (b2z (hasBit (maskOf a) 0) + b2z (inVp 2 (maskOf a)) + b2z (inVp 5 (maskOf a))) - 1) := by
  revert a; decide

lemma size_cert_false (a : Fin 89) :
    (∑ m : Fin 7, gCoeff (Fin.ofNat 11 m.1 * 10) a) ≤
    7 * (2 * (b2z (hasBit (maskOf a) 0) + b2z (inVp 9 (maskOf a)) + b2z (inVp 6 (maskOf a))) - 1) := by
  revert a; decide

lemma certMat_rep_0 (b : Fin 89) : certMat (rep 0) b ≤ 0 := by revert b; decide
lemma certMat_rep_1 (b : Fin 89) : certMat (rep 1) b ≤ 0 := by revert b; decide
lemma certMat_rep_2 (b : Fin 89) : certMat (rep 2) b ≤ 0 := by revert b; decide
lemma certMat_rep_3 (b : Fin 89) : certMat (rep 3) b ≤ 0 := by revert b; decide
lemma certMat_rep_4 (b : Fin 89) : certMat (rep 4) b ≤ 0 := by revert b; decide
lemma certMat_rep_5 (b : Fin 89) : certMat (rep 5) b ≤ 0 := by revert b; decide
lemma certMat_rep_6 (b : Fin 89) : certMat (rep 6) b ≤ 0 := by revert b; decide
lemma certMat_rep_7 (b : Fin 89) : certMat (rep 7) b ≤ 0 := by revert b; decide
lemma certMat_rep_8 (b : Fin 89) : certMat (rep 8) b ≤ 0 := by revert b; decide

lemma certMat_rep (r : Fin 9) (b : Fin 89) : certMat (rep r) b ≤ 0 := by
  fin_cases r
  · exact certMat_rep_0 b
  · exact certMat_rep_1 b
  · exact certMat_rep_2 b
  · exact certMat_rep_3 b
  · exact certMat_rep_4 b
  · exact certMat_rep_5 b
  · exact certMat_rep_6 b
  · exact certMat_rep_7 b
  · exact certMat_rep_8 b

/- `ℤ/11`-invariance of `certMat` and `size_cert`. -/

lemma fin11_ofNat_succ (n : ℕ) : Fin.ofNat 11 (n + 1) = Fin.ofNat 11 n + 1 := by
  apply Fin.ext
  change (n + 1) % 11 = (n % 11 + 1 % 11) % 11
  rw [Nat.add_mod]

lemma fin11_ofNat_self (s : Fin 11) : Fin.ofNat 11 s.1 = s := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt s.2

lemma hasBit_sh1_iter (n : ℕ) (a : Fin 89) (k : Fin 11) :
    hasBit (maskOf (sh1^[n] a)) (k + Fin.ofNat 11 n) = hasBit (maskOf a) k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', fin11_ofNat_succ, ← add_assoc, hasBit_sh1]
    exact ih k

lemma hasBit_sh (s : Fin 11) (a : Fin 89) (k : Fin 11) :
    hasBit (maskOf (sh s a)) (k + s) = hasBit (maskOf a) k := by
  have h := hasBit_sh1_iter s.1 a k
  rwa [fin11_ofNat_self] at h

lemma invSh1_iter_sh1_iter (m n : ℕ) (a : Fin 89) :
    invSh1^[m] (sh1^[n] a) =
      if n ≤ m then invSh1^[m - n] a else sh1^[n - m] a := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply', invSh1_sh1, ih m]
      by_cases h : n ≤ m
      · have h' : n + 1 ≤ m + 1 := by omega
        simp [h, h', Nat.succ_sub_succ]
      · have h' : ¬ n + 1 ≤ m + 1 := by omega
        simp [h, h', Nat.succ_sub_succ]

lemma sh_iter_mod (n : ℕ) (a : Fin 89) : sh1^[n] a = sh1^[n % 11] a := by
  have hdiv : n = n % 11 + 11 * (n / 11) := (Nat.mod_add_div n 11).symm
  conv_lhs => rw [hdiv, Function.iterate_add_apply]
  suffices h : ∀ q (x : Fin 89), sh1^[11 * q] x = x by rw [h]
  intro q x
  induction q generalizing x with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, sh1_iter_11, ih]

lemma invSh_iter_mod (n : ℕ) (a : Fin 89) : invSh1^[n] a = invSh1^[n % 11] a := by
  have hdiv : n = n % 11 + 11 * (n / 11) := (Nat.mod_add_div n 11).symm
  conv_lhs => rw [hdiv, Function.iterate_add_apply]
  suffices h : ∀ q (x : Fin 89), invSh1^[11 * q] x = x by rw [h]
  intro q x
  induction q generalizing x with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, invSh1_iter_11, ih]

lemma sh_invSh_cancel (s : Fin 11) (a : Fin 89) : sh s (invSh s a) = a := by
  have h : ∀ n (x : Fin 89), sh1^[n] (invSh1^[n] x) = x := by
    intro n x
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply', sh1_invSh1, ih]
  exact h s.1 a

lemma invSh_add_sh (k s : Fin 11) (a : Fin 89) :
    invSh (k + s) (sh s a) = invSh k a := by
  unfold invSh sh
  have h1 : (k + s).1 = (k.1 + s.1) % 11 := rfl
  rw [h1, ← invSh_iter_mod (k.1 + s.1), invSh1_iter_sh1_iter]
  simp

lemma inVp_sh (s j : Fin 11) (a : Fin 89) :
    inVp (j + s) (maskOf (sh s a)) = inVp j (maskOf a) := by
  unfold inVp
  rw [add_right_comm j s 10, add_right_comm j s 1, add_right_comm j s 4, add_right_comm j s 7,
    hasBit_sh, hasBit_sh, hasBit_sh, hasBit_sh]

lemma canAdjVp_sh (s i j : Fin 11) (a : Fin 89) :
    canAdjVp (i + s) (j + s) (maskOf (sh s a)) = canAdjVp i j (maskOf a) := by
  unfold canAdjVp
  rw [add_right_comm j s 10, add_right_comm j s 1, add_right_comm j s 4, add_right_comm j s 7,
    hasBit_sh, hasBit_sh, hasBit_sh, hasBit_sh, hasBit_sh]

lemma d1Pred_sh (s i : Fin 11) (d : Bool) (a : Fin 89) :
    d1Pred (i + s) d (sh s a) = d1Pred i d a := by
  unfold d1Pred
  rw [add_right_comm i s (2 * dir d), canAdjVp_sh]

lemma diffPred_sh (s i : Fin 11) (d : Bool) (a : Fin 89) :
    diffPred (i + s) d (sh s a) = diffPred i d a := by
  unfold diffPred
  rw [add_right_comm i s (5 * dir d), add_right_comm i s (2 * dir d), canAdjVp_sh, canAdjVp_sh]

lemma gCoeff_sh (s k : Fin 11) (a : Fin 89) :
    gCoeff (k + s) (sh s a) = gCoeff k a := by
  unfold gCoeff
  rw [hasBit_sh]

lemma mTerm_sh (s i : Fin 11) (d : Bool) (a b : Fin 89) :
    mTerm (i + s) d (sh s a) (sh s b) = mTerm i d a b := by
  unfold mTerm
  rw [add_right_comm i s (2 * dir d)]
  simp only [hasBit_sh, d1Pred_sh, diffPred_sh, inVp_sh]

lemma mInt_sh (s : Fin 11) (a b : Fin 89) :
    mInt (sh s a) (sh s b) = mInt a b := by
  unfold mInt
  symm
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun i => ?_
  change mTerm i true a b + mTerm i false a b =
    mTerm (i + s) true (sh s a) (sh s b) + mTerm (i + s) false (sh s a) (sh s b)
  rw [mTerm_sh, mTerm_sh]

lemma symLG_sh (s : Fin 11) (a b : Fin 89) :
    symLG (sh s a) (sh s b) = symLG a b := by
  unfold symLG
  symm
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun k => ?_
  change Lval (invSh k a) * gCoeff k b + gCoeff k a * Lval (invSh k b) =
    Lval (invSh (k + s) (sh s a)) * gCoeff (k + s) (sh s b) +
      gCoeff (k + s) (sh s a) * Lval (invSh (k + s) (sh s b))
  rw [invSh_add_sh, invSh_add_sh, gCoeff_sh, gCoeff_sh]

lemma certMat_sh (s : Fin 11) (a b : Fin 89) :
    certMat (sh s a) (sh s b) = certMat a b := by
  unfold certMat
  rw [mInt_sh, symLG_sh]

lemma certMat_nonpos (a b : Fin 89) : certMat a b ≤ 0 := by
  have ha : sh (orbSh a) (rep (orbId a)) = a := sh_orb a
  have hb : sh (orbSh a) (invSh (orbSh a) b) = b := sh_invSh_cancel (orbSh a) b
  rw [← ha, ← hb, certMat_sh]
  exact certMat_rep (orbId a) (invSh (orbSh a) b)

lemma size_cert_all (i : Fin 11) (d : Bool) (a : Fin 89) :
    (∑ m : Fin 7, gCoeff (i + Fin.ofNat 11 m.1 * dir d) a) ≤
    7 * (2 * (b2z (hasBit (maskOf a) i) +
      b2z (inVp (i + 2 * dir d) (maskOf a)) +
      b2z (inVp (i + 5 * dir d) (maskOf a))) - 1) := by
  set a0 := invSh i a
  have ha : sh i a0 = a := sh_invSh_cancel i a
  rw [← ha]
  have hsum : (∑ m : Fin 7, gCoeff (i + Fin.ofNat 11 m.1 * dir d) (sh i a0)) =
      ∑ m : Fin 7, gCoeff (Fin.ofNat 11 m.1 * dir d) a0 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_comm i, gCoeff_sh]
  rw [hsum]
  have hb0 : hasBit (maskOf (sh i a0)) i = hasBit (maskOf a0) 0 := by
    simpa using hasBit_sh i a0 0
  have hb1 : inVp (i + 2 * dir d) (maskOf (sh i a0)) = inVp (2 * dir d) (maskOf a0) := by
    rw [add_comm i, inVp_sh]
  have hb2 : inVp (i + 5 * dir d) (maskOf (sh i a0)) = inVp (5 * dir d) (maskOf a0) := by
    rw [add_comm i, inVp_sh]
  rw [hb0, hb1, hb2]
  cases d
  · simpa [dir] using size_cert_false a0
  · simpa [dir] using size_cert_true a0

/- Binary mask decoding on `Fin 11`. -/

lemma pow2_eq (k : Fin 11) : pow2 k = 2 ^ k.1 := by
  fin_cases k <;> rfl

lemma sum_pow2_lt (f : Fin 11 → Bool) :
    (∑ k : Fin 11, if f k then pow2 k else 0) < 2048 := by
  have hle : (∑ k : Fin 11, if f k then pow2 k else 0) ≤ ∑ k : Fin 11, pow2 k := by
    refine Finset.sum_le_sum fun k _ => ?_
    cases f k <;> simp
  have hsum : (∑ k : Fin 11, pow2 k) = 2047 := by decide
  omega

lemma sum_pow2_lo_lt (k : Fin 11) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin 11 => j.1 < k.1), pow2 j) < pow2 k := by
  revert k; decide

lemma hasBit_sum_pow2 (f : Fin 11 → Bool) (k : Fin 11) :
    hasBit (∑ j : Fin 11, if f j then pow2 j else 0) k = f k := by
  let g : Fin 11 → ℕ := fun j => if f j then pow2 j else 0
  let lo : Finset (Fin 11) := Finset.univ.filter fun j => j.1 < k.1
  let hi : Finset (Fin 11) := Finset.univ.filter fun j => k.1 < j.1
  have hsplit : (∑ j : Fin 11, g j) = (∑ j ∈ lo, g j) + g k + ∑ j ∈ hi, g j := by
    have h1 : (Finset.univ : Finset (Fin 11)) = lo ∪ ({k} ∪ hi) := by
      ext j; simp only [lo, hi, Finset.mem_univ, Finset.mem_union, Finset.mem_filter,
        Finset.mem_singleton, true_and, true_iff]
      rcases lt_trichotomy j.1 k.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr h)
    have hd1 : Disjoint lo ({k} ∪ hi) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [lo, hi, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_univ, true_and] at hj1 hj2
      rcases hj2 with rfl | hj2 <;> omega
    have hd2 : Disjoint ({k} : Finset (Fin 11)) hi := by
      rw [Finset.disjoint_singleton_left]
      simp [hi]
    rw [h1, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton, add_assoc]
  have hlo : ∑ j ∈ lo, g j < pow2 k := by
    have hle : ∑ j ∈ lo, g j ≤ ∑ j ∈ lo, pow2 j :=
      Finset.sum_le_sum fun j _ => by dsimp [g]; cases f j <;> simp
    exact lt_of_le_of_lt hle (sum_pow2_lo_lt k)
  have hhi : 2 * pow2 k ∣ ∑ j ∈ hi, g j := by
    refine Finset.dvd_sum fun j hj => ?_
    simp only [hi, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    dsimp [g]
    cases f j
    · simp
    · rw [if_pos rfl, pow2_eq, pow2_eq]
      have hpow : 2 ^ (k.1 + 1) ∣ 2 ^ j.1 := Nat.pow_dvd_pow 2 (by omega)
      simpa [pow_succ, mul_comm] using hpow
  obtain ⟨q, hq⟩ := hhi
  have hpos : 0 < pow2 k := by rw [pow2_eq]; positivity
  rw [show (∑ j : Fin 11, if f j then pow2 j else 0) = (∑ j ∈ lo, g j) + g k + 2 * pow2 k * q from by
    rw [← hq]; exact hsplit]
  unfold hasBit
  have hdiv : ((∑ j ∈ lo, g j) + g k + 2 * pow2 k * q) / pow2 k =
      (if f k then 1 else 0) + 2 * q := by
    have h1 : (∑ j ∈ lo, g j) + g k + 2 * pow2 k * q =
        (∑ j ∈ lo, g j) + ((if f k then 1 else 0) + 2 * q) * pow2 k := by
      dsimp [g]; cases f k <;> simp <;> ring
    rw [h1, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlo, zero_add]
  rw [hdiv]
  cases f k <;> simp

/- Elementary bipartite edge count bound. -/

lemma induce_edgeSet_ncard_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A T1 T2 D1 D2 : Finset V)
    (hA_ind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hT_ind : ∀ u ∈ T1 ∪ T2, ∀ v ∈ T1 ∪ T2, ¬ G.Adj u v)
    (hD1 : ∀ u ∈ A, ∀ v ∈ T1, G.Adj u v → u ∈ D1)
    (hD2 : ∀ u ∈ A, ∀ v ∈ T2, G.Adj u v → u ∈ D2) :
    (G.induce ((A ∪ T1 ∪ T2 : Finset V) : Set V)).edgeSet.ncard ≤
      T1.card * D1.card + T2.card * D2.card := by
  classical
  let W : Finset V := A ∪ T1 ∪ T2
  let emb : Sym2 W ↪ Sym2 V :=
    ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  let Eset : Finset (Sym2 W) := (G.induce (W : Set V)).edgeFinset
  have hncard : (G.induce (W : Set V)).edgeSet.ncard = Eset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hncard]
  let img : Finset (Sym2 V) := Eset.map emb
  have hcard_eq : Eset.card = img.card := (Finset.card_map emb).symm
  rw [hcard_eq]
  let B1 : Finset (Sym2 V) := (T1 ×ˢ D1).image fun p => s(p.1, p.2)
  let B2 : Finset (Sym2 V) := (T2 ×ˢ D2).image fun p => s(p.1, p.2)
  have hsub : img ⊆ B1 ∪ B2 := by
    intro e he
    rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
    rw [SimpleGraph.mem_edgeFinset] at he'
    induction e' using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x.1 y.1 := he'
      have hxW : x.1 ∈ W := x.2
      have hyW : y.1 ∈ W := y.2
      have hmem : ∀ z ∈ W, z ∈ A ∨ z ∈ T1 ∪ T2 := by
        intro z hz
        simp only [W, Finset.mem_union] at hz ⊢
        tauto
      have hsym : emb s(x, y) = s(x.1, y.1) := rfl
      rw [hsym]
      rcases hmem x.1 hxW with hxA | hxT <;> rcases hmem y.1 hyW with hyA | hyT
      · exact False.elim (hA_ind x.1 hxA y.1 hyA hadj)
      · rcases Finset.mem_union.mp hyT with hy1 | hy2
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(y.1, x.1), ?_, Sym2.eq_swap⟩)
          exact Finset.mem_product.mpr ⟨hy1, hD1 x.1 hxA y.1 hy1 hadj⟩
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(y.1, x.1), ?_, Sym2.eq_swap⟩)
          exact Finset.mem_product.mpr ⟨hy2, hD2 x.1 hxA y.1 hy2 hadj⟩
      · rcases Finset.mem_union.mp hxT with hx1 | hx2
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(x.1, y.1), ?_, rfl⟩)
          exact Finset.mem_product.mpr ⟨hx1, hD1 y.1 hyA x.1 hx1 hadj.symm⟩
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x.1, y.1), ?_, rfl⟩)
          exact Finset.mem_product.mpr ⟨hx2, hD2 y.1 hyA x.1 hx2 hadj.symm⟩
      · exact False.elim (hT_ind x.1 hxT y.1 hyT hadj)
  calc
    img.card ≤ (B1 ∪ B2).card := Finset.card_le_card hsub
    _ ≤ B1.card + B2.card := Finset.card_union_le B1 B2
    _ ≤ (T1 ×ˢ D1).card + (T2 ×ˢ D2).card := add_le_add Finset.card_image_le Finset.card_image_le
    _ = T1.card * D1.card + T2.card * D2.card := by rw [Finset.card_product, Finset.card_product]

/- Arithmetic helpers on `Fin 11`. -/

lemma fin11_j1_add1_false (i : Fin 11) : i + 2 * dir false + 1 = i + 10 := by
  fin_cases i <;> decide
lemma fin11_j1_add10_true (i : Fin 11) : i + 2 * dir true + 10 = i + 1 := by
  fin_cases i <;> decide
lemma fin11_j2_add1_false (i : Fin 11) : i + 5 * dir false + 1 = i + 7 := by
  fin_cases i <;> decide
lemma fin11_j2_add10_true (i : Fin 11) : i + 5 * dir true + 10 = i + 4 := by
  fin_cases i <;> decide
lemma fin11_j1_add10_false (i : Fin 11) : i + 2 * dir false + 10 = i + 8 := by
  fin_cases i <;> decide
lemma fin11_j1_add1_true (i : Fin 11) : i + 2 * dir true + 1 = i + 3 := by
  fin_cases i <;> decide
lemma fin11_j2_add10_false (i : Fin 11) : i + 5 * dir false + 10 = i + 5 := by
  fin_cases i <;> decide
lemma fin11_j2_add4_false (i : Fin 11) : i + 5 * dir false + 4 = i + 10 := by
  fin_cases i <;> decide
lemma fin11_j1_add4_false (i : Fin 11) : i + 2 * dir false + 4 = i + 2 := by
  fin_cases i <;> decide
lemma fin11_j2_add7_false (i : Fin 11) : i + 5 * dir false + 7 = i + 2 := by
  fin_cases i <;> decide
lemma fin11_j1_add7_false (i : Fin 11) : i + 2 * dir false + 7 = i + 5 := by
  fin_cases i <;> decide
lemma fin11_j2_add1_true (i : Fin 11) : i + 5 * dir true + 1 = i + 6 := by
  fin_cases i <;> decide
lemma fin11_j1_add4_true (i : Fin 11) : i + 2 * dir true + 4 = i + 6 := by
  fin_cases i <;> decide
lemma fin11_j1_add7_true (i : Fin 11) : i + 2 * dir true + 7 = i + 9 := by
  fin_cases i <;> decide
lemma fin11_j2_add4_true (i : Fin 11) : i + 5 * dir true + 4 = i + 9 := by
  fin_cases i <;> decide
lemma fin11_j2_add7_true (i : Fin 11) : i + 5 * dir true + 7 = i + 1 := by
  fin_cases i <;> decide
lemma fin11_add7_add1 (i : Fin 11) : i + 8 = (i + 7) + 1 := by
  fin_cases i <;> decide
lemma fin11_add3_add1 (i : Fin 11) : i + 4 = (i + 3) + 1 := by
  fin_cases i <;> decide

/- Graph classification and helper lemmas for the Band `And(4)` subcase. -/

lemma no_tri_of_cliqueFree3 {V : Type} {G : SimpleGraph V} (hTF : G.CliqueFree 3)
    {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) : False := by
  classical
  have hcl : G.IsNClique 3 ({u, v, w} : Finset V) := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact (hab rfl).elim
      · exact huv
      · exact huw
      · exact huv.symm
      · exact (hab rfl).elim
      · exact hvw
      · exact huw.symm
      · exact hvw.symm
      · exact (hab rfl).elim
    · have hne1 : u ≠ v := G.ne_of_adj huv
      have hne2 : u ≠ w := G.ne_of_adj huw
      have hne3 : v ≠ w := G.ne_of_adj hvw
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hne3]
      · simp [hne1, hne2]
  exact hTF {u, v, w} hcl

lemma card_filter_vType {V : Type} [Fintype V] [DecidableEq V] (vType : V → Fin 89)
    (P : Fin 89 → Bool) :
    ((Finset.univ.filter fun v : V => P (vType v) = true).card : ℤ) =
    ∑ a : Fin 89, b2z (P a) * ((Finset.univ.filter fun v : V => vType v = a).card : ℤ) := by
  have h1 : (Finset.univ.filter fun v : V => P (vType v) = true).card =
      ∑ a : Fin 89, ((Finset.univ.filter fun v : V => vType v = a).filter fun v => P (vType v) = true).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun h => ⟨vType v, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
    · intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
      exact hab (hv1.1.symm.trans hv2.1)
  rw [h1, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases hPa : P a
  · have hemp : ((Finset.univ.filter fun v : V => vType v = a).filter fun v => P (vType v) = true) = ∅ := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, h⟩; rw [hPa] at h; exact Bool.false_ne_true h
    rw [hemp]; simp [b2z]
  · have hfull : ((Finset.univ.filter fun v : V => vType v = a).filter fun v => P (vType v) = true) =
        (Finset.univ.filter fun v : V => vType v = a) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      rintro rfl; exact hPa
    rw [hfull]; simp [b2z]

lemma pair_quad_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (h50 : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (φ : Fin 11 → V)
    (hφ : ∀ i j : Fin 11, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) → G.Adj (φ i) (φ j))
    (vType : V → Fin 89)
    (hadj_iff : ∀ (v : V) (k : Fin 11), G.Adj (φ k) v ↔ hasBit (maskOf (vType v)) k = true)
    (hg_nonneg : ∀ k : Fin 11,
      0 ≤ ∑ a : Fin 89, gCoeff k a * ((Finset.univ.filter fun v : V => vType v = a).card : ℤ))
    (i : Fin 11) (d : Bool) :
    let n := Fintype.card V
    let S := Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true
    let Vp1 := Finset.univ.filter fun v : V => inVp (i + 2 * dir d) (maskOf (vType v)) = true
    let D1 := Finset.univ.filter fun v : V => d1Pred i d (vType v) = true
    let DIFF := Finset.univ.filter fun v : V => diffPred i d (vType v) = true
    4 * (n : ℤ) ^ 2 <
      100 * ((n : ℤ) - 2 * (S.card : ℤ)) * (D1.card : ℤ) +
      25 * ((n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ) + (DIFF.card : ℤ)) ^ 2 := by
  classical
  dsimp only
  set n : ℕ := Fintype.card V
  set j1 : Fin 11 := i + 2 * dir d
  set j2 : Fin 11 := i + 5 * dir d
  set S : Finset V := Finset.univ.filter fun v => hasBit (maskOf (vType v)) i = true
  set Vp1 : Finset V := Finset.univ.filter fun v => inVp j1 (maskOf (vType v)) = true
  set Vp2 : Finset V := Finset.univ.filter fun v => inVp j2 (maskOf (vType v)) = true
  set D1 : Finset V := Finset.univ.filter fun v => d1Pred i d (vType v) = true
  set DIFF : Finset V := Finset.univ.filter fun v => diffPred i d (vType v) = true
  set D2 : Finset V := Finset.univ.filter fun v => canAdjVp i j2 (maskOf (vType v)) = true
  let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
  have hx_nonneg : ∀ a : Fin 89, 0 ≤ x a := fun a => Nat.cast_nonneg _
  have hn_sum : (n : ℤ) = ∑ a : Fin 89, x a := by
    simpa [n, b2z, x] using card_filter_vType vType (fun _ => true)
  -- `S` is independent and has `2 * |S| + 1 < n`.
  have hS_ind : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact no_tri_of_cliqueFree3 hTF ((hadj_iff u i).mpr hu) huv ((hadj_iff v i).mpr hv)
  have hS_small : 2 * S.card + 1 < n := by
    by_contra! hge
    have h50i := h50 (S : Set V) (by rw [Set.ncard_coe_finset]; exact hge)
    have hzero : (G.induce (S : Set V)).edgeSet.ncard = 0 := by
      have hemp : (G.induce (S : Set V)).edgeSet = ∅ := by
        ext e
        simp only [Set.mem_empty_iff_false, iff_false]
        induction e using Sym2.ind with
        | _ a b => intro h; exact hS_ind a.1 a.2 b.1 b.2 h
      rw [hemp, Set.ncard_empty]
    rw [hzero] at h50i
    nlinarith
  -- Disjointness of `S`, `Vp1`, `Vp2`.
  have h_disj_S_j1 : Disjoint S Vp1 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [S, Vp1, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hv1 hv2
    have hvi : G.Adj (φ i) v := (hadj_iff v i).mpr hv1
    cases d
    · have hvj : G.Adj (φ (i + 10)) v := by
        rw [← fin11_j1_add1_false i]; exact (hadj_iff v _).mpr hv2.1.2
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 10) (by simp)) hvj hvi
    · have hvj : G.Adj (φ (i + 1)) v := by
        rw [← fin11_j1_add10_true i]; exact (hadj_iff v _).mpr hv2.1.1
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 1) (by simp)) hvj hvi
  have h_disj_S_j2 : Disjoint S Vp2 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [S, Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hv1 hv2
    have hvi : G.Adj (φ i) v := (hadj_iff v i).mpr hv1
    cases d
    · have hvj : G.Adj (φ (i + 7)) v := by
        rw [← fin11_j2_add1_false i]; exact (hadj_iff v _).mpr hv2.1.2
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 7) (by simp)) hvj hvi
    · have hvj : G.Adj (φ (i + 4)) v := by
        rw [← fin11_j2_add10_true i]; exact (hadj_iff v _).mpr hv2.1.1
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 4) (by simp)) hvj hvi
  have h_disj_j1_j2 : Disjoint Vp1 Vp2 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Vp1, Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hv1 hv2
    cases d
    · have h1 : G.Adj (φ (i + 8)) v := by
        rw [← fin11_j1_add10_false i]; exact (hadj_iff v _).mpr hv1.1.1
      have h2 : G.Adj (φ (i + 7)) v := by
        rw [← fin11_j2_add1_false i]; exact (hadj_iff v _).mpr hv2.1.2
      have hphi : G.Adj (φ (i + 7)) (φ (i + 8)) := hφ (i + 7) (i + 8) (Or.inl (fin11_add7_add1 i))
      exact no_tri_of_cliqueFree3 hTF hphi h1 h2
    · have h1 : G.Adj (φ (i + 3)) v := by
        rw [← fin11_j1_add1_true i]; exact (hadj_iff v _).mpr hv1.1.2
      have h2 : G.Adj (φ (i + 4)) v := by
        rw [← fin11_j2_add10_true i]; exact (hadj_iff v _).mpr hv2.1.1
      have hphi : G.Adj (φ (i + 3)) (φ (i + 4)) := hφ (i + 3) (i + 4) (Or.inl (fin11_add3_add1 i))
      exact no_tri_of_cliqueFree3 hTF hphi h2 h1
  -- Independence of `Vp1 ∪ Vp2`.
  have hVp_ind : ∀ u ∈ Vp1 ∪ Vp2, ∀ v ∈ Vp1 ∪ Vp2, ¬ G.Adj u v := by
    have hcomm : ∀ u ∈ Vp1, ∀ v ∈ Vp2, ∃ k : Fin 11, G.Adj (φ k) u ∧ G.Adj (φ k) v := by
      intro u hu v hv
      simp only [Vp1, Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp,
        Bool.and_eq_true, Bool.or_eq_true] at hu hv
      cases d
      · have hu10 : G.Adj (φ (i + 10)) u := by
          rw [← fin11_j1_add1_false i]; exact (hadj_iff u _).mpr hu.1.2
        have hv5 : G.Adj (φ (i + 5)) v := by
          rw [← fin11_j2_add10_false i]; exact (hadj_iff v _).mpr hv.1.1
        rcases hv.2 with hv10 | hv2
        · refine ⟨i + 10, hu10, ?_⟩
          rw [← fin11_j2_add4_false i]; exact (hadj_iff v _).mpr hv10
        · rcases hu.2 with hu2 | hu5
          · refine ⟨i + 2, ?_, ?_⟩
            · rw [← fin11_j1_add4_false i]; exact (hadj_iff u _).mpr hu2
            · rw [← fin11_j2_add7_false i]; exact (hadj_iff v _).mpr hv2
          · refine ⟨i + 5, ?_, hv5⟩
            rw [← fin11_j1_add7_false i]; exact (hadj_iff u _).mpr hu5
      · have hu1 : G.Adj (φ (i + 1)) u := by
          rw [← fin11_j1_add10_true i]; exact (hadj_iff u _).mpr hu.1.1
        have hv6 : G.Adj (φ (i + 6)) v := by
          rw [← fin11_j2_add1_true i]; exact (hadj_iff v _).mpr hv.1.2
        rcases hv.2 with hv9 | hv1
        · rcases hu.2 with hu6 | hu9
          · refine ⟨i + 6, ?_, hv6⟩
            rw [← fin11_j1_add4_true i]; exact (hadj_iff u _).mpr hu6
          · refine ⟨i + 9, ?_, ?_⟩
            · rw [← fin11_j1_add7_true i]; exact (hadj_iff u _).mpr hu9
            · rw [← fin11_j2_add4_true i]; exact (hadj_iff v _).mpr hv9
        · refine ⟨i + 1, hu1, ?_⟩
          rw [← fin11_j2_add7_true i]; exact (hadj_iff v _).mpr hv1
    intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu1 | hu2 <;> rcases Finset.mem_union.mp hv with hv1 | hv2
    · simp only [Vp1, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hu1 hv1
      exact no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr hu1.1.2) huv ((hadj_iff v _).mpr hv1.1.2)
    · obtain ⟨k, hku, hkv⟩ := hcomm u hu1 v hv2
      exact no_tri_of_cliqueFree3 hTF hku huv hkv
    · obtain ⟨k, hkv, hku⟩ := hcomm v hv1 u hu2
      exact no_tri_of_cliqueFree3 hTF hku huv hkv
    · simp only [Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hu2 hv2
      exact no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr hu2.1.2) huv ((hadj_iff v _).mpr hv2.1.2)
  -- Size bound `n ≤ 2 * (|S| + |Vp1| + |Vp2|)`.
  have hsize : n ≤ 2 * (S.card + Vp1.card + Vp2.card) := by
    have hsum_cert :
        (∑ m : Fin 7, ∑ a : Fin 89, gCoeff (i + Fin.ofNat 11 m.1 * dir d) a * x a) ≤
        ∑ a : Fin 89, 7 * (2 * (b2z (hasBit (maskOf a) i) +
          b2z (inVp j1 (maskOf a)) + b2z (inVp j2 (maskOf a))) - 1) * x a := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (size_cert_all i d a) (hx_nonneg a)
    have hlhs : 0 ≤ ∑ m : Fin 7, ∑ a : Fin 89, gCoeff (i + Fin.ofNat 11 m.1 * dir d) a * x a :=
      Finset.sum_nonneg fun m _ => hg_nonneg _
    have hrhs : (∑ a : Fin 89, 7 * (2 * (b2z (hasBit (maskOf a) i) +
          b2z (inVp j1 (maskOf a)) + b2z (inVp j2 (maskOf a))) - 1) * x a) =
        7 * (2 * ((S.card : ℤ) + (Vp1.card : ℤ) + (Vp2.card : ℤ)) - (n : ℤ)) := by
      have hS := card_filter_vType vType (fun a => hasBit (maskOf a) i)
      have hV1 := card_filter_vType vType (fun a => inVp j1 (maskOf a))
      have hV2 := card_filter_vType vType (fun a => inVp j2 (maskOf a))
      have hlin : ∀ a : Fin 89,
          7 * (2 * (b2z (hasBit (maskOf a) i) + b2z (inVp j1 (maskOf a)) +
            b2z (inVp j2 (maskOf a))) - 1) * x a =
          14 * (b2z (hasBit (maskOf a) i) * x a) +
          14 * (b2z (inVp j1 (maskOf a)) * x a) +
          14 * (b2z (inVp j2 (maskOf a)) * x a) - 7 * x a := fun a => by ring
      simp_rw [hlin, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      change 14 * (∑ a : Fin 89, b2z (hasBit (maskOf a) i) * x a) +
        14 * (∑ a : Fin 89, b2z (inVp j1 (maskOf a)) * x a) +
        14 * (∑ a : Fin 89, b2z (inVp j2 (maskOf a)) * x a) - 7 * (∑ a : Fin 89, x a) = _
      rw [← hS, ← hV1, ← hV2, ← hn_sum]
      ring
    have hge := hlhs.trans (hsum_cert.trans_eq hrhs)
    omega
  -- Adjacency containment in `D1` and `D2`.
  have hadj_vp : ∀ (j : Fin 11) (u : V), u ∈ S →
      ∀ v : V, inVp j (maskOf (vType v)) = true → G.Adj u v →
        canAdjVp i j (maskOf (vType u)) = true := by
    intro j u hu v hv huv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [inVp, Bool.and_eq_true, Bool.or_eq_true] at hv
    unfold canAdjVp
    have hn10 : hasBit (maskOf (vType u)) (j + 10) = false := by
      cases h : hasBit (maskOf (vType u)) (j + 10)
      · rfl
      · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h) huv ((hadj_iff v _).mpr hv.1.1))
    have hn1 : hasBit (maskOf (vType u)) (j + 1) = false := by
      cases h : hasBit (maskOf (vType u)) (j + 1)
      · rfl
      · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h) huv ((hadj_iff v _).mpr hv.1.2))
    have hn47 : (hasBit (maskOf (vType u)) (j + 4) && hasBit (maskOf (vType u)) (j + 7)) = false := by
      cases h4 : hasBit (maskOf (vType u)) (j + 4)
      · simp
      · cases h7 : hasBit (maskOf (vType u)) (j + 7)
        · simp
        · rcases hv.2 with hv4 | hv7
          · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h4) huv ((hadj_iff v _).mpr hv4))
          · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h7) huv ((hadj_iff v _).mpr hv7))
    simp [hu, hn10, hn1, hn47]
  -- Pick subsets `T1 ⊆ Vp1` and `T2 ⊆ Vp2` of total size `t = n / 2 - |S|`.
  let t : ℕ := n / 2 - S.card
  let r1 : ℕ := min t Vp1.card
  let r2 : ℕ := t - r1
  have hr1_le : r1 ≤ Vp1.card := min_le_right _ _
  have hr2_le : r2 ≤ Vp2.card := by omega
  obtain ⟨T1, hT1_sub, hT1_card⟩ := Finset.exists_subset_card_eq hr1_le
  obtain ⟨T2, hT2_sub, hT2_card⟩ := Finset.exists_subset_card_eq hr2_le
  have hdisj_ST1 : Disjoint S T1 := Disjoint.mono_right hT1_sub h_disj_S_j1
  have hdisj_ST2 : Disjoint S T2 := Disjoint.mono_right hT2_sub h_disj_S_j2
  have hdisj_T12 : Disjoint T1 T2 := Disjoint.mono hT1_sub hT2_sub h_disj_j1_j2
  have hW_card : (S ∪ T1 ∪ T2).card = n / 2 := by
    have hdisj_ST1_T2 : Disjoint (S ∪ T1) T2 := Finset.disjoint_union_left.mpr ⟨hdisj_ST2, hdisj_T12⟩
    rw [Finset.card_union_of_disjoint hdisj_ST1_T2, Finset.card_union_of_disjoint hdisj_ST1,
      hT1_card, hT2_card]
    omega
  have hW_half : 2 * ((S ∪ T1 ∪ T2 : Finset V) : Set V).ncard + 1 ≥ n := by
    rw [Set.ncard_coe_finset, hW_card]; omega
  have h50W := h50 ((S ∪ T1 ∪ T2 : Finset V) : Set V) hW_half
  have hedge : (G.induce ((S ∪ T1 ∪ T2 : Finset V) : Set V)).edgeSet.ncard ≤
      T1.card * D1.card + T2.card * D2.card := by
    refine induce_edgeSet_ncard_le G S T1 T2 D1 D2 hS_ind ?_ ?_ ?_
    · intro u hu v hv
      exact hVp_ind u (Finset.union_subset_union hT1_sub hT2_sub hu)
        v (Finset.union_subset_union hT1_sub hT2_sub hv)
    · intro u hu v hv huv
      have hv1 := (Finset.mem_filter.mp (hT1_sub hv)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj_vp j1 u hu v hv1 huv⟩
    · intro u hu v hv huv
      have hv2 := (Finset.mem_filter.mp (hT2_sub hv)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj_vp j2 u hu v hv2 huv⟩
  have hD2_le : D2.card ≤ D1.card + DIFF.card := by
    have hsub : D2 ⊆ D1 ∪ DIFF := by
      intro v hv
      have hv2 : canAdjVp i j2 (maskOf (vType v)) = true := (Finset.mem_filter.mp hv).2
      cases h1 : canAdjVp i j1 (maskOf (vType v))
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩)
        dsimp only [diffPred]
        rw [show i + 5 * dir d = j2 from rfl, show i + 2 * dir d = j1 from rfl, hv2, h1]
        rfl
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩)
        exact h1
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hgt : n ^ 2 < 50 * (t * D1.card + r2 * DIFF.card) := by
    have hr : r1 + r2 = t := by omega
    have h1 : T1.card * D1.card + T2.card * D2.card ≤ t * D1.card + r2 * DIFF.card := by
      rw [hT1_card, hT2_card]
      calc
        r1 * D1.card + r2 * D2.card
            ≤ r1 * D1.card + r2 * (D1.card + DIFF.card) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left r2 hD2_le) _
        _ = (r1 + r2) * D1.card + r2 * DIFF.card := by ring
        _ = t * D1.card + r2 * DIFF.card := by rw [hr]
    omega
  have hgtZ : (n : ℤ) ^ 2 < 50 * ((t : ℤ) * (D1.card : ℤ) + (r2 : ℤ) * (DIFF.card : ℤ)) := by
    exact_mod_cast hgt
  have htZ : 2 * (t : ℤ) ≤ (n : ℤ) - 2 * (S.card : ℤ) := by omega
  have hr2_bound : 8 * (r2 : ℤ) * (DIFF.card : ℤ) ≤
      ((n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ) + (DIFF.card : ℤ)) ^ 2 := by
    set U : ℤ := (n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ)
    set Y : ℤ := (DIFF.card : ℤ)
    have hY : 0 ≤ Y := Nat.cast_nonneg _
    have hr2_0 : 0 ≤ (r2 : ℤ) := Nat.cast_nonneg _
    by_cases hcase : t ≤ Vp1.card
    · have hr2_zero : (r2 : ℤ) = 0 := by omega
      rw [hr2_zero]; nlinarith
    · have h2r2 : 2 * (r2 : ℤ) ≤ U := by omega
      nlinarith [sq_nonneg (U - Y)]
  have hD1_nonneg : (0 : ℤ) ≤ (D1.card : ℤ) := Nat.cast_nonneg _
  have h100 : 200 * (t : ℤ) * (D1.card : ℤ) ≤ 100 * ((n : ℤ) - 2 * (S.card : ℤ)) * (D1.card : ℤ) := by
    nlinarith
  linarith

lemma mTerm_sum_identity {V : Type} [Fintype V] [DecidableEq V] (vType : V → Fin 89)
    (i : Fin 11) (d : Bool) :
    let n := Fintype.card V
    let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
    let S := Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true
    let Vp1 := Finset.univ.filter fun v : V => inVp (i + 2 * dir d) (maskOf (vType v)) = true
    let D1 := Finset.univ.filter fun v : V => d1Pred i d (vType v) = true
    let DIFF := Finset.univ.filter fun v : V => diffPred i d (vType v) = true
    100 * ((n : ℤ) - 2 * (S.card : ℤ)) * (D1.card : ℤ) +
    25 * ((n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ) + (DIFF.card : ℤ)) ^ 2 - 4 * (n : ℤ) ^ 2 =
    ∑ a : Fin 89, ∑ b : Fin 89, mTerm i d a b * x a * x b := by
  dsimp only
  set n : ℕ := Fintype.card V
  let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
  have hn_sum : (n : ℤ) = ∑ a : Fin 89, x a := by
    simpa [n, b2z, x] using card_filter_vType vType (fun _ => true)
  let u0 : Fin 89 → ℤ := fun a => 1 - 2 * b2z (hasBit (maskOf a) i)
  let d1 : Fin 89 → ℤ := fun a => b2z (d1Pred i d a)
  let v2 : Fin 89 → ℤ := fun a => u0 a - 2 * b2z (inVp (i + 2 * dir d) (maskOf a)) + b2z (diffPred i d a)
  have hU0 : (n : ℤ) - 2 * ((Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true).card : ℤ) =
      ∑ a : Fin 89, u0 a * x a := by
    have hS := card_filter_vType vType (fun a => hasBit (maskOf a) i)
    rw [hn_sum, hS]
    simp only [u0, sub_mul, one_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, x]
  have hD1 : ((Finset.univ.filter fun v : V => d1Pred i d (vType v) = true).card : ℤ) =
      ∑ a : Fin 89, d1 a * x a := card_filter_vType vType (d1Pred i d)
  have hV2 : (n : ℤ) - 2 * ((Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true).card : ℤ) -
      2 * ((Finset.univ.filter fun v : V => inVp (i + 2 * dir d) (maskOf (vType v)) = true).card : ℤ) +
      ((Finset.univ.filter fun v : V => diffPred i d (vType v) = true).card : ℤ) =
      ∑ a : Fin 89, v2 a * x a := by
    have hVp := card_filter_vType vType (fun a => inVp (i + 2 * dir d) (maskOf a))
    have hDf := card_filter_vType vType (diffPred i d)
    rw [hU0, hVp, hDf]
    simp only [v2, add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, x]
  rw [hV2, hU0, hD1, hn_sum]
  have hbilin : ∀ f g : Fin 89 → ℤ,
      (∑ a : Fin 89, f a * x a) * (∑ b : Fin 89, g b * x b) =
      ∑ a : Fin 89, ∑ b : Fin 89, (f a * g b) * x a * x b := by
    intro f g
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => by ring
  have h100 : 100 * (∑ a : Fin 89, u0 a * x a) * (∑ b : Fin 89, d1 b * x b) =
      50 * ((∑ a : Fin 89, u0 a * x a) * (∑ b : Fin 89, d1 b * x b)) +
      50 * ((∑ a : Fin 89, d1 a * x a) * (∑ b : Fin 89, u0 b * x b)) := by
    have hsym : (∑ a : Fin 89, u0 a * x a) * (∑ b : Fin 89, d1 b * x b) =
        (∑ a : Fin 89, d1 a * x a) * (∑ b : Fin 89, u0 b * x b) := mul_comm _ _
    linarith
  rw [h100, sq, sq, hbilin u0 d1, hbilin d1 u0, hbilin v2 v2]
  have h11 : (∑ a : Fin 89, x a) * (∑ b : Fin 89, x b) =
      ∑ a : Fin 89, ∑ b : Fin 89, (1 : ℤ) * x a * x b := by
    simpa using hbilin (fun _ => 1) (fun _ => 1)
  rw [h11]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  dsimp [mTerm, u0, d1, v2]; ring

/- Main proof of `H2`. -/

theorem main_proof : OMA.R_Erdos128_erdos_128_R2_H1_R1.H2 := by
  classical
  intro V _ G hTF _hmax h50 hδ _h3 _hnoG ⟨φ, hφ⟩
  let vMask : V → ℕ := fun v => ∑ k : Fin 11, if decide (G.Adj (φ k) v) then pow2 k else 0
  have hvMask_lt : ∀ v : V, vMask v < 2048 := fun v => sum_pow2_lt (fun k => decide (G.Adj (φ k) v))
  have hbit_vMask : ∀ (v : V) (k : Fin 11), hasBit (vMask v) k = decide (G.Adj (φ k) v) :=
    fun v k => hasBit_sum_pow2 (fun j => decide (G.Adj (φ j) v)) k
  have hisIndep : ∀ v : V, isIndepMask (vMask v) = true := by
    intro v
    unfold isIndepMask
    rw [List.all_eq_true]
    intro i _
    by_cases hi : G.Adj (φ i) v
    · have hb_i : hasBit (vMask v) i = true := by rw [hbit_vMask]; simp [hi]
      have hnot : ∀ d : Fin 11, (d = 1 ∨ d = 4 ∨ d = 7 ∨ d = 10) →
          hasBit (vMask v) (i + d) = false := by
        intro d hd
        rw [hbit_vMask, decide_eq_false_iff_not]
        intro h2
        have hphi : G.Adj (φ i) (φ (i + d)) := by
          apply hφ i (i + d)
          rcases hd with rfl | rfl | rfl | rfl <;> simp
        exact no_tri_of_cliqueFree3 hTF hphi h2 hi
      rw [hb_i, hnot 1 (by simp), hnot 4 (by simp), hnot 7 (by simp), hnot 10 (by simp)]
      rfl
    · have hb_i : hasBit (vMask v) i = false := by rw [hbit_vMask]; simp [hi]
      rw [hb_i]; rfl
  let vType : V → Fin 89 := fun v => idxOfMask (vMask v)
  have hmask_eq : ∀ v : V, maskOf (vType v) = vMask v := fun v =>
    maskOf_idxOfMask (vMask v) (hvMask_lt v) (hisIndep v)
  have hadj_iff : ∀ (v : V) (k : Fin 11), G.Adj (φ k) v ↔ hasBit (maskOf (vType v)) k = true := by
    intro v k
    rw [hmask_eq, hbit_vMask, decide_eq_true_eq]
  let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
  have hx_nonneg : ∀ a : Fin 89, 0 ≤ x a := fun a => Nat.cast_nonneg _
  have hn_sum : (Fintype.card V : ℤ) = ∑ a : Fin 89, x a := by
    simpa [b2z, x] using card_filter_vType vType (fun _ => true)
  have hg_nonneg : ∀ k : Fin 11, 0 ≤ ∑ a : Fin 89, gCoeff k a * x a := by
    intro k
    let Sk : Finset V := Finset.univ.filter fun v => hasBit (maskOf (vType v)) k = true
    have hset : (Sk : Set V) = G.neighborSet (φ k) := by
      ext v
      simp only [Sk, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborSet]
      exact (hadj_iff v k).symm
    have hdeg : 5 * Fintype.card V ≤ 14 * Sk.card := by
      have hcard : (G.neighborSet (φ k)).ncard = Sk.card := by rw [← hset, Set.ncard_coe_finset]
      rw [← hcard]; exact hδ (φ k)
    have h1 : (∑ a : Fin 89, gCoeff k a * x a) = 14 * (Sk.card : ℤ) - 5 * (Fintype.card V : ℤ) := by
      have hS := card_filter_vType vType (fun a => hasBit (maskOf a) k)
      change (∑ a : Fin 89, (14 * b2z (hasBit (maskOf a) k) - 5) * x a) = _
      simp_rw [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
      change 14 * (∑ a : Fin 89, b2z (hasBit (maskOf a) k) * x a) - 5 * (∑ a : Fin 89, x a) = _
      rw [← hS, ← hn_sum]
    rw [h1]
    omega
  have hsum_pos : (0 : ℤ) < ∑ a : Fin 89, ∑ b : Fin 89, mInt a b * x a * x b := by
    have h22 : (0 : ℤ) < ∑ i : Fin 11,
        ((∑ a : Fin 89, ∑ b : Fin 89, mTerm i true a b * x a * x b) +
         (∑ a : Fin 89, ∑ b : Fin 89, mTerm i false a b * x a * x b)) := by
      refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
      have ht := pair_quad_bound G hTF h50 φ hφ vType hadj_iff hg_nonneg i true
      have hf := pair_quad_bound G hTF h50 φ hφ vType hadj_iff hg_nonneg i false
      have hteq := mTerm_sum_identity vType i true
      have hfeq := mTerm_sum_identity vType i false
      dsimp only at ht hf hteq hfeq
      linarith
    refine lt_of_lt_of_eq h22 ?_
    simp_rw [← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold mInt
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hLG_nonneg : (0 : ℤ) ≤ ∑ a : Fin 89, ∑ b : Fin 89, symLG a b * x a * x b := by
    have heq : (∑ a : Fin 89, ∑ b : Fin 89, symLG a b * x a * x b) =
        2 * ∑ k : Fin 11, (∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b) := by
      have hterm : ∀ k : Fin 11,
          2 * ((∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b)) =
          ∑ a : Fin 89, ∑ b : Fin 89,
            (Lval (invSh k a) * gCoeff k b + gCoeff k a * Lval (invSh k b)) * x a * x b := by
        intro k
        have h1 : (∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b) =
            ∑ a : Fin 89, ∑ b : Fin 89, (Lval (invSh k a) * gCoeff k b) * x a * x b := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring
        have h2 : (∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b) =
            ∑ a : Fin 89, ∑ b : Fin 89, (gCoeff k a * Lval (invSh k b)) * x a * x b := by
          rw [mul_comm, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring
        calc
          2 * ((∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b))
              = (∑ a : Fin 89, ∑ b : Fin 89, (Lval (invSh k a) * gCoeff k b) * x a * x b) +
                (∑ a : Fin 89, ∑ b : Fin 89, (gCoeff k a * Lval (invSh k b)) * x a * x b) := by
                  rw [← h1, ← h2]; ring
          _ = _ := by
                simp only [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [Finset.mul_sum]
      simp_rw [hterm]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold symLG
      simp only [Finset.sum_mul]
    rw [heq]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => ?_)
    exact mul_nonneg
      (Finset.sum_nonneg fun a _ => mul_nonneg (Lval_nonneg _) (hx_nonneg a))
      (hg_nonneg k)
  have hcomb_pos : (0 : ℤ) < ∑ a : Fin 89, ∑ b : Fin 89, certMat a b * x a * x b := by
    have heq : (∑ a : Fin 89, ∑ b : Fin 89, certMat a b * x a * x b) =
        20 * (∑ a : Fin 89, ∑ b : Fin 89, mInt a b * x a * x b) +
        (∑ a : Fin 89, ∑ b : Fin 89, symLG a b * x a * x b) := by
      simp only [certMat, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [heq]
    linarith
  have hcomb_nonpos : (∑ a : Fin 89, ∑ b : Fin 89, certMat a b * x a * x b) ≤ 0 := by
    refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => ?_
    have hxy : 0 ≤ x a * x b := mul_nonneg (hx_nonneg a) (hx_nonneg b)
    have hmul : certMat a b * (x a * x b) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (certMat_nonpos a b) hxy
    linarith
  linarith

end Erdos128_R2_H1_R1_H2

theorem OMA.solution : OMA.R_Erdos128_erdos_128_R2_H1_R1.H2 :=
  Erdos128_R2_H1_R1_H2.main_proof
