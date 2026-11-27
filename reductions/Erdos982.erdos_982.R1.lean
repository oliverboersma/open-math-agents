import FormalConjectures.ErdosProblems.«982»
import Mathlib

/-! The Euclidean distance and acute-angle constraints, the finite Boolean
encoding, the reversal and deletion lemmas, and the certificates come from
Arhan Canli, Quantavane, arhancanli/quantavane-lean at
76a54a6c728161e75e1b0275c0b32ffc311f1f6a, Apache-2.0.
The submitted certificate checks use kernel reduction. -/


section
/-
Erdős #982, round 2 (geometry): oriented-angle signs as coordinate determinants (from E982B.Geom), and the
algebraic cores of the two lemmas used by the finite check:
  * `side_core`: four vertices in cyclic order and an affine function (here `d2 · u - d2 · w`): the half-plane rule.
  * `acute_of_le_left/right`, `cone_pos`, `quad_not_all_acute`: no four acute angles in a convex polygon.
Stated for `ℝ²`.
-/


open EuclideanGeometry

namespace E982C

/-- The orientation determinant matching `∡ a b c` (see `sign_oangle_eq`). -/
private noncomputable def o3 (a b c : ℝ²) : ℝ := (a 0 - b 0) * (c 1 - b 1) - (a 1 - b 1) * (c 0 - b 0)

theorem o3_rotate (a b c : ℝ²) : o3 b c a = o3 a b c := by unfold o3; ring
theorem o3_swap (a b c : ℝ²) : o3 a c b = - o3 a b c := by unfold o3; ring

theorem areaForm_eq_mul_sin (x y : ℝ²) :
    (positiveOrientation (R := ℝ) (M := ℝ²) (ι := Fin 2)).areaForm x y =
      ‖x‖ * ‖y‖ * Real.Angle.sin ((positiveOrientation (R := ℝ) (M := ℝ²) (ι := Fin 2)).oangle x y) := by
  set o := positiveOrientation (R := ℝ) (M := ℝ²) (ι := Fin 2)
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Orientation.oangle, Real.Angle.sin_coe, Complex.sin_arg, o.norm_kahler]
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have him : (o.kahler x y).im = o.areaForm x y := by
    simp [Orientation.kahler_apply_apply, Complex.real_smul]
  rw [him]
  field_simp

theorem areaForm_eq_o3 (a b c : ℝ²) :
    (positiveOrientation (R := ℝ) (M := ℝ²) (ι := Fin 2)).areaForm (a -ᵥ b) (c -ᵥ b) = o3 a b c := by
  have h := triangle_area_eq_det a c b
  unfold triangle_area at h
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.head_fin_const] at h
  unfold o3
  linarith

theorem sign_oangle_eq (a b c : ℝ²) : (∡ a b c).sign = SignType.sign (o3 a b c) := by
  rw [← areaForm_eq_o3]
  unfold EuclideanGeometry.oangle Real.Angle.sign
  rw [areaForm_eq_mul_sin]
  set x := a -ᵥ b
  set y := c -ᵥ b
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  have hpos : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hy)
  rw [sign_mul, sign_pos hpos, one_mul]

/-! Squared distances in coordinates. -/

private noncomputable def d2 (a b : ℝ²) : ℝ := (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2

theorem d2_nonneg (a b : ℝ²) : 0 ≤ d2 a b := by unfold d2; positivity

theorem d2_comm (a b : ℝ²) : d2 a b = d2 b a := by unfold d2; ring

theorem d2_self (a : ℝ²) : d2 a a = 0 := by unfold d2; ring

theorem dist_eq_sqrt_d2 (a b : ℝ²) : dist a b = Real.sqrt (d2 a b) := by
  rw [EuclideanSpace.dist_eq]
  simp [d2, Fin.sum_univ_two, Real.dist_eq, sq_abs]

theorem dist_eq_iff_d2 (a b c d : ℝ²) : dist a b = dist c d ↔ d2 a b = d2 c d := by
  rw [dist_eq_sqrt_d2, dist_eq_sqrt_d2]
  exact Real.sqrt_inj (d2_nonneg _ _) (d2_nonneg _ _)

theorem dist_lt_iff_d2 (a b c d : ℝ²) : dist a b < dist c d ↔ d2 a b < d2 c d := by
  rw [dist_eq_sqrt_d2, dist_eq_sqrt_d2]
  exact Real.sqrt_lt_sqrt_iff (d2_nonneg _ _)

theorem d2_pos {a b : ℝ²} (h : a ≠ b) : 0 < d2 a b := by
  rcases (d2_nonneg a b).lt_or_eq with h' | h'
  · exact h'
  · exfalso; apply h
    have h0 : (a 0 - b 0) ^ 2 = 0 := by unfold d2 at h'; nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
    have h1 : (a 1 - b 1) ^ 2 = 0 := by unfold d2 at h'; nlinarith [sq_nonneg (a 0 - b 0), sq_nonneg (a 1 - b 1)]
    ext i
    fin_cases i
    · simpa [sub_eq_zero] using h0
    · simpa [sub_eq_zero] using h1

/-! The half-plane rule. -/

/-- Four points `u, y, z, w` in cyclic order (all four triangle orientations of one strict sign `σ`): if `z` is not
farther from `u` than from `w`, then `y` is strictly nearer to `u` than to `w`. The function
`F p = d2 p u - d2 p w` is affine, and four points satisfy
`o3 u z w * F y = o3 y z w * F u + o3 u y w * F z - o3 u y z * F w`. -/
theorem side_core {u w y z : ℝ²} (huw : u ≠ w) (σ : ℝ)
    (h1 : 0 < σ * o3 u y z) (h2 : 0 < σ * o3 u y w) (h3 : 0 < σ * o3 u z w) (h4 : 0 < σ * o3 y z w)
    (hz : d2 z u ≤ d2 z w) : d2 y u < d2 y w := by
  have hd := d2_pos huw
  have key : o3 u z w * (d2 y u - d2 y w) =
      o3 y z w * (d2 u u - d2 u w) + o3 u y w * (d2 z u - d2 z w) - o3 u y z * (d2 w u - d2 w w) := by
    unfold o3 d2; ring
  rw [d2_self, d2_self, d2_comm w u] at key
  have k2 : (σ * o3 u z w) * (d2 y u - d2 y w) =
      (σ * o3 y z w) * (0 - d2 u w) + (σ * o3 u y w) * (d2 z u - d2 z w) - (σ * o3 u y z) * (d2 u w - 0) := by
    rw [mul_assoc, key]; ring
  have t1 : (σ * o3 y z w) * (0 - d2 u w) < 0 := mul_neg_of_pos_of_neg h4 (by linarith)
  have t2 : (σ * o3 u y w) * (d2 z u - d2 z w) ≤ 0 := by nlinarith
  have t3 : 0 < (σ * o3 u y z) * (d2 u w - 0) := mul_pos h1 (by linarith)
  have t4 : (σ * o3 u z w) * (d2 y u - d2 y w) < 0 := by rw [k2]; linarith
  by_contra hc
  push_neg at hc
  have : 0 ≤ (σ * o3 u z w) * (d2 y u - d2 y w) := mul_nonneg h3.le (by linarith)
  linarith

/-! Acute angles. -/

/-- `dt a b c`: the dot product of `a - b` and `c - b` (positive iff the angle at `b` is acute). -/
private noncomputable def dt (a b c : ℝ²) : ℝ := (a 0 - b 0) * (c 0 - b 0) + (a 1 - b 1) * (c 1 - b 1)

theorem cosine (a b c : ℝ²) : d2 a c = d2 a b + d2 b c - 2 * dt a b c := by unfold d2 dt; ring

theorem acute_of_le_left {a b c : ℝ²} (hbc : b ≠ c) (h : d2 a c ≤ d2 a b) : 0 < dt a b c := by
  have := cosine a b c
  have := d2_pos hbc
  linarith

theorem acute_of_le_right {a b c : ℝ²} (hab : a ≠ b) (h : d2 a c ≤ d2 b c) : 0 < dt a b c := by
  have := cosine a b c
  have := d2_pos hab
  linarith

theorem cone_identity (a v b x : ℝ²) (k : Fin 2) :
    o3 a v b * (x k - v k) = o3 x v b * (a k - v k) + o3 a v x * (b k - v k) := by
  fin_cases k <;> simp [o3] <;> ring

theorem cone_dot_identity (a v b x y : ℝ²) :
    dt x v y * (o3 a v b) ^ 2 = o3 x v b * o3 y v b * d2 a v +
      (o3 x v b * o3 a v y + o3 a v x * o3 y v b) * dt a v b + o3 a v x * o3 a v y * d2 b v := by
  unfold dt o3 d2; ring

theorem cone_coeff_pos {a v b x : ℝ²} (hO : 0 < o3 a v b) (hx : x ≠ v)
    (h1 : 0 ≤ o3 x v b) (h2 : 0 ≤ o3 a v x) : 0 < o3 x v b + o3 a v x := by
  rcases (add_nonneg h1 h2).lt_or_eq with h | h
  · exact h
  · exfalso
    have e1 : o3 x v b = 0 := by linarith
    have e2 : o3 a v x = 0 := by linarith
    apply hx
    ext k
    have := cone_identity a v b x k
    rw [e1, e2] at this
    have h0 : o3 a v b * (x k - v k) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · linarith

/-- The cone lemma: if the angle at `v` between `a` and `b` is acute (and `a, v, b` are positively oriented), then
so is the angle at `v` between any two points `x, y ≠ v` of the cone spanned by `a - v` and `b - v`. -/
theorem cone_pos {a v b x y : ℝ²} (hO : 0 < o3 a v b) (hab : 0 < dt a v b) (ha : a ≠ v) (hb : b ≠ v)
    (hx : x ≠ v) (hy : y ≠ v) (hx1 : 0 ≤ o3 x v b) (hx2 : 0 ≤ o3 a v x) (hy1 : 0 ≤ o3 y v b)
    (hy2 : 0 ≤ o3 a v y) : 0 < dt x v y := by
  have hA := d2_pos ha
  have hB := d2_pos hb
  have sx := cone_coeff_pos hO hx hx1 hx2
  have sy := cone_coeff_pos hO hy hy1 hy2
  have hid := cone_dot_identity a v b x y
  set α := o3 x v b
  set β := o3 a v x
  set γ := o3 y v b
  set δ := o3 a v y
  set m := min (min (d2 a v) (dt a v b)) (d2 b v) with hm
  have hm0 : 0 < m := lt_min (lt_min hA hab) hB
  have hmA : m ≤ d2 a v := (min_le_left _ _).trans (min_le_left _ _)
  have hmD : m ≤ dt a v b := (min_le_left _ _).trans (min_le_right _ _)
  have hmB : m ≤ d2 b v := min_le_right _ _
  have p1 : α * γ * m ≤ α * γ * d2 a v := mul_le_mul_of_nonneg_left hmA (mul_nonneg hx1 hy1)
  have p2 : (α * δ + β * γ) * m ≤ (α * δ + β * γ) * dt a v b :=
    mul_le_mul_of_nonneg_left hmD (add_nonneg (mul_nonneg hx1 hy2) (mul_nonneg hx2 hy1))
  have p3 : β * δ * m ≤ β * δ * d2 b v := mul_le_mul_of_nonneg_left hmB (mul_nonneg hx2 hy2)
  have hprod : 0 < (α + β) * (γ + δ) * m := mul_pos (mul_pos sx sy) hm0
  have hsq : 0 < (o3 a v b) ^ 2 := by positivity
  have hpos : 0 < dt x v y * (o3 a v b) ^ 2 := by
    rw [hid]; nlinarith
  by_contra hc
  push_neg at hc
  have : dt x v y * (o3 a v b) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hsq.le
  linarith

theorem quad_identity (A B C D : ℝ²) :
    o3 B C D * dt D A B + o3 A C D * dt A B C + o3 A B D * dt B C D + o3 A B C * dt C D A = 0 := by
  unfold o3 dt; ring

/-- A convex quadrilateral `A B C D` (positively oriented) has no four acute angles. -/
theorem quad_not_all_acute {A B C D : ℝ²} (h1 : 0 < o3 A B C) (h2 : 0 < o3 A B D) (h3 : 0 < o3 A C D)
    (h4 : 0 < o3 B C D) (hA : 0 < dt D A B) (hB : 0 < dt A B C) (hC : 0 < dt B C D) (hD : 0 < dt C D A) :
    False := by
  have := quad_identity A B C D
  have := mul_pos h4 hA
  have := mul_pos h3 hB
  have := mul_pos h2 hC
  have := mul_pos h1 hD
  linarith

end E982C
end

section
/-
Erdős Problem #982, round 2: the finite check for a general number `n` of vertices, as a CNF over structured
atoms, with at most `K` distinct distances at every vertex.

Vertices are `Fin n`, in the cyclic order of the polygon. Atoms:
  `E P Q`  the vertex pairs `P` and `Q` (each stored as (min, max)) have equal length
  `L P Q`  the pair `P` is strictly shorter than the pair `Q`
  `A v`    the interior angle at `v` is acute
Clause families:
  `eqvCls`    equal length is transitive
  `ordCls`    strict order: irreflexive on equal lengths, total, transitive
  `classCls`  at most `K` distinct distances at each vertex (every `K + 1` other vertices contain an equidistant pair)
  `sideCls`   half-plane rule: if `z` is not farther from `u` than from `w`, every vertex strictly inside the boundary
              arc from `u` to `z` that avoids `w` is strictly nearer to `u` than to `w`
  `acuteCls`  the angle at `v` is acute if `|v-1, v+1| <= |v-1, v|` or `<= |v, v+1|`; no four angles are acute
`gen n K` is `genA n K` relabelled to `Nat` by an injective code `enc`.
-/




open Std.Sat Std.Tactic.BVDecide

namespace E982C

private inductive Atom (n : Nat) where
  | E : Fin n × Fin n → Fin n × Fin n → Atom n
  | L : Fin n × Fin n → Fin n × Fin n → Atom n
  | A : Fin n → Atom n
  deriving DecidableEq

section Code

variable {n : Nat}

private def code (P : Fin n × Fin n) : Nat := P.1.val * n + P.2.val

private def enc : Atom n → Nat
  | .E P Q => code P * (n * n) + code Q
  | .L P Q => n * n * (n * n) + (code P * (n * n) + code Q)
  | .A v => 2 * (n * n * (n * n)) + v.val

variable [NeZero n]

theorem n_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)

private def fm (k : Nat) : Fin n := ⟨k % n, Nat.mod_lt _ n_pos⟩

private def decP (k : Nat) : Fin n × Fin n := (fm (k / n), fm k)

private def dec (x : Nat) : Atom n :=
  if x < n * n * (n * n) then .E (decP (x / (n * n))) (decP (x % (n * n)))
  else if x < 2 * (n * n * (n * n)) then
    .L (decP ((x - n * n * (n * n)) / (n * n))) (decP ((x - n * n * (n * n)) % (n * n)))
  else .A (fm (x - 2 * (n * n * (n * n))))

end Code

/-! Index combinatorics on the `n`-cycle. -/

section Comb

variable {n : Nat}

/-- `(a, b, c)` is in strict cyclic (counterclockwise index) order. -/
private def cycB (a b c : Fin n) : Bool :=
  (decide (a.val < b.val) && decide (b.val < c.val)) || (decide (b.val < c.val) && decide (c.val < a.val)) ||
    (decide (c.val < a.val) && decide (a.val < b.val))

/-- `y` lies strictly inside the boundary arc from `u` to `z` that avoids `w`. -/
private def btwB (u y z w : Fin n) : Bool := (cycB u y z && cycB u z w) || (cycB w z y && cycB w y u)

private def cp (u w : Fin n) : Fin n × Fin n := if u < w then (u, w) else (w, u)

/-- the equality atom of two pairs, in a canonical order -/
private def Eq' (P Q : Fin n × Fin n) : Atom n := if code P < code Q then .E P Q else .E Q P

private def pairsOf {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairsOf xs

private def subsets {α : Type} : Nat → List α → List (List α)
  | 0, _ => [[]]
  | _ + 1, [] => []
  | k + 1, x :: xs => (subsets k xs).map (x :: ·) ++ subsets (k + 1) xs

private def vs (n : Nat) : List (Fin n) := List.finRange n
private def prs (n : Nat) : List (Fin n × Fin n) := pairsOf (vs n)
private def others (v : Fin n) : List (Fin n) := (vs n).filter (· != v)

end Comb

/-! Clause families. -/

section Clauses

variable (n : Nat)

private def eqvCls : List (CNF.Clause (Atom n)) :=
  (prs n).flatMap fun P => (prs n).flatMap fun Q => (prs n).flatMap fun R =>
    if P != Q && Q != R && P != R then [[(Eq' P Q, false), (Eq' Q R, false), (Eq' P R, true)]] else []

private def ordCls : List (CNF.Clause (Atom n)) :=
  ((prs n).flatMap fun P => (prs n).flatMap fun Q =>
    if P != Q then [[(Eq' P Q, false), (.L P Q, false)], [(Eq' P Q, true), (.L P Q, true), (.L Q P, true)]]
    else []) ++
  ((prs n).flatMap fun P => (prs n).flatMap fun Q => (prs n).flatMap fun R =>
    if P != Q && Q != R && P != R then [[(.L P Q, false), (.L Q R, false), (.L P R, true)]] else [])

private def classCls (K : Nat) : List (CNF.Clause (Atom n)) :=
  (vs n).flatMap fun v => (subsets (K + 1) (others v)).map fun S =>
    (pairsOf S).map fun (a, b) => (Eq' (cp v a) (cp v b), true)

private def sideCls : List (CNF.Clause (Atom n)) :=
  (vs n).flatMap fun u => (vs n).flatMap fun w => (vs n).flatMap fun z => (vs n).flatMap fun y =>
    if btwB u y z w then [[(.L (cp z w) (cp z u), true), (.L (cp y u) (cp y w), true)]] else []

variable [NeZero n]

private def nx (v : Fin n) : Fin n := fm (v.val + 1)
private def pv (v : Fin n) : Fin n := fm (v.val + n - 1)

private def acuteCls : List (CNF.Clause (Atom n)) :=
  ((vs n).flatMap fun v =>
    [cp (pv n v) v, cp v (nx n v)].flatMap fun s =>
      [[(Eq' (cp (pv n v) (nx n v)) s, false), (.A v, true)], [(.L (cp (pv n v) (nx n v)) s, false), (.A v, true)]]) ++
  ((subsets 4 (vs n)).map fun S => S.map fun v => (.A v, false))

private def genA (K : Nat) : CNF (Atom n) :=
  ⟨(eqvCls n ++ ordCls n ++ classCls n K ++ sideCls n ++ acuteCls n).toArray⟩

private def gen (K : Nat) : CNF Nat := (genA n K).relabel enc

end Clauses

end E982C
end

section
/-
Erdős #982, round 2: the code `enc` of the atoms is injective (`dec_enc`).
-/



namespace E982C

variable {n : Nat} [NeZero n]

theorem fm_val (a : Fin n) : fm (n := n) a.val = a := by
  apply Fin.ext; simp [fm, Nat.mod_eq_of_lt a.isLt]

theorem code_lt (P : Fin n × Fin n) : code P < n * n := by
  unfold code
  have h1 := P.1.isLt
  have h2 := P.2.isLt
  calc P.1.val * n + P.2.val < P.1.val * n + n := by omega
    _ = (P.1.val + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right _ h1

theorem decP_code (P : Fin n × Fin n) : decP (code P) = P := by
  have hn := n_pos (n := n)
  have h2 := P.2.isLt
  have hd : (P.1.val * n + P.2.val) / n = P.1.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt h2, Nat.zero_add]
  have hm : (P.1.val * n + P.2.val) % n = P.2.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  unfold decP code
  rw [hd]
  ext
  · simp [fm, Nat.mod_eq_of_lt P.1.isLt]
  · simp [fm, hm]

theorem div_nn (P Q : Fin n × Fin n) : (code P * (n * n) + code Q) / (n * n) = code P := by
  have hq := code_lt Q
  have hnn : 0 < n * n := Nat.mul_pos n_pos n_pos
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hnn, Nat.div_eq_of_lt hq, Nat.zero_add]

theorem mod_nn (P Q : Fin n × Fin n) : (code P * (n * n) + code Q) % (n * n) = code Q := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (code_lt Q)]

theorem pq_lt (P Q : Fin n × Fin n) : code P * (n * n) + code Q < n * n * (n * n) := by
  have hp := code_lt P
  have hq := code_lt Q
  calc code P * (n * n) + code Q < code P * (n * n) + n * n := by omega
    _ = (code P + 1) * (n * n) := by ring
    _ ≤ n * n * (n * n) := Nat.mul_le_mul_right _ hp

theorem dec_enc (x : Atom n) : dec (enc x) = x := by
  rcases x with ⟨P, Q⟩ | ⟨P, Q⟩ | v
  · have h := pq_lt P Q
    simp only [enc, dec, if_pos h, div_nn, mod_nn, decP_code]
  · have h := pq_lt P Q
    have h1 : ¬ (n * n * (n * n) + (code P * (n * n) + code Q) < n * n * (n * n)) := by omega
    have h2 : n * n * (n * n) + (code P * (n * n) + code Q) < 2 * (n * n * (n * n)) := by omega
    have h3 : n * n * (n * n) + (code P * (n * n) + code Q) - n * n * (n * n) = code P * (n * n) + code Q := by
      omega
    simp only [enc, dec, if_neg h1, if_pos h2, h3, div_nn, mod_nn, decP_code]
  · have h1 : ¬ (2 * (n * n * (n * n)) + v.val < n * n * (n * n)) := by omega
    have h2 : ¬ (2 * (n * n * (n * n)) + v.val < 2 * (n * n * (n * n))) := by omega
    have h3 : 2 * (n * n * (n * n)) + v.val - 2 * (n * n * (n * n)) = v.val := by omega
    simp only [enc, dec, if_neg h1, if_neg h2, h3, fm_val]

end E982C
end

section
/-
Erdős #982, round 2: index combinatorics on the `n`-cycle (all by `omega`) and the orientation of polygon triples
from formal-conjectures' `IsCcwConvexPolygon`.
-/



open EuclideanGeometry

namespace E982C

variable {n : Nat}

/-- strict cyclic order of three indices, as a proposition -/
private def cycP (a b c : Fin n) : Prop :=
  (a.val < b.val ∧ b.val < c.val) ∨ (b.val < c.val ∧ c.val < a.val) ∨ (c.val < a.val ∧ a.val < b.val)

private instance (a b c : Fin n) : Decidable (cycP a b c) := by unfold cycP; infer_instance

theorem cycB_eq (a b c : Fin n) : cycB a b c = decide (cycP a b c) := by
  unfold cycB cycP
  by_cases h1 : a.val < b.val <;> by_cases h2 : b.val < c.val <;> by_cases h3 : c.val < a.val <;> simp [h1, h2, h3]

theorem cyc_true {a b c : Fin n} : cycB a b c = true ↔ cycP a b c := by
  rw [cycB_eq]; exact decide_eq_true_iff

theorem btw_true {u y z w : Fin n} :
    btwB u y z w = true ↔ (cycP u y z ∧ cycP u z w) ∨ (cycP w z y ∧ cycP w y u) := by
  unfold btwB
  simp only [Bool.or_eq_true, Bool.and_eq_true, cyc_true]

/-- Four vertices `u, y, z, w` with `y` strictly inside the arc from `u` to `z` that avoids `w`: they are distinct and
in cyclic order, counterclockwise or clockwise. -/
theorem btw_cases {u y z w : Fin n} (h : btwB u y z w = true) :
    u ≠ y ∧ u ≠ z ∧ u ≠ w ∧ y ≠ z ∧ y ≠ w ∧ z ≠ w ∧
    ((cycP u y z ∧ cycP u y w ∧ cycP u z w ∧ cycP y z w) ∨
     (¬ cycP u y z ∧ ¬ cycP u y w ∧ ¬ cycP u z w ∧ ¬ cycP y z w)) := by
  rw [btw_true] at h
  simp only [ne_eq, Fin.ext_iff]
  unfold cycP at *
  omega

theorem o3_of_ccw {p : Fin n → ℝ²} (hp : IsCcwConvexPolygon p) {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    0 < o3 (p i) (p j) (p k) := by
  have h := hp hij hjk
  rw [sign_oangle_eq] at h
  exact sign_eq_one_iff.mp h

theorem orient {p : Fin n → ℝ²} (hp : IsCcwConvexPolygon p) {i j k : Fin n}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (cycP i j k → 0 < o3 (p i) (p j) (p k)) ∧ (¬ cycP i j k → o3 (p i) (p j) (p k) < 0) := by
  have r1 := o3_rotate (p i) (p j) (p k)
  have r2 := o3_rotate (p j) (p k) (p i)
  have s1 := o3_swap (p i) (p j) (p k)
  have s2 := o3_swap (p j) (p k) (p i)
  have s3 := o3_swap (p k) (p i) (p j)
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hjk' : j.val ≠ k.val := fun h => hjk (Fin.ext h)
  have hik' : i.val ≠ k.val := fun h => hik (Fin.ext h)
  unfold cycP
  rcases Nat.lt_or_gt_of_ne hij' with h1 | h1 <;> rcases Nat.lt_or_gt_of_ne hjk' with h2 | h2 <;>
    rcases Nat.lt_or_gt_of_ne hik' with h3 | h3
  · exact ⟨fun _ => o3_of_ccw hp h1 h2, fun hc => absurd (Or.inl ⟨h1, h2⟩) hc⟩
  · omega
  · have := o3_of_ccw hp (i := i) (j := k) (k := j) h3 h2
    exact ⟨fun hc => by omega, fun _ => by linarith⟩
  · have := o3_of_ccw hp (i := k) (j := i) (k := j) h3 h1
    exact ⟨fun _ => by linarith, fun hc => absurd (Or.inr (Or.inr ⟨h3, h1⟩)) hc⟩
  · have := o3_of_ccw hp (i := j) (j := i) (k := k) h1 h3
    exact ⟨fun hc => by omega, fun _ => by linarith⟩
  · have := o3_of_ccw hp (i := j) (j := k) (k := i) h2 h3
    exact ⟨fun _ => by linarith, fun hc => absurd (Or.inr (Or.inl ⟨h2, h3⟩)) hc⟩
  · omega
  · have := o3_of_ccw hp (i := k) (j := j) (k := i) h2 h1
    exact ⟨fun hc => by omega, fun _ => by linarith⟩

/-! Neighbours of a vertex. -/

variable [NeZero n]

theorem nx_val (v : Fin n) : (nx n v).val = if v.val + 1 < n then v.val + 1 else 0 := by
  unfold nx fm
  simp only
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : v.val + 1 = n := by have := v.isLt; omega
    rw [this, Nat.mod_self]

theorem pv_val (v : Fin n) : (pv n v).val = if 0 < v.val then v.val - 1 else n - 1 := by
  unfold pv fm
  simp only
  split_ifs with h
  · have e : v.val + n - 1 = (v.val - 1) + n := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := v.isLt; omega)]
  · have e : v.val = 0 := by omega
    have := n_pos (n := n)
    rw [e, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]

theorem nb_facts (hn : 3 ≤ n) (v : Fin n) :
    pv n v ≠ v ∧ nx n v ≠ v ∧ pv n v ≠ nx n v ∧ cycP (pv n v) v (nx n v) := by
  have h1 := nx_val v
  have h2 := pv_val v
  have := v.isLt
  simp only [ne_eq, Fin.ext_iff]
  unfold cycP
  split_ifs at h1 h2 <;> omega

theorem nb_x (v x : Fin n) (hx : x ≠ v) :
    (x = nx n v ∨ cycP x v (nx n v)) ∧ (x = pv n v ∨ cycP (pv n v) v x) := by
  have h1 := nx_val v
  have h2 := pv_val v
  have := v.isLt
  have := x.isLt
  have hx' : x.val ≠ v.val := fun h => hx (Fin.ext h)
  simp only [Fin.ext_iff]
  unfold cycP
  split_ifs at h1 h2 <;> omega

end E982C
end

section
/-
Erdős #982, round 2: the bridge. A strictly convex `n`-gon (formal-conjectures' `IsCcwConvexPolygon`, `n ≥ 3`) with at
most `K` distinct distances at every vertex gives an assignment of the atoms satisfying every clause of `genA n K`.
-/


open EuclideanGeometry Std.Sat

namespace E982C

/-! List facts. -/

theorem mem_pairsOf {α : Type} {L : List α} {x y : α} (h : (x, y) ∈ pairsOf L) :
    x ∈ L ∧ y ∈ L ∧ (L.Nodup → x ≠ y) := by
  induction L with
  | nil => simp [pairsOf] at h
  | cons z zs ih =>
    simp only [pairsOf, List.mem_append, List.mem_map, Prod.mk.injEq] at h
    rcases h with ⟨t, ht, rfl, rfl⟩ | h
    · refine ⟨List.mem_cons_self, List.mem_cons_of_mem _ ht, fun hn => ?_⟩
      rintro rfl
      exact (List.nodup_cons.mp hn).1 ht
    · obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, fun hn => h3 (List.nodup_cons.mp hn).2⟩

theorem pairsOf_of_mem {α : Type} {L : List α} {x y : α} (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y) :
    (x, y) ∈ pairsOf L ∨ (y, x) ∈ pairsOf L := by
  induction L with
  | nil => simp at hx
  | cons z zs ih =>
    simp only [pairsOf, List.mem_append, List.mem_map, Prod.mk.injEq]
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · exact absurd rfl hxy
    · exact Or.inl (Or.inl ⟨y, hy', rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨x, hx', rfl, rfl⟩)
    · rcases ih hx' hy' with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inr h)

theorem mem_subsets {α : Type} : ∀ {k : Nat} {L S : List α}, S ∈ subsets k L → S.Sublist L ∧ S.length = k
  | 0, L, S, h => by simp [subsets] at h; subst h; exact ⟨List.nil_sublist _, rfl⟩
  | _ + 1, [], S, h => by simp [subsets] at h
  | k + 1, x :: xs, S, h => by
    simp only [subsets, List.mem_append, List.mem_map] at h
    rcases h with ⟨T, hT, rfl⟩ | h
    · obtain ⟨h1, h2⟩ := mem_subsets hT
      exact ⟨h1.cons_cons x, by simp [h2]⟩
    · obtain ⟨h1, h2⟩ := mem_subsets h
      exact ⟨h1.cons x, h2⟩

variable {n : Nat}

theorem vs_nodup : (vs n).Nodup := List.nodup_finRange n

theorem cycP_ne {a b c : Fin n} (h : cycP a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  unfold cycP at h
  simp only [ne_eq, Fin.ext_iff]
  omega

/-! The assignment given by a polygon. -/

variable (p : Fin n → ℝ²)

private noncomputable def len (P : Fin n × Fin n) : ℝ := dist (p P.1) (p P.2)

variable [NeZero n]

/-- the interior angle at `v` is acute -/
private def acute (v : Fin n) : Prop := 0 < dt (p (pv n v)) (p v) (p (nx n v))

private noncomputable instance (v : Fin n) : Decidable (acute p v) := by unfold acute; infer_instance

private noncomputable def asg : Atom n → Bool
  | .E P Q => decide (len p P = len p Q)
  | .L P Q => decide (len p P < len p Q)
  | .A v => decide (acute p v)

theorem len_cp (u w : Fin n) : len p (cp u w) = dist (p u) (p w) := by
  unfold cp len; split <;> simp [dist_comm]

theorem asg_Eq' (P Q : Fin n × Fin n) : asg p (Eq' P Q) = decide (len p P = len p Q) := by
  unfold Eq'; split
  · rfl
  · simp only [asg, eq_comm]

theorem asg_L (P Q : Fin n × Fin n) : asg p (.L P Q) = decide (len p P < len p Q) := rfl

theorem asg_A (v : Fin n) : asg p (.A v) = decide (acute p v) := rfl

variable {p}

theorem d2_le_of_dist_le {a b c d : ℝ²} (h : dist a b ≤ dist c d) : d2 a b ≤ d2 c d := by
  rcases h.lt_or_eq with h | h
  · exact ((dist_lt_iff_d2 _ _ _ _).mp h).le
  · exact ((dist_eq_iff_d2 _ _ _ _).mp h).le

/-! Each clause family is satisfied. -/

theorem eqv_ok : ∀ c ∈ eqvCls n, c.eval (asg p) = true := by
  intro c hc
  simp only [eqvCls, List.mem_flatMap] at hc
  obtain ⟨P, -, Q, -, R, -, hc⟩ := hc
  split_ifs at hc with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, asg_Eq', Bool.or_false]
    by_cases h1 : len p P = len p Q <;> by_cases h2 : len p Q = len p R <;> simp [h1, h2] <;> linarith
  · simp at hc

theorem ord_ok : ∀ c ∈ ordCls n, c.eval (asg p) = true := by
  intro c hc
  simp only [ordCls, List.mem_append, List.mem_flatMap] at hc
  rcases hc with ⟨P, -, Q, -, hc⟩ | ⟨P, -, Q, -, R, -, hc⟩
  · split_ifs at hc with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        simp only [CNF.Clause.eval, List.any_cons, List.any_nil, asg_Eq', asg_L, Bool.or_false]
      · by_cases h1 : len p P = len p Q <;> simp [h1]
      · rcases lt_trichotomy (len p P) (len p Q) with h1 | h1 | h1 <;> simp [h1]
    · simp at hc
  · split_ifs at hc with h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp only [CNF.Clause.eval, List.any_cons, List.any_nil, asg_L, Bool.or_false]
      by_cases h1 : len p P < len p Q <;> by_cases h2 : len p Q < len p R <;> simp [h1, h2] <;> linarith
    · simp at hc

theorem class_ok {K : Nat}
    (hK : ∀ v : Fin n, {d : ℝ | ∃ j : Fin n, j ≠ v ∧ d = dist (p v) (p j)}.ncard < K + 1) :
    ∀ c ∈ classCls n K, c.eval (asg p) = true := by
  intro c hc
  simp only [classCls, List.mem_flatMap, List.mem_map] at hc
  obtain ⟨v, -, S, hS, rfl⟩ := hc
  obtain ⟨hsub, hlen⟩ := mem_subsets hS
  have hnd : S.Nodup := (vs_nodup.filter _).sublist hsub
  have hne : ∀ j ∈ S, j ≠ v := fun j hj => by
    have := hsub.subset hj
    simp only [others, List.mem_filter, bne_iff_ne] at this
    exact this.2
  set D := {d : ℝ | ∃ j : Fin n, j ≠ v ∧ d = dist (p v) (p j)} with hDdef
  have hDfin : D.Finite := by
    have : D ⊆ Set.range (fun j : Fin n => dist (p v) (p j)) := by
      rintro d ⟨j, -, rfl⟩; exact ⟨j, rfl⟩
    exact (Set.finite_range _).subset this
  obtain ⟨x, hx, y, hy, hxy, heq⟩ : ∃ x ∈ S.toFinset, ∃ y ∈ S.toFinset, x ≠ y ∧
      dist (p v) (p x) = dist (p v) (p y) := by
    apply Finset.exists_ne_map_eq_of_card_lt_of_maps_to (t := hDfin.toFinset)
    · rw [List.toFinset_card_of_nodup hnd, hlen, ← Set.ncard_eq_toFinset_card D hDfin]
      exact hK v
    · intro j hj
      simp only [Finset.mem_coe, List.mem_toFinset] at hj
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, hDdef, Set.mem_setOf_eq]
      exact ⟨j, hne j hj, rfl⟩
  simp only [CNF.Clause.eval, List.any_map, List.any_eq_true]
  rcases pairsOf_of_mem (List.mem_toFinset.mp hx) (List.mem_toFinset.mp hy) hxy with h | h
  · exact ⟨(x, y), h, by simp [asg_Eq', len_cp, heq]⟩
  · exact ⟨(y, x), h, by simp [asg_Eq', len_cp, heq]⟩

theorem side_ok (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∀ c ∈ sideCls n, c.eval (asg p) = true := by
  intro c hc
  simp only [sideCls, List.mem_flatMap] at hc
  obtain ⟨u, -, w, -, z, -, y, -, hc⟩ := hc
  split_ifs at hc with hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    obtain ⟨huy, huz, huw, hyz, hyw, hzw, hcyc⟩ := btw_cases hb
    simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, asg_L, len_cp]
    by_cases h1 : dist (p z) (p w) < dist (p z) (p u)
    · simp [h1]
    · have hz : d2 (p z) (p u) ≤ d2 (p z) (p w) := d2_le_of_dist_le (not_lt.mp h1)
      have hpuw : p u ≠ p w := fun h => huw (hinj h)
      have o1 := orient hp huy hyz huz
      have o2 := orient hp huy hyw huw
      have o3' := orient hp huz hzw huw
      have o4 := orient hp hyz hzw hyw
      have key : d2 (p y) (p u) < d2 (p y) (p w) := by
        rcases hcyc with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩
        · refine side_core hpuw 1 ?_ ?_ ?_ ?_ hz
          · rw [one_mul]; exact o1.1 c1
          · rw [one_mul]; exact o2.1 c2
          · rw [one_mul]; exact o3'.1 c3
          · rw [one_mul]; exact o4.1 c4
        · refine side_core hpuw (-1) ?_ ?_ ?_ ?_ hz
          · have := o1.2 c1; linarith
          · have := o2.2 c2; linarith
          · have := o3'.2 c3; linarith
          · have := o4.2 c4; linarith
      have : dist (p y) (p u) < dist (p y) (p w) := (dist_lt_iff_d2 _ _ _ _).mpr key
      simp [this]
  · simp at hc

/-- The cone lemma at a vertex of the polygon. -/
theorem cone_at (hn : 3 ≤ n) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) {v x y : Fin n}
    (hx : x ≠ v) (hy : y ≠ v) (hv : acute p v) : 0 < dt (p x) (p v) (p y) := by
  obtain ⟨hpv, hnx, hpn, hcyc⟩ := nb_facts hn v
  have hO := (orient hp hpv hnx.symm hpn).1 hcyc
  have coeff : ∀ z : Fin n, z ≠ v → 0 ≤ o3 (p z) (p v) (p (nx n v)) ∧ 0 ≤ o3 (p (pv n v)) (p v) (p z) := by
    intro z hz
    obtain ⟨h1, h2⟩ := nb_x v z hz
    constructor
    · rcases h1 with h1 | h1
      · rw [h1]; exact le_of_eq (by unfold o3; ring)
      · exact ((orient hp hz hnx.symm (cycP_ne h1).2.2).1 h1).le
    · rcases h2 with h2 | h2
      · rw [h2]; exact le_of_eq (by unfold o3; ring)
      · exact ((orient hp hpv (Ne.symm hz) (cycP_ne h2).2.2).1 h2).le
  exact cone_pos hO hv (fun h => hpv (hinj h)) (fun h => hnx (hinj h)) (fun h => hx (hinj h))
    (fun h => hy (hinj h)) (coeff x hx).1 (coeff x hx).2 (coeff y hy).1 (coeff y hy).2

theorem no_four_acute (hn : 3 ≤ n) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) {a b c d : Fin n}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (ha : acute p a) (hb : acute p b) (hc : acute p c)
    (hd : acute p d) : False := by
  have hac : a < c := lt_trans hab hbc
  have hbd : b < d := lt_trans hbc hcd
  have had : a < d := lt_trans hac hcd
  exact quad_not_all_acute (o3_of_ccw hp hab hbc) (o3_of_ccw hp hab hbd) (o3_of_ccw hp hac hcd)
    (o3_of_ccw hp hbc hcd)
    (cone_at hn hinj hp (ne_of_gt had) (ne_of_gt hab) ha)
    (cone_at hn hinj hp (ne_of_lt hab) (ne_of_gt hbc) hb)
    (cone_at hn hinj hp (ne_of_lt hbc) (ne_of_gt hcd) hc)
    (cone_at hn hinj hp (ne_of_lt hcd) (ne_of_lt had) hd)

theorem acute_ok (hn : 3 ≤ n) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∀ c ∈ acuteCls n, c.eval (asg p) = true := by
  intro c hc
  simp only [acuteCls, List.mem_append, List.mem_flatMap, List.mem_map] at hc
  rcases hc with ⟨v, -, s, hs, hc⟩ | ⟨S, hS, rfl⟩
  · obtain ⟨hpv, hnx, -, -⟩ := nb_facts hn v
    have hA : len p (cp (pv n v) (nx n v)) ≤ len p s → asg p (.A v) = true := by
      intro hle
      rw [asg_A, decide_eq_true_eq]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rw [len_cp] at hle
      rcases hs with rfl | rfl <;> rw [len_cp] at hle
      · exact acute_of_le_left (fun h => hnx (hinj h).symm) (d2_le_of_dist_le hle)
      · exact acute_of_le_right (fun h => hpv (hinj h)) (d2_le_of_dist_le hle)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, asg_Eq']
      by_cases h : len p (cp (pv n v) (nx n v)) = len p s
      · simp [hA h.le]
      · simp [h]
    · simp only [CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false, asg_L]
      by_cases h : len p (cp (pv n v) (nx n v)) < len p s
      · simp [hA h.le]
      · simp [h]
  · obtain ⟨hsub, hlen⟩ := mem_subsets hS
    have hpw : S.Pairwise (· < ·) := (List.pairwise_lt_finRange n).sublist hsub
    match S, hlen, hpw with
    | [a, b, c, d], _, hpw =>
      have hab : a < b := List.rel_of_pairwise_cons hpw (by simp)
      have hbc : b < c := List.rel_of_pairwise_cons hpw.of_cons (by simp)
      have hcd : c < d := List.rel_of_pairwise_cons hpw.of_cons.of_cons (by simp)
      simp only [List.map_cons, List.map_nil, CNF.Clause.eval, List.any_cons, List.any_nil, Bool.or_false,
        asg_A]
      by_cases ha : acute p a
      · by_cases hb : acute p b
        · by_cases hc : acute p c
          · by_cases hd : acute p d
            · exact (no_four_acute hn hinj hp hab hbc hcd ha hb hc hd).elim
            · simp [hd]
          · simp [hc]
        · simp [hb]
      · simp [ha]

theorem genA_eval {K : Nat} (hn : 3 ≤ n) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p)
    (hK : ∀ v : Fin n, {d : ℝ | ∃ j : Fin n, j ≠ v ∧ d = dist (p v) (p j)}.ncard < K + 1) :
    (genA n K).eval (asg p) = true := by
  simp only [genA, CNF.eval, List.all_toArray, List.all_append, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨eqv_ok, ord_ok⟩, class_ok hK⟩, side_ok hinj hp⟩, acute_ok hn hinj hp⟩

end E982C
end
namespace E982C
open Std.Sat Std.Tactic.BVDecide
private inductive Shape (n : ℕ) where
  | eqv (p q r : Fin n × Fin n)
  | ord (p q : Fin n × Fin n)
  | trans (p q r : Fin n × Fin n)
  | classes (v : Fin n) (s : List (Fin n))
  | side (u w z y : Fin n)
  | acute (v : Fin n) (s : Fin n × Fin n)
  | four (s : List (Fin n))

private def block {n : ℕ} [NeZero n] (K : ℕ) : Shape n → List (CNF.Clause (Atom n))
  | .eqv P Q R => if P ∈ prs n ∧ Q ∈ prs n ∧ R ∈ prs n then
      if P != Q && Q != R && P != R then [[(Eq' P Q, false), (Eq' Q R, false), (Eq' P R, true)]] else []
    else []
  | .ord P Q => if P ∈ prs n ∧ Q ∈ prs n then
      if P != Q then [[(Eq' P Q, false), (.L P Q, false)], [(Eq' P Q, true), (.L P Q, true), (.L Q P, true)]] else []
    else []
  | .trans P Q R => if P ∈ prs n ∧ Q ∈ prs n ∧ R ∈ prs n then
      if P != Q && Q != R && P != R then [[(.L P Q, false), (.L Q R, false), (.L P R, true)]] else []
    else []
  | .classes v S => if v ∈ vs n ∧ S ∈ subsets (K+1) (others v) then
      [(pairsOf S).map fun (a,b) => (Eq' (cp v a) (cp v b),true)] else []
  | .side u w z y => if u ∈ vs n ∧ w ∈ vs n ∧ z ∈ vs n ∧ y ∈ vs n then
      if btwB u y z w then [[(.L (cp z w) (cp z u),true),(.L (cp y u) (cp y w),true)]] else []
    else []
  | .acute v s => if v ∈ vs n ∧ s ∈ [cp (pv n v) v,cp v (nx n v)] then
      [[(Eq' (cp (pv n v) (nx n v)) s,false),(.A v,true)],[(.L (cp (pv n v) (nx n v)) s,false),(.A v,true)]] else []
  | .four S => if S ∈ subsets 4 (vs n) then [S.map fun v => (.A v,false)] else []

private lemma block_sound {n : ℕ} [NeZero n] (K : ℕ) (w : Shape n) {c : CNF.Clause (Atom n)}
    (h : c ∈ block K w) : c ∈ (genA n K).clauses := by
  change c ∈ (eqvCls n ++ ordCls n ++ classCls n K ++ sideCls n ++ acuteCls n).toArray
  simp only [List.mem_toArray,List.mem_append]
  cases w with
  | eqv p q r =>
    simp only [block] at h
    split at h <;> rename_i a
    · left; left; left; left
      simp only [eqvCls,List.mem_flatMap]
      exact ⟨p,a.1,q,a.2.1,r,a.2.2,h⟩
    · contradiction
  | ord p q =>
    simp only [block] at h
    split at h <;> rename_i a
    · left; left; left; right
      simp only [ordCls,List.mem_append,List.mem_flatMap]
      exact Or.inl ⟨p,a.1,q,a.2,h⟩
    · contradiction
  | trans p q r =>
    simp only [block] at h
    split at h <;> rename_i a
    · left; left; left; right
      simp only [ordCls,List.mem_append,List.mem_flatMap]
      exact Or.inr ⟨p,a.1,q,a.2.1,r,a.2.2,h⟩
    · contradiction
  | classes v s =>
    simp only [block] at h
    split at h <;> rename_i a
    · left; left; right
      simp only [List.mem_singleton] at h
      simp only [classCls,List.mem_flatMap,List.mem_map]
      exact ⟨v,a.1,s,a.2,h.symm⟩
    · contradiction
  | side u w z y =>
    simp only [block] at h
    split at h <;> rename_i a
    · left; right
      simp only [sideCls,List.mem_flatMap]
      exact ⟨u,a.1,w,a.2.1,z,a.2.2.1,y,a.2.2.2,h⟩
    · contradiction
  | acute v s =>
    simp only [block] at h
    split at h <;> rename_i a
    · right
      simp only [acuteCls,List.mem_append,List.mem_flatMap]
      exact Or.inl ⟨v,a.1,s,a.2,h⟩
    · contradiction
  | four s =>
    simp only [block] at h
    split at h <;> rename_i a
    · right
      simp only [List.mem_singleton] at h
      simp only [acuteCls,List.mem_append,List.mem_map]
      exact Or.inr ⟨s,a,h.symm⟩
    · contradiction

private def core {n : ℕ} [NeZero n] (K : ℕ) (ws : List (Shape n × ℕ)) : CNF Nat :=
  (⟨(ws.filterMap fun (w,j) => (block K w)[j]?).toArray⟩ : CNF (Atom n)).relabel enc

private lemma unsat_of_core {n : ℕ} [NeZero n] (K : ℕ) (ws : List (Shape n × ℕ))
    (hc : (core K ws).Unsat) : (gen n K).Unsat := by
  intro a
  have h := hc a
  by_contra! hn
  have hg : (gen n K).eval a = true := by cases he : (gen n K).eval a <;> simp_all
  rw [gen,CNF.eval_relabel] at hg
  rw [core,CNF.eval_relabel] at h
  have ht : (⟨(ws.filterMap fun (w,j) => (block K w)[j]?).toArray⟩ : CNF (Atom n)).eval (a ∘ enc) = true := by
    simp only [CNF.eval,List.all_toArray,List.all_eq_true,List.mem_filterMap]
    intro c ⟨⟨w,j⟩,_,hj⟩
    have hm := block_sound K w (List.mem_of_getElem? hj)
    exact (Array.all_eq_true_iff_forall_mem.mp hg) c hm
  exact Bool.noConfusion (ht.symm.trans h)
end E982C

namespace E982C
open Std.Sat

private abbrev Lit := Nat × Bool
private def flipLit (u : Lit) : Lit := (u.1,!u.2)

private def propagate (trues : List Lit) : List (List Lit) → Bool
  | [] => false
  | c::cs =>
    match c.filter (fun u => !(trues.contains (flipLit u))) with
    | [] => true
    | [u] => propagate (u::trues) cs
    | _ => false

private lemma propagate_sound (a : Nat → Bool) (cs : List (List Lit)) (trues : List Lit)
    (ha : ∀ l ∈ trues, a l.1 = l.2) (hs : ∀ c ∈ cs, ∃ l ∈ c, a l.1 = l.2) :
    propagate trues cs = false := by
  induction cs generalizing trues with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨u,hu,he⟩ := hs c (.head _)
    have hnot : flipLit u ∉ trues := by
      intro h
      have h' := ha _ h
      simp [flipLit,he] at h'
    have H : u ∈ c.filter (fun l => !(trues.contains (flipLit l))) := by simpa using And.intro hu hnot
    unfold propagate
    split <;> rename_i hf
    · rw [hf] at H
      cases H
    · rw [hf,List.mem_singleton] at H
      subst u
      apply ih
      · intro l hl
        rcases List.mem_cons.mp hl with rfl | h
        · exact he
        · exact ha _ h
      · exact fun x hx => hs x (.tail _ hx)
    · rfl

private def refute (db : List (List Lit)) : List (List Lit × List Nat) → Bool
  | [] => false
  | (c,hs)::tail =>
    propagate (c.map flipLit) (hs.filterMap (fun i => db[i]?)) &&
      (c.isEmpty || refute (c::db) tail)

private lemma refute_sound (a : Nat → Bool) (trace : List (List Lit × List Nat))
    (db : List (List Lit)) (hdb : ∀ c ∈ db, ∃ l ∈ c, a l.1 = l.2) : refute db trace = false := by
  induction trace generalizing db with
  | nil => rfl
  | cons step steps ih =>
    obtain ⟨c,hs⟩ := step
    by_cases hc : ∃ l ∈ c, a l.1 = l.2
    · have ht := ih (c::db) (fun x h => by
        rcases List.mem_cons.mp h with rfl | h
        · exact hc
        · exact hdb _ h)
      obtain ⟨l,hl,_⟩ := hc
      have hn : c ≠ [] := by rintro rfl; simp at hl
      simp [refute,ht,hn]
    · have hA : ∀ l ∈ c.map flipLit, a l.1 = l.2 := by
        intro l hl
        obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hl
        have H : a u.1 ≠ u.2 := fun h => hc ⟨u,hu,h⟩
        change a u.1 = !u.2
        cases e : a u.1 <;> cases f : u.2 <;> simp_all
      have hB : ∀ cl ∈ hs.filterMap (fun i => db[i]?), ∃ l ∈ cl, a l.1 = l.2 := by
        intro cl h
        obtain ⟨i,hi,he⟩ := List.mem_filterMap.mp h
        exact hdb _ (List.mem_of_getElem? he)
      simp only [refute,propagate_sound a _ _ hA hB,Bool.false_and]

private lemma refuted_unsat (f : CNF Nat) (t : List (List Lit × List Nat))
    (hf : refute f.clauses.toList t = true) : f.Unsat := by
  intro a
  cases h : f.eval a with
  | false => rfl
  | true =>
    exfalso
    have hw := refute_sound a t f.clauses.toList (fun c hc => by
      have he := Array.all_eq_true_iff_forall_mem.mp h c (by simpa using hc)
      simpa [CNF.Clause.eval,List.any_eq_true] using he)
    simp [hw] at hf

end E982C

namespace E982C
open Std.Sat Std.Tactic.BVDecide
private def supports4 : List (Shape 4 × ℕ) := [(.eqv (0,1) (0,2) (2,3),0),
(.eqv (0,2) (0,1) (0,3),0),
(.eqv (0,2) (0,1) (1,2),0),
(.eqv (0,2) (0,1) (1,3),0),
(.eqv (0,3) (0,1) (1,2),0),
(.eqv (0,3) (0,1) (1,3),0),
(.eqv (0,3) (0,2) (2,3),0),
(.eqv (1,2) (0,1) (1,3),0),
(.eqv (1,2) (0,2) (2,3),0),
(.eqv (1,3) (0,2) (2,3),0),
(.ord (0,1) (0,2),0),
(.ord (0,1) (0,3),0),
(.ord (0,1) (1,2),0),
(.ord (0,1) (1,3),0),
(.ord (0,1) (2,3),0),
(.ord (0,2) (0,1),0),
(.ord (0,2) (0,3),0),
(.ord (0,2) (1,2),0),
(.ord (0,2) (1,3),0),
(.ord (0,2) (2,3),0),
(.ord (0,3) (0,1),0),
(.ord (0,3) (0,2),0),
(.ord (0,3) (1,2),0),
(.ord (0,3) (1,3),0),
(.ord (0,3) (2,3),0),
(.ord (1,2) (0,1),0),
(.ord (1,2) (0,2),0),
(.ord (1,2) (0,3),0),
(.ord (1,2) (1,3),0),
(.ord (1,2) (2,3),0),
(.ord (1,3) (0,1),0),
(.ord (1,3) (0,2),0),
(.ord (1,3) (0,3),0),
(.ord (1,3) (1,2),0),
(.ord (1,3) (2,3),0),
(.ord (2,3) (0,1),0),
(.ord (2,3) (0,2),0),
(.ord (2,3) (0,3),0),
(.ord (2,3) (1,2),0),
(.ord (2,3) (1,3),0),
(.classes 0 [1,2],0),
(.classes 0 [1,3],0),
(.classes 1 [0,2],0),
(.classes 1 [0,3],0),
(.classes 2 [0,3],0),
(.side 0 1 2 3,0)]
private def cert4_0 : List (List Lit × List Nat) := [([(274,false)],[40,10]),
([(289,false)],[41,16]),
([(35,true)],[43,42,3]),
([(275,false)],[44,14]),
([(305,false)],[45,24]),
([(291,false)],[2,21]),
([(306,false)],[3,27]),
([(38,true)],[49,47,9]),
([(54,true)],[50,49,12]),
([(278,false)],[51,21]),
([(353,false)],[52,35]),
([(294,false)],[3,28]),
([(354,false)],[4,38]),
([(310,false)],[4,35]),
([(355,false)],[5,41]),
([(39,true)],[58,55,18]),
([(55,true)],[59,57,21]),
([(103,true)],[60,59,24]),
([(279,false)],[61,31]),
([(369,false)],[62,49]),
([(295,false)],[4,38]),
([(370,false)],[5,52]),
([(311,false)],[5,45]),
([(371,false)],[6,55]),
([(359,false)],[6,52]),
([(374,false)],[7,58]),
([(27,true)],[70,66,26]),
([(59,true)],[71,24,33]),
([(107,true)],[72,20,36]),
([(123,true)],[73,13,38])]
private def cert4_1 : List (List Lit × List Nat) := [([(299,false)],[74,49]),
([(434,false)],[75,67]),
([(283,false)],[5,46]),
([(433,false)],[6,68]),
([(315,false)],[6,58]),
([(435,false)],[7,72]),
([(363,false)],[7,65]),
([(438,false)],[8,75]),
([(379,false)],[8,72]),
([(439,false)],[9,78]),
([],[27,17,85])]
private def cert4 : List (List Lit × List Nat) := cert4_0 ++ cert4_1
set_option maxRecDepth 80000 in
set_option maxHeartbeats 1800000 in
private theorem gen_4_unsat : (gen 4 1).Unsat := unsat_of_core 1 supports4
  (refuted_unsat (core 1 supports4) cert4 (by decide +kernel))
private def supports6 : List (Shape 6 × ℕ) := [(.ord (0,1) (0,2),0),
(.ord (0,1) (0,3),0),
(.ord (0,1) (0,4),0),
(.ord (0,2) (0,1),1),
(.ord (0,2) (0,3),0),
(.ord (0,2) (0,4),0),
(.ord (0,3) (0,4),0),
(.ord (0,4) (0,3),0),
(.ord (0,5) (0,4),1),
(.ord (1,2) (1,3),0),
(.ord (1,2) (1,3),1),
(.ord (1,2) (1,4),0),
(.ord (1,3) (1,4),0),
(.ord (1,5) (2,5),0),
(.ord (1,5) (3,5),0),
(.ord (2,3) (1,3),0),
(.ord (2,4) (1,4),0),
(.ord (2,4) (3,4),1),
(.ord (2,5) (1,5),0),
(.ord (2,5) (3,5),0),
(.ord (3,4) (1,4),0),
(.ord (3,4) (2,4),0),
(.ord (3,5) (1,5),0),
(.ord (3,5) (2,5),0),
(.ord (3,5) (4,5),1),
(.ord (4,5) (0,4),1),
(.ord (4,5) (2,4),0),
(.ord (4,5) (2,5),0),
(.ord (4,5) (3,4),0),
(.ord (4,5) (3,5),0),
(.trans (0,1) (0,2) (0,3),0),
(.trans (0,1) (0,3) (0,4),0),
(.trans (1,2) (1,3) (1,4),0),
(.trans (2,5) (1,5) (3,5),0),
(.trans (3,4) (2,4) (1,4),0),
(.trans (3,5) (2,5) (1,5),0),
(.trans (4,5) (2,5) (3,5),0),
(.trans (4,5) (3,4) (2,4),0),
(.trans (4,5) (3,5) (2,5),0),
(.classes 0 [1,2,3],0),
(.classes 0 [1,3,4],0),
(.classes 0 [2,3,4],0),
(.classes 1 [2,3,4],0),
(.classes 4 [1,2,3],0),
(.classes 4 [2,3,5],0),
(.classes 5 [1,2,3],0),
(.classes 5 [2,3,4],0),
(.side 1 2 3 0,0),
(.side 1 2 4 0,0),
(.side 1 2 5 0,0),
(.side 1 3 4 0,0),
(.side 1 3 4 5,0),
(.side 1 3 5 0,0),
(.side 2 1 5 4,0),
(.side 2 3 4 0,0),
(.side 2 3 4 5,0),
(.side 2 3 5 0,0),
(.side 2 3 5 1,0),
(.side 2 4 5 0,0),
(.side 2 4 5 1,0),
(.side 3 4 0 1,0),
(.side 3 4 5 0,0),
(.side 3 4 5 1,0),
(.side 4 3 1 0,0),
(.acute 1 (0,1),0),
(.acute 1 (0,1),1),
(.acute 2 (1,2),0),
(.acute 2 (1,2),1),
(.acute 3 (3,4),0),
(.acute 3 (3,4),1),
(.acute 4 (4,5),0),
(.acute 4 (4,5),1),
(.acute 5 (4,5),0),
(.acute 5 (4,5),1),
(.acute 5 (0,5),0),
(.acute 5 (0,5),1),
(.four [1,2,3,5],0),
(.four [1,3,4,5],0),
(.four [2,3,4,5],0)]
private def cert6_0 : List (List Lit × List Nat) := [([(2104,false),(2362,false)],[28,21,37,44,26]),
([(1371,false),(2593,true)],[65,66,4,5,31,40,2]),
([(2363,false),(2141,false)],[25,31,40,48,29]),
([(2595,false),(2596,false),(2597,false)],[80,81,69,70,13,1,59,0,65,15,35,45,14]),
([(2594,true),(1630,false)],[16,70,71,14,46,36,15]),
([(1335,true),(635,true),(598,true)],[55,57,25,27,48,50,21,18,58]),
([(2141,false),(598,true)],[29,3,67,12,0,7,37,46,8]),
([(1882,false),(2595,true)],[75,76,24,23,41,50,27]),
([(2595,true)],[76,1,64,12,0,56,8,38,47,9]),
([(1334,false),(1371,false)],[13,9,39,48,10]),
([(2597,false)],[1,6,80,81,34,7,66,14,8,86,5,70,17,51,15,68,37,56,29,65,31,0,58,26,44,53,30]),
([(173,false)],[0,83]),
([(1469,false)],[1,85]),
([(149,false)],[2,87]),
([(1445,false)],[3,89]),
([(2344,true)],[3,2,40]),
([(1480,true)],[2,1,24]),
([(1715,false),(1919,false)],[35,31,50,62,36]),
([(2357,true),(2141,true)],[75,27,74,22,76,77,23,29,59,60,25,30,81]),
([(2357,false),(1931,false)],[38,46,55,65,48]),
([(1919,false),(376,true)],[38,2,71,40,63,41,75,39,65,42,0,55,1]),
([(1371,true)],[75,77,42,14]),
([(75,false)],[0,26]),
([(2593,true)],[1,21]),
([(1334,false)],[2,14]),
([(1845,true)],[0,72]),
([(1882,true)],[1,74]),
([(1919,true)],[2,76]),
([(339,false)],[2,43]),
([(376,false)],[2,45])]
private def cert6_1 : List (List Lit × List Nat) := [([(413,false)],[2,48]),
([(1715,false)],[3,13]),
([],[4,2,11])]
private def cert6 : List (List Lit × List Nat) := cert6_0 ++ cert6_1
set_option maxRecDepth 80000 in
set_option maxHeartbeats 1800000 in
private theorem gen_6_unsat : (gen 6 2).Unsat := unsat_of_core 2 supports6
  (refuted_unsat (core 2 supports6) cert6 (by decide +kernel))
end E982C
/-
Erdős Problem #982 for every n ≤ 11, in the form of formal-conjectures' `Erdos982.erdos_982`: every convex n-gon
(`IsConvexPolygon`, strictly convex, either orientation) has a vertex with at least `n / 2` distinct distances to the
other vertices.

Even n = 4, 6, 8, 10: the bridge (`genA_eval`) and an LRAT certificate (`Cert.lean`). Odd n = 5, 7, 9, 11: delete the
last vertex. n = 3: trivial. The reflected orientation: `i ↦ p (-i)` as in formal-conjectures' definition.
-/


open EuclideanGeometry Std.Sat

namespace E982C

/-- the set of distances from vertex `v` to the other vertices -/
private def dset {n : Nat} (p : Fin n → ℝ²) (v : Fin n) : Set ℝ := {d : ℝ | ∃ j : Fin n, j ≠ v ∧ d = dist (p v) (p j)}

theorem genA_unsat {n K : Nat} [NeZero n] (h : (gen n K).Unsat) (a : Atom n → Bool) :
    (genA n K).eval a = false := by
  have h2 := h (fun x => a (dec x))
  unfold gen at h2
  rw [CNF.eval_relabel] at h2
  have hc : ((fun x => a (dec x)) ∘ enc) = a := by
    funext x
    simp [dec_enc]
  rw [hc] at h2
  exact h2

/-- A refuted CNF `gen n K` gives: every counterclockwise convex `n`-gon has a vertex with at least `K + 1` distinct
distances to the other vertices. -/
theorem ccw_of_unsat {n K : Nat} [NeZero n] (hn : 3 ≤ n) (hU : (gen n K).Unsat) (p : Fin n → ℝ²)
    (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) : ∃ v : Fin n, K + 1 ≤ (dset p v).ncard := by
  by_contra h
  push Not at h
  have h1 := genA_eval (K := K) hn hinj hp h
  have h2 := genA_unsat hU (asg p)
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Odd from even: delete the last vertex. -/
theorem ccw_succ {m k : Nat}
    (H : ∀ p : Fin m → ℝ², Function.Injective p → IsCcwConvexPolygon p → ∃ v : Fin m, k ≤ (dset p v).ncard)
    (p : Fin (m + 1) → ℝ²) (hinj : Function.Injective p) (hp : IsCcwConvexPolygon p) :
    ∃ v : Fin (m + 1), k ≤ (dset p v).ncard := by
  set q : Fin m → ℝ² := fun i => p (Fin.castSucc i) with hq
  have hqinj : Function.Injective q := fun a b h => Fin.castSucc_injective _ (hinj h)
  have hqc : IsCcwConvexPolygon q := by
    intro i j k hij hjk
    exact hp (Fin.castSucc_lt_castSucc_iff.mpr hij) (Fin.castSucc_lt_castSucc_iff.mpr hjk)
  obtain ⟨v, hv⟩ := H q hqinj hqc
  refine ⟨Fin.castSucc v, le_trans hv (Set.ncard_le_ncard ?_ ?_)⟩
  · rintro d ⟨j, hj, rfl⟩
    exact ⟨Fin.castSucc j, fun h => hj (Fin.castSucc_injective _ h), rfl⟩
  · apply (Set.finite_range (fun j : Fin (m + 1) => dist (p (Fin.castSucc v)) (p j))).subset
    rintro d ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩

/-- Both orientations: formal-conjectures' `IsConvexPolygon p` means `p` or `i ↦ p (-i)` is counterclockwise. -/
theorem of_ccw {n k : Nat} [NeZero n]
    (H : ∀ p : Fin n → ℝ², Function.Injective p → IsCcwConvexPolygon p → ∃ v : Fin n, k ≤ (dset p v).ncard)
    (p : Fin n → ℝ²) (hinj : Function.Injective p) (hp : IsConvexPolygon p) :
    ∃ v : Fin n, k ≤ (dset p v).ncard := by
  rcases hp with hccw | hcw
  · exact H p hinj hccw
  · set q : Fin n → ℝ² := fun i => p (-i) with hq
    have hqinj : Function.Injective q := fun a b hab => neg_injective (hinj hab)
    obtain ⟨v, hv⟩ := H q hqinj hcw
    refine ⟨-v, ?_⟩
    have hset : dset q v = dset p (-v) := by
      ext d
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨-j, fun h => hj (neg_injective h), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        refine ⟨-j, fun h => hj (by rw [← h, neg_neg]), ?_⟩
        simp only [hq, neg_neg]
    rw [← hset]
    exact hv

/-- n = 3 (and any n ≥ 2): some vertex has at least one distance. -/
theorem one_le {n : Nat} [NeZero n] (hn : 2 ≤ n) (p : Fin n → ℝ²) : ∃ v : Fin n, 1 ≤ (dset p v).ncard := by
  refine ⟨⟨0, by omega⟩, ?_⟩
  have hfin : (dset p ⟨0, by omega⟩).Finite := by
    apply (Set.finite_range (fun j : Fin n => dist (p ⟨0, by omega⟩) (p j))).subset
    rintro d ⟨j, -, rfl⟩
    exact ⟨j, rfl⟩
  have hne : (dset p ⟨0, by omega⟩).Nonempty :=
    ⟨_, ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h, rfl⟩⟩
  exact (Set.ncard_pos hfin).mpr hne


end E982C
namespace OMA.R_Erdos982_erdos_982_R1
open E982C EuclideanGeometry

/-- Two finite unsatisfiability certificates for distance comparisons,
half-plane order and acute-angle constraints. -/
def H1 : Prop := (gen 8 3).Unsat ∧ (gen 10 4).Unsat

/-- Exclude a realizable comparison table for an even polygon with at least
twelve vertices. The first point is the origin, the order is counterclockwise,
and every vertex has a circle through three other vertices. -/
def H2 : Prop := ∀ m : ℕ, 6 ≤ m → ∀ [NeZero (2*m)] (p : Fin (2*m) → ℝ²),
  Function.Injective p → IsCcwConvexPolygon p → p 0 = 0 →
  (∀ v, ∃ r : ℝ, 2 < ((Finset.univ.erase v).filter (fun j => dist (p v) (p j) = r)).card) →
  (genA (2*m) (m-1)).eval (asg p) = false

section
private lemma heavy {m : ℕ} (hm : 1 ≤ m) {p : Fin (2*m) → ℝ²} (v : Fin (2*m))
    (h : (dset p v).ncard < m) :
    ∃ r : ℝ, 2 < ((Finset.univ.erase v).filter (fun j => dist (p v) (p j) = r)).card := by
  classical
  let S := Finset.univ.erase v
  let f := fun j => dist (p v) (p j)
  have hd : (↑(S.image f) : Set ℝ) = dset p v := by
    ext r
    simp only [Finset.mem_coe,Finset.mem_image,S,Finset.mem_erase,Finset.mem_univ,and_true,dset,Set.mem_setOf_eq,f]
    exact exists_congr fun j => and_congr_right fun _ => eq_comm
  have card := Set.ncard_coe_finset (S.image f)
  rw [hd] at card
  have hS : S.card = 2*m - 1 := by simp [S]
  obtain ⟨r,_,hr⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun j (hj : j ∈ S) => Finset.mem_image_of_mem f hj)
    (show (S.image f).card * 2 < S.card by omega)
  exact ⟨r,hr⟩

private lemma normalized {m : ℕ} (hm : 6 ≤ m) [NeZero (2*m)] (hard : H2)
    (p : Fin (2*m) → ℝ²) (hinj : Function.Injective p) (hc : IsCcwConvexPolygon p) :
    ∃ i, m ≤ (dset p i).ncard := by
  let q := fun i => p i - p 0
  have hq : Function.Injective q := fun a b h => hinj (sub_left_inj.mp h)
  have horient : IsCcwConvexPolygon q := by
    intro i j k hij hjk
    simpa only [q,EuclideanGeometry.oangle,vsub_eq_sub,sub_sub_sub_cancel_right] using hc hij hjk
  have hdist (i j) : dist (q i) (q j) = dist (p i) (p j) := dist_sub_right _ _ _
  have hset (i) : dset q i = dset p i := by simp only [dset,hdist]
  by_contra! bad
  have hb (i) : (dset q i).ncard < m := hset i ▸ bad i
  have hg := genA_eval (K:=m-1) (p:=q) (by omega) hq horient (fun i => by
    have := hb i
    change (dset q i).ncard < m-1+1
    omega)
  have hh := hard m hm q hq horient (sub_self _) (fun v => heavy (by omega) v (hb v))
  exact Bool.noConfusion (hg.symm.trans hh)

private lemma even_case (small : H1) (large : H2) (m : ℕ) (hm : 2 ≤ m)
    (p : Fin (2*m) → ℝ²) (hi : Function.Injective p) (hc : IsCcwConvexPolygon p) :
    ∃ i, m ≤ (dset p i).ncard := by
  letI : NeZero (2*m) := ⟨by omega⟩
  by_cases h : 6 ≤ m
  · exact normalized h large p hi hc
  interval_cases m
  · exact ccw_of_unsat (K:=1) (by decide) gen_4_unsat p hi hc
  · exact ccw_of_unsat (K:=2) (by decide) gen_6_unsat p hi hc
  · exact ccw_of_unsat (K:=3) (by decide) small.1 p hi hc
  · exact ccw_of_unsat (K:=4) (by decide) small.2 p hi hc
private lemma cover_even_odd (small : H1) (large : H2) {n m : ℕ} (hm : 2 ≤ m)
    (he : n=2*m ∨ n=2*m+1) (p : Fin n → ℝ²) (hi : Function.Injective p)
    (hc : IsCcwConvexPolygon p) : ∃ i, m ≤ (dset p i).ncard := by
  rcases he with rfl | rfl
  · exact even_case small large m hm p hi hc
  · exact ccw_succ (even_case small large m hm) p hi hc
end

theorem main : H1 → H2 → type_of% @Erdos982.erdos_982 := by
  intro small large n hn p hi hc
  letI : NeZero n := ⟨by omega⟩
  apply of_ccw (p:=p) (hinj:=hi) (hp:=hc)
  intro q hq hqccw
  by_cases h3 : n=3
  · subst n
    exact one_le (by decide) q
  exact cover_even_odd small large (m:=n/2) (by omega) (by omega) q hq hqccw

end OMA.R_Erdos982_erdos_982_R1
