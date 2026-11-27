import FormalConjectures.ErdosProblems.«466»

/-!
Sárközy's digit construction from On distances near integers II,
Studia Sci. Math. Hungar. 11 (1976), 105–111. Two expansions of the same
word in bases k and k² give coordinate differences of comparable squared
size. This places all the distances strictly between consecutive integers.
-/

open Filter Metric

namespace OMA.Sarkozy466

private def value {k : ℕ} (b : ℕ) : {m : ℕ} → (Fin m → Fin (k - 1)) → ℤ
  | 0, _ => 0
  | m + 1, d => value b (fun i => d i.castSucc) + (d (Fin.last m)).val * (b : ℤ) ^ m

private theorem value_step {k b m : ℕ} (d : Fin (m + 1) → Fin (k - 1)) :
    (value b d : ℝ) =
      (value b (fun i : Fin m => d i.castSucc) : ℝ) + (d (Fin.last m)).val * (b : ℝ) ^ m := by
  push_cast [value]
  rfl

private theorem value_bounds {k b : ℕ} (hk : 2 ≤ k) (hb : 2 ≤ b) :
    ∀ {m : ℕ} (d : Fin m → Fin (k - 1)),
      0 ≤ (value b d : ℝ) ∧
        ((b : ℝ) - 1) * (value b d : ℝ) ≤ ((k : ℝ) - 2) * ((b : ℝ) ^ m - 1) := by
  intro m
  induction m with
  | zero =>
    intro d
    simp [value]
  | succ m ih =>
    intro d
    obtain ⟨hlo, hhi⟩ := ih (fun i => d i.castSucc)
    have hDigitNat : (d (Fin.last m)).val + 2 ≤ k := by
      have := (d (Fin.last m)).isLt
      omega
    have hDigit : ((d (Fin.last m)).val : ℝ) ≤ (k : ℝ) - 2 := by
      have h : ((d (Fin.last m)).val : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hDigitNat
      linarith
    have hB : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    have hd : (((b : ℝ) - 1) * (b : ℝ) ^ m) * (d (Fin.last m)).val ≤
        (((b : ℝ) - 1) * (b : ℝ) ^ m) * ((k : ℝ) - 2) :=
      mul_le_mul_of_nonneg_left hDigit (by positivity)
    rw [value_step, pow_succ]
    exact ⟨by positivity, by linarith only [hhi, hd]⟩

private theorem diff_bound {k b m : ℕ} (hk : 2 ≤ k) (hb : 2 ≤ b)
    (d e : Fin m → Fin (k - 1)) :
    ((b : ℝ) - 1) * |(value b d : ℝ) - (value b e : ℝ)| ≤ ((k : ℝ) - 2) * (b : ℝ) ^ m := by
  obtain ⟨hd0, hd⟩ := value_bounds hk hb d
  obtain ⟨he0, he⟩ := value_bounds hk hb e
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rcases le_total (value b d : ℝ) (value b e : ℝ) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    nlinarith only [he, mul_nonneg (sub_nonneg.mpr hb') hd0, hk']
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    nlinarith only [hd, mul_nonneg (sub_nonneg.mpr hb') he0, hk']

private theorem spread {c p x y : ℝ} (hc : 1 ≤ c) (hp : 0 ≤ p) (hy : 1 ≤ |y|)
    (hx : c * |x| ≤ (c - 1) * p) :
    |y| * p ≤ c * |x + y * p| ∧ |x + y * p| ≤ 2 * |y| * p := by
  have hreverse : |y| * p ≤ |x + y * p| + |x| := by
    have h := abs_add_le (x + y * p) (-x)
    rw [show x + y * p + -x = y * p by ring, abs_neg, abs_mul, abs_of_nonneg hp] at h
    exact h
  have hscaled := mul_le_mul_of_nonneg_left hreverse (show 0 ≤ c by linarith)
  have hextra := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hc)) hp
  have hsmall : |x| ≤ p := by
    have h1 : c * |x| ≤ c * p := by linarith only [hx, hp]
    exact le_of_mul_le_mul_left h1 (by linarith)
  have habs := abs_add_le x (y * p)
  rw [abs_mul, abs_of_nonneg hp] at habs
  have hlarge := mul_le_mul_of_nonneg_right hy hp
  exact ⟨by linarith only [hscaled, hx, hextra], by linarith only [habs, hsmall, hlarge]⟩

private theorem digit_separation {k : ℕ} (hk : 2 ≤ k) :
    ∀ {m : ℕ} (d e : Fin m → Fin (k - 1)), d ≠ e →
      ∃ i : ℕ, ∃ D : ℝ, 1 ≤ D ∧ D ≤ k ∧
        D * (k : ℝ) ^ i ≤ (k : ℝ) * |(value k d : ℝ) - (value k e : ℝ)| ∧
        |(value k d : ℝ) - (value k e : ℝ)| ≤ 2 * D * (k : ℝ) ^ i ∧
        D * ((k : ℝ) ^ 2) ^ i ≤ 2 * |(value (k ^ 2) d : ℝ) - (value (k ^ 2) e : ℝ)| ∧
        |(value (k ^ 2) d : ℝ) - (value (k ^ 2) e : ℝ)| ≤ 2 * D * ((k : ℝ) ^ 2) ^ i := by
  intro m
  induction m with
  | zero =>
    intro d e hne
    exact (hne (Subsingleton.elim _ _)).elim
  | succ m ih =>
    intro d e hne
    let d' : Fin m → Fin (k - 1) := fun i => d i.castSucc
    let e' : Fin m → Fin (k - 1) := fun i => e i.castSucc
    by_cases htop : d (Fin.last m) = e (Fin.last m)
    · have hne' : d' ≠ e' := by
        intro h
        apply hne
        funext j
        refine Fin.lastCases htop (fun i => congrFun h i) j
      obtain ⟨i, D, hD, hDk, hx1, hx2, hy1, hy2⟩ := ih d' e' hne'
      have hdiff (b : ℕ) : (value b d : ℝ) - (value b e : ℝ) =
          (value b d' : ℝ) - (value b e' : ℝ) := by
        rw [value_step, value_step, htop]
        dsimp [d', e']
        ring
      rw [hdiff k, hdiff (k ^ 2)]
      exact ⟨i, D, hD, hDk, hx1, hx2, hy1, hy2⟩
    · let y : ℝ := (d (Fin.last m)).val - (e (Fin.last m)).val
      have hd : (d (Fin.last m)).val < k := by
        have := (d (Fin.last m)).isLt
        omega
      have he : (e (Fin.last m)).val < k := by
        have := (e (Fin.last m)).isLt
        omega
      have hnot : (d (Fin.last m)).val ≠ (e (Fin.last m)).val :=
        fun h => htop (Fin.ext h)
      have hy : 1 ≤ |y| := by
        rcases lt_or_gt_of_ne hnot with h | h
        · have hr : ((d (Fin.last m)).val : ℝ) + 1 ≤ (e (Fin.last m)).val := by
            exact_mod_cast h
          have : y ≤ -1 := by dsimp [y]; linarith
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hr : ((e (Fin.last m)).val : ℝ) + 1 ≤ (d (Fin.last m)).val := by
            exact_mod_cast h
          have : 1 ≤ y := by dsimp [y]; linarith
          rwa [abs_of_nonneg (by linarith)]
      have hyk : |y| ≤ (k : ℝ) := by
        have hd' : ((d (Fin.last m)).val : ℝ) < (k : ℝ) := by exact_mod_cast hd
        have he' : ((e (Fin.last m)).val : ℝ) < (k : ℝ) := by exact_mod_cast he
        dsimp [y]
        rw [abs_le]
        constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (d (Fin.last m)).val,
          Nat.cast_nonneg (α := ℝ) (e (Fin.last m)).val]
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      have hk2 : 2 ≤ k ^ 2 := by nlinarith
      have htail₁ := diff_bound hk hk d' e'
      have htail₂ := diff_bound hk hk2 d' e'
      push_cast at htail₂
      set x := |(value k d' : ℝ) - (value k e' : ℝ)| with hx
      set z := |(value (k ^ 2) d' : ℝ) - (value (k ^ 2) e' : ℝ)| with hz
      set p := (k : ℝ) ^ m with hp
      set q := ((k : ℝ) ^ 2) ^ m with hq
      have hp0 : 0 ≤ p := by positivity
      have hq0 : 0 ≤ q := by positivity
      have htail₁' : (k : ℝ) * x ≤ ((k : ℝ) - 1) * p := by
        have h := mul_le_mul_of_nonneg_left htail₁ (show 0 ≤ (k : ℝ) by positivity)
        have h' := mul_nonneg (show 0 ≤ (k : ℝ) by positivity) hp0
        have hres : ((k : ℝ) - 1) * ((k : ℝ) * x) ≤
            ((k : ℝ) - 1) * (((k : ℝ) - 1) * p) := by
          linarith only [h, hp0]
        exact le_of_mul_le_mul_left hres (by linarith)
      have htail₂' : 2 * z ≤ (2 - 1) * q := by
        have h := mul_le_mul_of_nonneg_left htail₂ (by norm_num : (0 : ℝ) ≤ 2)
        have hpoly : (2 : ℝ) * ((k : ℝ) - 2) ≤ (k : ℝ) ^ 2 - 1 := by
          nlinarith [sq_nonneg ((k : ℝ) - 1)]
        have hprod := mul_le_mul_of_nonneg_right hpoly hq0
        have hres : ((k : ℝ) ^ 2 - 1) * (2 * z) ≤
            ((k : ℝ) ^ 2 - 1) * ((2 - 1) * q) := by
          linarith only [h, hprod]
        exact le_of_mul_le_mul_left hres (by nlinarith)
      have hdiff (b : ℕ) : (value b d : ℝ) - (value b e : ℝ) =
          (value b d' : ℝ) - (value b e' : ℝ) + y * (b : ℝ) ^ m := by
        simp only [value_step, d', e', y]
        ring
      rw [hdiff k, hdiff (k ^ 2)]
      push_cast
      have h₁ := spread (c := (k : ℝ)) (by linarith) hp0 hy htail₁'
      have h₂ := spread (c := 2) (by norm_num) hq0 hy htail₂'
      exact ⟨m, |y|, hy, hyk, h₁.1, h₁.2, h₂.1, h₂.2⟩


private def height {k m : ℕ} (d : Fin m → Fin (k - 1)) : ℤ :=
  8 * (k : ℤ) ^ 2 * value (k ^ 2) d

private noncomputable def point {k m : ℕ} (d : Fin m → Fin (k - 1)) :
    EuclideanSpace ℝ (Fin 2) :=
  !₂[(value k d : ℝ), (height d : ℝ)]

private theorem point_first {k m : ℕ} (d : Fin m → Fin (k - 1)) :
    point d 0 = (value k d : ℝ) := by simp [point]

private theorem point_second {k m : ℕ} (d : Fin m → Fin (k - 1)) :
    point d 1 = (height d : ℝ) := by simp [point]

private theorem point_dist {k m : ℕ} (d e : Fin m → Fin (k - 1)) :
    dist (point d) (point e) =
      Real.sqrt (((|height d - height e| : ℤ) : ℝ) ^ 2 +
        |(value k d : ℝ) - (value k e : ℝ)| ^ 2) := by
  rw [EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, point_first, point_second, Real.dist_eq, Int.cast_abs,
    Int.cast_sub]
  rw [add_comm]

private theorem point_injective {k m : ℕ} (hk : 2 ≤ k) :
    Function.Injective (@point k m) := by
  intro d e h
  by_contra hne
  obtain ⟨i, D, hD, _, hx, _, _, _⟩ := digit_separation hk d e hne
  have heq := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
  simp only [point_first] at heq
  rw [heq, sub_self, abs_zero, mul_zero] at hx
  exact (not_le_of_gt (show 0 < D * (k : ℝ) ^ i by positivity)) hx

private theorem nearestInt_gt {x δ : ℝ} (a : ℤ)
    (hleft : (a : ℝ) + δ < x) (hright : x < (a : ℝ) + 1 - δ) :
    δ < distToNearestInt x := by
  unfold distToNearestInt
  have hz : round x ≤ a ∨ a + 1 ≤ round x := by omega
  rcases hz with hza | haz
  · have hza' : ((round x : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hza
    exact (show δ < x - (round x : ℝ) by linarith).trans_le (le_abs_self _)
  · have haz' : (a : ℝ) + 1 ≤ ((round x : ℤ) : ℝ) := by exact_mod_cast haz
    exact (show δ < -(x - (round x : ℝ)) by linarith).trans_le (neg_le_abs _)

private theorem sqrt_separated {δ r : ℝ} (a : ℤ) (ha : 1 ≤ a) (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) (hlo : 3 * δ * (a : ℝ) ≤ r) (hhi : r ≤ (a : ℝ)) :
    δ < distToNearestInt (Real.sqrt ((a : ℝ) ^ 2 + r)) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hr : 0 ≤ r := (by positivity : 0 ≤ 3 * δ * (a : ℝ)).trans hlo
  have hs : 0 ≤ (a : ℝ) ^ 2 + r := by positivity
  have hsq := Real.sq_sqrt hs
  have hnonneg := Real.sqrt_nonneg ((a : ℝ) ^ 2 + r)
  apply nearestInt_gt a
  · by_contra! h
    have hsq' : (Real.sqrt ((a : ℝ) ^ 2 + r)) ^ 2 ≤ ((a : ℝ) + δ) ^ 2 := by
      gcongr
    have hgap : 0 < δ * ((a : ℝ) - δ) := mul_pos hδ (by linarith)
    nlinarith only [hsq', hsq, hgap, hlo]
  · by_contra! h
    have hsq' : ((a : ℝ) + 1 - δ) ^ 2 ≤ (Real.sqrt ((a : ℝ) ^ 2 + r)) ^ 2 := by
      have : 0 ≤ (a : ℝ) + 1 - δ := by linarith
      gcongr
    have hgap : 0 ≤ (a : ℝ) * (1 - 2 * δ) :=
      mul_nonneg (by linarith) (by linarith)
    have hpos : 0 < (1 - δ) ^ 2 := by
      have hd : 0 < 1 - δ := by linarith
      positivity
    nlinarith only [hsq', hsq, hgap, hpos, hhi]

private theorem point_separated {k m : ℕ} (hk : 2 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hsmall : 48 * δ * (k : ℝ) ^ 4 ≤ 1)
    (d e : Fin m → Fin (k - 1)) (hne : d ≠ e) :
    δ < distToNearestInt (dist (point d) (point e)) := by
  obtain ⟨i, D, hD, hDk, hx₁, hx₂, hy₁, hy₂⟩ := digit_separation hk d e hne
  let p : ℝ := (k : ℝ) ^ i
  let x : ℝ := |(value k d : ℝ) - (value k e : ℝ)|
  let a : ℤ := |height d - height e|
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < p := by dsimp [p]; positivity
  have hx0 : 0 ≤ x := abs_nonneg _
  have hx1 : D * p ≤ (k : ℝ) * x := hx₁
  have hx2 : x ≤ 2 * D * p := hx₂
  have hpow : ((k : ℝ) ^ 2) ^ i = p ^ 2 := by dsimp [p]; rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hpow] at hy₁ hy₂
  have haEq : (a : ℝ) = 8 * (k : ℝ) ^ 2 *
      |(value (k ^ 2) d : ℝ) - (value (k ^ 2) e : ℝ)| := by
    dsimp [a, height]
    push_cast
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  have haLo : 4 * (k : ℝ) ^ 2 * D * p ^ 2 ≤ (a : ℝ) := by
    rw [haEq]
    have h := mul_le_mul_of_nonneg_left hy₁ (show 0 ≤ 4 * (k : ℝ) ^ 2 by positivity)
    linarith only [h]
  have haHi : (a : ℝ) ≤ 16 * (k : ℝ) ^ 2 * D * p ^ 2 := by
    rw [haEq]
    have h := mul_le_mul_of_nonneg_left hy₂ (show 0 ≤ 8 * (k : ℝ) ^ 2 by positivity)
    linarith only [h]
  have ha : 1 ≤ a := by
    have hl : 0 < (a : ℝ) := lt_of_lt_of_le (by positivity) haLo
    have hn : 0 < a := by exact_mod_cast hl
    omega
  have hupper : x ^ 2 ≤ (a : ℝ) := by
    have hD2 : D ≤ (k : ℝ) ^ 2 := hDk.trans (by nlinarith [sq_nonneg ((k : ℝ) - 1)])
    calc
      x ^ 2 ≤ (2 * D * p) ^ 2 := by gcongr
      _ = 4 * D * p ^ 2 * D := by ring
      _ ≤ 4 * D * p ^ 2 * (k : ℝ) ^ 2 := by gcongr
      _ = 4 * (k : ℝ) ^ 2 * D * p ^ 2 := by ring
      _ ≤ (a : ℝ) := haLo
  have hlower : (a : ℝ) ≤ 16 * (k : ℝ) ^ 4 * x ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      (show (D * p) ^ 2 ≤ ((k : ℝ) * x) ^ 2 by gcongr)
      (show 0 ≤ 16 * (k : ℝ) ^ 2 by positivity)
    calc
      (a : ℝ) ≤ 16 * (k : ℝ) ^ 2 * D * p ^ 2 := haHi
      _ ≤ 16 * (k : ℝ) ^ 2 * (D * p) ^ 2 := by
        have hDsq : D ≤ D ^ 2 := by nlinarith [sq_nonneg (D - 1)]
        calc
          _ = (16 * (k : ℝ) ^ 2 * p ^ 2) * D := by ring
          _ ≤ (16 * (k : ℝ) ^ 2 * p ^ 2) * D ^ 2 :=
            mul_le_mul_of_nonneg_left hDsq (by positivity)
          _ = _ := by ring
      _ ≤ 16 * (k : ℝ) ^ 2 * ((k : ℝ) * x) ^ 2 := h
      _ = _ := by ring
  have hl : 3 * δ * (a : ℝ) ≤ x ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hlower (show 0 ≤ 3 * δ by positivity)
    have h' := mul_le_mul_of_nonneg_right hsmall (sq_nonneg x)
    linarith only [h, h']
  rw [point_dist]
  exact sqrt_separated a ha hδ hδhalf hl hupper

private theorem value_le_pow {k b m : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b)
    (d : Fin m → Fin (k - 1)) : (value b d : ℝ) ≤ (b : ℝ) ^ m := by
  have hb : 2 ≤ b := hk.trans hkb
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkb' : (k : ℝ) ≤ b := by exact_mod_cast hkb
  have hpow : 1 ≤ (b : ℝ) ^ m := one_le_pow₀ (by linarith)
  have h := (value_bounds hk hb d).2
  have h' : ((b : ℝ) - 1) * (value b d : ℝ) ≤ ((b : ℝ) - 1) * (b : ℝ) ^ m := by
    calc
      _ ≤ ((k : ℝ) - 2) * ((b : ℝ) ^ m - 1) := h
      _ ≤ ((b : ℝ) - 1) * (b : ℝ) ^ m :=
        mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  exact le_of_mul_le_mul_left h' (by linarith)

private theorem point_closedBall {k m : ℕ} (hk : 2 ≤ k) (d : Fin m → Fin (k - 1)) :
    point d ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2))
      (16 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 2) ^ m) := by
  have hk2 : k ≤ k ^ 2 := by nlinarith
  have hk2' : (k : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hk2
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  let B : ℝ := 8 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 2) ^ m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h₁ := value_le_pow hk le_rfl d
  have h₂ := value_le_pow hk hk2 d
  push_cast at h₂
  have hq : (k : ℝ) ^ m ≤ ((k : ℝ) ^ 2) ^ m := by gcongr
  have hBD : ((k : ℝ) ^ 2) ^ m ≤ B := by
    dsimp [B]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 8 * (k : ℝ) ^ 2 by nlinarith) (by positivity : 0 ≤ ((k : ℝ) ^ 2) ^ m)
  have h₁' := (h₁.trans hq).trans hBD
  have h₂' : (height d : ℝ) ≤ B := by
    dsimp [height, B]
    push_cast
    exact mul_le_mul_of_nonneg_left h₂ (by positivity)
  have h₁0 := (value_bounds hk hk d).1
  have h₂0 : 0 ≤ (height d : ℝ) := by
    have hv := (value_bounds hk (hk.trans hk2) d).1
    dsimp [height]
    push_cast
    positivity
  have hs₁ : (value k d : ℝ) ^ 2 ≤ B ^ 2 := by gcongr
  have hs₂ : (height d : ℝ) ^ 2 ≤ B ^ 2 := by gcongr
  rw [mem_closedBall, EuclideanSpace.dist_eq]
  simp only [Fin.sum_univ_two, point_first, point_second, PiLp.zero_apply,
    Real.dist_eq, sub_zero, sq_abs]
  rw [show 16 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 2) ^ m = 2 * B by dsimp [B]; ring,
    Real.sqrt_le_iff]
  exact ⟨by positivity, by nlinarith only [hs₁, hs₂, sq_nonneg B]⟩

-- The compactness argument is adapted from @timlantin's merged Graham variant,
-- open-math-agents, under Apache-2.0.
private def admissibleSizes (X δ : ℝ) : Set ℕ :=
  {n | ∃ (c : EuclideanSpace ℝ (Fin 2)) (P : Finset (EuclideanSpace ℝ (Fin 2))),
    P.card = n ∧ ↑P ⊆ closedBall c X ∧
      (P : Set (EuclideanSpace ℝ (Fin 2))).Pairwise fun x y => δ ≤ distToNearestInt (dist x y)}

private theorem admissible_bounded (X : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    BddAbove (admissibleSizes X δ) := by
  obtain ⟨t, _, htfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) X)
      (by positivity : 0 < δ / 3)
  refine ⟨htfin.toFinset.card, ?_⟩
  rintro n ⟨c, P, rfl, hPsub, hsep⟩
  have hchoice : ∀ x ∈ P, ∃ y ∈ t, dist (x - c) y < δ / 3 := by
    intro x hx
    have hx' : x - c ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) X := by
      rw [mem_closedBall]
      simpa [dist_eq_norm] using hPsub hx
    rcases Set.mem_iUnion.mp (hcover hx') with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyt, hyball⟩
    exact ⟨y, hyt, hyball⟩
  classical
  let f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun x =>
    if hx : x ∈ P then (hchoice x hx).choose else 0
  have hf_mem : ∀ x ∈ P, f x ∈ htfin.toFinset := by
    intro x hx
    simp only [f, dif_pos hx, Set.Finite.mem_toFinset]
    exact (hchoice x hx).choose_spec.1
  have hf_close : ∀ x ∈ P, dist (x - c) (f x) < δ / 3 := by
    intro x hx
    simp only [f, dif_pos hx]
    exact (hchoice x hx).choose_spec.2
  apply Finset.card_le_card_of_injOn f (fun x hx => hf_mem x hx)
  intro x hx y hy hxy
  by_contra hne
  have hlt : dist x y < δ := by
    calc
      dist x y = dist (x - c) (y - c) := by rw [dist_sub_right]
      _ ≤ dist (x - c) (f x) + dist (f x) (y - c) := dist_triangle _ _ _
      _ < δ / 3 + δ / 3 := by
        apply add_lt_add (hf_close x hx)
        rw [dist_comm, hxy]
        exact hf_close y hy
      _ < δ := by linarith
  have hnearest : distToNearestInt (dist x y) ≤ dist x y := by
    unfold distToNearestInt
    simpa [abs_of_nonneg (dist_nonneg : 0 ≤ dist x y)] using round_le (dist x y) (0 : ℤ)
  exact (not_le_of_gt hlt) ((hsep hx hy hne).trans hnearest)

private theorem pow_le_N {k m : ℕ} (hk : 2 ≤ k) {δ X : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hsmall : 48 * δ * (k : ℝ) ^ 4 ≤ 1)
    (hX : 16 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 2) ^ m ≤ X) :
    (k - 1) ^ m ≤ Erdos466.N X δ := by
  classical
  change _ ≤ sSup (admissibleSizes X δ)
  apply le_csSup (admissible_bounded X hδ)
  let P := (Finset.univ : Finset (Fin m → Fin (k - 1))).image point
  refine ⟨0, P, ?_, ?_, ?_⟩
  · simp [P, Finset.card_image_of_injective _ (point_injective hk)]
  · intro x hx
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    exact closedBall_subset_closedBall hX (point_closedBall hk d)
  · intro x hx y hy hxy
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hy
    exact (point_separated hk hδ hδhalf hsmall d e (fun h => hxy (congrArg point h))).le


private theorem exponent_choice {δ : ℝ} (hδ : 0 < δ) (hδ₀ : δ < (1 / 64 : ℝ) ^ 7) :
    ∃ k : ℕ, 2 ≤ k ∧ 48 * δ * (k : ℝ) ^ 4 ≤ 1 ∧
      (1 - δ ^ (1 / 7 : ℝ)) * Real.log (k : ℝ) ≤ Real.log ((k - 1 : ℕ) : ℝ) := by
  let e := δ ^ (1 / 7 : ℝ)
  have he : 0 < e := by dsimp [e]; positivity
  have he7 : e ^ 7 = δ := by
    dsimp [e]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    norm_num
  have he64 : e ≤ 1 / 64 := by
    by_contra! h
    have hpow : (1 / 64 : ℝ) ^ 7 < e ^ 7 := by gcongr
    rw [he7] at hpow
    linarith only [hpow, hδ₀]
  let k := ⌈4 / e⌉₊
  have hceil : 4 / e ≤ (k : ℝ) := Nat.le_ceil _
  have hceilu : (k : ℝ) < 4 / e + 1 := Nat.ceil_lt_add_one (by positivity)
  have hke : 4 ≤ (k : ℝ) * e := (div_le_iff₀ he).mp hceil
  have hkeu : (k : ℝ) * e ≤ 5 := by
    have h := (lt_div_iff₀ he).mp (show (k : ℝ) < (4 + e) / e by
      rw [add_div, div_self he.ne']
      exact hceilu)
    linarith only [h, he64]
  have hk4 : (4 : ℝ) ≤ k := by
    calc
      (4 : ℝ) ≤ (k : ℝ) * e := hke
      _ ≤ (k : ℝ) * 1 := mul_le_mul_of_nonneg_left (by linarith only [he64]) (by positivity)
      _ = _ := mul_one _
  have hk : 2 ≤ k := by exact_mod_cast (show (2 : ℝ) ≤ k by linarith)
  have hsmall : 48 * δ * (k : ℝ) ^ 4 ≤ 1 := by
    rw [← he7]
    calc
      48 * e ^ 7 * (k : ℝ) ^ 4 = 48 * e ^ 3 * ((k : ℝ) * e) ^ 4 := by ring
      _ ≤ 48 * (1 / 64 : ℝ) ^ 3 * (5 : ℝ) ^ 4 := by gcongr
      _ ≤ 1 := by norm_num
  refine ⟨k, hk, hsmall, ?_⟩
  change (1 - e) * Real.log (k : ℝ) ≤ _
  have hk0 : (0 : ℝ) < k := by linarith
  have hkm0 : 0 < (k : ℝ) - 1 := by linarith
  have hlog : 1 ≤ Real.log (k : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_one_lt_d9])
  have hRecip : 1 / ((k : ℝ) - 1) ≤ e := by
    apply (div_le_iff₀ hkm0).2
    linarith only [hke, he64]
  have hRatio := Real.log_le_sub_one_of_pos (div_pos hk0 hkm0)
  rw [Real.log_div hk0.ne' hkm0.ne',
    show (k : ℝ) / ((k : ℝ) - 1) - 1 = 1 / ((k : ℝ) - 1) by field_simp; ring] at hRatio
  have hProd := mul_le_mul_of_nonneg_left hlog he.le
  rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  linarith only [hRatio, hRecip, hProd]

private theorem growth {k : ℕ} (hk : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    (hδhalf : δ < 1 / 2) (hsmall : 48 * δ * (k : ℝ) ^ 4 ≤ 1)
    (hlog : (1 - δ ^ (1 / 7 : ℝ)) * Real.log (k : ℝ) ≤ Real.log ((k - 1 : ℕ) : ℝ))
    (he1 : δ ^ (1 / 7 : ℝ) < 1) :
    ∀ᶠ X : ℝ in atTop, X ^ (1 / 2 - δ ^ (1 / 7 : ℝ)) < Erdos466.N X δ := by
  let e := δ ^ (1 / 7 : ℝ)
  let L := Real.log (k : ℝ)
  let B := 16 * (k : ℝ) ^ 2
  let β := (1 - e) / 2
  have he : 0 < e := by dsimp [e]; positivity
  have hβ : 0 < β := by dsimp [β]; linarith
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : 0 < L := Real.log_pos (by linarith)
  have hB : 0 < B := by dsimp [B]; positivity
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hL2 : Real.log ((k : ℝ) ^ 2) = 2 * L := by
    rw [Real.log_pow]
    norm_num [L]
  have hlog' : (1 - e) * L ≤ Real.log ((k - 1 : ℕ) : ℝ) := hlog
  filter_upwards [eventually_ge_atTop B,
    (Real.tendsto_log_atTop.eventually_ge_atTop (2 * (β * (Real.log B + 2 * L) + 1) / e))]
    with X hX hLX
  have hX0 : 0 < X := hB.trans_le hX
  have hXB : Real.log B ≤ Real.log X := Real.log_le_log hB hX
  let u := (Real.log X - Real.log B) / (2 * L)
  have hu0 : 0 ≤ u := div_nonneg (sub_nonneg.mpr hXB) (by positivity)
  let m := ⌊u⌋₊
  have hm1 : (m : ℝ) ≤ u := Nat.floor_le hu0
  have hm2 : u < (m : ℝ) + 1 := Nat.lt_floor_add_one u
  have hmul1 : (m : ℝ) * (2 * L) ≤ Real.log X - Real.log B :=
    (le_div_iff₀ (by positivity : 0 < 2 * L)).mp hm1
  have hmul2 : Real.log X - Real.log B < ((m : ℝ) + 1) * (2 * L) :=
    (div_lt_iff₀ (by positivity : 0 < 2 * L)).mp hm2
  have hradius : B * ((k : ℝ) ^ 2) ^ m ≤ X := by
    apply (Real.log_le_log_iff (by positivity) hX0).mp
    rw [Real.log_mul hB.ne' (pow_ne_zero _ hk2.ne'), Real.log_pow, hL2]
    linarith only [hmul1]
  have hN := pow_le_N hk hδ hδhalf hsmall hradius
  have hkminus : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hlogsize : (1 / 2 - e) * Real.log X <
      (m : ℝ) * Real.log ((k - 1 : ℕ) : ℝ) := by
    have hLX' := (div_le_iff₀ he).mp hLX
    have hm' : Real.log X - Real.log B - 2 * L < (m : ℝ) * (2 * L) := by
      linarith only [hmul2]
    have heq : β * ((m : ℝ) * (2 * L)) = (m : ℝ) * ((1 - e) * L) := by dsimp [β]; ring
    calc
      (1 / 2 - e) * Real.log X < β * (Real.log X - Real.log B - 2 * L) := by
        dsimp [β] at hLX' ⊢
        linarith only [hLX']
      _ < β * ((m : ℝ) * (2 * L)) := mul_lt_mul_of_pos_left hm' hβ
      _ = (m : ℝ) * ((1 - e) * L) := heq
      _ ≤ (m : ℝ) * Real.log ((k - 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog' (by positivity)
  have hstrict : X ^ (1 / 2 - e) < (((k - 1 : ℕ) : ℝ) ^ m) := by
    apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hX0 _) (pow_pos hkminus _) ).mp
    rw [Real.log_rpow hX0, Real.log_pow]
    exact hlogsize
  exact hstrict.trans_le (by exact_mod_cast hN)

end OMA.Sarkozy466

theorem OMA.solution : type_of% @Erdos466.erdos_466.variants.sarkozy := by
  refine ⟨(1 / 64 : ℝ) ^ 7, by norm_num, ?_⟩
  intro δ hδ hδ₀
  obtain ⟨k, hk, hsmall, hlog⟩ := OMA.Sarkozy466.exponent_choice hδ hδ₀
  have hδhalf : δ < 1 / 2 := hδ₀.trans (by norm_num)
  have he1 : δ ^ (1 / 7 : ℝ) < 1 := Real.rpow_lt_one hδ.le (by linarith) (by norm_num)
  exact OMA.Sarkozy466.growth hk hδ hδhalf hsmall hlog he1
