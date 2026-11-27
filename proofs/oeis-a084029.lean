import OMAStatements.S_oeis_a084029

namespace OMA.S_oeis_a084029

private abbrev width (a : ℕ) := (Nat.digits 10 a).length
private abbrev ds (a : ℕ) := (Nat.digits 10 a).sum

private theorem dsStep (m : ℕ) : ds m = m%10 + ds (m/10) := by
  cases m with
  | zero => decide
  | succ m => unfold ds; rw [Nat.digits_def' (by decide : 1 < 10) (Nat.succ_pos m), List.sum_cons]

/-- The complementary positions add to 9, including padded leading zeros. -/
private theorem complement (u a : ℕ) (h : a < 10^u) : ds a + ds (10^u-1-a) = 9*u := by
  induction u generalizing a with
  | zero =>
    have : a = 0 := by simpa using h
    subst a
    decide
  | succ u ih =>
    rw [pow_succ] at h ⊢
    have hdiv : a/10 < 10^u := by omega
    have hc := ih (a/10) hdiv
    rw [dsStep a, dsStep (10^u*10-1-a),
      show (10^u*10-1-a)/10 = 10^u-1-a/10 by omega,
      show (10^u*10-1-a)%10 = 9-a%10 by omega]
    omega

private theorem digitBound (n : ℕ) : ds n ≤ 9*width n := by
  have aux (l : List ℕ) (hs : ∀ d ∈ l, d < 10) : l.sum ≤ 9*l.length := by
    induction l with
    | nil => decide
    | cons d l ih =>
      have hd := hs d (by simp)
      have htl := ih (fun c hc => hs c (List.mem_cons_of_mem _ hc))
      simp only [List.sum_cons, List.length_cons]
      omega
  exact aux _ (fun _ h => Nat.digits_lt_base (by decide : 1 < 10) h)

private theorem widthBound {n : ℕ} (hn : 36 ≤ n) : 18*width n ≤ n := by
  have hp (i : ℕ) : 18*(i+3) ≤ 10^(i+2) := by
    induction i with
    | zero => decide
    | succ i ih => rw [show i+1+2 = (i+2)+1 by omega, pow_succ]; omega
  by_cases hd : width n ≤ 2
  · omega
  · obtain ⟨i, hi⟩ : ∃ i, width n = i+3 := ⟨width n - 3, by omega⟩
    have hlow := (Nat.lt_digits_length_iff (k := i+2) (by decide : 1 < 10) n).mp (by change i+2 < width n; omega)
    rw [hi]
    exact (hp i).trans hlow

private theorem joined {lo hi k : ℕ} (hlo : width lo ≤ k) (hhi : 0 < hi) :
    width (lo + 10^k*hi) = k + width hi ∧ ds (lo + 10^k*hi) = ds lo + ds hi := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hlo
  have he := Nat.digits_append_zeroes_append_digits (b := 10) (n := lo) (k := v) (by decide) hhi
  unfold width ds
  rw [← he]
  simp [Nat.add_assoc]

private def glue (n hi lo j : ℕ) := 10^j*lo + 10^(n-width hi)*hi

private theorem glueSpec {n W hi lo j : ℕ} (hh : 0 < hi) (hl : 0 < lo)
    (hwh : width hi ≤ W) (hwl : width lo ≤ W) (hj : j+W ≤ n-W) (hW : W ≤ n)
    (hs : ds lo + ds hi = n) (hdh : n ∣ hi) (hdl : n ∣ lo) :
    qualifies n (glue n hi lo j) ∧ glue n hi lo j % 10^(n-W) = 10^j*lo := by
  have hword := Nat.digits_base_pow_mul (b := 10) (k := j) (by decide) hl
  have hwidth : width (10^j*lo) = j + width lo := by simp [width, hword]
  have hsum : ds (10^j*lo) = ds lo := by simp [ds, hword]
  have hcut : n-W ≤ n-width hi := by omega
  have hlow : width (10^j*lo) ≤ n-W := by omega
  obtain ⟨hw, hds⟩ := joined (hlow.trans hcut) hh
  have hpow : 10^(n-W) ∣ 10^(n-width hi)*hi := dvd_mul_of_dvd_left (Nat.pow_dvd_pow 10 hcut) _
  have hlt := (Nat.digits_length_le_iff (by decide : 1 < 10) (10^j*lo)).mp hlow
  unfold glue
  constructor
  · refine ⟨?_, dvd_add (dvd_mul_of_dvd_right hdl _) (dvd_mul_of_dvd_right hdh _), ?_⟩
    · change width _ = _
      omega
    · change ds _ = _
      omega
  · rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpow, Nat.mod_eq_of_lt hlt, Nat.add_zero, Nat.mod_eq_of_lt hlt]

/-- The blocks `n` and `n*(10^u-1)` have digit sums adding to `n`. Either
block can lead; the other may move among the unused positions below it. -/
private theorem largeRow {n : ℕ} (hn : 36 ≤ n) :
    ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ m ∈ s, qualifies n m := by
  let d := width n
  let u := (n-ds n)/9
  let W := u+d
  let A := n*(10^u-1)
  have hd : 0 < d := List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega))
  have h18 : 18*d ≤ n := widthBound hn
  have h9 : ds n ≤ 9*d := digitBound n
  have hmod : n%9 = ds n%9 := Nat.modEq_nine_digits_sum n
  have htotal : ds n + 9*u = n := by dsimp [u]; omega
  have hdu : d ≤ u := by omega
  have hW : 4*W ≤ n := by dsimp [W]; omega
  have hpow : n < 10^d := Nat.lt_base_pow_length_digits (by decide)
  have hnu : n < 10^u := hpow.trans_le (Nat.pow_le_pow_right (by decide) hdu)
  have hA : 0 < A := by dsimp [A]; exact Nat.mul_pos (by omega) (by omega)
  have hWA : width A ≤ W := by
    apply (Nat.digits_length_le_iff (by decide : 1 < 10) A).mpr
    dsimp only [A, W]
    rw [pow_add, Nat.mul_comm (10^u)]
    exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans_lt (Nat.mul_lt_mul_of_pos_right hpow (by positivity))
  have hsplit : A = (10^u-n) + 10^u*(n-1) := by
    dsimp only [A]
    zify [show 1 ≤ n by omega, show 1 ≤ 10^u by omega, hnu.le]
    ring
  have hsub : width (10^u-n) ≤ u := (Nat.digits_length_le_iff (by decide : 1 < 10) _).mpr (by omega)
  have hsumA : ds A = 9*u := by
    rw [hsplit, (joined hsub (show 0 < n-1 by omega)).2]
    have hc := complement u (n-1) (by omega)
    rw [show 10^u-1-(n-1) = 10^u-n by omega] at hc
    omega
  let K := n/2+1
  let f : Bool × Fin K → ℕ := fun p =>
    if p.1 then glue n A n p.2.val else glue n n A p.2.val
  have spec (p : Bool × Fin K) : qualifies n (f p) ∧
      f p % 10^(n-W) = 10^p.2.val * (if p.1 then n else A) := by
    obtain ⟨b,i⟩ := p
    have hi : i.val+W ≤ n-W := by have := i.isLt; dsimp [K] at this; omega
    have hdn : width n ≤ W := by change d ≤ u+d; omega
    cases b
    · exact glueSpec (by omega) hA hdn hWA hi (by omega) (by omega) dvd_rfl (dvd_mul_right ..)
    · exact glueSpec hA (by omega) hWA hdn hi (by omega) (by omega) (dvd_mul_right ..) dvd_rfl
  have hpow3 (l : ℕ) : (10:ℕ)^l % 3 = 1 := by
    induction l with
    | zero => decide
    | succ l ih => rw [pow_succ, Nat.mul_mod, ih]
  have hdiff (i j : ℕ) : 10^i*A ≠ 10^j*n := by
    intro he
    have hc : 10^i*(10^u-1) = 10^j := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < n by omega)
      calc n * (10^i*(10^u-1)) = 10^i*A := by dsimp [A]; ring
           _ = 10^j*n := he
           _ = n*10^j := Nat.mul_comm ..
    have hh := congrArg (fun x : ℕ => x%3) hc
    have hzero : (10^u-1)%3 = 0 := by have := hpow3 u; omega
    simp [Nat.mul_mod, hpow3, hzero] at hh
  have same (z : ℕ) (hz : 0 < z) {i j : Fin K} (h : 10^i.val*z = 10^j.val*z) : i = j := by
    exact Fin.ext ((Nat.pow_right_inj (by decide : 1 < 10)).mp (Nat.eq_of_mul_eq_mul_right hz h))
  have hinj : Function.Injective f := by
    rintro ⟨b,i⟩ ⟨c,j⟩ he
    have hl := congrArg (fun x : ℕ => x % 10^(n-W)) he
    change f (b,i) % _ = f (c,j) % _ at hl
    rw [(spec (b,i)).2, (spec (c,j)).2] at hl
    cases b <;> cases c
    · exact congrArg (Prod.mk false) (same A hA hl)
    · exact (hdiff _ _ hl).elim
    · exact (hdiff _ _ hl.symm).elim
    · exact congrArg (Prod.mk true) (same n (by omega) hl)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp [K]
    omega
  · intro m hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    exact (spec i).1

-- Offsets from the first n-digit integer in the finitely many short rows.
private def offsets : ℕ → List ℕ
  | 1 => [0]
  | 3 => [2, 11, 20]
  | 4 => [12, 120, 300, 1020]
  | 5 => [40, 130, 220, 310, 400]
  | 6 => [14, 32, 50, 104, 122, 140]
  | 7 => [6, 132, 321, 510, 1014, 1140, 1203]
  | 8 => [16, 160, 232, 304, 520, 1024, 1240, 1312]
  | 9 => [8, 17, 26, 35, 44, 53, 62, 71, 80]
  | 10 => [90, 180, 270, 360, 450, 540, 630, 720, 810, 900]
  | 11 => [109, 208, 307, 406, 505, 604, 703, 802, 901, 10009, 10108]
  | 12 => [56, 92, 128, 164, 236, 272, 308, 344, 380, 416, 452, 524]
  | 13 => [129, 246, 363, 480, 714, 831, 1065, 1182, 1416, 1533, 1650, 2118, 2235]
  | 14 => [256, 382, 508, 634, 760, 1138, 1264, 1390, 1516, 1642, 2146, 2272, 2524, 2650]
  | 15 => [95, 185, 275, 365, 455, 545, 590, 635, 680, 725, 770, 815, 860, 905, 950]
  | 16 => [96, 384, 528, 672, 816, 960, 1248, 1392, 1536, 1680, 1824, 2256, 2544, 2832, 3264, 3408]
  | 17 => [169, 475, 628, 781, 934, 1087, 1393, 1546, 1852, 2158, 2464, 2617, 2770, 2923, 3076, 3229, 3382]
  | 18 => [98, 188, 278, 296, 368, 386, 458, 476, 494, 548, 566, 584, 638, 656, 674, 692, 728, 746]
  | 19 => [189, 873, 1386, 1557, 1728, 2583, 2754, 2925, 3096, 3267, 3438, 3609, 3780, 3951, 4293, 4464, 4635, 4806, 5148]
  | 20 => [2980, 3880, 4780, 4960, 5680, 5860, 6580, 6760, 6940, 7480, 7660, 7840, 8380, 8560, 8740, 8920, 9280, 9460, 9640, 9820]
  | 21 => [299, 488, 677, 866, 929, 992, 1496, 1559, 1685, 1748, 1874, 1937, 2189, 2378, 2567, 2693, 2756, 2819, 2882, 2945, 3197]
  | 22 => [1398, 1596, 1794, 1992, 2388, 2586, 2784, 2982, 3378, 3576, 3774, 3972, 4368, 4566, 4764, 4962, 5358, 5556, 5754, 5952, 6348, 6546]
  | 23 => [1678, 1885, 2299, 3748, 3955, 4369, 4576, 4783, 4990, 5197, 5818, 6439, 6646, 6853, 7267, 7474, 7681, 8095, 8509, 8716, 8923, 9337, 9544]
  | 24 => [896, 968, 1688, 1976, 2696, 2768, 2984, 3488, 3776, 3848, 3992, 4496, 4568, 4784, 4856, 4928, 5288, 5576, 5648, 5792, 5864, 5936, 6296, 6368]
  | 25 => [3975, 4875, 5775, 6675, 7575, 8475, 8925, 9375, 9825, 12975, 13875, 14775, 15675, 16575, 17475, 17925, 18375, 18825, 19275, 19725, 19950, 21975, 22875, 23775, 24675]
  | 26 => [1888, 3994, 4696, 5398, 5866, 6568, 7738, 7972, 8674, 8908, 9376, 9844, 12886, 13588, 14758, 14992, 15694, 15928, 16396, 16864, 17098, 17566, 18268, 18736, 18970, 19438]
  | 27 => [899, 1898, 1979, 2789, 2897, 2978, 3599, 3788, 3869, 3896, 3977, 4598, 4679, 4787, 4868, 4895, 4949, 4976, 5489, 5597, 5678, 5759, 5786, 5867, 5894, 5948, 5975]
  | 28 => [6588, 7596, 7848, 8856, 9864, 12888, 13896, 16668, 17676, 17928, 18684, 18936, 19188, 19692, 19944, 22968, 23976, 24984, 25488, 25992, 26496, 26748, 27756, 28764, 29268, 29772, 31788, 32796]
  | 29 => [2899, 4987, 7597, 7858, 9685, 9946, 15688, 15949, 16993, 17776, 18298, 18559, 19864, 22996, 23779, 25867, 26389, 27694, 27955, 28477, 28738, 29782, 33697, 33958, 35785, 36568, 36829, 37873, 38395]
  | 30 => [29990, 38990, 39890, 39980, 47990, 48890, 48980, 49790, 49880, 49970, 56990, 57890, 57980, 58790, 58880, 58970, 59690, 59780, 59870, 59960, 65990, 66890, 66980, 67790, 67880, 67970, 68690, 68780, 68870, 68960]
  | 31 => [5889, 8679, 8958, 9795, 17886, 19839, 25698, 25977, 28488, 28767, 29883, 30999, 33789, 36579, 36858, 37695, 37974, 39369, 39648, 39927, 42996, 44949, 45786, 47739, 48297, 48576, 48855, 49692, 49971, 53598, 53877]
  | 32 => [8896, 18688, 18976, 25888, 28768, 35968, 37696, 37984, 38848, 44896, 47488, 47776, 48928, 49792, 54688, 54976, 56992, 57568, 57856, 59296, 59584, 59872, 61888, 64768, 66496, 66784, 67648, 67936, 69088, 69376, 69664, 69952]
  | 33 => [32999, 33989, 34979, 35969, 36959, 37949, 38939, 39929, 42899, 42998, 43889, 43988, 44879, 44978, 45869, 45968, 46859, 46958, 47849, 47948, 48839, 48938, 49829, 49928, 52799, 52898, 52997, 53789, 53888, 53987, 54779, 54878, 54977]
  | 34 => [8898, 18996, 28788, 37968, 38886, 39498, 48678, 48984, 49596, 54798, 57858, 58776, 59388, 59694, 63978, 64896, 67956, 68568, 68874, 69486, 69792, 74688, 74994, 77748, 78666, 78972, 79278, 79584, 79890, 83868, 84786, 85398, 86928, 87846]
  | 35 => [47995, 49885, 59965, 66895, 68785, 76975, 78865, 79495, 85795, 87685, 88945, 89575, 89890, 93985, 95875, 97765, 98395, 99655, 99970, 129895, 139975, 148795, 156985, 158875, 167695, 168955, 169585, 173995, 175885, 177775, 179665, 179980, 185965, 186595, 187855]
  | _ => []

private def shortEntries (n : ℕ) : Finset ℕ :=
  ((offsets n).map (fun i => 10^(n-1) + i)).toFinset

private theorem shortRows (j : Fin 36) : 0 < j.val → j.val ≠ 2 →
    j.val ≤ (shortEntries j.val).card ∧ ∀ m ∈ shortEntries j.val, qualifies j.val m := by
  revert j
  unfold qualifies
  decide +kernel

private theorem second (m : ℕ) : qualifies 2 m ↔ m = 20 := by
  constructor
  · intro h
    have hm : m < 100 := (Nat.digits_length_le_iff (by decide : 1 < 10) m).mp h.1.le
    have check : ∀ j : Fin 100, qualifies 2 j.val → j.val = 20 := by unfold qualifies; decide +kernel
    exact check ⟨m,hm⟩ h
  · rintro rfl
    unfold qualifies
    decide +kernel

end OMA.S_oeis_a084029

open OMA.S_oeis_a084029 in
theorem OMA.solution : type_of% @OMA.S_oeis_a084029.main := by
  refine ⟨second, ?_⟩
  intro n hn h2
  by_cases h : 36 ≤ n
  · exact largeRow h
  · exact ⟨shortEntries n, shortRows ⟨n, by omega⟩ hn h2⟩
