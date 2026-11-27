import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1
import Mathlib.Tactic

/-!
For an odd exponent, columns 5 through 13 suffice outside four classes modulo 3240.
The parent reduction by Tchikrazi handles even exponents using the second column.

Write the falling factorial in base 2^a. Each digit consists of a constant bit
repeated a variable number of times followed by a fixed suffix. In division by
the odd part d of k!, appending l identical bits restores the remainder when
2^l ≡ 1 modulo d. Repeating that block twice also restores the parity of the
quotient's binary digit sum. The nine periods are 8, 24, 24, 24, 216, 1080,
1080, 3240 and 3240, each dividing the next.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

/-- Appending a padded binary word adds its number of one-bits. -/
lemma count_ones_append (x w c : ℕ) (hc : c < 2^w) :
    (Nat.digits 2 (x * 2^w + c)).count 1 =
      (Nat.digits 2 x).count 1 + (Nat.digits 2 c).count 1 := by
  let ones (n : ℕ) := (Nat.digits 2 n).count 1
  change ones (x * 2^w + c) = ones x + ones c
  have hlen : (Nat.digits 2 c).length ≤ w := (Nat.digits_length_le_iff (by decide : 1 < 2) _).mpr hc
  have h := Nat.digits_append_zeroes_append_digits (b := 2) (m := x) (n := c)
    (k := w - (Nat.digits 2 c).length) (by decide)
  by_cases hx : x = 0
  · simp [hx, ones]
  have e := h (Nat.pos_of_ne_zero hx)
  rw [show (Nat.digits 2 c).length + (w - (Nat.digits 2 c).length) = w by omega] at e
  unfold ones
  rw [show x * 2 ^ w + c = c + 2^w*x by ring, ← e]
  simp [List.count_replicate, Nat.add_comm]

set_option maxHeartbeats 2000000 in
lemma periodic_column {a k t d z l : ℕ} {ds : List (Bool × ℕ)}
    (ht : t ≤ a) (hd : 0 < d) (hm : 2^l%d=1%d) (hc : ∀ s ∈ ds, s.2 < 2^t)
    (hw : ∀ w : ℕ, ds.foldr (fun s v => (v * 2^w + (if s.1 then 2^w-1 else 0)) * 2^t + s.2) 0 =
      (2^(w+t)).descFactorial k) (hf : k.factorial = d * 2^z) :
    OeisA249609.isEvil ((2 ^ (a)).choose k) = true ↔
      (Nat.digits 2 ((2 ^ ((a-t)%(l+l)+t)).descFactorial k / d)).count 1 % 2 = 0 := by
  let ones (x : ℕ) : ℕ := (Nat.digits 2 x).count 1
  have ones_join (x w c : ℕ) (hc : c < 2^w) :
      ones (x * 2^w + c) = ones x + ones c := count_ones_append x w c hc

  let state (d x : ℕ) : ℕ × ℕ := (x%d, ones (x/d)%2)

  have state_join {d : ℕ} (hd : 0 < d) (x w c : ℕ) (hc : c < 2^w) :
      state d (x*2^w+c) =
        let v := x%d * 2^w+c
        (v%d, ((state d x).2 + ones (v/d))%2) := by
    have he : x*2^w+c = (x%d * 2^w+c) + (x/d * 2^w)*d := by
      calc
        x*2^w+c = (x%d+d*(x/d))*2^w+c := by rw [Nat.mod_add_div]
        _ = _ := by ring
    have hv : (x%d * 2^w+c)/d < 2^w := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      have h := Nat.mul_le_mul_right (2^w) (Nat.succ_le_of_lt (Nat.mod_lt x hd))
      rw [Nat.succ_mul] at h
      nlinarith only [h,hc]
    unfold state
    rw [he, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hd,
        Nat.add_comm ((x % d * 2 ^ w + c) / d), ones_join _ _ _ hv]
    simp [Nat.add_mod]

  have state_join_eq {d x y : ℕ} (hd : 0 < d) (he : state d x = state d y)
      (w c : ℕ) (hc : c < 2^w) : state d (x*2^w+c) = state d (y*2^w+c) := by
    have hr : x%d = y%d := congrArg Prod.fst he
    rw [state_join hd x w c hc, state_join hd y w c hc, he, hr]

  let fill (b : Bool) (w : ℕ) : ℕ := if b then 2^w-1 else 0

  have fill_lt (b : Bool) (w : ℕ) : fill b w < 2^w := by
    have : 0 < 2^w := by positivity
    cases b <;> simp [fill]

  have fill_add (b : Bool) (w u : ℕ) :
      fill b (w+u) = fill b w * 2^u + fill b u := by
    have hw : 0 < 2^w := by positivity
    have hu : 0 < 2^u := by positivity
    cases b
    · simp [fill]
    simp only [fill, if_true, pow_add]
    have e := Nat.sub_add_cancel (show 1 ≤ 2^w by omega)
    have e' := Nat.sub_add_cancel (show 1 ≤ 2^u by omega)
    have hh := congrArg (· * 2^u) e
    simp only [Nat.add_mul, Nat.one_mul] at hh
    omega

  have state_repeat {d l : ℕ} (hd : 0 < d) (hmod : 2^l % d = 1 % d)
      (x : ℕ) (b : Bool) : state d (x*2^(l+l) + fill b (l+l)) = state d x := by
    let c := fill b l
    have hc := fill_lt b l
    have hdiv : d ∣ 2^l-1 :=
      (Nat.modEq_iff_dvd' (show 1 ≤ 2^l by exact Nat.one_le_two_pow)).mp hmod.symm
    have hz : c%d = 0 := by cases b <;> simp [c, fill, Nat.mod_eq_zero_of_dvd hdiv]
    have hrem (y : ℕ) : (y*2^l+c)%d = y%d := by
      rw [Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod, Nat.mul_mod, hmod, ← Nat.mul_mod, Nat.mul_one]
    rw [fill_add, pow_add]
    change state d (x*(2^l*2^l)+(c*2^l+c)) = _
    rw [show x*(2^l*2^l)+(c*2^l+c) = (x*2^l+c)*2^l+c by ring]
    rw [state_join hd _ _ _ hc, hrem x, state_join hd _ _ _ hc]
    dsimp only
    rw [hrem (x%d), Nat.mod_mod]
    unfold state
    congr 1
    omega


  let word (w t : ℕ) (ds : List (Bool × ℕ)) : ℕ :=
    ds.foldr (fun s v => (v * 2^w + fill s.1 w) * 2^t + s.2) 0

  have word_period {d l : ℕ} (hd : 0 < d) (hm : 2^l%d=1%d) (w t : ℕ)
      (ds : List (Bool × ℕ)) (hc : ∀ s ∈ ds, s.2 < 2^t) :
      state d (word (w+(l+l)) t ds) = state d (word w t ds) := by
    induction ds with
    | nil => rfl
    | cons s ds ih =>
      obtain ⟨b,c⟩ := s
      have hsmall : c < 2 ^ t := hc (b,c) (by simp)
      have he := ih (fun s hs => hc s (by simp [hs]))
      change state d ((word (w+(l+l)) t ds * 2^(w+(l+l))+fill b (w+(l+l)))*2^t+c) =
        state d ((word w t ds*2^w+fill b w)*2^t+c)
      apply state_join_eq hd _ t c hsmall
      rw [fill_add b w (l+l), pow_add]
      rw [show word (w+(l+l)) t ds*(2^w*2^(l+l))+
            (fill b w*2^(l+l)+fill b (l+l)) =
          (word (w+(l+l)) t ds * 2^w+fill b w)*2^(l+l)+fill b (l+l) by ring]
      rw [state_repeat hd hm]
      exact state_join_eq hd he w _ (fill_lt b w)

  have word_mod {d l : ℕ} (hd : 0 < d) (hm : 2^l%d=1%d) (w t : ℕ)
      (ds : List (Bool × ℕ)) (hc : ∀ s ∈ ds, s.2 < 2^t) :
      state d (word w t ds) = state d (word (w%(l+l)) t ds) := by
    have per (x q : ℕ) : state d (word (x+(l+l)*q) t ds) = state d (word x t ds) := by
      induction q with
      | zero => simp
      | succ q ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, word_period hd hm, ih]
        exact hc
    conv_lhs => rw [← Nat.mod_add_div w (l+l)]
    exact per _ _



  have ones_scaled (v n : ℕ) : ones (2^v * n) = ones n := by
    simpa only [Nat.mul_comm n, Nat.add_zero, show ones 0 = 0 by rfl] using
      ones_join n v 0 (by positivity)

  have column {a k t d z l : ℕ} {ds : List (Bool × ℕ)} (ht : t ≤ a)
      (hd : 0 < d) (hm : 2^l%d=1%d) (hc : ∀ s ∈ ds, s.2 < 2^t)
      (hword : ∀ w, word w t ds = (2^(w+t)).descFactorial k)
      (hfac : k.factorial = d * 2^z) :
      OeisA249609.isEvil ((2^a).choose k) = true ↔
        (state d (word ((a-t)%(l+l)) t ds)).2 = 0 := by
    rw [← word_mod hd hm (a-t) t ds hc, hword, Nat.sub_add_cancel ht,
        Nat.descFactorial_eq_factorial_mul_choose, hfac, Nat.mul_assoc]
    change (ones ((2^a).choose k) % 2 == 0) = true ↔
      ones (d * (2^z * (2^a).choose k) / d) % 2 = 0
    rw [Nat.mul_div_cancel_left _ hd, ones_scaled, beq_iff_eq]
  have he := column ht hd hm hc hw hf
  change _ ↔ ones ((2^((a-t)%(l+l)+t)).descFactorial k /d)%2 = 0
  rw [← hw]
  exact he

set_option maxHeartbeats 2000000 in
/-- Split the quotient into bytes to keep the depth of digit-count certificates small. -/
lemma chunk_certificate (n : ℕ) (h :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1)
      (fun i f v => if v < 256 then (Nat.digits 2 v).count 1 else
        f (v / 2^(8*2^i)) + f (v % 2^(8*2^i))) 13 n) % 2 = 0) :
    (Nat.digits 2 n).count 1 % 2 = 0 := by
  let ones (x : ℕ) : ℕ := (Nat.digits 2 x).count 1
  have ones_join (x w c : ℕ) (hc : c < 2^w) :
      ones (x * 2^w + c) = ones x + ones c := count_ones_append x w c hc
  let count := Nat.rec (motive := fun _ => ℕ → ℕ) ones
    (fun i f v => if v < 256 then ones v else
      f (v / 2^(8*2^i)) + f (v % 2^(8*2^i)))
  have spec (i v : ℕ) : count i v = ones v := by
    induction i generalizing v with
    | zero => rfl
    | succ i ih =>
      change (if v < 256 then ones v else
        count i (v / 2^(8*2^i)) + count i (v % 2^(8*2^i))) = ones v
      split_ifs
      · rfl
      rw [ih, ih, ← ones_join _ _ _ (Nat.mod_lt _ (by positivity)), Nat.div_add_mod']
  change count 13 n % 2 = 0 at h
  rw [spec] at h
  exact h

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma falling5 (x B : ℕ) (hx : 0 < x) (hB : B = 64) :
    ([(false, 0), (false, 24), (true, 14), (false, 34),
     (true, 54), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 5 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = low (low (high (low (high (low 0 0) 54) 34) 14) 24) 0 := by rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma col5 (a : ℕ) (ha : 31 ≤ a) (hr : a % 8 ∈ ([5, 7] : List ℕ)) :
    OeisA249609.isEvil ((2 ^ (a)).choose 5) = true := by
  let ds : List (Bool × ℕ) :=
    [(false, 0), (false, 24), (true, 14), (false, 34),
     (true, 54), (false, 0)]
  refine (periodic_column (k := 5) (t := 6) (l := 4) (d := 15) (z := 3)
      (ds := ds) (by omega) (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]
    decide
  · intro w
    rw [pow_add 2 w 6]
    exact falling5 (2^w) (2^6) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr
  · rw [show (a - 6) % (4 + 4) + 6 = 13 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 6) % (4 + 4) + 6 = 7 by omega]
    apply chunk_certificate
    decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma falling6 (x B : ℕ) (hx : 0 < x) (hB : B = 512) :
    ([(false, 0), (true, 392), (false, 273), (true, 287),
     (false, 84), (true, 497), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 6 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = low (high (low (high (low (high (low 0 0) 497) 84) 287) 273) 392) 0 := by rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma col6 (a : ℕ) (ha : 31 ≤ a) (hr : a % 24 ∈ ([1, 3, 19] : List ℕ)) :
    OeisA249609.isEvil ((2 ^ (a)).choose 6) = true := by
  let ds : List (Bool × ℕ) :=
    [(false, 0), (true, 392), (false, 273), (true, 287),
     (false, 84), (true, 497), (false, 0)]
  refine (periodic_column (k := 6) (t := 9) (l := 12) (d := 45) (z := 4)
      (ds := ds) (by omega) (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]
    decide
  · intro w
    rw [pow_add 2 w 9]
    exact falling6 (2^w) (2^9) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr
  · rw [show (a - 9) % (12 + 12) + 9 = 25 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 9) % (12 + 12) + 9 = 27 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 9) % (12 + 12) + 9 = 19 by omega]
    apply chunk_certificate
    decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma falling7 (x B : ℕ) (hx : 0 < x) (hB : B = 2048) :
    ([(false, 0), (false, 720), (true, 284), (false, 1623),
     (true, 1313), (false, 174), (true, 2027), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 7 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = low (low (high (low (high (low (high (low 0 0) 2027) 174) 1313) 1623) 284) 720) 0 := by rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma col7 (a : ℕ) (ha : 31 ≤ a) (hr : a % 24 ∈ ([9] : List ℕ)) :
    OeisA249609.isEvil ((2 ^ (a)).choose 7) = true := by
  let ds : List (Bool × ℕ) :=
    [(false, 0), (false, 720), (true, 284), (false, 1623),
     (true, 1313), (false, 174), (true, 2027), (false, 0)]
  refine (periodic_column (k := 7) (t := 11) (l := 12) (d := 315) (z := 4)
      (ds := ds) (by omega) (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]
    decide
  · intro w
    rw [pow_add 2 w 11]
    exact falling7 (2^w) (2^11) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [show (a - 11) % (12 + 12) + 11 = 33 by omega]
  apply chunk_certificate
  decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma falling8 (x B : ℕ) (hx : 0 < x) (hB : B = 16384) :
    ([(false, 0), (true, 11344), (false, 13067), (true, 3252),
     (false, 6768), (true, 14424), (false, 321), (true, 16356),
     (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 8 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = low (high (low (high (low (high (low (high (low 0 0) 16356) 321) 14424) 6768) 3252) 13067) 11344) 0 := by rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma col8 (a : ℕ) (ha : 31 ≤ a) (hr : a % 24 ∈ ([11] : List ℕ)) :
    OeisA249609.isEvil ((2 ^ (a)).choose 8) = true := by
  let ds : List (Bool × ℕ) :=
    [(false, 0), (true, 11344), (false, 13067), (true, 3252),
     (false, 6768), (true, 14424), (false, 321), (true, 16356),
     (false, 0)]
  refine (periodic_column (k := 8) (t := 14) (l := 12) (d := 315) (z := 7)
      (ds := ds) (by omega) (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]
    decide
  · intro w
    rw [pow_add 2 w 14]
    exact falling8 (2^w) (2^14) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [show (a - 14) % (12 + 12) + 14 = 35 by omega]
  apply chunk_certificate
  decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma falling9 (x B : ℕ) (hx : 0 < x) (hB : B = 131072) :
    ([(false, 0), (false, 40320), (true, 21488), (false, 118123),
     (true, 63788), (false, 22448), (true, 126536), (false, 545),
     (true, 131036), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 9 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = low (low (high (low (high (low (high (low (high (low 0 0) 131036) 545) 126536) 22448) 63788) 118123) 21488) 40320) 0 := by rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma col9 (a : ℕ) (ha : 31 ≤ a) (hr : a % 216 ∈ ([17, 41, 65, 161, 185] : List ℕ)) :
    OeisA249609.isEvil ((2 ^ (a)).choose 9) = true := by
  let ds : List (Bool × ℕ) :=
    [(false, 0), (false, 40320), (true, 21488), (false, 118123),
     (true, 63788), (false, 22448), (true, 126536), (false, 545),
     (true, 131036), (false, 0)]
  refine (periodic_column (k := 9) (t := 17) (l := 108) (d := 2835) (z := 7)
      (ds := ds) (by omega) (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]
    decide
  · intro w
    rw [pow_add 2 w 17]
    exact falling9 (2^w) (2^17) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr
  · rw [show (a - 17) % (108 + 108) + 17 = 17 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 17) % (108 + 108) + 17 = 41 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 17) % (108 + 108) + 17 = 65 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 17) % (108 + 108) + 17 = 161 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 17) % (108 + 108) + 17 = 185 by omega]
    apply chunk_certificate
    decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma falling10 (x B : ℕ) (hx : 0 < x) (hB : B = 2097152) :
    ([(false, 0), (true, 1734272), (false, 1026575), (true, 924452),
     (false, 723679), (true, 1827827), (false, 63272), (true, 2087702),
     (false, 869), (true, 2097107), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 10 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = low (high (low (high (low (high (low (high (low (high (low 0 0) 2097107) 869) 2087702) 63272) 1827827) 723679) 924452) 1026575) 1734272) 0 := by rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma col10 (a : ℕ) (ha : 31 ≤ a) (hr : a % 1080 ∈ ([137, 329, 353, 425, 521, 569, 785, 857, 953, 977, 1073] : List ℕ)) :
    OeisA249609.isEvil ((2 ^ (a)).choose 10) = true := by
  let ds : List (Bool × ℕ) :=
    [(false, 0), (true, 1734272), (false, 1026575), (true, 924452),
     (false, 723679), (true, 1827827), (false, 63272), (true, 2087702),
     (false, 869), (true, 2097107), (false, 0)]
  refine (periodic_column (k := 10) (t := 21) (l := 540) (d := 14175) (z := 8)
      (ds := ds) (by omega) (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]
    decide
  · intro w
    rw [pow_add 2 w 21]
    exact falling10 (2^w) (2^21) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a - 21) % (540 + 540) + 21 = 137 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 329 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 353 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 425 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 521 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 569 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 785 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 857 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 953 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 977 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 21) % (540 + 540) + 21 = 1073 by omega]
    apply chunk_certificate
    decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma falling11 (x B : ℕ) (hx : 0 < x) (hB : B = 16777216) :
    ([(false, 0), (false, 3628800), (true, 6148576), (false, 12753575),
     (true, 8367716), (false, 3416929), (true, 15875161), (false, 157772),
     (true, 16759066), (false, 1319), (true, 16777161), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 11 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = low (low (high (low (high (low (high (low (high (low (high (low 0 0) 16777161) 1319) 16759066) 157772) 15875161) 3416929) 8367716) 12753575) 6148576) 3628800) 0 := by rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma col11 (a : ℕ) (ha : 31 ≤ a) (hr : a % 1080 ∈ ([89, 113, 737, 1001] : List ℕ)) :
    OeisA249609.isEvil ((2 ^ (a)).choose 11) = true := by
  let ds : List (Bool × ℕ) :=
    [(false, 0), (false, 3628800), (true, 6148576), (false, 12753575),
     (true, 8367716), (false, 3416929), (true, 15875161), (false, 157772),
     (true, 16759066), (false, 1319), (true, 16777161), (false, 0)]
  refine (periodic_column (k := 11) (t := 24) (l := 540) (d := 155925) (z := 8)
      (ds := ds) (by omega) (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]
    decide
  · intro w
    rw [pow_add 2 w 24]
    exact falling11 (2^w) (2^24) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr
  · rw [show (a - 24) % (540 + 540) + 24 = 89 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 24) % (540 + 540) + 24 = 113 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 24) % (540 + 540) + 24 = 737 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 24) % (540 + 540) + 24 = 1001 by omega]
    apply chunk_certificate
    decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma falling12 (x B : ℕ) (hx : 0 < x) (hB : B = 268435456) :
    ([(false, 0), (true, 228518656), (false, 120543839), (true, 117517480),
     (false, 105258075), (true, 222439726), (false, 13339534), (true, 265797898),
     (false, 357422), (true, 268402786), (false, 1924), (true, 268435390),
     (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 12 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 268435390) 1924) 268402786) 357422) 265797898) 13339534) 222439726) 105258075) 117517480) 120543839) 228518656) 0 := by rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma col12 (a : ℕ) (ha : 31 ≤ a) (hr : a % 3240 ∈ ([641, 1625, 1721, 2465, 2921] : List ℕ)) :
    OeisA249609.isEvil ((2 ^ (a)).choose 12) = true := by
  let ds : List (Bool × ℕ) :=
    [(false, 0), (true, 228518656), (false, 120543839), (true, 117517480),
     (false, 105258075), (true, 222439726), (false, 13339534), (true, 265797898),
     (false, 357422), (true, 268402786), (false, 1924), (true, 268435390),
     (false, 0)]
  refine (periodic_column (k := 12) (t := 28) (l := 1620) (d := 467775) (z := 10)
      (ds := ds) (by omega) (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]
    decide
  · intro w
    rw [pow_add 2 w 28]
    exact falling12 (2^w) (2^28) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr
  · rw [show (a - 28) % (1620 + 1620) + 28 = 641 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 28) % (1620 + 1620) + 28 = 1625 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 28) % (1620 + 1620) + 28 = 1721 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 28) % (1620 + 1620) + 28 = 2465 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 28) % (1620 + 1620) + 28 = 2921 by omega]
    apply chunk_certificate
    decide +kernel

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
lemma falling13 (x B : ℕ) (hx : 0 < x) (hB : B = 2147483648) :
    ([(false, 0), (false, 479001600), (true, 661040768), (false, 1931559551),
     (true, 733468760), (false, 657206835), (true, 1941413498), (false, 44990230),
     (true, 2140557014), (false, 749462), (true, 2147427878), (false, 2716),
     (true, 2147483570), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 13 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = low (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 2147483570) 2716) 2147427878) 749462) 2140557014) 44990230) 1941413498) 657206835) 733468760) 1931559551) 661040768) 479001600) 0 := by rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma col13 (a : ℕ) (ha : 31 ≤ a) (hr : a % 3240 ∈ ([305, 761, 1289, 1385, 1841, 2369] : List ℕ)) :
    OeisA249609.isEvil ((2 ^ (a)).choose 13) = true := by
  let ds : List (Bool × ℕ) :=
    [(false, 0), (false, 479001600), (true, 661040768), (false, 1931559551),
     (true, 733468760), (false, 657206835), (true, 1941413498), (false, 44990230),
     (true, 2140557014), (false, 749462), (true, 2147427878), (false, 2716),
     (true, 2147483570), (false, 0)]
  refine (periodic_column (k := 13) (t := 31) (l := 1620) (d := 6081075) (z := 10)
      (ds := ds) (by omega) (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]
    decide
  · intro w
    rw [pow_add 2 w 31]
    exact falling13 (2^w) (2^31) (by positivity) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr
  · rw [show (a - 31) % (1620 + 1620) + 31 = 305 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 31) % (1620 + 1620) + 31 = 761 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 31) % (1620 + 1620) + 31 = 1289 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 31) % (1620 + 1620) + 31 = 1385 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 31) % (1620 + 1620) + 31 = 1841 by omega]
    apply chunk_certificate
    decide +kernel
  · rw [show (a - 31) % (1620 + 1620) + 31 = 2369 by omega]
    apply chunk_certificate
    decide +kernel

lemma witness (a k : ℕ) (hk : 1 ≤ k) (hb : k ≤ 2^a)
    (he : OeisA249609.isEvil ((2^a).choose k) = true) :
    ∃ j ∈ List.range' 1 (2 ^ a), OeisA249609.isEvil ((2^a).choose j) = true := by
  refine ⟨k, List.mem_range'.2 ⟨k-1, by omega, ?_⟩, he⟩
  simp
  omega

lemma small_rows (a : ℕ) (h5 : 5 ≤ a) (hb : a < 31) (ho : Odd a) :
    ∃ j ∈ List.range' 1 (2 ^ a), OeisA249609.isEvil ((2^a).choose j) = true := by
  have choose_eq (n k : ℕ) : n.choose k = n.descFactorial k / k.factorial := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]
  obtain ⟨s, hs⟩ := ho
  have cases : a = 5 ∨ a = 7 ∨ a = 9 ∨ a = 11 ∨ a = 13 ∨ a = 15 ∨ a = 17 ∨ a = 19 ∨ a = 21 ∨ a = 23 ∨ a = 25 ∨ a = 27 ∨ a = 29 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply witness 5 5 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 7 5 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 9 7 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 11 8 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 13 5 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 15 5 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 17 9 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 19 6 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 21 5 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 23 5 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 25 6 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 27 6 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel
  · apply witness 29 5 (by decide) (by decide)
    rw [choose_eq]
    decide +kernel

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 20000 in
lemma residues (r : Fin 3240) (ho : r.val % 2 = 1) (hr : r.val ∉ ([209, 545, 2705, 2801] : List ℕ)) :
    r.val % 8 ∈ ([5, 7] : List ℕ) ∨
    r.val % 24 ∈ ([1, 3, 19] : List ℕ) ∨
    r.val % 24 ∈ ([9] : List ℕ) ∨
    r.val % 24 ∈ ([11] : List ℕ) ∨
    r.val % 216 ∈ ([17, 41, 65, 161, 185] : List ℕ) ∨
    r.val % 1080 ∈ ([137, 329, 353, 425, 521, 569, 785, 857, 953, 977, 1073] : List ℕ) ∨
    r.val % 1080 ∈ ([89, 113, 737, 1001] : List ℕ) ∨
    r.val % 3240 ∈ ([641, 1625, 1721, 2465, 2921] : List ℕ) ∨
    r.val % 3240 ∈ ([305, 761, 1289, 1385, 1841, 2369] : List ℕ) := by
  revert r
  decide +kernel

def H1 : Prop :=
  ∀ q : ℕ, ∃ k ∈ List.range' 1 (2 ^ (3240 * q + 209)),
    OeisA249609.isEvil ((2 ^ (3240 * q + 209)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, ∃ k ∈ List.range' 1 (2 ^ (3240 * q + 545)),
    OeisA249609.isEvil ((2 ^ (3240 * q + 545)).choose k) = true

def H3 : Prop :=
  ∀ q : ℕ, ∃ k ∈ List.range' 1 (2 ^ (3240 * q + 2705)),
    OeisA249609.isEvil ((2 ^ (3240 * q + 2705)).choose k) = true

def H4 : Prop :=
  ∀ q : ℕ, ∃ k ∈ List.range' 1 (2 ^ (3240 * q + 2801)),
    OeisA249609.isEvil ((2 ^ (3240 * q + 2801)).choose k) = true

theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1.H1 := by
  intro h1 h2 h3 h4 a hpos ho hne1 hne3
  have hp := ho
  obtain ⟨s, hs⟩ := hp
  have ha : 5 ≤ a := by omega
  by_cases hb : a < 31
  · exact small_rows a ha hb ho
  have hlarge : 31 ≤ a := by omega
  have hk : 13 ≤ 2^a := le_trans (by decide : 13 ≤ 2^5) (Nat.pow_le_pow_right (by decide) ha)
  by_cases hr : a % 3240 ∈ ([209, 545, 2705, 2801] : List ℕ)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr | hr | hr
    · have e : a = 3240 * (a / 3240) + 209 := by omega
      exact e.symm ▸ h1 (a / 3240)
    · have e : a = 3240 * (a / 3240) + 545 := by omega
      exact e.symm ▸ h2 (a / 3240)
    · have e : a = 3240 * (a / 3240) + 2705 := by omega
      exact e.symm ▸ h3 (a / 3240)
    · have e : a = 3240 * (a / 3240) + 2801 := by omega
      exact e.symm ▸ h4 (a / 3240)
  have cover := residues ⟨a%3240, Nat.mod_lt _ (by decide)⟩ (by change a%3240%2=1; omega) hr
  dsimp only at cover
  simp only [Nat.mod_mod_of_dvd a (by decide : 8 ∣ 3240), Nat.mod_mod_of_dvd a (by decide : 24 ∣ 3240), Nat.mod_mod_of_dvd a (by decide : 216 ∣ 3240), Nat.mod_mod_of_dvd a (by decide : 1080 ∣ 3240), Nat.mod_mod_of_dvd a (by decide : 3240 ∣ 3240)] at cover
  rcases cover with h | h | h | h | h | h | h | h | h
  · exact witness a 5 (by decide) (by omega) (col5 a hlarge h)
  · exact witness a 6 (by decide) (by omega) (col6 a hlarge h)
  · exact witness a 7 (by decide) (by omega) (col7 a hlarge h)
  · exact witness a 8 (by decide) (by omega) (col8 a hlarge h)
  · exact witness a 9 (by decide) (by omega) (col9 a hlarge h)
  · exact witness a 10 (by decide) (by omega) (col10 a hlarge h)
  · exact witness a 11 (by decide) (by omega) (col11 a hlarge h)
  · exact witness a 12 (by decide) (by omega) (col12 a hlarge h)
  · exact witness a 13 (by decide) (by omega) (col13 a hlarge h)

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1
