import FormalConjectures.OEIS.«261876»

/-!
# Disproof of `OeisA261876.conjecture_3`

We refute `OeisA261876.conjecture_3` using the explicit witness triple `t = (42, 98, 14) ∈ triples`
and `n = 56271`: there do not exist `x, y, z, w : ℕ` with `56271 = x^2 + y^2 + z^2 + w^2` such that
`x * y * (42 * x^2 + 98 * y^2 + 14 * z^2)` is a square.

Because `56271 ≡ 7 (mod 8)`, any 4-square representation has exactly one coordinate `e ≡ 2 (mod 4)`
and three odd coordinates `1 ≤ u ≤ v ≤ s ≤ 237`. All such quadruples are exhaustively enumerated
via a tight two-pointer `(v, s)` scan for each `(e, u)` and verified inside the Lean 4 kernel by
pure `rfl` across 35 load-balanced parallel theorems covering `e = 4 * t + 2` (`0 ≤ t ≤ 58`), with
zero `native_decide`.
-/

namespace OeisA261876Disproof

/- ### Section 1: Fast exact non-square check and two-pointer four-square scanner -/

def Q (x y z : Nat) : Nat :=
  x * y * (42 * x * x + 98 * y * y + 14 * z * z)

def isqrtBin (v : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    let mid := (lo + hi) / 2
    if mid * mid ≤ v then isqrtBin v fuel mid hi
    else isqrtBin v fuel lo mid

def notSq (v : Nat) : Bool :=
  if v % 7 == 0 && v % 49 != 0 then true
  else
    let m16 := v % 16
    if m16 != 0 && m16 != 1 && m16 != 4 && m16 != 9 then true
    else
      let m9 := v % 9
      if m9 == 2 || m9 == 3 || m9 == 5 || m9 == 6 || m9 == 8 then true
      else
        let m5 := v % 5
        if m5 == 2 || m5 == 3 then true
        else
          let r := isqrtBin v 20 0 1048576
          r * r < v && v < (r + 1) * (r + 1)

def check6 (a b c : Nat) : Bool :=
  notSq (Q a b c) && notSq (Q a c b) &&
  notSq (Q b a c) && notSq (Q b c a) &&
  notSq (Q c a b) && notSq (Q c b a)

def check24 (a b c d : Nat) : Bool :=
  check6 a b c && check6 a b d && check6 a c d && check6 b c d

def sStart (rem : Nat) : Nat :=
  let r := isqrtBin rem 8 0 256
  if r % 2 == 1 then r else r + 1

def checkVS (e u rem : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, v, s =>
    if v > s then true
    else
      let sum := v * v + s * s
      if sum < rem then checkVS e u rem fuel (v + 2) s
      else if sum > rem then
        if s < 2 then true else checkVS e u rem fuel v (s - 2)
      else
        check24 e u v s &&
          (if s < 2 then true else checkVS e u rem fuel (v + 2) (s - 2))

def checkU (e remE : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, u =>
    if 3 * u * u > remE then true
    else
      let rem := remE - u * u
      let s0 := sStart rem
      (s0 * s0 + 2 * s0 + 1 > rem) &&
        checkVS e u rem 130 u s0 && checkU e remE fuel (u + 2)

def checkE (e : Nat) : Bool :=
  if e * e > 56271 then true
  else checkU e (56271 - e * e) 75 1

def checkERange : Nat → Nat → Bool
  | 0, _ => true
  | cnt + 1, t => checkE (4 * t + 2) && checkERange cnt (t + 1)

/- ### Section 2: 35 load-balanced parallel pure-rfl theorems covering all 0 ≤ t ≤ 58 -/

set_option maxRecDepth 4096 in
private theorem checkE_t_0 : checkE 2 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_1 : checkE 6 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_2 : checkE 10 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_3 : checkE 14 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_4 : checkE 18 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_5 : checkE 22 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_6 : checkE 26 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_7 : checkE 30 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_8 : checkE 34 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_9 : checkE 38 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_10 : checkE 42 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_11 : checkE 46 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_12 : checkE 50 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_13 : checkE 54 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_14 : checkE 58 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_15 : checkE 62 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_16 : checkE 66 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_17 : checkE 70 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_18 : checkE 74 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_t_19 : checkE 78 = true := rfl

set_option maxRecDepth 4096 in
private theorem checkE_blk_20 : checkERange 2 20 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_22 : checkERange 2 22 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_24 : checkERange 2 24 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_26 : checkERange 2 26 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_28 : checkERange 2 28 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_30 : checkERange 2 30 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_32 : checkERange 2 32 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_34 : checkERange 2 34 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_36 : checkERange 2 36 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_38 : checkERange 2 38 = true := rfl

set_option maxRecDepth 4096 in
private theorem checkE_blk_40 : checkERange 4 40 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_44 : checkERange 4 44 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_48 : checkERange 4 48 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_52 : checkERange 4 52 = true := rfl
set_option maxRecDepth 4096 in
private theorem checkE_blk_56 : checkERange 3 56 = true := rfl

/- ### Section 3: Soundness proofs -/

private def NoSq3 (x y z : Nat) : Prop := ¬ IsSquare (Q x y z)

private def NoSq6 (a b c : Nat) : Prop :=
  NoSq3 a b c ∧ NoSq3 a c b ∧ NoSq3 b a c ∧ NoSq3 b c a ∧ NoSq3 c a b ∧ NoSq3 c b a

private def NoSq24 (a b c d : Nat) : Prop :=
  NoSq6 a b c ∧ NoSq6 a b d ∧ NoSq6 a c d ∧ NoSq6 b c d

private lemma NoSq6_swap12 {a b c : Nat} (h : NoSq6 a b c) : NoSq6 b a c :=
  ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

private lemma NoSq6_swap23 {a b c : Nat} (h : NoSq6 a b c) : NoSq6 a c b :=
  ⟨h.2.1, h.1, h.2.2.2.2.1, h.2.2.2.2.2, h.2.2.1, h.2.2.2.1⟩

private lemma NoSq24_swap12 {a b c d : Nat} (h : NoSq24 a b c d) : NoSq24 b a c d :=
  ⟨NoSq6_swap12 h.1, NoSq6_swap12 h.2.1, h.2.2.2, h.2.2.1⟩

private lemma NoSq24_swap23 {a b c d : Nat} (h : NoSq24 a b c d) : NoSq24 a c b d :=
  ⟨NoSq6_swap23 h.1, h.2.2.1, h.2.1, NoSq6_swap12 h.2.2.2⟩

private lemma NoSq24_swap34 {a b c d : Nat} (h : NoSq24 a b c d) : NoSq24 a b d c :=
  ⟨h.2.1, h.1, NoSq6_swap23 h.2.2.1, NoSq6_swap23 h.2.2.2⟩

private lemma notSq_sound (v : Nat) (h : notSq v = true) : ¬ IsSquare v := by
  rintro ⟨r, rfl⟩
  dsimp only [notSq] at h
  have hf49 : ((r * r % 7 == 0) && (r * r % 49 != 0)) = false := by
    by_cases h7 : r * r % 7 = 0
    · have h7dvd : 7 ∣ r * r := Nat.dvd_of_mod_eq_zero h7
      have hr7 : 7 ∣ r := by
        rcases (by decide : Nat.Prime 7).dvd_mul.mp h7dvd with h1 | h1 <;> exact h1
      rcases hr7 with ⟨k, rfl⟩
      have h49 : (7 * k * (7 * k)) % 49 = 0 := by
        have : 7 * k * (7 * k) = 49 * (k * k) := by ring
        rw [this, Nat.mul_mod_right]
      simp [h49]
    · simp [h7]
  have hsq16 : (r * r) % 16 = 0 ∨ (r * r) % 16 = 1 ∨ (r * r) % 16 = 4 ∨ (r * r) % 16 = 9 := by
    have hm : (r * r) % 16 = (r % 16) * (r % 16) % 16 := Nat.mul_mod r r 16
    have hlt : r % 16 < 16 := Nat.mod_lt r (by omega)
    rw [hm]
    interval_cases (r % 16) <;> decide
  have hsq9 : (r * r) % 9 = 0 ∨ (r * r) % 9 = 1 ∨ (r * r) % 9 = 4 ∨ (r * r) % 9 = 7 := by
    have hm : (r * r) % 9 = (r % 9) * (r % 9) % 9 := Nat.mul_mod r r 9
    have hlt : r % 9 < 9 := Nat.mod_lt r (by omega)
    rw [hm]
    interval_cases (r % 9) <;> decide
  have hsq5 : (r * r) % 5 = 0 ∨ (r * r) % 5 = 1 ∨ (r * r) % 5 = 4 := by
    have hm : (r * r) % 5 = (r % 5) * (r % 5) % 5 := Nat.mul_mod r r 5
    have hlt : r % 5 < 5 := Nat.mod_lt r (by omega)
    rw [hm]
    interval_cases (r % 5) <;> decide
  have hf16 : ((r * r % 16 != 0) && (r * r % 16 != 1) && (r * r % 16 != 4) &&
      (r * r % 16 != 9)) = false := by
    rcases hsq16 with h16 | h16 | h16 | h16 <;> simp [h16]
  have hf9 : ((r * r % 9 == 2) || (r * r % 9 == 3) || (r * r % 9 == 5) ||
      (r * r % 9 == 6) || (r * r % 9 == 8)) = false := by
    rcases hsq9 with h9 | h9 | h9 | h9 <;> simp [h9]
  have hf5 : ((r * r % 5 == 2) || (r * r % 5 == 3)) = false := by
    rcases hsq5 with h5 | h5 | h5 <;> simp [h5]
  simp only [hf49, hf16, hf9, hf5, Bool.false_eq_true, ↓reduceIte,
    Bool.and_eq_true, decide_eq_true_eq] at h
  set s := isqrtBin (r * r) 20 0 1048576
  by_cases hrs : r ≤ s
  · nlinarith
  · nlinarith

private lemma check6_sound (a b c : Nat) (h : check6 a b c = true) : NoSq6 a b c := by
  unfold check6 at h
  simp only [Bool.and_eq_true] at h
  exact ⟨notSq_sound _ h.1.1.1.1.1, notSq_sound _ h.1.1.1.1.2,
    notSq_sound _ h.1.1.1.2, notSq_sound _ h.1.1.2,
    notSq_sound _ h.1.2, notSq_sound _ h.2⟩

private lemma check24_sound (a b c d : Nat) (h : check24 a b c d = true) : NoSq24 a b c d := by
  unfold check24 at h
  simp only [Bool.and_eq_true] at h
  exact ⟨check6_sound _ _ _ h.1.1.1, check6_sound _ _ _ h.1.1.2,
    check6_sound _ _ _ h.1.2, check6_sound _ _ _ h.2⟩

private lemma sStart_odd (rem : Nat) : sStart rem % 2 = 1 := by
  dsimp only [sStart]
  split_ifs with h
  · exact beq_iff_eq.mp h
  · have : isqrtBin rem 8 0 256 % 2 ≠ 1 := fun heq => h (beq_iff_eq.mpr heq)
    omega

private lemma checkVS_sound (e u rem : Nat) :
    ∀ fuel v s,
      checkVS e u rem fuel v s = true →
      v % 2 = 1 → s % 2 = 1 →
      ∀ v' s', v' % 2 = 1 → s' % 2 = 1 →
        v ≤ v' → v' ≤ s' → s' ≤ s →
        v' * v' + s' * s' = rem →
        NoSq24 e u v' s'
  | 0, _, _, h, _, _, _, _, _, _, _, _, _, _ => by simp [checkVS] at h
  | fuel + 1, v, s, h, hv_odd, hs_odd, v', s', hv'_odd, hs'_odd, hvv', hv's', hs's, hsum => by
    unfold checkVS at h
    by_cases hgt : v > s
    · omega
    · rw [if_neg hgt] at h
      by_cases hlt : v * v + s * s < rem
      · rw [if_pos hlt] at h
        have hv_lt : v < v' := by
          by_contra hge
          have hveq : v' = v := by omega
          subst hveq
          nlinarith
        exact checkVS_sound e u rem fuel (v + 2) s h (by omega) hs_odd
          v' s' hv'_odd hs'_odd (by omega) hv's' hs's hsum
      · rw [if_neg hlt] at h
        by_cases hbig : v * v + s * s > rem
        · rw [if_pos hbig] at h
          have hs_gt : s' < s := by
            by_contra hle
            have hseq : s' = s := by omega
            subst hseq
            nlinarith
          have hs2 : ¬ (s < 2) := by omega
          rw [if_neg hs2] at h
          exact checkVS_sound e u rem fuel v (s - 2) h hv_odd (by omega)
            v' s' hv'_odd hs'_odd hvv' hv's' (by omega) hsum
        · rw [if_neg hbig] at h
          simp only [Bool.and_eq_true] at h
          rcases h with ⟨h24, hrest⟩
          have heq_rem : v * v + s * s = rem := by omega
          by_cases hv_eq : v' = v
          · subst hv_eq
            have hs_eq : s' = s := by nlinarith
            subst hs_eq
            exact check24_sound e u v' s' h24
          · by_cases hs_eq : s' = s
            · subst hs_eq
              have hv_eq2 : v' = v := by nlinarith
              subst hv_eq2
              exact check24_sound e u v' s' h24
            · have hs2 : ¬ (s < 2) := by omega
              rw [if_neg hs2] at hrest
              exact checkVS_sound e u rem fuel (v + 2) (s - 2) hrest (by omega) (by omega)
                v' s' hv'_odd hs'_odd (by omega) hv's' (by omega) hsum

private lemma checkU_sound (e remE : Nat) :
    ∀ fuel u,
      checkU e remE fuel u = true →
      u % 2 = 1 →
      ∀ u' v' s', u' % 2 = 1 → v' % 2 = 1 → s' % 2 = 1 →
        u ≤ u' → u' ≤ v' → v' ≤ s' →
        u' * u' + v' * v' + s' * s' = remE →
        NoSq24 e u' v' s'
  | 0, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [checkU] at h
  | fuel + 1, u, h, hu_odd, u', v', s', hu'_odd, hv'_odd, hs'_odd, huu', hu'v', hv's', hsum => by
    unfold checkU at h
    by_cases hstop : 3 * u * u > remE
    · nlinarith
    · rw [if_neg hstop] at h
      dsimp only at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨hs0_gt, hvs⟩, hrest⟩
      by_cases heq : u' = u
      · subst heq
        set s0 := sStart (remE - u' * u')
        have hs'le : s' ≤ s0 := by
          by_contra hgt
          have h1 : s0 + 1 ≤ s' := by omega
          have h2 : (s0 + 1) * (s0 + 1) ≤ s' * s' := Nat.mul_le_mul h1 h1
          have h3 : (s0 + 1) * (s0 + 1) = s0 * s0 + 2 * s0 + 1 := by ring
          omega
        exact checkVS_sound e u' (remE - u' * u') 130 u' s0 hvs hu'_odd (sStart_odd _)
          v' s' hv'_odd hs'_odd hu'v' hv's' hs'le (by omega)
      · exact checkU_sound e remE fuel (u + 2) hrest (by omega)
          u' v' s' hu'_odd hv'_odd hs'_odd (by omega) hu'v' hv's' hsum

private lemma checkE_sound (e : Nat) (h : checkE e = true)
    (u' v' s' : Nat) (hu' : u' % 2 = 1) (hv' : v' % 2 = 1) (hs' : s' % 2 = 1)
    (huv : u' ≤ v') (hvs : v' ≤ s')
    (hsum : e * e + u' * u' + v' * v' + s' * s' = 56271) :
    NoSq24 e u' v' s' := by
  unfold checkE at h
  by_cases hbig : e * e > 56271
  · omega
  · rw [if_neg hbig] at h
    exact checkU_sound e (56271 - e * e) 75 1 h (by omega)
      u' v' s' hu' hv' hs' (by omega) huv hvs (by omega)

private lemma checkERange_sound :
    ∀ cnt t0 t, checkERange cnt t0 = true → t0 ≤ t → t < t0 + cnt → checkE (4 * t + 2) = true
  | 0, _, _, _, ht1, ht2 => by omega
  | cnt + 1, t0, t, h, ht1, ht2 => by
    unfold checkERange at h
    simp only [Bool.and_eq_true] at h
    by_cases heq : t = t0
    · subst heq; exact h.1
    · exact checkERange_sound cnt (t0 + 1) t h.2 (by omega) (by omega)

private lemma checkE_all (t : Nat) (ht : t ≤ 58) : checkE (4 * t + 2) = true := by
  if h20 : t < 20 then
    interval_cases t
    · exact checkE_t_0
    · exact checkE_t_1
    · exact checkE_t_2
    · exact checkE_t_3
    · exact checkE_t_4
    · exact checkE_t_5
    · exact checkE_t_6
    · exact checkE_t_7
    · exact checkE_t_8
    · exact checkE_t_9
    · exact checkE_t_10
    · exact checkE_t_11
    · exact checkE_t_12
    · exact checkE_t_13
    · exact checkE_t_14
    · exact checkE_t_15
    · exact checkE_t_16
    · exact checkE_t_17
    · exact checkE_t_18
    · exact checkE_t_19
  else if h22 : t < 22 then exact checkERange_sound 2 20 t checkE_blk_20 (by omega) (by omega)
  else if h24 : t < 24 then exact checkERange_sound 2 22 t checkE_blk_22 (by omega) (by omega)
  else if h26 : t < 26 then exact checkERange_sound 2 24 t checkE_blk_24 (by omega) (by omega)
  else if h28 : t < 28 then exact checkERange_sound 2 26 t checkE_blk_26 (by omega) (by omega)
  else if h30 : t < 30 then exact checkERange_sound 2 28 t checkE_blk_28 (by omega) (by omega)
  else if h32 : t < 32 then exact checkERange_sound 2 30 t checkE_blk_30 (by omega) (by omega)
  else if h34 : t < 34 then exact checkERange_sound 2 32 t checkE_blk_32 (by omega) (by omega)
  else if h36 : t < 36 then exact checkERange_sound 2 34 t checkE_blk_34 (by omega) (by omega)
  else if h38 : t < 38 then exact checkERange_sound 2 36 t checkE_blk_36 (by omega) (by omega)
  else if h40 : t < 40 then exact checkERange_sound 2 38 t checkE_blk_38 (by omega) (by omega)
  else if h44 : t < 44 then exact checkERange_sound 4 40 t checkE_blk_40 (by omega) (by omega)
  else if h48 : t < 48 then exact checkERange_sound 4 44 t checkE_blk_44 (by omega) (by omega)
  else if h52 : t < 52 then exact checkERange_sound 4 48 t checkE_blk_48 (by omega) (by omega)
  else if h56 : t < 56 then exact checkERange_sound 4 52 t checkE_blk_52 (by omega) (by omega)
  else exact checkERange_sound 3 56 t checkE_blk_56 (by omega) (by omega)

private lemma noSq24_of_even_three_odd (e a b c : Nat)
    (he : e % 4 = 2) (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1)
    (hsum : e * e + a * a + b * b + c * c = 56271) : NoSq24 e a b c := by
  have he_le : e ≤ 234 := by
    have : e ≤ 237 := by nlinarith
    omega
  set t := e / 4
  have het : e = 4 * t + 2 := by omega
  have hchk : checkE e = true := by
    rw [het]
    exact checkE_all t (by omega)
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · exact checkE_sound e hchk a b c ha hb hc hab hbc hsum
    · by_cases hac : a ≤ c
      · exact NoSq24_swap34 (checkE_sound e hchk a c b ha hc hb hac (by omega) (by omega))
      · exact NoSq24_swap34 (NoSq24_swap23
          (checkE_sound e hchk c a b hc ha hb (by omega) hab (by omega)))
  · by_cases hac : a ≤ c
    · exact NoSq24_swap23 (checkE_sound e hchk b a c hb ha hc (by omega) hac (by omega))
    · by_cases hbc : b ≤ c
      · exact NoSq24_swap23 (NoSq24_swap34
          (checkE_sound e hchk b c a hb hc ha hbc (by omega) (by omega)))
      · exact NoSq24_swap34 (NoSq24_swap23 (NoSq24_swap34
          (checkE_sound e hchk c b a hc hb ha (by omega) (by omega) (by omega))))

private lemma sq_mod8_cases (a : Nat) :
    (a % 4 = 0 ∧ a * a % 8 = 0) ∨
    (a % 2 = 1 ∧ a * a % 8 = 1) ∨
    (a % 4 = 2 ∧ a * a % 8 = 4) := by
  have hm : a * a % 8 = (a % 8) * (a % 8) % 8 := Nat.mul_mod a a 8
  have hlt : a % 8 < 8 := Nat.mod_lt a (by omega)
  have h4 : a % 4 = (a % 8) % 4 := by omega
  have h2 : a % 2 = (a % 8) % 2 := by omega
  rw [hm, h4, h2]
  interval_cases (a % 8) <;> decide

private lemma no_rep_56271 (x y z w : Nat)
    (hsum : 56271 = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) :
    ¬ IsSquare (x * y * (42 * x ^ 2 + 98 * y ^ 2 + 14 * z ^ 2)) := by
  have hsq : x * x + y * y + z * z + w * w = 56271 := by
    have : x ^ 2 = x * x := sq x
    have : y ^ 2 = y * y := sq y
    have : z ^ 2 = z * z := sq z
    have : w ^ 2 = w * w := sq w
    omega
  have hQ : x * y * (42 * x ^ 2 + 98 * y ^ 2 + 14 * z ^ 2) = Q x y z := by
    unfold Q; ring
  rw [hQ]
  have hmod : (x * x % 8 + y * y % 8 + z * z % 8 + w * w % 8) % 8 = 7 := by
    have := congrArg (· % 8) hsq
    omega
  have h24 : NoSq24 x y z w := by
    rcases sq_mod8_cases x with ⟨hx4, hxm⟩ | ⟨hx2, hxm⟩ | ⟨hx4, hxm⟩ <;>
    rcases sq_mod8_cases y with ⟨hy4, hym⟩ | ⟨hy2, hym⟩ | ⟨hy4, hym⟩ <;>
    rcases sq_mod8_cases z with ⟨hz4, hzm⟩ | ⟨hz2, hzm⟩ | ⟨hz4, hzm⟩ <;>
    rcases sq_mod8_cases w with ⟨hw4, hwm⟩ | ⟨hw2, hwm⟩ | ⟨hw4, hwm⟩ <;>
    simp only [hxm, hym, hzm, hwm] at hmod <;>
    try (exfalso; omega)
    · exact NoSq24_swap34 (NoSq24_swap23 (NoSq24_swap12
        (noSq24_of_even_three_odd w x y z hw4 hx2 hy2 hz2 (by omega))))
    · exact NoSq24_swap23 (NoSq24_swap12
        (noSq24_of_even_three_odd z x y w hz4 hx2 hy2 hw2 (by omega)))
    · exact NoSq24_swap12
        (noSq24_of_even_three_odd y x z w hy4 hx2 hz2 hw2 (by omega))
    · exact noSq24_of_even_three_odd x y z w hx4 hy2 hz2 hw2 (by omega)
  exact h24.1.1

end OeisA261876Disproof

theorem OMA.disproof : ¬ (type_of% @OeisA261876.conjecture_3) := by
  intro h
  have ht : (42, 98, 14) ∈ OeisA261876.triples := by decide
  rcases h (42, 98, 14) ht 56271 with ⟨x, y, z, w, hsum, hsq⟩
  exact OeisA261876Disproof.no_rep_56271 x y z w hsum hsq
