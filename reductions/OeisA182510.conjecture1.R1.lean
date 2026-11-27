import FormalConjectures.OEIS.«182510»

/-! # Dyadic blocks of the signed XOR recurrence

The sequence modulo `2^k` repeats under a shift of `3 * 2^k`. At the next
precision the normalized change has period three modulo two. This yields a
necessary filter on offsets before computing any new block. An independent
six-periodic comparison controls the beginning of each block.

The two unresolved hypotheses concern the sizes of the boundary projections
and the surviving interior offsets, respectively.
-/
-- Credit: @marcusbuffett

namespace OMA.R_OeisA182510_conjecture1_R1

open OeisA182510

private theorem xor_mod_two (x y : ℤ) : Int.xor x y ≡ x + y [ZMOD 2] := by
  induction x using Int.bitCasesOn with
  | h b x =>
    induction y using Int.bitCasesOn with
    | h c y =>
      rw [Int.lxor_bit]
      cases b <;> cases c <;> simp [Int.bit_val, Int.ModEq] <;> omega

private theorem bit_translate (k : ℕ) (b : Bool) (x s : ℤ) :
    Int.bit b x + 2^(k+1) * s = Int.bit b (x + 2^k * s) := by
  simp only [Int.bit_val, pow_succ]
  ring

theorem xor_translate (k : ℕ) (x y s t : ℤ) :
    Int.xor (x + 2^k*s) (y + 2^k*t) ≡ Int.xor x y + 2^k*(s+t) [ZMOD 2^(k+1)] := by
  induction k generalizing x y with
  | zero =>
    norm_num only [pow_zero, one_mul, zero_add, pow_one]
    apply (xor_mod_two (x+s) (y+t)).trans
    have h := (xor_mod_two x y).symm.add_right (s+t)
    convert h using 1 <;> ring
  | succ k ih =>
    induction x using Int.bitCasesOn with
    | h b x =>
      induction y using Int.bitCasesOn with
      | h c y =>
        rw [bit_translate k b x s, bit_translate k c y t, Int.lxor_bit, Int.lxor_bit]
        have h := Int.ModEq.mul_left' (c := 2) (ih x y)
        have h' := h.add_right (cond (b ^^ c) (1:ℤ) 0)
        simp only [Int.bit_val]
        convert h' using 1 <;> ring

private theorem lifts_again (k : ℕ) (s : ℕ → ℤ)
    (hs : ∀ n, a (n + 3*2^k) = a n + (2:ℤ)^k * s n) :
    (∀ n, s (n+3) % 2 = s n % 2) ∧
    ∃ s' : ℕ → ℤ, ∀ n, a (n + 3*2^(k+1)) = a n + (2:ℤ)^(k+1) * s' n := by
  let M : ℤ := 2^k
  let P : ℕ := 3*2^k
  have hM : M ≠ 0 := by dsimp [M]; positivity
  have hP : (P : ℤ) = M*3 := by dsimp [P,M]; push_cast; ring
  have shift : ∀ n, a (n+P) = a n + M*s n := hs
  have step (n : ℕ) : s (n+2) % 2 = (s (n+1) + 3 - s n) % 2 := by
    have hx := xor_translate k (a (n+1)) (n+2 : ℤ) (s (n+1)) 3
    obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hx
    change (Int.xor (a (n+1)) (n+2) + M*(s (n+1)+3)) -
      Int.xor (a (n+1) + M*s (n+1)) ((n:ℤ)+2+M*3) = 2^(k+1)*c at hc
    have hrec : a (n+2+P) =
        Int.xor (a (n+1+P)) ((n:ℤ)+2+M*3) - a (n+P) := by
      rw [show n+2+P = (n+P)+2 by omega, show n+1+P = (n+P)+1 by omega, a]
      push_cast
      rw [hP]
      congr 2 <;> ring
    rw [shift (n+2), shift (n+1), shift n] at hrec
    change Int.xor (a (n+1)) (n+2) - a n + M*s (n+2) = _ at hrec
    rw [pow_succ] at hc
    change _ = M * 2 * c at hc
    have heq : M * s (n+2) = M * (s (n+1) + 3 - s n - 2*c) := by
      linear_combination hrec - hc
    have := mul_left_cancel₀ hM heq
    omega
  have three (n : ℕ) : s (n+3) % 2 = s n % 2 := by
    have h := step n
    have h' := step (n+1)
    change s (n+3) % 2 = (s (n+2) + 3 - s (n+1)) % 2 at h'
    omega
  refine ⟨three, fun n => (s n + s (n+P)) / 2, ?_⟩
  intro n
  have loop (t : ℕ) : s (n + 3*t) % 2 = s n % 2 := by
    induction t with
    | zero => simp
    | succ t ih => rw [Nat.mul_succ, ← Nat.add_assoc, three, ih]
  have hp : s (n+P) % 2 = s n % 2 := loop (2^k)
  have he : s n + s (n+P) = 2 * ((s n + s (n+P))/2) := by omega
  have ht : n + 3*2^(k+1) = n+P+P := by dsimp [P]; rw [pow_succ]; omega
  rw [ht, shift (n+P), shift n, pow_succ]
  change a n + M*s n + M*s (n+P) = a n + M*2*((s n + s (n+P))/2)
  linear_combination M * he

theorem lifts (k : ℕ) : ∃ s : ℕ → ℤ, ∀ n, a (n+3*2^k) = a n + (2:ℤ)^k * s n := by
  induction k with
  | zero => exact ⟨fun n => a (n+3) - a n, by simp⟩
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih
    exact (lifts_again k s hs).2

theorem necessary (k r : ℕ) (hz : a (3*2^k+r) = 0) :
    (2 : ℤ)^(k+1) ∣ a r + a (3*2^k + r%3) - a (r%3) := by
  obtain ⟨s, hs⟩ := lifts k
  have hthree := (lifts_again k s hs).1
  have cycle (q i : ℕ) : s (i + 3*q) % 2 = s i % 2 := by
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, hthree, ih]
  have hmod : s r % 2 = s (r%3) % 2 := by
    simpa only [Nat.mod_add_div] using cycle (r/3) (r%3)
  obtain ⟨z,hz'⟩ := Int.modEq_iff_dvd.mp (show s r ≡ s (r%3) [ZMOD 2] from hmod)
  refine ⟨z, ?_⟩
  rw [Nat.add_comm (3*2^k), hs, pow_succ]
  rw [Nat.add_comm (3*2^k), hs] at hz
  linear_combination hz + (2:ℤ)^k * hz'

private theorem xor_error (y : ℕ) (x : ℤ) : |Int.xor x y - x| ≤ y := by
  induction y using Nat.binaryRec generalizing x with
  | zero => cases x <;> simp [Int.xor]
  | bit b y ih =>
    induction x using Int.bitCasesOn with
    | h c x =>
      have h := abs_le.mp (ih x)
      rw [← Int.bit_coe_nat, Int.lxor_bit]
      apply abs_le.mpr
      cases b <;> cases c <;> simp [Int.bit_val] at * <;> omega

/-- If one starts at `P` and ignores the XOR forcing, the state rotates with
period six. Every coordinate and every difference acquires at most one forcing
term's magnitude at each subsequent update. -/
private theorem window {P R : ℕ}
    (hb : (R : ℤ) * (P + R + 1) < |a P| ∧
      (R : ℤ) * (P + R + 1) < |a (P+1)| ∧
      (R : ℤ) * (P + R + 1) < |a P - a (P+1)|) :
    ∀ r ≤ R, a (P+r) ≠ 0 := by
  let u := a P
  let v := a (P+1)
  let w (i : ℕ) : ℤ := match i % 6 with
    | 0 => u | 1 => v | 2 => v-u | 3 => -u | 4 => -v | _ => u-v
  have hw (i : ℕ) : w (i+2) = w (i+1) - w i := by
    have hi := Nat.mod_lt i (by decide : 0 < 6)
    dsimp only [w]
    rw [Nat.add_mod i 2, Nat.add_mod i 1]
    interval_cases h : i % 6 <;> simp <;> ring
  let C : ℤ := P + R + 1
  let d (i : ℕ) := a (P+i) - w i
  have hzero : d 0 = 0 := by simp [d,w,u]
  have hone : d 1 = 0 := by simp [d,w,v]
  have bound (i : ℕ) (hi : i ≤ R) :
      |d i| ≤ i*C ∧ |d (i+1)| ≤ i*C ∧ |d (i+1)-d i| ≤ i*C := by
    induction i with
    | zero => simp [hzero,hone]
    | succ i ih =>
      obtain ⟨ha,hb,hc⟩ := ih (by omega)
      let e := Int.xor (a (P+i+1)) ((P+i+2:ℕ):ℤ) - a (P+i+1)
      have he : |e| ≤ C := by
        have hh := xor_error (P+i+2) (a (P+i+1))
        dsimp [C]
        exact hh.trans (by push_cast; omega)
      have hd : d (i+2) = d (i+1) - d i + e := by
        dsimp only [d, e]
        rw [hw, show P+(i+2) = (P+i)+2 by omega, a, show P+(i+1) = P+i+1 by omega]
        push_cast
        ring
      have hd' : d (i+2) - d (i+1) = -(d i) + e := by rw [hd]; ring
      have hC : 0 ≤ C := by dsimp [C]; positivity
      change |d (i+1)| ≤ (i+1:ℕ)*C ∧ |d (i+2)| ≤ (i+1:ℕ)*C ∧ |d (i+2)-d (i+1)| ≤ (i+1:ℕ)*C
      push_cast
      rw [add_mul, one_mul, hd', hd]
      have h2 := abs_add_le (d (i+1)-d i) e
      have h3 := abs_add_le (-(d i)) e
      rw [abs_neg] at h3
      omega
  intro r hr hz
  have h := (bound r hr).1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hle : (r:ℤ)*C ≤ (R:ℤ)*C := mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hC
  have hsmall : |w r| ≤ R*C := by simpa [d,hz] using h.trans hle
  have hmod := Nat.mod_lt r (by decide : 0 < 6)
  dsimp only [w] at hsmall
  change R*C < |u| ∧ R*C < |v| ∧ R*C < |u-v| at hb
  interval_cases h : r % 6 <;> simp [abs_sub_comm v u] at hsmall <;> omega

private theorem cast_xor (w : ℕ) (x : ℤ) (y : ℕ) :
    BitVec.ofInt w (Int.xor x y) = BitVec.ofInt w x ^^^ BitVec.ofNat w y := by
  cases x <;> simp [Int.xor, BitVec.not_xor_left]

theorem block (w P r : ℕ) :
    Nat.rec (motive := fun _ => BitVec w × BitVec w)
      (BitVec.ofInt w (a P), BitVec.ofInt w (a (P+1)))
      (fun j s => (s.2, (s.2 ^^^ BitVec.ofNat w (P+j+2)) - s.1)) r =
      (BitVec.ofInt w (a (P+r)), BitVec.ofInt w (a (P+r+1))) := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [ih]
    apply Prod.ext
    · rfl
    · change _ = BitVec.ofInt w (a (P+r+2))
      rw [a, show ((P+r:ℕ):ℤ)+2 = ((P+r+2:ℕ):ℤ) by push_cast; ring]
      simp only [sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, cast_xor]

private theorem batch {N L : ℕ} {x y u v : ℤ} (hx : a N = x) (hy : a (N+1) = y)
    (h : (List.range L).foldl (fun (s : ℤ × ℤ × Bool) j =>
        (s.2.1, Int.xor s.2.1 ((N+j+2 : ℕ) : ℤ) - s.1, s.2.2 && s.1 != 0))
      (x,y,true) = (u,v,true)) :
    a (N+L) = u ∧ a (N+L+1) = v ∧ ∀ n, N ≤ n → n < N+L → a n ≠ 0 := by
  let f := fun (s : ℤ × ℤ × Bool) (j : ℕ) =>
    (s.2.1, Int.xor s.2.1 ((N+j+2 : ℕ) : ℤ) - s.1, s.2.2 && s.1 != 0)
  let state (l : ℕ) := (List.range l).foldl f (x,y,true)
  have hs (l : ℕ) : (state l).1 = a (N+l) ∧ (state l).2.1 = a (N+l+1) ∧
      ((state l).2.2 = true → ∀ n, N ≤ n → n < N+l → a n ≠ 0) := by
    induction l with
    | zero => simp [state,hx,hy]; omega
    | succ l ih =>
      obtain ⟨ha,hb,hok⟩ := ih
      have hl : state (l+1) = f (state l) l := by simp [state, List.range_succ]
      rw [hl]
      simp only [f,ha,hb, Bool.and_eq_true, bne_iff_ne]
      refine ⟨rfl, ?_, ?_⟩
      · rw [show N+(l+1)+1 = (N+l)+2 by omega, a]
        push_cast
        rfl
      · rintro ⟨hflag, hnz⟩ n hN hn
        by_cases hh : n = N+l
        · simpa [hh] using hnz
        · exact hok hflag n hN (by omega)
  obtain ⟨ha,hb,hflag⟩ := hs L
  change state L = _ at h
  rw [h] at ha hb hflag
  exact ⟨ha.symm, hb.symm, hflag rfl⟩


private theorem extend {N L : ℕ} {x y u v : ℤ}
    (old : a N = x ∧ a (N+1) = y ∧ ∀ n, 55 ≤ n → n < N → a n ≠ 0)
    (h : (List.range L).foldl (fun (s : ℤ × ℤ × Bool) j =>
        (s.2.1, Int.xor s.2.1 ((N+j+2 : ℕ) : ℤ) - s.1, s.2.2 && s.1 != 0))
      (x,y,true) = (u,v,true)) :
    a (N+L) = u ∧ a (N+L+1) = v ∧ ∀ n, 55 ≤ n → n < N+L → a n ≠ 0 := by
  obtain ⟨hu,hv,hl⟩ := batch old.1 old.2.1 h
  refine ⟨hu,hv,fun n h₅₅ hn => ?_⟩
  by_cases hlt : n < N
  · exact old.2.2 n h₅₅ hlt
  · exact hl n (by omega) hn

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3200000 in
private theorem before_block : ∀ n, 55 ≤ n → n < 12288 → a n ≠ 0 := by
  have b0 : a 55 = 73 ∧ a 56 = 113 ∧ ∀ n, 55 ≤ n → n < 55 → a n ≠ 0 :=
    ⟨by decide, by decide, by omega⟩
  have b1 := extend (N := 55) (L := 256) (u := -960) (v := 8088) b0 (by decide)
  have b2 := extend (N := 311) (L := 256) (u := -11713) (v := -3004) b1 (by decide)
  have b3 := extend (N := 567) (L := 256) (u := -8375) (v := -42383) b2 (by decide)
  have b4 := extend (N := 823) (L := 256) (u := 85056) (v := 30104) b3 (by decide)
  have b5 := extend (N := 1079) (L := 256) (u := -75201) (v := 91460) b4 (by decide)
  have b6 := extend (N := 1335) (L := 256) (u := -139703) (v := -216463) b5 (by decide)
  have b7 := extend (N := 1591) (L := 256) (u := 228928) (v := 83352) b6 (by decide)
  have b8 := extend (N := 1847) (L := 256) (u := -93121) (v := 147012) b7 (by decide)
  have b9 := extend (N := 2103) (L := 256) (u := -178871) (v := -163727) b8 (by decide)
  have b10 := extend (N := 2359) (L := 256) (u := 66112) (v := -225384) b9 (by decide)
  have b11 := extend (N := 2615) (L := 256) (u := 260159) (v := 284484) b10 (by decide)
  have b12 := extend (N := 2871) (L := 256) (u := -253879) (v := -28559) b11 (by decide)
  have b13 := extend (N := 3127) (L := 256) (u := 17472) (v := -177256) b12 (by decide)
  have b14 := extend (N := 3383) (L := 256) (u := 173631) (v := 169028) b13 (by decide)
  have b15 := extend (N := 3639) (L := 256) (u := -225463) (v := -99727) b14 (by decide)
  have b16 := extend (N := 3895) (L := 256) (u := 265280) (v := 29080) b15 (by decide)
  have b17 := extend (N := 4151) (L := 256) (u := 52799) (v := 531780) b16 (by decide)
  have b18 := extend (N := 4407) (L := 256) (u := -649655) (v := -533903) b17 (by decide)
  have b19 := extend (N := 4663) (L := 256) (u := 486976) (v := -196200) b18 (by decide)
  have b20 := extend (N := 4919) (L := 256) (u := 473151) (v := 720452) b19 (by decide)
  have b21 := extend (N := 5175) (L := 256) (u := -879287) (v := -382863) b20 (by decide)
  have b22 := extend (N := 5431) (L := 256) (u := 528960) (v := -423016) b21 (by decide)
  have b23 := extend (N := 5687) (L := 256) (u := 468031) (v := 960324) b22 (by decide)
  have b24 := extend (N := 5943) (L := 256) (u := -1017783) (v := -735119) b23 (by decide)
  have b25 := extend (N := 6199) (L := 256) (u := 717888) (v := -125032) b24 (by decide)
  have b26 := extend (N := 6455) (L := 256) (u := 219711) (v := 961604) b25 (by decide)
  have b27 := extend (N := 6711) (L := 256) (u := -1001655) (v := -798095) b26 (by decide)
  have b28 := extend (N := 6967) (L := 256) (u := 1045568) (v := -254568) b27 (by decide)
  have b29 := extend (N := 7223) (L := 256) (u := 225855) (v := 1375556) b28 (by decide)
  have b30 := extend (N := 7479) (L := 256) (u := -1407415) (v := -1189263) b29 (by decide)
  have b31 := extend (N := 7735) (L := 256) (u := 1201728) (v := -221800) b30 (by decide)
  have b32 := extend (N := 7991) (L := 256) (u := -91073) (v := 1431108) b31 (by decide)
  have b33 := extend (N := 8247) (L := 256) (u := -1872567) (v := -2217871) b32 (by decide)
  have b34 := extend (N := 8503) (L := 256) (u := 2845248) (v := 1484696) b33 (by decide)
  have b35 := extend (N := 8759) (L := 256) (u := -2015169) (v := 1675076) b34 (by decide)
  have b36 := extend (N := 9015) (L := 256) (u := -1484727) (v := -3733391) b35 (by decide)
  have b37 := extend (N := 9271) (L := 256) (u := 3791936) (v := 2118552) b36 (by decide)
  have b38 := extend (N := 9527) (L := 256) (u := -2261441) (v := 1477700) b37 (by decide)
  have b39 := extend (N := 9783) (L := 256) (u := -1386679) (v := -3726735) b38 (by decide)
  have b40 := extend (N := 10039) (L := 256) (u := 3712064) (v := 2406808) b39 (by decide)
  have b41 := extend (N := 10295) (L := 256) (u := -2714049) (v := 1643844) b40 (by decide)
  have b42 := extend (N := 10551) (L := 256) (u := -1860023) (v := -4554127) b41 (by decide)
  have b43 := extend (N := 10807) (L := 256) (u := 4625984) (v := 2943384) b42 (by decide)
  have b44 := extend (N := 11063) (L := 256) (u := -2973633) (v := 1844804) b43 (by decide)
  have b45 := extend (N := 11319) (L := 256) (u := -1479351) (v := -4558735) b44 (by decide)
  have b46 := extend (N := 11575) (L := 256) (u := 4643392) (v := 3515288) b45 (by decide)
  have b47 := extend (N := 11831) (L := 256) (u := -3646401) (v := 1232708) b46 (by decide)
  have b48 := extend (N := 12087) (L := 201) (u := 3747840) (v := -1286143) b47 (by decide)
  exact b48.2.2

/-- The distance of the three boundary projections from zero dominates the
possible accumulated forcing through the first `k` positions of the block. -/
def H1 : Prop :=
  ∀ k : ℕ, 12 ≤ k →
    let P : ℕ := 3 * 2^k
    let B : ℤ := k * ((P : ℤ) + k + 1)
    B < |a P| ∧ B < |a (P+1)| ∧ B < |a P - a (P+1)|

/-- In the rest of the block a modular register only needs to exclude the
offsets passing the lower-block congruence. The test uses the lower-block
value and one of three boundary corrections before traversing the new block. -/
def H2 : Prop :=
  ∀ k : ℕ, 12 ≤ k →
    let P := 3 * 2^k
    ∀ r : ℕ, k < r → r < P →
      (2:ℤ)^(k+1) ∣ a r + a (P+r%3) - a (r%3) →
      let w := 2*k+6
      let state := Nat.rec (motive := fun _ => BitVec w × BitVec w)
        (BitVec.ofInt w (a P), BitVec.ofInt w (a (P+1)))
        (fun j s => (s.2, (s.2 ^^^ BitVec.ofNat w (P+j+2)) - s.1)) r
      state.1 ≠ 0

theorem main : H1 → H2 → type_of% @OeisA182510.conjecture1 := by
  intro hb hi
  have tail (n : ℕ) (hn : 12288 ≤ n) : a n ≠ 0 := by
    let k := Nat.log 2 (n/3)
    let P := 3*2^k
    have hk : 12 ≤ k := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
    have hlow : P ≤ n := by
      have h := Nat.pow_log_le_self 2 (show n/3 ≠ 0 by omega)
      change 2^k ≤ n/3 at h
      dsimp only [P]
      omega
    have hu : n < 2*P := by
      have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n/3)
      change n/3 < 2^(k+1) at h
      rw [pow_succ] at h
      dsimp only [P]
      omega
    let r := n - P
    have hr : r < P := by dsimp [r]; omega
    have heq : n = P+r := by dsimp [r]; omega
    rw [heq]
    by_cases hs : r ≤ k
    · exact window (P := P) (R := k) (hb k hk) r hs
    · intro hz
      have hbit := necessary k r hz
      have hcut := hi k hk r (by omega) hr hbit
      dsimp only at hcut
      rw [block (2*k+6) P r, hz] at hcut
      exact hcut rfl
  let Z : Finset ℕ := {0,6,11,23,36,42,48,54}
  have hsmall : ∀ n : Fin 55, a n = 0 ↔ n.val ∈ Z := by decide
  have heq : {n : ℕ | a n = 0} = (Z : Set ℕ) := by
    ext n
    change a n = 0 ↔ n ∈ Z
    by_cases hn : n < 55
    · exact hsmall ⟨n,hn⟩
    · have hnot : n ∉ Z := by simp [Z]; omega
      have hne : a n ≠ 0 := by
        by_cases h : n < 12288
        · exact before_block n (by omega) h
        · exact tail n (by omega)
      simp [hne,hnot]
  rw [heq,Set.ncard_coe_finset]
  decide


end OMA.R_OeisA182510_conjecture1_R1
