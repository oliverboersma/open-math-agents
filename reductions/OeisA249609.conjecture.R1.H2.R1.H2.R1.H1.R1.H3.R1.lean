import OMAReductions.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Tactic

/-!
# Three further binomial columns for OEIS A249609

For exponents `a = 3240*q + 2705`, columns 14, 15 and 16 supply an
even binary digit sum on 94 of the 105 residue classes of `q` modulo 105.
We use PanPapag's periodicity theorem from the parent reduction and certify
the parity of the representative coefficients by folding with bitwise xor.
The remaining classes are separated by their residues modulo seven.
-/

namespace OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1

open OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1

def H1 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([7, 21, 35, 77, 84, 91] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H2 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([33, 54, 68, 96] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

def H3 : Prop :=
  ∀ q : ℕ, q % 105 ∈ ([41] : List ℕ) →
    ∃ k ∈ List.range' 1 (2 ^ (3240*q+2705)),
      OeisA249609.isEvil ((2 ^ (3240*q+2705)).choose k) = true

section Certificates

private theorem weight_half (n : ℕ) :
    (Nat.digits 2 n).count 1 = (Nat.digits 2 (n/2)).count 1 + n%2 := by
  have hh := count_ones_append (n/2) 1 (n%2) (by simpa using Nat.mod_lt n (by decide : 0 < 2))
  rw [pow_one, Nat.div_add_mod'] at hh
  change (Nat.digits 2 n).count 1 = (Nat.digits 2 (n / 2)).count 1 + (Nat.digits 2 (n % 2)).count 1 at hh
  rw [hh]
  have h : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> rfl

private theorem xor_weight (a b : ℕ) : (Nat.digits 2 (a ^^^ b)).count 1 % 2 = ((Nat.digits 2 a).count 1 + (Nat.digits 2 b).count 1) % 2 := by
  induction h : a+b using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hzero : n = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a; subst b; rfl
    have half := ih (a/2+b/2) (by omega) (a/2) (b/2) rfl
    have ha := weight_half a
    have hb := weight_half b
    have hab := weight_half (a ^^^ b)
    rw [Nat.xor_div_two] at hab
    have hmod := Nat.xor_mod_two_eq (m := a) (n := b)
    omega

/-- Folding the two halves with xor preserves the parity and halves the bit width. -/
private theorem fold_certificate (i n : ℕ) (h :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base))) i n) = 0) :
    (Nat.digits 2 n).count 1 % 2 = 0 := by
  let count := Nat.rec (motive := fun _ => ℕ → ℕ) (fun v => (Nat.digits 2 v).count 1 % 2)
      (fun j f v => let base := 2^(8 * 2^j); f ((v / base) ^^^ (v % base)))
  have spec (j v : ℕ) : count j v = (Nat.digits 2 v).count 1 % 2 := by
    induction j generalizing v with
    | zero => rfl
    | succ j ih =>
      let w := 8*2^j
      change count j ((v / 2^w) ^^^ (v % 2^w)) = _
      rw [ih,xor_weight]
      have hh := count_ones_append (v / 2^w) w (v%2^w) (Nat.mod_lt _ (by positivity))
      rw [Nat.div_add_mod'] at hh
      exact congrArg (· % 2) hh.symm
  exact (spec i n).symm.trans h


set_option maxHeartbeats 4000000 in
private theorem falling14 (x B : ℕ) (hx : 0 < x) (hB : B = 34359738368) :
    ([(false, 0), (true, 28132717568), (false, 19802759039), (true, 7763021312), (false, 20313753095), (true, 24402034612), (false, 3336118785), (true, 33568795215), (false, 135036472), (true, 34343068715), (false, 1474472), (true, 34359647277), (false, 3730), (true, 34359738277), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 14 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 34359738277) 3730) 34359647277) 1474472) 34343068715) 135036472) 33568795215) 3336118785) 24402034612) 20313753095) 7763021312) 19802759039) 28132717568) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem parity14_5945 :
    (Nat.digits 2 ((2^5945).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 14
  decide +kernel

private theorem parity14_9185 :
    (Nat.digits 2 ((2^9185).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 14
  decide +kernel

private theorem parity14_12425 :
    (Nat.digits 2 ((2^12425).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 15
  decide +kernel

private theorem parity14_15665 :
    (Nat.digits 2 ((2^15665).descFactorial 14 / 42567525)).count 1 % 2 = 0 := by
  apply fold_certificate 15
  decide +kernel

set_option maxHeartbeats 3000000 in
private theorem column14 (a : ℕ) (ha : 35 ≤ a)
    (hr : a % 22680 ∈ ([5945, 9185, 12425, 15665] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 14) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (true, 28132717568), (false, 19802759039), (true, 7763021312), (false, 20313753095), (true, 24402034612), (false, 3336118785), (true, 33568795215), (false, 135036472), (true, 34343068715), (false, 1474472), (true, 34359647277), (false, 3730), (true, 34359738277), (false, 0)]
  refine (periodic_column (k := 14) (t := 35) (l := 11340) (d := 42567525) (z := 11)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 35]
    exact falling14 (2^w) (2^35) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr
  · rw [show (a-35) % (11340+11340) + 35 = 5945 by omega]
    exact parity14_5945
  · rw [show (a-35) % (11340+11340) + 35 = 9185 by omega]
    exact parity14_9185
  · rw [show (a-35) % (11340+11340) + 35 = 12425 by omega]
    exact parity14_12425
  · rw [show (a-35) % (11340+11340) + 35 = 15665 by omega]
    exact parity14_15665

set_option maxHeartbeats 4000000 in
private theorem falling15 (x B : ℕ) (hx : 0 < x) (hB : B = 549755813888) :
    ([(false, 0), (false, 87178291200), (true, 266290166528), (false, 392156797823), (true, 238766553488), (false, 159721605679), (true, 493092447128), (false, 14409322927), (true, 547074360113), (false, 368411614), (true, 549718501613), (false, 2749746), (true, 549755670563), (false, 5004), (true, 549755813783), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 15 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 549755813783) 5004) 549755670563) 2749746) 549718501613) 368411614) 547074360113) 14409322927) 493092447128) 159721605679) 238766553488) 392156797823) 266290166528) 87178291200) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem parity15_2705 :
    (Nat.digits 2 ((2^2705).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 13
  decide +kernel

private theorem parity15_18905 :
    (Nat.digits 2 ((2^18905).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity15_22145 :
    (Nat.digits 2 ((2^22145).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 16
  decide +kernel

private theorem parity15_41585 :
    (Nat.digits 2 ((2^41585).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_48065 :
    (Nat.digits 2 ((2^48065).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_67505 :
    (Nat.digits 2 ((2^67505).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity15_90185 :
    (Nat.digits 2 ((2^90185).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_93425 :
    (Nat.digits 2 ((2^93425).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_112865 :
    (Nat.digits 2 ((2^112865).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity15_158225 :
    (Nat.digits 2 ((2^158225).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_161465 :
    (Nat.digits 2 ((2^161465).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_180905 :
    (Nat.digits 2 ((2^180905).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_184145 :
    (Nat.digits 2 ((2^184145).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_200345 :
    (Nat.digits 2 ((2^200345).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_206825 :
    (Nat.digits 2 ((2^206825).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_226265 :
    (Nat.digits 2 ((2^226265).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_229505 :
    (Nat.digits 2 ((2^229505).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_245705 :
    (Nat.digits 2 ((2^245705).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_248945 :
    (Nat.digits 2 ((2^248945).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_268385 :
    (Nat.digits 2 ((2^268385).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_271625 :
    (Nat.digits 2 ((2^271625).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity15_291065 :
    (Nat.digits 2 ((2^291065).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity15_339665 :
    (Nat.digits 2 ((2^339665).descFactorial 15 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

set_option maxHeartbeats 3000000 in
private theorem column15 (a : ℕ) (ha : 39 ≤ a)
    (hr : a % 340200 ∈ ([2705, 18905, 22145, 41585, 48065, 67505, 90185, 93425, 112865, 158225, 161465, 180905, 184145, 200345, 206825, 226265, 229505, 245705, 248945, 268385, 271625, 291065, 339665] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 15) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (false, 87178291200), (true, 266290166528), (false, 392156797823), (true, 238766553488), (false, 159721605679), (true, 493092447128), (false, 14409322927), (true, 547074360113), (false, 368411614), (true, 549718501613), (false, 2749746), (true, 549755670563), (false, 5004), (true, 549755813783), (false, 0)]
  refine (periodic_column (k := 15) (t := 39) (l := 170100) (d := 638512875) (z := 11)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 39]
    exact falling15 (2^w) (2^39) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-39) % (170100+170100) + 39 = 2705 by omega]
    exact parity15_2705
  · rw [show (a-39) % (170100+170100) + 39 = 18905 by omega]
    exact parity15_18905
  · rw [show (a-39) % (170100+170100) + 39 = 22145 by omega]
    exact parity15_22145
  · rw [show (a-39) % (170100+170100) + 39 = 41585 by omega]
    exact parity15_41585
  · rw [show (a-39) % (170100+170100) + 39 = 48065 by omega]
    exact parity15_48065
  · rw [show (a-39) % (170100+170100) + 39 = 67505 by omega]
    exact parity15_67505
  · rw [show (a-39) % (170100+170100) + 39 = 90185 by omega]
    exact parity15_90185
  · rw [show (a-39) % (170100+170100) + 39 = 93425 by omega]
    exact parity15_93425
  · rw [show (a-39) % (170100+170100) + 39 = 112865 by omega]
    exact parity15_112865
  · rw [show (a-39) % (170100+170100) + 39 = 158225 by omega]
    exact parity15_158225
  · rw [show (a-39) % (170100+170100) + 39 = 161465 by omega]
    exact parity15_161465
  · rw [show (a-39) % (170100+170100) + 39 = 180905 by omega]
    exact parity15_180905
  · rw [show (a-39) % (170100+170100) + 39 = 184145 by omega]
    exact parity15_184145
  · rw [show (a-39) % (170100+170100) + 39 = 200345 by omega]
    exact parity15_200345
  · rw [show (a-39) % (170100+170100) + 39 = 206825 by omega]
    exact parity15_206825
  · rw [show (a-39) % (170100+170100) + 39 = 226265 by omega]
    exact parity15_226265
  · rw [show (a-39) % (170100+170100) + 39 = 229505 by omega]
    exact parity15_229505
  · rw [show (a-39) % (170100+170100) + 39 = 245705 by omega]
    exact parity15_245705
  · rw [show (a-39) % (170100+170100) + 39 = 248945 by omega]
    exact parity15_248945
  · rw [show (a-39) % (170100+170100) + 39 = 268385 by omega]
    exact parity15_268385
  · rw [show (a-39) % (170100+170100) + 39 = 271625 by omega]
    exact parity15_271625
  · rw [show (a-39) % (170100+170100) + 39 = 291065 by omega]
    exact parity15_291065
  · rw [show (a-39) % (170100+170100) + 39 = 339665 by omega]
    exact parity15_339665

set_option maxHeartbeats 4000000 in
private theorem falling16 (x B : ℕ) (hx : 0 < x) (hB : B = 8796093022208) :
    ([(false, 0), (true, 7488418654208), (false, 4339163001599), (true, 2630275407488), (false, 5056995703823), (true, 6089279676608), (false, 1009672107079), (true, 8523289811528), (false, 54631129552), (true, 8787885394208), (false, 928095739), (true, 8796014463728), (false, 4899621), (true, 8796092803808), (false, 6579), (true, 8796093022088), (false, 0)] : List (Bool × ℕ)).foldr
      (fun s v => (v * x + (if s.1 then x-1 else 0)) * B + s.2) 0 =
      (x * B).descFactorial 16 := by
  let low (v c : ℕ) := (v * x + 0) * B + c
  let high (v c : ℕ) := (v * x + (x-1)) * B + c
  calc
    _ = (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low (high (low 0 0) 8796093022088) 6579) 8796092803808) 4899621) 8796014463728) 928095739) 8787885394208) 54631129552) 8523289811528) 1009672107079) 6089279676608) 5056995703823) 2630275407488) 4339163001599) 7488418654208) 0) := rfl
    _ = _ := by
      dsimp only [low, high]
      rw [hB]
      apply Int.ofNat_inj.mp
      norm_num [Nat.descFactorial]
      simp (disch := omega) only [Nat.cast_sub, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem parity16_44825 :
    (Nat.digits 2 ((2^44825).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity16_64265 :
    (Nat.digits 2 ((2^64265).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 17
  decide +kernel

private theorem parity16_86945 :
    (Nat.digits 2 ((2^86945).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 18
  decide +kernel

private theorem parity16_132305 :
    (Nat.digits 2 ((2^132305).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_138785 :
    (Nat.digits 2 ((2^138785).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_154985 :
    (Nat.digits 2 ((2^154985).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_203585 :
    (Nat.digits 2 ((2^203585).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 19
  decide +kernel

private theorem parity16_294305 :
    (Nat.digits 2 ((2^294305).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity16_316985 :
    (Nat.digits 2 ((2^316985).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity16_320225 :
    (Nat.digits 2 ((2^320225).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

private theorem parity16_336425 :
    (Nat.digits 2 ((2^336425).descFactorial 16 / 638512875)).count 1 % 2 = 0 := by
  apply fold_certificate 20
  decide +kernel

set_option maxHeartbeats 3000000 in
private theorem column16 (a : ℕ) (ha : 43 ≤ a)
    (hr : a % 340200 ∈ ([44825, 64265, 86945, 132305, 138785, 154985, 203585, 294305, 316985, 320225, 336425] : List ℕ)) :
    OeisA249609.isEvil ((2^a).choose 16) = true := by
  let ds : List (Bool × ℕ) := [(false, 0), (true, 7488418654208), (false, 4339163001599), (true, 2630275407488), (false, 5056995703823), (true, 6089279676608), (false, 1009672107079), (true, 8523289811528), (false, 54631129552), (true, 8787885394208), (false, 928095739), (true, 8796014463728), (false, 4899621), (true, 8796092803808), (false, 6579), (true, 8796093022088), (false, 0)]
  refine (periodic_column (k := 16) (t := 43) (l := 170100) (d := 638512875) (z := 15)
    (ds := ds) ha (by decide) (by decide +kernel) ?_ ?_ (by decide)).2 ?_
  · dsimp only [ds]; decide
  · intro w
    rw [pow_add 2 w 43]
    exact falling16 (2^w) (2^43) (by positivity) (by decide)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr
  · rw [show (a-43) % (170100+170100) + 43 = 44825 by omega]
    exact parity16_44825
  · rw [show (a-43) % (170100+170100) + 43 = 64265 by omega]
    exact parity16_64265
  · rw [show (a-43) % (170100+170100) + 43 = 86945 by omega]
    exact parity16_86945
  · rw [show (a-43) % (170100+170100) + 43 = 132305 by omega]
    exact parity16_132305
  · rw [show (a-43) % (170100+170100) + 43 = 138785 by omega]
    exact parity16_138785
  · rw [show (a-43) % (170100+170100) + 43 = 154985 by omega]
    exact parity16_154985
  · rw [show (a-43) % (170100+170100) + 43 = 203585 by omega]
    exact parity16_203585
  · rw [show (a-43) % (170100+170100) + 43 = 294305 by omega]
    exact parity16_294305
  · rw [show (a-43) % (170100+170100) + 43 = 316985 by omega]
    exact parity16_316985
  · rw [show (a-43) % (170100+170100) + 43 = 320225 by omega]
    exact parity16_320225
  · rw [show (a-43) % (170100+170100) + 43 = 336425 by omega]
    exact parity16_336425

end Certificates

private theorem cover : ∀ q : Fin 105,
    (3240*q.val+2705) % 22680 ∈ ([5945, 9185, 12425, 15665] : List ℕ) ∨
    (3240*q.val+2705) % 340200 ∈ ([2705, 18905, 22145, 41585, 48065, 67505, 90185, 93425, 112865, 158225, 161465, 180905, 184145, 200345, 206825, 226265, 229505, 245705, 248945, 268385, 271625, 291065, 339665] : List ℕ) ∨
    (3240*q.val+2705) % 340200 ∈ ([44825, 64265, 86945, 132305, 138785, 154985, 203585, 294305, 316985, 320225, 336425] : List ℕ) ∨
    q.val ∈ ([7, 21, 35, 77, 84, 91] : List ℕ) ∨
    q.val ∈ ([33, 54, 68, 96] : List ℕ) ∨
    q.val ∈ ([41] : List ℕ) := by decide +kernel

theorem main : H1 → H2 → H3 → OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1.H3 := by
  intro h1 h2 h3 q
  have reduceMod (d : ℕ) (hd : d ∣ 340200) :
      (3240*(q%105)+2705)%d = (3240*q+2705)%d :=
    (((Nat.mod_modEq q 105).mul_left' 3240).of_dvd hd).add_right 2705
  have cases := cover ⟨q%105, Nat.mod_lt _ (by decide)⟩
  dsimp only at cases
  rw [reduceMod 22680 (by decide), reduceMod 340200 (by decide)] at cases
  have hbig : 16 ≤ 2^(3240*q+2705) :=
    le_trans (by decide : 16 ≤ 2^4) (Nat.pow_le_pow_right (by decide) (by omega))
  rcases cases with h | h | h | h | h | h
  · exact witness _ 14 (by decide) (by omega) (column14 _ (by omega) h)
  · exact witness _ 15 (by decide) (by omega) (column15 _ (by omega) h)
  · exact witness _ 16 (by decide) (by omega) (column16 _ (by omega) h)
  · exact h1 q h
  · exact h2 q h
  · exact h3 q h

end OMA.R_OeisA249609_conjecture_R1_H2_R1_H2_R1_H1_R1_H3_R1
