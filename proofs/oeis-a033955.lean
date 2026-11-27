import OMAStatements.S_oeis_a033955
import Mathlib

/-! A Chebyshev bound and a bounded certificate settle the prime-remainder inequality. -/


open Real

theorem prime_remainders_theta (p : ℕ) (hp : 65536 ≤ p) :
    (3 * √(p : ℝ) + 1) * log p < Chebyshev.theta p - Chebyshev.theta ((p : ℝ) / 3) := by
  let x : ℝ := p
  let z := √x
  have hx : 65536 ≤ x := by
    dsimp [x]
    exact_mod_cast hp
  have hz2 : z ^ 2 = x := sq_sqrt (by linarith)
  have hz0 : 0 ≤ z := sqrt_nonneg _
  have hz : 256 ≤ z := by nlinarith
  have hzpos : 0 < z := by positivity
  have hlog2hi : log 2 ≤ 7 / 10 := by linarith [log_two_lt_d9]
  have hlog2lo : 69 / 100 ≤ log 2 := by linarith [log_two_gt_d9]
  have hlog256 : log 256 = 8 * log 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℕ) by norm_num, log_pow]
    norm_num
  have hlogx : log x = 2 * log z := by
    rw [← hz2, log_pow]
    norm_num
  have hlogz : log z = log 256 + log (z / 256) := by
    rw [log_div (by positivity) (by positivity)]
    ring
  have hlogbound : log x ≤ z / 22 := by
    have h := log_le_sub_one_of_pos (show 0 < z / 256 by positivity)
    linarith
  have hlogp : log (x + 1) ≤ 2 * log x := by
    rw [← show log (x ^ (2 : ℕ)) = 2 * log x by rw [log_pow]; norm_num]
    exact log_le_log (by positivity) (by nlinarith)
  have hlog4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, log_pow]
    norm_num
  have hθlo := Chebyshev.theta_ge p
  have hθhi := Chebyshev.theta_le_log4_mul_x (x := x / 3) (by positivity)
  change x * log 2 - log (x + 1) - 2 * z * log x ≤ Chebyshev.theta x at hθlo
  rw [hlog4] at hθhi
  have hlogmul := mul_le_mul_of_nonneg_left hlogbound (show 0 ≤ 5 * z + 3 by positivity)
  have hmain := mul_le_mul_of_nonneg_left hlog2lo (show 0 ≤ x / 3 by positivity)
  change (3 * z + 1) * log x < Chebyshev.theta x - Chebyshev.theta (x / 3)
  nlinarith

open Finset
open scoped BigOperators

theorem prime_remainders_many (p : ℕ) (hp : 65536 ≤ p) :
    3 * √(p : ℝ) + 1 <
      ((p.primesLE \ Nat.primesLE ⌊(p : ℝ) / 3⌋₊).card : ℝ) := by
  let S := p.primesLE \ Nat.primesLE ⌊(p : ℝ) / 3⌋₊
  have hfloor : ⌊(p : ℝ) / 3⌋₊ ≤ p :=
    Nat.floor_le_of_le (by linarith [Nat.cast_nonneg (α := ℝ) p])
  have hsub : Nat.primesLE ⌊(p : ℝ) / 3⌋₊ ⊆ p.primesLE := by
    intro q hq
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hq
    exact Nat.mem_primesLE.mpr ⟨hle.trans hfloor, hprime⟩
  have heq : (∑ q ∈ S, log q) =
      Chebyshev.theta p - Chebyshev.theta ((p : ℝ) / 3) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE]
    exact eq_sub_of_add_eq (Finset.sum_sdiff hsub)
  have hsum : (∑ q ∈ S, log q) ≤ (S.card : ℝ) * log p := by
    calc
      (∑ q ∈ S, log q) ≤ ∑ _q ∈ S, log p := by
        apply Finset.sum_le_sum
        intro q hq
        have hq' := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hq).1
        exact log_le_log (by exact_mod_cast hq'.2.pos) (by exact_mod_cast hq'.1)
      _ = _ := by simp
  exact lt_of_mul_lt_mul_right
    ((prime_remainders_theta p hp).trans_le (heq ▸ hsum))
    (by positivity : 0 ≤ log (p : ℝ))

theorem prime_remainders_nth (n : ℕ) :
    (∑ q ∈ (Nat.nth Nat.Prime n).primesLE, Nat.nth Nat.Prime n % q) =
      ∑ k ∈ Finset.range n, Nat.nth Nat.Prime n % Nat.nth Nat.Prime k := by
  let f : ℕ ↪ ℕ := ⟨Nat.nth Nat.Prime, (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective⟩
  have hmap : (Finset.range (n + 1)).map f = (f n).primesLE := by
    ext q
    simp only [Finset.mem_map, Finset.mem_range, Nat.mem_primesLE]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega),
        Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k⟩
    · rintro ⟨hq, hprime⟩
      refine ⟨Nat.count Nat.Prime q, ?_, Nat.nth_count hprime⟩
      have he : f (Nat.count Nat.Prime q) = q := Nat.nth_count hprime
      have hk := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).le_iff_le.mp
        (show f (Nat.count Nat.Prime q) ≤ f n by rwa [he])
      omega
  change (∑ q ∈ (f n).primesLE, f n % q) = ∑ k ∈ Finset.range n, f n % f k
  rw [← hmap, Finset.sum_map, Finset.sum_range_succ, Nat.mod_self, add_zero]

theorem prime_remainders_assemble
    (small : ∀ p : ℕ, p.Prime → 17 ≤ p → p < 65536 → p < ∑ q ∈ p.primesLE, p % q)
    (large : ∀ (p : ℕ) (S : Finset ℕ), 65536 ≤ p →
      (∀ q ∈ S, p / 3 < q ∧ q ≤ p) →
      3 * √(p : ℝ) + 1 < (S.card : ℝ) → p < ∑ q ∈ S, p % q) :
    ∀ n : ℕ, 5 < n → Nat.nth Nat.Prime n <
      ∑ k ∈ range n, Nat.nth Nat.Prime n % Nat.nth Nat.Prime k := by
  intro n hn
  rw [← prime_remainders_nth]
  let p := Nat.nth Nat.Prime n
  change p < ∑ q ∈ p.primesLE, p % q
  have hprime : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
  have hcnt : Nat.count Nat.Prime 17 = 6 := by decide +kernel
  have h17 : Nat.nth Nat.Prime 6 = 17 := by
    simpa only [hcnt] using Nat.nth_count (show Nat.Prime 17 by decide +kernel)
  have hp17 : 17 ≤ p := h17 ▸ (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
  by_cases hp : p < 65536
  · exact small p hprime hp17 hp
  have hpbig : 65536 ≤ p := by omega
  let S := p.primesLE \ Nat.primesLE (p / 3)
  have hfloor : ⌊(p : ℝ) / 3⌋₊ = p / 3 := by
    simpa using Nat.floor_div_natCast (p : ℝ) 3
  have hm : 3 * √(p : ℝ) + 1 < (S.card : ℝ) := by
    simpa only [hfloor, S] using prime_remainders_many p hpbig
  have hS (q : ℕ) (hq : q ∈ S) : p / 3 < q ∧ q ≤ p := by
    obtain ⟨hup, hnot⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqp, hqpr⟩ := Nat.mem_primesLE.mp hup
    exact ⟨lt_of_not_ge (fun hle => hnot (Nat.mem_primesLE.mpr ⟨hle, hqpr⟩)), hqp⟩
  exact (large p S hpbig hS hm).trans_le
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.zero_le _))


open Finset
open scoped BigOperators

namespace PrimeRemainderBlocks

def valid (lo : ℕ) : List (ℕ × List ℕ) → ℕ → Bool
  | [], hi => decide (hi < lo)
  | (u, qs) :: tl, hi =>
    (decide (qs.toFinset.card = 5) &&
      qs.all (fun q => decide (q.Prime ∧ u < 2*q ∧ 4*q ≤ 3*lo))) &&
      valid (u+1) tl hi

theorem blockBound (lo u p : ℕ) (qs : Finset ℕ)
    (hcard : qs.card = 5)
    (hqs : ∀ q ∈ qs, q.Prime ∧ u < 2*q ∧ 4*q ≤ 3*lo)
    (hlo : lo ≤ p) (hup : p ≤ u) (hp : 0 < p) :
    p < ∑ q ∈ p.primesLE, p % q := by
  have hsub : qs ⊆ p.primesLE := by
    intro q hq
    have h := hqs q hq
    exact Nat.mem_primesLE.mpr ⟨by omega, h.1⟩
  have hmod (q : ℕ) (hq : q ∈ qs) : p ≤ 4 * (p % q) := by
    have h := hqs q hq
    have hqle : q ≤ p := by omega
    have hs : p - q < q := by omega
    rw [Nat.mod_eq_sub_mod hqle, Nat.mod_eq_of_lt hs]
    omega
  have hsum : 5*p ≤ 4 * ∑ q ∈ qs, p % q := by
    rw [Finset.mul_sum]
    simpa [hcard] using Finset.sum_le_sum hmod
  have hlt : p < ∑ q ∈ qs, p % q := by omega
  exact hlt.trans_le (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))

theorem valid_sound (lo hi : ℕ) (bs : List (ℕ × List ℕ))
    (h : valid lo bs hi = true) (p : ℕ) (hp : 0 < p) (hlo : lo ≤ p) (hhi : p ≤ hi) :
    p < ∑ q ∈ p.primesLE, p % q := by
  induction bs generalizing lo with
  | nil => simp [valid] at h; omega
  | cons block bs ih =>
    obtain ⟨u, qs⟩ := block
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hu : p ≤ u
    · apply blockBound lo u p qs.toFinset h.1.1 _ hlo hu hp
      intro q hq
      have hq' := List.mem_toFinset.mp hq
      exact of_decide_eq_true (List.all_eq_true.mp h.1.2 q hq')
    · exact ih (u+1) h.2 (by omega)

def blocks : List (ℕ × List ℕ) := [
  (307, [157, 163, 167, 173, 179]),
  (369, [191, 193, 197, 199, 211]),
  (444, [223, 227, 229, 233, 239]),
  (534, [269, 271, 277, 281, 283]),
  (642, [331, 337, 347, 349, 353]),
  (771, [389, 397, 401, 409, 419]),
  (926, [467, 479, 487, 491, 499]),
  (1112, [557, 563, 569, 571, 577]),
  (1335, [673, 677, 683, 691, 701]),
  (1603, [809, 811, 821, 823, 827]),
  (1924, [967, 971, 977, 983, 991]),
  (2310, [1163, 1171, 1181, 1187, 1193]),
  (2773, [1399, 1409, 1423, 1427, 1429]),
  (3328, [1667, 1669, 1693, 1697, 1699]),
  (3994, [1999, 2003, 2011, 2017, 2027]),
  (4794, [2399, 2411, 2417, 2423, 2437]),
  (5754, [2879, 2887, 2897, 2903, 2909]),
  (6906, [3457, 3461, 3463, 3467, 3469]),
  (8288, [4153, 4157, 4159, 4177, 4201]),
  (9946, [4987, 4993, 4999, 5003, 5009]),
  (11936, [5981, 5987, 6007, 6011, 6029]),
  (14324, [7177, 7187, 7193, 7207, 7211]),
  (17190, [8597, 8599, 8609, 8623, 8627]),
  (20629, [10321, 10331, 10333, 10337, 10343]),
  (24756, [12379, 12391, 12401, 12409, 12413]),
  (29708, [14867, 14869, 14879, 14887, 14891]),
  (35650, [17827, 17837, 17839, 17851, 17863]),
  (42781, [21391, 21397, 21401, 21407, 21419]),
  (51338, [25673, 25679, 25693, 25703, 25717]),
  (61606, [30809, 30817, 30829, 30839, 30841]),
  (65535, [32771, 32779, 32783, 32789, 32797])
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem blocks_checked : valid 256 blocks 65535 = true := by
  simp only [blocks, valid, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    List.toFinset_cons, List.toFinset_nil]
  norm_num

theorem finiteBlocks (p : ℕ) (hlo : 256 ≤ p) (hhi : p < 65536) :
    p < ∑ q ∈ p.primesLE, p % q :=
  valid_sound 256 65535 blocks blocks_checked p (by omega) hlo (by omega)

end PrimeRemainderBlocks


open Finset
open scoped BigOperators

namespace PrimeRemainderSmallData

def rowValid (row : ℕ × List ℕ) : Bool :=
  row.2.all (fun q => decide (q ≤ row.1 ∧ q.Prime)) &&
    decide (row.1 < ∑ q ∈ row.2.toFinset, row.1 % q)

def rows : List (ℕ × List ℕ) := [
  (17, [11, 13, 7, 5, 3, 2]),
  (19, [11, 13, 7, 5]),
  (23, [13, 17, 19, 5, 7]),
  (29, [17, 19, 11, 23]),
  (31, [17, 19, 11]),
  (37, [19, 23, 13]),
  (41, [23, 29, 31, 11]),
  (43, [23, 29, 31]),
  (47, [29, 31, 17, 37]),
  (53, [29, 31, 37]),
  (59, [31, 37, 41]),
  (61, [31, 37, 41]),
  (67, [37, 41, 43]),
  (71, [37, 41, 43]),
  (73, [37, 41, 43]),
  (79, [41, 43, 47]),
  (83, [43, 47, 53]),
  (89, [47, 53, 59]),
  (97, [53, 59, 61]),
  (101, [53, 59, 61]),
  (103, [53, 59, 61]),
  (107, [59, 61, 67]),
  (109, [59, 61, 67]),
  (113, [59, 61, 67]),
  (127, [67, 71, 73]),
  (131, [67, 71, 73]),
  (137, [71, 73, 79]),
  (139, [71, 73, 79]),
  (149, [79, 83, 89]),
  (151, [79, 83, 89]),
  (157, [79, 83, 89]),
  (163, [83, 89, 97]),
  (167, [89, 97, 101]),
  (173, [89, 97, 101]),
  (179, [97, 101, 103]),
  (181, [97, 101, 103]),
  (191, [97, 101, 103]),
  (193, [97, 101, 103]),
  (197, [101, 103, 107]),
  (199, [101, 103, 107]),
  (211, [107, 109, 113]),
  (223, [113, 127, 131]),
  (227, [127, 131, 137]),
  (229, [127, 131, 137]),
  (233, [127, 131, 137]),
  (239, [127, 131, 137]),
  (241, [127, 131, 137]),
  (251, [127, 131, 137])
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rowsValid : rows.all rowValid = true := by
  simp only [rows, rowValid, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    List.toFinset_cons, List.toFinset_nil]
  norm_num [Finset.sum_insert]

set_option maxHeartbeats 0 in
theorem rowsCover (p : ℕ) (hp : p.Prime) (hlo : 17 ≤ p) (hhi : p < 256) :
    p ∈ rows.map Prod.fst := by
  interval_cases p <;> (try norm_num at hp) <;> norm_num [rows]

end PrimeRemainderSmallData
open PrimeRemainderSmallData

theorem prime_remainders_small (p : ℕ) (hp : p.Prime) (hlo : 17 ≤ p) (hhi : p < 256) :
    p < ∑ q ∈ p.primesLE, p % q := by
  obtain ⟨⟨r, qs⟩, hm, he⟩ := List.mem_map.mp (rowsCover p hp hlo hhi)
  change r = p at he
  subst r
  have hv := List.all_eq_true.mp rowsValid (p, qs) hm
  simp only [rowValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hsub : qs.toFinset ⊆ p.primesLE := by
    intro q hq
    exact Nat.mem_primesLE.mpr
      (of_decide_eq_true (List.all_eq_true.mp hv.1 q (List.mem_toFinset.mp hq)))
  exact hv.2.trans_le (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))


open Finset
open scoped BigOperators

theorem prime_remainders_count_large
    (p : ℕ) (hp : 65536 ≤ p) (S : Finset ℕ)
    (hS : ∀ q ∈ S, p / 3 < q ∧ q ≤ p)
    (hcard : 3 * Real.sqrt (p : ℝ) + 1 < (S.card : ℝ)) :
    p < ∑ q ∈ S, p % q := by
  let u := Nat.sqrt p
  let t := 3 * u / 4
  let B := S.filter (fun q => p % q < t)
  have hu : 256 ≤ u := by
    apply (Nat.le_sqrt).2
    nlinarith
  have hroot : p < (u + 1) * (u + 1) := by
    simpa [u, Nat.succ_eq_add_one] using (Nat.lt_succ_sqrt p)
  have hu_sq : u * u ≤ p := by
    simpa [u] using Nat.sqrt_le p
  have hu_real : (u : ℝ) ≤ Real.sqrt (p : ℝ) := by
    calc
      (u : ℝ) = Real.sqrt ((u : ℝ) ^ 2) := by
        rw [Real.sqrt_sq (Nat.cast_nonneg _)]
      _ ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt (by
        have hcast : (u : ℝ) * u ≤ p := by exact_mod_cast hu_sq
        nlinarith [hcast])
  have hcard_nat : 3 * u + 2 ≤ S.card := by
    have h' : ((3 * u + 1 : ℕ) : ℝ) < (S.card : ℝ) := by
      norm_num at hcard ⊢
      nlinarith [hu_real]
    exact_mod_cast h'
  have ht_lo : 3 * u < 4 * (t + 1) := by
    dsimp [t]
    omega
  have ht_hi : 4 * t ≤ 3 * u := by
    dsimp [t]
    omega
  have hB : B.card ≤ 2 * t := by
    let f : ℕ → ℕ × ℕ := fun q => (p / q - 1, p % q)
    let target : Finset (ℕ × ℕ) := Finset.range 2 ×ˢ Finset.range t
    have hsub : B ⊆ S := by
      intro q hq
      exact (Finset.mem_filter.mp hq).1
    have hcardle : B.card ≤ target.card := by
      apply Finset.card_le_card_of_injOn f (s := B) (t := target)
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqS, hrem⟩
        rcases hS q hqS with ⟨hqlo, hqhi⟩
        have hqpos : 0 < q := by omega
        have hpt : p < 3 * q := by omega
        have hdivpos : 0 < p / q := Nat.div_pos hqhi hqpos
        have hdivlt : p / q < 3 := (Nat.div_lt_iff_lt_mul hqpos).2 hpt
        change f q ∈ target
        simp only [f, target, Finset.mem_product, Finset.mem_range]
        constructor
        · omega
        · exact hrem
      · intro q hq r hr heq
        have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
        have hrS : r ∈ S := (Finset.mem_filter.mp hr).1
        rcases hS q hqS with ⟨hqlo, hqhi⟩
        rcases hS r hrS with ⟨hrlo, hrhi⟩
        have hqpos : 0 < q := by omega
        have hrpos : 0 < r := by omega
        have hqpt : p < 3 * q := by omega
        have hrpt : p < 3 * r := by omega
        have hqdivpos : 0 < p / q := Nat.div_pos hqhi hqpos
        have _hrdivpos : 0 < p / r := Nat.div_pos hrhi hrpos
        have hfirst : p / q - 1 = p / r - 1 := congrArg Prod.fst heq
        have hdiv : p / q = p / r := by omega
        have hrem : p % q = p % r := congrArg Prod.snd heq
        have hqdecomp := Nat.div_add_mod' p q
        have hrdecomp := Nat.div_add_mod' p r
        rw [← hdiv, ← hrem] at hrdecomp
        have hmul : (p / q) * q = (p / q) * r := by
          exact Nat.add_right_cancel (hqdecomp.trans hrdecomp.symm)
        exact Nat.mul_left_cancel hqdivpos hmul
    simpa [target] using hcardle
  have hgood : p < t * (3 * u + 2 - 2 * t) := by
    have hsub : 2 * t ≤ 3 * u + 2 := by omega
    have htloR : (3 : ℝ) * u < 4 * ((t : ℝ) + 1) := by
      exact_mod_cast ht_lo
    have htloR' : 3 * (u : ℝ) / 4 - 1 ≤ (t : ℝ) := by linarith
    have hthiR : 4 * (t : ℝ) ≤ 3 * (u : ℝ) := by
      exact_mod_cast ht_hi
    have hsecR : 3 * (u : ℝ) / 2 + 2 ≤ ((3 * u + 2 - 2 * t : ℕ) : ℝ) := by
      have hsubcast : ((3 * u + 2 - 2 * t : ℕ) : ℝ) =
          (3 * (u : ℝ) + 2) - 2 * (t : ℝ) := by
        rw [Nat.cast_sub hsub]
        norm_num
      rw [hsubcast]
      linarith [hthiR]
    have htlopos : 0 ≤ 3 * (u : ℝ) / 4 - 1 := by
      have : (256 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
      linarith
    have hseclopos : 0 ≤ 3 * (u : ℝ) / 2 + 2 := by positivity
    have hprod :
        (3 * (u : ℝ) / 4 - 1) * (3 * (u : ℝ) / 2 + 2) ≤
          (t : ℝ) * ((3 * u + 2 - 2 * t : ℕ) : ℝ) := by
      calc
        (3 * (u : ℝ) / 4 - 1) * (3 * (u : ℝ) / 2 + 2) ≤
            (t : ℝ) * (3 * (u : ℝ) / 2 + 2) :=
          mul_le_mul_of_nonneg_right htloR' hseclopos
        _ ≤ (t : ℝ) * ((3 * u + 2 - 2 * t : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hsecR (by positivity)
    have hpoly :
        (u + 1 : ℝ) * (u + 1) <
          (3 * (u : ℝ) / 4 - 1) * (3 * (u : ℝ) / 2 + 2) := by
      have huR : (256 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
      nlinarith [sq_nonneg ((u : ℝ) - 8)]
    have hnat :
        ((p : ℝ)) < (t : ℝ) * ((3 * u + 2 - 2 * t : ℕ) : ℝ) := by
      have hrootR : (p : ℝ) < (u + 1 : ℝ) * (u + 1) := by exact_mod_cast hroot
      linarith [hpoly, hprod]
    exact_mod_cast hnat
  have hgoodcard : 3 * u + 2 - 2 * t ≤ S.card - B.card := by omega
  have hcardGood : (S \ B).card = S.card - B.card :=
    Finset.card_sdiff_of_subset (by
      intro q hq
      exact (Finset.mem_filter.mp hq).1)
  have hsumB : (∑ q ∈ B, p % q) + (∑ q ∈ S \ B, p % q) = ∑ q ∈ S, p % q := by
    simpa [add_comm] using (Finset.sum_sdiff (s₁ := B) (s₂ := S)
      (f := fun q => p % q) (by
        intro q hq
        exact (Finset.mem_filter.mp hq).1))
  have hsumGood : t * (S.card - B.card) ≤ ∑ q ∈ S \ B, p % q := by
    have hpoint : ∀ q ∈ S \ B, t ≤ p % q := by
      intro q hq
      have hqS : q ∈ S := (Finset.mem_sdiff.mp hq).1
      have hnot : q ∉ B := (Finset.mem_sdiff.mp hq).2
      have : ¬ p % q < t := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨hqS, h⟩)
      omega
    calc
      t * (S.card - B.card) = ∑ _q ∈ S \ B, t := by
        simp [mul_comm, hcardGood]
      _ ≤ ∑ q ∈ S \ B, p % q := by
        apply Finset.sum_le_sum
        intro q hq
        exact hpoint q hq
  have hsumlower : t * (S.card - B.card) ≤ ∑ q ∈ S, p % q := by
    exact hsumGood.trans (by
      rw [← hsumB]
      exact Nat.le_add_left _ _)
  have hgood' : p < t * (S.card - B.card) := hgood.trans_le
    (Nat.mul_le_mul_left t hgoodcard)
  exact hgood'.trans_le hsumlower


theorem OMA.solution : type_of% @OMA.S_oeis_a033955.main := by
  apply prime_remainders_assemble
  · intro p hp hlo hhi
    by_cases h : p < 256
    · exact prime_remainders_small p hp hlo h
    · exact PrimeRemainderBlocks.finiteBlocks p (by omega) hhi
  · intro p S hp hS hc
    exact prime_remainders_count_large p hp S hS hc
