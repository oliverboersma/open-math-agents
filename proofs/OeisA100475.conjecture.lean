import FormalConjectures.OEIS.«100475»
import Mathlib

/-!
Adapted from Daniel Veljjanoski’s Palomar proof of the reverse-prime theorem.
Source: https://github.com/veljjanoski/oeis100475-palomar/tree/0968200356e449a24a023264821d4ea966091cf0
The standalone proof is consolidated into one file and uses the catalog definitions directly.
Submission: @rleshner. Original source is licensed under Apache-2.0 (included below).
-/

open Nat Function

namespace OeisA100475Proof

open OeisA100475

/-- The step map of the recurrence; `f 0 = 0` only to make it total. -/
noncomputable def f (y : ℕ) : ℕ :=
  if y = 0 then 0 else reverseDigits (Nat.nth Nat.Prime (y - 1))

lemma aStartAt_eq_iterate (x n : ℕ) : aStartAt x n = f^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', ← ih]; rfl

/-- Number of decimal digits. -/
def D (n : ℕ) : ℕ := (Nat.digits 10 n).length

lemma prime_mod_ten_ne_zero {p : ℕ} (hp : p.Prime) : p % 10 ≠ 0 := by
  intro h
  have h10 : 10 ∣ p := Nat.dvd_of_mod_eq_zero h
  have h2 : 2 ∣ p := dvd_trans ⟨5, rfl⟩ h10
  have h5 : 5 ∣ p := dvd_trans ⟨2, rfl⟩ h10
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;>
    rcases hp.eq_one_or_self_of_dvd 5 h5 with h' | h' <;> omega

lemma digits_reverseDigits {p : ℕ} (hp0 : p ≠ 0) (hp : p % 10 ≠ 0) :
    Nat.digits 10 (reverseDigits p) = (Nat.digits 10 p).reverse := by
  unfold reverseDigits
  refine Nat.digits_ofDigits 10 (by norm_num) _ ?_ ?_
  · intro l hl
    exact Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hl)
  · intro h
    have hd : Nat.digits 10 p = p % 10 :: Nat.digits 10 (p / 10) :=
      Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hp0)
    simpa [List.getLast_reverse, hd] using hp

lemma length_digits_mono {m n : ℕ} (h : m ≤ n) : D m ≤ D n := by
  unfold D
  rw [Nat.digits_length_le_iff (by norm_num)]
  exact lt_of_le_of_lt h (Nat.lt_base_pow_length_digits (by norm_num))

lemma D_f {y : ℕ} (hy : y ≠ 0) : D (f y) = D (Nat.nth Nat.Prime (y - 1)) := by
  have hp := Nat.prime_nth_prime (y - 1)
  simp only [f, hy, ite_false, D]
  rw [digits_reverseDigits hp.ne_zero (prime_mod_ten_ne_zero hp), List.length_reverse]

lemma f_ne_zero {y : ℕ} (hy : y ≠ 0) : f y ≠ 0 := by
  have hp := Nat.prime_nth_prime (y - 1)
  rw [← Nat.digits_ne_nil_iff_ne_zero (b := 10)]
  simp only [f, hy, ite_false]
  rw [digits_reverseDigits hp.ne_zero (prime_mod_ten_ne_zero hp)]
  intro h
  exact (Nat.digits_ne_nil_iff_ne_zero.mpr hp.ne_zero) (List.reverse_eq_nil_iff.mp h)

lemma lt_nth_prime (y : ℕ) : y < Nat.nth Nat.Prime (y - 1) := by
  have := Nat.add_two_le_nth_prime (y - 1)
  omega

lemma D_le_D_f {y : ℕ} (hy : y ≠ 0) : D y ≤ D (f y) := by
  rw [D_f hy]
  exact length_digits_mono (lt_nth_prime y).le

lemma iterate_ne_zero {y : ℕ} (hy : y ≠ 0) (k : ℕ) : f^[k] y ≠ 0 := by
  induction k with
  | zero => simpa
  | succ k ih => rw [iterate_succ_apply']; exact f_ne_zero ih

lemma D_le_D_iterate {y : ℕ} (hy : y ≠ 0) (k : ℕ) : D y ≤ D (f^[k] y) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply']; exact ih.trans (D_le_D_f (iterate_ne_zero hy k))

lemma D_iterate_le_D_iterate {y : ℕ} (hy : y ≠ 0) {j k : ℕ} (h : j ≤ k) :
    D (f^[j] y) ≤ D (f^[k] y) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, iterate_add_apply]
  exact D_le_D_iterate (iterate_ne_zero hy j) m

/-- On a cycle (`f^[P] w = w`, `P > 0`) the digit count is constant. -/
lemma D_iterate_eq_of_cycle {w P : ℕ} (hw : w ≠ 0) (hP : 0 < P) (hcyc : f^[P] w = w) (k : ℕ) :
    D (f^[k] w) = D w := by
  -- reduce `k` modulo `P`
  have hmul : ∀ q, f^[P * q] w = w := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, iterate_add_apply, hcyc, ih]
  have hk : f^[k] w = f^[k % P] w := by
    conv_lhs => rw [← Nat.mod_add_div k P, iterate_add_apply, hmul]
  rw [hk]
  apply le_antisymm
  · have h1 : D (f^[k % P] w) ≤ D (f^[P] w) :=
      D_iterate_le_D_iterate hw (Nat.mod_lt k hP).le
    rwa [hcyc] at h1
  · exact D_le_D_iterate hw _

/- ## Sieve bounds on the prime-counting function (Legendre's recursion) -/
/-- The primes up to `300` in descending order, so that the head is the largest remaining prime. -/
def primesDesc : List ℕ :=
  [293, 283, 281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211, 199, 197, 193,
   191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89,
   83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 5, 3, 2]

/-- Legendre's `φ` along a descending prime list, with the pruning `φ(x) = 1` for `1 ≤ x < p`.
Written with `List.rec` directly so that the kernel evaluates it efficiently. -/
def phiList (ps : List ℕ) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun x => x)
    (fun p _ ih x => if x < p then (if x = 0 then 0 else 1) else ih x - ih (x / p)) ps x

theorem phiList_nil (x : ℕ) : phiList [] x = x := rfl

theorem phiList_cons (p : ℕ) (ps : List ℕ) (x : ℕ) :
    phiList (p :: ps) x = (if x < p then (if x = 0 then 0 else 1)
      else phiList ps x - phiList ps (x / p)) := rfl

/-- The numbers in `[1, x]` divisible by no element of `ps`. -/
def sieveSet (ps : List ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun n => ∀ p ∈ ps, ¬ p ∣ n)

lemma mem_sieveSet {ps : List ℕ} {x n : ℕ} :
    n ∈ sieveSet ps x ↔ (1 ≤ n ∧ n ≤ x) ∧ ∀ p ∈ ps, ¬ p ∣ n := by
  simp [sieveSet]

lemma sieveSet_nil (x : ℕ) : sieveSet [] x = Finset.Icc 1 x := by
  ext n; simp [sieveSet]

/-- Legendre's recursion step. -/
lemma card_sieveSet_cons {p : ℕ} {ps : List ℕ} (hp : p.Prime) (hps : ∀ q ∈ ps, q.Prime ∧ q ≠ p)
    (x : ℕ) :
    (sieveSet (p :: ps) x).card = (sieveSet ps x).card - (sieveSet ps (x / p)).card := by
  have hsplit : sieveSet (p :: ps) x = (sieveSet ps x).filter (fun n => ¬ p ∣ n) := by
    ext n; simp [sieveSet, List.mem_cons]; tauto
  have himage : (sieveSet ps x).filter (fun n => p ∣ n) = (sieveSet ps (x / p)).image (p * ·) := by
    ext n
    simp only [Finset.mem_filter, mem_sieveSet, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨h1, hx⟩, hq⟩, ⟨m, rfl⟩⟩
      refine ⟨m, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp at h1
        · exact hm
      · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [mul_comm]; exact hx)
      · intro q hq' hdvd
        exact hq q hq' (dvd_mul_of_dvd_right hdvd p)
    · rintro ⟨m, ⟨⟨h1, hm⟩, hq⟩, rfl⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p m⟩
      · exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne_zero (by omega))
      · rw [mul_comm]; exact (Nat.le_div_iff_mul_le hp.pos).1 hm
      · intro q hq' hdvd
        obtain ⟨hqp, hqne⟩ := hps q hq'
        rcases (Nat.Prime.dvd_mul hqp).1 hdvd with h | h
        · exact hqne ((Nat.prime_dvd_prime_iff_eq hqp hp).1 h)
        · exact hq q hq' h
  have hcard := Finset.card_filter_add_card_filter_not (s := sieveSet ps x) (fun n => p ∣ n)
  rw [himage, Finset.card_image_of_injective _ (mul_right_injective₀ hp.ne_zero)] at hcard
  rw [hsplit]
  omega

/-- Pruning: below `p`, only `1` survives the sieve by all primes less than `p`. -/
lemma card_sieveSet_of_lt {p : ℕ} {ps : List ℕ} (hps : ∀ q ∈ ps, q.Prime)
    (hcomplete : ∀ q, q.Prime → q < p → q ∈ ps) {x : ℕ} (hx : x < p) :
    (sieveSet (p :: ps) x).card = if x = 0 then 0 else 1 := by
  split_ifs with h0
  · subst h0; simp [sieveSet]
  · have : sieveSet (p :: ps) x = {1} := by
      ext n
      simp only [mem_sieveSet, Finset.mem_singleton, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨h1, hnx⟩, -, hq⟩
        by_contra hne
        have hn1 : n ≠ 1 := hne
        have hmf := Nat.minFac_prime hn1
        have hlt : Nat.minFac n < p := lt_of_le_of_lt (Nat.minFac_le (by omega)) (by omega)
        exact hq _ (hcomplete _ hmf hlt) (Nat.minFac_dvd n)
      · rintro rfl
        refine ⟨⟨le_rfl, by omega⟩, ?_, ?_⟩
        · intro h
          have := Nat.le_of_dvd one_pos h
          omega
        · intro q hq; exact Nat.Prime.not_dvd_one (hps q hq)
    rw [this, Finset.card_singleton]

/-- Trial-division primality test; the kernel can evaluate it for small numbers. -/
def isPrimeTD (q : ℕ) : Bool := 2 ≤ q && (List.range q).all (fun d => d < 2 || q % d != 0)

lemma isPrimeTD_iff (q : ℕ) : isPrimeTD q = true ↔ q.Prime := by
  rw [Nat.prime_def_lt]
  simp only [isPrimeTD, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hmq hdvd => ?_⟩
    rcases h m hmq with h' | h'
    · have hm : m = 0 ∨ m = 1 := by omega
      rcases hm with rfl | rfl
      · rw [zero_dvd_iff] at hdvd; omega
      · rfl
    · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) h'
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d hd => ?_⟩
    by_cases hd2 : d < 2
    · exact Or.inl hd2
    · exact Or.inr fun h0 => by have := h d hd (Nat.dvd_of_mod_eq_zero h0); omega

/-- The hypotheses of Legendre's recursion along a list: descending primes, each suffix complete. -/
def GoodList : List ℕ → Prop
  | [] => True
  | p :: ps => p.Prime ∧ (∀ q ∈ ps, q.Prime ∧ q ≠ p) ∧ (∀ q, q.Prime → q < p → q ∈ ps) ∧ GoodList ps

lemma goodList_of_sorted : ∀ (l : List ℕ), l.Pairwise (· > ·) → (∀ q ∈ l, q.Prime) →
    (∀ p ∈ l, ∀ q, q.Prime → q < p → q ∈ l) → GoodList l
  | [], _, _, _ => trivial
  | p :: ps, hsort, hprime, hcomp => by
    rw [List.pairwise_cons] at hsort
    refine ⟨hprime p (List.mem_cons_self), fun q hq => ⟨hprime q (List.mem_cons_of_mem p hq),
      (hsort.1 q hq).ne⟩, fun q hq hqp => ?_, ?_⟩
    · rcases List.mem_cons.1 (hcomp p List.mem_cons_self q hq hqp) with rfl | h
      · exact absurd hqp (lt_irrefl _)
      · exact h
    · refine goodList_of_sorted ps hsort.2 (fun q hq => hprime q (List.mem_cons_of_mem p hq))
        fun p' hp' q hq hqp' => ?_
      have hp'p : p' < p := hsort.1 p' hp'
      rcases List.mem_cons.1 (hcomp p' (List.mem_cons_of_mem p hp') q hq hqp') with rfl | h
      · exact absurd (hqp'.trans hp'p) (lt_irrefl _)
      · exact h

lemma phiList_eq_card : ∀ {ps : List ℕ}, GoodList ps → ∀ x, phiList ps x = (sieveSet ps x).card
  | [], _, x => by simp [phiList_nil, sieveSet_nil]
  | p :: ps, ⟨hp, hps, hcomp, hgood⟩, x => by
    rw [phiList_cons]
    by_cases hx : x < p
    · rw [if_pos hx, card_sieveSet_of_lt (fun q hq => (hps q hq).1) hcomp hx]
    · rw [if_neg hx, card_sieveSet_cons hp hps x, phiList_eq_card hgood x,
        phiList_eq_card hgood (x / p)]

lemma goodList_primesDesc : GoodList primesDesc := by
  have hsort : primesDesc.Pairwise (· > ·) := by decide +kernel
  have hprime : ∀ q ∈ primesDesc, isPrimeTD q = true := by decide +kernel
  have hcomp : ∀ q < 294, isPrimeTD q = true → q ∈ primesDesc := by decide +kernel
  have hle : ∀ p ∈ primesDesc, p ≤ 293 := by decide +kernel
  refine goodList_of_sorted _ hsort (fun q hq => (isPrimeTD_iff q).1 (hprime q hq)) ?_
  intro p hp q hq hqp
  exact hcomp q (by have := hle p hp; omega) ((isPrimeTD_iff q).2 hq)

/-- Every prime below `N` is either one of the listed small primes or survives the sieve. -/
lemma primeCounting'_le_sieve (N : ℕ) (hN : 2 ≤ N) :
    Nat.primeCounting' N ≤ primesDesc.length + ((sieveSet primesDesc (N - 1)).card - 1) := by
  have hcomp : ∀ q, q.Prime → q ≤ 293 → q ∈ primesDesc := by
    have h : ∀ q < 294, isPrimeTD q = true → q ∈ primesDesc := by decide +kernel
    intro q hq hq'
    exact h q (by omega) ((isPrimeTD_iff q).2 hq)
  have hprime : ∀ q ∈ primesDesc, q.Prime := by
    have h : ∀ q ∈ primesDesc, isPrimeTD q = true := by decide +kernel
    intro q hq; exact (isPrimeTD_iff q).1 (h q hq)
  have hle : ∀ p ∈ primesDesc, p ≤ 293 := by decide +kernel
  unfold Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  set S := (Finset.range N).filter Nat.Prime with hS
  have hsplit : S = S.filter (fun q => q ≤ 293) ∪ S.filter (fun q => ¬ q ≤ 293) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hq : q ≤ 293 <;> simp [hq]
  rw [hsplit]
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
  · refine (Finset.card_le_card (fun q hq => ?_)).trans (List.toFinset_card_le primesDesc)
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hq
    exact List.mem_toFinset.2 (hcomp q hq.1.2 hq.2)
  · have h1 : (1 : ℕ) ∈ sieveSet primesDesc (N - 1) := by
      rw [mem_sieveSet]
      exact ⟨⟨le_rfl, by omega⟩, fun p hp => Nat.Prime.not_dvd_one (hprime p hp)⟩
    rw [← Finset.card_erase_of_mem h1]
    refine Finset.card_le_card fun q hq => ?_
    simp only [hS, Finset.mem_filter, Finset.mem_range, not_le] at hq
    obtain ⟨⟨hqN, hq⟩, h293⟩ := hq
    rw [Finset.mem_erase, mem_sieveSet]
    refine ⟨hq.one_lt.ne', ⟨hq.one_le, by omega⟩, fun p hp hdvd => ?_⟩
    have hp' := hprime p hp
    have := (Nat.prime_dvd_prime_iff_eq hp' hq).1 hdvd
    have := hle p hp
    omega

theorem primeCounting'_1e5 : Nat.primeCounting' 100000 < 10000 := by
  have h := primeCounting'_le_sieve 100000 (by norm_num)
  have hphi : phiList primesDesc 99999 = 9540 := by decide +kernel
  rw [← phiList_eq_card goodList_primesDesc] at h
  simp only [show (100000 : ℕ) - 1 = 99999 from rfl, hphi,
    show primesDesc.length = 62 from rfl] at h
  omega

theorem primeCounting'_1e6 : Nat.primeCounting' 1000000 < 100000 := by
  have h := primeCounting'_le_sieve 1000000 (by norm_num)
  have hphi : phiList primesDesc 999999 = 94794 := by decide +kernel
  rw [← phiList_eq_card goodList_primesDesc] at h
  simp only [show (1000000 : ℕ) - 1 = 999999 from rfl, hphi,
    show primesDesc.length = 62 from rfl] at h
  omega

end OeisA100475Proof

open Nat Function

namespace OeisA100475Proof

open OeisA100475

def S (k : ℕ) : List ℕ := primesDesc.drop k

theorem S_0 : S 0 = 293 :: S 1 := rfl
theorem S_1 : S 1 = 283 :: S 2 := rfl
theorem S_2 : S 2 = 281 :: S 3 := rfl
theorem S_3 : S 3 = 277 :: S 4 := rfl
theorem S_4 : S 4 = 271 :: S 5 := rfl
theorem S_5 : S 5 = 269 :: S 6 := rfl
theorem S_6 : S 6 = 263 :: S 7 := rfl
theorem S_7 : S 7 = 257 :: S 8 := rfl
theorem S_8 : S 8 = 251 :: S 9 := rfl
theorem S_9 : S 9 = 241 :: S 10 := rfl
theorem S_10 : S 10 = 239 :: S 11 := rfl
theorem S_11 : S 11 = 233 :: S 12 := rfl
theorem S_12 : S 12 = 229 :: S 13 := rfl
theorem S_13 : S 13 = 227 :: S 14 := rfl
theorem S_14 : S 14 = 223 :: S 15 := rfl
theorem S_15 : S 15 = 211 :: S 16 := rfl
theorem S_16 : S 16 = 199 :: S 17 := rfl
theorem S_17 : S 17 = 197 :: S 18 := rfl
theorem S_18 : S 18 = 193 :: S 19 := rfl
theorem S_19 : S 19 = 191 :: S 20 := rfl
theorem S_20 : S 20 = 181 :: S 21 := rfl
theorem S_21 : S 21 = 179 :: S 22 := rfl
theorem S_22 : S 22 = 173 :: S 23 := rfl
theorem S_23 : S 23 = 167 :: S 24 := rfl
theorem S_24 : S 24 = 163 :: S 25 := rfl
theorem S_25 : S 25 = 157 :: S 26 := rfl
theorem S_26 : S 26 = 151 :: S 27 := rfl
theorem S_27 : S 27 = 149 :: S 28 := rfl
theorem S_28 : S 28 = 139 :: S 29 := rfl
theorem S_29 : S 29 = 137 :: S 30 := rfl
theorem S_30 : S 30 = 131 :: S 31 := rfl
theorem S_31 : S 31 = 127 :: S 32 := rfl
theorem S_32 : S 32 = 113 :: S 33 := rfl
theorem S_33 : S 33 = 109 :: S 34 := rfl
theorem S_34 : S 34 = 107 :: S 35 := rfl
theorem S_35 : S 35 = 103 :: S 36 := rfl
theorem S_36 : S 36 = 101 :: S 37 := rfl
theorem S_37 : S 37 = 97 :: S 38 := rfl
theorem S_38 : S 38 = 89 :: S 39 := rfl
theorem S_39 : S 39 = 83 :: S 40 := rfl
theorem S_40 : S 40 = 79 :: S 41 := rfl
theorem S_41 : S 41 = 73 :: S 42 := rfl
theorem S_42 : S 42 = 71 :: S 43 := rfl
theorem S_43 : S 43 = 67 :: S 44 := rfl
theorem S_44 : S 44 = 61 :: S 45 := rfl
theorem S_45 : S 45 = 59 :: S 46 := rfl
theorem S_46 : S 46 = 53 :: S 47 := rfl
theorem S_47 : S 47 = 47 :: S 48 := rfl
theorem S_48 : S 48 = 43 :: S 49 := rfl
theorem S_49 : S 49 = 41 :: S 50 := rfl
theorem S_50 : S 50 = 37 :: S 51 := rfl
theorem S_51 : S 51 = 31 :: S 52 := rfl
theorem S_52 : S 52 = 29 :: S 53 := rfl
theorem S_53 : S 53 = 23 :: S 54 := rfl
theorem S_54 : S 54 = 19 :: S 55 := rfl
theorem S_55 : S 55 = 17 :: S 56 := rfl
theorem S_56 : S 56 = 13 :: S 57 := rfl
theorem S_57 : S 57 = 11 :: S 58 := rfl
theorem S_58 : S 58 = 7 :: S 59 := rfl
theorem S_59 : S 59 = 5 :: S 60 := rfl
theorem S_60 : S 60 = 3 :: S 61 := rfl
theorem S_61 : S 61 = 2 :: S 62 := rfl

-- generated by gen_phi_chunks.py 9999999 30000 c7: 89 lemmas, 45 kernel leaves,
-- total nodes 318321, root value 978019

set_option maxRecDepth 100000 in
theorem c7_44_9999999 : phiList (S 44) 9999999 = 1315593 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c7_44_149253 : phiList (S 44) 149253 = 19656 := by decide +kernel

theorem c7_43_9999999 : phiList (S 43) 9999999 = 1295937 := by rw [S_43, phiList_cons]; norm_num [c7_44_9999999, c7_44_149253]

set_option maxRecDepth 100000 in
theorem c7_43_140845 : phiList (S 43) 140845 = 18250 := by decide +kernel

theorem c7_42_9999999 : phiList (S 42) 9999999 = 1277687 := by rw [S_42, phiList_cons]; norm_num [c7_43_9999999, c7_43_140845]

set_option maxRecDepth 100000 in
theorem c7_42_136986 : phiList (S 42) 136986 = 17468 := by decide +kernel

theorem c7_41_9999999 : phiList (S 41) 9999999 = 1260219 := by rw [S_41, phiList_cons]; norm_num [c7_42_9999999, c7_42_136986]

set_option maxRecDepth 100000 in
theorem c7_41_126582 : phiList (S 41) 126582 = 15872 := by decide +kernel

theorem c7_40_9999999 : phiList (S 40) 9999999 = 1244347 := by rw [S_40, phiList_cons]; norm_num [c7_41_9999999, c7_41_126582]

set_option maxRecDepth 100000 in
theorem c7_40_120481 : phiList (S 40) 120481 = 14877 := by decide +kernel

theorem c7_39_9999999 : phiList (S 39) 9999999 = 1229470 := by rw [S_39, phiList_cons]; norm_num [c7_40_9999999, c7_40_120481]

set_option maxRecDepth 100000 in
theorem c7_39_112359 : phiList (S 39) 112359 = 13669 := by decide +kernel

theorem c7_38_9999999 : phiList (S 38) 9999999 = 1215801 := by rw [S_38, phiList_cons]; norm_num [c7_39_9999999, c7_39_112359]

set_option maxRecDepth 100000 in
theorem c7_38_103092 : phiList (S 38) 103092 = 12359 := by decide +kernel

theorem c7_37_9999999 : phiList (S 37) 9999999 = 1203442 := by rw [S_37, phiList_cons]; norm_num [c7_38_9999999, c7_38_103092]

set_option maxRecDepth 100000 in
theorem c7_37_99009 : phiList (S 37) 99009 = 11711 := by decide +kernel

theorem c7_36_9999999 : phiList (S 36) 9999999 = 1191731 := by rw [S_36, phiList_cons]; norm_num [c7_37_9999999, c7_37_99009]

set_option maxRecDepth 100000 in
theorem c7_36_97087 : phiList (S 36) 97087 = 11345 := by decide +kernel

theorem c7_35_9999999 : phiList (S 35) 9999999 = 1180386 := by rw [S_35, phiList_cons]; norm_num [c7_36_9999999, c7_36_97087]

set_option maxRecDepth 100000 in
theorem c7_35_93457 : phiList (S 35) 93457 = 10780 := by decide +kernel

theorem c7_34_9999999 : phiList (S 34) 9999999 = 1169606 := by rw [S_34, phiList_cons]; norm_num [c7_35_9999999, c7_35_93457]

set_option maxRecDepth 100000 in
theorem c7_34_91743 : phiList (S 34) 91743 = 10452 := by decide +kernel

theorem c7_33_9999999 : phiList (S 33) 9999999 = 1159154 := by rw [S_33, phiList_cons]; norm_num [c7_34_9999999, c7_34_91743]

set_option maxRecDepth 100000 in
theorem c7_33_88495 : phiList (S 33) 88495 = 9956 := by decide +kernel

theorem c7_32_9999999 : phiList (S 32) 9999999 = 1149198 := by rw [S_32, phiList_cons]; norm_num [c7_33_9999999, c7_33_88495]

set_option maxRecDepth 100000 in
theorem c7_32_78740 : phiList (S 32) 78740 = 8749 := by decide +kernel

theorem c7_31_9999999 : phiList (S 31) 9999999 = 1140449 := by rw [S_31, phiList_cons]; norm_num [c7_32_9999999, c7_32_78740]

set_option maxRecDepth 100000 in
theorem c7_31_76335 : phiList (S 31) 76335 = 8399 := by decide +kernel

theorem c7_30_9999999 : phiList (S 30) 9999999 = 1132050 := by rw [S_30, phiList_cons]; norm_num [c7_31_9999999, c7_31_76335]

set_option maxRecDepth 100000 in
theorem c7_30_72992 : phiList (S 30) 72992 = 7957 := by decide +kernel

theorem c7_29_9999999 : phiList (S 29) 9999999 = 1124093 := by rw [S_29, phiList_cons]; norm_num [c7_30_9999999, c7_30_72992]

set_option maxRecDepth 100000 in
theorem c7_29_71942 : phiList (S 29) 71942 = 7769 := by decide +kernel

theorem c7_28_9999999 : phiList (S 28) 9999999 = 1116324 := by rw [S_28, phiList_cons]; norm_num [c7_29_9999999, c7_29_71942]

set_option maxRecDepth 100000 in
theorem c7_28_67114 : phiList (S 28) 67114 = 7182 := by decide +kernel

theorem c7_27_9999999 : phiList (S 27) 9999999 = 1109142 := by rw [S_27, phiList_cons]; norm_num [c7_28_9999999, c7_28_67114]

set_option maxRecDepth 100000 in
theorem c7_27_66225 : phiList (S 27) 66225 = 7035 := by decide +kernel

theorem c7_26_9999999 : phiList (S 26) 9999999 = 1102107 := by rw [S_26, phiList_cons]; norm_num [c7_27_9999999, c7_27_66225]

set_option maxRecDepth 100000 in
theorem c7_26_63694 : phiList (S 26) 63694 = 6725 := by decide +kernel

theorem c7_25_9999999 : phiList (S 25) 9999999 = 1095382 := by rw [S_25, phiList_cons]; norm_num [c7_26_9999999, c7_26_63694]

set_option maxRecDepth 100000 in
theorem c7_25_61349 : phiList (S 25) 61349 = 6433 := by decide +kernel

theorem c7_24_9999999 : phiList (S 24) 9999999 = 1088949 := by rw [S_24, phiList_cons]; norm_num [c7_25_9999999, c7_25_61349]

set_option maxRecDepth 100000 in
theorem c7_24_59880 : phiList (S 24) 59880 = 6249 := by decide +kernel

theorem c7_23_9999999 : phiList (S 23) 9999999 = 1082700 := by rw [S_23, phiList_cons]; norm_num [c7_24_9999999, c7_24_59880]

set_option maxRecDepth 100000 in
theorem c7_23_57803 : phiList (S 23) 57803 = 6007 := by decide +kernel

theorem c7_22_9999999 : phiList (S 22) 9999999 = 1076693 := by rw [S_22, phiList_cons]; norm_num [c7_23_9999999, c7_23_57803]

set_option maxRecDepth 100000 in
theorem c7_22_55865 : phiList (S 22) 55865 = 5772 := by decide +kernel

theorem c7_21_9999999 : phiList (S 21) 9999999 = 1070921 := by rw [S_21, phiList_cons]; norm_num [c7_22_9999999, c7_22_55865]

set_option maxRecDepth 100000 in
theorem c7_21_55248 : phiList (S 21) 55248 = 5685 := by decide +kernel

theorem c7_20_9999999 : phiList (S 20) 9999999 = 1065236 := by rw [S_20, phiList_cons]; norm_num [c7_21_9999999, c7_21_55248]

set_option maxRecDepth 100000 in
theorem c7_20_52356 : phiList (S 20) 52356 = 5375 := by decide +kernel

theorem c7_19_9999999 : phiList (S 19) 9999999 = 1059861 := by rw [S_19, phiList_cons]; norm_num [c7_20_9999999, c7_20_52356]

set_option maxRecDepth 100000 in
theorem c7_19_51813 : phiList (S 19) 51813 = 5304 := by decide +kernel

theorem c7_18_9999999 : phiList (S 18) 9999999 = 1054557 := by rw [S_18, phiList_cons]; norm_num [c7_19_9999999, c7_19_51813]

set_option maxRecDepth 100000 in
theorem c7_18_50761 : phiList (S 18) 50761 = 5185 := by decide +kernel

theorem c7_17_9999999 : phiList (S 17) 9999999 = 1049372 := by rw [S_17, phiList_cons]; norm_num [c7_18_9999999, c7_18_50761]

set_option maxRecDepth 100000 in
theorem c7_17_50251 : phiList (S 17) 50251 = 5128 := by decide +kernel

theorem c7_16_9999999 : phiList (S 16) 9999999 = 1044244 := by rw [S_16, phiList_cons]; norm_num [c7_17_9999999, c7_17_50251]

set_option maxRecDepth 100000 in
theorem c7_16_47393 : phiList (S 16) 47393 = 4844 := by decide +kernel

theorem c7_15_9999999 : phiList (S 15) 9999999 = 1039400 := by rw [S_15, phiList_cons]; norm_num [c7_16_9999999, c7_16_47393]

set_option maxRecDepth 100000 in
theorem c7_15_44843 : phiList (S 15) 44843 = 4614 := by decide +kernel

theorem c7_14_9999999 : phiList (S 14) 9999999 = 1034786 := by rw [S_14, phiList_cons]; norm_num [c7_15_9999999, c7_15_44843]

set_option maxRecDepth 100000 in
theorem c7_14_44052 : phiList (S 14) 44052 = 4537 := by decide +kernel

theorem c7_13_9999999 : phiList (S 13) 9999999 = 1030249 := by rw [S_13, phiList_cons]; norm_num [c7_14_9999999, c7_14_44052]

set_option maxRecDepth 100000 in
theorem c7_13_43668 : phiList (S 13) 43668 = 4502 := by decide +kernel

theorem c7_12_9999999 : phiList (S 12) 9999999 = 1025747 := by rw [S_12, phiList_cons]; norm_num [c7_13_9999999, c7_13_43668]

set_option maxRecDepth 100000 in
theorem c7_12_42918 : phiList (S 12) 42918 = 4436 := by decide +kernel

theorem c7_11_9999999 : phiList (S 11) 9999999 = 1021311 := by rw [S_11, phiList_cons]; norm_num [c7_12_9999999, c7_12_42918]

set_option maxRecDepth 100000 in
theorem c7_11_41841 : phiList (S 11) 41841 = 4322 := by decide +kernel

theorem c7_10_9999999 : phiList (S 10) 9999999 = 1016989 := by rw [S_10, phiList_cons]; norm_num [c7_11_9999999, c7_11_41841]

set_option maxRecDepth 100000 in
theorem c7_10_41493 : phiList (S 10) 41493 = 4288 := by decide +kernel

theorem c7_9_9999999 : phiList (S 9) 9999999 = 1012701 := by rw [S_9, phiList_cons]; norm_num [c7_10_9999999, c7_10_41493]

set_option maxRecDepth 100000 in
theorem c7_9_39840 : phiList (S 9) 39840 = 4135 := by decide +kernel

theorem c7_8_9999999 : phiList (S 8) 9999999 = 1008566 := by rw [S_8, phiList_cons]; norm_num [c7_9_9999999, c7_9_39840]

set_option maxRecDepth 100000 in
theorem c7_8_38910 : phiList (S 8) 38910 = 4045 := by decide +kernel

theorem c7_7_9999999 : phiList (S 7) 9999999 = 1004521 := by rw [S_7, phiList_cons]; norm_num [c7_8_9999999, c7_8_38910]

set_option maxRecDepth 100000 in
theorem c7_7_38022 : phiList (S 7) 38022 = 3964 := by decide +kernel

theorem c7_6_9999999 : phiList (S 6) 9999999 = 1000557 := by rw [S_6, phiList_cons]; norm_num [c7_7_9999999, c7_7_38022]

set_option maxRecDepth 100000 in
theorem c7_6_37174 : phiList (S 6) 37174 = 3883 := by decide +kernel

theorem c7_5_9999999 : phiList (S 5) 9999999 = 996674 := by rw [S_5, phiList_cons]; norm_num [c7_6_9999999, c7_6_37174]

set_option maxRecDepth 100000 in
theorem c7_5_36900 : phiList (S 5) 36900 = 3856 := by decide +kernel

theorem c7_4_9999999 : phiList (S 4) 9999999 = 992818 := by rw [S_4, phiList_cons]; norm_num [c7_5_9999999, c7_5_36900]

set_option maxRecDepth 100000 in
theorem c7_4_36101 : phiList (S 4) 36101 = 3777 := by decide +kernel

theorem c7_3_9999999 : phiList (S 3) 9999999 = 989041 := by rw [S_3, phiList_cons]; norm_num [c7_4_9999999, c7_4_36101]

set_option maxRecDepth 100000 in
theorem c7_3_35587 : phiList (S 3) 35587 = 3730 := by decide +kernel

theorem c7_2_9999999 : phiList (S 2) 9999999 = 985311 := by rw [S_2, phiList_cons]; norm_num [c7_3_9999999, c7_3_35587]

set_option maxRecDepth 100000 in
theorem c7_2_35335 : phiList (S 2) 35335 = 3705 := by decide +kernel

theorem c7_1_9999999 : phiList (S 1) 9999999 = 981606 := by rw [S_1, phiList_cons]; norm_num [c7_2_9999999, c7_2_35335]

set_option maxRecDepth 100000 in
theorem c7_1_34129 : phiList (S 1) 34129 = 3587 := by decide +kernel

theorem c7_0_9999999 : phiList (S 0) 9999999 = 978019 := by rw [S_0, phiList_cons]; norm_num [c7_1_9999999, c7_1_34129]

theorem c7_root : phiList primesDesc 9999999 = 978019 := by
  have h := c7_0_9999999
  simpa [S] using h

theorem primeCounting'_1e7 : Nat.primeCounting' 10000000 < 1000000 := by
  have h := primeCounting'_le_sieve 10000000 (by norm_num)
  rw [← phiList_eq_card goodList_primesDesc] at h
  simp only [show (10000000 : ℕ) - 1 = 9999999 from rfl, c7_root,
    show primesDesc.length = 62 from rfl] at h
  omega

end OeisA100475Proof

open Nat Function

namespace OeisA100475Proof

open OeisA100475

-- generated by gen_phi_chunks.py 99999999 30000 c8: 189 lemmas, 95 kernel leaves,
-- total nodes 1267127, root value 9773051

set_option maxRecDepth 100000 in
theorem c8_46_99999999 : phiList (S 46) 99999999 = 13608843 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_46_1694915 : phiList (S 46) 1694915 = 230684 := by decide +kernel

theorem c8_45_99999999 : phiList (S 45) 99999999 = 13378159 := by rw [S_45, phiList_cons]; norm_num [c8_46_99999999, c8_46_1694915]

set_option maxRecDepth 100000 in
theorem c8_45_1639344 : phiList (S 45) 1639344 = 219394 := by decide +kernel

theorem c8_44_99999999 : phiList (S 44) 99999999 = 13158765 := by rw [S_44, phiList_cons]; norm_num [c8_45_99999999, c8_45_1639344]

set_option maxRecDepth 100000 in
theorem c8_44_1492537 : phiList (S 44) 1492537 = 196553 := by decide +kernel

theorem c8_43_99999999 : phiList (S 43) 99999999 = 12962212 := by rw [S_43, phiList_cons]; norm_num [c8_44_99999999, c8_44_1492537]

set_option maxRecDepth 100000 in
theorem c8_43_1408450 : phiList (S 43) 1408450 = 182783 := by decide +kernel

theorem c8_42_99999999 : phiList (S 42) 99999999 = 12779429 := by rw [S_42, phiList_cons]; norm_num [c8_43_99999999, c8_43_1408450]

set_option maxRecDepth 100000 in
theorem c8_42_1369863 : phiList (S 42) 1369863 = 175352 := by decide +kernel

theorem c8_41_99999999 : phiList (S 41) 99999999 = 12604077 := by rw [S_41, phiList_cons]; norm_num [c8_42_99999999, c8_42_1369863]

set_option maxRecDepth 100000 in
theorem c8_41_1265822 : phiList (S 41) 1265822 = 159911 := by decide +kernel

theorem c8_40_99999999 : phiList (S 40) 99999999 = 12444166 := by rw [S_40, phiList_cons]; norm_num [c8_41_99999999, c8_41_1265822]

set_option maxRecDepth 100000 in
theorem c8_40_1204819 : phiList (S 40) 1204819 = 150352 := by decide +kernel

theorem c8_39_99999999 : phiList (S 39) 99999999 = 12293814 := by rw [S_39, phiList_cons]; norm_num [c8_40_99999999, c8_40_1204819]

set_option maxRecDepth 100000 in
theorem c8_39_1123595 : phiList (S 39) 1123595 = 138582 := by decide +kernel

theorem c8_38_99999999 : phiList (S 38) 99999999 = 12155232 := by rw [S_38, phiList_cons]; norm_num [c8_39_99999999, c8_39_1123595]

set_option maxRecDepth 100000 in
theorem c8_38_1030927 : phiList (S 38) 1030927 = 125779 := by decide +kernel

theorem c8_37_99999999 : phiList (S 37) 99999999 = 12029453 := by rw [S_37, phiList_cons]; norm_num [c8_38_99999999, c8_38_1030927]

set_option maxRecDepth 100000 in
theorem c8_37_990099 : phiList (S 37) 990099 = 119553 := by decide +kernel

theorem c8_36_99999999 : phiList (S 36) 99999999 = 11909900 := by rw [S_36, phiList_cons]; norm_num [c8_37_99999999, c8_37_990099]

set_option maxRecDepth 100000 in
theorem c8_36_970873 : phiList (S 36) 970873 = 116076 := by decide +kernel

theorem c8_35_99999999 : phiList (S 35) 99999999 = 11793824 := by rw [S_35, phiList_cons]; norm_num [c8_36_99999999, c8_36_970873]

set_option maxRecDepth 100000 in
theorem c8_35_934579 : phiList (S 35) 934579 = 110631 := by decide +kernel

theorem c8_34_99999999 : phiList (S 34) 99999999 = 11683193 := by rw [S_34, phiList_cons]; norm_num [c8_35_99999999, c8_35_934579]

set_option maxRecDepth 100000 in
theorem c8_34_917431 : phiList (S 34) 917431 = 107565 := by decide +kernel

theorem c8_33_99999999 : phiList (S 33) 99999999 = 11575628 := by rw [S_33, phiList_cons]; norm_num [c8_34_99999999, c8_34_917431]

set_option maxRecDepth 100000 in
theorem c8_33_884955 : phiList (S 33) 884955 = 102740 := by decide +kernel

theorem c8_32_99999999 : phiList (S 32) 99999999 = 11472888 := by rw [S_32, phiList_cons]; norm_num [c8_33_99999999, c8_33_884955]

set_option maxRecDepth 100000 in
theorem c8_32_787401 : phiList (S 32) 787401 = 90486 := by decide +kernel

theorem c8_31_99999999 : phiList (S 31) 99999999 = 11382402 := by rw [S_31, phiList_cons]; norm_num [c8_32_99999999, c8_32_787401]

set_option maxRecDepth 100000 in
theorem c8_31_763358 : phiList (S 31) 763358 = 86955 := by decide +kernel

theorem c8_30_99999999 : phiList (S 30) 99999999 = 11295447 := by rw [S_30, phiList_cons]; norm_num [c8_31_99999999, c8_31_763358]

set_option maxRecDepth 100000 in
theorem c8_30_729927 : phiList (S 30) 729927 = 82414 := by decide +kernel

theorem c8_29_99999999 : phiList (S 29) 99999999 = 11213033 := by rw [S_29, phiList_cons]; norm_num [c8_30_99999999, c8_30_729927]

set_option maxRecDepth 100000 in
theorem c8_29_719424 : phiList (S 29) 719424 = 80548 := by decide +kernel

theorem c8_28_99999999 : phiList (S 28) 99999999 = 11132485 := by rw [S_28, phiList_cons]; norm_num [c8_29_99999999, c8_29_719424]

set_option maxRecDepth 100000 in
theorem c8_28_671140 : phiList (S 28) 671140 = 74466 := by decide +kernel

theorem c8_27_99999999 : phiList (S 27) 99999999 = 11058019 := by rw [S_27, phiList_cons]; norm_num [c8_28_99999999, c8_28_671140]

set_option maxRecDepth 100000 in
theorem c8_27_662251 : phiList (S 27) 662251 = 72899 := by decide +kernel

theorem c8_26_99999999 : phiList (S 26) 99999999 = 10985120 := by rw [S_26, phiList_cons]; norm_num [c8_27_99999999, c8_27_662251]

set_option maxRecDepth 100000 in
theorem c8_27_636942 : phiList (S 27) 636942 = 70082 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_27_4218 : phiList (S 27) 4218 = 543 := by decide +kernel

theorem c8_26_636942 : phiList (S 26) 636942 = 69539 := by rw [S_26, phiList_cons]; norm_num [c8_27_636942, c8_27_4218]

theorem c8_25_99999999 : phiList (S 25) 99999999 = 10915581 := by rw [S_25, phiList_cons]; norm_num [c8_26_99999999, c8_26_636942]

set_option maxRecDepth 100000 in
theorem c8_25_613496 : phiList (S 25) 613496 = 66451 := by decide +kernel

theorem c8_24_99999999 : phiList (S 24) 99999999 = 10849130 := by rw [S_24, phiList_cons]; norm_num [c8_25_99999999, c8_25_613496]

set_option maxRecDepth 100000 in
theorem c8_25_598802 : phiList (S 25) 598802 = 64825 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_25_3673 : phiList (S 25) 3673 = 477 := by decide +kernel

theorem c8_24_598802 : phiList (S 24) 598802 = 64348 := by rw [S_24, phiList_cons]; norm_num [c8_25_598802, c8_25_3673]

theorem c8_23_99999999 : phiList (S 23) 99999999 = 10784782 := by rw [S_23, phiList_cons]; norm_num [c8_24_99999999, c8_24_598802]

set_option maxRecDepth 100000 in
theorem c8_24_578034 : phiList (S 24) 578034 = 62083 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_24_3461 : phiList (S 24) 3461 = 447 := by decide +kernel

theorem c8_23_578034 : phiList (S 23) 578034 = 61636 := by rw [S_23, phiList_cons]; norm_num [c8_24_578034, c8_24_3461]

theorem c8_22_99999999 : phiList (S 22) 99999999 = 10723146 := by rw [S_22, phiList_cons]; norm_num [c8_23_99999999, c8_23_578034]

set_option maxRecDepth 100000 in
theorem c8_23_558659 : phiList (S 23) 558659 = 59534 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_23_3229 : phiList (S 23) 3229 = 419 := by decide +kernel

theorem c8_22_558659 : phiList (S 22) 558659 = 59115 := by rw [S_22, phiList_cons]; norm_num [c8_23_558659, c8_23_3229]

theorem c8_21_99999999 : phiList (S 21) 99999999 = 10664031 := by rw [S_21, phiList_cons]; norm_num [c8_22_99999999, c8_22_558659]

set_option maxRecDepth 100000 in
theorem c8_23_552486 : phiList (S 23) 552486 = 58877 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_23_3193 : phiList (S 23) 3193 = 414 := by decide +kernel

theorem c8_22_552486 : phiList (S 22) 552486 = 58463 := by rw [S_22, phiList_cons]; norm_num [c8_23_552486, c8_23_3193]

set_option maxRecDepth 100000 in
theorem c8_22_3086 : phiList (S 22) 3086 = 402 := by decide +kernel

theorem c8_21_552486 : phiList (S 21) 552486 = 58061 := by rw [S_21, phiList_cons]; norm_num [c8_22_552486, c8_22_3086]

theorem c8_20_99999999 : phiList (S 20) 99999999 = 10605970 := by rw [S_20, phiList_cons]; norm_num [c8_21_99999999, c8_21_552486]

set_option maxRecDepth 100000 in
theorem c8_21_523560 : phiList (S 21) 523560 = 54971 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_21_2892 : phiList (S 21) 2892 = 378 := by decide +kernel

theorem c8_20_523560 : phiList (S 20) 523560 = 54593 := by rw [S_20, phiList_cons]; norm_num [c8_21_523560, c8_21_2892]

theorem c8_19_99999999 : phiList (S 19) 99999999 = 10551377 := by rw [S_19, phiList_cons]; norm_num [c8_20_99999999, c8_20_523560]

set_option maxRecDepth 100000 in
theorem c8_21_518134 : phiList (S 21) 518134 = 54388 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_21_2862 : phiList (S 21) 2862 = 376 := by decide +kernel

theorem c8_20_518134 : phiList (S 20) 518134 = 54012 := by rw [S_20, phiList_cons]; norm_num [c8_21_518134, c8_21_2862]

set_option maxRecDepth 100000 in
theorem c8_20_2712 : phiList (S 20) 2712 = 354 := by decide +kernel

theorem c8_19_518134 : phiList (S 19) 518134 = 53658 := by rw [S_19, phiList_cons]; norm_num [c8_20_518134, c8_20_2712]

theorem c8_18_99999999 : phiList (S 18) 99999999 = 10497719 := by rw [S_18, phiList_cons]; norm_num [c8_19_99999999, c8_19_518134]

set_option maxRecDepth 100000 in
theorem c8_20_507614 : phiList (S 20) 507614 = 52891 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_20_2657 : phiList (S 20) 2657 = 343 := by decide +kernel

theorem c8_19_507614 : phiList (S 19) 507614 = 52548 := by rw [S_19, phiList_cons]; norm_num [c8_20_507614, c8_20_2657]

set_option maxRecDepth 100000 in
theorem c8_19_2630 : phiList (S 19) 2630 = 339 := by decide +kernel

theorem c8_18_507614 : phiList (S 18) 507614 = 52209 := by rw [S_18, phiList_cons]; norm_num [c8_19_507614, c8_19_2630]

theorem c8_17_99999999 : phiList (S 17) 99999999 = 10445510 := by rw [S_17, phiList_cons]; norm_num [c8_18_99999999, c8_18_507614]

set_option maxRecDepth 100000 in
theorem c8_20_502512 : phiList (S 20) 502512 = 52350 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_20_2630 : phiList (S 20) 2630 = 340 := by decide +kernel

theorem c8_19_502512 : phiList (S 19) 502512 = 52010 := by rw [S_19, phiList_cons]; norm_num [c8_20_502512, c8_20_2630]

set_option maxRecDepth 100000 in
theorem c8_19_2603 : phiList (S 19) 2603 = 336 := by decide +kernel

theorem c8_18_502512 : phiList (S 18) 502512 = 51674 := by rw [S_18, phiList_cons]; norm_num [c8_19_502512, c8_19_2603]

set_option maxRecDepth 100000 in
theorem c8_18_2550 : phiList (S 18) 2550 = 330 := by decide +kernel

theorem c8_17_502512 : phiList (S 17) 502512 = 51344 := by rw [S_17, phiList_cons]; norm_num [c8_18_502512, c8_18_2550]

theorem c8_16_99999999 : phiList (S 16) 99999999 = 10394166 := by rw [S_16, phiList_cons]; norm_num [c8_17_99999999, c8_17_502512]

set_option maxRecDepth 100000 in
theorem c8_18_473933 : phiList (S 18) 473933 = 48679 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_18_2405 : phiList (S 18) 2405 = 314 := by decide +kernel

theorem c8_17_473933 : phiList (S 17) 473933 = 48365 := by rw [S_17, phiList_cons]; norm_num [c8_18_473933, c8_18_2405]

set_option maxRecDepth 100000 in
theorem c8_17_2381 : phiList (S 17) 2381 = 309 := by decide +kernel

theorem c8_16_473933 : phiList (S 16) 473933 = 48056 := by rw [S_16, phiList_cons]; norm_num [c8_17_473933, c8_17_2381]

theorem c8_15_99999999 : phiList (S 15) 99999999 = 10346110 := by rw [S_15, phiList_cons]; norm_num [c8_16_99999999, c8_16_473933]

set_option maxRecDepth 100000 in
theorem c8_16_448430 : phiList (S 16) 448430 = 45424 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_16_2125 : phiList (S 16) 2125 = 274 := by decide +kernel

theorem c8_15_448430 : phiList (S 15) 448430 = 45150 := by rw [S_15, phiList_cons]; norm_num [c8_16_448430, c8_16_2125]

theorem c8_14_99999999 : phiList (S 14) 99999999 = 10300960 := by rw [S_14, phiList_cons]; norm_num [c8_15_99999999, c8_15_448430]

set_option maxRecDepth 100000 in
theorem c8_15_440528 : phiList (S 15) 440528 = 44344 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_15_1975 : phiList (S 15) 1975 = 252 := by decide +kernel

theorem c8_14_440528 : phiList (S 14) 440528 = 44092 := by rw [S_14, phiList_cons]; norm_num [c8_15_440528, c8_15_1975]

theorem c8_13_99999999 : phiList (S 13) 99999999 = 10256868 := by rw [S_13, phiList_cons]; norm_num [c8_14_99999999, c8_14_440528]

set_option maxRecDepth 100000 in
theorem c8_15_436681 : phiList (S 15) 436681 = 43961 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_15_1958 : phiList (S 15) 1958 = 251 := by decide +kernel

theorem c8_14_436681 : phiList (S 14) 436681 = 43710 := by rw [S_14, phiList_cons]; norm_num [c8_15_436681, c8_15_1958]

set_option maxRecDepth 100000 in
theorem c8_14_1923 : phiList (S 14) 1923 = 246 := by decide +kernel

theorem c8_13_436681 : phiList (S 13) 436681 = 43464 := by rw [S_13, phiList_cons]; norm_num [c8_14_436681, c8_14_1923]

theorem c8_12_99999999 : phiList (S 12) 99999999 = 10213404 := by rw [S_12, phiList_cons]; norm_num [c8_13_99999999, c8_13_436681]

set_option maxRecDepth 100000 in
theorem c8_14_429184 : phiList (S 14) 429184 = 42910 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_14_1890 : phiList (S 14) 1890 = 243 := by decide +kernel

theorem c8_13_429184 : phiList (S 13) 429184 = 42667 := by rw [S_13, phiList_cons]; norm_num [c8_14_429184, c8_14_1890]

set_option maxRecDepth 100000 in
theorem c8_13_1874 : phiList (S 13) 1874 = 239 := by decide +kernel

theorem c8_12_429184 : phiList (S 12) 429184 = 42428 := by rw [S_12, phiList_cons]; norm_num [c8_13_429184, c8_13_1874]

theorem c8_11_99999999 : phiList (S 11) 99999999 = 10170976 := by rw [S_11, phiList_cons]; norm_num [c8_12_99999999, c8_12_429184]

set_option maxRecDepth 100000 in
theorem c8_13_418410 : phiList (S 13) 418410 = 41591 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_13_1827 : phiList (S 13) 1827 = 233 := by decide +kernel

theorem c8_12_418410 : phiList (S 12) 418410 = 41358 := by rw [S_12, phiList_cons]; norm_num [c8_13_418410, c8_13_1827]

set_option maxRecDepth 100000 in
theorem c8_12_1795 : phiList (S 12) 1795 = 229 := by decide +kernel

theorem c8_11_418410 : phiList (S 11) 418410 = 41129 := by rw [S_11, phiList_cons]; norm_num [c8_12_418410, c8_12_1795]

theorem c8_10_99999999 : phiList (S 10) 99999999 = 10129847 := by rw [S_10, phiList_cons]; norm_num [c8_11_99999999, c8_11_418410]

set_option maxRecDepth 100000 in
theorem c8_13_414937 : phiList (S 13) 414937 = 41237 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_13_1811 : phiList (S 13) 1811 = 232 := by decide +kernel

theorem c8_12_414937 : phiList (S 12) 414937 = 41005 := by rw [S_12, phiList_cons]; norm_num [c8_13_414937, c8_13_1811]

set_option maxRecDepth 100000 in
theorem c8_12_1780 : phiList (S 12) 1780 = 226 := by decide +kernel

theorem c8_11_414937 : phiList (S 11) 414937 = 40779 := by rw [S_11, phiList_cons]; norm_num [c8_12_414937, c8_12_1780]

set_option maxRecDepth 100000 in
theorem c8_11_1736 : phiList (S 11) 1736 = 220 := by decide +kernel

theorem c8_10_414937 : phiList (S 10) 414937 = 40559 := by rw [S_10, phiList_cons]; norm_num [c8_11_414937, c8_11_1736]

theorem c8_9_99999999 : phiList (S 9) 99999999 = 10089288 := by rw [S_9, phiList_cons]; norm_num [c8_10_99999999, c8_10_414937]

set_option maxRecDepth 100000 in
theorem c8_11_398406 : phiList (S 11) 398406 = 39127 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_11_1666 : phiList (S 11) 1666 = 211 := by decide +kernel

theorem c8_10_398406 : phiList (S 10) 398406 = 38916 := by rw [S_10, phiList_cons]; norm_num [c8_11_398406, c8_11_1666]

set_option maxRecDepth 100000 in
theorem c8_10_1653 : phiList (S 10) 1653 = 208 := by decide +kernel

theorem c8_9_398406 : phiList (S 9) 398406 = 38708 := by rw [S_9, phiList_cons]; norm_num [c8_10_398406, c8_10_1653]

theorem c8_8_99999999 : phiList (S 8) 99999999 = 10050580 := by rw [S_8, phiList_cons]; norm_num [c8_9_99999999, c8_9_398406]

set_option maxRecDepth 100000 in
theorem c8_9_389105 : phiList (S 9) 389105 = 37773 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_9_1550 : phiList (S 9) 1550 = 192 := by decide +kernel

theorem c8_8_389105 : phiList (S 8) 389105 = 37581 := by rw [S_8, phiList_cons]; norm_num [c8_9_389105, c8_9_1550]

theorem c8_7_99999999 : phiList (S 7) 99999999 = 10012999 := by rw [S_7, phiList_cons]; norm_num [c8_8_99999999, c8_8_389105]

set_option maxRecDepth 100000 in
theorem c8_9_380228 : phiList (S 9) 380228 = 36901 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_9_1514 : phiList (S 9) 1514 = 188 := by decide +kernel

theorem c8_8_380228 : phiList (S 8) 380228 = 36713 := by rw [S_8, phiList_cons]; norm_num [c8_9_380228, c8_9_1514]

set_option maxRecDepth 100000 in
theorem c8_8_1479 : phiList (S 8) 1479 = 180 := by decide +kernel

theorem c8_7_380228 : phiList (S 7) 380228 = 36533 := by rw [S_7, phiList_cons]; norm_num [c8_8_380228, c8_8_1479]

theorem c8_6_99999999 : phiList (S 6) 99999999 = 9976466 := by rw [S_6, phiList_cons]; norm_num [c8_7_99999999, c8_7_380228]

set_option maxRecDepth 100000 in
theorem c8_8_371747 : phiList (S 8) 371747 = 35883 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_8_1446 : phiList (S 8) 1446 = 175 := by decide +kernel

theorem c8_7_371747 : phiList (S 7) 371747 = 35708 := by rw [S_7, phiList_cons]; norm_num [c8_8_371747, c8_8_1446]

set_option maxRecDepth 100000 in
theorem c8_7_1413 : phiList (S 7) 1413 = 169 := by decide +kernel

theorem c8_6_371747 : phiList (S 6) 371747 = 35539 := by rw [S_6, phiList_cons]; norm_num [c8_7_371747, c8_7_1413]

theorem c8_5_99999999 : phiList (S 5) 99999999 = 9940927 := by rw [S_5, phiList_cons]; norm_num [c8_6_99999999, c8_6_371747]

set_option maxRecDepth 100000 in
theorem c8_7_369003 : phiList (S 7) 369003 = 35449 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_7_1403 : phiList (S 7) 1403 = 168 := by decide +kernel

theorem c8_6_369003 : phiList (S 6) 369003 = 35281 := by rw [S_6, phiList_cons]; norm_num [c8_7_369003, c8_7_1403]

set_option maxRecDepth 100000 in
theorem c8_6_1371 : phiList (S 6) 1371 = 164 := by decide +kernel

theorem c8_5_369003 : phiList (S 5) 369003 = 35117 := by rw [S_5, phiList_cons]; norm_num [c8_6_369003, c8_6_1371]

theorem c8_4_99999999 : phiList (S 4) 99999999 = 9905810 := by rw [S_4, phiList_cons]; norm_num [c8_5_99999999, c8_5_369003]

set_option maxRecDepth 100000 in
theorem c8_6_361010 : phiList (S 6) 361010 = 34505 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_6_1342 : phiList (S 6) 1342 = 162 := by decide +kernel

theorem c8_5_361010 : phiList (S 5) 361010 = 34343 := by rw [S_5, phiList_cons]; norm_num [c8_6_361010, c8_6_1342]

set_option maxRecDepth 100000 in
theorem c8_5_1332 : phiList (S 5) 1332 = 161 := by decide +kernel

theorem c8_4_361010 : phiList (S 4) 361010 = 34182 := by rw [S_4, phiList_cons]; norm_num [c8_5_361010, c8_5_1332]

theorem c8_3_99999999 : phiList (S 3) 99999999 = 9871628 := by rw [S_3, phiList_cons]; norm_num [c8_4_99999999, c8_4_361010]

set_option maxRecDepth 100000 in
theorem c8_6_355871 : phiList (S 6) 355871 = 34022 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_6_1322 : phiList (S 6) 1322 = 161 := by decide +kernel

theorem c8_5_355871 : phiList (S 5) 355871 = 33861 := by rw [S_5, phiList_cons]; norm_num [c8_6_355871, c8_6_1322]

set_option maxRecDepth 100000 in
theorem c8_5_1313 : phiList (S 5) 1313 = 158 := by decide +kernel

theorem c8_4_355871 : phiList (S 4) 355871 = 33703 := by rw [S_4, phiList_cons]; norm_num [c8_5_355871, c8_5_1313]

set_option maxRecDepth 100000 in
theorem c8_4_1284 : phiList (S 4) 1284 = 151 := by decide +kernel

theorem c8_3_355871 : phiList (S 3) 355871 = 33552 := by rw [S_3, phiList_cons]; norm_num [c8_4_355871, c8_4_1284]

theorem c8_2_99999999 : phiList (S 2) 99999999 = 9838076 := by rw [S_2, phiList_cons]; norm_num [c8_3_99999999, c8_3_355871]

set_option maxRecDepth 100000 in
theorem c8_6_353356 : phiList (S 6) 353356 = 33769 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_6_1313 : phiList (S 6) 1313 = 159 := by decide +kernel

theorem c8_5_353356 : phiList (S 5) 353356 = 33610 := by rw [S_5, phiList_cons]; norm_num [c8_6_353356, c8_6_1313]

set_option maxRecDepth 100000 in
theorem c8_5_1303 : phiList (S 5) 1303 = 157 := by decide +kernel

theorem c8_4_353356 : phiList (S 4) 353356 = 33453 := by rw [S_4, phiList_cons]; norm_num [c8_5_353356, c8_5_1303]

set_option maxRecDepth 100000 in
theorem c8_4_1275 : phiList (S 4) 1275 = 148 := by decide +kernel

theorem c8_3_353356 : phiList (S 3) 353356 = 33305 := by rw [S_3, phiList_cons]; norm_num [c8_4_353356, c8_4_1275]

set_option maxRecDepth 100000 in
theorem c8_3_1257 : phiList (S 3) 1257 = 146 := by decide +kernel

theorem c8_2_353356 : phiList (S 2) 353356 = 33159 := by rw [S_2, phiList_cons]; norm_num [c8_3_353356, c8_3_1257]

theorem c8_1_99999999 : phiList (S 1) 99999999 = 9804917 := by rw [S_1, phiList_cons]; norm_num [c8_2_99999999, c8_2_353356]

set_option maxRecDepth 100000 in
theorem c8_4_341296 : phiList (S 4) 341296 = 32289 := by decide +kernel

set_option maxRecDepth 100000 in
theorem c8_4_1232 : phiList (S 4) 1232 = 145 := by decide +kernel

theorem c8_3_341296 : phiList (S 3) 341296 = 32144 := by rw [S_3, phiList_cons]; norm_num [c8_4_341296, c8_4_1232]

set_option maxRecDepth 100000 in
theorem c8_3_1214 : phiList (S 3) 1214 = 140 := by decide +kernel

theorem c8_2_341296 : phiList (S 2) 341296 = 32004 := by rw [S_2, phiList_cons]; norm_num [c8_3_341296, c8_3_1214]

set_option maxRecDepth 100000 in
theorem c8_2_1205 : phiList (S 2) 1205 = 138 := by decide +kernel

theorem c8_1_341296 : phiList (S 1) 341296 = 31866 := by rw [S_1, phiList_cons]; norm_num [c8_2_341296, c8_2_1205]

theorem c8_0_99999999 : phiList (S 0) 99999999 = 9773051 := by rw [S_0, phiList_cons]; norm_num [c8_1_99999999, c8_1_341296]

theorem c8_root : phiList primesDesc 99999999 = 9773051 := by
  have h := c8_0_99999999
  simpa [S] using h

theorem primeCounting'_1e8 : Nat.primeCounting' 100000000 < 10000000 := by
  have h := primeCounting'_le_sieve 100000000 (by norm_num)
  rw [← phiList_eq_card goodList_primesDesc] at h
  simp only [show (100000000 : ℕ) - 1 = 99999999 from rfl, c8_root,
    show primesDesc.length = 62 from rfl] at h
  omega

end OeisA100475Proof

open Nat Function

namespace OeisA100475Proof

open OeisA100475

/-- The primes below `10008` (there are `1230`; the last is `10007`). -/
def primesTable : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
   191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
   283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
   401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503,
   509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
   631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743,
   751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
   877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997,
   1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093,
   1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213,
   1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303,
   1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439,
   1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543,
   1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627,
   1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753,
   1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877,
   1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999,
   2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111,
   2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239,
   2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347,
   2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447,
   2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593,
   2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699,
   2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801,
   2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927,
   2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061,
   3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203,
   3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323,
   3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457,
   3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557,
   3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673,
   3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797,
   3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919,
   3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049,
   4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159,
   4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283,
   4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441,
   4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561,
   4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679,
   4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813,
   4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957,
   4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077,
   5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209,
   5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351,
   5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477,
   5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591,
   5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717,
   5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849,
   5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987,
   6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121,
   6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257,
   6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359,
   6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521,
   6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659,
   6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781,
   6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907,
   6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019,
   7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187,
   7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321,
   7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487,
   7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583,
   7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703,
   7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867,
   7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009,
   8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147,
   8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273,
   8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423,
   8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573,
   8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693,
   8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819,
   8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951,
   8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091,
   9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221,
   9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349,
   9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467,
   9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623,
   9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749,
   9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871,
   9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973, 10007]

/-- `fTable[y-1] = reverse (p_y)` for `1 ≤ y ≤ 1229`. -/
def fTable : List ℕ :=
  [2, 3, 5, 7, 11, 31, 71, 91, 32, 92, 13, 73, 14, 34, 74, 35, 95, 16, 76, 17, 37, 97, 38, 98,
   79, 101, 301, 701, 901, 311, 721, 131, 731, 931, 941, 151, 751, 361, 761, 371, 971, 181,
   191, 391, 791, 991, 112, 322, 722, 922, 332, 932, 142, 152, 752, 362, 962, 172, 772, 182,
   382, 392, 703, 113, 313, 713, 133, 733, 743, 943, 353, 953, 763, 373, 973, 383, 983, 793,
   104, 904, 914, 124, 134, 334, 934, 344, 944, 754, 164, 364, 764, 974, 784, 194, 994, 305,
   905, 125, 325, 145, 745, 755, 365, 965, 175, 775, 785, 395, 995, 106, 706, 316, 716, 916,
   136, 146, 346, 746, 356, 956, 166, 376, 776, 386, 196, 107, 907, 917, 727, 337, 937, 347,
   157, 757, 167, 967, 377, 787, 797, 908, 118, 128, 328, 728, 928, 938, 358, 758, 958, 368,
   778, 188, 388, 788, 709, 119, 919, 929, 739, 149, 749, 359, 769, 179, 779, 389, 199, 799,
   9001, 3101, 9101, 1201, 1301, 3301, 9301, 9401, 1501, 1601, 3601, 9601, 7801, 1901, 3901,
   7901, 3011, 9011, 7111, 3211, 9211, 1511, 3511, 3611, 1711, 1811, 7811, 3911, 1021, 3121,
   7121, 3221, 9221, 1321, 7321, 9421, 9521, 7721, 9721, 3821, 9821, 1921, 7921, 1031, 3031,
   7031, 9131, 1231, 7231, 1631, 7631, 3731, 1831, 9931, 9041, 3241, 7241, 9241, 3341, 9341,
   7441, 1541, 3541, 9541, 1741, 1841, 3841, 7841, 9841, 3941, 9941, 1151, 3251, 1351, 3451,
   9451, 3551, 9551, 7651, 1751, 9751, 3851, 7951, 1061, 7061, 9061, 3161, 9161, 1261, 7261,
   7361, 7561, 3661, 7661, 9661, 3961, 7961, 9961, 9071, 1271, 3271, 3371, 1471, 7471, 3571,
   9571, 7771, 3871, 7871, 9871, 1081, 1181, 3281, 1381, 7481, 1681, 7681, 1781, 3781, 7781,
   9781, 9881, 1091, 7091, 3191, 1391, 3391, 9491, 1591, 3791, 9791, 7891, 3991, 7991, 9991,
   3002, 1102, 7102, 7202, 9202, 9302, 3502, 3602, 9602, 1802, 3802, 7802, 9802, 9902, 1112,
   3112, 9212, 1312, 7312, 1412, 3412, 3512, 1612, 9712, 3022, 7022, 3122, 1222, 7322, 9322,
   3422, 1522, 7622, 9622, 3722, 1822, 7822, 3922, 7922, 9032, 1132, 3332, 9332, 1432, 7432,
   1532, 7532, 1732, 7732, 1832, 3832, 9832, 3932, 9932, 1142, 7142, 3242, 7342, 1442, 7442,
   9542, 7642, 3742, 7742, 3052, 1252, 1352, 9352, 3452, 9452, 1552, 7552, 9752, 1952, 3952,
   9062, 7162, 1262, 3362, 7462, 7562, 9562, 3662, 1762, 7762, 3862, 7862, 9862, 3962, 9962,
   7072, 1172, 3172, 9172, 9272, 1372, 1472, 9472, 3572, 7672, 7772, 9872, 1972, 7972, 1082,
   3082, 9182, 3382, 7382, 3482, 1582, 7582, 1682, 9782, 7882, 7982, 3092, 9092, 7192, 7292,
   9392, 3592, 7592, 3692, 9692, 1792, 9992, 1003, 1103, 9103, 3203, 7303, 1403, 9403, 1603,
   7603, 9703, 3803, 9803, 9013, 9113, 1213, 7313, 3613, 7613, 9613, 1813, 7813, 1913, 3023,
   9023, 7123, 1223, 9223, 1523, 3523, 7523, 9523, 1723, 9923, 1033, 7033, 3133, 9133, 3233,
   9233, 1333, 3433, 7433, 9533, 1633, 1733, 3733, 9833, 1933, 7043, 3143, 3343, 9443, 7543,
   1643, 3643, 7643, 9643, 1943, 9943, 1153, 7153, 7253, 9253, 3353, 9353, 1453, 7453, 7553,
   9553, 1753, 1853, 3853, 3953, 7063, 3163, 7163, 3263, 1363, 7363, 3463, 9563, 1763, 3763,
   7763, 1963, 7963, 1073, 9073, 9173, 7273, 3373, 9373, 1673, 7673, 9673, 9773, 3973, 7973,
   3083, 1283, 3283, 3383, 7483, 1583, 3583, 3683, 7783, 1883, 9883, 7093, 1193, 7193, 9193,
   3293, 9293, 1393, 3493, 7493, 7693, 9893, 1004, 3004, 7004, 3104, 9104, 1204, 7204, 9404,
   1504, 7504, 3704, 9704, 1904, 3904, 9904, 1114, 7214, 9214, 3314, 9314, 3514, 7514, 9514,
   7714, 1024, 1124, 7124, 9124, 9224, 1324, 1424, 3424, 3524, 9524, 1624, 1724, 3724, 3824,
   9824, 7924, 7234, 7334, 9334, 9434, 7534, 3634, 3734, 1934, 7934, 9044, 1244, 3244, 1444,
   7444, 1544, 7544, 3644, 1844, 3844, 3944, 7054, 3154, 7154, 9154, 3254, 7454, 9454, 1654,
   7654, 3854, 1954, 7954, 3064, 1264, 7364, 9364, 3464, 9464, 1564, 7564, 3664, 3764, 9764,
   1964, 3074, 1274, 3274, 9274, 3374, 1574, 9574, 3874, 7874, 9874, 3974, 9974, 1084, 3184,
   7184, 1384, 1684, 1784, 7784, 9884, 3094, 9094, 9194, 1394, 3394, 7394, 3494, 1594, 7594,
   7694, 9694, 3794, 7894, 3994, 9994, 3005, 9005, 1105, 1205, 3205, 9305, 1505, 9505, 7705,
   1805, 7805, 9905, 1015, 7015, 3115, 9115, 7415, 3515, 7615, 1715, 9715, 9815, 7915, 9025,
   7225, 1325, 3325, 7325, 1625, 3725, 9725, 1825, 7925, 3035, 9035, 3235, 3335, 7435, 1535,
   1835, 7835, 3935, 9935, 7045, 3145, 7145, 9145, 1345, 7345, 1445, 3445, 9445, 1745, 7745,
   9745, 3845, 1055, 3055, 7055, 9155, 1255, 7255, 1355, 7555, 3655, 9655, 3755, 1855, 1955,
   3265, 9365, 1465, 7465, 1565, 3565, 7565, 9565, 9665, 3865, 9865, 3965, 1075, 1175, 7175,
   7375, 1475, 3475, 9475, 9775, 3875, 1975, 1085, 7085, 3185, 1285, 7285, 9385, 3485, 9485,
   1585, 7585, 1685, 7685, 9685, 9785, 1885, 7985, 3095, 3295, 7295, 9395, 3595, 1895, 7895,
   7006, 1106, 9206, 7306, 3406, 7406, 3506, 7606, 3706, 9706, 9806, 1906, 1016, 3116, 1216,
   1316, 3316, 3416, 1516, 3616, 3716, 7916, 9916, 3026, 1126, 7126, 1226, 9226, 7426, 7526,
   3626, 9626, 1726, 7726, 7826, 9926, 1036, 1136, 7136, 3236, 9236, 7336, 3436, 3536, 9536,
   1636, 7636, 3736, 9736, 9836, 7936, 1246, 7246, 9446, 1546, 9646, 3746, 1846, 1946, 1256,
   9256, 7456, 1556, 3556, 3656, 9656, 1756, 7756, 1856, 9956, 7066, 9166, 7366, 3566, 9566,
   1666, 3766, 9766, 9866, 1966, 1076, 3076, 9076, 9176, 3376, 7376, 1676, 3676, 9776, 1876,
   1976, 3976, 3086, 3286, 7286, 9286, 3386, 1486, 7586, 3686, 9686, 1786, 3886, 9986, 7096,
   1196, 7196, 7496, 9496, 9596, 1696, 7696, 1796, 7796, 3896, 1996, 7996, 1007, 3107, 9107,
   7207, 9307, 3407, 7507, 9607, 9707, 3017, 9017, 1217, 7217, 9217, 1517, 9517, 7717, 7817,
   3917, 7027, 1127, 3127, 9127, 9227, 7327, 3427, 7427, 3527, 3827, 7927, 7037, 9037, 1237,
   1337, 3337, 9437, 1537, 9637, 3937, 1147, 7147, 3347, 1547, 7547, 9547, 7747, 1847, 7847,
   9847, 9947, 7057, 7157, 3257, 9257, 7357, 1457, 7457, 9457, 9557, 1657, 3757, 7757, 3857,
   9857, 1957, 3067, 7067, 1267, 9367, 3467, 9467, 9667, 3767, 1867, 7867, 1967, 9967, 3077,
   7177, 3277, 7277, 1477, 3577, 7577, 9577, 9877, 3977, 7187, 3287, 9287, 1487, 3587, 7687,
   3787, 7787, 9787, 3887, 1097, 7097, 9197, 7297, 3397, 7397, 9497, 1597, 3697, 3997, 9008,
   1108, 7108, 9308, 3508, 9508, 9608, 1808, 7808, 9808, 3908, 1018, 1118, 7118, 3218, 7418,
   1618, 7618, 1718, 9718, 1918, 9028, 9128, 1228, 1328, 3328, 7328, 3428, 3628, 9628, 3728,
   7828, 1928, 3928, 7928, 1138, 7138, 9238, 3538, 3638, 9638, 7738, 7838, 9838, 9148, 3248,
   9248, 1348, 3448, 7448, 1648, 7648, 1058, 3158, 1258, 7258, 7358, 9358, 3458, 3658, 3758,
   1858, 7958, 9958, 9068, 3268, 7268, 9268, 1468, 7468, 3668, 9668, 7768, 1868, 9868, 3968,
   9968, 7078, 3178, 9178, 1378, 7378, 1478, 7478, 3578, 1678, 9778, 3878, 3088, 7088, 9188,
   1288, 1388, 7388, 9388, 9488, 1688, 3688, 7688, 7888, 3988, 3298, 9298, 3398, 1498, 1598,
   3698, 9698, 1798, 9998, 1009, 7009, 1109, 3109, 9209, 1409, 3409, 9409, 9509, 7609, 1909,
   3019, 9019, 7219, 3319, 7319, 1519, 7519, 1619, 3719, 1819, 7819, 9919, 3029, 9029, 1229,
   7229, 9329, 1429, 7529, 7729, 1829, 3829, 3929, 1139, 9139, 3239, 7339, 1439, 3439, 9439,
   1739, 7739, 1939, 7939, 3049, 3149, 9149, 1249, 1349, 3349, 7349, 9349, 1649, 3649, 7649,
   3749, 9749, 1949, 7949, 1159, 1259, 3359, 9359, 7459, 1559, 7859, 1069, 3169, 9169, 3269,
   9269, 1369, 3469, 9469, 1669, 7769, 9769, 9869, 7969, 9179, 1279, 3379, 9379, 3479, 9479,
   7679, 9679, 1879, 7879, 1979, 3089, 1189, 7189, 9289, 3389, 9389, 1589, 7589, 9589, 1789,
   3889, 7889, 1099, 7099, 3299, 9299, 1399, 1499, 9499, 7699, 3799]

/-- `rankL[y-1]` = number of steps until the orbit of `y` exceeds `1229`. -/
def rankL : List ℕ :=
  [9, 8, 7, 4, 6, 3, 3, 3, 4, 3, 5, 3, 4, 3, 3, 3, 3, 4, 3, 4, 4, 3, 3, 4, 4, 3, 2, 2, 3, 2, 2,
   3, 2, 2, 2, 3, 3, 2, 3, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 4, 3, 3, 2, 2, 3, 2, 2, 2, 2,
   2, 3, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 2, 3, 3, 2, 2, 3, 2, 2, 3, 2, 2, 2, 2,
   2, 2, 3, 2, 3, 2, 3, 2, 2, 2, 2, 2, 2, 3, 3, 2, 3, 2, 2, 2, 2, 3, 3, 2, 2, 2, 2, 3, 2, 2, 2,
   2, 4, 2, 2, 2, 2, 2, 2, 3, 2, 3, 2, 2, 2, 2, 2, 3, 3, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2,
   3, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
   2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   1, 3, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1,
   1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
   1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
   2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1]

def primes100 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

/-- Trial division by the primes up to `100`; decides primality below `10201`. -/
def isPrimeB (q : ℕ) : Bool := 2 ≤ q && primes100.all (fun d => q ≤ d || q % d != 0)

lemma isPrimeB_iff {q : ℕ} (hq : q ≤ 10200) : isPrimeB q = true ↔ q.Prime := by
  have hp100 : ∀ d ∈ primes100, d.Prime := by
    have h : ∀ d ∈ primes100, isPrimeTD d = true := by decide +kernel
    intro d hd; exact (isPrimeTD_iff d).1 (h d hd)
  have hcomp : ∀ d, d.Prime → d ≤ 100 → d ∈ primes100 := by
    have h : ∀ d < 101, isPrimeTD d = true → d ∈ primes100 := by decide +kernel
    intro d hd hd'; exact h d (by omega) ((isPrimeTD_iff d).2 hd)
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    by_contra hnp
    have hmf := Nat.minFac_prime (show q ≠ 1 by omega)
    have hsq := Nat.minFac_sq_le_self (by omega) hnp
    have hle : Nat.minFac q ≤ 100 := by
      by_contra hc
      push Not at hc
      nlinarith
    have hlt : Nat.minFac q < q := by
      rcases (Nat.minFac_le (by omega : 0 < q)).lt_or_eq with h' | h'
      · exact h'
      · exact absurd (Nat.prime_def_minFac.2 ⟨h2, h'⟩) hnp
    rcases h _ (hcomp _ hmf hle) with h' | h'
    · omega
    · exact h' (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd q))
  · intro hq'
    refine ⟨hq'.two_le, fun d hd => ?_⟩
    by_cases hdq : q ≤ d
    · exact Or.inl hdq
    · refine Or.inr fun h0 => ?_
      rcases hq'.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h0) with h | h
      · exact (hp100 d hd).one_lt.ne' h
      · omega

lemma count_eq_length_filter (p : ℕ → Prop) [DecidablePred p] (n : ℕ) :
    Nat.count p n = ((List.range n).filter (fun x => decide (p x))).length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : p n <;> simp [h]

/-- In the list of all `p`-numbers below `N`, the entry at index `k` has exactly `k` predecessors. -/
lemma count_getD_filter_range (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    ∀ k, k < ((List.range N).filter (fun x => decide (p x))).length →
      Nat.count p (((List.range N).filter (fun x => decide (p x))).getD k 0) = k := by
  induction N with
  | zero => intro k hk; simp at hk
  | succ N ih =>
    intro k hk
    by_cases h : p N
    · have hfilt : (List.range (N + 1)).filter (fun x => decide (p x)) =
          (List.range N).filter (fun x => decide (p x)) ++ [N] := by
        rw [List.range_succ, List.filter_append]; simp [h]
      rw [hfilt] at hk ⊢
      rw [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | hk'
      · rw [List.getD_append _ _ _ _ hk']; exact ih k hk'
      · subst hk'
        rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
        simp [count_eq_length_filter]
    · have hfilt : (List.range (N + 1)).filter (fun x => decide (p x)) =
          (List.range N).filter (fun x => decide (p x)) := by
        rw [List.range_succ, List.filter_append]; simp [h]
      rw [hfilt] at hk ⊢
      exact ih k hk

/-- Decimal digit reversal by structural recursion, so that the kernel can evaluate it. -/
def revAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, n, acc => if n = 0 then acc else revAux fuel (n / 10) (acc * 10 + n % 10)

def rev10 (n : ℕ) : ℕ := revAux n n 0

lemma revAux_eq : ∀ (fuel n acc : ℕ), n ≤ fuel →
    revAux fuel n acc =
      Nat.ofDigits 10 (Nat.digits 10 n).reverse + acc * 10 ^ (Nat.digits 10 n).length
  | 0, n, acc, h => by
    have hn : n = 0 := by omega
    subst hn; simp [revAux]
  | fuel + 1, n, acc, h => by
    by_cases hn : n = 0
    · subst hn; simp [revAux]
    · rw [revAux, if_neg hn, revAux_eq fuel (n / 10) _ (by omega),
        Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn), List.reverse_cons,
        Nat.ofDigits_append, Nat.ofDigits_singleton, List.length_cons, List.length_reverse]
      ring

lemma rev10_eq (n : ℕ) : rev10 n = reverseDigits n := by
  unfold rev10 reverseDigits
  rw [revAux_eq n n 0 le_rfl]
  simp

/-- Walk `fuel` consecutive numbers from `n` and check that the primes among them are exactly `T`. -/
def tableCheck : ℕ → ℕ → List ℕ → Bool
  | 0, _, T => T.isEmpty
  | fuel + 1, n, [] => if isPrimeB n then false else tableCheck fuel (n + 1) []
  | fuel + 1, n, q :: T' =>
    if isPrimeB n then (q == n) && tableCheck fuel (n + 1) T' else tableCheck fuel (n + 1) (q :: T')

lemma tableCheck_spec : ∀ (fuel n : ℕ) (T : List ℕ), tableCheck fuel n T = true →
    (List.range' n fuel).filter isPrimeB = T
  | 0, n, T, h => by
    simp only [tableCheck, List.isEmpty_iff] at h
    simp [h]
  | fuel + 1, n, T, h => by
    rw [List.range'_succ, List.filter_cons]
    cases T with
    | nil =>
      cases hp : isPrimeB n
      · rw [if_neg (by simp)]
        exact tableCheck_spec fuel (n + 1) [] (by simpa [tableCheck, hp] using h)
      · simp [tableCheck, hp] at h
    | cons q T' =>
      cases hp : isPrimeB n
      · rw [if_neg (by simp)]
        exact tableCheck_spec fuel (n + 1) (q :: T') (by simpa [tableCheck, hp] using h)
      · simp only [tableCheck, hp, ite_true, Bool.and_eq_true, beq_iff_eq] at h
        rw [if_pos rfl, h.1, tableCheck_spec fuel (n + 1) T' h.2]

set_option maxRecDepth 100000 in
lemma tc : tableCheck 10008 0 primesTable = true := by decide +kernel

lemma primesTable_eq : (List.range 10008).filter isPrimeB = primesTable := by
  rw [List.range_eq_range']
  exact tableCheck_spec 10008 0 primesTable tc

lemma primesTable_length : primesTable.length = 1230 := by decide +kernel

lemma filter_prime_eq :
    (List.range 10008).filter (fun x => decide (Nat.Prime x)) = primesTable := by
  rw [← primesTable_eq]
  apply List.filter_congr
  intro x hx
  rw [List.mem_range] at hx
  rw [Bool.eq_iff_iff, decide_eq_true_iff, isPrimeB_iff (by omega)]

lemma nth_prime_table (k : ℕ) (hk : k < 1230) : Nat.nth Nat.Prime k = primesTable.getD k 0 := by
  set L := (List.range 10008).filter (fun x => decide (Nat.Prime x)) with hL
  have hLT : L = primesTable := filter_prime_eq
  have hk' : k < L.length := by rw [hLT, primesTable_length]; exact hk
  have hcount := count_getD_filter_range Nat.Prime 10008 k hk'
  have hprime : Nat.Prime (L.getD k 0) := by
    have hmem : L.getD k 0 ∈ L := by
      rw [List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
    simpa [hL] using (List.mem_filter.1 hmem).2
  have := Nat.nth_count hprime
  rw [hcount] at this
  rw [this, hLT]

lemma nth_prime_1229 : Nat.nth Nat.Prime 1229 = 10007 := by
  rw [nth_prime_table 1229 (by norm_num)]
  decide +kernel

/-- The `v`-th prime below `10000` forces `v ≤ 1229`. -/
lemma le_1229_of_nth_prime_lt {v : ℕ} (hv : 1 ≤ v) (h : Nat.nth Nat.Prime (v - 1) < 10000) :
    v ≤ 1229 := by
  have h1 : Nat.primeCounting' (Nat.nth Nat.Prime (v - 1) + 1) = v := by
    unfold Nat.primeCounting'
    rw [Nat.count_succ, if_pos (Nat.prime_nth_prime _)]
    have := Nat.primeCounting'_nth_eq (v - 1)
    unfold Nat.primeCounting' at this
    omega
  have h2 : Nat.primeCounting' (Nat.nth Nat.Prime (v - 1) + 1) ≤ Nat.primeCounting' 10007 :=
    Nat.monotone_primeCounting' (by omega)
  have h3 : Nat.primeCounting' 10007 = 1229 := by
    have := Nat.primeCounting'_nth_eq 1229
    rwa [nth_prime_1229] at this
  omega

lemma fTable_eq : (primesTable.take 1229).map rev10 = fTable := by decide +kernel

lemma fTable_length : fTable.length = 1229 := by decide +kernel

lemma fTable_getD (i : ℕ) (hi : i < 1229) : fTable.getD i 0 = rev10 (primesTable.getD i 0) := by
  have hi1 : i < fTable.length := by rw [fTable_length]; exact hi
  have hi2 : i < primesTable.length := by rw [primesTable_length]; omega
  rw [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2,
    List.getElem_of_eq fTable_eq.symm hi1, List.getElem_map, List.getElem_take]

lemma f_eq_fTable {y : ℕ} (h1 : 1 ≤ y) (h2 : y ≤ 1229) : f y = fTable.getD (y - 1) 0 := by
  have hy : y ≠ 0 := by omega
  rw [f, if_neg hy, nth_prime_table (y - 1) (by omega), ← rev10_eq, fTable_getD (y - 1) (by omega)]

/-- For each index: the step leaves `{1, …, 1229}` or the rank drops. -/
def checkEdges : List ℕ → List ℕ → Bool
  | fy :: fs, r :: rs =>
    (decide (1229 < fy) || decide (rankL.getD (fy - 1) 0 < r)) && checkEdges fs rs
  | _, _ => true

lemma checkEdges_spec : ∀ (fs rs : List ℕ), checkEdges fs rs = true →
    ∀ i (hi : i < fs.length) (hi' : i < rs.length),
      1229 < fs[i] ∨ rankL.getD (fs[i] - 1) 0 < rs[i]
  | [], _, _, i, hi, _ => absurd hi (by simp)
  | _ :: _, [], _, i, _, hi' => absurd hi' (by simp)
  | fy :: fs, r :: rs, h, 0, _, _ => by
    simp only [checkEdges, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    simpa using h.1
  | fy :: fs, r :: rs, h, i + 1, hi, hi' => by
    simp only [checkEdges, Bool.and_eq_true] at h
    simpa using checkEdges_spec fs rs h.2 i (by simpa using hi) (by simpa using hi')

lemma edges_ok : checkEdges fTable rankL = true := by decide +kernel

lemma rankL_length : rankL.length = 1229 := by decide +kernel

lemma rank_lt {y : ℕ} (h1 : 1 ≤ y) (h2 : y ≤ 1229) (hf : f y ≤ 1229) :
    rankL.getD (f y - 1) 0 < rankL.getD (y - 1) 0 := by
  have hi : y - 1 < fTable.length := by rw [fTable_length]; omega
  have hi' : y - 1 < rankL.length := by rw [rankL_length]; omega
  rcases checkEdges_spec fTable rankL edges_ok (y - 1) hi hi' with h | h
  · rw [f_eq_fTable h1 h2, List.getD_eq_getElem _ _ hi] at hf; omega
  · rw [f_eq_fTable h1 h2, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi']
    exact h

/-- No cycle of the step map stays inside `{1, …, 1229}`. -/
lemma no_small_cycle {w P : ℕ} (hw1 : 1 ≤ w) (hP : 0 < P) (hcyc : f^[P] w = w)
    (hsmall : ∀ k, f^[k] w ≤ 1229) : False := by
  have hpos : ∀ k, 1 ≤ f^[k] w := fun k =>
    Nat.one_le_iff_ne_zero.2 (iterate_ne_zero (by omega) k)
  have hdec : ∀ k, rankL.getD (f^[k] w - 1) 0 + k ≤ rankL.getD (w - 1) 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := rank_lt (hpos k) (hsmall k) (by rw [← iterate_succ_apply' f k w]; exact hsmall (k + 1))
      rw [iterate_succ_apply']
      omega
  have := hdec P
  rw [hcyc] at this
  omega

end OeisA100475Proof

open Nat Function

namespace OeisA100475Proof

open OeisA100475

open Chebyshev in
/-- `π(x) log y ≤ x log 4 + y log y` for `1 ≤ y ≤ x` (after Mathlib's proof of
`Chebyshev.pi_le_log4_mul_div`, with a general split point `y`). -/
lemma pi_mul_log_le {x y : ℝ} (hy : 1 ≤ y) (hxy : y ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log y ≤ Real.log 4 * x + y * Real.log y := calc
  (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log y = ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log y := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.primesLE_card_eq_primeCounting]
  _ ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log p + (if (p : ℝ) ≤ y then Real.log y else 0)) := by
    refine Finset.sum_le_sum fun p _ => ?_
    split_ifs with h
    · linarith [Real.log_natCast_nonneg p]
    · have : Real.log y < Real.log p := Real.log_lt_log (by linarith) (not_le.mp h)
      linarith
  _ ≤ Real.log 4 * x + y * Real.log y := by
    rw [Finset.sum_add_distrib]
    gcongr ?_ + ?_
    · calc ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p = θ x := by
            rw [theta_eq_theta_coe_floor, theta_eq_sum_primesLE_log]
        _ ≤ Real.log 4 * x := theta_le_log4_mul_x (by linarith)
    · rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
      · exact Real.log_nonneg hy
      refine le_trans ?_ (Nat.floor_le (by linarith : (0 : ℝ) ≤ y))
      norm_cast
      rw [show ⌊y⌋₊ = (Finset.Icc 1 ⌊y⌋₊).card by simp]
      refine Finset.card_le_card fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE] at hp ⊢
      exact ⟨hp.1.2.one_le, Nat.le_floor hp.2⟩

lemma log_four_lt : Real.log 4 < 1.3863 := by
  have h := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [h4]; linarith

lemma log_ten_gt : (2.2794 : ℝ) < Real.log 10 := by
  have h2 := Real.log_two_gt_d9
  have h10 : Real.log 10 = 3 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (10 : ℝ) = 2 ^ 3 * (5 / 4) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  have h54 : (1 : ℝ) - (5 / 4)⁻¹ ≤ Real.log (5 / 4) := Real.one_sub_inv_le_log_of_pos (by norm_num)
  rw [h10]; norm_num at h54 ⊢; linarith

lemma primeCounting_pow_lt_of_nine_le {D : ℕ} (hD : 9 ≤ D) :
    Nat.primeCounting (10 ^ D) < 10 ^ (D - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, D = k + 2 := ⟨D - 2, by omega⟩
  have hk : 7 ≤ k := by omega
  have hx : ⌊((10 : ℝ) ^ (k + 2))⌋₊ = 10 ^ (k + 2) := by
    rw [show ((10 : ℝ) ^ (k + 2)) = ((10 ^ (k + 2) : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have hy1 : (1 : ℝ) ≤ (10 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hxy : (10 : ℝ) ^ k ≤ (10 : ℝ) ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have key := pi_mul_log_le hy1 hxy
  rw [hx, Real.log_pow] at key
  have hl4 := log_four_lt
  have hl10 := log_ten_gt
  by_contra hcon
  push Not at hcon
  have hcon' : ((10 : ℝ) ^ (k + 2 - 1)) ≤ (Nat.primeCounting (10 ^ (k + 2)) : ℝ) := by
    exact_mod_cast hcon
  have e1 : (10 : ℝ) ^ (k + 2) = 100 * (10 : ℝ) ^ k := by rw [pow_add]; ring
  have e2 : (10 : ℝ) ^ (k + 2 - 1) = 10 * (10 : ℝ) ^ k := by
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ]; ring
  set Y := (10 : ℝ) ^ k with hY
  set L := (k : ℝ) * Real.log 10 with hL
  have hYpos : 0 < Y := by positivity
  have hk' : (7 : ℝ) ≤ k := by exact_mod_cast hk
  have hLge : 7 * 2.2794 ≤ L := by
    have : (0 : ℝ) < Real.log 10 := by linarith
    nlinarith
  have hπ : 10 * Y * L ≤ Real.log 4 * (100 * Y) + Y * L := by
    have hL0 : 0 ≤ L := by linarith
    calc 10 * Y * L = (10 * Y) * L := by ring
      _ ≤ (Nat.primeCounting (10 ^ (k + 2)) : ℝ) * L := by
          rw [← e2]; exact mul_le_mul_of_nonneg_right hcon' hL0
      _ ≤ _ := by rw [← e1]; exact key
  have h9 : 9 * L ≤ 100 * Real.log 4 := by
    refine le_of_mul_le_mul_left ?_ hYpos
    nlinarith [hπ]
  linarith

lemma primeCounting'_nth_add_one {v : ℕ} (hv : 1 ≤ v) :
    Nat.primeCounting' (Nat.nth Nat.Prime (v - 1) + 1) = v := by
  unfold Nat.primeCounting'
  rw [Nat.count_succ, if_pos (Nat.prime_nth_prime _)]
  have := Nat.primeCounting'_nth_eq (v - 1)
  unfold Nat.primeCounting' at this
  omega

/-- Fewer than `10 ^ (D - 1)` primes below `10 ^ D`, for every `D ≥ 5`. -/
lemma primeCounting'_pow_lt {D : ℕ} (hD : 5 ≤ D) :
    Nat.primeCounting' (10 ^ D) < 10 ^ (D - 1) := by
  rcases Nat.lt_or_ge D 9 with h | h
  · interval_cases D
    · simpa using primeCounting'_1e5
    · simpa using primeCounting'_1e6
    · simpa using primeCounting'_1e7
    · simpa using primeCounting'_1e8
  · calc Nat.primeCounting' (10 ^ D) = Nat.primeCounting (10 ^ D - 1) :=
          (Nat.primeCounting_sub_one _).symm
      _ ≤ Nat.primeCounting (10 ^ D) := Nat.monotone_primeCounting (Nat.sub_le _ _)
      _ < 10 ^ (D - 1) := primeCounting_pow_lt_of_nine_le h

/- ## Main theorem -/

/-- On a cycle, every element `v` satisfies `p_v < 10 ^ D v`. -/
lemma nth_prime_lt_of_cycle {w P : ℕ} (hw : w ≠ 0) (hP : 0 < P) (hcyc : f^[P] w = w) (k : ℕ) :
    Nat.nth Nat.Prime (f^[k] w - 1) < 10 ^ D (f^[k] w) := by
  have hk : D (f^[k + 1] w) = D (f^[k] w) := by
    rw [D_iterate_eq_of_cycle hw hP hcyc (k + 1), D_iterate_eq_of_cycle hw hP hcyc k]
  rw [iterate_succ_apply', D_f (iterate_ne_zero hw k)] at hk
  rw [← hk]
  unfold D
  exact Nat.lt_base_pow_length_digits (by norm_num)

/-- Every element of a cycle is at most `1229`. -/
lemma cycle_le_1229 {w P : ℕ} (hw : w ≠ 0) (hP : 0 < P) (hcyc : f^[P] w = w) (k : ℕ) :
    f^[k] w ≤ 1229 := by
  have hlt := nth_prime_lt_of_cycle hw hP hcyc k
  set v := f^[k] w with hv
  have hv1 : 1 ≤ v := Nat.one_le_iff_ne_zero.2 (iterate_ne_zero hw k)
  rcases Nat.lt_or_ge (D v) 5 with hd | hd
  · apply le_1229_of_nth_prime_lt hv1
    calc Nat.nth Nat.Prime (v - 1) < 10 ^ D v := hlt
      _ ≤ 10 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 10000 := by norm_num
  · exfalso
    have hge : 10 ^ (D v - 1) ≤ v := by
      have h := Nat.base_pow_length_digits_le 10 v (by norm_num) (by omega)
      unfold D at hd ⊢
      rw [show (Nat.digits 10 v).length = (Nat.digits 10 v).length - 1 + 1 by omega,
        pow_succ] at h
      omega
    have h1 := primeCounting'_nth_add_one hv1
    have h2 : Nat.primeCounting' (Nat.nth Nat.Prime (v - 1) + 1) ≤
        Nat.primeCounting' (10 ^ D v) := Nat.monotone_primeCounting' hlt
    have h3 := primeCounting'_pow_lt hd
    omega

theorem conjecture_false :
    ¬ ∃ x : ℕ, 0 < x ∧ x ≠ 1 ∧ IsUltimatelyPeriodic (aStartAt x) := by
  rintro ⟨x, hx, -, N, P, hP, hper⟩
  have hw : f^[P] (f^[N] x) = f^[N] x := by
    have h := hper N le_rfl
    rw [aStartAt_eq_iterate, aStartAt_eq_iterate, add_comm, iterate_add_apply] at h
    exact h
  have hw0 : f^[N] x ≠ 0 := iterate_ne_zero (by omega) N
  exact no_small_cycle (Nat.one_le_iff_ne_zero.2 hw0) hP hw (cycle_le_1229 hw0 hP hw)

end OeisA100475Proof

theorem OMA.disproof : ¬ (type_of% @OeisA100475.conjecture) := by
  exact OeisA100475Proof.conjecture_false

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
