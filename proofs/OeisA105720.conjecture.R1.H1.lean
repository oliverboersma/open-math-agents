import OMAReductions.R_OeisA105720_conjecture_R1
import Mathlib

/-! Step H1: the sum of the primes from the n-th to the 2n-th is a square for n = 3, 6, 4072.
Primality below 291 squared is decided by trial division by odd numbers, written so that the
kernel can evaluate it. The sum over indices of the n-th prime function is turned into a sum
over the primes of an interval, whose endpoints are pinned down by counting primes. -/

-- Step OeisA105720.conjecture.R1.H1: hypothesis H1 of reduction OeisA105720.conjecture.R1
-- Credit: @ivillar

namespace A105720Step

/-- Trial division of `n` by the odd numbers `289 - 2 * j` for `j < k`, smallest divisor first. -/
def loop (n : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 =>
    if n < (289 - 2 * k) * (289 - 2 * k) then true
    else if n % (289 - 2 * k) = 0 then false
    else loop n k

/-- A primality test that is correct below 291 squared. -/
def isP (n : ℕ) : Bool :=
  decide (2 ≤ n) && (decide (n = 2) || decide (n % 2 = 1)) && loop n 144

lemma loop_iff (n : ℕ) : ∀ k : ℕ, loop n k = true ↔
    ∀ j < k, (289 - 2 * j) * (289 - 2 * j) ≤ n → ¬ (289 - 2 * j) ∣ n := by
  intro k
  induction k with
  | zero => simp [loop]
  | succ k ih =>
    rw [loop]
    by_cases h1 : n < (289 - 2 * k) * (289 - 2 * k)
    · rw [if_pos h1]
      refine ⟨fun _ j hj hle => ?_, fun _ => rfl⟩
      have h2 : 289 - 2 * k ≤ 289 - 2 * j := by omega
      have h3 := Nat.mul_le_mul h2 h2
      omega
    · rw [if_neg h1]
      by_cases h2 : n % (289 - 2 * k) = 0
      · rw [if_pos h2]
        refine ⟨fun h => absurd h (by simp), fun h => ?_⟩
        exact absurd (Nat.dvd_of_mod_eq_zero h2) (h k (Nat.lt_succ_self k) (by omega))
      · rw [if_neg h2, ih]
        constructor
        · intro h j hj hle
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
          · exact h j hlt hle
          · exact fun hd => h2 (Nat.mod_eq_zero_of_dvd hd)
        · intro h j hj hle
          exact h j (Nat.lt_succ_of_lt hj) hle

lemma isP_iff (n : ℕ) (hn : n < 84681) : isP n = true ↔ n.Prime := by
  unfold isP
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, loop_iff]
  constructor
  · rintro ⟨⟨h2, hpar⟩, hloop⟩
    rw [Nat.prime_def_le_sqrt]
    refine ⟨h2, fun m hm2 hms hdvd => ?_⟩
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
    rcases hpar with rfl | hodd
    · have : 2 * 2 ≤ m * m := Nat.mul_le_mul hm2 hm2
      omega
    · have hmodd : m % 2 = 1 := by
        by_contra hcon
        have h2m : 2 ∣ m := by omega
        have h2n : 2 ∣ n := h2m.trans hdvd
        omega
      have hm291 : m < 291 := by
        by_contra hcon
        have : 291 * 291 ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hj : (289 - m) / 2 < 144 := by omega
      have hd : 289 - 2 * ((289 - m) / 2) = m := by omega
      have h3 := hloop ((289 - m) / 2) hj
      rw [hd] at h3
      exact h3 hmm hdvd
  · intro hp
    refine ⟨⟨hp.two_le, ?_⟩, fun j hj hle hdvd => ?_⟩
    · rcases hp.eq_two_or_odd with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases (Nat.dvd_prime hp).mp hdvd with h | h
      · omega
      · rw [h] at hle
        have h2 := hp.two_le
        nlinarith

/-- Number of primes in `[lo, lo + len)`, for the kernel. -/
def cntP (lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | len + 1 => cntP lo len + (if isP (lo + len) then 1 else 0)

/-- Sum of the primes in `[lo, lo + len)`, for the kernel. -/
def sumP (lo : ℕ) : ℕ → ℕ
  | 0 => 0
  | len + 1 => sumP lo len + (if isP (lo + len) then lo + len else 0)

def cntChunks (lo size : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => cntChunks lo size k + cntP (lo + size * k) size

def sumChunks (lo size : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumChunks lo size k + sumP (lo + size * k) size

lemma cntP_add (lo a : ℕ) : ∀ b : ℕ, cntP lo (a + b) = cntP lo a + cntP (lo + a) b
  | 0 => by simp [cntP]
  | b + 1 => by
    rw [← Nat.add_assoc, cntP, cntP, cntP_add lo a b, Nat.add_assoc lo a b, Nat.add_assoc]

lemma sumP_add (lo a : ℕ) : ∀ b : ℕ, sumP lo (a + b) = sumP lo a + sumP (lo + a) b
  | 0 => by simp [sumP]
  | b + 1 => by
    rw [← Nat.add_assoc, sumP, sumP, sumP_add lo a b, Nat.add_assoc lo a b, Nat.add_assoc]

lemma cntChunks_eq (lo size : ℕ) : ∀ k : ℕ, cntChunks lo size k = cntP lo (size * k)
  | 0 => by simp [cntChunks, cntP]
  | k + 1 => by rw [cntChunks, cntChunks_eq lo size k, Nat.mul_succ, cntP_add]

lemma sumChunks_eq (lo size : ℕ) : ∀ k : ℕ, sumChunks lo size k = sumP lo (size * k)
  | 0 => by simp [sumChunks, sumP]
  | k + 1 => by rw [sumChunks, sumChunks_eq lo size k, Nat.mul_succ, sumP_add]

lemma count_eq : ∀ n : ℕ, n ≤ 84681 → Nat.count Nat.Prime n = cntP 0 n
  | 0, _ => by simp [cntP]
  | n + 1, hn => by
    rw [Nat.count_succ, cntP, count_eq n (by omega), Nat.zero_add]
    congr 1
    exact if_congr (isP_iff n (by omega)).symm rfl rfl

lemma sum_eq (lo : ℕ) : ∀ len : ℕ, lo + len ≤ 84681 →
    ∑ m ∈ (Finset.Ico lo (lo + len)).filter Nat.Prime, m = sumP lo len
  | 0, _ => by simp [sumP]
  | len + 1, hlen => by
    have ih := sum_eq lo len (by omega)
    rw [Finset.sum_filter] at ih ⊢
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right lo len), ih, sumP]
    congr 1
    exact if_congr (isP_iff (lo + len) (by omega)).symm rfl rfl

lemma sum_nth (a b : ℕ) (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, Nat.nth Nat.Prime i =
      ∑ m ∈ (Finset.Ico (Nat.nth Nat.Prime a) (Nat.nth Nat.Prime b)).filter Nat.Prime, m := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    have h1 : Nat.nth Nat.Prime a ≤ Nat.nth Nat.Prime b := hmono.monotone hb
    have h2 : Nat.nth Nat.Prime b < Nat.nth Nat.Prime (b + 1) := hmono (Nat.lt_succ_self b)
    have hsplit : (Finset.Ico (Nat.nth Nat.Prime a) (Nat.nth Nat.Prime (b + 1))).filter Nat.Prime =
        (Finset.Ico (Nat.nth Nat.Prime a) (Nat.nth Nat.Prime b)).filter Nat.Prime ∪
          {Nat.nth Nat.Prime b} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨hm1, hm2⟩, hmp⟩
        by_cases hlt : m < Nat.nth Nat.Prime b
        · exact Or.inl ⟨⟨hm1, hlt⟩, hmp⟩
        · right
          have hmk : Nat.nth Nat.Prime (Nat.count Nat.Prime m) = m := Nat.nth_count hmp
          have hk1 : Nat.count Nat.Prime m < b + 1 := by
            by_contra hcon
            have h3 := hmono.monotone (Nat.le_of_not_lt hcon)
            rw [hmk] at h3
            omega
          have hk2 : b ≤ Nat.count Nat.Prime m := by
            by_contra hcon
            have h3 := hmono (Nat.lt_of_not_le hcon)
            rw [hmk] at h3
            omega
          have hk : Nat.count Nat.Prime m = b := by omega
          rw [← hk]
          exact hmk.symm
      · rintro (⟨⟨hm1, hm2⟩, hmp⟩ | rfl)
        · exact ⟨⟨hm1, by omega⟩, hmp⟩
        · exact ⟨⟨h1, h2⟩, Nat.prime_nth_prime b⟩
    rw [Finset.sum_Ico_succ_top hb, ih, hsplit, Finset.sum_union, Finset.sum_singleton]
    rw [Finset.disjoint_singleton_right]
    simp

/-- The value `a n` as a kernel-computable sum, once the two end primes are identified. -/
lemma a_eq (n P Q : ℕ) (hn : 0 < n) (hPQ : P ≤ Q) (hQ : Q < 84681)
    (hP : isP P = true) (hQp : isP Q = true)
    (hcP : cntP 0 P = n - 1) (hcQ : cntP 0 Q = 2 * n) :
    OeisA105720.a n = sumP P (Q - P) := by
  have hPp : P.Prime := (isP_iff P (by omega)).mp hP
  have hQpr : Q.Prime := (isP_iff Q hQ).mp hQp
  have e1 : Nat.nth Nat.Prime (n - 1) = P := by
    rw [← hcP, ← count_eq P (by omega)]
    exact Nat.nth_count hPp
  have e2 : Nat.nth Nat.Prime (2 * n) = Q := by
    rw [← hcQ, ← count_eq Q (by omega)]
    exact Nat.nth_count hQpr
  unfold OeisA105720.a
  rw [if_neg (by omega), sum_nth (n - 1) (2 * n) (by omega), e1, e2]
  have h3 := sum_eq P (Q - P) (by omega)
  rw [Nat.add_sub_cancel' hPQ] at h3
  exact h3

lemma k1 : cntChunks 0 500 77 + cntP (0 + 500 * 77) 153 = 4071 := by decide +kernel

lemma k2 : cntChunks 38653 500 89 + cntP (38653 + 500 * 89) 278 = 4073 := by decide +kernel

lemma k3 : sumChunks 38653 500 89 + sumP (38653 + 500 * 89) 278 = 15735 * 15735 := by
  decide +kernel

end A105720Step

open A105720Step

theorem OMA.solution : OMA.R_OeisA105720_conjecture_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl
  · refine ⟨6, ?_⟩
    rw [a_eq 3 5 17 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · refine ⟨13, ?_⟩
    rw [a_eq 6 13 41 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)]
    decide +kernel
  · have c1 : cntP 0 38653 = 4071 := by
      rw [show (38653 : ℕ) = 500 * 77 + 153 from rfl, cntP_add, ← cntChunks_eq]
      exact k1
    have c2 : cntP 38653 44778 = 4073 := by
      rw [show (44778 : ℕ) = 500 * 89 + 278 from rfl, cntP_add, ← cntChunks_eq]
      exact k2
    have c3 : cntP 0 83431 = 2 * 4072 := by
      rw [show (83431 : ℕ) = 38653 + 44778 from rfl, cntP_add, c1, Nat.zero_add, c2]
    have s1 : sumP 38653 (83431 - 38653) = 15735 * 15735 := by
      rw [show (83431 - 38653 : ℕ) = 500 * 89 + 278 from rfl, sumP_add, ← sumChunks_eq]
      exact k3
    refine ⟨15735, ?_⟩
    rw [a_eq 4072 38653 83431 (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
      (by decide +kernel) c1 c3]
    exact s1
