import OMAReductions.R_Erdos821_erdos_821_variants_lichtman_R1
import Mathlib

/-!
Step H2 of Erdos821.erdos_821.variants.lichtman.R1. The totient of a product of k distinct
primes from P is the product of the shifted primes, a B-smooth number in [1, X^k]. A B-smooth
number up to X^k is determined by its exponents at 1, ..., B, each at most log_2 (X^k), so there
are at most (log_2 (X^k) + 1)^B such values. By pigeonhole some value n is the totient of more
than z of these products, and distinct prime sets give distinct products, so g n > z.
The fibre of the totient over a positive n is finite because every m in it divides nothing larger
than n (n+1)^(n+2): each prime p dividing m has p - 1 dividing n.
-/

namespace OMA.P1Erdos821H2

theorem tot_prod (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Nat.totient (∏ p ∈ s, p) = ∏ p ∈ s, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors (∏ p ∈ s, p)
  rw [Nat.primeFactors_prod hs] at h
  have hpos : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hp => (hs p hp).pos)
  rw [mul_comm (∏ p ∈ s, p) (∏ p ∈ s, (p - 1))] at h
  exact Nat.eq_of_mul_eq_mul_right hpos h

theorem fin_fiber (n : ℕ) (hn : 0 < n) : {m : ℕ | Nat.totient m = n}.Finite := by
  apply (Set.finite_Iic (n * (n + 1) ^ (n + 2))).subset
  intro m hm
  have hm' : Nat.totient m = n := hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.totient_zero] at hm'
    omega
  have hsub : m.primeFactors ⊆ Finset.range (n + 2) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : Nat.totient p ∣ Nat.totient m :=
      Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.totient_prime hpp, hm'] at h1
    have := Nat.le_of_dvd hn h1
    rw [Finset.mem_range]
    omega
  have hprod : ∏ p ∈ m.primeFactors, p ≤ (n + 1) ^ (n + 2) := by
    calc ∏ p ∈ m.primeFactors, p ≤ (n + 1) ^ m.primeFactors.card :=
          Finset.prod_le_pow_card _ _ _ (fun p hp => by
            have := hsub hp
            rw [Finset.mem_range] at this
            omega)
      _ ≤ (n + 1) ^ (n + 2) := Nat.pow_le_pow_right (by omega)
          (by simpa using Finset.card_le_card hsub)
  have key := Nat.totient_mul_prod_primeFactors m
  rw [hm'] at key
  have h1 : 0 < ∏ p ∈ m.primeFactors, (p - 1) := Finset.prod_pos (fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega)
  show m ≤ n * (n + 1) ^ (n + 2)
  calc m = m * 1 := (mul_one m).symm
    _ ≤ m * ∏ p ∈ m.primeFactors, (p - 1) := Nat.mul_le_mul_left _ h1
    _ = n * ∏ p ∈ m.primeFactors, p := key.symm
    _ ≤ n * (n + 1) ^ (n + 2) := Nat.mul_le_mul_left _ hprod

end OMA.P1Erdos821H2

open scoped Classical in
open OMA.P1Erdos821H2 in
theorem OMA.solution : OMA.R_Erdos821_erdos_821_variants_lichtman_R1.H2 := by
  unfold OMA.R_Erdos821_erdos_821_variants_lichtman_R1.H2
  intro P X B k z hP hX hB hz hlt
  set L := Nat.log 2 (X ^ k) with hL
  let S := P.powersetCard k
  let tot : Finset ℕ → ℕ := fun s => ∏ p ∈ s, (p - 1)
  let T := (Finset.Icc 1 (X ^ k)).filter (fun n => ∀ q, q.Prime → q ∣ n → q ≤ B)
  have hmaps : ∀ s ∈ S, tot s ∈ T := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    obtain ⟨hsP, hsk⟩ := hs
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Finset.prod_pos (fun p hp => Nat.sub_pos_of_lt (hP p (hsP hp)).one_lt)
    · calc tot s ≤ X ^ s.card := Finset.prod_le_pow_card _ _ _ (fun p hp =>
            (Nat.sub_le p 1).trans (hX p (hsP hp)))
        _ = X ^ k := by rw [hsk]
    · intro q hq hqd
      obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hqd
      exact hB p (hsP hp) q hq hqp
  have hbound : ∀ n ∈ T, ∀ q, n.factorization q ≤ L := by
    intro n hn q
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    by_cases hq : q.Prime
    · apply Nat.le_log_of_pow_le one_lt_two
      calc 2 ^ n.factorization q ≤ q ^ n.factorization q := Nat.pow_le_pow_left hq.two_le _
        _ ≤ n := Nat.ordProj_le q (by omega)
        _ ≤ X ^ k := hn.1.2
    · rw [Nat.factorization_eq_zero_of_not_prime n hq]
      exact Nat.zero_le _
  have hTcard : T.card ≤ (L + 1) ^ B := by
    let enc : ℕ → (Fin B → Fin (L + 1)) := fun n i =>
      ⟨min (n.factorization (i.val + 1)) L, Nat.lt_succ_of_le (min_le_right _ _)⟩
    have hinj : Set.InjOn enc T := by
      intro n hn m hm hnm
      rw [Finset.mem_coe] at hn hm
      have hn' := Finset.mem_filter.mp hn
      have hm' := Finset.mem_filter.mp hm
      rw [Finset.mem_Icc] at hn' hm'
      apply Nat.eq_of_factorization_eq (by omega) (by omega)
      intro q
      by_cases hq : q.Prime
      · by_cases hqB : q ≤ B
        · have h2 := hq.two_le
          have hi : q - 1 < B := by omega
          have h1 : min (n.factorization (q - 1 + 1)) L = min (m.factorization (q - 1 + 1)) L :=
            congrArg (fun f => (f ⟨q - 1, hi⟩ : Fin (L + 1)).val) hnm
          rw [show q - 1 + 1 = q by omega, min_eq_left (hbound n hn q),
            min_eq_left (hbound m hm q)] at h1
          exact h1
        · rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hqB (hn'.2 q hq h)),
            Nat.factorization_eq_zero_of_not_dvd (fun h => hqB (hm'.2 q hq h))]
      · rw [Nat.factorization_eq_zero_of_not_prime n hq, Nat.factorization_eq_zero_of_not_prime m hq]
    calc T.card ≤ (Finset.univ : Finset (Fin B → Fin (L + 1))).card :=
          Finset.card_le_card_of_injOn enc (by intro a _; simp) hinj
      _ = (L + 1) ^ B := by simp
  have hS : S.card = P.card.choose k := Finset.card_powersetCard k P
  obtain ⟨n, hnT, hnz⟩ : ∃ n ∈ T, z < ((S.filter (fun s => tot s = n)).card : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hsum : (S.card : ℝ) = ∑ n ∈ T, ((S.filter (fun s => tot s = n)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    have h1 : (S.card : ℝ) ≤ T.card * z := by
      rw [hsum]
      calc ∑ n ∈ T, ((S.filter (fun s => tot s = n)).card : ℝ) ≤ ∑ n ∈ T, z :=
            Finset.sum_le_sum hcon
        _ = T.card * z := by rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : (T.card : ℝ) * z ≤ ((L + 1 : ℕ) : ℝ) ^ B * z := by
      apply mul_le_mul_of_nonneg_right _ hz
      exact_mod_cast hTcard
    rw [hS] at h1
    linarith
  have hn' := Finset.mem_filter.mp hnT
  rw [Finset.mem_Icc] at hn'
  refine ⟨n, hn'.1.1, hn'.1.2, lt_of_lt_of_le hnz ?_⟩
  have himg : (((S.filter (fun s => tot s = n)).image (fun s => ∏ p ∈ s, p) : Finset ℕ) : Set ℕ)
      ⊆ {m | Nat.totient m = n} := by
    intro m hm
    rw [Finset.coe_image] at hm
    obtain ⟨s, hs, rfl⟩ := hm
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hs
    show Nat.totient (∏ p ∈ s, p) = n
    rw [tot_prod s (fun p hp => hP p (hs.1.1 hp))]
    exact hs.2
  have hinj : Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p)
      ((S.filter (fun s => tot s = n) : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro s hs s' hs' h
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard] at hs hs'
    have h' : ∏ p ∈ s, p = ∏ p ∈ s', p := h
    have e1 := Nat.primeFactors_prod (fun p hp => hP p (hs.1.1 hp))
    have e2 := Nat.primeFactors_prod (fun p hp => hP p (hs'.1.1 hp))
    calc s = (∏ p ∈ s, p).primeFactors := e1.symm
      _ = (∏ p ∈ s', p).primeFactors := by rw [h']
      _ = s' := e2
  have hfib : (S.filter (fun s => tot s = n)).card ≤ Erdos821.g n := by
    calc (S.filter (fun s => tot s = n)).card
        = ((S.filter (fun s => tot s = n)).image (fun s => ∏ p ∈ s, p)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ = ((((S.filter (fun s => tot s = n)).image (fun s => ∏ p ∈ s, p) : Finset ℕ)
            : Set ℕ)).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ {m | Nat.totient m = n}.ncard := Set.ncard_le_ncard himg (fin_fiber n hn'.1.1)
      _ = Erdos821.g n := rfl
  exact_mod_cast hfib
