import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1.H2.R1
-- Credit: @adammcarter
-- Splits step H2 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H3.R1 (3 the only repeated odd prime,
-- exponent e of 3 one of 359, 362, 446, 458, 487, 499) by ruling out e = 359, 362, 446 and 487.
-- Proving the two H proves the step.
--
-- PROVED BELOW (each also rules out every odd multiple of the exponent):
--   e = 359 (kill3_e359, weight): the prime factor q of (3^359 + 1)/4 (171 digits) is a simple prime
--     of n, and the odd primes of p + 1 for a simple prime p are again simple primes.  Following these
--     chains gives 46 distinct simple primes, among them 5, 7, 11, 13, 17, 31, 37, whose weight
--     prod (p + 1)/p is 2.059974 >= 2, while the balance equation gives prod over all simple
--     primes of (p + 1)/p = 2 (2^a/(2^a+1)) (3^e/(3^e+1)) < 2 (weight_kill).
--   e = 362, 446, 487 (kill3_e362, kill3_e446, kill3_e487): chains of forced simple primes from the
--     prime factors of 3^e + 1 (93, 212 and 232 digits on the chain) end in a prime with two sources
--     or a square, contradicting the balance equation.
-- Witness primes above 4.3 * 10^7 are certified by the Lucas test; factorizations from factordb and
-- ECM, re-checked here.
--
-- H1 (OPEN): e = 458, a no odd multiple of DA.
-- H2 (OPEN): e = 499, a no odd multiple of DA.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1 hiding H1 H2 main

-- H1: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent e of 3 equal to 458, and a no odd multiple of any d in DA.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 458 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

-- H2: the same with exponent e of 3 equal to 499.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 499 →
    (∀ d ∈ ({10, 12, 14, 18, 20, 22, 24, 25, 26, 27, 28, 29, 32, 33, 34, 35, 37, 38, 39, 45, 46, 48,
        51, 52, 55, 56, 57, 59, 62, 63, 64, 65, 67, 68, 69, 74, 76, 77, 80, 82, 83, 85, 86, 91,
        94, 95, 97, 106, 112, 115, 116, 118, 119, 121, 122, 123, 124, 131, 133, 134, 141, 142,
        143, 146, 147, 149, 152, 155, 157} : Finset ℕ),
      padicValNat 2 n % (2 * d) ≠ d) →
    padicValNat 2 n ≤ A

theorem prime_47029186391731 : Nat.Prime 47029186391731 := by
  refine lucas_primality 47029186391731 (13 : ZMod 47029186391731) ?_ (fun q hq hd => ?_)
  · rw [show 47029186391731 - 1 = 47029186391730 from by norm_num]
    reduce_mod_char
  · have e : 47029186391731 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 43 ^ 1, 179 ^ 1, 2663 ^ 1, 76481 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47029186391731 - 1) / 2 = 23514593195865 from by norm_num]
      have h2 : (13 : ZMod 47029186391731) ^ 23514593195865 = ((47029186391730 : ℕ) : ZMod 47029186391731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47029186391731 - 1) / 3 = 15676395463910 from by norm_num]
      have h2 : (13 : ZMod 47029186391731) ^ 15676395463910 = ((7550467011405 : ℕ) : ZMod 47029186391731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47029186391731 - 1) / 5 = 9405837278346 from by norm_num]
      have h2 : (13 : ZMod 47029186391731) ^ 9405837278346 = ((29213044674843 : ℕ) : ZMod 47029186391731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47029186391731 - 1) / 43 = 1093702009110 from by norm_num]
      have h2 : (13 : ZMod 47029186391731) ^ 1093702009110 = ((6759269526144 : ℕ) : ZMod 47029186391731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47029186391731 - 1) / 179 = 262732884870 from by norm_num]
      have h2 : (13 : ZMod 47029186391731) ^ 262732884870 = ((24042229890388 : ℕ) : ZMod 47029186391731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47029186391731 - 1) / 2663 = 17660227710 from by norm_num]
      have h2 : (13 : ZMod 47029186391731) ^ 17660227710 = ((29184600833408 : ℕ) : ZMod 47029186391731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47029186391731 - 1) / 76481 = 614913330 from by norm_num]
      have h2 : (13 : ZMod 47029186391731) ^ 614913330 = ((10534756318121 : ℕ) : ZMod 47029186391731) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_86263523 : Nat.Prime 86263523 := by
  refine lucas_primality 86263523 (2 : ZMod 86263523) ?_ (fun q hq hd => ?_)
  · rw [show 86263523 - 1 = 86263522 from by norm_num]
    reduce_mod_char
  · have e : 86263523 - 1 = [2 ^ 1, 113 ^ 1, 381697 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86263523 - 1) / 2 = 43131761 from by norm_num]
      have h2 : (2 : ZMod 86263523) ^ 43131761 = ((86263522 : ℕ) : ZMod 86263523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86263523 - 1) / 113 = 763394 from by norm_num]
      have h2 : (2 : ZMod 86263523) ^ 763394 = ((13538629 : ℕ) : ZMod 86263523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (86263523 - 1) / 381697 = 226 from by norm_num]
      have h2 : (2 : ZMod 86263523) ^ 226 = ((79992893 : ℕ) : ZMod 86263523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_291066066130451 : Nat.Prime 291066066130451 := by
  refine lucas_primality 291066066130451 (2 : ZMod 291066066130451) ?_ (fun q hq hd => ?_)
  · rw [show 291066066130451 - 1 = 291066066130450 from by norm_num]
    reduce_mod_char
  · have e : 291066066130451 - 1 = [2 ^ 1, 5 ^ 2, 13 ^ 1, 29 ^ 1, 179 ^ 1, 86263523 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291066066130451 - 1) / 2 = 145533033065225 from by norm_num]
      have h2 : (2 : ZMod 291066066130451) ^ 145533033065225 = ((291066066130450 : ℕ) : ZMod 291066066130451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291066066130451 - 1) / 5 = 58213213226090 from by norm_num]
      have h2 : (2 : ZMod 291066066130451) ^ 58213213226090 = ((214839756259023 : ℕ) : ZMod 291066066130451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291066066130451 - 1) / 13 = 22389697394650 from by norm_num]
      have h2 : (2 : ZMod 291066066130451) ^ 22389697394650 = ((183437667563487 : ℕ) : ZMod 291066066130451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291066066130451 - 1) / 29 = 10036760901050 from by norm_num]
      have h2 : (2 : ZMod 291066066130451) ^ 10036760901050 = ((24009619317301 : ℕ) : ZMod 291066066130451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291066066130451 - 1) / 179 = 1626067408550 from by norm_num]
      have h2 : (2 : ZMod 291066066130451) ^ 1626067408550 = ((230263944717308 : ℕ) : ZMod 291066066130451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_86263523).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291066066130451 - 1) / 86263523 = 3374150 from by norm_num]
      have h2 : (2 : ZMod 291066066130451) ^ 3374150 = ((54065946467019 : ℕ) : ZMod 291066066130451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9248363581047133 : Nat.Prime 9248363581047133 := by
  refine lucas_primality 9248363581047133 (2 : ZMod 9248363581047133) ?_ (fun q hq hd => ?_)
  · rw [show 9248363581047133 - 1 = 9248363581047132 from by norm_num]
    reduce_mod_char
  · have e : 9248363581047133 - 1 = [2 ^ 2, 3 ^ 1, 179 ^ 1, 367 ^ 1, 1009 ^ 1, 11627153 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9248363581047133 - 1) / 2 = 4624181790523566 from by norm_num]
      have h2 : (2 : ZMod 9248363581047133) ^ 4624181790523566 = ((9248363581047132 : ℕ) : ZMod 9248363581047133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9248363581047133 - 1) / 3 = 3082787860349044 from by norm_num]
      have h2 : (2 : ZMod 9248363581047133) ^ 3082787860349044 = ((6461033963970002 : ℕ) : ZMod 9248363581047133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9248363581047133 - 1) / 179 = 51666835648308 from by norm_num]
      have h2 : (2 : ZMod 9248363581047133) ^ 51666835648308 = ((1230272259852944 : ℕ) : ZMod 9248363581047133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9248363581047133 - 1) / 367 = 25199900765796 from by norm_num]
      have h2 : (2 : ZMod 9248363581047133) ^ 25199900765796 = ((7009050521883961 : ℕ) : ZMod 9248363581047133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9248363581047133 - 1) / 1009 = 9165870744348 from by norm_num]
      have h2 : (2 : ZMod 9248363581047133) ^ 9165870744348 = ((3890546707566927 : ℕ) : ZMod 9248363581047133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9248363581047133 - 1) / 11627153 = 795410844 from by norm_num]
      have h2 : (2 : ZMod 9248363581047133) ^ 795410844 = ((8613734297796202 : ℕ) : ZMod 9248363581047133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6779963644378513811 : Nat.Prime 6779963644378513811 := by
  refine lucas_primality 6779963644378513811 (2 : ZMod 6779963644378513811) ?_ (fun q hq hd => ?_)
  · rw [show 6779963644378513811 - 1 = 6779963644378513810 from by norm_num]
    reduce_mod_char
  · have e : 6779963644378513811 - 1 = [2 ^ 1, 5 ^ 1, 13 ^ 1, 17 ^ 1, 179 ^ 1, 229 ^ 1, 170111 ^ 1, 439961 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6779963644378513811 - 1) / 2 = 3389981822189256905 from by norm_num]
      have h2 : (2 : ZMod 6779963644378513811) ^ 3389981822189256905 = ((6779963644378513810 : ℕ) : ZMod 6779963644378513811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6779963644378513811 - 1) / 5 = 1355992728875702762 from by norm_num]
      have h2 : (2 : ZMod 6779963644378513811) ^ 1355992728875702762 = ((1700949972191430109 : ℕ) : ZMod 6779963644378513811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6779963644378513811 - 1) / 13 = 521535664952193370 from by norm_num]
      have h2 : (2 : ZMod 6779963644378513811) ^ 521535664952193370 = ((3678050416443826143 : ℕ) : ZMod 6779963644378513811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6779963644378513811 - 1) / 17 = 398821390845794930 from by norm_num]
      have h2 : (2 : ZMod 6779963644378513811) ^ 398821390845794930 = ((416967886302784686 : ℕ) : ZMod 6779963644378513811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6779963644378513811 - 1) / 179 = 37876891868036390 from by norm_num]
      have h2 : (2 : ZMod 6779963644378513811) ^ 37876891868036390 = ((94143178827 : ℕ) : ZMod 6779963644378513811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6779963644378513811 - 1) / 229 = 29606828141390890 from by norm_num]
      have h2 : (2 : ZMod 6779963644378513811) ^ 29606828141390890 = ((3747082255178342210 : ℕ) : ZMod 6779963644378513811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6779963644378513811 - 1) / 170111 = 39856115385710 from by norm_num]
      have h2 : (2 : ZMod 6779963644378513811) ^ 39856115385710 = ((1556283913140710874 : ℕ) : ZMod 6779963644378513811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6779963644378513811 - 1) / 439961 = 15410374202210 from by norm_num]
      have h2 : (2 : ZMod 6779963644378513811) ^ 15410374202210 = ((3773920280879848600 : ℕ) : ZMod 6779963644378513811) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_93151867 : Nat.Prime 93151867 := by
  refine lucas_primality 93151867 (2 : ZMod 93151867) ?_ (fun q hq hd => ?_)
  · rw [show 93151867 - 1 = 93151866 from by norm_num]
    reduce_mod_char
  · have e : 93151867 - 1 = [2 ^ 1, 3 ^ 1, 37 ^ 1, 419603 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93151867 - 1) / 2 = 46575933 from by norm_num]
      have h2 : (2 : ZMod 93151867) ^ 46575933 = ((93151866 : ℕ) : ZMod 93151867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93151867 - 1) / 3 = 31050622 from by norm_num]
      have h2 : (2 : ZMod 93151867) ^ 31050622 = ((42610470 : ℕ) : ZMod 93151867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93151867 - 1) / 37 = 2517618 from by norm_num]
      have h2 : (2 : ZMod 93151867) ^ 2517618 = ((49400857 : ℕ) : ZMod 93151867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (93151867 - 1) / 419603 = 222 from by norm_num]
      have h2 : (2 : ZMod 93151867) ^ 222 = ((17268982 : ℕ) : ZMod 93151867) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_34466190791 : Nat.Prime 34466190791 := by
  refine lucas_primality 34466190791 (7 : ZMod 34466190791) ?_ (fun q hq hd => ?_)
  · rw [show 34466190791 - 1 = 34466190790 from by norm_num]
    reduce_mod_char
  · have e : 34466190791 - 1 = [2 ^ 1, 5 ^ 1, 37 ^ 1, 93151867 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34466190791 - 1) / 2 = 17233095395 from by norm_num]
      have h2 : (7 : ZMod 34466190791) ^ 17233095395 = ((34466190790 : ℕ) : ZMod 34466190791) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34466190791 - 1) / 5 = 6893238158 from by norm_num]
      have h2 : (7 : ZMod 34466190791) ^ 6893238158 = ((59013944 : ℕ) : ZMod 34466190791) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34466190791 - 1) / 37 = 931518670 from by norm_num]
      have h2 : (7 : ZMod 34466190791) ^ 931518670 = ((4650825222 : ℕ) : ZMod 34466190791) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_93151867).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (34466190791 - 1) / 93151867 = 370 from by norm_num]
      have h2 : (7 : ZMod 34466190791) ^ 370 = ((3392652463 : ℕ) : ZMod 34466190791) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_598870342019651691538195877 : Nat.Prime 598870342019651691538195877 := by
  refine lucas_primality 598870342019651691538195877 (2 : ZMod 598870342019651691538195877) ?_ (fun q hq hd => ?_)
  · rw [show 598870342019651691538195877 - 1 = 598870342019651691538195876 from by norm_num]
    reduce_mod_char
  · have e : 598870342019651691538195877 - 1 = [2 ^ 2, 2953 ^ 1, 50707 ^ 1, 29010029 ^ 1, 34466190791 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (598870342019651691538195877 - 1) / 2 = 299435171009825845769097938 from by norm_num]
      have h2 : (2 : ZMod 598870342019651691538195877) ^ 299435171009825845769097938 = ((598870342019651691538195876 : ℕ) : ZMod 598870342019651691538195877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (598870342019651691538195877 - 1) / 2953 = 202800657642956888431492 from by norm_num]
      have h2 : (2 : ZMod 598870342019651691538195877) ^ 202800657642956888431492 = ((325640333438445930967636588 : ℕ) : ZMod 598870342019651691538195877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (598870342019651691538195877 - 1) / 50707 = 11810407675856423995468 from by norm_num]
      have h2 : (2 : ZMod 598870342019651691538195877) ^ 11810407675856423995468 = ((558379807374289564991821368 : ℕ) : ZMod 598870342019651691538195877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (598870342019651691538195877 - 1) / 29010029 = 20643562335620267444 from by norm_num]
      have h2 : (2 : ZMod 598870342019651691538195877) ^ 20643562335620267444 = ((494358764119757811184385325 : ℕ) : ZMod 598870342019651691538195877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_34466190791).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (598870342019651691538195877 - 1) / 34466190791 = 17375588316421436 from by norm_num]
      have h2 : (2 : ZMod 598870342019651691538195877) ^ 17375588316421436 = ((465075117864568902458607469 : ℕ) : ZMod 598870342019651691538195877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_161868664744491655705858963594331 : Nat.Prime 161868664744491655705858963594331 := by
  refine lucas_primality 161868664744491655705858963594331 (7 : ZMod 161868664744491655705858963594331) ?_ (fun q hq hd => ?_)
  · rw [show 161868664744491655705858963594331 - 1 = 161868664744491655705858963594330 from by norm_num]
    reduce_mod_char
  · have e : 161868664744491655705858963594331 - 1 = [2 ^ 1, 5 ^ 1, 151 ^ 1, 179 ^ 1, 598870342019651691538195877 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161868664744491655705858963594331 - 1) / 2 = 80934332372245827852929481797165 from by norm_num]
      have h2 : (7 : ZMod 161868664744491655705858963594331) ^ 80934332372245827852929481797165 = ((161868664744491655705858963594330 : ℕ) : ZMod 161868664744491655705858963594331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161868664744491655705858963594331 - 1) / 5 = 32373732948898331141171792718866 from by norm_num]
      have h2 : (7 : ZMod 161868664744491655705858963594331) ^ 32373732948898331141171792718866 = ((57752308590543080816607308053776 : ℕ) : ZMod 161868664744491655705858963594331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161868664744491655705858963594331 - 1) / 151 = 1071977912215176527853370619830 from by norm_num]
      have h2 : (7 : ZMod 161868664744491655705858963594331) ^ 1071977912215176527853370619830 = ((75602975440849736810359521601931 : ℕ) : ZMod 161868664744491655705858963594331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161868664744491655705858963594331 - 1) / 179 = 904294216449674054222675774270 from by norm_num]
      have h2 : (7 : ZMod 161868664744491655705858963594331) ^ 904294216449674054222675774270 = ((129140163 : ℕ) : ZMod 161868664744491655705858963594331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_598870342019651691538195877).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (161868664744491655705858963594331 - 1) / 598870342019651691538195877 = 270290 from by norm_num]
      have h2 : (7 : ZMod 161868664744491655705858963594331) ^ 270290 = ((157615517070125422484453524701974 : ℕ) : ZMod 161868664744491655705858963594331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1085893902234677 : Nat.Prime 1085893902234677 := by
  refine lucas_primality 1085893902234677 (2 : ZMod 1085893902234677) ?_ (fun q hq hd => ?_)
  · rw [show 1085893902234677 - 1 = 1085893902234676 from by norm_num]
    reduce_mod_char
  · have e : 1085893902234677 - 1 = [2 ^ 2, 1723 ^ 1, 117041 ^ 1, 1346183 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1085893902234677 - 1) / 2 = 542946951117338 from by norm_num]
      have h2 : (2 : ZMod 1085893902234677) ^ 542946951117338 = ((1085893902234676 : ℕ) : ZMod 1085893902234677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1085893902234677 - 1) / 1723 = 630234418012 from by norm_num]
      have h2 : (2 : ZMod 1085893902234677) ^ 630234418012 = ((60224507188612 : ℕ) : ZMod 1085893902234677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1085893902234677 - 1) / 117041 = 9277893236 from by norm_num]
      have h2 : (2 : ZMod 1085893902234677) ^ 9277893236 = ((649380459032718 : ℕ) : ZMod 1085893902234677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1085893902234677 - 1) / 1346183 = 806646572 from by norm_num]
      have h2 : (2 : ZMod 1085893902234677) ^ 806646572 = ((160355464897556 : ℕ) : ZMod 1085893902234677) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9290908227519896413 : Nat.Prime 9290908227519896413 := by
  refine lucas_primality 9290908227519896413 (2 : ZMod 9290908227519896413) ?_ (fun q hq hd => ?_)
  · rw [show 9290908227519896413 - 1 = 9290908227519896412 from by norm_num]
    reduce_mod_char
  · have e : 9290908227519896413 - 1 = [2 ^ 2, 3 ^ 1, 23 ^ 1, 31 ^ 1, 1085893902234677 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9290908227519896413 - 1) / 2 = 4645454113759948206 from by norm_num]
      have h2 : (2 : ZMod 9290908227519896413) ^ 4645454113759948206 = ((9290908227519896412 : ℕ) : ZMod 9290908227519896413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9290908227519896413 - 1) / 3 = 3096969409173298804 from by norm_num]
      have h2 : (2 : ZMod 9290908227519896413) ^ 3096969409173298804 = ((6547835750050292991 : ℕ) : ZMod 9290908227519896413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9290908227519896413 - 1) / 23 = 403952531631299844 from by norm_num]
      have h2 : (2 : ZMod 9290908227519896413) ^ 403952531631299844 = ((2352761306069212600 : ℕ) : ZMod 9290908227519896413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9290908227519896413 - 1) / 31 = 299706717016770852 from by norm_num]
      have h2 : (2 : ZMod 9290908227519896413) ^ 299706717016770852 = ((5994666602160846566 : ℕ) : ZMod 9290908227519896413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1085893902234677).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9290908227519896413 - 1) / 1085893902234677 = 8556 from by norm_num]
      have h2 : (2 : ZMod 9290908227519896413) ^ 8556 = ((2426363640732447560 : ℕ) : ZMod 9290908227519896413) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_52225651 : Nat.Prime 52225651 := by
  refine lucas_primality 52225651 (3 : ZMod 52225651) ?_ (fun q hq hd => ?_)
  · rw [show 52225651 - 1 = 52225650 from by norm_num]
    reduce_mod_char
  · have e : 52225651 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 2, 43 ^ 1, 2699 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52225651 - 1) / 2 = 26112825 from by norm_num]
      have h2 : (3 : ZMod 52225651) ^ 26112825 = ((52225650 : ℕ) : ZMod 52225651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52225651 - 1) / 3 = 17408550 from by norm_num]
      have h2 : (3 : ZMod 52225651) ^ 17408550 = ((50165677 : ℕ) : ZMod 52225651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52225651 - 1) / 5 = 10445130 from by norm_num]
      have h2 : (3 : ZMod 52225651) ^ 10445130 = ((6347479 : ℕ) : ZMod 52225651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52225651 - 1) / 43 = 1214550 from by norm_num]
      have h2 : (3 : ZMod 52225651) ^ 1214550 = ((25008859 : ℕ) : ZMod 52225651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (52225651 - 1) / 2699 = 19350 from by norm_num]
      have h2 : (3 : ZMod 52225651) ^ 19350 = ((18813384 : ℕ) : ZMod 52225651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_82842521093543 : Nat.Prime 82842521093543 := by
  refine lucas_primality 82842521093543 (5 : ZMod 82842521093543) ?_ (fun q hq hd => ?_)
  · rw [show 82842521093543 - 1 = 82842521093542 from by norm_num]
    reduce_mod_char
  · have e : 82842521093543 - 1 = [2 ^ 1, 7 ^ 1, 29 ^ 1, 3907 ^ 1, 52225651 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82842521093543 - 1) / 2 = 41421260546771 from by norm_num]
      have h2 : (5 : ZMod 82842521093543) ^ 41421260546771 = ((82842521093542 : ℕ) : ZMod 82842521093543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82842521093543 - 1) / 7 = 11834645870506 from by norm_num]
      have h2 : (5 : ZMod 82842521093543) ^ 11834645870506 = ((70841980877719 : ℕ) : ZMod 82842521093543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82842521093543 - 1) / 29 = 2856638658398 from by norm_num]
      have h2 : (5 : ZMod 82842521093543) ^ 2856638658398 = ((78323758528663 : ℕ) : ZMod 82842521093543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82842521093543 - 1) / 3907 = 21203614306 from by norm_num]
      have h2 : (5 : ZMod 82842521093543) ^ 21203614306 = ((1086779509910 : ℕ) : ZMod 82842521093543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_52225651).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (82842521093543 - 1) / 52225651 = 1586242 from by norm_num]
      have h2 : (5 : ZMod 82842521093543) ^ 1586242 = ((18913998264509 : ℕ) : ZMod 82842521093543) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3886084268132710540164562649868800513379104792251 : Nat.Prime 3886084268132710540164562649868800513379104792251 := by
  refine lucas_primality 3886084268132710540164562649868800513379104792251 (10 : ZMod 3886084268132710540164562649868800513379104792251) ?_ (fun q hq hd => ?_)
  · rw [show 3886084268132710540164562649868800513379104792251 - 1 = 3886084268132710540164562649868800513379104792250 from by norm_num]
    reduce_mod_char
  · have e : 3886084268132710540164562649868800513379104792251 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 3, 19 ^ 1, 179 ^ 1, 211 ^ 1, 3127009 ^ 1, 82842521093543 ^ 1, 9290908227519896413 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3886084268132710540164562649868800513379104792251 - 1) / 2 = 1943042134066355270082281324934400256689552396125 from by norm_num]
      have h2 : (10 : ZMod 3886084268132710540164562649868800513379104792251) ^ 1943042134066355270082281324934400256689552396125 = ((3886084268132710540164562649868800513379104792250 : ℕ) : ZMod 3886084268132710540164562649868800513379104792251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3886084268132710540164562649868800513379104792251 - 1) / 3 = 1295361422710903513388187549956266837793034930750 from by norm_num]
      have h2 : (10 : ZMod 3886084268132710540164562649868800513379104792251) ^ 1295361422710903513388187549956266837793034930750 = ((3886079904150926496308349704170060775015434771526 : ℕ) : ZMod 3886084268132710540164562649868800513379104792251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3886084268132710540164562649868800513379104792251 - 1) / 5 = 777216853626542108032912529973760102675820958450 from by norm_num]
      have h2 : (10 : ZMod 3886084268132710540164562649868800513379104792251) ^ 777216853626542108032912529973760102675820958450 = ((373303932218878952471080482618643060006221513700 : ℕ) : ZMod 3886084268132710540164562649868800513379104792251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3886084268132710540164562649868800513379104792251 - 1) / 19 = 204530750954353186324450665782568448072584462750 from by norm_num]
      have h2 : (10 : ZMod 3886084268132710540164562649868800513379104792251) ^ 204530750954353186324450665782568448072584462750 = ((2886010333950821193382983507478167887361400294542 : ℕ) : ZMod 3886084268132710540164562649868800513379104792251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3886084268132710540164562649868800513379104792251 - 1) / 179 = 21709967978395030950640014803736315717201702750 from by norm_num]
      have h2 : (10 : ZMod 3886084268132710540164562649868800513379104792251) ^ 21709967978395030950640014803736315717201702750 = ((3048806592469033004718782073486916022833515121644 : ℕ) : ZMod 3886084268132710540164562649868800513379104792251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3886084268132710540164562649868800513379104792251 - 1) / 211 = 18417460986410950427320202132079623286156894750 from by norm_num]
      have h2 : (10 : ZMod 3886084268132710540164562649868800513379104792251) ^ 18417460986410950427320202132079623286156894750 = ((1232434060410543584996696169245099473474082503701 : ℕ) : ZMod 3886084268132710540164562649868800513379104792251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3886084268132710540164562649868800513379104792251 - 1) / 3127009 = 1242748027950258710532832700471537022560250 from by norm_num]
      have h2 : (10 : ZMod 3886084268132710540164562649868800513379104792251) ^ 1242748027950258710532832700471537022560250 = ((1883093182095927586629597579662496299601006421725 : ℕ) : ZMod 3886084268132710540164562649868800513379104792251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_82842521093543).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3886084268132710540164562649868800513379104792251 - 1) / 82842521093543 = 46909295091884931282865842806445750 from by norm_num]
      have h2 : (10 : ZMod 3886084268132710540164562649868800513379104792251) ^ 46909295091884931282865842806445750 = ((2551185364450199421423860266380582307134129216773 : ℕ) : ZMod 3886084268132710540164562649868800513379104792251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9290908227519896413).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3886084268132710540164562649868800513379104792251 - 1) / 9290908227519896413 = 418267425849932981561721653250 from by norm_num]
      have h2 : (10 : ZMod 3886084268132710540164562649868800513379104792251) ^ 418267425849932981561721653250 = ((2358704117886616124177460933947042494669807682243 : ℕ) : ZMod 3886084268132710540164562649868800513379104792251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 : Nat.Prime 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 := by
  refine lucas_primality 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ?_ (fun q hq hd => ?_)
  · rw [show 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1 = 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683266 from by norm_num]
    reduce_mod_char
  · have e : 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1 = [2 ^ 1, 3 ^ 1, 359 ^ 1, 56207 ^ 1, 100957 ^ 1, 3755779 ^ 1, 19510643 ^ 1, 47029186391731 ^ 1, 291066066130451 ^ 1, 9248363581047133 ^ 1, 6779963644378513811 ^ 1, 161868664744491655705858963594331 ^ 1, 3886084268132710540164562649868800513379104792251 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 2 = 241791181470877677648872552875783844370281562430921584992816831537223682883589791446059434569287707480723569289115566397413263710852154071243261157911952401292714835841633 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 241791181470877677648872552875783844370281562430921584992816831537223682883589791446059434569287707480723569289115566397413263710852154071243261157911952401292714835841633 = ((483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683266 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 3 = 161194120980585118432581701917189229580187708287281056661877887691482455255726527630706289712858471653815712859410377598275509140568102714162174105274634934195143223894422 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 161194120980585118432581701917189229580187708287281056661877887691482455255726527630706289712858471653815712859410377598275509140568102714162174105274634934195143223894422 = ((38088674022933196169644863860307780875212400701197598362000782872478568671516519009800 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 359 = 1347026080617702939548036506271776291756443244740510222801207975137736394894650648724565095093524832761691193811228782158291162734552390369043237648534553767647436411374 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 1347026080617702939548036506271776291756443244740510222801207975137736394894650648724565095093524832761691193811228782158291162734552390369043237648534553767647436411374 = ((364353894205589532700660249706144892769867561938812751679801044909591894240469386823572975369 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 56207 = 8603596757374621582680895720311841741074299017237055348722288381775354773732445832229417494948590299454643346526787282630749326982480974655941827811907854939516958238 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 8603596757374621582680895720311841741074299017237055348722288381775354773732445832229417494948590299454643346526787282630749326982480974655941827811907854939516958238 = ((450647952452068092887166386444653545566270878267551575602025428915675244162939674113618355197907379925640492177345156140779153959294099630265575346341391472189280645203896 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 100957 = 4789983487442726658852235166967795088409551837533238606393154145571355782830111660331813238691476717428678928437167633693815460262332558836797075149062519712208461738 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 4789983487442726658852235166967795088409551837533238606393154145571355782830111660331813238691476717428678928437167633693815460262332558836797075149062519712208461738 = ((421058360158771169950641370437699075206468333604871084750122590376481282140224410400430940548857100085855872020079852395723416322427452351071069520574262162106545996897483 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 3755779 = 128756873858061231850368487004045682331298813072292903811867967490751550015903380601499414406059412697458273923527218399918239976767618153913348553209308855123112854 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 128756873858061231850368487004045682331298813072292903811867967490751550015903380601499414406059412697458273923527218399918239976767618153913348553209308855123112854 = ((55948271025188423615027875424559486828322826290014379007426315802380765154459270437841485819111900722062851199831699653700603533173981504426005422325154660894499009125171 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 19510643 = 24785567699729596574430945497366113907192250140697216897753378147221870943319478650299678444148427858653717285392958745379459171166440190745457354523062351281063862 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 24785567699729596574430945497366113907192250140697216897753378147221870943319478650299678444148427858653717285392958745379459171166440190745457354523062351281063862 = ((120383587788091942320144158085529233220683929710365319871794703909257778454823691749988516756105268248044256641692941107705255386471333412189476781850633435514902851890956 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_47029186391731).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 47029186391731 = 10282601083372817686171048351338608051228844453015127745599608212716402129340930127161183897497134770969606780171277027664310543196224462521769298488574642486 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 10282601083372817686171048351338608051228844453015127745599608212716402129340930127161183897497134770969606780171277027664310543196224462521769298488574642486 = ((125305592737945941630497525379721062964745426805160656840388291566330599002326694059423818862670077067744404314734132206520775951737946795708040509647977773597192666313485 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_291066066130451).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 291066066130451 = 1661417867670708591094344537348848317820973719945008385983020686838074535794447167273691883136095415239715218347696508345810295218285629081082724760390248566 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 1661417867670708591094344537348848317820973719945008385983020686838074535794447167273691883136095415239715218347696508345810295218285629081082724760390248566 = ((204258763153453723847203723399450455631421454550071549119381137607121167832878426084723152195707992291745875664183796981594204643153084977772284781384079563328794283692501 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_9248363581047133).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 9248363581047133 = 52288424725512620931112323166052393503189370058877808018418191051556503590313008284443293678843609597973719922576412975660643347378201981567894148497433002 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 52288424725512620931112323166052393503189370058877808018418191051556503590313008284443293678843609597973719922576412975660643347378201981567894148497433002 = ((227932168420432080781011221504059808628517035737734449920166395490769946257392946588025273618144325973843810636332027118847876951427906300310385444442084165417954428649388 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6779963644378513811).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 6779963644378513811 = 71325214751366560047856789311404908329340178279870283031491213945888379068055224626283653521434684923222772048297703076125976903219724921101781363116406 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 71325214751366560047856789311404908329340178279870283031491213945888379068055224626283653521434684923222772048297703076125976903219724921101781363116406 = ((132718286379709081561376077331729172072306657693077560883568241578511439215043506550214666923065014581965883124519884722984547142566442153877310756442525483435930202839827 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_161868664744491655705858963594331).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 161868664744491655705858963594331 = 2987498313556154324099829317307027266314621996541792747995148505213623694716209378461542579757684974953276538861785898435402590446439526886 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 2987498313556154324099829317307027266314621996541792747995148505213623694716209378461542579757684974953276538861785898435402590446439526886 = ((221237056199181829983506681135464193518822515157559012404305205814594631709185708158116222174488598960641211948047695568557446821699376492192002803698178505325891820313369 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3886084268132710540164562649868800513379104792251).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 - 1) / 3886084268132710540164562649868800513379104792251 = 124439494765284622162917779858015403849496558248349795914063521633509542148519677315678081890037256519123116009511110569766 from by norm_num]
      have h2 : (2 : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) ^ 124439494765284622162917779858015403849496558248349795914063521633509542148519677315678081890037256519123116009511110569766 = ((142200445162706304414282846587076181213670445125713226254689940405365651440991290045720246520290806431515053111935949260556535379182855687525416484726083556053928489571974 : ℕ) : ZMod 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_105576905351265533 : Nat.Prime 105576905351265533 := by
  refine lucas_primality 105576905351265533 (2 : ZMod 105576905351265533) ?_ (fun q hq hd => ?_)
  · rw [show 105576905351265533 - 1 = 105576905351265532 from by norm_num]
    reduce_mod_char
  · have e : 105576905351265533 - 1 = [2 ^ 2, 31 ^ 1, 25411973 ^ 1, 33504941 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105576905351265533 - 1) / 2 = 52788452675632766 from by norm_num]
      have h2 : (2 : ZMod 105576905351265533) ^ 52788452675632766 = ((105576905351265532 : ℕ) : ZMod 105576905351265533) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105576905351265533 - 1) / 31 = 3405706624234372 from by norm_num]
      have h2 : (2 : ZMod 105576905351265533) ^ 3405706624234372 = ((2001773786899774 : ℕ) : ZMod 105576905351265533) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105576905351265533 - 1) / 25411973 = 4154612684 from by norm_num]
      have h2 : (2 : ZMod 105576905351265533) ^ 4154612684 = ((311516998303859 : ℕ) : ZMod 105576905351265533) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (105576905351265533 - 1) / 33504941 = 3151084652 from by norm_num]
      have h2 : (2 : ZMod 105576905351265533) ^ 3151084652 = ((78394612755696572 : ℕ) : ZMod 105576905351265533) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_405527021 : Nat.Prime 405527021 := by
  refine lucas_primality 405527021 (10 : ZMod 405527021) ?_ (fun q hq hd => ?_)
  · rw [show 405527021 - 1 = 405527020 from by norm_num]
    reduce_mod_char
  · have e : 405527021 - 1 = [2 ^ 2, 5 ^ 1, 20276351 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (405527021 - 1) / 2 = 202763510 from by norm_num]
      have h2 : (10 : ZMod 405527021) ^ 202763510 = ((405527020 : ℕ) : ZMod 405527021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (405527021 - 1) / 5 = 81105404 from by norm_num]
      have h2 : (10 : ZMod 405527021) ^ 81105404 = ((400071718 : ℕ) : ZMod 405527021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (405527021 - 1) / 20276351 = 20 from by norm_num]
      have h2 : (10 : ZMod 405527021) ^ 20 = ((373308996 : ℕ) : ZMod 405527021) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1715966481680056951 : Nat.Prime 1715966481680056951 := by
  refine lucas_primality 1715966481680056951 (12 : ZMod 1715966481680056951) ?_ (fun q hq hd => ?_)
  · rw [show 1715966481680056951 - 1 = 1715966481680056950 from by norm_num]
    reduce_mod_char
  · have e : 1715966481680056951 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 2, 28209653 ^ 1, 405527021 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1715966481680056951 - 1) / 2 = 857983240840028475 from by norm_num]
      have h2 : (12 : ZMod 1715966481680056951) ^ 857983240840028475 = ((1715966481680056950 : ℕ) : ZMod 1715966481680056951) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1715966481680056951 - 1) / 3 = 571988827226685650 from by norm_num]
      have h2 : (12 : ZMod 1715966481680056951) ^ 571988827226685650 = ((365624939599360380 : ℕ) : ZMod 1715966481680056951) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1715966481680056951 - 1) / 5 = 343193296336011390 from by norm_num]
      have h2 : (12 : ZMod 1715966481680056951) ^ 343193296336011390 = ((812299157312128358 : ℕ) : ZMod 1715966481680056951) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1715966481680056951 - 1) / 28209653 = 60829053150 from by norm_num]
      have h2 : (12 : ZMod 1715966481680056951) ^ 60829053150 = ((1194427585090247684 : ℕ) : ZMod 1715966481680056951) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_405527021).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1715966481680056951 - 1) / 405527021 = 4231447950 from by norm_num]
      have h2 : (12 : ZMod 1715966481680056951) ^ 4231447950 = ((689218615486287752 : ℕ) : ZMod 1715966481680056951) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_7198260873233 : Nat.Prime 7198260873233 := by
  refine lucas_primality 7198260873233 (5 : ZMod 7198260873233) ?_ (fun q hq hd => ?_)
  · rw [show 7198260873233 - 1 = 7198260873232 from by norm_num]
    reduce_mod_char
  · have e : 7198260873233 - 1 = [2 ^ 4, 11 ^ 1, 13 ^ 1, 1039 ^ 1, 3028001 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7198260873233 - 1) / 2 = 3599130436616 from by norm_num]
      have h2 : (5 : ZMod 7198260873233) ^ 3599130436616 = ((7198260873232 : ℕ) : ZMod 7198260873233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7198260873233 - 1) / 11 = 654387352112 from by norm_num]
      have h2 : (5 : ZMod 7198260873233) ^ 654387352112 = ((3040811684581 : ℕ) : ZMod 7198260873233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7198260873233 - 1) / 13 = 553712374864 from by norm_num]
      have h2 : (5 : ZMod 7198260873233) ^ 553712374864 = ((6476068944899 : ℕ) : ZMod 7198260873233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7198260873233 - 1) / 1039 = 6928066288 from by norm_num]
      have h2 : (5 : ZMod 7198260873233) ^ 6928066288 = ((2043322058660 : ℕ) : ZMod 7198260873233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (7198260873233 - 1) / 3028001 = 2377232 from by norm_num]
      have h2 : (5 : ZMod 7198260873233) ^ 2377232 = ((6434358458432 : ℕ) : ZMod 7198260873233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_79493867560743552507580109246045037367489 : Nat.Prime 79493867560743552507580109246045037367489 := by
  refine lucas_primality 79493867560743552507580109246045037367489 (19 : ZMod 79493867560743552507580109246045037367489) ?_ (fun q hq hd => ?_)
  · rw [show 79493867560743552507580109246045037367489 - 1 = 79493867560743552507580109246045037367488 from by norm_num]
    reduce_mod_char
  · have e : 79493867560743552507580109246045037367489 - 1 = [2 ^ 6, 3 ^ 1, 751 ^ 1, 44633 ^ 1, 7198260873233 ^ 1, 1715966481680056951 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79493867560743552507580109246045037367489 - 1) / 2 = 39746933780371776253790054623022518683744 from by norm_num]
      have h2 : (19 : ZMod 79493867560743552507580109246045037367489) ^ 39746933780371776253790054623022518683744 = ((79493867560743552507580109246045037367488 : ℕ) : ZMod 79493867560743552507580109246045037367489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79493867560743552507580109246045037367489 - 1) / 3 = 26497955853581184169193369748681679122496 from by norm_num]
      have h2 : (19 : ZMod 79493867560743552507580109246045037367489) ^ 26497955853581184169193369748681679122496 = ((25105025871413356853285766167340480506973 : ℕ) : ZMod 79493867560743552507580109246045037367489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79493867560743552507580109246045037367489 - 1) / 751 = 105850689162108591887590025627223751488 from by norm_num]
      have h2 : (19 : ZMod 79493867560743552507580109246045037367489) ^ 105850689162108591887590025627223751488 = ((53978583202620959586375870414507815878101 : ℕ) : ZMod 79493867560743552507580109246045037367489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79493867560743552507580109246045037367489 - 1) / 44633 = 1781055890501278258409251209778527936 from by norm_num]
      have h2 : (19 : ZMod 79493867560743552507580109246045037367489) ^ 1781055890501278258409251209778527936 = ((49408084268249320350393758100214417354224 : ℕ) : ZMod 79493867560743552507580109246045037367489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_7198260873233).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79493867560743552507580109246045037367489 - 1) / 7198260873233 = 11043482441202491981257196736 from by norm_num]
      have h2 : (19 : ZMod 79493867560743552507580109246045037367489) ^ 11043482441202491981257196736 = ((60251570855922257463963500526509404213181 : ℕ) : ZMod 79493867560743552507580109246045037367489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1715966481680056951).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79493867560743552507580109246045037367489 - 1) / 1715966481680056951 = 46326002523611784045888 from by norm_num]
      have h2 : (19 : ZMod 79493867560743552507580109246045037367489) ^ 46326002523611784045888 = ((79339196118743229784606788801155374891757 : ℕ) : ZMod 79493867560743552507580109246045037367489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_953926410728922630090961310952540448409869 : Nat.Prime 953926410728922630090961310952540448409869 := by
  refine lucas_primality 953926410728922630090961310952540448409869 (11 : ZMod 953926410728922630090961310952540448409869) ?_ (fun q hq hd => ?_)
  · rw [show 953926410728922630090961310952540448409869 - 1 = 953926410728922630090961310952540448409868 from by norm_num]
    reduce_mod_char
  · have e : 953926410728922630090961310952540448409869 - 1 = [2 ^ 2, 3 ^ 1, 79493867560743552507580109246045037367489 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (953926410728922630090961310952540448409869 - 1) / 2 = 476963205364461315045480655476270224204934 from by norm_num]
      have h2 : (11 : ZMod 953926410728922630090961310952540448409869) ^ 476963205364461315045480655476270224204934 = ((953926410728922630090961310952540448409868 : ℕ) : ZMod 953926410728922630090961310952540448409869) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (953926410728922630090961310952540448409869 - 1) / 3 = 317975470242974210030320436984180149469956 from by norm_num]
      have h2 : (11 : ZMod 953926410728922630090961310952540448409869) ^ 317975470242974210030320436984180149469956 = ((721930004323703542027567204996848385518612 : ℕ) : ZMod 953926410728922630090961310952540448409869) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_79493867560743552507580109246045037367489).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (953926410728922630090961310952540448409869 - 1) / 79493867560743552507580109246045037367489 = 12 from by norm_num]
      have h2 : (11 : ZMod 953926410728922630090961310952540448409869) ^ 12 = ((3138428376721 : ℕ) : ZMod 953926410728922630090961310952540448409869) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1725910733925646133 : Nat.Prime 1725910733925646133 := by
  refine lucas_primality 1725910733925646133 (2 : ZMod 1725910733925646133) ?_ (fun q hq hd => ?_)
  · rw [show 1725910733925646133 - 1 = 1725910733925646132 from by norm_num]
    reduce_mod_char
  · have e : 1725910733925646133 - 1 = [2 ^ 2, 41 ^ 1, 79 ^ 1, 349 ^ 1, 34351 ^ 1, 11111753 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1725910733925646133 - 1) / 2 = 862955366962823066 from by norm_num]
      have h2 : (2 : ZMod 1725910733925646133) ^ 862955366962823066 = ((1725910733925646132 : ℕ) : ZMod 1725910733925646133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1725910733925646133 - 1) / 41 = 42095383754284052 from by norm_num]
      have h2 : (2 : ZMod 1725910733925646133) ^ 42095383754284052 = ((968009238804229614 : ℕ) : ZMod 1725910733925646133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1725910733925646133 - 1) / 79 = 21846971315514508 from by norm_num]
      have h2 : (2 : ZMod 1725910733925646133) ^ 21846971315514508 = ((764480087329041365 : ℕ) : ZMod 1725910733925646133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1725910733925646133 - 1) / 349 = 4945302962537668 from by norm_num]
      have h2 : (2 : ZMod 1725910733925646133) ^ 4945302962537668 = ((794358028984059107 : ℕ) : ZMod 1725910733925646133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1725910733925646133 - 1) / 34351 = 50243391281932 from by norm_num]
      have h2 : (2 : ZMod 1725910733925646133) ^ 50243391281932 = ((1072460090721666861 : ℕ) : ZMod 1725910733925646133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1725910733925646133 - 1) / 11111753 = 155322993044 from by norm_num]
      have h2 : (2 : ZMod 1725910733925646133) ^ 155322993044 = ((1231629107288404955 : ℕ) : ZMod 1725910733925646133) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_241627502749590458621 : Nat.Prime 241627502749590458621 := by
  refine lucas_primality 241627502749590458621 (2 : ZMod 241627502749590458621) ?_ (fun q hq hd => ?_)
  · rw [show 241627502749590458621 - 1 = 241627502749590458620 from by norm_num]
    reduce_mod_char
  · have e : 241627502749590458621 - 1 = [2 ^ 2, 5 ^ 1, 7 ^ 1, 1725910733925646133 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (241627502749590458621 - 1) / 2 = 120813751374795229310 from by norm_num]
      have h2 : (2 : ZMod 241627502749590458621) ^ 120813751374795229310 = ((241627502749590458620 : ℕ) : ZMod 241627502749590458621) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (241627502749590458621 - 1) / 5 = 48325500549918091724 from by norm_num]
      have h2 : (2 : ZMod 241627502749590458621) ^ 48325500549918091724 = ((225329004211082040984 : ℕ) : ZMod 241627502749590458621) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (241627502749590458621 - 1) / 7 = 34518214678512922660 from by norm_num]
      have h2 : (2 : ZMod 241627502749590458621) ^ 34518214678512922660 = ((184339973391643384313 : ℕ) : ZMod 241627502749590458621) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1725910733925646133).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (241627502749590458621 - 1) / 1725910733925646133 = 140 from by norm_num]
      have h2 : (2 : ZMod 241627502749590458621) ^ 140 = ((35775624867179166308 : ℕ) : ZMod 241627502749590458621) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_236311697689099468531339 : Nat.Prime 236311697689099468531339 := by
  refine lucas_primality 236311697689099468531339 (10 : ZMod 236311697689099468531339) ?_ (fun q hq hd => ?_)
  · rw [show 236311697689099468531339 - 1 = 236311697689099468531338 from by norm_num]
    reduce_mod_char
  · have e : 236311697689099468531339 - 1 = [2 ^ 1, 3 ^ 1, 163 ^ 1, 241627502749590458621 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236311697689099468531339 - 1) / 2 = 118155848844549734265669 from by norm_num]
      have h2 : (10 : ZMod 236311697689099468531339) ^ 118155848844549734265669 = ((236311697689099468531338 : ℕ) : ZMod 236311697689099468531339) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236311697689099468531339 - 1) / 3 = 78770565896366489510446 from by norm_num]
      have h2 : (10 : ZMod 236311697689099468531339) ^ 78770565896366489510446 = ((103627741600623370229881 : ℕ) : ZMod 236311697689099468531339) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236311697689099468531339 - 1) / 163 = 1449765016497542751726 from by norm_num]
      have h2 : (10 : ZMod 236311697689099468531339) ^ 1449765016497542751726 = ((20301636142489613523704 : ℕ) : ZMod 236311697689099468531339) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_241627502749590458621).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (236311697689099468531339 - 1) / 241627502749590458621 = 978 from by norm_num]
      have h2 : (10 : ZMod 236311697689099468531339) ^ 978 = ((61912289303930344058885 : ℕ) : ZMod 236311697689099468531339) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_170826287969 : Nat.Prime 170826287969 := by
  refine lucas_primality 170826287969 (3 : ZMod 170826287969) ?_ (fun q hq hd => ?_)
  · rw [show 170826287969 - 1 = 170826287968 from by norm_num]
    reduce_mod_char
  · have e : 170826287969 - 1 = [2 ^ 5, 7 ^ 1, 167 ^ 1, 379 ^ 1, 12049 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (170826287969 - 1) / 2 = 85413143984 from by norm_num]
      have h2 : (3 : ZMod 170826287969) ^ 85413143984 = ((170826287968 : ℕ) : ZMod 170826287969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (170826287969 - 1) / 7 = 24403755424 from by norm_num]
      have h2 : (3 : ZMod 170826287969) ^ 24403755424 = ((26140076326 : ℕ) : ZMod 170826287969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (170826287969 - 1) / 167 = 1022911904 from by norm_num]
      have h2 : (3 : ZMod 170826287969) ^ 1022911904 = ((86999723911 : ℕ) : ZMod 170826287969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (170826287969 - 1) / 379 = 450728992 from by norm_num]
      have h2 : (3 : ZMod 170826287969) ^ 450728992 = ((5761796708 : ℕ) : ZMod 170826287969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (170826287969 - 1) / 12049 = 14177632 from by norm_num]
      have h2 : (3 : ZMod 170826287969) ^ 14177632 = ((27882090778 : ℕ) : ZMod 170826287969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_28822863493563604394694586138432456377263959 : Nat.Prime 28822863493563604394694586138432456377263959 := by
  refine lucas_primality 28822863493563604394694586138432456377263959 (3 : ZMod 28822863493563604394694586138432456377263959) ?_ (fun q hq hd => ?_)
  · rw [show 28822863493563604394694586138432456377263959 - 1 = 28822863493563604394694586138432456377263958 from by norm_num]
    reduce_mod_char
  · have e : 28822863493563604394694586138432456377263959 - 1 = [2 ^ 1, 3 ^ 1, 23 ^ 1, 47 ^ 1, 110083 ^ 1, 170826287969 ^ 1, 236311697689099468531339 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28822863493563604394694586138432456377263959 - 1) / 2 = 14411431746781802197347293069216228188631979 from by norm_num]
      have h2 : (3 : ZMod 28822863493563604394694586138432456377263959) ^ 14411431746781802197347293069216228188631979 = ((28822863493563604394694586138432456377263958 : ℕ) : ZMod 28822863493563604394694586138432456377263959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28822863493563604394694586138432456377263959 - 1) / 3 = 9607621164521201464898195379477485459087986 from by norm_num]
      have h2 : (3 : ZMod 28822863493563604394694586138432456377263959) ^ 9607621164521201464898195379477485459087986 = ((18141713363891555923306023190222292016425728 : ℕ) : ZMod 28822863493563604394694586138432456377263959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28822863493563604394694586138432456377263959 - 1) / 23 = 1253167977981026278030199397323150277272346 from by norm_num]
      have h2 : (3 : ZMod 28822863493563604394694586138432456377263959) ^ 1253167977981026278030199397323150277272346 = ((11065718683415339036527819422815053687063529 : ℕ) : ZMod 28822863493563604394694586138432456377263959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28822863493563604394694586138432456377263959 - 1) / 47 = 613252414756672433929672045498562901643914 from by norm_num]
      have h2 : (3 : ZMod 28822863493563604394694586138432456377263959) ^ 613252414756672433929672045498562901643914 = ((11747918295612596616043059947168866422911223 : ℕ) : ZMod 28822863493563604394694586138432456377263959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28822863493563604394694586138432456377263959 - 1) / 110083 = 261828470277550615396515230675330944626 from by norm_num]
      have h2 : (3 : ZMod 28822863493563604394694586138432456377263959) ^ 261828470277550615396515230675330944626 = ((14621259852433525218078227885365530817988205 : ℕ) : ZMod 28822863493563604394694586138432456377263959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_170826287969).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28822863493563604394694586138432456377263959 - 1) / 170826287969 = 168726159399975461248059346914582 from by norm_num]
      have h2 : (3 : ZMod 28822863493563604394694586138432456377263959) ^ 168726159399975461248059346914582 = ((4683544634561074507028874119727143020204842 : ℕ) : ZMod 28822863493563604394694586138432456377263959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_236311697689099468531339).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28822863493563604394694586138432456377263959 - 1) / 236311697689099468531339 = 121969685696575395522 from by norm_num]
      have h2 : (3 : ZMod 28822863493563604394694586138432456377263959) ^ 121969685696575395522 = ((20352593548799684472381858825634130484015025 : ℕ) : ZMod 28822863493563604394694586138432456377263959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_32742290153 : Nat.Prime 32742290153 := by
  refine lucas_primality 32742290153 (3 : ZMod 32742290153) ?_ (fun q hq hd => ?_)
  · rw [show 32742290153 - 1 = 32742290152 from by norm_num]
    reduce_mod_char
  · have e : 32742290153 - 1 = [2 ^ 3, 11 ^ 1, 13 ^ 1, 29 ^ 1, 986927 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32742290153 - 1) / 2 = 16371145076 from by norm_num]
      have h2 : (3 : ZMod 32742290153) ^ 16371145076 = ((32742290152 : ℕ) : ZMod 32742290153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32742290153 - 1) / 11 = 2976571832 from by norm_num]
      have h2 : (3 : ZMod 32742290153) ^ 2976571832 = ((19603860219 : ℕ) : ZMod 32742290153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32742290153 - 1) / 13 = 2518637704 from by norm_num]
      have h2 : (3 : ZMod 32742290153) ^ 2518637704 = ((21256558312 : ℕ) : ZMod 32742290153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32742290153 - 1) / 29 = 1129044488 from by norm_num]
      have h2 : (3 : ZMod 32742290153) ^ 1129044488 = ((6415719723 : ℕ) : ZMod 32742290153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32742290153 - 1) / 986927 = 33176 from by norm_num]
      have h2 : (3 : ZMod 32742290153) ^ 33176 = ((30253296399 : ℕ) : ZMod 32742290153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3994559398667 : Nat.Prime 3994559398667 := by
  refine lucas_primality 3994559398667 (2 : ZMod 3994559398667) ?_ (fun q hq hd => ?_)
  · rw [show 3994559398667 - 1 = 3994559398666 from by norm_num]
    reduce_mod_char
  · have e : 3994559398667 - 1 = [2 ^ 1, 61 ^ 1, 32742290153 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3994559398667 - 1) / 2 = 1997279699333 from by norm_num]
      have h2 : (2 : ZMod 3994559398667) ^ 1997279699333 = ((3994559398666 : ℕ) : ZMod 3994559398667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3994559398667 - 1) / 61 = 65484580306 from by norm_num]
      have h2 : (2 : ZMod 3994559398667) ^ 65484580306 = ((2292930845234 : ℕ) : ZMod 3994559398667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_32742290153).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3994559398667 - 1) / 32742290153 = 122 from by norm_num]
      have h2 : (2 : ZMod 3994559398667) ^ 122 = ((3749841374171 : ℕ) : ZMod 3994559398667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_60467872480679 : Nat.Prime 60467872480679 := by
  refine lucas_primality 60467872480679 (19 : ZMod 60467872480679) ?_ (fun q hq hd => ?_)
  · rw [show 60467872480679 - 1 = 60467872480678 from by norm_num]
    reduce_mod_char
  · have e : 60467872480679 - 1 = [2 ^ 1, 13 ^ 1, 17 ^ 1, 61169 ^ 1, 2236511 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60467872480679 - 1) / 2 = 30233936240339 from by norm_num]
      have h2 : (19 : ZMod 60467872480679) ^ 30233936240339 = ((60467872480678 : ℕ) : ZMod 60467872480679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60467872480679 - 1) / 13 = 4651374806206 from by norm_num]
      have h2 : (19 : ZMod 60467872480679) ^ 4651374806206 = ((58413896938886 : ℕ) : ZMod 60467872480679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60467872480679 - 1) / 17 = 3556933675334 from by norm_num]
      have h2 : (19 : ZMod 60467872480679) ^ 3556933675334 = ((14305592071097 : ℕ) : ZMod 60467872480679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60467872480679 - 1) / 61169 = 988537862 from by norm_num]
      have h2 : (19 : ZMod 60467872480679) ^ 988537862 = ((57521555105809 : ℕ) : ZMod 60467872480679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (60467872480679 - 1) / 2236511 = 27036698 from by norm_num]
      have h2 : (19 : ZMod 60467872480679) ^ 27036698 = ((40927546802879 : ℕ) : ZMod 60467872480679) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_745257789612521 : Nat.Prime 745257789612521 := by
  refine lucas_primality 745257789612521 (6 : ZMod 745257789612521) ?_ (fun q hq hd => ?_)
  · rw [show 745257789612521 - 1 = 745257789612520 from by norm_num]
    reduce_mod_char
  · have e : 745257789612521 - 1 = [2 ^ 3, 5 ^ 1, 37 ^ 1, 47 ^ 1, 61 ^ 1, 8293 ^ 1, 21179 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (745257789612521 - 1) / 2 = 372628894806260 from by norm_num]
      have h2 : (6 : ZMod 745257789612521) ^ 372628894806260 = ((745257789612520 : ℕ) : ZMod 745257789612521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (745257789612521 - 1) / 5 = 149051557922504 from by norm_num]
      have h2 : (6 : ZMod 745257789612521) ^ 149051557922504 = ((294172284560472 : ℕ) : ZMod 745257789612521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (745257789612521 - 1) / 37 = 20142102421960 from by norm_num]
      have h2 : (6 : ZMod 745257789612521) ^ 20142102421960 = ((319648106721589 : ℕ) : ZMod 745257789612521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (745257789612521 - 1) / 47 = 15856548715160 from by norm_num]
      have h2 : (6 : ZMod 745257789612521) ^ 15856548715160 = ((677887252886879 : ℕ) : ZMod 745257789612521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (745257789612521 - 1) / 61 = 12217340813320 from by norm_num]
      have h2 : (6 : ZMod 745257789612521) ^ 12217340813320 = ((718883491282472 : ℕ) : ZMod 745257789612521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (745257789612521 - 1) / 8293 = 89865885640 from by norm_num]
      have h2 : (6 : ZMod 745257789612521) ^ 89865885640 = ((676028939443048 : ℕ) : ZMod 745257789612521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (745257789612521 - 1) / 21179 = 35188525880 from by norm_num]
      have h2 : (6 : ZMod 745257789612521) ^ 35188525880 = ((514916991029709 : ℕ) : ZMod 745257789612521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5962062316900169 : Nat.Prime 5962062316900169 := by
  refine lucas_primality 5962062316900169 (3 : ZMod 5962062316900169) ?_ (fun q hq hd => ?_)
  · rw [show 5962062316900169 - 1 = 5962062316900168 from by norm_num]
    reduce_mod_char
  · have e : 5962062316900169 - 1 = [2 ^ 3, 745257789612521 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5962062316900169 - 1) / 2 = 2981031158450084 from by norm_num]
      have h2 : (3 : ZMod 5962062316900169) ^ 2981031158450084 = ((5962062316900168 : ℕ) : ZMod 5962062316900169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_745257789612521).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5962062316900169 - 1) / 745257789612521 = 8 from by norm_num]
      have h2 : (3 : ZMod 5962062316900169) ^ 8 = ((6561 : ℕ) : ZMod 5962062316900169) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_178861869507005071 : Nat.Prime 178861869507005071 := by
  refine lucas_primality 178861869507005071 (19 : ZMod 178861869507005071) ?_ (fun q hq hd => ?_)
  · rw [show 178861869507005071 - 1 = 178861869507005070 from by norm_num]
    reduce_mod_char
  · have e : 178861869507005071 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 5962062316900169 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (178861869507005071 - 1) / 2 = 89430934753502535 from by norm_num]
      have h2 : (19 : ZMod 178861869507005071) ^ 89430934753502535 = ((178861869507005070 : ℕ) : ZMod 178861869507005071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (178861869507005071 - 1) / 3 = 59620623169001690 from by norm_num]
      have h2 : (19 : ZMod 178861869507005071) ^ 59620623169001690 = ((37612266666674566 : ℕ) : ZMod 178861869507005071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (178861869507005071 - 1) / 5 = 35772373901401014 from by norm_num]
      have h2 : (19 : ZMod 178861869507005071) ^ 35772373901401014 = ((21806634343013812 : ℕ) : ZMod 178861869507005071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5962062316900169).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (178861869507005071 - 1) / 5962062316900169 = 30 from by norm_num]
      have h2 : (19 : ZMod 178861869507005071) ^ 30 = ((115726957898841889 : ℕ) : ZMod 178861869507005071) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2170967411887213806804742451 : Nat.Prime 2170967411887213806804742451 := by
  refine lucas_primality 2170967411887213806804742451 (2 : ZMod 2170967411887213806804742451) ?_ (fun q hq hd => ?_)
  · rw [show 2170967411887213806804742451 - 1 = 2170967411887213806804742450 from by norm_num]
    reduce_mod_char
  · have e : 2170967411887213806804742451 - 1 = [2 ^ 1, 5 ^ 2, 19 ^ 1, 29 ^ 1, 440569 ^ 1, 178861869507005071 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2170967411887213806804742451 - 1) / 2 = 1085483705943606903402371225 from by norm_num]
      have h2 : (2 : ZMod 2170967411887213806804742451) ^ 1085483705943606903402371225 = ((2170967411887213806804742450 : ℕ) : ZMod 2170967411887213806804742451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2170967411887213806804742451 - 1) / 5 = 434193482377442761360948490 from by norm_num]
      have h2 : (2 : ZMod 2170967411887213806804742451) ^ 434193482377442761360948490 = ((415910198060309250441497051 : ℕ) : ZMod 2170967411887213806804742451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2170967411887213806804742451 - 1) / 19 = 114261442730905989831828550 from by norm_num]
      have h2 : (2 : ZMod 2170967411887213806804742451) ^ 114261442730905989831828550 = ((2099459056489131211318631580 : ℕ) : ZMod 2170967411887213806804742451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2170967411887213806804742451 - 1) / 29 = 74860945237490131269129050 from by norm_num]
      have h2 : (2 : ZMod 2170967411887213806804742451) ^ 74860945237490131269129050 = ((895642103201265545429623483 : ℕ) : ZMod 2170967411887213806804742451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2170967411887213806804742451 - 1) / 440569 = 4927644504917989706050 from by norm_num]
      have h2 : (2 : ZMod 2170967411887213806804742451) ^ 4927644504917989706050 = ((958103532823573622406587056 : ℕ) : ZMod 2170967411887213806804742451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_178861869507005071).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2170967411887213806804742451 - 1) / 178861869507005071 = 12137675950 from by norm_num]
      have h2 : (2 : ZMod 2170967411887213806804742451) ^ 12137675950 = ((638910915460493918039180014 : ℕ) : ZMod 2170967411887213806804742451) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2916963374916948341 : Nat.Prime 2916963374916948341 := by
  refine lucas_primality 2916963374916948341 (2 : ZMod 2916963374916948341) ?_ (fun q hq hd => ?_)
  · rw [show 2916963374916948341 - 1 = 2916963374916948340 from by norm_num]
    reduce_mod_char
  · have e : 2916963374916948341 - 1 = [2 ^ 2, 5 ^ 1, 73 ^ 1, 113 ^ 1, 744409 ^ 1, 23751337 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2916963374916948341 - 1) / 2 = 1458481687458474170 from by norm_num]
      have h2 : (2 : ZMod 2916963374916948341) ^ 1458481687458474170 = ((2916963374916948340 : ℕ) : ZMod 2916963374916948341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2916963374916948341 - 1) / 5 = 583392674983389668 from by norm_num]
      have h2 : (2 : ZMod 2916963374916948341) ^ 583392674983389668 = ((1796041729321645462 : ℕ) : ZMod 2916963374916948341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2916963374916948341 - 1) / 73 = 39958402396122580 from by norm_num]
      have h2 : (2 : ZMod 2916963374916948341) ^ 39958402396122580 = ((1145340661142739483 : ℕ) : ZMod 2916963374916948341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2916963374916948341 - 1) / 113 = 25813835176256180 from by norm_num]
      have h2 : (2 : ZMod 2916963374916948341) ^ 25813835176256180 = ((2739269799811422329 : ℕ) : ZMod 2916963374916948341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2916963374916948341 - 1) / 744409 = 3918495578260 from by norm_num]
      have h2 : (2 : ZMod 2916963374916948341) ^ 3918495578260 = ((908300307770787148 : ℕ) : ZMod 2916963374916948341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2916963374916948341 - 1) / 23751337 = 122812596820 from by norm_num]
      have h2 : (2 : ZMod 2916963374916948341) ^ 122812596820 = ((368580733166855928 : ℕ) : ZMod 2916963374916948341) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_425334757 : Nat.Prime 425334757 := by
  refine lucas_primality 425334757 (5 : ZMod 425334757) ?_ (fun q hq hd => ?_)
  · rw [show 425334757 - 1 = 425334756 from by norm_num]
    reduce_mod_char
  · have e : 425334757 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 11 ^ 1, 31 ^ 2, 479 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (425334757 - 1) / 2 = 212667378 from by norm_num]
      have h2 : (5 : ZMod 425334757) ^ 212667378 = ((425334756 : ℕ) : ZMod 425334757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (425334757 - 1) / 3 = 141778252 from by norm_num]
      have h2 : (5 : ZMod 425334757) ^ 141778252 = ((105062686 : ℕ) : ZMod 425334757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (425334757 - 1) / 7 = 60762108 from by norm_num]
      have h2 : (5 : ZMod 425334757) ^ 60762108 = ((39068582 : ℕ) : ZMod 425334757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (425334757 - 1) / 11 = 38666796 from by norm_num]
      have h2 : (5 : ZMod 425334757) ^ 38666796 = ((97185892 : ℕ) : ZMod 425334757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (425334757 - 1) / 31 = 13720476 from by norm_num]
      have h2 : (5 : ZMod 425334757) ^ 13720476 = ((293252593 : ℕ) : ZMod 425334757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (425334757 - 1) / 479 = 887964 from by norm_num]
      have h2 : (5 : ZMod 425334757) ^ 887964 = ((349936756 : ℕ) : ZMod 425334757) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1143006901 : Nat.Prime 1143006901 := by
  refine lucas_primality 1143006901 (2 : ZMod 1143006901) ?_ (fun q hq hd => ?_)
  · rw [show 1143006901 - 1 = 1143006900 from by norm_num]
    reduce_mod_char
  · have e : 1143006901 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 2, 7 ^ 1, 17 ^ 1, 101 ^ 1, 317 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1143006901 - 1) / 2 = 571503450 from by norm_num]
      have h2 : (2 : ZMod 1143006901) ^ 571503450 = ((1143006900 : ℕ) : ZMod 1143006901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1143006901 - 1) / 3 = 381002300 from by norm_num]
      have h2 : (2 : ZMod 1143006901) ^ 381002300 = ((329431289 : ℕ) : ZMod 1143006901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1143006901 - 1) / 5 = 228601380 from by norm_num]
      have h2 : (2 : ZMod 1143006901) ^ 228601380 = ((1114088667 : ℕ) : ZMod 1143006901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1143006901 - 1) / 7 = 163286700 from by norm_num]
      have h2 : (2 : ZMod 1143006901) ^ 163286700 = ((737565435 : ℕ) : ZMod 1143006901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1143006901 - 1) / 17 = 67235700 from by norm_num]
      have h2 : (2 : ZMod 1143006901) ^ 67235700 = ((820433577 : ℕ) : ZMod 1143006901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1143006901 - 1) / 101 = 11316900 from by norm_num]
      have h2 : (2 : ZMod 1143006901) ^ 11316900 = ((401539624 : ℕ) : ZMod 1143006901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1143006901 - 1) / 317 = 3605700 from by norm_num]
      have h2 : (2 : ZMod 1143006901) ^ 3605700 = ((275539106 : ℕ) : ZMod 1143006901) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_103359821 : Nat.Prime 103359821 := by
  refine lucas_primality 103359821 (2 : ZMod 103359821) ?_ (fun q hq hd => ?_)
  · rw [show 103359821 - 1 = 103359820 from by norm_num]
    reduce_mod_char
  · have e : 103359821 - 1 = [2 ^ 2, 5 ^ 1, 5167991 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103359821 - 1) / 2 = 51679910 from by norm_num]
      have h2 : (2 : ZMod 103359821) ^ 51679910 = ((103359820 : ℕ) : ZMod 103359821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103359821 - 1) / 5 = 20671964 from by norm_num]
      have h2 : (2 : ZMod 103359821) ^ 20671964 = ((82330798 : ℕ) : ZMod 103359821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (103359821 - 1) / 5167991 = 20 from by norm_num]
      have h2 : (2 : ZMod 103359821) ^ 20 = ((1048576 : ℕ) : ZMod 103359821) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_563275751 : Nat.Prime 563275751 := by
  refine lucas_primality 563275751 (11 : ZMod 563275751) ?_ (fun q hq hd => ?_)
  · rw [show 563275751 - 1 = 563275750 from by norm_num]
    reduce_mod_char
  · have e : 563275751 - 1 = [2 ^ 1, 5 ^ 3, 23 ^ 1, 97961 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563275751 - 1) / 2 = 281637875 from by norm_num]
      have h2 : (11 : ZMod 563275751) ^ 281637875 = ((563275750 : ℕ) : ZMod 563275751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563275751 - 1) / 5 = 112655150 from by norm_num]
      have h2 : (11 : ZMod 563275751) ^ 112655150 = ((80231747 : ℕ) : ZMod 563275751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563275751 - 1) / 23 = 24490250 from by norm_num]
      have h2 : (11 : ZMod 563275751) ^ 24490250 = ((57828151 : ℕ) : ZMod 563275751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (563275751 - 1) / 97961 = 5750 from by norm_num]
      have h2 : (11 : ZMod 563275751) ^ 5750 = ((2476611 : ℕ) : ZMod 563275751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_85617914153 : Nat.Prime 85617914153 := by
  refine lucas_primality 85617914153 (3 : ZMod 85617914153) ?_ (fun q hq hd => ?_)
  · rw [show 85617914153 - 1 = 85617914152 from by norm_num]
    reduce_mod_char
  · have e : 85617914153 - 1 = [2 ^ 3, 19 ^ 1, 563275751 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85617914153 - 1) / 2 = 42808957076 from by norm_num]
      have h2 : (3 : ZMod 85617914153) ^ 42808957076 = ((85617914152 : ℕ) : ZMod 85617914153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85617914153 - 1) / 19 = 4506206008 from by norm_num]
      have h2 : (3 : ZMod 85617914153) ^ 4506206008 = ((66278774818 : ℕ) : ZMod 85617914153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_563275751).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (85617914153 - 1) / 563275751 = 152 from by norm_num]
      have h2 : (3 : ZMod 85617914153) ^ 152 = ((45583370386 : ℕ) : ZMod 85617914153) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1236838333 : Nat.Prime 1236838333 := by
  refine lucas_primality 1236838333 (6 : ZMod 1236838333) ?_ (fun q hq hd => ?_)
  · rw [show 1236838333 - 1 = 1236838332 from by norm_num]
    reduce_mod_char
  · have e : 1236838333 - 1 = [2 ^ 2, 3 ^ 1, 17 ^ 1, 199 ^ 1, 30467 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1236838333 - 1) / 2 = 618419166 from by norm_num]
      have h2 : (6 : ZMod 1236838333) ^ 618419166 = ((1236838332 : ℕ) : ZMod 1236838333) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1236838333 - 1) / 3 = 412279444 from by norm_num]
      have h2 : (6 : ZMod 1236838333) ^ 412279444 = ((532260983 : ℕ) : ZMod 1236838333) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1236838333 - 1) / 17 = 72755196 from by norm_num]
      have h2 : (6 : ZMod 1236838333) ^ 72755196 = ((803609421 : ℕ) : ZMod 1236838333) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1236838333 - 1) / 199 = 6215268 from by norm_num]
      have h2 : (6 : ZMod 1236838333) ^ 6215268 = ((1138285186 : ℕ) : ZMod 1236838333) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1236838333 - 1) / 30467 = 40596 from by norm_num]
      have h2 : (6 : ZMod 1236838333) ^ 40596 = ((779765763 : ℕ) : ZMod 1236838333) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_98143321 : Nat.Prime 98143321 := by
  refine lucas_primality 98143321 (7 : ZMod 98143321) ?_ (fun q hq hd => ?_)
  · rw [show 98143321 - 1 = 98143320 from by norm_num]
    reduce_mod_char
  · have e : 98143321 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 11 ^ 1, 149 ^ 1, 499 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98143321 - 1) / 2 = 49071660 from by norm_num]
      have h2 : (7 : ZMod 98143321) ^ 49071660 = ((98143320 : ℕ) : ZMod 98143321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98143321 - 1) / 3 = 32714440 from by norm_num]
      have h2 : (7 : ZMod 98143321) ^ 32714440 = ((50080336 : ℕ) : ZMod 98143321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98143321 - 1) / 5 = 19628664 from by norm_num]
      have h2 : (7 : ZMod 98143321) ^ 19628664 = ((28970406 : ℕ) : ZMod 98143321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98143321 - 1) / 11 = 8922120 from by norm_num]
      have h2 : (7 : ZMod 98143321) ^ 8922120 = ((94888242 : ℕ) : ZMod 98143321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98143321 - 1) / 149 = 658680 from by norm_num]
      have h2 : (7 : ZMod 98143321) ^ 658680 = ((43152065 : ℕ) : ZMod 98143321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (98143321 - 1) / 499 = 196680 from by norm_num]
      have h2 : (7 : ZMod 98143321) ^ 196680 = ((77597731 : ℕ) : ZMod 98143321) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3152674112255680948997 : Nat.Prime 3152674112255680948997 := by
  refine lucas_primality 3152674112255680948997 (2 : ZMod 3152674112255680948997) ?_ (fun q hq hd => ?_)
  · rw [show 3152674112255680948997 - 1 = 3152674112255680948996 from by norm_num]
    reduce_mod_char
  · have e : 3152674112255680948997 - 1 = [2 ^ 2, 43 ^ 1, 151 ^ 1, 98143321 ^ 1, 1236838333 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3152674112255680948997 - 1) / 2 = 1576337056127840474498 from by norm_num]
      have h2 : (2 : ZMod 3152674112255680948997) ^ 1576337056127840474498 = ((3152674112255680948996 : ℕ) : ZMod 3152674112255680948997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3152674112255680948997 - 1) / 43 = 73318002610597231372 from by norm_num]
      have h2 : (2 : ZMod 3152674112255680948997) ^ 73318002610597231372 = ((1956399704874711119138 : ℕ) : ZMod 3152674112255680948997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3152674112255680948997 - 1) / 151 = 20878636505004509596 from by norm_num]
      have h2 : (2 : ZMod 3152674112255680948997) ^ 20878636505004509596 = ((1611605194056422947221 : ℕ) : ZMod 3152674112255680948997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_98143321).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3152674112255680948997 - 1) / 98143321 = 32123165184676 from by norm_num]
      have h2 : (2 : ZMod 3152674112255680948997) ^ 32123165184676 = ((2455581143877324126961 : ℕ) : ZMod 3152674112255680948997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1236838333).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3152674112255680948997 - 1) / 1236838333 = 2548978333012 from by norm_num]
      have h2 : (2 : ZMod 3152674112255680948997) ^ 2548978333012 = ((1995536521663145655288 : ℕ) : ZMod 3152674112255680948997) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6753438709 : Nat.Prime 6753438709 := by
  refine lucas_primality 6753438709 (11 : ZMod 6753438709) ?_ (fun q hq hd => ?_)
  · rw [show 6753438709 - 1 = 6753438708 from by norm_num]
    reduce_mod_char
  · have e : 6753438709 - 1 = [2 ^ 2, 3 ^ 1, 149 ^ 1, 3777091 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6753438709 - 1) / 2 = 3376719354 from by norm_num]
      have h2 : (11 : ZMod 6753438709) ^ 3376719354 = ((6753438708 : ℕ) : ZMod 6753438709) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6753438709 - 1) / 3 = 2251146236 from by norm_num]
      have h2 : (11 : ZMod 6753438709) ^ 2251146236 = ((2864281009 : ℕ) : ZMod 6753438709) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6753438709 - 1) / 149 = 45325092 from by norm_num]
      have h2 : (11 : ZMod 6753438709) ^ 45325092 = ((5977767178 : ℕ) : ZMod 6753438709) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6753438709 - 1) / 3777091 = 1788 from by norm_num]
      have h2 : (11 : ZMod 6753438709) ^ 1788 = ((5573858438 : ℕ) : ZMod 6753438709) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_121257168100572503 : Nat.Prime 121257168100572503 := by
  refine lucas_primality 121257168100572503 (5 : ZMod 121257168100572503) ?_ (fun q hq hd => ?_)
  · rw [show 121257168100572503 - 1 = 121257168100572502 from by norm_num]
    reduce_mod_char
  · have e : 121257168100572503 - 1 = [2 ^ 1, 8977439 ^ 1, 6753438709 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (121257168100572503 - 1) / 2 = 60628584050286251 from by norm_num]
      have h2 : (5 : ZMod 121257168100572503) ^ 60628584050286251 = ((121257168100572502 : ℕ) : ZMod 121257168100572503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (121257168100572503 - 1) / 8977439 = 13506877418 from by norm_num]
      have h2 : (5 : ZMod 121257168100572503) ^ 13506877418 = ((57103585346356993 : ℕ) : ZMod 121257168100572503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6753438709).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (121257168100572503 - 1) / 6753438709 = 17954878 from by norm_num]
      have h2 : (5 : ZMod 121257168100572503) ^ 17954878 = ((48062838645410321 : ℕ) : ZMod 121257168100572503) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_814848169635847220161 : Nat.Prime 814848169635847220161 := by
  refine lucas_primality 814848169635847220161 (11 : ZMod 814848169635847220161) ?_ (fun q hq hd => ?_)
  · rw [show 814848169635847220161 - 1 = 814848169635847220160 from by norm_num]
    reduce_mod_char
  · have e : 814848169635847220161 - 1 = [2 ^ 6, 3 ^ 1, 5 ^ 1, 7 ^ 1, 121257168100572503 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (814848169635847220161 - 1) / 2 = 407424084817923610080 from by norm_num]
      have h2 : (11 : ZMod 814848169635847220161) ^ 407424084817923610080 = ((814848169635847220160 : ℕ) : ZMod 814848169635847220161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (814848169635847220161 - 1) / 3 = 271616056545282406720 from by norm_num]
      have h2 : (11 : ZMod 814848169635847220161) ^ 271616056545282406720 = ((121137362418867073893 : ℕ) : ZMod 814848169635847220161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (814848169635847220161 - 1) / 5 = 162969633927169444032 from by norm_num]
      have h2 : (11 : ZMod 814848169635847220161) ^ 162969633927169444032 = ((93252340593094564467 : ℕ) : ZMod 814848169635847220161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (814848169635847220161 - 1) / 7 = 116406881376549602880 from by norm_num]
      have h2 : (11 : ZMod 814848169635847220161) ^ 116406881376549602880 = ((110597810523240547308 : ℕ) : ZMod 814848169635847220161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_121257168100572503).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (814848169635847220161 - 1) / 121257168100572503 = 6720 from by norm_num]
      have h2 : (11 : ZMod 814848169635847220161) ^ 6720 = ((780303288781006167939 : ℕ) : ZMod 814848169635847220161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1875395569 : Nat.Prime 1875395569 := by
  refine lucas_primality 1875395569 (13 : ZMod 1875395569) ?_ (fun q hq hd => ?_)
  · rw [show 1875395569 - 1 = 1875395568 from by norm_num]
    reduce_mod_char
  · have e : 1875395569 - 1 = [2 ^ 4, 3 ^ 1, 39070741 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1875395569 - 1) / 2 = 937697784 from by norm_num]
      have h2 : (13 : ZMod 1875395569) ^ 937697784 = ((1875395568 : ℕ) : ZMod 1875395569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1875395569 - 1) / 3 = 625131856 from by norm_num]
      have h2 : (13 : ZMod 1875395569) ^ 625131856 = ((476244790 : ℕ) : ZMod 1875395569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1875395569 - 1) / 39070741 = 48 from by norm_num]
      have h2 : (13 : ZMod 1875395569) ^ 48 = ((38909997 : ℕ) : ZMod 1875395569) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_932271328997334718624259 : Nat.Prime 932271328997334718624259 := by
  refine lucas_primality 932271328997334718624259 (2 : ZMod 932271328997334718624259) ?_ (fun q hq hd => ?_)
  · rw [show 932271328997334718624259 - 1 = 932271328997334718624258 from by norm_num]
    reduce_mod_char
  · have e : 932271328997334718624259 - 1 = [2 ^ 1, 13 ^ 1, 29 ^ 1, 1451 ^ 1, 2837 ^ 1, 160159 ^ 1, 1875395569 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (932271328997334718624259 - 1) / 2 = 466135664498667359312129 from by norm_num]
      have h2 : (2 : ZMod 932271328997334718624259) ^ 466135664498667359312129 = ((932271328997334718624258 : ℕ) : ZMod 932271328997334718624259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (932271328997334718624259 - 1) / 13 = 71713179153641132201866 from by norm_num]
      have h2 : (2 : ZMod 932271328997334718624259) ^ 71713179153641132201866 = ((538212348359023921831877 : ℕ) : ZMod 932271328997334718624259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (932271328997334718624259 - 1) / 29 = 32147287206804645469802 from by norm_num]
      have h2 : (2 : ZMod 932271328997334718624259) ^ 32147287206804645469802 = ((201480517690400251088444 : ℕ) : ZMod 932271328997334718624259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (932271328997334718624259 - 1) / 1451 = 642502638867908145158 from by norm_num]
      have h2 : (2 : ZMod 932271328997334718624259) ^ 642502638867908145158 = ((352121272456505540494228 : ℕ) : ZMod 932271328997334718624259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (932271328997334718624259 - 1) / 2837 = 328611677475267789434 from by norm_num]
      have h2 : (2 : ZMod 932271328997334718624259) ^ 328611677475267789434 = ((553496637354321448415856 : ℕ) : ZMod 932271328997334718624259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (932271328997334718624259 - 1) / 160159 = 5820911275653161662 from by norm_num]
      have h2 : (2 : ZMod 932271328997334718624259) ^ 5820911275653161662 = ((72676929858106399253266 : ℕ) : ZMod 932271328997334718624259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1875395569).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (932271328997334718624259 - 1) / 1875395569 = 497106500840482 from by norm_num]
      have h2 : (2 : ZMod 932271328997334718624259) ^ 497106500840482 = ((43007597839817689696576 : ℕ) : ZMod 932271328997334718624259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1882436454200818283269402985426012696134227562123 : Nat.Prime 1882436454200818283269402985426012696134227562123 := by
  refine lucas_primality 1882436454200818283269402985426012696134227562123 (2 : ZMod 1882436454200818283269402985426012696134227562123) ?_ (fun q hq hd => ?_)
  · rw [show 1882436454200818283269402985426012696134227562123 - 1 = 1882436454200818283269402985426012696134227562122 from by norm_num]
    reduce_mod_char
  · have e : 1882436454200818283269402985426012696134227562123 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 59 ^ 1, 814848169635847220161 ^ 1, 932271328997334718624259 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1882436454200818283269402985426012696134227562123 - 1) / 2 = 941218227100409141634701492713006348067113781061 from by norm_num]
      have h2 : (2 : ZMod 1882436454200818283269402985426012696134227562123) ^ 941218227100409141634701492713006348067113781061 = ((1882436454200818283269402985426012696134227562122 : ℕ) : ZMod 1882436454200818283269402985426012696134227562123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1882436454200818283269402985426012696134227562123 - 1) / 3 = 627478818066939427756467661808670898711409187374 from by norm_num]
      have h2 : (2 : ZMod 1882436454200818283269402985426012696134227562123) ^ 627478818066939427756467661808670898711409187374 = ((454273759324211383915993515874512397538956600046 : ℕ) : ZMod 1882436454200818283269402985426012696134227562123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1882436454200818283269402985426012696134227562123 - 1) / 7 = 268919493457259754752771855060858956590603937446 from by norm_num]
      have h2 : (2 : ZMod 1882436454200818283269402985426012696134227562123) ^ 268919493457259754752771855060858956590603937446 = ((901594038265371923802247702862447750814408632194 : ℕ) : ZMod 1882436454200818283269402985426012696134227562123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1882436454200818283269402985426012696134227562123 - 1) / 59 = 31905702613573191241854287888576486375156399358 from by norm_num]
      have h2 : (2 : ZMod 1882436454200818283269402985426012696134227562123) ^ 31905702613573191241854287888576486375156399358 = ((291743381056449682839636289972234056305390817560 : ℕ) : ZMod 1882436454200818283269402985426012696134227562123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_814848169635847220161).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1882436454200818283269402985426012696134227562123 - 1) / 814848169635847220161 = 2310168353255395432750913802 from by norm_num]
      have h2 : (2 : ZMod 1882436454200818283269402985426012696134227562123) ^ 2310168353255395432750913802 = ((620410612458318828346513509114567106545967585818 : ℕ) : ZMod 1882436454200818283269402985426012696134227562123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_932271328997334718624259).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1882436454200818283269402985426012696134227562123 - 1) / 932271328997334718624259 = 2019193764357629411558958 from by norm_num]
      have h2 : (2 : ZMod 1882436454200818283269402985426012696134227562123) ^ 2019193764357629411558958 = ((741427218885335080651838513566145628018145886468 : ℕ) : ZMod 1882436454200818283269402985426012696134227562123) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 : Nat.Prime 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 := by
  refine lucas_primality 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 (5 : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) ?_ (fun q hq hd => ?_)
  · rw [show 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 - 1 = 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088696 from by norm_num]
    reduce_mod_char
  · have e : 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 - 1 = [2 ^ 3, 3 ^ 2, 181 ^ 1, 103359821 ^ 1, 85617914153 ^ 1, 3152674112255680948997 ^ 1, 1882436454200818283269402985426012696134227562123 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 - 1) / 2 = 342213290808476775498132642399457166138411256478531812374836611249801433991281533944612544348 from by norm_num]
      have h2 : (5 : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) ^ 342213290808476775498132642399457166138411256478531812374836611249801433991281533944612544348 = ((684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088696 : ℕ) : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 - 1) / 3 = 228142193872317850332088428266304777425607504319021208249891074166534289327521022629741696232 from by norm_num]
      have h2 : (5 : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) ^ 228142193872317850332088428266304777425607504319021208249891074166534289327521022629741696232 = ((147433460744146495028867871868463065950373216342449141926112941918680886238476724959689446962 : ℕ) : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 - 1) / 181 = 3781362329375433983404780578999526697662002834016926103589354820439794850732392640271961816 from by norm_num]
      have h2 : (5 : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) ^ 3781362329375433983404780578999526697662002834016926103589354820439794850732392640271961816 = ((602104160493204095082192304954494305820918053066966602921737152305582757754754654416492897779 : ℕ) : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_103359821).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 - 1) / 103359821 = 6621785670632629588205897577927445639411686993508470034498929932353529017649547476376 from by norm_num]
      have h2 : (5 : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) ^ 6621785670632629588205897577927445639411686993508470034498929932353529017649547476376 = ((27128972558527043140755424928004662798520872090382097081732351622285832280174704503124818713 : ℕ) : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_85617914153).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 - 1) / 85617914153 = 7993964678862381009777007534930507410311992408263167755820453133897580575208048632 from by norm_num]
      have h2 : (5 : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) ^ 7993964678862381009777007534930507410311992408263167755820453133897580575208048632 = ((592794045569154843094839847332416936649886629536813265257039960298200982584435089498385693716 : ℕ) : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3152674112255680948997).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 - 1) / 3152674112255680948997 = 217093983471466002027659567031602157532270921578164024289758395382247768 from by norm_num]
      have h2 : (5 : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) ^ 217093983471466002027659567031602157532270921578164024289758395382247768 = ((283804497832037535173795121297491776314893946178678689099657513753892931250445051051568100581 : ℕ) : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1882436454200818283269402985426012696134227562123).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 - 1) / 1882436454200818283269402985426012696134227562123 = 363585490543171842423171518872229972031802152 from by norm_num]
      have h2 : (5 : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) ^ 363585490543171842423171518872229972031802152 = ((162925938710718053762437670686655941587738474546283692410422687276798376596289374685273189293 : ℕ) : ZMod 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_22620422017 : Nat.Prime 22620422017 := by
  refine lucas_primality 22620422017 (5 : ZMod 22620422017) ?_ (fun q hq hd => ?_)
  · rw [show 22620422017 - 1 = 22620422016 from by norm_num]
    reduce_mod_char
  · have e : 22620422017 - 1 = [2 ^ 7, 3 ^ 3, 6545261 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22620422017 - 1) / 2 = 11310211008 from by norm_num]
      have h2 : (5 : ZMod 22620422017) ^ 11310211008 = ((22620422016 : ℕ) : ZMod 22620422017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22620422017 - 1) / 3 = 7540140672 from by norm_num]
      have h2 : (5 : ZMod 22620422017) ^ 7540140672 = ((15673570660 : ℕ) : ZMod 22620422017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (22620422017 - 1) / 6545261 = 3456 from by norm_num]
      have h2 : (5 : ZMod 22620422017) ^ 3456 = ((14379989944 : ℕ) : ZMod 22620422017) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2258206814111 : Nat.Prime 2258206814111 := by
  refine lucas_primality 2258206814111 (19 : ZMod 2258206814111) ?_ (fun q hq hd => ?_)
  · rw [show 2258206814111 - 1 = 2258206814110 from by norm_num]
    reduce_mod_char
  · have e : 2258206814111 - 1 = [2 ^ 1, 5 ^ 1, 13 ^ 1, 1693 ^ 1, 10260379 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2258206814111 - 1) / 2 = 1129103407055 from by norm_num]
      have h2 : (19 : ZMod 2258206814111) ^ 1129103407055 = ((2258206814110 : ℕ) : ZMod 2258206814111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2258206814111 - 1) / 5 = 451641362822 from by norm_num]
      have h2 : (19 : ZMod 2258206814111) ^ 451641362822 = ((2221436564159 : ℕ) : ZMod 2258206814111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2258206814111 - 1) / 13 = 173708216470 from by norm_num]
      have h2 : (19 : ZMod 2258206814111) ^ 173708216470 = ((1106481867032 : ℕ) : ZMod 2258206814111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2258206814111 - 1) / 1693 = 1333849270 from by norm_num]
      have h2 : (19 : ZMod 2258206814111) ^ 1333849270 = ((1888507413413 : ℕ) : ZMod 2258206814111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2258206814111 - 1) / 10260379 = 220090 from by norm_num]
      have h2 : (19 : ZMod 2258206814111) ^ 220090 = ((920314635848 : ℕ) : ZMod 2258206814111) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4010575301861137 : Nat.Prime 4010575301861137 := by
  refine lucas_primality 4010575301861137 (5 : ZMod 4010575301861137) ?_ (fun q hq hd => ?_)
  · rw [show 4010575301861137 - 1 = 4010575301861136 from by norm_num]
    reduce_mod_char
  · have e : 4010575301861137 - 1 = [2 ^ 4, 3 ^ 1, 37 ^ 1, 2258206814111 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4010575301861137 - 1) / 2 = 2005287650930568 from by norm_num]
      have h2 : (5 : ZMod 4010575301861137) ^ 2005287650930568 = ((4010575301861136 : ℕ) : ZMod 4010575301861137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4010575301861137 - 1) / 3 = 1336858433953712 from by norm_num]
      have h2 : (5 : ZMod 4010575301861137) ^ 1336858433953712 = ((3139941642374586 : ℕ) : ZMod 4010575301861137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4010575301861137 - 1) / 37 = 108393927077328 from by norm_num]
      have h2 : (5 : ZMod 4010575301861137) ^ 108393927077328 = ((2198623160982629 : ℕ) : ZMod 4010575301861137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2258206814111).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4010575301861137 - 1) / 2258206814111 = 1776 from by norm_num]
      have h2 : (5 : ZMod 4010575301861137) ^ 1776 = ((3357049161656358 : ℕ) : ZMod 4010575301861137) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_15680976156013433 : Nat.Prime 15680976156013433 := by
  refine lucas_primality 15680976156013433 (3 : ZMod 15680976156013433) ?_ (fun q hq hd => ?_)
  · rw [show 15680976156013433 - 1 = 15680976156013432 from by norm_num]
    reduce_mod_char
  · have e : 15680976156013433 - 1 = [2 ^ 3, 11 ^ 1, 23 ^ 1, 797 ^ 1, 15077 ^ 1, 644747 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15680976156013433 - 1) / 2 = 7840488078006716 from by norm_num]
      have h2 : (3 : ZMod 15680976156013433) ^ 7840488078006716 = ((15680976156013432 : ℕ) : ZMod 15680976156013433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15680976156013433 - 1) / 11 = 1425543286910312 from by norm_num]
      have h2 : (3 : ZMod 15680976156013433) ^ 1425543286910312 = ((6572630064300327 : ℕ) : ZMod 15680976156013433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15680976156013433 - 1) / 23 = 681781572000584 from by norm_num]
      have h2 : (3 : ZMod 15680976156013433) ^ 681781572000584 = ((12181719328423334 : ℕ) : ZMod 15680976156013433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15680976156013433 - 1) / 797 = 19675001450456 from by norm_num]
      have h2 : (3 : ZMod 15680976156013433) ^ 19675001450456 = ((7648092847754854 : ℕ) : ZMod 15680976156013433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15680976156013433 - 1) / 15077 = 1040059438616 from by norm_num]
      have h2 : (3 : ZMod 15680976156013433) ^ 1040059438616 = ((7431443801683376 : ℕ) : ZMod 15680976156013433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (15680976156013433 - 1) / 644747 = 24321130856 from by norm_num]
      have h2 : (3 : ZMod 15680976156013433) ^ 24321130856 = ((5687857387804071 : ℕ) : ZMod 15680976156013433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6962353413269964253 : Nat.Prime 6962353413269964253 := by
  refine lucas_primality 6962353413269964253 (2 : ZMod 6962353413269964253) ?_ (fun q hq hd => ?_)
  · rw [show 6962353413269964253 - 1 = 6962353413269964252 from by norm_num]
    reduce_mod_char
  · have e : 6962353413269964253 - 1 = [2 ^ 2, 3 ^ 1, 37 ^ 1, 15680976156013433 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6962353413269964253 - 1) / 2 = 3481176706634982126 from by norm_num]
      have h2 : (2 : ZMod 6962353413269964253) ^ 3481176706634982126 = ((6962353413269964252 : ℕ) : ZMod 6962353413269964253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6962353413269964253 - 1) / 3 = 2320784471089988084 from by norm_num]
      have h2 : (2 : ZMod 6962353413269964253) ^ 2320784471089988084 = ((450283905890997363 : ℕ) : ZMod 6962353413269964253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6962353413269964253 - 1) / 37 = 188171713872161196 from by norm_num]
      have h2 : (2 : ZMod 6962353413269964253) ^ 188171713872161196 = ((4128949700608304537 : ℕ) : ZMod 6962353413269964253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_15680976156013433).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6962353413269964253 - 1) / 15680976156013433 = 444 from by norm_num]
      have h2 : (2 : ZMod 6962353413269964253) ^ 444 = ((3555987333119462278 : ℕ) : ZMod 6962353413269964253) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_905459623 : Nat.Prime 905459623 := by
  refine lucas_primality 905459623 (3 : ZMod 905459623) ?_ (fun q hq hd => ?_)
  · rw [show 905459623 - 1 = 905459622 from by norm_num]
    reduce_mod_char
  · have e : 905459623 - 1 = [2 ^ 1, 3 ^ 1, 139 ^ 1, 1033 ^ 1, 1051 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (905459623 - 1) / 2 = 452729811 from by norm_num]
      have h2 : (3 : ZMod 905459623) ^ 452729811 = ((905459622 : ℕ) : ZMod 905459623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (905459623 - 1) / 3 = 301819874 from by norm_num]
      have h2 : (3 : ZMod 905459623) ^ 301819874 = ((587551086 : ℕ) : ZMod 905459623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (905459623 - 1) / 139 = 6514098 from by norm_num]
      have h2 : (3 : ZMod 905459623) ^ 6514098 = ((117230112 : ℕ) : ZMod 905459623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (905459623 - 1) / 1033 = 876534 from by norm_num]
      have h2 : (3 : ZMod 905459623) ^ 876534 = ((901259562 : ℕ) : ZMod 905459623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (905459623 - 1) / 1051 = 861522 from by norm_num]
      have h2 : (3 : ZMod 905459623) ^ 861522 = ((725468530 : ℕ) : ZMod 905459623) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_24949974011374402181 : Nat.Prime 24949974011374402181 := by
  refine lucas_primality 24949974011374402181 (2 : ZMod 24949974011374402181) ?_ (fun q hq hd => ?_)
  · rw [show 24949974011374402181 - 1 = 24949974011374402180 from by norm_num]
    reduce_mod_char
  · have e : 24949974011374402181 - 1 = [2 ^ 2, 5 ^ 1, 19 ^ 1, 3919 ^ 1, 18503 ^ 1, 905459623 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24949974011374402181 - 1) / 2 = 12474987005687201090 from by norm_num]
      have h2 : (2 : ZMod 24949974011374402181) ^ 12474987005687201090 = ((24949974011374402180 : ℕ) : ZMod 24949974011374402181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24949974011374402181 - 1) / 5 = 4989994802274880436 from by norm_num]
      have h2 : (2 : ZMod 24949974011374402181) ^ 4989994802274880436 = ((24258322076827834329 : ℕ) : ZMod 24949974011374402181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24949974011374402181 - 1) / 19 = 1313156526914442220 from by norm_num]
      have h2 : (2 : ZMod 24949974011374402181) ^ 1313156526914442220 = ((10603967051005075732 : ℕ) : ZMod 24949974011374402181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24949974011374402181 - 1) / 3919 = 6366413373660220 from by norm_num]
      have h2 : (2 : ZMod 24949974011374402181) ^ 6366413373660220 = ((6313032357486227098 : ℕ) : ZMod 24949974011374402181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24949974011374402181 - 1) / 18503 = 1348428579764060 from by norm_num]
      have h2 : (2 : ZMod 24949974011374402181) ^ 1348428579764060 = ((5208793451894642249 : ℕ) : ZMod 24949974011374402181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_905459623).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24949974011374402181 - 1) / 905459623 = 27555037660 from by norm_num]
      have h2 : (2 : ZMod 24949974011374402181) ^ 27555037660 = ((2986628400727849370 : ℕ) : ZMod 24949974011374402181) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_142659759801404920771391593 : Nat.Prime 142659759801404920771391593 := by
  refine lucas_primality 142659759801404920771391593 (7 : ZMod 142659759801404920771391593) ?_ (fun q hq hd => ?_)
  · rw [show 142659759801404920771391593 - 1 = 142659759801404920771391592 from by norm_num]
    reduce_mod_char
  · have e : 142659759801404920771391593 - 1 = [2 ^ 3, 3 ^ 1, 37 ^ 1, 47 ^ 1, 137 ^ 1, 24949974011374402181 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142659759801404920771391593 - 1) / 2 = 71329879900702460385695796 from by norm_num]
      have h2 : (7 : ZMod 142659759801404920771391593) ^ 71329879900702460385695796 = ((142659759801404920771391592 : ℕ) : ZMod 142659759801404920771391593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142659759801404920771391593 - 1) / 3 = 47553253267134973590463864 from by norm_num]
      have h2 : (7 : ZMod 142659759801404920771391593) ^ 47553253267134973590463864 = ((98513230859901602911837040 : ℕ) : ZMod 142659759801404920771391593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142659759801404920771391593 - 1) / 37 = 3855669183821754615443016 from by norm_num]
      have h2 : (7 : ZMod 142659759801404920771391593) ^ 3855669183821754615443016 = ((142659758450553203098399504 : ℕ) : ZMod 142659759801404920771391593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142659759801404920771391593 - 1) / 47 = 3035314038327764271731736 from by norm_num]
      have h2 : (7 : ZMod 142659759801404920771391593) ^ 3035314038327764271731736 = ((129881691278840157698403853 : ℕ) : ZMod 142659759801404920771391593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142659759801404920771391593 - 1) / 137 = 1041312115338722049426216 from by norm_num]
      have h2 : (7 : ZMod 142659759801404920771391593) ^ 1041312115338722049426216 = ((64876686381314771690400404 : ℕ) : ZMod 142659759801404920771391593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_24949974011374402181).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (142659759801404920771391593 - 1) / 24949974011374402181 = 5717832 from by norm_num]
      have h2 : (7 : ZMod 142659759801404920771391593) ^ 5717832 = ((61903006422860229761980127 : ℕ) : ZMod 142659759801404920771391593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_126578756929969 : Nat.Prime 126578756929969 := by
  refine lucas_primality 126578756929969 (13 : ZMod 126578756929969) ?_ (fun q hq hd => ?_)
  · rw [show 126578756929969 - 1 = 126578756929968 from by norm_num]
    reduce_mod_char
  · have e : 126578756929969 - 1 = [2 ^ 4, 3 ^ 2, 7 ^ 1, 67349 ^ 1, 1864529 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126578756929969 - 1) / 2 = 63289378464984 from by norm_num]
      have h2 : (13 : ZMod 126578756929969) ^ 63289378464984 = ((126578756929968 : ℕ) : ZMod 126578756929969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126578756929969 - 1) / 3 = 42192918976656 from by norm_num]
      have h2 : (13 : ZMod 126578756929969) ^ 42192918976656 = ((109756808094435 : ℕ) : ZMod 126578756929969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126578756929969 - 1) / 7 = 18082679561424 from by norm_num]
      have h2 : (13 : ZMod 126578756929969) ^ 18082679561424 = ((44571214426817 : ℕ) : ZMod 126578756929969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126578756929969 - 1) / 67349 = 1879445232 from by norm_num]
      have h2 : (13 : ZMod 126578756929969) ^ 1879445232 = ((105196679217423 : ℕ) : ZMod 126578756929969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (126578756929969 - 1) / 1864529 = 67887792 from by norm_num]
      have h2 : (13 : ZMod 126578756929969) ^ 67887792 = ((31280140420875 : ℕ) : ZMod 126578756929969) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13134076368655567075211 : Nat.Prime 13134076368655567075211 := by
  refine lucas_primality 13134076368655567075211 (2 : ZMod 13134076368655567075211) ?_ (fun q hq hd => ?_)
  · rw [show 13134076368655567075211 - 1 = 13134076368655567075210 from by norm_num]
    reduce_mod_char
  · have e : 13134076368655567075211 - 1 = [2 ^ 1, 5 ^ 1, 10376209 ^ 1, 126578756929969 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13134076368655567075211 - 1) / 2 = 6567038184327783537605 from by norm_num]
      have h2 : (2 : ZMod 13134076368655567075211) ^ 6567038184327783537605 = ((13134076368655567075210 : ℕ) : ZMod 13134076368655567075211) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13134076368655567075211 - 1) / 5 = 2626815273731113415042 from by norm_num]
      have h2 : (2 : ZMod 13134076368655567075211) ^ 2626815273731113415042 = ((5818498770005198689159 : ℕ) : ZMod 13134076368655567075211) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13134076368655567075211 - 1) / 10376209 = 1265787569299690 from by norm_num]
      have h2 : (2 : ZMod 13134076368655567075211) ^ 1265787569299690 = ((9875822409667474084851 : ℕ) : ZMod 13134076368655567075211) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_126578756929969).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13134076368655567075211 - 1) / 126578756929969 = 103762090 from by norm_num]
      have h2 : (2 : ZMod 13134076368655567075211) ^ 103762090 = ((266742508384495481131 : ℕ) : ZMod 13134076368655567075211) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2345843457917157221 : Nat.Prime 2345843457917157221 := by
  refine lucas_primality 2345843457917157221 (2 : ZMod 2345843457917157221) ?_ (fun q hq hd => ?_)
  · rw [show 2345843457917157221 - 1 = 2345843457917157220 from by norm_num]
    reduce_mod_char
  · have e : 2345843457917157221 - 1 = [2 ^ 2, 5 ^ 1, 11 ^ 1, 41 ^ 1, 151 ^ 1, 157 ^ 1, 797 ^ 1, 13764409 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2345843457917157221 - 1) / 2 = 1172921728958578610 from by norm_num]
      have h2 : (2 : ZMod 2345843457917157221) ^ 1172921728958578610 = ((2345843457917157220 : ℕ) : ZMod 2345843457917157221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2345843457917157221 - 1) / 5 = 469168691583431444 from by norm_num]
      have h2 : (2 : ZMod 2345843457917157221) ^ 469168691583431444 = ((870848611949902839 : ℕ) : ZMod 2345843457917157221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2345843457917157221 - 1) / 11 = 213258496174287020 from by norm_num]
      have h2 : (2 : ZMod 2345843457917157221) ^ 213258496174287020 = ((1592429671637338772 : ℕ) : ZMod 2345843457917157221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2345843457917157221 - 1) / 41 = 57215694095540420 from by norm_num]
      have h2 : (2 : ZMod 2345843457917157221) ^ 57215694095540420 = ((1431693889682516541 : ℕ) : ZMod 2345843457917157221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2345843457917157221 - 1) / 151 = 15535387138524220 from by norm_num]
      have h2 : (2 : ZMod 2345843457917157221) ^ 15535387138524220 = ((1523344725586662398 : ℕ) : ZMod 2345843457917157221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2345843457917157221 - 1) / 157 = 14941678075905460 from by norm_num]
      have h2 : (2 : ZMod 2345843457917157221) ^ 14941678075905460 = ((479158761368023734 : ℕ) : ZMod 2345843457917157221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2345843457917157221 - 1) / 797 = 2943341854350260 from by norm_num]
      have h2 : (2 : ZMod 2345843457917157221) ^ 2943341854350260 = ((1939207795026950233 : ℕ) : ZMod 2345843457917157221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2345843457917157221 - 1) / 13764409 = 170428200580 from by norm_num]
      have h2 : (2 : ZMod 2345843457917157221) ^ 170428200580 = ((69138749852883254 : ℕ) : ZMod 2345843457917157221) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_14373616515152387435471235475346778247660988205097 : Nat.Prime 14373616515152387435471235475346778247660988205097 := by
  refine lucas_primality 14373616515152387435471235475346778247660988205097 (5 : ZMod 14373616515152387435471235475346778247660988205097) ?_ (fun q hq hd => ?_)
  · rw [show 14373616515152387435471235475346778247660988205097 - 1 = 14373616515152387435471235475346778247660988205096 from by norm_num]
    reduce_mod_char
  · have e : 14373616515152387435471235475346778247660988205097 - 1 = [2 ^ 3, 3 ^ 3, 7 ^ 1, 31 ^ 1, 37 ^ 1, 269 ^ 1, 2345843457917157221 ^ 1, 13134076368655567075211 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14373616515152387435471235475346778247660988205097 - 1) / 2 = 7186808257576193717735617737673389123830494102548 from by norm_num]
      have h2 : (5 : ZMod 14373616515152387435471235475346778247660988205097) ^ 7186808257576193717735617737673389123830494102548 = ((14373616515152387435471235475346778247660988205096 : ℕ) : ZMod 14373616515152387435471235475346778247660988205097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14373616515152387435471235475346778247660988205097 - 1) / 3 = 4791205505050795811823745158448926082553662735032 from by norm_num]
      have h2 : (5 : ZMod 14373616515152387435471235475346778247660988205097) ^ 4791205505050795811823745158448926082553662735032 = ((14373616515152184679875331022777071686330115251328 : ℕ) : ZMod 14373616515152387435471235475346778247660988205097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14373616515152387435471235475346778247660988205097 - 1) / 7 = 2053373787878912490781605067906682606808712600728 from by norm_num]
      have h2 : (5 : ZMod 14373616515152387435471235475346778247660988205097) ^ 2053373787878912490781605067906682606808712600728 = ((758478830393896463835264216295948195208533688037 : ℕ) : ZMod 14373616515152387435471235475346778247660988205097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14373616515152387435471235475346778247660988205097 - 1) / 31 = 463665048875883465660362434688605749924548006616 from by norm_num]
      have h2 : (5 : ZMod 14373616515152387435471235475346778247660988205097) ^ 463665048875883465660362434688605749924548006616 = ((5170713242661340731935654055643857516756592767564 : ℕ) : ZMod 14373616515152387435471235475346778247660988205097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14373616515152387435471235475346778247660988205097 - 1) / 37 = 388476122031145606364087445279642655342188870408 from by norm_num]
      have h2 : (5 : ZMod 14373616515152387435471235475346778247660988205097) ^ 388476122031145606364087445279642655342188870408 = ((8918365457199159522736024817377139184935256396982 : ℕ) : ZMod 14373616515152387435471235475346778247660988205097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14373616515152387435471235475346778247660988205097 - 1) / 269 = 53433518643689172622569648607237093857475792584 from by norm_num]
      have h2 : (5 : ZMod 14373616515152387435471235475346778247660988205097) ^ 53433518643689172622569648607237093857475792584 = ((2828067866877783079067827422553870267432814053008 : ℕ) : ZMod 14373616515152387435471235475346778247660988205097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2345843457917157221).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14373616515152387435471235475346778247660988205097 - 1) / 2345843457917157221 = 6127270115421311083715283290376 from by norm_num]
      have h2 : (5 : ZMod 14373616515152387435471235475346778247660988205097) ^ 6127270115421311083715283290376 = ((1682421959222810872139778896504619350226725540319 : ℕ) : ZMod 14373616515152387435471235475346778247660988205097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_13134076368655567075211).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (14373616515152387435471235475346778247660988205097 - 1) / 13134076368655567075211 = 1094375889990633761943772536 from by norm_num]
      have h2 : (5 : ZMod 14373616515152387435471235475346778247660988205097) ^ 1094375889990633761943772536 = ((6071607105662287932452533047187379127757390709146 : ℕ) : ZMod 14373616515152387435471235475346778247660988205097) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_64326272436179833 : Nat.Prime 64326272436179833 := by
  refine lucas_primality 64326272436179833 (10 : ZMod 64326272436179833) ?_ (fun q hq hd => ?_)
  · rw [show 64326272436179833 - 1 = 64326272436179832 from by norm_num]
    reduce_mod_char
  · have e : 64326272436179833 - 1 = [2 ^ 3, 3 ^ 1, 13 ^ 1, 19 ^ 1, 37 ^ 1, 59 ^ 1, 283 ^ 1, 757 ^ 1, 23203 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64326272436179833 - 1) / 2 = 32163136218089916 from by norm_num]
      have h2 : (10 : ZMod 64326272436179833) ^ 32163136218089916 = ((64326272436179832 : ℕ) : ZMod 64326272436179833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64326272436179833 - 1) / 3 = 21442090812059944 from by norm_num]
      have h2 : (10 : ZMod 64326272436179833) ^ 21442090812059944 = ((1162261468 : ℕ) : ZMod 64326272436179833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64326272436179833 - 1) / 13 = 4948174802783064 from by norm_num]
      have h2 : (10 : ZMod 64326272436179833) ^ 4948174802783064 = ((28036712213931899 : ℕ) : ZMod 64326272436179833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64326272436179833 - 1) / 19 = 3385593286114728 from by norm_num]
      have h2 : (10 : ZMod 64326272436179833) ^ 3385593286114728 = ((58445454027471097 : ℕ) : ZMod 64326272436179833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64326272436179833 - 1) / 37 = 1738547903680536 from by norm_num]
      have h2 : (10 : ZMod 64326272436179833) ^ 1738547903680536 = ((64120381303908037 : ℕ) : ZMod 64326272436179833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64326272436179833 - 1) / 59 = 1090275804003048 from by norm_num]
      have h2 : (10 : ZMod 64326272436179833) ^ 1090275804003048 = ((17548482013599081 : ℕ) : ZMod 64326272436179833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64326272436179833 - 1) / 283 = 227301316028904 from by norm_num]
      have h2 : (10 : ZMod 64326272436179833) ^ 227301316028904 = ((47564020904319803 : ℕ) : ZMod 64326272436179833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64326272436179833 - 1) / 757 = 84975260813976 from by norm_num]
      have h2 : (10 : ZMod 64326272436179833) ^ 84975260813976 = ((47850632919309290 : ℕ) : ZMod 64326272436179833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (64326272436179833 - 1) / 23203 = 2772325666344 from by norm_num]
      have h2 : (10 : ZMod 64326272436179833) ^ 2772325666344 = ((15515335621434162 : ℕ) : ZMod 64326272436179833) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_232285523 : Nat.Prime 232285523 := by
  refine lucas_primality 232285523 (2 : ZMod 232285523) ?_ (fun q hq hd => ?_)
  · rw [show 232285523 - 1 = 232285522 from by norm_num]
    reduce_mod_char
  · have e : 232285523 - 1 = [2 ^ 1, 7 ^ 1, 16591823 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (232285523 - 1) / 2 = 116142761 from by norm_num]
      have h2 : (2 : ZMod 232285523) ^ 116142761 = ((232285522 : ℕ) : ZMod 232285523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (232285523 - 1) / 7 = 33183646 from by norm_num]
      have h2 : (2 : ZMod 232285523) ^ 33183646 = ((206977463 : ℕ) : ZMod 232285523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (232285523 - 1) / 16591823 = 14 from by norm_num]
      have h2 : (2 : ZMod 232285523) ^ 14 = ((16384 : ℕ) : ZMod 232285523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_17189128703 : Nat.Prime 17189128703 := by
  refine lucas_primality 17189128703 (5 : ZMod 17189128703) ?_ (fun q hq hd => ?_)
  · rw [show 17189128703 - 1 = 17189128702 from by norm_num]
    reduce_mod_char
  · have e : 17189128703 - 1 = [2 ^ 1, 37 ^ 1, 232285523 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17189128703 - 1) / 2 = 8594564351 from by norm_num]
      have h2 : (5 : ZMod 17189128703) ^ 8594564351 = ((17189128702 : ℕ) : ZMod 17189128703) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17189128703 - 1) / 37 = 464571046 from by norm_num]
      have h2 : (5 : ZMod 17189128703) ^ 464571046 = ((10398361808 : ℕ) : ZMod 17189128703) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_232285523).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (17189128703 - 1) / 232285523 = 74 from by norm_num]
      have h2 : (5 : ZMod 17189128703) ^ 74 = ((12596785499 : ℕ) : ZMod 17189128703) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_119779213 : Nat.Prime 119779213 := by
  refine lucas_primality 119779213 (5 : ZMod 119779213) ?_ (fun q hq hd => ?_)
  · rw [show 119779213 - 1 = 119779212 from by norm_num]
    reduce_mod_char
  · have e : 119779213 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 17 ^ 1, 37 ^ 1, 2267 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119779213 - 1) / 2 = 59889606 from by norm_num]
      have h2 : (5 : ZMod 119779213) ^ 59889606 = ((119779212 : ℕ) : ZMod 119779213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119779213 - 1) / 3 = 39926404 from by norm_num]
      have h2 : (5 : ZMod 119779213) ^ 39926404 = ((111311064 : ℕ) : ZMod 119779213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119779213 - 1) / 7 = 17111316 from by norm_num]
      have h2 : (5 : ZMod 119779213) ^ 17111316 = ((12284458 : ℕ) : ZMod 119779213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119779213 - 1) / 17 = 7045836 from by norm_num]
      have h2 : (5 : ZMod 119779213) ^ 7045836 = ((118389426 : ℕ) : ZMod 119779213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119779213 - 1) / 37 = 3237276 from by norm_num]
      have h2 : (5 : ZMod 119779213) ^ 3237276 = ((111929357 : ℕ) : ZMod 119779213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (119779213 - 1) / 2267 = 52836 from by norm_num]
      have h2 : (5 : ZMod 119779213) ^ 52836 = ((84361782 : ℕ) : ZMod 119779213) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56737873 : Nat.Prime 56737873 := by
  refine lucas_primality 56737873 (5 : ZMod 56737873) ?_ (fun q hq hd => ?_)
  · rw [show 56737873 - 1 = 56737872 from by norm_num]
    reduce_mod_char
  · have e : 56737873 - 1 = [2 ^ 4, 3 ^ 2, 23 ^ 1, 37 ^ 1, 463 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56737873 - 1) / 2 = 28368936 from by norm_num]
      have h2 : (5 : ZMod 56737873) ^ 28368936 = ((56737872 : ℕ) : ZMod 56737873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56737873 - 1) / 3 = 18912624 from by norm_num]
      have h2 : (5 : ZMod 56737873) ^ 18912624 = ((42985869 : ℕ) : ZMod 56737873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56737873 - 1) / 23 = 2466864 from by norm_num]
      have h2 : (5 : ZMod 56737873) ^ 2466864 = ((7977695 : ℕ) : ZMod 56737873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56737873 - 1) / 37 = 1533456 from by norm_num]
      have h2 : (5 : ZMod 56737873) ^ 1533456 = ((36153302 : ℕ) : ZMod 56737873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56737873 - 1) / 463 = 122544 from by norm_num]
      have h2 : (5 : ZMod 56737873) ^ 122544 = ((16572483 : ℕ) : ZMod 56737873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_78539161 : Nat.Prime 78539161 := by
  refine lucas_primality 78539161 (22 : ZMod 78539161) ?_ (fun q hq hd => ?_)
  · rw [show 78539161 - 1 = 78539160 from by norm_num]
    reduce_mod_char
  · have e : 78539161 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 7 ^ 2, 19 ^ 2, 37 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78539161 - 1) / 2 = 39269580 from by norm_num]
      have h2 : (22 : ZMod 78539161) ^ 39269580 = ((78539160 : ℕ) : ZMod 78539161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78539161 - 1) / 3 = 26179720 from by norm_num]
      have h2 : (22 : ZMod 78539161) ^ 26179720 = ((15825949 : ℕ) : ZMod 78539161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78539161 - 1) / 5 = 15707832 from by norm_num]
      have h2 : (22 : ZMod 78539161) ^ 15707832 = ((4591199 : ℕ) : ZMod 78539161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78539161 - 1) / 7 = 11219880 from by norm_num]
      have h2 : (22 : ZMod 78539161) ^ 11219880 = ((34288500 : ℕ) : ZMod 78539161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78539161 - 1) / 19 = 4133640 from by norm_num]
      have h2 : (22 : ZMod 78539161) ^ 4133640 = ((72695434 : ℕ) : ZMod 78539161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78539161 - 1) / 37 = 2122680 from by norm_num]
      have h2 : (22 : ZMod 78539161) ^ 2122680 = ((30955189 : ℕ) : ZMod 78539161) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 : Nat.Prime 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 := by
  refine lucas_primality 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ?_ (fun q hq hd => ?_)
  · rw [show 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1 = 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884792 from by norm_num]
    reduce_mod_char
  · have e : 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1 = [2 ^ 3, 3 ^ 2, 7 ^ 1, 13 ^ 1, 73 ^ 1, 149 ^ 1, 223 ^ 1, 9769 ^ 1, 18427 ^ 1, 107671 ^ 1, 953861 ^ 1, 13097927 ^ 1, 18702169 ^ 1, 25709599 ^ 1, 56737873 ^ 1, 78539161 ^ 1, 119779213 ^ 1, 17189128703 ^ 1, 4010575301861137 ^ 1, 64326272436179833 ^ 1, 6962353413269964253 ^ 1, 142659759801404920771391593 ^ 1, 14373616515152387435471235475346778247660988205097 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 2 = 31264364784632668364292819784930167019216971108181035529906268189859505086415190962600490029040954445093840743680804766504985930191185344171303150215406503604844218899959266089096264877429573761003880034811442396 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 31264364784632668364292819784930167019216971108181035529906268189859505086415190962600490029040954445093840743680804766504985930191185344171303150215406503604844218899959266089096264877429573761003880034811442396 = ((62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884792 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 3 = 20842909856421778909528546523286778012811314072120690353270845459906336724276793975066993352693969630062560495787203177669990620127456896114202100143604335736562812599972844059397509918286382507335920023207628264 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 20842909856421778909528546523286778012811314072120690353270845459906336724276793975066993352693969630062560495787203177669990620127456896114202100143604335736562812599972844059397509918286382507335920023207628264 = ((7037454104147724306781904873957485311179232129470236176267505136259824460840360376822990526932016676095583878852677718369884419198097336033479461052442007993559041186206945868050289647858130182156166717611428742 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 7 = 8932675652752190961226519938551476291204848888051724437116076625674144310404340275028711436868844127169668783908801361858567408626052955477515185775830429601384062542845504596884647107837021074572537152803269256 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 8932675652752190961226519938551476291204848888051724437116076625674144310404340275028711436868844127169668783908801361858567408626052955477515185775830429601384062542845504596884647107837021074572537152803269256 = ((33747505853968076839796773794154144102718444208017947796823094333540796017555420852955421135484464237400787535579513133021475369548432688477651773809521848207967884443722885111479830853985900478936457869925960713 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 13 = 4809902274558872056045049197681564156802610939720159312293272029209154628679260148092383081390916068475975499027816117923843989260182360641738946186985615939206802907686040936784040750373780578615981543817144984 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 4809902274558872056045049197681564156802610939720159312293272029209154628679260148092383081390916068475975499027816117923843989260182360641738946186985615939206802907686040936784040750373780578615981543817144984 = ((34458651051096217691009996219889635528695073296320560468514006803577746133406268106954765119662707267802660516285415762759413763044595294127596383614970272926729956307927173364329682775563899495220450089247256110 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 73 = 856557939305004612720351226984388137512793728991261247394692279174233016066169615413712055590163135482023034073446705931643450142224256004693236992202917906982033394519431947646473010340536267424763836570176504 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 856557939305004612720351226984388137512793728991261247394692279174233016066169615413712055590163135482023034073446705931643450142224256004693236992202917906982033394519431947646473010340536267424763836570176504 = ((20583328109366432141932719989905292139421023375601569324614540957479511933393618757836268433131302947682641436026381402120555708944970748580314615515218103060453761562332293776678067532673767771087064925018275844 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 149 = 419655903149431790124735836039331100929086860512497121206795546172610806529062965940946174886455764363675714680279258610805180271022622069413465103562503404091868710066567330054983421173551325651058792413576408 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 419655903149431790124735836039331100929086860512497121206795546172610806529062965940946174886455764363675714680279258610805180271022622069413465103562503404091868710066567330054983421173551325651058792413576408 = ((54530136964814833033978550593614049754039802084594959713705757640052157930170905554613068850859581969733933681022223121981583983472286772728900341792835919139556651379221960591352912114885209960694133862114766568 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 223 = 280397890445136039141639639326727955329300189311040677398262494976318431268297676794623228960008560045684670346913047233228573364943366315437696414487950704976181335425643642054675021322238329695102063092479304 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 280397890445136039141639639326727955329300189311040677398262494976318431268297676794623228960008560045684670346913047233228573364943366315437696414487950704976181335425643642054675021322238329695102063092479304 = ((870997420821645996450176192295491311314912958182559453862607693941507229031888076007151833696878199483394473269448838418110244358911414403631420795735003173184694880540250780153620781902321 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 9769 = 6400729815668475455889614041341010752219668565499239539340007818581125004896139003500970422569547434761764918350047039923223652408882248781104135574860580121782008168688558929081024644780340620535137687544568 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 6400729815668475455889614041341010752219668565499239539340007818581125004896139003500970422569547434761764918350047039923223652408882248781104135574860580121782008168688558929081024644780340620535137687544568 = ((5411450450207703896795214496655046633122704803563390977686188292254154974695960236090053144978400003815322975164220827170294762421821398314097669838957865036669437349287492759130356894277233345133530883008697396 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 18427 = 3393321190061612673174452681926538993782707017765348187974848666615239060771171754772940796552987946501746431180420553156236601746479116966549427493938948673668445096864304128626066628038158545721374074435496 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 3393321190061612673174452681926538993782707017765348187974848666615239060771171754772940796552987946501746431180420553156236601746479116966549427493938948673668445096864304128626066628038158545721374074435496 = ((25557778294979512214026277270407067663715341070888283051957354830077521243121935058052325103251085280039207530538239600477215627872649600852267632720689177857710465841113281471285516975856151425256524107810657020 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 107671 = 580738820752712770649345130720995755945741585165569847589532338138579656293991714809010597636150020805859344552958638194221023863272103800861943331359539775888479142943954566951105959402802495769592184242952 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 580738820752712770649345130720995755945741585165569847589532338138579656293991714809010597636150020805859344552958638194221023863272103800861943331359539775888479142943954566951105959402802495769592184242952 = ((40101196879589020332532173315139615425662493292509701177401870108430103558721951769990312230900838472681866166874459064260155887837121347086049008272376278403594525578527067546392165813607618521416542197259875323 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 953861 = 65553292952815280977611664141693951255407173808722729055714130653962170769986803030211928213945122916428789401560195388017721513283770579091299781027647641752507375602858836012996159560836586800391000438872 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 65553292952815280977611664141693951255407173808722729055714130653962170769986803030211928213945122916428789401560195388017721513283770579091299781027647641752507375602858836012996159560836586800391000438872 = ((19091562946228432402907772725931079670987884191321825716015514553844207643903660272377247939431228663699415671896121522119041092649349474557136064329520467256026852529667214516588400375892873825153574503726239705 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 13097927 = 4773940912120317721161954832231110620667983736385312810173131700895799020167877094230329735238401381393229744474954665193199798745432822181907587393853470645369182298841529058620690873819891309671199119496 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 4773940912120317721161954832231110620667983736385312810173131700895799020167877094230329735238401381393229744474954665193199798745432822181907587393853470645369182298841529058620690873819891309671199119496 = ((37707873940609543600587385853571443961579092236110834269316919557849822376643357750534614460819339737086399969257167931405690360707714970922069242295714367908723988132086306425755641948214574192173066757740788764 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 18702169 = 3343394531899767172919121817895043833602078037919669694986316099470548585719142091230219342905195054658509474882919170124597412224345245107271049707165677265010728851820263851652315287860950648131121051768 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 3343394531899767172919121817895043833602078037919669694986316099470548585719142091230219342905195054658509474882919170124597412224345245107271049707165677265010728851820263851652315287860950648131121051768 = ((43842518041005600806599050652561507489659121642316630940865920756389306185514569665876154487536529027280207981849542509402329700488935129518665551888869408457859982144545939816957265686858398560271700575299312582 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 25709599 = 2432116096764688423517832369530941888219802347611958905302744565549972606450624995170130038126300954370687830928891949384740378890482527103694083304481450963497658512679195508968946958482672075982505992008 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 2432116096764688423517832369530941888219802347611958905302744565549972606450624995170130038126300954370687830928891949384740378890482527103694083304481450963497658512679195508968946958482672075982505992008 = ((41491918400165117362035935765513224330162746793535285696906570652851766468252247963290772676532583457915633811641095736155696541573452026655463002276502952580440702310142364491161235086977275964723623621145019845 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_56737873).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 56737873 = 1102063335530137633615303830121730753608510178313559111738512587169402881437419797622674012790044295283816534457708866404103161575732151403395159004829331674271406645785232946222579224195788014859276802104 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 1102063335530137633615303830121730753608510178313559111738512587169402881437419797622674012790044295283816534457708866404103161575732151403395159004829331674271406645785232946222579224195788014859276802104 = ((21258935843553419372085637324681695723236127335541379987681584420198710279250562569604162556966296721749157393621114594441141639491662978497856112814639755167460051676419698505202043770626084255291620108620214293 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_78539161).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 78539161 = 796147154783908841712552029551987880777513554242858171859163817394471659467184554278609877919142895990290518730670035207149359036091188806340906804833489464060972561190442716572851214375197457507952753272 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 796147154783908841712552029551987880777513554242858171859163817394471659467184554278609877919142895990290518730670035207149359036091188806340906804833489464060972561190442716572851214375197457507952753272 = ((44418120572615375452467653544084457418303869085902214128127304144713644707122291478670659380462190790447772841068483883735770860310895077411419060254430802220991332620168390577911823143181776399180917907671594225 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_119779213).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 119779213 = 522033231001988105637208015132478237592310296915726696750065776268867371610050417723156855756615372737402119075215576287097260026097939784782241810445131303456539139223752723923745681605531566833785759384 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 522033231001988105637208015132478237592310296915726696750065776268867371610050417723156855756615372737402119075215576287097260026097939784782241810445131303456539139223752723923745681605531566833785759384 = ((37795137582596039648390923208109735286208563922441817034186679201537737086314897182894296926211667132330558471252175030371855095449852256742994751738181998271090659422096990074015886138821558824682130061741984791 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_17189128703).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 17189128703 = 3637690464110159657845552148104148966789776570582820835361135778431608510647520859696537002424811554463097761550433690589486992939549618330797502577220246159308103808775032369841260927049511517175342664 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 3637690464110159657845552148104148966789776570582820835361135778431608510647520859696537002424811554463097761550433690589486992939549618330797502577220246159308103808775032369841260927049511517175342664 = ((45628860743434909992096123184224079853539222099418866344443251799348394374858754925489405406988789711833307076321166384449569721253986536081013450852601712839349992287148355579698972548181645336101497646964269391 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4010575301861137).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 4010575301861137 = 15590962608344099499286281262455578976031481899279578900371983726079746588182872566763694265456885259343728174469732885843558804748572401856976106683728408476622842322138204283882962788048403381816 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 15590962608344099499286281262455578976031481899279578900371983726079746588182872566763694265456885259343728174469732885843558804748572401856976106683728408476622842322138204283882962788048403381816 = ((4106717569931544662901504478112137539096874657774147108179550524933810427814437383478977877967091118325432255573746817853127322980510695736572551370926637785123810779139787792452992804163312181571870655970117794 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_64326272436179833).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 64326272436179833 = 972055852160594313105925412537012502256989533965162057769185228144722032307400404642421480558022743565437375086610190868421199215404353619432575095192316561244909346417272578111901593155133493624 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 972055852160594313105925412537012502256989533965162057769185228144722032307400404642421480558022743565437375086610190868421199215404353619432575095192316561244909346417272578111901593155133493624 = ((18169931212674203902374637910220457265184754880671121702544636670687845589033711161271833522667819615881631192352086728547137915859034334420909853756000577925259225768413117379934344637468640547724084856518841493 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_6962353413269964253).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 6962353413269964253 = 8980976094963537040704077115832101363884604991142911190104300547668444202171898494301478876030159572226374693078901414580464068426701739697575285958779100721953720375082679727301348686799274264 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 8980976094963537040704077115832101363884604991142911190104300547668444202171898494301478876030159572226374693078901414580464068426701739697575285958779100721953720375082679727301348686799274264 = ((53201130162104898135152157007800234699779862649191440567757158660254850349592602815388452652320396966336745611537577879029097974460722326853000977298247841636279784661028081796591870505514647969608279276598182821 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_142659759801404920771391593).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 142659759801404920771391593 = 438306707205387784000688728697925548776091946896282094370876997010764819106774345517658573020012476758574699958941802724605745004719724665099355709918843508758843093395215876427027997944 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 438306707205387784000688728697925548776091946896282094370876997010764819106774345517658573020012476758574699958941802724605745004719724665099355709918843508758843093395215876427027997944 = ((47105113058486729268489963174886953898550526976522326531269523973107296393833059397113035310892628465292665398026954618608748844639726960677988646799295154252576341867632408071896742359749466119908517881285544351 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_14373616515152387435471235475346778247660988205097).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 - 1) / 14373616515152387435471235475346778247660988205097 = 4350243343653197102272247197487935852374728353772318044177627195540738986573801978818107954066814746601477995376643659215065445670254110383153387927101891107762936 from by norm_num]
      have h2 : (5 : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) ^ 4350243343653197102272247197487935852374728353772318044177627195540738986573801978818107954066814746601477995376643659215065445670254110383153387927101891107762936 = ((23633880611943316593229346402098122840943514647516778309629900557747983024550979472985831464080347818614227965304627084557428153012855278623977846822694073818753173383986895519846185123521995310217073445432290063 : ℕ) : ZMod 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8638915776957163 : Nat.Prime 8638915776957163 := by
  refine lucas_primality 8638915776957163 (5 : ZMod 8638915776957163) ?_ (fun q hq hd => ?_)
  · rw [show 8638915776957163 - 1 = 8638915776957162 from by norm_num]
    reduce_mod_char
  · have e : 8638915776957163 - 1 = [2 ^ 1, 3 ^ 5, 4146139 ^ 1, 4287253 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8638915776957163 - 1) / 2 = 4319457888478581 from by norm_num]
      have h2 : (5 : ZMod 8638915776957163) ^ 4319457888478581 = ((8638915776957162 : ℕ) : ZMod 8638915776957163) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8638915776957163 - 1) / 3 = 2879638592319054 from by norm_num]
      have h2 : (5 : ZMod 8638915776957163) ^ 2879638592319054 = ((8132882634601378 : ℕ) : ZMod 8638915776957163) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8638915776957163 - 1) / 4146139 = 2083604958 from by norm_num]
      have h2 : (5 : ZMod 8638915776957163) ^ 2083604958 = ((7092080949899093 : ℕ) : ZMod 8638915776957163) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8638915776957163 - 1) / 4287253 = 2015023554 from by norm_num]
      have h2 : (5 : ZMod 8638915776957163) ^ 2015023554 = ((1751377022937026 : ℕ) : ZMod 8638915776957163) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_116004991998176173 : Nat.Prime 116004991998176173 := by
  refine lucas_primality 116004991998176173 (2 : ZMod 116004991998176173) ?_ (fun q hq hd => ?_)
  · rw [show 116004991998176173 - 1 = 116004991998176172 from by norm_num]
    reduce_mod_char
  · have e : 116004991998176173 - 1 = [2 ^ 2, 3 ^ 5, 151 ^ 1, 821 ^ 1, 2707 ^ 1, 355633 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116004991998176173 - 1) / 2 = 58002495999088086 from by norm_num]
      have h2 : (2 : ZMod 116004991998176173) ^ 58002495999088086 = ((116004991998176172 : ℕ) : ZMod 116004991998176173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116004991998176173 - 1) / 3 = 38668330666058724 from by norm_num]
      have h2 : (2 : ZMod 116004991998176173) ^ 38668330666058724 = ((47428889743468082 : ℕ) : ZMod 116004991998176173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116004991998176173 - 1) / 151 = 768244980120372 from by norm_num]
      have h2 : (2 : ZMod 116004991998176173) ^ 768244980120372 = ((21018532568491559 : ℕ) : ZMod 116004991998176173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116004991998176173 - 1) / 821 = 141297188791932 from by norm_num]
      have h2 : (2 : ZMod 116004991998176173) ^ 141297188791932 = ((47544385190767068 : ℕ) : ZMod 116004991998176173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116004991998176173 - 1) / 2707 = 42853709640996 from by norm_num]
      have h2 : (2 : ZMod 116004991998176173) ^ 42853709640996 = ((85891178393441720 : ℕ) : ZMod 116004991998176173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116004991998176173 - 1) / 355633 = 326192991084 from by norm_num]
      have h2 : (2 : ZMod 116004991998176173) ^ 326192991084 = ((56577926465202980 : ℕ) : ZMod 116004991998176173) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_111624850481 : Nat.Prime 111624850481 := by
  refine lucas_primality 111624850481 (3 : ZMod 111624850481) ?_ (fun q hq hd => ?_)
  · rw [show 111624850481 - 1 = 111624850480 from by norm_num]
    reduce_mod_char
  · have e : 111624850481 - 1 = [2 ^ 4, 5 ^ 1, 11 ^ 1, 13 ^ 1, 1489 ^ 1, 6553 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111624850481 - 1) / 2 = 55812425240 from by norm_num]
      have h2 : (3 : ZMod 111624850481) ^ 55812425240 = ((111624850480 : ℕ) : ZMod 111624850481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111624850481 - 1) / 5 = 22324970096 from by norm_num]
      have h2 : (3 : ZMod 111624850481) ^ 22324970096 = ((99432161086 : ℕ) : ZMod 111624850481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111624850481 - 1) / 11 = 10147713680 from by norm_num]
      have h2 : (3 : ZMod 111624850481) ^ 10147713680 = ((68550060970 : ℕ) : ZMod 111624850481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111624850481 - 1) / 13 = 8586526960 from by norm_num]
      have h2 : (3 : ZMod 111624850481) ^ 8586526960 = ((4873384270 : ℕ) : ZMod 111624850481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111624850481 - 1) / 1489 = 74966320 from by norm_num]
      have h2 : (3 : ZMod 111624850481) ^ 74966320 = ((69223883056 : ℕ) : ZMod 111624850481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (111624850481 - 1) / 6553 = 17034160 from by norm_num]
      have h2 : (3 : ZMod 111624850481) ^ 17034160 = ((73232144022 : ℕ) : ZMod 111624850481) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4312536798453050201 : Nat.Prime 4312536798453050201 := by
  refine lucas_primality 4312536798453050201 (15 : ZMod 4312536798453050201) ?_ (fun q hq hd => ?_)
  · rw [show 4312536798453050201 - 1 = 4312536798453050200 from by norm_num]
    reduce_mod_char
  · have e : 4312536798453050201 - 1 = [2 ^ 3, 5 ^ 2, 11 ^ 1, 17 ^ 1, 1033 ^ 1, 111624850481 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4312536798453050201 - 1) / 2 = 2156268399226525100 from by norm_num]
      have h2 : (15 : ZMod 4312536798453050201) ^ 2156268399226525100 = ((4312536798453050200 : ℕ) : ZMod 4312536798453050201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4312536798453050201 - 1) / 5 = 862507359690610040 from by norm_num]
      have h2 : (15 : ZMod 4312536798453050201) ^ 862507359690610040 = ((2311266092695418527 : ℕ) : ZMod 4312536798453050201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4312536798453050201 - 1) / 11 = 392048799859368200 from by norm_num]
      have h2 : (15 : ZMod 4312536798453050201) ^ 392048799859368200 = ((1458178411268115968 : ℕ) : ZMod 4312536798453050201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4312536798453050201 - 1) / 17 = 253678635203120600 from by norm_num]
      have h2 : (15 : ZMod 4312536798453050201) ^ 253678635203120600 = ((1542506643207862217 : ℕ) : ZMod 4312536798453050201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4312536798453050201 - 1) / 1033 = 4174769407989400 from by norm_num]
      have h2 : (15 : ZMod 4312536798453050201) ^ 4174769407989400 = ((2984415873271435406 : ℕ) : ZMod 4312536798453050201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_111624850481).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4312536798453050201 - 1) / 111624850481 = 38634200 from by norm_num]
      have h2 : (15 : ZMod 4312536798453050201) ^ 38634200 = ((3407159602202014834 : ℕ) : ZMod 4312536798453050201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_21835473162448454819220238921 : Nat.Prime 21835473162448454819220238921 := by
  refine lucas_primality 21835473162448454819220238921 (13 : ZMod 21835473162448454819220238921) ?_ (fun q hq hd => ?_)
  · rw [show 21835473162448454819220238921 - 1 = 21835473162448454819220238920 from by norm_num]
    reduce_mod_char
  · have e : 21835473162448454819220238921 - 1 = [2 ^ 3, 3 ^ 9, 5 ^ 1, 59 ^ 1, 109 ^ 1, 4312536798453050201 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21835473162448454819220238921 - 1) / 2 = 10917736581224227409610119460 from by norm_num]
      have h2 : (13 : ZMod 21835473162448454819220238921) ^ 10917736581224227409610119460 = ((21835473162448454819220238920 : ℕ) : ZMod 21835473162448454819220238921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21835473162448454819220238921 - 1) / 3 = 7278491054149484939740079640 from by norm_num]
      have h2 : (13 : ZMod 21835473162448454819220238921) ^ 7278491054149484939740079640 = ((15157254259624545185307710953 : ℕ) : ZMod 21835473162448454819220238921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21835473162448454819220238921 - 1) / 5 = 4367094632489690963844047784 from by norm_num]
      have h2 : (13 : ZMod 21835473162448454819220238921) ^ 4367094632489690963844047784 = ((1600390078853308376487717155 : ℕ) : ZMod 21835473162448454819220238921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21835473162448454819220238921 - 1) / 59 = 370092765465228047783393880 from by norm_num]
      have h2 : (13 : ZMod 21835473162448454819220238921) ^ 370092765465228047783393880 = ((7468439663277191784921775046 : ℕ) : ZMod 21835473162448454819220238921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21835473162448454819220238921 - 1) / 109 = 200325441857325273570827880 from by norm_num]
      have h2 : (13 : ZMod 21835473162448454819220238921) ^ 200325441857325273570827880 = ((20102773711435674994826319591 : ℕ) : ZMod 21835473162448454819220238921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4312536798453050201).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (21835473162448454819220238921 - 1) / 4312536798453050201 = 5063254920 from by norm_num]
      have h2 : (13 : ZMod 21835473162448454819220238921) ^ 5063254920 = ((11313609451734315603713161691 : ℕ) : ZMod 21835473162448454819220238921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_466281331 : Nat.Prime 466281331 := by
  refine lucas_primality 466281331 (3 : ZMod 466281331) ?_ (fun q hq hd => ?_)
  · rw [show 466281331 - 1 = 466281330 from by norm_num]
    reduce_mod_char
  · have e : 466281331 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 773 ^ 1, 20107 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466281331 - 1) / 2 = 233140665 from by norm_num]
      have h2 : (3 : ZMod 466281331) ^ 233140665 = ((466281330 : ℕ) : ZMod 466281331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466281331 - 1) / 3 = 155427110 from by norm_num]
      have h2 : (3 : ZMod 466281331) ^ 155427110 = ((199148193 : ℕ) : ZMod 466281331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466281331 - 1) / 5 = 93256266 from by norm_num]
      have h2 : (3 : ZMod 466281331) ^ 93256266 = ((64809315 : ℕ) : ZMod 466281331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466281331 - 1) / 773 = 603210 from by norm_num]
      have h2 : (3 : ZMod 466281331) ^ 603210 = ((419080075 : ℕ) : ZMod 466281331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (466281331 - 1) / 20107 = 23190 from by norm_num]
      have h2 : (3 : ZMod 466281331) ^ 23190 = ((290026677 : ℕ) : ZMod 466281331) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1917965578550425574480498445259 : Nat.Prime 1917965578550425574480498445259 := by
  refine lucas_primality 1917965578550425574480498445259 (3 : ZMod 1917965578550425574480498445259) ?_ (fun q hq hd => ?_)
  · rw [show 1917965578550425574480498445259 - 1 = 1917965578550425574480498445258 from by norm_num]
    reduce_mod_char
  · have e : 1917965578550425574480498445259 - 1 = [2 ^ 1, 3 ^ 1, 211 ^ 1, 1087 ^ 1, 60589 ^ 1, 107183 ^ 1, 460267 ^ 1, 466281331 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1917965578550425574480498445259 - 1) / 2 = 958982789275212787240249222629 from by norm_num]
      have h2 : (3 : ZMod 1917965578550425574480498445259) ^ 958982789275212787240249222629 = ((1917965578550425574480498445258 : ℕ) : ZMod 1917965578550425574480498445259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1917965578550425574480498445259 - 1) / 3 = 639321859516808524826832815086 from by norm_num]
      have h2 : (3 : ZMod 1917965578550425574480498445259) ^ 639321859516808524826832815086 = ((1053597720436700855711155854815 : ℕ) : ZMod 1917965578550425574480498445259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1917965578550425574480498445259 - 1) / 211 = 9089884258532822627869660878 from by norm_num]
      have h2 : (3 : ZMod 1917965578550425574480498445259) ^ 9089884258532822627869660878 = ((679571254287655780146731218782 : ℕ) : ZMod 1917965578550425574480498445259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1917965578550425574480498445259 - 1) / 1087 = 1764457753956233279190890934 from by norm_num]
      have h2 : (3 : ZMod 1917965578550425574480498445259) ^ 1764457753956233279190890934 = ((533264993333829212918811372639 : ℕ) : ZMod 1917965578550425574480498445259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1917965578550425574480498445259 - 1) / 60589 = 31655343025143599902300722 from by norm_num]
      have h2 : (3 : ZMod 1917965578550425574480498445259) ^ 31655343025143599902300722 = ((381175222330327691087799270099 : ℕ) : ZMod 1917965578550425574480498445259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1917965578550425574480498445259 - 1) / 107183 = 17894307665865161214749526 from by norm_num]
      have h2 : (3 : ZMod 1917965578550425574480498445259) ^ 17894307665865161214749526 = ((1228079911138932093894926550040 : ℕ) : ZMod 1917965578550425574480498445259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1917965578550425574480498445259 - 1) / 460267 = 4167071674811415057956574 from by norm_num]
      have h2 : (3 : ZMod 1917965578550425574480498445259) ^ 4167071674811415057956574 = ((948359554739757754773763357214 : ℕ) : ZMod 1917965578550425574480498445259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_466281331).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1917965578550425574480498445259 - 1) / 466281331 = 4113322689624100722318 from by norm_num]
      have h2 : (3 : ZMod 1917965578550425574480498445259) ^ 4113322689624100722318 = ((1574512985461799320251974760945 : ℕ) : ZMod 1917965578550425574480498445259) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_19149704835029612299033896988868835457 : Nat.Prime 19149704835029612299033896988868835457 := by
  refine lucas_primality 19149704835029612299033896988868835457 (5 : ZMod 19149704835029612299033896988868835457) ?_ (fun q hq hd => ?_)
  · rw [show 19149704835029612299033896988868835457 - 1 = 19149704835029612299033896988868835456 from by norm_num]
    reduce_mod_char
  · have e : 19149704835029612299033896988868835457 - 1 = [2 ^ 7, 3 ^ 6, 107 ^ 1, 1917965578550425574480498445259 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19149704835029612299033896988868835457 - 1) / 2 = 9574852417514806149516948494434417728 from by norm_num]
      have h2 : (5 : ZMod 19149704835029612299033896988868835457) ^ 9574852417514806149516948494434417728 = ((19149704835029612299033896988868835456 : ℕ) : ZMod 19149704835029612299033896988868835457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19149704835029612299033896988868835457 - 1) / 3 = 6383234945009870766344632329622945152 from by norm_num]
      have h2 : (5 : ZMod 19149704835029612299033896988868835457) ^ 6383234945009870766344632329622945152 = ((2983277037356687070469999875166677292 : ℕ) : ZMod 19149704835029612299033896988868835457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19149704835029612299033896988868835457 - 1) / 107 = 178969204065697311205924270924007808 from by norm_num]
      have h2 : (5 : ZMod 19149704835029612299033896988868835457) ^ 178969204065697311205924270924007808 = ((8610739699572568149878301402979663563 : ℕ) : ZMod 19149704835029612299033896988868835457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1917965578550425574480498445259).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19149704835029612299033896988868835457 - 1) / 1917965578550425574480498445259 = 9984384 from by norm_num]
      have h2 : (5 : ZMod 19149704835029612299033896988868835457) ^ 9984384 = ((12484939344572808987080884731074596527 : ℕ) : ZMod 19149704835029612299033896988868835457) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_12557612956332313 : Nat.Prime 12557612956332313 := by
  refine lucas_primality 12557612956332313 (10 : ZMod 12557612956332313) ?_ (fun q hq hd => ?_)
  · rw [show 12557612956332313 - 1 = 12557612956332312 from by norm_num]
    reduce_mod_char
  · have e : 12557612956332313 - 1 = [2 ^ 3, 3 ^ 5, 11 ^ 1, 53 ^ 1, 67 ^ 1, 3203 ^ 1, 51631 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12557612956332313 - 1) / 2 = 6278806478166156 from by norm_num]
      have h2 : (10 : ZMod 12557612956332313) ^ 6278806478166156 = ((12557612956332312 : ℕ) : ZMod 12557612956332313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12557612956332313 - 1) / 3 = 4185870985444104 from by norm_num]
      have h2 : (10 : ZMod 12557612956332313) ^ 4185870985444104 = ((7625597484987 : ℕ) : ZMod 12557612956332313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12557612956332313 - 1) / 11 = 1141601177848392 from by norm_num]
      have h2 : (10 : ZMod 12557612956332313) ^ 1141601177848392 = ((902781043392686 : ℕ) : ZMod 12557612956332313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12557612956332313 - 1) / 53 = 236936093515704 from by norm_num]
      have h2 : (10 : ZMod 12557612956332313) ^ 236936093515704 = ((11468421783645574 : ℕ) : ZMod 12557612956332313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12557612956332313 - 1) / 67 = 187427059049736 from by norm_num]
      have h2 : (10 : ZMod 12557612956332313) ^ 187427059049736 = ((7605102384463568 : ℕ) : ZMod 12557612956332313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12557612956332313 - 1) / 3203 = 3920578506504 from by norm_num]
      have h2 : (10 : ZMod 12557612956332313) ^ 3920578506504 = ((2892134066524604 : ℕ) : ZMod 12557612956332313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (12557612956332313 - 1) / 51631 = 243218472552 from by norm_num]
      have h2 : (10 : ZMod 12557612956332313) ^ 243218472552 = ((7593176653467995 : ℕ) : ZMod 12557612956332313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5879415781 : Nat.Prime 5879415781 := by
  refine lucas_primality 5879415781 (6 : ZMod 5879415781) ?_ (fun q hq hd => ?_)
  · rw [show 5879415781 - 1 = 5879415780 from by norm_num]
    reduce_mod_char
  · have e : 5879415781 - 1 = [2 ^ 2, 3 ^ 4, 5 ^ 1, 7 ^ 1, 518467 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5879415781 - 1) / 2 = 2939707890 from by norm_num]
      have h2 : (6 : ZMod 5879415781) ^ 2939707890 = ((5879415780 : ℕ) : ZMod 5879415781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5879415781 - 1) / 3 = 1959805260 from by norm_num]
      have h2 : (6 : ZMod 5879415781) ^ 1959805260 = ((5874632810 : ℕ) : ZMod 5879415781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5879415781 - 1) / 5 = 1175883156 from by norm_num]
      have h2 : (6 : ZMod 5879415781) ^ 1175883156 = ((623359436 : ℕ) : ZMod 5879415781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5879415781 - 1) / 7 = 839916540 from by norm_num]
      have h2 : (6 : ZMod 5879415781) ^ 839916540 = ((4819692320 : ℕ) : ZMod 5879415781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5879415781 - 1) / 518467 = 11340 from by norm_num]
      have h2 : (6 : ZMod 5879415781) ^ 11340 = ((2722756926 : ℕ) : ZMod 5879415781) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1319934691 : Nat.Prime 1319934691 := by
  refine lucas_primality 1319934691 (2 : ZMod 1319934691) ?_ (fun q hq hd => ?_)
  · rw [show 1319934691 - 1 = 1319934690 from by norm_num]
    reduce_mod_char
  · have e : 1319934691 - 1 = [2 ^ 1, 3 ^ 6, 5 ^ 1, 181061 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1319934691 - 1) / 2 = 659967345 from by norm_num]
      have h2 : (2 : ZMod 1319934691) ^ 659967345 = ((1319934690 : ℕ) : ZMod 1319934691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1319934691 - 1) / 3 = 439978230 from by norm_num]
      have h2 : (2 : ZMod 1319934691) ^ 439978230 = ((776221657 : ℕ) : ZMod 1319934691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1319934691 - 1) / 5 = 263986938 from by norm_num]
      have h2 : (2 : ZMod 1319934691) ^ 263986938 = ((530196592 : ℕ) : ZMod 1319934691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1319934691 - 1) / 181061 = 7290 from by norm_num]
      have h2 : (2 : ZMod 1319934691) ^ 7290 = ((721889612 : ℕ) : ZMod 1319934691) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_859270843 : Nat.Prime 859270843 := by
  refine lucas_primality 859270843 (2 : ZMod 859270843) ?_ (fun q hq hd => ?_)
  · rw [show 859270843 - 1 = 859270842 from by norm_num]
    reduce_mod_char
  · have e : 859270843 - 1 = [2 ^ 1, 3 ^ 6, 589349 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (859270843 - 1) / 2 = 429635421 from by norm_num]
      have h2 : (2 : ZMod 859270843) ^ 429635421 = ((859270842 : ℕ) : ZMod 859270843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (859270843 - 1) / 3 = 286423614 from by norm_num]
      have h2 : (2 : ZMod 859270843) ^ 286423614 = ((28016344 : ℕ) : ZMod 859270843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (859270843 - 1) / 589349 = 1458 from by norm_num]
      have h2 : (2 : ZMod 859270843) ^ 1458 = ((370779764 : ℕ) : ZMod 859270843) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 : Nat.Prime 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 := by
  refine lucas_primality 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ?_ (fun q hq hd => ?_)
  · rw [show 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1 = 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977346 from by norm_num]
    reduce_mod_char
  · have e : 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 13 ^ 1, 19 ^ 1, 37 ^ 1, 109 ^ 1, 163 ^ 1, 433 ^ 1, 487 ^ 1, 757 ^ 1, 1297 ^ 1, 3889 ^ 1, 8209 ^ 1, 19441 ^ 1, 19927 ^ 1, 59779 ^ 1, 70957 ^ 1, 208657 ^ 1, 224209 ^ 1, 572023 ^ 1, 1190701 ^ 1, 2051893 ^ 1, 5062663 ^ 1, 6627097 ^ 1, 859270843 ^ 1, 1319934691 ^ 1, 5879415781 ^ 1, 8638915776957163 ^ 1, 12557612956332313 ^ 1, 116004991998176173 ^ 1, 21835473162448454819220238921 ^ 1, 19149704835029612299033896988868835457 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 2 = 2850762658811133067325854538222753413049252333592504705786251894423259919067834394614399674891740003696567422546623539878121931026289298509695998781031355141023946468802717787591139219951494553642250532952713516860135021729453488673 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 2850762658811133067325854538222753413049252333592504705786251894423259919067834394614399674891740003696567422546623539878121931026289298509695998781031355141023946468802717787591139219951494553642250532952713516860135021729453488673 = ((5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977346 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 3 = 1900508439207422044883903025481835608699501555728336470524167929615506612711889596409599783261160002464378281697749026585414620684192865673130665854020903427349297645868478525060759479967663035761500355301809011240090014486302325782 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 1900508439207422044883903025481835608699501555728336470524167929615506612711889596409599783261160002464378281697749026585414620684192865673130665854020903427349297645868478525060759479967663035761500355301809011240090014486302325782 = ((130784463728941437304366605878791157545446108607097625128287829156986450640585159915213324860247524675186582838498440 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 7 = 814503616803180876378815582349358118014072095312144201653214826978074262590809827032685621397640001056162120727606725679463408864654085288484571080294672897435413276800776510740325491414712729612071580843632433388610006208415282478 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 814503616803180876378815582349358118014072095312144201653214826978074262590809827032685621397640001056162120727606725679463408864654085288484571080294672897435413276800776510740325491414712729612071580843632433388610006208415282478 = ((5133710509228230545171515630347476446765521665778211468925875618805780759045044657127038986868893015571626179998808861609586807068989048340489374843152963353953528255620138932833289260135149544667201369434152832420525789861085672535 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 13 = 438578870586328164203977621265038986622961897475769954736346445295886141395051445325292257675652308261010372699480544596634143234813738232260922889389439252465222533661956582706329110761768392868038543531186694901559234112223613642 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 438578870586328164203977621265038986622961897475769954736346445295886141395051445325292257675652308261010372699480544596634143234813738232260922889389439252465222533661956582706329110761768392868038543531186694901559234112223613642 = ((4604111511446440763022835581027410736134218825605500512404030541976486379057433122541037697256320652705940678125560353957516525637522168457447076675400278833655448127027574616788222670883110734541818642848876295778933629583799200137 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 19 = 300080279874856112350089951391868780320973929851842600609079146781395780954508883643621018409656842494375518162802477881907571686977820895757473555898037383265678575663443977641172549468578374067605319258180370195803686497837209334 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 300080279874856112350089951391868780320973929851842600609079146781395780954508883643621018409656842494375518162802477881907571686977820895757473555898037383265678575663443977641172549468578374067605319258180370195803686497837209334 = ((2334307620220935948970988761343892578195816433315089342305896322713217606446377569240144425536801270258782475834534586893109735451932920503904136008642429407371070016671334512657228044816635298734765626505554740323104372891017174749 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 37 = 154095278854655841477073218282310995299959585599594848961419021320176211841504561871048631075229189389003644461979650804222807082502124243767351285461154331947240349665011772302223741618999705602283812592038568478926217390781269658 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 154095278854655841477073218282310995299959585599594848961419021320176211841504561871048631075229189389003644461979650804222807082502124243767351285461154331947240349665011772302223741618999705602283812592038568478926217390781269658 = ((4560714472824657375529438495497824244838319960431223970765691803122255212050162078162792638402695057095879419872121683504658947961827563627894412505184514590190420934794003901835426770934212060152441950532610105576858010719592880426 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 109 = 52307571721305193895887239233445016753197290524633113867637649438958897597574943020447700456729174379753530688928872291341686807821821991003596307908832204422457733372526931882406224219293478048481661155095660859818991224393641994 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 52307571721305193895887239233445016753197290524633113867637649438958897597574943020447700456729174379753530688928872291341686807821821991003596307908832204422457733372526931882406224219293478048481661155095660859818991224393641994 = ((3534346507287173369617657468425608715365667697634774576178747996083886137900723694206141229018531191280300166515107468734575424952140628981967716486952274899934481945355478718140415665386605103919714820434286323993290364682265850868 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 163 = 34978682930197951746329503536475502000604323111564474917622722630960244405740299320422081900512147284620459172351209078259164797868580349812220843939035032405201797163223531136087597790815884093769945189603846832639693518152803542 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 34978682930197951746329503536475502000604323111564474917622722630960244405740299320422081900512147284620459172351209078259164797868580349812220843939035032405201797163223531136087597790815884093769945189603846832639693518152803542 = ((4438371450346815960565238356563716899948345970407345655535472218218341138403499048093743386376584805439366811615185191139072872726459463205801558397334756015995400327850259535049927045843317433688063130315312877997094786271075159960 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 433 = 13167494959866665437994709183476921076439964589341823121414558403802586231260205055955656696959538123309780242709577551400101298042906690575963042868505104577477812788927102944993714641808288931372981676455951579030646751637198562 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 13167494959866665437994709183476921076439964589341823121414558403802586231260205055955656696959538123309780242709577551400101298042906690575963042868505104577477812788927102944993714641808288931372981676455951579030646751637198562 = ((2735903137509770344224792674949277967412385109167085186319524033798155928646303714044103887612838373202550915744121818190253809136697269424408558109640046253588683574219278042941481883825607639698980531480859860642445276540014646898 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 487 = 11707444184029293910989135680586256316424034224199197970374751106461026361674884577471867248015359358096786129554922135023088012428292807021338804028876201811186638475575843070189483449492790774711501162023464134949219801763669358 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 11707444184029293910989135680586256316424034224199197970374751106461026361674884577471867248015359358096786129554922135023088012428292807021338804028876201811186638475575843070189483449492790774711501162023464134949219801763669358 = ((5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892768429173556377078199984935860052382096324676969832307622249759605720 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 757 = 7531737539791632938773724011156547986920085425607674255710044635200158306652138426986524900638679005803348540413800633759899421469720735824824303252394597466377665703573891116489139286529708199847425450337420123804848141953641978 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 7531737539791632938773724011156547986920085425607674255710044635200158306652138426986524900638679005803348540413800633759899421469720735824824303252394597466377665703573891116489139286529708199847425450337420123804848141953641978 = ((2705599632244161908522823521004653928768088898336045919389702263132660009806919186638206496695449621694355501073870076762021161940436379438665854019479134837872031930736266256301013432746345940166085320625811636482191856823140763652 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 1297 = 4395933167017938423015966905509257383267929581484201550942562674515435495864046869104702659817640715029402347797414864885307526640384423299454123023949660973051575125370420643933907817966838170612568285200791853292421004979882018 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 4395933167017938423015966905509257383267929581484201550942562674515435495864046869104702659817640715029402347797414864885307526640384423299454123023949660973051575125370420643933907817966838170612568285200791853292421004979882018 = ((4429978388139869936482969336412034467845377875401974007016446457930396039474053501152119617042913363654631407303513864348793678052086130272198086576160854000165354495128348839022925002768260255687626555470641877142984398100217824451 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 3889 = 1466064622685077432412370551927360973540371475233995734526228796309210552361961632612188055999866291435622228103174872655243986128202262026071483045014839362830520169093709327637510527102851403261635655928368998128122921948806114 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 1466064622685077432412370551927360973540371475233995734526228796309210552361961632612188055999866291435622228103174872655243986128202262026071483045014839362830520169093709327637510527102851403261635655928368998128122921948806114 = ((2364884236304829924691083140522045225457627842446502617851217029635128212878429310017667479637172430338301888187991701267747671008330621357309105716451240816324535476050122043550648343544559963794512897580033549265215542591253816822 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 8209 = 694545659352206862547412483426179416018821374976855818196187573254540119154058812185260001191799245632005706552959809934979152400119210259397246627124218574984516133220299132072393524168959569653368384200929106312616645566927394 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 694545659352206862547412483426179416018821374976855818196187573254540119154058812185260001191799245632005706552959809934979152400119210259397246627124218574984516133220299132072393524168959569653368384200929106312616645566927394 = ((1463215188209531315121200358915959195455911911303031430075668419163296891081981354387289348300821220732332570447368572892450532940298091041064675736837418514544067886829088127528543694004599927838222349316029649066306706115233337518 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 19441 = 293273253311160235309485575662029053345944378745178201305102813067564417372340352308461465448458413013380733763347928591957402502575927010924952294741150675482119898030216325044096416845995016063191248696333883736447201453572706 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 293273253311160235309485575662029053345944378745178201305102813067564417372340352308461465448458413013380733763347928591957402502575927010924952294741150675482119898030216325044096416845995016063191248696333883736447201453572706 = ((638216484967298960142507419601072185218524758653148940936190247935760826422523082158739363381243933511211206221978447556419802460725458286155497902142126092378946412999838888253264760324600476447959918658522110104344582015589262891 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 19927 = 286120606093354049011477346135670538771440992983640759350253615137578152162175379596968903988732875364738036086377632345874635522285271090449741434338470933007873384734552896832552739494303663736864609118554074056319066766643598 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 286120606093354049011477346135670538771440992983640759350253615137578152162175379596968903988732875364738036086377632345874635522285271090449741434338470933007873384734552896832552739494303663736864609118554074056319066766643598 = ((1666781744884973270955745490565647505515998203012799697923313535616877903663340774790275205729165979292241773587236168282991115985351320871554197877293944366864606372046423805172205270752966985317166919929383783887594027165461014922 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 59779 = 95376726235337930287420483387903893107922592669415838531465962777003961895241954352344457916383345445610245154540007021801031500235510748245905712073850520785692181829830468478600820353351329183902391574054886058988441483780374 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 95376726235337930287420483387903893107922592669415838531465962777003961895241954352344457916383345445610245154540007021801031500235510748245905712073850520785692181829830468478600820353351329183902391574054886058988441483780374 = ((4247428140717793008932531904572291099745663147693872641575785231392707118633538222070366889785365069637709151078633713832765275003628834094155012832610539492033895571088832484685999759970599230704902800691992182124330472104334844646 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 70957 = 80351837276410588591001720428506092789978503420170094727405383384958775570213915318133508318890032095397703469611836460902290993877680806959031491777593617008158362636602950733293099199557324961378032694525234067396733845271178 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 80351837276410588591001720428506092789978503420170094727405383384958775570213915318133508318890032095397703469611836460902290993877680806959031491777593617008158362636602950733293099199557324961378032694525234067396733845271178 = ((5251046927753388178005321065987516460272679811642886837136596089616003914754453258307790538666354485654639759466668975036152157823289576499037186579543529866453663413418857908299380371586455359331564207105497574501700707414370481543 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 208657 = 27324869607165185613958357862163775124239803443857667902694392178774351390730571172923982180245474666045878379796733777233660323174293683027130638138489052761459682338025733980562734247607265067956028630266068397994172462265378 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 27324869607165185613958357862163775124239803443857667902694392178774351390730571172923982180245474666045878379796733777233660323174293683027130638138489052761459682338025733980562734247607265067956028630266068397994172462265378 = ((1714236686983660384138575586420179081565053742578015573255438684485685428685461494126981166646071129690351736286517699360472547401173245234669761499760321437953149557581609316057895747749159059228500273415367356311725216504768371041 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 224209 = 25429511382782431279082057707074679544971453720345790809345315258738586935117095162231664874217716538556145583331833600596960256067234575861771818089651665553335918440407992431982116863743155302795610639650625236811501962271394 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 25429511382782431279082057707074679544971453720345790809345315258738586935117095162231664874217716538556145583331833600596960256067234575861771818089651665553335918440407992431982116863743155302795610639650625236811501962271394 = ((345558191903171920381710708930328595869863959067003175776569051842792473679658072598554373478094765936514544604519910637944066797571050138362500653926439240034316675731100838279376985637855281322608594226590675953699599030631434927 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 572023 = 9967300821159754301228637793315140870381968325023660607305132466433202577755909795985125335490845660739401816173907482314948633276246928916130990470772521877700534659629832323494472145181206188010798632057499495160631728897102 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 9967300821159754301228637793315140870381968325023660607305132466433202577755909795985125335490845660739401816173907482314948633276246928916130990470772521877700534659629832323494472145181206188010798632057499495160631728897102 = ((4065746840912570326981479177200480220832436833094815148943293571586612071181197050073541445021117494857782164100147026590932906979428655089139781409019657736058413059835402202894348737616423953993208622584706700328038875700235462244 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 1190701 = 4788377029684417947622206646711060817198024245536880721165518286157918602685030741746919965451847279369997039637362427474440570766782422303661454523060541884190819473239239385187615060290525587267081379712813740578256038635146 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 4788377029684417947622206646711060817198024245536880721165518286157918602685030741746919965451847279369997039637362427474440570766782422303661454523060541884190819473239239385187615060290525587267081379712813740578256038635146 = ((2979177918273378812512063114266456090646087224556691858480249784277850253274723604243638038135522208882690152260828949008587479788031001425922588560363990703606871477272034839607617933913751629433156853067396487983750762109881022805 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 2051893 = 2778666001405661082060180075883833526455085458737375395097358287613691278315033380994427755142924122940686890151312509841518959347577381968451570116990851999615912202831938885303609125769710753574626486812629622363480962924922 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 2778666001405661082060180075883833526455085458737375395097358287613691278315033380994427755142924122940686890151312509841518959347577381968451570116990851999615912202831938885303609125769710753574626486812629622363480962924922 = ((5687501532645392045504653683487183969602236196014412439421067599490659362303821992778567821467367646714536068915461329775197379035130793100877747287799974049905563758371504589304816834973680585365261385149432438626951574618581364556 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 5062663 = 1126190962665748467684242280484698828679393565636308285100648371982594898798452274865777032716473525374518281207587208501976896754253363697996883766915299375456729578406746721079850355416307407244863240137735226247583543178542 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 1126190962665748467684242280484698828679393565636308285100648371982594898798452274865777032716473525374518281207587208501976896754253363697996883766915299375456729578406746721079850355416307407244863240137735226247583543178542 = ((3954943009426952664034622484358801247271001400370072949602088634720643162642575571550469433053831350537640935495754752309770476520450103280305047904108428188676694355805476796726293876278220884094993466534760631777585127184803372573 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 6627097 = 860335274649256851778645925424889182412526128285885873041016871919412049972358755157620199279334527228609275689377578109426172885741463723768038639250747390908552106239796335436508389707135583994696481114645980543255975196818 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 860335274649256851778645925424889182412526128285885873041016871919412049972358755157620199279334527228609275689377578109426172885741463723768038639250747390908552106239796335436508389707135583994696481114645980543255975196818 = ((2233474662917806631195710427944945723063716922205532185938203586353946850051411751067063142474331542221246333239417964236953749951191398762434425360506147742655622571212711496102802465322007131063610409615355790777616694252365603663 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_859270843).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 859270843 = 6635306392704245563062482589608253268868922469867873093387975913022478569234623487892279558918397988040582036941345488847506329331575605457139894553669511956252765506213546192887960519222446265739871108259432740603616691622 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 6635306392704245563062482589608253268868922469867873093387975913022478569234623487892279558918397988040582036941345488847506329331575605457139894553669511956252765506213546192887960519222446265739871108259432740603616691622 = ((4075107415456804620228547663218019198322663048354795814277448609640675002061402486755502008702733628869520811216024354962867743603764916432001822698134763298812051538725066016703967924553776345230168885285187065992760259495297401365 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1319934691).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 1319934691 = 4319551078169416894772492252380316312254955853103651331770704849855726564986288999073515031800524142291169499304603912222081192388766905300916890260036896236139529525863060731678487598673917350115696796929952827279899141206 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 4319551078169416894772492252380316312254955853103651331770704849855726564986288999073515031800524142291169499304603912222081192388766905300916890260036896236139529525863060731678487598673917350115696796929952827279899141206 = ((109016630037685232650994696763004794899028923274439230864385173466386588291070466364037122022434684715789056221261899081978331150308386597485528826625764012769333207369163800778797011642240097991447078718996996234556131518777566948 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5879415781).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 5879415781 = 969743513640826847767327356575924873529284536099898836457625888875117784110949711591557084638079962896424869308498234912677944191914362761307830962884356397594921674345425167538815101857649877829672931904086923040537731866 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 969743513640826847767327356575924873529284536099898836457625888875117784110949711591557084638079962896424869308498234912677944191914362761307830962884356397594921674345425167538815101857649877829672931904086923040537731866 = ((5444116172754862594211009834920294795156935019450846858765236096255564181941752947335983040402622303045406302396327669950087270309566882255547908304309431123384286814475837264845963712736092472595202995417398190592568545441580857764 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8638915776957163).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 8638915776957163 = 659981583896223898301476821953863017586002134868288690462117543975662904227773704924407262453315481755373006501438657703879359146186485286663674812706479071395604877140453351279887589545574713380825318110115596265542 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 659981583896223898301476821953863017586002134868288690462117543975662904227773704924407262453315481755373006501438657703879359146186485286663674812706479071395604877140453351279887589545574713380825318110115596265542 = ((3399054789565463720303224420961001361033478345712040082243262883874045804757200743108465362236499672776091117006554783657039018035835475125075255416770189664408208637036100779643520118039698232262104370146451812012613586841741128050 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_12557612956332313).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 12557612956332313 = 454029387388246421666554089272428539167194581120257731149066924740722990091040110427709501510050886761685068832345307830441521036756588171366181217495990207131062014546062185860415435209815434031571188486635621815442 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 454029387388246421666554089272428539167194581120257731149066924740722990091040110427709501510050886761685068832345307830441521036756588171366181217495990207131062014546062185860415435209815434031571188486635621815442 = ((3682958632502561594127885715624526776390333122926701362999809745240537093632583214067710947100111974982284415644044049174627170576720671091276346095742893048294514061243507045541091388516825535412786813409174353642913510152535101415 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_116004991998176173).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 116004991998176173 = 49148965224806061315454178392911640163850134355684656316893923569452869166850796448852557459927253998755515529642339489822341965743015692805247421111193441316308676941256414900852019396909792841200393019755693125002 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 49148965224806061315454178392911640163850134355684656316893923569452869166850796448852557459927253998755515529642339489822341965743015692805247421111193441316308676941256414900852019396909792841200393019755693125002 = ((3485812638029635757288684749225627430340161755645609575783335287944815169700908879248792985772325999064023978244537489341985808229657948230305724709980155847977525484616190609378492162774506976276931944077604779856745430584912591451 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_21835473162448454819220238921).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 21835473162448454819220238921 = 261112973151754812588515949877894408557921062755015435559980103878177865983324015840250089680710058673497256263299455666065935159750531336321066302892859598139494471194312526931473711107080678634782757426 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 261112973151754812588515949877894408557921062755015435559980103878177865983324015840250089680710058673497256263299455666065935159750531336321066302892859598139494471194312526931473711107080678634782757426 = ((2867807611571230853519292025587726507373933326367231692879580960263465399956658064802700109346770470828213613213891349116744497039081753853778884902092641372570348536313457482238030138060126675249935281866379011647557734507005366663 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_19149704835029612299033896988868835457).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 - 1) / 19149704835029612299033896988868835457 = 297734370672531023135985842888479778577766253962666797687162139309432612579217667418803020372213320093657625571263306581480811933109944876645915191680450762804890442141146808368497620568391738178 from by norm_num]
      have h2 : (2 : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) ^ 297734370672531023135985842888479778577766253962666797687162139309432612579217667418803020372213320093657625571263306581480811933109944876645915191680450762804890442141146808368497620568391738178 = ((941291687204802764221462440142274449973258956664842060494475753092320695772958359114252913946865282879988330542451040129770403146303837472501280806160136802290757016285460961236623962596362684178840901547783778911125880716967863553 : ℕ) : ZMod 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_107779667 : Nat.Prime 107779667 := by
  refine lucas_primality 107779667 (2 : ZMod 107779667) ?_ (fun q hq hd => ?_)
  · rw [show 107779667 - 1 = 107779666 from by norm_num]
    reduce_mod_char
  · have e : 107779667 - 1 = [2 ^ 1, 19 ^ 1, 59 ^ 1, 48073 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107779667 - 1) / 2 = 53889833 from by norm_num]
      have h2 : (2 : ZMod 107779667) ^ 53889833 = ((107779666 : ℕ) : ZMod 107779667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107779667 - 1) / 19 = 5672614 from by norm_num]
      have h2 : (2 : ZMod 107779667) ^ 5672614 = ((71643806 : ℕ) : ZMod 107779667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107779667 - 1) / 59 = 1826774 from by norm_num]
      have h2 : (2 : ZMod 107779667) ^ 1826774 = ((35976522 : ℕ) : ZMod 107779667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107779667 - 1) / 48073 = 2242 from by norm_num]
      have h2 : (2 : ZMod 107779667) ^ 2242 = ((64634917 : ℕ) : ZMod 107779667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- Weight bound: a list L of distinct simple primes whose weight prod (p + 1)/p is at least 2 is
-- impossible, since the balance equation gives prod over P of (p + 1)/p = 2 (2^m/(2^m+1)) (3^e/(3^e+1)) < 2.
theorem weight_kill {m e : ℕ} {P : Finset ℕ} {L : List ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hL : L.Nodup) (hsub : ∀ x ∈ L, x ∈ P) (hw : 2 * L.prod ≤ (L.map (fun p => p + 1)).prod) :
    False := by
  have hF : L.toFinset ⊆ P := fun x hx => hsub x (List.mem_toFinset.mp hx)
  have hA : ∏ p ∈ L.toFinset, p = L.prod := by
    rw [List.prod_toFinset _ hL, List.map_id']
  have hB : ∏ p ∈ L.toFinset, (p + 1) = (L.map (fun p => p + 1)).prod := List.prod_toFinset _ hL
  have h1 := Finset.prod_sdiff hF (f := fun p => p + 1)
  have h2 := Finset.prod_sdiff hF (f := fun p => p)
  have hQ : ∏ p ∈ P \ L.toFinset, p ≤ ∏ p ∈ P \ L.toFinset, (p + 1) :=
    Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => Nat.le_succ i)
  have hpos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hP p hp).1.pos)
  rw [← h1] at E
  rw [← h2] at hpos E
  rw [hA] at hpos E
  rw [hB] at E
  have h3 : 2 ^ (m + 1) * 3 ^ e < 2 * ((2 ^ m + 1) * (1 + 3 ^ e)) := by
    rw [pow_succ]
    nlinarith [Nat.zero_le (2 ^ m), Nat.zero_le (3 ^ e)]
  have key : 2 ^ (m + 1) * 3 ^ e * ((∏ p ∈ P \ L.toFinset, p) * L.prod) <
      (2 ^ m + 1) * (1 + 3 ^ e) * ((∏ p ∈ P \ L.toFinset, (p + 1)) * (L.map (fun p => p + 1)).prod) :=
    calc 2 ^ (m + 1) * 3 ^ e * ((∏ p ∈ P \ L.toFinset, p) * L.prod)
        < 2 * ((2 ^ m + 1) * (1 + 3 ^ e)) * ((∏ p ∈ P \ L.toFinset, p) * L.prod) :=
          Nat.mul_lt_mul_of_pos_right h3 hpos
      _ = (2 ^ m + 1) * (1 + 3 ^ e) * ((∏ p ∈ P \ L.toFinset, p) * (2 * L.prod)) := by ring
      _ ≤ (2 ^ m + 1) * (1 + 3 ^ e) * ((∏ p ∈ P \ L.toFinset, (p + 1)) * (L.map (fun p => p + 1)).prod) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hw)
  omega

-- 3^359 + 1: the 46 forced simple primes listed below already have weight prod (p + 1)/p = 2.059974 >= 2
-- (chains from the kernel prime(s) of 3^359 + 1 through odd primes of p + 1).
set_option maxRecDepth 100000 in
theorem kill3_e359 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 359 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 : 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 ∈ P := S7 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 prime_483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 359 = 3 ^ 200 * 3 ^ 159 from pow_add 3 200 159]; norm_num : 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 ∣ 1 + 3 ^ 359).trans hd)
  have g125003 : 125003 ∈ P := S1 125003 (by norm_num) (by norm_num) (hnz (by norm_num)) 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 g483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 (by norm_num)
  have g105576905351265533 : 105576905351265533 ∈ P := S1 105576905351265533 prime_105576905351265533 (by norm_num) (hnz (by norm_num)) 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 g483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 (by norm_num)
  have g953926410728922630090961310952540448409869 : 953926410728922630090961310952540448409869 ∈ P := S1 953926410728922630090961310952540448409869 prime_953926410728922630090961310952540448409869 (by norm_num) (hnz (by norm_num)) 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 g483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 (by norm_num)
  have g28822863493563604394694586138432456377263959 : 28822863493563604394694586138432456377263959 ∈ P := S1 28822863493563604394694586138432456377263959 prime_28822863493563604394694586138432456377263959 (by norm_num) (hnz (by norm_num)) 483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 g483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267 (by norm_num)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 953926410728922630090961310952540448409869 g953926410728922630090961310952540448409869 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 125003 g125003 (by norm_num)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (hnz (by norm_num)) 105576905351265533 g105576905351265533 (by norm_num)
  have g947 : 947 ∈ P := S1 947 (by norm_num) (by norm_num) (hnz (by norm_num)) 125003 g125003 (by norm_num)
  have g321311 : 321311 ∈ P := S1 321311 (by norm_num) (by norm_num) (hnz (by norm_num)) 28822863493563604394694586138432456377263959 g28822863493563604394694586138432456377263959 (by norm_num)
  have g3994559398667 : 3994559398667 ∈ P := S1 3994559398667 prime_3994559398667 (by norm_num) (hnz (by norm_num)) 953926410728922630090961310952540448409869 g953926410728922630090961310952540448409869 (by norm_num)
  have g60467872480679 : 60467872480679 ∈ P := S1 60467872480679 prime_60467872480679 (by norm_num) (hnz (by norm_num)) 105576905351265533 g105576905351265533 (by norm_num)
  have g2170967411887213806804742451 : 2170967411887213806804742451 ∈ P := S1 2170967411887213806804742451 prime_2170967411887213806804742451 (by norm_num) (hnz (by norm_num)) 953926410728922630090961310952540448409869 g953926410728922630090961310952540448409869 (by norm_num)
  have g7 : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 97 g97 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 2170967411887213806804742451 g2170967411887213806804742451 (by norm_num)
  have g79 : 79 ∈ P := S1 79 (by norm_num) (by norm_num) (hnz (by norm_num)) 947 g947 (by norm_num)
  have g193 : 193 ∈ P := S1 193 (by norm_num) (by norm_num) (hnz (by norm_num)) 60467872480679 g60467872480679 (by norm_num)
  have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 2170967411887213806804742451 g2170967411887213806804742451 (by norm_num)
  have g431 : 431 ∈ P := S1 431 (by norm_num) (by norm_num) (hnz (by norm_num)) 2170967411887213806804742451 g2170967411887213806804742451 (by norm_num)
  have g2027 : 2027 ∈ P := S1 2027 (by norm_num) (by norm_num) (hnz (by norm_num)) 60467872480679 g60467872480679 (by norm_num)
  have g3347 : 3347 ∈ P := S1 3347 (by norm_num) (by norm_num) (hnz (by norm_num)) 321311 g321311 (by norm_num)
  have g101627 : 101627 ∈ P := S1 101627 (by norm_num) (by norm_num) (hnz (by norm_num)) 3994559398667 g3994559398667 (by norm_num)
  have g184007 : 184007 ∈ P := S1 184007 (by norm_num) (by norm_num) (hnz (by norm_num)) 60467872480679 g60467872480679 (by norm_num)
  have g3275507 : 3275507 ∈ P := S1 3275507 (by norm_num) (by norm_num) (hnz (by norm_num)) 3994559398667 g3994559398667 (by norm_num)
  have g2916963374916948341 : 2916963374916948341 ∈ P := S1 2916963374916948341 prime_2916963374916948341 (by norm_num) (hnz (by norm_num)) 2170967411887213806804742451 g2170967411887213806804742451 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 2027 g2027 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 184007 g184007 (by norm_num)
  have g31 : 31 ∈ P := S1 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 3347 g3347 (by norm_num)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 184007 g184007 (by norm_num)
  have g941 : 941 ∈ P := S1 941 (by norm_num) (by norm_num) (hnz (by norm_num)) 101627 g101627 (by norm_num)
  have g272959 : 272959 ∈ P := S1 272959 (by norm_num) (by norm_num) (hnz (by norm_num)) 3275507 g3275507 (by norm_num)
  have g425334757 : 425334757 ∈ P := S1 425334757 prime_425334757 (by norm_num) (hnz (by norm_num)) 2916963374916948341 g2916963374916948341 (by norm_num)
  have g1143006901 : 1143006901 ∈ P := S1 1143006901 prime_1143006901 (by norm_num) (hnz (by norm_num)) 2916963374916948341 g2916963374916948341 (by norm_num)
  have g37 : 37 ∈ P := S1 37 (by norm_num) (by norm_num) (hnz (by norm_num)) 425334757 g425334757 (by norm_num)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 425334757 g425334757 (by norm_num)
  have g157 : 157 ∈ P := S1 157 (by norm_num) (by norm_num) (hnz (by norm_num)) 941 g941 (by norm_num)
  have g853 : 853 ∈ P := S1 853 (by norm_num) (by norm_num) (hnz (by norm_num)) 272959 g272959 (by norm_num)
  have g133669 : 133669 ∈ P := S1 133669 (by norm_num) (by norm_num) (hnz (by norm_num)) 425334757 g425334757 (by norm_num)
  have g30079129 : 30079129 ∈ P := S1 30079129 (by norm_num) (by norm_num) (hnz (by norm_num)) 1143006901 g1143006901 (by norm_num)
  have g61 : 61 ∈ P := S1 61 (by norm_num) (by norm_num) (hnz (by norm_num)) 853 g853 (by norm_num)
  have g353 : 353 ∈ P := S1 353 (by norm_num) (by norm_num) (hnz (by norm_num)) 30079129 g30079129 (by norm_num)
  have g8521 : 8521 ∈ P := S1 8521 (by norm_num) (by norm_num) (hnz (by norm_num)) 30079129 g30079129 (by norm_num)
  have g13367 : 13367 ∈ P := S1 13367 (by norm_num) (by norm_num) (hnz (by norm_num)) 133669 g133669 (by norm_num)
  have g557 : 557 ∈ P := S1 557 (by norm_num) (by norm_num) (hnz (by norm_num)) 13367 g13367 (by norm_num)
  have g4261 : 4261 ∈ P := S1 4261 (by norm_num) (by norm_num) (hnz (by norm_num)) 8521 g8521 (by norm_num)
  have g2131 : 2131 ∈ P := S1 2131 (by norm_num) (by norm_num) (hnz (by norm_num)) 4261 g4261 (by norm_num)
  exact weight_kill hP E (L := [483582362941755355297745105751567688740563124861843169985633663074447365767179582892118869138575414961447138578231132794826527421704308142486522315823904802585429671683267, 125003, 105576905351265533, 953926410728922630090961310952540448409869, 28822863493563604394694586138432456377263959, 5, 11, 97, 947, 321311, 3994559398667, 60467872480679, 2170967411887213806804742451, 7, 59, 79, 193, 271, 431, 2027, 3347, 101627, 184007, 3275507, 2916963374916948341, 13, 17, 31, 41, 941, 272959, 425334757, 1143006901, 37, 43, 157, 853, 133669, 30079129, 61, 353, 8521, 13367, 557, 4261, 2131]) (by decide)
    (by intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    (by norm_num)

-- 3^362 + 1: 13^2 divides 337 + 1 (chain 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 -> 22620422017 -> 337).
theorem kill3_e362 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 362 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 : 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 ∈ P := S7 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 prime_684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 362 = 3 ^ 200 * 3 ^ 162 by rw [← pow_add]]; norm_num : 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 ∣ 1 + 3 ^ 362).trans hd)
  have g22620422017 : 22620422017 ∈ P := S1 22620422017 prime_22620422017 (by norm_num) (hnz (by norm_num)) 684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 g684426581616953550996265284798914332276822512957063624749673222499602867982563067889225088697 (by norm_num)
  have g337 : 337 ∈ P := S1 337 (by norm_num) (by norm_num) (hnz (by norm_num)) 22620422017 g22620422017 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 337 g337 (by norm_num)

-- 3^446 + 1: 5 divides 3^446 + 1 and 4139 + 1 (chain 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 -> 4139).
theorem kill3_e446 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 446 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 : 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 ∈ P := S7 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 prime_62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 446 = 3 ^ 200 * (3 ^ 200 * 3 ^ 46) by rw [← pow_add, ← pow_add]]; norm_num : 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 ∣ 1 + 3 ^ 446).trans hd)
  have g4139 : 4139 ∈ P := S1 4139 (by norm_num) (by norm_num) (hnz (by norm_num)) 62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 g62528729569265336728585639569860334038433942216362071059812536379719010172830381925200980058081908890187681487361609533009971860382370688342606300430813007209688437799918532178192529754859147522007760069622884793 (by norm_num)
  exact S8 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by rw [show (3:ℕ) ^ 446 = 3 ^ 200 * (3 ^ 200 * 3 ^ 46) by rw [← pow_add, ← pow_add]]; norm_num : 5 ∣ 1 + 3 ^ 446).trans hd) 4139 g4139 (by norm_num)

-- 3^487 + 1: 11 divides 242747 + 1 and 307 + 1 (chains 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 -> 107779667 -> 242747; 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 -> 107779667 -> 242747 -> 613 -> 307).
theorem kill3_e487 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 1 + 3 ^ 487 ∣ 1 + 3 ^ e) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 : 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 ∈ P := S7 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 prime_5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 (by norm_num) (hnz (by norm_num))
    ((by rw [show (3:ℕ) ^ 487 = 3 ^ 200 * (3 ^ 200 * 3 ^ 87) by rw [← pow_add, ← pow_add]]; norm_num : 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 ∣ 1 + 3 ^ 487).trans hd)
  have g107779667 : 107779667 ∈ P := S1 107779667 prime_107779667 (by norm_num) (hnz (by norm_num)) 5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 g5701525317622266134651709076445506826098504667185009411572503788846519838135668789228799349783480007393134845093247079756243862052578597019391997562062710282047892937605435575182278439902989107284501065905427033720270043458906977347 (by norm_num)
  have g242747 : 242747 ∈ P := S1 242747 (by norm_num) (by norm_num) (hnz (by norm_num)) 107779667 g107779667 (by norm_num)
  have g613 : 613 ∈ P := S1 613 (by norm_num) (by norm_num) (hnz (by norm_num)) 242747 g242747 (by norm_num)
  have g307 : 307 ∈ P := S1 307 (by norm_num) (by norm_num) (hnz (by norm_num)) 613 g613 (by norm_num)
  have := S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 242747 g242747 307 g307 (by norm_num) (by norm_num)
  omega

-- The balance equation of n, in the form used by the kill lemmas.
theorem kill_at {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hiff : ∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3)
    (k : ∀ (m : ℕ) (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p ≠ 2) →
      (2 ^ m + 1) * (1 + 3 ^ n.factorization 3) * ∏ p ∈ P, (p + 1) =
        2 ^ (m + 1) * 3 ^ n.factorization 3 * ∏ p ∈ P, p → False) : False := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he' =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he'⟩)
    omega
  have h3sq := (hiff 3).mpr rfl
  have he2 : 2 ≤ n.factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization hn0).mp h3sq.2.2
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  exact k _ _ hP E

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h hiff he hG => ?_⟩
  rcases he with he | he | he | he | he | he
  · exfalso
    exact (kill_at h hiff) (fun _ _ hP E => kill3_e359 hP E (by rw [he]))
  · exfalso
    exact (kill_at h hiff) (fun _ _ hP E => kill3_e362 hP E (by rw [he]))
  · exfalso
    exact (kill_at h hiff) (fun _ _ hP E => kill3_e446 hP E (by rw [he]))
  · exact (h1 n h hiff he hG).trans (le_max_left _ _)
  · exfalso
    exact (kill_at h hiff) (fun _ _ hP E => kill3_e487 hP E (by rw [he]))
  · exact (h2 n h hiff he hG).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H3_R1_H2_R1
