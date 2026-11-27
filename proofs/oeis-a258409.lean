import OMAStatements.S_oeis_a258409

-- Problem: A258409, both conjectures (primes and consecutive divisors).
-- Credit: @bnb9001

namespace OMA_A258409_Proof

open OMA.S_oeis_a258409

lemma modeq_one (n : ℕ) (hn : n ≠ 0) : ∀ d, d ∣ n → d ≡ 1 [MOD gcdPrimes n] := by
  intro d
  induction d using Nat.recOnMul with
  | zero => intro h; exact absurd (Nat.eq_zero_of_zero_dvd h) hn
  | one => intro _; rfl
  | prime p hp =>
    intro h
    have : gcdPrimes n ∣ p - 1 := Finset.gcd_dvd (Nat.mem_primeFactors.2 ⟨hp, h, hn⟩)
    exact ((Nat.modEq_iff_dvd' hp.one_le).2 this).symm
  | mul x y ihx ihy =>
    intro h
    have := (ihx (dvd_of_mul_right_dvd h)).mul (ihy (dvd_of_mul_left_dvd h))
    simpa using this

theorem part1 (n : ℕ) (hn : 2 ≤ n) : a n = gcdPrimes n := by
  have hn0 : n ≠ 0 := by omega
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    intro p hp
    have hpd : p ∈ n.divisors := Nat.mem_divisors.2 ⟨Nat.dvd_of_mem_primeFactors hp, hn0⟩
    exact Finset.gcd_dvd hpd
  · apply Finset.dvd_gcd
    intro d hd
    have hdn := Nat.dvd_of_mem_divisors hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    exact (Nat.modEq_iff_dvd' hd1).1 (modeq_one n hn0 d hdn).symm

theorem part2 (n : ℕ) (hn : 2 ≤ n) : a n = gcdConsecutive n := by
  have hn0 : n ≠ 0 := by omega
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    intro p hp
    simp only [consecutiveDivisors, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨h1, h2⟩, hlt, -⟩ := hp
    have a1 : a n ∣ p.1 - 1 := Finset.gcd_dvd h1
    have a2 : a n ∣ p.2 - 1 := Finset.gcd_dvd h2
    have hp1 : 1 ≤ p.1 := Nat.pos_of_mem_divisors h1
    have e : p.2 - p.1 = (p.2 - 1) - (p.1 - 1) := by omega
    rw [e]
    exact Nat.dvd_sub a2 a1
  · apply Finset.dvd_gcd
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    rcases Nat.eq_or_lt_of_le hd1 with h | h
    · subst h; simp
    · have hne : (n.divisors.filter (· < d)).Nonempty :=
        ⟨1, Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨one_dvd n, hn0⟩, h⟩⟩
      set c := (n.divisors.filter (· < d)).max' hne with hc
      have hcmem := Finset.max'_mem _ hne
      rw [← hc, Finset.mem_filter] at hcmem
      obtain ⟨hcd, hclt⟩ := hcmem
      have hcons : (c, d) ∈ consecutiveDivisors n := by
        simp only [consecutiveDivisors, Finset.mem_filter, Finset.mem_product]
        refine ⟨⟨hcd, hd⟩, hclt, fun x hx ⟨hcx, hxd⟩ => ?_⟩
        have : x ≤ c := Finset.le_max' _ x (Finset.mem_filter.2 ⟨hx, hxd⟩)
        omega
      have h1 : gcdConsecutive n ∣ d - c := Finset.gcd_dvd hcons
      have h2 : gcdConsecutive n ∣ c - 1 := ih c hclt hcd
      have hc1 : 1 ≤ c := Nat.pos_of_mem_divisors hcd
      have e : d - 1 = (d - c) + (c - 1) := by omega
      rw [e]
      exact dvd_add h1 h2

end OMA_A258409_Proof

open OMA_A258409_Proof OMA.S_oeis_a258409 in
theorem OMA.solution : type_of% @OMA.S_oeis_a258409.main :=
  fun n hn => ⟨part1 n hn, part2 n hn⟩
