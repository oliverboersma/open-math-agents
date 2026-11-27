import OMAStatements.S_oeis_a297402
import Mathlib

-- Problem: oeis-a297402, the gcd of (q^n - 1)/2 over the first n odd primes q divides
-- (p^n - 1)/2 for every odd prime p.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- (1) No odd prime l divides the gcd g: if l is among the first n odd primes, l would divide
-- l^n - 1; otherwise l exceeds all of them, and 1 together with these n primes would be
-- n + 1 distinct roots of x^n = 1 in the field ZMod l.
-- (2) So g = 2^j with 2^(j+1) | 3^n - 1. For j = 0 use that p^n - 1 is even; for j >= 1,
-- n is even and lifting the exponent gives v2(p^n - 1) >= v2(n) + 2 = v2(3^n - 1).

namespace A297402

open OMA.S_oeis_a297402

lemma even_pow_sub_one (q n : ℕ) (hq : Odd q) : 2 ∣ q ^ n - 1 := by
  obtain ⟨c, hc⟩ := (hq.pow : Odd (q ^ n))
  exact ⟨c, by omega⟩

lemma no_odd_prime (n : ℕ) (hn : 0 < n) (l : ℕ) (hl : l.Prime) (hl2 : l ≠ 2)
    (hdiv : ∀ i < n, l ∣ term n (Nat.nth Nat.Prime (i + 1))) : False := by
  have hfact : Fact l.Prime := ⟨hl⟩
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hroot : ∀ i < n, ((Nat.nth Nat.Prime (i + 1) : ℕ) : ZMod l) ^ n = 1 := by
    intro i hi
    have h1 := hdiv i hi
    unfold term at h1
    obtain ⟨q, hq⟩ : ∃ q, q = Nat.nth Nat.Prime (i + 1) := ⟨_, rfl⟩
    rw [← hq] at h1 ⊢
    have hqp : q.Prime := by rw [hq]; exact Nat.prime_nth_prime (i + 1)
    have hq3 : 2 < q := by
      have h2 := hmono (Nat.succ_pos i)
      rw [Nat.nth_prime_zero_eq_two] at h2
      rw [hq]; exact h2
    have hqodd : Odd q := hqp.odd_of_ne_two (by omega)
    have hqpos : 1 ≤ q ^ n := Nat.one_le_pow _ _ hqp.pos
    have h2 : l ∣ q ^ n - 1 := h1.trans (Nat.div_dvd_of_dvd (even_pow_sub_one q n hqodd))
    have h3 : ((q ^ n - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h2
    rw [Nat.cast_sub hqpos] at h3
    push_cast at h3
    exact sub_eq_zero.mp h3
  have hidx : Nat.nth Nat.Prime (Nat.count Nat.Prime l) = l := Nat.nth_count hl
  obtain ⟨idx, hidxdef⟩ : ∃ idx, idx = Nat.count Nat.Prime l := ⟨_, rfl⟩
  rw [← hidxdef] at hidx
  have hidx0 : idx ≠ 0 := by
    intro h0
    rw [h0, Nat.nth_prime_zero_eq_two] at hidx
    exact hl2 hidx.symm
  rcases Nat.lt_or_ge n idx with hbig | hsmall
  · have hlt : ∀ i < n, Nat.nth Nat.Prime (i + 1) < l := by
      intro i hi
      rw [← hidx]
      exact hmono (by omega)
    obtain ⟨T, hT⟩ : ∃ T : Finset ℕ,
        T = insert 1 ((Finset.range n).image (fun i => Nat.nth Nat.Prime (i + 1))) := ⟨_, rfl⟩
    have hTmem : ∀ x ∈ T, x = 1 ∨ ∃ i < n, x = Nat.nth Nat.Prime (i + 1) := by
      intro x hx
      rw [hT] at hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact Or.inl h
      · obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp h
        exact Or.inr ⟨i, Finset.mem_range.mp hi, hix.symm⟩
    have hTcard : T.card = n + 1 := by
      rw [hT, Finset.card_insert_of_notMem, Finset.card_image_of_injective, Finset.card_range]
      · intro a b hab
        have h1 := hmono.injective hab
        omega
      · intro h1
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h1
        have h2 := (Nat.prime_nth_prime (i + 1)).one_lt
        omega
    have hTlt : ∀ x ∈ T, x < l := by
      intro x hx
      rcases hTmem x hx with h | ⟨i, hi, h⟩
      · rw [h]; exact hl.one_lt
      · rw [h]; exact hlt i hi
    have hTroot : ∀ x ∈ T, ((x : ℕ) : ZMod l) ^ n = 1 := by
      intro x hx
      rcases hTmem x hx with h | ⟨i, hi, h⟩
      · rw [h]; simp
      · rw [h]; exact hroot i hi
    have hinj : Set.InjOn (fun x : ℕ => (x : ZMod l)) (T : Set ℕ) := by
      intro a ha b hb hab
      have h1 := (ZMod.natCast_eq_natCast_iff' a b l).mp hab
      rw [Nat.mod_eq_of_lt (hTlt a ha), Nat.mod_eq_of_lt (hTlt b hb)] at h1
      exact h1
    have hsub : T.image (fun x : ℕ => (x : ZMod l)) ⊆
        Polynomial.nthRootsFinset n (1 : ZMod l) := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      rw [← hxy]
      exact (Polynomial.mem_nthRootsFinset hn 1).mpr (hTroot x hx)
    have hc1 : (T.image (fun x : ℕ => (x : ZMod l))).card = n + 1 := by
      rw [Finset.card_image_of_injOn hinj, hTcard]
    have hc2 : (Polynomial.nthRootsFinset n (1 : ZMod l)).card ≤ n := by
      unfold Polynomial.nthRootsFinset
      exact le_trans (@Multiset.toFinset_card_le _ (Classical.decEq _) _)
        (Polynomial.card_nthRoots n 1)
    have hc3 := Finset.card_le_card hsub
    omega
  · have h1 := hdiv (idx - 1) (by omega)
    rw [show idx - 1 + 1 = idx by omega, hidx] at h1
    unfold term at h1
    have hlodd : Odd l := hl.odd_of_ne_two hl2
    have h2 : l ∣ l ^ n - 1 := h1.trans (Nat.div_dvd_of_dvd (even_pow_sub_one l n hlodd))
    have h3 : l ∣ l ^ n := dvd_pow_self l hn.ne'
    have h4 : l ∣ 1 := by
      have h5 : l ^ n - (l ^ n - 1) = 1 := by
        have h6 : 1 ≤ l ^ n := Nat.one_le_pow _ _ hl.pos
        omega
      rw [← h5]
      exact Nat.dvd_sub h3 h2
    exact hl.one_lt.ne' (Nat.dvd_one.mp h4)

/-- The 2-adic comparison: a power of two dividing `3^n - 1` divides `p^n - 1`. -/
lemma two_part (n : ℕ) (hn : 0 < n) (p : ℕ) (hp : 1 < p) (hpodd : Odd p) (j : ℕ)
    (hj3 : 2 ^ (j + 1) ∣ 3 ^ n - 1) : 2 ^ (j + 1) ∣ p ^ n - 1 := by
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · rw [hj0]
    exact even_pow_sub_one p n hpodd
  · have h4 : 2 ^ 2 ∣ 3 ^ n - 1 := (pow_dvd_pow 2 (by omega : 2 ≤ j + 1)).trans hj3
    have hneven : Even n := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      obtain ⟨k, hk⟩ := hodd
      have h9 : 9 ^ k % 4 = 1 := by rw [Nat.pow_mod]; norm_num
      have h3 : 3 ^ n = 3 * 9 ^ k := by
        rw [hk, pow_succ, pow_mul]; norm_num; ring
      rw [h3] at h4
      omega
    have h2p : ¬ 2 ∣ p := fun h => (Nat.not_even_iff_odd.mpr hpodd) (even_iff_two_dvd.mpr h)
    have h3ne : 3 ^ n - 1 ≠ 0 := by
      have h5 : 1 < 3 ^ n := Nat.one_lt_pow hn.ne' (by norm_num)
      omega
    have hpne : p ^ n - 1 ≠ 0 := by
      have h5 : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp
      omega
    have hv3 := padicValNat.pow_two_sub_one (x := 3) (by norm_num) (by norm_num) hn.ne' hneven
    have e4 : padicValNat 2 (3 + 1) = 2 := by
      rw [show (3 + 1 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have e2 : padicValNat 2 (3 - 1) = 1 := by
      rw [show (3 - 1 : ℕ) = 2 by norm_num, padicValNat_self]
    rw [e4, e2] at hv3
    have hvp := padicValNat.pow_two_sub_one_ge hp h2p hn.ne' hneven
    have hle : j + 1 ≤ padicValNat 2 (3 ^ n - 1) := (padicValNat_dvd_iff_le h3ne).mp hj3
    exact (padicValNat_dvd_iff_le hpne).mpr (by omega)

end A297402

theorem OMA.solution : type_of% @OMA.S_oeis_a297402.main := by
  intro n hn p hp hp2
  obtain ⟨g, hg⟩ : ∃ g, g = OMA.S_oeis_a297402.initialGcd n := ⟨_, rfl⟩
  rw [← hg]
  have hgd : ∀ i < n, g ∣ OMA.S_oeis_a297402.term n (Nat.nth Nat.Prime (i + 1)) := by
    intro i hi
    rw [hg]
    unfold OMA.S_oeis_a297402.initialGcd
    exact Finset.gcd_dvd (Finset.mem_range.mpr hi)
  have hg3 : g ∣ (3 ^ n - 1) / 2 := by
    have h1 := hgd 0 hn
    rw [zero_add, Nat.nth_prime_one_eq_three] at h1
    exact h1
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd g with ⟨j, hj⟩ | ⟨l, hl, hlg, hlodd⟩
  · have h3even := A297402.even_pow_sub_one 3 n (by decide)
    have hj3 : 2 ^ (j + 1) ∣ 3 ^ n - 1 := by
      rw [hj] at hg3
      obtain ⟨c, hc⟩ := hg3
      obtain ⟨d, hd⟩ := h3even
      rw [hd, Nat.mul_div_cancel_left _ (by norm_num)] at hc
      exact ⟨c, by rw [hd, hc, pow_succ]; ring⟩
    obtain ⟨c, hc⟩ := A297402.two_part n hn p hp.one_lt hpodd j hj3
    rw [hj]
    unfold OMA.S_oeis_a297402.term
    refine ⟨c, ?_⟩
    rw [hc, pow_succ, show 2 ^ j * 2 * c = 2 * (2 ^ j * c) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  · exfalso
    have hl2 : l ≠ 2 := by
      intro h2
      rw [h2] at hlodd
      exact absurd hlodd (by decide)
    exact A297402.no_odd_prime n hn l hl hl2 (fun i hi => hlg.trans (hgd i hi))
