import OMAStatements.S_oeis_a265310
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Fixed points of A265310

Removing the proper divisors of n from 1,...,n-1 cancels their product
from both sides of the factorial divisibility test. For n > 1 the first
factorial occurs at n precisely if n does not divide the product of the
remaining numbers. Proper divisors never lie strictly above n/2.
Consequently, for a factorization n = ab with a,b ≥ 3 and a ≠ b, the
remaining numbers include the distinct factors n-a and n-b, whose
product is a multiple of n. For squares a² with a ≥ 5 use n-a and n-2a.
-/

namespace FactorialDivisors

open Finset OMA.S_oeis_a265310

private def outside (n : ℕ) : Finset ℕ := Ico 1 n \ n.properDivisors

private theorem mem_outside {x n : ℕ} :
    x ∈ outside n ↔ 0 < x ∧ x < n ∧ ¬ x ∣ n := by
  simp only [outside, mem_sdiff, mem_Ico, Nat.mem_properDivisors]
  omega

private theorem product_dvd_factorial (n : ℕ) : divisorProduct n ∣ n.factorial := by
  rw [divisorProduct, ← prod_Ico_id_eq_factorial]
  apply prod_dvd_prod_of_subset
  intro d hd
  exact mem_Ico.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.lt_succ_of_le (Nat.divisor_le hd)⟩

private theorem previous_factorial {n : ℕ} (hn : 0 < n) :
    divisorProduct n ∣ (n - 1).factorial ↔ n ∣ (outside n).prod id := by
  have hsub : n.properDivisors ⊆ Ico 1 n := filter_subset _ _
  have hfac : (outside n).prod id * n.properDivisors.prod id = (n - 1).factorial := by
    calc
      _ = (Ico 1 n).prod id := prod_sdiff hsub
      _ = (n - 1).factorial := by
        change (∏ i ∈ Ico 1 n, i) = (n - 1).factorial
        simpa only [Nat.sub_add_cancel hn] using prod_Ico_id_eq_factorial (n - 1)
  have hpos : 0 < n.properDivisors.prod id := prod_pos fun _ h => Nat.pos_of_mem_properDivisors h
  rw [divisorProduct, ← Nat.insert_self_properDivisors hn.ne', prod_insert Nat.self_notMem_properDivisors,
    ← hfac]
  exact Nat.mul_dvd_mul_iff_right hpos

private theorem least_iff {n : ℕ} (hn : 1 < n) :
    IsLeast {k : ℕ | 0 < k ∧ divisorProduct n ∣ k.factorial} n ↔ ¬ n ∣ (outside n).prod id := by
  rw [← previous_factorial (by omega : 0 < n)]
  constructor
  · intro h hd
    have := h.2 (show n - 1 ∈ {k : ℕ | 0 < k ∧ divisorProduct n ∣ k.factorial} from
      ⟨by omega, hd⟩)
    omega
  · intro h
    refine ⟨⟨by omega, product_dvd_factorial n⟩, ?_⟩
    intro k hk
    by_contra! hlt
    exact h (hk.2.trans (Nat.factorial_dvd_factorial (by omega)))

private theorem prime_obstruction {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : n ≤ 2 * p) :
    ¬ n ∣ (outside n).prod id := by
  intro h
  obtain ⟨x, hx, hpx⟩ := (hp.prime.dvd_finsetProd_iff id).mp (hpn.trans h)
  obtain ⟨hx0, hxn, hnd⟩ := mem_outside.mp hx
  change p ∣ x at hpx
  obtain ⟨j, rfl⟩ := hpx
  have hj : j < 2 := Nat.lt_of_mul_lt_mul_left (by omega : p * j < p * 2)
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp_all

private theorem upper_half {n c : ℕ} (hc : 0 < c) (hh : 2 * c < n) : n - c ∈ outside n := by
  refine mem_outside.mpr ⟨by omega, by omega, ?_⟩
  intro hd
  have hrest := Nat.dvd_sub hd (dvd_refl (n - c))
  rw [show n - (n - c) = c by omega] at hrest
  have := Nat.le_of_dvd hc hrest
  omega

private theorem two_witnesses {n a b u v : ℕ} (hab : n = a * b) (hau : a ∣ u) (hbv : b ∣ v)
    (hu : 0 < u) (hv : 0 < v) (hu' : 2 * u < n) (hv' : 2 * v < n) (hne : u ≠ v) :
    n ∣ (outside n).prod id := by
  have ha : a ∣ n := hab ▸ dvd_mul_right a b
  have hb : b ∣ n := hab ▸ dvd_mul_left b a
  have hpair : n ∣ (n - u) * (n - v) := by
    rw [hab] at *
    exact mul_dvd_mul (Nat.dvd_sub ha hau) (Nat.dvd_sub hb hbv)
  have hxy : n - u ≠ n - v := by omega
  have hsub : ({n - u, n - v} : Finset ℕ) ⊆ outside n := by
    exact insert_subset (upper_half hu hu') (singleton_subset_iff.mpr (upper_half hv hv'))
  apply hpair.trans
  simpa [hxy] using prod_dvd_prod_of_subset ({n - u, n - v} : Finset ℕ) (outside n) id hsub

private theorem large_product {n a b : ℕ} (hn : 16 < n) (hab : n = a * b)
    (ha : 3 ≤ a) (hb : 3 ≤ b) : n ∣ (outside n).prod id := by
  have hua : 2 * a < n := by nlinarith [Nat.mul_le_mul_left a hb]
  have hvb : 2 * b < n := by nlinarith [Nat.mul_le_mul_right b ha]
  by_cases hne : a = b
  · subst b
    have ha5 : 5 ≤ a := by
      by_contra! hlt
      nlinarith [Nat.mul_le_mul (by omega : a ≤ 4) (by omega : a ≤ 4)]
    exact two_witnesses hab (dvd_refl a) (dvd_mul_left a 2) (by omega) (by omega)
      hua (by nlinarith [Nat.mul_le_mul_left a ha5]) (by omega)
  · exact two_witnesses hab (dvd_refl a) (dvd_refl b) (by omega) (by omega) hua hvb hne

private theorem composite_pair {n : ℕ} (hn : 2 ≤ n) (hp : ¬ n.Prime) :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by
  obtain ⟨a, b, ha, hb, he⟩ := (Nat.not_prime_iff_exists_mul_eq hn).mp hp
  refine ⟨a, b, ?_, ?_, he.symm⟩
  · by_contra! ha'
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> simp_all
  · by_contra! hb'
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> simp_all

private theorem large_composite {n : ℕ} (hn : 16 < n) (hp : ¬n.Prime)
    (htwo : ¬∃ p : ℕ, p.Prime ∧ n = 2 * p) : n ∣ (outside n).prod id := by
  have double (t : ℕ) (ht : n = 2 * t) : n ∣ (outside n).prod id := by
    obtain ⟨c, d, hc, hd, he⟩ := composite_pair (by omega : 2 ≤ t) (fun hp => htwo ⟨t, hp, ht⟩)
    by_cases hc3 : 3 ≤ c
    · exact large_product hn (a := c) (b := 2 * d) (by nlinarith) hc3 (by omega)
    · obtain rfl : c = 2 := by omega
      exact large_product hn (a := 4) (b := d) (by omega) (by decide) (by omega)
  obtain ⟨a, b, ha, hb, hab⟩ := composite_pair (by omega) hp
  by_cases ha3 : 3 ≤ a
  · by_cases hb3 : 3 ≤ b
    · exact large_product hn hab ha3 hb3
    · obtain rfl : b = 2 := by omega
      exact double a (by simpa [Nat.mul_comm] using hab)
  · obtain rfl : a = 2 := by omega
    exact double b hab

theorem classify (n : ℕ) (hn : 0 < n) :
    IsLeast {k : ℕ | 0 < k ∧ divisorProduct n ∣ k.factorial} n ↔
    n.Prime ∨ (∃ p : ℕ, p.Prime ∧ n = 2 * p) ∨ n = 1 ∨ n = 8 ∨ n = 9 := by
  by_cases hone : n = 1
  · subst n
    exact ⟨fun _ => Or.inr (Or.inr (Or.inl rfl)),
      fun _ => ⟨⟨by decide, by decide⟩, fun _ h => h.1⟩⟩
  rw [least_iff (by omega : 1 < n)]
  constructor
  · intro h
    by_cases hp : n.Prime
    · exact Or.inl hp
    by_cases ht : ∃ p : ℕ, p.Prime ∧ n = 2 * p
    · exact Or.inr (Or.inl ht)
    by_cases hlarge : 16 < n
    · exact (h (large_composite hlarge hp ht)).elim
    · have small : ∀ t : Fin 17, 1 < t.val → ¬ t.val.Prime →
          ¬((t.val / 2).Prime ∧ t.val = 2 * (t.val / 2)) →
          ¬ t.val ∣ (outside t.val).prod id → t.val = 8 ∨ t.val = 9 := by decide
      exact Or.inr (Or.inr (Or.inr (small ⟨n, by omega⟩ (show 1 < n by omega) hp
        (fun h => ht ⟨_, h.1, h.2⟩) h)))
  · rintro (hp | ⟨p, hp, rfl⟩ | h1 | rfl | rfl)
    · exact prime_obstruction hp (dvd_refl _) (by omega)
    · exact prime_obstruction hp (dvd_mul_left p 2) le_rfl
    · contradiction
    · decide
    · decide

end FactorialDivisors

theorem OMA.solution : type_of% @OMA.S_oeis_a265310.main := FactorialDivisors.classify
