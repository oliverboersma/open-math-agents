import OMAStatements.S_oeis_a121451
import Mathlib

-- Problem: oeis-a121451, maximum product of the parts of a partition of n into parts
-- congruent to 2 modulo 3.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- Let G(n) be the claimed value. Then x <= G(x) for x = 2 mod 3 and G(a) G(b) <= G(a + b)
-- (the only strict case is odd + odd, where 25 <= 32). By induction over the multiset of
-- parts the product is at most G(n). The value is attained by s twos, or by one five and
-- t twos.

namespace A121451

/-- The claimed value. -/
def G (n : ℕ) : ℕ :=
  if n = 1 ∨ n = 3 then 0 else
    if n % 2 = 0 then 2 ^ (n / 2) else 5 * 2 ^ ((n - 5) / 2)

lemma G_even (s : ℕ) : G (2 * s) = 2 ^ s := by
  unfold G
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

lemma G_odd (t : ℕ) : G (2 * t + 5) = 5 * 2 ^ t := by
  unfold G
  rw [if_neg (by omega), if_neg (by omega)]
  congr 2
  omega

lemma G_one : G 1 = 0 := by simp [G]

lemma G_three : G 3 = 0 := by simp [G]

lemma cases4 (n : ℕ) : (∃ s, n = 2 * s) ∨ n = 1 ∨ n = 3 ∨ ∃ t, n = 2 * t + 5 := by
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · exact Or.inl ⟨k, hk⟩
  · rcases (by omega : k = 0 ∨ k = 1 ∨ 2 ≤ k) with h | h | h
    · right; left; omega
    · right; right; left; omega
    · right; right; right; exact ⟨k - 2, by omega⟩

lemma G_mul (a b : ℕ) : G a * G b ≤ G (a + b) := by
  rcases cases4 a with ⟨s, rfl⟩ | rfl | rfl | ⟨s, rfl⟩
  · rcases cases4 b with ⟨t, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
    · rw [G_even, G_even, show 2 * s + 2 * t = 2 * (s + t) by ring, G_even, pow_add]
    · rw [G_one, mul_zero]; exact Nat.zero_le _
    · rw [G_three, mul_zero]; exact Nat.zero_le _
    · rw [G_even, G_odd, show 2 * s + (2 * t + 5) = 2 * (s + t) + 5 by ring, G_odd, pow_add]
      exact le_of_eq (by ring)
  · rw [G_one, zero_mul]; exact Nat.zero_le _
  · rw [G_three, zero_mul]; exact Nat.zero_le _
  · rcases cases4 b with ⟨t, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
    · rw [G_odd, G_even, show 2 * s + 5 + 2 * t = 2 * (s + t) + 5 by ring, G_odd, pow_add]
      exact le_of_eq (by ring)
    · rw [G_one, mul_zero]; exact Nat.zero_le _
    · rw [G_three, mul_zero]; exact Nat.zero_le _
    · rw [G_odd, G_odd, show 2 * s + 5 + (2 * t + 5) = 2 * (s + t + 5) by ring, G_even]
      have h : 2 ^ (s + t + 5) = 32 * (2 ^ s * 2 ^ t) := by rw [pow_add, pow_add]; ring
      rw [h]
      calc 5 * 2 ^ s * (5 * 2 ^ t) = 25 * (2 ^ s * 2 ^ t) := by ring
        _ ≤ 32 * (2 ^ s * 2 ^ t) := Nat.mul_le_mul_right _ (by norm_num)

lemma le_G (x : ℕ) (hx : x % 3 = 2) : x ≤ G x := by
  rcases cases4 x with ⟨s, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
  · rw [G_even]
    obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
    have h := Nat.lt_two_pow_self (n := r)
    rw [pow_succ]
    omega
  · omega
  · omega
  · rw [G_odd]
    have h := Nat.lt_two_pow_self (n := t)
    omega

lemma prod_le (s : Multiset ℕ) (h : ∀ x ∈ s, x % 3 = 2) : s.prod ≤ G s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp [G]
  | cons x t ih =>
    rw [Multiset.prod_cons, Multiset.sum_cons]
    have hx := h x (Multiset.mem_cons_self x t)
    have ht := ih (fun y hy => h y (Multiset.mem_cons_of_mem hy))
    calc x * t.prod ≤ G x * G t.sum := Nat.mul_le_mul (le_G x hx) ht
      _ ≤ G (x + t.sum) := G_mul _ _

end A121451

theorem OMA.solution : type_of% @OMA.S_oeis_a121451.main := by
  intro n hn
  show OMA.S_oeis_a121451.a n = A121451.G n
  apply le_antisymm
  · unfold OMA.S_oeis_a121451.a
    apply Finset.sup_le
    intro P _
    split_ifs with h
    · have h1 := A121451.prod_le P.parts h
      rwa [P.parts_sum] at h1
    · exact Nat.zero_le _
  · rcases A121451.cases4 n with ⟨s, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
    · rw [A121451.G_even]
      unfold OMA.S_oeis_a121451.a
      have hall : ∀ x ∈ Multiset.replicate s 2, x % 3 = 2 := by
        intro x hx
        rw [Multiset.eq_of_mem_replicate hx]
      have hpos : ∀ {i : ℕ}, i ∈ Multiset.replicate s 2 → 0 < i := by
        intro i hi
        rw [Multiset.eq_of_mem_replicate hi]
        norm_num
      have hsum : (Multiset.replicate s 2).sum = 2 * s := by
        rw [Multiset.sum_replicate, smul_eq_mul, mul_comm]
      refine le_trans ?_ (Finset.le_sup (Finset.mem_univ
        (⟨Multiset.replicate s 2, hpos, hsum⟩ : (2 * s).Partition)))
      rw [if_pos hall, Multiset.prod_replicate]
    · rw [A121451.G_one]; exact Nat.zero_le _
    · rw [A121451.G_three]; exact Nat.zero_le _
    · rw [A121451.G_odd]
      unfold OMA.S_oeis_a121451.a
      have hall : ∀ x ∈ (5 ::ₘ Multiset.replicate t 2), x % 3 = 2 := by
        intro x hx
        rcases Multiset.mem_cons.mp hx with h | h
        · rw [h]
        · rw [Multiset.eq_of_mem_replicate h]
      have hpos : ∀ {i : ℕ}, i ∈ (5 ::ₘ Multiset.replicate t 2) → 0 < i := by
        intro i hi
        rcases Multiset.mem_cons.mp hi with h | h
        · rw [h]; norm_num
        · rw [Multiset.eq_of_mem_replicate h]; norm_num
      have hsum : (5 ::ₘ Multiset.replicate t 2).sum = 2 * t + 5 := by
        rw [Multiset.sum_cons, Multiset.sum_replicate, smul_eq_mul]
        ring
      refine le_trans ?_ (Finset.le_sup (Finset.mem_univ
        (⟨5 ::ₘ Multiset.replicate t 2, hpos, hsum⟩ : (2 * t + 5).Partition)))
      rw [if_pos hall, Multiset.prod_cons, Multiset.prod_replicate]
