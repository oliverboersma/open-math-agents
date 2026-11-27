import OMAStatements.S_oeis_a000254
import Mathlib

-- Problem: A000254: Unsigned Stirling numbers of first kind, s(n+1,2): a(n+1) = (n+1)*a(n) + n!.
-- Upstream: formal-conjectures statements/oeis-a000254.lean:0 (declaration OMA.S_oeis_a000254.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Detlefs' four congruence observations for a(n) = n! H_n.

The recurrence a(n) = n a(n-1) + (n-1)! gives a(n) = (n-1)! modulo n, and a(n+1) = a(n) modulo n.
So a(n) is -1 modulo n for prime n (Wilson) and 0 modulo n for composite n other than 4
(a composite n other than 4 divides (n-1)!). The first, third and fourth statements follow by
reducing modulo n. For the second, with F = (n-1)!,
a(n+1)^2 - a(n)^2 = n (a(n) + F) ((n+2) a(n) + n F), and the cofactor is 4 modulo a prime n and
divisible by a composite n other than 4. The case n = 4 is a direct evaluation. -/

namespace A000254Aux

open OMA.S_oeis_a000254

theorem a_succ (m : ℕ) : a (m + 1) = (m + 1) * a m + m.factorial := rfl

theorem aux_lt {x y : ℕ} (hx : 2 ≤ x) (hxy : x < y) : x * y ∣ (x * y - 1).factorial := by
  obtain ⟨c, rfl⟩ : ∃ c, y = c + 1 := ⟨y - 1, by omega⟩
  have h1 : x ∣ c.factorial := Nat.dvd_factorial (by omega) (by omega)
  have h2 : x * (c + 1) ∣ (c + 1).factorial := by
    rw [Nat.factorial_succ, mul_comm x (c + 1)]
    exact mul_dvd_mul_left _ h1
  have h3 : c + 1 ≤ x * (c + 1) - 1 := by
    have : 2 * (c + 1) ≤ x * (c + 1) := Nat.mul_le_mul_right _ hx
    omega
  exact h2.trans (Nat.factorial_dvd_factorial h3)

theorem aux_sq {x : ℕ} (hx : 3 ≤ x) : x * x ∣ (x * x - 1).factorial := by
  have h1 : x ∣ (2 * x - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  have h2 : 2 * x * x ∣ (2 * x).factorial := by
    obtain ⟨c, hc⟩ : ∃ c, 2 * x = c + 1 := ⟨2 * x - 1, by omega⟩
    have hc' : 2 * x - 1 = c := by omega
    rw [hc'] at h1
    rw [hc, Nat.factorial_succ]
    exact mul_dvd_mul_left _ h1
  have h3 : 2 * x ≤ x * x - 1 := by
    have : 3 * x ≤ x * x := Nat.mul_le_mul_right _ hx
    omega
  have h4 : x * x ∣ 2 * x * x := ⟨2, by ring⟩
  exact h4.trans (h2.trans (Nat.factorial_dvd_factorial h3))

/-- A composite number other than 4 divides the factorial of its predecessor. -/
theorem dvd_factorial_of_not_prime {n : ℕ} (hn : 2 ≤ n) (h4 : n ≠ 4) (hp : ¬ n.Prime) :
    n ∣ (n - 1).factorial := by
  obtain ⟨x, hx, hx2, hxn⟩ := Nat.exists_dvd_of_not_prime2 hn hp
  obtain ⟨y, rfl⟩ := hx
  have hy2 : 2 ≤ y := by
    by_contra h
    have : y ≤ 1 := by omega
    have : x * y ≤ x * 1 := Nat.mul_le_mul_left _ this
    omega
  rcases lt_trichotomy x y with h | h | h
  · exact aux_lt hx2 h
  · subst h
    have hx3 : 3 ≤ x := by
      by_contra h3
      have : x = 2 := by omega
      subst this
      exact h4 rfl
    exact aux_sq hx3
  · rw [mul_comm]
    exact aux_lt hy2 h

theorem castA (n : ℕ) (hn : 1 ≤ n) :
    ((a n : ℕ) : ZMod n) = (((n - 1).factorial : ℕ) : ZMod n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h0 : ((m + 1 : ℕ) : ZMod (m + 1)) = 0 := ZMod.natCast_self (m + 1)
  rw [a_succ, Nat.cast_add, Nat.cast_mul, h0, zero_mul, zero_add, Nat.add_sub_cancel]

theorem castB (n : ℕ) (hn : 1 ≤ n) : ((a (n + 1) : ℕ) : ZMod n) = ((a n : ℕ) : ZMod n) := by
  have h0 : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
  have h1 : ((n.factorial : ℕ) : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_factorial hn le_rfl)
  rw [a_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_add, h0, h1, Nat.cast_one, zero_add, one_mul,
    add_zero]

theorem castF_prime {n : ℕ} (hp : n.Prime) : (((n - 1).factorial : ℕ) : ZMod n) = -1 := by
  have hfact : Fact n.Prime := ⟨hp⟩
  exact ZMod.wilsons_lemma n

theorem castA_prime {n : ℕ} (hp : n.Prime) : ((a n : ℕ) : ZMod n) = -1 := by
  rw [castA n hp.one_lt.le, castF_prime hp]

theorem castF_comp {n : ℕ} (hn : 2 ≤ n) (h4 : n ≠ 4) (hp : ¬ n.Prime) :
    (((n - 1).factorial : ℕ) : ZMod n) = 0 :=
  (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_factorial_of_not_prime hn h4 hp)

theorem castA_comp {n : ℕ} (hn : 2 ≤ n) (h4 : n ≠ 4) (hp : ¬ n.Prime) :
    ((a n : ℕ) : ZMod n) = 0 := by
  rw [castA n (by omega), castF_comp hn h4 hp]

theorem mod_of_cast {n x r : ℕ} (hr : r < n) (h : ((x : ℕ) : ZMod n) = ((r : ℕ) : ZMod n)) :
    x % n = r := by
  have := (ZMod.natCast_eq_natCast_iff' x r n).mp h
  rw [this, Nat.mod_eq_of_lt hr]

theorem a_le_succ (n : ℕ) : a n ≤ a (n + 1) := by
  rw [a_succ]
  nlinarith [Nat.zero_le (n * a n), Nat.zero_le n.factorial]

theorem a_succ_pos (n : ℕ) : 1 ≤ a (n + 1) := by
  rw [a_succ]
  have := Nat.factorial_pos n
  omega

theorem sq_le_cube (n : ℕ) : a n ^ 2 ≤ a (n + 1) ^ 3 :=
  (Nat.pow_le_pow_left (a_le_succ n) 2).trans
    (Nat.pow_le_pow_right (a_succ_pos n) (by norm_num))

theorem cast_cube_sub (n : ℕ) (hn : 1 ≤ n) :
    ((a (n + 1) ^ 3 - a n ^ 2 : ℕ) : ZMod n) = ((a n : ℕ) : ZMod n) ^ 3 - ((a n : ℕ) : ZMod n) ^ 2 := by
  rw [Nat.cast_sub (sq_le_cube n), Nat.cast_pow, Nat.cast_pow, castB n hn]

theorem cast_sq_add (n : ℕ) (hn : 1 ≤ n) :
    ((a n ^ 2 + a (n + 1) ^ 2 : ℕ) : ZMod n) =
      ((a n : ℕ) : ZMod n) ^ 2 + ((a n : ℕ) : ZMod n) ^ 2 := by
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_pow, castB n hn]

/-- The factorisation of the difference of squares. -/
theorem sq_sub_sq (n : ℕ) (hn : 1 ≤ n) :
    a (n + 1) ^ 2 - a n ^ 2 =
      n * ((a n + (n - 1).factorial) * ((n + 2) * a n + n * (n - 1).factorial)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hF : (m + 1).factorial = (m + 1) * m.factorial := Nat.factorial_succ m
  have h : a (m + 1 + 1) ^ 2 = a (m + 1) ^ 2 +
      (m + 1) * ((a (m + 1) + m.factorial) * ((m + 1 + 2) * a (m + 1) + (m + 1) * m.factorial)) := by
    rw [a_succ (m + 1), hF]
    ring
  rw [Nat.add_sub_cancel, h, Nat.add_sub_cancel_left]

theorem part1 (n : ℕ) (hn : 2 ≤ n) (h4 : n ≠ 4) :
    (n.Prime → a n % n = n - 1) ∧ (¬ n.Prime → a n % n = 0) := by
  constructor
  · intro hp
    apply mod_of_cast (by omega)
    rw [castA_prime hp, Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self, Nat.cast_one, zero_sub]
  · intro hp
    exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp (castA_comp hn h4 hp))

theorem part2 (n : ℕ) (hn : 3 ≤ n) :
    (n.Prime → a (n + 1) ^ 2 - a n ^ 2 ≡ 4 * n [MOD n ^ 2]) ∧
    (¬ n.Prime → (a (n + 1) ^ 2 - a n ^ 2) % n ^ 2 = 0) := by
  constructor
  · intro hp
    rw [sq_sub_sq n (by omega), sq, mul_comm 4 n]
    apply Nat.ModEq.mul_left'
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [castA_prime hp, castF_prime hp, ZMod.natCast_self]
    ring
  · intro hp
    by_cases h4 : n = 4
    · subst h4
      norm_num [a, Nat.factorial]
    · rw [sq_sub_sq n (by omega), sq]
      apply Nat.mod_eq_zero_of_dvd
      apply mul_dvd_mul_left
      apply Dvd.dvd.mul_right
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, castA_comp (by omega) h4 hp,
        castF_comp (by omega) h4 hp, add_zero]

theorem part3 (n : ℕ) (hn : 3 ≤ n) :
    (n.Prime → (a (n + 1) ^ 3 - a n ^ 2) % n = n - 2) ∧
    (¬ n.Prime → (a (n + 1) ^ 3 - a n ^ 2) % n = 0) := by
  constructor
  · intro hp
    apply mod_of_cast (by omega)
    rw [cast_cube_sub n (by omega), castA_prime hp, Nat.cast_sub (by omega : 2 ≤ n),
      ZMod.natCast_self]
    push_cast
    ring
  · intro hp
    by_cases h4 : n = 4
    · subst h4
      norm_num [a, Nat.factorial]
    · apply Nat.mod_eq_zero_of_dvd
      rw [← ZMod.natCast_eq_zero_iff, cast_cube_sub n (by omega), castA_comp (by omega) h4 hp]
      ring

theorem part4 (n : ℕ) (hn : 3 ≤ n) :
    (n.Prime → (a n ^ 2 + a (n + 1) ^ 2) % n = 2) ∧
    (¬ n.Prime → (a n ^ 2 + a (n + 1) ^ 2) % n = 0) := by
  constructor
  · intro hp
    apply mod_of_cast (by omega)
    rw [cast_sq_add n (by omega), castA_prime hp]
    push_cast
    ring
  · intro hp
    by_cases h4 : n = 4
    · subst h4
      norm_num [a, Nat.factorial]
    · apply Nat.mod_eq_zero_of_dvd
      rw [← ZMod.natCast_eq_zero_iff, cast_sq_add n (by omega), castA_comp (by omega) h4 hp]
      ring

end A000254Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a000254.main :=
  ⟨A000254Aux.part1, A000254Aux.part2, A000254Aux.part3, A000254Aux.part4⟩
