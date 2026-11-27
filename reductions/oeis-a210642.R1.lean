import OMAStatements.S_oeis_a210642

/-! For n at least seven, every composite m below 2n already divides (n-1)!.
The only remaining issue is existence of any qualifying modulus below 2n at
composite n. If n is prime, n itself qualifies. The two residual statements
separate even and odd composite n. The initial cases are checked in Lean.
Credit: @caa1982. -/

namespace OMA.R_oeis_a210642_R1

open OMA.S_oeis_a210642

def H1 : Prop := ∀ n : ℕ, 7 ≤ n → Even n → ∃ m : ℕ,
  1 < m ∧ m < 2 * n ∧ ∀ k : ℕ, 0 < k → k < n → ¬ (k.factorial ≡ n.factorial [MOD m])

def H2 : Prop := ∀ n : ℕ, 7 ≤ n → Odd n → ¬ n.Prime → ∃ m : ℕ,
  1 < m ∧ m < 2 * n ∧ ∀ k : ℕ, 0 < k → k < n → ¬ (k.factorial ≡ n.factorial [MOD m])

lemma product_dvd_factorial {x y n : ℕ} (hx : 0 < x) (hxy : x < y) (hyn : y ≤ n) :
    x * y ∣ n.factorial := by
  cases y with
  | zero => omega
  | succ y =>
    have hx' : x ∣ y.factorial := Nat.dvd_factorial hx (by omega)
    have hm : x * (y + 1) ∣ (y + 1).factorial := by
      rw [Nat.factorial_succ]
      simpa only [Nat.mul_comm x (y + 1)] using (Nat.mul_dvd_mul_left (y + 1) hx')
    exact hm.trans (Nat.factorial_dvd_factorial hyn)

lemma composite_dvd {m n : ℕ} (hn : 7 ≤ n) (hm : 1 < m) (hmn : m < 2 * n)
    (hcomp : ¬ m.Prime) : m ∣ (n - 1).factorial := by
  obtain ⟨x, y, hx0, hy0, hxy⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega)).mp hcomp
  have hx : 2 ≤ x := by
    by_contra! hx
    interval_cases x <;> simp_all
  have hy : 2 ≤ y := by
    by_contra! hy
    interval_cases y <;> simp_all
  have hx' : x < n := by
    have h := Nat.mul_le_mul_left x hy
    rw [hxy] at h
    omega
  have hy' : y < n := by
    have h := Nat.mul_le_mul_right y hx
    rw [hxy] at h
    omega
  rcases lt_trichotomy x y with hlt | heq | hgt
  · rw [← hxy]
    exact product_dvd_factorial (by omega) hlt (by omega)
  · subst y
    have hdouble : 2 * x < n := by
      by_cases ht : 4 ≤ x
      · have h := Nat.mul_le_mul_right x ht
        rw [hxy] at h
        omega
      · omega
    rw [← hxy]
    have hd : x * x ∣ x * (2 * x) := ⟨2, by ring⟩
    exact hd.trans (product_dvd_factorial (by omega) (by omega) (by omega))
  · rw [← hxy, mul_comm x y]
    exact product_dvd_factorial (by omega) hgt (by omega)

lemma prime_of_qualifies {m n : ℕ} (hn : 7 ≤ n) (hm : 1 < m) (hmn : m < 2 * n)
    (hgood : ∀ k : ℕ, 0 < k → k < n → ¬ (k.factorial ≡ n.factorial [MOD m])) : m.Prime := by
  by_contra hcomp
  have hd := composite_dvd hn hm hmn hcomp
  have hd' := hd.trans (Nat.factorial_dvd_factorial (Nat.sub_le n 1))
  apply hgood (n - 1) (by omega) (by omega)
  exact (Nat.modEq_zero_iff_dvd.mpr hd).trans (Nat.modEq_zero_iff_dvd.mpr hd').symm

lemma prime_qualifies {n : ℕ} (hp : n.Prime) :
    ∀ k : ℕ, 0 < k → k < n → ¬ (k.factorial ≡ n.factorial [MOD n]) := by
  intro k _ hkn heq
  have h0 : n.factorial ≡ 0 [MOD n] := Nat.modEq_zero_iff_dvd.mpr (hp.dvd_factorial.mpr le_rfl)
  exact (not_le_of_gt hkn) (hp.dvd_factorial.mp (Nat.modEq_zero_iff_dvd.mp (heq.trans h0)))

lemma value_of_finite_test (n m : ℕ) (hm : 1 < m)
    (good : ∀ k ∈ Finset.Ioo 0 n, ¬ (k.factorial ≡ n.factorial [MOD m]))
    (bad : ∀ r ∈ Finset.Ioo 1 m, ∃ k ∈ Finset.Ioo 0 n, k.factorial ≡ n.factorial [MOD r]) :
    a n = m := by
  let s : Set ℕ := {r | 1 < r ∧ ∀ k : ℕ, 0 < k → k < n → ¬ (k.factorial ≡ n.factorial [MOD r])}
  have hmem : m ∈ s := ⟨hm, fun k hk hkn => good k (Finset.mem_Ioo.mpr ⟨hk, hkn⟩)⟩
  change sInf s = m
  refine le_antisymm (Nat.sInf_le hmem) ?_
  have hr : sInf s ∈ s := Nat.sInf_mem ⟨m, hmem⟩
  by_contra! hrm
  rcases bad (sInf s) (Finset.mem_Ioo.mpr ⟨hr.1, hrm⟩) with ⟨k, hk, heq⟩
  exact hr.2 k (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2 heq

lemma large_of_witness {n m : ℕ} (hn : 7 ≤ n) (hm : 1 < m) (hmn : m < 2 * n)
    (hgood : ∀ k : ℕ, 0 < k → k < n → ¬ (k.factorial ≡ n.factorial [MOD m])) :
    (a n).Prime ∧ a n ≤ 2 * n := by
  let s : Set ℕ := {r | 1 < r ∧ ∀ k : ℕ, 0 < k → k < n → ¬ (k.factorial ≡ n.factorial [MOD r])}
  have hmem : m ∈ s := ⟨hm, hgood⟩
  have ha : a n ∈ s := Nat.sInf_mem ⟨m, hmem⟩
  have hale : a n ≤ m := Nat.sInf_le hmem
  exact ⟨prime_of_qualifies hn ha.1 (lt_of_le_of_lt hale hmn) ha.2, by omega⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a210642.main := by
  intro heven hodd
  have v1 := value_of_finite_test 1 2 (by decide) (by decide) (by decide)
  have v2 := value_of_finite_test 2 2 (by decide) (by decide) (by decide)
  have v3 := value_of_finite_test 3 3 (by decide) (by decide) (by decide)
  have v4 := value_of_finite_test 4 4 (by decide) (by decide) (by decide)
  have v5 := value_of_finite_test 5 5 (by decide) (by decide) (by decide)
  have v6 := value_of_finite_test 6 9 (by decide) (by decide) (by decide)
  refine ⟨?_, v4, v6⟩
  intro n hn hn4 hn6
  by_cases h7 : 7 ≤ n
  · by_cases hp : n.Prime
    · exact large_of_witness h7 hp.one_lt (by omega) (prime_qualifies hp)
    · rcases Nat.even_or_odd n with he | ho
      · obtain ⟨m, hm, hmn, hgood⟩ := heven n h7 he
        exact large_of_witness h7 hm hmn hgood
      · obtain ⟨m, hm, hmn, hgood⟩ := hodd n h7 ho hp
        exact large_of_witness h7 hm hmn hgood
  · interval_cases n <;> simp_all [v1, v2, v3, v5] <;> decide

end OMA.R_oeis_a210642_R1
