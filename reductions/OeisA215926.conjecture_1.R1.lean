import FormalConjectures.OEIS.«215926»

/-!
# Deficient multipliers and almost perfect numbers

For odd `n`, the greatest power of two below the least prime factor of `n` works.
Any smaller multiplier `k` is coprime to `n`. If its divisor sum is at most `2*k - 2`,
the greatest power of two at most `k` has at least as large an abundancy index.
Thus any obstruction comes from an almost perfect multiplier. The related
first-occurrence argument appears in Naitik Gupta's reduction of conjecture 2 (PR #906).
-/

namespace OMA.R_OeisA215926_conjecture_1_R1

open OeisA215926
open scoped ArithmeticFunction.sigma

private theorem nondeficient_iff {n : ℕ} (hn : 0 < n) :
    n.Perfect ∨ n.Abundant ↔ 2 * n ≤ σ 1 n := by
  rw [ArithmeticFunction.sigma_one_apply,
    Nat.perfect_iff_sum_divisors_eq_two_mul hn, Nat.abundant_iff_sum_divisors]
  omega

private theorem nondeficient_mul_of_dvd {r n : ℕ} (hr : 0 < r) (hn : 0 < n)
    (h : r ∣ n) (hs : r.Perfect ∨ r.Abundant) : n.Perfect ∨ n.Abundant := by
  have abundancy {t : ℕ} (ht : 0 < t) : t.Perfect ∨ t.Abundant ↔ 2 ≤ t.abundancyIndex := by
    rw [nondeficient_iff ht, ArithmeticFunction.sigma_one_apply, Nat.abundancyIndex,
      le_div_iff₀ (by positivity)]
    norm_cast
  exact (abundancy hn).mpr ((abundancy hr).mp hs |>.trans
    (Nat.abundancyIndex_le_of_dvd hn.ne' h))

private theorem sigma_two_pow (j : ℕ) : σ 1 (2 ^ j) + 1 = 2 * 2 ^ j := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
    Nat.geomSum_eq (m := 2) (by decide), pow_succ]
  have := Nat.two_pow_pos j
  omega

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = 1 + p := by
  rw [ArithmeticFunction.sigma_one_apply, hp.divisors]
  simp [Ne.symm hp.ne_one]

private theorem pow_mul_prime_nondeficient {j p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p < 2 * 2 ^ j) : ((2 ^ j) * p).Perfect ∨ ((2 ^ j) * p).Abundant := by
  apply (nondeficient_iff (Nat.mul_pos (Nat.two_pow_pos _) hp.pos)).mpr
  have hcop : (2 ^ j).Coprime p := (hp.odd_of_ne_two hp2).coprime_two_left.pow_left j
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime hp]
  have hσ := sigma_two_pow j
  have hd : p ≤ σ 1 (2 ^ j) := by omega
  nlinarith only [hd, congrArg (· * p) hσ]

private theorem replace_by_power {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hkn : k.Coprime n) (hodd : Odd n) (hdeficit : σ 1 k + 2 ≤ 2 * k)
    (hnondef : (k * n).Perfect ∨ (k * n).Abundant) :
    ((2 ^ (Nat.log 2 k)) * n).Perfect ∨ ((2 ^ (Nat.log 2 k)) * n).Abundant := by
  let j := Nat.log 2 k
  let x := 2 ^ j
  change (x * n).Perfect ∨ (x * n).Abundant
  have hx : 0 < x := by dsimp [x]; positivity
  have hkx : k ≤ 2 * x := by
    have hlog := Nat.lt_pow_succ_log_self Nat.one_lt_two k
    rw [Nat.succ_eq_add_one, pow_succ] at hlog
    dsimp [x, j]
    omega
  have hσ : σ 1 x + 1 = 2 * x := sigma_two_pow j
  have hcompare : σ 1 k * x ≤ σ 1 x * k := by
    have h₁ := Nat.mul_le_mul_right x hdeficit
    have h₂ := congrArg (· * k) hσ
    nlinarith only [h₁, h₂, hkx]
  have hnorm := (nondeficient_iff (Nat.mul_pos hk hn)).mp hnondef
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hkn] at hnorm
  have hxcop : x.Coprime n := hodd.coprime_two_left.pow_left j
  apply (nondeficient_iff (Nat.mul_pos hx hn)).mpr
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hxcop]
  have h₁ := Nat.mul_le_mul_right x hnorm
  have h₂ := Nat.mul_le_mul_right (σ 1 n) hcompare
  apply Nat.le_of_mul_le_mul_right (c := k) _ hk
  calc
    (2 * (x * n)) * k = (2 * (k * n)) * x := by ring
    _ ≤ (σ 1 k * σ 1 n) * x := h₁
    _ = (σ 1 k * x) * σ 1 n := by ring
    _ ≤ (σ 1 x * k) * σ 1 n := h₂
    _ = (σ 1 x * σ 1 n) * k := by ring

/-- The odd case of the almost perfect number conjecture. -/
def H1 : Prop := ∀ k : ℕ, Odd k → 1 + σ 1 k = 2 * k → k = 1

/-- The even case of the almost perfect number conjecture. -/
def H2 : Prop := ∀ k : ℕ, Even k → 1 + σ 1 k = 2 * k → k.isPowerOfTwo

theorem main : H1 → H2 → type_of% @OeisA215926.conjecture_1 := by
  intro halmostOdd halmostEven n hn
  let S := {k : ℕ | k.Deficient ∧ ((k * n).Perfect ∨ (k * n).Abundant)}
  have hnp : 0 < n := by omega
  change sInf S = 1 ∨ sInf S = 3 ∨ (sInf S).isPowerOfTwo
  by_cases hn₂ : 2 ∣ n
  · have hs : 3 ∈ S :=
      ⟨Nat.deficient_three, nondeficient_mul_of_dvd (by decide) (Nat.mul_pos (by decide) hnp)
        (Nat.mul_dvd_mul_left 3 hn₂) (Or.inl (by constructor <;> decide))⟩
    have hmin := Nat.sInf_mem (show S.Nonempty from ⟨3, hs⟩)
    have hp : 0 < sInf S := hmin.1.pos
    have hmax : sInf S ≤ 3 := Nat.sInf_le hs
    interval_cases h : sInf S <;> first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr ⟨1, rfl⟩)
  · have hodd : Odd n := Nat.not_even_iff_odd.mp (fun h => hn₂ (even_iff_two_dvd.mp h))
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpd : p ∣ n := Nat.minFac_dvd n
    have hp₂ : p ≠ 2 := fun he => hn₂ (he ▸ hpd)
    let j := Nat.log 2 p
    let x := 2 ^ j
    have hx : x < p := by
      have hxle : x ≤ p := Nat.pow_log_le_self 2 hp.ne_zero
      refine lt_of_le_of_ne hxle ?_
      intro he
      have hd : p ∣ 2 ^ j := he.symm ▸ dvd_rfl
      exact hp₂ ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    have hpx : p < 2 * x := by
      have h := Nat.lt_pow_succ_log_self Nat.one_lt_two p
      simpa [x, j, pow_succ, Nat.mul_comm] using h
    have hxp : 0 < x := Nat.two_pow_pos j
    have hs : x ∈ S :=
      ⟨Nat.prime_two.deficient_pow,
        nondeficient_mul_of_dvd (Nat.mul_pos hxp hp.pos) (Nat.mul_pos hxp hnp)
          (Nat.mul_dvd_mul_left x hpd) (pow_mul_prime_nondeficient hp hp₂ hpx)⟩
    let k := sInf S
    have hk : k ∈ S := Nat.sInf_mem ⟨x, hs⟩
    have hkp : k < p := (Nat.sInf_le hs).trans_lt hx
    refine Or.inr (Or.inr ?_)
    by_cases hσ : 1 + σ 1 k = 2 * k
    · rcases Nat.even_or_odd k with he | ho
      · exact halmostEven k he hσ
      · exact ⟨0, halmostOdd k ho hσ⟩
    · have hd := hk.1
      have hσ' : σ 1 k < 2 * k := by
        rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
        unfold Nat.Deficient at hd
        omega
      have hdeficit : σ 1 k + 2 ≤ 2 * k := by
        omega
      have hpow : 2 ^ (Nat.log 2 k) ∈ S :=
        ⟨Nat.prime_two.deficient_pow,
          replace_by_power hd.pos hnp (Nat.coprime_of_lt_minFac hd.pos.ne' hkp).symm
            hodd hdeficit hk.2⟩
      exact ⟨Nat.log 2 k, (Nat.sInf_le hpow).antisymm (Nat.pow_log_le_self 2 hd.pos.ne')⟩

end OMA.R_OeisA215926_conjecture_1_R1
