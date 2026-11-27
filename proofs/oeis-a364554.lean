import OMAStatements.S_oeis_a364554
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

open OMA.S_oeis_a364554

namespace TriangularPrimeQuotients

/-- After the division by 2 in a triangular number, its two factors are x
and either 2x+1 or 2x-1. The prime divides one of these two factors. -/
private lemma classify_factors {n p x y : ℕ} (hp : p.Prime) (hxy : n*p = x*y)
    (hnear : y = 2*x+1 ∨ y+1 = 2*x) : p ∈ divisorPrimes n := by
  have hdvd : p ∣ x*y := hxy ▸ Nat.dvd_mul_left _ _
  rcases hp.dvd_mul.mp hdvd with ⟨d, hx⟩ | ⟨d, hy⟩
  · have heq : n*p = (d*y)*p := by rw [hxy, hx]; ring
    have hn : n = d*y := Nat.eq_of_mul_eq_mul_right hp.pos heq
    refine ⟨hp, d, y, hn, Or.inr (Or.inr ?_)⟩
    rw [hx, Nat.mul_comm p d] at hnear
    omega
  · have heq : n*p = (d*x)*p := by rw [hxy, hy]; ring
    have hn : n = d*x := Nat.eq_of_mul_eq_mul_right hp.pos heq
    refine ⟨hp, d, x, hn, ?_⟩
    rw [hy, Nat.mul_comm p d] at hnear
    tauto

private lemma half_product {k m : ℕ} (h : k*(k+1) = 2*m) : k*(k+1)/2 = m := by
  rw [h]
  simp

private lemma classified {n p : ℕ} (h : p ∈ triangularPrimes n) : p ∈ divisorPrimes n := by
  obtain ⟨hp, k, hk⟩ := h
  let x := k/2
  have hd := Nat.mod_add_div k 2
  have hr := Nat.mod_lt k (by decide : 0 < 2)
  by_cases he : k % 2 = 0
  · have hform : k = 2*x := by dsimp [x]; omega
    have htri : k*(k+1)/2 = x*(2*x+1) := half_product (by rw [hform]; ring)
    exact classify_factors hp (hk.symm.trans htri) (Or.inl rfl)
  · have hform : k = 2*x+1 := by dsimp [x]; omega
    have htri : k*(k+1)/2 = (x+1)*(2*x+1) := half_product (by rw [hform]; ring)
    exact classify_factors hp (hk.symm.trans htri) (Or.inr (by omega))

private lemma yes_triangular {n p : ℕ} (h : p ∈ divisorPrimes n) : p ∈ triangularPrimes n := by
  obtain ⟨hp, d, r, rfl, h | h | h | h⟩ := h
  · refine ⟨hp, 2*r, half_product ?_⟩
    calc
      (2*r)*(2*r+1) = (2*r)*(d*p) := by rw [h]
      _ = 2*((d*r)*p) := by ring
  · refine ⟨hp, d*p, half_product ?_⟩
    calc
      (d*p)*(d*p+1) = (d*p)*(2*r) := by rw [h]
      _ = 2*((d*r)*p) := by ring
  · refine ⟨hp, r, half_product ?_⟩
    calc
      r*(r+1) = r*(2*(d*p)) := by rw [h]
      _ = 2*((d*r)*p) := by ring
  · refine ⟨hp, 2*(d*p), half_product ?_⟩
    calc
      (2*(d*p))*(2*(d*p)+1) = (2*(d*p))*r := by rw [h]
      _ = 2*((d*r)*p) := by ring

private lemma bounded {n : ℕ} (hn : 0 < n) : (divisorPrimes n).Finite := by
  refine (Set.finite_Iic (2*n+1)).subset ?_
  rintro p ⟨_, d, r, h, he⟩
  have hd : 0 < d := by
    by_contra! ht
    have hzero : d = 0 := by omega
    have hnzero : n = 0 := by simpa [hzero] using h
    omega
  have hr : r ≤ n := by
    rw [h]
    simpa using Nat.mul_le_mul_right r hd
  have hp : p ≤ d*p := by simpa using Nat.mul_le_mul_right p hd
  change p ≤ 2*n+1
  rcases he with he | he | he | he <;> omega

end TriangularPrimeQuotients

theorem OMA.solution : type_of% @OMA.S_oeis_a364554.main := by
  intro n hn
  have eq : triangularPrimes n = divisorPrimes n :=
    Set.ext fun _ => ⟨TriangularPrimeQuotients.classified, TriangularPrimeQuotients.yes_triangular⟩
  exact ⟨eq, eq ▸ TriangularPrimeQuotients.bounded hn, congrArg Set.ncard eq⟩
