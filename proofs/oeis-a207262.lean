import OMAStatements.S_oeis_a207262
import Mathlib

namespace A207262

lemma key (e u : ℕ) (hu : Odd u) :
    (∑ d ∈ (2 * u).divisors, d ^ e) =
      (2 ^ e + 1) * ∑ d ∈ (2 * u).divisors.filter (fun d => ¬ 2 ∣ d), d ^ e := by
  have hu0 : u ≠ 0 := by rintro rfl; exact absurd hu (by decide)
  have hcop : Nat.Coprime 2 u := Nat.coprime_two_left.mpr hu
  have hfilter : (2 * u).divisors.filter (fun d => ¬ 2 ∣ d) = u.divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd, _⟩, h2⟩
      have hodd : Odd d := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
      exact ⟨(Nat.coprime_two_right.mpr hodd).dvd_of_dvd_mul_left hd, hu0⟩
    · rintro ⟨hd, _⟩
      refine ⟨⟨Dvd.dvd.mul_left hd 2, by omega⟩, fun h2 => ?_⟩
      have h3 : 2 ∣ u := dvd_trans h2 hd
      obtain ⟨k, hk⟩ := hu
      omega
  rw [hfilter]
  have h1 : ∑ d ∈ (2 * u).divisors, d ^ e = ArithmeticFunction.sigma e (2 * u) :=
    ArithmeticFunction.sigma_apply.symm
  have h2 : ∑ d ∈ u.divisors, d ^ e = ArithmeticFunction.sigma e u :=
    ArithmeticFunction.sigma_apply.symm
  have h3 : ArithmeticFunction.sigma e 2 = 2 ^ e + 1 := by
    rw [ArithmeticFunction.sigma_apply, Nat.Prime.divisors Nat.prime_two]
    simp [add_comm]
  rw [h1, h2, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, h3]

end A207262

theorem OMA.solution : type_of% @OMA.S_oeis_a207262.main := by
  intro t
  show (∑ d ∈ (4 * t + 2).divisors, d ^ (4 * t + 2)) =
      (2 ^ (4 * t + 2) + 1) *
        ∑ d ∈ (4 * t + 2).divisors.filter (fun d => ¬ 2 ∣ d), d ^ (4 * t + 2)
  have e : 4 * t + 2 = 2 * (2 * t + 1) := by ring
  have h := A207262.key (4 * t + 2) (2 * t + 1) ⟨t, rfl⟩
  rw [← e] at h
  exact h
