import OMAStatements.S_oeis_a006579

/- Varun Vejalla gave the numerical counterexample for the equivalent
   Pillai-function conjecture in OEIS A018804 on June 19, 2025. -/

namespace A006579

open Finset ArithmeticFunction

def phi : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

def pillai : ArithmeticFunction ℕ := ArithmeticFunction.id * phi

theorem divisorSum (n : ℕ) :
    pillai n = ∑ d ∈ n.divisors, d * (n / d).totient := by
  rw [pillai, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => ArithmeticFunction.id a * phi b)]
  rfl

theorem fullSum {n : ℕ} (hn : 0 < n) :
    n + OMA.S_oeis_a006579.gcdSum n = pillai n := by
  have maps (k : ℕ) (_ : k ∈ range n) : n.gcd k ∈ n.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩
  calc
    n + OMA.S_oeis_a006579.gcdSum n = ∑ k ∈ range n, n.gcd k := by
      rw [sum_range_eq_add_Ico (Nat.gcd n) hn]
      simp [OMA.S_oeis_a006579.gcdSum]
    _ = ∑ d ∈ n.divisors, ∑ k ∈ (range n).filter (fun k => n.gcd k = d), d :=
      (sum_fiberwise_of_maps_to' maps (fun d => d)).symm
    _ = pillai n := by
      rw [divisorSum]
      refine sum_congr rfl fun d hd => ?_
      rw [sum_const, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
      simp [mul_comm]

theorem mulCoprime {a b : ℕ} (h : a.Coprime b) :
    pillai (a * b) = pillai a * pillai b := by
  have hphi : phi.IsMultiplicative :=
    ⟨Nat.totient_one, fun h => Nat.totient_mul h⟩
  exact (ArithmeticFunction.isMultiplicative_id.mul hphi).2 h

theorem atPrime {p : ℕ} (hp : p.Prime) : pillai p = p + (p - 1) := by
  rw [divisorSum, hp.divisors]
  simp [hp.ne_one.symm, hp.pos, Nat.totient_prime hp, Nat.add_comm]

end A006579

open A006579

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a006579.main) := by
  intro h
  have hvalue : pillai 23492890653051 = 610815156979325 := by
    change pillai ((((3 * 37) * 43) * 42307) * 116341) = _
    rw [mulCoprime (by decide), mulCoprime (by decide),
        mulCoprime (by decide), mulCoprime (by decide)]
    norm_num [atPrime]
  have hsum := fullSum (n := 23492890653051) (by decide)
  rw [hvalue] at hsum
  have exactSum : OMA.S_oeis_a006579.gcdSum 23492890653051 = 587322266326274 := by omega
  have composite : ¬ Nat.Prime 23492890653051 := by
    intro hp
    rcases (Nat.dvd_prime hp).mp (show 3 ∣ 23492890653051 by decide) with h | h <;> omega
  apply h 23492890653051 (by decide) composite
  rw [exactSum]
  decide
