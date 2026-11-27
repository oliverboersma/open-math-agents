import FormalConjectures.GreensOpenProblems.«46»

-- Credit: @marcusbuffett
-- Iwaniec, On the problem of Jacobsthal (1978).
-- The CRT interpretation of the covering problem is also described by
-- HJ van Veen in 30k30/scholia, erdos-687, following Ford et al.
namespace OMA.R_Green46_green_46_variants_upper_R1

open Green46 Filter Finset Real Asymptotics

/-- Iwaniec's Jacobsthal bound for an integer with k distinct prime factors. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, ∃ m : ℕ,
    (m : ℝ) ≤ C * ((k : ℝ) * log k)^2 ∧
      ∀ d : ℕ, 0 < d → d.primeFactors.card = k →
        ∀ a : ℤ, ∃ i : ℕ, i < m ∧ (a + i).natAbs.Coprime d

/-- Chinese remaindering converts a residue covering into an interval avoiding
integers coprime to the primorial. -/
def H2 : Prop := ∀ x y : ℕ, IsCoveredByResidues x y →
  ∃ a : ℤ, ∀ i : ℕ, i < y → ¬(a + i).natAbs.Coprime (primorial x)

theorem main : H1 → H2 → type_of% @Green46.green_46.variants.upper := by
  rintro ⟨C,hC,hI⟩ crt
  let D := log 4 + 1
  have count := tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le (show (0:ℝ)<1 by norm_num))
  refine IsBigO.of_bound (C * D^2) ?_
  filter_upwards [Nat.tendsto_primeCounting.eventually hI, count, eventually_ge_atTop 2,
    Nat.tendsto_primeCounting.eventually_ge_atTop 2] with x hi hc hx hk
  obtain ⟨m,hm,hwin⟩ := hi
  simp only [Nat.floor_natCast] at hc
  have hpx : x.primeCounting ≤ x := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    have sub : x.primesLE ⊆ Icc 1 x := fun p hp =>
      mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩
    simpa using card_le_card sub
  have logx : 0 < log x := log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlog : log x.primeCounting ≤ log x :=
    log_le_log (by exact_mod_cast (show 0 < x.primeCounting by omega)) (by exact_mod_cast hpx)
  have bound : (x.primeCounting : ℝ) * log x.primeCounting ≤ D * x :=
    (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans ((le_div_iff₀ logx).mp hc)
  have nonneg : 0 ≤ (x.primeCounting : ℝ) * log x.primeCounting :=
    mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by exact_mod_cast (show 1 ≤ x.primeCounting by omega)))
  have hm' := hm.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ nonneg bound 2) hC.le)
  have allm (y : ℕ) (hy : IsCoveredByResidues x y) : y ≤ m := by
    obtain ⟨a,ha⟩ := crt x y hy
    obtain ⟨i,him,hcop⟩ := hwin (primorial x) (primorial_pos x)
      (by rw [primeFactors_primorial, Nat.primesLE_card_eq_primeCounting]) a
    by_contra! h
    exact ha i (by omega) hcop
  have zero : IsCoveredByResidues x 0 := ⟨fun _ => 0, by simp⟩
  have hs : sSup {y : ℕ | IsCoveredByResidues x y} ≤ m :=
    csSup_le ⟨0,zero⟩ allm
  have hrs : maxY x ≤ m := by unfold maxY; exact_mod_cast hs
  have hpos : 0 ≤ maxY x := by unfold maxY; positivity
  rw [Real.norm_of_nonneg hpos, bestUpper, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ C * (D * (x : ℝ))^2 := hrs.trans hm'
    _ = _ := by ring

end OMA.R_Green46_green_46_variants_upper_R1
