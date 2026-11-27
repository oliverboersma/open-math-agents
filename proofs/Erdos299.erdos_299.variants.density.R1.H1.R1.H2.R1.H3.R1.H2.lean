import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1

/-!
The set of maximal prime powers of a positive integer determines it by multiplication. Expanding a product of factors 1 + exp(1)/q bounds the weighted reciprocal sum of the cofactor family. Taking logarithms gives the required prime-power mass.
-/
namespace OMA.FactorMass
open Finset Real
open scoped BigOperators
def powers (C : Finset ℕ) := C.biUnion fun n =>
  n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
def factors (n : ℕ) := n.primeFactors.image (fun p => p ^ n.factorization p)
lemma distinct (n : ℕ) : Set.InjOn (fun p => p ^ n.factorization p) (↑n.primeFactors) := by
  intro p hp q hq he
  have h (p : ℕ) (hp : p ∈ n.primeFactors) :
      (p^n.factorization p).primeFactors = {p} :=
    Nat.primeFactors_prime_pow (Finsupp.mem_support_iff.mp hp) (Nat.prime_of_mem_primeFactors hp)
  have eq := congrArg Nat.primeFactors he
  exact Finset.singleton_inj.mp ((h p hp).symm.trans (eq.trans (h q hq)))
lemma recover {n : ℕ} (hn : n ≠ 0) : ∏ q ∈ factors n, q = n := by
  rw [factors,prod_image (distinct n)]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm
lemma subset_powers {C : Finset ℕ} {n : ℕ} (hn : n ∈ C) (hz : n ≠ 0) :
    factors n ⊆ powers C := by
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
  have prime := Nat.prime_of_mem_primeFactors hp
  exact mem_biUnion.mpr ⟨n,hn,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.ordProj_dvd n p,hz⟩,
    prime.isPrimePow.pow (Finsupp.mem_support_iff.mp hp),(Nat.coprime_ordCompl prime hz).pow_left _⟩⟩
lemma exponential_bound (C : Finset ℕ) (hz : 0 ∉ C) :
    (∑ n ∈ C, exp (n.primeFactors.card : ℝ) / n) ≤
      exp (exp 1 * ∑ q ∈ powers C, (1:ℝ)/q) := by
  classical
  let w (q : ℕ) := exp 1 / (q : ℝ)
  have reconstruct (n : ℕ) (hn : n ∈ C) : ∏ q ∈ factors n, w q = exp (n.primeFactors.card : ℝ) / n := by
    have hne : n ≠ 0 := fun e => hz (e ▸ hn)
    have den : (∏ q ∈ factors n, (q : ℝ)) = n := by
      change (∏ x ∈ factors n, (Nat.castRingHom ℝ) x) = (Nat.castRingHom ℝ) n
      rw [← map_prod,recover hne]
    simp only [w,prod_div_distrib,prod_const,den]
    rw [factors,card_image_of_injOn (distinct n),← exp_nat_mul,mul_one]
  have inject : Set.InjOn factors (↑C) := by
    intro n hn m hm heq
    have h := congrArg (fun s : Finset ℕ => ∏ q ∈ s, q) heq
    simpa only [recover (show n≠0 from fun e => hz (e ▸ hn)),recover (show m≠0 from fun e => hz (e ▸ hm))] using h
  have included : C.image factors ⊆ (powers C).powerset := by
    intro s hs
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hs
    exact mem_powerset.mpr (subset_powers hn (fun e => hz (e ▸ hn)))
  calc
    _ = ∑ s ∈ C.image factors, ∏ q ∈ s, w q := by
      rw [sum_image inject]
      exact sum_congr rfl (fun n hn => (reconstruct n hn).symm)
    _ ≤ ∑ s ∈ (powers C).powerset, ∏ q ∈ s, w q :=
      sum_le_sum_of_subset_of_nonneg included (fun _ _ _ => prod_nonneg fun _ _ => by dsimp [w]; positivity)
    _ = ∏ q ∈ powers C, (1+w q) := (prod_one_add _).symm
    _ ≤ ∏ q ∈ powers C, exp (w q) := prod_le_prod
      (fun q _ => by dsimp [w]; positivity) (fun q _ => by linarith [add_one_le_exp (w q)])
    _ = _ := by rw [← Real.exp_sum,Finset.mul_sum]; congr 1; apply sum_congr rfl; intro q hq; dsimp [w]; ring
end OMA.FactorMass

namespace OMA.FactorMass
open Filter Finset Real

theorem density : ∀ᶠ N : ℕ in atTop, ∀ C : Finset ℕ,
    (log N)^(-(1/99:ℝ)) ≤ ∑ n ∈ C, (1:ℝ)/n →
    (∀ m ∈ C, (1-2/99:ℝ)*log (log N) ≤ m.primeFactors.card ∧
      (m.primeFactors.card:ℝ) ≤ 2*log (log N)) →
    (35/100:ℝ)*log (log N) ≤ ∑ q ∈ powers C, (1:ℝ)/q := by
  filter_upwards [eventually_ge_atTop 4] with N hN
  intro C hm hc
  let w := log (log N)
  have e := exp_one_lt_d9
  have hn : (4:ℝ) ≤ N := by exact_mod_cast hN
  have logbig : 1 < log N := (lt_log_iff_exp_lt (by linarith)).mpr (by linarith)
  have hw : 0 < w := log_pos logbig
  have hz : 0 ∉ C := by
    intro h
    have := (hc 0 h).1
    simp only [Nat.primeFactors_zero,card_empty,Nat.cast_zero] at this
    change (1-2/99:ℝ)*w ≤ 0 at this
    linarith
  have bound := exponential_bound C hz
  have mass : exp (-(1/99:ℝ)*w) ≤ ∑ n ∈ C, (1:ℝ)/n := by
    rw [Real.rpow_def_of_pos (by linarith : 0 < log N)] at hm
    simpa only [w,mul_comm] using hm
  have lower : exp ((1-3/99:ℝ)*w) ≤ exp (exp 1 * ∑ q ∈ powers C, (1:ℝ)/q) := calc
    _ = exp ((1-2/99:ℝ)*w) * exp (-(1/99:ℝ)*w) := by rw [← exp_add]; congr 1; ring
    _ ≤ exp ((1-2/99:ℝ)*w) * ∑ n ∈ C, (1:ℝ)/n := mul_le_mul_of_nonneg_left mass (exp_pos _).le
    _ ≤ ∑ n ∈ C, exp (n.primeFactors.card : ℝ)/n := by
      rw [mul_sum]
      apply sum_le_sum
      intro n hn
      rw [mul_one_div]
      apply div_le_div_of_nonneg_right (exp_le_exp.mpr (hc n hn).1) (by positivity)
    _ ≤ _ := bound
  have logbound := exp_le_exp.mp lower
  change 35/100*w ≤ _
  by_contra! bad
  have bad' := mul_lt_mul_of_pos_left bad (exp_pos 1)
  nlinarith only [bad', logbound, hw, mul_lt_mul_of_pos_right e hw]
end OMA.FactorMass

theorem OMA.solution : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1.H2 := OMA.FactorMass.density
