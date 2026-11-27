import OMAReductions.R_Erdos364_erdos_364_variants_strong_R1
import Mathlib

/-!
Reduce the arithmetic-progression gap bound to primitive progressions and
progressions in which a common prime square is obstructed from being removed.
-/

namespace OMA.R_Erdos364_erdos_364_variants_strong_R1_H2_R1

private theorem powerful_of_strip_prime_power {p j n : ℕ} (hp : p.Prime)
    (h : (p ^ j * n).Powerful)
    (hval : p ^ (j + 1) ∣ p ^ j * n → p ^ (j + 2) ∣ p ^ j * n) :
    n.Powerful := by
  intro q hq
  obtain ⟨hqPrime, hqn, hn⟩ := Nat.mem_primeFactors.mp hq
  by_cases hqp : q = p
  · subst q
    have hdiv : p ^ (j + 1) ∣ p ^ j * n := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left _ hqn
    have hdiv' := hval hdiv
    rw [pow_add] at hdiv'
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) hdiv'
  · have hcop : q.Coprime p :=
      hqPrime.coprime_iff_not_dvd.mpr (fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hqPrime hp).mp hd))
    have hdiv : q ^ 2 ∣ p ^ j * n := h q (Nat.mem_primeFactors.mpr
      ⟨hqPrime, dvd_mul_of_dvd_right hqn _, mul_ne_zero (pow_ne_zero _ hp.ne_zero) hn⟩)
    exact ((hcop.pow_left 2).pow_right j).dvd_of_dvd_mul_left hdiv

private theorem root_lt_of_lt_pow {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    {k : ℕ} (hk : 0 < k) (h : a < d ^ k) : a ^ (1 / (k : ℝ)) < d := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    a ^ (1 / (k : ℝ)) < (d ^ k) ^ (1 / (k : ℝ)) :=
      Real.rpow_lt_rpow ha h (by positivity)
    _ = d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hd, mul_one_div,
        div_self hk'.ne', Real.rpow_one]

/-- A polynomial bound for the start of a primitive powerful progression. -/
def H1 : Prop :=
  ∃ k C : ℕ, 0 < k ∧ ∀ a d : ℕ, 0 < a → 0 < d →
    a.Powerful → (a + d).Powerful → (a + 2 * d).Powerful →
    a.Coprime d → a ≤ C * d ^ k

/-- A polynomial bound in the nonprimitive case with no common cube,
where each common prime square has an entry of valuation exactly three. -/
def H2 : Prop :=
  ∃ k C : ℕ, 0 < k ∧ ∀ a d : ℕ, 0 < a → 0 < d →
    a.Powerful → (a + d).Powerful → (a + 2 * d).Powerful → ¬ a.Coprime d →
    (∀ p : ℕ, p.Prime → p ^ 3 ∣ a → ¬ p ^ 3 ∣ d) →
    (∀ p : ℕ, p.Prime → p ^ 2 ∣ a → p ^ 2 ∣ d →
      (p ^ 3 ∣ a ∧ ¬ p ^ 4 ∣ a) ∨
      (p ^ 3 ∣ a + d ∧ ¬ p ^ 4 ∣ a + d) ∨
      (p ^ 3 ∣ a + 2 * d ∧ ¬ p ^ 4 ∣ a + 2 * d)) →
    a ≤ C * d ^ k

theorem main : H1 → H2 → OMA.R_Erdos364_erdos_364_variants_strong_R1.H2 := by
  intro hPrimitive hReduced
  obtain ⟨k₁, C₁, hk₁, hPrimitive⟩ := hPrimitive
  obtain ⟨k₂, C₂, _, hReduced⟩ := hReduced
  let k := max k₁ k₂
  let C := max C₁ C₂
  have hk : 0 < k := hk₁.trans_le (le_max_left _ _)
  have hPoly : ∀ a d : ℕ, 0 < a → 0 < d →
      a.Powerful → (a + d).Powerful → (a + 2 * d).Powerful → a ≤ C * d ^ k := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a ih =>
      intro d ha hd hpa hpb hpc
      have hDescend {p j : ℕ} (hp : p.Prime) (hj : 0 < j) (hda : p ^ j ∣ a) (hdd : p ^ j ∣ d)
          (hva : p ^ (j + 1) ∣ a → p ^ (j + 2) ∣ a)
          (hvb : p ^ (j + 1) ∣ a + d → p ^ (j + 2) ∣ a + d)
          (hvc : p ^ (j + 1) ∣ a + 2 * d → p ^ (j + 2) ∣ a + 2 * d) :
          a ≤ C * d ^ k := by
        obtain ⟨x, hx⟩ := hda
        obtain ⟨y, hy⟩ := hdd
        have hxy : a + d = p ^ j * (x + y) := by rw [hx, hy]; ring
        have hxy₂ : a + 2 * d = p ^ j * (x + 2 * y) := by rw [hx, hy]; ring
        have hxPos : 0 < x := by
          by_contra! hn
          have : x = 0 := by omega
          simp_all
        have hyPos : 0 < y := by
          by_contra! hn
          have : y = 0 := by omega
          simp_all
        have hpj : 1 < p ^ j := one_lt_pow₀ hp.one_lt hj.ne'
        have hsmall : x < a := hx ▸ lt_mul_of_one_lt_left hxPos hpj
        rw [hx] at hpa hva
        rw [hxy] at hpb hvb
        rw [hxy₂] at hpc hvc
        have hxBound := ih x hsmall y hxPos hyPos
          (powerful_of_strip_prime_power hp hpa hva)
          (powerful_of_strip_prime_power hp hpb hvb)
          (powerful_of_strip_prime_power hp hpc hvc)
        have hpScale : p ^ j ≤ (p ^ j) ^ k := by
          simpa only [pow_one] using pow_le_pow_right₀ hpj.le (show 1 ≤ k by omega)
        calc
          a = p ^ j * x := hx
          _ ≤ p ^ j * (C * y ^ k) := Nat.mul_le_mul_left _ hxBound
          _ = C * (p ^ j * y ^ k) := by ring
          _ ≤ C * ((p ^ j) ^ k * y ^ k) := by gcongr
          _ = C * d ^ k := by rw [hy, mul_pow]
      by_cases hcop : a.Coprime d
      · exact (hPrimitive a d ha hd hpa hpb hpc hcop).trans
          (Nat.mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ (by omega) (le_max_left _ _)))
      by_cases hcube : ∀ p : ℕ, p.Prime → p ^ 3 ∣ a → ¬ p ^ 3 ∣ d
      · by_cases hsq : ∀ p : ℕ, p.Prime → p ^ 2 ∣ a → p ^ 2 ∣ d →
            (p ^ 3 ∣ a ∧ ¬ p ^ 4 ∣ a) ∨
            (p ^ 3 ∣ a + d ∧ ¬ p ^ 4 ∣ a + d) ∨
            (p ^ 3 ∣ a + 2 * d ∧ ¬ p ^ 4 ∣ a + 2 * d)
        · exact (hReduced a d ha hd hpa hpb hpc hcop hcube hsq).trans
            (Nat.mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ (by omega) (le_max_right _ _)))
        · push Not at hsq
          obtain ⟨p, hp, hda, hdd, hva, hvb, hvc⟩ := hsq
          exact hDescend (j := 2) hp (by decide) hda hdd hva hvb hvc
      · push Not at hcube
        obtain ⟨p, hp, hda, hdd⟩ := hcube
        have hPrimeDvd : p ∣ p ^ 3 := dvd_pow_self _ (by decide)
        have hdb : p ^ 3 ∣ a + d := dvd_add hda hdd
        have hdc : p ^ 3 ∣ a + 2 * d := dvd_add hda (dvd_mul_of_dvd_right hdd _)
        exact hDescend (j := 1) hp (by decide)
          (by simpa using hPrimeDvd.trans hda) (by simpa using hPrimeDvd.trans hdd)
          (fun _ => hda) (fun _ => hdb) (fun _ => hdc)
  let j := k + k
  have hj : 0 < j := by dsimp [j]; omega
  refine ⟨1 / (j : ℝ), by positivity, C ^ 2 + 2, ?_⟩
  intro a b c ha hab hbc hpa hpb hpc hAP
  let d := b - a
  have hd : 0 < d := by dsimp [d]; omega
  have hb : a + d = b := by dsimp [d]; omega
  have hc : a + 2 * d = c := by dsimp [d]; omega
  have habound : a ≤ C * d ^ k :=
    hPoly a d (by omega) hd hpa (hb ▸ hpb) (hc ▸ hpc)
  have hC : C < d ^ k := by
    by_contra! h
    have hbad : a ≤ C ^ 2 := habound.trans (by rw [pow_two]; gcongr)
    omega
  have hGap : a < d ^ j := calc
    a ≤ C * d ^ k := habound
    _ < d ^ k * d ^ k := by gcongr
    _ = d ^ j := (pow_add d k k).symm
  have hGapReal : (a : ℝ) < (d : ℝ) ^ j := by exact_mod_cast hGap
  have hSpan : d ≤ c - a := by dsimp [d]; omega
  have hSpanReal : (d : ℝ) ≤ (c : ℝ) - (a : ℝ) := by
    rw [← Nat.cast_sub (show a ≤ c by omega)]
    exact_mod_cast hSpan
  exact (root_lt_of_lt_pow (by positivity) (by positivity) hj hGapReal).trans_le hSpanReal

end OMA.R_Erdos364_erdos_364_variants_strong_R1_H2_R1
