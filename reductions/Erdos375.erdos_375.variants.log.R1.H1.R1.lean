import OMAReductions.R_Erdos375_erdos_375_variants_log_R1

/-! Ramachandra, Shorey and Tijdeman (1975), section 2. The first application
of their approximation argument either supplies the logarithmic form or
forces a large family. Removing one maximal prime-power factor for each
prime leaves cofactors whose product divides the factorial. At the cubic
scale this forces many elements with exactly one assigned prime. -/
namespace OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1
open Filter Finset Real

-- The finite factorial bound after assigning each prime to one position
-- where its valuation is maximal. A counts unassigned positions, B the
-- positions with exactly one assigned prime.
def H1 : Prop := ∀ n k : ℕ, ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card < J.card → (∀ p ∈ P, p < k) →
  ∃ (a : ℕ) (B : Finset (Fin k)) (p e u : Fin k → ℕ), B ⊆ J ∧
    J.card ≤ 2*a+B.card ∧ (n+1)^a ≤ k.factorial ∧
    (∏ i ∈ B, u i) ≤ k.factorial ∧ Set.InjOn p B ∧
    ∀ i ∈ B, (p i).Prime ∧ p i < k ∧ 0 < u i ∧ n+i.val+1 = u i*(p i)^(e i)

-- First-stage extraction from a small obstruction (the proof of Lemma 6).
def H2 : Prop := ∀ b : ℝ, 0 < b → ∀ S₀ : ℝ, ∃ δ > (0:ℝ), ∃ c > (0:ℝ),
  ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k:ℝ) < c*(log n/log (log n))^3 →
  ∀ J : Finset (Fin k),
  let P := J.biUnion (fun i => (n+i.val+1).primeFactors)
  P.card < J.card → (∀ p ∈ P, p < k) →
  δ*(log n/log (log n))^2 ≤ J.card ∨ ∃ (S : ℝ) (u v : ℚ) (m : ℤ), S₀ ≤ S ∧ S ≤ (n:ℝ)^b ∧ 0 < u ∧ 0 < v ∧
    ((u.num.natAbs+u.den:ℕ):ℝ) ≤ (log S)^16 ∧ ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S ∧
    2*log S/log (log S) ≤ |(m:ℝ)| ∧ |(m:ℝ)| ≤ (log S)^16 ∧
    |log (v:ℝ)| ≤ (log S)^(3/4:ℝ) ∧
    0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

-- Second-stage extraction (the close cofactors and close exponents on
-- pages 116–118). This statement concerns individual factorizations.
def H3 : Prop := ∀ b : ℝ, 0 < b → ∀ S₀ : ℝ, ∀ δ > (0:ℝ), ∃ c > (0:ℝ),
  ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, (k:ℝ) < c*(log n/log (log n))^3 →
  ∀ (B : Finset (Fin k)) (p e u : Fin k → ℕ),
    δ*(log n/log (log n))^2 ≤ B.card → (∏ i ∈ B, u i) ≤ k.factorial →
    Set.InjOn p B →
    (∀ i ∈ B, (p i).Prime ∧ p i < k ∧ 0 < u i ∧ n+i.val+1 = u i*(p i)^(e i)) →
    ∃ (S : ℝ) (u v : ℚ) (m : ℤ), S₀ ≤ S ∧ S ≤ (n:ℝ)^b ∧ 0 < u ∧ 0 < v ∧
    ((u.num.natAbs+u.den:ℕ):ℝ) ≤ (log S)^16 ∧ ((v.num.natAbs+v.den:ℕ):ℝ) ≤ S ∧
    2*log S/log (log S) ≤ |(m:ℝ)| ∧ |(m:ℝ)| ≤ (log S)^16 ∧
    |log (v:ℝ)| ≤ (log S)^(3/4:ℝ) ∧
    0 < |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| ∧ |(m:ℝ)*log (u:ℝ)-log (v:ℝ)| < (n:ℝ)^(-(1/2:ℝ))

theorem main : H1 → H2 → H3 → OMA.R_Erdos375_erdos_375_variants_log_R1.H1 := by
  intro extraction small large b hb S₀
  obtain ⟨δ,hδ,c₁,hc₁,hs⟩ := small b hb S₀
  obtain ⟨c₂,hc₂,hl⟩ := large b hb S₀ (δ/2) (by positivity)
  let c := min (min c₁ c₂) (min 1 (δ/12))
  have hc : 0<c := by dsimp [c]; positivity
  have hc1 : c≤c₁ := (min_le_left ..).trans (min_le_left ..)
  have hc2 : c≤c₂ := (min_le_left ..).trans (min_le_right ..)
  have hc3 : c≤1 := (min_le_right ..).trans (min_le_left ..)
  have hcd : c≤δ/12 := (min_le_right ..).trans (min_le_right ..)
  refine ⟨c,hc,?_⟩
  have tlog : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have tll : Tendsto (fun n : ℕ => log (log (n:ℝ))) atTop atTop :=
    tendsto_log_atTop.comp tlog
  filter_upwards [hs,hl,tlog.eventually_ge_atTop 1,tll.eventually_ge_atTop 1,
    eventually_ge_atTop 2] with n hs hl hlog hll hn
  intro k hk J P hJ hP
  let L := log (n:ℝ)
  let l := log L
  let Q := L/l
  change 1≤L at hlog
  change 1≤l at hll
  change (k:ℝ)<c*Q^3 at hk
  have lp : 0<l := by linarith
  have Lp : 0<L := by linarith
  have qp : 0<Q := div_pos Lp lp
  have ql : Q≤L := (div_le_iff₀ lp).mpr (by nlinarith only [mul_nonneg Lp.le (sub_nonneg.mpr hll)])
  have kpos : 0<k := by
    have : J.card ≤ k := (card_le_card (subset_univ J)).trans_eq (by simp)
    omega
  rcases hs k (hk.trans_le (mul_le_mul_of_nonneg_right hc1 (pow_nonneg qp.le _))) J hJ hP with hbig|done
  · obtain ⟨a,B,p,e,u,_,hcard,hpow,hfac,hinj,hsingle⟩ := extraction n k J hJ hP
    change δ*Q^2 ≤ _ at hbig
    have hkc : (k:ℝ) ≤ L^3 := calc
      _ ≤ c*Q^3 := hk.le
      _ ≤ 1*L^3 := mul_le_mul hc3 (pow_le_pow_left₀ qp.le ql 3) (pow_nonneg qp.le _) zero_le_one
      _ = _ := one_mul _
    have hkl : log (k:ℝ) ≤ 3*l := by
      have v := log_le_log (by exact_mod_cast kpos) hkc
      rwa [Real.log_pow] at v
    have hnZ : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
    have kn : (n:ℝ)^a ≤ (k:ℝ)^k := by
      exact_mod_cast (Nat.pow_le_pow_left (Nat.le_succ n) a).trans (hpow.trans k.factorial_le_pow)
    have lg := log_le_log (pow_pos hnZ a) kn
    rw [Real.log_pow,Real.log_pow] at lg
    change (a:ℝ)*L ≤ (k:ℝ)*log k at lg
    have ha : (a:ℝ)*L ≤ 3*c*Q^2*L := calc
      _ ≤ (k:ℝ)*log k := lg
      _ ≤ (c*Q^3)*(3*l) := mul_le_mul hk.le hkl (log_natCast_nonneg _) (by positivity)
      _ = _ := by dsimp [Q]; field_simp <;> ring
    have ha' : (a:ℝ) ≤ 3*c*Q^2 := le_of_mul_le_mul_right ha Lp
    have hB : δ/2*Q^2 ≤ (B.card:ℝ) := by
      have hcard' : (J.card:ℝ) ≤ 2*(a:ℝ)+(B.card:ℝ) := by exact_mod_cast hcard
      nlinarith only [hbig,hcard',ha',mul_le_mul_of_nonneg_right hcd (sq_nonneg Q)]
    exact hl k (hk.trans_le (mul_le_mul_of_nonneg_right hc2 (pow_nonneg qp.le _))) B p e u hB hfac hinj hsingle
  · exact done

end OMA.R_Erdos375_erdos_375_variants_log_R1_H1_R1
