import FormalConjectures.ErdosProblems.«1057»
import Mathlib

/-!
# An upper bound for the Carmichael counting function

Erdős, On pseudoprimes and Carmichael numbers, Publ. Math. Debrecen 4 (1956), 201–206.
The counting argument uses Pomerance's Rankin method in Two methods in elementary
analytic number theory, Number Theory and Applications (1989), 135–161.
-/

namespace CarmichaelCount

open Filter Finset Real
open scoped Topology

private theorem carmichael_composite {n : ℕ} (hn : IsCarmichael n) : ¬n.Prime ∧ 1 < n :=
  (hn 1 (by decide) (Nat.coprime_one_right n)).2

/-- The exponent of the group of units modulo a Carmichael number divides its predecessor. -/
private theorem carmichael_exponent_dvd {n : ℕ} (hn : IsCarmichael n) :
    ArithmeticFunction.carmichael n ∣ n - 1 := by
  have hn1 := (carmichael_composite hn).2
  have : NeZero n := ⟨by omega⟩
  rw [ArithmeticFunction.carmichael_eq_exponent']
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro a
  let b : ℕ := (a : ZMod n).val + n
  have hb : 1 ≤ b := by unfold b; omega
  have hcast : (b : ZMod n) = a := by simp [b]
  have hc : n.Coprime b := ((ZMod.isUnit_iff_coprime b n).1 (hcast ▸ a.isUnit)).symm
  have hp := (Nat.probablePrime_iff_modEq n hb).1 (hn b hb hc).1
  apply Units.ext
  simpa [hcast] using (ZMod.natCast_eq_natCast_iff _ _ _).2 hp

private theorem carmichael_prime {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.carmichael p = p - 1 := by
  by_cases h2 : p = 2
  · subst p
    simpa using ArithmeticFunction.carmichael_two_pow_of_le_two (n := 1) (by decide)
  · simpa [Nat.totient_prime hp] using ArithmeticFunction.carmichael_pow_of_prime_ne_two 1 hp h2

private theorem prime_sub_one_dvd {n p : ℕ} (hn : IsCarmichael n) (hp : p.Prime)
    (hpn : p ∣ n) : p - 1 ∣ n - 1 := by
  rw [← carmichael_prime hp]
  exact (ArithmeticFunction.carmichael_dvd hpn).trans (carmichael_exponent_dvd hn)

private theorem coprime_pred {n : ℕ} (hn : 1 ≤ n) : n.Coprime (n - 1) := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hpp
  apply hp.not_dvd_one
  have hb := Nat.dvd_sub hpn hpp
  rwa [show n - (n - 1) = 1 by omega] at hb

private theorem carmichael_squarefree {n : ℕ} (hn : IsCarmichael n) : Squarefree n := by
  refine Nat.squarefree_iff_prime_squarefree.2 fun p hp hpp => ?_
  have hp' : p ∣ ArithmeticFunction.carmichael (p ^ 2) := by
    by_cases h : p = 2
    · subst p
      rw [ArithmeticFunction.carmichael_two_pow_of_le_two (by decide)]
      decide
    · rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two _ hp h, Nat.totient_prime_pow hp (by decide : 0 < 2)]
      simp
  have hpn : p ∣ n := (dvd_mul_right p p).trans hpp
  have hdiv : p ^ 2 ∣ n := by simpa [pow_two] using hpp
  have hppred := hp'.trans ((ArithmeticFunction.carmichael_dvd hdiv).trans (carmichael_exponent_dvd hn))
  exact hp.not_dvd_one <| (coprime_pred (by have := (carmichael_composite hn).2; omega) :
    n.Coprime (n - 1)).gcd_eq_one ▸ Nat.dvd_gcd hpn hppred

/-- The least divisor above the cutoff is at most the cutoff times the largest prime factor. -/
private theorem exists_large_divisor {n : ℕ} {a b : ℝ} (ha : 1 ≤ a)
    (hn : a < n) (hsmall : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ b) :
    ∃ d : ℕ, d ∣ n ∧ a < d ∧ (d : ℝ) ≤ a * b := by
  classical
  let h : ∃ d : ℕ, a < d ∧ d ∣ n := ⟨n, hn, dvd_rfl⟩
  let d := Nat.find h
  obtain ⟨had, hdn⟩ : a < (d : ℝ) ∧ d ∣ n := Nat.find_spec h
  have hd : 1 < d := by exact_mod_cast ha.trans_lt had
  obtain ⟨p, hp, c, hc⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
  have hcpos : 0 < c := by
    by_contra! hzero
    have : c = 0 := by omega
    simp [this] at hc
    omega
  have hcd : c < d := by rw [hc]; simpa using (Nat.mul_lt_mul_of_pos_right hp.one_lt hcpos)
  have hcn : c ∣ n := (show c ∣ d by rw [hc]; exact dvd_mul_left ..).trans hdn
  have hca : (c : ℝ) ≤ a := by
    by_contra! hnca
    exact (Nat.find_min h hcd) ⟨hnca, hcn⟩
  have hpb := hsmall p hp ((show p ∣ d from ⟨c, hc⟩).trans hdn)
  refine ⟨d, hdn, had, ?_⟩
  rw [hc, Nat.cast_mul, mul_comm]
  exact mul_le_mul hca hpb (by positivity) (by linarith)

private theorem carmichael_from_prime {n p : ℕ} (hn : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) : ∃ j : ℕ, 0 < j ∧ n = p * (1 + (p - 1) * j) := by
  obtain ⟨k, hk⟩ := hpn
  have hn' := carmichael_composite hn
  have hk' : 1 < k := by
    by_contra! hsmall
    interval_cases k
    · simp_all
    · simp_all
  have heq : n - 1 = (k - 1) + (p - 1) * k := by
    have hp' : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
    have hk'' : k - 1 + 1 = k := Nat.sub_add_cancel hk'.le
    calc
      n - 1 = ((p - 1 + 1) * k) - 1 := by rw [hp', hk]
      _ = _ := by rw [Nat.add_mul, one_mul]; omega
  have hj : p - 1 ∣ k - 1 := by
    have h := Nat.dvd_sub (prime_sub_one_dvd hn hp ⟨k, hk⟩) (dvd_mul_right (p - 1) k)
    rwa [heq, Nat.add_sub_cancel] at h
  obtain ⟨j, hj⟩ := hj
  have hj' : 0 < j := Nat.pos_of_ne_zero (by intro h; simp [h] at hj; omega)
  refine ⟨j, hj', ?_⟩
  rw [hk]
  congr 1
  omega

private noncomputable def carms (N : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 N).filter IsCarmichael

private theorem mem_carms {n N : ℕ} : n ∈ carms N ↔ IsCarmichael n ∧ n ≤ N := by
  classical
  simp only [carms, mem_filter, mem_Icc]
  constructor
  · tauto
  · rintro ⟨h, hN⟩
    exact ⟨⟨(carmichael_composite h).2.le, hN⟩, h⟩

private theorem count_eq_card {x : ℝ} (hx : 0 ≤ x) :
    Erdos1057.carmichaelCounting x = ((carms ⌊x⌋₊).card : ℝ) := by
  have heq : {n : ℕ | IsCarmichael n ∧ (n : ℝ) ≤ x} = (carms ⌊x⌋₊ : Set ℕ) := by
    ext n
    simp [mem_carms, Nat.le_floor_iff hx]
  unfold Erdos1057.carmichaelCounting
  rw [heq, Set.ncard_coe_finset]

private theorem card_fiber_le {N d : ℕ} :
    (((carms N).filter fun n => d ∣ n).card : ℝ) ≤ (N : ℝ) / d := by
  classical
  have hs : (carms N).filter (fun n => d ∣ n) ⊆ (Ioc 0 N).filter (fun n => d ∣ n) := by
    intro n hn
    simp only [mem_filter, mem_carms, mem_Ioc] at hn ⊢
    exact ⟨⟨Nat.zero_lt_of_lt (carmichael_composite hn.1.1).2, hn.1.2⟩, hn.2⟩
  have h := Finset.card_le_card hs
  rw [Nat.Ioc_filter_dvd_card_eq_div] at h
  exact (by exact_mod_cast h : (((carms N).filter fun n => d ∣ n).card : ℝ) ≤ (N / d : ℕ)).trans
    Nat.cast_div_le

/-- For a fixed divisor, the possible Carmichael numbers occupy one residue class modulo the divisor times its Carmichael exponent. -/
private theorem card_fiber_carmichael_le {N d : ℕ} :
    (((carms N).filter fun n => d ∣ n).card : ℝ) ≤
      1 + (N : ℝ) / (d * ArithmeticFunction.carmichael d) := by
  classical
  let lambdaD := ArithmeticFunction.carmichael d
  let m := d * lambdaD
  let S := (carms N).filter fun n => d ∣ n
  have hcard : S.card ≤ N / m + 1 := by
    rw [← Finset.card_range (N / m + 1)]
    refine Finset.card_le_card_of_injOn (fun k : ℕ => k / m) ?_ ?_
    · intro n hn
      exact mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_carms.mp (mem_filter.mp hn).1).2))
    · intro a ha b hb heq
      obtain ⟨ha, hda⟩ := mem_filter.mp ha
      obtain ⟨hb, hdb⟩ := mem_filter.mp hb
      have hac := (mem_carms.mp ha).1
      have hbc := (mem_carms.mp hb).1
      have hLambdaeq (n : ℕ) (hn : IsCarmichael n) (hdn : d ∣ n) : 1 ≡ n [MOD lambdaD] :=
        (Nat.modEq_iff_dvd' (carmichael_composite hn).2.le).2
          ((ArithmeticFunction.carmichael_dvd hdn).trans (carmichael_exponent_dvd hn))
      have hcop : d.Coprime lambdaD := (coprime_pred (carmichael_composite hac).2.le).coprime_dvd_left hda
        |>.coprime_dvd_right ((ArithmeticFunction.carmichael_dvd hda).trans (carmichael_exponent_dvd hac))
      have habd : a ≡ b [MOD d] := (Nat.modEq_zero_iff_dvd.mpr hda).trans (Nat.modEq_zero_iff_dvd.mpr hdb).symm
      have hab : a ≡ b [MOD m] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1
        ⟨habd, (hLambdaeq _ hac hda).symm.trans (hLambdaeq _ hbc hdb)⟩
      change a % m = b % m at hab
      have h₁ := Nat.mod_add_div a m
      have h₂ := Nat.mod_add_div b m
      change a / m = b / m at heq
      rw [hab, heq] at h₁
      omega
  have hcast : (S.card : ℝ) ≤ (N / m : ℕ) + (1 : ℝ) := by exact_mod_cast hcard
  calc
    (S.card : ℝ) ≤ (N / m : ℕ) + (1 : ℝ) := hcast
    _ ≤ 1 + (N : ℝ) / m := by
      have h : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / m := Nat.cast_div_le
      linarith
    _ = _ := by simp [m, lambdaD]

private theorem card_biUnion_real_le {α β : Type*} [DecidableEq β] (S : Finset α)
    (F : α → Finset β) (u : α → ℝ) (hf : ∀ a ∈ S, ((F a).card : ℝ) ≤ u a) :
    ((S.biUnion F).card : ℝ) ≤ ∑ a ∈ S, u a := by
  calc
    _ ≤ ((∑ a ∈ S, (F a).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ = ∑ a ∈ S, ((F a).card : ℝ) := by push_cast; rfl
    _ ≤ _ := sum_le_sum hf

private theorem reciprocal_telescope {B : ℕ} (hB : 0 < B) (N : ℕ) :
    ∑ q ∈ Ico B N, 1 / (((q : ℝ) + 1) * q) ≤ 1 / (B : ℝ) := by
  have hsum (M : ℕ) (hM : B ≤ M) :
      ∑ q ∈ Ico B M, 1 / (((q : ℝ) + 1) * q) = 1 / (B : ℝ) - 1 / (M : ℝ) := by
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [sum_Ico_succ_top hm, ih, Nat.cast_succ]
      have ha : (0 : ℝ) < m := by exact_mod_cast (hB.trans_le hm)
      field_simp; ring
  by_cases h : B ≤ N
  · rw [hsum N h]
    exact sub_le_self _ (by positivity)
  · simp [Finset.Ico_eq_empty_of_le (by omega : N ≤ B)]

private noncomputable def carmsLarge (N B : ℕ) : Finset ℕ := by
  classical
  exact (carms N).filter fun n => ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ B < p

/-- The cofactor of a prime divisor is one plus a positive multiple of the prime minus one. -/
private theorem card_large_le {N B : ℕ} (hB : 0 < B) :
    ((carmsLarge N B).card : ℝ) ≤ (N : ℝ) / B := by
  classical
  let F := fun q : ℕ => (Icc 1 (N / ((q + 1) * q))).image
    (fun j => (q + 1) * (1 + q * j))
  have hcover : carmsLarge N B ⊆ (Ico B N).biUnion F := by
    intro n hn
    obtain ⟨hn, p, hp, hpn, hBp⟩ := mem_filter.mp hn
    obtain ⟨hn, hnN⟩ := mem_carms.mp hn
    obtain ⟨j, hj, heq⟩ := carmichael_from_prime hn hp hpn
    let q := p - 1
    have he : q + 1 = p := Nat.sub_add_cancel hp.one_lt.le
    have hpN := (Nat.le_of_dvd (by have := (carmichael_composite hn).2; omega) hpn).trans hnN
    refine mem_biUnion.mpr ⟨q, mem_Ico.mpr ⟨by omega, by omega⟩, mem_image.mpr ?_⟩
    refine ⟨j, mem_Icc.mpr ⟨hj, ?_⟩, by simpa only [he] using heq.symm⟩
    apply (Nat.le_div_iff_mul_le (show 0 < (q + 1) * q from Nat.mul_pos (by omega) (by omega))).2
    calc
      j * ((q + 1) * q) = (q + 1) * (q * j) := by ring
      _ ≤ (q + 1) * (1 + q * j) := by gcongr; omega
      _ = n := by simpa only [he] using heq.symm
      _ ≤ N := hnN
  calc
    _ ≤ (((Ico B N).biUnion F).card : ℝ) := by exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ q ∈ Ico B N, (N : ℝ) * (1 / (((q : ℝ) + 1) * q)) := by
      apply card_biUnion_real_le
      intro q hq
      have hcard : (F q).card ≤ N / ((q + 1) * q) := by
        simpa [F, Nat.card_Icc] using (Finset.card_image_le (s := Icc 1 (N / ((q + 1) * q)))
          (f := fun j => (q + 1) * (1 + q * j)))
      calc
        _ ≤ ((N / ((q + 1) * q) : ℕ) : ℝ) := by exact_mod_cast hcard
        _ ≤ (N : ℝ) / (((q : ℝ) + 1) * q) := by
          simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
            (Nat.cast_div_le (α := ℝ) (m := N) (n := (q + 1) * q))
        _ = _ := by ring
    _ ≤ _ := by
      rw [← Finset.mul_sum, div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (reciprocal_telescope hB N) (Nat.cast_nonneg N)

private theorem carmichael_pos {d : ℕ} (hd : 0 < d) :
    0 < ArithmeticFunction.carmichael d := by
  have : NeZero d := ⟨hd.ne'⟩
  rw [ArithmeticFunction.carmichael_eq_exponent']
  exact Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite

private noncomputable def midDivs (a L : ℝ) : Finset ℕ := by
  classical
  exact (Icc 1 ⌊a * L⌋₊).filter fun d => a < (d : ℝ)

private noncomputable def lowDivs (a L : ℝ) (m : ℕ) : Finset ℕ := by
  classical
  exact (midDivs a L).filter fun d => Squarefree d ∧ ArithmeticFunction.carmichael d = m

private theorem Icc_one_floor_card_le {x : ℝ} (hx : 0 ≤ x) :
    ((Icc 1 ⌊x⌋₊).card : ℝ) ≤ x := by
  simpa [Nat.card_Icc] using (Nat.floor_le hx)

private theorem midDivs_card_le {a L : ℝ} (ha : 0 ≤ a * L) :
    ((midDivs a L).card : ℝ) ≤ a * L := by
  classical
  apply le_trans _ (Icc_one_floor_card_le ha)
  exact_mod_cast Finset.card_filter_le ..

/-- Count four classes using the square root cutoff, large prime divisors and the two ranges of the Carmichael exponent. -/
private theorem finite_bound {x L : ℝ} (hx : 1 ≤ x) (hL : 16 ≤ L)
    (hL3 : L ^ 3 ≤ Real.sqrt x)
    (hD : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ L ^ 3 →
      ((lowDivs (Real.sqrt x) L m).card : ℝ) ≤ Real.sqrt x / L ^ 5) :
    Erdos1057.carmichaelCounting x ≤ 3 * x / L := by
  classical
  let N := ⌊x⌋₊
  let a := Real.sqrt x
  let B := ⌊L⌋₊
  have hX : 0 ≤ x := by linarith
  have hN : (N : ℝ) ≤ x := Nat.floor_le hX
  have ha : 1 ≤ a := Real.one_le_sqrt.mpr hx
  have ha0 : 0 < a := by linarith
  have ha2 : a ^ 2 = x := Real.sq_sqrt hX
  have hL0 : 0 < L := by linarith
  have hL2 : L ^ 2 ≤ a := by nlinarith [mul_nonneg (show 0 ≤ L - 1 by linarith) (sq_nonneg L)]
  have hLB : L / 2 ≤ B := by
    have h := Nat.lt_floor_add_one L
    change L < (B : ℝ) + 1 at h
    linarith
  have hB0 : 0 < B := by exact_mod_cast (show 0 < (B : ℝ) by linarith)
  have hAL : 0 ≤ a * L := by positivity
  let F := fun d => (carms N).filter fun n => d ∣ n
  let S₀ := Icc 1 ⌊a⌋₊
  let S₁ := carmsLarge N B
  let high := (midDivs a L).filter fun d => L ^ 3 ≤ (ArithmeticFunction.carmichael d : ℝ)
  let S₂ := high.biUnion F
  let smallLambda := Icc 1 ⌊L ^ 3⌋₊
  let S₃ := smallLambda.biUnion fun m => (lowDivs a L m).biUnion F
  have hcover : carms N ⊆ (S₀ ∪ S₁) ∪ (S₂ ∪ S₃) := by
    intro n hn
    obtain ⟨hcarm, _⟩ := mem_carms.mp hn
    by_cases hnle : (n : ℝ) ≤ a
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_Icc.mpr
        ⟨(carmichael_composite hcarm).2.le, (Nat.le_floor_iff ha0.le).mpr hnle⟩))))
    by_cases hlarge : n ∈ S₁
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr hlarge)))
    have hsmall (p : ℕ) (hp : p.Prime) (hpn : p ∣ n) : (p : ℝ) ≤ L := by
      apply (Nat.le_floor_iff hL0.le).mp
      by_contra! hBp
      exact hlarge (mem_filter.mpr ⟨hn, p, hp, hpn, hBp⟩)
    obtain ⟨d, hdn, had, hdL⟩ := exists_large_divisor ha (lt_of_not_ge hnle) hsmall
    have hdpos : 0 < d := by exact_mod_cast (show (0 : ℝ) < d from ha0.trans had)
    have hmid : d ∈ midDivs a L := mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hdpos, (Nat.le_floor_iff hAL).mpr hdL⟩, had⟩
    have hF : n ∈ F d := mem_filter.mpr ⟨hn, hdn⟩
    apply mem_union.mpr
    right
    by_cases hlargeD : L ^ 3 ≤ (ArithmeticFunction.carmichael d : ℝ)
    · exact mem_union.mpr (Or.inl (mem_biUnion.mpr ⟨d, mem_filter.mpr ⟨hmid, hlargeD⟩, hF⟩))
    · have hl : (ArithmeticFunction.carmichael d : ℝ) ≤ L ^ 3 := le_of_not_ge hlargeD
      have hm : ArithmeticFunction.carmichael d ∈ smallLambda := mem_Icc.mpr
        ⟨carmichael_pos hdpos, (Nat.le_floor_iff (by positivity)).mpr hl⟩
      have hd : d ∈ lowDivs a L (ArithmeticFunction.carmichael d) := mem_filter.mpr
        ⟨hmid, (carmichael_squarefree hcarm).squarefree_of_dvd hdn, rfl⟩
      exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨_, hm, mem_biUnion.mpr ⟨d, hd, hF⟩⟩))
  have h₀ : (S₀.card : ℝ) ≤ x / L ^ 2 := by
    apply (Icc_one_floor_card_le ha0.le).trans
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      a * L ^ 2 ≤ a * a := mul_le_mul_of_nonneg_left hL2 ha0.le
      _ = x := by rw [← pow_two, ha2]
  have h₁ : (S₁.card : ℝ) ≤ 2 * x / L := by
    apply (card_large_le hB0).trans
    have : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB0
    calc
      (N : ℝ) / B ≤ x / B := div_le_div_of_nonneg_right hN this.le
      _ ≤ x / (L / 2) := div_le_div_of_nonneg_left hX (by positivity) hLB
      _ = _ := by ring
  have h₂ : (S₂.card : ℝ) ≤ 2 * x / L ^ 2 := by
    have hH : (high.card : ℝ) ≤ a * L := by
      apply le_trans _ (midDivs_card_le hAL)
      exact_mod_cast Finset.card_filter_le ..
    have hF (d : ℕ) (hd : d ∈ high) : ((F d).card : ℝ) ≤ 1 + x / (a * L ^ 3) := by
      obtain ⟨hm, hC⟩ := mem_filter.mp hd
      have had := (mem_filter.mp hm).2
      have hle : a * L ^ 3 ≤ (d : ℝ) * ArithmeticFunction.carmichael d := by
        exact mul_le_mul had.le hC (by positivity) (by positivity)
      apply (card_fiber_carmichael_le (N := N) (d := d)).trans
      apply add_le_add_right
      calc
        (N : ℝ) / ((d : ℝ) * ArithmeticFunction.carmichael d) ≤
            x / ((d : ℝ) * ArithmeticFunction.carmichael d) :=
          div_le_div_of_nonneg_right hN (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left hX (by positivity) hle
    have hA : a * L ≤ x / L ^ 2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      calc
        a * L * L ^ 2 = a * L ^ 3 := by ring
        _ ≤ a * a := mul_le_mul_of_nonneg_left hL3 ha0.le
        _ = x := by rw [← pow_two, ha2]
    calc
      _ ≤ ∑ d ∈ high, (1 + x / (a * L ^ 3)) := card_biUnion_real_le high F _ hF
      _ = (high.card : ℝ) * (1 + x / (a * L ^ 3)) := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ (a * L) * (1 + x / (a * L ^ 3)) := mul_le_mul_of_nonneg_right hH (by positivity)
      _ = a * L + x / L ^ 2 := by field_simp
      _ ≤ x / L ^ 2 + x / L ^ 2 := add_le_add_left hA _
      _ = _ := by ring
  have h₃ : (S₃.card : ℝ) ≤ x / L ^ 2 := by
    have hM : (smallLambda.card : ℝ) ≤ L ^ 3 := Icc_one_floor_card_le (by positivity)
    have hF (m : ℕ) (hm : m ∈ smallLambda) :
        (((lowDivs a L m).biUnion F).card : ℝ) ≤ (a / L ^ 5) * (x / a) := by
      have hDe := hD m (mem_Icc.mp hm).1 ((Nat.le_floor_iff (by positivity)).mp (mem_Icc.mp hm).2)
      calc
        _ ≤ ∑ d ∈ lowDivs a L m, x / a := by
          apply card_biUnion_real_le
          intro d hd
          have had := (mem_filter.mp (mem_filter.mp hd).1).2
          calc
            _ ≤ (N : ℝ) / d := card_fiber_le
            _ ≤ x / d := div_le_div_of_nonneg_right hN (by positivity)
            _ ≤ _ := div_le_div_of_nonneg_left hX ha0 had.le
        _ = ((lowDivs a L m).card : ℝ) * (x / a) := by simp only [sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right hDe (by positivity)
    calc
      _ ≤ ∑ m ∈ smallLambda, (a / L ^ 5) * (x / a) := card_biUnion_real_le _ _ _ hF
      _ = (smallLambda.card : ℝ) * ((a / L ^ 5) * (x / a)) := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ L ^ 3 * ((a / L ^ 5) * (x / a)) := mul_le_mul_of_nonneg_right hM (by positivity)
      _ = _ := by field_simp
  have hcast : ((carms N).card : ℝ) ≤ (S₀.card : ℝ) + S₁.card + (S₂.card + S₃.card) := by
    have hncard : (carms N).card ≤ S₀.card + S₁.card + (S₂.card + S₃.card) := calc
      _ ≤ ((S₀ ∪ S₁) ∪ (S₂ ∪ S₃)).card := Finset.card_le_card hcover
      _ ≤ (S₀ ∪ S₁).card + (S₂ ∪ S₃).card := Finset.card_union_le (S₀ ∪ S₁) (S₂ ∪ S₃)
      _ ≤ _ := Nat.add_le_add (Finset.card_union_le S₀ S₁) (Finset.card_union_le S₂ S₃)
    exact_mod_cast hncard
  have hfin : 4 * (x / L ^ 2) ≤ x / L := by
    have h := mul_nonneg hX (show 0 ≤ L - 4 by linarith)
    apply (le_div_iff₀ hL0).mpr
    field_simp
    nlinarith
  rw [count_eq_card hX]
  change ((carms N).card : ℝ) ≤ 3 * x / L
  calc
    _ ≤ (S₀.card : ℝ) + S₁.card + (S₂.card + S₃.card) := hcast
    _ ≤ x / L ^ 2 + 2 * x / L + (2 * x / L ^ 2 + x / L ^ 2) :=
      add_le_add (add_le_add h₀ h₁) (add_le_add h₂ h₃)
    _ = 2 * (x / L) + 4 * (x / L ^ 2) := by ring
    _ ≤ 2 * (x / L) + x / L := add_le_add_right hfin _
    _ = _ := by ring


open Filter Finset Real ArithmeticFunction
open scoped Topology ArithmeticFunction.zeta

private theorem sum_rpow_squarefree_le_prod {D P : Finset ℕ} (s : ℝ)
    (hD : ∀ d ∈ D, Squarefree d ∧ d.primeFactors ⊆ P) :
    ∑ d ∈ D, (d : ℝ) ^ s ≤ ∏ p ∈ P, (1 + (p : ℝ) ^ s) := by
  classical
  rw [Finset.prod_one_add]
  let D' := D.image Nat.primeFactors
  have hsub : D' ⊆ P.powerset := by
    intro A hA
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hA
    exact mem_powerset.mpr (hD d hd).2
  have hinj : Set.InjOn Nat.primeFactors (D : Set ℕ) := by
    intro a ha b hb heq
    rw [← Nat.prod_primeFactors_of_squarefree (hD a ha).1, heq,
      Nat.prod_primeFactors_of_squarefree (hD b hb).1]
  calc
    _ = ∑ A ∈ D', ∏ p ∈ A, (p : ℝ) ^ s := by
      rw [Finset.sum_image hinj]
      refine sum_congr rfl fun d hd => ?_
      rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), ← Nat.cast_prod,
        Nat.prod_primeFactors_of_squarefree (hD d hd).1]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

private theorem prod_one_add_rpow_le_sum {P : Finset ℕ} {s : ℝ}
    (hp : ∀ p ∈ P, p.Prime) :
    ∏ p ∈ P, (1 + (p : ℝ) ^ s) ≤ ∑ n ∈ Icc 1 (∏ p ∈ P, p), (n : ℝ) ^ s := by
  classical
  let f := fun A : Finset ℕ => ∏ p ∈ A, p
  let S := P.powerset.image f
  have hf (A : Finset ℕ) (hA : A ⊆ P) : (f A).primeFactors = A :=
    Nat.primeFactors_prod fun p hp' => hp p (hA hp')
  have hinj : Set.InjOn f (P.powerset : Set (Finset ℕ)) := by
    intro A hA B hB heq
    rw [← hf A (mem_powerset.mp hA), heq, hf B (mem_powerset.mp hB)]
  have hsub : S ⊆ Icc 1 (∏ p ∈ P, p) := by
    intro n hn
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hn
    have hA' := mem_powerset.mp hA
    refine mem_Icc.mpr ⟨?_, Nat.le_of_dvd ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hA')⟩
    · exact Finset.prod_pos fun p hp' => (hp p (hA' hp')).pos
    · exact Finset.prod_pos fun p hp' => (hp p hp').pos
  rw [Finset.prod_one_add]
  calc
    _ = ∑ n ∈ S, (n : ℝ) ^ s := by
      rw [Finset.sum_image hinj]
      refine sum_congr rfl fun A hA => ?_
      rw [Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p), ← Nat.cast_prod]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

private theorem sum_Icc_rpow_le {N : ℕ} {s : ℝ} (hN : 1 ≤ N) (hs : 1 < s) :
    ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-s) ≤ 1 + 1 / (s - 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-s)
  have hanti : AntitoneOn f (Set.Icc (1 : ℝ) (N : ℝ)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
  have h := AntitoneOn.sum_le_integral_Ico hN (by simpa only [Nat.cast_one] using hanti)
  have hsum : (∑ n ∈ Icc 1 N, f n) = 1 + ∑ n ∈ Ico 1 N, f (n + 1) := by
    have hset : Icc 1 N = insert 1 ((Ico 1 N).image fun n => n + 1) := by
      ext n
      simp only [mem_Icc, mem_insert, mem_image, mem_Ico]
      constructor
      · intro hn
        by_cases he : n = 1
        · exact Or.inl he
        · exact Or.inr ⟨n - 1, by omega, by omega⟩
      · rintro (rfl | ⟨a, ha, rfl⟩) <;> omega
    rw [hset, sum_insert, sum_image (by intro a _ b _ he; simp only at he; omega)]
    · simp [f]
    · simp
  have hint : (∫ x in (1 : ℝ)..(N : ℝ), f x) ≤ 1 / (s - 1) := by
    have hi : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hN)]
      simp
    change (∫ x in (1 : ℝ)..(N : ℝ), x ^ (-s)) ≤ _
    rw [integral_rpow (r := -s) (Or.inr ⟨by linarith, hi⟩), Real.one_rpow]
    rw [show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (sub_le_self _ (by positivity))
      (by linarith)
  rw [show (∑ n ∈ Icc 1 N, (n : ℝ) ^ (-s)) = ∑ n ∈ Icc 1 N, f n from rfl, hsum]
  push_cast at h
  exact add_le_add_right (h.trans hint) 1

private theorem half_le_log_one_add {x : ℝ} (hx : 0 ≤ x) (h₁ : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have h₀ : 0 < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h₀)
  rw [Real.log_inv] at h
  have h' : x / (1 + x) ≤ Real.log (1 + x) := by
    have he : (1 + x)⁻¹ - 1 = -(x / (1 + x)) := by field_simp; ring
    rw [he] at h
    linarith
  exact (div_le_div_of_nonneg_left hx h₀ (by linarith)).trans h'

private theorem sum_prime_rpow_le {P : Finset ℕ} {s : ℝ}
    (hp : ∀ p ∈ P, p.Prime) (hs : 1 < s) :
    ∑ p ∈ P, (p : ℝ) ^ (-s) ≤ 2 * Real.log (1 + 1 / (s - 1)) := by
  have h1 : 1 ≤ ∏ p ∈ P, p := Finset.prod_pos fun p h => (hp p h).pos
  have hprod := (prod_one_add_rpow_le_sum (s := -s) hp).trans (sum_Icc_rpow_le h1 hs)
  have hpos (p : ℕ) : 0 < 1 + (p : ℝ) ^ (-s) := by positivity
  have hp0 : 0 < ∏ p ∈ P, (1 + (p : ℝ) ^ (-s)) := Finset.prod_pos fun p _ => hpos p
  have hlog := Real.log_le_log hp0 hprod
  rw [Real.log_prod (fun p _ => (hpos p).ne')] at hlog
  have hcomp := Finset.sum_le_sum (s := P) fun p h =>
    half_le_log_one_add (x := (p : ℝ) ^ (-s)) (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (hp p h).one_lt.le) (by linarith))
  simp_rw [div_eq_mul_inv, ← Finset.sum_mul] at hcomp
  linarith

/-- A finite Euler product gives the prime reciprocal bound needed for the split. -/
private theorem prime_reciprocal_bound {T : ℝ} (hT : 1 < T) :
    ∑ p ∈ Nat.primesLE ⌊T⌋₊, (p : ℝ)⁻¹ ≤
      (2 * Real.exp 1) * Real.log (1 + Real.log T) := by
  let u := Real.log T
  have hu : 0 < u := Real.log_pos hT
  let σ := 1 + 1 / u
  have hσ : 1 < σ := lt_add_of_pos_right _ (one_div_pos.mpr hu)
  have hp (p : ℕ) (h : p ∈ Nat.primesLE ⌊T⌋₊) : p.Prime := (Nat.mem_primesLE.mp h).2
  have hb := sum_prime_rpow_le (s := σ) hp hσ
  have heq : 1 / (σ - 1) = u := by simp [σ]
  rw [heq] at hb
  have hcomp : ∀ p ∈ Nat.primesLE ⌊T⌋₊, (p : ℝ)⁻¹ ≤ Real.exp 1 * (p : ℝ) ^ (-σ) := by
    intro p h
    have hpp : 0 < (p : ℝ) := by exact_mod_cast (hp p h).pos
    have hle : (p : ℝ) ≤ T := (Nat.le_floor_iff (by linarith : 0 ≤ T)).mp (Nat.mem_primesLE.mp h).1
    have hlog := Real.log_le_log hpp hle
    have hdiv : Real.log p / u ≤ 1 := (div_le_iff₀ hu).2 (by simpa [u] using hlog)
    rw [← Real.rpow_neg_one, Real.rpow_def_of_pos hpp, Real.rpow_def_of_pos hpp,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [σ]
    linarith [show Real.log p * (1 / u) ≤ 1 by simpa [div_eq_mul_inv, one_mul] using hdiv]
  calc
    _ ≤ ∑ p ∈ Nat.primesLE ⌊T⌋₊, Real.exp 1 * (p : ℝ) ^ (-σ) := sum_le_sum hcomp
    _ ≤ _ := by rw [← Finset.mul_sum]; nlinarith [Real.exp_pos 1]

/-- Bound the divisor sum by geometric series over the prime powers in the factorization. -/
private theorem divisor_rpow_sum_le {m : ℕ} (hm : m ≠ 0) {s : ℝ} (hs : 1 / 2 ≤ s) :
    ∑ d ∈ m.divisors, (d : ℝ) ^ (-s) ≤
      Real.exp (4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s)) := by
  let w : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ) ^ (-s), by simp [Real.zero_rpow,
    show -s ≠ 0 by linarith]⟩
  have hw : w.IsMultiplicative := by
    constructor
    · simp [w]
    · intro a b _
      change ((↑(a * b) : ℝ) ^ (-s)) = _
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
      rfl
  let g := (↑ζ : ArithmeticFunction ℝ) * w
  have hg : g.IsMultiplicative := (ArithmeticFunction.isMultiplicative_zeta.natCast).mul hw
  have hprod := ArithmeticFunction.IsMultiplicative.multiplicative_factorization g hg hm
  rw [Nat.prod_factorization_eq_prod_primeFactors] at hprod
  change ((↑ζ : ArithmeticFunction ℝ) * w) m = _ at hprod
  rw [ArithmeticFunction.coe_zeta_mul_apply] at hprod
  change (∑ d ∈ m.divisors, (d : ℝ) ^ (-s)) = _ at hprod
  rw [hprod, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · change 0 ≤ ((↑ζ : ArithmeticFunction ℝ) * w) (p ^ m.factorization p)
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    exact sum_nonneg (fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _)
  · have hpp := Nat.prime_of_mem_primeFactors hp
    let v : ℝ := (p : ℝ) ^ (-s)
    have hv : 0 ≤ v := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hv34 : v ≤ 3 / 4 := by
      have hTwoP : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      have h₁ : v ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) :=
        (Real.rpow_le_rpow_of_nonpos zero_lt_two hTwoP (by linarith)).trans
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
      refine h₁.trans ?_
      rw [Real.rpow_neg zero_le_two, ← Real.sqrt_eq_rpow]
      have hpos : 0 < Real.sqrt 2 := by positivity
      rw [← one_div, div_le_iff₀ hpos]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hv1 : v < 1 := by linarith
    have hvsum : (∑ j ∈ range (m.factorization p + 1), v ^ j) ≤ (1 - v)⁻¹ := by
      have hsumm := summable_geometric_of_lt_one hv hv1
      rw [← tsum_geometric_of_lt_one hv hv1]
      exact hsumm.sum_le_tsum _ (fun _ _ => by positivity)
    have hgeom : (1 - v)⁻¹ ≤ 1 + 4 * v := by
      rw [← one_div, div_le_iff₀ (by linarith : 0 < 1 - v)]
      nlinarith [mul_nonneg hv (show 0 ≤ 3 - 4 * v by linarith)]
    change ((↑ζ : ArithmeticFunction ℝ) * w) (p ^ m.factorization p) ≤ _
    rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hpp]
    have he : (∑ i ∈ range (m.factorization p + 1), w (p ^ i)) =
        ∑ i ∈ range (m.factorization p + 1), v ^ i := by
      refine sum_congr rfl fun i _ => ?_
      change ((↑(p ^ i) : ℝ) ^ (-s)) = _
      rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) i,
        ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm, Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    rw [he]
    exact hvsum.trans (hgeom.trans (by simpa only [add_comm] using Real.add_one_le_exp (4 * v)))

private noncomputable def allowedPrimes (m : ℕ) : Finset ℕ :=
  (m.divisors.image (fun d : ℕ => d + 1)).filter Nat.Prime

private theorem sum_allowedPrimes_le {m : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    ∑ p ∈ allowedPrimes m, (p : ℝ) ^ (-s) ≤ ∑ d ∈ m.divisors, (d : ℝ) ^ (-s) := by
  calc
    _ ≤ ∑ p ∈ m.divisors.image (fun d : ℕ => d + 1), (p : ℝ) ^ (-s) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset (s := m.divisors.image (fun d : ℕ => d + 1)) Nat.Prime) fun _ _ _ => by positivity
    _ = ∑ d ∈ m.divisors, ((d + 1 : ℕ) : ℝ) ^ (-s) :=
      sum_image (fun _ _ _ _ h => by omega)
    _ ≤ _ := sum_le_sum fun d hd => Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast Nat.pos_of_mem_divisors hd) (by exact_mod_cast Nat.le_succ d) (by linarith)

/-- The Rankin bound for squarefree divisors with a fixed Carmichael exponent. -/
private theorem card_rankin {D : Finset ℕ} {m : ℕ} {Y s : ℝ}
    (hm : m ≠ 0) (hs : 1 / 2 ≤ s) (hY : 0 < Y)
    (hD : ∀ d ∈ D, Squarefree d ∧ (d : ℝ) ≤ Y ∧ d.primeFactors ⊆ allowedPrimes m) :
    (D.card : ℝ) ≤ Y ^ s * Real.exp (Real.exp (4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s))) := by
  have hterm (d : ℕ) (hd : d ∈ D) : 1 ≤ Y ^ s * (d : ℝ) ^ (-s) := by
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (hD d hd).1.ne_zero
    have hle := Real.rpow_le_rpow hd0.le (hD d hd).2.1 (show 0 ≤ s by linarith)
    have he : (d : ℝ) ^ s * (d : ℝ) ^ (-s) = 1 := by
      rw [← Real.rpow_add hd0, add_neg_cancel, Real.rpow_zero]
    rw [← he]
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  calc
    _ = ∑ _d ∈ D, (1 : ℝ) := by simp
    _ ≤ ∑ d ∈ D, Y ^ s * (d : ℝ) ^ (-s) := sum_le_sum hterm
    _ = Y ^ s * ∑ d ∈ D, (d : ℝ) ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (sum_rpow_squarefree_le_prod (-s) fun d hd => ⟨(hD d hd).1, (hD d hd).2.2⟩).trans
        ((Real.prod_one_add_le_exp_sum _ fun p => by positivity).trans
          (Real.exp_le_exp.mpr ((sum_allowedPrimes_le (show 0 ≤ s by linarith)).trans
            (divisor_rpow_sum_le hm hs))))

private theorem primeFactors_card_log_le {m : ℕ} (hm : 0 < m) :
    (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log m := by
  have hprod : 2 ^ m.primeFactors.card ≤ m := by
    calc
      _ = ∏ _p ∈ m.primeFactors, (2 : ℕ) := by simp
      _ ≤ ∏ p ∈ m.primeFactors, p := Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have hx : (2 : ℝ) ^ m.primeFactors.card ≤ m := by exact_mod_cast hprod
  have h := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ m.primeFactors.card) hx
  simpa only [Real.log_pow, mul_comm (Real.log 2)] using h

/-- Split the prime divisors at the cutoff and bound the large-prime part by their number. -/
private theorem sum_primeFactors_rpow_le {m : ℕ} {T s : ℝ}
    (hT : 1 < T) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hc : (m.primeFactors.card : ℝ) ≤ T) :
    ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s) ≤
      ((2 * Real.exp 1) * Real.log (1 + Real.log T) + 1) * Real.exp ((1 - s) * Real.log T) := by
  classical
  let P := m.primeFactors
  let E := Real.exp ((1 - s) * Real.log T)
  have hE : 0 ≤ E := Real.exp_nonneg _
  let small := P.filter (fun p : ℕ => (p : ℝ) ≤ T)
  let large := P.filter (fun p : ℕ => ¬(p : ℝ) ≤ T)
  have hT0 : 0 < T := by linarith
  have hsmall : ∑ p ∈ small, (p : ℝ) ^ (-s) ≤
      ((2 * Real.exp 1) * Real.log (1 + Real.log T)) * E := by
    have hsub : small ⊆ Nat.primesLE ⌊T⌋₊ := by
      intro p hp
      obtain ⟨hp, hpT⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hT0.le).mpr hpT, Nat.prime_of_mem_primeFactors hp⟩
    have hterm (p : ℕ) (hp : p ∈ small) : (p : ℝ) ^ (-s) ≤ (p : ℝ)⁻¹ * E := by
      obtain ⟨hp, hpT⟩ := mem_filter.mp hp
      have hpp : (0 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
      have he : (p : ℝ) ^ (-s) = ((p : ℝ) ^ (-1 : ℝ)) * ((p : ℝ) ^ (1 - s)) := by
        rw [← Real.rpow_add hpp]
        congr 1
        ring
      rw [he, Real.rpow_neg_one]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have he' : T ^ (1 - s) = E := by
        rw [Real.rpow_def_of_pos hT0]
        simp only [E, mul_comm (Real.log T)]
      rw [← he']
      exact Real.rpow_le_rpow hpp.le hpT (by linarith)
    calc
      _ ≤ ∑ p ∈ small, (p : ℝ)⁻¹ * E := sum_le_sum hterm
      _ = (∑ p ∈ small, (p : ℝ)⁻¹) * E := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)).trans
          (prime_reciprocal_bound hT)) hE
  have hlarge : ∑ p ∈ large, (p : ℝ) ^ (-s) ≤ E := by
    have hcard : (large.card : ℝ) ≤ (P.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le (s := P) ..
    have hc' : (large.card : ℝ) ≤ T := hcard.trans hc
    calc
      _ ≤ ∑ _p ∈ large, T ^ (-s) := sum_le_sum fun p hp =>
        Real.rpow_le_rpow_of_nonpos hT0 (le_of_not_ge (mem_filter.mp hp).2) (by linarith)
      _ = (large.card : ℝ) * T ^ (-s) := by simp [nsmul_eq_mul]
      _ ≤ T * T ^ (-s) := mul_le_mul_of_nonneg_right hc' (by positivity)
      _ = E := by
        calc
          T * T ^ (-s) = T ^ (1 : ℝ) * T ^ (-s) := by rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hT0, Real.rpow_def_of_pos hT0]; dsimp [E]; congr 1; ring
  have hsplit : ∑ p ∈ small, (p : ℝ) ^ (-s) + ∑ p ∈ large, (p : ℝ) ^ (-s) =
      ∑ p ∈ P, (p : ℝ) ^ (-s) := Finset.sum_filter_add_sum_filter_not P _ _
  rw [← hsplit, add_mul, one_mul]
  exact add_le_add hsmall hlarge

section

open scoped Asymptotics

private theorem eventually_log_le_rpow {r : ℝ} (hr : 0 < r) :
    ∀ᶠ u in atTop, Real.log u ≤ u ^ r := by
  filter_upwards [(isLittleO_log_rpow_atTop hr).bound one_pos,
    eventually_ge_atTop (0 : ℝ)] with u hu hu0
  have hpow : 0 ≤ u ^ r := Real.rpow_nonneg hu0 _
  change ‖Real.log u‖ ≤ 1 * ‖u ^ r‖ at hu
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg hpow] using hu)

private theorem rankin_parameters : ∀ᶠ t : ℝ in atTop,
    let u := Real.log t
    let v := Real.log u
    let ell := t * v / (1000 * u)
    let s := 1 - v / (8 * u)
    1 / 2 ≤ s ∧ Real.log 16 ≤ ell ∧ 3 * ell ≤ t / 2 ∧
      (∀ m : ℕ, 0 < m → (m : ℝ) ≤ (Real.exp ell) ^ 3 →
        Real.exp (Real.exp (4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s))) ≤ Real.exp ell) ∧
      (Real.exp (t / 2) * Real.exp ell) ^ s ≤ Real.exp (t / 2) / (Real.exp ell) ^ 6 := by
  let C := 4 * Real.exp 1 + 1
  have htQuarter := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 1000
  have htHalf := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop (Real.log 16)
  have huPow := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 8)).comp
    Real.tendsto_log_atTop).eventually_ge_atTop (8 * C)
  have huLog := Real.tendsto_log_atTop.eventually (eventually_log_le_rpow (by norm_num : (0 : ℝ) < 1 / 4))
  have huOne := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hvOne := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_gt_atTop (1 : ℝ), htQuarter, htHalf, huPow, huLog, huOne,
    hvOne, eventually_log_le_rpow (by norm_num : (0 : ℝ) < 1 / 4)] with
    t ht htq hth hup hul hu1 hv1 htl
  let u := Real.log t
  let v := Real.log u
  let ell := t * v / (1000 * u)
  let s := 1 - v / (8 * u)
  change 1 / 2 ≤ s ∧ Real.log 16 ≤ ell ∧ 3 * ell ≤ t / 2 ∧ _ ∧ _
  change 1 ≤ u at hu1
  change 1 ≤ v at hv1
  change v ≤ u ^ (1 / 4 : ℝ) at hul
  change 8 * C ≤ u ^ (5 / 8 : ℝ) at hup
  change u ≤ t ^ (1 / 4 : ℝ) at htl
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hvu : v ≤ u := (Real.log_le_sub_one_of_pos hu0).trans (by linarith)
  have hdiv : 0 ≤ v / (8 * u) := by positivity
  have hdiv' : v / (8 * u) ≤ 1 / 8 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hs : 1 / 2 ≤ s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; linarith
  have hell : t ^ (1 / 2 : ℝ) ≤ ell := by
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      t ^ (1 / 2 : ℝ) * (1000 * u) ≤ t ^ (1 / 2 : ℝ) * (t ^ (1 / 4 : ℝ) * t ^ (1 / 4 : ℝ)) := by
        gcongr
      _ = t := by
        rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
        norm_num
      _ ≤ t * v := by nlinarith
  have hell0 : 0 ≤ ell := (by positivity : 0 ≤ t ^ (1 / 2 : ℝ)).trans hell
  have hell3 : 3 * ell ≤ t / 2 := by
    have hb : ell ≤ t / 1000 := by
      apply (div_le_iff₀ (by positivity : 0 < 1000 * u)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hvu ht0.le]
    linarith
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := half_le_log_one_add (x := 1) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  refine ⟨hs, hth.trans hell, hell3, ?_, ?_⟩
  · intro m hm hM
    have hmc : (m.primeFactors.card : ℝ) ≤ t := by
      apply le_of_mul_le_mul_right _ (by linarith : 0 < Real.log 2)
      calc
        (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log m := primeFactors_card_log_le hm
        _ ≤ Real.log ((Real.exp ell) ^ 3) := Real.log_le_log (by exact_mod_cast hm) hM
        _ = 3 * ell := by rw [Real.log_pow, Real.log_exp]; norm_num
        _ ≤ _ := hell3.trans (by nlinarith [mul_le_mul_of_nonneg_left hlogtwo ht0.le])
    have hbound := sum_primeFactors_rpow_le (m := m) ht (by linarith) hs1 hmc
    have huq : 1 ≤ u ^ (1 / 4 : ℝ) := Real.one_le_rpow hu1 (by norm_num)
    have hlog : Real.log (1 + u) ≤ 2 * u ^ (1 / 4 : ℝ) := by
      calc
        Real.log (1 + u) ≤ Real.log (2 * u) := Real.log_le_log (by positivity) (by linarith)
        _ = Real.log 2 + v := by rw [Real.log_mul (by norm_num) hu0.ne']
        _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hExp : Real.exp ((1 - s) * u) = u ^ (1 / 8 : ℝ) := by
      rw [Real.rpow_def_of_pos hu0]
      congr 1
      change (1 - s) * u = v * (1 / 8)
      dsimp [s]
      field_simp; ring
    have hK : (2 * Real.exp 1) * Real.log (1 + u) + 1 ≤ C * u ^ (1 / 4 : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * Real.exp 1 by positivity)
      dsimp [C]
      linarith
    have hpow : (8 * C) * u ^ (3 / 8 : ℝ) ≤ u := by
      calc
        _ ≤ u ^ (5 / 8 : ℝ) * u ^ (3 / 8 : ℝ) := mul_le_mul_of_nonneg_right hup (by positivity)
        _ = _ := by rw [← Real.rpow_add hu0]; norm_num
    have hsum : 4 * (∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s)) ≤ u / 2 := by
      change (∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s)) ≤
        ((2 * Real.exp 1) * Real.log (1 + u) + 1) * Real.exp ((1 - s) * u) at hbound
      rw [hExp] at hbound
      have hprod := hbound.trans (mul_le_mul_of_nonneg_right hK (show 0 ≤ u ^ (1 / 8 : ℝ) by positivity))
      rw [mul_assoc, ← Real.rpow_add hu0, show (1 / 4 + 1 / 8 : ℝ) = 3 / 8 by norm_num] at hprod
      linarith
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr hsum
      _ = t ^ (1 / 2 : ℝ) := by rw [Real.rpow_def_of_pos ht0]; congr 1; dsimp [u]; ring
      _ ≤ _ := hell
  · rw [← Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      ← Real.exp_nat_mul, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have h : (1 - s) * t = 125 * ell := by
      dsimp [s, ell]
      field_simp; ring
    nlinarith [mul_nonneg (show 0 ≤ 1 - s by linarith) hell0]

end

private theorem lowDivs_count {x L s : ℝ} (hx : 1 ≤ x) (hL : 0 < L)
    (hs : 1 / 2 ≤ s) (hpow : (Real.sqrt x * L) ^ s ≤ Real.sqrt x / L ^ 6)
    (hB : ∀ m : ℕ, 0 < m → (m : ℝ) ≤ L ^ 3 →
      Real.exp (Real.exp (4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s))) ≤ L)
    (m : ℕ) (hm : 0 < m) (hmL : (m : ℝ) ≤ L ^ 3) :
    ((lowDivs (Real.sqrt x) L m).card : ℝ) ≤ Real.sqrt x / L ^ 5 := by
  classical
  have ha : 0 < Real.sqrt x := by positivity
  have hY : 0 < Real.sqrt x * L := by positivity
  have hD (d : ℕ) (hd : d ∈ lowDivs (Real.sqrt x) L m) :
      Squarefree d ∧ (d : ℝ) ≤ Real.sqrt x * L ∧ d.primeFactors ⊆ allowedPrimes m := by
    obtain ⟨hd, hsqd, hLambda⟩ := mem_filter.mp hd
    have hle := (mem_Icc.mp (mem_filter.mp hd).1).2
    refine ⟨hsqd, (Nat.le_floor_iff hY.le).mp hle, ?_⟩
    intro p hp
    obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hdiv : p - 1 ∣ m := by
      rw [← hLambda, ← carmichael_prime hp]
      exact ArithmeticFunction.carmichael_dvd hpd
    exact mem_filter.mpr ⟨mem_image.mpr ⟨p - 1, Nat.mem_divisors.mpr ⟨hdiv, hm.ne'⟩,
      Nat.sub_add_cancel hp.one_lt.le⟩, hp⟩
  calc
    _ ≤ (Real.sqrt x * L) ^ s * Real.exp (Real.exp (4 * ∑ p ∈ m.primeFactors, (p : ℝ) ^ (-s))) :=
      card_rankin hm.ne' hs hY hD
    _ ≤ (Real.sqrt x / L ^ 6) * L := mul_le_mul hpow (hB m hm hmL) (by positivity) (by positivity)
    _ = _ := by field_simp

end CarmichaelCount

open Filter Real

/-- Erdős's upper bound for the number of Carmichael numbers, using the counting split and
Rankin method described by Pomerance. -/
theorem OMA.solution : type_of% @Erdos1057.erdos_1057.variants.upper_bound := by
  refine ⟨1 / 2000, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
    Real.tendsto_log_atTop.eventually CarmichaelCount.rankin_parameters] with x hx hu h
  let t := Real.log x
  let u := Real.log t
  let v := Real.log u
  let ell := t * v / (1000 * u)
  let L := Real.exp ell
  let s := 1 - v / (8 * u)
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := Real.exp_pos ell
  change 1 / 2 ≤ s ∧ Real.log 16 ≤ ell ∧ 3 * ell ≤ t / 2 ∧ _ ∧ _ at h
  obtain ⟨hs, hel, hel3, hB, hpow⟩ := h
  have hL : 16 ≤ L := by
    have h := Real.exp_le_exp.mpr hel
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 16)] using h
  have hA : Real.exp (t / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    congr 1
    dsimp [t]
    ring
  have hL3 : L ^ 3 ≤ Real.sqrt x := by
    rw [← hA]
    dsimp [L]
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by exact_mod_cast hel3)
  change (Real.exp (t / 2) * L) ^ s ≤ Real.exp (t / 2) / L ^ 6 at hpow
  rw [hA] at hpow
  have hcc := CarmichaelCount.finite_bound hx hL hL3
    (CarmichaelCount.lowDivs_count hx hL0 hs hpow hB)
  have hlogu : 0 < u := hu
  have hexp : Real.exp (ell / 2) ^ 2 = L := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hgt : 3 < Real.exp (ell / 2) := by
    by_contra! hle
    have hsq : Real.exp (ell / 2) ^ 2 ≤ (3 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hle 2
    rw [hexp] at hsq
    linarith
  have hf : 3 * x / L < x * Real.exp (-ell / 2) := by
    apply (div_lt_iff₀ hL0).mpr
    have he : Real.exp (-ell / 2) * L = Real.exp (ell / 2) := by
      dsimp [L]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, he]
    simpa only [mul_comm (3 : ℝ) x] using mul_lt_mul_of_pos_left hgt hx0
  refine hcc.trans_lt (hf.trans_eq ?_)
  congr 2
  dsimp [ell, t, u, v]
  have hn : Real.log (Real.log x) ≠ 0 := hlogu.ne'
  field_simp; ring
