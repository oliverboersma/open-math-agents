import FormalConjectures.ErdosProblems.«979»
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Chebyshev

/-! The number of representations as a sum of two prime squares is unbounded. Formalization of Paul Erdős, On the sum and difference of squares of primes, Journal of the London Mathematical Society 12 (1937), §2, with explicit quantitative split-prime supply and a Chinese remainder count. -/

/-! # A polynomial supply of split primes from a short interval of quadratic values -/

namespace OMA.PrimeSupply1085
open Finset

private abbrev arg (X i : ℕ) := 2*(X+i)
private abbrev norm (X i : ℕ) := (arg X i)^2+1

private theorem root_mod {X i p e : ℕ} (he : 0 < e) (h : p^e ∣ norm X i) :
    (arg X i : ZMod p)^2 = -1 := by
  have hdiv : p ∣ norm X i := (dvd_pow_self p he.ne').trans h
  have eq := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  simpa only [norm, Nat.cast_add, Nat.cast_pow, Nat.cast_one, add_eq_zero_iff_eq_neg] using eq

/-- Two roots of the same sign modulo p are congruent modulo the
whole prime power. The other factor in the difference of squares is
nonzero modulo the odd prime p. -/
private theorem same_root {X p e i j : ℕ} (hp : p.Prime) (hn : p ≠ 2) (he : 0 < e)
    (hi : p^e ∣ norm X i) (hj : p^e ∣ norm X j)
    (hs : (arg X i : ZMod p) = arg X j) : i % p^e = j % p^e := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp2 : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h => hn ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hr := root_mod he hi
  have hnr : (arg X i : ZMod p) ≠ 0 := by
    intro h; simp [h] at hr
  have hc : ¬ (p : ℤ) ∣ 2*((arg X i : ℤ) + (arg X j : ℤ)) := by
    intro h
    have eq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_add, Int.cast_natCast] at eq
    rw [← hs, ← two_mul] at eq
    exact (mul_ne_zero hp2 (mul_ne_zero hp2 hnr)) eq
  have hdi : (p:ℤ)^e ∣ (norm X i : ℤ) := by exact_mod_cast hi
  have hdj : (p:ℤ)^e ∣ (norm X j : ℤ) := by exact_mod_cast hj
  have hd : (p:ℤ)^e ∣ ((j:ℤ)-i)*(2*((arg X i:ℤ)+(arg X j:ℤ))) := by
    rw [show ((j:ℤ)-i)*(2*((arg X i:ℤ)+(arg X j:ℤ))) =
      (norm X j:ℤ)-(norm X i:ℤ) by simp only [norm,arg]; push_cast; ring]
    exact dvd_sub hdj hdi
  have diff := (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_right e hc hd
  have hmod := (ZMod.intCast_eq_intCast_iff_dvd_sub (i:ℤ) (j:ℤ) (p^e)).mpr
    (by exact_mod_cast diff)
  exact (ZMod.natCast_eq_natCast_iff' i j (p^e)).mp (by simpa using hmod)

private theorem root_count (X L p e : ℕ) (hp : p.Prime) (hn : p ≠ 2) (he : 0 < e) :
    ((range L).filter (fun i => p^e ∣ norm X i)).card ≤ 2*(L/(p^e)+1) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let A := (range L).filter (fun i => p^e ∣ norm X i)
  change A.card ≤ _
  by_cases hempty : A.Nonempty
  · obtain ⟨j,hj⟩ := hempty
    let z := (arg X j : ZMod p)
    let S : Finset (ZMod p) := {z,-z}
    let f (i : ℕ) := (i/(p^e), (arg X i : ZMod p))
    have hjroot := root_mod he (mem_filter.mp hj).2
    have hmem (i : ℕ) (hi : i ∈ A) : f i ∈ (range (L/(p^e)+1)).product S := by
      have hmod := root_mod he (mem_filter.mp hi).2
      obtain h|h := sq_eq_sq_iff_eq_or_eq_neg.mp (hmod.trans hjroot.symm)
      all_goals
        refine mem_product.mpr ⟨mem_range.mpr ?_,?_⟩
        · exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (mem_filter.mp hi).1).le)
        · simpa [f,S,z] using (show (arg X i : ZMod p) = arg X j ∨
              (arg X i : ZMod p) = - (arg X j : ZMod p) from by tauto)
    have hc := card_le_card_of_injOn f hmem (by
      intro i hi i' hi' eq
      have heq : i/(p^e) = i'/(p^e) := congrArg Prod.fst eq
      have hcong := same_root hp hn he (mem_filter.mp hi).2 (mem_filter.mp hi').2
        (congrArg Prod.snd eq)
      have h1 := Nat.mod_add_div i (p^e)
      have h2 := Nat.mod_add_div i' (p^e)
      rw [hcong,heq] at h1
      omega)
    have hs : S.card ≤ 2 := card_le_two
    have hc' : A.card ≤ (range (L/p^e+1)).card*S.card :=
      hc.trans_eq (Finset.card_product _ _)
    rw [card_range] at hc'
    simpa [mul_comm] using hc'.trans (Nat.mul_le_mul_left _ hs)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hempty]

private theorem val_product (X L M p : ℕ) (hp : p.Prime) (hn : p ≠ 2) (hLM : L ≤ M)
    (hb : ∀ i ∈ range L, norm X i ≤ M) :
    (∏ i ∈ range L, norm X i).factorization p ≤ 2*L.factorial.factorization p + 2*Nat.log p M := by
  classical
  let E := Ico 1 (Nat.log p M+1)
  have heq (i : ℕ) (hi : i ∈ range L) :
      (norm X i).factorization p = (E.filter (fun e => p^e ∣ norm X i)).card :=
    Nat.factorization_eq_card_pow_dvd_of_lt hp (Nat.zero_lt_succ _)
      ((hb _ hi).trans_lt (Nat.lt_pow_succ_log_self hp.one_lt _))
  have hsum : (∑ i ∈ range L, (norm X i).factorization p) =
      ∑ e ∈ E, ((range L).filter (fun i => p^e ∣ norm X i)).card := by
    calc
      _ = ∑ i ∈ range L, (E.filter (fun e => p^e ∣ norm X i)).card := sum_congr rfl heq
      _ = _ := by simp only [Finset.card_filter]; rw [sum_comm]
  rw [Nat.factorization_prod (fun _ _ => Nat.succ_ne_zero _), Finsupp.finsetSum_apply, hsum]
  have hfac : L.factorial.factorization p = ∑ e ∈ E, L/p^e :=
    Nat.factorization_factorial hp (lt_of_le_of_lt (Nat.log_mono_right hLM) (Nat.lt_succ_self _))
  calc
    _ ≤ ∑ e ∈ E, 2*(L/p^e+1) := sum_le_sum (fun e h => root_count _ _ _ _ hp hn (mem_Ico.mp h).1)
    _ = _ := by simp [mul_add,sum_add_distrib,← mul_sum,← hfac,E,Nat.card_Ico,mul_comm (Nat.log p M) 2]

private theorem part_prod_le (S : Finset ℕ) (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ S, p^n.factorization p ≤ n := by
  classical
  let T := S ∩ n.primeFactors
  have h : ∏ p ∈ T, p^n.factorization p = ∏ p ∈ S, p^n.factorization p := by
    apply prod_subset inter_subset_left
    intro p hp hpt
    have hpn : p ∉ n.primeFactors := fun h => hpt (mem_inter.mpr ⟨hp,h⟩)
    have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp
      (show p ∉ n.factorization.support by simpa using hpn)
    simp [hz]
  rw [← h]
  refine (Finset.prod_le_prod_of_subset_of_one_le' (show T ⊆ n.primeFactors from inter_subset_right)
    (fun p hp _ => Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors hp).pos)).trans_eq
    (Nat.prod_primeFactors_pow_factorization hn).symm

private theorem factor_exists {X L p : ℕ} (hp : p.Prime) (h : p ∣ ∏ i ∈ range L, norm X i) :
    ∃ i ∈ range L, p ∣ norm X i :=
  (hp.prime.dvd_finsetProd_iff _).mp h

private theorem number_bound (X L M : ℕ) (hLM : L ≤ M) (hM : M ≠ 0)
    (hb : ∀ i ∈ range L, norm X i ≤ M) :
    let W := ∏ i ∈ range L, norm X i
    W ≤ L.factorial ^ 2 * M ^ (2*W.primeFactors.card) := by
  classical
  let W := ∏ i ∈ range L, norm X i
  have hW : W ≠ 0 := prod_ne_zero_iff.mpr (fun _ _ => Nat.succ_ne_zero _)
  have wp (p : ℕ) (hpp : p ∈ W.primeFactors) :
      p^W.factorization p ≤ (p^L.factorial.factorization p)^2*M^2 := by
    have hp := Nat.prime_of_mem_primeFactors hpp
    have hn : p ≠ 2 := by
      rintro rfl
      obtain ⟨i,_,hd⟩ := factor_exists hp (Nat.dvd_of_mem_primeFactors hpp)
      have hv : norm X i % 2 = 1 := by simp [norm,arg,Nat.add_mod,Nat.pow_mod]
      have := Nat.mod_eq_zero_of_dvd hd
      omega
    have hval := val_product X L M p hp hn hLM hb
    calc
      _ ≤ p^(2*L.factorial.factorization p+2*Nat.log p M) :=
        Nat.pow_le_pow_right hp.pos hval
      _ = (p^L.factorial.factorization p)^2*(p^Nat.log p M)^2 := by
        rw [pow_add, ← pow_mul, ← pow_mul, mul_comm 2 (L.factorial.factorization p),
          mul_comm 2 (Nat.log p M)]
      _ ≤ _ := by gcongr; exact Nat.pow_log_le_self _ hM
  change W ≤ _
  calc
    W = ∏ p ∈ W.primeFactors, p^W.factorization p := Nat.prod_primeFactors_pow_factorization hW
    _ ≤ ∏ p ∈ W.primeFactors, ((p^L.factorial.factorization p)^2*M^2) := Finset.prod_le_prod' wp
    _ = (∏ p ∈ W.primeFactors, p^L.factorial.factorization p)^2 * M^(2*W.primeFactors.card) := by
      rw [prod_mul_distrib,prod_pow,prod_const,pow_mul]
    _ ≤ _ := by gcongr; exact part_prod_le _ _ L.factorial_ne_zero

/-- At least k different split primes occur among the quadratic values
at 8k consecutive even inputs near 2k⁴. -/
theorem prime_supply (k : ℕ) (hk : 8 ≤ k) : ∃ S : Finset ℕ, S.card = k ∧
    ∀ p ∈ S, p.Prime ∧ p % 4 = 1 ∧ p ≤ k^10 ∧ ∃ i ≤ k^5, p ∣ i^2+1 := by
  classical
  let X := k^4
  let L := 8*k
  let M := k^10
  let W := ∏ i ∈ range L, norm X i
  have hkpos : 0 < k := by omega
  have hW : W ≠ 0 := prod_ne_zero_iff.mpr (fun _ _ => Nat.succ_ne_zero _)
  have hLk : L ≤ k^2 := by
    calc L ≤ k*k := Nat.mul_le_mul_right k hk
         _ = _ := by ring
  have hLX : L ≤ X := hLk.trans (Nat.pow_le_pow_right hkpos (by decide : 2 ≤ 4))
  have hLM : L ≤ M := hLk.trans (Nat.pow_le_pow_right hkpos (by decide : 2 ≤ 10))
  have hu (i : ℕ) (hi : i ∈ range L) : arg X i < k^5 := by
    have hi' := mem_range.mp hi
    calc arg X i < 4*X := by dsimp [arg]; omega
         _ ≤ k*X := Nat.mul_le_mul_right _ (by omega)
         _ = _ := by dsimp [X]; ring
  have hbounds (i : ℕ) (hi : i ∈ range L) : norm X i ≤ M := by
    have hsq := Nat.pow_lt_pow_left (hu i hi) (by decide : 2≠0)
    change (arg X i)^2+1 ≤ k^10
    calc _ ≤ (k^5)^2 := hsq
         _ = _ := by ring
  have hLpow : L.factorial ≤ k^(2*L) := by
    calc L.factorial ≤ L^L := Nat.factorial_le_pow _
         _ ≤ (k^2)^L := Nat.pow_le_pow_left hLk _
         _ = _ := (pow_mul _ _ _).symm
  have hlow : k^(8*L) ≤ W := by
    calc k^(8*L) = ∏ i ∈ range L, k^8 := by simp [pow_mul]
         _ ≤ W := by
           apply Finset.prod_le_prod'
           intro i _
           change k^8 ≤ (2*(k^4+i))^2+1
           nlinarith [Nat.zero_le (k^4*i), Nat.zero_le (i^2)]
  have hcount : k ≤ W.primeFactors.card := by
    by_contra! h
    have hbound := number_bound X L M hLM (pow_ne_zero _ hkpos.ne') hbounds
    change W ≤ L.factorial^2 * M^(2*W.primeFactors.card) at hbound
    have high : W ≤ k^(4*L+20*k) := by
      calc W ≤ _ := hbound
           _ ≤ (k^(2*L))^2*(k^10)^(2*k) := by
             apply Nat.mul_le_mul (Nat.pow_le_pow_left hLpow 2)
             exact Nat.pow_le_pow_right (pow_pos hkpos _) (by omega)
           _ = _ := by rw [← pow_mul,← pow_mul,← pow_add]; congr 1; ring
    exact (Nat.pow_lt_pow_right (show 1<k by omega)
      (show 4*L+20*k < 8*L by dsimp [L]; omega)).not_ge (hlow.trans high)
  obtain ⟨S,hS,hcard⟩ := exists_subset_card_eq hcount
  refine ⟨S,hcard,?_⟩
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors (hS hp)
  obtain ⟨i,hi,hdiv⟩ := factor_exists hpp (Nat.dvd_of_mem_primeFactors (hS hp))
  have hn : p ≠ 2 := by
    rintro rfl
    have h := Nat.mod_eq_zero_of_dvd hdiv
    simp [norm,arg,Nat.add_mod,Nat.pow_mod] at h
  have h4 : p % 4 = 1 := by
    let _ : Fact p.Prime := ⟨hpp⟩
    have he := @ZMod.mod_four_ne_three_of_sq_eq_neg_one p _ _ (root_mod (e:=1) (by decide)
      (by simpa using hdiv))
    have hodd := hpp.mod_two_eq_one_iff_ne_two.mpr hn
    omega
  exact ⟨hpp,h4,(Nat.le_of_dvd (Nat.zero_lt_succ _) hdiv).trans (hbounds i hi),
    arg X i,(hu i hi).le,hdiv⟩

end OMA.PrimeSupply1085

/-! Split prime blocks, their moduli, and a quantitative supply of ordinary primes
outside the blocks for Erdős's two-prime-squares construction. -/

open Finset Filter
open scoped Topology
noncomputable section
namespace OMA.Supply979

def modOf (s : Finset ℕ) := ∏ p ∈ s, p
def total {k : ℕ} (P : Fin k → Finset ℕ) := ∏ i, modOf (P i)

structure Blocks (k : ℕ) where
  P : Fin k → Finset ℕ
  card : ∀ i, (P i).card = k
  disjoint : ∀ i j, i ≠ j → Disjoint (P i) (P j)
  prime : ∀ i p, p ∈ P i → p.Prime ∧ p % 4 = 1 ∧ k^2 < p ∧ p ≤ (3*k^2)^10
  positive : ∀ i, 0 < modOf (P i)
  coprime : ∀ i j, i ≠ j → (modOf (P i)).Coprime (modOf (P j))
  phi : ∀ i, modOf (P i) ≤ 2*(modOf (P i)).totient
  Q : Finset ℕ
  good : ∀ p ∈ Q, p < total P ∧ p.Prime ∧ ∀ i, p.Coprime (modOf (P i))
  many : (total P:ℝ)/(k:ℝ)^4 ≤ Q.card

abbrev Blocks.m {k : ℕ} (s : Blocks k) (i : Fin k) := modOf (s.P i)
abbrev Blocks.A {k : ℕ} (s : Blocks k) := total s.P

private theorem choose_blocks (k : ℕ) (hk : 8 ≤ k) :
    ∃ P : Fin k → Finset ℕ, (∀ i, (P i).card = k) ∧
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      ∀ i p, p ∈ P i → p.Prime ∧ p%4=1 ∧ k^2<p ∧ p≤(3*k^2)^10 := by
  classical
  obtain ⟨S,sc,ps⟩ := PrimeSupply1085.prime_supply (3*k^2) (by nlinarith)
  let T := S \ range (k^2+1)
  have large : k*k ≤ T.card := by
    have h1 := card_sdiff_add_card_inter S (range (k^2+1))
    have h2 := card_le_card (inter_subset_right (s₁ := S) (s₂ := range (k^2+1)))
    rw [card_range] at h2
    dsimp [T]; rw [sc] at h1; nlinarith
  obtain ⟨U,hU,hu⟩ := exists_subset_card_eq large
  let e : Fin k × Fin k ≃ U := finProdFinEquiv.trans (U.equivFinOfCardEq hu).symm
  let P (i : Fin k) := univ.image (fun j : Fin k => (e (i,j)).val)
  refine ⟨P, ?_, ?_, ?_⟩
  · intro i
    have inj : Function.Injective (fun j : Fin k => (e (i,j)).val) :=
      fun a b h => congrArg Prod.snd (e.injective (Subtype.ext h))
    simp [P, card_image_of_injective _ inj]
  · intro i j hj
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨a,_,rfl⟩ := mem_image.mp hp
    obtain ⟨b,_,eq⟩ := mem_image.mp hq
    exact hj (congrArg Prod.fst (e.injective (Subtype.ext eq))).symm
  · intro i p hp
    obtain ⟨j,_,rfl⟩ := mem_image.mp hp
    have mem := mem_sdiff.mp (hU (e (i,j)).property)
    have h := ps _ mem.1
    exact ⟨h.1,h.2.1,by simpa using mem.2,h.2.2.1⟩

private theorem totient_bound (k : ℕ) (hk : 8 ≤ k) (s : Finset ℕ) (card : s.card = k)
    (prime : ∀ p ∈ s, p.Prime ∧ k^2 < p) : modOf s ≤ 2*(modOf s).totient := by
  have ratio := Nat.totient_eq_mul_prod_factors (modOf s)
  rw [show (modOf s).primeFactors = s from Nat.primeFactors_prod (fun p hp => (prime p hp).1)] at ratio
  have hkq : (8:ℚ) ≤ k := by exact_mod_cast hk
  have kp : (0:ℚ) < k := by positivity
  have sqp : 1 ≤ (k:ℚ)^2 := by nlinarith
  have bpos : 0 ≤ 1-((k:ℚ)^2)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ sqp)
  have step : (1-((k:ℚ)^2)⁻¹)^k ≤ ∏ p ∈ s, (1-(p:ℚ)⁻¹) := by
    calc
      _ = ∏ _p ∈ s, (1-((k:ℚ)^2)⁻¹) := by simp [card]
      _ ≤ _ := by
        apply prod_le_prod (fun _ _ => bpos)
        intro p hp
        have hpq : (k:ℚ)^2 ≤ p := by exact_mod_cast (prime p hp).2.le
        exact sub_le_sub_left (inv_anti₀ (by positivity) hpq) _
  have bern := one_add_mul_le_pow (a := -((k:ℚ)^2)⁻¹) (by linarith) k
  have low : (1:ℚ)/2 ≤ 1+(k:ℚ)*(-((k:ℚ)^2)⁻¹) := by
    field_simp
    nlinarith
  have hprod : (1:ℚ)/2 ≤ ∏ p ∈ s, (1-(p:ℚ)⁻¹) := by
    exact low.trans (bern.trans (by simpa only [sub_eq_add_neg] using step))
  have bound := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (modOf s:ℚ) by positivity)
  rw [← ratio] at bound
  exact_mod_cast (show (modOf s:ℚ) ≤ 2*((modOf s).totient:ℚ) by linarith)

private theorem good_count (k A : ℕ) (hk : 400 ≤ k) (hA : k^8 ≤ A)
    (hlog : Real.log A ≤ 30*(k:ℝ)^3) (Q : Finset ℕ)
    (all : A.primeCounting ≤ Q.card + k^2 + 1) : (A:ℝ)/(k:ℝ)^4 ≤ Q.card := by
  have kpos : 0 < k := by omega
  have kres : (400:ℝ) ≤ k := by exact_mod_cast hk
  have kl : 1 ≤ k^8 := Nat.one_le_pow _ _ kpos
  have kl' : 1 < k^8 := Nat.one_lt_pow (by decide) (by omega)
  have Apos : (1:ℝ) < A := by exact_mod_cast kl'.trans_le hA
  have al : Real.log ((A:ℝ)+1) ≤ Real.log A + 1 := by
    calc
      _ ≤ Real.log ((A:ℝ)*2) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log A + Real.log 2 := Real.log_mul (by positivity) (by norm_num)
      _ ≤ _ := by linarith [Real.log_two_lt_d9]
  have bc := (div_le_iff₀ (Real.log_pos Apos)).mp (Chebyshev.pi_ge A)
  have hcnt : (A.primeCounting:ℝ) ≤ Q.card + (k:ℝ)^2+1 := by exact_mod_cast all
  have combine := mul_le_mul hcnt hlog (Real.log_nonneg Apos.le) (by positivity)
  have log2 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hmax := mul_le_mul_of_nonneg_left log2 (show (0:ℝ) ≤ A by positivity)
  have k2 : (1:ℝ) ≤ (k:ℝ)^2 := by nlinarith
  have k3 : (400:ℝ) ≤ (k:ℝ)^3 := by nlinarith only [kres, mul_nonneg (by linarith : (0:ℝ) ≤ k) (sub_nonneg.mpr k2)]
  have hs : (k:ℝ)^8 ≤ A := by exact_mod_cast hA
  have e5 : (400:ℝ)*k^5 ≤ (k:ℝ)^8 := by
    calc _ ≤ (k:ℝ)^3*k^5 := by gcongr
         _ = _ := by ring
  have e3 : (k:ℝ)^3 ≤ (k:ℝ)^5 := by
    calc _ = (k:ℝ)^3*1 := by ring
         _ ≤ (k:ℝ)^3*(k:ℝ)^2 := by gcongr
         _ = _ := by ring
  have ei : 4 * (30*(k:ℝ)^5+60*k^3+1) ≤ A := by linarith
  have main : (A:ℝ) ≤ 120 * (k:ℝ)^3 * Q.card := by
    nlinarith only [ei, al, bc, combine, hmax, hlog]
  apply (div_le_iff₀ (show 0 < (k:ℝ)^4 by positivity)).mpr
  calc
    _ ≤ _ := main
    _ ≤ (k:ℝ) * k^3 * Q.card := by gcongr; linarith
    _ = _ := by ring

theorem supply : ∀ᶠ k : ℕ in atTop, Nonempty (Blocks k) := by
  classical
  filter_upwards [eventually_ge_atTop 400] with k hk
  obtain ⟨P,card,dis,prime⟩ := choose_blocks k (by omega)
  have kp : 0 < k := by omega
  have mp : ∀ i, 0 < modOf (P i) := fun i =>
    Finset.prod_pos fun p hp => (prime i p hp).1.pos
  have cp (i j : Fin k) (hij : i ≠ j) : (modOf (P i)).Coprime (modOf (P j)) := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    exact ((prime i p hp).1.coprime_iff_not_dvd).mpr fun div =>
      (disjoint_left.mp (dis i j hij) hp) (by rwa [(Nat.prime_dvd_prime_iff_eq
        (prime i p hp).1 (prime j q hq).1).mp div])
  let A := total P
  have Ap : 0 < A := prod_pos fun i _ => mp i
  have low (i : Fin k) : (k^2)^k ≤ modOf (P i) := by
    calc
      _ = ∏ _p ∈ P i, k^2 := by simp [card]
      _ ≤ _ := prod_le_prod' fun p hp => (prime i p hp).2.2.1.le
  have hA : k^8 ≤ A := by
    let i : Fin k := ⟨0,kp⟩
    calc
      _ = (k^2)^4 := by ring
      _ ≤ (k^2)^k := Nat.pow_le_pow_right (by positivity) (by omega)
      _ ≤ modOf (P i) := low i
      _ ≤ _ := single_le_prod' (s := univ) (f := fun i => modOf (P i))
        (fun i _ => mp i) (mem_univ i)
  have hi (i : Fin k) : modOf (P i) ≤ ((3*k^2)^10)^k := by
    calc
      _ ≤ ∏ _p ∈ P i, (3*k^2)^10 := prod_le_prod' fun p hp => (prime i p hp).2.2.2
      _ = _ := by simp [card]
  have high : A ≤ (((3*k^2)^10)^k)^k := by
    calc
      _ ≤ ∏ _i : Fin k, ((3*k^2)^10)^k := prod_le_prod' fun i _ => hi i
      _ = _ := by simp
  have cup : (A:ℝ) ≤ (((3*(k:ℝ)^2)^10)^k)^k := by exact_mod_cast high
  have logA := Real.log_le_log (by exact_mod_cast Ap) cup
  rw [Real.log_pow,Real.log_pow,Real.log_pow, Real.log_mul (by norm_num) (by positivity),
    Real.log_pow] at logA
  have lowerK : (400:ℝ) ≤ k := by exact_mod_cast hk
  have ls : Real.log 3 + 2*Real.log k ≤ 3*(k:ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show 0<(3:ℝ) by norm_num),
      Real.log_le_sub_one_of_pos (show (0:ℝ)<k by positivity)]
  have logbound : Real.log A ≤ 30*(k:ℝ)^3 := by
    norm_num only [Nat.cast_ofNat] at logA
    nlinarith only [logA, mul_le_mul_of_nonneg_left ls (show 0 ≤ 10*(k:ℝ)^2 by positivity)]
  let U := univ.biUnion P
  let bad := insert A U
  let Q := A.primesLE \ bad
  have boundU : U.card ≤ k^2 := by
    calc _ ≤ ∑ i : Fin k, (P i).card := card_biUnion_le
         _ = _ := by simp [card, sq]
  have boundQ : A.primeCounting ≤ Q.card + k^2 + 1 := by
    have eq := card_sdiff_add_card_inter A.primesLE bad
    have le := card_le_card (inter_subset_right (s₁ := A.primesLE) (s₂ := bad))
    have ins := card_insert_le A U
    rw [Nat.primesLE_card_eq_primeCounting] at eq
    dsimp [Q,bad] at *; omega
  refine ⟨⟨P,card,dis,prime,mp,cp,fun i => totient_bound k (by omega) _ (card i)
    (fun p hp => ⟨(prime i p hp).1,(prime i p hp).2.2.1⟩),Q,?_,
    good_count k A hk hA logbound Q boundQ⟩⟩
  intro p hp
  obtain ⟨mem,nmem⟩ := mem_sdiff.mp hp
  obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp mem
  have ne : p ≠ A := fun h => nmem (by simp [bad,h])
  refine ⟨le.lt_of_ne ne, pr, fun i => Nat.Coprime.prod_right fun q hq => ?_⟩
  exact (pr.coprime_iff_not_dvd).mpr fun div => nmem (mem_insert_of_mem
    (mem_biUnion.mpr ⟨i,mem_univ _,by rwa [(Nat.prime_dvd_prime_iff_eq pr (prime i q hq).1).mp div]⟩))

/-- The loss from discarding light fibers over all blocks is smaller than the prime density. -/
theorem light_loss : ∀ᶠ k : ℕ in atTop,
    (3/4:ℝ)^k + 1/(k:ℝ)^5 < 1/(k:ℝ)^4 := by
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 (r := (3/4:ℝ)) (by norm_num)
  filter_upwards [h.eventually_lt_const (show (0:ℝ) < 1/2 by norm_num),eventually_ge_atTop 3]
    with k hk hk3
  have kp : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have k3 : (3:ℝ) ≤ k := by exact_mod_cast hk3
  have h' : (k:ℝ)^4*(3/4:ℝ)^k < 1/2 := hk
  apply (mul_lt_mul_iff_of_pos_left (pow_pos kp 4)).mp
  have div5 : (k:ℝ)^4*(1/(k:ℝ)^5) = 1/k := by field_simp
  have div4 : (k:ℝ)^4*(1/(k:ℝ)^4) = 1 := by field_simp
  rw [mul_add,div5,div4]
  linarith [(div_lt_iff₀ kp).mpr (show (1:ℝ) < 1/2*k by linarith)]

theorem exponential_gain :
    Tendsto (fun k : ℕ => (2:ℝ)^k/(k:ℝ)^12) atTop atTop := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt 12 (r := (2:ℝ)) (by norm_num)
  have hp : ∀ᶠ k : ℕ in atTop, 0 < (k:ℝ)^12/(2:ℝ)^k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    positivity
  have hi := (tendsto_nhdsWithin_iff.mpr ⟨h,hp⟩).inv_tendsto_nhdsGT_zero
  exact hi.congr fun k => inv_div ((k:ℝ)^12) ((2:ℝ)^k)

end OMA.Supply979
end

/-! Erdős's heavy-residue-class lemma, from section 2 of his 1937 paper
*On the sum and difference of squares of primes*. If every block had few
frequent residues, CRT would allow too few integers avoiding all light fibers. -/
namespace OMA.Analytic979
open Finset
open scoped Classical

theorem heavy {k : ℕ} (hk : 0<k) (m : Fin k → ℕ) (mp : ∀ i, 0 < m i)
    (co : ∀ i j, i≠j → (m i).Coprime (m j)) (P : Finset ℕ)
    (good : ∀ p∈P, p < ∏ i, m i)
    (unit : ∀ p∈P, ∀ i, p.Coprime (m i))
    (many : ((∏ i, m i : ℕ):ℝ)/(k:ℝ)^4 ≤ P.card)
    (small : (3/4:ℝ)^k + 1/(k:ℝ)^5 < 1/(k:ℝ)^4) :
    ∃ i, ∃ H : Finset (ZMod (m i)), 3*m i ≤ 4*H.card ∧ (∀ x∈H, IsUnit x) ∧
      ∀ x∈H, ⌈((∏ i, m i : ℕ):ℝ) / ((m i:ℝ)*(k:ℝ)^6)⌉₊ ≤
        (P.filter (fun p : ℕ => (p : ZMod (m i))=x)).card := by
  classical
  let A := ∏ i, m i
  have Ap : 0<A := prod_pos fun i _ => mp i
  have kp : 0<(k:ℝ) := by exact_mod_cast hk
  have _ (i:Fin k) : NeZero (m i) := ⟨(mp i).ne'⟩
  let fib (i : Fin k) (x : ZMod (m i)) := P.filter (fun p : ℕ => (p:ZMod (m i))=x)
  let width (i : Fin k) : ℝ := A/((m i:ℝ)*(k:ℝ)^6)
  have wp (i : Fin k) : 0<width i := by
    dsimp [width]; exact div_pos (by exact_mod_cast Ap) (mul_pos (by exact_mod_cast mp i) (by positivity))
  let H (i : Fin k) := univ.filter (fun x : ZMod (m i) => width i ≤ (fib i x).card)
  have memH (i : Fin k) (x : ZMod (m i)) : x∈H i ↔ width i≤(fib i x).card := by simp [H]
  suffices rich : ∃ i, 3*m i ≤ 4*(H i).card by
    obtain ⟨i,hi⟩ := rich
    refine ⟨i,H i,hi,?_,fun x hx => Nat.ceil_le.mpr ((memH i x).mp hx)⟩
    intro x hx
    have non : 0<(fib i x).card := by exact_mod_cast (wp i).trans_le ((memH i x).mp hx)
    obtain ⟨p,hp⟩ := card_pos.mp non
    obtain ⟨pP,rfl⟩ := mem_filter.mp hp
    exact (ZMod.isUnit_iff_coprime ..).mpr (unit p pP i)
  by_contra! few
  let L (i : Fin k) := (univ \ H i).biUnion (fib i)
  have light (i : Fin k) : ((L i).card:ℝ) ≤ A/(k:ℝ)^6 := by
    let J := univ \ H i
    have jbound : J.card ≤ m i := by simpa [ZMod.card] using J.card_le_univ
    have raw : (L i).card ≤ ∑ x∈J, (fib i x).card := card_biUnion_le
    calc
      _ ≤ ∑ x∈J, ((fib i x).card:ℝ) := by exact_mod_cast raw
      _ ≤ ∑ _x∈J, width i := sum_le_sum fun x hx => le_of_lt (lt_of_not_ge
        (fun h => (mem_sdiff.mp hx).2 ((memH i x).mpr h)))
      _ = (J.card:ℝ)*width i := by simp
      _ ≤ (m i:ℝ)*width i := mul_le_mul_of_nonneg_right (by exact_mod_cast jbound) (wp i).le
      _ = _ := by
        have nz : (m i:ℝ) ≠ 0 := by exact_mod_cast (mp i).ne'
        dsimp [width]; field_simp
  let S := P.filter (fun p => ∀ i, (p:ZMod (m i))∈H i)
  let encode (p:S) (i:Fin k) : H i := ⟨p.val,(mem_filter.mp p.property).2 i⟩
  have inj : Function.Injective encode := by
    intro p q h
    have eq : (p.val : ZMod A)=(q.val : ZMod A) := by
      apply (ZMod.prodEquivPi m (fun i j ij => co i j ij)).injective
      funext i
      simpa [encode] using congrArg Subtype.val (congrFun h i)
    apply Subtype.ext
    have hp := good p.val (mem_filter.mp p.property).1
    have hq := good q.val (mem_filter.mp q.property).1
    simpa [A,ZMod.val_natCast,Nat.mod_eq_of_lt hp,Nat.mod_eq_of_lt hq] using congrArg ZMod.val eq
  have sc : S.card ≤ ∏ i, (H i).card := by simpa [Fintype.card_pi] using Fintype.card_le_of_injective encode inj
  have reduced : (S.card:ℝ) ≤ (3/4:ℝ)^k*A := by
    calc
      _ ≤ ∏ i, ((H i).card:ℝ) := by exact_mod_cast sc
      _ ≤ ∏ i, ((3/4:ℝ)*m i) := Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => by
        have b : (4:ℝ)*(H i).card < 3*m i := by exact_mod_cast few i
        linarith
      _ = _ := by simp only [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,Nat.cast_prod,A]
  have cover : P ⊆ S ∪ univ.biUnion L := by
    intro p hp
    by_cases all : ∀ i, (p:ZMod (m i))∈H i
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,all⟩)
    · push Not at all
      obtain ⟨i,hi⟩ := all
      exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,
        mem_biUnion.mpr ⟨(p:ZMod (m i)),mem_sdiff.mpr ⟨mem_univ _,hi⟩,mem_filter.mpr ⟨hp,rfl⟩⟩⟩)
  have bound := (card_le_card cover).trans
    (card_union_le .. |>.trans (Nat.add_le_add_left (card_biUnion_le (s:=univ) (t:=L)) _))
  have total : (P.card:ℝ) ≤ S.card+∑ i, ((L i).card:ℝ) := by exact_mod_cast bound
  have err : (∑ i, ((L i).card:ℝ)) ≤ A/(k:ℝ)^5 := calc
    _ ≤ ∑ _i:Fin k, (A:ℝ)/(k:ℝ)^6 := sum_le_sum fun i _ => light i
    _ = _ := by simp; field_simp
  have cancel := mul_lt_mul_of_pos_right small (show 0<(A:ℝ) by exact_mod_cast Ap)
  change (A:ℝ)/(k:ℝ)^4 ≤ P.card at many
  rw [add_mul,one_div_mul_eq_div,one_div_mul_eq_div] at cancel
  linarith

end OMA.Analytic979

/-! A squarefree product of k primes congruent to 1 modulo 4 has 2^k
independent square roots of -1. Each acts on the heavily occupied residues
to produce disjoint families of ordered pairs whose sum of squares vanishes. -/

namespace OMA.CRT979
open Finset

private theorem two_roots {p : ℕ} (hp : p.Prime) (hm : p%4=1) :
    ∃ T : Finset (ZMod p), T.card=2 ∧ ∀ x∈T, x^2 = -1 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p%4≠3)
  have sq : x^2 = -1 := by simpa [pow_two] using hx.symm
  have nx : x≠0 := by intro h; simp [h] at sq
  have ne : x ≠ -x := by
    intro e
    have prod : (2:ZMod p)*x=0 := by linear_combination e
    have bad := (mul_eq_zero.mp prod).resolve_right nx
    have dv := (ZMod.natCast_eq_zero_iff 2 p).mp bad
    have le := Nat.le_of_dvd (by decide) dv
    have := hp.two_le
    omega
  refine ⟨{x,-x}, by simp [ne],?_⟩
  intro y hy
  simp only [mem_insert,mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact sq
  · simpa using sq

theorem roots (S : Finset ℕ) (hs : ∀p∈S,p.Prime ∧ p%4=1) :
    ∃ R : Finset (ZMod (∏ p∈S,p)), R.card=2^S.card ∧ ∀x∈R,x^2 = -1 := by
  classical
  induction S using Finset.induction with
  | empty =>
    simp only [prod_empty,card_empty,pow_zero]
    exact ⟨{0},by simp,fun _ _ => Subsingleton.elim ..⟩
  | @insert p S hnot ih =>
    obtain ⟨hp,hm⟩ := hs p (mem_insert_self ..)
    have old (q) (hq : q∈S) := hs q (mem_insert_of_mem hq)
    obtain ⟨A,ha,asq⟩ := two_roots hp hm
    obtain ⟨B,hb,bsq⟩ := ih old
    have cop : p.Coprime (∏ q∈S,q) := by
      by_contra bad
      obtain ⟨q,hq,div⟩ := (hp.prime.dvd_finsetProd_iff id).mp (hp.dvd_iff_not_coprime.mpr bad)
      exact hnot ((Nat.prime_dvd_prime_iff_eq hp (old q hq).1).mp div ▸ hq)
    let eq := ZMod.chineseRemainder cop
    rw [prod_insert hnot,card_insert_of_notMem hnot]
    refine ⟨(A×ˢB).map eq.symm.toEquiv.toEmbedding,?_,?_⟩
    · simp [ha,hb,pow_succ,mul_comm]
    · intro z hz
      obtain ⟨⟨a,b⟩,hab,rfl⟩ := mem_map.mp hz
      apply eq.injective
      change eq ((eq.symm (a,b))^2) = eq (-1)
      rw [map_pow,RingEquiv.apply_symm_apply,map_neg,map_one]
      exact Prod.ext (asq a (mem_product.mp hab).1) (bsq b (mem_product.mp hab).2)

private theorem acts_injectively {m : ℕ} {r : ZMod m} (h : r^2 = -1) :
    Function.Injective (fun y => r*y) := by
  intro x y he
  have e := congrArg (r*·) he
  simpa only [← mul_assoc, ← sq, h, neg_one_mul, neg_inj] using e

private theorem overlap {m : ℕ} [NeZero m] {H : Finset (ZMod m)}
    (heavy : 3*m ≤ 4*H.card) {r : ZMod m} (hr : r^2 = -1) :
    m ≤ 2*(H.filter (fun y=>r*y∈H)).card := by
  classical
  let B := H.filter (fun y=>r*y∉H)
  have bad : B.image (fun z=>r*z) ⊆ Hᶜ := by
    rintro x hx
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
    exact mem_compl.mpr (mem_filter.mp hz).2
  have hbad := card_le_card bad
  rw [card_image_of_injective _ (acts_injectively hr),card_compl,ZMod.card] at hbad
  have part := card_filter_add_card_filter_not (s:=H) (p:=fun z=>r*z∈H)
  change _ + B.card = _ at part
  have total : H.card ≤ m := by simpa only [ZMod.card] using card_le_univ H
  omega

private theorem count_roots {m : ℕ} [NeZero m] (R H : Finset (ZMod m))
    (hr : ∀ r∈R, r^2 = -1) (hu : ∀z∈H,IsUnit z) (big : 3*m ≤ 4*H.card)
    (P : Finset ℕ) (L : ℕ)
    (rich : ∀ z∈H, L ≤ (P.filter (fun n : ℕ => (n:ZMod m)=z)).card) :
    R.card*m*L^2 ≤ 2*((P×ˢP).filter (fun xy => m ∣ xy.1^2+xy.2^2)).card := by
  classical
  let F (z : ZMod m) := P.filter fun n : ℕ => (n:ZMod m)=z
  let J (r : ZMod m) := H.filter fun z => r*z∈H
  let box (r z : ZMod m) := F (r*z) ×ˢ F z
  let E (r : ZMod m) := (J r).biUnion (box r)
  have boxmem (r z : ZMod m) (x : ℕ × ℕ) : x∈box r z ↔
      (x.1∈P ∧ (x.1:ZMod m)=r*z) ∧ (x.2∈P ∧ (x.2:ZMod m)=z) := by
    simp only [box,F,mem_product,mem_filter]
  have nb (r : ZMod m) : ∀u∈J r, L^2 ≤ (box r u).card := by
    intro u hu
    obtain ⟨uh,ruh⟩ := mem_filter.mp hu
    simpa only [box,card_product,sq] using Nat.mul_le_mul (rich _ ruh) (rich _ uh)
  have dis (r : ZMod m) : ((J r:Set (ZMod m))).PairwiseDisjoint (box r) := by
    intro u _ v _ huv
    apply disjoint_left.mpr
    intro x hu hv
    exact huv (((boxmem r u x).mp hu).2.2.symm.trans ((boxmem r v x).mp hv).2.2)
  have count (r) (rmem : r∈R) : m*L^2 ≤ 2*(E r).card := by
    have c := sum_le_sum (s:=J r) (nb r)
    rw [sum_const,nsmul_eq_mul,← card_biUnion (dis r)] at c
    have ov : m ≤ 2*(J r).card := by simpa only [J] using overlap big (hr r rmem)
    have c' : (J r).card*L^2 ≤ (E r).card := by exact_mod_cast c
    exact (Nat.mul_le_mul_right (L^2) ov).trans
      (by simpa only [mul_assoc] using Nat.mul_le_mul_left 2 c')
  have dj : (R:Set (ZMod m)).PairwiseDisjoint E := by
    intro r _ s _ ne
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨z,hz,hx⟩ := mem_biUnion.mp ha
    obtain ⟨z',_,hx'⟩ := mem_biUnion.mp hb
    obtain ⟨⟨_,rp⟩,_,q⟩ := (boxmem r z a).mp hx
    obtain ⟨⟨_,sp⟩,_,q'⟩ := (boxmem s z' a).mp hx'
    have zz := q.symm.trans q'
    rw [← zz] at sp
    obtain ⟨u,eu⟩ := hu z (mem_filter.mp hz).1
    exact ne (u.mul_left_inj.mp (by simpa only [eu] using rp.symm.trans sp))
  have inside : R.biUnion E ⊆ (P×ˢP).filter (fun xy => m ∣ xy.1^2+xy.2^2) := by
    intro a ha
    obtain ⟨r,hr',ha⟩ := mem_biUnion.mp ha
    obtain ⟨z,hz,ha⟩ := mem_biUnion.mp ha
    obtain ⟨⟨hp,rp⟩,hq,q⟩ := (boxmem r z a).mp ha
    refine mem_filter.mpr ⟨mem_product.mpr ⟨hp,hq⟩, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
    simp only [Nat.cast_add,Nat.cast_pow,rp,q,mul_pow,hr r hr',neg_one_mul,neg_add_cancel]
  have all := sum_le_sum (s:=R) count
  rw [sum_const,nsmul_eq_mul,← mul_sum,← card_biUnion dj,← mul_assoc] at all
  exact all.trans (Nat.mul_le_mul_left 2 (card_le_card inside))

theorem pair_count (S : Finset ℕ) (hs : ∀p∈S,p.Prime ∧ p%4=1)
    (m : ℕ) [NeZero m] (hm : m = ∏p∈S,p)
    (H : Finset (ZMod m)) (hu : ∀z∈H,IsUnit z) (big : 3*m ≤ 4*H.card)
    (P : Finset ℕ) (L : ℕ)
    (rich : ∀ z∈H, L ≤ (P.filter (fun n : ℕ => (n:ZMod m)=z)).card) :
    2^S.card*m*L^2 ≤ 2*((P×ˢP).filter (fun xy => m ∣ xy.1^2+xy.2^2)).card := by
  subst m
  obtain ⟨R,hR,sq⟩ := roots S hs
  rw [← hR]
  exact count_roots R H sq hu big P L rich

end OMA.CRT979

/-! Pigeonhole the multiples of a block modulus and pass from ordered
prime pairs to unordered representations of a sum of squares. -/
namespace OMA.Finish979
open Finset Filter
open scoped Classical

private def pair (v : ℕ × ℕ) : Multiset ℕ := {v.1,v.2}

private theorem forget_order (T : Finset (ℕ × ℕ)) : T.card ≤ 2*(T.image pair).card := by
  classical
  let enc (v : ℕ×ℕ) := (decide (v.1≤v.2),pair v)
  have hf : Set.MapsTo enc (T : Set _) (((univ : Finset Bool) ×ˢ (T.image pair)) : Finset _) := by
    intro v hv; exact mem_product.mpr ⟨mem_univ _,mem_image_of_mem _ hv⟩
  have hi : Function.Injective enc := by
    rintro ⟨a,b⟩ ⟨c,d⟩ he
    have ho : (a≤b ↔ c≤d) := by simpa [enc] using congrArg Prod.fst he
    have heq := congrArg Prod.snd he
    change ({a,b} : Multiset ℕ)={c,d} at heq
    have sum := congrArg Multiset.sum heq
    simp only [Multiset.sum_cons,Multiset.sum_singleton,Multiset.insert_eq_cons] at sum
    have ha : a=c ∨ a=d := by
      have h : a∈({a,b}:Multiset ℕ) := by simp
      simpa [heq] using h
    apply Prod.ext <;> dsimp <;> omega
  simpa using card_le_card_of_injOn enc hf hi.injOn

theorem hit {A m L : ℕ} (hm : 0 < m) (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ p≤A)
    (large : 4*L*A^2 < m*((P ×ˢ P).filter (fun ab => m ∣ ab.1^2+ab.2^2)).card) :
    ∃ n : ℕ, m≤n ∧ (L:ℕ∞)<(Erdos979.solutionSet n 2).encard := by
  classical
  let E := (P ×ˢ P).filter (fun ab => m ∣ ab.1^2+ab.2^2)
  let score (ab : ℕ×ℕ) := ab.1^2+ab.2^2
  let C := Icc 1 (2*A^2/m)
  have facts {z : ℕ×ℕ} (hz : z ∈ E) :
      m ∣ score z ∧ (score z/m ∈ C) ∧ z.1.Prime ∧ z.2.Prime := by
    have hz' := mem_filter.mp hz
    obtain ⟨a,b⟩ := mem_product.mp hz'.1
    obtain ⟨ap,al⟩ := hp _ a
    obtain ⟨bp,bl⟩ := hp _ b
    have pos : 0<score z := by dsimp [score]; nlinarith [ap.pos, sq_nonneg z.2]
    have h := Nat.le_of_dvd pos hz'.2
    refine ⟨hz'.2,mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hm).mpr (by simpa using h),?_⟩,ap,bp⟩
    exact Nat.div_le_div_right (by dsimp [score]; nlinarith [Nat.pow_le_pow_left al 2,Nat.pow_le_pow_left bl 2])
  have count : C.card*(2*L)<E.card := by
    have c : C.card=2*A^2/m := by simp [C,Nat.card_Icc]
    rw [c]
    have ratio := Nat.div_mul_le_self (2*A^2) m
    by_contra! he
    have u := Nat.mul_le_mul_left m he
    have v := Nat.mul_le_mul_right (2*L) ratio
    change 4*L*A^2 < m*E.card at large
    nlinarith only [large,u,v]
  obtain ⟨z,hz,zsize⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (fun x hx => (facts hx).2.1) count
  let T := E.filter (fun w => score w/m=z)
  have sub : (↑(T.image pair) : Set (Multiset ℕ)) ⊆ Erdos979.solutionSet (m*z) 2 := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hw
    obtain ⟨vE,ve⟩ := mem_filter.mp hv
    obtain ⟨dv,_,pr,ps⟩ := facts vE
    refine ⟨by simp [pair],?_,?_⟩
    · intro u hu; have alt : u=v.1 ∨ u=v.2 := by simpa [pair] using hu
      rcases alt with rfl|rfl <;> assumption
    · have h := Nat.mul_div_cancel' dv
      change score v/m=z at ve
      rw [ve] at h
      simpa [pair,score] using h
  have bound := Set.encard_le_encard sub
  rw [Set.encard_coe_eq_coe_finsetCard] at bound
  have hz1 := (mem_Icc.mp hz).1
  have unordered := forget_order T
  change 2*L<T.card at zsize
  refine ⟨m*z,by nlinarith,lt_of_lt_of_le ?_ bound⟩
  exact_mod_cast (by omega : L<(T.image pair).card)

theorem enough {k m A L count : ℕ} (hk : 0 < k) (hm : 0 < m) (hA : 0 < A)
    (growth : 8*(L:ℝ)*(k:ℝ)^12 < (2:ℝ)^k)
    (h : 2^k*m*⌈(A:ℝ)/((m:ℝ)*(k:ℝ)^6)⌉₊^2 ≤ 2*count) :
    4*L*A^2 < m*count := by
  let w := ⌈(A:ℝ)/((m:ℝ)*(k:ℝ)^6)⌉₊
  have wp : (A:ℝ) ≤ (w:ℝ)*((m:ℝ)*(k:ℝ)^6) :=
    (div_le_iff₀ (by positivity)).mp (Nat.le_ceil _)
  change 2^k*m*w^2 ≤ 2*count at h
  have hc : (2:ℝ)^k*m*(w:ℝ)^2 ≤ 2*count := by exact_mod_cast h
  have sq := pow_le_pow_left₀ (Nat.cast_nonneg A : (0:ℝ)≤A) wp 2
  have bp : 0 < (k:ℝ)^12 := by positivity
  have s : (8*(L:ℝ)*(A:ℝ)^2)*(k:ℝ)^12 < (2*count*(m:ℝ))*(k:ℝ)^12 := calc
    _ = (8*(L:ℝ)*(k:ℝ)^12)*(A:ℝ)^2 := by ring
    _ < (2:ℝ)^k*(A:ℝ)^2 := mul_lt_mul_of_pos_right growth (by positivity)
    _ ≤ (2:ℝ)^k*((w:ℝ)*((m:ℝ)*(k:ℝ)^6))^2 := mul_le_mul_of_nonneg_left sq (by positivity)
    _ = ((2:ℝ)^k*m*(w:ℝ)^2)*((m:ℝ)*(k:ℝ)^12) := by ring
    _ ≤ (2*count:ℝ)*((m:ℝ)*(k:ℝ)^12) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring
  have ans := (mul_lt_mul_iff_left₀ bp).mp s
  exact_mod_cast (by nlinarith only [ans] : 4*(L:ℝ)*(A:ℝ)^2 < (m:ℝ)*count)

theorem finish (hits : ∀ L N : ℕ, ∃ n ≥ N, (L:ℕ∞)<(Erdos979.solutionSet n 2).encard) :
    type_of% @Erdos979.erdos_979.variants.k2 := by
  apply ENat.eq_top_iff_forall_ge.mpr
  intro L
  apply le_limsup_of_frequently_le'
  rw [frequently_atTop]
  intro N
  obtain ⟨n,hn,good⟩ := hits L N
  exact ⟨n,hn,good.le⟩

end OMA.Finish979

/-! Combine the prime-block argument with the ordered-to-unordered count. -/

namespace OMA.Assemble979
open Finset Filter OMA.Supply979

theorem result : type_of% @Erdos979.erdos_979.variants.k2 := by
  classical
  apply OMA.Finish979.finish
  intro L N
  obtain ⟨k,hs,small,amp,hk,hN⟩ := (supply.and (light_loss.and
    ((exponential_gain.eventually_gt_atTop (8*(L:ℝ))).and
    ((eventually_ge_atTop 1).and (eventually_ge_atTop N))))).exists
  obtain ⟨blocks⟩ := hs
  let m := blocks.m
  let A := total blocks.P
  have hk' : 0<k := by omega
  have ap : 0 < A := prod_pos (fun j _ => blocks.positive j)
  have kp : (0:ℝ)<k := by exact_mod_cast hk'
  obtain ⟨i,H,big,units,fibers⟩ := OMA.Analytic979.heavy hk' m blocks.positive blocks.coprime blocks.Q
    (fun p hp => (blocks.good p hp).1) (fun p hp => (blocks.good p hp).2.2) blocks.many small
  let S := blocks.P i
  let _ : NeZero (m i) := ⟨(blocks.positive i).ne'⟩
  have pairs := OMA.CRT979.pair_count S (fun p hp => ⟨(blocks.prime i p hp).1,(blocks.prime i p hp).2.1⟩)
    (m i) rfl H units big blocks.Q _ fibers
  have sc : S.card=k := blocks.card i
  rw [sc] at pairs
  have g := (lt_div_iff₀ (pow_pos kp 12)).mp amp
  have bound := OMA.Finish979.enough (m:=m i) (A:=A) hk' (blocks.positive i) ap g pairs
  obtain ⟨n,hn,hits⟩ := OMA.Finish979.hit (blocks.positive i) blocks.Q
    (fun p hp => ⟨(blocks.good p hp).2.1,(blocks.good p hp).1.le⟩) bound
  obtain ⟨p,hp⟩ := card_pos.mp (sc ▸ hk' : 0<S.card)
  have dvd : p ∣ m i := Finset.dvd_prod_of_mem (f:=id) hp
  have pbig := (blocks.prime i p hp).2.2.1
  have km : k ≤ m i := (show k≤p by nlinarith [Nat.one_le_of_lt hk']).trans
    (Nat.le_of_dvd (blocks.positive i) dvd)
  exact ⟨n,hN.trans (km.trans hn),hits⟩

end OMA.Assemble979

theorem OMA.solution : type_of% @Erdos979.erdos_979.variants.k2 :=
  OMA.Assemble979.result
