import OMAReductions.R_Erdos690_erdos_690_variants_large_k_R1
import Mathlib

/-! CRT counts each prime pattern in one period, and complete periods determine natural density. -/

open Finset
open scoped Classical

namespace PrimePattern

private lemma card_crt (m q : ℕ) (hm : 0 < m) (hq : 0 < q) (hc : m.Coprime q)
    (A B : Finset ℕ) (hA : A ⊆ range m) (hB : B ⊆ range q) :
    ((range (m*q)).filter (fun n => n%m ∈ A ∧ n%q ∈ B)).card = A.card * B.card := by
  rw [← card_product]
  apply le_antisymm
  · apply Finset.card_le_card_of_injOn (fun n => (n%m,n%q))
    · intro n hn
      exact mem_product.mpr (mem_filter.mp hn).2
    · intro x hx y hy hxy
      have h := (Nat.modEq_and_modEq_iff_modEq_mul hc).1
        ⟨congrArg Prod.fst hxy, congrArg Prod.snd hxy⟩
      exact h.eq_of_lt_of_lt (mem_range.mp (mem_filter.mp hx).1)
        (mem_range.mp (mem_filter.mp hy).1)
  · let g (a : ℕ × ℕ) := Nat.chineseRemainder hc a.1 a.2
    have ha (a : ℕ × ℕ) (ha : a ∈ A ×ˢ B) : (g a : ℕ)%m = a.1 := by
      exact (show (g a : ℕ)%m = a.1%m from (g a).property.1).trans (Nat.mod_eq_of_lt (mem_range.mp (hA (mem_product.mp ha).1)))
    have hb (a : ℕ × ℕ) (ha : a ∈ A ×ˢ B) : (g a : ℕ)%q = a.2 := by
      exact (show (g a : ℕ)%q = a.2%q from (g a).property.2).trans (Nat.mod_eq_of_lt (mem_range.mp (hB (mem_product.mp ha).2)))
    apply Finset.card_le_card_of_injOn (fun a => (g a : ℕ))
    · intro a hab
      have hlt : (g a : ℕ) < m*q := Nat.chineseRemainder_lt_mul hc a.1 a.2 hm.ne' hq.ne'
      exact mem_filter.mpr ⟨mem_range.mpr hlt, by
        rw [ha a hab, hb a hab]
        exact mem_product.mp hab⟩
    · intro a hab b hbb h
      change (g a : ℕ) = (g b : ℕ) at h
      exact Prod.ext ((ha a hab).symm.trans (h ▸ ha b hbb)) ((hb a hab).symm.trans (h ▸ hb b hbb))

private def patterns (Q T : Finset ℕ) : Finset ℕ :=
  (range (∏ p ∈ Q,p)).filter fun n => Q.filter (· ∣ n) = T

private lemma pattern_mod (Q : Finset ℕ) (n : ℕ) :
    Q.filter (· ∣ n%(∏ p ∈ Q,p)) = Q.filter (· ∣ n) := by
  ext a
  by_cases ha : a ∈ Q
  · simp only [mem_filter, ha, true_and]
    exact (Nat.mod_modEq n (∏ p ∈ Q,p)).dvd_iff (Finset.dvd_prod_of_mem id ha)
  · simp [ha]

private lemma insert_pattern {Q T : Finset ℕ} {p n : ℕ} (hp : p ∉ Q) :
    (insert p Q).filter (· ∣ n) = T ↔
      (p ∣ n ↔ p ∈ T) ∧ Q.filter (· ∣ n) = T.erase p := by
  have he : ((insert p Q).filter (· ∣ n)).erase p = Q.filter (· ∣ n) := by
    ext r
    by_cases hr : r=p
    · subst r
      simp [hp]
    · simp [hr]
  constructor
  · intro h
    refine ⟨?_, he.symm.trans (congrArg (erase · p) h)⟩
    rw [← h]
    simp
  · intro h
    ext r
    by_cases hr : r = p
    · subst r
      simpa using h.1
    · have hx := Finset.ext_iff.mp h.2 r
      simpa [hr] using hx

private lemma pattern_card (Q T : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (hT : T ⊆ Q) :
    (patterns Q T).card = ∏ p ∈ Q \ T, (p-1) := by
  induction Q using Finset.induction_on generalizing T with
  | empty =>
    have he : T = ∅ := Finset.subset_empty.mp hT
    simp [he, patterns]
  | insert p Q hp ih =>
    have hQ' : ∀ r ∈ Q, r.Prime := fun r hr => hQ r (mem_insert_of_mem hr)
    have hp' := hQ p (mem_insert_self p Q)
    let q := ∏ r ∈ Q,r
    let T' := T.erase p
    have hT' : T' ⊆ Q := fun r hr =>
      (mem_insert.mp (hT (mem_erase.mp hr).2)).resolve_left (mem_erase.mp hr).1
    have hq : 0 < q := Finset.prod_pos fun r hr => (hQ' r hr).pos
    have hcop : p.Coprime q := hp'.coprime_iff_not_dvd.mpr (by
      intro h
      have hprime : Prime p := Nat.prime_iff.mp hp'
      obtain ⟨r, hr, hpr⟩ := hprime.exists_mem_finset_dvd h
      have he := ((Nat.dvd_prime (hQ' r hr)).mp hpr).resolve_left hp'.ne_one
      exact hp (he ▸ hr))
    let A := if p ∈ T then ({0} : Finset ℕ) else Ico 1 p
    have hA : A ⊆ range p := by
      intro a ha
      unfold A at ha
      split at ha
      · obtain rfl := mem_singleton.mp ha
        exact mem_range.mpr hp'.pos
      · exact mem_range.mpr (mem_Ico.mp ha).2
    have hB : patterns Q T' ⊆ range q := fun r hr => (mem_filter.mp hr).1
    have hform : patterns (insert p Q) T =
        (range (p*q)).filter (fun n => n%p ∈ A ∧ n%q ∈ patterns Q T') := by
      unfold patterns
      rw [prod_insert hp]
      ext n
      simp only [mem_filter, insert_pattern hp, mem_range, T']
      have hloc : n%p ∈ A ↔ (p ∣ n ↔ p ∈ T) := by
        by_cases ht : p ∈ T
        · simp [A, ht, Nat.dvd_iff_mod_eq_zero]
        · have hlt := Nat.mod_lt n hp'.pos
          simp [A, ht, Nat.dvd_iff_mod_eq_zero, hlt]
          omega
      rw [hloc]
      simp only [q, pattern_mod, Nat.mod_lt n (show 0 < ∏ p ∈ Q,p from hq), true_and]
    rw [hform, card_crt p q hp'.pos hq hcop A _ hA hB, ih T' hQ' hT']
    have hRest : Q \ T' = Q \ T := by
      ext r
      by_cases hr : r=p
      · subst r
        simp [hp]
      · simp [T', hr]
    rw [hRest]
    by_cases ht : p∈T
    · have hEq : insert p Q \ T = Q \ T := by
        ext r
        by_cases hr : r=p <;> simp_all
      simp [A, ht, hEq]
    · have hEq : insert p Q \ T = insert p (Q \ T) := by
        ext r
        by_cases hr : r=p <;> simp_all
      rw [hEq, prod_insert (fun h => hp (mem_sdiff.mp h).1)]
      simp [A, ht]

private lemma weight_eq (Q T : Finset ℕ) (hQ : ∀ p ∈ Q,p.Prime) (hT : T ⊆ Q) :
    ((patterns Q T).card : ℝ) / ((∏ p ∈ Q,p : ℕ) : ℝ) =
      (∏ p ∈ T, 1/(p:ℝ)) * ∏ p ∈ Q \ T, (1-1/(p:ℝ)) := by
  have hprod : (∏ p ∈ Q \ T,p) * (∏ p ∈ T,p) = ∏ p ∈ Q,p :=
    Finset.prod_sdiff hT
  rw [pattern_card Q T hQ hT, ← hprod, Nat.cast_mul, Nat.cast_prod,
    Nat.cast_prod, Nat.cast_prod]
  have ht : (∏ p ∈ T, (p:ℝ))⁻¹ = ∏ p ∈ T, 1/(p:ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, one_div]
  have hc : (∏ p ∈ Q \ T, ((p-1 : ℕ) : ℝ)) / (∏ p ∈ Q \ T, (p:ℝ)) =
      ∏ p ∈ Q \ T, (1-1/(p:ℝ)) := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpp := hQ p (mem_sdiff.mp hp).1
    have hpos : 0 < (p:ℝ) := by exact_mod_cast hpp.pos
    rw [Nat.cast_sub hpp.one_lt.le]
    norm_num
    field_simp
  rw [← ht, ← hc, div_eq_mul_inv, mul_inv_rev]
  ring

theorem exact_probability : ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∀ R : Finset ℕ → Prop,
    let q := ∏ p ∈ Q, p
    (((range q).filter (fun n => R (Q.filter (· ∣ n)))).card : ℝ) / q =
      ∑ T ∈ Q.powerset.filter R, (∏ p ∈ T, 1/(p:ℝ)) * ∏ p ∈ Q \ T, (1-1/(p:ℝ)) := by
  intro Q hQ R
  classical
  let q := ∏ p ∈ Q,p
  let N := (range q).filter (fun n => R (Q.filter (· ∣ n)))
  let Ts := Q.powerset.filter R
  have hMaps : ∀ n ∈ N, Q.filter (· ∣ n) ∈ Ts := by
    intro n hn
    exact mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), (mem_filter.mp hn).2⟩
  have hCard : N.card = ∑ T ∈ Ts, (patterns Q T).card := by
    rw [Finset.card_eq_sum_card_fiberwise hMaps]
    apply sum_congr rfl
    intro T hT
    congr 1
    ext n
    have hR := (mem_filter.mp hT).2
    simp only [N, patterns, mem_filter, and_assoc]
    exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,h.2 ▸ hR,h.2⟩⟩
  change (N.card : ℝ) / q = ∑ T ∈ Ts, _
  rw [hCard, Nat.cast_sum, Finset.sum_div]
  apply sum_congr rfl
  intro T hT
  exact weight_eq Q T hQ (mem_powerset.mp (mem_filter.mp hT).1)

end PrimePattern

open Filter
open scoped Topology

namespace FactorDensity

private def Modular (m : ℕ) (f : ℕ → ℝ) := ∀ a b, a ≡ b [MOD m] → f a = f b

private noncomputable def mean (M : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ n ∈ range M, f n) / M

private noncomputable def flag (P : ℕ → Prop) (n : ℕ) : ℝ := by
  classical
  exact if P n then 1 else 0

private theorem flag_nonneg (P : ℕ → Prop) (n : ℕ) : 0 ≤ flag P n := by
  unfold flag
  split <;> norm_num

private theorem flag_le_one (P : ℕ → Prop) (n : ℕ) : flag P n ≤ 1 := by
  unfold flag
  split <;> norm_num

private theorem modular_flag {M : ℕ} {P : ℕ → Prop}
    (h : ∀ a b, a ≡ b [MOD M] → (P a ↔ P b)) : Modular M (flag P) := by
  classical
  intro a b hab
  unfold flag
  simp only [h a b hab]

private theorem sum_blocks {M : ℕ} {f : ℕ → ℝ} (hf : Modular M f) (q : ℕ) :
    (∑ n ∈ range (M*q), f n) = (q : ℝ) * ∑ n ∈ range M, f n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, sum_range_add, ih, Nat.cast_succ, add_mul, one_mul]
    congr 1
    apply sum_congr rfl
    intro n _
    exact hf _ _ (by simp [Nat.ModEq, Nat.add_mod])

private theorem mean_tendsto {M : ℕ} (hM : 0 < M) {f : ℕ → ℝ} (hf : Modular M f)
    (hlo : ∀ n, 0 ≤ f n) (hhi : ∀ n, f n ≤ 1) :
    Tendsto (fun N => mean N f) atTop (𝓝 (mean M f)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hM' : 0 < (M : ℝ) := by exact_mod_cast hM
  have hLarge : ∀ᶠ N : ℕ in atTop, (M : ℝ)/ε < (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  filter_upwards [eventually_ge_atTop (1 : ℕ), hLarge] with N hN hNlarge
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hdecomp : (N : ℝ) = (M : ℝ) * ((N/M : ℕ) : ℝ) + ((N%M : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N M).symm
  let R := ∑ n ∈ range (N%M), f n
  have hR₀ : 0 ≤ R := sum_nonneg fun n _ => hlo n
  have hR₁ : R ≤ ((N%M : ℕ) : ℝ) := by
    have h := sum_le_sum (s := range (N%M)) (fun n _ => hhi n)
    simpa using h
  have hμ₀ : 0 ≤ mean M f := div_nonneg (sum_nonneg fun n _ => hlo n) (by positivity)
  have hμ₁ : mean M f ≤ 1 := by
    rw [mean, div_le_one₀ hM']
    have h := sum_le_sum (s := range M) (fun n _ => hhi n)
    simpa using h
  have hNsum : (∑ n ∈ range N, f n) =
      ((N/M : ℕ) : ℝ) * (∑ n ∈ range M, f n) + R := by
    conv_lhs => rw [← Nat.div_add_mod N M, sum_range_add, sum_blocks hf]
    congr 1
    apply sum_congr rfl
    intro n _
    exact hf _ _ (by simp [Nat.ModEq, Nat.add_mod])
  have herr : mean N f - mean M f = (R - ((N%M : ℕ) : ℝ)*mean M f)/N := by
    rw [mean, hNsum]
    have he : (N : ℝ) * mean M f =
        ((N/M : ℕ) : ℝ) * (∑ n ∈ range M, f n) + ((N%M : ℕ) : ℝ) * mean M f := by
      conv_lhs => rw [hdecomp, add_mul]
      rw [mean]
      field_simp
    field_simp
    linarith
  rw [Real.dist_eq, herr, abs_div, abs_of_pos hN']
  have hMr : ((N%M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.mod_lt N hM).le
  have hμR₀ : 0 ≤ ((N%M : ℕ) : ℝ) * mean M f := by positivity
  have hμR₁ : ((N%M : ℕ) : ℝ) * mean M f ≤ ((N%M : ℕ) : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hμ₁ (by positivity : 0 ≤ ((N%M : ℕ) : ℝ))
  apply (div_lt_iff₀ hN').mpr
  have hbound := (div_lt_iff₀ hε).mp hNlarge
  rw [abs_lt]
  constructor <;> linarith

private theorem mean_flag_card (N : ℕ) (P : ℕ → Prop) :
    mean N (flag P) = (((range N).filter P).card : ℝ) / N := by
  classical
  unfold mean
  congr 1
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hn : P n <;> simp [flag, hn]

private theorem density_erase {M : ℕ} {P : ℕ → Prop} (hM : 0 < M)
    (hper : ∀ a b, a ≡ b [MOD M] → (P a ↔ P b)) :
    {n : ℕ | 0 < n ∧ P n}.HasDensity ((((range M).filter P).card : ℝ) / M) := by
  classical
  have hμ := mean_tendsto hM (modular_flag hper) (flag_nonneg P) (flag_le_one P)
  rw [mean_flag_card] at hμ
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlow := hμ.sub hinv
  rw [sub_zero] at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hμ
  all_goals
    intro N
    dsimp only
    rw [mean_flag_card]
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    have hfin : ({n : ℕ | 0 < n ∧ P n} ∩ Set.Iio N) =
        ↑(((range N).filter P).erase 0) := by
      ext n
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, mem_coe, mem_erase,
        mem_filter, mem_range]
      rw [Nat.pos_iff_ne_zero]
      tauto
    rw [hfin, Set.ncard_coe_finset]
  · let A := (range N).filter P
    have hc : (A.card : ℝ) ≤ ((A.erase 0).card : ℝ) + 1 := by
      have hc := pred_card_le_card_erase (s := A) (a := 0)
      exact_mod_cast (show A.card ≤ (A.erase 0).card + 1 by omega)
    change (A.card : ℝ) / N - (N : ℝ)⁻¹ ≤ ((A.erase 0).card : ℝ) / N
    rw [← one_div, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast (card_le_card (erase_subset 0 ((range N).filter P)))) (by positivity)

private theorem prime_product_factor (S T : Finset ℕ) (hT : T ⊆ S)
    (hS : ∀ q ∈ S, q.Prime) :
    (∏ q ∈ T, 1 / (q : ℝ)) * (∏ q ∈ S \ T, (1 - 1 / (q : ℝ))) =
      (∏ q ∈ S, (1 - 1 / (q : ℝ))) * ∏ q ∈ T, 1 / ((q : ℝ) - 1) := by
  have h := prod_sdiff (f := fun q : ℕ => 1 - 1 / (q : ℝ)) hT
  rw [← h, mul_assoc, ← prod_mul_distrib, mul_comm]
  congr 1
  apply prod_congr rfl
  intro q hq
  have h1 : 1 < (q : ℝ) := by exact_mod_cast (hS q (hT hq)).one_lt
  have h0 : (q : ℝ) ≠ 0 := by linarith
  have hne : (q : ℝ) - 1 ≠ 0 := by linarith
  field_simp

theorem density_formula (k p : ℕ) (hp : p.Prime) :
    (Erdos690.kthPrimeFactorSet (k+1) p).HasDensity
      ((∏ x ∈ Nat.primesBelow p, (1-1/(x:ℝ))) *
       (∑ T ∈ (Nat.primesBelow p).powersetCard k, ∏ x ∈ T, 1/((x:ℝ)-1)) / p) := by
  classical
  let S := Nat.primesBelow p
  let Q := insert p S
  let M := ∏ q ∈ Q, q
  let R := fun T : Finset ℕ => p ∈ T ∧ (T.erase p).card = k
  let P := fun n : ℕ => R (Q.filter (· ∣ n))
  have hpS : p ∉ S := by simp [S, Nat.mem_primesBelow]
  have hS (q) (hq : q ∈ S) : q.Prime := (Nat.mem_primesBelow.mp hq).2
  have hQ (q) (hq : q ∈ Q) : q.Prime :=
    (mem_insert.mp hq).elim (fun h => h ▸ hp) (hS q)
  have hper (a b : ℕ) (hab : a ≡ b [MOD M]) : P a ↔ P b := by
    unfold P
    have h : Q.filter (· ∣ a) = Q.filter (· ∣ b) :=
      filter_congr fun q hq => hab.dvd_iff (dvd_prod_of_mem id hq)
    rw [h]
  have heq : Erdos690.kthPrimeFactorSet (k+1) p = {n : ℕ | 0 < n ∧ P n} := by
    ext n
    unfold Erdos690.kthPrimeFactorSet P R
    simp only [Set.mem_ofPred_eq, Nat.add_sub_cancel]
    have hfactor (hn : 0 < n) : (Q.filter (· ∣ n)).erase p = n.primeFactors.filter (· < p) := by
      rw [← filter_erase]
      have e : Q.erase p = S := erase_insert hpS
      rw [e]
      ext q
      simp only [mem_filter, S, Nat.mem_primesBelow, Nat.mem_primeFactors_of_ne_zero hn.ne']
      tauto
    constructor <;> rintro ⟨hn, hpn, hcard⟩ <;> refine ⟨hn, ?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_insert_self .., Nat.dvd_of_mem_primeFactors hpn⟩
    · rw [hfactor hn, hcard]
    · exact (Nat.mem_primeFactors_of_ne_zero hn.ne').mpr ⟨hp, (mem_filter.mp hpn).2⟩
    · rw [← hfactor hn, hcard]
  rw [heq]
  have h := density_erase (prod_pos fun q hq => (hQ q hq).pos) hper
  convert h using 1
  symm
  rw [PrimePattern.exact_probability Q hQ R]
  have himage : Q.powerset.filter R =
      (S.powersetCard k).image (insert p) := by
    ext T
    constructor
    · intro hT
      obtain ⟨hsub, hm, hc⟩ := (mem_filter.mp hT).imp_left mem_powerset.mp
      have hts : T.erase p ⊆ S := by
        intro q hq
        exact (mem_insert.mp (hsub (mem_erase.mp hq).2)).resolve_left (mem_erase.mp hq).1
      exact mem_image.mpr ⟨T.erase p, mem_powersetCard.mpr ⟨hts, hc⟩, insert_erase hm⟩
    · intro hT
      obtain ⟨U,hU,rfl⟩ := mem_image.mp hT
      obtain ⟨hu,hc⟩ := mem_powersetCard.mp hU
      exact mem_filter.mpr ⟨mem_powerset.mpr (insert_subset_insert _ hu),
        mem_insert_self .., by simpa [erase_insert (fun h => hpS (hu h))] using hc⟩
  rw [filter_congr_decidable Q.powerset R (Classical.decPred R), himage, sum_image]
  · have he : (∑ T ∈ S.powersetCard k,
        (∏ q ∈ insert p T, 1/(q:ℝ)) * ∏ q ∈ Q \ insert p T, (1-1/(q:ℝ))) =
        (∏ x ∈ S, (1-1/(x:ℝ))) *
          (∑ T ∈ S.powersetCard k, ∏ x ∈ T, 1/((x:ℝ)-1)) / p := by
      rw [mul_sum, sum_div]
      apply sum_congr rfl
      intro T hT
      have ht := (mem_powersetCard.mp hT).1
      have hpt : p ∉ T := fun h => hpS (ht h)
      have hd : Q \ insert p T = S \ T := by
        ext q
        by_cases hq : q = p
        · subst q
          simp [hpS]
        · simp [Q, hq]
      rw [prod_insert hpt, hd, mul_assoc, prime_product_factor S T ht hS]
      ring
    exact he
  · intro T hT U hU h
    have hpT : p ∉ T := fun hpT => hpS ((mem_powersetCard.mp hT).1 hpT)
    have hpU : p ∉ U := fun hpU => hpS ((mem_powersetCard.mp hU).1 hpU)
    simpa only [erase_insert hpT, erase_insert hpU] using congrArg (fun V : Finset ℕ => V.erase p) h

end FactorDensity

theorem OMA.solution : OMA.R_Erdos690_erdos_690_variants_large_k_R1.H1 := FactorDensity.density_formula