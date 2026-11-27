import OMAReductions.R_Erdos375_erdos_375_variants_bounded_gap_R1

/-! Count two prime divisors just above the fourth root of x. Their cofactor
is short, four distinct divisors are already too large, and summing the two
endpoint floor errors reduces the short interval count to a bilinear estimate.
Credit: @marcusbuffett. -/

namespace OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1

open Finset Filter
open scoped BigOperators

private lemma count_div (x k d : ℕ) :
    ((Ioc x (x+k)).filter (d ∣ ·)).card = (x+k)/d - x/d := by
  have hu : (Ioc 0 (x+k)).filter (d ∣ ·) =
      ((Ioc 0 x).filter (d ∣ ·)) ∪ ((Ioc x (x+k)).filter (d ∣ ·)) := by
    ext n
    simp only [mem_union, mem_filter, mem_Ioc]
    omega
  have hd : Disjoint ((Ioc 0 x).filter (d ∣ ·)) ((Ioc x (x+k)).filter (d ∣ ·)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [mem_filter, mem_Ioc] at hn hm
    omega
  have hh := congrArg Finset.card hu
  rw [card_union_of_disjoint hd, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at hh
  omega

private lemma bound_fiber {N n k : ℕ} (hN : 2 ≤ N) (hn : 0 < n)
    (hb : n ≤ N^1001) (hk : N^499 ≤ k) :
    let P := (Ioc (N^251) (N^252)).filter Nat.Prime
    ((P ×ˢ P).filter (fun w => w.1*w.2 ∣ n)).card ≤
      if n ∈ Nat.smoothNumbers (k+1) then 9 else 0 := by
  classical
  intro P
  let Q := P.filter (· ∣ n)
  have hmem {p : ℕ} (hp : p ∈ P) : N^251 < p ∧ p ≤ N^252 ∧ p.Prime := by
    simpa [P, and_assoc] using hp
  have hq : Q ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨h,d⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(hmem h).2.2,d,hn.ne'⟩
  have hc : Q.card ≤ 3 := by
    by_contra! h
    have hl : (N^251)^Q.card ≤ ∏ p ∈ Q, p := by
      simpa using Finset.prod_le_prod' (fun p (hp : p ∈ Q) => (hmem (mem_filter.mp hp).1).1.le)
    have h4 : (N^251)^4 ≤ (N^251)^Q.card :=
      Nat.pow_le_pow_right (by positivity) (by omega)
    have hd := (Finset.prod_dvd_prod_of_subset Q n.primeFactors id hq).trans (Nat.prod_primeFactors_dvd n)
    have he : (N^251)^4 = N^1004 := by rw [← pow_mul]
    have hg : N^1001 < N^1004 := Nat.pow_lt_pow_right (by omega) (by decide)
    rw [he] at h4
    have hh := Nat.le_of_dvd hn hd
    change (∏ p ∈ Q, p) ≤ n at hh
    omega
  let T := (P ×ˢ P).filter (fun w => w.1*w.2 ∣ n)
  have hsub : T ⊆ Q ×ˢ Q := by
    intro w hw
    obtain ⟨hw,hd⟩ := mem_filter.mp hw
    obtain ⟨h1,h2⟩ := mem_product.mp hw
    exact mem_product.mpr ⟨mem_filter.mpr ⟨h1,(dvd_mul_right _ _).trans hd⟩,
      mem_filter.mpr ⟨h2,(dvd_mul_left _ _).trans hd⟩⟩
  change T.card ≤ _
  split_ifs with hs
  · have ht := card_le_card hsub
    rw [card_product] at ht
    nlinarith
  · apply le_of_eq
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨p,q⟩ hw
    obtain ⟨hw,hd⟩ := mem_filter.mp hw
    obtain ⟨hp,hq⟩ := mem_product.mp hw
    obtain ⟨r,hr⟩ := hd
    have hpq : N^502 ≤ p*q := by
      rw [show (502:ℕ) = 251+251 by decide, pow_add]
      exact Nat.mul_le_mul (hmem hp).1.le (hmem hq).1.le
    have hr0 : 0 < r := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hr; omega
    have h502 : 0 < N^502 := by positivity
    have hrk : r ≤ N^499 := by
      apply Nat.le_of_mul_le_mul_left _ h502
      calc N^502*r ≤ (p*q)*r := Nat.mul_le_mul_right _ hpq
           _ = n := hr.symm
           _ ≤ N^502*N^499 := by simpa [← pow_add] using hb
    have he : N^252 ≤ N^499 := Nat.pow_le_pow_right (by omega) (by decide)
    apply hs
    rw [hr]
    apply Nat.mul_mem_smoothNumbers
    · apply Nat.mul_mem_smoothNumbers
      · exact Nat.mem_smoothNumbers_of_lt (hmem hp).2.2.pos (by have := (hmem hp).2.1; omega)
      · exact Nat.mem_smoothNumbers_of_lt (hmem hq).2.2.pos (by have := (hmem hq).2.1; omega)
    · exact Nat.mem_smoothNumbers_of_lt hr0 (by omega)

private lemma smooth_indices (x k : ℕ) :
    ((Ioc x (x+k)).filter (· ∈ Nat.smoothNumbers (k+1))).card =
    ((univ : Finset (Fin k)).filter (fun i => x+i.val+1 ∈ Nat.smoothNumbers (k+1))).card := by
  symm
  apply card_bij (fun i _ => x+i.val+1)
  · intro i hi
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by have := i.isLt; omega⟩,(mem_filter.mp hi).2⟩
  · intro i hi j hj h
    apply Fin.ext
    omega
  · intro n hn
    obtain ⟨h,hs⟩ := mem_filter.mp hn
    obtain ⟨hl,hr⟩ := mem_Ioc.mp h
    let i : Fin k := ⟨n-x-1,by omega⟩
    have he : x+i.val+1=n := by dsimp [i]; omega
    exact ⟨i,mem_filter.mpr ⟨mem_univ _,he.symm ▸ hs⟩,he⟩

private lemma count_upper {N x k : ℕ} (hN : 2 ≤ N) (hb : x+k ≤ N^1001) (hk : N^499 ≤ k) :
    let P := (Ioc (N^251) (N^252)).filter Nat.Prime
    (∑ w ∈ P ×ˢ P, ((x+k)/(w.1*w.2)-x/(w.1*w.2))) ≤
      9 * ((univ : Finset (Fin k)).filter (fun i => x+i.val+1 ∈ Nat.smoothNumbers (k+1))).card := by
  classical
  intro P
  simp_rw [← count_div x k, card_filter]
  rw [sum_comm]
  calc _ ≤ ∑ n ∈ Ioc x (x+k), (if n ∈ Nat.smoothNumbers (k+1) then 9 else 0) := by
          apply sum_le_sum
          intro n hn
          obtain ⟨hl,hr⟩ := mem_Ioc.mp hn
          simpa only [card_filter] using bound_fiber hN (by omega : 0 < n) (hr.trans hb) hk
       _ = _ := by
          rw [← card_filter, ← smooth_indices x k, card_filter, mul_sum]
          apply sum_congr rfl
          intro n hn
          split_ifs <;> simp

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
    c ≤ ∑ p ∈ (Ioc (N^251) (N^252)).filter Nat.Prime, 1/(p:ℝ)

def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ t : ℕ, N^1000 ≤ t → t ≤ N^1001 →
    let P := (Ioc (N^251) (N^252)).filter Nat.Prime
    |∑ w ∈ P ×ˢ P, ((((t/(w.1*w.2):ℕ):ℝ) - (t:ℝ)/((w.1*w.2:ℕ):ℝ)) + 1/2)| ≤
      ε*(N:ℝ)^499

private lemma interval_lower (P : Finset ℕ) (x k : ℕ) :
    let B := fun t : ℕ => ∑ w ∈ P ×ˢ P,
      ((((t/(w.1*w.2):ℕ):ℝ) - (t:ℝ)/((w.1*w.2:ℕ):ℝ)) + 1/2)
    ((∑ w ∈ P ×ˢ P, ((x+k)/(w.1*w.2)-x/(w.1*w.2)) : ℕ) : ℝ) =
      B (x+k) - B x + (k:ℝ)*(∑ p ∈ P, 1/(p:ℝ))^2 := by
  dsimp only
  have hs : (∑ p ∈ P, 1/(p:ℝ))^2 = ∑ w ∈ P ×ˢ P, 1/((w.1*w.2:ℕ):ℝ) := by
    rw [sq, sum_mul, sum_product]
    apply sum_congr rfl
    intro p hp
    rw [mul_sum]
    apply sum_congr rfl
    intro q hq
    simp [Nat.cast_mul, div_eq_mul_inv, mul_comm]
  rw [hs, ← sum_sub_distrib, mul_sum, ← sum_add_distrib, Nat.cast_sum]
  apply sum_congr rfl
  intro w hw
  rw [Nat.cast_sub (Nat.div_le_div_right (by omega : x ≤ x+k)), Nat.cast_add]
  ring

theorem main : H1 → H2 → OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1.H1 := by
  rintro ⟨c,hc,hm⟩ herror
  refine ⟨499/1000,by norm_num,by norm_num,c^2/18,by positivity,?_⟩
  let ε := c^2/4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ht : Tendsto (Nat.nthRoot 1000) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b^1000)] with x hx
    exact (Nat.le_nthRoot_iff (by decide)).2 hx
  filter_upwards [ht.eventually hm, ht.eventually (herror ε hε),
    ht.eventually (eventually_ge_atTop (2^1001))] with x hx he hlarge
  let N := Nat.nthRoot 1000 x
  let k := ⌊(x:ℝ)^(499/1000:ℝ)⌋₊
  let P := (Ioc (N^251) (N^252)).filter Nat.Prime
  change c ≤ ∑ p ∈ P, 1/(p:ℝ) at hx
  change 2^1001 ≤ N at hlarge
  have hN : 2 ≤ N := (show 2 ≤ 2^1001 from (pow_one (2:ℕ)) ▸ Nat.pow_le_pow_right (by decide) (by decide : 1 ≤ 1001)).trans hlarge
  have hl : N^1000 ≤ x := Nat.pow_nthRoot_le (.inl (by decide))
  have hx1 : 1 ≤ x := le_trans (Nat.one_le_pow _ _ (by omega : 0 < N)) hl
  have hkx : k ≤ x := by
    apply Nat.floor_le_of_le
    exact Real.rpow_le_self_of_one_le (by exact_mod_cast hx1) (by norm_num)
  have hk : N^499 ≤ k := by
    apply Nat.le_floor
    push_cast
    have h := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (N:ℝ)^1000)
      (by exact_mod_cast hl : (N:ℝ)^1000 ≤ (x:ℝ)) (by norm_num : 0 ≤ (499/1000:ℝ))
    rw [← Real.rpow_natCast_mul (by positivity)] at h
    rw [show ((1000:ℕ):ℝ)*(499/1000) = ((499:ℕ):ℝ) by norm_num, Real.rpow_natCast] at h
    exact h
  have hu : x+k ≤ N^1001 := by
    have hlt : x < (N+1)^1000 := (Nat.nthRoot_lt_iff (by decide : (1000:ℕ) ≠ 0)).mp (show N < N+1 by omega)
    have hle : (N+1)^1000 ≤ (2*N)^1000 := Nat.pow_le_pow_left (by omega) _
    rw [mul_pow] at hle
    calc x+k ≤ 2*(2^1000*N^1000) := by omega
         _ = 2^1001*N^1000 := by rw [← Nat.mul_assoc, ← pow_succ' (2:ℕ) 1000]
         _ ≤ N*N^1000 := Nat.mul_le_mul_right _ hlarge
         _ = N^1001 := by rw [pow_succ N 1000, Nat.mul_comm]
  let B := fun t : ℕ => ∑ w ∈ P ×ˢ P,
    ((((t/(w.1*w.2):ℕ):ℝ) - (t:ℝ)/((w.1*w.2:ℕ):ℝ)) + 1/2)
  have he1 : |B x| ≤ ε*(N:ℝ)^499 := he x hl ((Nat.le_add_right x k).trans hu)
  have he2 : |B (x+k)| ≤ ε*(N:ℝ)^499 := he (x+k) (hl.trans (Nat.le_add_right x k)) hu
  have herr : ε*(N:ℝ)^499 ≤ ε*(k:ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hε.le
    exact_mod_cast hk
  have hd := (abs_le.mp (he1.trans herr)).2
  have hd' := (abs_le.mp (he2.trans herr)).1
  have hsq := mul_self_le_mul_self hc.le hx
  rw [←sq,←sq] at hsq
  have hpos := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) k)
  have hu' := count_upper hN hu hk
  have hreal : ((∑ w ∈ P ×ˢ P, ((x+k)/(w.1*w.2)-x/(w.1*w.2)) : ℕ) : ℝ) ≤
      9 * (((univ : Finset (Fin k)).filter
        (fun i => x+i.val+1 ∈ Nat.smoothNumbers (k+1))).card : ℝ) := by exact_mod_cast hu'
  rw [interval_lower] at hreal
  change B (x+k) - B x + _ ≤ _ at hreal
  change c^2/18*(k:ℝ) ≤ _
  dsimp [ε] at hd hd'
  linarith

end OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1
