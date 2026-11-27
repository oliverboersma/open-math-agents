import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1

 /-! A weighted pigeonhole argument for the common-divisor step of Bloom's
unit-fraction theorem. Separate off the distinguished prime power q and all
remaining full prime powers above exp(log N / (2 (log log N)^2)).
One obligation gives the divisor decomposition. The other bounds the total
reciprocal weight of these rough divisors, with an extra penalty when they
have many prime factors. The proof below recovers the cofactor family and
its normal number of distinct prime factors. -/
namespace OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1_H1_R1
open Real Filter Finset
open scoped Classical

def H1 : Prop := ∀ᶠ N : ℕ in atTop,
  let w := log (log N)
  let M := (N:ℝ)^(1-1/w)
  let R := (range N).filter (fun d => 0 < d ∧ ∀ p : ℕ, p ∈ d.primeFactors →
      exp (log N / (2*w^2)) < (p : ℝ) ^ d.factorization p)
  ∀ n q : ℕ, 0 < n → n < N → M ≤ n → (n.primeFactors.card : ℝ) ≤ 2*w →
    IsPrimePow q → q ∣ n → Nat.Coprime q (n/q) →
    ∃ d ∈ R, M*(N:ℝ)^(-2/w) < q*(d:ℝ) ∧ q*d ∣ n ∧ Nat.Coprime (q*d) (n/(q*d))

def H2 : Prop := ∀ᶠ N : ℕ in atTop,
  let w := log (log N)
  let R := (range N).filter (fun d => 0 < d ∧ ∀ p : ℕ, p ∈ d.primeFactors →
      exp (log N / (2*w^2)) < (p : ℝ) ^ d.factorization p)
  ∑ d ∈ R, (if (d.primeFactors.card : ℝ) ≤ w/110 then (log N)^(-(1/99:ℝ))
    else 1+log N) / d < (log N)^(-(1/100:ℝ))/2

lemma prime_count {q d m : ℕ} (hq : IsPrimePow q) (hd : d ≠ 0) (hm : m ≠ 0) :
    (q*d*m).primeFactors.card ≤ 1 + d.primeFactors.card + m.primeFactors.card := by
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff _).mp hq
  rw [Nat.primeFactors_mul (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hd) hm,
    Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) hd, Nat.primeFactors_prime_pow (by omega) hp]
  have := card_union_le ({p} : Finset ℕ) d.primeFactors
  simp only [card_singleton] at this
  exact (card_union_le _ _).trans (Nat.add_le_add_right this _)

lemma harmonic_budget {C : Finset ℕ} {N : ℕ} (hc : C ⊆ Icc 1 N) :
    ∑ m ∈ C, (1:ℝ)/m ≤ 1+log N := by
  apply le_trans (sum_le_sum_of_subset_of_nonneg hc (fun _ _ _ => by positivity))
  simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
    using harmonic_le_one_add_log N

theorem main : H1 → H2 → OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1.H1 := by
  intro split bound
  have large : ∀ᶠ N : ℕ in atTop, (2000:ℝ) ≤ log (log N) :=
    ((tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  unfold H1 at split
  unfold H2 at bound
  filter_upwards [split,bound,large] with N hsplit hbound hw
  intro A q hz hA reg hq mass
  let w := log (log N)
  let M := (N:ℝ)^(1-1/w)
  let K := M*(N:ℝ)^(-2/w)
  let R := (range N).filter (fun d => 0 < d ∧ ∀ p : ℕ, p ∈ d.primeFactors →
      exp (log N / (2*w^2)) < (p : ℝ) ^ d.factorization p)
  let S := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
  let price (d : ℕ) := if (d.primeFactors.card:ℝ) ≤ w/110 then (log N)^(-(1/99:ℝ)) else 1+log N
  change ∑ d ∈ R, price d/d < _ at hbound
  have can (n : ℕ) (hn : n ∈ S) : ∃ d ∈ R, K < q*(d:ℝ) ∧ q*d ∣ n ∧ Nat.Coprime (q*d) (n/(q*d)) := by
    obtain ⟨ha,hd,hc⟩ := mem_filter.mp hn
    have rr := reg n ha
    exact hsplit n q (Nat.pos_of_ne_zero fun h => hz (h ▸ ha)) (mem_range.mp (hA ha)) rr.1 rr.2.2.2 hq hd hc
  let f (n : ℕ) := if h : n∈S then (can n h).choose else 1
  have hf (n : ℕ) (hn : n∈S) : f n ∈ R ∧ K < q*(f n:ℝ) ∧ q*f n ∣ n ∧ Nat.Coprime (q*f n) (n/(q*f n)) := by
    simpa [f,hn] using (can n hn).choose_spec
  let F (d : ℕ) := S.filter (fun n => f n = d)
  let C (d : ℕ) := (F d).image (fun n => n/(q*d))
  have spec {d n : ℕ} (hn : n ∈ F d) : n ∈ A ∧ K < q*(d:ℝ) ∧
      q*d*(n/(q*d)) = n ∧ Nat.Coprime (q*d) (n/(q*d)) := by
    obtain ⟨hs,he⟩ := mem_filter.mp hn
    obtain ⟨_,hb,hd,hc⟩ := he ▸ hf n hs
    exact ⟨(mem_filter.mp hs).1,hb,Nat.mul_div_cancel' hd,hc⟩
  have co {d m : ℕ} (hm : m ∈ C d) : q*d*m ∈ A ∧ K < q*(d:ℝ) ∧ Nat.Coprime m (q*d) ∧ 0 < m := by
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hm
    obtain ⟨ha,hK,eq,hc⟩ := spec hn
    refine ⟨eq.symm ▸ ha,hK,hc.symm,Nat.pos_of_ne_zero ?_⟩
    intro he
    rw [he,mul_zero] at eq
    exact hz (eq.symm ▸ ha)
  have enough : ∃ d ∈ R, price d < ∑ m ∈ C d, (1:ℝ)/m := by
    by_contra! none
    apply (not_le_of_gt hbound)
    apply le_trans mass
    change ∑ n ∈ S, (q:ℝ)/n ≤ _
    rw [← sum_fiberwise_of_maps_to (s := S) (t := R) (g := f) (fun n hn => (hf n hn).1)]
    apply sum_le_sum
    intro d hd
    change ∑ n ∈ F d, (q:ℝ)/n ≤ _
    have inj : Set.InjOn (fun n => n/(q*d)) (↑(F d)) := by
      intro n hn m hm he
      simpa only [(spec hn).2.2.1,(spec hm).2.2.1] using congrArg (fun t => q*d*t) he
    calc
      _ = (∑ m ∈ C d, (1:ℝ)/m)/d := by
        rw [sum_div,Finset.sum_image inj]
        apply sum_congr rfl
        intro n hn
        have hnz : n≠0 := fun he => hz (he ▸ (spec hn).1)
        have hqz : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
        have hdz : (d:ℝ) ≠ 0 := by exact_mod_cast (mem_filter.mp hd).2.1.ne'
        have he : (q:ℝ)*d*(n/(q*d) : ℕ) = n := by exact_mod_cast (spec hn).2.2.1
        have hmz : ((n/(q*d):ℕ):ℝ) ≠ 0 := by intro h; rw [h,mul_zero] at he; exact hnz (by exact_mod_cast he.symm)
        field_simp
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_right (none d hd) (by positivity)
  obtain ⟨d,hd,heavy⟩ := enough
  have sub : C d ⊆ Icc 1 N := by
    intro m hm
    obtain ⟨ha,_,_,hp⟩ := co hm
    exact mem_Icc.mpr ⟨hp, (Nat.le_of_dvd (Nat.pos_of_ne_zero fun he => hz (he ▸ ha)) (dvd_mul_left m _)).trans (mem_range.mp (hA ha)).le⟩
  have hl : (d.primeFactors.card:ℝ) ≤ w/110 := by
    by_contra high
    exact (not_lt_of_ge (harmonic_budget sub)) (by simpa [price,high] using heavy)
  have lower : (log N)^(-(1/99:ℝ)) < ∑ m ∈ C d, (1:ℝ)/m := by simpa [price,hl] using heavy
  have hne : (C d).Nonempty := by
    by_contra! empty
    rw [empty,sum_empty] at lower
    have hlog : 0 ≤ log N := by
      by_cases h : N=0
      · simp [h]
      · exact log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)
    exact (not_lt_of_ge (rpow_nonneg hlog _)) lower
  obtain ⟨m₀,hm₀⟩ := hne
  have hKD : K < ((q*d : ℕ) : ℝ) := by rw [Nat.cast_mul]; exact (co hm₀).2.1
  refine ⟨q*d,C d,hKD,dvd_mul_right q d,lower.le,?_⟩
  intro m hm
  obtain ⟨ha,_,hc,hpos⟩ := co hm
  obtain ⟨_,_,hlo,hhi⟩ := reg _ ha
  have hdz : d≠0 := (mem_filter.mp hd).2.1.ne'
  have hnum : ((q*d*m).primeFactors.card:ℝ) ≤ 1+d.primeFactors.card+m.primeFactors.card := by
    exact_mod_cast prime_count hq hdz hpos.ne'
  have hmono : (m.primeFactors.card:ℝ) ≤ (q*d*m).primeFactors.card := by
    exact_mod_cast card_le_card (Nat.primeFactors_mono (dvd_mul_left m (q*d)) (fun he => hz (he ▸ ha)))
  refine ⟨ha,hc,?_,hmono.trans hhi⟩
  change (99/100:ℝ)*w ≤ _ at hlo
  change 2000 ≤ w at hw
  change (1-2/99:ℝ)*w ≤ _
  linarith
end OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1_H1_R1
