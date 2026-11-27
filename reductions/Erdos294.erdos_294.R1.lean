import FormalConjectures.ErdosProblems.«294»
import Mathlib

/-!
Glue two unit-fraction representations on disjoint denominator intervals as in
Section 4 of Liu and Sawhney. A short block is dilated by the prescribed least
denominator. The long block fills the remaining mass. This separates smooth
denominator representation (Lemma 4.1) from the choice of interval scales.
The proved upper bound is from vkascheev's merged PR #833.
-/

namespace OMA.R_Erdos294_erdos_294_R1

open Filter Real

namespace OMAHelp

theorem key (p N : ℕ) (hp : p.Prime) (h : (N / p) * Nat.lcmUpto (N / p) < p) :
    ¬ Erdos294.HasUnitFractionSolution p N := by
  rintro ⟨s, hps, hs, hsum⟩
  set L := N / p with hL
  set D := Nat.lcmUpto L with hD
  set J := s.filter (fun n => p ∣ n) with hJ
  set R := s.filter (fun n => ¬ p ∣ n) with hR
  set E := ∏ n ∈ R, n with hE
  have hp2 := hp.two_le
  have hpos : ∀ n ∈ s, 0 < n := fun n hn => by have := (hs n hn).1; omega
  have hDpos : 0 < D := Nat.lcmUpto_pos L
  have hdivJ : ∀ n ∈ J, n / p ∣ D := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have h1 : 1 ≤ n / p := (Nat.one_le_div_iff hp.pos).2 (hs n hn.1).1
    have h2 : n / p ≤ L := Nat.div_le_div_right (hs n hn.1).2
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hdivR : ∀ n ∈ R, n ∣ E := fun n hn => Finset.dvd_prod_of_mem _ hn
  have hnat : p * D * E = (∑ n ∈ R, p * D * (E / n)) + E * ∑ n ∈ J, D / (n / p) := by
    apply Nat.cast_injective (R := ℚ)
    have e1 : ((p * D * E : ℕ) : ℚ) = ∑ n ∈ s, ((p * D * E : ℕ) : ℚ) * (1 / n) := by
      rw [← Finset.mul_sum, hsum, mul_one]
    rw [e1, ← Finset.sum_filter_add_sum_filter_not s (fun n => p ∣ n)]
    push_cast
    rw [add_comm, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℚ) ≠ 0 := by
        have := hpos n (Finset.mem_filter.1 hn).1; positivity
      rw [Nat.cast_div (hdivR n hn) hn0]
      field_simp
    · apply Finset.sum_congr rfl
      intro n hn
      have hnp : p ∣ n := (Finset.mem_filter.1 hn).2
      have hn0 : 0 < n := hpos n (Finset.mem_filter.1 hn).1
      have hq0 : ((n / p : ℕ) : ℚ) ≠ 0 := by
        have : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 hnp) hp.pos
        positivity
      rw [Nat.cast_div (hdivJ n hn) hq0, Nat.cast_div hnp (by exact_mod_cast hp.ne_zero)]
      have : (n : ℚ) ≠ 0 := by positivity
      have : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp
  set A := ∑ n ∈ J, D / (n / p) with hA
  have hdvd : p ∣ E * A := by
    have h1 : p ∣ ∑ n ∈ R, p * D * (E / n) :=
      Finset.dvd_sum fun n _ => by rw [mul_assoc]; exact dvd_mul_right _ _
    have h2 : p ∣ p * D * E := by rw [mul_assoc]; exact dvd_mul_right _ _
    rw [hnat] at h2
    exact (Nat.dvd_add_right h1).1 h2
  have hpJ : p ∈ J := Finset.mem_filter.2 ⟨hps, dvd_refl p⟩
  have hApos : 0 < A := by
    have : D / (p / p) ≤ A := Finset.single_le_sum (f := fun n => D / (n / p))
      (fun _ _ => Nat.zero_le _) hpJ
    rw [Nat.div_self hp.pos, Nat.div_one] at this
    omega
  have hcard : J.card ≤ L := by
    have hsub : J ⊆ (Finset.Icc 1 L).image (fun j => j * p) := by
      intro n hn
      rw [Finset.mem_image]
      have hn' := Finset.mem_filter.1 hn
      refine ⟨n / p, Finset.mem_Icc.2 ⟨(Nat.one_le_div_iff hp.pos).2 (hs n hn'.1).1,
        Nat.div_le_div_right (hs n hn'.1).2⟩, Nat.div_mul_cancel hn'.2⟩
    calc J.card ≤ ((Finset.Icc 1 L).image (fun j => j * p)).card := Finset.card_le_card hsub
      _ ≤ (Finset.Icc 1 L).card := Finset.card_image_le
      _ = L := by simp
  have hAle : A ≤ L * D := by
    calc A ≤ J.card • D := Finset.sum_le_card_nsmul _ _ _ (fun n _ => Nat.div_le_self _ _)
      _ ≤ L * D := by rw [smul_eq_mul]; exact Nat.mul_le_mul_right _ hcard
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with hE' | hA'
  · obtain ⟨n, hn, hpn⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hE'
    exact (Finset.mem_filter.1 hn).2 hpn
  · have := Nat.le_of_dvd hApos hA'
    omega


theorem bound_ev : ∀ᶠ N : ℕ in atTop, (Erdos294.t N : ℝ) ≤ 200 * ((N : ℝ) / log N) := by
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 := hlog.eventually (Real.isLittleO_log_id_atTop.bound (by norm_num : (0:ℝ) < 1 / 4))
  have h2 := hlog.eventually_ge_atTop 1
  filter_upwards [h1, h2, eventually_ge_atTop 2] with N h1 h2 hN2
  set x := log (N : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hNpos : (0 : ℝ) < N := by have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
                                 linarith
  have hxN : x < N := by
    have := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hexp : exp x = N := exp_log hNpos
  have hq0 : 0 ≤ 100 * (N : ℝ) / x := by positivity
  have hq1 : 1 ≤ 100 * (N : ℝ) / x := by
    rw [le_div_iff₀ hx0]; linarith
  set n0 := ⌊100 * (N : ℝ) / x⌋₊ with hn0def
  have hn0 : n0 ≠ 0 := (Nat.floor_pos.2 hq1).ne'
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul n0 hn0
  have hp_gt : 100 * (N : ℝ) / x < p := by
    have h3 := Nat.lt_floor_add_one (100 * (N : ℝ) / x)
    have h4 : (n0 : ℝ) + 1 ≤ p := by exact_mod_cast hlt
    linarith
  have hp_le : (p : ℝ) ≤ 200 * ((N : ℝ) / x) := by
    have h3 : (p : ℝ) ≤ 2 * n0 := by exact_mod_cast hle
    have h4 := Nat.floor_le hq0
    have : 200 * ((N : ℝ) / x) = 2 * (100 * N / x) := by ring
    linarith
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hkey : (N / p) * Nat.lcmUpto (N / p) < p := by
    set L := N / p with hLdef
    have hL : (L : ℝ) ≤ x / 100 := by
      have h5 := (div_lt_iff₀ hx0).1 hp_gt
      calc (L : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
        _ ≤ x / 100 := by
          rw [div_le_div_iff₀ hppos (by norm_num)]; nlinarith
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have hD : (Nat.lcmUpto L : ℝ) ≤ exp (0.07 * x) := by
      have hψ := Chebyshev.psi_le_const_mul_self hL0
      rw [Chebyshev.psi_eq_log_lcmUpto] at hψ
      have hl4 : log 4 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4); linarith
      have hDpos : (0 : ℝ) < Nat.lcmUpto L := by exact_mod_cast Nat.lcmUpto_pos L
      calc (Nat.lcmUpto L : ℝ) = exp (log (Nat.lcmUpto L)) := (exp_log hDpos).symm
        _ ≤ exp (0.07 * x) := exp_le_exp.2 (by nlinarith)
    have hlx : log x ≤ x / 4 := by
      have := h1
      simp only [norm_eq_abs, id] at this
      rw [abs_of_pos hx0] at this
      have := le_abs_self (log x)
      linarith
    have hx2 : x ^ 2 ≤ exp (x / 2) := by
      calc x ^ 2 = exp (log x) ^ 2 := by rw [exp_log hx0]
        _ = exp (2 * log x) := by rw [← exp_nat_mul]; norm_num
        _ ≤ exp (x / 2) := exp_le_exp.2 (by linarith)
    have hmain : (x / 100) * exp (0.07 * x) ≤ 100 * (N : ℝ) / x := by
      rw [le_div_iff₀ hx0]
      have e1 : exp (x / 2) * exp (0.07 * x) ≤ exp x := by
        rw [← exp_add]; exact exp_le_exp.2 (by linarith)
      have e2 : x ^ 2 * exp (0.07 * x) ≤ exp (x / 2) * exp (0.07 * x) :=
        mul_le_mul_of_nonneg_right hx2 (exp_pos _).le
      nlinarith [exp_pos (0.07 * x)]
    have : ((L * Nat.lcmUpto L : ℕ) : ℝ) < p := by
      push_cast
      calc (L : ℝ) * Nat.lcmUpto L ≤ (x / 100) * exp (0.07 * x) :=
            mul_le_mul hL hD (by positivity) (by positivity)
        _ < p := by linarith
    exact_mod_cast this
  have ht : Erdos294.t N ≤ p := Nat.sInf_le ⟨hp.pos, key p N hp hkey⟩
  have : (Erdos294.t N : ℝ) ≤ p := by exact_mod_cast ht
  linarith

end OMAHelp

theorem verified_upper : type_of% @Erdos294.erdos_294.variants.erdos_graham_upper := by
  apply Asymptotics.IsBigO.of_bound 200
  filter_upwards [OMAHelp.bound_ev, eventually_ge_atTop 2] with N h hN
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) (log_nonneg hN'))]
  exact h

open Erdos294 Filter Finset

/-- Lemma 4.1, using divisibility by the lcm of the prime powers up to the
smoothness cutoff. The denominators lie between N/16 and N. -/
def H1 : Prop := ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ d a : ℕ, 0 < d → d ∣ Nat.lcmUpto (⌊c * (N : ℝ) / ((Real.log N)^3 * (Real.log (Real.log N))^4)⌋₊) →
    d ≤ 3*a → a ≤ d →
    ∃ B : Finset ℕ, (∀ b ∈ B, N ≤ 16*b ∧ b ≤ N) ∧
      ∑ b ∈ B, (1 : ℚ)/b = (a : ℚ)/d

/-- A choice of the smaller interval scale. Its lcm exceeds four times the
large scale, divides the large-scale lcm, and its dilates stay strictly
below the second block throughout the proposed denominator range. -/
def H2 : Prop := ∀ c : ℝ, 0 < c → ∀ N₀ : ℕ, ∃ K : ℝ, ∀ᶠ N : ℕ in atTop,
    ∃ L : ℕ, N₀ ≤ L ∧ 32 ≤ L ∧ 4*N ≤ Nat.lcmUpto (⌊c * (L : ℝ) / ((Real.log L)^3 * (Real.log (Real.log L))^4)⌋₊) ∧
      Nat.lcmUpto (⌊c * (L : ℝ) / ((Real.log L)^3 * (Real.log (Real.log L))^4)⌋₊) ∣ Nat.lcmUpto (⌊c * (N : ℝ) / ((Real.log N)^3 * (Real.log (Real.log N))^4)⌋₊) ∧
      32*(L : ℝ)*|(N : ℝ) / (Real.log N * (Real.log (Real.log N))^3 * (Real.log (Real.log (Real.log N)))^K)| ≤ N

lemma two_minimum {N : ℕ} (hN : 6 ≤ N) : HasUnitFractionSolution 2 N := by
  refine ⟨{2,3,6},by decide,?_,by norm_num⟩
  intro n hn
  simp only [Finset.mem_insert,Finset.mem_singleton] at hn
  omega

/-- Combining the two representations preserves the requested smallest
denominator. No denominator from the first block reaches the second. -/
lemma glue {m N L Q u v : ℕ} (hm : 3 ≤ m) (hL : 32 ≤ L) (hN : 16*(m*L) < N)
    (hQ : 0 < Q) (hu : u ≤ Q) (hv : v + Q = u*m)
    (B D : Finset ℕ) (hB : ∀ b ∈ B, L ≤ 16*b ∧ b ≤ L)
    (hD : ∀ d ∈ D, N ≤ 16*d ∧ d ≤ N)
    (h1 : ∑ b ∈ B, (1 : ℚ)/b = (v : ℚ)/Q)
    (h2 : ∑ d ∈ D, (1 : ℚ)/d = ((Q-u : ℕ) : ℚ)/Q) :
    HasUnitFractionSolution m N := by
  classical
  let C := B.image (m*·)
  have hC (n : ℕ) (hn : n ∈ C) : m < n ∧ n ≤ m*L := by
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hb₀,hb₁⟩ := hB b hb
    exact ⟨by nlinarith [Nat.mul_le_mul_left m (show 2 ≤ b by omega)],Nat.mul_le_mul_left _ hb₁⟩
  have hmL : m ≤ m*L := by simpa using Nat.mul_le_mul_left m (show 1 ≤ L by omega)
  have hSep : Disjoint (insert m C) D := by
    apply Finset.disjoint_left.mpr
    intro d hd hd'
    have dl : d ≤ m*L := (Finset.mem_insert.mp hd).elim (fun e => e ▸ hmL) (fun hc => (hC d hc).2)
    have := (hD d hd').1
    omega
  have hmC : m ∉ C := fun h => (lt_irrefl m) (hC m h).1
  refine ⟨(insert m C) ∪ D,mem_union_left _ (mem_insert_self _ _),?_,?_⟩
  · intro n hn
    rcases mem_union.mp hn with h | h
    · rcases mem_insert.mp h with rfl | h
      · omega
      · obtain ⟨ha,hb⟩ := hC n h
        omega
    · obtain ⟨ha,hb⟩ := hD n h
      omega
  · have himg : ∑ n ∈ C, (1 : ℚ)/n = (∑ b ∈ B, (1 : ℚ)/b) / m := by
      rw [Finset.sum_div]
      unfold C
      rw [Finset.sum_image]
      · apply sum_congr rfl
        intro b hb
        push_cast
        ring
      · intro a ha b hb eq
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m) eq
    have hq : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    rw [sum_union hSep,sum_insert hmC,himg,h1,h2,Nat.cast_sub hu]
    have hv' : (v : ℚ) + Q = (u : ℚ)*m := by exact_mod_cast hv
    field_simp [hq,hm']
    nlinarith

lemma round_numerator {Q m : ℕ} (hm : 3 ≤ m) (hQ : 4*m ≤ Q) :
    ∃ u v : ℕ, v + Q = u*m ∧ Q ≤ 3*v ∧ v ≤ Q ∧ u ≤ Q ∧ Q ≤ 3*(Q-u) := by
  let u := (4*Q)/(3*m)+1
  have hd : 0 < 3*m := by omega
  have hlow := Nat.lt_mul_div_succ (4*Q) hd
  have hupp := Nat.div_mul_le_self (4*Q) (3*m)
  have hl : 4*Q ≤ 3*(u*m) := by dsimp [u]; nlinarith
  have hh : 3*(u*m) ≤ 5*Q := by dsimp [u]; nlinarith
  have hu3 := Nat.mul_le_mul_left u hm
  refine ⟨u,u*m-Q,by omega,by omega,by omega,by omega,by omega⟩

theorem main : H1 → H2 → type_of% @Erdos294.erdos_294 := by
  intro h1 h2
  obtain ⟨c,hc,N₀,hR⟩ := h1
  obtain ⟨K,hK⟩ := h2 c hc N₀
  refine ⟨⟨K,Asymptotics.IsBigO.of_bound 1 ?_⟩,verified_upper⟩
  filter_upwards [hK,eventually_ge_atTop (max 6 N₀)] with N h hh
  obtain ⟨L,hL₀,hL,hQ,hdiv,hscale⟩ := h
  let Q := Nat.lcmUpto (⌊c * (L : ℝ) / ((Real.log L)^3 * (Real.log (Real.log L))^4)⌋₊)
  have hQpos : 0 < Q := Nat.lcmUpto_pos _
  let T : ℝ := (N : ℝ) / (Real.log N * (Real.log (Real.log N))^3 * (Real.log (Real.log (Real.log N)))^K)
  change 32*(L : ℝ)*|T| ≤ N at hscale
  have hmin : 0 < t N ∧ ¬ HasUnitFractionSolution (t N) N := by
    apply Nat.sInf_mem (s := {m : ℕ | 0 < m ∧ ¬ HasUnitFractionSolution m N})
    exact ⟨N+1,Nat.succ_pos _,fun ⟨_,hm,ha,_⟩ => by have := (ha _ hm).2; omega⟩
  rw [one_mul,Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_eq_abs]
  change |T| ≤ (t N : ℝ)
  by_contra! small
  let m := t N
  have hm : 0 < m := hmin.1
  apply hmin.2
  by_cases hm1 : m = 1
  · change HasUnitFractionSolution m N
    simpa [hm1] using hasUnitFractionSolution_one (N := N) (by omega)
  by_cases hm2 : m = 2
  · change HasUnitFractionSolution m N
    simpa [hm2] using two_minimum (N := N) (by omega)
  have hm3 : 3 ≤ m := by omega
  have hml : 32*(m*L) ≤ N := by
    have hs : 32*(L : ℝ)*(m : ℝ) ≤ N := (mul_le_mul_of_nonneg_left small.le (by positivity)).trans hscale
    exact_mod_cast (by simpa only [mul_assoc,mul_comm (L : ℝ) (m : ℝ)] using hs :
      (32 : ℝ)*((m : ℝ)*(L : ℝ)) ≤ N)
  have hmL : m ≤ m*L := by simpa using Nat.mul_le_mul_left m (show 1 ≤ L by omega)
  obtain ⟨u,v,hv,hl,hr,hu,hd⟩ := round_numerator hm3 (show 4*m ≤ Q by dsimp [Q]; omega)
  obtain ⟨B,hB,hsB⟩ := hR L hL₀ Q v hQpos dvd_rfl hl hr
  obtain ⟨D,hD,hsD⟩ := hR N (by omega) Q (Q-u) hQpos hdiv hd (Nat.sub_le _ _)
  exact glue (m := m) hm3 hL (show 16*(m*L) < N by omega) hQpos hu hv B D hB hD hsB hsD

end OMA.R_Erdos294_erdos_294_R1
