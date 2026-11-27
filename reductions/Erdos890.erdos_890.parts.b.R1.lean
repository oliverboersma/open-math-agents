import FormalConjectures.ErdosProblems.«890»

/-! The one-variable factorial upper bound is ported from
ChironTheCentaur/rh-lab-erdos890-omega@c42a1231b7d9, Apache-2.0.
The primorial lower bound comes from @mucoucah’s accepted proof in this repository
at a634340ede671933fd26c40e756591ba34559e9c. The block comparison and
the split into prime factors above and below powers of log n are new. -/
open Filter Finset Real
open scoped Nat.Prime ArithmeticFunction.omega

namespace E890

lemma omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

lemma lower_main (c : ℝ) (hc0 : 0 ≤ c) (N : ℕ) (hN2 : 2 ≤ N)
    (n : ℕ) (hn : n = ∏ q ∈ Nat.primesLE N, q)
    (hlo : ‖log (N : ℝ)‖ ≤ (log 2) ^ 2 / 4 * ‖(N : ℝ) ^ (1 - c)‖) :
    c ≤ (ω n : ℝ) * (log (log (n : ℝ)) / log (n : ℝ)) := by
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hlog2' : log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hlN : 0 < log (N : ℝ) := Real.log_pos (by linarith)
  have hprime : ∀ q ∈ Nat.primesLE N, q.Prime := fun q hq => (Nat.mem_primesLE.mp hq).2
  have hω : ω n = Nat.primeCounting N := by
    rw [hn, omega_eq_card, Nat.primeFactors_prod hprime, Nat.primesLE_card_eq_primeCounting]
  have hlow : (2 : ℝ) ^ (Nat.primeCounting N) ≤ (n : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting, hn]
    push_cast
    calc (2:ℝ) ^ (Nat.primesLE N).card = ∏ _q ∈ Nat.primesLE N, (2:ℝ) := by simp
      _ ≤ ∏ q ∈ Nat.primesLE N, (q : ℝ) := by
          apply Finset.prod_le_prod
          · intro i _; norm_num
          · intro i hi; exact_mod_cast (hprime i hi).two_le
  have hupp : (n : ℝ) ≤ (N : ℝ) ^ (Nat.primeCounting N) := by
    rw [← Nat.primesLE_card_eq_primeCounting, hn]
    push_cast
    calc ∏ q ∈ Nat.primesLE N, (q : ℝ) ≤ ∏ _q ∈ Nat.primesLE N, (N : ℝ) := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i hi; exact_mod_cast (Nat.mem_primesLE.mp hi).1
      _ = (N : ℝ) ^ (Nat.primesLE N).card := by simp
  have hk0 : (0 : ℝ) ≤ (Nat.primeCounting N : ℝ) := Nat.cast_nonneg _
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le (by positivity) hlow
  have hlogn_low : (Nat.primeCounting N : ℝ) * log 2 ≤ log (n : ℝ) := by
    have h := Real.log_le_log (by positivity) hlow
    rwa [Real.log_pow] at h
  have hlogn_upp : log (n : ℝ) ≤ (Nat.primeCounting N : ℝ) * log (N : ℝ) := by
    have h := Real.log_le_log hnpos hupp
    rwa [Real.log_pow] at h
  have hcheb := Chebyshev.pi_ge N
  rw [div_le_iff₀ hlN] at hcheb
  have hN1 : log ((N : ℝ) + 1) ≤ 2 * log (N : ℝ) := by
    have h0 : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by nlinarith
    have h := Real.log_le_log (by positivity) h0
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hA1 : 1 ≤ (N : ℝ) ^ c := Real.one_le_rpow (by linarith) hc0
  have hBpos : 0 < (N : ℝ) ^ (1 - c) := Real.rpow_pos_of_pos hNpos _
  have hAB : (N : ℝ) ^ c * (N : ℝ) ^ (1 - c) = N := by
    rw [← Real.rpow_add hNpos]; simp
  rw [Real.norm_of_nonneg hlN.le, Real.norm_of_nonneg hBpos.le] at hlo
  have h1 : (N : ℝ) ^ c * (N : ℝ) ^ (1 - c) * log 2
      ≤ ((Nat.primeCounting N : ℝ) + 2) * ((log 2) ^ 2 / 4 * (N : ℝ) ^ (1 - c)) := by
    calc (N : ℝ) ^ c * (N : ℝ) ^ (1 - c) * log 2 = N * log 2 := by rw [hAB]
      _ ≤ ((Nat.primeCounting N : ℝ) + 2) * log (N : ℝ) := by linarith
      _ ≤ ((Nat.primeCounting N : ℝ) + 2) * ((log 2) ^ 2 / 4 * (N : ℝ) ^ (1 - c)) := by
          apply mul_le_mul_of_nonneg_left hlo
          positivity
  have h2 : 4 * (N : ℝ) ^ c ≤ ((Nat.primeCounting N : ℝ) + 2) * log 2 := by
    have h : (4 * (N : ℝ) ^ c) * ((N : ℝ) ^ (1 - c) * log 2 / 4)
        ≤ (((Nat.primeCounting N : ℝ) + 2) * log 2) * ((N : ℝ) ^ (1 - c) * log 2 / 4) := by
      nlinarith
    exact le_of_mul_le_mul_right h (by positivity)
  have h3 : (N : ℝ) ^ c ≤ (Nat.primeCounting N : ℝ) * log 2 := by nlinarith
  have hkpos : 0 < (Nat.primeCounting N : ℝ) := by
    by_contra h
    have h' : (Nat.primeCounting N : ℝ) ≤ 0 := not_lt.mp h
    nlinarith
  have hlogn1 : (N : ℝ) ^ c ≤ log (n : ℝ) := h3.trans hlogn_low
  have hlogn_pos : 0 < log (n : ℝ) := by linarith
  have hloglog : c * log (N : ℝ) ≤ log (log (n : ℝ)) := by
    have h := Real.log_le_log (by linarith) hlogn1
    rwa [Real.log_rpow hNpos] at h
  rw [hω]
  calc c = (Nat.primeCounting N : ℝ)
        * (c * log (N : ℝ) / ((Nat.primeCounting N : ℝ) * log (N : ℝ))) := by
        field_simp
    _ ≤ (Nat.primeCounting N : ℝ) * (log (log (n : ℝ)) / log (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hkpos.le
        exact div_le_div₀ (le_trans (by positivity) hloglog) hloglog hlogn_pos hlogn_upp

/-- Lower bound: frequently `c ≤ ω n * (log log n / log n)` for every `0 ≤ c < 1`. -/
lemma lower_frequently (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∃ᶠ n : ℕ in atTop, c ≤ (ω n : ℝ) * (log (log n) / log n) := by
  rw [Filter.frequently_atTop]
  intro a
  have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hε0 : 0 < (log 2) ^ 2 / 4 := by positivity
  have hlo := (isLittleO_log_rpow_atTop (r := 1 - c) (by linarith)).bound hε0
  obtain ⟨X0, hX0⟩ := Filter.eventually_atTop.mp hlo
  obtain ⟨p, hpa, hp⟩ := Nat.exists_infinite_primes a
  have hNp : p ≤ max p (max ⌈X0⌉₊ 2) := le_max_left _ _
  have hNX : X0 ≤ ((max p (max ⌈X0⌉₊ 2) : ℕ) : ℝ) := by
    calc X0 ≤ (⌈X0⌉₊ : ℝ) := Nat.le_ceil X0
      _ ≤ ((max p (max ⌈X0⌉₊ 2) : ℕ) : ℝ) := by
          exact_mod_cast (le_max_left _ _).trans (le_max_right _ _)
  have hN2 : 2 ≤ max p (max ⌈X0⌉₊ 2) := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨∏ q ∈ Nat.primesLE (max p (max ⌈X0⌉₊ 2)), q, ?_, ?_⟩
  · have hmem : p ∈ Nat.primesLE (max p (max ⌈X0⌉₊ 2)) := Nat.mem_primesLE.mpr ⟨hNp, hp⟩
    have hdvd : p ∣ ∏ q ∈ Nat.primesLE (max p (max ⌈X0⌉₊ 2)), q :=
      Finset.dvd_prod_of_mem (fun q => q) hmem
    have hpos : 0 < ∏ q ∈ Nat.primesLE (max p (max ⌈X0⌉₊ 2)), q :=
      Finset.prod_pos (fun q hq => (Nat.mem_primesLE.mp hq).2.pos)
    exact hpa.trans (Nat.le_of_dvd hpos hdvd)
  · exact lower_main c hc0 _ hN2 _ rfl (hX0 _ hNX)

end E890


namespace Erdos890OmegaFC
theorem omega_eq_card (n : ℕ) : ω n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- `k` distinct positive integers have product at least `k!`. -/
theorem factorial_card_le_prod (s : Finset ℕ) : (∀ x ∈ s, 0 < x) → s.card.factorial ≤ ∏ x ∈ s, x := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro h0
    have hnot : a ∉ s := fun h => lt_irrefl a (ha a h)
    have ih' := ih (fun x hx => h0 x (mem_insert_of_mem hx))
    have hcard : s.card + 1 ≤ a := by
      have hsub : insert a s ⊆ Icc 1 a := by
        intro x hx
        rw [mem_Icc]
        rcases mem_insert.mp hx with rfl | hx'
        · exact ⟨h0 _ (mem_insert_self _ _), le_rfl⟩
        · exact ⟨h0 x (mem_insert_of_mem hx'), (ha x hx').le⟩
      have := card_le_card hsub
      rw [card_insert_of_notMem hnot, Nat.card_Icc] at this
      omega
    rw [card_insert_of_notMem hnot, prod_insert hnot, Nat.factorial_succ]
    exact Nat.mul_le_mul hcard ih'

/-- `ω(n)! ≤ n` for `n ≠ 0`. -/
theorem factorial_omega_le {n : ℕ} (hn : n ≠ 0) : (ω n).factorial ≤ n := by
  rw [omega_eq_card]
  calc (n.primeFactors.card).factorial ≤ ∏ p ∈ n.primeFactors, p :=
        factorial_card_le_prod _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

/-- `k log k − k ≤ log k!`. -/
theorem mul_log_sub_le_log_factorial (k : ℕ) :
    (k : ℝ) * log k - k ≤ log (k.factorial : ℝ) := by
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (Nat.cast_nonneg k) k
  rw [div_le_iff₀ hf] at h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hl := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_mul (exp_pos _).ne' hf.ne', Real.log_exp] at hl
  linarith

/-- `log x ≤ c x` eventually, for every `c > 0`. -/
theorem eventually_log_le (c : ℝ) (hc : 0 < c) : ∀ᶠ x : ℝ in atTop, log x ≤ c * x := by
  filter_upwards [isLittleO_log_id_atTop.bound hc, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have h0 : 0 ≤ log x := Real.log_nonneg hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, id, abs_of_nonneg (by linarith)] at hx
  exact hx

/-- The analytic core of the upper half, in the variable `L = log n`. -/
theorem upper_aux {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ k : ℕ, (k : ℝ) * log k - k ≤ L → (k : ℝ) * (log L / L) ≤ 1 + ε := by
  set c : ℝ := ε / (3 * (1 + ε)) with hc
  have hcpos : 0 < c := by positivity
  have hℓ : ∀ᶠ ℓ : ℝ in atTop, log ℓ ≤ c * ℓ ∧ 1 / c ≤ ℓ :=
    (eventually_log_le c hcpos).and (eventually_ge_atTop _)
  filter_upwards [tendsto_log_atTop.eventually hℓ, eventually_ge_atTop (1 : ℝ)] with L hL hL1
  obtain ⟨hlogℓ, hℓbig⟩ := hL
  set ℓ := log L with hℓdef
  have hcℓ : 1 ≤ c * ℓ := by
    rw [div_le_iff₀ hcpos] at hℓbig
    linarith
  have hℓpos : 0 < ℓ := by
    by_contra h
    push Not at h
    nlinarith
  have hLpos : 0 < L := by linarith
  intro k hk
  by_contra hcon
  push Not at hcon
  -- `(1+ε) L < k ℓ`
  have h1 : (1 + ε) * L < k * ℓ := by
    have h := mul_lt_mul_of_pos_right hcon hLpos
    rwa [mul_assoc, div_mul_cancel₀ _ hLpos.ne'] at h
  set y : ℝ := (1 + ε) * L / ℓ with hy
  have hypos : 0 < y := by positivity
  have hyk : y < k := by rw [hy, div_lt_iff₀ hℓpos]; linarith
  have hyℓ : y * ℓ = (1 + ε) * L := by rw [hy, div_mul_cancel₀ _ hℓpos.ne']
  have hlogy : log y = log (1 + ε) + ℓ - log ℓ := by
    rw [hy, Real.log_div (by positivity) hℓpos.ne', Real.log_mul (by positivity) hLpos.ne']
  have hlog1ε : 0 ≤ log (1 + ε) := Real.log_nonneg (by linarith)
  -- `log y − 1 ≥ ℓ (1 − 2c)`
  have hly : ℓ * (1 - 2 * c) ≤ log y - 1 := by rw [hlogy]; nlinarith
  have hc2 : (1 + ε) * (1 - 2 * c) = 1 + ε / 3 := by
    rw [hc]; field_simp; ring
  have hc1 : 2 * c < 1 := by
    rw [hc, mul_div_assoc', div_lt_one (by positivity)]; linarith
  have hly0 : 0 ≤ log y - 1 := le_trans (by nlinarith) hly
  have hlk : log y ≤ log k := Real.log_le_log hypos hyk.le
  -- `k (log k − 1) ≥ y (log y − 1) ≥ (1 + ε/3) L`
  have hk1 : y * (log y - 1) ≤ k * (log k - 1) :=
    mul_le_mul hyk.le (by linarith) hly0 (by positivity)
  have hk2 : (1 + ε / 3) * L ≤ y * (log y - 1) := by
    have := mul_le_mul_of_nonneg_left hly hypos.le
    calc (1 + ε / 3) * L = (1 + ε) * (1 - 2 * c) * L := by rw [hc2]
      _ = y * (ℓ * (1 - 2 * c)) := by
        rw [show y * (ℓ * (1 - 2 * c)) = (y * ℓ) * (1 - 2 * c) by ring, hyℓ]; ring
      _ ≤ y * (log y - 1) := this
  nlinarith

/-- **Upper half**: for every `ε > 0`, eventually `g n ≤ 1 + ε`. -/
theorem eventually_g_le {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, (ω n : ℝ) * (log (log n) / log n) ≤ 1 + ε := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (upper_aux hε), eventually_ge_atTop 1] with n hn hn1
  apply hn
  have hf := factorial_omega_le (n := n) (by omega)
  have hfR : ((ω n).factorial : ℝ) ≤ n := by exact_mod_cast hf
  have hfpos : (0 : ℝ) < (ω n).factorial := by exact_mod_cast Nat.factorial_pos _
  exact (mul_log_sub_le_log_factorial (ω n)).trans (Real.log_le_log hfpos hfR)


end Erdos890OmegaFC
namespace OMA.R_Erdos890_erdos_890_parts_b_R1

/-- At any fixed power of log n, bound the distinct prime factors up to that cutoff in the block. -/
def H1 : Prop := ∀ k : ℕ, 2 ≤ k → ∀ B : ℕ, 1 ≤ B → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ n : ℕ in atTop,
    (∑ i ∈ range k, (((n + i).primeFactors.filter
      (fun p : ℕ => (p : ℝ) ≤ (log n) ^ B)).card : ℝ)) * (log (log n) / log n) ≤ 1 + ε

/-- The factors above a sufficiently large power of log n contribute arbitrarily little. -/
def H2 : Prop := ∀ k : ℕ, 2 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ B : ℕ, 1 ≤ B ∧
  ∀ᶠ n : ℕ in atTop,
    (∑ i ∈ range k, (((n + i).primeFactors.filter
      (fun p : ℕ => ¬ (p : ℝ) ≤ (log n) ^ B)).card : ℝ)) * (log (log n) / log n) ≤ ε

theorem main : H1 → H2 → type_of% @Erdos890.erdos_890.parts.b := by
  intro hsmall hlarge k hk
  have hnlog : ∀ᶠ n : ℕ in atTop, 0 ≤ log (log n) / log n := by
    have ht : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
      tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    exact div_nonneg (log_nonneg hn) (by linarith)
  have he (n : ℕ) :
      (∑ i ∈ range k, (ω (n + i) : EReal)) * ((log (log n) : EReal) / (log n : EReal)) =
        (((∑ i ∈ range k, (ω (n + i) : ℝ)) * (log (log n) / log n) : ℝ) : EReal) := by
    simp only [← Nat.cast_sum, EReal.coe_mul, EReal.coe_div, EReal.coe_natCast]
  simp_rw [he]
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro b hb
    obtain ⟨x,hx,hxb⟩ := EReal.lt_iff_exists_real_btwn.mp hb
    have hx' : (1 : ℝ) < x := by exact_mod_cast hx
    apply le_trans (Filter.limsup_le_of_le (h := ?_)) hxb.le
    by_cases hk1 : k = 1
    · subst k
      filter_upwards [Erdos890OmegaFC.eventually_g_le (sub_pos.mpr hx')] with n h
      simp only [Finset.sum_range_one, add_zero]
      exact_mod_cast (show (ω n : ℝ) * (log (log n) / log n) ≤ x by linarith)
    · let ε := (x - 1) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      obtain ⟨B,hB,hl⟩ := hlarge k (by omega) ε hε
      filter_upwards [hsmall k (by omega) B hB ε hε, hl] with n hs hl
      have hsplit :
          (∑ i ∈ range k, (ω (n + i) : ℝ)) =
          (∑ i ∈ range k, (((n + i).primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ (log n)^B)).card : ℝ)) +
          (∑ i ∈ range k, (((n + i).primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ (log n)^B)).card : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [E890.omega_eq_card]
        exact_mod_cast (Finset.card_filter_add_card_filter_not
          (s := (n+i).primeFactors) (p := (fun p : ℕ => (p : ℝ) ≤ (log n)^B))).symm
      exact_mod_cast (show (∑ i ∈ range k, (ω (n + i) : ℝ)) * (log (log n) / log n) ≤ x by
        rw [hsplit, add_mul]; dsimp [ε] at hs hl; linarith)
  · apply le_of_forall_lt_imp_le_of_dense
    intro b hb
    obtain ⟨x,hbx,hx⟩ := EReal.lt_iff_exists_real_btwn.mp hb
    have hx' : x < (1 : ℝ) := by exact_mod_cast hx
    apply hbx.le.trans
    apply Filter.le_limsup_of_frequently_le'
    apply ((E890.lower_frequently (max x 0) (le_max_right _ _) (max_lt hx' one_pos)).and_eventually hnlog).mono
    intro n ⟨hn,hnl⟩
    have hsum : (ω n : ℝ) ≤ ∑ i ∈ range k, (ω (n + i) : ℝ) := by
      simpa only [add_zero] using
        (Finset.single_le_sum (f := fun i : ℕ => (ω (n+i) : ℝ)) (fun i _ => Nat.cast_nonneg _) (show 0 ∈ range k by exact Finset.mem_range.mpr (by omega)))
    exact_mod_cast ((le_max_left x 0).trans (hn.trans (mul_le_mul_of_nonneg_right hsum hnl)))
end OMA.R_Erdos890_erdos_890_parts_b_R1
