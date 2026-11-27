import FormalConjectures.ErdosProblems.«4»

-- Problem: Erdős Problem 4
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/4.lean:43 (declaration Erdos4.erdos_4)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Erdős 4 via short translates. -/

namespace OMAErdos4

open Real

/-- Short translates (Proposition 1.2 of "Improved long gaps between primes"): for some
`δ > 0` and all large `x`, any set `S ⊆ [1, H]` (`x < H ≤ x (log x)^2`) with `|S| ≤ δ x` and any
residue `b < Q(x)` admit `1 ≤ t ≤ e^x` such that every `b + Q(x) t + s`, `s ∈ S`, is not prime. -/
def rk_Prop12 : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ H : ℕ, x < H → (H : ℝ) ≤ x * Real.log x ^ 2 →
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H → (S.card : ℝ) ≤ δ * x →
    ∀ b : ℕ, b < primorial ⌊x⌋₊ →
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp x ∧ ∀ s ∈ S, ¬ (b + primorial ⌊x⌋₊ * t + s).Prime

/-- Positions sharing a prime factor with `Q` are covered for every translate. -/
lemma rk_covered {Q t s : ℕ} (hQ : 0 < Q) (hs : ¬ Nat.Coprime s Q) (ht : 1 ≤ t) (hs1 : 1 ≤ s) :
    ¬ (Q * t + s).Prime := by
  obtain ⟨p, hp, hps, hpQ⟩ := Nat.Prime.not_coprime_iff_dvd.1 hs
  intro hpr
  have hdvd : p ∣ Q * t + s := Nat.dvd_add (Dvd.dvd.mul_right hpQ t) hps
  rcases (Nat.dvd_prime hpr).1 hdvd with h | h
  · exact hp.one_lt.ne' h
  · have : p ≤ s := Nat.le_of_dvd hs1 hps
    have : Q * t ≥ 1 := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hQ.ne' (by omega))
    omega

/-- Survivors of the trivial covering (`b = 0`, all primes `≤ k`) are `1` and primes. -/
lemma rk_survivors_card (k H : ℕ) (hH : H < (k + 1) ^ 2) :
    ((Finset.Icc 1 H).filter (fun s => Nat.Coprime s (primorial k))).card ≤ 1 + Nat.primeCounting H := by
  have hsub : (Finset.Icc 1 H).filter (fun s => Nat.Coprime s (primorial k)) ⊆
      insert 1 ((Finset.range (H + 1)).filter Nat.Prime) := by
    intro s hs
    rw [Finset.mem_filter, Finset.mem_Icc] at hs
    rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    by_cases h1 : s = 1
    · exact Or.inl h1
    right
    refine ⟨by omega, ?_⟩
    by_contra hnp
    have hs2 : 2 ≤ s := by omega
    set p := s.minFac
    have hp : p.Prime := Nat.minFac_prime h1
    have hpk : k < p := by
      by_contra hle
      push Not at hle
      have : p ∣ primorial k := hp.dvd_primorial_iff.2 hle
      exact (Nat.Prime.not_coprime_iff_dvd.2 ⟨p, hp, Nat.minFac_dvd s, this⟩) hs.2
    have hsq : p ^ 2 ≤ s := Nat.minFac_sq_le_self (by omega) hnp
    have : (k + 1) ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hpk 2
    omega
  calc _ ≤ (insert 1 ((Finset.range (H + 1)).filter Nat.Prime)).card := Finset.card_le_card hsub
    _ ≤ ((Finset.range (H + 1)).filter Nat.Prime).card + 1 := Finset.card_insert_le _ _
    _ = 1 + Nat.primeCounting H := by
        rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]; ring

/-- From a run of composites after `N` and a prime `r ≤ N`, extract a long prime gap. -/
lemma rk_gap {N H r : ℕ} (hr : r.Prime) (hrN : r ≤ N)
    (hcomp : ∀ s, 1 ≤ s → s ≤ H → ¬ (N + s).Prime) :
    ∃ n : ℕ, Nat.count Nat.Prime r ≤ n ∧ n ≤ N ∧
      H < (n + 1).nth Nat.Prime - n.nth Nat.Prime ∧ n.nth Nat.Prime ≤ (n + 1).nth Nat.Prime := by
  have hex : ∃ q, q ≤ N ∧ q.Prime := ⟨r, hrN, hr⟩
  set q := Nat.findGreatest Nat.Prime N
  have hq : q.Prime := Nat.findGreatest_spec (P := Nat.Prime) hrN hr
  have hqN : q ≤ N := Nat.findGreatest_le N
  have hrq : r ≤ q := Nat.le_findGreatest hrN hr
  have hgreat : ∀ i, q < i → i ≤ N → ¬ i.Prime := fun i hi hiN => Nat.findGreatest_is_greatest hi hiN
  refine ⟨Nat.count Nat.Prime q, Nat.count_monotone _ hrq, ?_, ?_⟩
  · exact le_trans (Nat.count_le _) hqN
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime q) = q := Nat.nth_count hq
  have h2 : Nat.count Nat.Prime q + 1 = Nat.count Nat.Prime (q + 1) := by
    rw [Nat.count_succ]; simp [hq]
  have h3 : Nat.nth Nat.Prime (Nat.count Nat.Prime q + 1) = sInf {i : ℕ | i.Prime ∧ q + 1 ≤ i} := by
    rw [h2, Nat.nth_count_eq_sInf]
  have hne : {i : ℕ | i.Prime ∧ q + 1 ≤ i}.Nonempty := by
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (q + 1)
    exact ⟨p, hp2, hp1⟩
  have hmem := Nat.sInf_mem hne
  set m := sInf {i : ℕ | i.Prime ∧ q + 1 ≤ i}
  have hm : N + H < m := by
    by_contra hle
    push Not at hle
    by_cases hmN : m ≤ N
    · exact hgreat m (by have := hmem.2; omega) hmN hmem.1
    · exact hcomp (m - N) (by omega) (by omega) (by rw [Nat.add_sub_cancel' (by omega)]; exact hmem.1)
  rw [h1, h3]
  constructor <;> omega

/-- The target scale is at most `C · log A · A / T` once `log₃ y ≥ T ≥ 1` and `log y ≤ A`. -/
lemma rk_scale_le {C T A : ℝ} (hC : 0 ≤ C) (hT : 1 ≤ T) {y : ℝ}
    (hy : Real.exp (Real.exp (Real.exp T)) ≤ y) (hyA : Real.log y ≤ A) :
    C * Real.log (Real.log y) * Real.log (Real.log (Real.log (Real.log y))) /
      (Real.log (Real.log (Real.log y))) ^ 2 * Real.log y ≤ C * Real.log A * A / T := by
  have ey : 0 < Real.exp (Real.exp (Real.exp T)) := Real.exp_pos _
  have hy0 : 0 < y := lt_of_lt_of_le ey hy
  have ha : Real.exp (Real.exp T) ≤ Real.log y := by
    rw [← Real.log_exp (Real.exp (Real.exp T))]; exact Real.log_le_log ey hy
  have ha0 : 0 < Real.log y := lt_of_lt_of_le (Real.exp_pos _) ha
  have hb : Real.exp T ≤ Real.log (Real.log y) := by
    rw [← Real.log_exp (Real.exp T)]; exact Real.log_le_log (Real.exp_pos _) ha
  have hb0 : 0 < Real.log (Real.log y) := lt_of_lt_of_le (Real.exp_pos _) hb
  have hc : T ≤ Real.log (Real.log (Real.log y)) := by
    rw [← Real.log_exp T]; exact Real.log_le_log (Real.exp_pos _) hb
  set a := Real.log y
  set b := Real.log a
  set c := Real.log b
  have hc0 : 0 < c := by linarith
  have hd : Real.log c ≤ c := Real.log_le_self hc0.le
  have hd0 : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hbA : b ≤ Real.log A := Real.log_le_log ha0 hyA
  have h1 : b * Real.log c / c ^ 2 ≤ b / T := by
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    have h5 : Real.log c * T ≤ c * c := mul_le_mul hd hc (by linarith) hc0.le
    have h6 := mul_le_mul_of_nonneg_left h5 hb0.le
    nlinarith
  have h2 : b / T ≤ Real.log A / T := div_le_div_of_nonneg_right hbA (by linarith)
  calc C * b * Real.log c / c ^ 2 * a = C * (b * Real.log c / c ^ 2) * a := by ring
    _ ≤ C * (Real.log A / T) * A := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (h1.trans h2) hC) hyA ha0.le
        have : 0 ≤ Real.log A := le_trans hb0.le hbA
        have : 0 < T := by linarith
        positivity
    _ = C * Real.log A * A / T := by ring

set_option maxHeartbeats 1000000 in
theorem rk_main (h : rk_Prop12) : ∀ C > 0, Erdos4.Erdos4For C := by
  intro C hC
  obtain ⟨δ0, hδ0, x0, hP⟩ := h
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min δ0 1 := ⟨_, rfl⟩
  have hδ : 0 < δ := hδdef ▸ lt_min hδ0 one_pos
  have hδ1 : δ ≤ 1 := hδdef ▸ min_le_right _ _
  have hδδ0 : δ ≤ δ0 := hδdef ▸ min_le_left _ _
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le (ε := 1 / 10) (by norm_num))
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 40 * C / δ + 1 := ⟨_, rfl⟩
  have hCδ : 0 ≤ 40 * C / δ := by positivity
  have hT1 : 1 ≤ T := by linarith
  have hlog4 : Real.log 4 < 1.39 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  apply Set.infinite_of_forall_exists_gt
  intro M
  obtain ⟨n0, hn0def⟩ : ∃ n0 : ℕ, n0 = max M ⌈Real.exp (Real.exp (Real.exp T))⌉₊ := ⟨_, rfl⟩
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℕ, K0 = max (max ⌈x0⌉₊ ⌈X1⌉₊)
    (max ⌈Real.exp (8 / δ + 1)⌉₊ (2 * (Nat.nth Nat.Prime n0 + 1) + 2)) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = K0 + 3 := ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (k : ℝ) := ⟨_, rfl⟩
  have hkK : K0 ≤ k := by omega
  have hxK : (K0 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hkK
  have hx3 : (3 : ℝ) ≤ x := by
    rw [hxdef, hk]; push_cast; linarith [(Nat.cast_nonneg K0 : (0:ℝ) ≤ K0)]
  have hx0 : x0 ≤ x := le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast
      (hK0 ▸ le_trans (le_max_left _ _) (le_max_left _ _) : ⌈x0⌉₊ ≤ K0)) hxK)
  have hxX1 : X1 ≤ x := le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast
      (hK0 ▸ le_trans (le_max_right _ _) (le_max_left _ _) : ⌈X1⌉₊ ≤ K0)) hxK)
  have hxE : Real.exp (8 / δ + 1) ≤ x := le_trans (Nat.le_ceil _) (le_trans (by exact_mod_cast
      (hK0 ▸ le_trans (le_max_left _ _) (le_max_right _ _) : ⌈Real.exp (8 / δ + 1)⌉₊ ≤ K0)) hxK)
  have hkN : 2 * (Nat.nth Nat.Prime n0 + 1) + 2 ≤ k :=
    le_trans (hK0 ▸ le_trans (le_max_right _ _) (le_max_right _ _)) hkK
  have hxpos : 0 < x := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log x := ⟨_, rfl⟩
  have hL : 8 / δ + 1 ≤ L := by
    rw [hLdef, ← Real.log_exp (8 / δ + 1)]; exact Real.log_le_log (Real.exp_pos _) hxE
  have hL8 : 8 / δ ≤ L := by linarith
  have h8δ : 0 ≤ 8 / δ := by positivity
  have hL1 : 1 ≤ L := by linarith
  have hδL : 8 ≤ δ * L := by
    have := mul_le_mul_of_nonneg_left hL8 hδ.le
    rwa [mul_div_cancel₀ _ hδ.ne'] at this
  have hfloor : ⌊x⌋₊ = k := by rw [hxdef]; simp
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ, H = ⌊δ * x * L / 4⌋₊ := ⟨_, rfl⟩
  have hH1 : (H : ℝ) ≤ δ * x * L / 4 := hHdef ▸ Nat.floor_le (by positivity)
  have hH2 : δ * x * L / 4 < H + 1 := hHdef ▸ Nat.lt_floor_add_one _
  have hδxL : 8 * x ≤ δ * x * L := by nlinarith
  have hxH : x < H := by nlinarith
  have hHle : (H : ℝ) ≤ x * L ^ 2 := by
    have : δ * x * L ≤ x * L * L := by
      have := mul_le_mul_of_nonneg_left (le_trans hδ1 hL1) (by positivity : 0 ≤ x * L)
      nlinarith
    nlinarith
  have hLx : L ≤ x - 1 := hLdef ▸ Real.log_le_sub_one_of_pos hxpos
  have hHsq : H < (k + 1) ^ 2 := by
    have : (H : ℝ) < ((k : ℝ) + 1) ^ 2 := by
      have : δ * x * L ≤ x * L := by nlinarith
      rw [← hxdef]; nlinarith
    exact_mod_cast this
  -- the survivor set
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = primorial k := ⟨_, rfl⟩
  have hQpos : 0 < Q := hQdef ▸ primorial_pos k
  obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ, S = (Finset.Icc 1 H).filter (fun s => Nat.Coprime s Q) :=
    ⟨_, rfl⟩
  have hSsub : S ⊆ Finset.Icc 1 H := hSdef ▸ Finset.filter_subset _ _
  have hScard : (S.card : ℝ) ≤ δ0 * x := by
    have h1 : S.card ≤ 1 + Nat.primeCounting H := hSdef ▸ hQdef ▸ rk_survivors_card k H hHsq
    have hHX1 : X1 ≤ (H : ℝ) := by linarith
    have h2 := hX1 (H : ℝ) hHX1
    rw [Nat.floor_natCast] at h2
    have hlogH : L ≤ Real.log H := hLdef ▸ Real.log_le_log hxpos hxH.le
    have h3 : (Real.log 4 + 1 / 10) * (H : ℝ) / Real.log H ≤ 3 / 8 * δ * x := by
      rw [div_le_iff₀ (by linarith)]
      have h6 : (Real.log 4 + 1 / 10) * (H : ℝ) ≤ 3 / 2 * (δ * x * L / 4) := by
        have := mul_le_mul (by linarith : Real.log 4 + 1 / 10 ≤ 3 / 2) hH1 (Nat.cast_nonneg _)
          (by norm_num)
        linarith
      have h7 : 3 / 2 * (δ * x * L / 4) ≤ 3 / 8 * δ * x * Real.log H := by
        have := mul_le_mul_of_nonneg_left hlogH (by positivity : 0 ≤ 3 / 8 * δ * x)
        nlinarith
      linarith
    have h4 : (S.card : ℝ) ≤ 1 + 3 / 8 * δ * x := by
      have : (S.card : ℝ) ≤ 1 + (Nat.primeCounting H : ℝ) := by exact_mod_cast h1
      linarith only [this, h2, h3]
    have h5 : 2 ≤ δ * x := by
      have := mul_le_mul_of_nonneg_left hLx hδ.le
      linarith
    have h6 : δ * x ≤ δ0 * x := mul_le_mul_of_nonneg_right hδδ0 hxpos.le
    linarith only [h4, h5, h6]
  obtain ⟨t, ht1, htx, htS⟩ := hP x hx0 H hxH (hLdef ▸ hHle) S hSsub hScard 0
    (by rw [hfloor, ← hQdef]; exact hQpos)
  rw [hfloor, ← hQdef] at htS
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = Q * t := ⟨_, rfl⟩
  have hcomp : ∀ s, 1 ≤ s → s ≤ H → ¬ (N + s).Prime := by
    intro s hs1 hsH
    by_cases hcop : Nat.Coprime s Q
    · have := htS s (by rw [hSdef, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hs1, hsH⟩, hcop⟩)
      simpa [hNdef] using this
    · rw [hNdef]; exact rk_covered hQpos hcop ht1 hs1
  -- a prime r between nth n0 and k
  obtain ⟨r, hr, hr1, hr2⟩ := Nat.exists_prime_lt_and_le_two_mul (k / 2) (by omega)
  have hrk : r ≤ k := by omega
  have hrQ : r ≤ Q := Nat.le_of_dvd hQpos (hQdef ▸ hr.dvd_primorial_iff.2 hrk)
  have hQN : Q ≤ N := hNdef ▸ Nat.le_mul_of_pos_right Q ht1
  have hrN : r ≤ N := le_trans hrQ hQN
  have hnr : Nat.nth Nat.Prime n0 < r := by omega
  obtain ⟨n, hn1, hnN, hgap, hmono⟩ := rk_gap hr hrN hcomp
  have hn0 : n0 < n := by
    have := (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2 hnr
    exact lt_of_lt_of_le this hn1
  refine ⟨n, ?_, lt_of_le_of_lt (hn0def ▸ le_max_left _ _) hn0⟩
  -- size of `n`
  have hnE : Real.exp (Real.exp (Real.exp T)) ≤ (n : ℝ) := by
    have h1 : Real.exp (Real.exp (Real.exp T)) ≤ (⌈Real.exp (Real.exp (Real.exp T))⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : ⌈Real.exp (Real.exp (Real.exp T))⌉₊ ≤ n := by
      have := hn0def ▸ (le_max_right M ⌈Real.exp (Real.exp (Real.exp T))⌉₊); omega
    exact le_trans h1 (by exact_mod_cast h2)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hnE
  have hNle : (N : ℝ) ≤ 4 ^ k * Real.exp x := by
    have hk0 : k ≠ 0 := hk ▸ Nat.succ_ne_zero _
    have hQ4 : (Q : ℝ) ≤ 4 ^ k := by
      have h1 : Q ≤ 4 ^ k := hQdef ▸ (primorial_lt_four_pow k hk0).le
      have h2 : ((Q : ℕ) : ℝ) ≤ ((4 ^ k : ℕ) : ℝ) := Nat.cast_le.2 h1
      rw [Nat.cast_pow] at h2
      exact le_trans h2 (le_of_eq (by norm_num))
    have hN' : (N : ℝ) = (Q : ℝ) * (t : ℝ) := by rw [hNdef, Nat.cast_mul]
    rw [hN']
    have h4 : (0 : ℝ) ≤ 4 ^ k := by positivity
    have h5 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    exact mul_le_mul hQ4 htx h5 h4
  have hlogn : Real.log n ≤ 2.4 * x := by
    have h1 : Real.log n ≤ Real.log (4 ^ k * Real.exp x) :=
      Real.log_le_log hnpos (le_trans (by exact_mod_cast hnN) hNle)
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp,
      ← hxdef] at h1
    nlinarith
  have hscale := rk_scale_le hC.le hT1 hnE hlogn
  have hlog24 : Real.log (2.4 * x) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num) hxpos.ne', ← hLdef]
    have : Real.log 2.4 ≤ 2.4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h8 : 8 ≤ 8 / δ := by rw [le_div_iff₀ hδ]; linarith
    linarith
  have hCT : C / T ≤ δ / 40 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have : 40 * C / δ * δ = 40 * C := div_mul_cancel₀ _ hδ.ne'
    nlinarith
  have hbound : C * Real.log (2.4 * x) * (2.4 * x) / T ≤ 0.12 * δ * x * L := by
    have e : C * Real.log (2.4 * x) * (2.4 * x) / T = (C / T) * (Real.log (2.4 * x) * (2.4 * x)) := by
      ring
    rw [e]
    have h0 : 0 ≤ Real.log (2.4 * x) := Real.log_nonneg (by linarith)
    have h1 : Real.log (2.4 * x) * (2.4 * x) ≤ 2 * L * (2.4 * x) :=
      mul_le_mul_of_nonneg_right hlog24 (by linarith)
    have h2 : (C / T) * (Real.log (2.4 * x) * (2.4 * x)) ≤ (δ / 40) * (2 * L * (2.4 * x)) :=
      mul_le_mul hCT h1 (by positivity) (by positivity)
    nlinarith
  have hgapR : (H : ℝ) + 1 ≤ ((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ) := by
    exact_mod_cast hgap
  have hfin : 0.12 * δ * x * L < (H : ℝ) + 1 := by nlinarith
  rw [Set.mem_ofPred_eq]
  rw [Nat.cast_sub hmono] at hgapR
  linarith

/-! ## Proposition 1.2 (short translates) -/

section Translates

open Finset Real

/-! ## Basic sum manipulations -/

theorem tr_sum_succ (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1 + 1)).filter Nat.Prime, f p =
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, f p +
        (if (n + 1).Prime then f (n + 1) else 0) := by
  rw [Finset.range_add_one (n := n + 1), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp)]
    ring
  · simp

/-- log n! as a sum over primes. -/
theorem tr_log_factorial (n : ℕ) :
    Real.log ((n.factorial : ℕ) : ℝ) =
      ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
        ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum_of_support_subset]
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le ((hp.1.dvd_factorial).1 hp.2.1), hp.1⟩
  · intro i _
    simp

/-- θ(n) ≤ n log 4. -/
theorem tr_theta_le (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p ≤ n * Real.log 4 := by
  have h1 : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p =
      Real.log ((primorial n : ℕ) : ℝ) := by
    unfold primorial
    rw [Nat.cast_prod, Real.log_prod]
    intro p hp
    have := (Finset.mem_filter.1 hp).2.pos
    positivity
  rw [h1, ← Real.log_pow]
  apply Real.log_le_log
  · exact_mod_cast primorial_pos n
  · exact_mod_cast primorial_le_four_pow n

theorem tr_log_factorial_le (n : ℕ) :
    Real.log ((n.factorial : ℕ) : ℝ) ≤ n * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log
  · exact_mod_cast Nat.factorial_pos n
  · exact_mod_cast Nat.factorial_le_pow n

theorem tr_log_factorial_ge (n : ℕ) (hn : 1 ≤ n) :
    n * Real.log n - n ≤ Real.log ((n.factorial : ℕ) : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (n := n) (by omega)
  have h1 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h2 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

/-! ## Legendre bounds -/

theorem tr_div_le_fact (p n : ℕ) (hp : p.Prime) :
    (n : ℝ) / p ≤ ((n.factorial.factorization p : ℕ) : ℝ) + 1 := by
  have h1 : n / p ≤ n.factorial.factorization p := by
    rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p n))]
    rcases Nat.eq_zero_or_pos (n / p) with h | h
    · rw [h]; exact Nat.zero_le _
    · have hpn : p ≤ n := (Nat.div_pos_iff.1 h).2
      have hl : 0 < Nat.log p n := Nat.log_pos hp.one_lt hpn
      have hmem : 1 ∈ Finset.Ico 1 (Nat.log p n + 1) := by
        simp only [Finset.mem_Ico]; omega
      have := Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) hmem
      simpa using this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h2 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by exact_mod_cast h1
  have h3 : (n : ℝ) = p * ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod n p).symm
  have h4 : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt n hp.pos
  rw [div_le_iff₀ hp0]
  nlinarith

theorem tr_fact_le_div (p n : ℕ) (hp : p.Prime) :
    ((n.factorial.factorization p : ℕ) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
  have h1 := Nat.factorization_factorial_le_div_pred hp n
  have h2 : ((n / (p - 1) : ℕ) : ℝ) ≤ (n : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
  have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le]; simp
  rw [h3] at h2
  calc ((n.factorial.factorization p : ℕ) : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ _ := h2

/-! ## Mertens' first theorem, upper bound -/

theorem tr_mertens1_upper (n : ℕ) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p ≤ Real.log n + Real.log 4 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (Finset.range (0 + 1)).filter Nat.Prime = ∅ := by decide
    rw [this]
    simp only [Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : (n : ℝ) * ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p ≤
      Real.log ((n.factorial : ℕ) : ℝ) +
        ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p := by
    rw [tr_log_factorial, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Finset.mem_filter.1 hp).2
    have h := tr_div_le_fact p n hpp
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have : (n : ℝ) * (Real.log p / p) = (n / p) * Real.log p := by ring
    rw [this]
    nlinarith
  have h1 := tr_log_factorial_le n
  have h2 := tr_theta_le n
  have : (n : ℝ) * ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p ≤
      n * (Real.log n + Real.log 4) := by linarith
  exact le_of_mul_le_mul_left this hn'

/-! ## The tail sum ∑ log p / (p (p-1)) is bounded -/

theorem tr_tail_real (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) / ((x + 1) * (x + 1 - 1)) ≤
      (2 + Real.log x) / x - (2 + Real.log (x + 1)) / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hd : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (x := (x + 1) / x) (by positivity)
    have e : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have hd' : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 2 := by
    have : (x + 1) * (1 / x) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hx0]; linarith
    have h0 : 0 ≤ x + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hd h0]
  have e1 : x + 1 - 1 = x := by ring
  rw [e1, div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
    (by positivity)]
  nlinarith [mul_pos hx0 hx0]

theorem tr_prime_telescope (a g : ℕ → ℝ)
    (ha : ∀ m : ℕ, 1 ≤ m → 0 ≤ a (m + 1) ∧ a (m + 1) ≤ g m - g (m + 1)) :
    ∀ n : ℕ, 1 ≤ n → ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, a p ≤ g 1 - g n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have : (Finset.range (1 + 1)).filter Nat.Prime = ∅ := by decide
    rw [this]; simp
  | succ m hm ih =>
    rw [tr_sum_succ]
    obtain ⟨h1, h2⟩ := ha m hm
    split_ifs <;> linarith

theorem tr_tail_bound (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / (p * ((p : ℝ) - 1)) ≤ 2 := by
  have h := tr_prime_telescope (fun m => Real.log m / (m * ((m : ℝ) - 1)))
    (fun m => (2 + Real.log m) / m) ?_ n hn
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have : 0 ≤ (2 + Real.log n) / n := by positivity
    simp only [Nat.cast_one, Real.log_one, add_zero, div_one] at h
    linarith
  · intro m hm
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    refine ⟨?_, ?_⟩
    · push_cast
      have : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
      have : 0 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1 - 1) := by nlinarith
      positivity
    · push_cast
      exact tr_tail_real m hm'

/-! ## Mertens' first theorem, lower bound -/

theorem tr_mertens1_lower_explicit (n : ℕ) (hn : 1 ≤ n) :
    Real.log n - 3 ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : Real.log ((n.factorial : ℕ) : ℝ) ≤
      (n : ℝ) * (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p +
        ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / (p * ((p : ℝ) - 1))) := by
    rw [tr_log_factorial, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Finset.mem_filter.1 hp).2
    have h := tr_fact_le_div p n hpp
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have e : (n : ℝ) * (Real.log p / p + Real.log p / (p * ((p : ℝ) - 1))) =
        (n / ((p : ℝ) - 1)) * Real.log p := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h hl
  have h1 := tr_log_factorial_ge n hn
  have h2 := tr_tail_bound n hn
  have : (n : ℝ) * (Real.log n - 1) ≤ n * (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      Real.log p / p + 2) := by nlinarith
  have := le_of_mul_le_mul_left this hn'
  linarith

theorem tr_mertens1_lower : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    Real.log n - C ≤ ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p :=
  ⟨3, tr_mertens1_lower_explicit⟩

/-! ## Mertens' second theorem -/

theorem tr_log4_le : Real.log 4 ≤ 3 := by
  have := Real.log_le_sub_one_of_pos (x := 4) (by norm_num)
  linarith

theorem tr_E_bound (n : ℕ) (hn : 1 ≤ n) :
    |∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p - Real.log n| ≤ 3 := by
  have h1 := tr_mertens1_upper n
  have h2 := tr_mertens1_lower_explicit n hn
  have h3 := tr_log4_le
  rw [abs_le]; constructor <;> linarith

theorem tr_step_real (l l' E K D : ℝ) (hl : 0 < l) (hll : l ≤ l') (hd : l' - l ≤ 1)
    (hE : |E| ≤ K) (h1 : D ≤ l' / l - 1) (h2 : 1 - l / l' ≤ D) :
    |(l + E) * (1 / l - 1 / l') - D| ≤ (K + 1) * (1 / l - 1 / l') := by
  have hl' : 0 < l' := by linarith
  have ha : 0 ≤ 1 / l - 1 / l' := by
    have := one_div_le_one_div_of_le hl hll
    linarith
  have key : l' / l - 1 - (1 - l / l') ≤ 1 / l - 1 / l' := by
    have e1 : l' / l - 1 - (1 - l / l') = (l' - l) * (l' - l) / (l * l') := by
      field_simp
    have e2 : 1 / l - 1 / l' = (l' - l) / (l * l') := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have heq : (l + E) * (1 / l - 1 / l') = (1 - l / l') + E * (1 / l - 1 / l') := by
    field_simp
  have hEa : |E * (1 / l - 1 / l')| ≤ K * (1 / l - 1 / l') := by
    rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_right hE ha
  rw [abs_le] at hEa ⊢
  rw [heq]
  constructor <;> nlinarith [hEa.1, hEa.2]

theorem tr_telescope_abs (Q g : ℕ → ℝ)
    (h : ∀ n : ℕ, 2 ≤ n → |Q (n + 1) - Q n| ≤ g n - g (n + 1)) :
    ∀ n : ℕ, 2 ≤ n → |Q n - Q 2| ≤ g 2 - g n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have h1 := h m hm
    have h2 := abs_sub_le (Q (m + 1)) (Q m) (Q 2)
    linarith

theorem tr_Q_step (n : ℕ) (hn : 2 ≤ n) :
    |(∑ p ∈ (Finset.range (n + 1 + 1)).filter Nat.Prime, (1 : ℝ) / p -
        (∑ p ∈ (Finset.range (n + 1 + 1)).filter Nat.Prime, Real.log p / p) /
          Real.log ((n + 1 : ℕ) : ℝ) - Real.log (Real.log ((n + 1 : ℕ) : ℝ))) -
      (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p -
        (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p) / Real.log n -
          Real.log (Real.log n))| ≤
      4 / Real.log n - 4 / Real.log ((n + 1 : ℕ) : ℝ) := by
  set P := ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p with hP
  set S := ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p with hS
  set l := Real.log n with hl
  set l' := Real.log ((n + 1 : ℕ) : ℝ) with hl'
  set x : ℝ := if (n + 1).Prime then 1 / ((n + 1 : ℕ) : ℝ) else 0 with hx
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hlpos : 0 < l := Real.log_pos hn1
  have hn1' : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hll : l ≤ l' := by
    rw [hl, hl', hn1']; exact Real.log_le_log (by linarith) (by linarith)
  have hl'pos : 0 < l' := lt_of_lt_of_le hlpos hll
  have hP1 : ∑ p ∈ (Finset.range (n + 1 + 1)).filter Nat.Prime, (1 : ℝ) / p = P + x := by
    rw [tr_sum_succ]
  have hS1 : ∑ p ∈ (Finset.range (n + 1 + 1)).filter Nat.Prime, Real.log p / p = S + x * l' := by
    rw [tr_sum_succ, hx]
    split_ifs
    · ring
    · ring
  rw [hP1, hS1]
  have e : P + x - (S + x * l') / l' - Real.log l' - (P - S / l - Real.log l) =
      (l + (S - l)) * (1 / l - 1 / l') - (Real.log l' - Real.log l) := by
    field_simp
    ring
  rw [e]
  have hd : l' - l ≤ 1 := by
    rw [hl, hl', ← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (x := ((n + 1 : ℕ) : ℝ) / n) (by positivity)
    have e2 : ((n + 1 : ℕ) : ℝ) / n - 1 = 1 / n := by rw [hn1']; field_simp; ring
    have e3 : (1 : ℝ) / n ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have h1 : Real.log l' - Real.log l ≤ l' / l - 1 := by
    rw [← Real.log_div hl'pos.ne' hlpos.ne']
    exact Real.log_le_sub_one_of_pos (by positivity)
  have h2 : 1 - l / l' ≤ Real.log l' - Real.log l := by
    have := Real.log_le_sub_one_of_pos (x := l / l') (by positivity)
    rw [Real.log_div hlpos.ne' hl'pos.ne'] at this
    linarith
  have hE : |S - l| ≤ 3 := tr_E_bound n (by omega)
  have := tr_step_real l l' (S - l) 3 (Real.log l' - Real.log l) hlpos hll hd hE h1 h2
  have e4 : 4 / l - 4 / l' = (3 + 1) * (1 / l - 1 / l') := by ring
  rw [e4]
  exact this

theorem tr_mertens2 : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    |∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p - Real.log (Real.log n)| ≤ C := by
  set Q : ℕ → ℝ := fun n =>
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p -
      (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p) / Real.log n -
        Real.log (Real.log n) with hQ
  have hT := tr_telescope_abs Q (fun n => 4 / Real.log n) (fun n hn => by
    simp only [hQ]
    exact tr_Q_step n hn)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|Q 2| + 4 / Real.log 2 + (1 + 3 / Real.log 2), fun n hn => ?_⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn'
  have hlpos : 0 < Real.log n := lt_of_lt_of_le hlog2 hln
  have h1 := hT n hn
  have h4 : 0 ≤ 4 / Real.log n := by positivity
  have hQn : |Q n| ≤ |Q 2| + 4 / Real.log 2 := by
    have := abs_sub_abs_le_abs_sub (Q n) (Q 2)
    linarith
  set S := ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log p / p with hS
  have hS0 : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro p hp
    have hpp := (Finset.mem_filter.1 hp).2
    have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_le)
    positivity
  have hSu : S ≤ Real.log n + 3 := by
    have := tr_mertens1_upper n
    have := tr_log4_le
    linarith
  have hSl : |S / Real.log n| ≤ 1 + 3 / Real.log 2 := by
    rw [abs_of_nonneg (by positivity)]
    have e : S / Real.log n ≤ 1 + 3 / Real.log n := by
      rw [div_le_iff₀ hlpos, add_mul, div_mul_cancel₀ _ hlpos.ne']
      linarith
    have : 3 / Real.log n ≤ 3 / Real.log 2 :=
      div_le_div_of_nonneg_left (by norm_num) hlog2 hln
    linarith
  have e : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p - Real.log (Real.log n) =
      Q n + S / Real.log n := by
    simp only [hQ, hS]; ring
  rw [e]
  calc |Q n + S / Real.log n| ≤ |Q n| + |S / Real.log n| := abs_add_le _ _
    _ ≤ _ := by linarith


/-! ## Definitions (verbatim from defs.lean) -/

/-- product of the primes indexed by `T` -/
noncomputable def tr_prodP {ι : Type*} (p : ι → ℕ) (T : Finset ι) : ℝ := ∏ i ∈ T, (p i : ℝ)

/-- `1 / φ(∏ T)` -/
noncomputable def tr_phiInv {ι : Type*} (p : ι → ℕ) (T : Finset ι) : ℝ :=
  ∏ i ∈ T, 1 / ((p i : ℝ) - 1)

/-- `B = ∑_{d | P, d > 1} 1 / (φ(d) log d)` -/
noncomputable def tr_B {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
    tr_phiInv p T / Real.log (tr_prodP p T)

/-- the sieve coefficients `a(1) = 1`, `a(d) = -1/(B log d)` -/
noncomputable def tr_a {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (T : Finset ι) : ℝ :=
  if T = ∅ then 1 else -1 / (tr_B p * Real.log (tr_prodP p T))

/-- the prime set used for the sieve at scale `n` -/
noncomputable def tr_primes (n : ℕ) : Finset ℕ :=
  (Finset.Ioc (n ^ 4) ⌊Real.exp (Real.sqrt n)⌋₊).filter Nat.Prime


/-! ## Coefficient bounds: elementary real inequalities -/

theorem tr_c_exp_sub_sq_le (t : ℝ) (ht : 0 ≤ t) : Real.exp (t - t ^ 2) ≤ 1 + t := by
  have h1 : 0 < 1 + t := by linarith
  have h2 := Real.one_sub_inv_le_log_of_pos h1
  have h3 : t - t ^ 2 ≤ 1 - (1 + t)⁻¹ := by
    have e : 1 - (1 + t)⁻¹ = t / (1 + t) := by field_simp; ring
    rw [e, le_div_iff₀ h1]
    nlinarith [mul_nonneg ht (sq_nonneg t)]
  calc Real.exp (t - t ^ 2) ≤ Real.exp (Real.log (1 + t)) := Real.exp_le_exp.2 (by linarith)
    _ = 1 + t := Real.exp_log h1

theorem tr_c_log4 : 1 < Real.log 4 ∧ Real.log 4 = 2 * Real.log 2 := by
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  exact ⟨by rw [e]; linarith, e⟩

theorem tr_c_geom (d h : ℝ) (hd : 1 < d) (hh : 0 < h) (J : ℕ) :
    ∑ j ∈ range J, h * d ^ (-(((j : ℝ) + 1) * h)) ≤ 1 / Real.log d := by
  have hl : 0 < Real.log d := Real.log_pos hd
  set v := h * Real.log d with hv
  have hv0 : 0 < v := mul_pos hh hl
  set q := Real.exp (-v) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hterm : ∀ j : ℕ, d ^ (-(((j : ℝ) + 1) * h)) = q * q ^ j := by
    intro j
    rw [Real.rpow_def_of_pos (by linarith), ← pow_succ', hq, ← Real.exp_nat_mul]
    congr 1
    push_cast
    rw [hv]; ring
  have hsum : ∑ j ∈ range J, q ^ j ≤ 1 / (1 - q) := by
    rw [le_div_iff₀ (by linarith), geom_sum_mul_neg]
    have : 0 ≤ q ^ J := by positivity
    linarith
  have hqe : q * Real.exp v = 1 := by rw [hq, ← Real.exp_add]; simp
  have hev := Real.add_one_le_exp v
  calc ∑ j ∈ range J, h * d ^ (-(((j : ℝ) + 1) * h))
      = h * q * ∑ j ∈ range J, q ^ j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [hterm]; ring
    _ ≤ h * q * (1 / (1 - q)) := by
        apply mul_le_mul_of_nonneg_left hsum; positivity
    _ ≤ 1 / Real.log d := by
        rw [mul_one_div, div_le_div_iff₀ (by linarith) hl]
        have : q * (v + 1) ≤ 1 := by nlinarith
        rw [hv] at this
        nlinarith

theorem tr_c_inv_sq_sum (S : Finset ℕ) : ∑ q ∈ S, 1 / (q : ℝ) ^ 2 ≤ 2 := by
  have hs := (Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two
  have h1 := hs.sum_le_tsum S (fun _ _ => by positivity)
  rw [hasSum_zeta_two.tsum_eq] at h1
  have := Real.pi_lt_d2
  have hp := Real.pi_pos
  nlinarith

theorem tr_c_split (g : ℕ → ℝ) (Z w : ℕ) (h : Z ≤ w) :
    ∑ q ∈ (Ioc Z w).filter Nat.Prime, g q =
      ∑ q ∈ (range (w + 1)).filter Nat.Prime, g q -
        ∑ q ∈ (range (Z + 1)).filter Nat.Prime, g q := by
  rw [eq_sub_iff_add_eq, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, add_comm,
    ← Finset.Ico_add_one_add_one_eq_Ioc]
  exact Finset.sum_range_add_sum_Ico _ (by omega)

/-! ## Products over subsets -/

theorem tr_c_prod_identity {ι : Type*} [Fintype ι] (p : ι → ℕ) (x : ℝ) :
    ∑ T : Finset ι, tr_phiInv p T * tr_prodP p T ^ x =
      ∏ i, (1 + (p i : ℝ) ^ x * (1 / ((p i : ℝ) - 1))) := by
  rw [Finset.prod_one_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold tr_phiInv tr_prodP
  rw [← Real.finsetProd_rpow _ _ (fun i _ => Nat.cast_nonneg _), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by ring

theorem tr_c_sum_ne_empty {ι : Type*} [Fintype ι] [DecidableEq ι] (f : Finset ι → ℝ) :
    ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅), f T =
      ∑ T : Finset ι, f T - f ∅ := by
  rw [Finset.filter_ne', Finset.sum_erase_eq_sub (Finset.mem_univ _)]

theorem tr_c_prodP_ge {ι : Type*} (p : ι → ℕ) (hp : ∀ i, 2 ≤ p i) (T : Finset ι) (hT : T ≠ ∅) :
    2 ≤ tr_prodP p T := by
  classical
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hT
  unfold tr_prodP
  rw [← Finset.mul_prod_erase T _ ha]
  have h1 : (1 : ℝ) ≤ ∏ i ∈ T.erase a, (p i : ℝ) := by
    calc (1 : ℝ) = ∏ i ∈ T.erase a, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => by
          have := hp i
          exact_mod_cast (by omega : 1 ≤ p i))
  have h2 : (2 : ℝ) ≤ p a := by exact_mod_cast hp a
  nlinarith

theorem tr_c_phiInv_nonneg {ι : Type*} (p : ι → ℕ) (hp : ∀ i, 2 ≤ p i) (T : Finset ι) :
    0 ≤ tr_phiInv p T := by
  unfold tr_phiInv
  refine Finset.prod_nonneg fun i _ => ?_
  have : (2 : ℝ) ≤ p i := by exact_mod_cast hp i
  have : 0 < (p i : ℝ) - 1 := by linarith
  positivity

theorem tr_c_B_ge {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (hp : ∀ i, 2 ≤ p i)
    (h : ℝ) (hh : 0 < h) (J : ℕ) :
    ∑ j ∈ range J, h * (∏ i, (1 + (p i : ℝ) ^ (-(((j : ℝ) + 1) * h)) *
        (1 / ((p i : ℝ) - 1))) - 1) ≤ tr_B p := by
  unfold tr_B
  calc ∑ j ∈ range J, h * (∏ i, (1 + (p i : ℝ) ^ (-(((j : ℝ) + 1) * h)) *
        (1 / ((p i : ℝ) - 1))) - 1)
      = ∑ j ∈ range J, h * ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
          tr_phiInv p T * tr_prodP p T ^ (-(((j : ℝ) + 1) * h)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [tr_c_sum_ne_empty, tr_c_prod_identity]
        simp [tr_phiInv, tr_prodP]
    _ = ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
          tr_phiInv p T * ∑ j ∈ range J, h * tr_prodP p T ^ (-(((j : ℝ) + 1) * h)) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
          tr_phiInv p T / Real.log (tr_prodP p T) := by
        refine Finset.sum_le_sum fun T hT => ?_
        have hT' : T ≠ ∅ := (Finset.mem_filter.1 hT).2
        have hd := tr_c_prodP_ge p hp T hT'
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left (tr_c_geom _ h (by linarith) hh J)
          (tr_c_phiInv_nonneg p hp T)

/-! ## Lower bound for the Euler product `E(s)` -/

theorem tr_c_t_bounds (q a r : ℝ) (hq : 2 ≤ q) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hr : 1 - a ≤ r) :
    0 ≤ (1 - a) / q ∧ ((1 - a) / q) ^ 2 ≤ 1 / q ^ 2 ∧ (1 - a) / q ≤ r * (1 / (q - 1)) := by
  refine ⟨div_nonneg (by linarith) (by linarith), ?_, ?_⟩
  · rw [div_pow]
    gcongr
    nlinarith
  · rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith

theorem tr_c_E_ge (C : ℝ)
    (hC : ∀ n : ℕ, 2 ≤ n →
      |∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p - Real.log (Real.log n)| ≤ C)
    (Z Y : ℕ) (hZ : 4 ≤ Z) (hZY : Z ≤ Y) (s : ℝ) (hs1 : 1 / Real.log Y ≤ s)
    (hs2 : s ≤ 1 / Real.log Z) :
    Real.exp (-(2 * C + 3 + Real.log 4)) / 2 / (s * Real.log Z) ≤
      ∏ q ∈ (Ioc Z Y).filter Nat.Prime, (1 + (q : ℝ) ^ (-s) * (1 / ((q : ℝ) - 1))) := by
  have hZr : (4 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hYr : (Z : ℝ) ≤ Y := by exact_mod_cast hZY
  obtain ⟨hlog4, hlog4e⟩ := tr_c_log4
  have hL4 : Real.log 4 ≤ Real.log Z := Real.log_le_log (by norm_num) hZr
  have hL : 0 < Real.log Z := by linarith
  have hLY : Real.log Z ≤ Real.log Y := Real.log_le_log (by linarith) hYr
  have hLY0 : 0 < Real.log Y := by linarith
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs1
  have hsL : s * Real.log Z ≤ 1 := by rwa [le_div_iff₀ hL] at hs2
  have hs1' : s ≤ 1 := by nlinarith
  have hinv : Real.log Z ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
  have hinvY : 1 / s ≤ Real.log Y := by
    rw [div_le_iff₀ hs0]; rw [div_le_iff₀ (by linarith)] at hs1; linarith
  set w := ⌊Real.exp (1 / s)⌋₊ with hw
  have hexp0 := Real.exp_pos (1 / s)
  have hZexp : (Z : ℝ) ≤ Real.exp (1 / s) := by
    calc (Z : ℝ) = Real.exp (Real.log Z) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.2 hinv
  have hexpY : Real.exp (1 / s) ≤ Y := by
    calc Real.exp (1 / s) ≤ Real.exp (Real.log Y) := Real.exp_le_exp.2 hinvY
      _ = Y := Real.exp_log (by linarith)
  have hZw : Z ≤ w := Nat.le_floor hZexp
  have hwY : w ≤ Y := by
    have := Nat.floor_le_floor hexpY
    rw [Nat.floor_natCast] at this
    exact this
  have hwle : (w : ℝ) ≤ Real.exp (1 / s) := Nat.floor_le hexp0.le
  have hwgt : Real.exp (1 / s) < w + 1 := Nat.lt_floor_add_one _
  have hwr : (Z : ℝ) ≤ w := by exact_mod_cast hZw
  have hw0 : (0 : ℝ) < w := by linarith
  have hlogw_le : Real.log w ≤ 1 / s := by
    calc Real.log w ≤ Real.log (Real.exp (1 / s)) := Real.log_le_log hw0 hwle
      _ = 1 / s := Real.log_exp _
  have hlogw_ge : 1 / (2 * s) ≤ Real.log w := by
    set u := Real.exp (1 / (2 * s)) with hu
    have hu2 : 2 ≤ u := by
      have h2 : Real.log 2 ≤ 1 / (2 * s) := by
        rw [show 1 / (2 * s) = (1 / s) / 2 by ring]
        linarith
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ u := Real.exp_le_exp.2 h2
    have hsq : Real.exp (1 / s) = u * u := by
      rw [hu, ← Real.exp_add]; congr 1; field_simp; ring
    have : u ≤ w := by nlinarith
    calc 1 / (2 * s) = Real.log u := (Real.log_exp _).symm
      _ ≤ Real.log w := Real.log_le_log (by positivity) this
  set P := (Ioc Z Y).filter Nat.Prime with hP
  set t : ℕ → ℝ := fun q => if q ≤ w then (1 - s * Real.log q) / q else 0 with ht
  have hpt : ∀ q ∈ P, 0 ≤ t q ∧ t q ^ 2 ≤ 1 / (q : ℝ) ^ 2 ∧
      1 + t q ≤ 1 + (q : ℝ) ^ (-s) * (1 / ((q : ℝ) - 1)) := by
    intro q hq
    have hqp := (Finset.mem_filter.1 hq).2
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hqp.two_le
    have hlq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
    have hpow : 0 ≤ (q : ℝ) ^ (-s) * (1 / ((q : ℝ) - 1)) := by
      have : 0 < (q : ℝ) - 1 := by linarith
      positivity
    simp only [ht]
    split_ifs with hqw
    · have hqw' : (q : ℝ) ≤ w := by exact_mod_cast hqw
      have hlqw : Real.log q ≤ Real.log w := Real.log_le_log (by linarith) hqw'
      have hslq : s * Real.log q ≤ 1 := by
        calc s * Real.log q ≤ s * (1 / s) :=
              mul_le_mul_of_nonneg_left (by linarith) hs0.le
          _ = 1 := by field_simp
      have hslq0 : 0 ≤ s * Real.log q := mul_nonneg hs0.le hlq
      have hr : 1 - s * Real.log q ≤ (q : ℝ) ^ (-s) := by
        rw [Real.rpow_def_of_pos (by linarith)]
        have := Real.add_one_le_exp (Real.log q * -s)
        linarith
      obtain ⟨a1, a2, a3⟩ := tr_c_t_bounds q (s * Real.log q) _ hq2 hslq0 hslq hr
      exact ⟨a1, a2, by linarith⟩
    · refine ⟨le_refl _, by simp, by linarith⟩
  have hprod : Real.exp (∑ q ∈ P, (t q - t q ^ 2)) ≤
      ∏ q ∈ P, (1 + (q : ℝ) ^ (-s) * (1 / ((q : ℝ) - 1))) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod (fun q _ => (Real.exp_pos _).le)
    intro q hq
    obtain ⟨h0, -, h3⟩ := hpt q hq
    exact (tr_c_exp_sub_sq_le _ h0).trans h3
  have hsq : ∑ q ∈ P, t q ^ 2 ≤ 2 :=
    (Finset.sum_le_sum fun q hq => (hpt q hq).2.1).trans (tr_c_inv_sq_sum P)
  have hfilt : P.filter (fun q => q ≤ w) = (Ioc Z w).filter Nat.Prime := by
    ext q
    simp only [hP, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h1, _⟩, h3⟩, h4⟩; exact ⟨⟨h1, h4⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, by omega⟩, h3⟩, h2⟩
  have hsumt : ∑ q ∈ P, t q = ∑ q ∈ (Ioc Z w).filter Nat.Prime, (1 : ℝ) / q -
      s * ∑ q ∈ (Ioc Z w).filter Nat.Prime, Real.log q / q := by
    have e1 : ∑ q ∈ P, t q = ∑ q ∈ P.filter (fun q => q ≤ w), (1 - s * Real.log q) / q := by
      exact (Finset.sum_filter _ _).symm
    rw [e1, hfilt, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hsplit := tr_c_split (fun q : ℕ => (1 : ℝ) / q) Z w hZw
  have hCw := hC w (by omega)
  have hCZ := hC Z (by omega)
  rw [abs_le] at hCw hCZ
  have hlogsum : ∑ q ∈ (Ioc Z w).filter Nat.Prime, Real.log q / q ≤ Real.log w + Real.log 4 := by
    refine le_trans ?_ (tr_mertens1_upper w)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.filter_subset_filter
      intro x hx
      simp only [Finset.mem_Ioc] at hx
      simp only [Finset.mem_range]; omega
    · intro q hq _
      have h2 := (Finset.mem_filter.1 hq).2.two_le
      have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
      positivity
  have hslw : s * (Real.log w + Real.log 4) ≤ 1 + Real.log 4 := by
    have : s * Real.log w ≤ 1 := by
      calc s * Real.log w ≤ s * (1 / s) := mul_le_mul_of_nonneg_left hlogw_le hs0.le
        _ = 1 := by field_simp
    nlinarith
  have hll : Real.log (1 / (2 * s)) ≤ Real.log (Real.log w) :=
    Real.log_le_log (by positivity) hlogw_ge
  have hkey : Real.log (1 / (2 * s)) - Real.log (Real.log Z) + -(2 * C + 3 + Real.log 4) ≤
      ∑ q ∈ P, (t q - t q ^ 2) := by
    rw [Finset.sum_sub_distrib, hsumt]
    have := mul_le_mul_of_nonneg_left hlogsum hs0.le
    linarith
  calc Real.exp (-(2 * C + 3 + Real.log 4)) / 2 / (s * Real.log Z)
      = Real.exp (Real.log (1 / (2 * s)) - Real.log (Real.log Z) + -(2 * C + 3 + Real.log 4)) := by
        rw [Real.exp_add, Real.exp_sub, Real.exp_log (by positivity), Real.exp_log hL]
        field_simp
    _ ≤ Real.exp (∑ q ∈ P, (t q - t q ^ 2)) := Real.exp_le_exp.2 hkey
    _ ≤ _ := hprod

/-! ## Lower bound for `B` -/

theorem tr_c_harmonic (J : ℕ) :
    Real.log ((J : ℝ) + 1) ≤ ∑ j ∈ range J, 1 / ((j : ℝ) + 1) := by
  have h := log_add_one_le_harmonic J
  have e : ((harmonic J : ℚ) : ℝ) = ∑ j ∈ range J, 1 / ((j : ℝ) + 1) := by
    simp [harmonic]
  rw [e] at h
  exact_mod_cast h

theorem tr_c_B_lower (C : ℝ)
    (hC : ∀ n : ℕ, 2 ≤ n →
      |∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p - Real.log (Real.log n)| ≤ C)
    (Z Y : ℕ) (hZ : 4 ≤ Z) (hZY : Z ≤ Y) :
    (Real.exp (-(2 * C + 3 + Real.log 4)) / 2 *
        Real.log ((⌊Real.log Y / Real.log Z⌋₊ : ℝ) + 1) - 1) / Real.log Z ≤
      tr_B (fun i : ((Ioc Z Y).filter Nat.Prime) => (i : ℕ)) := by
  set c := Real.exp (-(2 * C + 3 + Real.log 4)) / 2 with hc
  have hc0 : 0 < c := by positivity
  have hZr : (4 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hYr : (Z : ℝ) ≤ Y := by exact_mod_cast hZY
  obtain ⟨hlog4, -⟩ := tr_c_log4
  have hL4 : Real.log 4 ≤ Real.log Z := Real.log_le_log (by norm_num) hZr
  set L := Real.log Z with hLdef
  have hL : 0 < L := by linarith
  set LY := Real.log Y with hLYdef
  have hLY : L ≤ LY := Real.log_le_log (by linarith) hYr
  have hLY0 : 0 < LY := by linarith
  set J := ⌊LY / L⌋₊ with hJ
  have hJle : (J : ℝ) ≤ LY / L := Nat.floor_le (by positivity)
  set h := 1 / LY with hh
  have hh0 : 0 < h := by positivity
  have hp : ∀ i : ((Ioc Z Y).filter Nat.Prime), 2 ≤ (i : ℕ) :=
    fun i => (Finset.mem_filter.1 i.2).2.two_le
  have hB := tr_c_B_ge (fun i : ((Ioc Z Y).filter Nat.Prime) => (i : ℕ)) hp h hh0 J
  have hterm : ∀ j ∈ range J, c / L * (1 / ((j : ℝ) + 1)) - h ≤
      h * (∏ i : ((Ioc Z Y).filter Nat.Prime), (1 + ((i : ℕ) : ℝ) ^ (-(((j : ℝ) + 1) * h)) *
        (1 / (((i : ℕ) : ℝ) - 1))) - 1) := by
    intro j hj
    have hjJ : (j : ℝ) + 1 ≤ J := by
      have := Finset.mem_range.1 hj
      exact_mod_cast (by omega : j + 1 ≤ J)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    set s := ((j : ℝ) + 1) * h with hs
    have hs1 : 1 / LY ≤ s := by rw [hs, ← hh]; nlinarith
    have hs2 : s ≤ 1 / L := by
      rw [hs, hh, le_div_iff₀ hL]
      have : ((j : ℝ) + 1) ≤ LY / L := hjJ.trans hJle
      rw [le_div_iff₀ hL] at this
      calc (j + 1) * (1 / LY) * L = ((j + 1) * L) / LY := by ring
        _ ≤ LY / LY := by gcongr
        _ = 1 := div_self hLY0.ne'
    have hE := tr_c_E_ge C hC Z Y hZ hZY s hs1 hs2
    rw [Finset.prod_coe_sort ((Ioc Z Y).filter Nat.Prime)
      (fun q : ℕ => 1 + (q : ℝ) ^ (-s) * (1 / ((q : ℝ) - 1)))]
    have e : c / L * (1 / ((j : ℝ) + 1)) = h * (c / (s * L)) := by
      rw [hs]; field_simp
    rw [e, ← hc] at *
    rw [mul_sub, mul_one]
    have := mul_le_mul_of_nonneg_left hE hh0.le
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hharm := tr_c_harmonic J
  have hJh : (J : ℝ) * h ≤ 1 / L := by
    rw [hh, mul_one_div, div_le_div_iff₀ hLY0 hL]
    rw [le_div_iff₀ hL] at hJle
    linarith
  have h1 : c * Real.log ((J : ℝ) + 1) / L ≤ c / L * ∑ j ∈ range J, 1 / ((j : ℝ) + 1) := by
    rw [mul_comm c, mul_div_assoc, mul_comm]
    exact mul_le_mul_of_nonneg_left hharm (by positivity)
  calc (c * Real.log ((J : ℝ) + 1) - 1) / L = c * Real.log ((J : ℝ) + 1) / L - 1 / L := by ring
    _ ≤ _ := by linarith

/-! ## Upper bound for the twisted Euler product -/

theorem tr_c_pow_term (q x lq ly : ℝ) (hq : 2 ≤ q) (hx0 : 0 ≤ x) (hx2 : x ≤ 2) (hly : 0 < ly)
    (hxl : x * ly ≤ 2 * lq) :
    Real.exp x * (1 / (q - 1)) ≤ 1 / q + 2 * (1 / q ^ 2) + 4 * Real.exp 2 / ly * (lq / q) := by
  set u := Real.exp x with hu
  set E := Real.exp 2 with hE
  have hE0 : 0 < E := Real.exp_pos 2
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_exp hx0
  have huE : u ≤ E := Real.exp_le_exp.2 hx2
  have hA : u - 1 ≤ x * E := by
    have h1 := Real.add_one_le_exp (-x)
    have h2 : Real.exp (-x) * u = 1 := by rw [hu, ← Real.exp_add]; simp
    have h3 : (1 - x) * u ≤ 1 := by nlinarith [Real.exp_pos x]
    nlinarith
  have hxlq : x ≤ 2 * lq / ly := by rw [le_div_iff₀ hly]; exact hxl
  have hq1 : 0 < q - 1 := by linarith
  have hq0 : 0 < q := by linarith
  have ha : 1 / (q - 1) ≤ 1 / q + 2 * (1 / q ^ 2) := by
    have e : 1 / q + 2 * (1 / q ^ 2) = (q + 2) / q ^ 2 := by field_simp
    rw [e, div_le_div_iff₀ hq1 (by positivity)]
    nlinarith
  have hb : (u - 1) * (1 / (q - 1)) ≤ 2 * (u - 1) / q := by
    rw [mul_one_div, div_le_div_iff₀ hq1 hq0]
    nlinarith
  have hc : 2 * (u - 1) / q ≤ 4 * E / ly * (lq / q) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hq0]
    have : x * E ≤ 2 * lq / ly * E := mul_le_mul_of_nonneg_right hxlq hE0.le
    calc 2 * (u - 1) ≤ 2 * (2 * lq / ly * E) := by linarith
      _ = 4 * E / ly * lq := by ring
  calc u * (1 / (q - 1)) = 1 / (q - 1) + (u - 1) * (1 / (q - 1)) := by ring
    _ ≤ _ := by linarith

theorem tr_c_F_le (C : ℝ)
    (hC : ∀ n : ℕ, 2 ≤ n →
      |∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p - Real.log (Real.log n)| ≤ C)
    (Z Y : ℕ) (hZ : 4 ≤ Z) (hZY : Z ≤ Y) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2 / Real.log Y) :
    ∏ i : ((Ioc Z Y).filter Nat.Prime), (1 + ((i : ℕ) : ℝ) ^ γ * (1 / (((i : ℕ) : ℝ) - 1))) ≤
      Real.exp (2 * C + 4 + 8 * Real.exp 2) * (Real.log Y / Real.log Z) := by
  have hZr : (4 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hYr : (Z : ℝ) ≤ Y := by exact_mod_cast hZY
  obtain ⟨hlog4, -⟩ := tr_c_log4
  have hL4 : Real.log 4 ≤ Real.log Z := Real.log_le_log (by norm_num) hZr
  set L := Real.log Z with hLdef
  have hL : 0 < L := by linarith
  set LY := Real.log Y with hLYdef
  have hLY : L ≤ LY := Real.log_le_log (by linarith) hYr
  have hLY0 : 0 < LY := by linarith
  set P := (Ioc Z Y).filter Nat.Prime with hP
  set E := Real.exp 2 with hE
  have hnn : ∀ i : P, 0 ≤ ((i : ℕ) : ℝ) ^ γ * (1 / (((i : ℕ) : ℝ) - 1)) := by
    intro i
    have : (2 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_filter.1 i.2).2.two_le
    have : 0 < ((i : ℕ) : ℝ) - 1 := by linarith
    positivity
  refine (Real.prod_one_add_le_exp_sum _ hnn).trans ?_
  rw [Finset.sum_coe_sort P (fun q : ℕ => (q : ℝ) ^ γ * (1 / ((q : ℝ) - 1)))]
  have hpt : ∀ q ∈ P, (q : ℝ) ^ γ * (1 / ((q : ℝ) - 1)) ≤
      1 / (q : ℝ) + 2 * (1 / (q : ℝ) ^ 2) + 4 * E / LY * (Real.log q / q) := by
    intro q hq
    have hmem := Finset.mem_filter.1 hq
    have hqY : (q : ℝ) ≤ Y := by exact_mod_cast (Finset.mem_Ioc.1 hmem.1).2
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hmem.2.two_le
    have hlq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
    have hlqY : Real.log q ≤ LY := Real.log_le_log (by linarith) hqY
    rw [Real.rpow_def_of_pos (by linarith)]
    have hγl : γ * LY ≤ 2 := by rwa [le_div_iff₀ hLY0] at hγ
    apply tr_c_pow_term q _ (Real.log q) LY hq2 (mul_nonneg hlq hγ0) _ hLY0
    · nlinarith
    · nlinarith
  refine Real.exp_le_exp.2 (Finset.sum_le_sum hpt) |>.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsplit := tr_c_split (fun q : ℕ => (1 : ℝ) / q) Z Y hZY
  have hCY := hC Y (by omega)
  have hCZ := hC Z (by omega)
  rw [abs_le] at hCY hCZ
  have hsq := tr_c_inv_sq_sum P
  have hlogsum : ∑ q ∈ P, Real.log q / q ≤ 2 * LY := by
    refine le_trans ?_ ((tr_mertens1_upper Y).trans (by linarith))
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.filter_subset_filter
      intro x hx
      simp only [Finset.mem_Ioc] at hx
      simp only [Finset.mem_range]; omega
    · intro q hq _
      have h2 := (Finset.mem_filter.1 hq).2.two_le
      have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
      positivity
  have hE0 : 0 < E := Real.exp_pos 2
  have h3 : 4 * E / LY * ∑ q ∈ P, Real.log q / q ≤ 8 * E := by
    calc 4 * E / LY * ∑ q ∈ P, Real.log q / q ≤ 4 * E / LY * (2 * LY) :=
          mul_le_mul_of_nonneg_left hlogsum (by positivity)
      _ = 8 * E := by field_simp; ring
  calc Real.exp (∑ q ∈ P, 1 / (q : ℝ) + 2 * ∑ q ∈ P, 1 / (q : ℝ) ^ 2 +
        4 * E / LY * ∑ q ∈ P, Real.log q / q)
      ≤ Real.exp (Real.log LY - Real.log L + (2 * C + 4 + 8 * E)) := by
        apply Real.exp_le_exp.2
        rw [hP, hsplit]
        rw [hP] at hsq h3
        linarith
    _ = Real.exp (2 * C + 4 + 8 * E) * (LY / L) := by
        rw [Real.exp_add, Real.exp_sub, Real.exp_log hLY0, Real.exp_log hL]; ring

/-! ## The twisted absolute coefficient sum -/

theorem tr_c_term_le (B ld D φ LY E2 : ℝ) (hB : 0 < B) (hld : 0 < ld) (hD : 0 ≤ D) (hφ : 0 ≤ φ)
    (hLY : 0 < LY) (hE2 : 0 ≤ E2) (h : D ≤ E2 ∨ LY ≤ ld) :
    1 / (B * ld) * D * φ ≤ E2 / B * (φ / ld) + 1 / (B * LY) * (φ * D) := by
  have hBld : 0 < B * ld := mul_pos hB hld
  have h2 : 0 ≤ 1 / (B * LY) * (φ * D) := by positivity
  have h3 : 0 ≤ E2 / B * (φ / ld) := by positivity
  rcases h with h | h
  · have h1 : 1 / (B * ld) * D * φ ≤ E2 / B * (φ / ld) := by
      calc 1 / (B * ld) * D * φ ≤ 1 / (B * ld) * E2 * φ := by gcongr
        _ = E2 / B * (φ / ld) := by field_simp
    linarith
  · have h1 : 1 / (B * ld) * D * φ ≤ 1 / (B * LY) * (φ * D) := by
      rw [mul_assoc, mul_comm D φ]
      gcongr
    linarith

theorem tr_c_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) (hp : ∀ i, 2 ≤ p i)
    (LY : ℝ) (hLY : 0 < LY) (hB : 0 < tr_B p) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2 / LY) :
    ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
        |tr_a p T| * tr_prodP p T ^ γ * tr_phiInv p T ≤
      Real.exp 2 + (∏ i, (1 + (p i : ℝ) ^ γ * (1 / ((p i : ℝ) - 1)))) / (tr_B p * LY) := by
  set B := tr_B p with hBdef
  have hγ' : γ * LY ≤ 2 := by rwa [le_div_iff₀ hLY] at hγ
  have hterm : ∀ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
      |tr_a p T| * tr_prodP p T ^ γ * tr_phiInv p T ≤
        Real.exp 2 / B * (tr_phiInv p T / Real.log (tr_prodP p T)) +
          1 / (B * LY) * (tr_phiInv p T * tr_prodP p T ^ γ) := by
    intro T hT
    have hT' : T ≠ ∅ := (Finset.mem_filter.1 hT).2
    have hd := tr_c_prodP_ge p hp T hT'
    have hld : 0 < Real.log (tr_prodP p T) := Real.log_pos (by linarith)
    have ha : |tr_a p T| = 1 / (B * Real.log (tr_prodP p T)) := by
      rw [tr_a, if_neg hT', abs_div, abs_neg, abs_one, abs_of_pos (mul_pos hB hld)]
    rw [ha]
    have hD : 0 ≤ tr_prodP p T ^ γ := Real.rpow_nonneg (by linarith) _
    apply tr_c_term_le _ _ _ _ _ _ hB hld hD (tr_c_phiInv_nonneg p hp T) hLY (Real.exp_pos 2).le
    by_cases hc : Real.log (tr_prodP p T) ≤ LY
    · left
      rw [Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.2
      nlinarith
    · right; linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    tr_c_sum_ne_empty (fun T => tr_phiInv p T * tr_prodP p T ^ γ), tr_c_prod_identity]
  have hBsum : ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
      tr_phiInv p T / Real.log (tr_prodP p T) = B := rfl
  have he : tr_phiInv p ∅ * tr_prodP p ∅ ^ γ = 1 := by simp [tr_phiInv, tr_prodP]
  rw [hBsum, he, div_mul_cancel₀ _ hB.ne', mul_sub, mul_one, one_div_mul_eq_div]
  have : 0 < 1 / (B * LY) := by positivity
  linarith

/-! ## Final asymptotic bookkeeping -/

theorem tr_c_log_le (y : ℝ) (hy : 256 ≤ y) : Real.log y ≤ y / 8 := by
  have hy0 : 0 < y := by linarith
  have hs := Real.sqrt_pos.2 hy0
  have h1 := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hy0.le] at h1
  have h16 : 16 ≤ Real.sqrt y := by
    rw [show (16 : ℝ) = Real.sqrt 256 by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hy
  have hsq := Real.mul_self_sqrt hy0.le
  nlinarith

theorem tr_c_final_B (c l X : ℝ) (hc : 0 < c) (hl : 256 ≤ l) (hl8c : 8 / c ≤ l)
    (hX : l / 2 - 3 - l / 8 ≤ X) : c / 32 ≤ (c * X - 1) / (4 * l) := by
  have hcl : 8 ≤ c * l := by rwa [div_le_iff₀ hc, mul_comm] at hl8c
  rw [le_div_iff₀ (by linarith)]
  nlinarith

theorem tr_c_final_2 (F K B b0 LY L : ℝ) (hb0 : 0 < b0) (hB : b0 ≤ B) (hLY : 0 < LY) (hL : 0 < L)
    (hF : F ≤ K * (LY / L)) (hK : K / b0 ≤ L) : F / (B * LY) ≤ 1 := by
  have hB0 : 0 < B := by linarith
  rw [div_le_iff₀ hb0] at hK
  have hK' : K ≤ B * L := by nlinarith
  rw [div_le_one (mul_pos hB0 hLY)]
  calc F ≤ K * (LY / L) := hF
    _ ≤ B * L * (LY / L) := mul_le_mul_of_nonneg_right hK' (by positivity)
    _ = B * LY := by field_simp

/-- the analytic input: `B ≍ 1` and the twisted absolute coefficient sum is bounded -/
theorem tr_coef_bounds : ∃ b0 K1 : ℝ, 0 < b0 ∧ 0 ≤ K1 ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    b0 ≤ tr_B (fun i : tr_primes n => (i : ℕ)) ∧
    ∀ γ : ℝ, 0 ≤ γ → γ ≤ 2 / Real.log (⌊Real.exp (Real.sqrt n)⌋₊ : ℕ) →
      ∑ T ∈ (Finset.univ : Finset (Finset (tr_primes n))).filter (fun T => T ≠ ∅),
        |tr_a (fun i : tr_primes n => (i : ℕ)) T| *
          tr_prodP (fun i : tr_primes n => (i : ℕ)) T ^ γ *
          tr_phiInv (fun i : tr_primes n => (i : ℕ)) T ≤ K1 := by
  obtain ⟨C, hC⟩ := tr_mertens2
  set c := Real.exp (-(2 * C + 3 + Real.log 4)) / 2 with hc
  have hc0 : 0 < c := by positivity
  set K := Real.exp (2 * C + 4 + 8 * Real.exp 2) with hK
  set b0 := c / 32 with hb0
  have hb00 : 0 < b0 := by positivity
  refine ⟨b0, Real.exp 2 + 1, hb00, by positivity, ?_⟩
  set A := max (max 256 (8 / c)) (K / b0) with hA
  refine ⟨⌈Real.exp A⌉₊ + 2, fun n hn => ?_⟩
  have hnA : Real.exp A ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈Real.exp A⌉₊ ≤ n))
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hnA
  set l := Real.log n with hl
  have hlA : A ≤ l := by
    rw [← Real.log_exp A]; exact Real.log_le_log (Real.exp_pos _) hnA
  have hl256 : 256 ≤ l := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlA
  have hl8c : 8 / c ≤ l := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlA
  have hlK : K / b0 ≤ l := le_trans (le_max_right _ _) hlA
  set x := Real.sqrt n with hx
  have hxpos : 0 < x := Real.sqrt_pos.2 hn0
  have hxl : Real.log x = l / 2 := by rw [hx, Real.log_sqrt hn0.le]
  have hxexp : x = Real.exp (l / 2) := by rw [← hxl, Real.exp_log hxpos]
  have hquad := Real.quadratic_le_exp_of_nonneg (x := l / 2) (by linarith)
  rw [← hxexp] at hquad
  have hx4l : 4 * l ≤ x := by nlinarith
  have hx2 : 2 ≤ x := by linarith
  set Y := ⌊Real.exp x⌋₊ with hY
  have hex2 : 2 ≤ Real.exp x := by have := Real.add_one_le_exp x; linarith
  have hYgt : Real.exp x < Y + 1 := Nat.lt_floor_add_one _
  have hY1 : Real.exp x / 2 ≤ Y := by linarith
  have hlog2 := Real.log_two_lt_d9
  have hlogY : x / 2 ≤ Real.log Y := by
    have h := Real.log_le_log (by positivity) hY1
    rw [Real.log_div (Real.exp_pos x).ne' (by norm_num), Real.log_exp] at h
    linarith
  have hZ4 : 4 ≤ n ^ 4 := by
    have : 2 ≤ n := by omega
    calc 4 ≤ 2 ^ 4 := by norm_num
      _ ≤ n ^ 4 := Nat.pow_le_pow_left this 4
  have hnexp : (n : ℝ) = Real.exp l := (Real.exp_log hn0).symm
  have hZY : n ^ 4 ≤ Y := by
    apply Nat.le_floor
    push_cast
    rw [hnexp, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.2 (by push_cast; linarith)
  have hLZ : Real.log ((n ^ 4 : ℕ) : ℝ) = 4 * l := by
    have e : Real.log ((n : ℝ) ^ 4) = 4 * Real.log n := by rw [Real.log_pow]; norm_num
    push_cast; rw [e]
  have hLYpos : 0 < Real.log Y := by linarith
  -- part 1
  have hBl := tr_c_B_lower C hC (n ^ 4) Y hZ4 hZY
  rw [hLZ] at hBl
  have hJ : Real.log (Y : ℝ) / (4 * l) <
      (⌊Real.log (Y : ℝ) / (4 * l)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogJ : l / 2 - 3 - l / 8 ≤
      Real.log ((⌊Real.log (Y : ℝ) / (4 * l)⌋₊ : ℝ) + 1) := by
    have h1 : x / (8 * l) ≤ Real.log (Y : ℝ) / (4 * l) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have h2 := Real.log_le_log (by positivity) (h1.trans hJ.le)
    rw [Real.log_div hxpos.ne' (by positivity), Real.log_mul (by norm_num) (by positivity),
      hxl] at h2
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have h3 := tr_c_log_le l hl256
    linarith
  have hB : b0 ≤ tr_B (fun i : ((Ioc (n ^ 4) Y).filter Nat.Prime) => (i : ℕ)) :=
    (tr_c_final_B c l _ hc0 hl256 hl8c hlogJ).trans hBl
  refine ⟨hB, fun γ hγ0 hγ => ?_⟩
  -- part 2
  have hp : ∀ i : ((Ioc (n ^ 4) Y).filter Nat.Prime), 2 ≤ (i : ℕ) :=
    fun i => (Finset.mem_filter.1 i.2).2.two_le
  have hS := tr_c_sum_bound (fun i : ((Ioc (n ^ 4) Y).filter Nat.Prime) => (i : ℕ)) hp
    (Real.log (Y : ℝ)) hLYpos (lt_of_lt_of_le hb00 hB) γ hγ0 hγ
  have hF := tr_c_F_le C hC (n ^ 4) Y hZ4 hZY γ hγ0 hγ
  rw [hLZ] at hF
  have h2 := tr_c_final_2 _ K _ b0 (Real.log (Y : ℝ)) (4 * l) hb00 hB hLYpos (by positivity) hF
    (by linarith)
  exact hS.trans (by linarith)

theorem tr_crt_mul_sum (a b : ℕ) (hab : Nat.Coprime a b) (A B : ℕ → ℝ) :
    ∑ t ∈ Finset.range (a * b), A (t % a) * B (t % b)
      = (∑ x ∈ Finset.range a, A x) * (∑ y ∈ Finset.range b, B y) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hinj : Set.InjOn (fun t => (t % a, t % b)) (Finset.range (a * b) : Set ℕ) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    simp only [Prod.mk.injEq] at hxy
    have h1 : x ≡ y [MOD a * b] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hab).mp ⟨hxy.1, hxy.2⟩
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h1
  have himg : (Finset.range (a * b)).image (fun t => (t % a, t % b))
      = Finset.range a ×ˢ Finset.range b := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_image, Finset.mem_range] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at ht)
      have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at ht)
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨Nat.mod_lt _ ha, Nat.mod_lt _ hb⟩
    · rw [Finset.card_image_of_injOn hinj, Finset.card_product]
      simp
  rw [← himg, Finset.sum_image hinj]

theorem tr_crt_full {ι : Type*} [DecidableEq ι] (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (g : ι → ℕ → ℝ) (U : Finset ι) :
    ∑ t ∈ Finset.range (∏ i ∈ U, p i), ∏ i ∈ U, g i (t % p i)
      = ∏ i ∈ U, ∑ j ∈ Finset.range (p i), g i j := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hcop : Nat.Coprime (p a) (∏ i ∈ s, p i) := by
      apply Nat.Coprime.prod_right
      intro i hi
      rw [Nat.coprime_primes (hp a) (hp i)]
      intro h
      exact ha (hinj h ▸ hi)
    have key : ∀ t, ∏ i ∈ insert a s, g i (t % p i)
        = g a (t % p a) * (fun y => ∏ i ∈ s, g i (y % p i)) (t % ∏ i ∈ s, p i) := by
      intro t
      rw [Finset.prod_insert ha]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [Nat.mod_mod_of_dvd _ (Finset.dvd_prod_of_mem p hi)]
    rw [Finset.sum_congr rfl (fun t _ => key t), Finset.prod_insert ha, Finset.prod_insert ha,
      tr_crt_mul_sum _ _ hcop (g a) (fun y => ∏ i ∈ s, g i (y % p i)), ih]

theorem tr_crt_shift (F : ℕ → ℝ) (m : ℕ) (hper : ∀ t, F (t + m) = F t) (c : ℕ) :
    ∑ t ∈ Finset.range m, F (t + c) = ∑ t ∈ Finset.range m, F t := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h1 := Finset.sum_range_succ (fun t => F (t + c)) m
    have h2 := Finset.sum_range_succ' (fun t => F (t + c)) m
    have h3 : F (m + c) = F (0 + c) := by rw [add_comm m c, hper, zero_add]
    have h4 : ∑ t ∈ Finset.range m, F (t + (c + 1))
        = ∑ t ∈ Finset.range m, F (t + 1 + c) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      omega
    rw [h4]
    linarith

theorem tr_crt_bound (F : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (C : ℝ)
    (hper : ∀ t, F (t + m) = F t) (hF : ∀ t, |F t| ≤ 1) (hC : |C| ≤ 1)
    (hS : ∑ t ∈ Finset.range m, F t = m * C) (T : ℕ) :
    |∑ t ∈ Finset.range T, F (t + 1) - T * C| ≤ 2 * m := by
  induction T using Nat.strong_induction_on with
  | _ T ih =>
    by_cases hT : T < m
    · have h1 : |∑ t ∈ Finset.range T, F (t + 1)| ≤ T := by
        calc |∑ t ∈ Finset.range T, F (t + 1)|
            ≤ ∑ t ∈ Finset.range T, |F (t + 1)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ t ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum (fun t _ => hF _)
          _ = T := by simp
      have h2 : |(T : ℝ) * C| ≤ T := by
        rw [abs_mul, Nat.abs_cast]
        have : (0 : ℝ) ≤ T := Nat.cast_nonneg T
        nlinarith [abs_nonneg C]
      have h3 : (T : ℝ) ≤ m := by exact_mod_cast hT.le
      calc |∑ t ∈ Finset.range T, F (t + 1) - T * C|
          ≤ |∑ t ∈ Finset.range T, F (t + 1)| + |(T : ℝ) * C| := abs_sub _ _
        _ ≤ 2 * m := by linarith
    · push Not at hT
      obtain ⟨k, rfl⟩ : ∃ k, T = k + m := ⟨T - m, by omega⟩
      have hk := ih k (by omega)
      rw [Finset.sum_range_add]
      have h5 : ∑ x ∈ Finset.range m, F (k + x + 1) = m * C := by
        rw [← hS, ← tr_crt_shift F m hper (k + 1)]
        apply Finset.sum_congr rfl
        intro t _
        congr 1
        omega
      rw [h5]
      push_cast
      have e : ∑ x ∈ Finset.range k, F (x + 1) + m * C - (k + m) * C
          = ∑ x ∈ Finset.range k, F (x + 1) - k * C := by ring
      rw [e]
      exact hk

theorem tr_crt_avg {ι : Type*} [DecidableEq ι] (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (U : Finset ι) (g : ι → ℕ → ℝ) (hg : ∀ i j, |g i j| ≤ 1) (T : ℕ) :
    |∑ t ∈ Finset.range T, ∏ i ∈ U, g i ((t + 1) % p i)
      - T * ∏ i ∈ U, ((1 : ℝ) / p i * ∑ j ∈ Finset.range (p i), g i j)| ≤ 2 * ∏ i ∈ U, (p i : ℝ) := by
  have hm : 0 < ∏ i ∈ U, p i := Finset.prod_pos (fun i _ => (hp i).pos)
  have hper : ∀ t, (fun t => ∏ i ∈ U, g i (t % p i)) (t + ∏ i ∈ U, p i)
      = (fun t => ∏ i ∈ U, g i (t % p i)) t := by
    intro t
    simp only
    apply Finset.prod_congr rfl
    intro i hi
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem p hi
    rw [hk, Nat.add_mul_mod_self_left]
  have hF : ∀ t, |(fun t => ∏ i ∈ U, g i (t % p i)) t| ≤ 1 := by
    intro t
    simp only
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hg _ _)
  have hC : |∏ i ∈ U, ((1 : ℝ) / p i * ∑ j ∈ Finset.range (p i), g i j)| ≤ 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro i _
    have hpi : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
    have hs : |∑ j ∈ Finset.range (p i), g i j| ≤ p i := by
      calc |∑ j ∈ Finset.range (p i), g i j|
          ≤ ∑ j ∈ Finset.range (p i), |g i j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range (p i), (1 : ℝ) := Finset.sum_le_sum (fun j _ => hg _ _)
        _ = p i := by simp
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / p i)]
    calc 1 / (p i : ℝ) * |∑ j ∈ Finset.range (p i), g i j| ≤ 1 / p i * p i := by
          gcongr
      _ = 1 := by field_simp
  have hS : ∑ t ∈ Finset.range (∏ i ∈ U, p i), (fun t => ∏ i ∈ U, g i (t % p i)) t
      = ((∏ i ∈ U, p i : ℕ) : ℝ)
        * ∏ i ∈ U, ((1 : ℝ) / p i * ∑ j ∈ Finset.range (p i), g i j) := by
    simp only
    rw [tr_crt_full p hp hinj g U, Nat.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hpi : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne_zero
    field_simp
  have h := tr_crt_bound (fun t => ∏ i ∈ U, g i (t % p i)) _ hm _ hper hF hC hS T
  rw [Nat.cast_prod] at h
  exact h

theorem tr_n_exp_cube (y : ℝ) (hy : 0 ≤ y) : y ^ 3 / 27 ≤ Real.exp y := by
  have h := Real.add_one_le_exp (y / 3)
  have he : Real.exp y = Real.exp (y / 3) ^ 3 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [he]
  calc y ^ 3 / 27 = (y / 3) ^ 3 := by ring
    _ ≤ (y / 3 + 1) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    _ ≤ Real.exp (y / 3) ^ 3 := pow_le_pow_left₀ (by positivity) h 3

theorem tr_n_S2 (x s C k S2 : ℝ) (hx : 100 ≤ x) (hs0 : 0 ≤ s) (hs : s ≤ x) (hC0 : 0 ≤ C)
    (hC : C ≤ x) (hk0 : 0 ≤ k) (hk : k ≤ (x + 1) / 10) (hS0 : 0 ≤ S2)
    (hS : S2 ≤ 2 * (s + C) / (x ^ 4 - 1)) : 4 * k ^ 2 * S2 ≤ 1 / 40 := by
  have hx2 : 100 * x ≤ x ^ 2 := by nlinarith
  have hx4 : 10000 * x ^ 2 ≤ x ^ 4 := by nlinarith
  have hpos : 0 < x ^ 4 - 1 := by nlinarith
  have h1 : S2 * (x ^ 4 - 1) ≤ 2 * (s + C) := (le_div_iff₀ hpos).mp hS
  have h2 : S2 * x ^ 4 ≤ 8 * x := by
    nlinarith [mul_nonneg hS0 (by nlinarith : (0:ℝ) ≤ x ^ 4 - 2)]
  have h3 : S2 * x ^ 3 ≤ 8 := by
    have e : S2 * x ^ 4 = x * (S2 * x ^ 3) := by ring
    rw [e] at h2
    have hxp : 0 < x := by linarith
    nlinarith
  have h4 : S2 * x ^ 2 ≤ 8 / 100 := by
    have e : S2 * x ^ 3 = x * (S2 * x ^ 2) := by ring
    rw [e] at h3
    have hS2x : 0 ≤ S2 * x ^ 2 := by positivity
    nlinarith
  have hk2 : k ^ 2 ≤ ((x + 1) / 10) ^ 2 := pow_le_pow_left₀ hk0 hk 2
  have hk3 : ((x + 1) / 10) ^ 2 ≤ x ^ 2 / 25 := by nlinarith
  have h5 : 4 * k ^ 2 * S2 ≤ 4 * (x ^ 2 / 25) * S2 :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  nlinarith

theorem tr_n_v (x k lg : ℝ) (hx : 100 ≤ x) (hk0 : 0 ≤ k) (hk : k ≤ (x + 1) / 10)
    (hlg : 1 ≤ lg) : 0 ≤ k * (x / 8) / ((x ^ 4 - 1) * lg) ∧
      k * (x / 8) / ((x ^ 4 - 1) * lg) ≤ 1 / 80 := by
  have hx2 : 100 * x ≤ x ^ 2 := by nlinarith
  have hx4 : 10000 * x ^ 2 ≤ x ^ 4 := by nlinarith
  have hd : 0 < x ^ 4 - 1 := by nlinarith
  have hQ : 0 < (x ^ 4 - 1) * lg := mul_pos hd (by linarith)
  refine ⟨div_nonneg (by positivity) hQ.le, ?_⟩
  rw [div_le_iff₀ hQ]
  have h1 : x ^ 4 - 1 ≤ (x ^ 4 - 1) * lg := by nlinarith [mul_le_mul_of_nonneg_left hlg hd.le]
  have h2 : k * (x / 8) ≤ (x + 1) / 10 * (x / 8) :=
    mul_le_mul_of_nonneg_right hk (by linarith)
  nlinarith

theorem tr_n_expm1 (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1 / 80) : Real.exp v - 1 ≤ 1 / 40 := by
  have hm := Real.add_one_le_exp (-v)
  have hprod : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
  have hE0 : 0 < Real.exp v := Real.exp_pos v
  have hA : Real.exp v * (1 - v) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - v ≤ Real.exp (-v)) hE0.le]
  have hB : Real.exp v * (79 / 80) ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (79 / 80 : ℝ) ≤ 1 - v) hE0.le]
  have hC : Real.exp v * v ≤ Real.exp v * (1 / 80) := mul_le_mul_of_nonneg_left h1 hE0.le
  nlinarith

theorem tr_n_E1 (x s L k K1 B b0 : ℝ) (hs : 3 ≤ s) (hx : x = s ^ 2) (hL0 : 0 < L)
    (hL : L ≤ s) (hK1 : 0 ≤ K1) (hb0 : 0 < b0) (hB : b0 ≤ B) (hk0 : 0 ≤ k)
    (hk : k ≤ b0 / (64 * (K1 + 1)) * (x + 1)) :
    -((1 / L) * (x / 8)) + k * (1 / L) * K1 / B ≤ -(s / 16) := by
  have hBp : 0 < B := by linarith
  have hx9 : 9 ≤ x := by nlinarith
  have hk' : k * (64 * (K1 + 1)) ≤ b0 * (x + 1) := by
    have := mul_le_mul_of_nonneg_right hk (by positivity : (0:ℝ) ≤ 64 * (K1 + 1))
    have e : b0 / (64 * (K1 + 1)) * (x + 1) * (64 * (K1 + 1)) = b0 * (x + 1) := by
      field_simp
    linarith
  have hq1 : k * K1 / B ≤ k * K1 / b0 :=
    div_le_div_of_nonneg_left (mul_nonneg hk0 hK1) hb0 hB
  have hq2 : k * K1 / b0 ≤ (x + 1) / 64 := by
    rw [div_le_iff₀ hb0]
    nlinarith
  have e : -((1 / L) * (x / 8)) + k * (1 / L) * K1 / B = (-(x / 8) + k * K1 / B) / L := by
    field_simp
  rw [e, div_le_iff₀ hL0]
  nlinarith [mul_le_mul_of_nonneg_left hL (by linarith : (0:ℝ) ≤ s)]

theorem tr_n_tail (s : ℝ) (hs : 624 ≤ s) : Real.exp (-(s / 16)) ≤ 1 / 40 := by
  have h1 : Real.exp (-(s / 16)) * Real.exp (s / 16) = 1 := by rw [← Real.exp_add]; simp
  have h2 : 40 ≤ Real.exp (s / 16) := by linarith [Real.add_one_le_exp (s / 16)]
  have h3 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-(s / 16))).le
  linarith

theorem tr_n_Aterm (s x k K1 E : ℝ) (hs : 110592 * (1 + K1) ^ 2 ≤ s) (hs1 : 1 ≤ s)
    (hx : x = s ^ 2) (hk0 : 0 ≤ k) (hk : k ≤ (x + 1) / 10) (hK1 : 0 ≤ K1) (hE : 0 ≤ E)
    (hE2 : E ≤ Real.exp (-(s / 8))) : k * (2 * (2 * (1 + K1) ^ 2 * E)) ≤ 1 / 10 := by
  set c := (1 + K1) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set F := Real.exp (s / 8) with hFdef
  have hF0 : 0 < F := Real.exp_pos _
  have hF1 : (s / 8) ^ 3 / 27 ≤ F := tr_n_exp_cube (s / 8) (by linarith)
  have hx1 : x + 1 ≤ 2 * s ^ 2 := by nlinarith
  have h8 : 8 * c * s ^ 2 ≤ s ^ 3 / 13824 := by
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg s)]
  have hF : (x + 1) * (4 * c) ≤ F := by
    nlinarith [mul_le_mul_of_nonneg_right hx1 (by positivity : (0:ℝ) ≤ 4 * c)]
  have hEF : E * F ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hE2 hF0.le
    have e : Real.exp (-(s / 8)) * F = 1 := by rw [hFdef, ← Real.exp_add]; simp
    linarith
  have hk4 : k * (4 * c) ≤ (x + 1) / 10 * (4 * c) := mul_le_mul_of_nonneg_right hk (by positivity)
  calc k * (2 * (2 * c * E)) = (k * (4 * c)) * E := by ring
    _ ≤ ((x + 1) / 10 * (4 * c)) * E := mul_le_mul_of_nonneg_right hk4 hE
    _ ≤ (F / 10) * E := mul_le_mul_of_nonneg_right (by linarith) hE
    _ ≤ 1 / 10 := by nlinarith

theorem tr_n_eta (x k lg : ℝ) (hx : 100 ≤ x) (hk0 : 0 ≤ k) (hk : k ≤ (x + 1) / 10)
    (hlg : 1 ≤ lg) : k * (2 * (2 * (2 * (x / 8) / ((x ^ 4 - 1) * lg)) ^ 2)) ≤ 1 / 10 := by
  have hx2 : 100 * x ≤ x ^ 2 := by nlinarith
  have hx4 : 10000 * x ^ 2 ≤ x ^ 4 := by nlinarith
  have hd : 0 < x ^ 4 - 1 := by nlinarith
  set Q := (x ^ 4 - 1) * lg with hQdef
  have hQ : 0 < Q := mul_pos hd (by linarith)
  have hQ1 : x ^ 4 - 1 ≤ Q := by nlinarith [mul_le_mul_of_nonneg_left hlg hd.le]
  set η := 2 * (x / 8) / Q with hη
  have hη0 : 0 ≤ η := div_nonneg (by linarith) hQ.le
  have hηQ : η * Q = 2 * (x / 8) := div_mul_cancel₀ _ hQ.ne'
  have hη1 : η * (x + 1) ≤ 1 := by
    have h : (η * (x + 1)) * Q ≤ 1 * Q := by
      have e : (η * (x + 1)) * Q = (x / 4) * (x + 1) := by
        rw [show (η * (x + 1)) * Q = (η * Q) * (x + 1) by ring, hηQ]; ring
      rw [e]; nlinarith
    exact le_of_mul_le_mul_right h hQ
  have hη2 : η ≤ 1 / 4 := by nlinarith
  have hk' : k * η ^ 2 ≤ (x + 1) / 10 * η ^ 2 := mul_le_mul_of_nonneg_right hk (by positivity)
  have e2 : (x + 1) / 10 * η ^ 2 = η * (η * (x + 1)) / 10 := by ring
  have h3 : η * (η * (x + 1)) ≤ η * 1 := mul_le_mul_of_nonneg_left hη1 hη0
  nlinarith

theorem tr_n_W (x T : ℝ) (k : ℕ) (hx : 300 ≤ x) (hk : (k : ℝ) ≤ (x + 1) / 10)
    (hT : Real.exp x - 1 ≤ T) :
    ((k : ℝ) + 1) * (2 * (Real.exp (x / 8) ^ 2 * 2 ^ k) ^ 2 / T) ≤ 1 / 10 := by
  have h2k : (2 : ℝ) ^ k ≤ Real.exp k := by
    calc (2 : ℝ) ^ k ≤ Real.exp 1 ^ k :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1]) k
      _ = Real.exp k := by rw [← Real.exp_nat_mul]; simp
  set G := Real.exp (x / 2 + 2 * k) with hG
  set H := Real.exp (x / 2 - 2 * k) with hH
  have hP : (Real.exp (x / 8) ^ 2 * 2 ^ k) ^ 2 ≤ G := by
    calc (Real.exp (x / 8) ^ 2 * 2 ^ k) ^ 2 ≤ (Real.exp (x / 8) ^ 2 * Real.exp k) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left h2k (by positivity)) 2
      _ = G := by
          rw [hG, show x / 2 + 2 * (k : ℝ) = (x / 8 + x / 8 + k) + (x / 8 + x / 8 + k) by ring]
          simp only [Real.exp_add]; ring
  have hGH : G * H = Real.exp x := by
    rw [hG, hH, ← Real.exp_add]; congr 1; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hH1 : x ^ 3 / 1728 ≤ H := by
    have h := tr_n_exp_cube (x / 4) (by linarith)
    have h' : Real.exp (x / 4) ≤ H := Real.exp_le_exp.mpr (by linarith)
    have e : (x / 4) ^ 3 / 27 = x ^ 3 / 1728 := by ring
    linarith
  have hx2 : 300 * x ≤ x ^ 2 := by nlinarith
  have hx3 : 300 * x ^ 2 ≤ x ^ 3 := by nlinarith
  have hH2 : 40 * (k + 1) ≤ H := by nlinarith
  have hG0 : 0 < G := Real.exp_pos _
  have hex : 2 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hTp : 0 < T := by linarith
  rw [show ((k : ℝ) + 1) * (2 * (Real.exp (x / 8) ^ 2 * 2 ^ k) ^ 2 / T)
      = ((k : ℝ) + 1) * (2 * (Real.exp (x / 8) ^ 2 * 2 ^ k) ^ 2) / T by ring,
    div_le_iff₀ hTp]
  have h1 : ((k : ℝ) + 1) * (2 * (Real.exp (x / 8) ^ 2 * 2 ^ k) ^ 2) ≤ ((k : ℝ) + 1) * (2 * G) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : 40 * (k + 1) * G ≤ H * G := mul_le_mul_of_nonneg_right hH2 hG0.le
  nlinarith

theorem tr_n_final (W k A H e a c : ℝ) (hk : 0 ≤ k) (h1 : (k + 1) * W ≤ 1 / 10)
    (h2 : k * (2 * A) ≤ 1 / 10) (h3 : k * (2 * (2 * H ^ 2)) ≤ 1 / 10) (he : e ≤ 1 / 40)
    (ha : a ≤ 1 / 40) (hc : c ≤ 1 / 40) (ha0 : 0 ≤ a) (hc0 : 0 ≤ c) :
    W + k * (2 * (A + 2 * H ^ 2) + W) < (1 - e) * (1 - a - c) := by
  have e1 : W + k * (2 * (A + 2 * H ^ 2) + W) = (k + 1) * W + k * (2 * A) + k * (2 * (2 * H ^ 2)) := by
    ring
  rw [e1]
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - e - 39 / 40)
    (by linarith : (0:ℝ) ≤ 1 - a - c - 19 / 20)]

theorem tr_num (b0 K1 C : ℝ) (hb0 : 0 < b0) (hK1 : 0 ≤ K1) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (k T : ℕ) (L B S2 : ℝ),
      (k : ℝ) ≤ min (1 / 10) (b0 / (64 * (K1 + 1))) * ((n : ℝ) + 1) →
      Real.sqrt n - 1 ≤ L → L ≤ Real.sqrt n → b0 ≤ B →
      0 ≤ S2 → S2 ≤ 2 * (Real.sqrt n + C) / ((n : ℝ) ^ 4 - 1) →
      Real.exp n - 1 ≤ T →
      Real.exp (k * Real.log (Real.exp (n / 8)) / (((n : ℝ) ^ 4 - 1) * Real.log ((n : ℝ) ^ 4))) - 1 ≤ 1 ∧
      2 * (Real.exp (n / 8) ^ 2 * 2 ^ k) ^ 2 / T +
        k * (2 * (2 * (1 + K1) ^ 2 * Real.exp (-(2 * (1 / L) * Real.log (Real.exp (n / 8))) +
            k * (2 * (1 / L)) * K1 / B) +
          2 * (2 * Real.log (Real.exp (n / 8)) / (((n : ℝ) ^ 4 - 1) * Real.log ((n : ℝ) ^ 4))) ^ 2) +
          2 * (Real.exp (n / 8) ^ 2 * 2 ^ k) ^ 2 / T) <
      (1 - (Real.exp (k * Real.log (Real.exp (n / 8)) / (((n : ℝ) ^ 4 - 1) * Real.log ((n : ℝ) ^ 4))) - 1)) *
        (1 - 4 * (k : ℝ) ^ 2 * S2 - Real.exp (-((1 / L) * Real.log (Real.exp (n / 8))) + k * (1 / L) * K1 / B)) := by
  set R : ℝ := 110592 * (1 + K1) ^ 2 + C + 10000 with hRdef
  refine ⟨⌈R ^ 2⌉₊, fun n hn k T L B S2 hk hL1 hL2 hB hS0 hS2 hT => ?_⟩
  rw [Real.log_exp]
  set x : ℝ := (n : ℝ) with hxdef
  have hR : R ^ 2 ≤ x := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
  have hR0 : 10000 ≤ R := by have := sq_nonneg (1 + K1); linarith
  have hRK : 110592 * (1 + K1) ^ 2 ≤ R := by linarith
  have hRC : C ≤ R := by have := sq_nonneg (1 + K1); linarith
  have hx0 : 0 ≤ x := by positivity
  set s := Real.sqrt x with hsdef
  have hs : R ≤ s := (Real.le_sqrt' (by linarith)).mpr hR
  have hxs : x = s ^ 2 := (Real.sq_sqrt hx0).symm
  have hsx : s ≤ x := by nlinarith
  have hxR : R ≤ x := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hx1 : (0 : ℝ) ≤ x + 1 := by linarith
  have hk10 : (k : ℝ) ≤ (x + 1) / 10 := by
    have := mul_le_mul_of_nonneg_right (min_le_left (1 / 10 : ℝ) (b0 / (64 * (K1 + 1)))) hx1
    linarith
  have hkb : (k : ℝ) ≤ b0 / (64 * (K1 + 1)) * (x + 1) :=
    hk.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hx1)
  have hlg : 1 ≤ Real.log (x ^ 4) := by
    have h4 : x ≤ x ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
    have he : Real.exp 1 ≤ x ^ 4 := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (x ^ 4) := Real.log_le_log (Real.exp_pos 1) he
  obtain ⟨hv0, hv⟩ := tr_n_v x k (Real.log (x ^ 4)) (by linarith) hk0 hk10 hlg
  have he := tr_n_expm1 _ hv0 hv
  have hL0 : 0 < L := by linarith
  have hE1 := tr_n_E1 x s L k K1 B b0 (by linarith) hxs hL0 hL2 hK1 hb0 hB hk0 hkb
  have hc : Real.exp (-((1 / L) * (x / 8)) + k * (1 / L) * K1 / B) ≤ 1 / 40 :=
    (Real.exp_le_exp.mpr hE1).trans (tr_n_tail s (by linarith))
  have hE2 : Real.exp (-(2 * (1 / L) * (x / 8)) + k * (2 * (1 / L)) * K1 / B)
      ≤ Real.exp (-(s / 8)) := by
    apply Real.exp_le_exp.mpr
    have e : -(2 * (1 / L) * (x / 8)) + k * (2 * (1 / L)) * K1 / B
        = 2 * (-((1 / L) * (x / 8)) + k * (1 / L) * K1 / B) := by ring
    rw [e]; linarith
  refine ⟨by linarith, ?_⟩
  exact tr_n_final _ _ _ _ _ _ _ hk0 (tr_n_W x T k (by linarith) hk10 hT)
    (tr_n_Aterm s x k K1 _ (by linarith) (by linarith) hxs hk0 hk10 hK1 (Real.exp_pos _).le hE2)
    (tr_n_eta x k _ (by linarith) hk0 hk10 hlg) he
    (tr_n_S2 x s C k S2 (by linarith) (by positivity) hsx hC (by linarith) hk0 hk10 hS0 hS2)
    hc (mul_nonneg (by positivity) hS0) (Real.exp_pos _).le

theorem tr_n_logle (y t : ℝ) (hy : 0 < y) (h : y ≤ Real.exp t) : Real.log y ≤ t :=
  calc Real.log y ≤ Real.log (Real.exp t) := Real.log_le_log hy h
    _ = t := Real.log_exp t

theorem tr_n_theta : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Real.sqrt n < (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) - 2 * Real.sqrt n * Real.log n := by
  refine ⟨27001 ^ 2, fun n hn => ?_⟩
  set x : ℝ := (n : ℝ) with hxdef
  have hR : (27001 : ℝ) ^ 2 ≤ x := by rw [hxdef]; exact_mod_cast hn
  have hx0 : 0 ≤ x := by positivity
  set s := Real.sqrt x with hsdef
  have hs : (27001 : ℝ) ≤ s := (Real.le_sqrt' (by norm_num)).mpr hR
  have hxs : x = s ^ 2 := (Real.sq_sqrt hx0).symm
  have hE : s ^ 3 / 27000 ≤ Real.exp (s / 10) := by
    have h := tr_n_exp_cube (s / 10) (by linarith)
    have e : (s / 10) ^ 3 / 27 = s ^ 3 / 27000 := by ring
    linarith
  have hs3 : 27001 * s ^ 2 ≤ s ^ 3 := by nlinarith [sq_nonneg s]
  have hs2 : 27001 * s ≤ s ^ 2 := by nlinarith
  have hx1 : x + 1 ≤ Real.exp (s / 10) := by nlinarith
  have hl1 : Real.log (x + 1) ≤ s / 10 := tr_n_logle _ _ (by linarith) hx1
  have hl2 : Real.log x ≤ s / 10 := tr_n_logle _ _ (by nlinarith) (by linarith)
  have hl3 : 2 * s * Real.log x ≤ 2 * s * (s / 10) :=
    mul_le_mul_of_nonneg_left hl2 (by linarith)
  have hlog2 := Real.log_two_gt_d9
  have h4 : x * 0.6931471803 ≤ x * Real.log 2 := mul_le_mul_of_nonneg_left hlog2.le hx0
  nlinarith

/-! ## The sieve framework -/

section Sieve

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- local factor `ψ_{s,p}(t)` -/
noncomputable def tr_psi (p : ι → ℕ) (ρ : ι → κ → ℕ) (i : ι) (s : κ) (t : ℕ) : ℝ :=
  if t % p i = ρ i s then -1 else 1 / ((p i : ℝ) - 1)

/-- local factor attached to an optional label -/
noncomputable def tr_psio (p : ι → ℕ) (ρ : ι → κ → ℕ) (i : ι) (o : Option κ) (t : ℕ) : ℝ :=
  match o with
  | none => 1
  | some s => tr_psi p ρ i s t

/-- local mean of a product of two local factors -/
noncomputable def tr_mean (p : ι → ℕ) (ρ : ι → κ → ℕ) (i : ι) (o o' : Option κ) : ℝ :=
  1 / (p i : ℝ) * ∑ j ∈ range (p i), tr_psio p ρ i o j * tr_psio p ρ i o' j

theorem tr_s_sum_ite (n r : ℕ) (hr : r < n) (A B : ℝ) :
    ∑ j ∈ range n, (if j = r then A else B) = A + (n - 1) * B := by
  have h : ∀ j ∈ range n, (if j = r then A else B) = B + (if j = r then A - B else 0) := by
    intro j _; split_ifs <;> ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq' (range n) r,
    if_pos (Finset.mem_range.2 hr)]
  simp only [sum_const, card_range, nsmul_eq_mul]
  ring

theorem tr_s_sum_ite2 (n r r' : ℕ) (hr : r < n) (hr' : r' < n) (hne : r ≠ r') (A A' B : ℝ) :
    ∑ j ∈ range n, (if j = r then A else if j = r' then A' else B) = A + A' + (n - 2) * B := by
  have h : ∀ j ∈ range n, (if j = r then A else if j = r' then A' else B) =
      B + (if j = r then A - B else 0) + (if j = r' then A' - B else 0) := by
    intro j _
    by_cases h1 : j = r
    · subst h1; simp [hne]
    · have hne' : r' ≠ r := Ne.symm hne
      by_cases h2 : j = r' <;> simp [h1, h2, hne']
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (range n) r, Finset.sum_ite_eq' (range n) r',
    if_pos (Finset.mem_range.2 hr), if_pos (Finset.mem_range.2 hr')]
  simp only [sum_const, card_range, nsmul_eq_mul]
  ring

variable (p : ι → ℕ) (ρ : ι → κ → ℕ)

theorem tr_s_psi_range (i : ι) (s : κ) (j : ℕ) (hj : j < p i) :
    tr_psi p ρ i s j = if j = ρ i s then -1 else 1 / ((p i : ℝ) - 1) := by
  unfold tr_psi; rw [Nat.mod_eq_of_lt hj]

theorem tr_s_mean_none_none (hp : ∀ i, (p i).Prime) (i : ι) : tr_mean p ρ i none none = 1 := by
  unfold tr_mean tr_psio
  have : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
  simp only [mul_one, sum_const, card_range, nsmul_eq_mul]
  field_simp

theorem tr_s_mean_some_none (hp : ∀ i, (p i).Prime) (hρ : ∀ i s, ρ i s < p i) (i : ι) (s : κ) :
    tr_mean p ρ i (some s) none = 0 := by
  unfold tr_mean tr_psio
  simp only [mul_one]
  rw [Finset.sum_congr rfl (fun j hj => tr_s_psi_range p ρ i s j (Finset.mem_range.1 hj)),
    tr_s_sum_ite _ _ (hρ i s)]
  have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
  have : (p i : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem tr_s_mean_none_some (hp : ∀ i, (p i).Prime) (hρ : ∀ i s, ρ i s < p i) (i : ι) (s : κ) :
    tr_mean p ρ i none (some s) = 0 := by
  have := tr_s_mean_some_none p ρ hp hρ i s
  unfold tr_mean at *
  simpa [mul_comm] using this

theorem tr_s_mean_comm (i : ι) (o o' : Option κ) : tr_mean p ρ i o o' = tr_mean p ρ i o' o := by
  unfold tr_mean; simp only [mul_comm (tr_psio p ρ i o _)]

theorem tr_s_mean_same (hp : ∀ i, (p i).Prime) (hρ : ∀ i s, ρ i s < p i) (i : ι) (s : κ) :
    tr_mean p ρ i (some s) (some s) = 1 / ((p i : ℝ) - 1) := by
  unfold tr_mean tr_psio
  have h : ∀ j ∈ range (p i), tr_psi p ρ i s j * tr_psi p ρ i s j =
      if j = ρ i s then 1 else 1 / ((p i : ℝ) - 1) * (1 / ((p i : ℝ) - 1)) := by
    intro j hj
    rw [tr_s_psi_range p ρ i s j (Finset.mem_range.1 hj)]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h, tr_s_sum_ite _ _ (hρ i s)]
  have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
  have : (p i : ℝ) - 1 ≠ 0 := by linarith
  have : (p i : ℝ) ≠ 0 := by linarith
  field_simp
  ring

theorem tr_s_mean_diff (hp : ∀ i, (p i).Prime) (hρ : ∀ i s, ρ i s < p i)
    (hρi : ∀ i, Function.Injective (ρ i)) (i : ι) (s s' : κ) (hss : s ≠ s') :
    tr_mean p ρ i (some s) (some s') = -(1 / ((p i : ℝ) - 1) ^ 2) := by
  unfold tr_mean tr_psio
  have hne : ρ i s ≠ ρ i s' := fun h => hss (hρi i h)
  have h : ∀ j ∈ range (p i), tr_psi p ρ i s j * tr_psi p ρ i s' j =
      if j = ρ i s then -(1 / ((p i : ℝ) - 1)) else
        if j = ρ i s' then -(1 / ((p i : ℝ) - 1)) else 1 / ((p i : ℝ) - 1) * (1 / ((p i : ℝ) - 1)) := by
    intro j hj
    rw [tr_s_psi_range p ρ i s j (Finset.mem_range.1 hj),
      tr_s_psi_range p ρ i s' j (Finset.mem_range.1 hj)]
    by_cases h1 : j = ρ i s
    · have : j ≠ ρ i s' := h1 ▸ hne
      simp [h1, hne]
    · have hne' : ρ i s' ≠ ρ i s := Ne.symm hne
      by_cases h2 : j = ρ i s' <;> simp [h1, h2, hne']
  rw [Finset.sum_congr rfl h, tr_s_sum_ite2 _ _ _ (hρ i s) (hρ i s') hne]
  have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
  have : (p i : ℝ) - 1 ≠ 0 := by linarith
  have : (p i : ℝ) ≠ 0 := by linarith
  field_simp
  ring

theorem tr_s_psi_abs (hp : ∀ i, (p i).Prime) (i : ι) (o : Option κ) (t : ℕ) :
    |tr_psio p ρ i o t| ≤ 1 := by
  have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
  cases o with
  | none => simp [tr_psio]
  | some s =>
    simp only [tr_psio, tr_psi]
    split_ifs
    · simp
    · rw [abs_of_nonneg (by have : 0 < (p i : ℝ) - 1 := by linarith
                            positivity)]
      rw [div_le_one (by linarith)]; linarith

theorem tr_s_psio_mod (i : ι) (o : Option κ) (t : ℕ) :
    tr_psio p ρ i o (t % p i) = tr_psio p ρ i o t := by
  cases o with
  | none => rfl
  | some s => simp only [tr_psio, tr_psi, Nat.mod_mod]

/-! ### labelled prime sets -/

/-- `∏_{i labelled} p_i` -/
noncomputable def tr_N (f : ι → Option κ) : ℝ := ∏ i, (if f i = none then 1 else (p i : ℝ))

/-- `1/φ` of the labelled product -/
noncomputable def tr_W (f : ι → Option κ) : ℝ :=
  ∏ i, (if f i = none then 1 else 1 / ((p i : ℝ) - 1))

/-- primes carrying label `s` -/
def tr_r (f : ι → Option κ) (s : κ) : Finset ι := univ.filter (fun i => f i = some s)

/-- the product of local factors -/
noncomputable def tr_Psi (f : ι → Option κ) (t : ℕ) : ℝ := ∏ i, tr_psio p ρ i (f i) t

/-- the Gram matrix -/
noncomputable def tr_M (f g : ι → Option κ) : ℝ := ∏ i, tr_mean p ρ i (f i) (g i)

omit [DecidableEq κ] in
theorem tr_s_prod_fiber [DecidableEq κ] (h : ι → ℝ) (f : ι → Option κ) :
    ∏ s, ∏ i ∈ tr_r f s, h i = ∏ i, (if f i = none then 1 else h i) := by
  unfold tr_r
  simp_rw [Finset.prod_filter]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases hfi : f i with
  | none => simp
  | some s0 => simp [Finset.prod_ite_eq']

theorem tr_s_N_nonneg (f : ι → Option κ) : 0 ≤ tr_N p f := by
  unfold tr_N; exact Finset.prod_nonneg (fun i _ => by split_ifs <;> positivity)

theorem tr_s_N_ge_one (hp : ∀ i, (p i).Prime) (f : ι → Option κ) : 1 ≤ tr_N p f := by
  unfold tr_N
  calc (1 : ℝ) = ∏ _i : ι, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => by
      split_ifs
      · exact le_refl _
      · exact_mod_cast (hp i).one_lt.le)

theorem tr_s_W_nonneg (hp : ∀ i, (p i).Prime) (f : ι → Option κ) : 0 ≤ tr_W p f := by
  unfold tr_W
  refine Finset.prod_nonneg (fun i _ => ?_)
  have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
  split_ifs
  · norm_num
  · have : 0 < (p i : ℝ) - 1 := by linarith
    positivity

theorem tr_s_avg_pair (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (f g : ι → Option κ) (T : ℕ) :
    |∑ t ∈ range T, tr_Psi p ρ f (t + 1) * tr_Psi p ρ g (t + 1) - T * tr_M p ρ f g|
      ≤ 2 * (tr_N p f * tr_N p g) := by
  classical
  set U := univ.filter (fun i => f i ≠ none ∨ g i ≠ none) with hU
  have hPsi : ∀ t, tr_Psi p ρ f t * tr_Psi p ρ g t =
      ∏ i ∈ U, (tr_psio p ρ i (f i) (t % p i) * tr_psio p ρ i (g i) (t % p i)) := by
    intro t
    unfold tr_Psi
    rw [← Finset.prod_mul_distrib, hU]
    rw [Finset.prod_filter_of_ne]
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [tr_s_psio_mod, tr_s_psio_mod]
    · intro i _ hne
      by_contra hc
      push Not at hc
      apply hne
      rw [hc.1, hc.2]; simp [tr_psio]
  have hM : tr_M p ρ f g = ∏ i ∈ U, ((1 : ℝ) / p i *
      ∑ j ∈ range (p i), tr_psio p ρ i (f i) j * tr_psio p ρ i (g i) j) := by
    unfold tr_M
    rw [hU, Finset.prod_filter_of_ne]
    · rfl
    · intro i _ hne
      by_contra hc
      push Not at hc
      apply hne
      rw [hc.1, hc.2]; exact tr_s_mean_none_none p ρ hp i
  have hbd : ∀ i j, |tr_psio p ρ i (f i) j * tr_psio p ρ i (g i) j| ≤ 1 := by
    intro i j
    rw [abs_mul]
    exact mul_le_one₀ (tr_s_psi_abs p ρ hp i _ _) (abs_nonneg _) (tr_s_psi_abs p ρ hp i _ _)
  have key := tr_crt_avg p hp hinj U (fun i j => tr_psio p ρ i (f i) j * tr_psio p ρ i (g i) j)
    hbd T
  rw [hM]
  simp_rw [hPsi]
  refine le_trans key ?_
  have hUle : ∏ i ∈ U, (p i : ℝ) ≤ tr_N p f * tr_N p g := by
    unfold tr_N
    rw [← Finset.prod_mul_distrib, hU, Finset.prod_filter]
    refine Finset.prod_le_prod (fun i _ => by split_ifs <;> positivity) (fun i _ => ?_)
    have h1 : (1 : ℝ) ≤ p i := by exact_mod_cast (hp i).one_lt.le
    by_cases hf : f i = none <;> by_cases hg : g i = none <;> simp [hf, hg] <;> nlinarith
  linarith

theorem tr_s_avg_quad (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (c : (ι → Option κ) → ℝ) (T : ℕ) :
    |∑ t ∈ range T, (∑ f, c f * tr_Psi p ρ f (t + 1)) ^ 2
      - T * ∑ f, ∑ g, c f * c g * tr_M p ρ f g| ≤ 2 * (∑ f, |c f| * tr_N p f) ^ 2 := by
  have hexp : ∀ t, (∑ f, c f * tr_Psi p ρ f (t + 1)) ^ 2 =
      ∑ f, ∑ g, c f * c g * (tr_Psi p ρ f (t + 1) * tr_Psi p ρ g (t + 1)) := by
    intro t
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl (fun g _ => by ring))
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have h2 : ∀ f, ∑ t ∈ range T, ∑ g, c f * c g * (tr_Psi p ρ f (t + 1) * tr_Psi p ρ g (t + 1))
      = ∑ g, c f * c g * ∑ t ∈ range T, (tr_Psi p ρ f (t + 1) * tr_Psi p ρ g (t + 1)) := by
    intro f
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun g _ => by rw [Finset.mul_sum])
  simp_rw [h2]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have h3 : ∀ f, ∑ g, c f * c g * ∑ t ∈ range T, (tr_Psi p ρ f (t + 1) * tr_Psi p ρ g (t + 1))
      - T * ∑ g, c f * c g * tr_M p ρ f g = ∑ g, c f * c g *
        (∑ t ∈ range T, (tr_Psi p ρ f (t + 1) * tr_Psi p ρ g (t + 1)) - T * tr_M p ρ f g) := by
    intro f
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun g _ => by ring)
  simp_rw [h3]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have h4 : ∀ f, |∑ g, c f * c g *
        (∑ t ∈ range T, (tr_Psi p ρ f (t + 1) * tr_Psi p ρ g (t + 1)) - T * tr_M p ρ f g)|
      ≤ ∑ g, 2 * ((|c f| * tr_N p f) * (|c g| * tr_N p g)) := by
    intro f
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun g _ => ?_))
    rw [abs_mul, abs_mul]
    have := tr_s_avg_pair p ρ hp hinj f g T
    have hf := tr_s_N_nonneg p f
    have hg := tr_s_N_nonneg p g
    calc |c f| * |c g| * |∑ t ∈ range T, tr_Psi p ρ f (t + 1) * tr_Psi p ρ g (t + 1)
          - T * tr_M p ρ f g| ≤ |c f| * |c g| * (2 * (tr_N p f * tr_N p g)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  refine le_trans (Finset.sum_le_sum (fun f _ => h4 f)) (le_of_eq ?_)
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun f _ => by rw [Finset.mul_sum])

theorem tr_s_M_self (hp : ∀ i, (p i).Prime) (hρ : ∀ i s, ρ i s < p i) (f : ι → Option κ) :
    tr_M p ρ f f = tr_W p f := by
  unfold tr_M tr_W
  refine Finset.prod_congr rfl (fun i _ => ?_)
  cases f i with
  | none => simp [tr_s_mean_none_none p ρ hp]
  | some s => simp [tr_s_mean_same p ρ hp hρ]

theorem tr_s_M_comm (f g : ι → Option κ) : tr_M p ρ f g = tr_M p ρ g f := by
  unfold tr_M
  exact Finset.prod_congr rfl (fun i _ => tr_s_mean_comm p ρ i _ _)

theorem tr_s_rowsum (hp : ∀ i, (p i).Prime) (hρ : ∀ i s, ρ i s < p i)
    (hρi : ∀ i, Function.Injective (ρ i)) (f : ι → Option κ) :
    ∑ g, |tr_M p ρ f g| = tr_W p f *
      ∏ i, (if f i = none then 1 else 1 + ((Fintype.card κ : ℝ) - 1) / ((p i : ℝ) - 1)) := by
  unfold tr_M tr_W
  simp_rw [Finset.abs_prod]
  rw [← Fintype.prod_sum (fun i o => |tr_mean p ρ i (f i) o|), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_option]
  have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
  cases hfi : f i with
  | none =>
    simp [tr_s_mean_none_none p ρ hp, tr_s_mean_none_some p ρ hp hρ]
  | some s0 =>
    simp only [tr_s_mean_some_none p ρ hp hρ, abs_zero, zero_add, reduceCtorEq, if_false]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s0), tr_s_mean_same p ρ hp hρ]
    have hrest : ∑ x ∈ univ.erase s0, |tr_mean p ρ i (some s0) (some x)| =
        ∑ x ∈ univ.erase s0, 1 / ((p i : ℝ) - 1) ^ 2 := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [tr_s_mean_diff p ρ hp hρ hρi i s0 x (Ne.symm (Finset.ne_of_mem_erase hx)), abs_neg,
        abs_of_nonneg (by positivity)]
    rw [hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), nsmul_eq_mul,
      Finset.card_univ]
    have hk : 1 ≤ Fintype.card κ := Fintype.card_pos_iff.2 ⟨s0⟩
    rw [Nat.cast_sub hk]
    have : 0 < (p i : ℝ) - 1 := by linarith
    rw [abs_of_pos (by positivity)]
    field_simp
    ring

theorem tr_s_gram (hp : ∀ i, (p i).Prime) (hρ : ∀ i s, ρ i s < p i)
    (c : (ι → Option κ) → ℝ) :
    |∑ f, ∑ g, c f * c g * tr_M p ρ f g - ∑ f, c f ^ 2 * tr_W p f|
      ≤ ∑ f, c f ^ 2 * (∑ g, |tr_M p ρ f g| - tr_W p f) := by
  classical
  set E : (ι → Option κ) → (ι → Option κ) → ℝ :=
    fun f g => tr_M p ρ f g - if f = g then tr_W p f else 0 with hE
  have hsplit : ∑ f, ∑ g, c f * c g * tr_M p ρ f g - ∑ f, c f ^ 2 * tr_W p f =
      ∑ f, ∑ g, c f * c g * E f g := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    simp only [hE, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    ring
  have hEsymm : ∀ f g, |E f g| = |E g f| := by
    intro f g
    simp only [hE]
    by_cases h : f = g
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), tr_s_M_comm]
  have hErow : ∀ f, ∑ g, |E f g| = ∑ g, |tr_M p ρ f g| - tr_W p f := by
    intro f
    have hpt : ∀ g, |E f g| = |tr_M p ρ f g| - if f = g then tr_W p f else 0 := by
      intro g
      simp only [hE]
      by_cases h : f = g
      · subst h
        simp only [if_true, tr_s_M_self p ρ hp hρ, sub_self, abs_zero,
          abs_of_nonneg (tr_s_W_nonneg p hp f)]
      · rw [if_neg h, sub_zero, sub_zero]
    simp_rw [hpt]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  rw [hsplit]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hb : ∀ f g, |c f * c g * E f g| ≤ (c f ^ 2 * |E f g| + c g ^ 2 * |E g f|) / 2 := by
    intro f g
    rw [abs_mul, abs_mul, hEsymm g f]
    have h1 : |c f| * |c g| ≤ (c f ^ 2 + c g ^ 2) / 2 := by
      have := sq_nonneg (|c f| - |c g|)
      have h3 : |c f| ^ 2 = c f ^ 2 := sq_abs _
      have h4 : |c g| ^ 2 = c g ^ 2 := sq_abs _
      nlinarith
    have := mul_le_mul_of_nonneg_right h1 (abs_nonneg (E f g))
    linarith
  calc ∑ f, |∑ g, c f * c g * E f g| ≤ ∑ f, ∑ g, |c f * c g * E f g| :=
        Finset.sum_le_sum (fun f _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ f, ∑ g, (c f ^ 2 * |E f g| + c g ^ 2 * |E g f|) / 2 :=
        Finset.sum_le_sum (fun f _ => Finset.sum_le_sum (fun g _ => hb f g))
    _ = (∑ f, ∑ g, c f ^ 2 * |E f g| + ∑ f, ∑ g, c g ^ 2 * |E g f|) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ f, ∑ g, c f ^ 2 * |E f g| := by
        rw [Finset.sum_comm (f := fun f g => c g ^ 2 * |E g f|)]
        ring
    _ = ∑ f, c f ^ 2 * (∑ g, |tr_M p ρ f g| - tr_W p f) := by
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [← hErow, Finset.mul_sum]

end Sieve

/-! ### coefficient facts -/

section Coef

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)

theorem tr_s_prodP_empty : tr_prodP p ∅ = 1 := by simp [tr_prodP]

theorem tr_s_phiInv_empty : tr_phiInv p ∅ = 1 := by simp [tr_phiInv]

theorem tr_s_a_empty : tr_a p ∅ = 1 := by simp [tr_a]

theorem tr_s_prodP_ge_mem (hp : ∀ i, (p i).Prime) (T : Finset ι) (i : ι) (hi : i ∈ T) :
    (p i : ℝ) ≤ tr_prodP p T := by
  unfold tr_prodP
  rw [← Finset.mul_prod_erase T _ hi]
  have h1 : (1 : ℝ) ≤ ∏ j ∈ T.erase i, (p j : ℝ) := by
    calc (1 : ℝ) = ∏ j ∈ T.erase i, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => by
          exact_mod_cast (hp j).one_lt.le)
  have h2 : (0 : ℝ) ≤ p i := by positivity
  nlinarith

theorem tr_s_prodP_ge_one (hp : ∀ i, (p i).Prime) (T : Finset ι) : 1 ≤ tr_prodP p T := by
  unfold tr_prodP
  calc (1 : ℝ) = ∏ j ∈ T, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => by
        exact_mod_cast (hp j).one_lt.le)

theorem tr_s_phiInv_nonneg (hp : ∀ i, (p i).Prime) (T : Finset ι) : 0 ≤ tr_phiInv p T := by
  unfold tr_phiInv
  refine Finset.prod_nonneg (fun i _ => ?_)
  have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
  have : 0 < (p i : ℝ) - 1 := by linarith
  positivity

theorem tr_s_phiInv_le_one (hp : ∀ i, (p i).Prime) (T : Finset ι) : tr_phiInv p T ≤ 1 := by
  unfold tr_phiInv
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
  · have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
    have : 0 < (p i : ℝ) - 1 := by linarith
    positivity
  · have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
    rw [div_le_one (by linarith)]; linarith

theorem tr_s_inv_prodP_le (hp : ∀ i, (p i).Prime) (T : Finset ι) :
    1 / tr_prodP p T ≤ tr_phiInv p T := by
  unfold tr_prodP tr_phiInv
  rw [one_div, ← Finset.prod_inv_distrib]
  refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => ?_)
  have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
  rw [one_div]
  exact inv_anti₀ (by linarith) (by linarith)

variable {z : ℝ}

theorem tr_s_log_prodP (hp : ∀ i, (p i).Prime) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (T : Finset ι) (hT : T ≠ ∅) : Real.log z ≤ Real.log (tr_prodP p T) := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hT
  exact Real.log_le_log (by linarith) ((hpz i).le.trans (tr_s_prodP_ge_mem p hp T i hi))

theorem tr_s_B_pos (hz : 1 < z) (hB : 1 ≤ tr_B p * Real.log z) : 0 < tr_B p := by
  have hl : 0 < Real.log z := Real.log_pos hz
  by_contra h
  push Not at h
  nlinarith

theorem tr_s_a_abs (hp : ∀ i, (p i).Prime) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (T : Finset ι) (hT : T ≠ ∅) :
    |tr_a p T| = 1 / (tr_B p * Real.log (tr_prodP p T)) := by
  have hBp := tr_s_B_pos p hz hB
  have hl := tr_s_log_prodP p hp hz hpz T hT
  have hl0 : 0 < Real.log z := Real.log_pos hz
  unfold tr_a
  rw [if_neg hT, neg_div, abs_neg, abs_of_pos (by apply div_pos one_pos; nlinarith)]

theorem tr_s_a_abs_log (hp : ∀ i, (p i).Prime) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (T : Finset ι) (hT : T ≠ ∅) :
    |tr_a p T| * Real.log (tr_prodP p T) = 1 / tr_B p := by
  have hBp := tr_s_B_pos p hz hB
  have hl := tr_s_log_prodP p hp hz hpz T hT
  have hl0 : 0 < Real.log z := Real.log_pos hz
  rw [tr_s_a_abs p hp hz hpz hB T hT]
  have : Real.log (tr_prodP p T) ≠ 0 := by linarith
  field_simp

theorem tr_s_a_abs_le_one (hp : ∀ i, (p i).Prime) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (T : Finset ι) : |tr_a p T| ≤ 1 := by
  by_cases hT : T = ∅
  · subst hT; simp [tr_s_a_empty]
  have hBp := tr_s_B_pos p hz hB
  have hl := tr_s_log_prodP p hp hz hpz T hT
  rw [tr_s_a_abs p hp hz hpz hB T hT, div_le_one (by nlinarith [Real.log_pos hz])]
  nlinarith

theorem tr_s_sum_ne (F : Finset ι → ℝ) :
    ∑ T, F T = F ∅ + ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅), F T := by
  rw [Finset.filter_ne', Finset.add_sum_erase _ _ (Finset.mem_univ _)]

theorem tr_s_sum_abs_a (hp : ∀ i, (p i).Prime) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) :
    ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅), |tr_a p T| * tr_phiInv p T = 1 := by
  have hBp := tr_s_B_pos p hz hB
  have h : ∀ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
      |tr_a p T| * tr_phiInv p T = (1 / tr_B p) * (tr_phiInv p T / Real.log (tr_prodP p T)) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    rw [tr_s_a_abs p hp hz hpz hB T hT.2]
    have hl := tr_s_log_prodP p hp hz hpz T hT.2
    have hl0 : 0 < Real.log z := Real.log_pos hz
    have : Real.log (tr_prodP p T) ≠ 0 := by linarith
    field_simp
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  change 1 / tr_B p * tr_B p = 1
  field_simp

theorem tr_s_sum_a_phi (hp : ∀ i, (p i).Prime) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) :
    ∑ T, tr_a p T * tr_phiInv p T = 0 := by
  rw [tr_s_sum_ne]
  have h : ∀ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
      tr_a p T * tr_phiInv p T = -(|tr_a p T| * tr_phiInv p T) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    have hBp := tr_s_B_pos p hz hB
    have hl := tr_s_log_prodP p hp hz hpz T hT.2
    have hl0 : 0 < Real.log z := Real.log_pos hz
    have hneg : tr_a p T < 0 := by
      unfold tr_a; rw [if_neg hT.2]
      apply div_neg_of_neg_of_pos (by norm_num); nlinarith
    rw [abs_of_neg hneg]; ring
  rw [Finset.sum_congr rfl h, Finset.sum_neg_distrib, tr_s_sum_abs_a p hp hz hpz hB,
    tr_s_a_empty, tr_s_phiInv_empty]
  ring

theorem tr_s_sum_abs_a_all (hp : ∀ i, (p i).Prime) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) :
    ∑ T, |tr_a p T| * tr_phiInv p T = 2 := by
  rw [tr_s_sum_ne, tr_s_sum_abs_a p hp hz hpz hB, tr_s_a_empty, tr_s_phiInv_empty]
  norm_num

/-- the paper's (4.7) -/
theorem tr_s_star (hp : ∀ i, (p i).Prime) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (i : ι) :
    ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => i ∈ T), |tr_a p T| * tr_phiInv p T
      ≤ 2 / ((p i : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
  have hpi : 0 < (p i : ℝ) - 1 := by linarith
  have hBp := tr_s_B_pos p hz hB
  have hl0 : 0 < Real.log z := Real.log_pos hz
  have hlz : Real.log z ≤ Real.log (p i) := Real.log_le_log (by linarith) (hpz i).le
  set F : Finset ι → ℝ := fun T => |tr_a p T| * tr_phiInv p T with hF
  have hFn : ∀ T, 0 ≤ F T := fun T => mul_nonneg (abs_nonneg _) (tr_s_phiInv_nonneg p hp T)
  have hterm : ∀ T ∈ (univ : Finset (Finset ι)).filter (fun T => i ∈ T),
      |tr_a p T| * tr_phiInv p T ≤ 1 / ((p i : ℝ) - 1) * F (T.erase i) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    have hphi : tr_phiInv p T = 1 / ((p i : ℝ) - 1) * tr_phiInv p (T.erase i) := by
      unfold tr_phiInv; exact (Finset.mul_prod_erase T (fun j => 1 / ((p j : ℝ) - 1)) hT.2).symm
    have hprod : tr_prodP p T = (p i : ℝ) * tr_prodP p (T.erase i) := by
      unfold tr_prodP; exact (Finset.mul_prod_erase T (fun j => (p j : ℝ)) hT.2).symm
    have hTne : T ≠ ∅ := Finset.ne_empty_of_mem hT.2
    have hφ := tr_s_phiInv_nonneg p hp (T.erase i)
    have hge := tr_s_prodP_ge_one p hp (T.erase i)
    have haT : |tr_a p T| ≤ |tr_a p (T.erase i)| := by
      rw [tr_s_a_abs p hp hz hpz hB T hTne, hprod]
      by_cases he : T.erase i = ∅
      · rw [he, tr_s_a_empty, abs_one, tr_s_prodP_empty, mul_one,
          div_le_one (by nlinarith)]
        nlinarith
      · rw [tr_s_a_abs p hp hz hpz hB _ he]
        have hl := tr_s_log_prodP p hp hz hpz _ he
        have hmono : Real.log (tr_prodP p (T.erase i)) ≤
            Real.log ((p i : ℝ) * tr_prodP p (T.erase i)) :=
          Real.log_le_log (by linarith) (by nlinarith)
        apply one_div_le_one_div_of_le (by nlinarith)
        nlinarith
    rw [hphi, hF]
    have := mul_le_mul_of_nonneg_right haT hφ
    have h1p : 0 ≤ 1 / ((p i : ℝ) - 1) := by positivity
    calc |tr_a p T| * (1 / ((p i : ℝ) - 1) * tr_phiInv p (T.erase i))
        = 1 / ((p i : ℝ) - 1) * (|tr_a p T| * tr_phiInv p (T.erase i)) := by ring
      _ ≤ 1 / ((p i : ℝ) - 1) * (|tr_a p (T.erase i)| * tr_phiInv p (T.erase i)) :=
        mul_le_mul_of_nonneg_left this h1p
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hinj : Set.InjOn (fun T => T.erase i)
      (((univ : Finset (Finset ι)).filter (fun T => i ∈ T)) : Set (Finset ι)) := by
    intro T1 h1 T2 h2 heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at h1 h2
    have := congrArg (insert i) heq
    simp only [Finset.insert_erase h1, Finset.insert_erase h2] at this
    exact this
  rw [← Finset.sum_image (f := F) hinj]
  have hle : ∑ T ∈ ((univ : Finset (Finset ι)).filter (fun T => i ∈ T)).image
      (fun T => T.erase i), F T ≤ ∑ T, F T := Finset.sum_le_univ_sum_of_nonneg hFn
  have htot : ∑ T, F T = 2 := tr_s_sum_abs_a_all p hp hz hpz hB
  rw [htot] at hle
  calc 1 / ((p i : ℝ) - 1) * _ ≤ 1 / ((p i : ℝ) - 1) * 2 :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 2 / ((p i : ℝ) - 1) := by ring

theorem tr_s_rpow_sub_one (d γ : ℝ) (hd : 1 ≤ d) (hγ : 0 ≤ γ) :
    d ^ γ - 1 ≤ γ * Real.log d * d ^ γ := by
  have hd0 : 0 < d := by linarith
  rw [Real.rpow_def_of_pos hd0]
  set v := Real.log d * γ
  have hv : 0 ≤ v := mul_nonneg (Real.log_nonneg hd) hγ
  have h1 := Real.add_one_le_exp (-v)
  have h2 : Real.exp (-v) * Real.exp v = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp v := Real.exp_pos v
  have : γ * Real.log d = v := by ring
  rw [this]
  nlinarith

theorem tr_s_A_ge_one (hp : ∀ i, (p i).Prime) : 1 ≤ ∑ T, tr_a p T ^ 2 * tr_phiInv p T := by
  rw [tr_s_sum_ne, tr_s_a_empty, tr_s_phiInv_empty]
  have : 0 ≤ ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
      tr_a p T ^ 2 * tr_phiInv p T :=
    Finset.sum_nonneg (fun T _ => mul_nonneg (sq_nonneg _) (tr_s_phiInv_nonneg p hp T))
  linarith

/-- `A_γ ≤ A (1 + γ K1 / B)` -/
theorem tr_s_Agamma (hp : ∀ i, (p i).Prime) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (K1 γ : ℝ) (hγ : 0 ≤ γ) (hK1 : 0 ≤ K1)
    (hK : ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
        |tr_a p T| * tr_prodP p T ^ γ * tr_phiInv p T ≤ K1) :
    ∑ T, tr_a p T ^ 2 * tr_phiInv p T * tr_prodP p T ^ γ ≤
      (∑ T, tr_a p T ^ 2 * tr_phiInv p T) * (1 + γ * K1 / tr_B p) := by
  have hBp := tr_s_B_pos p hz hB
  have hA1 := tr_s_A_ge_one p hp
  have hdiff : ∑ T, tr_a p T ^ 2 * tr_phiInv p T * tr_prodP p T ^ γ
      - ∑ T, tr_a p T ^ 2 * tr_phiInv p T ≤ γ * K1 / tr_B p := by
    rw [← Finset.sum_sub_distrib, tr_s_sum_ne]
    simp only [tr_s_prodP_empty, Real.one_rpow, mul_one, sub_self, zero_add]
    have hterm : ∀ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
        tr_a p T ^ 2 * tr_phiInv p T * tr_prodP p T ^ γ - tr_a p T ^ 2 * tr_phiInv p T ≤
          (γ / tr_B p) * (|tr_a p T| * tr_prodP p T ^ γ * tr_phiInv p T) := by
      intro T hT
      rw [Finset.mem_filter] at hT
      have hal := tr_s_a_abs_log p hp hz hpz hB T hT.2
      have hd1 := tr_s_prodP_ge_one p hp T
      have hrp := tr_s_rpow_sub_one (tr_prodP p T) γ hd1 hγ
      have hφ := tr_s_phiInv_nonneg p hp T
      have hsq : tr_a p T ^ 2 = |tr_a p T| * |tr_a p T| := by rw [← sq_abs, sq]
      have e1 : tr_a p T ^ 2 * tr_phiInv p T * tr_prodP p T ^ γ - tr_a p T ^ 2 * tr_phiInv p T
          = tr_a p T ^ 2 * tr_phiInv p T * (tr_prodP p T ^ γ - 1) := by ring
      rw [e1]
      have hnn : 0 ≤ tr_a p T ^ 2 * tr_phiInv p T := mul_nonneg (sq_nonneg _) hφ
      calc tr_a p T ^ 2 * tr_phiInv p T * (tr_prodP p T ^ γ - 1)
          ≤ tr_a p T ^ 2 * tr_phiInv p T * (γ * Real.log (tr_prodP p T) * tr_prodP p T ^ γ) :=
            mul_le_mul_of_nonneg_left hrp hnn
        _ = γ * (|tr_a p T| * Real.log (tr_prodP p T)) *
              (|tr_a p T| * tr_prodP p T ^ γ * tr_phiInv p T) := by rw [hsq]; ring
        _ = _ := by rw [hal]; ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have : 0 ≤ γ / tr_B p := by positivity
    calc γ / tr_B p * _ ≤ γ / tr_B p * K1 := mul_le_mul_of_nonneg_left hK this
      _ = _ := by ring
  have : 0 ≤ γ * K1 / tr_B p := by positivity
  nlinarith

end Coef

/-! ### labelled sets versus tuples of sets -/

section Tuples

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (p : ι → ℕ)

theorem tr_s_N_eq (f : ι → Option κ) : tr_N p f = ∏ s, tr_prodP p (tr_r f s) := by
  unfold tr_N tr_prodP; rw [tr_s_prod_fiber]

theorem tr_s_W_eq (f : ι → Option κ) : tr_W p f = ∏ s, tr_phiInv p (tr_r f s) := by
  unfold tr_W tr_phiInv; rw [tr_s_prod_fiber]

omit [Fintype κ] in
theorem tr_s_mem_r (f : ι → Option κ) (s : κ) (i : ι) : i ∈ tr_r f s ↔ f i = some s := by
  simp [tr_r]

theorem tr_s_rr_inj : Function.Injective (fun (f : ι → Option κ) => fun s => tr_r f s) := by
  intro f g hfg
  funext i
  have h : ∀ s, (i ∈ tr_r f s ↔ i ∈ tr_r g s) := fun s => by
    have := congrFun hfg s
    simp only at this
    rw [this]
  cases hf : f i with
  | none =>
    cases hg : g i with
    | none => rfl
    | some s =>
      have := (h s).2 ((tr_s_mem_r g s i).2 hg)
      rw [tr_s_mem_r, hf] at this
      exact absurd this (by simp)
  | some s =>
    have := (h s).1 ((tr_s_mem_r f s i).2 hf)
    rw [tr_s_mem_r] at this
    exact this.symm

theorem tr_s_sum_inj (h : (κ → Finset ι) → ℝ) (hh : ∀ F, 0 ≤ h F) :
    ∑ f : ι → Option κ, h (fun s => tr_r f s) ≤ ∑ F, h F := by
  rw [← Finset.sum_image (f := h) (fun f _ g _ hfg => tr_s_rr_inj hfg)]
  exact Finset.sum_le_univ_sum_of_nonneg hh

/-- every pairwise disjoint family comes from a labelling -/
theorem tr_s_mem_image (F : κ → Finset ι)
    (hF : ∀ i s s', s ≠ s' → ¬ (i ∈ F s ∧ i ∈ F s')) :
    F ∈ (univ : Finset (ι → Option κ)).image (fun f => fun s => tr_r f s) := by
  classical
  rw [Finset.mem_image]
  refine ⟨fun i => if h : ∃ s, i ∈ F s then some h.choose else none, Finset.mem_univ _, ?_⟩
  funext s
  ext i
  rw [tr_s_mem_r]
  constructor
  · intro hi
    by_cases h : ∃ s, i ∈ F s
    · simp only [h, dif_pos, Option.some.injEq] at hi
      rw [← hi]; exact h.choose_spec
    · simp only [h, dif_neg, not_false_eq_true, reduceCtorEq] at hi
  · intro hi
    have h : ∃ s, i ∈ F s := ⟨s, hi⟩
    simp only [h, dif_pos, Option.some.injEq]
    by_contra hne
    exact hF i _ _ hne ⟨h.choose_spec, hi⟩

theorem tr_s_sum_surj (h : (κ → Finset ι) → ℝ) (hh : ∀ F, 0 ≤ h F) :
    ∑ F, h F ≤ ∑ f : ι → Option κ, h (fun s => tr_r f s) +
      ∑ s, ∑ s', ∑ i, (if s ≠ s' then
        ∑ F, (if i ∈ F s ∧ i ∈ F s' then h F else 0) else 0) := by
  classical
  set Im := (univ : Finset (ι → Option κ)).image (fun f => fun s => tr_r f s) with hIm
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun F => F ∈ Im)]
  have h1 : ∑ F ∈ univ.filter (fun F => F ∈ Im), h F = ∑ f : ι → Option κ, h (fun s => tr_r f s) := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hIm,
      Finset.sum_image (f := h) (fun f _ g _ hfg => tr_s_rr_inj hfg)]
  rw [h1]
  refine add_le_add_right ?_ (∑ f : ι → Option κ, h (fun s => tr_r f s))
  set Bad : (κ → Finset ι) → ℝ := fun F => ∑ s, ∑ s', ∑ i, (if s ≠ s' then
      (if i ∈ F s ∧ i ∈ F s' then h F else 0) else 0) with hBad
  have hBadnn : ∀ F, 0 ≤ Bad F := fun F => Finset.sum_nonneg (fun s _ => Finset.sum_nonneg
    (fun s' _ => Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hh F | exact le_refl _)))
  have hpt : ∀ F ∈ univ.filter (fun F => F ∉ Im), h F ≤ Bad F := by
    intro F hF
    rw [Finset.mem_filter] at hF
    have : ∃ i s s', s ≠ s' ∧ (i ∈ F s ∧ i ∈ F s') := by
      by_contra hc
      push Not at hc
      exact hF.2 (tr_s_mem_image F (fun i s s' hss h2 => by
        have := hc i s s' hss h2.1; exact this h2.2))
    obtain ⟨i, s, s', hss, hi⟩ := this
    have e : h F = (if s ≠ s' then (if i ∈ F s ∧ i ∈ F s' then h F else 0) else 0) := by
      rw [if_pos hss, if_pos hi]
    rw [e, hBad]
    refine le_trans ?_ (Finset.single_le_sum (fun s _ => Finset.sum_nonneg (fun s' _ =>
      Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hh F | exact le_refl _)))
      (Finset.mem_univ s))
    refine le_trans ?_ (Finset.single_le_sum (fun s' _ =>
      Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hh F | exact le_refl _))
      (Finset.mem_univ s'))
    exact Finset.single_le_sum (f := fun i => if s ≠ s' then (if i ∈ F s ∧ i ∈ F s' then h F
      else 0) else 0) (fun i _ => by split_ifs <;> first | exact hh F | exact le_refl _)
      (Finset.mem_univ i)
  refine le_trans (Finset.sum_le_sum hpt) ?_
  refine le_trans (Finset.sum_le_univ_sum_of_nonneg hBadnn) (le_of_eq ?_)
  rw [hBad, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s' _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> simp

/-- the doubly-occupied mass of a product weight -/
theorem tr_s_pair_mass (g : Finset ι → ℝ) (hg : ∀ T, 0 ≤ g T) (hA : 1 ≤ ∑ T, g T)
    (s s' : κ) (hss : s ≠ s') (i : ι) :
    ∑ F : κ → Finset ι, (if i ∈ F s ∧ i ∈ F s' then ∏ s'', g (F s'') else 0) ≤
      (∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => i ∈ T), g T) ^ 2 *
        (∑ T, g T) ^ Fintype.card κ := by
  classical
  set G : κ → Finset ι → ℝ := fun s'' T =>
    if s'' = s ∨ s'' = s' then (if i ∈ T then g T else 0) else g T with hG
  have hpt : ∀ F : κ → Finset ι, (if i ∈ F s ∧ i ∈ F s' then ∏ s'', g (F s'') else 0) =
      ∏ s'', G s'' (F s'') := by
    intro F
    by_cases hc : i ∈ F s ∧ i ∈ F s'
    · rw [if_pos hc]
      refine Finset.prod_congr rfl (fun s'' _ => ?_)
      simp only [hG]
      split_ifs with h1 h2
      · rfl
      · rcases h1 with h1 | h1 <;> subst h1
        · exact absurd hc.1 h2
        · exact absurd hc.2 h2
      · rfl
    · rw [if_neg hc]
      symm
      rw [not_and_or] at hc
      rcases hc with hc | hc
      · exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hG, hc])
      · exact Finset.prod_eq_zero (Finset.mem_univ s') (by simp [hG, hc])
  simp_rw [hpt]
  rw [← Fintype.prod_sum (fun s'' T => G s'' T)]
  set σ := ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => i ∈ T), g T
  set A := ∑ T, g T
  have hσ : ∀ s'', (s'' = s ∨ s'' = s') → ∑ T, G s'' T = σ := by
    intro s'' h
    simp only [hG, if_pos h]
    rw [← Finset.sum_filter]
  have hA' : ∀ s'', ¬ (s'' = s ∨ s'' = s') → ∑ T, G s'' T = A := by
    intro s'' h
    simp only [hG, if_neg h]
    rfl
  have hσ0 : 0 ≤ σ := Finset.sum_nonneg (fun T _ => hg T)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s),
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hss, Finset.mem_univ s'⟩),
    hσ s (Or.inl rfl), hσ s' (Or.inr rfl)]
  have hrest : ∏ x ∈ (univ.erase s).erase s', ∑ T, G x T ≤ A ^ Fintype.card κ := by
    have : ∏ x ∈ (univ.erase s).erase s', ∑ T, G x T = A ^ ((univ.erase s).erase s').card := by
      rw [← Finset.prod_const]
      refine Finset.prod_congr rfl (fun x hx => hA' x ?_)
      rw [Finset.mem_erase, Finset.mem_erase] at hx
      push Not
      exact ⟨hx.2.1, hx.1⟩
    rw [this]
    exact pow_le_pow_right₀ hA (le_trans (Finset.card_le_card (fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))) (le_of_eq Finset.card_univ))
  have : σ * (σ * ∏ x ∈ (univ.erase s).erase s', ∑ T, G x T) ≤ σ * (σ * A ^ Fintype.card κ) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrest hσ0) hσ0
  linarith [this]

end Tuples

/-! ### the main weight and its diagonal mass -/

section Main

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (p : ι → ℕ) (ρ : ι → κ → ℕ)

/-- the truncated product coefficients -/
noncomputable def tr_c (D : ℝ) (f : ι → Option κ) : ℝ :=
  if tr_N p f ≤ D then ∏ s, tr_a p (tr_r f s) else 0

theorem tr_s_log_N (hp : ∀ i, (p i).Prime) (f : ι → Option κ) :
    Real.log (tr_N p f) = ∑ i, (if f i = none then 0 else Real.log (p i)) := by
  unfold tr_N
  rw [Real.log_prod (fun i _ => by
    have : (0 : ℝ) < p i := by exact_mod_cast (hp i).pos
    split_ifs <;> positivity)]
  refine Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)

/-- `∑_{i labelled} 1/(p_i - 1) ≤ log N / ((z-1) log z)` -/
theorem tr_s_sum_inv_labelled (hp : ∀ i, (p i).Prime) {z : ℝ} (hz : 1 < z)
    (hpz : ∀ i, z < p i) (f : ι → Option κ) :
    ∑ i, (if f i = none then 0 else 1 / ((p i : ℝ) - 1)) ≤
      Real.log (tr_N p f) / ((z - 1) * Real.log z) := by
  have hl0 : 0 < Real.log z := Real.log_pos hz
  rw [tr_s_log_N p hp, Finset.sum_div]
  refine Finset.sum_le_sum (fun i _ => ?_)
  split_ifs
  · simp
  · have hzi := hpz i
    have hlz : Real.log z ≤ Real.log (p i) := Real.log_le_log (by linarith) hzi.le
    rw [div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith

theorem tr_s_row_bound (hp : ∀ i, (p i).Prime) (hρ : ∀ i s, ρ i s < p i)
    (hρi : ∀ i, Function.Injective (ρ i)) {z D : ℝ} (hz : 1 < z) (hpz : ∀ i, z < p i)
    (f : ι → Option κ) (hN : tr_N p f ≤ D) :
    ∑ g, |tr_M p ρ f g| - tr_W p f ≤
      (Real.exp (Fintype.card κ * Real.log D / ((z - 1) * Real.log z)) - 1) * tr_W p f := by
  rw [tr_s_rowsum p ρ hp hρ hρi]
  have hW := tr_s_W_nonneg p hp f
  have hl0 : 0 < Real.log z := Real.log_pos hz
  set k : ℝ := (Fintype.card κ : ℝ) with hkdef
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hG : ∏ i, (if f i = none then 1 else 1 + (k - 1) / ((p i : ℝ) - 1)) ≤
      Real.exp (k * Real.log D / ((z - 1) * Real.log z)) := by
    have h1 : ∏ i, (if f i = none then 1 else 1 + (k - 1) / ((p i : ℝ) - 1)) ≤
        ∏ i, Real.exp (k * (if f i = none then 0 else 1 / ((p i : ℝ) - 1))) := by
      refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
      · have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
        split_ifs
        · norm_num
        · have : 0 < (p i : ℝ) - 1 := by linarith
          by_cases hk1 : 1 ≤ k
          · have : 0 ≤ (k - 1) / ((p i : ℝ) - 1) := div_nonneg (by linarith) this.le
            linarith
          · have hkc : k = 0 := by
              have hc : (Fintype.card κ : ℝ) < 1 := lt_of_not_ge hk1
              have hc2 : Fintype.card κ < 1 := by exact_mod_cast hc
              have hc3 : Fintype.card κ = 0 := by omega
              rw [hkdef, hc3]; simp
            rw [hkc]
            have : (1 : ℝ) / ((p i : ℝ) - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
            have : (0 - 1) / ((p i : ℝ) - 1) = -(1 / ((p i : ℝ) - 1)) := by ring
            linarith
      · have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
        split_ifs
        · simp
        · refine le_trans ?_ (Real.add_one_le_exp _)
          have : 0 < (p i : ℝ) - 1 := by linarith
          have : (k - 1) / ((p i : ℝ) - 1) ≤ k * (1 / ((p i : ℝ) - 1)) := by
            rw [mul_one_div]; exact div_le_div_of_nonneg_right (by linarith) this.le
          linarith
    refine le_trans h1 ?_
    rw [← Real.exp_sum, Real.exp_le_exp, ← Finset.mul_sum]
    have h3 := tr_s_sum_inv_labelled p hp hz hpz f
    have hN1 := tr_s_N_ge_one p hp f
    have hlog : Real.log (tr_N p f) ≤ Real.log D := Real.log_le_log (by linarith) hN
    have hz1 : 0 < (z - 1) * Real.log z := by
      have : 0 < z - 1 := by linarith
      positivity
    have h4 : Real.log (tr_N p f) / ((z - 1) * Real.log z) ≤ Real.log D / ((z - 1) * Real.log z) :=
      div_le_div_of_nonneg_right hlog hz1.le
    calc k * ∑ i, (if f i = none then 0 else 1 / ((p i : ℝ) - 1))
        ≤ k * (Real.log D / ((z - 1) * Real.log z)) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) hk
      _ = k * Real.log D / ((z - 1) * Real.log z) := by ring
  have := mul_le_mul_of_nonneg_left hG hW
  nlinarith

theorem tr_s_c_sq_W (D : ℝ) (f : ι → Option κ) :
    tr_c p D f ^ 2 * tr_W p f =
      if tr_N p f ≤ D then ∏ s, (tr_a p (tr_r f s) ^ 2 * tr_phiInv p (tr_r f s)) else 0 := by
  unfold tr_c
  split_ifs
  · rw [tr_s_W_eq, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  · simp

theorem tr_s_pow_sum (g : Finset ι → ℝ) :
    (∑ T, g T) ^ Fintype.card κ = ∑ F : κ → Finset ι, ∏ s, g (F s) := by
  rw [← Fintype.prod_sum (fun (_ : κ) T => g T), Finset.prod_const, Finset.card_univ]

/-- `∑_f ∏_s G(r_s f) prod^γ ≤ A_γ^k` -/
theorem tr_s_sum_le_pow (hp : ∀ i, (p i).Prime) (g : Finset ι → ℝ) (hg : ∀ T, 0 ≤ g T)
    (γ : ℝ) :
    ∑ f : ι → Option κ, ∏ s, (g (tr_r f s) * tr_prodP p (tr_r f s) ^ γ) ≤
      (∑ T, g T * tr_prodP p T ^ γ) ^ Fintype.card κ := by
  rw [tr_s_pow_sum]
  exact tr_s_sum_inj (fun F => ∏ s, (g (F s) * tr_prodP p (F s) ^ γ))
    (fun F => Finset.prod_nonneg (fun s _ => mul_nonneg (hg _)
      (Real.rpow_nonneg (le_trans zero_le_one (tr_s_prodP_ge_one p hp _)) _)))

theorem tr_s_N_rpow (hp : ∀ i, (p i).Prime) (f : ι → Option κ) (γ : ℝ) :
    tr_N p f ^ γ = ∏ s, tr_prodP p (tr_r f s) ^ γ := by
  rw [tr_s_N_eq, Real.finsetProd_rpow _ _ (fun s _ =>
    le_trans zero_le_one (tr_s_prodP_ge_one p hp _))]

/-- tail of the diagonal sum beyond the cutoff `D` -/
theorem tr_s_tail (hp : ∀ i, (p i).Prime) (g : Finset ι → ℝ) (hg : ∀ T, 0 ≤ g T)
    (D β : ℝ) (hD : 0 < D) (hβ : 0 ≤ β) :
    ∑ f : ι → Option κ, (if tr_N p f ≤ D then 0 else ∏ s, g (tr_r f s)) ≤
      Real.exp (-(β * Real.log D)) * (∑ T, g T * tr_prodP p T ^ β) ^ Fintype.card κ := by
  have hpt : ∀ f : ι → Option κ, (if tr_N p f ≤ D then 0 else ∏ s, g (tr_r f s)) ≤
      Real.exp (-(β * Real.log D)) * ∏ s, (g (tr_r f s) * tr_prodP p (tr_r f s) ^ β) := by
    intro f
    have hP : 0 ≤ ∏ s, g (tr_r f s) := Finset.prod_nonneg (fun s _ => hg _)
    rw [Finset.prod_mul_distrib, ← tr_s_N_rpow p hp]
    have hN1 := tr_s_N_ge_one p hp f
    split_ifs with h
    · have : 0 ≤ tr_N p f ^ β := Real.rpow_nonneg (by linarith) _
      positivity
    · push Not at h
      have hratio : 1 ≤ Real.exp (-(β * Real.log D)) * tr_N p f ^ β := by
        rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add, Real.one_le_exp_iff]
        have := Real.log_le_log hD h.le
        nlinarith
      nlinarith
  refine le_trans (Finset.sum_le_sum (fun f _ => hpt f)) ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (tr_s_sum_le_pow p hp g hg β) (Real.exp_pos _).le

/-- lower bound for the diagonal mass `Δ` -/
theorem tr_s_Delta_lower (hp : ∀ i, (p i).Prime) {z : ℝ} (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (D β K1 : ℝ) (hD : 0 < D) (hβ : 0 ≤ β) (hK1 : 0 ≤ K1)
    (hK : ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
        |tr_a p T| * tr_prodP p T ^ β * tr_phiInv p T ≤ K1) :
    (∑ T, tr_a p T ^ 2 * tr_phiInv p T) ^ Fintype.card κ *
      (1 - 4 * (Fintype.card κ : ℝ) ^ 2 * ∑ i, 1 / ((p i : ℝ) - 1) ^ 2
        - Real.exp (-(β * Real.log D) + Fintype.card κ * β * K1 / tr_B p))
      ≤ ∑ f : ι → Option κ, tr_c p D f ^ 2 * tr_W p f := by
  set g : Finset ι → ℝ := fun T => tr_a p T ^ 2 * tr_phiInv p T with hgdef
  have hg : ∀ T, 0 ≤ g T := fun T => mul_nonneg (sq_nonneg _) (tr_s_phiInv_nonneg p hp T)
  set A := ∑ T, g T with hAdef
  have hA1 : 1 ≤ A := tr_s_A_ge_one p hp
  set k := Fintype.card κ with hk
  have hBp := tr_s_B_pos p hz hB
  -- σ_i bound
  have hσ : ∀ i, ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => i ∈ T), g T ≤
      2 / ((p i : ℝ) - 1) := by
    intro i
    refine le_trans (Finset.sum_le_sum (fun T _ => ?_)) (tr_s_star p hp hz hpz hB i)
    have ha := tr_s_a_abs_le_one p hp hz hpz hB T
    have hφ := tr_s_phiInv_nonneg p hp T
    have : tr_a p T ^ 2 ≤ |tr_a p T| := by
      rw [← sq_abs]; nlinarith [abs_nonneg (tr_a p T)]
    exact mul_le_mul_of_nonneg_right this hφ
  -- the full sum over labellings
  have hfull : A ^ k * (1 - 4 * (k : ℝ) ^ 2 * ∑ i, 1 / ((p i : ℝ) - 1) ^ 2) ≤
      ∑ f : ι → Option κ, ∏ s, g (tr_r f s) := by
    have hs := tr_s_sum_surj (κ := κ) (fun F => ∏ s, g (F s))
      (fun F => Finset.prod_nonneg (fun s _ => hg _))
    rw [← tr_s_pow_sum] at hs
    have hpair : ∑ s : κ, ∑ s' : κ, ∑ i : ι, (if s ≠ s' then
        ∑ F : κ → Finset ι, (if i ∈ F s ∧ i ∈ F s' then ∏ s'', g (F s'') else 0) else 0) ≤
        ∑ s : κ, ∑ s' : κ, ∑ i : ι, 4 / ((p i : ℝ) - 1) ^ 2 * A ^ k := by
      refine Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun s' _ =>
        Finset.sum_le_sum (fun i _ => ?_)))
      have h2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
      have hpos : 0 < (p i : ℝ) - 1 := by linarith
      split_ifs with hss
      · refine le_trans (tr_s_pair_mass g hg hA1 s s' hss i) ?_
        have hσi := hσ i
        have hσ0 : 0 ≤ ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => i ∈ T), g T :=
          Finset.sum_nonneg (fun T _ => hg T)
        have hsq : (∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => i ∈ T), g T) ^ 2 ≤
            4 / ((p i : ℝ) - 1) ^ 2 := by
          have := pow_le_pow_left₀ hσ0 hσi 2
          rw [div_pow] at this; norm_num at this; linarith
        exact mul_le_mul_of_nonneg_right hsq (pow_nonneg (by linarith) _)
      · exact mul_nonneg (by positivity) (pow_nonneg (by linarith) _)
    have hcnt : ∑ s : κ, ∑ s' : κ, ∑ i : ι, 4 / ((p i : ℝ) - 1) ^ 2 * A ^ k =
        A ^ k * (4 * (k : ℝ) ^ 2 * ∑ i, 1 / ((p i : ℝ) - 1) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul]
      rw [show (∑ i, 4 / ((p i : ℝ) - 1) ^ 2) = 4 * ∑ i, 1 / ((p i : ℝ) - 1) ^ 2 by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
      rw [← hk]
      ring
    nlinarith [hs, hpair, hcnt]
  have htail := tr_s_tail (κ := κ) p hp g hg D β hD hβ
  have hAb := tr_s_Agamma p hp hz hpz hB K1 β hβ hK1 hK
  have hAbk : (∑ T, g T * tr_prodP p T ^ β) ^ k ≤
      A ^ k * Real.exp (k * β * K1 / tr_B p) := by
    have h0 : 0 ≤ ∑ T, g T * tr_prodP p T ^ β := Finset.sum_nonneg (fun T _ => mul_nonneg (hg T)
      (Real.rpow_nonneg (le_trans zero_le_one (tr_s_prodP_ge_one p hp _)) _))
    have h1 : (∑ T, g T * tr_prodP p T ^ β) ^ k ≤ (A * (1 + β * K1 / tr_B p)) ^ k :=
      pow_le_pow_left₀ h0 hAb k
    have h2 : (1 + β * K1 / tr_B p) ^ k ≤ Real.exp (k * β * K1 / tr_B p) := by
      have := Real.add_one_le_exp (β * K1 / tr_B p)
      calc (1 + β * K1 / tr_B p) ^ k ≤ Real.exp (β * K1 / tr_B p) ^ k :=
            pow_le_pow_left₀ (by positivity) (by linarith) k
        _ = Real.exp (k * β * K1 / tr_B p) := by
            rw [← Real.exp_nat_mul]; ring_nf
    rw [mul_pow] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _))
  have hsplit : ∑ f : ι → Option κ, ∏ s, g (tr_r f s) =
      ∑ f : ι → Option κ, tr_c p D f ^ 2 * tr_W p f +
      ∑ f : ι → Option κ, (if tr_N p f ≤ D then 0 else ∏ s, g (tr_r f s)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [tr_s_c_sq_W]
    split_ifs <;> simp [hgdef]
  have hexp : Real.exp (-(β * Real.log D)) * (A ^ k * Real.exp (k * β * K1 / tr_B p)) =
      A ^ k * Real.exp (-(β * Real.log D) + k * β * K1 / tr_B p) := by
    rw [Real.exp_add]; ring
  have htail2 : ∑ f : ι → Option κ, (if tr_N p f ≤ D then 0 else ∏ s, g (tr_r f s)) ≤
      A ^ k * Real.exp (-(β * Real.log D) + k * β * K1 / tr_B p) := by
    rw [← hexp]
    exact le_trans htail (mul_le_mul_of_nonneg_left hAbk (Real.exp_pos _).le)
  have e : A ^ k * (1 - 4 * (k : ℝ) ^ 2 * ∑ i, 1 / ((p i : ℝ) - 1) ^ 2
      - Real.exp (-(β * Real.log D) + k * β * K1 / tr_B p)) =
      A ^ k * (1 - 4 * (k : ℝ) ^ 2 * ∑ i, 1 / ((p i : ℝ) - 1) ^ 2)
      - A ^ k * Real.exp (-(β * Real.log D) + k * β * K1 / tr_B p) := by ring
  rw [e]
  linarith [hfull, hsplit, htail2]

end Main

/-! ### one uncovered form: the modified weight -/

section Eps

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)

/-- the truncated one-coordinate sum `ε(m)` stays small -/
theorem tr_s_eps (hp : ∀ i, (p i).Prime) {z : ℝ} (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (Fr : Finset ι) (N' D β K1 : ℝ) (hN' : 1 ≤ N')
    (hD : 0 < D) (hβ : 0 ≤ β)
    (hK : ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
        |tr_a p T| * tr_prodP p T ^ β * tr_phiInv p T ≤ K1) :
    |∑ T ∈ Fr.powerset, (if N' * tr_prodP p T ≤ D then tr_a p T * tr_phiInv p T else 0)| ≤
      (1 + K1) * (N' ^ β * Real.exp (-(β * Real.log D))) +
        ∑ i ∈ univ.filter (fun i => i ∉ Fr), 2 / ((p i : ℝ) - 1) := by
  classical
  set Y : Finset ι → ℝ := fun T => tr_a p T * tr_phiInv p T with hY
  have hYabs : ∀ T, |Y T| = |tr_a p T| * tr_phiInv p T := fun T => by
    rw [hY]; simp only; rw [abs_mul, abs_of_nonneg (tr_s_phiInv_nonneg p hp T)]
  set good : Finset ι → Prop := fun T => T ⊆ Fr ∧ N' * tr_prodP p T ≤ D with hgood
  have h1 : ∑ T ∈ Fr.powerset, (if N' * tr_prodP p T ≤ D then Y T else 0) =
      ∑ T, (if good T then Y T else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext T; simp [hgood, Finset.mem_powerset]
  have h0 : ∑ T, Y T = 0 := tr_s_sum_a_phi p hp hz hpz hB
  have h2 : ∑ T, (if good T then Y T else 0) = -∑ T, (if good T then 0 else Y T) := by
    have : ∑ T, (if good T then Y T else 0) + ∑ T, (if good T then 0 else Y T) = ∑ T, Y T := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun T _ => by split_ifs <;> simp)
    linarith
  rw [h1, h2, abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  -- pointwise split
  have hpt : ∀ T, |(if good T then 0 else Y T)| ≤
      (∑ i ∈ univ.filter (fun i => i ∉ Fr), (if i ∈ T then |Y T| else 0)) +
        (N' * tr_prodP p T) ^ β * Real.exp (-(β * Real.log D)) * |Y T| := by
    intro T
    have hnn1 : 0 ≤ ∑ i ∈ univ.filter (fun i => i ∉ Fr), (if i ∈ T then |Y T| else 0) :=
      Finset.sum_nonneg (fun i _ => by split_ifs <;> simp)
    have hP1 := tr_s_prodP_ge_one p hp T
    have hNP : 1 ≤ N' * tr_prodP p T := by nlinarith
    have hnn2 : 0 ≤ (N' * tr_prodP p T) ^ β * Real.exp (-(β * Real.log D)) * |Y T| := by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ N' * tr_prodP p T) β
      positivity
    by_cases hg : good T
    · rw [if_pos hg, abs_zero]; linarith
    rw [if_neg hg]
    simp only [hgood, not_and_or] at hg
    rcases hg with hg | hg
    · obtain ⟨i, hiT, hiF⟩ := Finset.not_subset.1 hg
      have : |Y T| ≤ ∑ i ∈ univ.filter (fun i => i ∉ Fr), (if i ∈ T then |Y T| else 0) := by
        have hmem : i ∈ univ.filter (fun i => i ∉ Fr) := by simp [hiF]
        have := Finset.single_le_sum (f := fun i => if i ∈ T then |Y T| else 0)
          (fun i _ => by split_ifs <;> simp) hmem
        simpa [hiT] using this
      linarith
    · push Not at hg
      have hratio : 1 ≤ (N' * tr_prodP p T) ^ β * Real.exp (-(β * Real.log D)) := by
        rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add, Real.one_le_exp_iff]
        have := Real.log_le_log hD hg.le
        nlinarith
      have := mul_le_mul_of_nonneg_right hratio (abs_nonneg (Y T))
      linarith
  refine le_trans (Finset.sum_le_sum (fun T _ => hpt T)) ?_
  rw [Finset.sum_add_distrib, add_comm]
  refine add_le_add ?_ ?_
  · -- the cutoff part
    have e : ∀ T, (N' * tr_prodP p T) ^ β * Real.exp (-(β * Real.log D)) * |Y T| =
        (N' ^ β * Real.exp (-(β * Real.log D))) * (|tr_a p T| * tr_prodP p T ^ β * tr_phiInv p T) := by
      intro T
      rw [Real.mul_rpow (by linarith) (le_trans zero_le_one (tr_s_prodP_ge_one p hp T)), hYabs]
      ring
    simp_rw [e]
    rw [← Finset.mul_sum, tr_s_sum_ne]
    simp only [tr_s_a_empty, abs_one, tr_s_prodP_empty, Real.one_rpow, tr_s_phiInv_empty,
      mul_one]
    have : 0 ≤ N' ^ β * Real.exp (-(β * Real.log D)) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
    nlinarith
  · rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine le_trans (le_of_eq ?_) (tr_s_star p hp hz hpz hB i)
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun T _ => by rw [hYabs])

end Eps

section Uncov

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (p : ι → ℕ) (ρ : ι → κ → ℕ)

/-- forget label `s0` -/
def tr_strip (s0 : κ) (f : ι → Option κ) : ι → Option κ :=
  fun i => if f i = some s0 then none else f i

/-- coefficients of the weight with form `s0` replaced by its uncovered value -/
noncomputable def tr_cs (D : ℝ) (s0 : κ) (f' : ι → Option κ) : ℝ :=
  ∑ f ∈ univ.filter (fun f => tr_strip s0 f = f'), tr_c p D f * tr_phiInv p (tr_r f s0)

theorem tr_s_N_strip_le (hp : ∀ i, (p i).Prime) (s0 : κ) (f : ι → Option κ) :
    tr_N p (tr_strip s0 f) ≤ tr_N p f := by
  unfold tr_N tr_strip
  refine Finset.prod_le_prod (fun i _ => by split_ifs <;> positivity) (fun i _ => ?_)
  by_cases h : f i = some s0
  · simp only [h, if_true, reduceCtorEq, if_false]
    exact_mod_cast (hp i).one_lt.le
  · simp [h]

theorem tr_s_R_uncov (hp : ∀ i, (p i).Prime) (D : ℝ) (s0 : κ) (t : ℕ)
    (ht : ∀ i, t % p i ≠ ρ i s0) :
    ∑ f, tr_c p D f * tr_Psi p ρ f t = ∑ f', tr_cs p D s0 f' * tr_Psi p ρ f' t := by
  have hpt : ∀ f : ι → Option κ, tr_Psi p ρ f t =
      tr_phiInv p (tr_r f s0) * tr_Psi p ρ (tr_strip s0 f) t := by
    intro f
    unfold tr_Psi tr_phiInv tr_r
    rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    unfold tr_strip
    by_cases h : f i = some s0
    · rw [h]; simp only [tr_psio, tr_psi, if_neg (ht i), if_true, mul_one]
    · rw [if_neg h, if_neg h, one_mul]
  rw [Finset.sum_congr rfl (fun f _ => by rw [hpt f])]
  unfold tr_cs
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise (s := (univ : Finset (ι → Option κ))) (g := tr_strip s0)
    (f := fun (f : ι → Option κ) => tr_c p D f * (tr_phiInv p (tr_r f s0) *
      tr_Psi p ρ (tr_strip s0 f) t))]
  refine Finset.sum_congr rfl (fun f' _ => Finset.sum_congr rfl (fun f hf => ?_))
  rw [Finset.mem_filter] at hf
  rw [hf.2]; ring

theorem tr_s_cs_abs_sum (hp : ∀ i, (p i).Prime) (D : ℝ) (s0 : κ) :
    ∑ f', |tr_cs p D s0 f'| * tr_N p f' ≤ ∑ f : ι → Option κ, |tr_c p D f| * tr_N p f := by
  rw [← Finset.sum_fiberwise (s := (univ : Finset (ι → Option κ))) (g := tr_strip s0)
    (f := fun (f : ι → Option κ) => |tr_c p D f| * tr_N p f)]
  refine Finset.sum_le_sum (fun f' _ => ?_)
  unfold tr_cs
  have hN := tr_s_N_nonneg p f'
  refine le_trans (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hN) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun f hf => ?_)
  rw [Finset.mem_filter] at hf
  rw [abs_mul, abs_of_nonneg (tr_s_phiInv_nonneg p hp _), ← hf.2]
  have h1 := tr_s_phiInv_le_one p hp (tr_r f s0)
  have h2 := tr_s_N_strip_le p hp s0 f
  have h3 := tr_s_phiInv_nonneg p hp (tr_r f s0)
  have h4 := tr_s_N_nonneg p (tr_strip s0 f)
  have h5 := abs_nonneg (tr_c p D f)
  calc |tr_c p D f| * tr_phiInv p (tr_r f s0) * tr_N p (tr_strip s0 f)
      ≤ |tr_c p D f| * 1 * tr_N p (tr_strip s0 f) := by gcongr
    _ ≤ |tr_c p D f| * tr_N p f := by rw [mul_one]; gcongr

theorem tr_s_cs_ne (hp : ∀ i, (p i).Prime) (D : ℝ) (s0 : κ) (f' : ι → Option κ) (h : tr_cs p D s0 f' ≠ 0) :
    tr_N p f' ≤ D := by
  by_contra hc
  apply h
  unfold tr_cs
  refine Finset.sum_eq_zero (fun f hf => ?_)
  rw [Finset.mem_filter] at hf
  have : ¬ tr_N p f ≤ D := fun h' => hc (le_trans (hf.2 ▸ tr_s_N_strip_le p hp s0 f) h')
  simp [tr_c, this]

theorem tr_s_prod_ite_one (s0 : κ) (x : ℝ) (y : κ → ℝ) (hy : y s0 = 1) :
    ∏ s, (if s = s0 then x else y s) = x * ∏ s, y s := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s0), ← Finset.mul_prod_erase _ y
    (Finset.mem_univ s0), hy, if_pos rfl, one_mul]
  congr 1
  exact Finset.prod_congr rfl (fun s hs => by rw [if_neg (Finset.ne_of_mem_erase hs)])

/-- explicit form of `c'` on labellings avoiding `s0` -/
theorem tr_s_cs_formula (D : ℝ) (s0 : κ) (f' : ι → Option κ) (hav : ∀ i, f' i ≠ some s0) :
    tr_cs p D s0 f' = (∏ s, tr_a p (tr_r f' s)) *
      ∑ T ∈ (univ.filter (fun i => f' i = none)).powerset,
        (if tr_N p f' * tr_prodP p T ≤ D then tr_a p T * tr_phiInv p T else 0) := by
  classical
  set Fr := univ.filter (fun i => f' i = none) with hFr
  set ext : Finset ι → ι → Option κ := fun T i => if i ∈ T then some s0 else f' i with hext
  have hr0 : tr_r f' s0 = ∅ := by
    ext i; simp [tr_r, hav i]
  have hr_ext : ∀ T, T ⊆ Fr → ∀ s, tr_r (ext T) s = if s = s0 then T else tr_r f' s := by
    intro T hT s
    ext i
    rw [tr_s_mem_r]
    simp only [hext]
    by_cases hs : s = s0
    · subst hs
      rw [if_pos rfl]
      by_cases hi : i ∈ T
      · simp [hi]
      · simp [hi, hav i]
    · rw [if_neg hs, tr_s_mem_r]
      by_cases hi : i ∈ T
      · have : f' i = none := by
          have := hT hi; rw [hFr, Finset.mem_filter] at this; exact this.2
        simp [hi, this, Ne.symm hs]
      · simp [hi]
  have hN_ext : ∀ T, T ⊆ Fr → tr_N p (ext T) = tr_N p f' * tr_prodP p T := by
    intro T hT
    unfold tr_N tr_prodP
    rw [show ∏ i ∈ T, (p i : ℝ) = ∏ i, (if i ∈ T then (p i : ℝ) else 1) by
      rw [← Finset.prod_filter]; congr 1; ext; simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [hext, Finset.mem_univ, true_and]
    by_cases hi : i ∈ T
    · have : f' i = none := by
        have := hT hi; rw [hFr, Finset.mem_filter] at this; exact this.2
      simp [hi, this]
    · simp [hi]
  unfold tr_cs
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun f => tr_r f s0) ext ?_ ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    simp only [Finset.mem_coe, Finset.mem_powerset]
    intro i hi
    rw [tr_s_mem_r] at hi
    rw [hFr, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hf]; simp [tr_strip, hi]
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_powerset] at hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    funext i
    simp only [tr_strip, hext]
    by_cases hi : i ∈ T
    · have : f' i = none := by
        have := hT hi; rw [hFr, Finset.mem_filter] at this; exact this.2
      simp [hi, this]
    · simp [hi, hav i]
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    funext i
    simp only [hext, tr_s_mem_r]
    by_cases hi : f i = some s0
    · simp [hi]
    · rw [if_neg hi, ← hf]; simp [tr_strip, hi]
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_powerset] at hT
    rw [hr_ext T hT s0, if_pos rfl]
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hTsub : tr_r f s0 ⊆ Fr := by
      intro i hi
      rw [tr_s_mem_r] at hi
      rw [hFr, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hf]; simp [tr_strip, hi]
    have hfe : ext (tr_r f s0) = f := by
      funext i
      simp only [hext, tr_s_mem_r]
      by_cases hi : f i = some s0
      · simp [hi]
      · rw [if_neg hi, ← hf]; simp [tr_strip, hi]
    conv_lhs => rw [← hfe]
    unfold tr_c
    rw [hN_ext _ hTsub]
    have hprod : ∏ s, tr_a p (tr_r (ext (tr_r f s0)) s) =
        tr_a p (tr_r f s0) * ∏ s, tr_a p (tr_r f' s) := by
      simp_rw [hr_ext _ hTsub]
      have := tr_s_prod_ite_one s0 (tr_a p (tr_r f s0)) (fun s => tr_a p (tr_r f' s))
        (by simp only [hr0, tr_s_a_empty])
      rw [← this]
      exact Finset.prod_congr rfl (fun s _ => by split_ifs <;> rfl)
    rw [hprod]
    split_ifs <;> (try rw [hfe]) <;> ring

end Uncov

/-! ### the comparison -/

section Final

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (p : ι → ℕ) (ρ : ι → κ → ℕ)

theorem tr_s_Apow (hp : ∀ i, (p i).Prime) {z : ℝ} (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (K1 γ : ℝ) (hγ : 0 ≤ γ) (hK1 : 0 ≤ K1)
    (hK : ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
        |tr_a p T| * tr_prodP p T ^ γ * tr_phiInv p T ≤ K1) (k : ℕ) :
    (∑ T, tr_a p T ^ 2 * tr_phiInv p T * tr_prodP p T ^ γ) ^ k ≤
      (∑ T, tr_a p T ^ 2 * tr_phiInv p T) ^ k * Real.exp (k * γ * K1 / tr_B p) := by
  have hBp := tr_s_B_pos p hz hB
  have hA1 := tr_s_A_ge_one p hp
  have hAb := tr_s_Agamma p hp hz hpz hB K1 γ hγ hK1 hK
  have h0 : 0 ≤ ∑ T, tr_a p T ^ 2 * tr_phiInv p T * tr_prodP p T ^ γ :=
    Finset.sum_nonneg (fun T _ => mul_nonneg (mul_nonneg (sq_nonneg _)
      (tr_s_phiInv_nonneg p hp T))
      (Real.rpow_nonneg (le_trans zero_le_one (tr_s_prodP_ge_one p hp _)) _))
  have h1 := pow_le_pow_left₀ h0 hAb k
  have h2 : (1 + γ * K1 / tr_B p) ^ k ≤ Real.exp (k * γ * K1 / tr_B p) := by
    have := Real.add_one_le_exp (γ * K1 / tr_B p)
    calc (1 + γ * K1 / tr_B p) ^ k ≤ Real.exp (γ * K1 / tr_B p) ^ k :=
          pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = Real.exp (k * γ * K1 / tr_B p) := by
          rw [← Real.exp_nat_mul]; ring_nf
  rw [mul_pow] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _))

theorem tr_s_c_total (hp : ∀ i, (p i).Prime) {z : ℝ} (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (D : ℝ) (hD : 1 ≤ D) :
    ∑ f : ι → Option κ, |tr_c p D f| * tr_N p f ≤ D ^ 2 * 2 ^ Fintype.card κ := by
  set g : Finset ι → ℝ := fun T => |tr_a p T| * tr_phiInv p T with hg
  have hgn : ∀ T, 0 ≤ g T := fun T => mul_nonneg (abs_nonneg _) (tr_s_phiInv_nonneg p hp T)
  have hpt : ∀ f : ι → Option κ, |tr_c p D f| * tr_N p f ≤ D ^ 2 * ∏ s, g (tr_r f s) := by
    intro f
    unfold tr_c
    split_ifs with h
    · have hN1 := tr_s_N_ge_one p hp f
      have hdiv : (∏ s, |tr_a p (tr_r f s)|) / tr_N p f ≤ ∏ s, g (tr_r f s) := by
        rw [tr_s_N_eq, ← Finset.prod_div_distrib]
        refine Finset.prod_le_prod (fun s _ => div_nonneg (abs_nonneg _)
          (le_trans zero_le_one (tr_s_prodP_ge_one p hp _))) (fun s _ => ?_)
        rw [hg, div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left (tr_s_inv_prodP_le p hp _) (abs_nonneg _)
      rw [Finset.abs_prod]
      have hP : 0 ≤ ∏ s, |tr_a p (tr_r f s)| := Finset.prod_nonneg (fun s _ => abs_nonneg _)
      have e : (∏ s, |tr_a p (tr_r f s)|) * tr_N p f =
          tr_N p f ^ 2 * ((∏ s, |tr_a p (tr_r f s)|) / tr_N p f) := by
        field_simp
      rw [e]
      have hN2 : tr_N p f ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (by linarith) h 2
      have hq : 0 ≤ (∏ s, |tr_a p (tr_r f s)|) / tr_N p f := div_nonneg hP (by linarith)
      calc tr_N p f ^ 2 * ((∏ s, |tr_a p (tr_r f s)|) / tr_N p f)
          ≤ D ^ 2 * ((∏ s, |tr_a p (tr_r f s)|) / tr_N p f) := mul_le_mul_of_nonneg_right hN2 hq
        _ ≤ D ^ 2 * ∏ s, g (tr_r f s) := mul_le_mul_of_nonneg_left hdiv (by positivity)
    · simp only [abs_zero, zero_mul]
      exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun s _ => hgn _))
  refine le_trans (Finset.sum_le_sum (fun f _ => hpt f)) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 := tr_s_sum_inj (κ := κ) (fun F => ∏ s, g (F s))
    (fun F => Finset.prod_nonneg (fun s _ => hgn _))
  rw [← tr_s_pow_sum] at h1
  refine le_trans h1 (le_of_eq ?_)
  rw [hg, tr_s_sum_abs_a_all p hp hz hpz hB]

/-- diagonal mass of the modified weight -/
theorem tr_s_Delta2 (hp : ∀ i, (p i).Prime) {z : ℝ} (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (D β K1 : ℝ) (hD : 1 ≤ D) (hβ : 0 ≤ β) (hK1 : 0 ≤ K1)
    (hK : ∀ γ, 0 ≤ γ → γ ≤ 2 * β → ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
        |tr_a p T| * tr_prodP p T ^ γ * tr_phiInv p T ≤ K1) (s0 : κ) :
    ∑ f', tr_cs p D s0 f' ^ 2 * tr_W p f' ≤
      (∑ T, tr_a p T ^ 2 * tr_phiInv p T) ^ Fintype.card κ *
        (2 * (1 + K1) ^ 2 * Real.exp (-(2 * β * Real.log D) +
          Fintype.card κ * (2 * β) * K1 / tr_B p) +
         2 * (2 * Real.log D / ((z - 1) * Real.log z)) ^ 2) := by
  set g : Finset ι → ℝ := fun T => tr_a p T ^ 2 * tr_phiInv p T with hgdef
  have hg : ∀ T, 0 ≤ g T := fun T => mul_nonneg (sq_nonneg _) (tr_s_phiInv_nonneg p hp T)
  set η := 2 * Real.log D / ((z - 1) * Real.log z) with hη
  set E := Real.exp (-(β * Real.log D)) with hE
  have hl0 : 0 < Real.log z := Real.log_pos hz
  have hz1 : 0 < (z - 1) * Real.log z := mul_pos (by linarith) hl0
  have hη0 : 0 ≤ η := div_nonneg (by have := Real.log_nonneg hD; linarith) hz1.le
  have hD0 : 0 < D := by linarith
  -- pointwise bound
  have hpt : ∀ f' : ι → Option κ, tr_cs p D s0 f' ^ 2 * tr_W p f' ≤
      (∏ s, g (tr_r f' s)) * (2 * (1 + K1) ^ 2 * (tr_N p f' ^ (2 * β) * E ^ 2) + 2 * η ^ 2) := by
    intro f'
    have hPg : 0 ≤ ∏ s, g (tr_r f' s) := Finset.prod_nonneg (fun s _ => hg _)
    have hN1 := tr_s_N_ge_one p hp f'
    have hR : 0 ≤ 2 * (1 + K1) ^ 2 * (tr_N p f' ^ (2 * β) * E ^ 2) + 2 * η ^ 2 := by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ tr_N p f') (2 * β)
      positivity
    by_cases hc : tr_cs p D s0 f' = 0
    · rw [hc]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact mul_nonneg hPg hR
    have hND := tr_s_cs_ne p hp D s0 f' hc
    have hav : ∀ i, f' i ≠ some s0 := by
      intro i hi
      apply hc
      unfold tr_cs
      refine Finset.sum_eq_zero (fun f hf => ?_)
      rw [Finset.mem_filter] at hf
      have := congrFun hf.2 i
      simp only [tr_strip] at this
      split_ifs at this with h
      · rw [hi] at this; exact absurd this (by simp)
      · rw [hi] at this; exact absurd this h
    rw [tr_s_cs_formula p D s0 f' hav]
    set ε := ∑ T ∈ (univ.filter (fun i => f' i = none)).powerset,
        (if tr_N p f' * tr_prodP p T ≤ D then tr_a p T * tr_phiInv p T else 0) with hε
    have hεb := tr_s_eps p hp hz hpz hB (univ.filter (fun i => f' i = none)) (tr_N p f') D β K1
      hN1 hD0 hβ (hK β hβ (by linarith))
    have hlab : ∑ i ∈ univ.filter (fun i => i ∉ univ.filter (fun i => f' i = none)),
        2 / ((p i : ℝ) - 1) ≤ η := by
      have h1 : ∑ i ∈ univ.filter (fun i => i ∉ univ.filter (fun i => f' i = none)),
          2 / ((p i : ℝ) - 1) = 2 * ∑ i, (if f' i = none then 0 else 1 / ((p i : ℝ) - 1)) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases h : f' i = none <;> simp [h] <;> ring
      rw [h1, hη]
      have h2 := tr_s_sum_inv_labelled p hp hz hpz f'
      have h3 : Real.log (tr_N p f') ≤ Real.log D := Real.log_le_log (by linarith) hND
      have h4 := div_le_div_of_nonneg_right h3 hz1.le
      rw [mul_div_assoc]
      linarith
    set x := (1 + K1) * (tr_N p f' ^ β * E) with hx
    have hx0 : 0 ≤ x := by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ tr_N p f') β
      have : 0 < E := Real.exp_pos _
      positivity
    have hεabs : |ε| ≤ x + η := by linarith
    have hεsq : ε ^ 2 ≤ 2 * x ^ 2 + 2 * η ^ 2 := by
      have h1 : ε ^ 2 ≤ (x + η) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hεabs 2
      nlinarith [sq_nonneg (x - η)]
    have hxsq : x ^ 2 = (1 + K1) ^ 2 * (tr_N p f' ^ (2 * β) * E ^ 2) := by
      rw [hx, mul_pow, mul_pow, mul_comm 2 β, Real.rpow_mul (by linarith), Real.rpow_two]
    have hPW : (∏ s, tr_a p (tr_r f' s)) ^ 2 * tr_W p f' = ∏ s, g (tr_r f' s) := by
      rw [tr_s_W_eq, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    calc ((∏ s, tr_a p (tr_r f' s)) * ε) ^ 2 * tr_W p f'
        = (∏ s, g (tr_r f' s)) * ε ^ 2 := by rw [← hPW]; ring
      _ ≤ (∏ s, g (tr_r f' s)) * (2 * x ^ 2 + 2 * η ^ 2) := mul_le_mul_of_nonneg_left hεsq hPg
      _ = _ := by rw [hxsq]; ring
  refine le_trans (Finset.sum_le_sum (fun f' _ => hpt f')) ?_
  -- sum up
  have hsplit : ∀ f' : ι → Option κ,
      (∏ s, g (tr_r f' s)) * (2 * (1 + K1) ^ 2 * (tr_N p f' ^ (2 * β) * E ^ 2) + 2 * η ^ 2) =
      (2 * (1 + K1) ^ 2 * E ^ 2) * ∏ s, (g (tr_r f' s) * tr_prodP p (tr_r f' s) ^ (2 * β)) +
      (2 * η ^ 2) * ∏ s, g (tr_r f' s) := by
    intro f'
    rw [show ∏ s, (g (tr_r f' s) * tr_prodP p (tr_r f' s) ^ (2 * β)) =
        (∏ s, g (tr_r f' s)) * tr_N p f' ^ (2 * β) by
      rw [Finset.prod_mul_distrib (f := fun s => g (tr_r f' s)), tr_s_N_rpow p hp]]
    ring
  rw [Finset.sum_congr rfl (fun f' _ => hsplit f')]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hs1 := tr_s_sum_le_pow (κ := κ) p hp g hg (2 * β)
  have hs0 : ∑ f' : ι → Option κ, ∏ s, g (tr_r f' s) ≤ (∑ T, g T) ^ Fintype.card κ := by
    have h1 := tr_s_sum_inj (κ := κ) (fun F => ∏ s, g (F s))
      (fun F => Finset.prod_nonneg (fun s _ => hg _))
    rw [← tr_s_pow_sum] at h1
    exact h1
  have hAp := tr_s_Apow p hp hz hpz hB K1 (2 * β) (by linarith) hK1 (hK _ (by linarith) le_rfl)
    (Fintype.card κ)
  set A := ∑ T, tr_a p T ^ 2 * tr_phiInv p T
  have hA1 : 1 ≤ A := tr_s_A_ge_one p hp
  have hE2 : E ^ 2 * Real.exp (Fintype.card κ * (2 * β) * K1 / tr_B p) =
      Real.exp (-(2 * β * Real.log D) + Fintype.card κ * (2 * β) * K1 / tr_B p) := by
    rw [hE, sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
  have hc1 : 0 ≤ 2 * (1 + K1) ^ 2 * E ^ 2 := by positivity
  have hc2 : 0 ≤ 2 * η ^ 2 := by positivity
  have t1 : 2 * (1 + K1) ^ 2 * E ^ 2 * ∑ f' : ι → Option κ,
      ∏ s, (g (tr_r f' s) * tr_prodP p (tr_r f' s) ^ (2 * β)) ≤
      2 * (1 + K1) ^ 2 * E ^ 2 * (A ^ Fintype.card κ *
        Real.exp (Fintype.card κ * (2 * β) * K1 / tr_B p)) :=
    mul_le_mul_of_nonneg_left (le_trans hs1 hAp) hc1
  have t2 : 2 * η ^ 2 * ∑ f' : ι → Option κ, ∏ s, g (tr_r f' s)
      ≤ 2 * η ^ 2 * A ^ Fintype.card κ := mul_le_mul_of_nonneg_left hs0 hc2
  have e3 : 2 * (1 + K1) ^ 2 * E ^ 2 * (A ^ Fintype.card κ *
        Real.exp (Fintype.card κ * (2 * β) * K1 / tr_B p)) =
      A ^ Fintype.card κ * (2 * (1 + K1) ^ 2 *
        Real.exp (-(2 * β * Real.log D) + Fintype.card κ * (2 * β) * K1 / tr_B p)) := by
    rw [← hE2]; ring
  nlinarith [t1, t2, e3]

/-- **The abstract covering theorem.** -/
theorem tr_abstract (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hρ : ∀ i s, ρ i s < p i) (hρi : ∀ i, Function.Injective (ρ i))
    (z D β K1 : ℝ) (T : ℕ) (hz : 1 < z) (hpz : ∀ i, z < p i)
    (hB : 1 ≤ tr_B p * Real.log z) (hD : 1 ≤ D) (hβ : 0 ≤ β) (hK1 : 0 ≤ K1)
    (hK : ∀ γ, 0 ≤ γ → γ ≤ 2 * β → ∑ T ∈ (univ : Finset (Finset ι)).filter (fun T => T ≠ ∅),
        |tr_a p T| * tr_prodP p T ^ γ * tr_phiInv p T ≤ K1) (hT : 0 < T)
    (hεG : Real.exp (Fintype.card κ * Real.log D / ((z - 1) * Real.log z)) - 1 ≤ 1)
    (hmain : 2 * (D ^ 2 * 2 ^ Fintype.card κ) ^ 2 / T +
      Fintype.card κ * (2 * (2 * (1 + K1) ^ 2 * Real.exp (-(2 * β * Real.log D) +
          Fintype.card κ * (2 * β) * K1 / tr_B p) +
         2 * (2 * Real.log D / ((z - 1) * Real.log z)) ^ 2) +
        2 * (D ^ 2 * 2 ^ Fintype.card κ) ^ 2 / T) <
      (1 - (Real.exp (Fintype.card κ * Real.log D / ((z - 1) * Real.log z)) - 1)) *
        (1 - 4 * (Fintype.card κ : ℝ) ^ 2 * ∑ i, 1 / ((p i : ℝ) - 1) ^ 2
          - Real.exp (-(β * Real.log D) + Fintype.card κ * β * K1 / tr_B p))) :
    ∃ t < T, ∀ s, ∃ i, (t + 1) % p i = ρ i s := by
  by_contra hcon
  push Not at hcon
  set k := Fintype.card κ with hk
  set εG := Real.exp (k * Real.log D / ((z - 1) * Real.log z)) - 1 with hεGdef
  have hεG0 : 0 ≤ εG := by
    have hl0 : 0 < Real.log z := Real.log_pos hz
    have : 0 ≤ k * Real.log D / ((z - 1) * Real.log z) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hD))
        (mul_pos (by linarith) hl0).le
    have := Real.add_one_le_exp (k * Real.log D / ((z - 1) * Real.log z))
    linarith
  set A := ∑ T, tr_a p T ^ 2 * tr_phiInv p T with hA
  have hA1 : 1 ≤ A := tr_s_A_ge_one p hp
  have hAk : 1 ≤ A ^ k := one_le_pow₀ hA1
  set Y := 2 * (1 + K1) ^ 2 * Real.exp (-(2 * β * Real.log D) + k * (2 * β) * K1 / tr_B p) +
         2 * (2 * Real.log D / ((z - 1) * Real.log z)) ^ 2 with hY
  set e := 1 - 4 * (k : ℝ) ^ 2 * ∑ i, 1 / ((p i : ℝ) - 1) ^ 2
          - Real.exp (-(β * Real.log D) + k * β * K1 / tr_B p) with he
  set X := D ^ 2 * 2 ^ k with hX
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hXc : ∑ f : ι → Option κ, |tr_c p D f| * tr_N p f ≤ X :=
    tr_s_c_total (κ := κ) p hp hz hpz hB D hD
  have hX0 : 0 ≤ ∑ f : ι → Option κ, |tr_c p D f| * tr_N p f :=
    Finset.sum_nonneg (fun f _ => mul_nonneg (abs_nonneg _) (tr_s_N_nonneg p f))
  -- lower bound for S1
  set S1 := ∑ t ∈ range T, (∑ f, tr_c p D f * tr_Psi p ρ f (t + 1)) ^ 2 with hS1
  have hQ := tr_s_avg_quad p ρ hp hinj (tr_c p D) T
  have hG := tr_s_gram p ρ hp hρ (tr_c p D)
  have hrow : ∑ f, tr_c p D f ^ 2 * (∑ g, |tr_M p ρ f g| - tr_W p f) ≤
      εG * ∑ f : ι → Option κ, tr_c p D f ^ 2 * tr_W p f := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun f _ => ?_)
    by_cases hc : tr_c p D f = 0
    · simp [hc]
    have hN : tr_N p f ≤ D := by
      by_contra h; apply hc; simp [tr_c, h]
    have := tr_s_row_bound p ρ hp hρ hρi hz hpz f hN
    have hc2 : 0 ≤ tr_c p D f ^ 2 := sq_nonneg _
    calc tr_c p D f ^ 2 * (∑ g, |tr_M p ρ f g| - tr_W p f)
        ≤ tr_c p D f ^ 2 * (εG * tr_W p f) := mul_le_mul_of_nonneg_left this hc2
      _ = _ := by ring
  have hΔ := tr_s_Delta_lower (κ := κ) p hp hz hpz hB D β K1 (by linarith) hβ hK1
    (hK β hβ (by linarith))
  have hX2 : (∑ f : ι → Option κ, |tr_c p D f| * tr_N p f) ^ 2 ≤ X ^ 2 :=
    pow_le_pow_left₀ hX0 hXc 2
  have hS1low : (T : ℝ) * ((1 - εG) * (A ^ k * e)) - 2 * X ^ 2 ≤ S1 := by
    have h1 : (1 - εG) * (A ^ k * e) ≤ ∑ f, ∑ g, tr_c p D f * tr_c p D g * tr_M p ρ f g := by
      have hΔ' : (1 - εG) * (A ^ k * e) ≤
          (1 - εG) * ∑ f : ι → Option κ, tr_c p D f ^ 2 * tr_W p f :=
        mul_le_mul_of_nonneg_left hΔ (by linarith)
      have := abs_le.1 hG
      have e1 : (1 - εG) * ∑ f : ι → Option κ, tr_c p D f ^ 2 * tr_W p f =
          ∑ f : ι → Option κ, tr_c p D f ^ 2 * tr_W p f -
            εG * ∑ f : ι → Option κ, tr_c p D f ^ 2 * tr_W p f := by ring
      linarith
    have h2 := abs_le.1 hQ
    have h3 := mul_le_mul_of_nonneg_left h1 hTpos.le
    linarith
  -- upper bound for S1
  have hstep : ∀ t ∈ range T, (∑ f, tr_c p D f * tr_Psi p ρ f (t + 1)) ^ 2 ≤
      ∑ s, (∑ f', tr_cs p D s f' * tr_Psi p ρ f' (t + 1)) ^ 2 := by
    intro t ht
    obtain ⟨s, hs⟩ := hcon t (Finset.mem_range.1 ht)
    rw [tr_s_R_uncov p ρ hp D s (t + 1) hs]
    exact Finset.single_le_sum (f := fun s => (∑ f', tr_cs p D s f' * tr_Psi p ρ f' (t + 1)) ^ 2)
      (fun s _ => sq_nonneg _) (Finset.mem_univ s)
  have hper : ∀ s, ∑ t ∈ range T, (∑ f', tr_cs p D s f' * tr_Psi p ρ f' (t + 1)) ^ 2 ≤
      (T : ℝ) * (2 * (A ^ k * Y)) + 2 * X ^ 2 := by
    intro s
    have hQs := tr_s_avg_quad p ρ hp hinj (tr_cs p D s) T
    have hGs := tr_s_gram p ρ hp hρ (tr_cs p D s)
    have hrows : ∑ f, tr_cs p D s f ^ 2 * (∑ g, |tr_M p ρ f g| - tr_W p f) ≤
        εG * ∑ f, tr_cs p D s f ^ 2 * tr_W p f := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun f _ => ?_)
      by_cases hc : tr_cs p D s f = 0
      · simp [hc]
      have hN := tr_s_cs_ne p hp D s f hc
      have := tr_s_row_bound p ρ hp hρ hρi hz hpz f hN
      have hc2 : 0 ≤ tr_cs p D s f ^ 2 := sq_nonneg _
      calc tr_cs p D s f ^ 2 * (∑ g, |tr_M p ρ f g| - tr_W p f)
          ≤ tr_cs p D s f ^ 2 * (εG * tr_W p f) := mul_le_mul_of_nonneg_left this hc2
        _ = _ := by ring
    have hΔs := tr_s_Delta2 p hp hz hpz hB D β K1 hD hβ hK1 hK s
    have hΔs0 : 0 ≤ ∑ f, tr_cs p D s f ^ 2 * tr_W p f :=
      Finset.sum_nonneg (fun f _ => mul_nonneg (sq_nonneg _) (tr_s_W_nonneg p hp f))
    have hXs := tr_s_cs_abs_sum p hp D s
    have hXs0 : 0 ≤ ∑ f', |tr_cs p D s f'| * tr_N p f' :=
      Finset.sum_nonneg (fun f _ => mul_nonneg (abs_nonneg _) (tr_s_N_nonneg p f))
    have hXs2 : (∑ f', |tr_cs p D s f'| * tr_N p f') ^ 2 ≤ X ^ 2 :=
      pow_le_pow_left₀ hXs0 (le_trans hXs hXc) 2
    have hq1 : ∑ f, ∑ g, tr_cs p D s f * tr_cs p D s g * tr_M p ρ f g ≤ 2 * (A ^ k * Y) := by
      have := abs_le.1 hGs
      have hm1 : εG * ∑ f, tr_cs p D s f ^ 2 * tr_W p f ≤ 1 * ∑ f, tr_cs p D s f ^ 2 * tr_W p f :=
        mul_le_mul_of_nonneg_right hεG hΔs0
      linarith
    have h2 := abs_le.1 hQs
    have h3 := mul_le_mul_of_nonneg_left hq1 hTpos.le
    linarith
  have hS1up : S1 ≤ k * ((T : ℝ) * (2 * (A ^ k * Y)) + 2 * X ^ 2) := by
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_comm]
    refine le_trans (Finset.sum_le_sum (fun s _ => hper s)) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hk]
  -- contradiction
  have hmain' : 2 * X ^ 2 / T + k * (2 * Y + 2 * X ^ 2 / T) < (1 - εG) * e := hmain
  have hTA : 0 < (T : ℝ) * A ^ k := by positivity
  have hm := mul_lt_mul_of_pos_left hmain' hTA
  have hXX : 2 * X ^ 2 ≤ (T : ℝ) * A ^ k * (2 * X ^ 2 / T) := by
    rw [show (T : ℝ) * A ^ k * (2 * X ^ 2 / T) = A ^ k * (2 * X ^ 2) by field_simp]
    nlinarith [sq_nonneg X]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hkX : (k : ℝ) * (2 * X ^ 2) ≤ k * ((T : ℝ) * A ^ k * (2 * X ^ 2 / T)) :=
    mul_le_mul_of_nonneg_left hXX hk0
  have hexp : (T : ℝ) * A ^ k * (2 * X ^ 2 / T + k * (2 * Y + 2 * X ^ 2 / T)) =
      (T : ℝ) * A ^ k * (2 * X ^ 2 / T) + k * ((T : ℝ) * A ^ k * (2 * X ^ 2 / T)) +
        k * ((T : ℝ) * (2 * (A ^ k * Y))) := by ring
  have hexp2 : (T : ℝ) * A ^ k * ((1 - εG) * e) = (T : ℝ) * ((1 - εG) * (A ^ k * e)) := by ring
  have hk2 : (k : ℝ) * ((T : ℝ) * (2 * (A ^ k * Y)) + 2 * X ^ 2) =
      k * ((T : ℝ) * (2 * (A ^ k * Y))) + k * (2 * X ^ 2) := by ring
  linarith [hS1low, hS1up, hm, hXX, hkX, hexp, hexp2, hk2]

end Final

/-! ### Proposition 1.2 -/

section Prop12

/-- divisibility from the residue condition -/
theorem tr_s_dvd_of_mod (q Q b s t : ℕ) (hq : q.Prime) (hQ : ¬ q ∣ Q)
    (ht : t % q = ((-((b + s : ℕ) : ZMod q)) * ((Q : ZMod q))⁻¹).val) :
    q ∣ b + Q * t + s := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hQ0 : (Q : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hQ
  have h1 : ((t : ℕ) : ZMod q) = (-((b + s : ℕ) : ZMod q)) * ((Q : ZMod q))⁻¹ := by
    rw [← ZMod.natCast_mod, ht, ZMod.natCast_zmod_val]
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [h1]
  push_cast
  field_simp
  ring

theorem tr_s_rho_inj (q Q b H : ℕ) (hq : q.Prime) (hQ : ¬ q ∣ Q) (hH : H < q) (s s' : ℕ)
    (hs : s ≤ H) (hs' : s' ≤ H)
    (h : ((-((b + s : ℕ) : ZMod q)) * ((Q : ZMod q))⁻¹).val =
      ((-((b + s' : ℕ) : ZMod q)) * ((Q : ZMod q))⁻¹).val) : s = s' := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hQ0 : (Q : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hQ
  have h1 := ZMod.val_injective q h
  have h2 : ((b + s : ℕ) : ZMod q) = ((b + s' : ℕ) : ZMod q) := by
    have := congrArg (fun v => -v * (Q : ZMod q)) h1
    simp only [neg_mul, neg_neg] at this
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀ hQ0, mul_one, mul_one] at this
    exact this
  push_cast at h2
  have h3 : ((s : ℕ) : ZMod q) = ((s' : ℕ) : ZMod q) := add_left_cancel h2
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
  exact h3

theorem tr_s_cube_lt (x : ℝ) (n : ℕ) (hn : 3 ≤ n) (hx1 : 1 ≤ x) (hxn : x < n + 1) :
    x * Real.log x ^ 2 < (n : ℝ) ^ 4 := by
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hl : Real.log x < x := lt_of_le_of_lt (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : Real.log x ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hl0 hl.le 2
  have h2 : x * Real.log x ^ 2 ≤ x ^ 3 := by nlinarith
  have h3 : x ^ 3 < ((n : ℝ) + 1) ^ 3 := pow_lt_pow_left₀ hxn (by linarith) (by norm_num)
  have h4 : ((n : ℝ) + 1) ^ 3 ≤ (n : ℝ) ^ 4 := by nlinarith [sq_nonneg ((n : ℝ) - 3)]
  linarith

theorem tr_s_primes_sum (n Y : ℕ) (hY : Y = ⌊Real.exp (Real.sqrt n)⌋₊) (C : ℝ)
    (hM : |∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, (1 : ℝ) / p - Real.log (Real.log Y)| ≤ C) :
    ∑ q ∈ tr_primes n, 1 / (q : ℝ) ≤ Real.log (Real.log Y) + C := by
  have hsub : tr_primes n ⊆ (Finset.range (Y + 1)).filter Nat.Prime := by
    intro q hq
    rw [tr_primes, Finset.mem_filter, Finset.mem_Ioc] at hq
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hq.2⟩
  have h1 : ∑ q ∈ tr_primes n, 1 / (q : ℝ) ≤
      ∑ q ∈ (Finset.range (Y + 1)).filter Nat.Prime, 1 / (q : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
  have := (abs_le.1 hM).2
  linarith

theorem tr_prop12 :
    ∃ δ : ℝ, 0 < δ ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ H : ℕ, x < H → (H : ℝ) ≤ x * Real.log x ^ 2 →
    ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 H → (S.card : ℝ) ≤ δ * x →
    ∀ b : ℕ, b < primorial ⌊x⌋₊ →
    ∃ t : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ Real.exp x ∧ ∀ s ∈ S, ¬ (b + primorial ⌊x⌋₊ * t + s).Prime := by
  obtain ⟨b0, K1, hb0, hK1, n1, hcoef⟩ := tr_coef_bounds
  obtain ⟨C, hC⟩ := tr_mertens2
  obtain ⟨N, hN⟩ := tr_num b0 K1 (max C 0) hb0 hK1 (le_max_right _ _)
  obtain ⟨Nθ, hNθ⟩ := tr_n_theta
  set δ := min (1 / 10) (b0 / (64 * (K1 + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  refine ⟨δ, hδ0, (N + n1 + Nθ + ⌈Real.exp (1 / b0)⌉₊ + 100 : ℕ), ?_⟩
  intro x hx H hxH hHx S hS hSc b _hb
  set n := ⌊x⌋₊ with hn
  have hx0 : (0 : ℝ) ≤ x := le_trans (Nat.cast_nonneg _) hx
  have hnM : N + n1 + Nθ + ⌈Real.exp (1 / b0)⌉₊ + 100 ≤ n := Nat.le_floor hx
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hn3 : 3 ≤ n := by omega
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast (show 100 ≤ n by omega)
  have hx1 : 1 ≤ x := by linarith
  -- the data
  set P := tr_primes n with hP
  set Y := ⌊Real.exp (Real.sqrt n)⌋₊ with hYdef
  set Q := primorial n with hQ
  let p : P → ℕ := fun i => (i : ℕ)
  have hmemP : ∀ q ∈ P, q.Prime ∧ n ^ 4 < q ∧ q ≤ Y := by
    intro q hq
    rw [hP, tr_primes, Finset.mem_filter, Finset.mem_Ioc] at hq
    exact ⟨hq.2, hq.1.1, hq.1.2⟩
  have hp : ∀ i : P, (p i).Prime := fun i => (hmemP i.1 i.2).1
  have hpinj : Function.Injective p := Subtype.val_injective
  have hHn : H < n ^ 4 := by
    have := tr_s_cube_lt x n hn3 hx1 hxn
    have h' : (H : ℝ) < (n : ℝ) ^ 4 := lt_of_le_of_lt hHx this
    exact_mod_cast h'
  have hpH : ∀ i : P, H < p i := fun i => lt_trans hHn (hmemP i.1 i.2).2.1
  have hQd : ∀ i : P, ¬ p i ∣ Q := by
    intro i hd
    have := ((hp i).dvd_primorial_iff).1 hd
    have h2 : n ^ 4 < p i := (hmemP i.1 i.2).2.1
    have : n ≤ n ^ 4 := Nat.le_self_pow (by norm_num) n
    omega
  let ρ : P → S → ℕ := fun i s =>
    ((-((b + (s : ℕ) : ℕ) : ZMod (p i))) * ((Q : ZMod (p i)))⁻¹).val
  have hρ : ∀ i s, ρ i s < p i := by
    intro i s
    have : NeZero (p i) := ⟨(hp i).ne_zero⟩
    exact ZMod.val_lt _
  have hρi : ∀ i, Function.Injective (ρ i) := by
    intro i s s' h
    have hs := Finset.mem_Icc.1 (hS s.2)
    have hs' := Finset.mem_Icc.1 (hS s'.2)
    exact Subtype.ext (tr_s_rho_inj (p i) Q b H (hp i) (hQd i) (hpH i) s s' hs.2 hs'.2 h)
  -- parameters
  have hnn1 : n1 ≤ n := by omega
  obtain ⟨hBb, hKc⟩ := hcoef n hnn1
  set B := tr_B p with hBdef
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 1 / b0 ≤ Real.log n := by
    have h1 : Real.exp (1 / b0) ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega :
      ⌈Real.exp (1 / b0)⌉₊ ≤ n))
    calc 1 / b0 = Real.log (Real.exp (1 / b0)) := (Real.log_exp _).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos _) h1
  have hz : (1 : ℝ) < (n : ℝ) ^ 4 := one_lt_pow₀ (by linarith) (by norm_num)
  have hlogz : Real.log ((n : ℝ) ^ 4) = 4 * Real.log n := by
    rw [Real.log_pow]; push_cast; ring
  have hB : 1 ≤ B * Real.log ((n : ℝ) ^ 4) := by
    rw [hlogz]
    have h1 : b0 * (1 / b0) = 1 := by field_simp
    have h2 : 0 ≤ Real.log n := le_trans (by positivity) hlogn
    have h3 : b0 * (1 / b0) ≤ B * Real.log n :=
      mul_le_mul hBb hlogn (by positivity) (le_trans hb0.le hBb)
    nlinarith
  have hpz : ∀ i : P, (n : ℝ) ^ 4 < p i := by
    intro i; exact_mod_cast (hmemP i.1 i.2).2.1
  -- the size of Y
  have hsq1 : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hYle : (Y : ℝ) ≤ Real.exp (Real.sqrt n) := Nat.floor_le (Real.exp_pos _).le
  have hYge : Real.exp (Real.sqrt n) - 1 < Y := Nat.sub_one_lt_floor _
  have hexp1 : Real.exp (Real.sqrt n - 1) ≤ Real.exp (Real.sqrt n) - 1 := by
    have he : Real.exp (Real.sqrt n) = Real.exp (Real.sqrt n - 1) * Real.exp 1 := by
      rw [← Real.exp_add]; ring_nf
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h3 : 1 ≤ Real.exp (Real.sqrt n - 1) := Real.one_le_exp (by linarith)
    rw [he]; nlinarith
  have hYpos : (0 : ℝ) < Y := lt_of_le_of_lt (le_trans (Real.exp_pos _).le hexp1) hYge
  set L := Real.log (Y : ℝ) with hL
  have hL1 : L ≤ Real.sqrt n := by
    rw [hL, ← Real.log_exp (Real.sqrt n)]; exact Real.log_le_log hYpos hYle
  have hL2 : Real.sqrt n - 1 ≤ L := by
    rw [hL, ← Real.log_exp (Real.sqrt n - 1)]
    exact Real.log_le_log (Real.exp_pos _) (le_trans hexp1 hYge.le)
  have hLpos : 0 < L := by
    have : (2 : ℝ) ≤ Real.sqrt n := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  -- T
  set T := ⌊Real.exp x⌋₊ with hTdef
  have hTge : Real.exp n - 1 ≤ T := by
    have := Nat.sub_one_lt_floor (Real.exp x)
    have h2 : Real.exp n ≤ Real.exp x := Real.exp_le_exp.2 hnx
    linarith
  have hTpos : 0 < T := by
    have h1 : (1 : ℝ) < Real.exp n - 1 := by
      have := Real.add_one_le_exp (n : ℝ); linarith
    have : (1 : ℝ) < T := lt_of_lt_of_le h1 hTge
    exact_mod_cast (lt_trans zero_lt_one this)
  -- the prime sum
  have hS2 : ∑ i : P, 1 / ((p i : ℝ) - 1) ^ 2 ≤ 2 * (Real.sqrt n + max C 0) / ((n : ℝ) ^ 4 - 1) := by
    have hz1 : 0 < (n : ℝ) ^ 4 - 1 := by linarith
    have h1 : ∀ i : P, 1 / ((p i : ℝ) - 1) ^ 2 ≤ 2 / ((n : ℝ) ^ 4 - 1) * (1 / (p i : ℝ)) := by
      intro i
      have hpi := hpz i
      have hp2 : (2 : ℝ) ≤ p i := by exact_mod_cast (hp i).two_le
      rw [div_le_iff₀ (by nlinarith)]
      have : 0 < (p i : ℝ) := by linarith
      field_simp
      nlinarith
    refine le_trans (Finset.sum_le_sum (fun i _ => h1 i)) ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ i : P, 1 / (p i : ℝ) ≤ Real.sqrt n + max C 0 := by
      have e : ∑ i : P, 1 / (p i : ℝ) = ∑ q ∈ P, 1 / (q : ℝ) :=
        Finset.sum_coe_sort P (fun q => 1 / (q : ℝ))
      rw [e]
      have hY2 : 2 ≤ Y := by
        have : (1 : ℝ) < Y := by
          have := Real.add_one_le_exp (Real.sqrt n - 1)
          linarith
        have : (1 : ℕ) < Y := by exact_mod_cast this
        omega
      have hps := tr_s_primes_sum n Y hYdef C (hC Y hY2)
      have hll : Real.log (Real.log (Y : ℝ)) ≤ Real.sqrt n := by
        rw [← hL]
        calc Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos hLpos
          _ ≤ Real.sqrt n := by linarith
      have : C ≤ max C 0 := le_max_left _ _
      linarith
    have h2 : 0 ≤ 2 / ((n : ℝ) ^ 4 - 1) := by positivity
    calc 2 / ((n : ℝ) ^ 4 - 1) * ∑ i : P, 1 / (p i : ℝ)
        ≤ 2 / ((n : ℝ) ^ 4 - 1) * (Real.sqrt n + max C 0) := mul_le_mul_of_nonneg_left hsum h2
      _ = _ := by ring
  have hS20 : 0 ≤ ∑ i : P, 1 / ((p i : ℝ) - 1) ^ 2 := Finset.sum_nonneg (fun i _ => div_nonneg zero_le_one (sq_nonneg _))
  have hk : (Fintype.card S : ℝ) ≤ δ * ((n : ℝ) + 1) := by
    rw [Fintype.card_coe]
    calc (S.card : ℝ) ≤ δ * x := hSc
      _ ≤ δ * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left hxn.le hδ0.le
  have hNn : N ≤ n := by omega
  obtain ⟨hεG, hmain⟩ := hN n hNn (Fintype.card S) T L B _ hk hL2 hL1 hBb hS20 hS2 hTge
  -- apply the abstract theorem
  have hK : ∀ γ, 0 ≤ γ → γ ≤ 2 * (1 / L) → ∑ T ∈ (Finset.univ : Finset (Finset P)).filter
      (fun T => T ≠ ∅), |tr_a p T| * tr_prodP p T ^ γ * tr_phiInv p T ≤ K1 := by
    intro γ hγ hγ2
    have h' : γ ≤ 2 / L := by rw [div_eq_mul_one_div]; exact hγ2
    exact hKc γ hγ h'
  obtain ⟨t, htT, hcov⟩ := tr_abstract p ρ hp hpinj hρ hρi ((n : ℝ) ^ 4) (Real.exp (n / 8))
    (1 / L) K1 T hz hpz hB (Real.one_le_exp (by positivity)) (by positivity) hK1 hK hTpos
    hεG hmain
  -- conclude
  have hQY : (Y : ℝ) < Q := by
    have h1 := hNθ n (by omega)
    have h2 := Chebyshev.theta_ge n
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h2
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast primorial_pos n
    have h3 : Real.sqrt n < Real.log Q := by rw [hQ]; linarith
    calc (Y : ℝ) ≤ Real.exp (Real.sqrt n) := hYle
      _ < Real.exp (Real.log Q) := Real.exp_lt_exp.2 h3
      _ = Q := Real.exp_log hQpos
  refine ⟨t + 1, by omega, ?_, ?_⟩
  · have h1 : ((t + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast htT
    exact le_trans h1 (Nat.floor_le (Real.exp_pos _).le)
  · intro s hs hprime
    obtain ⟨i, hi⟩ := hcov ⟨s, hs⟩
    have hd := tr_s_dvd_of_mod (p i) Q b s (t + 1) (hp i) (hQd i) hi
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime (p i) hd) with h1 | h1
    · exact (hp i).one_lt.ne' h1
    · have hpY : (p i : ℝ) ≤ Y := by exact_mod_cast (hmemP i.1 i.2).2.2
      have hQle : Q ≤ b + Q * (t + 1) + s := by
        have : Q ≤ Q * (t + 1) := Nat.le_mul_of_pos_right Q (by omega)
        omega
      have : (Q : ℝ) ≤ (p i : ℝ) := by rw [h1]; exact_mod_cast hQle
      linarith

end Prop12

end Translates

/-- Proposition 1.2 (short translates). -/
lemma rk_prop12_holds : rk_Prop12 := tr_prop12

end OMAErdos4

theorem OMA.solution : type_of% @Erdos4.erdos_4 :=
  OMAErdos4.rk_main OMAErdos4.rk_prop12_holds
