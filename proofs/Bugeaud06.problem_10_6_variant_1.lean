import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_6

-- Problem: Bugeaud Collection of Conjectures and Open Questions: Rapidly Increasing Sequences Dense Modulo One — problem 10 6 variant 1
-- Upstream: formal-conjectures FormalConjectures/Books/BugeaudDistributionModuloOne/Problem10_6.lean:250 (declaration Bugeaud06.problem_10_6_variant_1)
-- Credit: @sho-404 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Witness: the increasing enumeration of S = {a * 2^t : 1 ≤ a ≤ ⌊log t⌋ + 1}.

namespace OMA

open Filter

/-- The multiplier bound at exponent `t`. -/
noncomputable def A (t : ℕ) : ℕ := ⌊Real.log t⌋₊ + 1

/-- Membership predicate of the witness set. -/
def P (x : ℕ) : Prop := ∃ a t : ℕ, 1 ≤ a ∧ a ≤ A t ∧ x = a * 2 ^ t

theorem A_mono : Monotone A := by
  intro s t h
  unfold A
  apply Nat.add_le_add_right
  apply Nat.floor_le_floor
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simpa using Real.log_natCast_nonneg t
  · exact Real.log_le_log (by exact_mod_cast hs) (by exact_mod_cast h)

theorem pow_mem (t : ℕ) : P (2 ^ t) := ⟨1, t, le_rfl, by unfold A; omega, by ring⟩

theorem P_infinite : (Set.ofPred P).Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun t : ℕ => 2 ^ t)
    (Nat.pow_right_injective le_rfl) pow_mem

/-- The witness sequence. -/
noncomputable def m (n : ℕ) : ℕ := Nat.nth P n

theorem m_mem (n : ℕ) : P (m n) := Nat.nth_mem_of_infinite P_infinite n

theorem m_strictMono : StrictMono m := Nat.nth_strictMono P_infinite

theorem m_le_pow (n : ℕ) : m n ≤ 2 ^ n := by
  induction n with
  | zero =>
    unfold m
    rw [Nat.nth_zero]
    exact Nat.sInf_le (pow_mem 0)
  | succ n ih =>
    by_contra h
    push Not at h
    have h1 : 2 ^ (n + 1) ≤ m n := Nat.le_nth_of_lt_nth_succ h (pow_mem (n + 1))
    have h2 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self n)
    omega

/-- Any two elements `x < y` of the set satisfy `x ≤ A t * (y - x)`. -/
theorem gap {a t b u : ℕ} (hat : a ≤ A t) (hbu : b ≤ A u)
    (h : a * 2 ^ t < b * 2 ^ u) : a * 2 ^ t ≤ A t * (b * 2 ^ u - a * 2 ^ t) := by
  rcases le_total t u with htu | hut
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le htu
    have h' : a * 2 ^ t < (b * 2 ^ e) * 2 ^ t := by rw [pow_add] at h; nlinarith
    have h1 : a < b * 2 ^ e := Nat.lt_of_mul_lt_mul_right h'
    have h2 : (a + 1) * 2 ^ t ≤ (b * 2 ^ e) * 2 ^ t := Nat.mul_le_mul_right _ h1
    have h3 : b * 2 ^ (t + e) = (b * 2 ^ e) * 2 ^ t := by rw [pow_add]; ring
    have h4 : 2 ^ t ≤ b * 2 ^ (t + e) - a * 2 ^ t := by
      rw [h3]; rw [Nat.add_mul] at h2; omega
    calc a * 2 ^ t ≤ A t * 2 ^ t := Nat.mul_le_mul_right _ hat
      _ ≤ A t * (b * 2 ^ (t + e) - a * 2 ^ t) := Nat.mul_le_mul_left _ h4
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hut
    have h3 : a * 2 ^ (u + e) = (a * 2 ^ e) * 2 ^ u := by rw [pow_add]; ring
    have h' : (a * 2 ^ e) * 2 ^ u < b * 2 ^ u := by rw [← h3]; exact h
    have h1 : a * 2 ^ e < b := Nat.lt_of_mul_lt_mul_right h'
    have h2 : (a * 2 ^ e + 1) * 2 ^ u ≤ b * 2 ^ u := Nat.mul_le_mul_right _ h1
    have h4 : 2 ^ u ≤ b * 2 ^ u - a * 2 ^ (u + e) := by
      rw [h3]; rw [Nat.add_mul] at h2; omega
    have hAA : A u ≤ A (u + e) := A_mono (Nat.le_add_right u e)
    calc a * 2 ^ (u + e) ≤ b * 2 ^ u := h.le
      _ ≤ A (u + e) * 2 ^ u := Nat.mul_le_mul_right _ (hbu.trans hAA)
      _ ≤ A (u + e) * (b * 2 ^ u - a * 2 ^ (u + e)) := Nat.mul_le_mul_left _ h4

theorem m_sublac : Bugeaud06.IsGenuinelySublacunary m := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 3] with n hn
  obtain ⟨a, t, ha, hat, hx⟩ := m_mem n
  obtain ⟨b, u, hb, hbu, hy⟩ := m_mem (n + 1)
  have hlt : m n < m (n + 1) := m_strictMono (Nat.lt_succ_self n)
  have hg := gap hat hbu (by rw [← hx, ← hy]; exact hlt)
  rw [← hx, ← hy] at hg
  have htn : t ≤ n := by
    have h1 : 2 ^ t ≤ m n := by rw [hx]; exact Nat.le_mul_of_pos_left _ ha
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans (m_le_pow n))
  have hA : (A t : ℝ) ≤ Real.log n + 1 := by
    have h1 : A t ≤ A n := A_mono htn
    have h2 : (A n : ℝ) ≤ Real.log n + 1 := by
      unfold A
      push_cast
      linarith [Nat.floor_le (Real.log_natCast_nonneg n)]
    exact le_trans (by exact_mod_cast h1) h2
  have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : (1 : ℝ) ≤ Real.log n :=
    (Real.le_log_iff_exp_le (by linarith)).2 (by linarith [Real.exp_one_lt_d9])
  have hpos : 0 < m n := by rw [hx]; positivity
  have hx0 : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hpos
  have hgR : (m n : ℝ) ≤ A t * ((m (n + 1) : ℝ) - m n) := by
    rw [← Nat.cast_sub hlt.le]
    exact_mod_cast hg
  have hd0 : (0 : ℝ) ≤ (m (n + 1) : ℝ) - m n := by
    have : (m n : ℝ) < m (n + 1) := by exact_mod_cast hlt
    linarith
  have h5 : (A t : ℝ) * ((m (n + 1) : ℝ) - m n) ≤ (Real.log n + 1) * ((m (n + 1) : ℝ) - m n) :=
    mul_le_mul_of_nonneg_right hA hd0
  have h6 : (1 : ℝ) * ((m (n + 1) : ℝ) - m n) ≤ Real.log n * ((m (n + 1) : ℝ) - m n) :=
    mul_le_mul_of_nonneg_right hlog hd0
  have h7 : (1 / 2 : ℝ) / Real.log n * m n ≤ (m (n + 1) : ℝ) - m n := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  rw [le_div_iff₀ hx0]
  linarith

/-- Multiples of a step `d` in `[ε/2, ε)` come within `ε` of any target modulo one. -/
theorem step {d ε : ℝ} (hd : ε / 2 ≤ d) (hdε : d < ε) (hε1 : ε ≤ 1) (hε : 0 < ε) (y : ℝ) :
    ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ 4 / ε ∧ ∃ k : ℤ, |j * d - y - k| < ε := by
  have hd0 : 0 < d := by linarith
  have hz1 : 1 ≤ Int.fract y + 1 := by linarith [Int.fract_nonneg y]
  have hz2 : Int.fract y + 1 < 2 := by linarith [Int.fract_lt_one y]
  have hq0 : 0 ≤ (Int.fract y + 1) / d := div_nonneg (by linarith) hd0.le
  have hj1 : (⌊(Int.fract y + 1) / d⌋₊ : ℝ) ≤ (Int.fract y + 1) / d := Nat.floor_le hq0
  have hj2 : (Int.fract y + 1) / d < (⌊(Int.fract y + 1) / d⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [le_div_iff₀ hd0] at hj1
  rw [div_lt_iff₀ hd0] at hj2
  refine ⟨⌊(Int.fract y + 1) / d⌋₊, ?_, ?_, 1 - ⌊y⌋, ?_⟩
  · apply Nat.le_floor
    rw [le_div_iff₀ hd0]
    push_cast
    linarith
  · have h1 : (Int.fract y + 1) / d ≤ 4 / ε := by
      rw [div_le_div_iff₀ hd0 hε]
      nlinarith
    exact (Nat.floor_le hq0).trans h1
  · have hy : (⌊y⌋ : ℝ) + Int.fract y = y := Int.floor_add_fract y
    push_cast
    rw [abs_lt]
    constructor <;> linarith

/-- The Diophantine core: the set comes within `ε` of every target modulo one. -/
theorem core (ξ : ℝ) (hξ : Irrational ξ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (y : ℝ) :
    ∃ x : ℕ, P x ∧ ∃ k : ℤ, |ξ * (x : ℝ) - y - k| < ε := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 / ε)
  have h4 : (4 : ℝ) ≤ 4 / ε := by rw [le_div_iff₀ hε]; linarith
  have hNε : 4 ≤ (N : ℝ) * ε := by rw [div_le_iff₀ hε] at hN; exact hN
  have hNpos : 0 < N := by exact_mod_cast (by linarith : (0 : ℝ) < N)
  obtain ⟨t0, ht0⟩ : ∃ t0, N * N ≤ A t0 := by
    refine ⟨⌈Real.exp ((N * N : ℕ) : ℝ)⌉₊, ?_⟩
    unfold A
    have hc : (0 : ℝ) < (⌈Real.exp ((N * N : ℕ) : ℝ)⌉₊ : ℝ) :=
      Nat.cast_pos.2 (Nat.ceil_pos.2 (Real.exp_pos _))
    have : (N * N : ℕ) ≤ ⌊Real.log (⌈Real.exp ((N * N : ℕ) : ℝ)⌉₊ : ℝ)⌋₊ := by
      apply Nat.le_floor
      rw [Real.le_log_iff_exp_le hc]
      exact Nat.le_ceil _
    omega
  obtain ⟨p, q, hq0, hqN, hpq⟩ := Real.exists_int_int_abs_mul_sub_le ((2 : ℝ) ^ t0 * ξ) hNpos
  lift q to ℕ using hq0.le
  have hq0' : 0 < q := by exact_mod_cast hq0
  have hqN' : q ≤ N := by exact_mod_cast hqN
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (q : ℝ) * ((2 : ℝ) ^ t0 * ξ) - p := ⟨_, rfl⟩
  have hγ0 : γ ≠ 0 := by
    have hirr : Irrational (((q : ℤ) : ℝ) * (((2 ^ t0 : ℕ) : ℝ) * ξ) - ((p : ℤ) : ℝ)) :=
      ((hξ.natCast_mul (m := 2 ^ t0) (by positivity)).intCast_mul
        (m := (q : ℤ)) (by exact_mod_cast hq0'.ne')).sub_intCast p
    intro h
    apply hirr.ne_zero
    rw [← h, hγ]
    push_cast
    ring
  have hγε : |γ| < ε := by
    have h1 : |γ| ≤ 1 / ((N : ℝ) + 1) := by rw [hγ]; exact_mod_cast hpq
    have h2 : 1 / ((N : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hγpos : 0 < |γ| := abs_pos.2 hγ0
  have hex : ∃ s : ℕ, ε / 2 ≤ 2 ^ s * |γ| := by
    obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (ε / 2 / |γ|) (one_lt_two)
    rw [div_lt_iff₀ hγpos] at hs
    exact ⟨s, hs.le⟩
  classical
  obtain ⟨s, hs1, hmin⟩ : ∃ s : ℕ, ε / 2 ≤ 2 ^ s * |γ| ∧ ∀ r < s, ¬ (ε / 2 ≤ 2 ^ r * |γ|) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr => Nat.find_min hex hr⟩
  have hs2 : 2 ^ s * |γ| < ε := by
    cases s with
    | zero => simpa using hγε
    | succ r =>
      have := hmin r (Nat.lt_succ_self r)
      push Not at this
      rw [pow_succ]
      linarith
  have key : ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ 4 / ε ∧ ∃ k : ℤ, |j * (2 ^ s * γ) - y - k| < ε := by
    rcases lt_or_gt_of_ne hγ0 with hneg | hpos
    · obtain ⟨j, hj1, hj2, k, hk⟩ := step hs1 hs2 hε1 hε (-y)
      refine ⟨j, hj1, hj2, -k, ?_⟩
      rw [abs_of_neg hneg] at hk
      rw [← abs_neg]
      convert hk using 2
      push_cast
      ring
    · obtain ⟨j, hj1, hj2, k, hk⟩ := step hs1 hs2 hε1 hε y
      refine ⟨j, hj1, hj2, k, ?_⟩
      rw [abs_of_pos hpos] at hk
      exact hk
  obtain ⟨j, hj1, hj2, k, hk⟩ := key
  have hjN : j ≤ N := by exact_mod_cast hj2.trans hN
  refine ⟨(j * q) * 2 ^ (t0 + s), ⟨j * q, t0 + s, Nat.mul_pos hj1 hq0', ?_, rfl⟩,
    k + j * 2 ^ s * p, ?_⟩
  · exact (Nat.mul_le_mul hjN hqN').trans (ht0.trans (A_mono (Nat.le_add_right t0 s)))
  · convert hk using 2
    rw [hγ]
    push_cast
    ring

theorem m_dense (ξ : ℝ) (hξ : Irrational ξ) :
    Dense (Set.range fun n => (↑(ξ * m n) : AddCircle (1 : ℝ))) := by
  rw [Metric.dense_iff]
  intro z r hr
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨x, hx, k, hk⟩ := core ξ hξ (lt_min hr one_pos) (min_le_right _ _) y
  obtain ⟨n, hn⟩ : ∃ n, m n = x := by
    have hmem : x ∈ Set.range (Nat.nth P) := by
      rw [Nat.range_nth_of_infinite P_infinite]
      exact hx
    exact hmem
  subst hn
  refine ⟨_, ?_, ⟨n, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hnorm : ‖((ξ * (m n : ℝ) - y : ℝ) : AddCircle (1 : ℝ))‖ ≤ |ξ * (m n : ℝ) - y - k| := by
    have h1 : ‖((ξ * (m n : ℝ) - y : ℝ) : UnitAddCircle)‖ = _ := UnitAddCircle.norm_eq
    exact h1.le.trans (round_le _ k)
  have h2 : ‖((ξ * (m n : ℝ) - y : ℝ) : AddCircle (1 : ℝ))‖ < r :=
    hnorm.trans_lt (hk.trans_le (min_le_left _ _))
  exact h2

end OMA

theorem OMA.solution : type_of% @Bugeaud06.problem_10_6_variant_1 :=
  ⟨OMA.m, OMA.m_strictMono, OMA.m_sublac, OMA.m_dense⟩
