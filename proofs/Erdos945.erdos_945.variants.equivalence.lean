import FormalConjectures.ErdosProblems.«945»

-- Problem: Erdős Problem 945 — equivalence
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/945.lean:74 (declaration Erdos945.erdos_945.variants.equivalence)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Write `S x` for the set of `k` such that some run `n+1, ..., n+k ≤ x` has pairwise distinct
divisor counts, so that `F x = sSup (S x)`.

* `Erdos945Constant → Erdos945Prop`. Suppose every interval `[x, x + (log x)^C]` with `x ≥ X`
  (and `X ≥ 1`) contains two integers with the same divisor count. If a run `n+1, ..., n+k ≤ x`
  had `k > X + (log x)^C`, the interval starting at `x' = max (n+1) X` would lie inside the run,
  contradicting injectivity. So `F x ≤ X + (log x)^C ≤ (log x)^(C+1)` once `log x ≥ X + 1`.

* `Erdos945Prop → Erdos945Constant`. Suppose `F y ≤ (log y)^c` for large `y`, and take
  `C = c + 2`. If the integers of `[x, x + (log x)^C]` had distinct divisor counts, they would
  form a run of length `k = ⌊(log x)^C⌋` ending at `y ≤ 2 x^C`, so that
  `(log x)^C - 1 < k ≤ F y ≤ (log y)^c ≤ ((C+1) log x)^c`, which fails once `log x` is large.
-/

open Filter Real

/-- A run with distinct divisor counts is short, if all intervals `[x, x + (log x)^C]` beyond
`X` contain two integers with the same divisor count. -/
theorem OMA.e945_run_le {C X : ℝ} (hC : 0 < C) (hX1 : 1 ≤ X)
    (hX : ∀ x : ℝ, X ≤ x → ∃ a b : ℕ, a ≠ b ∧ (a : ℝ) ∈ Set.Icc x (x + Real.log x ^ C) ∧
      (b : ℝ) ∈ Set.Icc x (x + Real.log x ^ C) ∧ Erdos945.τ a = Erdos945.τ b)
    {x : ℝ} (hx : X ≤ x) {n k : ℕ} (hnk : (n : ℝ) + (k : ℝ) ≤ x)
    (hinj : Set.InjOn Erdos945.τ (Set.Ioc n (n + k))) :
    (k : ℝ) ≤ X + Real.log x ^ C := by
  have hx1 : (1 : ℝ) ≤ x := le_trans hX1 hx
  have hpow : 0 ≤ Real.log x ^ C := Real.rpow_nonneg (Real.log_nonneg hx1) C
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_contra hcon
  have hk : X + Real.log x ^ C < (k : ℝ) := not_le.mp hcon
  -- The interval starting at `x' = max (n + 1) X` lies inside the run.
  have hx'X : X ≤ max ((n : ℝ) + 1) X := le_max_right _ _
  have hx'n : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) X := le_max_left _ _
  have hx'x : max ((n : ℝ) + 1) X ≤ x := max_le (by linarith) hx
  have hx'1 : (1 : ℝ) ≤ max ((n : ℝ) + 1) X := le_trans hX1 hx'X
  have hx'le : max ((n : ℝ) + 1) X ≤ n + X := max_le (by linarith) (by linarith)
  have hpow' : Real.log (max ((n : ℝ) + 1) X) ^ C ≤ Real.log x ^ C :=
    Real.rpow_le_rpow (Real.log_nonneg hx'1) (Real.log_le_log (by linarith) hx'x) hC.le
  obtain ⟨a, b, hab, ha, hb, hτ⟩ := hX _ hx'X
  have key : ∀ m : ℕ,
      (m : ℝ) ∈ Set.Icc (max ((n : ℝ) + 1) X)
        (max ((n : ℝ) + 1) X + Real.log (max ((n : ℝ) + 1) X) ^ C) →
      m ∈ Set.Ioc n (n + k) := by
    intro m hm
    refine ⟨?_, ?_⟩
    · have h1 : (n : ℝ) < m := by linarith [hm.1]
      exact_mod_cast h1
    · have h2 : (m : ℝ) ≤ ((n + k : ℕ) : ℝ) := by push_cast; linarith [hm.2]
      exact_mod_cast h2
  exact hab (hinj (key a ha) (key b hb) hτ)

/-- The resulting bound on `F`. -/
theorem OMA.e945_F_le {C X : ℝ} (hC : 0 < C) (hX1 : 1 ≤ X)
    (hX : ∀ x : ℝ, X ≤ x → ∃ a b : ℕ, a ≠ b ∧ (a : ℝ) ∈ Set.Icc x (x + Real.log x ^ C) ∧
      (b : ℝ) ∈ Set.Icc x (x + Real.log x ^ C) ∧ Erdos945.τ a = Erdos945.τ b)
    {x : ℝ} (hx : X ≤ x) :
    (Erdos945.F x : ℝ) ≤ X + Real.log x ^ C := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hne : {k : ℕ | ∃ n : ℕ, (n : ℝ) + (k : ℝ) ≤ x ∧
      Set.InjOn Erdos945.τ (Set.Ioc n (n + k))}.Nonempty :=
    ⟨0, 0, by simpa using hx0, by simp⟩
  have hbdd : BddAbove {k : ℕ | ∃ n : ℕ, (n : ℝ) + (k : ℝ) ≤ x ∧
      Set.InjOn Erdos945.τ (Set.Ioc n (n + k))} := by
    refine ⟨⌊x⌋₊, ?_⟩
    rintro k ⟨n, hnk, -⟩
    exact Nat.le_floor (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hmem : Erdos945.F x ∈ {k : ℕ | ∃ n : ℕ, (n : ℝ) + (k : ℝ) ≤ x ∧
      Set.InjOn Erdos945.τ (Set.Ioc n (n + k))} := Nat.sSup_mem hne hbdd
  obtain ⟨n, hnk, hinj⟩ := hmem
  exact OMA.e945_run_le hC hX1 hX hx hnk hinj

/-- If long intervals always contain a repeated divisor count, then `F x ≤ (log x)^O(1)`. -/
theorem OMA.e945_backward : Erdos945.Erdos945Constant → Erdos945.Erdos945Prop := by
  unfold Erdos945.Erdos945Constant Erdos945.Erdos945Prop
  rintro ⟨C, hC, h⟩
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp h
  have hX1 : (1 : ℝ) ≤ max X₀ 1 := le_max_right _ _
  have hXprop : ∀ x : ℝ, max X₀ 1 ≤ x → ∃ a b : ℕ, a ≠ b ∧
      (a : ℝ) ∈ Set.Icc x (x + Real.log x ^ C) ∧
      (b : ℝ) ∈ Set.Icc x (x + Real.log x ^ C) ∧ Erdos945.τ a = Erdos945.τ b :=
    fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  refine ⟨fun _ => C + 1, Asymptotics.isBigO_const_const _ one_ne_zero _, ?_⟩
  refine Filter.eventually_atTop.mpr
    ⟨max (max X₀ 1) (Real.exp (max X₀ 1 + 1)), fun x hx => ?_⟩
  have hxX : max X₀ 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp (max X₀ 1 + 1) ≤ x := le_trans (le_max_right _ _) hx
  have hL : max X₀ 1 + 1 ≤ Real.log x := by
    have h1 := Real.log_le_log (Real.exp_pos _) hxe
    rwa [Real.log_exp] at h1
  have hb := OMA.e945_F_le hC hX1 hXprop hxX
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hA : (1 : ℝ) ≤ Real.log x ^ C := Real.one_le_rpow hL1 hC.le
  have hsplit : Real.log x ^ (C + 1) = Real.log x ^ C * Real.log x := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  show (Erdos945.F x : ℝ) ≤ Real.log x ^ (C + 1)
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ Real.log x ^ C),
    mul_nonneg (sub_nonneg.mpr hA) (by linarith : (0 : ℝ) ≤ max X₀ 1)]

/-- If `F x ≤ (log x)^O(1)`, then long intervals always contain a repeated divisor count. -/
theorem OMA.e945_forward : Erdos945.Erdos945Prop → Erdos945.Erdos945Constant := by
  unfold Erdos945.Erdos945Prop Erdos945.Erdos945Constant
  rintro ⟨O, hO, hF⟩
  obtain ⟨c, hc⟩ := hO.bound
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.mp hc
  obtain ⟨Y₂, hY₂⟩ := Filter.eventually_atTop.mp hF
  have hc'0 : (0 : ℝ) ≤ max c 0 := le_max_right _ _
  have hM1 : (1 : ℝ) ≤ (max c 0 + 2 + 1) ^ max c 0 := Real.one_le_rpow (by linarith) hc'0
  refine ⟨max c 0 + 2, by linarith, Filter.eventually_atTop.mpr
    ⟨max (max (max Y₁ Y₂) (Real.exp 1) + 1) (Real.exp ((max c 0 + 2 + 1) ^ max c 0 + 2)),
      fun x hx => ?_⟩⟩
  have hxa : max (max Y₁ Y₂) (Real.exp 1) + 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxb : Real.exp ((max c 0 + 2 + 1) ^ max c 0 + 2) ≤ x := le_trans (le_max_right _ _) hx
  have hLM : (max c 0 + 2 + 1) ^ max c 0 + 2 ≤ Real.log x := by
    have h1 := Real.log_le_log (Real.exp_pos _) hxb
    rwa [Real.log_exp] at h1
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxb
  have hx1 : 1 ≤ x := by
    have h1 := Real.add_one_le_exp ((max c 0 + 2 + 1) ^ max c 0 + 2)
    linarith
  have hLC0 : 0 ≤ Real.log x ^ (max c 0 + 2) := Real.rpow_nonneg hLpos.le _
  have hn_le : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hn_lt : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
  have hk_le : ((⌊Real.log x ^ (max c 0 + 2)⌋₊ : ℕ) : ℝ) ≤ Real.log x ^ (max c 0 + 2) :=
    Nat.floor_le hLC0
  have hk_lt : Real.log x ^ (max c 0 + 2) < ((⌊Real.log x ^ (max c 0 + 2)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  by_contra hno
  -- Otherwise the integers of the interval form a run with distinct divisor counts.
  have hinj : Set.InjOn Erdos945.τ
      (Set.Ioc ⌊x⌋₊ (⌊x⌋₊ + ⌊Real.log x ^ (max c 0 + 2)⌋₊)) := by
    intro a ha b hb hτ
    by_contra hab
    apply hno
    have mem : ∀ m : ℕ, m ∈ Set.Ioc ⌊x⌋₊ (⌊x⌋₊ + ⌊Real.log x ^ (max c 0 + 2)⌋₊) →
        (m : ℝ) ∈ Set.Icc x (x + Real.log x ^ (max c 0 + 2)) := by
      intro m hm
      have h1 : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hm.1
      have h2 : (m : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) + ((⌊Real.log x ^ (max c 0 + 2)⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast hm.2
      exact ⟨by linarith, by linarith⟩
    exact ⟨a, b, hab, mem a ha, mem b hb, hτ⟩
  -- Hence `k ≤ F y`, where `y = ⌊x⌋ + k` is the end of the run.
  let y : ℝ := ((⌊x⌋₊ : ℕ) : ℝ) + ((⌊Real.log x ^ (max c 0 + 2)⌋₊ : ℕ) : ℝ)
  have hy_ge : x - 1 ≤ y := by
    dsimp only [y]
    linarith [Nat.cast_nonneg (α := ℝ) ⌊Real.log x ^ (max c 0 + 2)⌋₊]
  have hbdd : BddAbove {k : ℕ | ∃ n : ℕ, (n : ℝ) + (k : ℝ) ≤
      y ∧
      Set.InjOn Erdos945.τ (Set.Ioc n (n + k))} := by
    refine ⟨⌊y⌋₊, ?_⟩
    rintro k ⟨n, hnk, -⟩
    exact Nat.le_floor (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hkF : ⌊Real.log x ^ (max c 0 + 2)⌋₊ ≤
      Erdos945.F y :=
    le_csSup hbdd ⟨⌊x⌋₊, le_refl _, hinj⟩
  have hkF' : ((⌊Real.log x ^ (max c 0 + 2)⌋₊ : ℕ) : ℝ) ≤
      (Erdos945.F y : ℝ) := by
    exact_mod_cast hkF
  -- `y` is large enough for both hypotheses to apply.
  have hyY1 : Y₁ ≤ y := by
    linarith [le_max_left Y₁ Y₂, le_max_left (max Y₁ Y₂) (Real.exp 1)]
  have hyY2 : Y₂ ≤ y := by
    linarith [le_max_right Y₁ Y₂, le_max_left (max Y₁ Y₂) (Real.exp 1)]
  have hye : Real.exp 1 ≤ y := by
    linarith [le_max_right (max Y₁ Y₂) (Real.exp 1)]
  have hypos : 0 < y :=
    lt_of_lt_of_le (Real.exp_pos 1) hye
  have hlogy1 : 1 ≤ Real.log y := by
    have h1 := Real.log_le_log (Real.exp_pos 1) hye
    rwa [Real.log_exp] at h1
  have hO' : O y ≤ max c 0 := by
    have h1 := hY₁ _ hyY1
    simp only [Pi.one_apply, norm_one, mul_one, Real.norm_eq_abs] at h1
    exact le_trans (le_trans (le_abs_self _) h1) (le_max_left _ _)
  have hFy : (Erdos945.F y : ℝ) ≤
      Real.log y ^ max c 0 :=
    le_trans (hY₂ _ hyY2) (Real.rpow_le_rpow_of_exponent_le hlogy1 hO')
  -- But `log y ≤ (C + 1) * log x`, because `y ≤ 2 * x ^ C`.
  have hLx : Real.log x ≤ x := by
    have h1 := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hLCx : Real.log x ^ (max c 0 + 2) ≤ x ^ (max c 0 + 2) :=
    Real.rpow_le_rpow hLpos.le hLx (by linarith)
  have hxxC : x ≤ x ^ (max c 0 + 2) := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : (1 : ℝ) ≤ max c 0 + 2)
    rwa [Real.rpow_one] at h1
  have hxCpos : 0 < x ^ (max c 0 + 2) := Real.rpow_pos_of_pos hxpos _
  have hlogy : Real.log y ≤
      (max c 0 + 2 + 1) * Real.log x := by
    have h1 : Real.log y ≤
        Real.log (2 * x ^ (max c 0 + 2)) := Real.log_le_log hypos (by dsimp only [y]; linarith)
    have h2 : Real.log (2 * x ^ (max c 0 + 2)) = Real.log 2 + (max c 0 + 2) * Real.log x := by
      rw [Real.log_mul (by norm_num) hxCpos.ne', Real.log_rpow hxpos]
    have h3 : Real.log 2 ≤ 1 := by
      have h4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hpow1 : Real.log y ^ max c 0 ≤
      ((max c 0 + 2 + 1) * Real.log x) ^ max c 0 :=
    Real.rpow_le_rpow (by linarith) hlogy hc'0
  have hpow2 : ((max c 0 + 2 + 1) * Real.log x) ^ max c 0 =
      (max c 0 + 2 + 1) ^ max c 0 * Real.log x ^ max c 0 :=
    Real.mul_rpow (by linarith) hLpos.le
  -- Compare with `(log x)^C = (log x)^c * (log x)^2`.
  have hA : (1 : ℝ) ≤ Real.log x ^ max c 0 := Real.one_le_rpow hL1 hc'0
  have hsplit : Real.log x ^ (max c 0 + 2) = Real.log x ^ max c 0 * Real.log x ^ 2 := by
    rw [Real.rpow_add hLpos, Real.rpow_two]
  have hL2 : (max c 0 + 2 + 1) ^ max c 0 + 2 ≤ Real.log x ^ 2 := by nlinarith
  have h5 : Real.log x ^ max c 0 * Real.log x ^ 2 <
      (max c 0 + 2 + 1) ^ max c 0 * Real.log x ^ max c 0 + 1 := by
    calc Real.log x ^ max c 0 * Real.log x ^ 2
        = Real.log x ^ (max c 0 + 2) := hsplit.symm
      _ < ((⌊Real.log x ^ (max c 0 + 2)⌋₊ : ℕ) : ℝ) + 1 := hk_lt
      _ ≤ (max c 0 + 2 + 1) ^ max c 0 * Real.log x ^ max c 0 + 1 := by linarith
  have h6 := mul_le_mul_of_nonneg_left hL2 (by linarith : (0 : ℝ) ≤ Real.log x ^ max c 0)
  nlinarith

theorem OMA.solution : type_of% @Erdos945.erdos_945.variants.equivalence :=
  ⟨OMA.e945_forward, OMA.e945_backward⟩
