import FormalConjectures.ErdosProblems.«480»

-- Problem: Erdős Problem 480 — chung graham best possible
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/480.lean:62 (declaration Erdos480.erdos_480.variants.chung_graham_best_possible)
-- Credit: @DomTheDeveloper (the owner of the agent is credited as the solver)
--
-- The extremal sequence is the one of Chung and Graham: write n = sum e_i G_i in the numeration
-- system of the even Fibonacci numbers G_i = F_{2i} (digits 0,1,2, no block 2 1...1 2) and put
-- x_n = (sum e_i / G_i) / c.  We prove n |x_{m+n} - x_m| >= 1/c for ALL m and n >= 1.
-- Proof: with tau = (3 - sqrt 5)/2 one has 1/G_i = sqrt5 * tau^i + tau^(2i)/G_i, so the difference
-- D of the digit sums splits as sqrt5 * B + R, B = n*tau - k (k an integer), |B| < 1, and R has the
-- sign of B (both are decided by the lowest differing digit).  The integer
-- N = n^2 - 3nk + k^2 = B * (sqrt5 * n + B) is nonzero, which gives n*sqrt5*|B| > 1 unless N = 1;
-- N = 1 forces n = G_j, B = tau^j, and then R >= tau^(2j)/G_j, which is exactly what is missing.

open Filter

/-- The even-indexed Fibonacci numbers. -/
def OMA.G (i : ℕ) : ℕ := Nat.fib (2 * i)

theorem OMA.G_zero : OMA.G 0 = 0 := by
  unfold OMA.G; simp

theorem OMA.G_one : OMA.G 1 = 1 := by
  unfold OMA.G; simp

theorem OMA.G_two : OMA.G 2 = 3 := by
  unfold OMA.G; decide

theorem OMA.G_rec (i : ℕ) : OMA.G (i + 2) + OMA.G i = 3 * OMA.G (i + 1) := by
  unfold OMA.G
  have e1 : 2 * (i + 2) = 2 * i + 2 + 2 := by ring
  have e2 : 2 * (i + 1) = 2 * i + 2 := by ring
  rw [e1, e2]
  have h1 : Nat.fib (2 * i + 2) = Nat.fib (2 * i) + Nat.fib (2 * i + 1) := Nat.fib_add_two
  have h2 : Nat.fib (2 * i + 1 + 2) = Nat.fib (2 * i + 1) + Nat.fib (2 * i + 1 + 1) :=
    Nat.fib_add_two
  have h3 : Nat.fib (2 * i + 2 + 2) = Nat.fib (2 * i + 2) + Nat.fib (2 * i + 2 + 1) :=
    Nat.fib_add_two
  have e3 : 2 * i + 1 + 2 = 2 * i + 2 + 1 := by ring
  have e4 : 2 * i + 1 + 1 = 2 * i + 2 := by ring
  rw [e3, e4] at h2
  omega

theorem OMA.G_le_succ (i : ℕ) : OMA.G i ≤ OMA.G (i + 1) := by
  unfold OMA.G
  exact Nat.fib_mono (by omega)

theorem OMA.G_pos (i : ℕ) : 0 < OMA.G (i + 1) := by
  unfold OMA.G
  exact Nat.fib_pos.mpr (by omega)

theorem OMA.G_double (i : ℕ) : 2 * OMA.G (i + 1) ≤ OMA.G (i + 2) := by
  have h := OMA.G_rec i
  have h2 := OMA.G_le_succ i
  omega

theorem OMA.G_ge_pow (k : ℕ) : 2 ^ k ≤ OMA.G (k + 1) := by
  induction k with
  | zero => simp [OMA.G_one]
  | succ k ih =>
    have h : 2 * OMA.G (k + 1) ≤ OMA.G (k + 1 + 1) := OMA.G_double k
    have e : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

theorem OMA.G_cast_pos (i : ℕ) : (0 : ℝ) < (OMA.G (i + 1) : ℝ) := by
  exact_mod_cast OMA.G_pos i

/-- The smaller root of y^2 = 3y - 1. -/
noncomputable def OMA.tau : ℝ := (3 - Real.sqrt 5) / 2

theorem OMA.sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem OMA.sqrt5_gt : (11 : ℝ) / 5 < Real.sqrt 5 := by
  have h := OMA.sqrt5_sq
  have h0 := Real.sqrt_nonneg 5
  nlinarith

theorem OMA.sqrt5_lt : Real.sqrt 5 < (9 : ℝ) / 4 := by
  have h := OMA.sqrt5_sq
  have h0 := Real.sqrt_nonneg 5
  nlinarith

theorem OMA.tau_sq : OMA.tau ^ 2 = 3 * OMA.tau - 1 := by
  unfold OMA.tau
  linear_combination (1 / 4 : ℝ) * OMA.sqrt5_sq

theorem OMA.tau_gt : (3 : ℝ) / 8 < OMA.tau := by
  unfold OMA.tau
  have := OMA.sqrt5_lt
  linarith

theorem OMA.tau_lt : OMA.tau < (2 : ℝ) / 5 := by
  unfold OMA.tau
  have := OMA.sqrt5_gt
  linarith

theorem OMA.tau_pos : 0 < OMA.tau := by
  have := OMA.tau_gt
  linarith

theorem OMA.sqrt5_eq : Real.sqrt 5 = 3 - 2 * OMA.tau := by
  unfold OMA.tau; ring

theorem OMA.pow_root (y : ℝ) (hy : y ^ 2 = 3 * y - 1) : ∀ i : ℕ,
    y ^ (i + 1) = (OMA.G (i + 1) : ℝ) * y - (OMA.G i : ℝ) ∧
      y ^ (i + 2) = (OMA.G (i + 2) : ℝ) * y - (OMA.G (i + 1) : ℝ) := by
  intro i
  induction i with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [OMA.G_one, OMA.G_zero]
    · rw [OMA.G_two, OMA.G_one]
      simp only [Nat.zero_add]
      push_cast
      linarith [hy]
  | succ i ih =>
    refine ⟨ih.2, ?_⟩
    have hrec : (OMA.G (i + 1 + 2) : ℝ) = 3 * (OMA.G (i + 2) : ℝ) - (OMA.G (i + 1) : ℝ) := by
      have h := OMA.G_rec (i + 1)
      have h' : (OMA.G (i + 1 + 2) : ℝ) + (OMA.G (i + 1) : ℝ) = 3 * (OMA.G (i + 1 + 1) : ℝ) := by
        exact_mod_cast h
      have e : OMA.G (i + 1 + 1) = OMA.G (i + 2) := rfl
      rw [e] at h'
      linarith
    have e : y ^ (i + 1 + 2) = y * y ^ (i + 2) := by ring
    have e2 : OMA.G (i + 1 + 1) = OMA.G (i + 2) := rfl
    rw [e, ih.2, hrec, e2]
    linear_combination (OMA.G (i + 2) : ℝ) * hy

theorem OMA.tau_pow (i : ℕ) :
    OMA.tau ^ (i + 1) = (OMA.G (i + 1) : ℝ) * OMA.tau - (OMA.G i : ℝ) :=
  (OMA.pow_root OMA.tau OMA.tau_sq i).1

theorem OMA.binet (i : ℕ) :
    Real.sqrt 5 * (OMA.G (i + 1) : ℝ) * OMA.tau ^ (i + 1) = 1 - OMA.tau ^ (2 * (i + 1)) := by
  have hs : (3 - OMA.tau) ^ 2 = 3 * (3 - OMA.tau) - 1 := by
    linear_combination OMA.tau_sq
  have h1 := (OMA.pow_root (3 - OMA.tau) hs i).1
  have h2 := OMA.tau_pow i
  have h3 : (3 - OMA.tau) * OMA.tau = 1 := by
    linear_combination (-1 : ℝ) * OMA.tau_sq
  have h4 : (3 - OMA.tau) ^ (i + 1) * OMA.tau ^ (i + 1) = 1 := by
    rw [← mul_pow, h3, one_pow]
  have h5 : OMA.tau ^ (2 * (i + 1)) = OMA.tau ^ (i + 1) * OMA.tau ^ (i + 1) := by ring
  have h6 : Real.sqrt 5 * (OMA.G (i + 1) : ℝ) = (3 - OMA.tau) ^ (i + 1) - OMA.tau ^ (i + 1) := by
    rw [h1, h2, OMA.sqrt5_eq]; ring
  rw [h6, h5]
  linear_combination h4

/-- The weights attached to the digit in position p (which belongs to G (p+1)). -/
noncomputable def OMA.wt (p : ℕ) : ℝ := OMA.tau ^ (p + 1)

noncomputable def OMA.wv (p : ℕ) : ℝ := 1 / (OMA.G (p + 1) : ℝ)

noncomputable def OMA.ww (p : ℕ) : ℝ := OMA.tau ^ (2 * (p + 1)) / (OMA.G (p + 1) : ℝ)

def OMA.wG (p : ℕ) : ℕ := OMA.G (p + 1)

def OMA.wK (p : ℕ) : ℕ := OMA.G p

theorem OMA.wt_pos (p : ℕ) : 0 < OMA.wt p := pow_pos OMA.tau_pos _

theorem OMA.wv_pos (p : ℕ) : 0 < OMA.wv p := by
  unfold OMA.wv
  exact div_pos one_pos (OMA.G_cast_pos p)

theorem OMA.ww_pos (p : ℕ) : 0 < OMA.ww p := by
  unfold OMA.ww
  exact div_pos (pow_pos OMA.tau_pos _) (OMA.G_cast_pos p)

theorem OMA.wv_eq (p : ℕ) : OMA.wv p = Real.sqrt 5 * OMA.wt p + OMA.ww p := by
  unfold OMA.wv OMA.wt OMA.ww
  have h := OMA.binet p
  have hG := OMA.G_cast_pos p
  field_simp
  linarith

theorem OMA.wv_succ_le (p : ℕ) : OMA.wv (p + 1) ≤ OMA.wv p := by
  unfold OMA.wv
  apply one_div_le_one_div_of_le (OMA.G_cast_pos p)
  exact_mod_cast OMA.G_le_succ (p + 1)

theorem OMA.ww_succ_le (p : ℕ) : OMA.ww (p + 1) ≤ OMA.ww p / 8 := by
  unfold OMA.ww
  have hG1 := OMA.G_cast_pos p
  have hG2 := OMA.G_cast_pos (p + 1)
  have hd : 2 * (OMA.G (p + 1) : ℝ) ≤ (OMA.G (p + 1 + 1) : ℝ) := by
    exact_mod_cast OMA.G_double p
  have ha : 0 < OMA.tau ^ (2 * (p + 1)) := pow_pos OMA.tau_pos _
  have ht : OMA.tau ^ 2 ≤ 1 / 4 := by
    have h1 := OMA.tau_lt
    have h2 := OMA.tau_pos
    nlinarith
  have e : OMA.tau ^ (2 * (p + 1 + 1)) = OMA.tau ^ (2 * (p + 1)) * OMA.tau ^ 2 := by ring
  rw [e, div_le_iff₀ hG2]
  have e2 : OMA.tau ^ (2 * (p + 1)) / (OMA.G (p + 1) : ℝ) / 8 * (OMA.G (p + 1 + 1) : ℝ)
      = OMA.tau ^ (2 * (p + 1)) * ((OMA.G (p + 1 + 1) : ℝ) / (8 * (OMA.G (p + 1) : ℝ))) := by
    field_simp
  rw [e2]
  apply mul_le_mul_of_nonneg_left _ ha.le
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem OMA.ww_anti (i j : ℕ) (h : i ≤ j) : OMA.ww j ≤ OMA.ww i := by
  induction j, h using Nat.le_induction with
  | base => exact le_refl _
  | succ j _ ih =>
    have h1 := OMA.ww_succ_le j
    have h2 := OMA.ww_pos j
    linarith

/-- Value of a digit list (low digit first, the head sits in position i) for a weight w. -/
noncomputable def OMA.val (w : ℕ → ℝ) : ℕ → List ℕ → ℝ
  | _, [] => 0
  | i, (x :: xs) => (x : ℝ) * w i + OMA.val w (i + 1) xs

def OMA.nval (g : ℕ → ℕ) : ℕ → List ℕ → ℕ
  | _, [] => 0
  | i, (x :: xs) => x * g i + OMA.nval g (i + 1) xs

theorem OMA.val_nil (w : ℕ → ℝ) (i : ℕ) : OMA.val w i [] = 0 := rfl

theorem OMA.val_cons (w : ℕ → ℝ) (i x : ℕ) (xs : List ℕ) :
    OMA.val w i (x :: xs) = (x : ℝ) * w i + OMA.val w (i + 1) xs := rfl

theorem OMA.nval_cast (g : ℕ → ℕ) : ∀ (l : List ℕ) (i : ℕ),
    ((OMA.nval g i l : ℕ) : ℝ) = OMA.val (fun t => (g t : ℝ)) i l := by
  intro l
  induction l with
  | nil => intro i; simp [OMA.nval, OMA.val]
  | cons x xs ih =>
    intro i
    simp only [OMA.nval, OMA.val]
    push_cast
    rw [ih (i + 1)]

theorem OMA.val_nonneg (w : ℕ → ℝ) (hw : ∀ t, 0 ≤ w t) : ∀ (l : List ℕ) (i : ℕ),
    0 ≤ OMA.val w i l := by
  intro l
  induction l with
  | nil => intro i; rw [OMA.val_nil]
  | cons x xs ih =>
    intro i
    rw [OMA.val_cons]
    have h1 := ih (i + 1)
    have h2 : 0 ≤ (x : ℝ) * w i := mul_nonneg (Nat.cast_nonneg x) (hw i)
    linarith

theorem OMA.val_wt : ∀ (l : List ℕ) (i : ℕ),
    OMA.val OMA.wt i l = OMA.tau * OMA.val (fun t => (OMA.wG t : ℝ)) i l
      - OMA.val (fun t => (OMA.wK t : ℝ)) i l := by
  intro l
  induction l with
  | nil => intro i; simp [OMA.val]
  | cons x xs ih =>
    intro i
    rw [OMA.val_cons, OMA.val_cons, OMA.val_cons, ih (i + 1)]
    have h := OMA.tau_pow i
    simp only [OMA.wt, OMA.wG, OMA.wK]
    rw [h]; ring

theorem OMA.val_wv : ∀ (l : List ℕ) (i : ℕ),
    OMA.val OMA.wv i l = Real.sqrt 5 * OMA.val OMA.wt i l + OMA.val OMA.ww i l := by
  intro l
  induction l with
  | nil => intro i; simp [OMA.val]
  | cons x xs ih =>
    intro i
    rw [OMA.val_cons, OMA.val_cons, OMA.val_cons, ih (i + 1), OMA.wv_eq i]
    ring

/-- The automaton recognising the admissible digit strings. State true means: the last digit
different from 1 was a 2. -/
def OMA.nxt (s : Bool) (x : ℕ) : Bool := if x = 0 then false else if x = 1 then s else true

def OMA.adm : Bool → List ℕ → Prop
  | _, [] => True
  | s, (x :: xs) => x ≤ 2 ∧ (x = 2 → s = false) ∧ OMA.adm (OMA.nxt s x) xs

def OMA.fin : Bool → List ℕ → Bool
  | s, [] => s
  | s, (x :: xs) => OMA.fin (OMA.nxt s x) xs

theorem OMA.adm_mono : ∀ (l : List ℕ), OMA.adm true l → OMA.adm false l := by
  intro l
  induction l with
  | nil => intro _; trivial
  | cons x xs ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, fun _ => rfl, ?_⟩
    have hx : x = 0 ∨ x = 1 := by
      rcases Nat.lt_or_ge x 2 with h | h
      · omega
      · exfalso
        have hx2 : x = 2 := by omega
        exact absurd (h2 hx2) (by decide)
    rcases hx with rfl | rfl
    · exact h3
    · exact ih h3

theorem OMA.adm_tail (s : Bool) (x : ℕ) (xs : List ℕ) (h : OMA.adm s (x :: xs)) :
    x ≤ 2 ∧ OMA.adm false xs := by
  obtain ⟨h1, _, h3⟩ := h
  refine ⟨h1, ?_⟩
  cases hn : OMA.nxt s x with
  | false => rw [hn] at h3; exact h3
  | true => rw [hn] at h3; exact OMA.adm_mono xs h3

theorem OMA.tb : ∀ (l : List ℕ) (i : ℕ),
    (OMA.adm false l → OMA.val OMA.wt i l < OMA.tau ^ i) ∧
    (OMA.adm true l → OMA.val OMA.wt i l < OMA.tau ^ i * (1 - OMA.tau)) := by
  intro l
  induction l with
  | nil =>
    intro i
    have hp : 0 < OMA.tau ^ i := pow_pos OMA.tau_pos i
    have hlt := OMA.tau_lt
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [OMA.val_nil]; exact hp
    · rw [OMA.val_nil]; exact mul_pos hp (by linarith)
  | cons x xs ih =>
    intro i
    obtain ⟨ihF, ihR⟩ := ih (i + 1)
    have hp : 0 < OMA.tau ^ i := pow_pos OMA.tau_pos i
    have hlt := OMA.tau_lt
    have hgt := OMA.tau_gt
    have hsq := OMA.tau_sq
    have hw : OMA.wt i = OMA.tau ^ i * OMA.tau := by unfold OMA.wt; ring
    have hpow : OMA.tau ^ (i + 1) = OMA.tau ^ i * OMA.tau := by ring
    have hprod : 0 < OMA.tau ^ i * OMA.tau := mul_pos hp OMA.tau_pos
    have e : OMA.tau ^ i * OMA.tau * (1 - OMA.tau)
        = OMA.tau ^ i * (1 - OMA.tau) - OMA.tau ^ i * OMA.tau := by
      linear_combination (-(OMA.tau ^ i)) * hsq
    rw [hpow] at ihF ihR
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := h
      rw [OMA.val_cons, hw]
      interval_cases x
      · have hT := ihF h3
        have h5 : OMA.tau ^ i * OMA.tau ≤ OMA.tau ^ i * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hp.le
        push_cast
        linarith
      · have hT := ihF h3
        have h5 : OMA.tau ^ i * OMA.tau ≤ OMA.tau ^ i * (1 / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hp.le
        push_cast
        linarith
      · have hT := ihR h3
        push_cast
        linarith
    · obtain ⟨h1, h2, h3⟩ := h
      rw [OMA.val_cons, hw]
      interval_cases x
      · have hT := ihF h3
        have h5 : OMA.tau ^ i * OMA.tau ≤ OMA.tau ^ i * (1 / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hp.le
        push_cast
        linarith
      · have hT := ihR h3
        push_cast
        linarith
      · exact absurd (h2 rfl) (by decide)

theorem OMA.wb : ∀ (l : List ℕ) (s : Bool) (i : ℕ), OMA.adm s l →
    OMA.val OMA.ww (i + 1) l ≤ 2 / 7 * OMA.ww i := by
  intro l
  induction l with
  | nil =>
    intro s i _
    rw [OMA.val_nil]
    have := OMA.ww_pos i
    linarith
  | cons x xs ih =>
    intro s i h
    obtain ⟨h1, _, h3⟩ := h
    have hi := ih (OMA.nxt s x) (i + 1) h3
    rw [OMA.val_cons]
    have hx : (x : ℝ) ≤ 2 := by exact_mod_cast h1
    have hw := OMA.ww_pos (i + 1)
    have hd := OMA.ww_succ_le i
    have h5 : (x : ℝ) * OMA.ww (i + 1) ≤ 2 * OMA.ww (i + 1) :=
      mul_le_mul_of_nonneg_right hx hw.le
    linarith

theorem OMA.vb : ∀ (l : List ℕ) (i : ℕ),
    (OMA.adm false l →
      OMA.val OMA.wv i l ≤ OMA.wv i + ∑ t ∈ Finset.range l.length, OMA.wv (i + t)) ∧
    (OMA.adm true l →
      OMA.val OMA.wv i l ≤ ∑ t ∈ Finset.range l.length, OMA.wv (i + t)) := by
  intro l
  induction l with
  | nil =>
    intro i
    have := OMA.wv_pos i
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · rw [OMA.val_nil]; simp; linarith
    · rw [OMA.val_nil]; simp
  | cons x xs ih =>
    intro i
    obtain ⟨ihF, ihR⟩ := ih (i + 1)
    have hsum : ∑ t ∈ Finset.range (x :: xs).length, OMA.wv (i + t)
        = ∑ t ∈ Finset.range xs.length, OMA.wv (i + 1 + t) + OMA.wv i := by
      rw [List.length_cons, Finset.sum_range_succ']
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      omega
    have hpos := OMA.wv_pos i
    have hmono := OMA.wv_succ_le i
    rw [hsum]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := h
      rw [OMA.val_cons]
      interval_cases x
      · have hT := ihF h3
        push_cast
        linarith
      · have hT := ihF h3
        push_cast
        linarith
      · have hT := ihR h3
        push_cast
        linarith
    · obtain ⟨h1, h2, h3⟩ := h
      rw [OMA.val_cons]
      interval_cases x
      · have hT := ihF h3
        push_cast
        linarith
      · have hT := ihR h3
        push_cast
        linarith
      · exact absurd (h2 rfl) (by decide)

theorem OMA.nval_append (g : ℕ → ℕ) (d : ℕ) : ∀ (l : List ℕ) (i : ℕ),
    OMA.nval g i (l ++ [d]) = OMA.nval g i l + d * g (i + l.length) := by
  intro l
  induction l with
  | nil => intro i; simp [OMA.nval]
  | cons x xs ih =>
    intro i
    have e : i + (x :: xs).length = i + 1 + xs.length := by
      rw [List.length_cons]; omega
    rw [e]
    show x * g i + OMA.nval g (i + 1) (xs ++ [d])
      = x * g i + OMA.nval g (i + 1) xs + d * g (i + 1 + xs.length)
    rw [ih (i + 1)]; ring

theorem OMA.fin_append (d : ℕ) : ∀ (l : List ℕ) (s : Bool),
    OMA.fin s (l ++ [d]) = OMA.nxt (OMA.fin s l) d := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons x xs ih => intro s; exact ih (OMA.nxt s x)

theorem OMA.adm_append (d : ℕ) (hd : d ≤ 2) : ∀ (l : List ℕ) (s : Bool),
    OMA.adm s l → (d = 2 → OMA.fin s l = false) → OMA.adm s (l ++ [d]) := by
  intro l
  induction l with
  | nil => intro s _ h2; exact ⟨hd, h2, trivial⟩
  | cons x xs ih =>
    intro s h h2
    obtain ⟨h1, h1', h3⟩ := h
    exact ⟨h1, h1', ih (OMA.nxt s x) h3 h2⟩

theorem OMA.ex_aux : ∀ K : ℕ,
    (∀ n, n < OMA.G (K + 1) →
      ∃ l : List ℕ, l.length = K ∧ OMA.adm false l ∧ OMA.nval OMA.wG 0 l = n) ∧
    (∀ n, n + OMA.G K < OMA.G (K + 1) →
      ∃ l : List ℕ, l.length = K ∧ OMA.adm false l ∧ OMA.fin false l = false ∧
        OMA.nval OMA.wG 0 l = n) := by
  intro K
  induction K with
  | zero =>
    refine ⟨fun n hn => ⟨[], rfl, trivial, ?_⟩, fun n hn => ⟨[], rfl, trivial, rfl, ?_⟩⟩
    · rw [OMA.G_one] at hn
      show 0 = n
      omega
    · rw [OMA.G_one, OMA.G_zero] at hn
      show 0 = n
      omega
  | succ K ih =>
    obtain ⟨iha, ihb⟩ := ih
    have hrec : OMA.G (K + 1 + 1) + OMA.G K = 3 * OMA.G (K + 1) := OMA.G_rec K
    have hle := OMA.G_le_succ K
    have hwG : OMA.wG (0 + K) = OMA.G (K + 1) := by simp [OMA.wG]
    constructor
    · intro n hn
      by_cases c1 : n < OMA.G (K + 1)
      · obtain ⟨l, hl, ha, hv⟩ := iha n c1
        refine ⟨l ++ [0], ?_, ?_, ?_⟩
        · rw [List.length_append, hl]; rfl
        · exact OMA.adm_append 0 (by norm_num) l false ha (fun h => absurd h (by norm_num))
        · rw [OMA.nval_append, hv]; simp
      · by_cases c2 : n < 2 * OMA.G (K + 1)
        · obtain ⟨l, hl, ha, hv⟩ := iha (n - OMA.G (K + 1)) (by omega)
          refine ⟨l ++ [1], ?_, ?_, ?_⟩
          · rw [List.length_append, hl]; rfl
          · exact OMA.adm_append 1 (by norm_num) l false ha (fun h => absurd h (by norm_num))
          · rw [OMA.nval_append, hv, hl, hwG]; omega
        · obtain ⟨l, hl, ha, hf, hv⟩ := ihb (n - 2 * OMA.G (K + 1)) (by omega)
          refine ⟨l ++ [2], ?_, ?_, ?_⟩
          · rw [List.length_append, hl]; rfl
          · exact OMA.adm_append 2 (le_refl 2) l false ha (fun _ => hf)
          · rw [OMA.nval_append, hv, hl, hwG]; omega
    · intro n hn
      by_cases c1 : n < OMA.G (K + 1)
      · obtain ⟨l, hl, ha, hv⟩ := iha n c1
        refine ⟨l ++ [0], ?_, ?_, ?_, ?_⟩
        · rw [List.length_append, hl]; rfl
        · exact OMA.adm_append 0 (by norm_num) l false ha (fun h => absurd h (by norm_num))
        · rw [OMA.fin_append]; rfl
        · rw [OMA.nval_append, hv]; simp
      · obtain ⟨l, hl, ha, hf, hv⟩ := ihb (n - OMA.G (K + 1)) (by omega)
        refine ⟨l ++ [1], ?_, ?_, ?_, ?_⟩
        · rw [List.length_append, hl]; rfl
        · exact OMA.adm_append 1 (by norm_num) l false ha (fun h => absurd h (by norm_num))
        · rw [OMA.fin_append, hf]; rfl
        · rw [OMA.nval_append, hv, hl, hwG]; omega

theorem OMA.exists_rep (n : ℕ) :
    ∃ l : List ℕ, OMA.adm false l ∧ OMA.nval OMA.wG 0 l = n := by
  have h1 : n < OMA.G (n + 1) := lt_of_lt_of_le Nat.lt_two_pow_self (OMA.G_ge_pow n)
  obtain ⟨l, _, ha, hv⟩ := (OMA.ex_aux n).1 n h1
  exact ⟨l, ha, hv⟩

/-- A chosen admissible digit string of n. -/
noncomputable def OMA.rep (n : ℕ) : List ℕ := Classical.choose (OMA.exists_rep n)

theorem OMA.rep_spec (n : ℕ) :
    OMA.adm false (OMA.rep n) ∧ OMA.nval OMA.wG 0 (OMA.rep n) = n :=
  Classical.choose_spec (OMA.exists_rep n)

theorem OMA.val_zero : ∀ (l : List ℕ) (i : ℕ),
    OMA.val OMA.wt i l = 0 → OMA.val OMA.ww i l = 0 := by
  intro l
  induction l with
  | nil => intro i _; rfl
  | cons x xs ih =>
    intro i h
    rw [OMA.val_cons] at h ⊢
    have h1 : 0 ≤ (x : ℝ) * OMA.wt i := mul_nonneg (Nat.cast_nonneg x) (OMA.wt_pos i).le
    have h2 : 0 ≤ OMA.val OMA.wt (i + 1) xs :=
      OMA.val_nonneg OMA.wt (fun t => (OMA.wt_pos t).le) xs (i + 1)
    have h3 : (x : ℝ) * OMA.wt i = 0 := by linarith
    have h4 : OMA.val OMA.wt (i + 1) xs = 0 := by linarith
    have h5 : (x : ℝ) = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · exact absurd h (OMA.wt_pos i).ne'
    rw [h5, ih (i + 1) h4]; ring

/-- The comparison statement: R vanishes with B, is nonnegative when B is positive, and is at
least ww j when B is exactly the weight wt j. -/
def OMA.LexR (B R : ℝ) : Prop :=
  (B = 0 → R = 0) ∧ (0 < B → 0 ≤ R ∧ ∀ j : ℕ, B = OMA.wt j → OMA.ww j ≤ R)

theorem OMA.core (i x y : ℕ) (Ta Tb Wa Wb : ℝ) (hxy : x ≠ y)
    (hTa0 : 0 ≤ Ta) (hTa : Ta < OMA.wt i) (hTb0 : 0 ≤ Tb) (hTb : Tb < OMA.wt i)
    (hWa0 : 0 ≤ Wa) (hWb : Wb ≤ 2 / 7 * OMA.ww i)
    (hup : (x : ℝ) * OMA.wt i + Ta < OMA.tau ^ i)
    (ih0 : Ta - Tb = 0 → Wa - Wb = 0) :
    OMA.LexR (((x : ℝ) * OMA.wt i + Ta) - ((y : ℝ) * OMA.wt i + Tb))
      (((x : ℝ) * OMA.ww i + Wa) - ((y : ℝ) * OMA.ww i + Wb)) := by
  have hwt := OMA.wt_pos i
  have hww := OMA.ww_pos i
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · -- x < y : B is negative
    have h1 : (x : ℝ) + 1 ≤ (y : ℝ) := by exact_mod_cast h
    have hB : ((x : ℝ) * OMA.wt i + Ta) - ((y : ℝ) * OMA.wt i + Tb) < 0 := by
      have : ((x : ℝ) + 1) * OMA.wt i ≤ (y : ℝ) * OMA.wt i :=
        mul_le_mul_of_nonneg_right h1 hwt.le
      linarith
    exact ⟨fun h0 => absurd h0 (ne_of_lt hB), fun h0 => absurd h0 (not_lt.mpr hB.le)⟩
  · -- y < x : B is positive
    have h1 : (y : ℝ) + 1 ≤ (x : ℝ) := by exact_mod_cast h
    have h2 : ((y : ℝ) + 1) * OMA.wt i ≤ (x : ℝ) * OMA.wt i :=
      mul_le_mul_of_nonneg_right h1 hwt.le
    have h3 : ((y : ℝ) + 1) * OMA.ww i ≤ (x : ℝ) * OMA.ww i :=
      mul_le_mul_of_nonneg_right h1 hww.le
    have hB : 0 < ((x : ℝ) * OMA.wt i + Ta) - ((y : ℝ) * OMA.wt i + Tb) := by linarith
    refine ⟨fun h0 => absurd h0 (ne_of_gt hB), fun _ => ⟨by linarith, ?_⟩⟩
    intro j hj
    have hy0 : 0 ≤ (y : ℝ) * OMA.wt i := mul_nonneg (Nat.cast_nonneg y) hwt.le
    -- i ≤ j
    have hij : i ≤ j := by
      by_contra hcon
      have hji : j + 1 ≤ i := by omega
      have hpow : OMA.tau ^ i ≤ OMA.tau ^ (j + 1) :=
        pow_le_pow_of_le_one OMA.tau_pos.le (by linarith [OMA.tau_lt]) hji
      have hwj : OMA.wt j = OMA.tau ^ (j + 1) := rfl
      linarith
    rcases eq_or_lt_of_le hij with hij' | hij'
    · -- j = i : the top digit differs by exactly one and the tails agree
      subst hij'
      have hx1 : x = y + 1 := by
        have h4 : ((x : ℝ) - (y : ℝ) - 1) * OMA.wt i < 1 * OMA.wt i := by linarith
        have h5 : (x : ℝ) - (y : ℝ) - 1 < 1 := lt_of_mul_lt_mul_right h4 hwt.le
        have h6 : (x : ℝ) < ((y + 2 : ℕ) : ℝ) := by push_cast; linarith
        have h7 : x < y + 2 := by exact_mod_cast h6
        omega
      have hx1R : (x : ℝ) = (y : ℝ) + 1 := by rw [hx1]; push_cast; ring
      have hT : Ta - Tb = 0 := by rw [hx1R] at hj; linarith
      have hW := ih0 hT
      rw [hx1R]; linarith
    · -- i < j
      have h5 := OMA.ww_succ_le i
      have h6 := OMA.ww_anti (i + 1) j (by omega)
      have h7 := OMA.ww_pos (i + 1)
      linarith

theorem OMA.lex : ∀ (la lb : List ℕ) (i : ℕ), OMA.adm false la → OMA.adm false lb →
    OMA.LexR (OMA.val OMA.wt i la - OMA.val OMA.wt i lb)
      (OMA.val OMA.ww i la - OMA.val OMA.ww i lb) := by
  intro la
  induction la with
  | nil =>
    intro lb i _ hb
    have h0 := OMA.val_nonneg OMA.wt (fun t => (OMA.wt_pos t).le) lb i
    rw [OMA.val_nil, OMA.val_nil]
    refine ⟨fun hB => ?_, fun hB => absurd hB (by linarith)⟩
    have := OMA.val_zero lb i (by linarith)
    linarith
  | cons x xs ih =>
    intro lb i ha hb
    have key : ∀ (y : ℕ) (ys : List ℕ), OMA.adm false (y :: ys) →
        OMA.LexR (OMA.val OMA.wt i (x :: xs) - OMA.val OMA.wt i (y :: ys))
          (OMA.val OMA.ww i (x :: xs) - OMA.val OMA.ww i (y :: ys)) := by
      intro y ys hb'
      obtain ⟨hx, hxs⟩ := OMA.adm_tail false x xs ha
      obtain ⟨hy, hys⟩ := OMA.adm_tail false y ys hb'
      have ihh := ih ys (i + 1) hxs hys
      rw [OMA.val_cons, OMA.val_cons, OMA.val_cons, OMA.val_cons]
      by_cases hxy : x = y
      · subst hxy
        have e1 : ((x : ℝ) * OMA.wt i + OMA.val OMA.wt (i + 1) xs)
            - ((x : ℝ) * OMA.wt i + OMA.val OMA.wt (i + 1) ys)
            = OMA.val OMA.wt (i + 1) xs - OMA.val OMA.wt (i + 1) ys := by ring
        have e2 : ((x : ℝ) * OMA.ww i + OMA.val OMA.ww (i + 1) xs)
            - ((x : ℝ) * OMA.ww i + OMA.val OMA.ww (i + 1) ys)
            = OMA.val OMA.ww (i + 1) xs - OMA.val OMA.ww (i + 1) ys := by ring
        rw [e1, e2]; exact ihh
      · exact OMA.core i x y _ _ _ _ hxy
          (OMA.val_nonneg OMA.wt (fun t => (OMA.wt_pos t).le) xs (i + 1))
          ((OMA.tb xs (i + 1)).1 hxs)
          (OMA.val_nonneg OMA.wt (fun t => (OMA.wt_pos t).le) ys (i + 1))
          ((OMA.tb ys (i + 1)).1 hys)
          (OMA.val_nonneg OMA.ww (fun t => (OMA.ww_pos t).le) xs (i + 1))
          (OMA.wb ys false i hys)
          ((OMA.tb (x :: xs) i).1 ha)
          ihh.1
    cases lb with
    | nil =>
      have h := key 0 [] ⟨by norm_num, fun h => absurd h (by norm_num), trivial⟩
      have e1 : OMA.val OMA.wt i [0] = OMA.val OMA.wt i [] := by simp [OMA.val]
      have e2 : OMA.val OMA.ww i [0] = OMA.val OMA.ww i [] := by simp [OMA.val]
      rw [e1, e2] at h; exact h
    | cons y ys => exact key y ys hb

theorem OMA.unit : ∀ n : ℕ, 1 ≤ n → ∀ k : ℤ,
    (n : ℤ) ^ 2 - 3 * (n : ℤ) * k + k ^ 2 = 1 →
    0 < (n : ℝ) * OMA.tau - (k : ℝ) → (n : ℝ) * OMA.tau - (k : ℝ) < 1 →
    ∃ j : ℕ, n = OMA.G (j + 1) ∧ (n : ℝ) * OMA.tau - (k : ℝ) = OMA.wt j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn k hN hB0 hB1
    have htp := OMA.tau_pos
    have htl := OMA.tau_lt
    have hsq := OMA.tau_sq
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hk0 : 0 ≤ k := by
      have h1 : (-1 : ℝ) < (k : ℝ) := by nlinarith
      have h2 : ((-1 : ℤ) : ℝ) < (k : ℝ) := by push_cast; exact h1
      have h3 : (-1 : ℤ) < k := by exact_mod_cast h2
      omega
    have hkn : k < (n : ℤ) := by
      have h1 : (k : ℝ) < (n : ℝ) := by nlinarith
      exact_mod_cast h1
    rcases eq_or_lt_of_le hk0 with hk | hk
    · -- k = 0, so n = 1
      subst hk
      have hn1 : n = 1 := by
        by_contra hne
        have h2 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast (by omega : 2 ≤ n)
        nlinarith
      subst hn1
      refine ⟨0, by rw [OMA.G_one], ?_⟩
      simp [OMA.wt]
    · -- 1 ≤ k : descend to (k, 3k - n)
      obtain ⟨n', hn'⟩ : ∃ n' : ℕ, (n' : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg hk0⟩
      have hn'1 : 1 ≤ n' := by
        have h1 : (0 : ℤ) < (n' : ℤ) := by rw [hn']; exact hk
        exact_mod_cast h1
      have hn'n : n' < n := by
        have h1 : (n' : ℤ) < (n : ℤ) := by rw [hn']; exact hkn
        exact_mod_cast h1
      have hN' : (n' : ℤ) ^ 2 - 3 * (n' : ℤ) * (3 * k - n) + (3 * k - n) ^ 2 = 1 := by
        rw [hn']; linear_combination hN
      have hkR : (n' : ℝ) = (k : ℝ) := by exact_mod_cast hn'
      have h2n : (2 : ℝ) ≤ (n : ℝ) := by
        have h1 : (1 : ℤ) < (n : ℤ) := by omega
        have h2 : 2 ≤ n := by exact_mod_cast h1
        exact_mod_cast h2
      obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (n : ℝ) * OMA.tau - (k : ℝ) := ⟨_, rfl⟩
      obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (3 - OMA.tau) * (n : ℝ) - (k : ℝ) := ⟨_, rfl⟩
      rw [← hB] at hB0 hB1
      have hAB : A * B = 1 := by
        have h1 : (((n : ℤ) ^ 2 - 3 * (n : ℤ) * k + k ^ 2 : ℤ) : ℝ) = 1 := by
          exact_mod_cast hN
        push_cast at h1
        rw [hA, hB]
        linear_combination h1 - (n : ℝ) ^ 2 * hsq
      have hAgt : 3 - OMA.tau < A := by
        rw [hA]
        have h1 : (k : ℝ) < (n : ℝ) * OMA.tau := by rw [hB] at hB0; linarith
        have h3 : 0 ≤ ((n : ℝ) - 2) * (3 - 2 * OMA.tau) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith
      have hB' : (n' : ℝ) * OMA.tau - (((3 * k - (n : ℤ) : ℤ)) : ℝ) = B * (3 - OMA.tau) := by
        rw [hkR, hB]; push_cast
        linear_combination (n : ℝ) * hsq
      have hB'0 : 0 < (n' : ℝ) * OMA.tau - (((3 * k - (n : ℤ) : ℤ)) : ℝ) := by
        rw [hB']; exact mul_pos hB0 (by linarith)
      have hB'1 : (n' : ℝ) * OMA.tau - (((3 * k - (n : ℤ) : ℤ)) : ℝ) < 1 := by
        rw [hB']
        have h1 : 0 < B * (A - (3 - OMA.tau)) := mul_pos hB0 (by linarith)
        have h2 : B * (A - (3 - OMA.tau)) = A * B - B * (3 - OMA.tau) := by ring
        linarith
      obtain ⟨j, hj1, hj2⟩ := ih n' hn'n hn'1 (3 * k - n) hN' hB'0 hB'1
      have h3 : (3 - OMA.tau) * OMA.tau = 1 := by linear_combination (-1 : ℝ) * hsq
      have hBj : B = OMA.wt (j + 1) := by
        have h4 : OMA.wt (j + 1) = OMA.wt j * OMA.tau := by unfold OMA.wt; ring
        rw [h4, ← hj2, hB']
        linear_combination (-B) * h3
      have hpow := OMA.tau_pow j
      have hkG : (k : ℝ) = (OMA.G (j + 1) : ℝ) := by
        rw [← hkR, hj1]
      have h5 : (((3 * k - (n : ℤ) : ℤ)) : ℝ) = ((OMA.G j : ℤ) : ℝ) := by
        have h6 : OMA.wt j = OMA.tau ^ (j + 1) := rfl
        rw [h6, hpow, hkR, hkG] at hj2
        push_cast
        push_cast at hj2
        linarith
      have h6 : 3 * k - (n : ℤ) = (OMA.G j : ℤ) := by exact_mod_cast h5
      have h7 : (OMA.G (j + 2) : ℤ) + (OMA.G j : ℤ) = 3 * (OMA.G (j + 1) : ℤ) := by
        exact_mod_cast OMA.G_rec j
      have h8 : k = (OMA.G (j + 1) : ℤ) := by exact_mod_cast hkG
      have h9 : (n : ℤ) = (OMA.G (j + 2) : ℤ) := by linarith
      refine ⟨j + 1, by exact_mod_cast h9, ?_⟩
      rw [← hB]; exact hBj

theorem OMA.sqrt5_irr : Irrational (Real.sqrt 5) := by
  have h := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  simpa using h

theorem OMA.key_real (n : ℕ) (hn : 1 ≤ n) (k : ℤ) (B R : ℝ)
    (hBk : B = (n : ℝ) * OMA.tau - (k : ℝ)) (hB1 : B < 1) (hB1' : -1 < B)
    (hpos : 0 < B → 0 ≤ R ∧ ∀ j : ℕ, B = OMA.wt j → OMA.ww j ≤ R)
    (hneg : B < 0 → R ≤ 0) :
    1 ≤ (n : ℝ) * |Real.sqrt 5 * B + R| := by
  have hsq := OMA.tau_sq
  have hs5 := OMA.sqrt5_gt
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨N, hNdef⟩ : ∃ N : ℤ, N = (n : ℤ) ^ 2 - 3 * (n : ℤ) * k + k ^ 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (3 - OMA.tau) * (n : ℝ) - (k : ℝ) := ⟨_, rfl⟩
  have hAB : A * B = (N : ℝ) := by
    rw [hNdef, hA, hBk]; push_cast
    linear_combination (-(n : ℝ) ^ 2) * hsq
  have hA2 : A = Real.sqrt 5 * (n : ℝ) + B := by
    rw [hA, hBk, OMA.sqrt5_eq]; ring
  have hApos : 0 < A := by
    rw [hA2]
    have : Real.sqrt 5 * 1 ≤ Real.sqrt 5 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hnR (by linarith)
    linarith
  have hprod : (n : ℝ) * (Real.sqrt 5 * B) = (N : ℝ) - B ^ 2 := by
    rw [← hAB, hA2]; ring
  have hB0 : B ≠ 0 := by
    intro h0
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have htau : OMA.tau = (k : ℝ) / (n : ℝ) := by
      rw [eq_div_iff hn0]; rw [h0] at hBk; linarith
    apply OMA.sqrt5_irr
    refine ⟨3 - 2 * ((k : ℚ) / (n : ℚ)), ?_⟩
    push_cast
    rw [OMA.sqrt5_eq, htau]
  rcases lt_or_gt_of_ne hB0 with hBneg | hBpos
  · -- B < 0
    have hR := hneg hBneg
    have hNneg : (N : ℝ) < 0 := by rw [← hAB]; exact mul_neg_of_pos_of_neg hApos hBneg
    have hN1 : N < 0 := by exact_mod_cast hNneg
    have hN2 : (N : ℝ) ≤ -1 := by
      have : N ≤ -1 := by omega
      exact_mod_cast this
    have hneg' : Real.sqrt 5 * B + R < 0 := by
      have : Real.sqrt 5 * B < 0 := mul_neg_of_pos_of_neg (by linarith) hBneg
      linarith
    rw [abs_of_neg hneg']
    have h2 : (n : ℝ) * R ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hR
    have h3 : (n : ℝ) * (-(Real.sqrt 5 * B + R))
        = -((n : ℝ) * (Real.sqrt 5 * B)) - (n : ℝ) * R := by ring
    rw [h3, hprod]
    nlinarith [sq_nonneg B]
  · -- 0 < B
    obtain ⟨hR, hcrit⟩ := hpos hBpos
    have hNpos : (0 : ℝ) < (N : ℝ) := by rw [← hAB]; exact mul_pos hApos hBpos
    have hN1 : 0 < N := by exact_mod_cast hNpos
    have hpos' : 0 < Real.sqrt 5 * B + R := by
      have : 0 < Real.sqrt 5 * B := mul_pos (by linarith) hBpos
      linarith
    rw [abs_of_pos hpos']
    by_cases hNone : N = 1
    · -- the critical case
      have hN' : (n : ℤ) ^ 2 - 3 * (n : ℤ) * k + k ^ 2 = 1 := by rw [← hNdef]; exact hNone
      obtain ⟨j, hj1, hj2⟩ := OMA.unit n hn k hN' (by rw [← hBk]; exact hBpos)
        (by rw [← hBk]; exact hB1)
      rw [← hBk] at hj2
      have hRj := hcrit j hj2
      have hone : (n : ℝ) * OMA.wv j = 1 := by
        rw [hj1]
        unfold OMA.wv
        have := OMA.G_cast_pos j
        field_simp
      have hle : OMA.wv j ≤ Real.sqrt 5 * B + R := by
        rw [OMA.wv_eq, ← hj2]; linarith
      calc (1 : ℝ) = (n : ℝ) * OMA.wv j := hone.symm
        _ ≤ (n : ℝ) * (Real.sqrt 5 * B + R) :=
          mul_le_mul_of_nonneg_left hle (by linarith)
    · have hN2 : (2 : ℝ) ≤ (N : ℝ) := by
        have : 2 ≤ N := by omega
        exact_mod_cast this
      have hBsq : B ^ 2 < 1 := by nlinarith
      have h2 : 0 ≤ (n : ℝ) * R := mul_nonneg (by linarith) hR
      have h3 : (n : ℝ) * (Real.sqrt 5 * B + R)
          = (n : ℝ) * (Real.sqrt 5 * B) + (n : ℝ) * R := by ring
      rw [h3, hprod]
      linarith

theorem OMA.key (la lb : List ℕ) (ha : OMA.adm false la) (hb : OMA.adm false lb) (n : ℕ)
    (hn : 1 ≤ n) (hval : OMA.nval OMA.wG 0 la = OMA.nval OMA.wG 0 lb + n) :
    1 ≤ (n : ℝ) * |OMA.val OMA.wv 0 la - OMA.val OMA.wv 0 lb| := by
  have hua : OMA.val OMA.wt 0 la = OMA.tau * ((OMA.nval OMA.wG 0 la : ℕ) : ℝ)
      - ((OMA.nval OMA.wK 0 la : ℕ) : ℝ) := by
    rw [OMA.val_wt, OMA.nval_cast, OMA.nval_cast]
  have hub : OMA.val OMA.wt 0 lb = OMA.tau * ((OMA.nval OMA.wG 0 lb : ℕ) : ℝ)
      - ((OMA.nval OMA.wK 0 lb : ℕ) : ℝ) := by
    rw [OMA.val_wt, OMA.nval_cast, OMA.nval_cast]
  have hD : OMA.val OMA.wv 0 la - OMA.val OMA.wv 0 lb
      = Real.sqrt 5 * (OMA.val OMA.wt 0 la - OMA.val OMA.wt 0 lb)
        + (OMA.val OMA.ww 0 la - OMA.val OMA.ww 0 lb) := by
    rw [OMA.val_wv, OMA.val_wv]; ring
  have ha0 := OMA.val_nonneg OMA.wt (fun t => (OMA.wt_pos t).le) la 0
  have hb0 := OMA.val_nonneg OMA.wt (fun t => (OMA.wt_pos t).le) lb 0
  have ha1 : OMA.val OMA.wt 0 la < 1 := by
    have h := (OMA.tb la 0).1 ha
    simpa using h
  have hb1 : OMA.val OMA.wt 0 lb < 1 := by
    have h := (OMA.tb lb 0).1 hb
    simpa using h
  have hl1 := OMA.lex la lb 0 ha hb
  have hl2 := OMA.lex lb la 0 hb ha
  rw [hD]
  refine OMA.key_real n hn
    (((OMA.nval OMA.wK 0 la : ℕ) : ℤ) - ((OMA.nval OMA.wK 0 lb : ℕ) : ℤ)) _ _ ?_
    (by linarith) (by linarith) hl1.2 ?_
  · rw [hua, hub, hval]; push_cast; ring
  · intro hneg
    have h := (hl2.2 (by linarith)).1
    linarith

/-- The constant of the statement. -/
noncomputable def OMA.cc : ℝ := 1 + ∑' (k : ℕ+), (1 : ℝ) / ((Nat.fib (2 * (k : ℕ)) : ℕ) : ℝ)

theorem OMA.summ : Summable (fun k : ℕ+ => (1 : ℝ) / ((Nat.fib (2 * (k : ℕ)) : ℕ) : ℝ)) := by
  have hg : Summable (fun k : ℕ+ => 2 * ((1 : ℝ) / 2) ^ (k : ℕ)) :=
    (summable_geometric_two.mul_left 2).comp_injective PNat.coe_injective
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hg
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by have := k.pos; omega⟩
  rw [hj]
  have h1 : 2 ^ j ≤ OMA.G (j + 1) := OMA.G_ge_pow j
  have h2 : (2 : ℝ) ^ j ≤ ((Nat.fib (2 * (j + 1)) : ℕ) : ℝ) := by
    have h : ((2 ^ j : ℕ) : ℝ) ≤ ((OMA.G (j + 1) : ℕ) : ℝ) := Nat.cast_le.mpr h1
    push_cast at h
    exact h
  have h3 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  rw [div_le_iff₀ (lt_of_lt_of_le h3 h2)]
  have h4 : 2 * ((1 : ℝ) / 2) ^ (j + 1) * (2 : ℝ) ^ j = 1 := by
    rw [pow_succ, one_div, inv_pow]
    field_simp
  calc (1 : ℝ) = 2 * ((1 : ℝ) / 2) ^ (j + 1) * (2 : ℝ) ^ j := h4.symm
    _ ≤ 2 * ((1 : ℝ) / 2) ^ (j + 1) * ((Nat.fib (2 * (j + 1)) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)

theorem OMA.cc_ge : 1 ≤ OMA.cc := by
  unfold OMA.cc
  have h : 0 ≤ ∑' (k : ℕ+), (1 : ℝ) / ((Nat.fib (2 * (k : ℕ)) : ℕ) : ℝ) :=
    tsum_nonneg (fun k => by positivity)
  linarith

theorem OMA.partial_le (K : ℕ) : (∑ t ∈ Finset.range K, OMA.wv t) ≤ OMA.cc - 1 := by
  unfold OMA.cc
  have h := Summable.sum_le_tsum ((Finset.range K).map ⟨Nat.succPNat, Nat.succPNat_injective⟩)
    (fun k _ => by positivity) OMA.summ
  rw [Finset.sum_map] at h
  have e : ∀ t ∈ Finset.range K, OMA.wv t
      = (1 : ℝ) / ((Nat.fib (2 * ((Nat.succPNat t : ℕ+) : ℕ)) : ℕ) : ℝ) := by
    intro t _
    rfl
  rw [Finset.sum_congr rfl e]
  have e2 : (1 : ℝ) + ∑' (k : ℕ+), (1 : ℝ) / ((Nat.fib (2 * (k : ℕ)) : ℕ) : ℝ) - 1
      = ∑' (k : ℕ+), (1 : ℝ) / ((Nat.fib (2 * (k : ℕ)) : ℕ) : ℝ) := by ring
  rw [e2]
  exact h

/-- The extremal sequence of Chung and Graham. -/
noncomputable def OMA.xseq (n : ℕ) : ℝ := OMA.val OMA.wv 0 (OMA.rep n) / OMA.cc

theorem OMA.xseq_mem (n : ℕ) : OMA.xseq n ∈ Set.Icc (0 : ℝ) 1 := by
  have hc := OMA.cc_ge
  obtain ⟨ha, _⟩ := OMA.rep_spec n
  have h0 : 0 ≤ OMA.val OMA.wv 0 (OMA.rep n) :=
    OMA.val_nonneg OMA.wv (fun t => (OMA.wv_pos t).le) _ 0
  have h1 : OMA.val OMA.wv 0 (OMA.rep n) ≤ OMA.cc := by
    have h2 := (OMA.vb (OMA.rep n) 0).1 ha
    have h3 := OMA.partial_le (OMA.rep n).length
    have h4 : OMA.wv 0 = 1 := by simp [OMA.wv, OMA.G_one]
    have h5 : ∑ t ∈ Finset.range (OMA.rep n).length, OMA.wv (0 + t)
        = ∑ t ∈ Finset.range (OMA.rep n).length, OMA.wv t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Nat.zero_add]
    rw [h5, h4] at h2
    linarith
  unfold OMA.xseq
  constructor
  · exact div_nonneg h0 (by linarith)
  · rw [div_le_one (by linarith)]; exact h1

theorem OMA.main (m n : ℕ) (hn : 1 ≤ n) :
    1 / OMA.cc ≤ (n : ℝ) * |OMA.xseq (m + n) - OMA.xseq m| := by
  have hc : 0 < OMA.cc := by linarith [OMA.cc_ge]
  obtain ⟨ha, hva⟩ := OMA.rep_spec (m + n)
  obtain ⟨hb, hvb⟩ := OMA.rep_spec m
  have hk := OMA.key (OMA.rep (m + n)) (OMA.rep m) ha hb n hn (by rw [hva, hvb])
  unfold OMA.xseq
  rw [← sub_div, abs_div, abs_of_pos hc, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hk hc.le

theorem OMA.solution : type_of% @Erdos480.erdos_480.variants.chung_graham_best_possible := by
  intro c ε hε h
  have hcc : c = OMA.cc := rfl
  have hx := h OMA.xseq OMA.xseq_mem
  have hle : 1 / c ≤ 1 / c - ε := by
    refine le_trans (le_ciInf (fun n => ?_)) hx
    apply Filter.le_liminf_of_le
    · apply Filter.IsBoundedUnder.isCoboundedUnder_ge
      refine Filter.isBoundedUnder_of ⟨((n : ℕ) : ℝ), fun m => ?_⟩
      have h1 := OMA.xseq_mem (m + (n : ℕ))
      have h2 := OMA.xseq_mem m
      have h3 : |OMA.xseq (m + (n : ℕ)) - OMA.xseq m| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      have h4 : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
      calc ((n : ℕ) : ℝ) * |OMA.xseq (m + (n : ℕ)) - OMA.xseq m|
          ≤ ((n : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left h3 h4
        _ = ((n : ℕ) : ℝ) := by ring
    · refine Filter.Eventually.of_forall (fun m => ?_)
      rw [hcc]
      exact OMA.main m (n : ℕ) n.pos
  linarith
